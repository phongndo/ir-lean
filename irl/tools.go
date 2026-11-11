package main

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"sync"
	"time"
)

// capabilitiesSchema names what `irl capabilities` prints. tools/irlean/schemas.py names it too, as every
// schema the repo writes, and irl/schema_test.go checks they agree.
const capabilitiesSchema = "ir-lean.irl.capabilities/1"

// A command irl runs: one of the repo's tools, by its path in the checkout.
type command struct {
	name string
	what string
	path string
	// The arguments that print its contract as JSON, if it has one.
	capabilities []string
}

var commands = []command{
	{"emit", "translate LLVM IR to Lean", "build/ir-lean", nil},
	{"verify", "check one claim about one function", "tools/verify.py", []string{"capabilities"}},
	{"ptf", "proof tests: run a property on generated inputs", "tools/prooftest/prooftest.py",
		[]string{"capabilities"}},
	{"store", "find, check and add stored lemmas", "tools/store/store.py", []string{"capabilities", "--json"}},
}

// Tools with a name, and nothing built yet. docs/roadmap.md has where each stands.
var planned = []command{
	{name: "sopt", what: "the superoptimizer"},
	{name: "msc", what: "the memory-safety checker"},
}

func findCommand(list []command, name string) (command, bool) {
	i := slices.IndexFunc(list, func(c command) bool { return c.name == name })
	if i < 0 {
		return command{}, false
	}
	return list[i], true
}

// capabilities reads the contract of every command that has one, at once, and says which are built. The
// error says which couldn't be read. Their answers are as each tool prints them.
func capabilities(ctx context.Context, root string) (map[string]any, error) {
	entries := map[string]any{}
	var mu sync.Mutex
	var wg sync.WaitGroup
	var problems []string
	for _, c := range commands {
		path := filepath.Join(root, c.path)
		_, statErr := os.Stat(path)
		entry := map[string]any{"what": c.what, "runs": c.path, "built": statErr == nil}
		entries[c.name] = entry
		if c.capabilities == nil {
			continue
		}
		wg.Go(func() {
			r := runTool(ctx, root, append([]string{path}, c.capabilities...), nil, 5*time.Second)
			var contract map[string]any
			err := r.err
			if err == nil {
				err = json.Unmarshal(r.stdout, &contract)
			}
			mu.Lock()
			defer mu.Unlock()
			if err != nil || r.exit != 0 {
				why := fmt.Sprintf("exited %d", r.exit)
				if err != nil {
					why = err.Error()
				}
				problem := fmt.Sprintf("%s %s: %s: %s", c.path, strings.Join(c.capabilities, " "), why,
					bytes.TrimSpace(r.stderr))
				entry["error"] = problem
				problems = append(problems, problem)
				return
			}
			entry["capabilities"] = contract
		})
	}
	wg.Wait()
	for _, c := range planned {
		entries[c.name] = map[string]any{"what": c.what, "built": false}
	}
	var names []string
	for _, t := range newTools() {
		names = append(names, t.Name)
	}
	result := map[string]any{"schema": capabilitiesSchema, "root": root, "commands": entries, "mcp_tools": names}
	if problems != nil {
		slices.Sort(problems)
		return result, errors.New(strings.Join(problems, "; "))
	}
	return result, nil
}

// An MCP tool, as tools/list gives it, and how irl runs it.
type mcpTool struct {
	Name         string         `json:"name"`
	Title        string         `json:"title"`
	Description  string         `json:"description"`
	InputSchema  map[string]any `json:"inputSchema"`
	OutputSchema map[string]any `json:"outputSchema,omitempty"`
	Annotations  annotations    `json:"annotations"`
	// The command it runs, by its name in commands, and nothing for `capabilities`, which irl answers itself.
	command string
	// The command's arguments, and what it's sent on stdin, from the call's arguments.
	argv func(arguments json.RawMessage) ([]string, []byte, error)
	// Whether it runs Lean, and so takes one of the server's job slots.
	heavy bool
	// How to fill InputSchema and OutputSchema from the command's contract.
	fromContract func(t *mcpTool, contract map[string]any) error
}

type annotations struct {
	ReadOnly    bool `json:"readOnlyHint"`
	Destructive bool `json:"destructiveHint"`
	Idempotent  bool `json:"idempotentHint"`
	OpenWorld   bool `json:"openWorldHint"`
}

// stdinRequest sends the call's arguments to the tool as its request, on stdin, as `-` asks it to read one.
// The tool decides whether it's valid, as it does for a request file.
func stdinRequest(sub string) func(json.RawMessage) ([]string, []byte, error) {
	return func(arguments json.RawMessage) ([]string, []byte, error) {
		return []string{sub, "-"}, arguments, nil
	}
}

// requestSchemas takes a tool's input from its contract's request_json_schema, and its output from its
// schema and statuses, so the MCP schemas can't say anything the tool doesn't.
func requestSchemas(t *mcpTool, contract map[string]any) error {
	input, ok := contract["request_json_schema"].(map[string]any)
	if !ok {
		return errors.New("its capabilities have no request_json_schema")
	}
	statuses, ok := contract["statuses"].(map[string]any)
	if !ok {
		return errors.New("its capabilities have no statuses")
	}
	t.InputSchema = input
	t.OutputSchema = answerSchema([]any{contract["schema"]}, map[string]any{"enum": slices.Sorted(maps.Keys(statuses))})
	return nil
}

// answerSchema is what every answer has: the schema it names, and a status.
func answerSchema(schemas []any, status map[string]any) map[string]any {
	return map[string]any{
		"type":       "object",
		"properties": map[string]any{"schema": map[string]any{"enum": schemas}, "status": status},
		"required":   []string{"schema", "status"},
	}
}

// newTools is the MCP tools, each with its schemas still to be read from its command's contract.
func newTools() []*mcpTool {
	return []*mcpTool{
		{
			Name:  "verify_check",
			Title: "Check a claim about LLVM IR",
			Description: "Checks one claim about one function in LLVM IR, as `irl verify check` does, and answers " +
				"proved, counterexample, unsupported, timeout or error. Give `proof` and `theorem` to check a " +
				"proof, or `statement` and `witnesses` to look for a counterexample. Only `proved` says the claim " +
				"holds, and only as `claim.statement` and `assumptions` say. `reproduce.command` reruns it from a " +
				"terminal.",
			Annotations:  annotations{ReadOnly: true},
			command:      "verify",
			argv:         stdinRequest("check"),
			heavy:        true,
			fromContract: requestSchemas,
		},
		{
			Name:  "ptf_run",
			Title: "Run a proof test",
			Description: "Runs a property of one function in LLVM IR on generated inputs, as `irl ptf run` does: " +
				"tier 1 of a proof test. Answers passed_tier1, counterexample, vacuous or unknown. passed_tier1 " +
				"means no input tried made the property false: tested, not proved. A counterexample is shrunk, " +
				"checked by Lean's kernel, and stored, so the next run tries it first.",
			Annotations:  annotations{},
			command:      "ptf",
			argv:         stdinRequest("run"),
			heavy:        true,
			fromContract: requestSchemas,
		},
		{
			Name:  "store_lookup",
			Title: "Find stored lemmas",
			Description: "Finds stored lemmas that prove a statement, as `irl store lookup` does: exact, a stored " +
				"lemma states it, instance, one does once instantiated, with its hypotheses as side conditions, " +
				"or none. A lemma is checked again wherever it's used, so the store isn't trusted.",
			InputSchema: map[string]any{
				"type": "object",
				"properties": map[string]any{
					"statement": map[string]any{
						"type":        "string",
						"minLength":   1,
						"description": "A closed proposition, elaborated with `open IRLean`",
					},
					"imports": map[string]any{
						"type":        "array",
						"items":       map[string]any{"type": "string", "minLength": 1},
						"description": "Modules the statement needs",
					},
				},
				"required":             []string{"statement"},
				"additionalProperties": false,
			},
			Annotations: annotations{ReadOnly: true, Idempotent: true},
			command:     "store",
			argv:        storeLookup,
			heavy:       true,
			fromContract: func(t *mcpTool, contract map[string]any) error {
				schemas, ok := contract["schemas"].(map[string]any)
				if !ok || schemas["lookup"] == nil {
					return errors.New("its capabilities name no lookup schema")
				}
				// An error comes back in the store's own schema, with the status error. The store's contract
				// doesn't list a lookup's statuses, so any is allowed here.
				t.OutputSchema = answerSchema([]any{schemas["lookup"], contract["schema"]}, map[string]any{"type": "string"})
				return nil
			},
		},
		{
			Name:  "capabilities",
			Title: "What irl's tools take and answer",
			Description: "Every command's contract, as `irl capabilities` prints it: each one's statuses, reasons, " +
				"exit codes and request fields, and which commands are built.",
			InputSchema: map[string]any{"type": "object", "additionalProperties": false},
			Annotations: annotations{ReadOnly: true, Idempotent: true},
		},
	}
}

func storeLookup(arguments json.RawMessage) ([]string, []byte, error) {
	var a struct {
		Statement string   `json:"statement"`
		Imports   []string `json:"imports"`
	}
	decoder := json.NewDecoder(bytes.NewReader(arguments))
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(&a); err != nil {
		return nil, nil, fmt.Errorf("store_lookup takes {statement, imports}: %w", err)
	}
	if strings.TrimSpace(a.Statement) == "" {
		return nil, nil, errors.New("store_lookup needs a statement")
	}
	argv := []string{"lookup", "--statement", a.Statement}
	for _, m := range a.Imports {
		argv = append(argv, "--import", m)
	}
	return append(argv, "--json"), nil, nil
}
