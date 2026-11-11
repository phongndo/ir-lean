package main

import (
	"context"
	"io"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"
)

// These run the real checkout's tools for their contracts, which needs Python and no Lean.

func realRoot(t *testing.T) string {
	t.Helper()
	wd, err := os.Getwd()
	if err != nil {
		t.Fatal(err)
	}
	for dir := wd; ; dir = filepath.Dir(dir) {
		if isRoot(dir) {
			return dir
		}
		if filepath.Dir(dir) == dir {
			t.Fatalf("no ir-lean checkout above %s", wd)
		}
	}
}

// What verify_check and ptf_run take is what their tools' request_fields say they take: the JSON Schema in
// tools/verify.py and tools/prooftest/prooftest.py has one property for each field, and no others.
func TestRequestSchemasHaveEveryRequestField(t *testing.T) {
	root := realRoot(t)
	caps, err := capabilities(context.Background(), root)
	if err != nil {
		t.Fatal(err)
	}
	for _, name := range []string{"verify", "ptf"} {
		contract := caps["commands"].(map[string]any)[name].(map[string]any)["capabilities"].(map[string]any)
		fields := slices.Sorted(maps.Keys(contract["request_fields"].(map[string]any)))
		schema := contract["request_json_schema"].(map[string]any)
		properties := slices.Sorted(maps.Keys(schema["properties"].(map[string]any)))
		if !slices.Equal(fields, properties) {
			t.Errorf("%s's request has fields %v, and its JSON Schema properties %v", name, fields, properties)
		}
	}
	if _, err := newServer(context.Background(), root, root, 1, io.Discard); err != nil {
		t.Errorf("the server can't start on the real tools: %v", err)
	}
}

// The schema irl writes is named in the registry of every schema the repo writes, tools/irlean/schemas.py.
func TestCapabilitiesSchemaIsInTheRegistry(t *testing.T) {
	registry, err := os.ReadFile(filepath.Join(realRoot(t), "tools", "irlean", "schemas.py"))
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(registry), `"`+capabilitiesSchema+`"`) {
		t.Errorf("tools/irlean/schemas.py doesn't name %s", capabilitiesSchema)
	}
}
