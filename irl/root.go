package main

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
)

// What a checkout of ir-lean has, which no other directory is likely to.
var rootMarkers = []string{"lakefile.toml", "tools/verify.py"}

// findRoot is the checkout irl runs the tools of: IRL_ROOT if it's set, or else the first directory holding
// rootMarkers, above irl's own binary and then above the working directory. build/irl finds the checkout it
// was built in, wherever it's run from.
func findRoot() (string, error) {
	if dir := os.Getenv("IRL_ROOT"); dir != "" {
		if !isRoot(dir) {
			return "", fmt.Errorf("IRL_ROOT is %s, which isn't an ir-lean checkout: it has no lakefile.toml "+
				"and tools/verify.py", dir)
		}
		return filepath.Abs(dir)
	}
	var starts []string
	if exe, err := os.Executable(); err == nil {
		if real, err := filepath.EvalSymlinks(exe); err == nil {
			starts = append(starts, filepath.Dir(real))
		}
	}
	if wd, err := os.Getwd(); err == nil {
		starts = append(starts, wd)
	}
	for _, start := range starts {
		for dir := start; ; dir = filepath.Dir(dir) {
			if isRoot(dir) {
				return dir, nil
			}
			if filepath.Dir(dir) == dir {
				break
			}
		}
	}
	return "", errors.New("no ir-lean checkout above irl's binary or the working directory: set IRL_ROOT")
}

func isRoot(dir string) bool {
	for _, marker := range rootMarkers {
		if _, err := os.Stat(filepath.Join(dir, marker)); err != nil {
			return false
		}
	}
	return true
}
