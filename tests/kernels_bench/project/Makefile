# The synthetic project's own build, which bench/kernels/harness.py drives as it would a project's. Like
# xxHash's, it builds again with other flags what it built, when it's run with them: `flags` holds the last
# ones, and every object depends on it. `make check` is its own test, and runs hot.
CC ?= clang
CFLAGS ?= -O3

hot: hot.o kernel.o
	$(CC) $(CFLAGS) -o $@ hot.o kernel.o

hot.o: hot.c flags
	$(CC) $(CFLAGS) -c -o $@ hot.c

kernel.o: kernel.c flags
	$(CC) $(CFLAGS) -c -o $@ kernel.c

flags: FORCE
	@echo '$(CFLAGS)' | cmp -s - $@ || echo '$(CFLAGS)' > $@

check: hot
	./hot mix 1 > /dev/null

.PHONY: FORCE check
