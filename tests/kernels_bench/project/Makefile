# The synthetic project's own build, which bench/kernels/harness.py drives as it would a project's.
CC ?= clang
CFLAGS ?= -O3

hot: hot.o kernel.o
	$(CC) $(CFLAGS) -o $@ hot.o kernel.o

hot.o: hot.c
	$(CC) $(CFLAGS) -c -o $@ hot.c

kernel.o: kernel.c
	$(CC) $(CFLAGS) -c -o $@ kernel.c
