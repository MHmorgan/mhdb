
CC=gcc
CFLAGS=--std=c90 -Wno-deprecated-declarations

all : clean test

test : dbm.c test.c
	$(CC) $(CFLAGS) $^ -o $@

clean :
	rm -f test

purge : clean
	rm -f *.dir *.pag