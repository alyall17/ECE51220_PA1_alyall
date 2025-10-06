CC=gcc
CFLAGS=-std=c99 -O3 -Wall -Wshadow
LDLIBS=-lm

pa1: pa1.c
	$(CC) $(CFLAGS) -o pa1 pa1.c $(LDLIBS)

clean:
	rm -f pa1 *.o out_*
