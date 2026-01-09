# Blood Runtime Library Makefile

CC = cc
CFLAGS = -O2 -Wall -Wextra

.PHONY: all clean

all: runtime.o

runtime.o: runtime.c
	$(CC) $(CFLAGS) -c runtime.c -o runtime.o

clean:
	rm -f runtime.o
