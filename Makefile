
CFLAGS= -g -Wall -I../cJSON

all:
	g++ $(CFLAGS) generatefsm.cpp
	rm -f yy.json.dump
	./a.out
