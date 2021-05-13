
CFLAGS= -g -Wall -I../cJSON

SOURCES = generatefsm.cpp atomiccAssert.cpp

all: $(OBJS)
	g++ $(CFLAGS) $(SOURCES)
	rm -f yy.json.dump
	./a.out
