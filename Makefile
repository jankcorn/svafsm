
JSONDIR=../cJSON

CFLAGS= -g -Wall -I$(JSONDIR)

SOURCES = generatefsm.cpp atomiccAssert.cpp $(JSONDIR)/cJSON.c

all: $(OBJS)
	g++ $(CFLAGS) $(SOURCES)
	rm -f yy.json.dump
	./a.out
