OBJS = Lib.vo Quot.vo syntaxdb.vo quotsyntax.vo
CC = coqc

all: $(OBJS)

%.vo: %.v
	coqc $(FLAGS) $<

clean:
	rm *.vo



