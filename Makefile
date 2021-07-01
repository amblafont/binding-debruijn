OBJS = Lib.vo Quot.vo syntaxdb.vo quotsyntax.vo Summary.vo
CC = coqc

all: $(OBJS)

%.vo: %.v
	coqc $(FLAGS) $<

clean:
	rm *.vo



