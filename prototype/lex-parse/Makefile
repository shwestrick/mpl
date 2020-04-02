MLTON=mlton
MLLEX=mllex
MLYACC=mlyacc
SED=sed

all: proto.lex.sml proto.grm.sml main

%.lex.sml: %.lex
	rm -f $<.*
	$(MLLEX) $<
	mv $<.sml $<.sml.in
	$(SED) -e 's/val s = List.map f (List.rev (tl (List.rev s)))/val s = Pervasive.List.map f (Pervasive.List.rev (tl (Pervasive.List.rev s)))/' $<.sml.in > $<.sml
	mv $<.sml $<.sml.in
	$(SED) -e 's/in Vector.fromList(List.map g/in Vector.fromList(Pervasive.List.map g/' $<.sml.in > $<.sml
	rm -f $<.sml.in
	chmod -w $<.*

%.grm.sig %.grm.sml: %.grm
	rm -f $<.*
	$(MLYACC) $<
	mv $<.sml $<.sml.in
	$(SED) -e 's/in f 0 handle General.Subscript => ()/in f 0 handle Pervasive.General.Subscript => ()/' $<.sml.in > $<.sml
	mv $<.sml $<.sml.in
	$(SED) -e 's/in Array.fromList(List.map actionRowLookUp actionRowNumbers)/in Array.fromList(Pervasive.List.map actionRowLookUp actionRowNumbers)/' $<.sml.in > $<.sml
	rm -f $<.sml.in
	chmod -w $<.*

main: proto.lex.sml proto.grm.sml LexParse.sml sources.mlb
	$(MLTON) -output main sources.mlb

.PHONY: clean
clean:
	rm -f *.grm.desc *.grm.sig *.grm.sml *.lex.sml main
