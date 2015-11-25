.PHONY: dep-only clean

dep-only: escher_components.ml escher_core.ml escher_types.ml escher_synth.ml pie.ml
	ocamlfind ocamlopt -package batteries -w a -c escher_types.ml escher_core.ml escher_components.ml escher_synth.ml
	ocamlfind ocamlopt -package batteries -w a -c pie.ml
	ocamlfind ocamlopt -package batteries -w a -c postGen.ml
	ocamlfind ocamlopt -package qcheck -package batteries -w a -c testGen.ml
	ocamlfind ocamlc -package batteries -w a -g -c escher_types.ml escher_core.ml escher_components.ml escher_synth.ml
	ocamlfind ocamlc -package batteries -w a -g -c pie.ml
	ocamlfind ocamlc -package batteries -w a -g -c postGen.ml
	ocamlfind ocamlc -package qcheck -package batteries -w a -g -c testGen.ml

clean:
	rm -f *.cm* *.o

cleaner: clean
	rm -f *.mcf.*our *.mcf.tml *.e
