.PHONY: dep-only clean

dep-only: escher_components.ml escher_core.ml escher_types.ml escher_synth.ml specInfer.ml
	ocamlfind ocamlopt -package batteries -w a -c escher_types.ml escher_core.ml escher_components.ml escher_synth.ml
	ocamlfind ocamlopt -package batteries -w a -c specInfer.ml
	ocamlfind ocamlopt -package batteries -w a -c specify.ml
	ocamlfind ocamlopt -package qcheck -package batteries -w a -c testGen.ml
	ocamlfind ocamlc -package batteries -w a -g -c escher_types.ml escher_core.ml escher_components.ml escher_synth.ml
	ocamlfind ocamlc -package batteries -w a -g -c specInfer.ml
	ocamlfind ocamlc -package batteries -w a -g -c specify.ml
	ocamlfind ocamlc -package qcheck -package batteries -w a -g -c testGen.ml

clean:
	rm -f *.cm* *.o
	rm -f *.mcf.*our *.e

cleaner: clean
	rm -f *.mcf.tml
