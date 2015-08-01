.PHONY: dep-only clean

dep-only: escher_components.ml escher_core.ml escher_types.ml escher_synth.ml specInfer.ml
	ocamlfind ocamlopt -package batteries -w a -c escher_types.ml escher_core.ml escher_components.ml escher_synth.ml
	ocamlfind ocamlopt -package batteries -w a -c specInfer.ml
	ocamlfind ocamlopt -package batteries -w a -c specify.ml
	ocamlfind ocamlc -package batteries -w a -g -c escher_types.ml escher_core.ml escher_components.ml escher_synth.ml
	ocamlfind ocamlc -package batteries -w a -g -c specInfer.ml
	ocamlfind ocamlc -package batteries -w a -g -c specify.ml

clean:
	rm -f *.cm* *.o
	rm -f *.mcf.*our *.e

cleaner: clean
	rm -f *.mcf.tml

dist-clean: cleaner
	rm -f *.ml simplify abduce chkSAT chkVALID verify var_replace smt2ml makefile infer-test*
