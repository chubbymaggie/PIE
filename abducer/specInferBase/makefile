.PHONY: dep-only clean

dep-only: escher_components.ml escher_core.ml escher_types.ml escher_synth.ml specInfer.ml
	ocamlopt -w a -c escher_types.ml escher_core.ml escher_components.ml escher_synth.ml
	ocamlfind ocamlopt -package batteries -w a -c specInfer.ml
	ocamlc -w a -c escher_types.ml escher_core.ml escher_components.ml escher_synth.ml
	ocamlfind ocamlc -package batteries -w a -c specInfer.ml

clean:
	rm -f *.cm* *.o
	rm -f *.mcf.* *.e

dist-clean: clean
	rm -f *.ml simplify abduce chkSAT chkVALID verify var_replace smt2ml makefile infer-test*
