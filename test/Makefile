all: io_roundtrip

io_roundtrip: io_roundtrip.native
	./$<

%.native: %.ml
	ocamlbuild $@

io_roundtrip.ml: io_roundtrip.vo

%.vo: Makefile.coq %.v
	$(MAKE) -f $< $@

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

.PHONY: all io_roundtrip

clean:
	ocamlbuild -clean
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	$(RM) Makefile.coq* *.ml*
