V=@

all: coq html

coq: Makefile.coq
	$(MAKE) -f $<

html: Makefile.coq
	$(MAKE) -f $< $@

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

clean:
	$Vif [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	$Vfind . -name *~    -print -delete
	$Vfind . -name *.aux -print -delete
	$V$(RM) Makefile.coq*
