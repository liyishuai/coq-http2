all: io_roundtrip

io_roundtrip:
	coqc -Q ../src HTTP2 io_roundtrip.v
	ocamlbuild io_roundtrip.native
	./io_roundtrip.native

.PHONY: all io_roundtrip
