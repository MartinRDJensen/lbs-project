.PHONY: clean all

IMPL_SRCS=Test.fst
SPEC_SRCS=$(IMPL_SRCS) fstar/Spec.NeedSchr.fst

OCAML_SRCS=dist/spec/Test.ml dist/spec/Spec_NeedSchr.ml
GENC_SRCS=dist/impl/Test.c
C_SRCS=$(GENC_SRCS) main.c

all: $(OCAML_SRCS) out/main

clean:
	rm -rf dist

dist:
	mkdir dist

$(OCAML_SRCS): $(SPEC_SRCS) dist
	fstar $(SPEC_SRCS) --codegen OCaml --odir dist/spec --include $(KREMLIN_HOME)/kremlib

dist/impl/out.krml: $(IMPL_SRCS) dist
	fstar $(IMPL_SRCS) --codegen Kremlin --odir dist/impl --include $(KREMLIN_HOME)/kremlib

$(GENC_SRCS): dist/impl/out.krml
	krml -tmpdir dist/impl -skip-compilation dist/impl/out.krml

out/main: $(C_SRCS)
	gcc -I"$(KREMLIN_HOME)/include" -I"$(KREMLIN_HOME)/kremlib/dist/minimal" $(C_SRCS) -o dist/main $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a
