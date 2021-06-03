.PHONY: clean all

FSTAR_HOME ?= $(HOME)/everest/FStar
KREMLIN_HOME ?= $(HOME)/everest/kremlin
HACL_STAR ?= $(HOME)/everest/hacl-star

FSTAR ?= $(FSTAR_HOME)/bin/fstar.exe
KRML ?= $(KREMLIN_HOME)/krml

SPEC_SRCS=fstar/Spec.NeedSchr.fst
IMPL_SRCS=fstar/Impl.NeedSchr.fst

OCAML_SRCS=dist/spec/Spec_NeedSchr.ml
GENC_SRCS=dist/impl/Impl_NeedSchr.c
C_SRCS=$(GENC_SRCS) main.c

INCLUDE_DIRS=-I"$(KREMLIN_HOME)/include"
INCLUDE_DIRS+= -I"$(KREMLIN_HOME)/kremlib/dist/minimal"
INCLUDE_DIRS+= -I$(HACL_STAR)/dist/gcc-compatible

LIBRARIES=$(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a
LIBRARIES+= $(HACL_STAR)/dist/gcc-compatible/libevercrypt.a
LIBRARIES+= -I.

FSTAR_INCLUDES=--include $(KREMLIN_HOME)/kremlib
FSTAR_INCLUDES+= --include fstar
# FSTAR_INCLUDES+= --include $(HACL_STAR)/specs/lemmas
# FSTAR_INCLUDES+= --include $(HACL_STAR)/code/bignum
# FSTAR_INCLUDES+= --include $(HACL_STAR)/code/meta
# FSTAR_INCLUDES+= --include $(HACL_STAR)/code/poly1305
# FSTAR_INCLUDES+= --include $(HACL_STAR)/code/curve25519
# FSTAR_INCLUDES+= --include $(HACL_STAR)/code/salsa20
# FSTAR_INCLUDES+= --include $(HACL_STAR)/code/nacl-box
# FSTAR_INCLUDES+= --include $(HACL_STAR)/lib

all: $(OCAML_SRCS) dist/impl/main

clean:
	rm -rf dist

dist:
	mkdir dist

$(OCAML_SRCS): $(SPEC_SRCS) dist
	$(FSTAR) $(SPEC_SRCS) --codegen OCaml --odir dist/spec

dist/impl/out.krml: $(IMPL_SRCS) $(SPEC_SRCS) dist
	$(FSTAR) $(IMPL_SRCS) --codegen Kremlin --odir dist/impl $(FSTAR_INCLUDES) --z3rlimit 10

$(GENC_SRCS): dist/impl/out.krml
	$(KRML) -tmpdir dist/impl -skip-compilation -skip-makefiles dist/impl/out.krml -add-include "<header.h>"

dist/impl/main: $(C_SRCS) header.h
	gcc $(INCLUDE_DIRS) $(C_SRCS) -o dist/impl/main $(LIBRARIES) -O3
