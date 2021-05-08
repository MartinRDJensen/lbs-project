.PHONY: clean all

all: out/main

clean:
	rm -f Test.fst.checked.lax
	rm -rf out dist

dist/Test.c: Test.fst
	krml -tmpdir dist -skip-compilation Test.fst

out/main: dist/Test.c
	mkdir -p out
	gcc -I"$(KREMLIN_HOME)/include" -I"$(KREMLIN_HOME)/kremlib/dist/minimal" -Idist main.c dist/Test.c -o out/main
