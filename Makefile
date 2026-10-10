.PHONY: clean

coqmakefile: _CoqProject
	rocq makefile -f _CoqProject -o CoqMakefile

build:
	make -f CoqMakefile

all: coqmakefile build

clean:
	rm *.aux *.d CoqMakefile CoqMakefile.conf *.glob *.vok *.vos