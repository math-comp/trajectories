all: Makefile.coq
	make -f Makefile.coq

Makefile.coq:
	coq_makefile *.v -o Makefile.coq

run:
	python3 -m http.server

clean:
	make -f Makefile.coq clean