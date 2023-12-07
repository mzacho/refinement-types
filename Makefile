help:
	dune exec _build/default/bin/main.exe -- -help

test:
	dune runtest

clean:
	dune clean
	rm -rf _coverage/

coverage:
	make clean
	BISECT_ENABLE=yes dune build

	find . -name '*.coverage' | xargs rm -f
	dune runtest
	@echo "======================"
	bisect-ppx-report html
	bisect-ppx-report summary
	@echo "======================"
	@echo "For summary see _coverage/index.html"

# rebuild clean (without coverage instrumentation)
build:
	make clean
	dune build

demo-4:
	dune exec _build/default/bin/main.exe -- -example 4 -debug
