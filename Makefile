help:
	dune exec _build/default/bin/main.exe -- -help

test:
	dune runtest

clean:
	dune clean
	rm -rf _coverage/ *.coverage

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

demo-42:
	dune exec _build/default/bin/main.exe -- -example 42 -debug

demo-ackermann:
	dune exec _build/default/bin/main.exe -- -example ackermann -debug

demo-length:
	dune exec _build/default/bin/main.exe -- -example length -debug

demo-append:
	dune exec _build/default/bin/main.exe -- -example append -debug

demo-loop:
	dune exec _build/default/bin/main.exe -- -example loop -debug

demo-gauss:
	dune exec _build/default/bin/main.exe -- -example gauss -debug
