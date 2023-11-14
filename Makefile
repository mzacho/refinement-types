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
