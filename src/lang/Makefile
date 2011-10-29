
lang_types.cmo: lang_types.ml
	ocamlc -c lang_types.ml

explain_conflicts:
	@rm -f lang_parser.conflicts
	menhir --explain lang_parser.mly
	@less lang_parser.conflicts

DISTFILES = $(wildcard *.ml*) Makefile
top_srcdir=../..
include $(top_srcdir)/Makefile.rules
