all: saml_dssi.ml

lang_types.cmo: lang_types.ml
	ocamlc -c lang_types.ml

explain_conflicts:
	@rm -f lang_parser.conflicts
	menhir --explain lang_parser.mly
	@less lang_parser.conflicts

saml_dssi.ml: saml_dssi.c
	echo 'let c = "' > $@
	cat $^ | sed 's/\\n/\\\\n/g' | sed 's/"/\\"/g' >> $@
	echo '"' >> $@

DISTFILES = $(wildcard *.ml*) Makefile
top_srcdir=../..
include $(top_srcdir)/Makefile.rules
