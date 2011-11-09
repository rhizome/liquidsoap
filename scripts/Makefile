
SUBDIRS = tests
DISTFILES = $(wildcard *.in) Makefile ask-liquidsoap.rb ask-liquidsoap.pl \
	    $(wildcard *.liq) extract-replaygain liquidtts

check:
	../src/liquidsoap --errors-as-warnings --no-pervasives pervasives.liq

top_srcdir = ..
include $(top_srcdir)/Makefile.rules
