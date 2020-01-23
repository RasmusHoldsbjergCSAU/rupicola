# Makefile originally based off of one from coq-club, also borrowing from fiat-crypto's Makefile

COQPATH?=$(COQUTIL_FOLDER)/src:$(BEDROCK2_FOLDER)/src
export COQPATH

all: deps Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject -o Makefile.coq INSTALLDEFAULTROOT = Rupicola | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

COQUTIL_FOLDER := bedrock2/deps/coqutil
BEDROCK2_FOLDER := bedrock2/bedrock2

coqutil:
	$(MAKE) --no-print-directory -C $(COQUTIL_FOLDER) 

clean-coqutil:
	$(MAKE) --no-print-directory -C $(COQUTIL_FOLDER) clean

bedrock2: coqutil
	$(MAKE) --no-print-directory -C $(BEDROCK2_FOLDER) noex

clean-bedrock2:
	$(MAKE) --no-print-directory -C $(BEDROCK2_FOLDER) clean

deps: bedrock2

cleanall: clean clean-coqutil clean-bedrock2

vofile: Makefile.coq
	+make -f Makefile.coq $@

%.vo: deps +vofile

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony base coqutil clean-coqutil bedrock2 clean-bedrock2 deps cleanall
