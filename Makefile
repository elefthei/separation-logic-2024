COQMAKEFILE=CoqMakefile

all: theories proposal.pdf

theories: $(COQMAKEFILE)
	$(MAKE) -f $^

$(COQMAKEFILE) : _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o $(COQMAKEFILE)

install: $(COQMAKEFILE)
	$(MAKE) -f $^ install

uninstall: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) uninstall

proposal.pdf: proposal.tex main.bib util.tex
	pdflatex proposal.tex
	bibtex proposal
	pdflatex proposal.tex
	pdflatex proposal.tex

.PHONY: clean
clean:
	test ! -f $(COQMAKEFILE) || ( $(MAKE) -f $(COQMAKEFILE) clean && rm $(COQMAKEFILE) )
	-rm -f proposal.pdf proposal.aux proposal.log
