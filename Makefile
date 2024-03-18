
all: proposal.pdf
proposal.pdf: proposal.tex main.bib util.tex
	pdflatex proposal.tex
	bibtex proposal
	pdflatex proposal.tex
	pdflatex proposal.tex

clean:
	-rm -f proposal.pdf proposal.aux proposal.log
