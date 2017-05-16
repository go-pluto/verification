.PHONY: all build clean

all: clean build clean

build:
	pdflatex bluepaper.tex
	biber bluepaper
	pdflatex bluepaper.tex
	pdflatex bluepaper.tex

clean:
	rm -f *.aux *.log *.blg *.bbl *.bcf *.out *.run.xml *.toc
