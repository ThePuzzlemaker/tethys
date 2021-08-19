all:
	latexmk -pdf paper.tex
clean:
	latexmk -c
	rm -f paper.dvi
	rm -f paper.bbl
	rm -f paper.run.xml
