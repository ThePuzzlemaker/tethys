all:
	latexmk -pdf paper.tex
clean:
	latexmk -c
	rm paper.dvi
