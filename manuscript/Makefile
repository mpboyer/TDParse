main:
	lualatex --shell-escape tdparse.tex

slides:
	lualatex --shell-escape slides.tex

all:
	make clean;
	\rm -f tdparse.bbl;
	make main;
	bibtex tdparse;
	make main;
	bibtex tdparse;
	make main;

pres:
	make clean;
	make slides;
	biber slides;
	make slides;
	make slides;

clean:
	\rm -f *.log *.out *.toc *.aux *.run.xml *.nav *.blg *.bcf *.vrb
