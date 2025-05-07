main:
	lualatex --shell-escape tdparse.tex

all:
	make clean;
	\rm -f tdparse.bbl;
	make main; 
	bibtex tdparse.tex;
	make main; 
	bibtex tdparse.tex;
	make main;

clean:
	\rm -f tdparse.log tdparse.out tdparse.toc tdparse.aux 
