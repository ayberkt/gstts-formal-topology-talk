all: latex/slides.pdf

latex/slides.pdf: latex/slides.tex
	cd latex && tectonic slides.tex

latex/slides.tex: slides.lagda
	agda --latex slides.lagda
