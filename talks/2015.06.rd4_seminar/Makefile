slides: slides.tex
	pdflatex slides.tex
#	dvips -t landscape slides.dvi -o slides.ps
#	ps2pdf slides.ps slides.pdf

slides.tex: slides.lhs slides.fmt
	lhs2TeX --poly slides.lhs > slides.tex
	- pdflatex slides.tex
	asy *.asy

clean:
	- rm *.pre *.vrb *.asy slides.tex slides-*.pdf slides.ps slides.dvi slides.aux slides.log slides.toc slides.ptb slides.nav slides.out slides.snm
