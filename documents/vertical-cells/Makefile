all : main.pdf

main.pdf : main.tex one_closed_cell.pdf initial_state.pdf third_case.pdf
	pdflatex main.tex && bibtex main && pdflatex main.tex && \
        pdflatex main.tex

SVGFILES= one_closed_cell.svg initial_state.svg third_case.svg

PDFFILES= $(SVGFILES:.svg=.pdf)

$(PDFFILES): %.pdf: %.svg
	inkscape --export-type=pdf $<

clean :
	rm -f $(PDFFILES) main.pdf
