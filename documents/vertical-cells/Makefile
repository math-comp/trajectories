all : main.pdf

SVGFILES= one_closed_cell.svg initial_state.svg third_case.svg \
  main_program_steps.svg sweeping_steps.svg sides_4th_degenerate.svg

PDFFILES= $(SVGFILES:.svg=.pdf)

main.pdf : main.tex $(PDFFILES)
	pdflatex main.tex && bibtex main && pdflatex main.tex && \
        pdflatex main.tex

$(PDFFILES): %.pdf: %.svg
	inkscape --export-type=pdf $<

clean :
	rm -f $(PDFFILES) main.pdf
