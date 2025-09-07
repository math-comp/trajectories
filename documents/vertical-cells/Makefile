all : main.pdf

SVGFILES= one_closed_cell.svg initial_state.svg third_case.svg \
  main_program_steps.svg sweeping_steps.svg sides_4th_degenerate.svg\
  simple_case1.svg simple_case2.svg simple_case3.svg bad_case1.svg \
  event_order.svg

PSFILES= cells_spiral3.ps empty_spiral.ps partial_spiral2.ps partial_spiral.ps

PDF2= $(PSFILES:.ps=.pdf)

PDFFILES= $(SVGFILES:.svg=.pdf)

main.pdf : main.tex $(PDFFILES)
	pdflatex main.tex && bibtex main && pdflatex main.tex && \
        pdflatex main.tex

slides_itp25.pdf : slides_itp25.tex $(PDFFILES) $(PDF2)
	pdflatex slides_itp25.tex

$(PDFFILES): %.pdf: %.svg
	inkscape --export-type=pdf $<

$(PDF2): %.pdf: %.ps
	ps2pdf -sPAPERSIZE=a4 $<

clean :
	rm -f $(PDFFILES) main.pdf
