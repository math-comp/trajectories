all : FHG_paper.pdf

PSFILES=empty_spiral.ps\
smooth_spiral_bare.ps\
cells_spiral2.ps\
spiral_bline.ps\
sorting_input.ps\
safe_straight_path.ps\
broken_safe_path.ps\
smooth_connect.ps\
bezier_example3.ps\
small_bline.ps\
small_curve.ps\
repair.ps

PDFFILES= $(PSFILES:.ps=.pdf)

FHG_paper.pdf : FHG_paper.tex FHG_paper.bib $(PDFFILES) illustration.png
	pdflatex FHG_paper.tex && bibtex FHG_paper && pdflatex FHG_paper && \
	pdflatex FHG_paper.tex

$(PDFFILES): %.pdf: %.ps
	ps2pdf -sPAPERSIZE=a4 $<

clean :
	rm -f $(PDFFILES) FHG_paper.pdf FHG_paper.aux
