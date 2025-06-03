all : intro_slides.pdf FHG_paper.pdf FHG_slides.pdf

PSFILES=bezier_example.ps bezier_example2.ps cells_spiral.ps \
  collision.ps collision2.ps empty_spiral.ps polygon.ps repair2.ps \
  repair.ps smooth_spiral.ps smooth_spiral2.ps spiral_bline.ps spiral_safe2.ps\
  partial_spiral.ps partial_spiral2.ps smooth_spiral_bare.ps cells_spiral2.ps\
  spiral_safe3.ps bezier_example3.ps small_bline.ps small_curve.ps\
  sorting_input.ps safe_straight_path.ps broken_safe_path.ps smooth_connect.ps

PDFFILES= $(PSFILES:.ps=.pdf)

intro_slides.pdf : intro_slides.tex $(PDFFILES)
	pdflatex intro_slides.tex

FHG_paper.pdf : FHG_paper.tex FHG_paper.bib $(PDFFILES) illustration.png
	pdflatex FHG_paper.tex; bibtex FHG_paper; pdflatex FHG_paper.tex; \
        pdflatex FHG_paper.tex

FHG_slides.pdf : FHG_slides.tex $(PDFFILES)
	PDFLATEX FHG_slides.tex; pdflatex FHG_slides.tex

$(PDFFILES): %.pdf: %.ps
	ps2pdf -sPAPERSIZE=a4 $<

clean:
	rm -f $(PDFFILES) FHG_paper.pdf intro_slides.pdf FHG_slides.pdf
