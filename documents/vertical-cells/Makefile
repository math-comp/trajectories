main.pdf : main.tex one_closed_cell.pdf initial_state.pdf third_case.pdf
	pdflatex main.tex && bibtex main && pdflatex main.tex && \
        pdflatex main.tex

one_closed_cell.pdf : one_closed_cell.svg
	inkscape --export-type=pdf one_closed_cell.svg

initial_state.pdf : initial_state.svg
	inkscape --export-type=pdf initial_state.svg

third_case.pdf : third_case.svg
	inkscape --export-type=pdf third_case.svg
