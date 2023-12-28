# Makefile for compiling lisa.tex using latexmk

# Default target
all: lisa.pdf

lisa.pdf: lisa.tex kernel.tex  lisa.tex  macro.tex  prooflib.tex  quickguide.tex  shortcuts.tex  theory.tex  theorytopics.tex
	latexmk lisa.tex

# Clean target
clean:
	latexmk -c lisa.tex
