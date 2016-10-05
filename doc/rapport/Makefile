
TARGET := report
DVI    := pdflatex
BIB    := biber
IDX    := makeindex
PDF    := ps2pdf
PS     := dvips
GLOS   := makeglossaries
OBJDIR := out

LATEXFLAGS := -output-directory $(OBJDIR) -interaction=batchmode

MAIN := main

all: dvi copy

dvi:
	@mkdir -p $(OBJDIR)
	@echo -e "First compilation"
	@$(DVI) $(LATEXFLAGS) $(MAIN).tex
	@echo -e "Generating index"
	@$(IDX) $(MAIN).idx
	@echo -e "Generating bibliography"
	@$(BIB) --output-directory $(OBJDIR) $(MAIN)
	@echo -e "Generating glossary"
	@$(GLOS) -q -d $(OBJDIR) $(MAIN)
	@echo -e "Second compilation"
	@$(DVI) $(LATEXFLAGS) $(MAIN).tex
	@$(DVI) $(LATEXFLAGS) $(MAIN).tex

ps: dvi
	@$(PS) $(MAIN).dvi

pdf: ps
	@$(PS) $(MAIN).ps

copy:
	@cp $(OBJDIR)/$(MAIN).pdf $(TARGET).pdf

latexmk:
	latexmk --output-directory=./$(OBJDIR) -pvc main.tex
	cp main.pdf $(TARGET).pdf

clean:
	@echo -e "Cleaning"
	@rm -f $(MAIN).{ps,pdf,log,aux,out,dvi,bbl,blg}
