MAIN := main
RULES := rules
OLD := old
DIFF := diff
LTEX := ltex

LATEX_FLAGS := -jobname=$(MAIN) -shell-escape
LATEXRUN := latexrun -Wall --latex-cmd lualatex --latex-args "$(LATEX_FLAGS)"
LATEXDIFF := latexdiff
BIBTEX := bibtex

OTT = ott
OTTFILES = $(MAIN).ott
OTT_FLAGS = -tex_wrap false -tex_show_meta false -merge true $(OTTFILES)

MAKEDEPS  := Makefile
LATEXDEPS := main.bib
MOREDEPS := listproc.sty ottalt.sty
GENERATED := $(RULES).tex $(MAIN).tex

all: $(MAIN).pdf

$(RULES).tex: $(OTTFILES)
	$(OTT) -o $(RULES).tex $(OTT_FLAGS)

$(MAIN).tex: $(RULES).tex $(MAIN).mng
	$(OTT) -tex_filter $(MAIN).mng $(MAIN).tex $(OTT_FLAGS)

.PHONY: FORCE
$(MAIN).pdf: $(MAIN).tex $(LATEXDEPS)
	$(LATEXRUN) $(MAIN).tex

$(DIFF).pdf: $(RULES).tex $(MAIN).mng
	$(LATEXDIFF) $(OLD).mng $(MAIN).mng > $(DIFF).mng
	$(OTT) -tex_filter $(DIFF).mng $(DIFF).tex $(OTT_FLAGS)
	$(LATEXRUN) -o $(DIFF).pdf $(DIFF).tex
	rm $(DIFF).mng $(DIFF).tex

.PHONY: zip
zip: $(MAIN).pdf
	cp latex.out/$(MAIN).bbl $(MAIN).bbl
	zip -o submit.zip $(MAIN).bbl $(LATEXDEPS) $(MOREDEPS) $(GENERATED)
	rm $(MAIN).bbl

# N.B. https://github.com/ionathanch/ltex-ls-plus fixes issue with `hiddenFalsePositives`. To use custom LTeX+:
# 1. Compile `ltex-ls-plus` with `mvn -B -Dmaven.test.skip=true package`
# 2. Copy output files in `ltex-ls-plus/target/ltex-ls-plus-<VERSION>.tar.gz/ltex-ls-plus-<VERSION>` to `~/.local/share/ltex`
# 3. Create simlink with `ln -sf ~/.local/share/ltex/bin/ltex-cli-plus ~/.local/bin/ltex`
check: $(MAIN).tex
	ltex --client-configuration=$(LTEX).json $(MAIN).tex > latex.out/$(LTEX).log \
	&& echo "No LTeX errors found." || echo "LTeX errors written to latex.out/$(LTEX).log."

.PHONY: count
count:
	cd ../CBPV && \
	tokei -f *.lean

.PHONY: clean
clean:
	$(LATEXRUN) --clean-all
	rm -f $(GENERATED)
