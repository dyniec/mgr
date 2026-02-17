.PHONY: clean

SRC := mgr
AGDA:=agda
build_latex:=_build/latex
src_lagda_tex:=$(build_latex)/src_lagda_tex
src_tex:=$(build_latex)/src_tex
lagda_md_files := $(shell find $(SRC) -name '*.lagda.md')
transpiled_files := $(patsubst $(SRC)/%.md,$(src_lagda_tex)/%.tex,$(lagda_md_files))
latex_files := $(patsubst $(SRC)/%.lagda.md,$(src_tex)/%.tex,$(lagda_md_files)) 
agda_sty := $(src_tex)/agda.sty

all_lagda_tex: $(transpiled_files)
all_latex: $(latex_files)

doc.pdf: doc.tex $(LATEX_DEPS) all_lagda_tex all_latex
	latexmk $(LATEXMK_OPTS) doc.tex
	cp $(build_latex)/doc.pdf doc.pdf

LATEXMK_OPTS := -outdir=$(build_latex)  -pdf -xelatex --quiet

LATEX_DEPS := $(latex_files) $(agda_sty) references.bib $(EXTRA_DIRS)

$(src_lagda_tex)/%.lagda.tex : $(SRC)/%.lagda.md pandoc/code-block.lua
	@mkdir -p '$(@D)'
	pandoc $< --indented-code-classes=default \
		--filter=pandoc-latex-environment \
		--lua-filter=pandoc/code-block.lua \
		-o $@
	sed 's/^\\textbackslash /\\/' $@ > $@.tmp
	mv $@.tmp $@

AGDA_LATEX_OPTS:=--latex --latex-dir=$(src_tex) --include-path=$(src_lagda_tex) --only-scope-checking

$(src_tex)/%.tex : $(src_lagda_tex)/%.lagda.tex 
	$(AGDA) $(AGDA_LATEX_OPTS) $<

clean:
	$(RM) -rf _build doc.pdf doc.fdb_latexmk doc.aux doc.fls doc.log doc.out doc.toc


