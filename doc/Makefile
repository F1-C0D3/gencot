
SEC_DESIGN = names modular files comments const preprocessor ccode types operations decls fundefs parmod isabelle
SRC_DESIGN = $(foreach sec,$(SEC_DESIGN),design-$(sec).tex)
SEC_IMPL = origin itemprops parmod comments preprocessor ccode ctypinfo operations isabelle ccomps ocomps all
SRC_IMPL = $(foreach sec,$(SEC_IMPL),impl-$(sec).tex)
SEC_APP = items parmod itemprops transauto transtype transfunction 
SRC_APP = $(foreach sec,$(SEC_APP),app-$(sec).tex)

SEC_VERIF = sem type prop
SRC_VERIF = $(foreach sec,$(SEC_VERIF),verif/Section_$(sec).thy)
TEX_VERIF = $(foreach sec,$(SEC_VERIF),Section_$(sec).tex)

gencot-devel.pdf: gencot-devel.tex $(SRC_DESIGN) $(SRC_IMPL) $(SRC_APP) $(SRC_VERIF)
	(cd verif; make)
	cp verif/output/document/Section*.tex .
	cp verif/output/document/session.tex .
	cp verif/output/document/*.sty .
	pdflatex gencot-devel.tex
	pdflatex gencot-devel.tex

view-verif:
	isabelle jedit -d verif -l HOL verif/Section_prop.thy

clean-git: 
	rm -f $(TEX_VERIF) session.tex *.sty 
	rm -rf verif/output

clean: clean-git
	rm -f *.aux *.log *.out gencot-devel.pdf
	rm -f verif/*.thy~
