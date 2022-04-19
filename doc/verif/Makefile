SEC_VERIF = sem type prop
SRC_VERIF = $(foreach sec,$(SEC_VERIF),Section_$(sec).thy)
TEX_VERIF = $(foreach sec,$(SEC_VERIF),output/document/Section_$(sec).tex)

$(TEX_VERIF): $(SRC_VERIF)
	isabelle build -v -c -d . Chapter_verif

edit:
	isabelle jedit -d . -l HOL Section_prop.thy
