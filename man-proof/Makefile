# Location of the Cogent installation directory (with subdirectories cogent and isabelle)
COGENTROOT=$(COGENT_HOME)

ifdef ISABELLE_HOME
# Alternative location of Isabelle installation directory
ISABELLEROOT=$(ISABELLE_HOME)
else
# Use Isabelle in Cogent installation 
ISABELLEROOT=$(COGENTROOT)/isabelle
endif

ISABELLE=$(ISABELLEROOT)/bin/isabelle

all: doc

edit: 
	$(ISABELLE) jedit -l HOL Chapter_intro.thy

doc:
	$(ISABELLE) build -v -b -d . man-proof
	if [ -e output/document.pdf ]; then cp output/document.pdf man-proof.pdf; fi

clean:
	-rm -f *~
	-rm -r output


