# -*- Makefile -*-

# --------------------------------------------------------------------
OCAMLBUILD_JOBS  ?= 1
OCAMLBUILD_BIN   ?= ocamlbuild
OCAMLBUILD_EXTRA ?= 
OCAMLBUILD_OPTS  := -use-ocamlfind -j $(OCAMLBUILD_JOBS)

# In Emacs, use classic display to enable error jumping.
ifeq ($(shell echo $$TERM), dumb)
 OCAMLBUILD_OPTS += -classic-display
endif
ifeq ($(LINT),1)
 OCAMLBUILD_OPTS += -tag lint
endif
OCAMLBUILD_OPTS += $(OCAMLBUILD_EXTRA)

OCAMLBUILD := $(OCAMLBUILD_BIN) $(OCAMLBUILD_OPTS)

# --------------------------------------------------------------------
.PHONY: all build byte native 
.PHONY: clean 

all: build
	@true

build: native

define do-build
	rm -f "$(1)$(EXE)"
	$(OCAMLBUILD) "src/$(1)"
	if [ ! -z "$(EXE)" ]; then \
	  cp "_build/src/$(1)" "$(1)$(EXE)"; \
	fi
endef

native:
	$(call do-build,ecwhy3.native)

wrapper:
	$(call do-build,zkRun.native)

clean:
	$(OCAMLBUILD) -clean
	rm -f ecwhy3.native zkRun.native extraction.mlw InTheHead.ml

ast:
	$(call do-build,tree/ecAst.native)
