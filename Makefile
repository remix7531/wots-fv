CC      ?= gcc
AR      ?= ar
NPROC   := $(shell nproc)

ifeq ($(CC),ccomp)
  CFLAGS = -std=c99 -Wall -O2 -Isrc -Wp,-w
else
  CFLAGS = -std=c99 -Wall -Wextra -Wpedantic -Werror -O2 -Isrc
endif

# xmss-reference (static lib + headers) comes from the Nix devshell.
# XMSSREF_PREFIX is exported by flake.nix's shellHook.
XMSSREF_CFLAGS  ?= -I$(XMSSREF_PREFIX)/include
XMSSREF_LDFLAGS ?= -L$(XMSSREF_PREFIX)/lib -lxmssref -lcrypto

# Number of random test vectors per `make test`.  Override with `make test N=64`.
N ?= 512

# All build artifacts land here.  Source tree stays clean.
BUILD = build

LIB      = $(BUILD)/libwots.a
LIB_SRCS = src/wots.c src/sha256.c
LIB_OBJS = $(patsubst src/%.c,$(BUILD)/src/%.o,$(LIB_SRCS))
LIB_HDRS = src/wots.h src/sha256.h

MAIN        = $(BUILD)/test/main
MAIN_OCAML  = $(BUILD)/test/main_ocaml
GEN         = $(BUILD)/test/gen_vectors

# --- Rocq-extracted library (Rocq → OCaml → C-linkable static lib). ---
# libwots_ocaml.a drops in for libwots.a: same ABI, same test harness.
# The OCaml runtime is embedded via ocamlopt -output-complete-obj, so
# consumers need no OCaml dependency at link time.
OCAML_DIR     = ocaml
OCAML_BUILD   = $(BUILD)/ocaml
OCAML_LIB     = $(BUILD)/libwots_ocaml.a
OCAML_EXTRACT = $(OCAML_BUILD)/wots_extracted.ml
OCAML_BLOB    = $(OCAML_BUILD)/ocaml_blob.o
OCAML_WRAP    = $(OCAML_BUILD)/wrap.o
OCAMLFIND    ?= ocamlfind
OCAMLOPT      = $(OCAMLFIND) ocamlopt
OCAML_PKGS    = digestif.c
OCAML_INCDIR := $(shell $(OCAMLFIND) ocamlc -where)
# digestif ships its main package and the [.c] subpackage with overlapping
# .cmi files; tell findlib to ignore the dup in the parent dir.
OCAMLFIND_IGNORE_DUPS_IN := $(shell $(OCAMLFIND) query digestif 2>/dev/null)
export OCAMLFIND_IGNORE_DUPS_IN

# Vectors live in $(BUILD)/vectors-$(N).bin.  Caching by filename means
#   - `make test N=64` after `make test N=32` reuses the 32 file and
#     creates a fresh 64 file;
#   - re-running `make test` with the same N reuses the file, so a
#     failing run is reproducible via `./$(MAIN) < $(VECTORS)`;
#   - `make retest` forces a new random draw at the current N.
VECTORS = $(BUILD)/vectors-$(N).bin

# Bright cyan section banner; bright blue success banner.
BANNER  = printf '\n\033[1;36m══ %s ══\033[0m\n'
SUCCESS = printf '\033[1;34m✓ %s\033[0m\n'

all: banner-lib lib banner-test test \
     banner-ocaml-lib ocaml-lib banner-test-ocaml test-ocaml \
     banner-clight clight banner-proof proof

banner-lib:        ; @$(BANNER) "C library"
banner-test:       ; @$(BANNER) "C tests"
banner-ocaml-lib:  ; @$(BANNER) "OCaml-extracted library"
banner-test-ocaml: ; @$(BANNER) "OCaml-extracted tests"
banner-clight:     ; @$(BANNER) "clightgen (C -> Clight AST)"
banner-proof:      ; @$(BANNER) "Rocq verification"

lib: $(LIB)

ocaml-lib: $(OCAML_LIB)

test: $(VECTORS) $(MAIN)
	./$(MAIN) < $(VECTORS)

test-ocaml: $(VECTORS) $(MAIN_OCAML)
	./$(MAIN_OCAML) < $(VECTORS)

retest:
	@rm -f $(VECTORS)
	@$(MAKE) --no-print-directory test N=$(N)

clight: proof/clight/wots.v proof/clight/sha256.v

proof: Makefile.coq proof/clight/wots.v proof/clight/sha256.v
	@$(MAKE) -j $(NPROC) --no-print-directory -f Makefile.coq
	@$(SUCCESS) "All Verifications Succeeded"

# --- Build rules ---

$(BUILD)/src/%.o: src/%.c $(LIB_HDRS)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) -c $< -o $@

$(LIB): $(LIB_OBJS)
	@mkdir -p $(@D)
	$(AR) rcs $@ $^

$(MAIN): test/main.c $(LIB) $(LIB_HDRS)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) -o $@ test/main.c $(LIB)

$(GEN): test/gen_vectors.c
	@mkdir -p $(@D)
	$(CC) -std=c99 -Wall -O2 $(XMSSREF_CFLAGS) -o $@ test/gen_vectors.c $(XMSSREF_LDFLAGS)

$(BUILD)/vectors-%.bin: $(GEN)
	@mkdir -p $(@D)
	./$(GEN) $* > $@

# --- Rocq-extracted library. ---
# Pipeline:
#   1. `rocq compile Extract.v`  →  ocaml/wots_extracted.ml(i)
#   2. ocamlopt -output-complete-obj packs all OCaml sources plus the
#      OCaml runtime into one .o that C can link without any OCaml
#      dependency at use-time.
#   3. wrap.c compiles to a small C bridge calling into that blob.
#   4. ar rcs the two .o into libwots_ocaml.a.

# Project args (-Q ..., -arg ...) shared by every direct rocq compile call.
ROCQ_ARGS = $(shell grep -E '^-[A-Z]' _RocqProject | tr '\n' ' ')

# Build the pure model directly with rocq compile -- no Makefile.coq, no
# clightgen, so ocaml-lib stands alone with only Stdlib + Rocq as deps.
proof/model/notation.vo: proof/model/notation.v
	@rocq compile $(ROCQ_ARGS) $<

proof/model/wots.vo: proof/model/wots.v proof/model/notation.vo
	@rocq compile $(ROCQ_ARGS) $<

$(OCAML_EXTRACT): proof/model/wots.vo proof/model/extract.v
	@mkdir -p $(@D)
	@rocq compile $(ROCQ_ARGS) proof/model/extract.v

# Stage OCaml sources into build/ocaml/ alongside the extracted module so
# ocamlopt's .cmi/.cmx/.o intermediates land in build/ and not the tree.
$(OCAML_BLOB): $(OCAML_EXTRACT) \
               $(OCAML_DIR)/sha256_ext.ml \
               $(OCAML_DIR)/wots.mli $(OCAML_DIR)/wots.ml \
               $(OCAML_DIR)/glue.ml
	@mkdir -p $(@D)
	@cp $(OCAML_DIR)/sha256_ext.ml \
	    $(OCAML_DIR)/wots.mli $(OCAML_DIR)/wots.ml \
	    $(OCAML_DIR)/glue.ml $(OCAML_BUILD)/
	cd $(OCAML_BUILD) && $(OCAMLOPT) -package $(OCAML_PKGS) -linkpkg \
	    -output-complete-obj -o $(notdir $@) \
	    sha256_ext.ml wots_extracted.mli wots_extracted.ml \
	    wots.mli wots.ml glue.ml

$(OCAML_WRAP): $(OCAML_DIR)/wrap.c $(LIB_HDRS)
	@mkdir -p $(@D)
	$(CC) -std=c99 -Wall -O2 -I$(OCAML_INCDIR) -Isrc -c $< -o $@

$(OCAML_LIB): $(OCAML_BLOB) $(OCAML_WRAP) $(BUILD)/src/sha256.o
	@mkdir -p $(@D)
	$(AR) rcs $@ $^

# Same test harness, linked against libwots_ocaml.a instead of libwots.a.
$(MAIN_OCAML): test/main.c $(OCAML_LIB) $(LIB_HDRS)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) -o $@ test/main.c $(OCAML_LIB) -lm -ldl -lpthread

# --- VST source generation (kept in proof/ so _RocqProject finds it) ---

proof/clight/wots.v: src/wots.c src/wots.h src/sha256.h
	@mkdir -p $(@D)
	clightgen -normalize -Isrc -Wp,-w -o $@ $<

proof/clight/sha256.v: src/sha256.c src/sha256.h
	@mkdir -p $(@D)
	clightgen -normalize -Isrc -Wp,-w -o $@ $<

Makefile.coq: _RocqProject
	@rocq makefile -f _RocqProject -o Makefile.coq

clean:
	@if [ -e Makefile.coq ]; then $(MAKE) --no-print-directory -f Makefile.coq cleanall 2>/dev/null; fi
	@rm -rf $(BUILD)
	@rm -f Makefile.coq Makefile.coq.conf proof/clight/wots.v proof/clight/sha256.v

.PHONY: all lib ocaml-lib test test-ocaml retest clight proof clean \
        banner-lib banner-test banner-ocaml-lib banner-test-ocaml \
        banner-clight banner-proof
