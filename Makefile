# ============================================================================
# wots+fv build system.
#
# User-facing targets:
#   make            full build: lib + tests + ocaml lib + ocaml tests + proof
#   make test       C library + tests
#   make test-ocaml Rocq-extracted reference library + tests
#   make proof      VST proofs
#   make lint       clang-tidy + -fanalyzer + ASan/UBSan + MSan + CompCert + ctgrind (CI gate)
#   make test-ct    ctgrind: constant-time check on wotsfv_sign
#                   under gcc, clang, and CompCert
#   make clean
#
# Knobs:
#   N=512           vectors per test run (default 512)
#   CC=ccomp        build with CompCert
#   CFLAGS=...      override compiler flags
# ============================================================================

# ----- Configuration --------------------------------------------------------

CC    ?= gcc
AR    ?= ar
N     ?= 512
NPROC := $(shell nproc)

ifeq ($(CC),ccomp)
  CFLAGS = -std=c99 -Wall -O2 -Isrc -Wp,-w
else
  CFLAGS = -std=c99 -Wall -Wextra -Wpedantic -Werror -O2 -Isrc
endif

# Sanitizer flags for `make test-asan`.
ASAN_CFLAGS = -std=c99 -Wall -Wextra -Wpedantic -Werror -O1 -g \
              -fsanitize=address,undefined -fno-omit-frame-pointer \
              -fno-sanitize-recover=all -Isrc

# MSan flags for `make test-msan`.  Clang-only; needs all linked code
# instrumented, so we only run it against the pure C test path (not the
# OCaml-extracted variant which pulls in uninstrumented runtime).
MSAN_CFLAGS = -std=c99 -Wall -Wextra -Wpedantic -Werror -O1 -g \
              -fsanitize=memory -fsanitize-memory-track-origins=2 \
              -fno-omit-frame-pointer -fno-sanitize-recover=all -Isrc

# xmss-reference comes from the Nix devshell; XMSSREF_PREFIX is set in
# flake.nix's shellHook.
XMSSREF_CFLAGS  ?= -I$(XMSSREF_PREFIX)/include
XMSSREF_LDFLAGS ?= -L$(XMSSREF_PREFIX)/lib -lxmssref -lcrypto

# clang-tidy bypasses the Nix gcc-wrapper that injects glibc's include path,
# so discover the system include dirs from gcc and pass them as -isystem.
SYS_INCLUDES := $(shell echo | $(CC) -E -Wp,-v -xc - 2>&1 \
                  | sed -n 's|^ \(/.*\)|-isystem \1|p')

# ----- Artifact paths -------------------------------------------------------

BUILD = build

# C library
LIB      = $(BUILD)/libwots.a
LIB_SRCS = src/wots.c src/sha256.c src/util.c
LIB_OBJS = $(patsubst src/%.c,$(BUILD)/src/%.o,$(LIB_SRCS))
LIB_HDRS = src/wots.h src/sha256.h src/util.h

# Test binaries
MAIN       = $(BUILD)/test/main
MAIN_OCAML = $(BUILD)/test/main_ocaml
GEN        = $(BUILD)/test/gen_vectors
CTGRIND    = $(BUILD)/test/ctgrind

# valgrind ships memcheck.h via pkg-config.
VALGRIND_CFLAGS := $(shell pkg-config --cflags valgrind 2>/dev/null)

# Compiler for the ctgrind harness itself.  Defaults to $(CC) so the
# harness matches the library; test-ct-ccomp overrides it to gcc since
# CompCert cannot accept valgrind.h's client-request inline asm.
HARNESS_CC ?= $(CC)

# Vectors live in $(BUILD)/vectors-$(N).bin so different N values cache
# independently; `make retest` discards and regenerates at the current N.
VECTORS = $(BUILD)/vectors-$(N).bin

# OCaml-extracted library
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

# Project args from _RocqProject for direct `rocq compile` calls.
ROCQ_ARGS = $(shell grep -E '^-[A-Z]' _RocqProject | tr '\n' ' ')

# Cyan banner; blue success line.
BANNER  = printf '\n\033[1;36m══ %s ══\033[0m\n'
SUCCESS = printf '\033[1;34m✓ %s\033[0m\n'

# ----- Top-level targets ----------------------------------------------------

.PHONY: all lib ocaml-lib test test-ocaml retest clight proof clean \
        test-asan test-msan test-ccomp \
        test-ct test-ct-gcc test-ct-clang test-ct-ccomp \
        lint lint-tidy lint-fanalyzer \
        main-bin ct-bin

all:
	@$(BANNER) "C library";                   $(MAKE) --no-print-directory lib
	@$(BANNER) "C tests";                     $(MAKE) --no-print-directory test
	@$(BANNER) "OCaml-extracted library";     $(MAKE) --no-print-directory ocaml-lib
	@$(BANNER) "OCaml-extracted tests";       $(MAKE) --no-print-directory test-ocaml
	@$(BANNER) "clightgen (C -> Clight AST)"; $(MAKE) --no-print-directory clight
	@$(BANNER) "Rocq verification";           $(MAKE) --no-print-directory proof

lib:       $(LIB)
ocaml-lib: $(OCAML_LIB)
clight:    proof/clight/wots.v proof/clight/sha256.v

test: $(VECTORS) $(MAIN)
	./$(MAIN) < $(VECTORS)

test-ocaml: $(VECTORS) $(MAIN_OCAML)
	./$(MAIN_OCAML) < $(VECTORS)

retest:
	@rm -f $(VECTORS)
	@$(MAKE) --no-print-directory test N=$(N)

proof: Makefile.coq proof/clight/wots.v proof/clight/sha256.v
	@$(MAKE) -j $(NPROC) --no-print-directory -f Makefile.coq
	@$(SUCCESS) "All Verifications Succeeded"

# ----- Quality gates --------------------------------------------------------
# Each sub-target builds in its own BUILD=build/<config> subdir so they
# can run side-by-side without clobbering each other's objects.  No
# sub-target cleans on its own; `make clean` removes everything and
# `make lint` does a single clean upfront.

lint:
	@$(MAKE) --no-print-directory clean
	@$(MAKE) --no-print-directory lint-tidy
	@$(MAKE) --no-print-directory lint-fanalyzer
	@$(MAKE) --no-print-directory test-asan
	@$(MAKE) --no-print-directory test-msan
	@$(MAKE) --no-print-directory test-ccomp
	@$(MAKE) --no-print-directory test-ct

lint-tidy:
	@$(BANNER) "clang-tidy"
	clang-tidy $(LIB_SRCS) $(TEST_SRCS) -- -std=c99 -Isrc -Itest -D_DEFAULT_SOURCE=1 $(SYS_INCLUDES)

lint-fanalyzer:
	@$(BANNER) "gcc -fanalyzer"
	@$(MAKE) --no-print-directory main-bin BUILD=build/fanalyzer \
	    CC=gcc CFLAGS="$(CFLAGS) -fanalyzer"

test-asan:
	@$(BANNER) "C tests (ASan + UBSan)"
	@$(MAKE) --no-print-directory test BUILD=build/asan CFLAGS="$(ASAN_CFLAGS)"

test-msan:
	@$(BANNER) "C tests (MSan)"
	@$(MAKE) --no-print-directory test BUILD=build/msan CC=clang CFLAGS="$(MSAN_CFLAGS)"

test-ccomp:
	@$(BANNER) "C tests (CompCert)"
	@$(MAKE) --no-print-directory test BUILD=build/ccomp CC=ccomp

# ctgrind: run wotsfv_sign under valgrind with sk_seed marked
# uninitialized.  Any branch or memory index dependent on a secret
# byte is reported and --error-exitcode=1 fails the build.  Run
# across gcc / clang / CompCert since each can lower constant-time
# source to branchy code differently.
$(CTGRIND): test/ctgrind.c $(LIB) $(LIB_HDRS)
	@mkdir -p $(@D)
	$(HARNESS_CC) -std=c99 -Wall -Wextra -Wpedantic -Werror -O1 -g -Isrc \
	    $(VALGRIND_CFLAGS) -o $@ test/ctgrind.c $(LIB)

# Phony aliases so test-ct-X can pass a goal that the outer make won't
# pre-expand under the wrong BUILD root.
main-bin: $(MAIN)
ct-bin:   $(CTGRIND)

test-ct: test-ct-gcc test-ct-clang test-ct-ccomp

test-ct-gcc:
	@$(BANNER) "ctgrind on wotsfv_sign (gcc)"
	@$(MAKE) --no-print-directory ct-bin BUILD=build/ct-gcc CC=gcc
	valgrind -q --error-exitcode=1 --track-origins=yes \
	    --leak-check=no --errors-for-leak-kinds=none ./build/ct-gcc/test/ctgrind
	@$(SUCCESS) "wotsfv_sign: no secret-dependent branches (gcc)"

test-ct-clang:
	@$(BANNER) "ctgrind on wotsfv_sign (clang)"
	@$(MAKE) --no-print-directory ct-bin BUILD=build/ct-clang CC=clang
	valgrind -q --error-exitcode=1 --track-origins=yes \
	    --leak-check=no --errors-for-leak-kinds=none ./build/ct-clang/test/ctgrind
	@$(SUCCESS) "wotsfv_sign: no secret-dependent branches (clang)"

test-ct-ccomp:
	@$(BANNER) "ctgrind on wotsfv_sign (CompCert)"
	@$(MAKE) --no-print-directory ct-bin BUILD=build/ct-ccomp CC=ccomp HARNESS_CC=gcc
	valgrind -q --error-exitcode=1 --track-origins=yes \
	    --leak-check=no --errors-for-leak-kinds=none ./build/ct-ccomp/test/ctgrind
	@$(SUCCESS) "wotsfv_sign: no secret-dependent branches (CompCert)"

# ----- C library + tests ----------------------------------------------------

$(BUILD)/src/%.o: src/%.c $(LIB_HDRS)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) -c $< -o $@

$(LIB): $(LIB_OBJS)
	@mkdir -p $(@D)
	$(AR) rcs $@ $^

# Test harness sources.  Split across modules so each TU has one job:
#   common.c   shared helpers (rng, status)
#   sha256.c   SHA-256 KATs + NIST CAVS parser
#   wots.c     WOTS+ self-consistency + tamper + vector cross-check
#   runner.c   banner + section drivers
TEST_SRCS = test/common.c test/sha256.c test/wots.c test/runner.c
TEST_HDRS = test/common.h

# _DEFAULT_SOURCE exposes glibc's getrandom(2) / getline(3) to every
# test TU; safer than per-file #define which would race with header
# include order.
TEST_CFLAGS = $(CFLAGS) -Itest -D_DEFAULT_SOURCE=1

$(MAIN): $(TEST_SRCS) $(TEST_HDRS) $(LIB) $(LIB_HDRS)
	@mkdir -p $(@D)
	$(CC) $(TEST_CFLAGS) -o $@ $(TEST_SRCS) $(LIB)

$(GEN): test/gen_vectors.c
	@mkdir -p $(@D)
	$(CC) -std=c99 -Wall -O2 $(XMSSREF_CFLAGS) -o $@ test/gen_vectors.c $(XMSSREF_LDFLAGS)

$(BUILD)/vectors-%.bin: $(GEN)
	@mkdir -p $(@D)
	./$(GEN) $* > $@

# ----- OCaml-extracted library ----------------------------------------------
# Pipeline:
#   1. `rocq compile extract.v`  →  build/ocaml/wots_extracted.ml(i)
#   2. ocamlopt -output-complete-obj packs all OCaml sources plus the OCaml
#      runtime into one .o that C can link without any OCaml dep at use-time.
#   3. wrap.c compiles to a small C bridge calling into that blob.
#   4. ar rcs the .o files into libwots_ocaml.a.
# libwots_ocaml.a is ABI-compatible with libwots.a, so the same test
# harness can link against either.

proof/model/notation.vo: proof/model/notation.v
	@rocq compile $(ROCQ_ARGS) $<

proof/model/wots.vo: proof/model/wots.v proof/model/notation.vo
	@rocq compile $(ROCQ_ARGS) $<

$(OCAML_EXTRACT): proof/model/wots.vo proof/model/extract.v
	@mkdir -p $(@D)
	@rocq compile $(ROCQ_ARGS) proof/model/extract.v

# Stage OCaml sources into build/ocaml/ alongside the extracted module so
# ocamlopt's .cmi/.cmx/.o intermediates land in build/, not in the tree.
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

$(OCAML_LIB): $(OCAML_BLOB) $(OCAML_WRAP) $(BUILD)/src/sha256.o $(BUILD)/src/util.o
	@mkdir -p $(@D)
	$(AR) rcs $@ $^

$(MAIN_OCAML): $(TEST_SRCS) $(TEST_HDRS) $(OCAML_LIB) $(LIB_HDRS)
	@mkdir -p $(@D)
	$(CC) $(TEST_CFLAGS) -o $@ $(TEST_SRCS) $(OCAML_LIB) -lm -ldl -lpthread

# ----- VST / Rocq -----------------------------------------------------------
# Clight ASTs land in proof/clight/ so _RocqProject finds them.

proof/clight/wots.v: src/wots.c src/wots.h src/sha256.h src/util.h
	@mkdir -p $(@D)
	clightgen -normalize -Isrc -Wp,-w -include src/util.c -o $@ src/wots.c

proof/clight/sha256.v: src/sha256.c src/sha256.h src/util.h
	@mkdir -p $(@D)
	clightgen -normalize -Isrc -Wp,-w -o $@ $<

Makefile.coq: _RocqProject
	@rocq makefile -f _RocqProject -o Makefile.coq

# ----- Clean ----------------------------------------------------------------

clean:
	@if [ -e Makefile.coq ]; then \
	    $(MAKE) --no-print-directory -f Makefile.coq cleanall 2>/dev/null; \
	fi
	@rm -rf $(BUILD)
	@rm -f Makefile.coq Makefile.coq.conf \
	       proof/clight/wots.v proof/clight/sha256.v
