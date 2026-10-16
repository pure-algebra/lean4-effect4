# The C prototype of the Val wire frames and a toy host. The system C compiler, no dependency.
# Run from this folder: make test. The fixtures are the repository's committed bytes.

ROOT    := ../../../..
CC      ?= cc
CFLAGS  ?= -std=c11 -O2 -g -Wall -Wextra -Wpedantic -Wshadow -Wconversion -Wno-sign-conversion
SAN     ?= -fsanitize=address,undefined -fno-omit-frame-pointer

FRAMES  := $(ROOT)/ocaml/engine/test/modeled/modeled.txt \
           $(ROOT)/ocaml/engine/test/todo/todo-host.txt \
           $(wildcard $(ROOT)/ocaml/goldens/eff/*.hex)
TODO    := $(ROOT)/ocaml/engine/test/todo/todo-host.txt

.PHONY: test test-san lean-diff clean

# The differential against Lean's compiled decoder needs the pinned toolchain and the core's shared
# library that a Lake build leaves. This target runs no Lake; it fails with a message when the
# library is absent. In a worktree with no build, name the main checkout's: LEAN_LIBDIR=<path>.
LEAN_TOOLCHAIN ?= $(HOME)/.elan/toolchains/$(shell sed 's|/|--|; s|:|---|' $(ROOT)/lean-toolchain)
LEAN_LIBDIR    ?= $(ROOT)/.lake/build/lib
# The core's library binds its package dependencies' symbols at load (hash, typescript), as Lake
# loads them together; link them by path and put their folders on the loader's path.
LEAN_PKGDIRS   := $(wildcard $(LEAN_LIBDIR)/../../packages/*/.lake/build/lib)
LEAN_PKGLIBS   := $(wildcard $(addsuffix /lib*.dylib,$(LEAN_PKGDIRS)) $(addsuffix /lib*.so,$(LEAN_PKGDIRS)))
empty          :=
space          := $(empty) $(empty)
LEAN_LOADPATH  := $(subst $(space),:,$(strip $(LEAN_LIBDIR) $(LEAN_PKGDIRS)))

test: test_val test_host
	./test_val $(FRAMES)
	./test_host $(TODO)

test-san: CFLAGS += $(SAN)
test-san: clean test

test_val: test_val.c fixture.c fixture.h e4val.c e4val.h
	$(CC) $(CFLAGS) -o $@ test_val.c fixture.c e4val.c

test_host: test_host.c e4host.c e4host.h e4val.c e4val.h
	$(CC) $(CFLAGS) -o $@ test_host.c e4host.c e4val.c

lean_diff: lean_diff.c fixture.c fixture.h e4val.c e4val.h
	@test -f $(LEAN_LIBDIR)/libeffect4_Effect4.dylib -o -f $(LEAN_LIBDIR)/libeffect4_Effect4.so || \
	  { echo "no libeffect4_Effect4 under LEAN_LIBDIR=$(LEAN_LIBDIR): build the core first"; exit 1; }
	$(CC) -std=c11 -O2 -g -Wall -Wextra -Wno-unused-parameter -I$(LEAN_TOOLCHAIN)/include -o $@ lean_diff.c fixture.c e4val.c \
	  -L$(LEAN_LIBDIR) -leffect4_Effect4 $(LEAN_PKGLIBS) -L$(LEAN_TOOLCHAIN)/lib/lean -lleanshared \
	  -Wl,-rpath,$(LEAN_TOOLCHAIN)/lib/lean -Wl,-rpath,$(LEAN_LIBDIR)

lean-diff: lean_diff
	DYLD_LIBRARY_PATH=$(LEAN_LOADPATH) LD_LIBRARY_PATH=$(LEAN_LOADPATH) ./lean_diff $(FRAMES)

clean:
	rm -rf test_val test_host lean_diff *.dSYM
