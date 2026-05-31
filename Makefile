ifeq ($(filter -j%,$(MAKEFLAGS)),)
MAKEFLAGS += -j$(shell nproc)
endif

.PHONY: all
all: musl examples

BUILD_DIR := build
ARCH := $(shell uname -m)
THIRD_PARTY_DIR ?= ../third_party
$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

# Also `distclean`s musl: changing musl build flags (e.g. `LDSO_OBJS=`)
# only affects libc.so's *link* step, and `make install` will not
# relink an already-built libc.so — so a half-clean would silently
# keep the stale libc around.
.PHONY: clean
clean:
	rm -rf $(BUILD_DIR)
	if [ -d "$(MUSL_DIR)" ]; then $(MAKE) -C $(MUSL_DIR) distclean; fi

# ==================== Musl ====================
MUSL_DIR := $(THIRD_PARTY_DIR)/impl-loader/musl
MUSL_CC := $(BUILD_DIR)/bin/musl-gcc

.PHONY: musl
musl: $(MUSL_CC)
$(MUSL_CC): | $(BUILD_DIR)
	@test -x "$(MUSL_DIR)/configure" || { echo "missing musl source at $(MUSL_DIR); run ../setup.sh from the LeanLoad umbrella checkout or set THIRD_PARTY_DIR"; exit 1; }
	cd $(MUSL_DIR) && ./configure \
	    --prefix=$(abspath $(BUILD_DIR)) \
	    --syslibdir=$(abspath $(BUILD_DIR))/lib
	# `LDSO_OBJS=` strips musl's dynamic-loader bootstrap (`dlstart`)
	# from libc.so. Native `exec` of these binaries does not work as
	# a result; they are intended to be loaded by elfloader, which
	# does the dynamic-loader's job itself. Differential testing
	# against the kernel exec path is forfeited; that's the
	# tradeoff.
	#
	# `LDFLAGS=-Wl,-soname,libc.so` sets DT_SONAME on the produced
	# libc.so — required by elfloader's discover stage (`Effects.io`
	# fails loud on SONAME-less .so files; dedup by SONAME is the
	# only sound key without realpath/inode tracking). Stock musl
	# (with the `dlstart` bootstrap intact) sets SONAME implicitly
	# via its own link rules; stripping LDSO_OBJS also strips that,
	# so we set it back explicitly.
	$(MAKE) -C $(MUSL_DIR) LDSO_OBJS= LDFLAGS=-Wl,-soname,libc.so install

# ==================== Examples ====================
# -rpath,<our build>: embed DT_RUNPATH so the binaries resolve their
#                     libc + libfoo/libbar from our build, not the
#                     system search path.
EX_DIR := examples
LDFLAGS := -Wl,-rpath,$(abspath $(BUILD_DIR))/lib \
           -Wl,-rpath,$(abspath $(BUILD_DIR)) \
           -Wl,--hash-style=both

.PHONY: examples
examples: $(BUILD_DIR)/main
$(BUILD_DIR)/main: $(wildcard $(EX_DIR)/*.c $(EX_DIR)/*.h) $(MUSL_CC) | $(BUILD_DIR)
	$(MUSL_CC) $(LDFLAGS) -fPIC -shared -Wl,-soname,libfoo.so -o $(BUILD_DIR)/libfoo.so $(EX_DIR)/libfoo.c
	$(MUSL_CC) $(LDFLAGS) -fPIC -shared -Wl,-soname,libbar.so -o $(BUILD_DIR)/libbar.bootstrap.so $(EX_DIR)/libbar.c
	$(MUSL_CC) $(LDFLAGS) -fPIC -shared -Wl,-soname,libbaz.so $(EX_DIR)/libbaz.c $(BUILD_DIR)/libbar.bootstrap.so -o $(BUILD_DIR)/libbaz.so
	$(MUSL_CC) $(LDFLAGS) -fPIC -shared -Wl,-soname,libbar.so $(EX_DIR)/libbar.c -L$(BUILD_DIR) -lbaz -o $(BUILD_DIR)/libbar.so
	$(MUSL_CC) $(LDFLAGS) -fPIC -shared -Wl,-soname,libunused.so -o $(BUILD_DIR)/libunused.so $(EX_DIR)/libunused.c
	$(MUSL_CC) $(LDFLAGS) $(EX_DIR)/main.c -pthread -L$(BUILD_DIR) -lfoo -lbar -Wl,-rpath-link,$(BUILD_DIR) -o $(BUILD_DIR)/main
