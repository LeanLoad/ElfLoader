ifeq ($(filter -j%,$(MAKEFLAGS)),)
MAKEFLAGS += -j$(shell nproc)
endif

.PHONY: all
all: musl examples

BUILD_DIR := build
ARCH := $(shell uname -m)
$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

# Also `distclean`s musl: changing musl build flags (e.g. `LDSO_OBJS=`)
# only affects libc.so's *link* step, and `make install` will not
# relink an already-built libc.so — so a half-clean would silently
# keep the stale libc around.
.PHONY: clean
clean:
	rm -rf $(BUILD_DIR)
	$(MAKE) -C $(MUSL_DIR) distclean

# ==================== Musl ====================
MUSL_DIR := third_party/musl
MUSL_CC := $(BUILD_DIR)/bin/musl-gcc

.PHONY: musl
musl: $(MUSL_CC)
$(MUSL_CC): | $(BUILD_DIR)
	cd $(MUSL_DIR) && ./configure \
	    --prefix=$(abspath $(BUILD_DIR)) \
	    --syslibdir=$(abspath $(BUILD_DIR))/lib
	# `LDSO_OBJS=` strips musl's dynamic-loader bootstrap (`dlstart`)
	# from libc.so. Native `exec` of these binaries does not work as
	# a result; they are intended to be loaded by leanload, which
	# does the dynamic-loader's job itself. Differential testing
	# against the kernel exec path is forfeited; that's the
	# tradeoff.
	$(MAKE) -C $(MUSL_DIR) LDSO_OBJS= install

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
