ifeq ($(filter -j%,$(MAKEFLAGS)),)
MAKEFLAGS += -j$(shell nproc)
endif

.PHONY: all
all: musl examples

BUILD_DIR := build
ARCH := $(shell uname -m)
$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

.PHONY: clean
clean:
	rm -rf $(BUILD_DIR)

# ==================== Musl ====================
MUSL_DIR := ../third_party/musl
MUSL_CC := $(BUILD_DIR)/bin/musl-gcc

.PHONY: musl
musl: $(MUSL_CC)
$(MUSL_CC): | $(BUILD_DIR)
	cd $(MUSL_DIR) && ./configure \
	    --prefix=$(abspath $(BUILD_DIR)) \
	    --syslibdir=$(abspath $(BUILD_DIR))/lib
	$(MAKE) -C $(MUSL_DIR) LDSO_OBJS= install

# ==================== Examples ====================
# -rpath,<our build>: embed DT_RUNPATH so the binaries resolve their
#                     libc + libfoo/libbar from our build, not the
#                     system search path.
LDFLAGS := -Wl,-rpath,$(abspath $(BUILD_DIR))/lib \
           -Wl,-rpath,$(abspath $(BUILD_DIR))

.PHONY: examples
examples: $(BUILD_DIR)/main
$(BUILD_DIR)/main: $(wildcard *.c *.h) $(MUSL_CC) | $(BUILD_DIR)
	$(MUSL_CC) $(LDFLAGS) -fPIC -shared -Wl,-soname,libfoo.so -o $(BUILD_DIR)/libfoo.so libfoo.c
	$(MUSL_CC) $(LDFLAGS) -fPIC -shared -Wl,-soname,libbar.so -o $(BUILD_DIR)/libbar.bootstrap.so libbar.c
	$(MUSL_CC) $(LDFLAGS) -fPIC -shared -Wl,-soname,libbaz.so libbaz.c $(BUILD_DIR)/libbar.bootstrap.so -o $(BUILD_DIR)/libbaz.so
	$(MUSL_CC) $(LDFLAGS) -fPIC -shared -Wl,-soname,libbar.so libbar.c -L$(BUILD_DIR) -lbaz -o $(BUILD_DIR)/libbar.so
	$(MUSL_CC) $(LDFLAGS) -fPIC -shared -Wl,-soname,libunused.so -o $(BUILD_DIR)/libunused.so libunused.c
	$(MUSL_CC) $(LDFLAGS) main.c -pthread -L$(BUILD_DIR) -lfoo -lbar -Wl,-rpath-link,$(BUILD_DIR) -o $(BUILD_DIR)/main
