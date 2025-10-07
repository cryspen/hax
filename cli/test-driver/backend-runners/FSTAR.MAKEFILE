.PHONY: all clean

ROOTS=$(wildcard *.fst *.fsti)
OUTPUT_DIR=fstar_checked

FSTAR=fstar.exe \
	--cache_dir $(OUTPUT_DIR) \
	--odir $(OUTPUT_DIR) \
	$(addprefix --include , $(INCLUDE_PATHS) $(OUTPUT_DIR)) \
	--already_cached 'Prims FStar'

all: all-checked

.depend: $(wildcard *.fst *.fsti)
	mkdir -p $(OUTPUT_DIR)
	$(FSTAR) --dep full $(ROOTS) -o $@

include .depend

all-checked: .depend $(ALL_CHECKED_FILES)

$(OUTPUT_DIR)/%.checked:
	$(FSTAR) $< --cache_checked_modules

clean:
	rm $(OUTPUT_DIR)/*.checked .depend
	$(MAKE) -C $(OUTPUT_DIR) clean
