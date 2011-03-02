# Build file for creating DMG files.
# Modified from template by Remko Tronçon
# http://el-tramo.be/git/fancy-dmg/plain/Makefile

# If you create a DMG template, you should make one containing all
# the files listed in $(SOURCE_FILES) below, and arrange everything to suit
# your style. The contents of the files themselves does not matter, so
# they can be empty (they will be overwritten later). 
#
# Remko Tronçon 
# http://el-tramo.be/about
# Licensed under the MIT License. See COPYING for details.


################################################################################
# Customizable variables
################################################################################

NAME ?= Twelf

# Some of this blatantly rides off of the OSX non-case-sensitivity thing
SOURCE_DIR ?= ..
SOURCE_FILES ?= Twelf/LICENSE Twelf/bin Twelf/emacs Twelf/vim Twelf/examples

TEMPLATE_DMG ?= template.dmg

################################################################################
# DMG building. No editing should be needed beyond this point.
################################################################################

MASTER_DMG=$(NAME).dmg
WC_DMG=wc.dmg
WC_DIR=wc

.PHONY: all
all: $(MASTER_DMG)

$(TEMPLATE_DMG): $(TEMPLATE_DMG).bz2
	bunzip2 -k $<

$(TEMPLATE_DMG).bz2: 
	@echo
	@echo --------------------- Generating empty template --------------------
	mkdir template
	hdiutil create -fs HFSX -layout SPUD -size 40m "$(TEMPLATE_DMG)" -srcfolder template -format UDRW -volname "$(NAME)" -quiet
	rmdir template
	bzip2 "$(TEMPLATE_DMG)"
	@echo

$(WC_DMG): $(TEMPLATE_DMG)
	cp $< $@

$(MASTER_DMG): $(WC_DMG) $(addprefix $(SOURCE_DIR)/,$(SOURCE_FILES))
	@echo
	@echo --------------------- Creating Disk Image --------------------
	mkdir -p $(WC_DIR)
	hdiutil attach "$(WC_DMG)" -noautoopen -quiet -mountpoint "$(WC_DIR)"
	for i in $(SOURCE_FILES); do  \
		rm -rf "$(WC_DIR)/$$i"; \
		ditto -rsrc "$(SOURCE_DIR)/$$i" "$(WC_DIR)/$$i"; \
	done
	WC_DEV=`hdiutil info | grep "$(WC_DIR)" | grep "Apple_HFS" | awk '{print $$1}'` && \
	hdiutil detach $$WC_DEV -force
	rm -f "$(MASTER_DMG)"
	hdiutil convert "$(WC_DMG)" -quiet -format UDZO -imagekey zlib-level=9 -o "$@"
	rm -rf $(WC_DIR)
	@echo

.PHONY: clean
clean:
	-rm -rf $(TEMPLATE_DMG) $(MASTER_DMG) $(WC_DMG)