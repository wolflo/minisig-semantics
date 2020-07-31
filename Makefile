.PHONY: test* build*

BACKEND := llvm

HARNESS_DIR := test
TEST_DIR 	:= $(HARNESS_DIR)/msig-tests
EXPECT_DIR  := $(TEST_DIR)/expect

DIFF := git --no-pager diff --no-index --ignore-all-space -R

tests := $(wildcard $(TEST_DIR)/*.msig)

build	   :; kompile --backend $(BACKEND) minisig.k
build-test :; kompile --backend $(BACKEND) $(HARNESS_DIR)/test-harness.k
build-all  : build build-test

$(TEST_DIR)/%.msig.out: $(TEST_DIR)/%.msig
	krun $< --directory $(HARNESS_DIR) > $@

$(TEST_DIR)/%.msig.run: $(TEST_DIR)/%.msig.out
	$(DIFF) $< $(EXPECT_DIR)/$*.msig.expect

test: $(tests:=.run)
