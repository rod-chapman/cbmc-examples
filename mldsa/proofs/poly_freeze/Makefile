# SPDX-License-Identifier: Apache-2.0

include ../Makefile_params.common

FUNCTION_NAME = poly_freeze
HARNESS_ENTRY = harness
HARNESS_FILE = $(FUNCTION_NAME)_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = poly_freeze

DEFINES +=
INCLUDES += -I$(SRCDIR)

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/reduce.c

CHECK_FUNCTION_CONTRACTS=$(FUNCTION_NAME)
USE_FUNCTION_CONTRACTS=ml_dsa_freeze
APPLY_LOOP_CONTRACTS=on
USE_DYNAMIC_FRAMES=1

# Disable any setting of EXTERNAL_SAT_SOLVER, and choose SMT backend instead
EXTERNAL_SAT_SOLVER=
CBMCFLAGS=--smt2

# If this proof is found to consume huge amounts of RAM, you can set the
# EXPENSIVE variable. With new enough versions of the proof tools, this will
# restrict the number of EXPENSIVE CBMC jobs running at once. See the
# documentation in Makefile.common under the "Job Pools" heading for details.
# EXPENSIVE = true

# This function is large enough to need...
CBMC_OBJECT_BITS = 8

include ../Makefile.common
