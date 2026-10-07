SHELL := /bin/sh
.DEFAULT_GOAL := check
.NOTPARALLEL:
export LEAN_NUM_THREADS := 1

.PHONY: check build audit drafts palomar palomar-structure
check: build audit

build:
	lake build

audit:
	python3 scripts/group_subprojects.py --check
	python3 scripts/audit_local_sources.py
	lake env lean AxiomAudit.lean
	lake env lean AllLocalAxiomAudit.lean

drafts:
	lake build +GinibrePoincare.Analysis.DynamicalFactorization:olean +GinibrePoincare.Analysis.NonQuadraticPotential:olean

# Registry readiness is separate from the existing proof-library checks.
palomar-structure:
	python3 scripts/check_palomar.py --structure-only

palomar:
	python3 scripts/verify_palomar.py
