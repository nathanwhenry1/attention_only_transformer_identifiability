# Contributing

Corrections are welcome as focused pull requests. For a mathematical or Lean change:

1. explain which Lean declaration is affected;
2. keep the pinned toolchain unless the pull request is specifically a toolchain upgrade;
3. run `python3 scripts/check_local_imports.py . AnyLayerIdentifiabilityProof`;
4. run `python3 scripts/check_no_placeholders.py AnyLayerIdentifiabilityProof AnyLayerIdentifiabilityProof.lean`;
5. run `lake build` and `./scripts/print_axioms.sh`;
6. include the relevant axiom output when a theorem dependency changes.

Equivalently, `make check` runs the import, audit, build, and axiom steps in order.

For exposition changes, preserve mathematical attribution and keep links usable for
readers who do not know Lean.
