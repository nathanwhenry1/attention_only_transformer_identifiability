# Identifiability of Attention-Only Transformers

> **Identifiability of deep causal attention-only transformers with skip connections**
>
> Nathan W. Henry, Center for Human-Compatible AI, UC Berkeley, `nathan.henry@berkeley.edu`

[![Build Lean formalization](https://github.com/nathanwhenry1/attention_only_transformer_identifiability/actions/workflows/build-lean.yml/badge.svg)](https://github.com/nathanwhenry1/attention_only_transformer_identifiability/actions/workflows/build-lean.yml)
[![Lean 4.30.0](https://img.shields.io/badge/Lean-4.30.0-blue)](lean-toolchain)
[![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue.svg)](LICENSE)

This repository contains a complete Lean 4 formalization of an identifiability theorem
for attention-only transformers: a generic such network is determined exactly, layer by
layer, by the function it computes.

## Result

Consider an `L`-layer attention-only transformer with causal masking, one attention
head per layer, and additive skip connections, with layer `ℓ` acting by
`X ↦ X + V_ℓ · X · softmax_causal(Xᵀ · A_ℓ · X)`.

For depth `L ≥ 1`, context multiplicity `r ≥ 2` (sequence length `r + 1`), and
dimension `d ≥ max(2, C(L,2) + 2(L-1))`, there is a Lebesgue-null set `N` of
parameters such that every `θ'` outside `N` is identified, among *all* parameters, by
the input-output map of its network:

> if `TF_θ(X) = TF_{θ'}(X)` for every input `X`, then `θ = θ'`.

The exceptional set `N` is an explicit finite union of proper algebraic subsets, cut
out by explicit polynomial nonvanishing conditions.

The public Lean declaration is:

```lean
TransformerIdentifiability.identifiability :
  ∀ (L r d : ℕ), 1 ≤ L → 2 ≤ r → 2 ≤ d → Nat.choose L 2 + 2 * (L - 1) ≤ d →
    ∃ N : Set (Params L d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : Params L d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ, transformer θ X = transformer θ' X) →
        θ = θ'
```

## Start here

- **For the model and the final theorem:** open
  [`AnyLayerIdentifiabilityProof/Identifiability.lean`](AnyLayerIdentifiabilityProof/Identifiability.lean)
  — it holds the model definitions (`causalSoftmax`, `attnLayer`,
  `transformer`) and the public theorem, then defers to
  [`AnyLayerIdentifiabilityProof/IdentifiabilityProof.lean`](AnyLayerIdentifiabilityProof/IdentifiabilityProof.lean).
- **For the result statement:** read [`problem_statement.md`](problem_statement.md).
- **For verification details:** inspect the GitHub Actions run.

## Proof at a glance

The proof is by induction on depth, inspired by Fefferman's related proof of identifiability of `tanh` networks in "Reconstructing a neural net from its output" (1994). We 

## Repository contents

```text
.
├── AnyLayerIdentifiabilityProof.lean          # Lean root importing the project
├── AnyLayerIdentifiabilityProof/
│   ├── Identifiability.lean                    # Trusted model defs + public theorem `identifiability`
│   ├── IdentifiabilityProof.lean               # Proof bridge → all-depth core
│   └── NLayer/
│       ├── IdentifiabilityMain.lean            # All-depth assembly
│       ├── Foundations/                         # Polynomial genericity / Zariski foundations  (4 files)
│       ├── Analytic/                            # Toolkit: complex-analytic, stratification, quadric  (8 files)
│       ├── Step1/                               # Step 1: attention-matrix identification  (12 files)
│       ├── IDL/                                 # Inductive descent lemma: cascade, trichotomy, matching  (23 files)
│       ├── Step2/                               # Step 3: realization, the sweep, matching realization  (5 files)
│       └── Genericity/                          # Step 8: certificates, anchors, witnesses, null set  (7 files)
├── scripts/
│   ├── check_no_placeholders.py
│   ├── check_local_imports.py
│   ├── check_axioms.py
│   └── print_axioms.sh
├── problem_statement.md
├── Makefile
├── lakefile.toml
├── lake-manifest.json
├── lean-toolchain                              # Lean 4.30.0
├── CITATION.cff
├── NOTICE
└── LICENSE                                     # Apache-2.0 for code and repository text
```

The formalization is roughly 51,000 lines of Lean across 64 files.

## Build and verify

Install [`elan`](https://github.com/leanprover/elan), then run:

```bash
lake exe cache get
make check
```

The individual commands are:

```bash
make imports   # all project-local imports resolve
make audit     # no active sorry/admit or project assumption declarations
make build     # compile the project
make axioms    # print and check final kernel dependencies
```

Lean and Mathlib are pinned to `v4.30.0` in `lean-toolchain` and `lake-manifest.json`.

## Citation

```bibtex
@misc{henry2026identifiability,
  author       = {Nathan W. Henry},
  title        = {Identifiability of deep causal attention-only transformers with skip connections},
  year         = {2026},
  howpublished = {GitHub repository},
  url          = {https://github.com/nathanwhenry1/attention_only_transformer_identifiability}
}
```

See [`CITATION.cff`](CITATION.cff) for machine-readable metadata.

## License

The Lean code and repository documentation are licensed under Apache-2.0. The paper
remains copyright Nathan W. Henry. See [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
