# Identifiability of attention-only transformers

Consider an `L`-layer attention-only transformer with causal masking, a single
attention head per layer, and additive skip connections. Each layer `ℓ` acts on a
`d × T` activation matrix `X` by

```
X ↦ X + V_ℓ · X · softmax_causal(Xᵀ · A_ℓ · X),
```

so the network is determined by its parameters `θ = (V_ℓ, A_ℓ)_{ℓ=1}^{L}`, a point
of `(ℝ^{d×d})^{2L}`.

**Question.** To what extent is `θ` determined by the input-output map `X ↦ TF_θ(X)`?
A priori, distinct parameter settings could compute the same function.

## Result formalized here

For depth `L ≥ 1`, context multiplicity `r ≥ 2` (sequence length `r + 1`), and
dimension `d ≥ max(2, C(L,2) + 2(L-1))`, there is an explicit Lebesgue-null set `N`
of parameters — a finite union of proper algebraic subsets, cut out by explicit
polynomial nonvanishing conditions — such that every `θ'` outside `N` is identified,
among *all* parameters, by the input-output map of its network. That is, if
`TF_θ(X) = TF_{θ'}(X)` for all inputs `X`, then `θ = θ'`.

The exact Lean target is `TransformerIdentifiability.identifiability`; the all-depth
core is `TransformerIdentifiability.IdentifiabilityProof.identifiability_all_depth`.

The proof is by induction on depth: complex-analytic continuation in an
inverse-temperature variable identifies the innermost attention matrix through an
`L`-tier hierarchy of accumulating singularities; everything thereafter is
real-variable (saturated limits of the attention gates, a structural trichotomy, and
a `K = I` cancellation identity created by the skip connections).
