import Mathlib
import AnyLayerIdentifiabilityProof.IdentifiabilityProof

set_option autoImplicit false

open MeasureTheory Matrix

namespace TransformerIdentifiability

/-! ## Trusted base — verify this section by hand -/

/-- Column-wise causal softmax: entry `(i, j)` is
`exp (M i j) / ∑_{i' ≤ j} exp (M i' j)` for `i ≤ j`, and `0` otherwise. -/
noncomputable def causalSoftmax {T : ℕ} (M : Matrix (Fin T) (Fin T) ℝ) :
    Matrix (Fin T) (Fin T) ℝ :=
  Matrix.of fun i j =>
    if i ≤ j then Real.exp (M i j) / ∑ i' ∈ Finset.Iic j, Real.exp (M i' j) else 0

/-- One single-head causal attention layer with additive skip connection:
`X ↦ X + V·X·causalSoftmax (Xᵀ·A·X)`  (eq. (1) of the paper; note
`(Xᵀ * A * X) i j = X_{:,i}ᵀ A X_{:,j}`, the paper's score convention). -/
noncomputable def attnLayer {d T : ℕ} (V A : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin T) ℝ) : Matrix (Fin d) (Fin T) ℝ :=
  X + V * X * causalSoftmax (Xᵀ * A * X)

/-- Depth-`L` parameter space: layer `ℓ` carries `(V ℓ, A ℓ)`,
so `Params L d ≅ (ℝ^{d×d})^{2L}`. -/
abbrev Params (L d : ℕ) : Type :=
  Fin L → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ

/-- The network `TF_θ = Layer_{V_L,A_L} ∘ ⋯ ∘ Layer_{V_1,A_1}`, by recursion:
the empty network is the identity, and a depth-`(L+1)` network applies its
first layer `θ 0`, then the depth-`L` network of the remaining layers. -/
noncomputable def transformer {d T : ℕ} :
    {L : ℕ} → Params L d → Matrix (Fin d) (Fin T) ℝ → Matrix (Fin d) (Fin T) ℝ
  | 0, _, X => X
  | _ + 1, θ, X => transformer (Fin.tail θ) (attnLayer (θ 0).1 (θ 0).2 X)

/-- `Matrix (Fin n) (Fin m) ℝ` is definitionally `Fin n → Fin m → ℝ`; give it
the measure-space structure of that pi type.  Mathlib's `Pi` and `Prod`
instances then make `volume` on `Params L d` the product Lebesgue measure,
i.e. Lebesgue measure on `ℝ^(2·L·d²)`. -/
noncomputable instance {n m : ℕ} : MeasureSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (MeasureSpace (Fin n → Fin m → ℝ))

/-! ## Proof-module bridge — not part of the trusted model definition -/

@[simp] theorem causalSoftmax_eq_nlayer {T : ℕ}
    (M : Matrix (Fin T) (Fin T) ℝ) :
    causalSoftmax M = NLayer.causalSoftmax M := by
  rfl

@[simp] theorem attnLayer_eq_nlayer {d T : ℕ}
    (V A : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin T) ℝ) :
    attnLayer V A X = NLayer.attnLayer V A X := by
  rfl

@[simp] theorem transformer_eq_nlayer {d T : ℕ} :
    ∀ {L : ℕ} (θ : Params L d) (X : Matrix (Fin d) (Fin T) ℝ),
      transformer θ X = NLayer.transformer θ X
  | 0, _, _ => rfl
  | L + 1, θ, X => by
      simp [transformer, NLayer.transformer, transformer_eq_nlayer (Fin.tail θ)]

/-! ## Public theorem -/

/-- **Main theorem** (Theorem 3.4 of the paper, null-set form).
For depth `L ≥ 1`, context multiplicity `r ≥ 2` (sequence length `r + 1`) and
dimension `d ≥ max 2 (C(L,2) + 2(L-1))`, there is a Lebesgue-null set `N` of
parameters such that every `θ'` outside `N` is identified, among *all*
parameters, by the input-output map of its network. -/
theorem identifiability (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r)
    (hd₁ : 2 ≤ d) (hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d) :
    ∃ N : Set (Params L d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : Params L d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ,
          transformer θ X = transformer θ' X) →
        θ = θ' := by
  simpa [Params, transformer, attnLayer, causalSoftmax,
    NLayer.transformer, NLayer.attnLayer, NLayer.causalSoftmax] using
    IdentifiabilityProof.identifiability_all_depth L r d hL hr hd₁ hd₂

end TransformerIdentifiability
