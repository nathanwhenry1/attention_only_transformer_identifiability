import AnyLayerIdentifiabilityProof.NLayer.Analytic.AlgebraicQuadric

set_option autoImplicit false

open Filter Topology Matrix

namespace TransformerIdentifiability.NLayer

/-!
# Dial paths and first-gate saturation

This file formalizes the "Dial paths" lemma (`lem:dial`) from
`n_layer_proof.tex`, lines 2075–2136.

Given a base point `(w0, v0)` on the bilinear quadric `q(w, v) = 0` (here
`q = matrixBilin A`), a direction `y`, and a scalar `c`, the *dial path* is
`τ ↦ (w0 - (c/τ)•y, v0 + (c/τ)•y)`.  Its sum is constant, it converges to
`(w0, v0)` as `τ → ∞`, and under the bracket normalisation
`matrixBilin A w0 y - matrixBilin A y v0 = 1` the rescaled gate argument
`τ·q(w(τ), v(τ)) + b` converges to `c + b`.  Applying the (continuous) sigmoid
gives first-gate saturation `s₁(τ) → sig (c + b)`.

The connection `sig (c + b) = t` (with `c = sigmoidLogit t - b`) belongs to a
higher layer and is deliberately *not* established here; this file is purely
about `sig (c + b)`.
-/

/-! ## Bilinearity of `matrixBilin`

`matrixBilin A w v = w ⬝ᵥ A.mulVec v` (see `AlgebraicQuadric.lean`).  Only
`matrixBilin_sub` is available there, so we record the additivity and scalar
homogeneity needed to expand the dial identity. -/

/-- `matrixBilin` is additive in its left argument. -/
theorem matrixBilin_add_left {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (w w' v : Fin d → ℝ) :
    matrixBilin A (w + w') v = matrixBilin A w v + matrixBilin A w' v := by
  simp [matrixBilin, add_dotProduct]

/-- `matrixBilin` is additive in its right argument. -/
theorem matrixBilin_add_right {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (w v v' : Fin d → ℝ) :
    matrixBilin A w (v + v') = matrixBilin A w v + matrixBilin A w v' := by
  simp [matrixBilin, Matrix.mulVec_add, dotProduct_add]

/-- `matrixBilin` is subtractive in its left argument. -/
theorem matrixBilin_sub_left {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (w w' v : Fin d → ℝ) :
    matrixBilin A (w - w') v = matrixBilin A w v - matrixBilin A w' v := by
  simp [matrixBilin, sub_dotProduct]

/-- `matrixBilin` is subtractive in its right argument. -/
theorem matrixBilin_sub_right {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (w v v' : Fin d → ℝ) :
    matrixBilin A w (v - v') = matrixBilin A w v - matrixBilin A w v' := by
  simp [matrixBilin, Matrix.mulVec_sub, dotProduct_sub]

/-- `matrixBilin` is homogeneous in its left argument. -/
theorem matrixBilin_smul_left {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (a : ℝ) (w v : Fin d → ℝ) :
    matrixBilin A (a • w) v = a * matrixBilin A w v := by
  simp [matrixBilin, smul_dotProduct, smul_eq_mul]

/-- `matrixBilin` is homogeneous in its right argument. -/
theorem matrixBilin_smul_right {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (a : ℝ) (w v : Fin d → ℝ) :
    matrixBilin A w (a • v) = a * matrixBilin A w v := by
  simp [matrixBilin, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/-! ## The dial path -/

/-- The **dial path** (`lem:dial`): with base point `(w0, v0)`, direction `y`,
and scalar `c`, the path sends `τ` to `(w0 - (c/τ)•y, v0 + (c/τ)•y)`. -/
noncomputable def dialPath {d : ℕ} (w0 v0 y : Fin d → ℝ) (c : ℝ) :
    ℝ → (Fin d → ℝ) × (Fin d → ℝ) :=
  fun τ => (w0 - (c / τ) • y, v0 + (c / τ) • y)

@[simp] theorem dialPath_fst {d : ℕ} (w0 v0 y : Fin d → ℝ) (c τ : ℝ) :
    (dialPath w0 v0 y c τ).1 = w0 - (c / τ) • y := rfl

@[simp] theorem dialPath_snd {d : ℕ} (w0 v0 y : Fin d → ℝ) (c τ : ℝ) :
    (dialPath w0 v0 y c τ).2 = v0 + (c / τ) • y := rfl

/-- `lem:dial`(a): the sum of the two dial components is the constant `w0 + v0`,
because the perturbations cancel. -/
theorem dialPath_fst_add_snd {d : ℕ} (w0 v0 y : Fin d → ℝ) (c τ : ℝ) :
    (dialPath w0 v0 y c τ).1 + (dialPath w0 v0 y c τ).2 = w0 + v0 := by
  simp only [dialPath_fst, dialPath_snd]
  abel

/-- The scalar `c / τ` tends to `0` as `τ → ∞`. -/
theorem tendsto_const_div_atTop {c : ℝ} :
    Tendsto (fun τ : ℝ => c / τ) atTop (𝓝 0) := by
  simpa using
    ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul c).congr
      (fun τ => by rw [div_eq_mul_inv])

/-- Each scaled perturbation `(c/τ)•y` tends to `0` as `τ → ∞`. -/
theorem tendsto_dialPath_smul_atTop {d : ℕ} (y : Fin d → ℝ) (c : ℝ) :
    Tendsto (fun τ : ℝ => (c / τ) • y) atTop (𝓝 (0 : Fin d → ℝ)) := by
  have h := (tendsto_const_div_atTop (c := c)).smul_const y
  simpa using h

/-- The dial path converges to its base point `(w0, v0)` as `τ → ∞`. -/
theorem tendsto_dialPath_atTop {d : ℕ} (w0 v0 y : Fin d → ℝ) (c : ℝ) :
    Tendsto (dialPath w0 v0 y c) atTop (𝓝 (w0, v0)) := by
  have hfst : Tendsto (fun τ : ℝ => w0 - (c / τ) • y) atTop (𝓝 w0) := by
    have h := (tendsto_dialPath_smul_atTop y c).const_sub w0
    simpa using h
  have hsnd : Tendsto (fun τ : ℝ => v0 + (c / τ) • y) atTop (𝓝 v0) := by
    have h := (tendsto_dialPath_smul_atTop y c).const_add v0
    simpa using h
  exact hfst.prodMk_nhds hsnd

/-! ## The exact dial identity -/

/-- `lem:dial`(b), exact dial identity.  Under `hq : matrixBilin A w0 v0 = 0`
and the bracket normalisation
`hbracket : matrixBilin A w0 y - matrixBilin A y v0 = 1`, for `τ ≠ 0`,
`q(w(τ), v(τ)) = (c/τ) - (c/τ)² · ρ̂` where `ρ̂ = matrixBilin A y y`. -/
theorem matrixBilin_dialPath {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (w0 v0 y : Fin d → ℝ) (c : ℝ)
    (hq : matrixBilin A w0 v0 = 0)
    (hbracket : matrixBilin A w0 y - matrixBilin A y v0 = 1)
    {τ : ℝ} (_hτ : τ ≠ 0) :
    matrixBilin A (dialPath w0 v0 y c τ).1 (dialPath w0 v0 y c τ).2
      = (c / τ) - (c / τ) ^ 2 * matrixBilin A y y := by
  set a : ℝ := c / τ with ha
  simp only [dialPath_fst, dialPath_snd]
  -- Expand `matrixBilin A (w0 - a•y) (v0 + a•y)` by bilinearity.
  rw [matrixBilin_sub_left, matrixBilin_add_right, matrixBilin_add_right,
    matrixBilin_smul_left, matrixBilin_smul_left, matrixBilin_smul_right,
    matrixBilin_smul_right, hq]
  -- The goal is now algebraic in the scalars; the bracket
  -- `matrixBilin A w0 y - matrixBilin A y v0 = 1` collapses the linear part to `a`.
  linear_combination a * hbracket

/-! ## The gate argument and its limit -/

/-- `lem:dial`(b), rescaled form.  Multiplying the exact dial identity by `τ` and
adding the bias `b` gives, for `τ ≠ 0`,
`τ·q(w(τ), v(τ)) + b = (c + b) - (c²·ρ̂)/τ`. -/
theorem tau_mul_matrixBilin_dialPath_add {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (w0 v0 y : Fin d → ℝ) (c b : ℝ)
    (hq : matrixBilin A w0 v0 = 0)
    (hbracket : matrixBilin A w0 y - matrixBilin A y v0 = 1)
    {τ : ℝ} (hτ : τ ≠ 0) :
    τ * matrixBilin A (dialPath w0 v0 y c τ).1 (dialPath w0 v0 y c τ).2 + b
      = (c + b) - (c ^ 2 * matrixBilin A y y) / τ := by
  rw [matrixBilin_dialPath A w0 v0 y c hq hbracket hτ]
  field_simp
  ring

/-- `Continuous sig`: the logistic sigmoid is continuous on all of `ℝ`.
Uses `sig x = (1 + Real.exp (-x))⁻¹` with `one_add_exp_ne_zero`. -/
theorem continuous_sig : Continuous sig := by
  have hden : Continuous (fun x : ℝ => 1 + Real.exp (-x)) :=
    continuous_const.add (Real.continuous_exp.comp continuous_neg)
  exact hden.inv₀ (fun x => one_add_exp_ne_zero x)

/-- The error term `(c²·ρ̂)/τ` tends to `0` as `τ → ∞`. -/
theorem tendsto_dial_error_atTop {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (y : Fin d → ℝ) (c : ℝ) :
    Tendsto (fun τ : ℝ => (c ^ 2 * matrixBilin A y y) / τ) atTop (𝓝 0) :=
  tendsto_const_div_atTop

/-- `lem:dial` gate-argument limit.  The rescaled gate argument
`τ·q(w(τ), v(τ)) + b` tends to `c + b` as `τ → ∞`. -/
theorem tendsto_tau_mul_matrixBilin_dialPath_add {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (w0 v0 y : Fin d → ℝ) (c b : ℝ)
    (hq : matrixBilin A w0 v0 = 0)
    (hbracket : matrixBilin A w0 y - matrixBilin A y v0 = 1) :
    Tendsto
      (fun τ : ℝ =>
        τ * matrixBilin A (dialPath w0 v0 y c τ).1 (dialPath w0 v0 y c τ).2 + b)
      atTop (𝓝 (c + b)) := by
  -- The function eventually equals `(c + b) - (c²·ρ̂)/τ` on `atTop` (where `τ ≠ 0`).
  have heq :
      (fun τ : ℝ =>
          τ * matrixBilin A (dialPath w0 v0 y c τ).1 (dialPath w0 v0 y c τ).2 + b)
        =ᶠ[atTop]
        (fun τ : ℝ => (c + b) - (c ^ 2 * matrixBilin A y y) / τ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
    exact tau_mul_matrixBilin_dialPath_add A w0 v0 y c b hq hbracket hτ.ne'
  refine Tendsto.congr' heq.symm ?_
  have h := (tendsto_dial_error_atTop A y c).const_sub (c + b)
  simpa using h

/-- `lem:dial`(c), first-gate saturation (the payoff).  For `τ → ∞`,
`s₁(τ) = sig (τ·q(w(τ), v(τ)) + b)` converges to `sig (c + b)`. -/
theorem tendsto_sig_tau_mul_matrixBilin_dialPath_add {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (w0 v0 y : Fin d → ℝ) (c b : ℝ)
    (hq : matrixBilin A w0 v0 = 0)
    (hbracket : matrixBilin A w0 y - matrixBilin A y v0 = 1) :
    Tendsto
      (fun τ : ℝ =>
        sig (τ * matrixBilin A (dialPath w0 v0 y c τ).1
          (dialPath w0 v0 y c τ).2 + b))
      atTop (𝓝 (sig (c + b))) :=
  (continuous_sig.tendsto (c + b)).comp
    (tendsto_tau_mul_matrixBilin_dialPath_add A w0 v0 y c b hq hbracket)

end TransformerIdentifiability.NLayer
