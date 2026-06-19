import AnyLayerIdentifiabilityProof.NLayer.Step1.PolynomialFamily
import AnyLayerIdentifiabilityProof.NLayer.Step1.TierSets

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Step 1 terminal-visible tier tower

This shard builds the *terminal-visible* nested tail tower used to close the genuine
last step of Claim B.

## Why this tower exists

The concrete formal-phi tower `step1FormalPhiPropagationPolynomialNestedTailData`
drives every gate blow-up, but its top step `step (L-1)` reads the out-of-range
attention matrix `(paramStream θ' L).2 = 0`, so its leading coefficient is identically
zero (`fixedOStar_concretePrimedTierSystem_boundary_stepLead_eq_zero`).  Hence the
concrete zero-free tier `T0 (L-1)` is empty and the concrete chain cannot reach a
nonempty terminal tier.

The TeX proof (`n_layer_proof.tex`, Claim B/C) instead controls the *visible*
coefficient `g = e_ι^T V'_L W'_{L-1}(z) w` at the top tier through the single combined
nested family `{f_2, …, f_L, g}`.  The existing combined product tower
`step1PropagationVisibleNestedTailData` multiplies the visible factor at **every**
level, which spoils the level-0 lead (`f_2 · g_1` can vanish), so its `T0 0` need not
equal `firstPoleSet`.

The terminal-visible tower is the formal-phi tower at every level **except**

* level `m = L - 2`, where the visible factor `g = step1VisiblePoly (L-1)` is
  multiplied in (so the level-`(L-2)` threshold also dominates `g`, giving `g ≠ 0` at the
  terminal tier through `eval_step1VisiblePoly_ne_zero_of_terminalVisibleZeroFreeRegion_succ`),
  and
* level `m = L - 1`, where the (otherwise zero) boundary polynomial is replaced by the
  constant `1` (so the terminal lead is the nonzero constant `1`).

The steps `0, …, L-3` are unchanged, so `zeroFreeRegion j` and the tier sets `T0 j`
agree with the formal-phi tower for `j ≤ L-3`.

## Why localizing the visible factor to one level is the WRONG construction

`g` is **multilinear**: `hasDominantTopCoeff_step1VisiblePoly` gives top monomial
`gateTop K K`, the all-ones monomial, so `g` has degree `1` in every variable.  Hence its
last-variable leading coefficient `(lastVariablePolynomial g).leadingCoeff`
(`step1TerminalVisible_stepLead_eq_mul_visible`) is **not** a constant for `L - 1 ≥ 2`:
it is itself multilinear with top coefficient `step1VisibleTailCoeff (L-2)`.  Consequently
the tier sets do **not** agree at the top interior level:
`T0 (L-2) = (formal-phi T0 (L-2)) ∩ {visible-lead ≠ 0}`, a strict subset, and the
visible-lead locus is not controlled by the formal-phi region.

The TeX proof (`n_layer_proof.tex`, `lem:nested`, lines 1336-1417) does **not** localize
the visible factor.  It forms the *single global product* `P = f_2 · … · f_L · g` and
builds the nested regions from `P`'s iterated leading coefficients
(`HasDominantTopCoeff.prod` + `HasDominantTopCoeff.leadingCoeff_finSuccEquiv`), each of
which keeps the *same* constant top coefficient `∏(-κ_j)·(visible top)` — nonzero from the
existing `O_star` genericity, with **no** intermediate visible coefficients needed.  So
the correct fix is the global-product iterated-lc tower (`step m` polynomial `= P_{m+1}`,
giving `lc(step m) = (step (m-1)).poly` and hence `leadingCoeff_ne_on_region` for free),
**not** the localization in this file.

This file is therefore retained only for its reusable factor / leading-coefficient lemmas
(`lastVariablePolynomial_leadingCoeff_step1TerminalVisibleTailPoly_visible`,
`formalPhiLead_ne_of_terminalVisible_stepLead_ne`), which the global-product construction
also uses.  See `../STEP_1_PLAN.md` (Progress 2026-06-17, "The wall is a formalization
artifact").
-/

/-- The terminal-visible tail polynomial at level `m` for depth `L`.

At `m = L - 2` the visible factor is multiplied in; at `m = L - 1` a nonzero constant is
used so the terminal lead does not vanish; elsewhere it is the formal-phi propagation
polynomial. -/
noncomputable def step1TerminalVisibleTailPoly {d : Nat} (L : Nat)
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (iota : Fin d) (m : Nat) : MvPolynomial (Fin (m + 1)) ℂ :=
  if m + 2 = L then
    step1FormalPhiPropagationTailPoly θ w v m * step1VisiblePoly (K := m + 1) θ w iota
  else if m + 1 = L then
    1
  else
    step1FormalPhiPropagationTailPoly θ w v m

/-- At the visible level `m = L - 2`, the terminal-visible polynomial is the formal-phi
propagation polynomial times the visible factor. -/
theorem step1TerminalVisibleTailPoly_eq_visible {d : Nat} (L : Nat)
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (iota : Fin d) {m : Nat}
    (hvis : m + 2 = L) :
    step1TerminalVisibleTailPoly L θ w v iota m =
      step1FormalPhiPropagationTailPoly θ w v m *
        step1VisiblePoly (K := m + 1) θ w iota := by
  unfold step1TerminalVisibleTailPoly
  rw [if_pos hvis]

/-- Polynomial-backed nested data for the terminal-visible tower. -/
noncomputable def step1TerminalVisibleNestedTailData {d : Nat} (L : Nat)
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (iota : Fin d) : PolynomialNestedTailData :=
  PolynomialNestedTailData.ofPolynomials
    (fun m => step1TerminalVisibleTailPoly L θ w v iota m)

@[simp]
theorem step1TerminalVisibleNestedTailData_tailData {d : Nat} (L : Nat)
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (iota : Fin d) (m : Nat) :
    (step1TerminalVisibleNestedTailData L θ w v iota).tailData m =
      PolynomialTailPresentationData.ofPolynomial
        (step1TerminalVisibleTailPoly L θ w v iota m) :=
  rfl

@[simp]
theorem step1TerminalVisibleNestedTailData_poly {d : Nat} (L : Nat)
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (iota : Fin d) (m : Nat) :
    ((step1TerminalVisibleNestedTailData L θ w v iota).tailData m).poly =
      step1TerminalVisibleTailPoly L θ w v iota m :=
  rfl

/-! ## Visible nonvanishing at the terminal tier

At the visible level `m = L - 2`, the tower's polynomial is the product
`φ'_{m+1} · g`, so membership of a length-`(m+1)` prefix in the zero-free region at
level `m + 1 = L - 1` makes the whole product nonzero, hence the visible factor `g`
nonzero.  This is the visible coefficient nonvanishing consumed by Claim C/D, now
sourced from the terminal-visible tower itself. -/
theorem eval_step1VisiblePoly_ne_zero_of_terminalVisibleZeroFreeRegion_succ {d : Nat}
    {L : Nat}
    {θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
    {w v : Fin d → ℝ} {iota : Fin d} {m : Nat} (hm : m + 2 = L)
    {z : Fin (m + 1) → ℂ}
    (hz : z ∈ (step1TerminalVisibleNestedTailData L θ w v iota).zeroFreeRegion (m + 1)) :
    MvPolynomial.eval z (step1VisiblePoly (K := m + 1) θ w iota) ≠ 0 := by
  have hprod_eval :
      MvPolynomial.eval z
        ((step1TerminalVisibleNestedTailData L θ w v iota).tailData m).poly ≠ 0 :=
    (step1TerminalVisibleNestedTailData L θ w v iota).zeroFreeRegion_eval_ne_zero_of_mem_succ
      (m := m) hz
  rw [step1TerminalVisibleNestedTailData_poly,
    step1TerminalVisibleTailPoly_eq_visible L θ w v iota hm,
    MvPolynomial.eval_mul] at hprod_eval
  exact (mul_ne_zero_iff.mp hprod_eval).2

/-! ## Leading-coefficient factorization at the visible level

At `m = L - 2` the terminal tower's step leading coefficient factors as the formal-phi
leading coefficient times the visible leading coefficient.  Because the visible factor
`g = step1VisiblePoly (m+1)` is *multilinear* — its top monomial `gateTop (m+1) (m+1)`
sends every variable to `1` (`hasDominantTopCoeff_step1VisiblePoly`) — the visible
leading coefficient `(lastVariablePolynomial g).leadingCoeff` is **not** a constant for
`m + 1 ≥ 2`; it is a multilinear polynomial in the lower variables whose own top
coefficient is `step1VisibleTailCoeff m`.  This is exactly why placing the visible factor
at a single level does not by itself collapse the visible nonvanishing into a constant:
each lower level still needs `step1VisibleTailCoeff K ≠ 0`. -/
theorem lastVariablePolynomial_leadingCoeff_step1TerminalVisibleTailPoly_visible {d : Nat}
    (L : Nat) (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (iota : Fin d) {m : Nat} (hm : m + 2 = L) :
    (lastVariablePolynomial (step1TerminalVisibleTailPoly L θ w v iota m)).leadingCoeff =
      (lastVariablePolynomial (step1FormalPhiPropagationTailPoly θ w v m)).leadingCoeff *
        (lastVariablePolynomial (step1VisiblePoly (K := m + 1) θ w iota)).leadingCoeff := by
  rw [step1TerminalVisibleTailPoly_eq_visible L θ w v iota hm, lastVariablePolynomial_mul,
    Polynomial.leadingCoeff_mul]

/-- The terminal tower's step leading-coefficient evaluator factors as the formal-phi
leading coefficient times the visible leading coefficient at the visible level. -/
theorem step1TerminalVisible_stepLead_eq_mul_visible {d : Nat} (L : Nat)
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (iota : Fin d) {m : Nat} (hm : m + 2 = L) (x : Fin m → ℂ) :
    ((step1TerminalVisibleNestedTailData L θ w v iota).tailData m).presentation.lead x =
      ((step1FormalPhiPropagationTailData θ w v m).presentation.lead x) *
        MvPolynomial.eval x
          (lastVariablePolynomial (step1VisiblePoly (K := m + 1) θ w iota)).leadingCoeff := by
  have hlhs :
      ((step1TerminalVisibleNestedTailData L θ w v iota).tailData m).presentation.lead x =
        MvPolynomial.eval x
          (lastVariablePolynomial (step1TerminalVisibleTailPoly L θ w v iota m)).leadingCoeff :=
    rfl
  have hrhs :
      (step1FormalPhiPropagationTailData θ w v m).presentation.lead x =
        MvPolynomial.eval x
          (lastVariablePolynomial (step1FormalPhiPropagationTailPoly θ w v m)).leadingCoeff :=
    rfl
  rw [hlhs, hrhs,
    lastVariablePolynomial_leadingCoeff_step1TerminalVisibleTailPoly_visible L θ w v iota hm,
    map_mul]

/-- From nonvanishing of the terminal tower's step lead at the visible level, recover the
formal-phi propagation leading coefficient — the input the concrete gate needs to blow
up.  No constancy of the visible factor is required: this is a pure product argument. -/
theorem formalPhiLead_ne_of_terminalVisible_stepLead_ne {d : Nat} (L : Nat)
    {θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
    {w v : Fin d → ℝ} {iota : Fin d} {m : Nat} (hm : m + 2 = L) {x : Fin m → ℂ}
    (h : ((step1TerminalVisibleNestedTailData L θ w v iota).tailData m).presentation.lead x ≠ 0) :
    (step1FormalPhiPropagationTailData θ w v m).presentation.lead x ≠ 0 := by
  rw [step1TerminalVisible_stepLead_eq_mul_visible L θ w v iota hm] at h
  exact (mul_ne_zero_iff.mp h).1

end TransformerIdentifiability.NLayer
