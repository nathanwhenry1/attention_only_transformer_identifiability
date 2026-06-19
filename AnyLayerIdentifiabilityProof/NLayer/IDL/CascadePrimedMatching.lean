import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadePoint
import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeBridgeMatching
import AnyLayerIdentifiabilityProof.NLayer.Analytic.DialAsymptotics

set_option autoImplicit false

open Filter Topology Matrix

namespace TransformerIdentifiability.NLayer

/-!
# R2: the primed side of the trichotomy (genuine `Frec` convergence)

`prop:trichotomy`, primed side.  On the primed parameter every deeper limiting slope is
positive (`SignRegionData.primed_positive`), so every running gate saturates to `1` and the
closed recursion `Frec` converges to the *genuine* telescoped limit vector
`texMatchingPrimedTelescopedLimitVector` (TeX matching Step 2, `eq:limthetaprime`).

This is the easy side of the trichotomy: all `Λ > 0`, no rigidity needed.  The analytic
inputs are:
* the **dial first gate** converges to the free dial limit `δ.t` (`DialPathData.exact_identity`
  + `continuous_sig`), and
* every **deeper gate** saturates to `1` because the peeled limiting slope is positive
  (`SignRegionData.primed_positive`, rewritten through the R1b bridge
  `re_specializedPhi_eq_matrixBilin_peelPoint`).

These feed `CascadePoint.primed_gateLimits` → `frec_tendsto_of_gateLimits` →
`frecLimit_eq_texMatchingPrimedTelescopedLimitVector`.
-/

/-- The dial probe converges to its base point. -/
theorem tendsto_dialPathData_probe {L d : Nat} {θ' : Params (L + 1) d} {b : ℝ}
    (δ : DialPathData (Params.headAttention θ') b) :
    Tendsto δ.probe atTop (𝓝 δ.base) := by
  have hsmul : Tendsto (fun τ : ℝ => (δ.c / τ) • δ.y) atTop (𝓝 (0 : Fin d → ℝ)) :=
    tendsto_dialPath_smul_atTop δ.y δ.c
  have h1 : Tendsto (fun τ : ℝ => (δ.probe τ).1) atTop (𝓝 δ.base.1) := by
    have := (tendsto_const_nhds (x := δ.base.1)).sub hsmul
    simpa [DialPathData.probe, dialProbe, dialW] using this
  have h2 : Tendsto (fun τ : ℝ => (δ.probe τ).2) atTop (𝓝 δ.base.2) := by
    have := (tendsto_const_nhds (x := δ.base.2)).add hsmul
    simpa [DialPathData.probe, dialProbe, dialV] using this
  exact h1.prodMk_nhds h2

/-- The dial first gate of the primed recursion converges to the dial limit `δ.t`. -/
theorem tendsto_firstLayerGate_dialPathData {L d : Nat} {θ' : Params (L + 1) d}
    {r : Nat} (δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ))) :
    Tendsto
      (fun τ => firstLayerGate r (Params.headAttention θ') (δ.probe τ).1 (δ.probe τ).2 τ)
      atTop (𝓝 δ.t) := by
  -- the argument of the gate sigmoid converges to `δ.c + log r`
  have harg :
      Tendsto (fun τ : ℝ =>
          τ * matrixBilin (Params.headAttention θ') (δ.probe τ).1 (δ.probe τ).2
            + Real.log (r : ℝ))
        atTop (𝓝 (δ.c + Real.log (r : ℝ))) := by
    have heq :
        (fun τ : ℝ =>
          τ * matrixBilin (Params.headAttention θ') (δ.probe τ).1 (δ.probe τ).2
            + Real.log (r : ℝ))
          =ᶠ[atTop]
        (fun τ : ℝ =>
          δ.c + Real.log (r : ℝ)
            - δ.c ^ 2 * matrixBilin (Params.headAttention θ') δ.y δ.y / τ) := by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with τ hτ
      exact δ.exact_identity τ hτ
    have herr :
        Tendsto (fun τ : ℝ =>
          δ.c ^ 2 * matrixBilin (Params.headAttention θ') δ.y δ.y / τ) atTop (𝓝 0) :=
      tendsto_const_div_atTop
    have hlim :
        Tendsto (fun τ : ℝ =>
          δ.c + Real.log (r : ℝ)
            - δ.c ^ 2 * matrixBilin (Params.headAttention θ') δ.y δ.y / τ) atTop
          (𝓝 (δ.c + Real.log (r : ℝ))) := by
      simpa using (tendsto_const_nhds (x := δ.c + Real.log (r : ℝ))).sub herr
    exact hlim.congr' heq.symm
  have hsig :
      Tendsto (fun τ : ℝ =>
          sig (τ * matrixBilin (Params.headAttention θ') (δ.probe τ).1 (δ.probe τ).2
            + Real.log (r : ℝ)))
        atTop (𝓝 (sig (δ.c + Real.log (r : ℝ)))) :=
    (continuous_sig.tendsto _).comp harg
  rw [δ.c_targets_t] at hsig
  exact hsig

end TransformerIdentifiability.NLayer
