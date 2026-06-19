import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadePrimedMatching

set_option autoImplicit false

open Filter Topology Matrix

namespace TransformerIdentifiability.NLayer

/-!
# R3 (`Λ ≠ 0` branch): the unprimed saturated `Frec` convergence

This is the unprimed analogue of R2 (`CascadePrimedMatching`), for the `Λ ≠ 0` case of the
trichotomy (`prop:trichotomy`, Case 1).  Given that every deeper limiting slope of the
*unprimed* recursion is nonzero along the dial path, each running gate saturates to its sign
`1[Λ>0]`, and the closed recursion `Frec` converges to the **genuine** unprimed saturated
limit vector `texMatchingUnprimedSaturatedLimitVector θ (texMatchingSaturatedContributionMatrix
θ ς) δ.t δ.base` (TeX matching Step 1, `eq:limtheta`), where the saturation matrix `D` is
built from the *actual* per-level constants `ς`.

The first-layer gate uses the unprimed first attention `headAttention θ`; in the matching
context this equals the primed `headAttention θ'` (`FirstLayerEndpointData.attention_eq`), so
the dial first gate converges to the same dial limit `δ.t` as in R2.

The genuine `Λ ≡ 0` (`α`) branch needs the quadric-rigidity analysis (`lem:cascade`(b),
K2/K3) and is **not** covered here — see `CASCADE_PROGRESS.md` R3.
-/

/-- **R3 core (`Λ ≠ 0`).**  If the unprimed first attention matches the primed one
(`hAA`) and every deeper limiting slope is nonzero along the dial path, the unprimed `Frec`
converges to the genuine saturated limit vector. -/
theorem unprimed_frec_tendsto_of_slopeSigns {L d : Nat} (r : Nat) (θ θ' : Params (L + 1) d)
    (δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (ς : Nat -> ℝ) (hς0 : ς 0 = δ.t)
    (hsign :
      ∀ n : Nat, 1 ≤ n → n < L + 1 →
        matrixBilin (paramStream θ n).2
            (peelPoint (paramStream θ) ς n δ.base).1
            (peelPoint (paramStream θ) ς n δ.base).2 ≠ 0 ∧
          ς n =
            if 0 < matrixBilin (paramStream θ n).2
                (peelPoint (paramStream θ) ς n δ.base).1
                (peelPoint (paramStream θ) ς n δ.base).2 then 1 else 0) :
    Tendsto (fun τ => Frec r θ (δ.probe τ).1 (δ.probe τ).2 τ) atTop
      (𝓝 (texMatchingUnprimedSaturatedLimitVector θ
        (texMatchingSaturatedContributionMatrix θ ς) δ.t δ.base)) := by
  have hP : Tendsto δ.probe atTop (𝓝 δ.base) := tendsto_dialPathData_probe δ
  have hgate0 :
      Tendsto
        (fun τ => firstLayerGate r (Params.headAttention θ) (δ.probe τ).1 (δ.probe τ).2 τ)
        atTop (𝓝 δ.t) := by
    rw [hAA]; exact tendsto_firstLayerGate_dialPathData δ
  have hGL : GateLimits r θ δ.probe ς δ.base :=
    gateLimits_dialHead_of_slopeSigns r θ δ.probe δ.base δ.t ς hς0 hP hgate0 hsign
  have hfrec :=
    frec_tendsto_of_gateLimits r θ δ.probe ς δ.base hP hGL
  rw [frecLimit_eq_texMatchingUnprimedSaturatedLimitVector r θ ς δ.base, hς0] at hfrec
  exact hfrec

/-- The slope-sign hypothesis of `unprimed_frec_tendsto_of_slopeSigns` rephrased through the
R1b bridge `re_specializedPhi_eq_matrixBilin_peelPoint`: it suffices that the trichotomy's
specialised formal slope `(specializedPhi …).re` is nonzero with `ς` recording its sign.
This is the form the trichotomy (`prop:trichotomy`, Case 1) delivers. -/
theorem unprimed_frec_tendsto_of_specializedPhiSigns {L d : Nat} (r : Nat)
    (θ θ' : Params (L + 1) d)
    (δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (tail : Nat -> ℝ)
    (hsign :
      ∀ n : Nat, 1 ≤ n → n < L + 1 →
        (specializedPhi θ n (gateAssignmentOfTail δ.t tail) δ.base).re ≠ 0 ∧
          realGateOfTail δ.t tail n =
            if 0 < (specializedPhi θ n (gateAssignmentOfTail δ.t tail) δ.base).re
              then 1 else 0) :
    Tendsto (fun τ => Frec r θ (δ.probe τ).1 (δ.probe τ).2 τ) atTop
      (𝓝 (texMatchingUnprimedSaturatedLimitVector θ
        (texMatchingSaturatedContributionMatrix θ (realGateOfTail δ.t tail)) δ.t δ.base)) := by
  refine unprimed_frec_tendsto_of_slopeSigns r θ θ' δ hAA (realGateOfTail δ.t tail) rfl ?_
  intro n hn1 hnL
  have hbridge := re_specializedPhi_eq_matrixBilin_peelPoint θ n δ.t tail δ.base
  rw [← hbridge]
  exact hsign n hn1 hnL

end TransformerIdentifiability.NLayer
