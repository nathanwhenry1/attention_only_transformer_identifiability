import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeTrichotomyBuilder
import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeCanonicalTrichotomyMatching

set_option autoImplicit false

open Filter Topology Matrix

namespace TransformerIdentifiability.NLayer

/-!
# Builder-backed trichotomy construction surface

This module exposes the honest cascade builder as the trichotomy construction package
consumed by matching.  The actual branch data remains in `CascadeTrichotomyBuilder`;
this file only assembles the existing records and forwards the canonical matching
closed-recursion theorem.
-/

/-- Canonical unprimed actual gate saturation on a chosen subset of a sign region.

This is the subset-local form needed by `CascadeStepData`: prior saturation is only
assumed on the current cascade component `U0`, while the canonical dial construction
still uses the ambient sign-region data. -/
noncomputable def canonicalFrecGateAlongSignRegion_unprimed_saturates_of_nonzero_on_subset
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (U0 : Set (ProbePair d × ℝ)) (hU0 : U0 ⊆ signRegion.U)
    (level : Nat) (tail : Nat → ℝ)
    (hlevel_pos : 1 ≤ level) (hlevel_lt : level < L + 1)
    (hprior :
      ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n → n < level →
        EventuallyExpClose
          (fun τ : ℝ => canonicalFrecGateAlongSignRegion r signRegion θ n x τ)
          (tail (n - 1))) :
    ∀ x ∈ U0,
      specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1 ≠ 0 →
        EventuallyExpClose
          (fun τ : ℝ => canonicalFrecGateAlongSignRegion r signRegion θ level x τ)
          (if 0 < (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re
            then 1 else 0) := by
  intro x hxU0 hne
  have _hlevel_ne : level ≠ 0 := Nat.ne_of_gt hlevel_pos
  have hx : x ∈ signRegion.U := hU0 hxU0
  let δ :=
    DialPathData.ofRegularQuadric
      (Params.headAttention θ') (Real.log (r : ℝ)) x.1 x.2
      (signRegion.point_on_quadric x hx)
      (signRegion.point_regular x hx)
      (signRegion.t_pos hx)
      (signRegion.t_lt_one hx)
  have hP0 : Tendsto (DialPathData.probe δ) atTop (𝓝 x.1) := by
    have hPδ : Tendsto (DialPathData.probe δ) atTop (𝓝 δ.base) :=
      tendsto_dialPathData_probe δ
    simpa [δ, DialPathData.ofRegularQuadric] using hPδ
  have hgate0 :
      Tendsto
        (fun τ : ℝ =>
          firstLayerGate r (Params.headAttention θ) (δ.probe τ).1 (δ.probe τ).2 τ)
        atTop (𝓝 (realGateOfTail x.2 tail 0)) := by
    have h := tendsto_firstLayerGate_dialPathData δ
    rw [hAA]
    simpa [δ, DialPathData.ofRegularQuadric, realGateOfTail] using h
  have hPath :
      Tendsto
        (fun τ : ℝ => frecRunningPath r θ (DialPathData.probe δ) level τ)
        atTop
        (𝓝 (peelPoint (paramStream θ) (realGateOfTail x.2 tail) level x.1)) := by
    refine
      tendsto_frecRunningPath_of_prior_frecRunningGate r θ (DialPathData.probe δ)
        (realGateOfTail x.2 tail) x.1 level hP0 (Nat.le_of_lt hlevel_lt) ?_
    intro k hk
    cases k with
    | zero =>
        simpa [frecRunningGate] using hgate0
    | succ k =>
        have hk_pos : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
        have hclose := hprior x hxU0 (k + 1) hk_pos hk
        have htend :
            Tendsto
              (fun τ : ℝ => frecRunningGate r θ (DialPathData.probe δ) (k + 1) τ)
              atTop (𝓝 (tail k)) := by
          refine hclose.tendsto.congr' ?_
          filter_upwards with τ
          symm
          simp [canonicalFrecGateAlongSignRegion, δ, hx]
        simpa [realGateOfTail] using htend
  have hReNe :
      (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re ≠ 0 :=
    specializedPhi_gateAssignmentOfTail_re_ne_zero_of_ne θ level x.2 tail x.1 hne
  have hbridge :=
    re_specializedPhi_eq_matrixBilin_peelPoint θ level x.2 tail x.1
  by_cases hpos :
      0 < (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re
  · have hΛ :
        0 < matrixBilin (paramStream θ level).2
          (peelPoint (paramStream θ) (realGateOfTail x.2 tail) level x.1).1
          (peelPoint (paramStream θ) (realGateOfTail x.2 tail) level x.1).2 := by
      simpa [hbridge] using hpos
    have hfirst :
        EventuallyExpClose
          (fun τ : ℝ =>
            firstLayerGate r (paramStream θ level).2
              (frecRunningPath r θ (DialPathData.probe δ) level τ).1
              (frecRunningPath r θ (DialPathData.probe δ) level τ).2 τ)
          1 :=
      eventuallyExpClose_firstLayerGate_of_tendsto_pos r (paramStream θ level).2
        (fun τ : ℝ => frecRunningPath r θ (DialPathData.probe δ) level τ)
        (peelPoint (paramStream θ) (realGateOfTail x.2 tail) level x.1)
        hPath hΛ
    rw [if_pos hpos]
    refine hfirst.congr_of_forall_eq ?_ rfl
    intro τ
    rw [← frecRunningGate_eq_firstLayerGate_frecRunningPath r θ
      (DialPathData.probe δ) hlevel_lt τ]
    simp [canonicalFrecGateAlongSignRegion, δ, hx]
  · have hneg :
        (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re < 0 := by
      exact lt_of_le_of_ne (le_of_not_gt hpos) hReNe
    have hΛ :
        matrixBilin (paramStream θ level).2
          (peelPoint (paramStream θ) (realGateOfTail x.2 tail) level x.1).1
          (peelPoint (paramStream θ) (realGateOfTail x.2 tail) level x.1).2 < 0 := by
      simpa [hbridge] using hneg
    have hfirst :
        EventuallyExpClose
          (fun τ : ℝ =>
            firstLayerGate r (paramStream θ level).2
              (frecRunningPath r θ (DialPathData.probe δ) level τ).1
              (frecRunningPath r θ (DialPathData.probe δ) level τ).2 τ)
          0 :=
      eventuallyExpClose_firstLayerGate_of_tendsto_neg r (paramStream θ level).2
        (fun τ : ℝ => frecRunningPath r θ (DialPathData.probe δ) level τ)
        (peelPoint (paramStream θ) (realGateOfTail x.2 tail) level x.1)
        hPath hΛ
    rw [if_neg hpos]
    refine hfirst.congr_of_forall_eq ?_ rfl
    intro τ
    rw [← frecRunningGate_eq_firstLayerGate_frecRunningPath r θ
      (DialPathData.probe δ) hlevel_lt τ]
    simp [canonicalFrecGateAlongSignRegion, δ, hx]

/-- Build the one-level cascade step for the canonical unprimed actual gate on a
current component of a sign region. -/
noncomputable def cascadeStepData_of_canonicalFrecGateAlongSignRegion
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (A : Matrix (Fin d) (Fin d) ℝ)
    (U0 : Set (ProbePair d × ℝ)) (hU0 : U0 ⊆ signRegion.U)
    (level : Nat) (tail : Nat -> ℝ)
    (hlevel_pos : 1 ≤ level) (hlevel_lt : level < L + 1)
    (prior_saturates :
      ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n -> n < level ->
        EventuallyExpClose
          (fun τ => canonicalFrecGateAlongSignRegion r signRegion θ n x τ)
          (tail (n - 1)))
    (provider : CascadeCurveRigidityProvider θ A level tail) :
    CascadeStepData θ A U0 level tail
      (canonicalFrecGateAlongSignRegion r signRegion θ) :=
  CascadeStepData.ofZeroBranchProvider
    (θ := θ) (A := A) (U0 := U0) (level := level) (tail := tail)
    (unprimed := canonicalFrecGateAlongSignRegion r signRegion θ)
    hlevel_pos hlevel_lt prior_saturates
    (canonicalFrecGateAlongSignRegion_unprimed_saturates_of_nonzero_on_subset
      signRegion hAA U0 hU0 level tail hlevel_pos hlevel_lt prior_saturates)
    provider

/-- Conditional-provider variant of
`cascadeStepData_of_canonicalFrecGateAlongSignRegion`.  The curve-rigidity provider is
only requested when the zero-slope branch is actually entered. -/
noncomputable def
    cascadeStepData_of_canonicalFrecGateAlongSignRegion_conditionalZeroBranchProvider
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (A : Matrix (Fin d) (Fin d) ℝ)
    (U0 : Set (ProbePair d × ℝ)) (hU0 : U0 ⊆ signRegion.U)
    (level : Nat) (tail : Nat -> ℝ)
    (hlevel_pos : 1 ≤ level) (hlevel_lt : level < L + 1)
    (prior_saturates :
      ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n -> n < level ->
        EventuallyExpClose
          (fun τ => canonicalFrecGateAlongSignRegion r signRegion θ n x τ)
          (tail (n - 1)))
    (provider :
      (∀ x ∈ U0,
        specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1 = 0) ->
      CascadeCurveRigidityProvider θ A level tail) :
    CascadeStepData θ A U0 level tail
      (canonicalFrecGateAlongSignRegion r signRegion θ) :=
  CascadeStepData.ofConditionalZeroBranchProvider
    (θ := θ) (A := A) (U0 := U0) (level := level) (tail := tail)
    (unprimed := canonicalFrecGateAlongSignRegion r signRegion θ)
    hlevel_pos hlevel_lt prior_saturates
    (canonicalFrecGateAlongSignRegion_unprimed_saturates_of_nonzero_on_subset
      signRegion hAA U0 hU0 level tail hlevel_pos hlevel_lt prior_saturates)
    provider

/-- Zero-alpha branch source for the canonical unprimed actual gate on a sign-region
component. -/
noncomputable def cascadeLevelBranchSource_zeroAlpha_of_canonicalFrecGateAlongSignRegion
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (A : Matrix (Fin d) (Fin d) ℝ)
    (Ustar U0 : Set (ProbePair d × ℝ))
    (hU0 : U0 ⊆ signRegion.U) (hUstar : Ustar ⊆ U0)
    {levelPred : Nat} (tail : Nat -> ℝ)
    (hlevel_lt : levelPred + 1 < L + 1)
    (prior_saturates :
      ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n -> n < levelPred + 1 ->
        EventuallyExpClose
          (fun τ => canonicalFrecGateAlongSignRegion r signRegion θ n x τ)
          (tail (n - 1)))
    (provider : CascadeCurveRigidityProvider θ A (levelPred + 1) tail)
    (slope_zero_on_current :
      ∀ x ∈ U0,
        specializedPhi θ (levelPred + 1) (gateAssignmentOfTail x.2 tail) x.1 = 0)
    (dimension_pos : 0 < d)
    (head_det_ne_zero : A.det ≠ 0)
    (head_sym_ne_zero : symPart A ≠ 0)
    (head_value_ne_zero : (paramStream θ 0).1 ≠ 0) :
    CascadeLevelBranchSource (Real.log (r : ℝ)) θ A Ustar
      (canonicalFrecGateAlongSignRegion r signRegion θ) (levelPred + 1)
      (sig (Real.log (r : ℝ))) :=
  CascadeLevelBranchSource.ofZeroAlphaStep
    (b := Real.log (r : ℝ)) (θ := θ) (A := A) (Ustar := Ustar)
    (unprimed := canonicalFrecGateAlongSignRegion r signRegion θ)
    (levelPred := levelPred) (tail := tail)
    (cascadeStepData_of_canonicalFrecGateAlongSignRegion
      signRegion hAA A U0 hU0 (levelPred + 1) tail
      (Nat.succ_le_succ (Nat.zero_le levelPred)) hlevel_lt prior_saturates provider)
    hUstar
    (by
      intro x hx
      change specializedPhi θ (levelPred + 1) (gateAssignmentOfTail x.2 tail) x.1 = 0
      exact slope_zero_on_current x hx)
    dimension_pos head_det_ne_zero head_sym_ne_zero head_value_ne_zero
    (canonicalFrecHeadGateAlongSignRegion r signRegion θ)
    (canonicalDialProbeAlongSignRegion r signRegion)
    (canonicalAlphaSlopeAlongSignRegion r signRegion θ (levelPred + 1) tail)
    (by
      intro x hx τ
      exact
        canonicalFrecGateAlongSignRegion_eq_sig_alphaSlope
          signRegion (Nat.succ_le_succ (Nat.zero_le levelPred)) hlevel_lt tail
          x (hU0 (hUstar hx)) τ)
    (canonicalFrecGateAlongSignRegion_alphaSlopeErrorBound
      signRegion A Ustar (fun x hx => hU0 (hUstar hx)) (levelPred + 1) tail)

/-- Conditional-provider variant of the canonical zero-alpha branch source. -/
noncomputable def
    cascadeLevelBranchSource_zeroAlpha_of_canonicalFrecGateAlongSignRegion_conditionalZeroBranchProvider
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (A : Matrix (Fin d) (Fin d) ℝ)
    (Ustar U0 : Set (ProbePair d × ℝ))
    (hU0 : U0 ⊆ signRegion.U) (hUstar : Ustar ⊆ U0)
    {levelPred : Nat} (tail : Nat -> ℝ)
    (hlevel_lt : levelPred + 1 < L + 1)
    (prior_saturates :
      ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n -> n < levelPred + 1 ->
        EventuallyExpClose
          (fun τ => canonicalFrecGateAlongSignRegion r signRegion θ n x τ)
          (tail (n - 1)))
    (provider :
      (∀ x ∈ U0,
        specializedPhi θ (levelPred + 1) (gateAssignmentOfTail x.2 tail) x.1 = 0) ->
      CascadeCurveRigidityProvider θ A (levelPred + 1) tail)
    (slope_zero_on_current :
      ∀ x ∈ U0,
        specializedPhi θ (levelPred + 1) (gateAssignmentOfTail x.2 tail) x.1 = 0)
    (dimension_pos : 0 < d)
    (head_det_ne_zero : A.det ≠ 0)
    (head_sym_ne_zero : symPart A ≠ 0)
    (head_value_ne_zero : (paramStream θ 0).1 ≠ 0) :
    CascadeLevelBranchSource (Real.log (r : ℝ)) θ A Ustar
      (canonicalFrecGateAlongSignRegion r signRegion θ) (levelPred + 1)
      (sig (Real.log (r : ℝ))) :=
  CascadeLevelBranchSource.ofZeroAlphaStep
    (b := Real.log (r : ℝ)) (θ := θ) (A := A) (Ustar := Ustar)
    (unprimed := canonicalFrecGateAlongSignRegion r signRegion θ)
    (levelPred := levelPred) (tail := tail)
    (cascadeStepData_of_canonicalFrecGateAlongSignRegion_conditionalZeroBranchProvider
      signRegion hAA A U0 hU0 (levelPred + 1) tail
      (Nat.succ_le_succ (Nat.zero_le levelPred)) hlevel_lt prior_saturates provider)
    hUstar
    (by
      intro x hx
      exact slope_zero_on_current x hx)
    dimension_pos head_det_ne_zero head_sym_ne_zero head_value_ne_zero
    (canonicalFrecHeadGateAlongSignRegion r signRegion θ)
    (canonicalDialProbeAlongSignRegion r signRegion)
    (canonicalAlphaSlopeAlongSignRegion r signRegion θ (levelPred + 1) tail)
    (by
      intro x hx τ
      exact
        canonicalFrecGateAlongSignRegion_eq_sig_alphaSlope
          signRegion (Nat.succ_le_succ (Nat.zero_le levelPred)) hlevel_lt tail
          x (hU0 (hUstar hx)) τ)
    (canonicalFrecGateAlongSignRegion_alphaSlopeErrorBound
      signRegion A Ustar (fun x hx => hU0 (hUstar hx)) (levelPred + 1) tail)

/-- Nonzero branch source for the canonical unprimed actual gate on a sign-region
component. -/
noncomputable def cascadeLevelBranchSource_nonzero_of_canonicalFrecGateAlongSignRegion
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (A : Matrix (Fin d) (Fin d) ℝ)
    (Ustar U0 : Set (ProbePair d × ℝ))
    (hU0 : U0 ⊆ signRegion.U)
    (level : Nat) (tail : Nat -> ℝ)
    (hlevel_pos : 1 ≤ level) (hlevel_lt : level < L + 1)
    (prior_saturates :
      ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n -> n < level ->
        EventuallyExpClose
          (fun τ => canonicalFrecGateAlongSignRegion r signRegion θ n x τ)
          (tail (n - 1)))
    (provider : CascadeCurveRigidityProvider θ A level tail)
    (U1 : Set (ProbePair d × ℝ))
    (U1_subset_current : U1 ⊆ U0)
    (Ustar_subset_component : Ustar ⊆ U1)
    (component_nonempty : U1.Nonempty)
    (component_relatively_open_in_current :
      ∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ U1 = W ∩ U0)
    (component_connected : IsPreconnected U1)
    (slope_nonzero :
      ∀ x ∈ U1,
        specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1 ≠ 0)
    (selected : ℝ)
    (selected_zero_or_one : selected = 0 ∨ selected = 1)
    (selected_matches_slope :
      ∀ x ∈ U1,
        (if 0 < (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re
          then 1 else 0) = selected) :
    CascadeLevelBranchSource (Real.log (r : ℝ)) θ A Ustar
      (canonicalFrecGateAlongSignRegion r signRegion θ) level selected :=
  CascadeLevelBranchSource.ofNonzeroStep
    (b := Real.log (r : ℝ)) (θ := θ) (A := A) (Ustar := Ustar)
    (unprimed := canonicalFrecGateAlongSignRegion r signRegion θ)
    (level := level) (tail := tail)
    (cascadeStepData_of_canonicalFrecGateAlongSignRegion
      signRegion hAA A U0 hU0 level tail hlevel_pos hlevel_lt
      prior_saturates provider)
    U1 U1_subset_current Ustar_subset_component component_nonempty
    component_relatively_open_in_current component_connected
    (by
      intro x hx
      change specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1 ≠ 0
      exact slope_nonzero x hx)
    selected selected_zero_or_one
    (by
      intro x hx
      change
        (if 0 < (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re
          then 1 else 0) = selected
      exact selected_matches_slope x hx)

/-- Nonzero branch source variant that needs no zero-branch provider.  A zero-slope
hypothesis on the whole current component contradicts nonzero slope on the selected
nonempty subcomponent. -/
noncomputable def
    cascadeLevelBranchSource_nonzero_of_canonicalFrecGateAlongSignRegion_noZeroBranchProvider
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (A : Matrix (Fin d) (Fin d) ℝ)
    (Ustar U0 : Set (ProbePair d × ℝ))
    (hU0 : U0 ⊆ signRegion.U)
    (level : Nat) (tail : Nat -> ℝ)
    (hlevel_pos : 1 ≤ level) (hlevel_lt : level < L + 1)
    (prior_saturates :
      ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n -> n < level ->
        EventuallyExpClose
          (fun τ => canonicalFrecGateAlongSignRegion r signRegion θ n x τ)
          (tail (n - 1)))
    (U1 : Set (ProbePair d × ℝ))
    (U1_subset_current : U1 ⊆ U0)
    (Ustar_subset_component : Ustar ⊆ U1)
    (component_nonempty : U1.Nonempty)
    (component_relatively_open_in_current :
      ∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ U1 = W ∩ U0)
    (component_connected : IsPreconnected U1)
    (slope_nonzero :
      ∀ x ∈ U1,
        specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1 ≠ 0)
    (selected : ℝ)
    (selected_zero_or_one : selected = 0 ∨ selected = 1)
    (selected_matches_slope :
      ∀ x ∈ U1,
        (if 0 < (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re
          then 1 else 0) = selected) :
    CascadeLevelBranchSource (Real.log (r : ℝ)) θ A Ustar
      (canonicalFrecGateAlongSignRegion r signRegion θ) level selected :=
  CascadeLevelBranchSource.ofNonzeroStep
    (b := Real.log (r : ℝ)) (θ := θ) (A := A) (Ustar := Ustar)
    (unprimed := canonicalFrecGateAlongSignRegion r signRegion θ)
    (level := level) (tail := tail)
    (cascadeStepData_of_canonicalFrecGateAlongSignRegion_conditionalZeroBranchProvider
      signRegion hAA A U0 hU0 level tail hlevel_pos hlevel_lt
      prior_saturates
      (by
        intro hzero
        let x : ProbePair d × ℝ := Classical.choose component_nonempty
        have hx : x ∈ U1 := Classical.choose_spec component_nonempty
        exact False.elim ((slope_nonzero x hx) (hzero x (U1_subset_current hx)))))
    U1 U1_subset_current Ustar_subset_component component_nonempty
    component_relatively_open_in_current component_connected
    (by
      intro x hx
      change specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1 ≠ 0
      exact slope_nonzero x hx)
    selected selected_zero_or_one
    (by
      intro x hx
      change
        (if 0 < (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re
          then 1 else 0) = selected
      exact selected_matches_slope x hx)

/-- Zero-alpha branch choice for the canonical unprimed actual gate, preserving the
current cascade component. -/
noncomputable def cascadeLevelBranchChoice_zeroAlpha_of_canonicalFrecGateAlongSignRegion
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion : SignRegionData (L := L + 1) (d := d) θ' O
      (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (A : Matrix (Fin d) (Fin d) ℝ)
    (U0 : Set (ProbePair d × ℝ))
    (hU0 : U0 ⊆ signRegion.U)
    (U0_nonempty : U0.Nonempty)
    (U0_connected : IsPreconnected U0)
    {levelPred : Nat} (tail : Nat -> ℝ)
    (hlevel_lt : levelPred + 1 < L + 1)
    (prior_saturates : ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n -> n < levelPred + 1 ->
      EventuallyExpClose
        (fun τ => canonicalFrecGateAlongSignRegion r signRegion θ n x τ)
        (tail (n - 1)))
    (provider : CascadeCurveRigidityProvider θ A (levelPred + 1) tail)
    (slope_zero_on_current : ∀ x ∈ U0,
      specializedPhi θ (levelPred + 1) (gateAssignmentOfTail x.2 tail) x.1 = 0)
    (dimension_pos : 0 < d)
    (head_det_ne_zero : A.det ≠ 0)
    (head_sym_ne_zero : symPart A ≠ 0)
    (head_value_ne_zero : (paramStream θ 0).1 ≠ 0) :
    CascadeLevelBranchChoice (Real.log (r : ℝ)) θ A U0
      (canonicalFrecGateAlongSignRegion r signRegion θ) (levelPred + 1) tail where
  Unext := U0
  Unext_subset_current := fun _ hx => hx
  nonempty := U0_nonempty
  relatively_open_in_current := by
    refine ⟨Set.univ, isOpen_univ, ?_⟩
    ext x
    simp
  connected := U0_connected
  value := sig (Real.log (r : ℝ))
  source_on_subset := by
    intro Ufinal hUfinal
    exact
      cascadeLevelBranchSource_zeroAlpha_of_canonicalFrecGateAlongSignRegion
        signRegion hAA A Ufinal U0 hU0 hUfinal tail hlevel_lt
        prior_saturates provider slope_zero_on_current dimension_pos
        head_det_ne_zero head_sym_ne_zero head_value_ne_zero

/-- Conditional-provider variant of the canonical zero-alpha branch choice. -/
noncomputable def
    cascadeLevelBranchChoice_zeroAlpha_of_canonicalFrecGateAlongSignRegion_conditionalZeroBranchProvider
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion : SignRegionData (L := L + 1) (d := d) θ' O
      (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (A : Matrix (Fin d) (Fin d) ℝ)
    (U0 : Set (ProbePair d × ℝ))
    (hU0 : U0 ⊆ signRegion.U)
    (U0_nonempty : U0.Nonempty)
    (U0_connected : IsPreconnected U0)
    {levelPred : Nat} (tail : Nat -> ℝ)
    (hlevel_lt : levelPred + 1 < L + 1)
    (prior_saturates : ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n -> n < levelPred + 1 ->
      EventuallyExpClose
        (fun τ => canonicalFrecGateAlongSignRegion r signRegion θ n x τ)
        (tail (n - 1)))
    (provider :
      (∀ x ∈ U0,
        specializedPhi θ (levelPred + 1) (gateAssignmentOfTail x.2 tail) x.1 = 0) ->
      CascadeCurveRigidityProvider θ A (levelPred + 1) tail)
    (slope_zero_on_current : ∀ x ∈ U0,
      specializedPhi θ (levelPred + 1) (gateAssignmentOfTail x.2 tail) x.1 = 0)
    (dimension_pos : 0 < d)
    (head_det_ne_zero : A.det ≠ 0)
    (head_sym_ne_zero : symPart A ≠ 0)
    (head_value_ne_zero : (paramStream θ 0).1 ≠ 0) :
    CascadeLevelBranchChoice (Real.log (r : ℝ)) θ A U0
      (canonicalFrecGateAlongSignRegion r signRegion θ) (levelPred + 1) tail where
  Unext := U0
  Unext_subset_current := fun _ hx => hx
  nonempty := U0_nonempty
  relatively_open_in_current := by
    refine ⟨Set.univ, isOpen_univ, ?_⟩
    ext x
    simp
  connected := U0_connected
  value := sig (Real.log (r : ℝ))
  source_on_subset := by
    intro Ufinal hUfinal
    exact
      cascadeLevelBranchSource_zeroAlpha_of_canonicalFrecGateAlongSignRegion_conditionalZeroBranchProvider
        signRegion hAA A Ufinal U0 hU0 hUfinal tail hlevel_lt
        prior_saturates provider slope_zero_on_current dimension_pos
        head_det_ne_zero head_sym_ne_zero head_value_ne_zero

/-- Nonzero branch choice for the canonical unprimed actual gate from an already
selected local component and constant sign. -/
noncomputable def cascadeLevelBranchChoice_nonzero_of_canonicalFrecGateAlongSignRegion
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion : SignRegionData (L := L + 1) (d := d) θ' O
      (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (A : Matrix (Fin d) (Fin d) ℝ)
    (U0 : Set (ProbePair d × ℝ))
    (hU0 : U0 ⊆ signRegion.U)
    (level : Nat) (tail : Nat -> ℝ)
    (hlevel_pos : 1 ≤ level) (hlevel_lt : level < L + 1)
    (prior_saturates : ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n -> n < level ->
      EventuallyExpClose
        (fun τ => canonicalFrecGateAlongSignRegion r signRegion θ n x τ)
        (tail (n - 1)))
    (provider : CascadeCurveRigidityProvider θ A level tail)
    (U1 : Set (ProbePair d × ℝ))
    (U1_subset_current : U1 ⊆ U0)
    (component_nonempty : U1.Nonempty)
    (component_relatively_open_in_current :
      ∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ U1 = W ∩ U0)
    (component_connected : IsPreconnected U1)
    (slope_nonzero : ∀ x ∈ U1,
      specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1 ≠ 0)
    (selected : ℝ)
    (selected_zero_or_one : selected = 0 ∨ selected = 1)
    (selected_matches_slope : ∀ x ∈ U1,
      (if 0 < (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re
        then 1 else 0) = selected) :
    CascadeLevelBranchChoice (Real.log (r : ℝ)) θ A U0
      (canonicalFrecGateAlongSignRegion r signRegion θ) level tail where
  Unext := U1
  Unext_subset_current := U1_subset_current
  nonempty := component_nonempty
  relatively_open_in_current := component_relatively_open_in_current
  connected := component_connected
  value := selected
  source_on_subset := by
    intro Ufinal hUfinal
    exact
      cascadeLevelBranchSource_nonzero_of_canonicalFrecGateAlongSignRegion
        signRegion hAA A Ufinal U0 hU0 level tail hlevel_pos hlevel_lt
        prior_saturates provider U1 U1_subset_current hUfinal component_nonempty
        component_relatively_open_in_current component_connected slope_nonzero
        selected selected_zero_or_one selected_matches_slope

/-- Nonzero branch choice variant that needs no zero-branch provider. -/
noncomputable def
    cascadeLevelBranchChoice_nonzero_of_canonicalFrecGateAlongSignRegion_noZeroBranchProvider
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion : SignRegionData (L := L + 1) (d := d) θ' O
      (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (A : Matrix (Fin d) (Fin d) ℝ)
    (U0 : Set (ProbePair d × ℝ))
    (hU0 : U0 ⊆ signRegion.U)
    (level : Nat) (tail : Nat -> ℝ)
    (hlevel_pos : 1 ≤ level) (hlevel_lt : level < L + 1)
    (prior_saturates : ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n -> n < level ->
      EventuallyExpClose
        (fun τ => canonicalFrecGateAlongSignRegion r signRegion θ n x τ)
        (tail (n - 1)))
    (U1 : Set (ProbePair d × ℝ))
    (U1_subset_current : U1 ⊆ U0)
    (component_nonempty : U1.Nonempty)
    (component_relatively_open_in_current :
      ∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ U1 = W ∩ U0)
    (component_connected : IsPreconnected U1)
    (slope_nonzero : ∀ x ∈ U1,
      specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1 ≠ 0)
    (selected : ℝ)
    (selected_zero_or_one : selected = 0 ∨ selected = 1)
    (selected_matches_slope : ∀ x ∈ U1,
      (if 0 < (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re
        then 1 else 0) = selected) :
    CascadeLevelBranchChoice (Real.log (r : ℝ)) θ A U0
      (canonicalFrecGateAlongSignRegion r signRegion θ) level tail where
  Unext := U1
  Unext_subset_current := U1_subset_current
  nonempty := component_nonempty
  relatively_open_in_current := component_relatively_open_in_current
  connected := component_connected
  value := selected
  source_on_subset := by
    intro Ufinal hUfinal
    exact
      cascadeLevelBranchSource_nonzero_of_canonicalFrecGateAlongSignRegion_noZeroBranchProvider
        signRegion hAA A Ufinal U0 hU0 level tail hlevel_pos hlevel_lt
        prior_saturates U1 U1_subset_current hUfinal component_nonempty
        component_relatively_open_in_current component_connected slope_nonzero
        selected selected_zero_or_one selected_matches_slope

/-- Nonzero branch choice for the canonical unprimed actual gate, built directly
from a point-local sign neighborhood while preserving the selected component
topology. -/
noncomputable def
    cascadeLevelBranchChoice_nonzero_of_canonicalFrecGateAlongSignRegion_point
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion : SignRegionData (L := L + 1) (d := d) θ' O
      (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (A : Matrix (Fin d) (Fin d) ℝ)
    (U0 : Set (ProbePair d × ℝ))
    (hU0 : U0 ⊆ signRegion.U)
    (x0 : ProbePair d × ℝ)
    (level : Nat) (tail : Nat -> ℝ)
    (hlevel_pos : 1 ≤ level) (hlevel_lt : level < L + 1)
    (prior_saturates : ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n -> n < level ->
      EventuallyExpClose
        (fun τ => canonicalFrecGateAlongSignRegion r signRegion θ n x τ)
        (tail (n - 1)))
    (provider : CascadeCurveRigidityProvider θ A level tail)
    (localSignNeighborhood :
      ∃ U1 : Set (ProbePair d × ℝ),
        x0 ∈ U1 ∧
        U1 ⊆ U0 ∧
        (∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ U1 = W ∩ U0) ∧
        U1.Nonempty ∧
        IsPreconnected U1 ∧
        (∀ x ∈ U1,
          (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re ≠ 0) ∧
        ((∀ x ∈ U1,
          0 < (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re) ∨
         (∀ x ∈ U1,
          (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re < 0))) :
    CascadeLevelBranchChoice (Real.log (r : ℝ)) θ A U0
      (canonicalFrecGateAlongSignRegion r signRegion θ) level tail := by
  classical
  let U1 : Set (ProbePair d × ℝ) := Classical.choose localSignNeighborhood
  have hlocal :
      x0 ∈ U1 ∧
      U1 ⊆ U0 ∧
      (∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ U1 = W ∩ U0) ∧
      U1.Nonempty ∧
      IsPreconnected U1 ∧
      (∀ x ∈ U1,
        (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re ≠ 0) ∧
      ((∀ x ∈ U1,
        0 < (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re) ∨
       (∀ x ∈ U1,
        (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re < 0)) := by
    simpa [U1] using Classical.choose_spec localSignNeighborhood
  rcases hlocal with
    ⟨_hx0_U1, hU1_subset_U0, hU1_rel_open, hU1_nonempty,
      hU1_preconnected, hU1_re_ne, hU1_sign⟩
  have slope_nonzero :
      ∀ x ∈ U1,
        specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1 ≠ 0 := by
    intro x hxU1 hzero
    have hre_ne :
        (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re ≠ 0 := by
      exact hU1_re_ne x hxU1
    apply hre_ne
    simp [hzero]
  by_cases hU1_pos :
      ∀ x ∈ U1,
        0 < (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re
  · exact
      cascadeLevelBranchChoice_nonzero_of_canonicalFrecGateAlongSignRegion
        signRegion hAA A U0 hU0 level tail hlevel_pos hlevel_lt
        prior_saturates provider U1 hU1_subset_U0 hU1_nonempty
        hU1_rel_open hU1_preconnected slope_nonzero 1 (Or.inr rfl)
        (by
          intro x hxU1
          have hpos :
              0 <
                (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re := by
            exact hU1_pos x hxU1
          exact if_pos hpos)
  · have hU1_neg :
        ∀ x ∈ U1,
          (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re < 0 := by
      rcases hU1_sign with hpos | hneg
      · exact False.elim (hU1_pos hpos)
      · exact hneg
    exact
      cascadeLevelBranchChoice_nonzero_of_canonicalFrecGateAlongSignRegion
        signRegion hAA A U0 hU0 level tail hlevel_pos hlevel_lt
        prior_saturates provider U1 hU1_subset_U0 hU1_nonempty
        hU1_rel_open hU1_preconnected slope_nonzero 0 (Or.inl rfl)
        (by
          intro x hxU1
          have hneg :
              (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re < 0 := by
            exact hU1_neg x hxU1
          exact if_neg (not_lt_of_ge (le_of_lt hneg)))

/-- Providerless variant of
`cascadeLevelBranchChoice_nonzero_of_canonicalFrecGateAlongSignRegion_point`. -/
noncomputable def
    cascadeLevelBranchChoice_nonzero_of_canonicalFrecGateAlongSignRegion_point_noZeroBranchProvider
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion : SignRegionData (L := L + 1) (d := d) θ' O
      (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (A : Matrix (Fin d) (Fin d) ℝ)
    (U0 : Set (ProbePair d × ℝ))
    (hU0 : U0 ⊆ signRegion.U)
    (x0 : ProbePair d × ℝ)
    (level : Nat) (tail : Nat -> ℝ)
    (hlevel_pos : 1 ≤ level) (hlevel_lt : level < L + 1)
    (prior_saturates : ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n -> n < level ->
      EventuallyExpClose
        (fun τ => canonicalFrecGateAlongSignRegion r signRegion θ n x τ)
        (tail (n - 1)))
    (localSignNeighborhood :
      ∃ U1 : Set (ProbePair d × ℝ),
        x0 ∈ U1 ∧
        U1 ⊆ U0 ∧
        (∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ U1 = W ∩ U0) ∧
        U1.Nonempty ∧
        IsPreconnected U1 ∧
        (∀ x ∈ U1,
          (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re ≠ 0) ∧
        ((∀ x ∈ U1,
          0 < (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re) ∨
         (∀ x ∈ U1,
          (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re < 0))) :
    CascadeLevelBranchChoice (Real.log (r : ℝ)) θ A U0
      (canonicalFrecGateAlongSignRegion r signRegion θ) level tail := by
  classical
  let U1 : Set (ProbePair d × ℝ) := Classical.choose localSignNeighborhood
  have hlocal :
      x0 ∈ U1 ∧
      U1 ⊆ U0 ∧
      (∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ U1 = W ∩ U0) ∧
      U1.Nonempty ∧
      IsPreconnected U1 ∧
      (∀ x ∈ U1,
        (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re ≠ 0) ∧
      ((∀ x ∈ U1,
        0 < (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re) ∨
       (∀ x ∈ U1,
        (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re < 0)) := by
    simpa [U1] using Classical.choose_spec localSignNeighborhood
  rcases hlocal with
    ⟨_hx0_U1, hU1_subset_U0, hU1_rel_open, hU1_nonempty,
      hU1_preconnected, hU1_re_ne, hU1_sign⟩
  have slope_nonzero :
      ∀ x ∈ U1,
        specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1 ≠ 0 := by
    intro x hxU1 hzero
    have hre_ne :
        (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re ≠ 0 := by
      exact hU1_re_ne x hxU1
    apply hre_ne
    simp [hzero]
  by_cases hU1_pos :
      ∀ x ∈ U1,
        0 < (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re
  · exact
      cascadeLevelBranchChoice_nonzero_of_canonicalFrecGateAlongSignRegion_noZeroBranchProvider
        signRegion hAA A U0 hU0 level tail hlevel_pos hlevel_lt
        prior_saturates U1 hU1_subset_U0 hU1_nonempty
        hU1_rel_open hU1_preconnected slope_nonzero 1 (Or.inr rfl)
        (by
          intro x hxU1
          have hpos :
              0 <
                (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re := by
            exact hU1_pos x hxU1
          exact if_pos hpos)
  · have hU1_neg :
        ∀ x ∈ U1,
          (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re < 0 := by
      rcases hU1_sign with hpos | hneg
      · exact False.elim (hU1_pos hpos)
      · exact hneg
    exact
      cascadeLevelBranchChoice_nonzero_of_canonicalFrecGateAlongSignRegion_noZeroBranchProvider
        signRegion hAA A U0 hU0 level tail hlevel_pos hlevel_lt
        prior_saturates U1 hU1_subset_U0 hU1_nonempty
        hU1_rel_open hU1_preconnected slope_nonzero 0 (Or.inl rfl)
        (by
          intro x hxU1
          have hneg :
              (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re < 0 := by
            exact hU1_neg x hxU1
          exact if_neg (not_lt_of_ge (le_of_lt hneg)))

private theorem continuous_vecC_of_continuous {X : Type*} [TopologicalSpace X] {d : Nat}
    {v : X -> Fin d -> ℝ} (hv : Continuous v) :
    Continuous fun x => vecC (v x) := by
  rw [continuous_pi_iff]
  intro i
  exact Complex.continuous_ofReal.comp ((continuous_apply i).comp hv)

private theorem continuous_complex_matrix_mulVec_of_continuous {X : Type*}
    [TopologicalSpace X] {d : Nat}
    {A : X -> Matrix (Fin d) (Fin d) ℂ} {v : X -> Fin d -> ℂ}
    (hA : Continuous A) (hv : Continuous v) :
    Continuous fun x => Matrix.mulVec (A x) (v x) := by
  rw [continuous_pi_iff]
  intro i
  simpa [Matrix.mulVec, dotProduct] using
    (continuous_finsetSum Finset.univ fun j _ =>
      ((continuous_apply j).comp ((continuous_apply i).comp hA)).mul
        ((continuous_apply j).comp hv))

private theorem continuous_complex_dotProduct_of_continuous {X : Type*}
    [TopologicalSpace X] {d : Nat} {v w : X -> Fin d -> ℂ}
    (hv : Continuous v) (hw : Continuous w) :
    Continuous fun x => dotProduct (v x) (w x) := by
  simpa [dotProduct] using
    (continuous_finsetSum Finset.univ fun i _ =>
      ((continuous_apply i).comp hv).mul ((continuous_apply i).comp hw))

/-- The arbitrary fixed tail gate stream is continuous in its displayed first gate
coordinate. -/
theorem continuous_gateAssignmentOfTail_apply {d n : Nat} (tail : Nat -> ℝ) :
    Continuous fun x : ProbePair d × ℝ => gateAssignmentOfTail x.2 tail n := by
  cases n with
  | zero =>
      simpa [gateAssignmentOfTail, complexGateAssignmentOfTail]
        using Complex.continuous_ofReal.comp
          (continuous_snd : Continuous fun x : ProbePair d × ℝ => x.2)
  | succ n =>
      simpa [gateAssignmentOfTail, complexGateAssignmentOfTail]
        using (continuous_const : Continuous fun _ : ProbePair d × ℝ => (tail n : ℂ))

private theorem continuous_formalFactor_gateAssignmentOfTail {d : Nat}
    (θs : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (tail : Nat -> ℝ) (n : Nat) :
    Continuous fun x : ProbePair d × ℝ =>
      formalFactor θs (gateAssignmentOfTail x.2 tail) n := by
  refine continuous_matrix ?_
  intro i j
  simpa [formalFactor, matC] using
    (continuous_const.sub
      ((continuous_gateAssignmentOfTail_apply (d := d) (n := n) tail).mul
        continuous_const))

/-- The formal transported `w` vector is continuous under an arbitrary fixed tail. -/
theorem continuous_formalWVec_gateAssignmentOfTail {d : Nat}
    (θs : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (tail : Nat -> ℝ) :
    ∀ n : Nat,
      Continuous fun x : ProbePair d × ℝ =>
        formalWVec θs n (gateAssignmentOfTail x.2 tail) x.1.1
  | 0 => by
      simpa [formalWVec] using
        continuous_vecC_of_continuous
          ((continuous_fst : Continuous fun x : ProbePair d × ℝ => x.1).fst)
  | n + 1 => by
      simpa [formalWVec_succ] using
        continuous_complex_matrix_mulVec_of_continuous
          (continuous_formalFactor_gateAssignmentOfTail θs tail n)
          (continuous_formalWVec_gateAssignmentOfTail θs tail n)

/-- The formal transported `v` vector is continuous under an arbitrary fixed tail. -/
theorem continuous_formalVVec_gateAssignmentOfTail {d : Nat}
    (θs : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (tail : Nat -> ℝ) :
    ∀ n : Nat,
      Continuous fun x : ProbePair d × ℝ =>
        formalVVec θs n (gateAssignmentOfTail x.2 tail) x.1.1 x.1.2
  | 0 => by
      simpa [formalVVec] using
        continuous_vecC_of_continuous
          ((continuous_fst : Continuous fun x : ProbePair d × ℝ => x.1).snd)
  | n + 1 => by
      have hleft :
          Continuous fun x : ProbePair d × ℝ =>
            Matrix.mulVec (matC (skipB (θs n).1))
              (formalVVec θs n (gateAssignmentOfTail x.2 tail) x.1.1 x.1.2) :=
        continuous_complex_matrix_mulVec_of_continuous continuous_const
          (continuous_formalVVec_gateAssignmentOfTail θs tail n)
      have hright :
          Continuous fun x : ProbePair d × ℝ =>
            gateAssignmentOfTail x.2 tail n •
              (Matrix.mulVec (matC (θs n).1)
                (formalWVec θs n (gateAssignmentOfTail x.2 tail) x.1.1)) :=
        (continuous_gateAssignmentOfTail_apply (d := d) (n := n) tail).smul
          (continuous_complex_matrix_mulVec_of_continuous continuous_const
            (continuous_formalWVec_gateAssignmentOfTail θs tail n))
      simpa [formalVVec_succ] using hleft.add hright

/-- The formal slope is continuous under an arbitrary fixed tail. -/
theorem continuous_formalPhi_gateAssignmentOfTail {d : Nat}
    (θs : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (tail : Nat -> ℝ) :
    Continuous fun x : ProbePair d × ℝ =>
      formalPhi θs n (gateAssignmentOfTail x.2 tail) x.1.1 x.1.2 := by
  simpa [formalPhi] using
    continuous_complex_dotProduct_of_continuous
      (continuous_formalWVec_gateAssignmentOfTail θs tail n)
      (continuous_complex_matrix_mulVec_of_continuous continuous_const
        (continuous_formalVVec_gateAssignmentOfTail θs tail n))

/-- The real part of the specialized slope used for trichotomy component selection
is continuous under an arbitrary fixed tail. -/
theorem continuous_specializedPhi_gateAssignmentOfTail_re
    {L d : Nat} (θ : Params L d) (level : Nat) (tail : Nat -> ℝ) :
    Continuous fun x : ProbePair d × ℝ =>
      (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re := by
  exact Complex.continuous_re.comp
    (by
      simpa [specializedPhi] using
        continuous_formalPhi_gateAssignmentOfTail (paramStream θ) level tail)

/-- Assemble provider-facing cascade induction data by iterating explicit canonical
branch choices from the full sign region. -/
noncomputable def cascadeTrichotomyInductionProviderData_of_canonicalChoices
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion : SignRegionData (L := L + 1) (d := d) θ' O
      (Params.headAttention θ') (Real.log (r : ℝ)))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (tail0 : Nat -> ℝ)
    (choose :
      ∀ {level : Nat}, 1 ≤ level -> level < L + 1 ->
        (Slevel : CascadeInductionState (Real.log (r : ℝ)) θ A signRegion.U
          (canonicalFrecGateAlongSignRegion r signRegion θ) level) ->
          CascadeLevelBranchChoice (Real.log (r : ℝ)) θ A Slevel.U
            (canonicalFrecGateAlongSignRegion r signRegion θ) level Slevel.tail) :
    CascadeTrichotomyInductionProviderData
      (L := L + 1) (d := d) (Real.log (r : ℝ)) θ A signRegion.U
      (canonicalFrecGateAlongSignRegion r signRegion θ)
      (canonicalFrecGateAlongSignRegion r signRegion θ') := by
  let hrel : ∃ W : Set (ProbePair d × ℝ), IsOpen W ∧
      signRegion.U = W ∩ signRegion.U :=
    ⟨Set.univ, isOpen_univ, by
      ext x
      simp⟩
  let Sfinal : CascadeInductionState (Real.log (r : ℝ)) θ A signRegion.U
      (canonicalFrecGateAlongSignRegion r signRegion θ) (L + 1) := by
    simpa using
      (CascadeInductionState.iterateFromInitial
        (b := Real.log (r : ℝ)) (θ := θ) (A := A)
        (signU := signRegion.U)
        (unprimed := canonicalFrecGateAlongSignRegion r signRegion θ)
        (hnonempty := signRegion.nonempty)
        (hrel := hrel)
        (hconn := signRegion.connected)
        (tail0 := tail0)
        (steps := L)
        (choose := choose))
  exact
    Sfinal.toProviderData (canonicalFrecGateAlongSignRegion r signRegion θ')
      (by
        intro x hx n hn_pos hn_lt
        exact
          canonicalFrecGateAlongSignRegion_primed_saturates_one signRegion x
            (Sfinal.subset_sign_region hx) n hn_pos hn_lt)

/-- Package an honest cascade builder as the TeX trichotomy construction data. -/
noncomputable def texTrichotomyConstructionData_of_cascadeBuilder
    {L d : Nat} {b : ℝ}
    {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ}
    {signU Ustar : Set (ProbePair d × ℝ)}
    {unprimed primed : GateAlongBase d}
    (B : CascadeTrichotomyBuilderData b θ A signU Ustar unprimed primed) :
    TexTrichotomyConstructionData (L := L) (d := d) b signU where
  unprimed := unprimed
  primed := primed
  Ustar := Ustar
  trichotomy := B.toTrichotomyData

/-- Package a provider-facing cascade induction frontier as TeX trichotomy construction
data. -/
noncomputable def texTrichotomyConstructionData_of_inductionProvider
    {L d : Nat} {b : ℝ}
    {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ}
    {signU : Set (ProbePair d × ℝ)}
    {unprimed primed : GateAlongBase d}
    (P : CascadeTrichotomyInductionProviderData b θ A signU unprimed primed) :
    TexTrichotomyConstructionData (L := L) (d := d) b signU :=
  texTrichotomyConstructionData_of_cascadeBuilder P.toBuilderData

/-- The saturated lower-layer contribution for the trichotomy constants produced by
an honest cascade builder. -/
noncomputable def texMatchingSaturatedContributionData_of_cascadeBuilder
    {L d : Nat} {b : ℝ}
    {θB θ : Params (L + 1) d} {A : Matrix (Fin d) (Fin d) ℝ}
    {signU Ustar : Set (ProbePair d × ℝ)}
    {unprimed primed : GateAlongBase d}
    (B : CascadeTrichotomyBuilderData
      (L := L + 1) (d := d) b θB A signU Ustar unprimed primed) :
    TexMatchingSaturatedContributionData (L := L) (d := d) θ
      (texTrichotomyConstructionData_of_cascadeBuilder B).trichotomy.varsigma where
  D :=
    texMatchingSaturatedContributionMatrix θ
      (texTrichotomyConstructionData_of_cascadeBuilder B).trichotomy.varsigma
  D_eq := rfl

/-- Provider-facing saturated lower-layer contribution for the trichotomy constants
compiled from a cascade induction frontier. -/
noncomputable def texMatchingSaturatedContributionData_of_inductionProvider
    {L d : Nat} {b : ℝ}
    {θB θ : Params (L + 1) d} {A : Matrix (Fin d) (Fin d) ℝ}
    {signU : Set (ProbePair d × ℝ)}
    {unprimed primed : GateAlongBase d}
    (P : CascadeTrichotomyInductionProviderData
      (L := L + 1) (d := d) b θB A signU unprimed primed) :
    TexMatchingSaturatedContributionData (L := L) (d := d) θ
      (texTrichotomyConstructionData_of_inductionProvider P).trichotomy.varsigma :=
  texMatchingSaturatedContributionData_of_cascadeBuilder (θ := θ) P.toBuilderData

/-- Builder-backed closed-recursion/R4 obligation from canonical actual gate data. -/
theorem texMatchingRegularQuadricClosedRecursionLimitObligation_of_cascadeBuilder
    {L d r : Nat}
    {θ θ' θB : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    {A : Matrix (Fin d) (Fin d) ℝ}
    {Ustar : Set (ProbePair d × ℝ)}
    {unprimed primed : GateAlongBase d}
    (B : CascadeTrichotomyBuilderData
      (L := L + 1) (d := d) (Real.log (r : ℝ)) θB A signRegion.U Ustar
        unprimed primed)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ')
        (texTrichotomyConstructionData_of_cascadeBuilder B).Ustar)
    (S : TexMatchingSaturatedContributionData (L := L) (d := d) θ
      (texTrichotomyConstructionData_of_cascadeBuilder B).trichotomy.varsigma)
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (actual :
      TexTrichotomyMatchingCanonicalActualGateData
        (θ := θ) (θ' := θ') signRegion
        (texTrichotomyConstructionData_of_cascadeBuilder B) N) :
    TexMatchingRegularQuadricClosedRecursionLimitObligation
      signRegion (texTrichotomyConstructionData_of_cascadeBuilder B) N S :=
  texMatchingRegularQuadricClosedRecursionLimitObligation_of_canonicalActualTrichotomyGates
    signRegion (texTrichotomyConstructionData_of_cascadeBuilder B) N S hAA actual

/-- Provider-facing closed-recursion/R4 obligation from canonical actual gate data. -/
theorem texMatchingRegularQuadricClosedRecursionLimitObligation_of_inductionProvider
    {L d r : Nat}
    {θ θ' θB : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    {A : Matrix (Fin d) (Fin d) ℝ}
    {unprimed primed : GateAlongBase d}
    (P : CascadeTrichotomyInductionProviderData
      (L := L + 1) (d := d) (Real.log (r : ℝ)) θB A signRegion.U
        unprimed primed)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ')
        (texTrichotomyConstructionData_of_inductionProvider P).Ustar)
    (S : TexMatchingSaturatedContributionData (L := L) (d := d) θ
      (texTrichotomyConstructionData_of_inductionProvider P).trichotomy.varsigma)
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (actual :
      TexTrichotomyMatchingCanonicalActualGateData
        (θ := θ) (θ' := θ') signRegion
        (texTrichotomyConstructionData_of_inductionProvider P) N) :
    TexMatchingRegularQuadricClosedRecursionLimitObligation
      signRegion (texTrichotomyConstructionData_of_inductionProvider P) N S :=
  texMatchingRegularQuadricClosedRecursionLimitObligation_of_cascadeBuilder
    signRegion P.toBuilderData N S hAA actual

end TransformerIdentifiability.NLayer
