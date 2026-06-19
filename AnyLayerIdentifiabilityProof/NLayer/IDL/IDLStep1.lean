import AnyLayerIdentifiabilityProof.NLayer.IDL.IDLStatement
import AnyLayerIdentifiabilityProof.NLayer.IDL.IDLBase
import AnyLayerIdentifiabilityProof.NLayer.Step1

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Step 1 endpoint for IDL

This file owns the construction of the first-attention endpoint and depth certificate
from the TeX generic step clauses.
-/

/-- The concrete analytic inputs still needed to instantiate the fixed-probe
zero-free descent constructor.

These are exactly the TeX Step 1 bridges after fixing `(w, v) ∈ O_star` and the
visible coordinate: zero-freeness of the first leading coefficient, Claim B for the
zero-free tier chain, and Claim C for the last-tier blow-up. -/
structure FixedOStarZeroFreeAnalyticBridgeData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ') : Type where
  lead_nonzero_on_first_stratum :
    ∀ τ ∈ p.concretePrimedTierSystem.stratification.S 0,
      (p.concretePrimedTierSystem.nestedFamily.step 0).lead
        (gatePrefix p.concretePrimedTierSystem.stratification 0 τ) ≠ 0
  propagation : ZeroFreeTierPropagation p.concretePrimedTierSystem
  lastTier : LastTierConcreteData p.concretePrimedTierSystem

/-- Proven form of the fixed-`O_star` first-leading-coefficient obligation for the
depth range where the first propagation polynomial `f₂` is present.

The unrestricted statement is missing this hypothesis: at depth `L = 1`,
`O_star` has no `κ₂` condition, while the first extracted leading coefficient is the
`f₂` coefficient. -/
theorem fixedOStar_firstLead_nonzero_on_firstStratum_of_tex_of_depth_gt_one
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ')
    (hDepth : 1 < L) :
    ∀ τ ∈ p.concretePrimedTierSystem.stratification.S 0,
      (p.concretePrimedTierSystem.nestedFamily.step 0).lead
        (gatePrefix p.concretePrimedTierSystem.stratification 0 τ) ≠ 0 := by
  intro τ _hτ
  have hpoly :
      Step1PolynomialFamilyAssumptionsForDepth L d (paramStream θ') p.probe.1 p.iota :=
    p.step1PolynomialFamilyAssumptionsForDepth hStanding.depth_pos
  have h0 : 0 < L - 1 := by omega
  have hkappa0 : step1KappaScalar (paramStream θ') 0 p.probe.1 ≠ 0 :=
    hpoly.kappa_ne ⟨0, h0⟩
  have hlead :
      (step1FormalPhiPropagationTailData (paramStream θ') p.probe.1 p.probe.2 0).presentation.lead
        (gatePrefix p.concretePrimedTierSystem.stratification 0 τ) ≠ 0 := by
    let q :=
      lastVariablePolynomial
        (step1FormalPhiPropagationTailPoly (paramStream θ') p.probe.1 p.probe.2 0)
    change
      MvPolynomial.eval (gatePrefix p.concretePrimedTierSystem.stratification 0 τ)
        q.leadingCoeff ≠ 0
    apply eval_ne_zero_of_ne_zero_fin_zero
    apply Polynomial.leadingCoeff_ne_zero.mpr
    intro hzero
    have hdegree :=
      step1FormalPhiPropagationTailData_degree_eq_two
        (paramStream θ') p.probe.1 p.probe.2 0 hkappa0
    change q.natDegree = 2 at hdegree
    rw [hzero, Polynomial.natDegree_zero] at hdegree
    norm_num at hdegree
  simpa [FixedOStarProbe.concretePrimedTierSystem] using hlead

/-- Explicit TeX Step 1 Claim B level-set input for all fixed `O_star` probes.

This is the remaining analytic obligation after the polynomial tower, scaled gate
identity, prefix continuity, and quadratic degree have been compiled by
`fixedOStar_zeroFreeTierPropagation_of_levelSetLead_frequently`. -/
abbrev FixedOStarZeroFreeLevelSetLeadData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (_hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  (p : FixedOStarProbe r L d O θ θ') ->
    ∀ {j : Nat} {τ : ℂ}, j + 1 < L -> τ ∈ p.concretePrimedTierSystem.T0 j ->
      (∀ᶠ z in puncturedNhds τ,
        z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1)) ->
      BlowsUpAt (p.concretePrimedTierSystem.stratification.H (j + 1)) τ ->
      ∃ᶠ z in puncturedNhds τ,
        z ∈ p.concretePrimedTierSystem.stratification.S (j + 1)
          ∧ (p.concretePrimedTierSystem.nestedFamily.step (j + 1)).lead
            (gatePrefix p.concretePrimedTierSystem.stratification (j + 1) z) ≠ 0

/-- At-tier form of the fixed-`O_star` Claim B level-set input.

At a zero-free tier point, the concrete stratification already supplies punctured
regularity for `omega (j+1)`, and the scaled polynomial tower supplies blow-up of
`H'_{j+1}`.  This leaves only the genuine level-set conclusion: frequently hit the next
stratum while avoiding the next leading-coefficient zero locus. -/
abbrev FixedOStarZeroFreeLevelSetLeadAtTierData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (_hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  (p : FixedOStarProbe r L d O θ θ') ->
    ∀ {j : Nat} {τ : ℂ}, j + 1 < L -> τ ∈ p.concretePrimedTierSystem.T0 j ->
      ∃ᶠ z in puncturedNhds τ,
        z ∈ p.concretePrimedTierSystem.stratification.S (j + 1)
          ∧ (p.concretePrimedTierSystem.nestedFamily.step (j + 1)).lead
            (gatePrefix p.concretePrimedTierSystem.stratification (j + 1) z) ≠ 0

/-- Cleaner analytic core of the fixed-`O_star` Claim B at-tier input.

The concrete successor stratum is the regular-domain level set where the next gate
argument hits the sigmoid pole set `oddPiI`.  This package isolates that genuine
pole-hitting statement while keeping the recursive leading-coefficient zero locus
explicit. -/
abbrev FixedOStarRegularPoleLeadAtTierData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (_hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  (p : FixedOStarProbe r L d O θ θ') ->
    ∀ {j : Nat} {τ : ℂ}, j + 1 < L -> τ ∈ p.concretePrimedTierSystem.T0 j ->
      ∃ᶠ z in puncturedNhds τ,
        z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1)
          ∧ p.concretePrimedTierSystem.stratification.H (j + 1) z ∈ oddPiI
          ∧ (p.concretePrimedTierSystem.nestedFamily.step (j + 1)).lead
            (gatePrefix p.concretePrimedTierSystem.stratification (j + 1) z) ≠ 0

/-- Honest pole-hit-plus-avoidance interface for the fixed-`O_star` Claim-B core.

This version does not claim the punctured regularity or preactivation blow-up from the
standing assumptions.  It records only the pole-hit and next-leading-coefficient
avoidance conclusion once those two analytic facts are supplied at a zero-free tier
point. -/
abbrev FixedOStarRegularPoleHitAvoidanceData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (_hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  (p : FixedOStarProbe r L d O θ θ') ->
    ∀ {j : Nat} {τ : ℂ}, j + 1 < L -> τ ∈ p.concretePrimedTierSystem.T0 j ->
      (∀ᶠ z in puncturedNhds τ,
        z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1)) ->
      BlowsUpAt (p.concretePrimedTierSystem.stratification.H (j + 1)) τ ->
      ∃ᶠ z in puncturedNhds τ,
        z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1)
          ∧ p.concretePrimedTierSystem.stratification.H (j + 1) z ∈ oddPiI
          ∧ (p.concretePrimedTierSystem.nestedFamily.step (j + 1)).lead
            (gatePrefix p.concretePrimedTierSystem.stratification (j + 1) z) ≠ 0

/-- Pole-hitting part of the fixed-`O_star` Claim-B core, separated from avoidance of
the next leading-coefficient zero locus. -/
abbrev FixedOStarRegularPoleHitData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (_hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  (p : FixedOStarProbe r L d O θ θ') ->
    ∀ {j : Nat} {τ : ℂ}, j + 1 < L -> τ ∈ p.concretePrimedTierSystem.T0 j ->
      (∀ᶠ z in puncturedNhds τ,
        z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1)) ->
      BlowsUpAt (p.concretePrimedTierSystem.stratification.H (j + 1)) τ ->
      ∃ᶠ z in puncturedNhds τ,
        z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1)
          ∧ p.concretePrimedTierSystem.stratification.H (j + 1) z ∈ oddPiI

/-- Smaller preimage form of the pole-hitting part of the fixed-`O_star` Claim-B core.

This is the exact analytic pole-preimage obligation for the concrete successor
preactivation, separated from the already-compiled punctured regularity of the next
domain. -/
abbrev FixedOStarRegularPolePreimageData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (_hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  (p : FixedOStarProbe r L d O θ θ') ->
    ∀ {j : Nat} {τ : ℂ}, j + 1 < L -> τ ∈ p.concretePrimedTierSystem.T0 j ->
      BlowsUpAt (p.concretePrimedTierSystem.stratification.H (j + 1)) τ ->
      ∃ᶠ z in puncturedNhds τ,
        p.concretePrimedTierSystem.stratification.H (j + 1) z ∈ oddPiI

/-- The stronger at-tier regular-pole Claim-B input contains the preimage-only pole-hit
field: discard regularity and leading-coefficient avoidance from its frequent
conclusion. -/
theorem fixedOStarRegularPolePreimageData_of_regularPoleLeadAtTierData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hpole : FixedOStarRegularPoleLeadAtTierData hr hStanding) :
    FixedOStarRegularPolePreimageData hr hStanding := by
  intro p j τ hj hτ _hH
  exact (hpole p hj hτ).mono fun _z hz => hz.2.1

/-- Compile the preimage-only pole-hitting obligation with punctured regularity to recover
the separated pole-hit Claim-B field. -/
theorem fixedOStarRegularPoleHitData_of_regularPolePreimageData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hpreimage : FixedOStarRegularPolePreimageData hr hStanding) :
    FixedOStarRegularPoleHitData hr hStanding := by
  intro p j τ hj hτ hOmega hH
  have hpoleFreq := hpreimage p hj hτ hH
  exact (hpoleFreq.and_eventually hOmega).mono fun z hz => ⟨hz.2, hz.1⟩

/-- Avoidance part of the fixed-`O_star` Claim-B core: along regular pole hits, the
next leading coefficient is eventually nonzero. -/
abbrev FixedOStarRegularPoleLeadAvoidanceOnPoleHitData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (_hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  (p : FixedOStarProbe r L d O θ θ') ->
    ∀ {j : Nat} {τ : ℂ}, j + 1 < L -> τ ∈ p.concretePrimedTierSystem.T0 j ->
      (∀ᶠ z in puncturedNhds τ,
        z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1)) ->
      BlowsUpAt (p.concretePrimedTierSystem.stratification.H (j + 1)) τ ->
      ∀ᶠ z in puncturedNhds τ,
        z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1)
          ∧ p.concretePrimedTierSystem.stratification.H (j + 1) z ∈ oddPiI ->
          (p.concretePrimedTierSystem.nestedFamily.step (j + 1)).lead
            (gatePrefix p.concretePrimedTierSystem.stratification (j + 1) z) ≠ 0

/-- The preimage side of the fixed-`O_star` Claim-B split is vacuous in depth at most
one, since there is no successor tier `j + 1 < L`. -/
theorem fixedOStarRegularPolePreimageData_of_depth_le_one
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hDepth : L <= 1) :
    FixedOStarRegularPolePreimageData hr hStanding := by
  intro _p _j _τ hj _hτ _hH
  omega

/-- The leading-coefficient avoidance side of the fixed-`O_star` Claim-B split is
vacuous in depth at most one. -/
theorem fixedOStarRegularPoleLeadAvoidanceOnPoleHitData_of_depth_le_one
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hDepth : L <= 1) :
    FixedOStarRegularPoleLeadAvoidanceOnPoleHitData hr hStanding := by
  intro _p _j _τ hj _hτ _hOmega _hH
  omega

/-- Depth-sharpened pole-preimage obligation.

The `L <= 1` branch is already closed by
`fixedOStarRegularPolePreimageData_of_depth_le_one`, so the remaining analytic
preimage problem only needs to be supplied under `1 < L`. -/
abbrev FixedOStarRegularPolePreimageDataOfDepthGTOne
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  1 < L -> FixedOStarRegularPolePreimageData hr hStanding

/-- Depth-gated version of
`fixedOStarRegularPolePreimageData_of_regularPoleLeadAtTierData`, matching the
`regularPolePreimage_depth_gt_one` provider field exactly. -/
theorem fixedOStarRegularPolePreimageDataOfDepthGTOne_of_regularPoleLeadAtTierData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hpole : FixedOStarRegularPoleLeadAtTierData hr hStanding) :
    FixedOStarRegularPolePreimageDataOfDepthGTOne hr hStanding := by
  intro _hDepth
  exact fixedOStarRegularPolePreimageData_of_regularPoleLeadAtTierData hpole

/-- The older level-set Claim-B surface implies the reduced preimage-only pole-hit
field.

The level-set conclusion gives frequent successor-stratum points.  The concrete
sigmoid stratification identifies every successor-stratum point with a pole value of the
successor preactivation, so the leading-coefficient part of that older surface can be
discarded. -/
theorem fixedOStarRegularPolePreimageData_of_zeroFreeLevelSetLeadData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hlevel : FixedOStarZeroFreeLevelSetLeadData hr hStanding) :
    FixedOStarRegularPolePreimageData hr hStanding := by
  intro p j τ hj hτ hH
  have hOmega :
      ∀ᶠ z in puncturedNhds τ,
        z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1) :=
    p.concretePrimedTierSystem.T0_punctured_omega_succ (by omega) hτ
  have hfreq := hlevel p hj hτ hOmega hH
  exact hfreq.mono fun _z hz =>
    p.concretePrimedTierSystem.stratification.sigmoid.gateArgument_mem_oddPiI
      (by omega) hz.1

/-- Depth-gated form of
`fixedOStarRegularPolePreimageData_of_zeroFreeLevelSetLeadData`, matching the actual
`regularPolePreimage_depth_gt_one` provider field. -/
theorem fixedOStarRegularPolePreimageDataOfDepthGTOne_of_zeroFreeLevelSetLeadData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hlevel : FixedOStarZeroFreeLevelSetLeadData hr hStanding) :
    FixedOStarRegularPolePreimageDataOfDepthGTOne hr hStanding := by
  intro _hDepth
  exact fixedOStarRegularPolePreimageData_of_zeroFreeLevelSetLeadData hlevel

/-- Depth-sharpened leading-coefficient avoidance obligation.

The `L <= 1` branch is vacuous, so only the genuine `1 < L` branch remains. -/
abbrev FixedOStarRegularPoleLeadAvoidanceOnPoleHitDataOfDepthGTOne
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  1 < L -> FixedOStarRegularPoleLeadAvoidanceOnPoleHitData hr hStanding

/-- Interior polynomial-zero-locus form of the fixed-`O_star` lead-avoidance
obligation.

For non-last successor steps (`j + 2 < L`), the abstract leading coefficient in the
actual formal-phi nested family is the concrete Step 1 propagation leading-coefficient
polynomial.  This interface exposes the remaining avoidance as a zero-locus avoidance
statement for that explicit polynomial. -/
abbrev FixedOStarRegularPoleInteriorPropagationLeadingCoeffAvoidanceOnPoleHitDataOfDepthGTOne
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (_hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  1 < L ->
    (p : FixedOStarProbe r L d O θ θ') ->
      ∀ {j : Nat} {τ : ℂ}, j + 2 < L -> τ ∈ p.concretePrimedTierSystem.T0 j ->
        (∀ᶠ z in puncturedNhds τ,
          z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1)) ->
        BlowsUpAt (p.concretePrimedTierSystem.stratification.H (j + 1)) τ ->
        ∀ᶠ z in puncturedNhds τ,
          z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1)
            ∧ p.concretePrimedTierSystem.stratification.H (j + 1) z ∈ oddPiI ->
            MvPolynomial.eval
              (gatePrefix p.concretePrimedTierSystem.stratification (j + 1) z)
              (step1PropagationLeadingCoeffPoly (paramStream θ') p.probe.1 (j + 1))
                ≠ 0

/-- Boundary form of lead avoidance at the last successor step.

The compiled polynomial-family assumptions identify the formal-phi leading coefficient
with the Step 1 propagation leading-coefficient polynomial only for `m < L - 1`.  This
keeps the remaining `j + 2 = L` boundary obligation explicit. -/
abbrev FixedOStarRegularPoleLastStepLeadAvoidanceOnPoleHitDataOfDepthGTOne
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (_hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  1 < L ->
    (p : FixedOStarProbe r L d O θ θ') ->
      ∀ {j : Nat} {τ : ℂ}, j + 1 < L -> ¬ j + 2 < L ->
        τ ∈ p.concretePrimedTierSystem.T0 j ->
        (∀ᶠ z in puncturedNhds τ,
          z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1)) ->
        BlowsUpAt (p.concretePrimedTierSystem.stratification.H (j + 1)) τ ->
        ∀ᶠ z in puncturedNhds τ,
          z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1)
            ∧ p.concretePrimedTierSystem.stratification.H (j + 1) z ∈ oddPiI ->
            (p.concretePrimedTierSystem.nestedFamily.step (j + 1)).lead
              (gatePrefix p.concretePrimedTierSystem.stratification (j + 1) z) ≠ 0

/-- Boundary form of the last-step split Claim-B obligation.

At the split boundary `j + 2 = L`, the current formal-phi nested tower has no
available successor `κ_{L+1}` coefficient.  With `paramStream` zero outside the finite
depth, the boundary formal-phi leading coefficient is identically zero (proved below),
so the existing last-step lead-avoidance field is equivalent to saying that regular
successor pole hits do not occur eventually in this boundary situation. -/
abbrev FixedOStarRegularPoleLastStepNoPoleHitDataOfDepthGTOne
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (_hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  1 < L ->
    (p : FixedOStarProbe r L d O θ θ') ->
      ∀ {j : Nat} {τ : ℂ}, j + 1 < L -> ¬ j + 2 < L ->
        τ ∈ p.concretePrimedTierSystem.T0 j ->
        (∀ᶠ z in puncturedNhds τ,
          z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1)) ->
        BlowsUpAt (p.concretePrimedTierSystem.stratification.H (j + 1)) τ ->
        ∀ᶠ z in puncturedNhds τ,
          ¬ (z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1)
              ∧ p.concretePrimedTierSystem.stratification.H (j + 1) z ∈ oddPiI)

/-- At the split boundary `m + 1 = L`, the current formal-phi nested-family lead is
identically zero.

This is a finite-depth artifact of the present `paramStream`: the polynomial
`formalPhiPoly (paramStream θ') L` reads the out-of-range attention matrix
`(paramStream θ' L).2 = 0`.  Thus the last-step lead-avoidance field cannot be proved by
the same kappa-leading-coefficient argument used on the interior range. -/
theorem fixedOStar_concretePrimedTierSystem_boundary_stepLead_eq_zero
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ')
    {m : Nat} (hm : m + 1 = L) :
    (p.concretePrimedTierSystem.nestedFamily.step m).lead = 0 := by
  subst L
  funext x
  simp [FixedOStarProbe.concretePrimedTierSystem,
    step1FormalPhiPropagationPolynomialNestedTailData,
    step1FormalPhiPropagationTailData,
    step1FormalPhiPropagationTailPoly,
    PolynomialTailPresentationData.ofPolynomial,
    polynomialTailPresentation, lastVariablePolynomial,
    formalPhiPoly, matPolyC]

/-- Pointwise boundary no-pole formulation for the last-step split.

This is stronger than the eventual no-pole-hit field and removes the irrelevant
punctured regularity, zero-free tier, and blow-up hypotheses. -/
abbrev FixedOStarRegularPoleLastStepPointwiseNoPoleDataOfDepthGTOne
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (_hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  1 < L ->
    (p : FixedOStarProbe r L d O θ θ') ->
      ∀ {j : Nat} {z : ℂ}, j + 1 < L -> ¬ j + 2 < L ->
        z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1) ->
        p.concretePrimedTierSystem.stratification.H (j + 1) z ∉ oddPiI

/-- Boundary no-pole formulation at the actual last successor layer.

At the split boundary `j + 2 = L`, the gate argument in the no-pole condition is
`H (j+1)`, hence layer `L - 1`.  This package states that condition directly as the
formal-phi polynomial preactivation plus the real bias `log r`, avoiding the misleading
one-past-depth `H L` constant. -/
abbrev FixedOStarRegularPoleLastBoundaryFormalPhiNoPoleDataOfDepthGTOne
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (_hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  1 < L ->
    (p : FixedOStarProbe r L d O θ θ') ->
      ∀ z, z ∈ p.concretePrimedTierSystem.stratification.omega (L - 1) ->
        z *
            MvPolynomial.eval
              (gatePrefix p.concretePrimedTierSystem.stratification (L - 1) z)
            (formalPhiPoly (K := L - 1) (paramStream θ') (L - 1)
                p.probe.1 p.probe.2)
            + (Real.log (r : ℝ) : ℂ) ∉ oddPiI

/-- Generic polynomial-region form of the last-boundary no-pole condition.

For depth `L`, this asks that the scalar preactivation assembled from
`formalPhiPoly θ (L - 1) w v` avoid the sigmoid pole set on an arbitrary region in
the product of the boundary base variable and the `L - 1` gate-prefix variables. -/
abbrev Step1LastBoundaryFormalPhiNoPoleOnRegionAssumptionsForDepth
    (L d r : Nat)
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d -> ℝ)
    (R : Set (ℂ × (Fin (L - 1) -> ℂ))) : Prop :=
  1 < L ->
    ∀ q ∈ R,
      q.1 *
          MvPolynomial.eval q.2
            (formalPhiPoly (K := L - 1) θ (L - 1) w v)
          + (Real.log (r : ℝ) : ℂ) ∉ oddPiI

/-- The concrete regular-domain graph on which the fixed-`O_star` last-boundary
formal-phi no-pole condition is evaluated. -/
def fixedOStarLastBoundaryRegularDomainGraph
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ') :
    Set (ℂ × (Fin (L - 1) -> ℂ)) :=
  {q | q.1 ∈ p.concretePrimedTierSystem.stratification.omega (L - 1)
      ∧ q.2 =
        gatePrefix p.concretePrimedTierSystem.stratification (L - 1) q.1}

/-- Build a fixed `O_star` probe from raw probe membership and an explicit visible
coordinate.  This is useful for provider surfaces whose assumptions do not need to
mention the tail-agreement threshold carried by `FixedOStarProbe`. -/
noncomputable def fixedOStarProbeOfOStarVisibleCoord
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    {probe : ProbePair d}
    (hp : probe ∈ O_star θ' O)
    (iota : Fin d)
    (hvisible : visibleTailCoord θ' probe.1 iota ≠ 0) :
    FixedOStarProbe r L d O θ θ' where
  probe := probe
  mem_O_star := hp
  iota := iota
  visible_iota_ne := hvisible
  T0 := hStanding.agreement.T0 probe
  tail_agreement := hStanding.agreement.at (O_star_mem_base hp)

/-- Raw-probe version of the concrete last-boundary regular-domain graph. -/
noncomputable def fixedOStarLastBoundaryRegularDomainGraphOfOStar
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    {probe : ProbePair d}
    (hp : probe ∈ O_star θ' O)
    (iota : Fin d)
    (hvisible : visibleTailCoord θ' probe.1 iota ≠ 0) :
    Set (ℂ × (Fin (L - 1) -> ℂ)) :=
  fixedOStarLastBoundaryRegularDomainGraph
    (fixedOStarProbeOfOStarVisibleCoord hStanding hp iota hvisible)

/-- The raw-probe graph agrees with the graph of any fixed-probe package carrying the
same raw probe and visible coordinate. -/
theorem fixedOStarLastBoundaryRegularDomainGraphOfOStar_eq
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ') :
    fixedOStarLastBoundaryRegularDomainGraphOfOStar
        hStanding p.mem_O_star p.iota p.visible_iota_ne =
      fixedOStarLastBoundaryRegularDomainGraph p := by
  ext q
  simp [fixedOStarLastBoundaryRegularDomainGraphOfOStar,
    fixedOStarProbeOfOStarVisibleCoord, fixedOStarLastBoundaryRegularDomainGraph,
    FixedOStarProbe.concretePrimedTierSystem, FixedOStarProbe.concretePrimedStratification,
    ConstantProbeConcreteData.toConcreteStratification]

/-- Compile the generic no-pole-on-region witness on the concrete last-boundary graph
to the fixed-`O_star` boundary field. -/
theorem fixedOStarLastBoundaryFormalPhiNoPole_of_noPoleOnRegularDomainGraph
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hboundary :
      (p : FixedOStarProbe r L d O θ θ') ->
        Step1LastBoundaryFormalPhiNoPoleOnRegionAssumptionsForDepth
          L d r (paramStream θ') p.probe.1 p.probe.2
          (fixedOStarLastBoundaryRegularDomainGraph (θ := θ) (θ' := θ') p)) :
    FixedOStarRegularPoleLastBoundaryFormalPhiNoPoleDataOfDepthGTOne
      hr hStanding := by
  intro hDepth p z hz
  exact hboundary p hDepth
    ⟨z, gatePrefix p.concretePrimedTierSystem.stratification (L - 1) z⟩
    ⟨hz, rfl⟩

/-- The concrete last-boundary preactivation is the formal-phi polynomial evaluated on
the last in-range gate prefix, plus the real bias. -/
theorem fixedOStar_concretePrimedTierSystem_H_lastBoundary_eq_formalPhiPoly
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ') (z : ℂ) :
    p.concretePrimedTierSystem.stratification.H (L - 1) z =
      z *
          MvPolynomial.eval
            (gatePrefix p.concretePrimedTierSystem.stratification (L - 1) z)
            (formalPhiPoly (K := L - 1) (paramStream θ') (L - 1)
              p.probe.1 p.probe.2)
          + (Real.log (r : ℝ) : ℂ) := by
  have hprefix :
      extendGate
          (gatePrefix p.concretePrimedTierSystem.stratification (L - 1) z) =
        constantProbeGatePrefix (paramStream θ') (Real.log (r : ℝ))
          p.probe.1 p.probe.2 (L - 1) z := by
    funext k
    by_cases hk : k < L - 1
    · simp [extendGate, gatePrefix, FixedOStarProbe.concretePrimedTierSystem,
        FixedOStarProbe.concretePrimedStratification,
        ConstantProbeConcreteData.toConcreteStratification,
        ConcreteStratificationData.toConcreteStratification,
        ConstantProbeConcreteData.toConcreteStratificationData,
        constantProbeGatePrefix, hk]
    · simp [extendGate, constantProbeGatePrefix, hk]
  have hphi :
      formalPhi (paramStream θ') (L - 1)
          (constantProbeGatePrefix (paramStream θ') (Real.log (r : ℝ))
            p.probe.1 p.probe.2 (L - 1) z) p.probe.1 p.probe.2 =
        formalPhi (paramStream θ') (L - 1)
          (extendGate
            (gatePrefix p.concretePrimedTierSystem.stratification (L - 1) z))
          p.probe.1 p.probe.2 := by
    rw [← hprefix]
  simp [FixedOStarProbe.concretePrimedTierSystem,
    FixedOStarProbe.concretePrimedStratification,
    ConstantProbeConcreteData.toConcreteStratification,
    ConcreteStratificationData.toConcreteStratification,
    ConstantProbeConcreteData.toConcreteStratificationData,
    constantProbeGateArgument, eval_formalPhiPoly, hphi]

/-- The direct last-boundary polynomial no-pole statement implies the older indexed
pointwise boundary field. -/
theorem fixedOStarRegularPoleLastStepPointwiseNoPoleDataOfDepthGTOne_of_lastBoundaryFormalPhiNoPole
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hboundary :
      FixedOStarRegularPoleLastBoundaryFormalPhiNoPoleDataOfDepthGTOne
        hr hStanding) :
    FixedOStarRegularPoleLastStepPointwiseNoPoleDataOfDepthGTOne
      hr hStanding := by
  intro hDepth p j z hj hlast hω
  have hj_boundary : j + 1 = L - 1 := by omega
  have hω_boundary :
      z ∈ p.concretePrimedTierSystem.stratification.omega (L - 1) := by
    simpa [hj_boundary] using hω
  have hno := hboundary hDepth p z hω_boundary
  rwa [hj_boundary,
    fixedOStar_concretePrimedTierSystem_H_lastBoundary_eq_formalPhiPoly
      (p := p) (z := z)]

/-- The pointwise boundary no-pole statement implies the existing eventual no-pole-hit
field. -/
theorem fixedOStarRegularPoleLastStepNoPoleHitDataOfDepthGTOne_of_pointwiseNoPole
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hpoint :
      FixedOStarRegularPoleLastStepPointwiseNoPoleDataOfDepthGTOne hr hStanding) :
    FixedOStarRegularPoleLastStepNoPoleHitDataOfDepthGTOne hr hStanding := by
  intro hDepth p j _τ hj hlast _hτ _hOmega _hH
  filter_upwards [] with z hhit
  exact hpoint hDepth p hj hlast hhit.1 hhit.2

/-- The boundary no-pole-hit condition implies the existing last-step lead-avoidance
field, vacuously. -/
theorem fixedOStarRegularPoleLastStepLeadAvoidanceOfDepthGTOne_of_noPoleHit
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hnoPole :
      FixedOStarRegularPoleLastStepNoPoleHitDataOfDepthGTOne hr hStanding) :
    FixedOStarRegularPoleLastStepLeadAvoidanceOnPoleHitDataOfDepthGTOne
      hr hStanding := by
  intro hDepth p j τ hj hlast hτ hOmega hH
  have hno := hnoPole hDepth p hj hlast hτ hOmega hH
  filter_upwards [hno] with z hz hhit
  exact False.elim (hz hhit)

/-- The actual formal-phi tail leading coefficient is the concrete Step 1 propagation
leading-coefficient polynomial, whenever the relevant quadratic coefficient is present.

The proof is a coefficient comparison: after moving the last variable to the front, the
coefficient of last-gate power `2` in `formalPhiPoly θ (m+1)` is exactly the
`f_{m+2}` polynomial already packaged by `step1PropagationLeadingCoeffPoly`. -/
theorem step1FormalPhiPropagation_leadingCoeff_eq_step1PropagationLeadingCoeffPoly_of_kappa
    {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (m : Nat)
    (hkappa : step1KappaScalar θ m w ≠ 0) :
    (lastVariablePolynomial (step1FormalPhiPropagationTailPoly θ w v m)).leadingCoeff =
      step1PropagationLeadingCoeffPoly θ w m := by
  apply MvPolynomial.ext
  intro a
  let lift : Fin (m + 1) →₀ Nat := Finsupp.mapDomain Fin.castSucc a
  let formalIdx : Fin (m + 1) →₀ Nat := Finsupp.single (Fin.last m) 2 + lift
  have hdegreeFormal :
      (lastVariablePolynomial (step1FormalPhiPropagationTailPoly θ w v m)).natDegree = 2 := by
    simpa [step1FormalPhiPropagationTailData, PolynomialTailPresentationData.ofPolynomial,
      polynomialTailPresentation] using
      step1FormalPhiPropagationTailData_degree_eq_two θ w v m hkappa
  have hdegreeProp :
      (lastVariablePolynomial (step1PropagationTailPoly θ w m)).natDegree = 0 := by
    simpa [step1PropagationTailData, PolynomialTailPresentationData.ofPolynomial,
      polynomialTailPresentation] using
      step1PropagationTailData_degree θ w m
  have hzero : (nestedLastToFrontEquiv m).symm (0 : Fin (m + 1)) = Fin.last m := by
    apply (nestedLastToFrontEquiv m).injective
    simp
  have hsucc : ∀ k : Fin m, (nestedLastToFrontEquiv m).symm k.succ = k.castSucc := by
    intro k
    apply (nestedLastToFrontEquiv m).injective
    simp
  have hlastNotRange : Fin.last m ∉ Set.range (Fin.castSucc : Fin m → Fin (m + 1)) := by
    rintro ⟨k, hk⟩
    exact Fin.castSucc_ne_last k hk
  have hmapFormal :
      Finsupp.mapDomain (nestedLastToFrontEquiv m) formalIdx = Finsupp.cons 2 a := by
    ext i
    refine Fin.cases ?_ ?_ i
    · rw [Finsupp.cons_zero]
      rw [← Equiv.apply_symm_apply (nestedLastToFrontEquiv m) (0 : Fin (m + 1))]
      rw [Finsupp.mapDomain_apply (Equiv.injective (nestedLastToFrontEquiv m))]
      rw [hzero]
      dsimp [formalIdx]
      rw [Finsupp.single_eq_same]
      dsimp [lift]
      rw [Finsupp.mapDomain_notin_range a (Fin.last m) hlastNotRange]
      norm_num
    · intro k
      rw [Finsupp.cons_succ]
      rw [← Equiv.apply_symm_apply (nestedLastToFrontEquiv m) k.succ]
      rw [Finsupp.mapDomain_apply (Equiv.injective (nestedLastToFrontEquiv m))]
      rw [hsucc k]
      dsimp [formalIdx]
      rw [Finsupp.single_eq_of_ne]
      · dsimp [lift]
        rw [Finsupp.mapDomain_apply (Fin.castSucc_injective m)]
        simp
      · exact Fin.castSucc_ne_last k
  have hmapProp :
      Finsupp.mapDomain (nestedLastToFrontEquiv m) lift = Finsupp.cons 0 a := by
    ext i
    refine Fin.cases ?_ ?_ i
    · rw [Finsupp.cons_zero]
      rw [← Equiv.apply_symm_apply (nestedLastToFrontEquiv m) (0 : Fin (m + 1))]
      rw [Finsupp.mapDomain_apply (Equiv.injective (nestedLastToFrontEquiv m))]
      rw [hzero]
      dsimp [lift]
      exact Finsupp.mapDomain_notin_range a (Fin.last m) hlastNotRange
    · intro k
      rw [Finsupp.cons_succ]
      rw [← Equiv.apply_symm_apply (nestedLastToFrontEquiv m) k.succ]
      rw [Finsupp.mapDomain_apply (Equiv.injective (nestedLastToFrontEquiv m))]
      rw [hsucc k]
      dsimp [lift]
      rw [Finsupp.mapDomain_apply (Fin.castSucc_injective m)]
  rw [Polynomial.leadingCoeff, hdegreeFormal]
  unfold step1PropagationLeadingCoeffPoly
  rw [Polynomial.leadingCoeff, hdegreeProp]
  unfold lastVariablePolynomial
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [← hmapFormal]
  rw [← hmapProp]
  rw [MvPolynomial.coeff_rename_mapDomain (nestedLastToFrontEquiv m)
    (Equiv.injective (nestedLastToFrontEquiv m))]
  rw [MvPolynomial.coeff_rename_mapDomain (nestedLastToFrontEquiv m)
    (Equiv.injective (nestedLastToFrontEquiv m))]
  dsimp [formalIdx, lift]
  simpa [step1FormalPhiPropagationTailPoly, step1PropagationTailPoly] using
    coeff_formalPhiPoly_step1LastSqCoeffPoly_succ
      (K := m + 1) θ ⟨m, Nat.lt_succ_self m⟩ w v
      (Finsupp.mapDomain Fin.castSucc a)

/-- Pointwise evaluator form of
`step1FormalPhiPropagation_leadingCoeff_eq_step1PropagationLeadingCoeffPoly_of_kappa`. -/
theorem step1FormalPhiPropagationTailData_lead_eq_step1PropagationLeadingCoeffPoly_of_kappa
    {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (m : Nat)
    (hkappa : step1KappaScalar θ m w ≠ 0) :
    (step1FormalPhiPropagationTailData θ w v m).presentation.lead =
      fun x => MvPolynomial.eval x (step1PropagationLeadingCoeffPoly θ w m) := by
  funext x
  change MvPolynomial.eval x
      (lastVariablePolynomial (step1FormalPhiPropagationTailPoly θ w v m)).leadingCoeff =
    MvPolynomial.eval x (step1PropagationLeadingCoeffPoly θ w m)
  rw [step1FormalPhiPropagation_leadingCoeff_eq_step1PropagationLeadingCoeffPoly_of_kappa
    θ w v m hkappa]

/-- For a fixed `O_star` probe, every interior formal-phi nested-family lead is the
concrete Step 1 propagation leading-coefficient polynomial. -/
theorem fixedOStar_concretePrimedTierSystem_stepLead_eq_step1PropagationLeadingCoeffPoly
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ')
    {m : Nat} (hm : m < L - 1) :
    (p.concretePrimedTierSystem.nestedFamily.step m).lead =
      fun x => MvPolynomial.eval x
        (step1PropagationLeadingCoeffPoly (paramStream θ') p.probe.1 m) := by
  have hpoly :
      Step1PolynomialFamilyAssumptionsForDepth L d (paramStream θ') p.probe.1 p.iota :=
    p.step1PolynomialFamilyAssumptionsForDepth hStanding.depth_pos
  have hkappa : step1KappaScalar (paramStream θ') m p.probe.1 ≠ 0 :=
    hpoly.kappa_ne ⟨m, hm⟩
  simpa [FixedOStarProbe.concretePrimedTierSystem,
    step1FormalPhiPropagationNestedTailFamily] using
    step1FormalPhiPropagationTailData_lead_eq_step1PropagationLeadingCoeffPoly_of_kappa
      (paramStream θ') p.probe.1 p.probe.2 m hkappa

/-- Region form of the interior Claim-B leading-coefficient avoidance field.

The existing provider asks for eventual avoidance along regular successor pole hits.
This static version asks only that the explicit propagation leading-coefficient
polynomial be nonzero on the already-constructed formal-phi nested region. -/
abbrev FixedOStarRegularPoleInteriorPropagationLeadingCoeffNonzeroOnRegionDataOfDepthGTOne
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (_hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  1 < L ->
    (p : FixedOStarProbe r L d O θ θ') ->
      ∀ {m : Nat}, m < L - 1 ->
        ∀ x ∈ p.concretePrimedTierSystem.nestedFamily.region m,
          MvPolynomial.eval x
            (step1PropagationLeadingCoeffPoly (paramStream θ') p.probe.1 m) ≠ 0

/-- The threshold of a degree-zero tail presentation is the constant `1`. -/
theorem tailPresentation_threshold_eq_one_of_degree_eq_zero {α : Type*}
    (P : TailPresentation α) (hdegree : P.degree = 0) (x : α) :
    P.threshold x = 1 := by
  cases P with
  | mk degree lead lower =>
      dsimp at hdegree ⊢
      subst degree
      simp [TailPresentation.threshold, tailThreshold]

/-- Every evaluator-form tail threshold is at least `1`. -/
theorem one_le_tailPresentation_threshold {α : Type*}
    (P : TailPresentation α) (x : α) :
    1 <= P.threshold x := by
  cases P with
  | mk degree lead lower =>
      dsimp [TailPresentation.threshold, tailThreshold]
      have hsum_nonneg :
          0 <= ∑ i : Fin degree, ‖lower i x‖ / ‖lead x‖ := by
        exact Finset.sum_nonneg fun i _hi =>
          div_nonneg (norm_nonneg _) (norm_nonneg _)
      linarith

/-- Nested regions are contravariant in the threshold tower. -/
theorem nestedTailFamily_region_subset_of_threshold_le
    {F G : NestedTailFamily}
    (hthreshold :
      ∀ m : Nat, ∀ x : Fin m -> ℂ, G.threshold m x <= F.threshold m x) :
    ∀ m : Nat, F.region m ⊆ G.region m := by
  intro m
  induction m with
  | zero =>
      intro z _hz
      simp
  | succ m ih =>
      intro z hz
      exact ⟨ih hz.1,
        lt_of_le_of_lt (hthreshold m (nestedInit z)) hz.2⟩

/-- The propagation tower packages extracted leading coefficients as degree-zero tail
presentations, so its recursive threshold is constantly `1`. -/
theorem step1PropagationNestedTailFamily_threshold_eq_one {d : Nat}
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d -> ℝ) (m : Nat) (x : Fin m -> ℂ) :
    (step1PropagationNestedTailFamily θ w).threshold m x = 1 :=
  tailPresentation_threshold_eq_one_of_degree_eq_zero
    ((step1PropagationNestedTailFamily θ w).step m)
    (step1PropagationNestedTailFamily_step_degree θ w m) x

/-- The formal-phi propagation region is contained in the degree-zero propagation
leading-coefficient region, because formal-phi thresholds are always at least `1` while
the propagation thresholds are exactly `1`. -/
theorem step1FormalPhiPropagationNestedTailFamily_region_subset_step1PropagationNestedTailFamily_region
    {d : Nat}
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d -> ℝ) :
    ∀ m : Nat,
      (step1FormalPhiPropagationNestedTailFamily θ w v).region m ⊆
        (step1PropagationNestedTailFamily θ w).region m := by
  apply nestedTailFamily_region_subset_of_threshold_le
  intro m x
  rw [step1PropagationNestedTailFamily_threshold_eq_one]
  simpa [NestedTailFamily.threshold] using
    one_le_tailPresentation_threshold
      ((step1FormalPhiPropagationNestedTailFamily θ w v).step m) x

/-- The fixed-probe formal-phi nested region is contained in the corresponding Step 1
propagation leading-coefficient nested region. -/
theorem fixedOStar_concretePrimedTierSystem_region_subset_step1PropagationNestedTailFamily_region
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ') :
    ∀ m : Nat,
      p.concretePrimedTierSystem.nestedFamily.region m ⊆
        (step1PropagationNestedTailFamily (paramStream θ') p.probe.1).region m := by
  intro m x hx
  let A := p.concretePrimedTierSystem
  let D :=
    step1FormalPhiPropagationPolynomialNestedTailData (paramStream θ')
      p.probe.1 p.probe.2
  have hfamily : A.nestedFamily = D.toNestedTailFamily := by
    simp [A, D, FixedOStarProbe.concretePrimedTierSystem]
  have hxA : x ∈ A.nestedFamily.region m := by
    simpa [A] using hx
  have hxD : x ∈ D.toNestedTailFamily.region m := by
    simpa [hfamily] using hxA
  have hxFormal :
      x ∈ (step1FormalPhiPropagationNestedTailFamily
          (paramStream θ') p.probe.1 p.probe.2).region m := by
    simpa [D] using hxD
  exact
    (step1FormalPhiPropagationNestedTailFamily_region_subset_step1PropagationNestedTailFamily_region
      (paramStream θ') p.probe.1 p.probe.2 m) hxFormal

/-- Per-fixed-probe Step 1 nested largeness supplies the static interior
leading-coefficient nonvanishing field used by the reduced Step 1 provider. -/
theorem fixedOStarRegularPoleInteriorPropagationLeadingCoeffNonzeroOnRegionDataOfDepthGTOne_of_nestedLargeness
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hnested :
      (p : FixedOStarProbe r L d O θ θ') ->
        Step1PropagationNestedLargenessAssumptionsForDepth
          L d (paramStream θ') p.probe.1 p.iota) :
    FixedOStarRegularPoleInteriorPropagationLeadingCoeffNonzeroOnRegionDataOfDepthGTOne
      hr hStanding := by
  intro _hDepth p m hm x hx
  exact (hnested p).leadingCoeff_ne_on_region m hm x
    ((fixedOStar_concretePrimedTierSystem_region_subset_step1PropagationNestedTailFamily_region
      (p := p) m) hx)

/-- **Generic topological persistence (Claim B, `Z_ε ⊆ T_{j+1}` step).**

Near a zero-free tier point of the tier system built from the concrete primed
stratification and an *arbitrary* polynomial nested family `D`, every regular successor
pole hit has its successor gate prefix in `D`'s nested region.

The proof uses only generic `PolynomialNestedTailData` facts of `D`
(`isOpen_zeroFreeRegion`, `continuousOn_thresholds_zeroFreeRegion`,
`zeroFreeRegion_subset_region`) together with the concrete stratification's gate
analyticity / blow-up.  In particular it does **not** depend on `D` being the formal-phi
tower, so it applies verbatim to the global-product iterated-lc tower — the family for
which `leadingCoeff_ne_on_region` is actually provable (TeX `lem:nested`).  This is the
mechanism that lets the lead-avoidance step use the real nested regions `N_k` instead of
the unprovable exterior polydomain. -/
theorem fixedOStar_eventually_successorPrefix_mem_region_of_regularPoleHit_of_family
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ')
    (D : PolynomialNestedTailData)
    {j : Nat} {τ : ℂ} (hj : j + 1 < L)
    (hτ : τ ∈ (TierSystem.ofPolynomialNestedTailData
      p.concretePrimedStratification D).T0 j) :
    ∀ᶠ z in puncturedNhds τ,
      z ∈ p.concretePrimedStratification.omega (j + 1)
        ∧ p.concretePrimedStratification.H (j + 1) z ∈ oddPiI ->
        gatePrefix p.concretePrimedStratification (j + 1) z ∈
          D.toNestedTailFamily.region (j + 1) := by
  let A := TierSystem.ofPolynomialNestedTailData p.concretePrimedStratification D
  have hfamily : A.nestedFamily = D.toNestedTailFamily := rfl
  have hτA : τ ∈ A.T0 j := hτ
  have hprefix :
      ContinuousAt (fun z => gatePrefix A.stratification j z) τ := by
    refine continuousAt_gatePrefix A.stratification ?_
    intro i
    have hiL : (i : Nat) < L := by omega
    have hτT : τ ∈ A.T j := A.T0_subset_T j hτA
    have hωj : τ ∈ A.stratification.omega j :=
      A.mem_omega (by omega) hτT
    have hωi : τ ∈ A.stratification.omega ((i : Nat) + 1) := by
      rw [ConcreteStratification.omega] at hωj ⊢
      intro hmem
      exact hωj
        (partialUnion_mono_right (S := A.stratification.S) (by omega) hmem)
    exact ((A.stratification.gate_analyticOn (j := (i : Nat)) hiL) τ hωi).continuousAt
  have hpref :
      ∀ᶠ z in puncturedNhds τ,
        gatePrefix A.stratification j z ∈ A.nestedFamily.zeroFreeRegion j := by
    have hτprefix :
        gatePrefix A.stratification j τ ∈ A.nestedFamily.zeroFreeRegion j :=
      A.T0_mem_zeroFreeRegion hτA
    have hzeroOpen : IsOpen (A.nestedFamily.zeroFreeRegion j) := by
      simpa [PolynomialNestedTailData.zeroFreeRegion, hfamily] using
        (D.isOpen_zeroFreeRegion j)
    exact (hprefix.tendsto.eventually (hzeroOpen.mem_nhds hτprefix)).filter_mono
      nhdsWithin_le_nhds
  have hthreshold :
      PuncturedBoundedAt
        (fun z : ℂ =>
          ((A.nestedFamily.threshold j (gatePrefix A.stratification j z) : ℝ) : ℂ))
        τ := by
    have hτprefixA :
        gatePrefix A.stratification j τ ∈ A.nestedFamily.zeroFreeRegion j :=
      A.T0_mem_zeroFreeRegion hτA
    have hτprefixD :
        gatePrefix A.stratification j τ ∈ D.zeroFreeRegion j := by
      simpa [PolynomialNestedTailData.zeroFreeRegion, hfamily] using hτprefixA
    have hthreshold_contD :
        ContinuousAt (D.threshold j) (gatePrefix A.stratification j τ) :=
      (D.continuousOn_thresholds_zeroFreeRegion j).continuousAt
        ((D.isOpen_zeroFreeRegion j).mem_nhds hτprefixD)
    have hthreshold_contR :
        ContinuousAt
          (fun z : ℂ => D.threshold j (gatePrefix A.stratification j z)) τ :=
      hthreshold_contD.comp hprefix
    have hthreshold_contC :
        ContinuousAt
          (fun z : ℂ =>
            ((D.threshold j (gatePrefix A.stratification j z) : ℝ) : ℂ)) τ :=
      Complex.continuous_ofReal.continuousAt.comp hthreshold_contR
    simpa [PolynomialNestedTailData.threshold, hfamily] using
      (PuncturedBoundedAt.of_continuousAt hthreshold_contC)
  have hgate : BlowsUpAt (A.stratification.s j) τ := by
    exact A.stratification.gate_blowsUpAt_of_mem_stratum
      (by omega) (A.T0_mem_stratum hτA)
  have hlarge :
      ∀ᶠ z in puncturedNhds τ,
        A.nestedFamily.threshold j (gatePrefix A.stratification j z) <
          ‖A.stratification.s j z‖ := by
    rcases hthreshold with ⟨C, hC⟩
    rw [BlowsUpAt, Filter.tendsto_atTop] at hgate
    filter_upwards [hC, hgate (C + 1)] with z hCz hsz
    have hthreshold_abs :
        |A.nestedFamily.threshold j (gatePrefix A.stratification j z)| ≤ C := by
      simpa [Real.norm_eq_abs] using hCz
    have hthreshold_le :
        A.nestedFamily.threshold j (gatePrefix A.stratification j z) ≤ C :=
      (le_abs_self _).trans hthreshold_abs
    linarith
  filter_upwards [hpref, hlarge] with z hprefz hlargez hhit
  rcases hhit with ⟨hregular, hpole⟩
  have hS : z ∈ A.stratification.S (j + 1) := by
    simpa [A, FixedOStarProbe.concretePrimedStratification,
      FixedOStarProbe.concretePrimedData,
      ConstantProbeConcreteData.toConcreteStratification,
      ConcreteStratificationData.toConcreteStratification,
      ConstantProbeConcreteData.toConcreteStratificationData,
      ConcreteStratification.omega] using
      constantProbeStratum_mem_of_notMem_previous_and_pole
        (paramStream θ') (Real.log (r : ℝ)) p.probe.1 p.probe.2
        (hprev := by
          simpa [A, FixedOStarProbe.concretePrimedStratification,
            FixedOStarProbe.concretePrimedData,
            ConstantProbeConcreteData.toConcreteStratification,
            ConcreteStratificationData.toConcreteStratification,
            ConstantProbeConcreteData.toConcreteStratificationData,
            ConcreteStratification.omega] using hregular)
        (hpole := by
          simpa [A, FixedOStarProbe.concretePrimedStratification,
            FixedOStarProbe.concretePrimedData,
            ConstantProbeConcreteData.toConcreteStratification,
            ConcreteStratificationData.toConcreteStratification,
            ConstantProbeConcreteData.toConcreteStratificationData] using hpole)
  have hTsucc : z ∈ A.T (j + 1) := by
    refine (A.mem_succ).mpr ?_
    exact ⟨hS, A.nestedFamily.zeroFreeRegion_subset_region j hprefz, hlargez⟩
  exact A.mem_region hTsucc

/-- Near a zero-free tier point, every regular successor pole hit has its successor gate
prefix in the formal-phi nested region.

This is the topological part of the interior Claim-B split: the current zero-free prefix
persists by openness, and the current gate blows up past the threshold.  It is the
formal-phi instance of
`fixedOStar_eventually_successorPrefix_mem_region_of_regularPoleHit_of_family`. -/
theorem fixedOStar_eventually_successorPrefix_mem_region_of_regularPoleHit
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ')
    {j : Nat} {τ : ℂ} (hj : j + 1 < L)
    (hτ : τ ∈ p.concretePrimedTierSystem.T0 j) :
    ∀ᶠ z in puncturedNhds τ,
      z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1)
        ∧ p.concretePrimedTierSystem.stratification.H (j + 1) z ∈ oddPiI ->
        gatePrefix p.concretePrimedTierSystem.stratification (j + 1) z ∈
          p.concretePrimedTierSystem.nestedFamily.region (j + 1) :=
  fixedOStar_eventually_successorPrefix_mem_region_of_regularPoleHit_of_family
    p
    (step1FormalPhiPropagationPolynomialNestedTailData (paramStream θ')
      p.probe.1 p.probe.2)
    hj hτ

/-- **Claim B avoidance assembly (the analytic kernel).**

For the tier system built from the concrete primed stratification and an arbitrary
polynomial nested family `D` whose level-`(j+1)` leading coefficient is nonvanishing on
its nested region `N_{j+1}`, the *frequent* successor pole hits can be taken to *also*
avoid the next leading-coefficient zero locus.

This is the honest form of "a frequently-accumulating set minus the lead-zero locus is
still frequent": the lead-avoidance holds **eventually** (the successor prefix persists
in the open region `N_{j+1}` by `..._of_family`, where the lead is nonzero), so it does
not kill the frequently-many pole hits — `Filter.Frequently.and_eventually`.

Combined with the global-product tower's `globalLcTower_leadingCoeff_ne_on_region`
(`Step1/NestedLargeness.lean`), whose `hlead` hypothesis is provable from
`HasDominantTopCoeff P` alone, this discharges the interior Claim-B lead avoidance on the
real nested regions — the step that was an unprovable wall for the formal-phi tower
(exterior polydomain). -/
theorem fixedOStar_frequently_poleHit_and_leadNonzero_of_family
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ')
    (D : PolynomialNestedTailData)
    {j : Nat} {τ : ℂ} (hj : j + 1 < L)
    (hlead : ∀ x ∈ D.toNestedTailFamily.region (j + 1),
      (D.toNestedTailFamily.step (j + 1)).lead x ≠ 0)
    (hτ : τ ∈ (TierSystem.ofPolynomialNestedTailData
      p.concretePrimedStratification D).T0 j)
    (hpole : ∃ᶠ z in puncturedNhds τ,
      z ∈ p.concretePrimedStratification.omega (j + 1)
        ∧ p.concretePrimedStratification.H (j + 1) z ∈ oddPiI) :
    ∃ᶠ z in puncturedNhds τ,
      (z ∈ p.concretePrimedStratification.omega (j + 1)
        ∧ p.concretePrimedStratification.H (j + 1) z ∈ oddPiI)
        ∧ (D.toNestedTailFamily.step (j + 1)).lead
            (gatePrefix p.concretePrimedStratification (j + 1) z) ≠ 0 := by
  have hpersist :=
    fixedOStar_eventually_successorPrefix_mem_region_of_regularPoleHit_of_family p D hj hτ
  refine (hpole.and_eventually hpersist).mono ?_
  rintro z ⟨hhit, hreg⟩
  exact ⟨hhit, hlead _ (hreg hhit)⟩

/-- **Global-product Claim-B avoidance (the wall, removed).**

The previous lemma instantiated at the global-product iterated-lc tower of any DTC top
polynomial `P` (in practice `P = f_2·⋯·f_L·g`): the `hlead` hypothesis — nonvanishing of
the level-`(j+1)` leading coefficient on the nested region `N_{j+1}` — is supplied by
`globalLcTower_leadingCoeff_ne_on_region`, which holds from `HasDominantTopCoeff P` alone.

So, at a zero-free tier point of the global-product tier system, the frequent successor
pole hits frequently avoid the next leading-coefficient zero locus.  For the formal-phi
tower this same step required nonvanishing on the exterior polydomain, which is false; the
global product replaces that with the genuine nested regions, where it is provable. -/
theorem fixedOStar_globalProduct_frequently_poleHit_and_leadNonzero
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ')
    {n : Nat} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : HasDominantTopCoeff P)
    {j : Nat} {τ : ℂ} (hj : j + 1 < L)
    (hτ : τ ∈ (TierSystem.ofPolynomialNestedTailData
      p.concretePrimedStratification (globalLcNestedTailData n P)).T0 j)
    (hpole : ∃ᶠ z in puncturedNhds τ,
      z ∈ p.concretePrimedStratification.omega (j + 1)
        ∧ p.concretePrimedStratification.H (j + 1) z ∈ oddPiI) :
    ∃ᶠ z in puncturedNhds τ,
      (z ∈ p.concretePrimedStratification.omega (j + 1)
        ∧ p.concretePrimedStratification.H (j + 1) z ∈ oddPiI)
        ∧ ((globalLcNestedTailData n P).toNestedTailFamily.step (j + 1)).lead
            (gatePrefix p.concretePrimedStratification (j + 1) z) ≠ 0 :=
  fixedOStar_frequently_poleHit_and_leadNonzero_of_family p (globalLcNestedTailData n P) hj
    (fun x hx => globalLcTower_leadingCoeff_ne_on_region n hP (j + 1) x hx) hτ hpole

/-- **The global-product tier system `A_gp`** (Step 1, the TeX tier system).

It pairs the concrete primed stratification (so it shares `H`, `omega`, `S`, gate
analyticity, gate blow-up with `concretePrimedTierSystem`) with the iterated-lc tower of
the *single global product* `P = f_2·⋯·f_{n+2}·g`.  Unlike `concretePrimedTierSystem`
(whose formal-phi family has the unprovable exterior-polydomain region), this tier system's
nested regions `N_k` are the genuine TeX regions on which every iterated leading
coefficient is nonvanishing (`globalLcTower_leadingCoeff_ne_on_region`).  In the depth-`L`
application `n = L - 2`. -/
noncomputable def FixedOStarProbe.globalProductTierSystem
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ') (n : Nat) : TierSystem L :=
  TierSystem.ofPolynomialNestedTailData p.concretePrimedStratification
    (globalLcNestedTailData n
      (step1GlobalProductPoly (paramStream θ') p.probe.1 p.iota n))

/-- **Claim-B avoidance for the concrete global-product tier system.**

The previous global-product avoidance, instantiated at the actual Step 1 family product
`P = ∏ a, step1PolynomialFamilyPoly` (DTC from `hasDominantTopCoeff_step1GlobalProductPoly`,
which needs only the standing `O_star` nonvanishing of the `κ_j` and the visible tail).
At a zero-free tier point of `A_gp`, the frequent successor pole hits frequently avoid the
next leading-coefficient zero locus — with no genericity strengthening. -/
theorem fixedOStar_step1GlobalProduct_frequently_poleHit_and_leadNonzero
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ') {n : Nat}
    (hfam : Step1PolynomialFamilyAssumptions (n + 1) d (paramStream θ') p.probe.1 p.iota)
    {j : Nat} {τ : ℂ} (hj : j + 1 < L)
    (hτ : τ ∈ (p.globalProductTierSystem n).T0 j)
    (hpole : ∃ᶠ z in puncturedNhds τ,
      z ∈ p.concretePrimedStratification.omega (j + 1)
        ∧ p.concretePrimedStratification.H (j + 1) z ∈ oddPiI) :
    ∃ᶠ z in puncturedNhds τ,
      (z ∈ p.concretePrimedStratification.omega (j + 1)
        ∧ p.concretePrimedStratification.H (j + 1) z ∈ oddPiI)
        ∧ ((globalLcNestedTailData n
              (step1GlobalProductPoly (paramStream θ') p.probe.1 p.iota n)).toNestedTailFamily.step
                (j + 1)).lead
            (gatePrefix p.concretePrimedStratification (j + 1) z) ≠ 0 :=
  fixedOStar_globalProduct_frequently_poleHit_and_leadNonzero p
    (hasDominantTopCoeff_step1GlobalProductPoly hfam) hj hτ hpole

/-- Compile the static interior region nonvanishing field into the existing eventual
pole-hit avoidance field. -/
theorem fixedOStarInteriorLeadAvoidanceOfDepthGTOne_of_nonzeroOnRegion
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hnonzero :
      FixedOStarRegularPoleInteriorPropagationLeadingCoeffNonzeroOnRegionDataOfDepthGTOne
        hr hStanding) :
    FixedOStarRegularPoleInteriorPropagationLeadingCoeffAvoidanceOnPoleHitDataOfDepthGTOne
      hr hStanding := by
  intro hDepth p j τ hj hτ _hOmega _hH
  have hregion :=
    fixedOStar_eventually_successorPrefix_mem_region_of_regularPoleHit
      (p := p) (j := j) (τ := τ) (by omega) hτ
  have hnonzero_m := hnonzero hDepth p (m := j + 1) (by omega)
  filter_upwards [hregion] with z hz hhit
  exact hnonzero_m
    (gatePrefix p.concretePrimedTierSystem.stratification (j + 1) z)
    (hz hhit)

/-- Compile the interior polynomial zero-locus avoidance plus the explicit last-step
boundary case into the original depth-gated lead-avoidance field. -/
theorem fixedOStarRegularPoleLeadAvoidanceOfDepthGTOne_of_interiorPropagation_and_lastStep
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hinterior :
      FixedOStarRegularPoleInteriorPropagationLeadingCoeffAvoidanceOnPoleHitDataOfDepthGTOne
        hr hStanding)
    (hlast :
      FixedOStarRegularPoleLastStepLeadAvoidanceOnPoleHitDataOfDepthGTOne
        hr hStanding) :
    FixedOStarRegularPoleLeadAvoidanceOnPoleHitDataOfDepthGTOne hr hStanding := by
  intro hDepth p j τ hj hτ hOmega hH
  by_cases hInterior : j + 2 < L
  · have havoidEventual := hinterior hDepth p hInterior hτ hOmega hH
    have hleadEq :=
      fixedOStar_concretePrimedTierSystem_stepLead_eq_step1PropagationLeadingCoeffPoly
        hStanding p (m := j + 1) (by omega)
    filter_upwards [havoidEventual] with z hz hhit
    specialize hz hhit
    rwa [hleadEq]
  · exact hlast hDepth p hj hInterior hτ hOmega hH

/-- Recover the always-on pole-preimage field from the depth-gated one and the
previously proved shallow-depth case. -/
theorem fixedOStarRegularPolePreimageData_of_depth_gt_one_preimageData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hpreimage : FixedOStarRegularPolePreimageDataOfDepthGTOne hr hStanding) :
    FixedOStarRegularPolePreimageData hr hStanding := by
  by_cases hDepth : L <= 1
  · exact fixedOStarRegularPolePreimageData_of_depth_le_one hDepth
  · exact hpreimage (by omega)

/-- Recover the always-on leading-coefficient avoidance field from the depth-gated one
and the previously proved shallow-depth case. -/
theorem fixedOStarRegularPoleLeadAvoidanceOnPoleHitData_of_depth_gt_one_leadAvoidanceData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hlead :
      FixedOStarRegularPoleLeadAvoidanceOnPoleHitDataOfDepthGTOne hr hStanding) :
    FixedOStarRegularPoleLeadAvoidanceOnPoleHitData hr hStanding := by
  by_cases hDepth : L <= 1
  · exact fixedOStarRegularPoleLeadAvoidanceOnPoleHitData_of_depth_le_one hDepth
  · exact hlead (by omega)

/-- Combine the separated pole-hit and leading-coefficient-avoidance Claim-B inputs into
the provider-facing pole-hit-plus-avoidance field. -/
theorem fixedOStarRegularPoleHitAvoidanceData_of_poleHitData_of_leadAvoidanceOnPoleHitData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hpole : FixedOStarRegularPoleHitData hr hStanding)
    (hlead : FixedOStarRegularPoleLeadAvoidanceOnPoleHitData hr hStanding) :
    FixedOStarRegularPoleHitAvoidanceData hr hStanding := by
  intro p j τ hj hτ hOmega hH
  have hpoleFreq := hpole p hj hτ hOmega hH
  have hleadEventual := hlead p hj hτ hOmega hH
  exact (hpoleFreq.and_eventually hleadEventual).mono fun z hz => by
    rcases hz with ⟨⟨hregular, hpolez⟩, hleadz⟩
    exact ⟨hregular, hpolez, hleadz ⟨hregular, hpolez⟩⟩

/-- Combine the preimage-only pole-hit obligation with leading-coefficient avoidance to
recover the provider-facing pole-hit-plus-avoidance field. -/
theorem fixedOStarRegularPoleHitAvoidanceData_of_regularPolePreimage_and_leadAvoidance
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hpreimage : FixedOStarRegularPolePreimageData hr hStanding)
    (hlead : FixedOStarRegularPoleLeadAvoidanceOnPoleHitData hr hStanding) :
    FixedOStarRegularPoleHitAvoidanceData hr hStanding :=
  fixedOStarRegularPoleHitAvoidanceData_of_poleHitData_of_leadAvoidanceOnPoleHitData
    (fixedOStarRegularPoleHitData_of_regularPolePreimageData hpreimage) hlead

/-- Regular pole hits in the concrete successor preactivation give the at-tier Claim B
level-set statement. -/
theorem fixedOStarZeroFreeLevelSetLeadAtTierData_of_regularPoleLeadAtTierData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hpole : FixedOStarRegularPoleLeadAtTierData hr hStanding) :
    FixedOStarZeroFreeLevelSetLeadAtTierData hr hStanding := by
  intro p j τ hj hτ
  have hfreq := hpole p hj hτ
  exact hfreq.mono fun z hz => by
    rcases hz with ⟨hregular, hpolez, hlead⟩
    refine ⟨?_, hlead⟩
    simpa [FixedOStarProbe.concretePrimedTierSystem,
      FixedOStarProbe.concretePrimedStratification,
      FixedOStarProbe.concretePrimedData,
      ConstantProbeConcreteData.toConcreteStratification,
      ConcreteStratificationData.toConcreteStratification,
      ConstantProbeConcreteData.toConcreteStratificationData,
      ConcreteStratification.omega] using
      constantProbeStratum_mem_of_notMem_previous_and_pole
        (paramStream θ') (Real.log (r : ℝ)) p.probe.1 p.probe.2
        (hprev := by
          simpa [FixedOStarProbe.concretePrimedTierSystem,
            FixedOStarProbe.concretePrimedStratification,
            FixedOStarProbe.concretePrimedData,
            ConstantProbeConcreteData.toConcreteStratification,
            ConcreteStratificationData.toConcreteStratification,
            ConstantProbeConcreteData.toConcreteStratificationData,
            ConcreteStratification.omega] using hregular)
        (hpole := by
          simpa [FixedOStarProbe.concretePrimedTierSystem,
            FixedOStarProbe.concretePrimedStratification,
            FixedOStarProbe.concretePrimedData,
            ConstantProbeConcreteData.toConcreteStratification,
            ConcreteStratificationData.toConcreteStratification,
            ConstantProbeConcreteData.toConcreteStratificationData] using hpolez)

/-- The at-tier Claim B input is enough for the previous level-set interface. -/
theorem fixedOStarZeroFreeLevelSetLeadData_of_atTierData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hlevel : FixedOStarZeroFreeLevelSetLeadAtTierData hr hStanding) :
    FixedOStarZeroFreeLevelSetLeadData hr hStanding := by
  intro p j τ hj hτ _hOmega _hH
  exact hlevel p hj hτ

/-- Regular pole hits also supply the older level-set Claim B interface. -/
theorem fixedOStarZeroFreeLevelSetLeadData_of_regularPoleLeadAtTierData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hpole : FixedOStarRegularPoleLeadAtTierData hr hStanding) :
    FixedOStarZeroFreeLevelSetLeadData hr hStanding :=
  fixedOStarZeroFreeLevelSetLeadData_of_atTierData
    (fixedOStarZeroFreeLevelSetLeadAtTierData_of_regularPoleLeadAtTierData hpole)

/-- The concrete primed gate argument is exactly the scaled formal-phi tier path.

This is the `H'_{j+1}(z) = z * φ'_{j+1}(z) + b` identity needed by the scaled
zero-free propagation constructor. -/
theorem fixedOStar_concretePrimedTierSystem_H_eq_scaledTierPhiPath
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ') (j : Nat) :
    p.concretePrimedTierSystem.stratification.H (j + 1) =
      scaledTierPhiPath p.concretePrimedTierSystem j := by
  funext z
  rw [scaledTierPhiPath]
  rw [FixedOStarProbe.concretePrimedTierSystem_tierPhiPath_eq_formalPhi p j z]
  simp [FixedOStarProbe.concretePrimedTierSystem, FixedOStarProbe.concretePrimedStratification,
    TierSystem.ofPolynomialNestedTailData, ConstantProbeConcreteData.toConcreteStratification,
    ConcreteStratificationData.toConcreteStratification,
    ConstantProbeConcreteData.toConcreteStratificationData, constantProbeGateArgument]

/-- Punctured-neighborhood form of
`fixedOStar_concretePrimedTierSystem_H_eq_scaledTierPhiPath`. -/
theorem fixedOStar_concretePrimedTierSystem_H_eventuallyEq_scaledTierPhiPath
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ') (j : Nat) (τ : ℂ) :
    p.concretePrimedTierSystem.stratification.H (j + 1)
      =ᶠ[puncturedNhds τ] scaledTierPhiPath p.concretePrimedTierSystem j :=
  Filter.Eventually.of_forall fun z =>
    congrFun (fixedOStar_concretePrimedTierSystem_H_eq_scaledTierPhiPath p j) z

/-- Package the formal zero-free scaled propagation data for a fixed `O_star` probe.

The concrete Step 1 setup supplies the polynomial tower, the scaled gate identity, gate
prefix continuity, and the quadratic degree.  The only mathematical Claim-B input left
in this constructor is the level-set/nonzero-next-lead statement. -/
noncomputable def fixedOStar_zeroFreeScaledPropagationAnalyticData_of_levelSetLead_frequently
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ')
    (hlevelLead :
      ∀ {j : Nat} {τ : ℂ}, j + 1 < L -> τ ∈ p.concretePrimedTierSystem.T0 j ->
        (∀ᶠ z in puncturedNhds τ,
          z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1)) ->
        BlowsUpAt (p.concretePrimedTierSystem.stratification.H (j + 1)) τ ->
        ∃ᶠ z in puncturedNhds τ,
          z ∈ p.concretePrimedTierSystem.stratification.S (j + 1)
            ∧ (p.concretePrimedTierSystem.nestedFamily.step (j + 1)).lead
              (gatePrefix p.concretePrimedTierSystem.stratification (j + 1) z) ≠ 0) :
    ZeroFreeScaledPropagationAnalyticData p.concretePrimedTierSystem := by
  let A := p.concretePrimedTierSystem
  let D :=
    step1FormalPhiPropagationPolynomialNestedTailData (paramStream θ')
      p.probe.1 p.probe.2
  have hfamily : A.nestedFamily = D.toNestedTailFamily := by
    simp [A, D, FixedOStarProbe.concretePrimedTierSystem]
  have hH_scaled :
      ∀ {j : Nat} {τ : ℂ}, j + 1 < L -> τ ∈ A.T j ->
        A.stratification.H (j + 1) =ᶠ[puncturedNhds τ] scaledTierPhiPath A j := by
    intro j τ _hj _hτ
    simpa [A] using
      fixedOStar_concretePrimedTierSystem_H_eventuallyEq_scaledTierPhiPath
        (p := p) j τ
  have hprefix :
      ∀ {j : Nat} {τ : ℂ}, j + 1 < L -> τ ∈ A.T0 j ->
        ContinuousAt (fun z => gatePrefix A.stratification j z) τ := by
    intro j τ hj hτ
    refine continuousAt_gatePrefix A.stratification ?_
    intro i
    have hiL : (i : Nat) < L := by omega
    have hτT : τ ∈ A.T j := A.T0_subset_T j hτ
    have hωj : τ ∈ A.stratification.omega j :=
      A.mem_omega (by omega) hτT
    have hωi : τ ∈ A.stratification.omega ((i : Nat) + 1) := by
      rw [ConcreteStratification.omega] at hωj ⊢
      intro hmem
      exact hωj
        (partialUnion_mono_right (S := A.stratification.S) (by omega) hmem)
    exact ((A.stratification.gate_analyticOn (j := (i : Nat)) hiL) τ hωi).continuousAt
  have hpoly :
      Step1PolynomialFamilyAssumptionsForDepth L d (paramStream θ') p.probe.1 p.iota :=
    p.step1PolynomialFamilyAssumptionsForDepth hStanding.depth_pos
  have hdegree :
      ∀ {j : Nat} {τ : ℂ}, j + 1 < L -> τ ∈ A.T0 j ->
        (D.tailData j).presentation.degree = 2 := by
    intro j τ hj _hτ
    have hkappa : step1KappaScalar (paramStream θ') j p.probe.1 ≠ 0 :=
      hpoly.kappa_ne ⟨j, by omega⟩
    simpa [D] using
      step1FormalPhiPropagationTailData_degree_eq_two
        (paramStream θ') p.probe.1 p.probe.2 j hkappa
  have hlevelLeadA :
      ∀ {j : Nat} {τ : ℂ}, j + 1 < L -> τ ∈ A.T0 j ->
        (∀ᶠ z in puncturedNhds τ, z ∈ A.stratification.omega (j + 1)) ->
        BlowsUpAt (A.stratification.H (j + 1)) τ ->
        ∃ᶠ z in puncturedNhds τ,
          z ∈ A.stratification.S (j + 1)
            ∧ (A.nestedFamily.step (j + 1)).lead
              (gatePrefix A.stratification (j + 1) z) ≠ 0 := by
    intro j τ hj hτ hOmega hH
    simpa [A] using
      hlevelLead (j := j) (τ := τ) hj (by simpa [A] using hτ)
        (by simpa [A] using hOmega) (by simpa [A] using hH)
  exact
    ZeroFreeScaledPropagationAnalyticData.ofPolynomialNestedTailData
      D hfamily hH_scaled hprefix hdegree hlevelLeadA

/-- The pole-hit-plus-avoidance interface supplies the stronger at-tier regular-pole
interface once the compiled Step 1 tower provides punctured regularity and blow-up at
zero-free tier points. -/
theorem fixedOStarRegularPoleLeadAtTierData_of_poleHitAvoidanceData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hhit : FixedOStarRegularPoleHitAvoidanceData hr hStanding) :
    FixedOStarRegularPoleLeadAtTierData hr hStanding := by
  intro p j τ hj hτ
  let A := p.concretePrimedTierSystem
  have hτA : τ ∈ A.T0 j := by
    simpa [A] using hτ
  have hOmega : ∀ᶠ z in puncturedNhds τ, z ∈ A.stratification.omega (j + 1) := by
    have hjm : j < L := by omega
    exact A.T0_punctured_omega_succ hjm hτA
  have hlevelLead :
      ∀ {k : Nat} {ζ : ℂ}, k + 1 < L -> ζ ∈ p.concretePrimedTierSystem.T0 k ->
        (∀ᶠ z in puncturedNhds ζ,
          z ∈ p.concretePrimedTierSystem.stratification.omega (k + 1)) ->
        BlowsUpAt (p.concretePrimedTierSystem.stratification.H (k + 1)) ζ ->
        ∃ᶠ z in puncturedNhds ζ,
          z ∈ p.concretePrimedTierSystem.stratification.S (k + 1)
            ∧ (p.concretePrimedTierSystem.nestedFamily.step (k + 1)).lead
              (gatePrefix p.concretePrimedTierSystem.stratification (k + 1) z) ≠ 0 := by
    intro k ζ hk hζ hOmegaζ hHζ
    have hfreq := hhit p hk hζ hOmegaζ hHζ
    exact hfreq.mono fun z hz => by
      rcases hz with ⟨hregular, hpolez, hlead⟩
      refine ⟨?_, hlead⟩
      simpa [FixedOStarProbe.concretePrimedTierSystem,
        FixedOStarProbe.concretePrimedStratification,
        FixedOStarProbe.concretePrimedData,
        ConstantProbeConcreteData.toConcreteStratification,
        ConcreteStratificationData.toConcreteStratification,
        ConstantProbeConcreteData.toConcreteStratificationData,
        ConcreteStratification.omega] using
        constantProbeStratum_mem_of_notMem_previous_and_pole
          (paramStream θ') (Real.log (r : ℝ)) p.probe.1 p.probe.2
          (hprev := by
            simpa [FixedOStarProbe.concretePrimedTierSystem,
              FixedOStarProbe.concretePrimedStratification,
              FixedOStarProbe.concretePrimedData,
              ConstantProbeConcreteData.toConcreteStratification,
              ConcreteStratificationData.toConcreteStratification,
              ConstantProbeConcreteData.toConcreteStratificationData,
              ConcreteStratification.omega] using hregular)
          (hpole := by
            simpa [FixedOStarProbe.concretePrimedTierSystem,
              FixedOStarProbe.concretePrimedStratification,
              FixedOStarProbe.concretePrimedData,
              ConstantProbeConcreteData.toConcreteStratification,
              ConcreteStratificationData.toConcreteStratification,
              ConstantProbeConcreteData.toConcreteStratificationData] using hpolez)
  have H : ZeroFreeScaledPropagationAnalyticData A := by
    simpa [A] using
      fixedOStar_zeroFreeScaledPropagationAnalyticData_of_levelSetLead_frequently
        hr hStanding p hlevelLead
  have hBridge : ZeroFreeScaledPropagationBridgeData A :=
    H.toZeroFreeScaledPropagationBridgeData
  have hH : BlowsUpAt (A.stratification.H (j + 1)) τ :=
    ZeroFreeScaledPropagationBridgeData.gateArgument_blowsUpAt hBridge hj hτA
  simpa [A] using hhit p hj hτ (by simpa [A] using hOmega) (by simpa [A] using hH)

/-- Compile the depth-gated preimage/avoidance split back to the at-tier regular-pole
Claim-B field.

For `L <= 1` the at-tier field is empty.  For `1 < L`, the preimage-only pole-hit
statement and eventual leading-coefficient avoidance are combined with the already
compiled punctured regularity and blow-up at zero-free tier points. -/
theorem fixedOStarRegularPoleLeadAtTierData_of_regularPolePreimage_leadAvoidance_depth_gt_one
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hpreimage : FixedOStarRegularPolePreimageDataOfDepthGTOne hr hStanding)
    (hlead :
      FixedOStarRegularPoleLeadAvoidanceOnPoleHitDataOfDepthGTOne hr hStanding) :
    FixedOStarRegularPoleLeadAtTierData hr hStanding := by
  by_cases hDepth : 1 < L
  · exact fixedOStarRegularPoleLeadAtTierData_of_poleHitAvoidanceData
      (fixedOStarRegularPoleHitAvoidanceData_of_regularPolePreimage_and_leadAvoidance
        (hpreimage hDepth) (hlead hDepth))
  · intro _p _j _τ hj _hτ
    omega

/-- Claim-B reduction for a fixed `O_star` probe.

The polynomial tower, scaled concrete `H` identity, prefix continuity, and quadratic
degree are discharged from the concrete Step 1 setup.  The remaining analytic input is the
level-set statement that frequently produces successor-stratum points where the next
leading coefficient is nonzero. -/
theorem fixedOStar_zeroFreeTierPropagation_of_levelSetLead_frequently
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ')
    (hlevelLead :
      ∀ {j : Nat} {τ : ℂ}, j + 1 < L -> τ ∈ p.concretePrimedTierSystem.T0 j ->
        (∀ᶠ z in puncturedNhds τ,
          z ∈ p.concretePrimedTierSystem.stratification.omega (j + 1)) ->
        BlowsUpAt (p.concretePrimedTierSystem.stratification.H (j + 1)) τ ->
        ∃ᶠ z in puncturedNhds τ,
          z ∈ p.concretePrimedTierSystem.stratification.S (j + 1)
            ∧ (p.concretePrimedTierSystem.nestedFamily.step (j + 1)).lead
              (gatePrefix p.concretePrimedTierSystem.stratification (j + 1) z) ≠ 0) :
    ZeroFreeTierPropagation p.concretePrimedTierSystem := by
  let A := p.concretePrimedTierSystem
  have H : ZeroFreeScaledPropagationAnalyticData A :=
    by
      simpa [A] using
        fixedOStar_zeroFreeScaledPropagationAnalyticData_of_levelSetLead_frequently
          _hr hStanding p hlevelLead
  simpa [A] using H.toZeroFreeTierPropagation

/-- TeX Step 1 Claim B interface for a fixed `O_star` probe, reduced to the explicit
level-set-leading-coefficient input above. -/
theorem fixedOStar_zeroFreeTierPropagation_of_tex
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (claimB : FixedOStarZeroFreeLevelSetLeadData hr hStanding)
    (p : FixedOStarProbe r L d O θ θ') :
    ZeroFreeTierPropagation p.concretePrimedTierSystem :=
  fixedOStar_zeroFreeTierPropagation_of_levelSetLead_frequently
    hr hStanding p (claimB p)

/-- Explicit TeX Step 1 Claim C input for all fixed `O_star` probes.

The concrete constant-probe construction supplies continuity of the lower last-layer
terms and of the final visible coefficient.  The remaining last-tier analytic input is
pointwise nonvanishing of that visible coefficient on the concrete last tier. -/
abbrev FixedOStarLastTierVisibleCoeffNonzeroData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (_hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  (p : FixedOStarProbe r L d O θ θ') ->
    ∀ {τ : ℂ}, 0 < L -> τ ∈ p.concretePrimedTierSystem.T (L - 1) ->
      p.concretePrimedTierSystem.stratification.lastLayer.coeff (L - 1) τ ≠ 0

/-- The concrete visible coefficient is evaluation of the corresponding visible
polynomial on the already-constructed gate prefix. -/
theorem constantProbeLastCoeff_eq_eval_formalVisiblePoly
    {d : Nat} (θ : LayerStream d) (b : ℝ)
    (w v : Fin d -> ℝ) (m : Nat) (iota : Fin d) (τ : ℂ) :
    constantProbeLastCoeff θ b w v m iota τ =
      MvPolynomial.eval (fun i : Fin m => constantProbeGate θ b w v (i : Nat) τ)
        (formalVisiblePoly θ m w iota) := by
  let x : Fin m -> ℂ := fun i => constantProbeGate θ b w v (i : Nat) τ
  have heval :=
    congrFun (eval_formalVisiblePoly θ m x w) iota
  have hstream :
      formalVisible θ m (extendGate x) w =
        formalVisible θ m (constantProbeGateStream θ b w v τ) w := by
    exact formalVisible_congr_of_eqOn_lt θ w (by
      intro i hi
      simp [x, extendGate, constantProbeGateStream, hi])
  calc
    constantProbeLastCoeff θ b w v m iota τ =
        formalVisible θ m (constantProbeGateStream θ b w v τ) w iota := by
          simp [constantProbeLastCoeff, formalVisibleCoord]
    _ = formalVisible θ m (extendGate x) w iota := by
          rw [hstream]
    _ = MvPolynomial.eval x (formalVisiblePoly θ m w iota) := by
          simpa using heval.symm

/-- Claim-C provider reduced to the polynomial nonvanishing statement for the visible
coefficient on the concrete last tier.  The last-layer expansion and coefficient
identification are discharged by
`fixedOStarLastTierVisibleCoeffNonzeroData_of_visiblePolynomialNonzero`. -/
abbrev FixedOStarLastTierVisiblePolynomialNonzeroData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (_hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  (p : FixedOStarProbe r L d O θ θ') ->
    ∀ {τ : ℂ}, 0 < L -> τ ∈ p.concretePrimedTierSystem.T (L - 1) ->
      MvPolynomial.eval
          (gatePrefix p.concretePrimedTierSystem.stratification (L - 1) τ)
          (step1VisiblePoly (K := L - 1) (paramStream θ') p.probe.1 p.iota) ≠ 0

/-- The visible-polynomial nested zero-free regions, obtained by peeling the visible
polynomials `g_{m+1}` in the last gate variable at every depth `m + 1`. -/
noncomputable def step1VisibleNestedTailData {d : Nat}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (iota : Fin d) : PolynomialNestedTailData :=
  PolynomialNestedTailData.ofPolynomials
    (fun m => step1VisiblePoly (K := m + 1) θ w iota)

/-- Membership in the visible zero-free nested region gives pointwise nonvanishing of
the visible polynomial.  At depth zero, the `O_star` visible-coordinate field already
makes the constant visible polynomial nonzero. -/
theorem eval_step1VisiblePoly_ne_zero_of_visibleZeroFreeRegion
    {K d : Nat}
    {θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
    {w : Fin d → ℝ} {iota : Fin d}
    (hpoly : Step1PolynomialFamilyAssumptions K d θ w iota)
    {z : Fin K → ℂ}
    (hz : z ∈ (step1VisibleNestedTailData θ w iota).zeroFreeRegion K) :
    MvPolynomial.eval z (step1VisiblePoly (K := K) θ w iota) ≠ 0 := by
  cases K with
  | zero =>
      exact eval_ne_zero_of_ne_zero_fin_zero
        hpoly.hasDominantTopCoeff_visible.ne_zero z
  | succ m =>
      let D := step1VisibleNestedTailData θ w iota
      have hne : MvPolynomial.eval z (D.tailData m).poly ≠ 0 :=
        D.zeroFreeRegion_eval_ne_zero_of_mem_succ (m := m) hz
      simpa [D, step1VisibleNestedTailData] using hne

/-- The depth-one visible-polynomial Claim-C field is already forced by the fixed
`O_star` visible-coordinate choice.

For `L = 1`, the last visible polynomial has no gate variables, so nonvanishing of its
dominant coefficient is pointwise nonvanishing everywhere.  The impossible `L = 0` case
is discharged by the field's own `0 < L` argument. -/
theorem fixedOStarLastTierVisiblePolynomialNonzeroData_of_depth_le_one
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (hDepth : L <= 1) :
    FixedOStarLastTierVisiblePolynomialNonzeroData hr hStanding := by
  intro p τ hL _hτ
  have hL_eq : L = 1 := by omega
  subst L
  have hpoly :
      Step1PolynomialFamilyAssumptionsForDepth 1 d (paramStream θ') p.probe.1 p.iota :=
    p.step1PolynomialFamilyAssumptionsForDepth hL
  exact
    eval_ne_zero_of_ne_zero_fin_zero
      hpoly.hasDominantTopCoeff_visible.ne_zero
      (gatePrefix p.concretePrimedTierSystem.stratification (1 - 1) τ)

/-- Depth-sharpened pointwise Claim-C obligation.

The `L <= 1` branch is already proved from the fixed `O_star` visible coordinate, so
the pointwise visible-polynomial nonvanishing field only has to be supplied in the
genuine depth-`> 1` case. -/
abbrev FixedOStarLastTierVisiblePolynomialNonzeroDataOfDepthGTOne
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  1 < L -> FixedOStarLastTierVisiblePolynomialNonzeroData hr hStanding

/-- Exact TeX Claim-C region form for the depth-`> 1` branch.

The last-tier point already supplies membership of its gate prefix in the concrete
formal-phi nested region.  Claim C only needs the visible polynomial `g` to be nonzero
on that last region; it does not need the stronger tower inclusion into the visible
zero-free nested region. -/
abbrev FixedOStarLastTierVisiblePolynomialNonzeroOnLastRegionDataOfDepthGTOne
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (_hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  1 < L ->
    (p : FixedOStarProbe r L d O θ θ') ->
      ∀ z ∈ p.concretePrimedTierSystem.nestedFamily.region (L - 1),
        MvPolynomial.eval z
          (step1VisiblePoly (K := L - 1) (paramStream θ') p.probe.1 p.iota) ≠ 0

/-- Generic Step 1 Claim-C visible nonvanishing on the propagation nested-largeness
region.

This is closer to the polynomial-family/nested-largeness layer than the concrete
fixed-probe last-region statement: the concrete formal-phi last region is already known
to sit inside this propagation region for each fixed `O_star` probe. -/
abbrev Step1VisiblePolynomialNonzeroOnPropagationLastRegionAssumptionsForDepth
    (L d : Nat)
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d -> ℝ) (iota : Fin d) : Prop :=
  1 < L ->
    ∀ z ∈ (step1PropagationNestedTailFamily θ w).region (L - 1),
      MvPolynomial.eval z (step1VisiblePoly (K := L - 1) θ w iota) ≠ 0

/-- Corrected visible-polynomial nonvanishing statement on the combined
propagation-visible zero-free region.

This is the TeX nested-region target: the tower includes both the propagation factors
and the visible factor, so visible nonvanishing is read off from the combined
zero-free region instead of the propagation-only exterior region. -/
abbrev Step1VisiblePolynomialNonzeroOnPropagationVisibleLastRegionAssumptionsForDepth
    (L d : Nat)
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d -> ℝ) (iota : Fin d) : Prop :=
  1 < L ->
    ∀ z ∈ (step1PropagationVisibleNestedTailData θ w iota).zeroFreeRegion (L - 1),
      MvPolynomial.eval z (step1VisiblePoly (K := L - 1) θ w iota) ≠ 0

/-- Combined Step 1 propagation-region primitive for a fixed probe.

The nested-largeness field supplies interior leading-coefficient nonvanishing, while the
visible field supplies the last-region Claim-C polynomial nonvanishing. -/
structure Step1PropagationPrimitiveAssumptionsForDepth
    (L d : Nat)
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d -> ℝ) (iota : Fin d) : Prop where
  nestedLargeness :
    Step1PropagationNestedLargenessAssumptionsForDepth L d θ w iota
  visiblePolynomialNonzeroOnLastRegion :
    Step1VisiblePolynomialNonzeroOnPropagationLastRegionAssumptionsForDepth
      L d θ w iota

/-- Slice zero-free form of the propagation nested-largeness nonvanishing field.

The propagation step polynomial is independent of the newly peeled variable, so
nonvanishing of the extracted leading coefficient on the recursive region is equivalent
to nonvanishing of the concrete propagation polynomial after adjoining any fixed last
coordinate.  The zero slice is the narrow form already exposed by
`leadingCoeff_ne_on_region_iff_tailPoly_snoc_zero_ne_on_region`. -/
abbrev Step1PropagationTailSliceNonzeroOnRegionAssumptionsForDepth
    (L d : Nat)
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d -> ℝ) : Prop :=
  ∀ m : Nat, m < L - 1 ->
    ∀ x : Fin m -> ℂ,
      x ∈ (step1PropagationNestedTailFamily θ w).region m ->
        MvPolynomial.eval (Fin.snoc x 0) (step1PropagationTailPoly θ w m) ≠ 0

/-- Positive-tail part of the propagation slice zero-free witness.

The base slice `m = 0` is forced by the polynomial-family certificate because it has no
previous gate variables.  This interface keeps only the genuine recursive slice
nonvanishing obligations. -/
abbrev Step1PropagationPositiveTailSliceNonzeroOnRegionAssumptionsForDepth
    (L d : Nat)
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d -> ℝ) : Prop :=
  ∀ m : Nat, 0 < m -> m < L - 1 ->
    ∀ x : Fin m -> ℂ,
      x ∈ (step1PropagationNestedTailFamily θ w).region m ->
        MvPolynomial.eval (Fin.snoc x 0) (step1PropagationTailPoly θ w m) ≠ 0

/-- Corrected positive-tail propagation factor nonvanishing statement on the combined
propagation-visible zero-free region.

At successor level `m + 1`, membership in the combined zero-free region makes the
product polynomial nonzero, hence in particular the propagation factor
`step1PropagationTailPoly θ w m` is nonzero. -/
abbrev Step1PropagationPositiveTailSliceNonzeroOnPropagationVisibleRegionAssumptionsForDepth
    (L d : Nat)
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d -> ℝ) (iota : Fin d) : Prop :=
  ∀ m : Nat, 0 < m -> m < L - 1 ->
    ∀ z : Fin (m + 1) -> ℂ,
      z ∈ (step1PropagationVisibleNestedTailData θ w iota).zeroFreeRegion (m + 1) ->
        MvPolynomial.eval z (step1PropagationTailPoly θ w m) ≠ 0

/-- Reconstruct the full propagation slice zero-free witness from its positive-tail
part and the polynomial-family certificate.

The missing `m = 0` branch reduces to pointwise nonvanishing of a polynomial in no
variables, already proved from the dominant top coefficient. -/
theorem step1PropagationTailSliceNonzeroOnRegionAssumptionsForDepth_of_positiveTailSlice
    {L d : Nat}
    {θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
    {w : Fin d -> ℝ} {iota : Fin d}
    (hpoly : Step1PolynomialFamilyAssumptionsForDepth L d θ w iota)
    (hpositive :
      Step1PropagationPositiveTailSliceNonzeroOnRegionAssumptionsForDepth
        L d θ w) :
    Step1PropagationTailSliceNonzeroOnRegionAssumptionsForDepth L d θ w := by
  intro m hm x hx
  by_cases hzero : m = 0
  · subst m
    rw [eval_step1PropagationTailPoly_snoc_eq_leadingCoeff_eval]
    exact eval_step1PropagationLeadingCoeffPoly_zero_ne_of_depth hpoly hm x
  · have hpos : 0 < m := by omega
    exact hpositive m hpos hm x hx

/-- Polynomial-family/certificate-facing form of the Step 1 propagation primitive.

This keeps the algebraic nonzero data from `Step1PolynomialFamilyAssumptionsForDepth`
separate from the two genuine pointwise zero-free statements: propagation-tail
zero-freeness on the recursive region and visible-polynomial nonvanishing on the last
propagation region. -/
structure Step1PropagationPrimitivePolynomialWitnessAssumptionsForDepth
    (L d : Nat)
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d -> ℝ) (iota : Fin d) : Prop where
  polynomialFamily : Step1PolynomialFamilyAssumptionsForDepth L d θ w iota
  propagationTailSliceNonzeroOnRegion :
    Step1PropagationTailSliceNonzeroOnRegionAssumptionsForDepth L d θ w
  visiblePolynomialNonzeroOnLastRegion :
    Step1VisiblePolynomialNonzeroOnPropagationLastRegionAssumptionsForDepth
      L d θ w iota

/-- Minimal zero-free part of the propagation primitive once the polynomial-family
certificate is supplied elsewhere.

For fixed `O_star` probes, the polynomial-family field is already a consequence of the
standing Step 1 assumptions, so callers only need to provide these two pointwise
nonvanishing witnesses. -/
structure Step1PropagationPrimitiveZeroFreeWitnessAssumptionsForDepth
    (L d : Nat)
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d -> ℝ) (iota : Fin d) : Prop where
  propagationTailSliceNonzeroOnRegion :
    Step1PropagationTailSliceNonzeroOnRegionAssumptionsForDepth L d θ w
  visiblePolynomialNonzeroOnLastRegion :
    Step1VisiblePolynomialNonzeroOnPropagationLastRegionAssumptionsForDepth
      L d θ w iota

/-- Base-tail-reduced zero-free part of the propagation primitive.

For fixed `O_star` probes, both the polynomial-family certificate and the base
propagation slice `m = 0` are mechanical consequences of the standing assumptions, so
callers only provide positive-tail slice zero-freeness and the last-region visible
nonvanishing witness. -/
structure Step1PropagationPrimitiveBaseTailReducedZeroFreeWitnessAssumptionsForDepth
    (L d : Nat)
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d -> ℝ) (iota : Fin d) : Prop where
  propagationPositiveTailSliceNonzeroOnRegion :
    Step1PropagationPositiveTailSliceNonzeroOnRegionAssumptionsForDepth L d θ w
  visiblePolynomialNonzeroOnLastRegion :
    Step1VisiblePolynomialNonzeroOnPropagationLastRegionAssumptionsForDepth
      L d θ w iota

/-- Compile the base-tail-reduced zero-free witness to the current zero-free witness
once a polynomial-family certificate is available. -/
theorem step1PropagationPrimitiveZeroFreeWitnessAssumptionsForDepth_of_baseTailReduced
    {L d : Nat}
    {θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
    {w : Fin d -> ℝ} {iota : Fin d}
    (hpoly : Step1PolynomialFamilyAssumptionsForDepth L d θ w iota)
    (h :
      Step1PropagationPrimitiveBaseTailReducedZeroFreeWitnessAssumptionsForDepth
        L d θ w iota) :
    Step1PropagationPrimitiveZeroFreeWitnessAssumptionsForDepth L d θ w iota where
  propagationTailSliceNonzeroOnRegion :=
    step1PropagationTailSliceNonzeroOnRegionAssumptionsForDepth_of_positiveTailSlice
      hpoly h.propagationPositiveTailSliceNonzeroOnRegion
  visiblePolynomialNonzeroOnLastRegion :=
    h.visiblePolynomialNonzeroOnLastRegion

/-- Fixed-`O_star` version of the base-tail-reduced propagation compiler, filling the
polynomial-family certificate from the standing assumptions. -/
theorem step1PropagationPrimitiveZeroFreeWitnessAssumptionsForDepth_of_fixedOStar_baseTailReduced
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ')
    (h :
      Step1PropagationPrimitiveBaseTailReducedZeroFreeWitnessAssumptionsForDepth
        L d (paramStream θ') p.probe.1 p.iota) :
    Step1PropagationPrimitiveZeroFreeWitnessAssumptionsForDepth
      L d (paramStream θ') p.probe.1 p.iota :=
  step1PropagationPrimitiveZeroFreeWitnessAssumptionsForDepth_of_baseTailReduced
    (p.step1PolynomialFamilyAssumptionsForDepth hStanding.depth_pos) h

/-- For fixed `O_star` probes, compile the minimal zero-free propagation witness to the
polynomial-witness package by filling the polynomial-family certificate from the
standing assumptions. -/
theorem step1PropagationPrimitivePolynomialWitnessAssumptionsForDepth_of_fixedOStar_zeroFreeWitness
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ')
    (h :
      Step1PropagationPrimitiveZeroFreeWitnessAssumptionsForDepth
        L d (paramStream θ') p.probe.1 p.iota) :
    Step1PropagationPrimitivePolynomialWitnessAssumptionsForDepth
      L d (paramStream θ') p.probe.1 p.iota where
  polynomialFamily := p.step1PolynomialFamilyAssumptionsForDepth hStanding.depth_pos
  propagationTailSliceNonzeroOnRegion :=
    h.propagationTailSliceNonzeroOnRegion
  visiblePolynomialNonzeroOnLastRegion :=
    h.visiblePolynomialNonzeroOnLastRegion

/-- Compile the polynomial-family plus narrow zero-free/visible witness package to the
current combined propagation primitive. -/
theorem step1PropagationPrimitiveAssumptionsForDepth_of_polynomialWitness
    {L d : Nat}
    {θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
    {w : Fin d -> ℝ} {iota : Fin d}
    (h :
      Step1PropagationPrimitivePolynomialWitnessAssumptionsForDepth
        L d θ w iota) :
    Step1PropagationPrimitiveAssumptionsForDepth L d θ w iota where
  nestedLargeness :=
    step1PropagationNestedLargenessAssumptionsForDepth_of_tailPoly_snoc_zero_ne_on_region
      h.polynomialFamily h.propagationTailSliceNonzeroOnRegion
  visiblePolynomialNonzeroOnLastRegion :=
    h.visiblePolynomialNonzeroOnLastRegion

/-- The generic propagation-region visible nonvanishing statement implies the concrete
last-region Claim-C field.

The only bridge used here is the already-proved inclusion from the concrete fixed-probe
formal-phi nested region into the Step 1 propagation nested-largeness region. -/
theorem fixedOStarVisibleNonzeroOnLastRegionOfDepthGTOne_of_step1PropagationVisibleNonzero
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hvisible :
      (p : FixedOStarProbe r L d O θ θ') ->
        Step1VisiblePolynomialNonzeroOnPropagationLastRegionAssumptionsForDepth
          L d (paramStream θ') p.probe.1 p.iota) :
    FixedOStarLastTierVisiblePolynomialNonzeroOnLastRegionDataOfDepthGTOne
      hr hStanding := by
  intro hDepth p z hz
  exact hvisible p hDepth z
    ((fixedOStar_concretePrimedTierSystem_region_subset_step1PropagationNestedTailFamily_region
      (p := p) (L - 1)) hz)

/-- The exact last-region nonvanishing form implies the pointwise Claim-C provider
field.

This is the concrete use of TeX `(R)` in Claim C: last-tier membership gives the gate
prefix in the formal-phi region, and the region nonvanishing hypothesis evaluates `g`
there. -/
theorem fixedOStarLastTierVisiblePolynomialNonzeroDataOfDepthGTOne_of_visibleNonzeroOnLastRegionData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hvisibleRegion :
      FixedOStarLastTierVisiblePolynomialNonzeroOnLastRegionDataOfDepthGTOne
        hr hStanding) :
    FixedOStarLastTierVisiblePolynomialNonzeroDataOfDepthGTOne hr hStanding := by
  intro hDepth p τ _hL hτ
  exact hvisibleRegion hDepth p
    (gatePrefix p.concretePrimedTierSystem.stratification (L - 1) τ)
    (p.concretePrimedTierSystem.mem_region hτ)

/-- Recover the always-on pointwise Claim-C field from the depth-gated version and the
already-closed depth-`<= 1` branch. -/
theorem fixedOStarLastTierVisiblePolynomialNonzeroData_of_depth_gt_one_visiblePolynomialNonzeroData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (hvisible :
      FixedOStarLastTierVisiblePolynomialNonzeroDataOfDepthGTOne hr hStanding) :
    FixedOStarLastTierVisiblePolynomialNonzeroData hr hStanding := by
  by_cases hDepth : L <= 1
  · exact fixedOStarLastTierVisiblePolynomialNonzeroData_of_depth_le_one
      hr hStanding hDepth
  · exact hvisible (by omega)

/-- Smaller Claim-C obligation for fixed `O_star` probes.

Instead of asking directly that the visible polynomial is nonzero at every last-tier
prefix, this asks that the last-tier gate prefix lies in the visible polynomial's
zero-free nested region.  The wrapper
`fixedOStarLastTierVisiblePolynomialNonzeroData_of_visibleNestedRegion` combines this
with the already-proved fixed-`O_star` polynomial-family facts. -/
abbrev FixedOStarLastTierVisibleNestedRegionData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hr : 2 <= r)
    (_hStanding : Step1StandingAssumptions r L d O θ θ') : Prop :=
  (p : FixedOStarProbe r L d O θ θ') ->
    ∀ {τ : ℂ}, 0 < L -> τ ∈ p.concretePrimedTierSystem.T (L - 1) ->
      gatePrefix p.concretePrimedTierSystem.stratification (L - 1) τ ∈
        (step1VisibleNestedTailData (paramStream θ') p.probe.1 p.iota).zeroFreeRegion
          (L - 1)

/-- Compile the visible-region Claim-C obligation to the previous polynomial
nonvanishing interface. -/
theorem fixedOStarLastTierVisiblePolynomialNonzeroData_of_visibleNestedRegion
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (hregion : FixedOStarLastTierVisibleNestedRegionData hr hStanding) :
    FixedOStarLastTierVisiblePolynomialNonzeroData hr hStanding := by
  intro p τ hL hτ
  have hpoly :
      Step1PolynomialFamilyAssumptionsForDepth L d (paramStream θ') p.probe.1 p.iota :=
    p.step1PolynomialFamilyAssumptionsForDepth hL
  exact
    eval_step1VisiblePoly_ne_zero_of_visibleZeroFreeRegion
      (K := L - 1) hpoly (hregion p hL hτ)

/-- Last-layer coefficient identification for fixed `O_star` probes. -/
theorem fixedOStar_lastLayer_visibleCoeff_eq_step1VisiblePoly
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ')
    (hL : 0 < L) (τ : ℂ) :
    p.concretePrimedTierSystem.stratification.lastLayer.coeff (L - 1) τ =
      MvPolynomial.eval
        (gatePrefix p.concretePrimedTierSystem.stratification (L - 1) τ)
        (step1VisiblePoly (K := L - 1) (paramStream θ') p.probe.1 p.iota) := by
  cases L with
  | zero =>
      omega
  | succ m =>
      let A := p.concretePrimedTierSystem
      have hcoeff :
          A.stratification.lastLayer.coeff m τ =
            constantProbeLastCoeff (paramStream θ') (Real.log (r : ℝ))
              p.probe.1 p.probe.2 m p.iota τ := by
        simp [A, FixedOStarProbe.concretePrimedTierSystem,
          FixedOStarProbe.concretePrimedStratification,
          ConstantProbeConcreteData.toConcreteStratification,
          ConcreteStratificationData.toConcreteStratification,
          ConstantProbeConcreteData.toConcreteStratificationData,
          constantProbeObservableExpansion, constantProbeLastLayerExpansion_succ,
          LastLayerExpansion.snoc, LastLayerExpansion.coeffSnoc]
      have hpoly :=
        constantProbeLastCoeff_eq_eval_formalVisiblePoly
          (paramStream θ') (Real.log (r : ℝ)) p.probe.1 p.probe.2 m p.iota τ
      calc
        p.concretePrimedTierSystem.stratification.lastLayer.coeff ((m + 1) - 1) τ =
            constantProbeLastCoeff (paramStream θ') (Real.log (r : ℝ))
              p.probe.1 p.probe.2 m p.iota τ := by
              simpa [A] using hcoeff
        _ = MvPolynomial.eval
              (gatePrefix p.concretePrimedTierSystem.stratification ((m + 1) - 1) τ)
              (step1VisiblePoly (K := (m + 1) - 1) (paramStream θ')
                p.probe.1 p.iota) := by
              simpa [FixedOStarProbe.concretePrimedTierSystem,
                FixedOStarProbe.concretePrimedStratification,
                FixedOStarProbe.concretePrimedData,
                ConstantProbeConcreteData.toConcreteStratification,
                ConcreteStratificationData.toConcreteStratification,
                ConstantProbeConcreteData.toConcreteStratificationData,
                gatePrefix, step1VisiblePoly] using hpoly

/-- The fixed-probe tier system with the same concrete stratification as
`p.concretePrimedTierSystem`, but with the combined propagation-visible nested tower.

This is the corrected TeX-style target for Claim C: the last tier is cut out using a
tower that includes the visible polynomial, instead of the propagation-only tower whose
region is merely an exterior polydomain. -/
noncomputable def FixedOStarProbe.propagationVisibleTierSystem
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ') : TierSystem L :=
  TierSystem.ofPolynomialNestedTailData
    p.concretePrimedTierSystem.stratification
    (step1PropagationVisibleNestedTailData (paramStream θ') p.probe.1 p.iota)

/-! ## Decoupled combined-tier Claim B (corrected TeX path)

The combined propagation-visible tier system `propagationVisibleTierSystem` shares its
stratification with the concrete formal-phi system `concretePrimedTierSystem`, but its
nested family is the combined product tower `f_{j+2} · g_{j+1}`.  The scaled formal-phi
identity `H'_{j+1} = z·φ'_{j+1} + b` is therefore *false* for the combined tower's own
step polynomial.  The lemmas below assemble Claim B for the combined tier directly through
`ZeroFreeDecoupledPropagationData`: blow-up of `H'_{j+1}` is sourced from the formal-phi
system (whose scaled identity is genuine), while all tier membership uses the combined
zero-free regions. -/

/-- Continuity of a one-step tail threshold at any point where the leading coefficient is
nonzero.  The threshold is continuous on the open lead-nonzero locus, which is a
neighborhood of any of its points. -/
theorem continuousAt_tailPresentation_threshold_of_lead_ne {α : Type*}
    [TopologicalSpace α] (P : TailPresentation α) {x : α}
    (hlead : Continuous P.lead)
    (hlower : ∀ i : Fin P.degree, Continuous (P.lower i))
    (hx : P.lead x ≠ 0) :
    ContinuousAt P.threshold x := by
  have hopen : IsOpen {y : α | P.lead y ≠ 0} := by
    have hset : {y : α | P.lead y ≠ 0} = P.lead ⁻¹' ({0}ᶜ) := by
      ext y; simp
    rw [hset]
    exact hlead.isOpen_preimage _ isOpen_compl_singleton
  refine (P.continuousOn_threshold hlead.continuousOn
    (fun i => (hlower i).continuousOn) (fun y hy => hy)).continuousAt ?_
  exact hopen.mem_nhds hx

/-- Gate-prefix continuity at any concrete-stratum point.  This depends only on the shared
stratification, so it serves both the formal-phi and combined propagation-visible tier
systems. -/
theorem fixedOStar_gatePrefix_continuousAt_of_mem_stratum
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ') {j : Nat} {τ : ℂ} (hj : j < L)
    (hτ : τ ∈ p.concretePrimedTierSystem.stratification.S j) :
    ContinuousAt
      (fun z => gatePrefix p.concretePrimedTierSystem.stratification j z) τ := by
  refine continuousAt_gatePrefix p.concretePrimedTierSystem.stratification ?_
  intro i
  have hiL : (i : Nat) < L := by omega
  have hωj : τ ∈ p.concretePrimedTierSystem.stratification.omega j :=
    p.concretePrimedTierSystem.stratification.mem_omega_of_mem_stratum hj hτ
  have hωi : τ ∈ p.concretePrimedTierSystem.stratification.omega ((i : Nat) + 1) := by
    rw [ConcreteStratification.omega] at hωj ⊢
    intro hmem
    exact hωj
      (partialUnion_mono_right (S := p.concretePrimedTierSystem.stratification.S)
        (by omega) hmem)
  exact ((p.concretePrimedTierSystem.stratification.gate_analyticOn
    (j := (i : Nat)) hiL) τ hωi).continuousAt

/-- The `j`-th formal-phi nested step is the canonical last-variable presentation of the
formal-phi propagation polynomial `f_{j+2}`. -/
theorem fixedOStar_concretePrimedTierSystem_step_eq
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ') (j : Nat) :
    p.concretePrimedTierSystem.nestedFamily.step j =
      polynomialTailPresentation
        (step1FormalPhiPropagationTailPoly (paramStream θ') p.probe.1 p.probe.2 j) := by
  simp [FixedOStarProbe.concretePrimedTierSystem, step1FormalPhiPropagationTailData,
    PolynomialTailPresentationData.ofPolynomial]

/-- The formal-phi leading coefficient `f_{j+2}` is nonzero at the prefix of a combined
propagation-visible zero-free tier point.  This is the decoupling bridge: combined-region
membership controls the *formal-phi* leading coefficient even though the combined tower's
own step polynomial is the product `f_{j+2} · g_{j+1}`. -/
theorem fixedOStar_formalPhiLead_ne_of_mem_propagationVisibleTierSystem_T0
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ') {j : Nat} {τ : ℂ} (hj : j < L - 1)
    (hτ : τ ∈ p.propagationVisibleTierSystem.T0 j) :
    (p.concretePrimedTierSystem.nestedFamily.step j).lead
        (gatePrefix p.concretePrimedTierSystem.stratification j τ) ≠ 0 := by
  have hzfree :
      gatePrefix p.concretePrimedTierSystem.stratification j τ ∈
        (step1PropagationVisibleNestedTailData (paramStream θ') p.probe.1
          p.iota).zeroFreeRegion j := by
    simpa [FixedOStarProbe.propagationVisibleTierSystem,
      PolynomialNestedTailData.zeroFreeRegion] using
      p.propagationVisibleTierSystem.T0_mem_zeroFreeRegion hτ
  rw [fixedOStar_concretePrimedTierSystem_stepLead_eq_step1PropagationLeadingCoeffPoly
    hStanding p hj]
  exact
    eval_step1PropagationLeadingCoeffPoly_ne_zero_of_propagationVisibleZeroFreeRegion hzfree

/-- **Generic blow-up of `H'_{j+1}` (TeX Claim B, steps i–iii).**

At a stratum point `τ ∈ S'^j` with `τ ≠ 0` where the formal-phi leading coefficient
`f_{j+1}(s'_{<j}(τ))` is nonzero, the next preactivation `H'_{j+1}` blows up: the gate
`s'_j` blows up (stratum), so `φ'_{j+1} = f_{j+1}·s'_j² + c_1·s'_j + c_0` blows up
(quadratic with nonzero leading coefficient and bounded threshold), hence so does
`H'_{j+1} = τ·φ'_{j+1} + b`.

This isolates exactly the data needed for blow-up — `τ ∈ S'^j`, `τ ≠ 0`, and the
formal-phi lead `≠ 0` — independent of which tier system supplied the point.  In
particular it applies to the global-product tier system `A_gp`, whose tier points share
this stratification, once the formal-phi lead is shown nonzero there. -/
theorem fixedOStar_H_blowsUpAt_of_stratum_formalPhiLead_ne
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ') {j : Nat} {τ : ℂ} (hj : j + 1 < L)
    (hτS : τ ∈ p.concretePrimedTierSystem.stratification.S j)
    (hτ0 : τ ≠ 0)
    (hlead0 :
      (p.concretePrimedTierSystem.nestedFamily.step j).lead
        (gatePrefix p.concretePrimedTierSystem.stratification j τ) ≠ 0) :
    BlowsUpAt (p.concretePrimedTierSystem.stratification.H (j + 1)) τ := by
  have hjm : j < L := by omega
  have hjL1 : j < L - 1 := by omega
  have hgate :
      BlowsUpAt (p.concretePrimedTierSystem.stratification.s j) τ :=
    p.concretePrimedTierSystem.stratification.gate_blowsUpAt_of_mem_stratum hjm hτS
  have hprefix :
      ContinuousAt
        (fun z => gatePrefix p.concretePrimedTierSystem.stratification j z) τ :=
    fixedOStar_gatePrefix_continuousAt_of_mem_stratum p hjm hτS
  have hpoly :
      Step1PolynomialFamilyAssumptionsForDepth L d (paramStream θ') p.probe.1 p.iota :=
    p.step1PolynomialFamilyAssumptionsForDepth hStanding.depth_pos
  have hkappa : step1KappaScalar (paramStream θ') j p.probe.1 ≠ 0 :=
    hpoly.kappa_ne ⟨j, hjL1⟩
  have hstepeq := fixedOStar_concretePrimedTierSystem_step_eq p j
  have hleadCont :
      Continuous (p.concretePrimedTierSystem.nestedFamily.step j).lead := by
    rw [hstepeq]
    exact continuous_polynomialTailPresentation_lead _
  have hlowerCont :
      ∀ i : Fin (p.concretePrimedTierSystem.nestedFamily.step j).degree,
        Continuous ((p.concretePrimedTierSystem.nestedFamily.step j).lower i) := by
    rw [hstepeq]
    intro i
    exact continuous_polynomialTailPresentation_lower _ i
  have hthresholdCont :
      ContinuousAt (p.concretePrimedTierSystem.nestedFamily.threshold j)
        (gatePrefix p.concretePrimedTierSystem.stratification j τ) :=
    continuousAt_tailPresentation_threshold_of_lead_ne
      (p.concretePrimedTierSystem.nestedFamily.step j) hleadCont hlowerCont hlead0
  have hthreshold :
      PuncturedBoundedAt
        (fun z : ℂ =>
          ((p.concretePrimedTierSystem.nestedFamily.threshold j
            (gatePrefix p.concretePrimedTierSystem.stratification j z) : ℝ) : ℂ)) τ := by
    have hcomp :
        ContinuousAt
          (fun z : ℂ =>
            ((p.concretePrimedTierSystem.nestedFamily.threshold j
              (gatePrefix p.concretePrimedTierSystem.stratification j z) : ℝ) : ℂ)) τ :=
      Complex.continuous_ofReal.continuousAt.comp (hthresholdCont.comp hprefix)
    exact PuncturedBoundedAt.of_continuousAt hcomp
  have hdeg : (p.concretePrimedTierSystem.nestedFamily.step j).degree = 2 := by
    rw [hstepeq]
    have := step1FormalPhiPropagationTailData_degree_eq_two
      (paramStream θ') p.probe.1 p.probe.2 j hkappa
    simpa [step1FormalPhiPropagationTailData, PolynomialTailPresentationData.ofPolynomial]
      using this
  have hlead_tendsto :
      Filter.Tendsto (tierLeadingCoeffPath p.concretePrimedTierSystem j) (puncturedNhds τ)
        (nhds ((p.concretePrimedTierSystem.nestedFamily.step j).lead
          (gatePrefix p.concretePrimedTierSystem.stratification j τ))) :=
    tierLeadingCoeffPath_tendsto_of_continuousAt p.concretePrimedTierSystem hprefix
      hleadCont.continuousAt
  have hphi : BlowsUpAt (tierPhiPath p.concretePrimedTierSystem j) τ :=
    phi_blowsUpAt_of_quadratic_threshold p.concretePrimedTierSystem hdeg hthreshold hgate
      hlead0 hlead_tendsto
  have hscaled : BlowsUpAt (scaledTierPhiPath p.concretePrimedTierSystem j) τ :=
    scaledTierPhiPath_blowsUpAt_of_phi p.concretePrimedTierSystem hτ0 hphi
  exact hscaled.congr
    (fixedOStar_concretePrimedTierSystem_H_eventuallyEq_scaledTierPhiPath p j τ).symm

/-- Blow-up of the concrete formal-phi preactivation `H'_{j+1}` at every point of the
combined propagation-visible zero-free tier `T0 j` (formal-phi-lead instance of
`fixedOStar_H_blowsUpAt_of_stratum_formalPhiLead_ne`). -/
theorem fixedOStar_propagationVisible_H_blowsUpAt
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ') {j : Nat} {τ : ℂ} (hj : j + 1 < L)
    (hτ : τ ∈ p.propagationVisibleTierSystem.T0 j) :
    BlowsUpAt (p.concretePrimedTierSystem.stratification.H (j + 1)) τ :=
  fixedOStar_H_blowsUpAt_of_stratum_formalPhiLead_ne hStanding p hj
    (p.propagationVisibleTierSystem.T0_mem_stratum hτ)
    (p.propagationVisibleTierSystem.T0_ne_zero (by omega) hτ)
    (fixedOStar_formalPhiLead_ne_of_mem_propagationVisibleTierSystem_T0 hStanding p
      (by omega) hτ)

/-- Compile the polynomial-form Claim-C provider to the coefficient-form provider
currently consumed by the Step 1 endpoint. -/
theorem fixedOStarLastTierVisibleCoeffNonzeroData_of_visiblePolynomialNonzero
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (hvisible : FixedOStarLastTierVisiblePolynomialNonzeroData hr hStanding) :
    FixedOStarLastTierVisibleCoeffNonzeroData hr hStanding := by
  intro p τ hL hτ
  rw [fixedOStar_lastLayer_visibleCoeff_eq_step1VisiblePoly p hL τ]
  exact hvisible p hL hτ

/-- Combined fixed-`O_star` Step 1 provider data for the recursive IDL package.

The first field is the still-hard at-tier Claim-B level-set statement: the concrete
Step 1 setup supplies the punctured regularity and blow-up hypotheses consumed by the
older level-set interface, so the provider only records the frequent successor-stratum
nonvanishing conclusion.  The second field is the remaining Claim-C visible-polynomial
nonvanishing statement; the previously exposed visible nested-region obligation is
stronger than this pointwise interface and is available through
`fixedOStarStep1ProviderData_of_visibleNestedRegion`.  The polynomial interface compiles
to the concrete last-layer coefficient interface through
`fixedOStarLastTierVisibleCoeffNonzeroData_of_step1ProviderData`. -/
structure FixedOStarStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') : Prop where
  levelSetLeadAtTier : FixedOStarZeroFreeLevelSetLeadAtTierData hr hStanding
  visiblePolynomialNonzero :
    FixedOStarLastTierVisiblePolynomialNonzeroData hr hStanding

/-- Compatibility constructor from the previous visible nested-region Claim-C
obligation to the reduced visible-polynomial provider package. -/
theorem fixedOStarStep1ProviderData_of_visibleNestedRegion
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (hlevel : FixedOStarZeroFreeLevelSetLeadAtTierData hr hStanding)
    (hregion : FixedOStarLastTierVisibleNestedRegionData hr hStanding) :
    FixedOStarStep1ProviderData hr hStanding where
  levelSetLeadAtTier := hlevel
  visiblePolynomialNonzero :=
    fixedOStarLastTierVisiblePolynomialNonzeroData_of_visibleNestedRegion
      hr hStanding hregion

/-- Compose regular-pole Claim B with the exact pointwise Claim-C field consumed by
the Step 1 endpoint.

This avoids asking for a visible nested-region or tower-inclusion bridge when the
caller can prove the last-tier visible polynomial is nonzero directly on the concrete
last tier. -/
theorem fixedOStarStep1ProviderData_of_regularPoleAndVisiblePolynomialNonzero
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hpole : FixedOStarRegularPoleLeadAtTierData hr hStanding)
    (hvisible : FixedOStarLastTierVisiblePolynomialNonzeroData hr hStanding) :
    FixedOStarStep1ProviderData hr hStanding where
  levelSetLeadAtTier :=
    fixedOStarZeroFreeLevelSetLeadAtTierData_of_regularPoleLeadAtTierData hpole
  visiblePolynomialNonzero := hvisible

/-- Provider constructor from the weaker Claim-B pole-hit-plus-avoidance interface and
the exact pointwise Claim-C visible-polynomial nonvanishing interface. -/
theorem fixedOStarStep1ProviderData_of_poleHitAvoidanceAndVisiblePolynomialNonzero
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hhit : FixedOStarRegularPoleHitAvoidanceData hr hStanding)
    (hvisible : FixedOStarLastTierVisiblePolynomialNonzeroData hr hStanding) :
    FixedOStarStep1ProviderData hr hStanding :=
  fixedOStarStep1ProviderData_of_regularPoleAndVisiblePolynomialNonzero
    (fixedOStarRegularPoleLeadAtTierData_of_poleHitAvoidanceData hhit)
    hvisible

/-- Strictly smaller provider-facing Step 1 surface than the visible-zero-free bridge
package: Claim B remains the pole-hit-plus-avoidance statement, while Claim C is only
the pointwise visible-polynomial nonvanishing used to build the last-tier coefficient
data. -/
structure FixedOStarPointwiseStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') : Prop where
  poleHitAvoidance : FixedOStarRegularPoleHitAvoidanceData hr hStanding
  visiblePolynomialNonzero :
    FixedOStarLastTierVisiblePolynomialNonzeroData hr hStanding

/-- Decomposed pointwise Step 1 provider surface.

Compared with `FixedOStarPointwiseStep1ProviderData`, the Claim-B field is split into
the preactivation pole-preimage statement and the leading-coefficient avoidance statement.
The constructor below compiles this back to the provider surface currently consumed by
the endpoint. -/
structure FixedOStarPreimagePointwiseStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') : Prop where
  regularPolePreimage : FixedOStarRegularPolePreimageData hr hStanding
  regularPoleLeadAvoidance :
    FixedOStarRegularPoleLeadAvoidanceOnPoleHitData hr hStanding
  visiblePolynomialNonzero :
    FixedOStarLastTierVisiblePolynomialNonzeroData hr hStanding

/-- Depth-gated decomposed provider surface.

This compatibility surface keeps the historical "bridge" name but no longer asks for
the stronger visible zero-free tower inclusion.  Claim B is split into the pole-preimage
and lead-avoidance fields, while Claim C asks only for the pointwise visible-polynomial
nonvanishing field actually consumed by the last-tier coefficient constructor in the
genuine `1 < L` case.  The `L <= 1` Claim-C branch is compiled by
`fixedOStarLastTierVisiblePolynomialNonzeroData_of_depth_le_one`. -/
structure FixedOStarPreimageDepthBridgeStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') : Prop where
  regularPolePreimage : FixedOStarRegularPolePreimageData hr hStanding
  regularPoleLeadAvoidance :
    FixedOStarRegularPoleLeadAvoidanceOnPoleHitData hr hStanding
  visiblePolynomialNonzero_depth_gt_one :
    FixedOStarLastTierVisiblePolynomialNonzeroDataOfDepthGTOne hr hStanding

/-- Fully depth-gated decomposed provider surface.

This is the sharpened version of `FixedOStarPreimageDepthBridgeStep1ProviderData`:
the two Claim-B branches and the pointwise Claim-C branch are required only under
`1 < L`.  The already proved `L <= 1` lemmas recover the old always-on Claim-B fields
and close Claim C. -/
structure FixedOStarDepthGatedPreimageBridgeStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') : Prop where
  regularPolePreimage_depth_gt_one :
    FixedOStarRegularPolePreimageDataOfDepthGTOne hr hStanding
  regularPoleLeadAvoidance_depth_gt_one :
    FixedOStarRegularPoleLeadAvoidanceOnPoleHitDataOfDepthGTOne hr hStanding
  visiblePolynomialNonzero_depth_gt_one :
    FixedOStarLastTierVisiblePolynomialNonzeroDataOfDepthGTOne hr hStanding

/-- Depth-gated provider with the Claim-B lead-avoidance field split into the interior
propagation-polynomial zero-locus statement and the last-step boundary statement.
Claim C is the pointwise visible-polynomial nonvanishing obligation, not the stronger
visible zero-free bridge. -/
structure FixedOStarDepthGatedPreimageSplitLeadBridgeStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') : Prop where
  regularPolePreimage_depth_gt_one :
    FixedOStarRegularPolePreimageDataOfDepthGTOne hr hStanding
  regularPoleInteriorPropagationLeadingCoeffAvoidance_depth_gt_one :
    FixedOStarRegularPoleInteriorPropagationLeadingCoeffAvoidanceOnPoleHitDataOfDepthGTOne
      hr hStanding
  regularPoleLastStepLeadAvoidance_depth_gt_one :
    FixedOStarRegularPoleLastStepLeadAvoidanceOnPoleHitDataOfDepthGTOne hr hStanding
  visiblePolynomialNonzero_depth_gt_one :
    FixedOStarLastTierVisiblePolynomialNonzeroDataOfDepthGTOne hr hStanding

/-- Variant of the split-lead depth-gated provider where the boundary last-step field is
replaced by the equivalent no-pole-hit formulation exposed above. -/
structure FixedOStarDepthGatedPreimageSplitLeadNoPoleBridgeStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') : Prop where
  regularPolePreimage_depth_gt_one :
    FixedOStarRegularPolePreimageDataOfDepthGTOne hr hStanding
  regularPoleInteriorPropagationLeadingCoeffAvoidance_depth_gt_one :
    FixedOStarRegularPoleInteriorPropagationLeadingCoeffAvoidanceOnPoleHitDataOfDepthGTOne
      hr hStanding
  regularPoleLastStepNoPoleHit_depth_gt_one :
    FixedOStarRegularPoleLastStepNoPoleHitDataOfDepthGTOne hr hStanding
  visiblePolynomialNonzero_depth_gt_one :
    FixedOStarLastTierVisiblePolynomialNonzeroDataOfDepthGTOne hr hStanding

/-- Split-lead/no-pole provider whose Claim-C field is the exact last formal-phi region
nonvanishing statement for the visible polynomial.

This is weaker than the visible zero-free bridge: it asks only for the TeX `(R)`
conclusion used in Claim C at depth `L - 1`, not for compatibility with the whole
visible nested zero-free tower. -/
structure FixedOStarDepthGatedPreimageSplitLeadNoPoleLastRegionStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') : Prop where
  regularPolePreimage_depth_gt_one :
    FixedOStarRegularPolePreimageDataOfDepthGTOne hr hStanding
  regularPoleInteriorPropagationLeadingCoeffAvoidance_depth_gt_one :
    FixedOStarRegularPoleInteriorPropagationLeadingCoeffAvoidanceOnPoleHitDataOfDepthGTOne
      hr hStanding
  regularPoleLastStepNoPoleHit_depth_gt_one :
    FixedOStarRegularPoleLastStepNoPoleHitDataOfDepthGTOne hr hStanding
  visiblePolynomialNonzeroOnLastRegion_depth_gt_one :
    FixedOStarLastTierVisiblePolynomialNonzeroOnLastRegionDataOfDepthGTOne
      hr hStanding

/-- Last-region provider variant where the interior lead field is the static
nonvanishing-on-region surface. -/
structure FixedOStarDepthGatedPreimageRegionLeadNoPoleLastRegionStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') : Prop where
  regularPolePreimage_depth_gt_one :
    FixedOStarRegularPolePreimageDataOfDepthGTOne hr hStanding
  regularPoleInteriorPropagationLeadingCoeffNonzeroOnRegion_depth_gt_one :
    FixedOStarRegularPoleInteriorPropagationLeadingCoeffNonzeroOnRegionDataOfDepthGTOne
      hr hStanding
  regularPoleLastStepNoPoleHit_depth_gt_one :
    FixedOStarRegularPoleLastStepNoPoleHitDataOfDepthGTOne hr hStanding
  visiblePolynomialNonzeroOnLastRegion_depth_gt_one :
    FixedOStarLastTierVisiblePolynomialNonzeroOnLastRegionDataOfDepthGTOne
      hr hStanding

/-- Compile the split-lead compatibility provider back to the current fully depth-gated
provider surface. -/
theorem fixedOStarDepthGatedPreimageBridgeStep1ProviderData_of_splitLeadBridgeData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D : FixedOStarDepthGatedPreimageSplitLeadBridgeStep1ProviderData hr hStanding) :
    FixedOStarDepthGatedPreimageBridgeStep1ProviderData hr hStanding where
  regularPolePreimage_depth_gt_one :=
    D.regularPolePreimage_depth_gt_one
  regularPoleLeadAvoidance_depth_gt_one :=
    fixedOStarRegularPoleLeadAvoidanceOfDepthGTOne_of_interiorPropagation_and_lastStep
      D.regularPoleInteriorPropagationLeadingCoeffAvoidance_depth_gt_one
      D.regularPoleLastStepLeadAvoidance_depth_gt_one
  visiblePolynomialNonzero_depth_gt_one :=
    D.visiblePolynomialNonzero_depth_gt_one

/-- Compile the no-pole-hit boundary provider to the current split-lead provider by the
proved boundary reduction of the last-step field. -/
theorem fixedOStarDepthGatedPreimageSplitLeadBridgeStep1ProviderData_of_splitLeadNoPoleBridgeData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D :
      FixedOStarDepthGatedPreimageSplitLeadNoPoleBridgeStep1ProviderData
        hr hStanding) :
    FixedOStarDepthGatedPreimageSplitLeadBridgeStep1ProviderData hr hStanding where
  regularPolePreimage_depth_gt_one :=
    D.regularPolePreimage_depth_gt_one
  regularPoleInteriorPropagationLeadingCoeffAvoidance_depth_gt_one :=
    D.regularPoleInteriorPropagationLeadingCoeffAvoidance_depth_gt_one
  regularPoleLastStepLeadAvoidance_depth_gt_one :=
    fixedOStarRegularPoleLastStepLeadAvoidanceOfDepthGTOne_of_noPoleHit
      D.regularPoleLastStepNoPoleHit_depth_gt_one
  visiblePolynomialNonzero_depth_gt_one :=
    D.visiblePolynomialNonzero_depth_gt_one

/-- Compile the static-region interior lead provider to the current last-region
frontier package. -/
theorem fixedOStarSplitLeadNoPoleLastRegionData_of_regionLeadNoPoleLastRegionData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D :
      FixedOStarDepthGatedPreimageRegionLeadNoPoleLastRegionStep1ProviderData
        hr hStanding) :
    FixedOStarDepthGatedPreimageSplitLeadNoPoleLastRegionStep1ProviderData
      hr hStanding where
  regularPolePreimage_depth_gt_one :=
    D.regularPolePreimage_depth_gt_one
  regularPoleInteriorPropagationLeadingCoeffAvoidance_depth_gt_one :=
    fixedOStarInteriorLeadAvoidanceOfDepthGTOne_of_nonzeroOnRegion
      D.regularPoleInteriorPropagationLeadingCoeffNonzeroOnRegion_depth_gt_one
  regularPoleLastStepNoPoleHit_depth_gt_one :=
    D.regularPoleLastStepNoPoleHit_depth_gt_one
  visiblePolynomialNonzeroOnLastRegion_depth_gt_one :=
    D.visiblePolynomialNonzeroOnLastRegion_depth_gt_one

/-- Constructor for the static-region lead frontier using the generic Step 1
propagation-region visible-polynomial nonvanishing statement.

This keeps Claim C at the polynomial-family/nested-largeness layer: concrete
fixed-probe last-region nonvanishing is recovered by the propagation-region inclusion. -/
theorem fixedOStarRegionLeadNoPoleLastRegionData_of_step1PropagationVisibleNonzero
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hlevel : FixedOStarZeroFreeLevelSetLeadData hr hStanding)
    (hnested :
      (p : FixedOStarProbe r L d O θ θ') ->
        Step1PropagationNestedLargenessAssumptionsForDepth
          L d (paramStream θ') p.probe.1 p.iota)
    (hnoPole : FixedOStarRegularPoleLastStepNoPoleHitDataOfDepthGTOne hr hStanding)
    (hvisible :
      (p : FixedOStarProbe r L d O θ θ') ->
        Step1VisiblePolynomialNonzeroOnPropagationLastRegionAssumptionsForDepth
          L d (paramStream θ') p.probe.1 p.iota) :
    FixedOStarDepthGatedPreimageRegionLeadNoPoleLastRegionStep1ProviderData
      hr hStanding where
  regularPolePreimage_depth_gt_one :=
    fixedOStarRegularPolePreimageDataOfDepthGTOne_of_zeroFreeLevelSetLeadData hlevel
  regularPoleInteriorPropagationLeadingCoeffNonzeroOnRegion_depth_gt_one :=
    fixedOStarRegularPoleInteriorPropagationLeadingCoeffNonzeroOnRegionDataOfDepthGTOne_of_nestedLargeness
      hnested
  regularPoleLastStepNoPoleHit_depth_gt_one :=
    hnoPole
  visiblePolynomialNonzeroOnLastRegion_depth_gt_one :=
    fixedOStarVisibleNonzeroOnLastRegionOfDepthGTOne_of_step1PropagationVisibleNonzero
      hvisible

/-- Static-region lead frontier from the combined per-probe Step 1 propagation
primitive. -/
theorem fixedOStarRegionLeadNoPoleLastRegionData_of_step1PropagationPrimitive
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hlevel : FixedOStarZeroFreeLevelSetLeadData hr hStanding)
    (hprop :
      (p : FixedOStarProbe r L d O θ θ') ->
        Step1PropagationPrimitiveAssumptionsForDepth
          L d (paramStream θ') p.probe.1 p.iota)
    (hnoPole : FixedOStarRegularPoleLastStepNoPoleHitDataOfDepthGTOne
      hr hStanding) :
    FixedOStarDepthGatedPreimageRegionLeadNoPoleLastRegionStep1ProviderData
      hr hStanding :=
  fixedOStarRegionLeadNoPoleLastRegionData_of_step1PropagationVisibleNonzero
    hlevel
    (fun p => (hprop p).nestedLargeness)
    hnoPole
    (fun p => (hprop p).visiblePolynomialNonzeroOnLastRegion)

/-- Split-lead/no-pole last-region frontier from the combined per-probe Step 1
propagation primitive. -/
theorem fixedOStarSplitLeadNoPoleLastRegionData_of_step1PropagationPrimitive
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hlevel : FixedOStarZeroFreeLevelSetLeadData hr hStanding)
    (hprop :
      (p : FixedOStarProbe r L d O θ θ') ->
        Step1PropagationPrimitiveAssumptionsForDepth
          L d (paramStream θ') p.probe.1 p.iota)
    (hnoPole : FixedOStarRegularPoleLastStepNoPoleHitDataOfDepthGTOne
      hr hStanding) :
    FixedOStarDepthGatedPreimageSplitLeadNoPoleLastRegionStep1ProviderData
      hr hStanding :=
  fixedOStarSplitLeadNoPoleLastRegionData_of_regionLeadNoPoleLastRegionData
    (fixedOStarRegionLeadNoPoleLastRegionData_of_step1PropagationPrimitive
      hlevel hprop hnoPole)

/-- Pointwise boundary variant of the combined Step 1 propagation primitive constructor. -/
theorem fixedOStarSplitLeadNoPoleLastRegionData_of_step1PropagationPrimitive_pointwiseNoPole
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hlevel : FixedOStarZeroFreeLevelSetLeadData hr hStanding)
    (hprop :
      (p : FixedOStarProbe r L d O θ θ') ->
        Step1PropagationPrimitiveAssumptionsForDepth
          L d (paramStream θ') p.probe.1 p.iota)
    (hpoint :
      FixedOStarRegularPoleLastStepPointwiseNoPoleDataOfDepthGTOne
        hr hStanding) :
    FixedOStarDepthGatedPreimageSplitLeadNoPoleLastRegionStep1ProviderData
      hr hStanding :=
  fixedOStarSplitLeadNoPoleLastRegionData_of_step1PropagationPrimitive
    hlevel hprop
    (fixedOStarRegularPoleLastStepNoPoleHitDataOfDepthGTOne_of_pointwiseNoPole
      hpoint)

/-- Fully reduced constructor using a generic polynomial no-pole witness on the
concrete last-boundary regular-domain graph, rather than the fixed-`O_star` boundary
field itself. -/
theorem fixedOStarSplitLeadNoPoleLastRegionData_of_regularPole_step1Primitive_noPoleGraph
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hpole : FixedOStarRegularPoleLeadAtTierData hr hStanding)
    (hprop :
      (p : FixedOStarProbe r L d O θ θ') ->
        Step1PropagationPrimitiveAssumptionsForDepth
          L d (paramStream θ') p.probe.1 p.iota)
    (hboundary :
      (p : FixedOStarProbe r L d O θ θ') ->
        Step1LastBoundaryFormalPhiNoPoleOnRegionAssumptionsForDepth
          L d r (paramStream θ') p.probe.1 p.probe.2
          (fixedOStarLastBoundaryRegularDomainGraph (θ := θ) (θ' := θ') p)) :
    FixedOStarDepthGatedPreimageSplitLeadNoPoleLastRegionStep1ProviderData
      hr hStanding :=
  fixedOStarSplitLeadNoPoleLastRegionData_of_step1PropagationPrimitive_pointwiseNoPole
    (fixedOStarZeroFreeLevelSetLeadData_of_regularPoleLeadAtTierData hpole)
    hprop
    (by
      intro hDepth p j z _hj hlast hω
      have hj_boundary : j + 1 = L - 1 := by omega
      have hω_boundary :
          z ∈ p.concretePrimedTierSystem.stratification.omega (L - 1) := by
        simpa [hj_boundary] using hω
      have hboundaryData :
          FixedOStarRegularPoleLastBoundaryFormalPhiNoPoleDataOfDepthGTOne
            hr hStanding :=
        fixedOStarLastBoundaryFormalPhiNoPole_of_noPoleOnRegularDomainGraph
          hboundary
      have hno := hboundaryData hDepth p z hω_boundary
      rwa [hj_boundary,
        fixedOStar_concretePrimedTierSystem_H_lastBoundary_eq_formalPhiPoly
          (p := p) (z := z)])

/-- Fully split variant with the last-boundary no-pole input stated as the generic
polynomial no-pole witness on the concrete regular-domain graph. -/
theorem fixedOStarSplitLeadNoPoleLastRegionData_of_splitPolynomialWitness_noPoleGraph
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hpreimage : FixedOStarRegularPolePreimageDataOfDepthGTOne hr hStanding)
    (hlead :
      FixedOStarRegularPoleLeadAvoidanceOnPoleHitDataOfDepthGTOne hr hStanding)
    (hprop :
      (p : FixedOStarProbe r L d O θ θ') ->
        Step1PropagationPrimitivePolynomialWitnessAssumptionsForDepth
          L d (paramStream θ') p.probe.1 p.iota)
    (hboundary :
      (p : FixedOStarProbe r L d O θ θ') ->
        Step1LastBoundaryFormalPhiNoPoleOnRegionAssumptionsForDepth
          L d r (paramStream θ') p.probe.1 p.probe.2
          (fixedOStarLastBoundaryRegularDomainGraph (θ := θ) (θ' := θ') p)) :
    FixedOStarDepthGatedPreimageSplitLeadNoPoleLastRegionStep1ProviderData
      hr hStanding :=
  fixedOStarSplitLeadNoPoleLastRegionData_of_regularPole_step1Primitive_noPoleGraph
    (fixedOStarRegularPoleLeadAtTierData_of_regularPolePreimage_leadAvoidance_depth_gt_one
      hpreimage hlead)
    (fun p => step1PropagationPrimitiveAssumptionsForDepth_of_polynomialWitness
      (hprop p))
    hboundary

/-- Compile the last-region Claim-C provider to the currently exposed split-lead/no-pole
provider surface. -/
theorem fixedOStarSplitLeadNoPoleBridgeData_of_splitLeadNoPoleLastRegionData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D :
      FixedOStarDepthGatedPreimageSplitLeadNoPoleLastRegionStep1ProviderData
        hr hStanding) :
    FixedOStarDepthGatedPreimageSplitLeadNoPoleBridgeStep1ProviderData
      hr hStanding where
  regularPolePreimage_depth_gt_one :=
    D.regularPolePreimage_depth_gt_one
  regularPoleInteriorPropagationLeadingCoeffAvoidance_depth_gt_one :=
    D.regularPoleInteriorPropagationLeadingCoeffAvoidance_depth_gt_one
  regularPoleLastStepNoPoleHit_depth_gt_one :=
    D.regularPoleLastStepNoPoleHit_depth_gt_one
  visiblePolynomialNonzero_depth_gt_one :=
    fixedOStarLastTierVisiblePolynomialNonzeroDataOfDepthGTOne_of_visibleNonzeroOnLastRegionData
      D.visiblePolynomialNonzeroOnLastRegion_depth_gt_one

/-- Compile the fully depth-gated provider surface to the previous decomposed package
whose Claim-B fields were always-on. -/
theorem fixedOStarPreimageDepthBridgeStep1ProviderData_of_depthGatedPreimageBridgeData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D : FixedOStarDepthGatedPreimageBridgeStep1ProviderData hr hStanding) :
    FixedOStarPreimageDepthBridgeStep1ProviderData hr hStanding where
  regularPolePreimage :=
    fixedOStarRegularPolePreimageData_of_depth_gt_one_preimageData
      D.regularPolePreimage_depth_gt_one
  regularPoleLeadAvoidance :=
    fixedOStarRegularPoleLeadAvoidanceOnPoleHitData_of_depth_gt_one_leadAvoidanceData
      D.regularPoleLeadAvoidance_depth_gt_one
  visiblePolynomialNonzero_depth_gt_one :=
    D.visiblePolynomialNonzero_depth_gt_one

/-- Compile the decomposed pointwise Step 1 surface to the existing pointwise provider
package. -/
theorem fixedOStarPointwiseStep1ProviderData_of_preimagePointwiseData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D : FixedOStarPreimagePointwiseStep1ProviderData hr hStanding) :
    FixedOStarPointwiseStep1ProviderData hr hStanding where
  poleHitAvoidance :=
    fixedOStarRegularPoleHitAvoidanceData_of_regularPolePreimage_and_leadAvoidance
      D.regularPolePreimage D.regularPoleLeadAvoidance
  visiblePolynomialNonzero := D.visiblePolynomialNonzero

/-- Compile the depth-gated decomposed Step 1 package to the decomposed pointwise
provider surface. -/
theorem fixedOStarPreimagePointwiseStep1ProviderData_of_preimageDepthBridgeData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D : FixedOStarPreimageDepthBridgeStep1ProviderData hr hStanding) :
    FixedOStarPreimagePointwiseStep1ProviderData hr hStanding where
  regularPolePreimage := D.regularPolePreimage
  regularPoleLeadAvoidance := D.regularPoleLeadAvoidance
  visiblePolynomialNonzero :=
    fixedOStarLastTierVisiblePolynomialNonzeroData_of_depth_gt_one_visiblePolynomialNonzeroData
      hr hStanding D.visiblePolynomialNonzero_depth_gt_one

/-- Compile the depth-gated decomposed Step 1 package to the pointwise provider
surface currently exposed to the recursive IDL package. -/
theorem fixedOStarPointwiseStep1ProviderData_of_preimageDepthBridgeData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D : FixedOStarPreimageDepthBridgeStep1ProviderData hr hStanding) :
    FixedOStarPointwiseStep1ProviderData hr hStanding :=
  fixedOStarPointwiseStep1ProviderData_of_preimagePointwiseData
    (fixedOStarPreimagePointwiseStep1ProviderData_of_preimageDepthBridgeData D)

/-- Compile the fully depth-gated decomposed Step 1 package to the pointwise provider
surface. -/
theorem fixedOStarPointwiseStep1ProviderData_of_depthGatedPreimageBridgeData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D : FixedOStarDepthGatedPreimageBridgeStep1ProviderData hr hStanding) :
    FixedOStarPointwiseStep1ProviderData hr hStanding :=
  fixedOStarPointwiseStep1ProviderData_of_preimageDepthBridgeData
    (fixedOStarPreimageDepthBridgeStep1ProviderData_of_depthGatedPreimageBridgeData D)

/-- Compile the pointwise provider-facing Step 1 surface to the endpoint provider
package. -/
theorem fixedOStarStep1ProviderData_of_pointwiseData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D : FixedOStarPointwiseStep1ProviderData hr hStanding) :
    FixedOStarStep1ProviderData hr hStanding :=
  fixedOStarStep1ProviderData_of_poleHitAvoidanceAndVisiblePolynomialNonzero
    D.poleHitAvoidance D.visiblePolynomialNonzero

/-- Compile the fully depth-gated decomposed Step 1 package directly to the endpoint
provider package. -/
theorem fixedOStarStep1ProviderData_of_depthGatedPreimageBridgeData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D : FixedOStarDepthGatedPreimageBridgeStep1ProviderData hr hStanding) :
    FixedOStarStep1ProviderData hr hStanding :=
  fixedOStarStep1ProviderData_of_pointwiseData
    (fixedOStarPointwiseStep1ProviderData_of_depthGatedPreimageBridgeData D)

/-- Compile the split-lead bridge provider directly to the endpoint provider package. -/
theorem fixedOStarStep1ProviderData_of_splitLeadBridgeData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D : FixedOStarDepthGatedPreimageSplitLeadBridgeStep1ProviderData hr hStanding) :
    FixedOStarStep1ProviderData hr hStanding :=
  fixedOStarStep1ProviderData_of_depthGatedPreimageBridgeData
    (fixedOStarDepthGatedPreimageBridgeStep1ProviderData_of_splitLeadBridgeData D)

/-- Compile the split-lead/no-pole last-region provider directly to the endpoint
provider package. -/
theorem fixedOStarStep1ProviderData_of_splitLeadNoPoleLastRegionData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D :
      FixedOStarDepthGatedPreimageSplitLeadNoPoleLastRegionStep1ProviderData
        hr hStanding) :
    FixedOStarStep1ProviderData hr hStanding :=
  fixedOStarStep1ProviderData_of_splitLeadBridgeData
    (fixedOStarDepthGatedPreimageSplitLeadBridgeStep1ProviderData_of_splitLeadNoPoleBridgeData
      (fixedOStarSplitLeadNoPoleBridgeData_of_splitLeadNoPoleLastRegionData D))

/-- Provider-facing Step 1 surface with the final boundary no-pole obligation exposed
as a per-fixed-probe polynomial no-pole witness on the concrete regular-domain graph.

This is the same reduced frontier as the current recursive Step 1 provider except that
the bundled `FixedOStarRegularPoleLastBoundaryFormalPhiNoPoleDataOfDepthGTOne` field is
replaced by the narrower graph witness from
`Step1LastBoundaryFormalPhiNoPoleOnRegionAssumptionsForDepth`. -/
structure FixedOStarGraphBoundaryReducedStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') : Prop where
  regularPolePreimage :
    FixedOStarRegularPolePreimageDataOfDepthGTOne hr hStanding
  regularPoleLeadAvoidance :
    FixedOStarRegularPoleLeadAvoidanceOnPoleHitDataOfDepthGTOne hr hStanding
  propagationPolynomialWitness :
    (p : FixedOStarProbe r L d O θ θ') ->
      Step1PropagationPrimitivePolynomialWitnessAssumptionsForDepth
        L d (paramStream θ') p.probe.1 p.iota
  lastBoundaryNoPoleOnRegularDomainGraph :
    (p : FixedOStarProbe r L d O θ θ') ->
      Step1LastBoundaryFormalPhiNoPoleOnRegionAssumptionsForDepth
        L d r (paramStream θ') p.probe.1 p.probe.2
        (fixedOStarLastBoundaryRegularDomainGraph (θ := θ) (θ' := θ') p)

/-- Graph-boundary provider surface with the propagation polynomial-family certificate
removed.

For each fixed `O_star` probe, `Step1PolynomialFamilyAssumptionsForDepth` is already
compiled from the standing assumptions by
`FixedOStarProbe.step1PolynomialFamilyAssumptionsForDepth`.  This structure therefore
asks only for the two pointwise propagation zero-free witnesses plus the graph
boundary no-pole witness. -/
structure FixedOStarGraphBoundaryStandingPolynomialReducedStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') : Prop where
  regularPolePreimage :
    FixedOStarRegularPolePreimageDataOfDepthGTOne hr hStanding
  regularPoleLeadAvoidance :
    FixedOStarRegularPoleLeadAvoidanceOnPoleHitDataOfDepthGTOne hr hStanding
  propagationZeroFreeWitness :
    (p : FixedOStarProbe r L d O θ θ') ->
      Step1PropagationPrimitiveZeroFreeWitnessAssumptionsForDepth
        L d (paramStream θ') p.probe.1 p.iota
  lastBoundaryNoPoleOnRegularDomainGraph :
    (p : FixedOStarProbe r L d O θ θ') ->
      Step1LastBoundaryFormalPhiNoPoleOnRegionAssumptionsForDepth
        L d r (paramStream θ') p.probe.1 p.probe.2
        (fixedOStarLastBoundaryRegularDomainGraph (θ := θ) (θ' := θ') p)

/-- Graph-boundary provider surface with the Claim-B lead-avoidance field removed.

The interior part of lead avoidance follows from the per-probe propagation zero-free
witness: its nested-largeness component gives nonvanishing of the propagation leading
coefficient on the concrete formal-phi region.  The split-boundary part follows from
the graph-boundary no-pole witness. -/
structure FixedOStarGraphBoundaryLeadReducedStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') : Prop where
  regularPolePreimage :
    FixedOStarRegularPolePreimageDataOfDepthGTOne hr hStanding
  propagationZeroFreeWitness :
    (p : FixedOStarProbe r L d O θ θ') ->
      Step1PropagationPrimitiveZeroFreeWitnessAssumptionsForDepth
        L d (paramStream θ') p.probe.1 p.iota
  lastBoundaryNoPoleOnRegularDomainGraph :
    (p : FixedOStarProbe r L d O θ θ') ->
      Step1LastBoundaryFormalPhiNoPoleOnRegionAssumptionsForDepth
        L d r (paramStream θ') p.probe.1 p.probe.2
        (fixedOStarLastBoundaryRegularDomainGraph (θ := θ) (θ' := θ') p)

/-- Lead-reduced graph-boundary provider with the base propagation tail slice removed.

The `m = 0` branch of the propagation tail-slice witness follows from the fixed
`O_star` polynomial-family certificate, so this surface asks only for positive-tail
slice zero-freeness plus the same visible and boundary witnesses as before. -/
structure FixedOStarGraphBoundaryBaseTailLeadReducedStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') : Prop where
  regularPolePreimage :
    FixedOStarRegularPolePreimageDataOfDepthGTOne hr hStanding
  propagationBaseTailReducedZeroFreeWitness :
    (p : FixedOStarProbe r L d O θ θ') ->
      Step1PropagationPrimitiveBaseTailReducedZeroFreeWitnessAssumptionsForDepth
        L d (paramStream θ') p.probe.1 p.iota
  lastBoundaryNoPoleOnRegularDomainGraph :
    (p : FixedOStarProbe r L d O θ θ') ->
      Step1LastBoundaryFormalPhiNoPoleOnRegionAssumptionsForDepth
        L d r (paramStream θ') p.probe.1 p.probe.2
        (fixedOStarLastBoundaryRegularDomainGraph (θ := θ) (θ' := θ') p)

/-- Base-tail/lead-reduced graph-boundary provider with Claim B exposed at the
regular-pole-at-tier level.

The preimage-only pole field in
`FixedOStarGraphBoundaryBaseTailLeadReducedStep1ProviderData` is a consequence of this
more concrete TeX Claim-B target.  The propagation and boundary witnesses are stated
directly over raw `O_star` probes and explicit visible coordinates, since they depend
only on the primed polynomial data and the concrete regular-domain graph, not on the
tail-agreement threshold packaged in `FixedOStarProbe`. -/
structure FixedOStarGraphBoundaryBaseTailLeadAtTierReducedStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') : Prop where
  regularPoleLeadAtTier :
    FixedOStarRegularPoleLeadAtTierData hr hStanding
  propagationPositiveTailSliceNonzeroOnRegion :
    (probe : ProbePair d) ->
      probe ∈ O_star θ' O ->
        (iota : Fin d) ->
          visibleTailCoord θ' probe.1 iota ≠ 0 ->
            Step1PropagationPositiveTailSliceNonzeroOnRegionAssumptionsForDepth
              L d (paramStream θ') probe.1
  visiblePolynomialNonzeroOnLastRegion :
    (probe : ProbePair d) ->
      probe ∈ O_star θ' O ->
        (iota : Fin d) ->
          visibleTailCoord θ' probe.1 iota ≠ 0 ->
            Step1VisiblePolynomialNonzeroOnPropagationLastRegionAssumptionsForDepth
              L d (paramStream θ') probe.1 iota
  lastBoundaryNoPoleOnOStarRegularDomainGraph :
    (probe : ProbePair d) ->
      (hp : probe ∈ O_star θ' O) ->
        (iota : Fin d) ->
          (hvisible : visibleTailCoord θ' probe.1 iota ≠ 0) ->
      Step1LastBoundaryFormalPhiNoPoleOnRegionAssumptionsForDepth
        L d r (paramStream θ') probe.1 probe.2
        (fixedOStarLastBoundaryRegularDomainGraphOfOStar
          (θ := θ) hStanding hp iota hvisible)

/-- Projection of the fixed generic probe region to input directions `w`.

The positive-tail propagation witness and the propagation-region visible witness do not
depend on the output probe vector `v`.  This projection is the exact domain needed for
those two fields. -/
abbrev OStarInputProjection {L d : Nat} (θ' : Params L d)
    (O : Set (ProbePair d)) : Set (Fin d -> ℝ) :=
  {w | ∃ v : Fin d -> ℝ, (w, v) ∈ O_star θ' O}

/-- Projection-level positive-tail propagation witness.

Compared with the raw `O_star` surface, this removes the irrelevant output probe vector
and visible-coordinate arguments from the propagation zero-free obligation. -/
abbrev Step1PropagationPositiveTailSliceNonzeroOnOStarProjectionData
    (L d : Nat) (θ' : Params L d) (O : Set (ProbePair d)) : Prop :=
  (w : Fin d -> ℝ) ->
    w ∈ OStarInputProjection θ' O ->
      Step1PropagationPositiveTailSliceNonzeroOnRegionAssumptionsForDepth
        L d (paramStream θ') w

/-- Depth-sharpened projection-level positive-tail propagation witness.

The positive-tail slice obligation is vacuous for `L <= 2`; only depths with a genuine
positive recursive tail need to supply the witness. -/
abbrev Step1PropagationPositiveTailSliceNonzeroOnOStarProjectionDataOfDepthGTTwo
    (L d : Nat) (θ' : Params L d) (O : Set (ProbePair d)) : Prop :=
  2 < L -> Step1PropagationPositiveTailSliceNonzeroOnOStarProjectionData L d θ' O

/-- Projection-level positive-tail propagation-factor witness on the combined
propagation-visible zero-free regions.

Unlike the older propagation-only region field, this statement is sourced from the same
combined tower that contains the visible polynomial. -/
abbrev Step1PropagationPositiveTailSliceNonzeroOnOStarProjectionPropagationVisibleData
    (L d : Nat) (θ' : Params L d) (O : Set (ProbePair d)) : Prop :=
  (w : Fin d -> ℝ) ->
    w ∈ OStarInputProjection θ' O ->
      (iota : Fin d) ->
        visibleTailCoord θ' w iota ≠ 0 ->
          Step1PropagationPositiveTailSliceNonzeroOnPropagationVisibleRegionAssumptionsForDepth
            L d (paramStream θ') w iota

/-- Depth-sharpened projection-level positive-tail propagation-factor witness on the
combined propagation-visible zero-free regions. -/
abbrev Step1PropagationPositiveTailSliceNonzeroOnOStarProjectionPropagationVisibleDataOfDepthGTTwo
    (L d : Nat) (θ' : Params L d) (O : Set (ProbePair d)) : Prop :=
  2 < L ->
    Step1PropagationPositiveTailSliceNonzeroOnOStarProjectionPropagationVisibleData
      L d θ' O

/-- The positive-tail propagation slice field is vacuous through depth two. -/
theorem step1PropagationPositiveTailSliceNonzeroOnRegionAssumptionsForDepth_of_depth_le_two
    {L d : Nat}
    {θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
    {w : Fin d -> ℝ}
    (hDepth : L <= 2) :
    Step1PropagationPositiveTailSliceNonzeroOnRegionAssumptionsForDepth
      L d θ w := by
  intro m hm_pos hm _x _hx
  omega

/-- Recover the always-on projection-level propagation witness from its genuine
`2 < L` branch. -/
theorem step1PropagationPositiveTailSliceNonzeroOnOStarProjectionData_of_depth_gt_two
    {L d : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    (h :
      Step1PropagationPositiveTailSliceNonzeroOnOStarProjectionDataOfDepthGTTwo
        L d θ' O) :
    Step1PropagationPositiveTailSliceNonzeroOnOStarProjectionData L d θ' O := by
  intro w hw
  by_cases hDepth : 2 < L
  · exact h hDepth w hw
  · exact
      step1PropagationPositiveTailSliceNonzeroOnRegionAssumptionsForDepth_of_depth_le_two
        (L := L) (d := d) (θ := paramStream θ') (w := w) (by omega)

/-- Projection-level Claim-C visible-polynomial witness.

The visible polynomial depends on `w` and the chosen visible coordinate, but not on the
output probe vector `v`; the only `O_star` information retained here is that `w` occurs
as the input side of some generic probe. -/
abbrev Step1VisiblePolynomialNonzeroOnOStarProjectionLastRegionData
    (L d : Nat) (θ' : Params L d) (O : Set (ProbePair d)) : Prop :=
  (w : Fin d -> ℝ) ->
    w ∈ OStarInputProjection θ' O ->
      (iota : Fin d) ->
        visibleTailCoord θ' w iota ≠ 0 ->
          Step1VisiblePolynomialNonzeroOnPropagationLastRegionAssumptionsForDepth
            L d (paramStream θ') w iota

/-- Projection-level Claim-C visible-polynomial witness on the combined
propagation-visible zero-free last region. -/
abbrev Step1VisiblePolynomialNonzeroOnOStarProjectionPropagationVisibleLastRegionData
    (L d : Nat) (θ' : Params L d) (O : Set (ProbePair d)) : Prop :=
  (w : Fin d -> ℝ) ->
    w ∈ OStarInputProjection θ' O ->
      (iota : Fin d) ->
        visibleTailCoord θ' w iota ≠ 0 ->
          Step1VisiblePolynomialNonzeroOnPropagationVisibleLastRegionAssumptionsForDepth
            L d (paramStream θ') w iota

/-- Raw probe/coordinate concrete tier system used by the `O_star` Step 1 frontier.

This is the primed tier system carried by any `FixedOStarProbe`, but without the
unprimed parameters or tail-agreement proof. -/
noncomputable def fixedOStarProbeCoordTierSystem
    {L d r : Nat} {θ' : Params L d}
    (probe : ProbePair d) (iota : Fin d) : TierSystem L :=
  TierSystem.ofPolynomialNestedTailData
    ((ConstantProbeConcreteData.ofConcrete (paramStream θ') (Real.log (r : ℝ))
      probe.1 probe.2 L iota).toConcreteStratification)
    (step1FormalPhiPropagationPolynomialNestedTailData (paramStream θ')
      probe.1 probe.2)

/-- The raw probe-coordinate tier path evaluates the formal propagation polynomial. -/
theorem fixedOStarProbeCoordTierSystem_tierPhiPath_eq_formalPhi
    {L d r : Nat} {θ' : Params L d}
    (probe : ProbePair d) (iota : Fin d) (j : Nat) (z : ℂ) :
    tierPhiPath (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ') probe iota) j z =
      formalPhi (paramStream θ') (j + 1)
        (constantProbeGatePrefix (paramStream θ') (Real.log (r : ℝ))
          probe.1 probe.2 (j + 1) z)
        probe.1 probe.2 := by
  rw [tierPhiPath, fixedOStarProbeCoordTierSystem,
    TierSystem.ofPolynomialNestedTailData_nestedFamily,
    step1FormalPhiPropagationPolynomialNestedTailData_toNestedTailFamily,
    step1FormalPhiPropagationNestedTailFamily_evalStep_eq_formalPhi]
  apply congrArg
    (fun y => formalPhi (paramStream θ') (j + 1) y probe.1 probe.2)
  funext k
  by_cases hk : k < j + 1
  · simp [extendGate, gatePrefix,
      ConstantProbeConcreteData.toConcreteStratification,
      ConcreteStratificationData.toConcreteStratification,
      ConstantProbeConcreteData.toConcreteStratificationData,
      constantProbeGatePrefix, hk]
  · simp [extendGate, constantProbeGatePrefix, hk]

/-- The raw probe-coordinate successor gate argument is the scaled formal-phi tier path. -/
theorem fixedOStarProbeCoordTierSystem_H_eq_scaledTierPhiPath
    {L d r : Nat} {θ' : Params L d}
    (probe : ProbePair d) (iota : Fin d) (j : Nat) :
    (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ') probe iota).stratification.H
        (j + 1) =
      scaledTierPhiPath
        (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ') probe iota) j := by
  funext z
  rw [scaledTierPhiPath]
  rw [fixedOStarProbeCoordTierSystem_tierPhiPath_eq_formalPhi probe iota j z]
  simp [fixedOStarProbeCoordTierSystem, TierSystem.ofPolynomialNestedTailData,
    ConstantProbeConcreteData.toConcreteStratification,
    ConcreteStratificationData.toConcreteStratification,
    ConstantProbeConcreteData.toConcreteStratificationData, constantProbeGateArgument]

/-- Punctured-neighborhood form of the raw probe-coordinate scaled successor identity. -/
theorem fixedOStarProbeCoordTierSystem_H_eventuallyEq_scaledTierPhiPath
    {L d r : Nat} {θ' : Params L d}
    (probe : ProbePair d) (iota : Fin d) (j : Nat) (τ : ℂ) :
    (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ') probe iota).stratification.H
        (j + 1)
      =ᶠ[puncturedNhds τ]
        scaledTierPhiPath
          (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ') probe iota) j :=
  Filter.Eventually.of_forall fun z =>
    congrFun (fixedOStarProbeCoordTierSystem_H_eq_scaledTierPhiPath
      (r := r) (θ' := θ') probe iota j) z

/-- `O_star` genericity makes every raw formal propagation step quadratic in the last
gate variable. -/
theorem fixedOStarProbeCoordTierSystem_step_degree_eq_two_of_OStar
    {L d r : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    {probe : ProbePair d} (hp : probe ∈ O_star θ' O)
    {iota : Fin d} (hvisible : visibleTailCoord θ' probe.1 iota ≠ 0)
    {j : Nat} (hj : j + 1 < L) :
    ((fixedOStarProbeCoordTierSystem
      (r := r) (θ' := θ') probe iota).nestedFamily.step j).degree = 2 := by
  have hpoly :
      Step1PolynomialFamilyAssumptionsForDepth L d (paramStream θ') probe.1 iota :=
    step1PolynomialFamilyAssumptionsForDepth_of_OStar (by omega) hp hvisible
  have hkappa : step1KappaScalar (paramStream θ') j probe.1 ≠ 0 :=
    hpoly.kappa_ne ⟨j, by omega⟩
  simpa [fixedOStarProbeCoordTierSystem, TierSystem.ofPolynomialNestedTailData,
    step1FormalPhiPropagationPolynomialNestedTailData,
    step1FormalPhiPropagationTailData] using
    step1FormalPhiPropagationTailData_degree_eq_two
      (paramStream θ') probe.1 probe.2 j hkappa

/-- At raw zero-free tier points, the formal tail leading and lower coefficient paths are
analytic. -/
theorem fixedOStarProbeCoordTierSystem_coeffPaths_analyticAt
    {L d r : Nat} {θ' : Params L d}
    (probe : ProbePair d) (iota : Fin d)
    {j : Nat} {τ : ℂ}
    (hτω :
      τ ∈ (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ')
        probe iota).stratification.omega j) :
    let A := fixedOStarProbeCoordTierSystem (r := r) (θ' := θ') probe iota
    AnalyticAt ℂ (tierLeadingCoeffPath A j) τ ∧
      ∀ i : Fin (A.nestedFamily.step j).degree,
        AnalyticAt ℂ
          (fun z => (A.nestedFamily.step j).lower i (gatePrefix A.stratification j z)) τ := by
  let A := fixedOStarProbeCoordTierSystem (r := r) (θ' := θ') probe iota
  have hωj : τ ∈ A.stratification.omega j := hτω
  have hω_raw :
      τ ∈ (partialUnion (constantProbeStratum (paramStream θ') (Real.log (r : ℝ))
        probe.1 probe.2) j)ᶜ := by
    simpa [A, fixedOStarProbeCoordTierSystem, ConcreteStratification.omega,
      TierSystem.ofPolynomialNestedTailData,
      ConstantProbeConcreteData.toConcreteStratification,
      ConcreteStratificationData.toConcreteStratification,
      ConstantProbeConcreteData.toConcreteStratificationData] using hωj
  have hgate :
      ∀ i : Fin j,
        AnalyticAt ℂ
          (fun z =>
            gatePrefix A.stratification j z i) τ := by
    intro i
    have hωi :
        τ ∈
          (partialUnion (constantProbeStratum (paramStream θ') (Real.log (r : ℝ))
            probe.1 probe.2) ((i : Nat) + 1))ᶜ := by
      intro hmem
      exact hω_raw
        (partialUnion_mono_right
          (S := constantProbeStratum (paramStream θ') (Real.log (r : ℝ))
            probe.1 probe.2)
          (by omega) hmem)
    simpa [A, fixedOStarProbeCoordTierSystem, gatePrefix,
      TierSystem.ofPolynomialNestedTailData,
      ConstantProbeConcreteData.toConcreteStratification,
      ConcreteStratificationData.toConcreteStratification,
      ConstantProbeConcreteData.toConcreteStratificationData] using
      (constantProbeGate_analyticOn_later_omega
        (paramStream θ') (Real.log (r : ℝ)) probe.1 probe.2
        (i := (i : Nat)) (j := (i : Nat) + 1) (by omega) τ hωi)
  have hlead :
      AnalyticAt ℂ
        (fun z =>
          MvPolynomial.eval (fun i : Fin j => gatePrefix A.stratification j z i)
            (lastVariablePolynomial
              (step1FormalPhiPropagationTailPoly
                (paramStream θ') probe.1 probe.2 j)).leadingCoeff) τ :=
    gatePolynomial_eval_analyticOnNhd
      (lastVariablePolynomial
        (step1FormalPhiPropagationTailPoly
          (paramStream θ') probe.1 probe.2 j)).leadingCoeff
      (U := {τ})
      (g := fun i z => gatePrefix A.stratification j z i)
      (fun i z hz => by
        have hz' : z = τ := by simpa using hz
        subst z
        exact hgate i) τ (by simp)
  have hlead' : AnalyticAt ℂ (tierLeadingCoeffPath A j) τ := by
    simpa [A, fixedOStarProbeCoordTierSystem, tierLeadingCoeffPath,
      TierSystem.ofPolynomialNestedTailData,
      step1FormalPhiPropagationPolynomialNestedTailData,
      step1FormalPhiPropagationTailData, polynomialTailPresentation] using hlead
  refine ⟨hlead', ?_⟩
  intro i
  have hlower :
      AnalyticAt ℂ
        (fun z =>
          MvPolynomial.eval (fun k : Fin j => gatePrefix A.stratification j z k)
            ((lastVariablePolynomial
              (step1FormalPhiPropagationTailPoly
                (paramStream θ') probe.1 probe.2 j)).coeff (i : Nat))) τ :=
    gatePolynomial_eval_analyticOnNhd
      ((lastVariablePolynomial
        (step1FormalPhiPropagationTailPoly
          (paramStream θ') probe.1 probe.2 j)).coeff (i : Nat))
      (U := {τ})
      (g := fun k z => gatePrefix A.stratification j z k)
      (fun k z hz => by
        have hz' : z = τ := by simpa using hz
        subst z
        exact hgate k) τ (by simp)
  simpa [A, fixedOStarProbeCoordTierSystem,
    TierSystem.ofPolynomialNestedTailData,
    step1FormalPhiPropagationPolynomialNestedTailData,
    step1FormalPhiPropagationTailData, polynomialTailPresentation] using hlower

/-- The raw fixed-`O_star` current gate has the standard analytic reciprocal at a
zero-free tier point: `1 + exp(-H_j)` vanishes at the stratum point and is a local
punctured reciprocal for `s_j`. -/
theorem fixedOStarProbeCoord_currentGate_localReciprocal
    {L d r : Nat} {θ' : Params L d}
    (probe : ProbePair d) (iota : Fin d)
    {j : Nat} {τ : ℂ} (hj : j < L)
    (hτS :
      τ ∈ (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ')
        probe iota).stratification.S j) :
    ∃ Y : ℂ -> ℂ,
      AnalyticAt ℂ Y τ
        ∧ Y τ = 0
        ∧ ∀ᶠ z in puncturedNhds τ,
          Y z *
            (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ') probe iota).stratification.s
              j z = 1 := by
  let A := fixedOStarProbeCoordTierSystem (r := r) (θ' := θ') probe iota
  let Y : ℂ -> ℂ := fun z => 1 + Complex.exp (-(A.stratification.H j z))
  have hτomega : τ ∈ A.stratification.omega j :=
    A.stratification.mem_omega_of_mem_stratum hj hτS
  have hτomega_raw :
      τ ∈ (partialUnion (constantProbeStratum (paramStream θ') (Real.log (r : ℝ))
        probe.1 probe.2) j)ᶜ := by
    simpa [A, fixedOStarProbeCoordTierSystem, ConcreteStratification.omega,
      TierSystem.ofPolynomialNestedTailData,
      ConstantProbeConcreteData.toConcreteStratification,
      ConcreteStratificationData.toConcreteStratification,
      ConstantProbeConcreteData.toConcreteStratificationData] using hτomega
  have hH : AnalyticAt ℂ (A.stratification.H j) τ := by
    simpa [A, fixedOStarProbeCoordTierSystem,
      TierSystem.ofPolynomialNestedTailData,
      ConstantProbeConcreteData.toConcreteStratification,
      ConcreteStratificationData.toConcreteStratification,
      ConstantProbeConcreteData.toConcreteStratificationData] using
      (constantProbeGateArgument_analyticOn_omega
        (paramStream θ') (Real.log (r : ℝ)) probe.1 probe.2 j τ hτomega_raw)
  have hY : AnalyticAt ℂ Y τ := by
    exact analyticAt_const.add hH.neg.cexp'
  have hpole : A.stratification.H j τ ∈ oddPiI :=
    A.stratification.sigmoid.gateArgument_mem_oddPiI hj hτS
  have hYτ : Y τ = 0 := by
    simpa [Y] using (one_add_exp_neg_eq_zero_iff (A.stratification.H j τ)).2 hpole
  have hden_ne :
      ∀ᶠ z in puncturedNhds τ,
        1 + Complex.exp (-(A.stratification.H j z)) ≠ 0 :=
    A.stratification.sigmoid.denom_eventually_ne j hj τ hτS
  have hrecip :
      ∀ᶠ z in puncturedNhds τ, Y z * A.stratification.s j z = 1 := by
    filter_upwards [hden_ne] with z hdenz
    have hs :
        A.stratification.s j z = csig (A.stratification.H j z) := by
      simpa using congrFun (A.stratification.gate_formula hj) z
    rw [hs]
    simp [Y, csig, hdenz]
  exact ⟨Y, hY, hYτ, hrecip⟩

/-- Raw fixed-`O_star` successor preactivation local reciprocal normal form, reduced to
the scaled successor identity and analytic coefficient paths of the quadratic
presentation.  The reciprocal of the current gate is supplied concretely by
`fixedOStarProbeCoord_currentGate_localReciprocal`. -/
theorem fixedOStarProbeCoord_H_localReciprocalNormalForm_of_scaled_quadratic
    {L d r : Nat} {θ' : Params L d}
    (probe : ProbePair d) (iota : Fin d)
    {j : Nat} {τ : ℂ}
    (hj : j + 1 < L)
    (hτS :
      τ ∈ (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ')
        probe iota).stratification.S j)
    (hτ0 : τ ≠ 0)
    (hlead0 :
      ((fixedOStarProbeCoordTierSystem (r := r) (θ' := θ') probe iota).nestedFamily.step
          j).lead
        (gatePrefix (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ')
          probe iota).stratification j τ) ≠ 0)
    (hH_scaled :
      ((fixedOStarProbeCoordTierSystem (r := r) (θ' := θ') probe iota).stratification.H
          (j + 1))
        =ᶠ[puncturedNhds τ]
          scaledTierPhiPath
            (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ') probe iota) j)
    (hdegree :
      ((fixedOStarProbeCoordTierSystem (r := r) (θ' := θ') probe iota).nestedFamily.step
          j).degree = 2)
    (hlead :
      AnalyticAt ℂ
        (tierLeadingCoeffPath
          (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ') probe iota) j) τ)
    (hlower :
      ∀ i : Fin
          ((fixedOStarProbeCoordTierSystem (r := r) (θ' := θ') probe iota).nestedFamily.step
            j).degree,
        AnalyticAt ℂ
          (fun z =>
            ((fixedOStarProbeCoordTierSystem
                  (r := r) (θ' := θ') probe iota).nestedFamily.step j).lower i
              (gatePrefix
                (fixedOStarProbeCoordTierSystem
                  (r := r) (θ' := θ') probe iota).stratification j z)) τ) :
    ∃ R : ℂ -> ℂ,
      AnalyticAt ℂ R τ
        ∧ R τ = 0
        ∧ (¬ ∀ᶠ z in nhds τ, R z = R τ)
        ∧ ∀ᶠ z in puncturedNhds τ,
          R z *
            (fixedOStarProbeCoordTierSystem
              (r := r) (θ' := θ') probe iota).stratification.H (j + 1) z = 1 := by
  let A := fixedOStarProbeCoordTierSystem (r := r) (θ' := θ') probe iota
  rcases fixedOStarProbeCoord_currentGate_localReciprocal
      (r := r) (θ' := θ') probe iota (j := j) (τ := τ) (by omega)
      (by simpa [A] using hτS) with
    ⟨Y, hY, hYτ, hYrecip⟩
  simpa [A] using
    H_local_reciprocalNormalForm_of_scaledTierPhiPath_quadratic
      (A := A) (j := j) (τ := τ) (Y := Y)
      (H := A.stratification.H (j + 1))
      (by simpa [A] using hH_scaled)
      (by simpa [A] using hdegree)
      hY hYτ
      (by simpa [A] using hYrecip)
      hτ0 hlead0
      (by simpa [A] using hlead)
      (by simpa [A] using hlower)

noncomputable def fixedOStarLastBoundaryRegularDomainGraphOfProbeCoord
    {L d r : Nat} {θ' : Params L d}
    (probe : ProbePair d) (iota : Fin d) :
    Set (ℂ × (Fin (L - 1) -> ℂ)) :=
  let strat :=
    (ConstantProbeConcreteData.ofConcrete (paramStream θ') (Real.log (r : ℝ))
      probe.1 probe.2 L iota).toConcreteStratification
  {q | q.1 ∈ strat.omega (L - 1)
      ∧ q.2 = gatePrefix strat (L - 1) q.1}

/-- The raw-probe/coordinate graph is the same graph as the older `O_star` wrapper. -/
theorem fixedOStarLastBoundaryRegularDomainGraphOfProbeCoord_eq_ofOStar
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    {probe : ProbePair d}
    (hp : probe ∈ O_star θ' O)
    (iota : Fin d)
    (hvisible : visibleTailCoord θ' probe.1 iota ≠ 0) :
    fixedOStarLastBoundaryRegularDomainGraphOfProbeCoord
        (r := r) (θ' := θ') probe iota =
      fixedOStarLastBoundaryRegularDomainGraphOfOStar
        (θ := θ) hStanding hp iota hvisible := by
  ext q
  simp [fixedOStarLastBoundaryRegularDomainGraphOfProbeCoord,
    fixedOStarLastBoundaryRegularDomainGraphOfOStar,
    fixedOStarProbeOfOStarVisibleCoord, fixedOStarLastBoundaryRegularDomainGraph,
    FixedOStarProbe.concretePrimedTierSystem, FixedOStarProbe.concretePrimedStratification]

/-- Boundary no-pole witness on the raw probe/coordinate graph. -/
abbrev Step1LastBoundaryFormalPhiNoPoleOnOStarProbeCoordGraphData
    {L d r : Nat} {O : Set (ProbePair d)}
    (θ' : Params L d) : Prop :=
  (probe : ProbePair d) ->
    probe ∈ O_star θ' O ->
      (iota : Fin d) ->
        visibleTailCoord θ' probe.1 iota ≠ 0 ->
          Step1LastBoundaryFormalPhiNoPoleOnRegionAssumptionsForDepth
            L d r (paramStream θ') probe.1 probe.2
            (fixedOStarLastBoundaryRegularDomainGraphOfProbeCoord
              (r := r) (θ' := θ') probe iota)

/-- Compile the existing fixed-probe last-boundary formal-phi no-pole package to the
active raw probe/coordinate graph witness.

The proof only transports the raw graph through the already-proved graph equalities and
then evaluates the fixed-probe boundary no-pole statement at the graph base point. -/
theorem step1LastBoundaryFormalPhiNoPoleOnOStarProbeCoordGraphData_of_lastBoundaryFormalPhiNoPole
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hboundary :
      FixedOStarRegularPoleLastBoundaryFormalPhiNoPoleDataOfDepthGTOne
        hr hStanding) :
    Step1LastBoundaryFormalPhiNoPoleOnOStarProbeCoordGraphData
      (L := L) (d := d) (O := O) (r := r) θ' := by
  intro probe hp iota hvisible hDepth q hq
  let p : FixedOStarProbe r L d O θ θ' :=
    fixedOStarProbeOfOStarVisibleCoord hStanding hp iota hvisible
  have hqGraph :
      q ∈ fixedOStarLastBoundaryRegularDomainGraph
        (θ := θ) (θ' := θ') p := by
    have hEqCoord :
        fixedOStarLastBoundaryRegularDomainGraphOfProbeCoord
            (r := r) (θ' := θ') probe iota =
          fixedOStarLastBoundaryRegularDomainGraphOfOStar
            (θ := θ) hStanding hp iota hvisible :=
      fixedOStarLastBoundaryRegularDomainGraphOfProbeCoord_eq_ofOStar
        hStanding hp iota hvisible
    have hEqOStar :
        fixedOStarLastBoundaryRegularDomainGraphOfOStar
            (θ := θ) hStanding hp iota hvisible =
          fixedOStarLastBoundaryRegularDomainGraph p := by
      simpa [p] using
        fixedOStarLastBoundaryRegularDomainGraphOfOStar_eq
          (θ := θ) (θ' := θ') hStanding p
    simpa [hEqCoord, hEqOStar] using hq
  have hno := hboundary hDepth p q.1 hqGraph.1
  rw [hqGraph.2]
  simpa [p] using hno

/-- Finite depth index for the positive propagation slices that remain after the
`m = 0` slice has been discharged from the fixed-`O_star` polynomial-family
certificate. -/
abbrev Step1PositivePropagationSliceIndex (L : Nat) : Type :=
  {m : Fin (L - 1) // 0 < (m.1 : Nat)}

/-- Concrete indexed polynomial nonvanishing obligations for the positive propagation
tail slices on the `O_star` input projection.

For each remaining depth slice `m`, every projected input `w`, and every point of the
recursive propagation threshold region, the explicit propagation polynomial must avoid
zero on the slice with the newly adjoined gate coordinate set to `0`. -/
abbrev Step1ProjectionPositiveTailSlicePolynomialNonzeroObligations
    (L d : Nat) (θ' : Params L d) (O : Set (ProbePair d)) : Prop :=
  (m : Step1PositivePropagationSliceIndex L) ->
    (w : Fin d -> ℝ) ->
      w ∈ OStarInputProjection θ' O ->
        ∀ x : Fin (m.1 : Nat) -> ℂ,
          x ∈ (step1PropagationNestedTailFamily (paramStream θ') w).region
              (m.1 : Nat) ->
            MvPolynomial.eval (Fin.snoc x 0)
              (step1PropagationTailPoly (paramStream θ') w (m.1 : Nat)) ≠ 0

/-- The indexed positive propagation obligations are empty through depth two. -/
theorem step1ProjectionPositiveTailSlicePolynomialNonzeroObligations_of_depth_le_two
    {L d : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    (hDepth : L <= 2) :
    Step1ProjectionPositiveTailSlicePolynomialNonzeroObligations L d θ' O := by
  intro m
  have hm_lt : (m.1 : Nat) < L - 1 := m.1.isLt
  have hm_pos : 0 < (m.1 : Nat) := m.2
  have hfalse : False := by omega
  exact False.elim hfalse

/-- Compile indexed positive propagation obligations to the active projection-level
propagation witness. -/
theorem step1PropagationPositiveTailSliceNonzeroOnOStarProjectionDataOfDepthGTTwo_of_indexed
    {L d : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    (h :
      Step1ProjectionPositiveTailSlicePolynomialNonzeroObligations L d θ' O) :
    Step1PropagationPositiveTailSliceNonzeroOnOStarProjectionDataOfDepthGTTwo
      L d θ' O := by
  intro _hDepth w hw m hm_pos hm x hx
  exact h ⟨⟨m, hm⟩, hm_pos⟩ w hw x hx

/-- Concrete visible-polynomial nonvanishing obligation on the projected last
propagation region.

This is the exact pointwise condition that a future generic set would need for Claim C:
after choosing a visible coordinate that is already nonzero on `O_star`, the last
visible polynomial must avoid zero throughout the last propagation threshold region. -/
abbrev Step1ProjectionVisibleLastRegionPolynomialNonzeroObligations
    (L d : Nat) (θ' : Params L d) (O : Set (ProbePair d)) : Prop :=
  1 < L ->
    (w : Fin d -> ℝ) ->
      w ∈ OStarInputProjection θ' O ->
        (iota : Fin d) ->
          visibleTailCoord θ' w iota ≠ 0 ->
            ∀ z ∈ (step1PropagationNestedTailFamily (paramStream θ') w).region (L - 1),
              MvPolynomial.eval z
                (step1VisiblePoly (K := L - 1) (paramStream θ') w iota) ≠ 0

/-- Compile the concrete projected visible-polynomial obligation to the active
projection-level Claim-C witness. -/
theorem step1VisiblePolynomialNonzeroOnOStarProjectionLastRegionData_of_concrete
    {L d : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    (h :
      Step1ProjectionVisibleLastRegionPolynomialNonzeroObligations L d θ' O) :
    Step1VisiblePolynomialNonzeroOnOStarProjectionLastRegionData L d θ' O := by
  intro w hw iota hvisible hDepth z hz
  exact h hDepth w hw iota hvisible z hz

/-- Lower-level concrete polynomial/formal-phi no-pole frontier for the active
projection/graph generic witness.

This package is stated in the form most suitable for adding to a future bad-set
definition: finite positive propagation-slice indices, the single last visible
polynomial condition over the projected propagation region, and the last-boundary
formal-phi no-pole graph condition. -/
structure Step1OStarProjectionGraphConcretePolynomialObligations
    (L d r : Nat) (θ' : Params L d) (O : Set (ProbePair d)) : Prop where
  propagationPositiveTailSlices :
    Step1ProjectionPositiveTailSlicePolynomialNonzeroObligations L d θ' O
  visibleLastRegion :
    Step1ProjectionVisibleLastRegionPolynomialNonzeroObligations L d θ' O
  lastBoundaryNoPole :
    Step1LastBoundaryFormalPhiNoPoleOnOStarProbeCoordGraphData
      (L := L) (d := d) (O := O) (r := r) θ'

/-- Pointwise region-nonvanishing part of the concrete projection/graph frontier.

The positive propagation slices are genuinely present only for `2 < L`; at smaller
depths the index type is empty and the compiler below fills that branch mechanically.
The visible last-region condition remains separately depth-gated by its own `1 < L`
premise. -/
structure Step1OStarProjectionConcretePointwiseRegionNonzeroObligations
    (L d : Nat) (θ' : Params L d) (O : Set (ProbePair d)) : Prop where
  propagationPositiveTailSlices_depth_gt_two :
    2 < L ->
      Step1ProjectionPositiveTailSlicePolynomialNonzeroObligations L d θ' O
  visibleLastRegion :
    Step1ProjectionVisibleLastRegionPolynomialNonzeroObligations L d θ' O

/-- Depth-sharpened concrete projection/graph frontier.

This separates the pointwise region-nonvanishing obligations from the formal-phi
no-pole witness on the raw graph and avoids asking for the positive propagation slices
in depths where their index type is empty. -/
structure Step1OStarProjectionGraphConcreteByDepthObligations
    (L d r : Nat) (θ' : Params L d) (O : Set (ProbePair d)) : Prop where
  pointwiseRegionNonzero :
    Step1OStarProjectionConcretePointwiseRegionNonzeroObligations L d θ' O
  lastBoundaryNoPole :
    Step1LastBoundaryFormalPhiNoPoleOnOStarProbeCoordGraphData
      (L := L) (d := d) (O := O) (r := r) θ'

/-- Compile the depth-sharpened split frontier to the older combined concrete
projection/graph frontier. -/
theorem step1OStarProjectionGraphConcretePolynomialObligations_of_byDepth
    {L d r : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    (D : Step1OStarProjectionGraphConcreteByDepthObligations L d r θ' O) :
    Step1OStarProjectionGraphConcretePolynomialObligations L d r θ' O where
  propagationPositiveTailSlices := by
    by_cases hDepth : 2 < L
    · exact D.pointwiseRegionNonzero.propagationPositiveTailSlices_depth_gt_two hDepth
    · exact
        step1ProjectionPositiveTailSlicePolynomialNonzeroObligations_of_depth_le_two
          (L := L) (d := d) (θ' := θ') (O := O) (by omega)
  visibleLastRegion :=
    D.pointwiseRegionNonzero.visibleLastRegion
  lastBoundaryNoPole :=
    D.lastBoundaryNoPole

/-- Projection-level base-tail zero-free witness.

This is the existing propagation primitive zero-free record, but stated on the
`O_star` input projection.  It combines the two pointwise region-nonvanishing fields:
positive propagation slices and the visible last-region condition. -/
abbrev Step1OStarProjectionBaseTailZeroFreeWitnessData
    (L d : Nat) (θ' : Params L d) (O : Set (ProbePair d)) : Prop :=
  (w : Fin d -> ℝ) ->
    w ∈ OStarInputProjection θ' O ->
      (iota : Fin d) ->
        visibleTailCoord θ' w iota ≠ 0 ->
          Step1PropagationPrimitiveBaseTailReducedZeroFreeWitnessAssumptionsForDepth
            L d (paramStream θ') w iota

/-- Split projection-level base-tail zero-free witness.

The first and third fields are the legacy compatibility surface consumed by the current
concrete descent path.  The second and fourth fields are the corrected TeX-region
surface: propagation-factor and visible-factor nonvanishing are sourced from the
combined propagation-visible zero-free tower. -/
structure Step1OStarProjectionSplitBaseTailZeroFreeWitnessData
    (L d : Nat) (θ' : Params L d) (O : Set (ProbePair d)) : Prop where
  propagationPositiveTailSliceNonzeroOnProjection_depth_gt_two :
    Step1PropagationPositiveTailSliceNonzeroOnOStarProjectionDataOfDepthGTTwo
      L d θ' O
  propagationPositiveTailSliceNonzeroOnProjectionPropagationVisible_depth_gt_two :
    Step1PropagationPositiveTailSliceNonzeroOnOStarProjectionPropagationVisibleDataOfDepthGTTwo
      L d θ' O
  visiblePolynomialNonzeroOnProjectionLastRegion :
    Step1VisiblePolynomialNonzeroOnOStarProjectionLastRegionData L d θ' O
  visiblePolynomialNonzeroOnProjectionPropagationVisibleLastRegion :
    Step1VisiblePolynomialNonzeroOnOStarProjectionPropagationVisibleLastRegionData
      L d θ' O

/-- Compile the split projection primitives to the existing base-tail zero-free
witness. -/
theorem step1OStarProjectionBaseTailZeroFreeWitnessData_of_split
    {L d : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    (D : Step1OStarProjectionSplitBaseTailZeroFreeWitnessData L d θ' O) :
    Step1OStarProjectionBaseTailZeroFreeWitnessData L d θ' O := by
  intro w hw iota hvisible
  exact
    { propagationPositiveTailSliceNonzeroOnRegion :=
        step1PropagationPositiveTailSliceNonzeroOnOStarProjectionData_of_depth_gt_two
          D.propagationPositiveTailSliceNonzeroOnProjection_depth_gt_two w hw
      visiblePolynomialNonzeroOnLastRegion :=
        D.visiblePolynomialNonzeroOnProjectionLastRegion w hw iota hvisible }

/-- A projection-level base-tail zero-free witness supplies the split pointwise
region-nonvanishing obligations.

For the propagation-slice branch the polynomial does not depend on the visible
coordinate, so any visible coordinate from the witnessing `O_star` probe is enough. -/
theorem step1OStarProjectionConcretePointwiseRegionNonzeroObligations_of_baseTailZeroFree
    {L d : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    (hzeroFree :
      Step1OStarProjectionBaseTailZeroFreeWitnessData L d θ' O) :
    Step1OStarProjectionConcretePointwiseRegionNonzeroObligations L d θ' O where
  propagationPositiveTailSlices_depth_gt_two := by
    intro _hDepth m w hw x hx
    rcases hw with ⟨v, hp⟩
    rcases exists_visibleTailCoord_ne_zero_of_mem_O_star
        (θ' := θ') (O := O) (p := (w, v)) hp with
      ⟨iota, hvisible⟩
    exact
      (hzeroFree w ⟨v, hp⟩ iota hvisible).propagationPositiveTailSliceNonzeroOnRegion
        (m.1 : Nat) m.2 m.1.isLt x hx
  visibleLastRegion := by
    intro hDepth w hw iota hvisible z hz
    exact (hzeroFree w hw iota hvisible).visiblePolynomialNonzeroOnLastRegion
      hDepth z hz

/-- Concrete projection/graph obligations with the two pointwise nonzero fields bundled
as one base-tail zero-free primitive witness. -/
structure Step1OStarProjectionGraphBaseTailZeroFreeConcreteObligations
    (L d r : Nat) (θ' : Params L d) (O : Set (ProbePair d)) : Prop where
  baseTailZeroFree :
    Step1OStarProjectionBaseTailZeroFreeWitnessData L d θ' O
  lastBoundaryNoPole :
    Step1LastBoundaryFormalPhiNoPoleOnOStarProbeCoordGraphData
      (L := L) (d := d) (O := O) (r := r) θ'

/-- Graph frontier with the base-tail zero-free witness split into its primitive
projection fields and the boundary condition stated as the formal-phi graph witness. -/
structure Step1OStarProjectionGraphSplitBaseTailZeroFreeConcreteObligations
    (L d r : Nat) (θ' : Params L d) (O : Set (ProbePair d)) : Prop where
  baseTailZeroFree :
    Step1OStarProjectionSplitBaseTailZeroFreeWitnessData L d θ' O
  lastBoundaryNoPole :
    Step1LastBoundaryFormalPhiNoPoleOnOStarProbeCoordGraphData
      (L := L) (d := d) (O := O) (r := r) θ'

/-- Compile the split base-tail graph frontier to the existing bundled base-tail
frontier. -/
theorem step1OStarProjectionGraphBaseTailZeroFreeConcreteObligations_of_splitBaseTail
    {L d r : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    (D :
      Step1OStarProjectionGraphSplitBaseTailZeroFreeConcreteObligations
        L d r θ' O) :
    Step1OStarProjectionGraphBaseTailZeroFreeConcreteObligations L d r θ' O where
  baseTailZeroFree :=
    step1OStarProjectionBaseTailZeroFreeWitnessData_of_split D.baseTailZeroFree
  lastBoundaryNoPole := D.lastBoundaryNoPole

/-- Build the split base-tail graph frontier when the boundary input is already
available as the fixed-probe formal-phi no-pole package. -/
theorem step1SplitBaseTailGraphObligations_of_formalPhiNoPole
    {L d r : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    {θ : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (baseTailZeroFree :
      Step1OStarProjectionSplitBaseTailZeroFreeWitnessData L d θ' O)
    (hboundary :
      FixedOStarRegularPoleLastBoundaryFormalPhiNoPoleDataOfDepthGTOne
        hr hStanding) :
    Step1OStarProjectionGraphSplitBaseTailZeroFreeConcreteObligations
      L d r θ' O where
  baseTailZeroFree := baseTailZeroFree
  lastBoundaryNoPole :=
    step1LastBoundaryFormalPhiNoPoleOnOStarProbeCoordGraphData_of_lastBoundaryFormalPhiNoPole
      hboundary

/-- Build the split base-tail graph frontier when the boundary input is already
available on the raw probe/coordinate graph. -/
theorem step1SplitBaseTailGraphObligations_of_graphNoPole
    {L d r : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    (baseTailZeroFree :
      Step1OStarProjectionSplitBaseTailZeroFreeWitnessData L d θ' O)
    (lastBoundaryNoPole :
      Step1LastBoundaryFormalPhiNoPoleOnOStarProbeCoordGraphData
        (L := L) (d := d) (O := O) (r := r) θ') :
    Step1OStarProjectionGraphSplitBaseTailZeroFreeConcreteObligations
      L d r θ' O where
  baseTailZeroFree := baseTailZeroFree
  lastBoundaryNoPole := lastBoundaryNoPole

/-- Compile the bundled base-tail zero-free graph frontier to the depth-sharpened
concrete projection/graph obligations. -/
theorem step1OStarProjectionGraphConcreteByDepthObligations_of_baseTailZeroFreeConcrete
    {L d r : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    (D : Step1OStarProjectionGraphBaseTailZeroFreeConcreteObligations L d r θ' O) :
    Step1OStarProjectionGraphConcreteByDepthObligations L d r θ' O where
  pointwiseRegionNonzero :=
    step1OStarProjectionConcretePointwiseRegionNonzeroObligations_of_baseTailZeroFree
      D.baseTailZeroFree
  lastBoundaryNoPole := D.lastBoundaryNoPole

/-- Compile the bundled base-tail zero-free graph frontier to the older concrete
polynomial/no-pole obligation package. -/
theorem step1OStarProjectionGraphConcretePolynomialObligations_of_baseTailZeroFreeConcrete
    {L d r : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    (D : Step1OStarProjectionGraphBaseTailZeroFreeConcreteObligations L d r θ' O) :
    Step1OStarProjectionGraphConcretePolynomialObligations L d r θ' O :=
  step1OStarProjectionGraphConcretePolynomialObligations_of_byDepth
    (step1OStarProjectionGraphConcreteByDepthObligations_of_baseTailZeroFreeConcrete D)

/-- Generic-polynomial part of the projection/graph-reduced Step 1 frontier.

This record contains only the primed-parameter nonvanishing/no-pole statements that are
meant to come from the TeX generic polynomial exclusions on the `O_star` input
projection and the raw last-boundary graph.  The boundary field is already stated in
the formal-phi graph form consumed by the fixed-probe compilers.  The Claim-B
regular-pole-at-tier statement is deliberately not bundled here, since it is the
separate analytic pole-preimage content. -/
structure Step1OStarProjectionGraphGenericPolynomialWitnessData
    (L d r : Nat) (θ' : Params L d) (O : Set (ProbePair d)) : Prop where
  propagationPositiveTailSliceNonzeroOnProjection_depth_gt_two :
    Step1PropagationPositiveTailSliceNonzeroOnOStarProjectionDataOfDepthGTTwo
      L d θ' O
  visiblePolynomialNonzeroOnProjectionLastRegion :
    Step1VisiblePolynomialNonzeroOnOStarProjectionLastRegionData L d θ' O
  lastBoundaryNoPoleOnProbeCoordGraph :
    Step1LastBoundaryFormalPhiNoPoleOnOStarProbeCoordGraphData
      (L := L) (d := d) (O := O) (r := r) θ'

/-- Compile the concrete polynomial/no-pole frontier to the active generic-polynomial
witness record. -/
theorem step1OStarProjectionGraphGenericPolynomialWitnessData_of_concreteObligations
    {L d r : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    (D : Step1OStarProjectionGraphConcretePolynomialObligations L d r θ' O) :
    Step1OStarProjectionGraphGenericPolynomialWitnessData L d r θ' O where
  propagationPositiveTailSliceNonzeroOnProjection_depth_gt_two :=
    step1PropagationPositiveTailSliceNonzeroOnOStarProjectionDataOfDepthGTTwo_of_indexed
      D.propagationPositiveTailSlices
  visiblePolynomialNonzeroOnProjectionLastRegion :=
    step1VisiblePolynomialNonzeroOnOStarProjectionLastRegionData_of_concrete
      D.visibleLastRegion
  lastBoundaryNoPoleOnProbeCoordGraph :=
    D.lastBoundaryNoPole

/-- Compile the bundled base-tail zero-free graph frontier directly to the active
generic-polynomial witness record. -/
theorem step1OStarProjectionGraphGenericPolynomialWitnessData_of_baseTailZeroFreeConcrete
    {L d r : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    (D : Step1OStarProjectionGraphBaseTailZeroFreeConcreteObligations L d r θ' O) :
    Step1OStarProjectionGraphGenericPolynomialWitnessData L d r θ' O :=
  step1OStarProjectionGraphGenericPolynomialWitnessData_of_concreteObligations
    (step1OStarProjectionGraphConcretePolynomialObligations_of_baseTailZeroFreeConcrete D)

/-- Compile the split base-tail graph frontier directly to the active
generic-polynomial witness record. -/
theorem step1OStarProjectionGraphGenericPolynomialWitnessData_of_splitBaseTailZeroFreeConcrete
    {L d r : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    (D :
      Step1OStarProjectionGraphSplitBaseTailZeroFreeConcreteObligations
        L d r θ' O) :
    Step1OStarProjectionGraphGenericPolynomialWitnessData L d r θ' O :=
  step1OStarProjectionGraphGenericPolynomialWitnessData_of_baseTailZeroFreeConcrete
    (step1OStarProjectionGraphBaseTailZeroFreeConcreteObligations_of_splitBaseTail D)

/-- Compile split base-tail zero-freeness and raw graph no-pole directly to the active
generic-polynomial witness record. -/
theorem step1OStarProjectionGraphGenericPolynomialWitnessData_of_splitBaseTail_graphNoPole
    {L d r : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    (baseTailZeroFree :
      Step1OStarProjectionSplitBaseTailZeroFreeWitnessData L d θ' O)
    (lastBoundaryNoPole :
      Step1LastBoundaryFormalPhiNoPoleOnOStarProbeCoordGraphData
        (L := L) (d := d) (O := O) (r := r) θ') :
    Step1OStarProjectionGraphGenericPolynomialWitnessData L d r θ' O :=
  step1OStarProjectionGraphGenericPolynomialWitnessData_of_splitBaseTailZeroFreeConcrete
    (step1SplitBaseTailGraphObligations_of_graphNoPole
      baseTailZeroFree lastBoundaryNoPole)

/-- Projection/graph-reduced version of the active base-tail/lead-at-tier frontier.

The remaining propagation and visible-polynomial fields are stated on the `w`-projection
of `O_star`; the propagation field is needed only when `2 < L`.  The boundary field is
stated on the raw probe/coordinate graph, without rebuilding a fixed-probe package in
the assumption. -/
structure FixedOStarGraphBoundaryBaseTailLeadAtTierProjectionGraphReducedStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') : Prop where
  regularPoleLeadAtTier :
    FixedOStarRegularPoleLeadAtTierData hr hStanding
  propagationPositiveTailSliceNonzeroOnOStarProjection_depth_gt_two :
    Step1PropagationPositiveTailSliceNonzeroOnOStarProjectionDataOfDepthGTTwo
      L d θ' O
  visiblePolynomialNonzeroOnOStarProjectionLastRegion :
    Step1VisiblePolynomialNonzeroOnOStarProjectionLastRegionData L d θ' O
  lastBoundaryNoPoleOnOStarProbeCoordGraph :
    Step1LastBoundaryFormalPhiNoPoleOnOStarProbeCoordGraphData (O := O) (r := r) θ'

/-- Compile the generic-polynomial witness package plus the separate regular-pole
Claim-B field into the active projection/graph-reduced provider. -/
theorem fixedOStarProjectionGraphReducedProviderData_of_regularPole_and_genericPolynomials
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hpole : FixedOStarRegularPoleLeadAtTierData hr hStanding)
    (hgeneric :
      Step1OStarProjectionGraphGenericPolynomialWitnessData L d r θ' O) :
    FixedOStarGraphBoundaryBaseTailLeadAtTierProjectionGraphReducedStep1ProviderData
      hr hStanding where
  regularPoleLeadAtTier := hpole
  propagationPositiveTailSliceNonzeroOnOStarProjection_depth_gt_two :=
    hgeneric.propagationPositiveTailSliceNonzeroOnProjection_depth_gt_two
  visiblePolynomialNonzeroOnOStarProjectionLastRegion :=
    hgeneric.visiblePolynomialNonzeroOnProjectionLastRegion
  lastBoundaryNoPoleOnOStarProbeCoordGraph :=
    hgeneric.lastBoundaryNoPoleOnProbeCoordGraph

/-- Compile the projection/graph-reduced frontier to the active raw-`O_star` frontier. -/
theorem fixedOStarGraphBoundaryBaseTailLeadAtTierReducedStep1ProviderData_of_projectionGraphReduced
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D :
      FixedOStarGraphBoundaryBaseTailLeadAtTierProjectionGraphReducedStep1ProviderData
        hr hStanding) :
    FixedOStarGraphBoundaryBaseTailLeadAtTierReducedStep1ProviderData
      hr hStanding where
  regularPoleLeadAtTier := D.regularPoleLeadAtTier
  propagationPositiveTailSliceNonzeroOnRegion := fun probe hp _iota _hvisible =>
    step1PropagationPositiveTailSliceNonzeroOnOStarProjectionData_of_depth_gt_two
      D.propagationPositiveTailSliceNonzeroOnOStarProjection_depth_gt_two
      probe.1 ⟨probe.2, hp⟩
  visiblePolynomialNonzeroOnLastRegion := fun probe hp iota hvisible =>
    D.visiblePolynomialNonzeroOnOStarProjectionLastRegion
      probe.1 ⟨probe.2, hp⟩ iota hvisible
  lastBoundaryNoPoleOnOStarRegularDomainGraph := fun probe hp iota hvisible => by
    have hboundary :=
      D.lastBoundaryNoPoleOnOStarProbeCoordGraph probe hp iota hvisible
    simpa [fixedOStarLastBoundaryRegularDomainGraphOfProbeCoord_eq_ofOStar
      hStanding hp iota hvisible] using hboundary

/-- Compile the regular-pole-at-tier graph-boundary frontier to the existing
base-tail/lead-reduced frontier by discarding the extra regularity and
leading-coefficient information in the Claim-B witness and repackaging the raw
`O_star` polynomial/no-pole witnesses for arbitrary fixed-probe packages. -/
theorem fixedOStarGraphBoundaryBaseTailLeadReducedStep1ProviderData_of_leadAtTierReduced
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D :
      FixedOStarGraphBoundaryBaseTailLeadAtTierReducedStep1ProviderData
        hr hStanding) :
    FixedOStarGraphBoundaryBaseTailLeadReducedStep1ProviderData
      hr hStanding where
  regularPolePreimage :=
    fixedOStarRegularPolePreimageDataOfDepthGTOne_of_regularPoleLeadAtTierData
      D.regularPoleLeadAtTier
  propagationBaseTailReducedZeroFreeWitness := fun p =>
    { propagationPositiveTailSliceNonzeroOnRegion :=
        D.propagationPositiveTailSliceNonzeroOnRegion
          p.probe p.mem_O_star p.iota p.visible_iota_ne
      visiblePolynomialNonzeroOnLastRegion :=
        D.visiblePolynomialNonzeroOnLastRegion
          p.probe p.mem_O_star p.iota p.visible_iota_ne }
  lastBoundaryNoPoleOnRegularDomainGraph := fun p => by
    have hboundary :=
      D.lastBoundaryNoPoleOnOStarRegularDomainGraph
        p.probe p.mem_O_star p.iota p.visible_iota_ne
    simpa [fixedOStarLastBoundaryRegularDomainGraphOfOStar_eq hStanding p] using hboundary

/-- Compile the base-tail-reduced graph-boundary provider to the current lead-reduced
provider by reconstructing the `m = 0` propagation slice from the standing
polynomial-family certificate. -/
theorem fixedOStarGraphBoundaryLeadReducedStep1ProviderData_of_baseTailLeadReduced
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D :
      FixedOStarGraphBoundaryBaseTailLeadReducedStep1ProviderData
        hr hStanding) :
    FixedOStarGraphBoundaryLeadReducedStep1ProviderData hr hStanding where
  regularPolePreimage := D.regularPolePreimage
  propagationZeroFreeWitness := fun p =>
    step1PropagationPrimitiveZeroFreeWitnessAssumptionsForDepth_of_fixedOStar_baseTailReduced
      hStanding p (D.propagationBaseTailReducedZeroFreeWitness p)
  lastBoundaryNoPoleOnRegularDomainGraph :=
    D.lastBoundaryNoPoleOnRegularDomainGraph

/-- Per-probe zero-free propagation witnesses supply the static interior
leading-coefficient nonvanishing field. -/
theorem fixedOStarInteriorLeadNonzero_of_zeroFreeWitness
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hprop :
      (p : FixedOStarProbe r L d O θ θ') ->
        Step1PropagationPrimitiveZeroFreeWitnessAssumptionsForDepth
          L d (paramStream θ') p.probe.1 p.iota) :
    FixedOStarRegularPoleInteriorPropagationLeadingCoeffNonzeroOnRegionDataOfDepthGTOne
      hr hStanding := by
  intro _hDepth p m hm x hx
  have hprimitive :
      Step1PropagationPrimitiveAssumptionsForDepth
        L d (paramStream θ') p.probe.1 p.iota :=
    step1PropagationPrimitiveAssumptionsForDepth_of_polynomialWitness
      (step1PropagationPrimitivePolynomialWitnessAssumptionsForDepth_of_fixedOStar_zeroFreeWitness
        hStanding p (hprop p))
  have hsubset :=
    fixedOStar_concretePrimedTierSystem_region_subset_step1PropagationNestedTailFamily_region
      (p := p) m
  exact hprimitive.nestedLargeness.leadingCoeff_ne_on_region m hm x (hsubset hx)

/-- The graph-boundary no-pole witness supplies the split-boundary no-pole-hit field. -/
theorem fixedOStarLastStepNoPoleHit_of_boundaryGraph
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hboundary :
      (p : FixedOStarProbe r L d O θ θ') ->
        Step1LastBoundaryFormalPhiNoPoleOnRegionAssumptionsForDepth
          L d r (paramStream θ') p.probe.1 p.probe.2
          (fixedOStarLastBoundaryRegularDomainGraph (θ := θ) (θ' := θ') p)) :
    FixedOStarRegularPoleLastStepNoPoleHitDataOfDepthGTOne hr hStanding :=
  fixedOStarRegularPoleLastStepNoPoleHitDataOfDepthGTOne_of_pointwiseNoPole
    (fixedOStarRegularPoleLastStepPointwiseNoPoleDataOfDepthGTOne_of_lastBoundaryFormalPhiNoPole
      (fixedOStarLastBoundaryFormalPhiNoPole_of_noPoleOnRegularDomainGraph hboundary))

/-- Reconstruct the depth-gated Claim-B lead-avoidance field from the propagation
zero-free witness and the graph-boundary no-pole witness. -/
theorem fixedOStarLeadAvoidance_of_zeroFreeWitness_boundaryGraph
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hprop :
      (p : FixedOStarProbe r L d O θ θ') ->
        Step1PropagationPrimitiveZeroFreeWitnessAssumptionsForDepth
          L d (paramStream θ') p.probe.1 p.iota)
    (hboundary :
      (p : FixedOStarProbe r L d O θ θ') ->
        Step1LastBoundaryFormalPhiNoPoleOnRegionAssumptionsForDepth
          L d r (paramStream θ') p.probe.1 p.probe.2
          (fixedOStarLastBoundaryRegularDomainGraph (θ := θ) (θ' := θ') p)) :
    FixedOStarRegularPoleLeadAvoidanceOnPoleHitDataOfDepthGTOne hr hStanding :=
  fixedOStarRegularPoleLeadAvoidanceOfDepthGTOne_of_interiorPropagation_and_lastStep
    (fixedOStarInteriorLeadAvoidanceOfDepthGTOne_of_nonzeroOnRegion
      (fixedOStarInteriorLeadNonzero_of_zeroFreeWitness hprop))
    (fixedOStarRegularPoleLastStepLeadAvoidanceOfDepthGTOne_of_noPoleHit
      (fixedOStarLastStepNoPoleHit_of_boundaryGraph hboundary))

/-- The projection/graph generic-polynomial witness supplies the full depth-gated
regular-pole lead-avoidance branch.

The remaining regular-pole content is therefore only the pole-preimage branch: the
positive propagation slices and formal-phi no-pole witness on the raw graph recover the
interior and last-step leading-coefficient avoidance obligations. -/
theorem fixedOStarRegularPoleLeadAvoidanceDataOfDepthGTOne_of_genericPolynomials
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hgeneric :
      Step1OStarProjectionGraphGenericPolynomialWitnessData L d r θ' O) :
    FixedOStarRegularPoleLeadAvoidanceOnPoleHitDataOfDepthGTOne hr hStanding :=
  fixedOStarLeadAvoidance_of_zeroFreeWitness_boundaryGraph
    (fun p =>
      step1PropagationPrimitiveZeroFreeWitnessAssumptionsForDepth_of_fixedOStar_baseTailReduced
        hStanding p
        { propagationPositiveTailSliceNonzeroOnRegion :=
            step1PropagationPositiveTailSliceNonzeroOnOStarProjectionData_of_depth_gt_two
              hgeneric.propagationPositiveTailSliceNonzeroOnProjection_depth_gt_two
              p.probe.1 ⟨p.probe.2, p.mem_O_star⟩
          visiblePolynomialNonzeroOnLastRegion :=
            hgeneric.visiblePolynomialNonzeroOnProjectionLastRegion
              p.probe.1 ⟨p.probe.2, p.mem_O_star⟩ p.iota p.visible_iota_ne })
    (fun p => by
      have hboundary :=
        hgeneric.lastBoundaryNoPoleOnProbeCoordGraph
          p.probe p.mem_O_star p.iota p.visible_iota_ne
      simpa [fixedOStarLastBoundaryRegularDomainGraphOfProbeCoord_eq_ofOStar
          hStanding p.mem_O_star p.iota p.visible_iota_ne,
        fixedOStarLastBoundaryRegularDomainGraphOfOStar_eq hStanding p] using
        hboundary)

/-- Compile the remaining depth-gated pole-preimage input with the existing generic
polynomial package to recover the active regular-pole-at-tier Claim-B field. -/
theorem fixedOStarRegularPoleLeadAtTierData_of_regularPolePreimage_and_genericPolynomials
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (hpreimage : FixedOStarRegularPolePreimageDataOfDepthGTOne hr hStanding)
    (hgeneric :
      Step1OStarProjectionGraphGenericPolynomialWitnessData L d r θ' O) :
    FixedOStarRegularPoleLeadAtTierData hr hStanding :=
  fixedOStarRegularPoleLeadAtTierData_of_regularPolePreimage_leadAvoidance_depth_gt_one
    hpreimage
    (fixedOStarRegularPoleLeadAvoidanceDataOfDepthGTOne_of_genericPolynomials
      hgeneric)

/-- Family-level remaining regular-pole input for Step 1.

This is the narrow geometric pole-preimage statement left after the shared
projection/graph generic-polynomial package has supplied all leading-coefficient
avoidance data.  It is depth-gated because the `L <= 1` branch is already vacuous. -/
structure Step1OStarRegularPolePreimageFamilyData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r) : Prop where
  regularPolePreimage_depth_gt_one :
    ∀ hStanding : Step1StandingAssumptions r L d O θ θ',
      FixedOStarRegularPolePreimageDataOfDepthGTOne hr hStanding

/-- Family-level compiler from the reduced regular-pole preimage package plus the
shared generic-polynomial witness to the active regular-pole-at-tier family. -/
theorem fixedOStarRegularPoleLeadAtTierData_family_of_regularPolePreimage_and_genericPolynomials
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    (hpreimage :
      Step1OStarRegularPolePreimageFamilyData
        (L := L) (d := d) (r := r) (O := O) (θ := θ) (θ' := θ') hr)
    (hgeneric :
      Step1OStarProjectionGraphGenericPolynomialWitnessData L d r θ' O) :
    ∀ hStanding : Step1StandingAssumptions r L d O θ θ',
      FixedOStarRegularPoleLeadAtTierData hr hStanding := by
  intro hStanding
  exact
    fixedOStarRegularPoleLeadAtTierData_of_regularPolePreimage_and_genericPolynomials
      (hpreimage.regularPolePreimage_depth_gt_one hStanding) hgeneric

/-- Compile the lead-reduced graph-boundary surface to the current
standing-polynomial-reduced frontier by reconstructing Claim-B lead avoidance from the
already-present propagation and graph-boundary witnesses. -/
theorem fixedOStarGraphBoundaryStandingPolynomialReducedStep1ProviderData_of_leadReduced
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D :
      FixedOStarGraphBoundaryLeadReducedStep1ProviderData hr hStanding) :
    FixedOStarGraphBoundaryStandingPolynomialReducedStep1ProviderData
      hr hStanding where
  regularPolePreimage := D.regularPolePreimage
  regularPoleLeadAvoidance :=
    fixedOStarLeadAvoidance_of_zeroFreeWitness_boundaryGraph
      D.propagationZeroFreeWitness D.lastBoundaryNoPoleOnRegularDomainGraph
  propagationZeroFreeWitness := D.propagationZeroFreeWitness
  lastBoundaryNoPoleOnRegularDomainGraph :=
    D.lastBoundaryNoPoleOnRegularDomainGraph

/-- Compile the standing-polynomial-reduced graph-boundary surface to the existing
graph-boundary provider by reconstructing the per-probe polynomial-family certificate
from the standing assumptions. -/
theorem fixedOStarGraphBoundaryReducedStep1ProviderData_of_standingPolynomialReduced
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D :
      FixedOStarGraphBoundaryStandingPolynomialReducedStep1ProviderData
        hr hStanding) :
    FixedOStarGraphBoundaryReducedStep1ProviderData hr hStanding where
  regularPolePreimage := D.regularPolePreimage
  regularPoleLeadAvoidance := D.regularPoleLeadAvoidance
  propagationPolynomialWitness := fun p =>
    step1PropagationPrimitivePolynomialWitnessAssumptionsForDepth_of_fixedOStar_zeroFreeWitness
      hStanding p (D.propagationZeroFreeWitness p)
  lastBoundaryNoPoleOnRegularDomainGraph :=
    D.lastBoundaryNoPoleOnRegularDomainGraph

/-- Compile the graph-boundary reduced Step 1 surface directly to the endpoint provider
package. -/
theorem fixedOStarStep1ProviderData_of_graphBoundaryReducedStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D : FixedOStarGraphBoundaryReducedStep1ProviderData hr hStanding) :
    FixedOStarStep1ProviderData hr hStanding :=
  fixedOStarStep1ProviderData_of_splitLeadNoPoleLastRegionData
    (fixedOStarSplitLeadNoPoleLastRegionData_of_splitPolynomialWitness_noPoleGraph
      D.regularPolePreimage D.regularPoleLeadAvoidance
      D.propagationPolynomialWitness
      D.lastBoundaryNoPoleOnRegularDomainGraph)

/-- Compile the standing-polynomial-reduced graph-boundary surface directly to the
endpoint provider package. -/
theorem fixedOStarStep1ProviderData_of_graphBoundaryStandingPolynomialReducedStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D :
      FixedOStarGraphBoundaryStandingPolynomialReducedStep1ProviderData
        hr hStanding) :
    FixedOStarStep1ProviderData hr hStanding :=
  fixedOStarStep1ProviderData_of_graphBoundaryReducedStep1ProviderData
    (fixedOStarGraphBoundaryReducedStep1ProviderData_of_standingPolynomialReduced D)

/-- Compile the lead-reduced graph-boundary surface directly to the endpoint provider
package. -/
theorem fixedOStarStep1ProviderData_of_graphBoundaryLeadReducedStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D : FixedOStarGraphBoundaryLeadReducedStep1ProviderData hr hStanding) :
    FixedOStarStep1ProviderData hr hStanding :=
  fixedOStarStep1ProviderData_of_graphBoundaryStandingPolynomialReducedStep1ProviderData
    (fixedOStarGraphBoundaryStandingPolynomialReducedStep1ProviderData_of_leadReduced D)

/-- Compile the base-tail/lead-reduced graph-boundary surface directly to the endpoint
provider package. -/
theorem fixedOStarStep1ProviderData_of_graphBoundaryBaseTailLeadReducedStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D :
      FixedOStarGraphBoundaryBaseTailLeadReducedStep1ProviderData
        hr hStanding) :
    FixedOStarStep1ProviderData hr hStanding :=
  fixedOStarStep1ProviderData_of_graphBoundaryLeadReducedStep1ProviderData
    (fixedOStarGraphBoundaryLeadReducedStep1ProviderData_of_baseTailLeadReduced D)

/-- Compile the regular-pole-at-tier base-tail graph-boundary surface directly to the
endpoint provider package. -/
theorem fixedOStarStep1ProviderData_of_graphBoundaryBaseTailLeadAtTierReducedStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D :
      FixedOStarGraphBoundaryBaseTailLeadAtTierReducedStep1ProviderData
        hr hStanding) :
    FixedOStarStep1ProviderData hr hStanding :=
  fixedOStarStep1ProviderData_of_graphBoundaryBaseTailLeadReducedStep1ProviderData
    (fixedOStarGraphBoundaryBaseTailLeadReducedStep1ProviderData_of_leadAtTierReduced D)

/-- Compile the projection/graph-reduced Step 1 surface directly to the endpoint
provider package. -/
theorem fixedOStarStep1ProviderData_of_graphBoundaryBaseTailLeadAtTierProjectionGraphReducedStep1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D :
      FixedOStarGraphBoundaryBaseTailLeadAtTierProjectionGraphReducedStep1ProviderData
        hr hStanding) :
    FixedOStarStep1ProviderData hr hStanding :=
  fixedOStarStep1ProviderData_of_graphBoundaryBaseTailLeadAtTierReducedStep1ProviderData
    (fixedOStarGraphBoundaryBaseTailLeadAtTierReducedStep1ProviderData_of_projectionGraphReduced D)

/-- Extract the Claim-C provider expected by the endpoint constructors. -/
theorem fixedOStarLastTierVisibleCoeffNonzeroData_of_step1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D : FixedOStarStep1ProviderData hr hStanding) :
    FixedOStarLastTierVisibleCoeffNonzeroData hr hStanding :=
  fixedOStarLastTierVisibleCoeffNonzeroData_of_visiblePolynomialNonzero
    hr hStanding D.visiblePolynomialNonzero

/-- Concrete continuity of lower last-layer coefficients for fixed `O_star` probes. -/
theorem fixedOStar_lastLayer_lowerCoeff_continuousAt_of_mem
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ') :
    ∀ {τ : ℂ}, 0 < L -> τ ∈ p.concretePrimedTierSystem.T (L - 1) ->
      ∀ i, i < L - 1 ->
        ContinuousAt
          (p.concretePrimedTierSystem.stratification.lastLayer.coeff i) τ := by
  intro τ hL hτ i hi
  cases L with
  | zero =>
      omega
  | succ m =>
      let A := p.concretePrimedTierSystem
      have hlast : (m + 1) - 1 < m + 1 := by omega
      have hregularLast : τ ∉ partialUnion A.stratification.S ((m + 1) - 1) := by
        have hω : τ ∈ A.stratification.omega ((m + 1) - 1) :=
          A.mem_omega hlast hτ
        simpa [ConcreteStratification.omega] using hω
      have hregular_i :
          τ ∉ partialUnion A.stratification.S (i + 1) := by
        intro hmem
        exact hregularLast
          ((partialUnion_mono_right (S := A.stratification.S) (by omega)) hmem)
      have hcont :=
        constantProbeObservableExpansion_coeff_continuousAt_of_regular
          (paramStream θ') (Real.log (r : ℝ)) p.probe.1 p.probe.2
          (m + 1) i p.iota τ (by omega) (by
            simpa [A, FixedOStarProbe.concretePrimedTierSystem,
              FixedOStarProbe.concretePrimedStratification,
              FixedOStarProbe.concretePrimedData,
              ConstantProbeConcreteData.toConcreteStratification,
              ConcreteStratificationData.toConcreteStratification,
              ConstantProbeConcreteData.toConcreteStratificationData] using hregular_i)
      simpa [A, FixedOStarProbe.concretePrimedTierSystem,
        FixedOStarProbe.concretePrimedStratification,
        FixedOStarProbe.concretePrimedData,
        ConstantProbeConcreteData.toConcreteStratification,
        ConcreteStratificationData.toConcreteStratification,
        ConstantProbeConcreteData.toConcreteStratificationData] using hcont

/-- Concrete continuity of the final visible coefficient for fixed `O_star` probes. -/
theorem fixedOStar_lastLayer_visibleCoeff_continuousAt_of_mem
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ') :
    ∀ {τ : ℂ}, 0 < L -> τ ∈ p.concretePrimedTierSystem.T (L - 1) ->
      ContinuousAt
        (p.concretePrimedTierSystem.stratification.lastLayer.coeff (L - 1)) τ := by
  intro τ hL hτ
  cases L with
  | zero =>
      omega
  | succ m =>
      let A := p.concretePrimedTierSystem
      have hlast : (m + 1) - 1 < m + 1 := by omega
      have hregularLast : τ ∉ partialUnion A.stratification.S ((m + 1) - 1) := by
        have hω : τ ∈ A.stratification.omega ((m + 1) - 1) :=
          A.mem_omega hlast hτ
        simpa [ConcreteStratification.omega] using hω
      have hcont :=
        constantProbeObservableExpansion_lastCoeff_continuousAt_of_regular
          (paramStream θ') (Real.log (r : ℝ)) p.probe.1 p.probe.2
          m p.iota (τ := τ) (by
            simpa [A, FixedOStarProbe.concretePrimedTierSystem,
              FixedOStarProbe.concretePrimedStratification,
              FixedOStarProbe.concretePrimedData,
              ConstantProbeConcreteData.toConcreteStratification,
              ConcreteStratificationData.toConcreteStratification,
              ConstantProbeConcreteData.toConcreteStratificationData] using hregularLast)
      simpa [A, FixedOStarProbe.concretePrimedTierSystem,
        FixedOStarProbe.concretePrimedStratification,
        FixedOStarProbe.concretePrimedData,
        ConstantProbeConcreteData.toConcreteStratification,
        ConcreteStratificationData.toConcreteStratification,
        ConstantProbeConcreteData.toConcreteStratificationData] using hcont

/-- TeX Step 1 Claim C interface for a fixed `O_star` probe, reduced to the explicit
last-visible-coefficient nonvanishing input above. -/
noncomputable def fixedOStar_lastTierConcreteData_of_tex
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (claimC : FixedOStarLastTierVisibleCoeffNonzeroData hr hStanding)
    (p : FixedOStarProbe r L d O θ θ') :
    LastTierConcreteData p.concretePrimedTierSystem :=
  LastTierConcreteData.of_continuousAt
    (LastTierVisibleCoeffData.of_continuousAt
      (fun hm hτ =>
        fixedOStar_lastLayer_visibleCoeff_continuousAt_of_mem p hm hτ)
      (fun hm hτ => claimC p hm hτ))
    (fun hm hτ _ hi =>
      lastTierLowerGate_continuousAt_of_mem
        p.concretePrimedTierSystem hm hτ hi)
    (fun hm hτ i hi =>
      fixedOStar_lastLayer_lowerCoeff_continuousAt_of_mem p hm hτ i hi)

/-- The TeX Step 1 analytic bridge for a fixed `O_star` probe.

This now only assembles the three field-level TeX interfaces above.  The hard analytic
work remains isolated under names matching the consumed downstream interfaces. -/
noncomputable def fixedOStar_zeroFreeAnalyticBridgeData_of_tex
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (claimB : FixedOStarZeroFreeLevelSetLeadData hr hStanding)
    (claimC : FixedOStarLastTierVisibleCoeffNonzeroData hr hStanding)
    (p : FixedOStarProbe r L d O θ θ')
    (hDepth : 1 < L) :
    FixedOStarZeroFreeAnalyticBridgeData p where
  lead_nonzero_on_first_stratum :=
    fixedOStar_firstLead_nonzero_on_firstStratum_of_tex_of_depth_gt_one
      hr hStanding p hDepth
  propagation := fixedOStar_zeroFreeTierPropagation_of_tex hr hStanding claimB p
  lastTier := fixedOStar_lastTierConcreteData_of_tex hr hStanding claimC p

/-- The probe bias is nonzero under the IDL arity hypothesis `r >= 2`. -/
theorem log_nat_ne_zero_of_two_le {r : Nat} (hr : 2 <= r) :
    Real.log (r : ℝ) ≠ 0 := by
  have hr_pos_nat : 0 < r := lt_of_lt_of_le (Nat.zero_lt_succ 1) hr
  have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr_pos_nat
  have hr_ne_one_nat : r ≠ 1 := by omega
  have hr_ne_one : (r : ℝ) ≠ 1 := by exact_mod_cast hr_ne_one_nat
  exact Real.log_ne_zero_of_pos_of_ne_one hr_pos hr_ne_one

/-- In the zero-free fixed-probe setup, the unprimed first slope cannot vanish.

This packages the part of TeX Step 4 that is not built into
`ZeroFreeConcreteDescentData.ofOStarProbeChainAndLastSubset`: the transferred last tier
and the zero-free chain put a nonempty primed first tier inside the unprimed first
stratum; if the unprimed slope were zero, that stratum would be empty. -/
theorem fixedOStar_unprimed_firstSlope_ne_of_zeroFreeBridge
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 0 < r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ')
    (B : FixedOStarZeroFreeAnalyticBridgeData p) :
    firstSlope θ p.probe.1 p.probe.2 ≠ 0 := by
  let unprimed := p.concreteUnprimedStratification
  let primed := p.concretePrimedTierSystem
  have hLast : primed.T0 (L - 1) ⊆ partialUnion unprimed.S L := by
    simpa [unprimed, primed] using
      p.zeroFreeLastTier_subset_partialUnion_of_concrete
        hr hStanding.depth_pos B.lastTier
  have hT0S0 : primed.T0 0 ⊆ unprimed.S 0 := by
    simpa [unprimed, primed] using
      tier_descent_to_first_set
        (S := unprimed.S) (T := primed.T0) (m := L)
        hStanding.depth_pos unprimed.strataSystem B.propagation.chain hLast
  have hprimedSlope :
      primed.stratification.lambda1 ≠ 0 := by
    rw [show primed.stratification.lambda1 =
        firstSlope θ' p.probe.1 p.probe.2 by
      simpa [primed] using p.concretePrimedTierSystem_lambda1_eq_firstSlope]
    exact p.primed_firstSlope_ne
  have hfirstSubset :
      firstPoleSet unprimed.b primed.stratification.lambda1 ⊆ primed.T0 0 := by
    intro τ hτ
    have hτT : τ ∈ primed.T 0 := by
      exact firstPoleSet_subset_tier_zero_of_tierSystem
        (A := primed) (b := unprimed.b) (by simp [unprimed, primed])
        hprimedSlope hτ
    have hτS : τ ∈ primed.stratification.S 0 := by
      simpa [primed] using hτT
    rw [primed.T0_zero_eq_stratum_of_lead_ne]
    · exact hτS
    · simpa [primed] using B.lead_nonzero_on_first_stratum
  have hT0_nonempty : (primed.T0 0).Nonempty := by
    rcases firstPoleSet_nonempty unprimed.b primed.stratification.lambda1 with ⟨τ, hτ⟩
    exact ⟨τ, hfirstSubset hτ⟩
  intro hzero
  rcases hT0_nonempty with ⟨τ, hτ⟩
  have hτS : τ ∈ unprimed.S 0 := hT0S0 hτ
  have hunprimedLambda_zero : unprimed.lambda1 = 0 := by
    rw [show unprimed.lambda1 = firstSlope θ p.probe.1 p.probe.2 by
      simpa [unprimed] using p.concreteUnprimedStratification_lambda1_eq_firstSlope]
    exact hzero
  exact unprimed.notMem_first_stratum_of_lambda_eq_zero hunprimedLambda_zero τ hτS

/-- Construct fixed-probe zero-free descent from an already assembled analytic bridge. -/
theorem fixedOStar_zeroFreeConcreteDescent_exists_of_bridge
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ')
    (B : FixedOStarZeroFreeAnalyticBridgeData p) :
    ∃ m : Nat, ∃ D : ZeroFreeConcreteDescentData m,
      D.unprimed.lambda1 = firstSlope θ p.probe.1 p.probe.2 ∧
        D.primed.stratification.lambda1 =
          firstSlope θ' p.probe.1 p.probe.2 := by
  have hr_pos : 0 < r := lt_of_lt_of_le (Nat.zero_lt_succ 1) hr
  have hunprimedSlope_ne :
      firstSlope θ p.probe.1 p.probe.2 ≠ 0 :=
    fixedOStar_unprimed_firstSlope_ne_of_zeroFreeBridge
      hr_pos hStanding p B
  exact p.fixedOStar_zeroFreeConcreteDescent_exists_of_concrete
    hr_pos hStanding.depth_pos (log_nat_ne_zero_of_two_le hr)
    hunprimedSlope_ne B.lead_nonzero_on_first_stratum B.propagation B.lastTier

/-- The fixed-probe zero-free concrete descent constructor needed by the Step 1
open-`O_star` assembly. -/
theorem fixedOStar_zeroFreeConcreteDescent_exists_of_tex
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (claimB : FixedOStarZeroFreeLevelSetLeadData hr hStanding)
    (claimC : FixedOStarLastTierVisibleCoeffNonzeroData hr hStanding)
    (p : FixedOStarProbe r L d O θ θ')
    (hDepth : 1 < L) :
    ∃ m : Nat, ∃ D : ZeroFreeConcreteDescentData m,
      D.unprimed.lambda1 = firstSlope θ p.probe.1 p.probe.2 ∧
        D.primed.stratification.lambda1 =
          firstSlope θ' p.probe.1 p.probe.2 := by
  have B : FixedOStarZeroFreeAnalyticBridgeData p :=
    fixedOStar_zeroFreeAnalyticBridgeData_of_tex hr hStanding claimB claimC p hDepth
  exact fixedOStar_zeroFreeConcreteDescent_exists_of_bridge hr hStanding p B

/-- If the head value matrix vanishes, the full concrete constant-probe observable is
the observable of the tail parameter family with the same probe vectors. -/
theorem constantProbeObservable_paramStream_tail_eq_of_headValue_zero
    {m d : Nat} (r : Nat) (θ : Params (m + 1) d)
    (w v : Fin d -> ℝ) (iota : Fin d) (τ : ℝ)
    (hV0 : (θ 0).1 = 0) :
    constantProbeObservable (paramStream θ) (Real.log (r : ℝ)) w v (m + 1)
        iota (τ : ℂ) =
      constantProbeObservable (paramStream (Params.tail θ)) (Real.log (r : ℝ))
        w v m iota (τ : ℂ) := by
  simpa [Params.tail, hV0] using
    constantProbeObservable_paramStream_tail_shift r θ w v iota τ

/-- The zero-free first tier for the fixed primed probe is nonempty once the bridge
proves nonvanishing of the first leading coefficient on the first stratum. -/
theorem fixedOStar_first_zeroFreeTier_nonempty
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ')
    (hlead0 :
      ∀ τ ∈ p.concretePrimedTierSystem.stratification.S 0,
        (p.concretePrimedTierSystem.nestedFamily.step 0).lead
          (gatePrefix p.concretePrimedTierSystem.stratification 0 τ) ≠ 0) :
    (p.concretePrimedTierSystem.T0 0).Nonempty := by
  let A := p.concretePrimedTierSystem
  have hprimedSlope : A.stratification.lambda1 ≠ 0 := by
    rw [show A.stratification.lambda1 =
        firstSlope θ' p.probe.1 p.probe.2 by
      simpa [A] using p.concretePrimedTierSystem_lambda1_eq_firstSlope]
    exact p.primed_firstSlope_ne
  have hfirstSubset :
      firstPoleSet A.stratification.b A.stratification.lambda1 ⊆ A.T0 0 := by
    intro τ hτ
    have hτT : τ ∈ A.T 0 := by
      exact firstPoleSet_subset_tier_zero_of_tierSystem
        (A := A) (b := A.stratification.b) rfl hprimedSlope hτ
    have hτS : τ ∈ A.stratification.S 0 := by
      simpa [A] using hτT
    rw [A.T0_zero_eq_stratum_of_lead_ne]
    · exact hτS
    · simpa [A] using hlead0
  rcases firstPoleSet_nonempty A.stratification.b A.stratification.lambda1 with ⟨τ, hτ⟩
  exact ⟨τ, hfirstSubset hτ⟩

/-- Depth-drop transfer: if the unprimed first value vanishes, the primed last zero-free
tier transfers into the singular union of the unprimed tail stratification. -/
theorem fixedOStar_zeroFreeLastTier_subset_tail_partialUnion_of_headValue_zero
    {m d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params (m + 1) d}
    (hr : 0 < r)
    (p : FixedOStarProbe r (m + 1) d O θ θ')
    (firstValue_zero : (θ 0).1 = 0)
    (lastTier : LastTierConcreteData p.concretePrimedTierSystem) :
    p.concretePrimedTierSystem.T0 m ⊆
      partialUnion
        (ConstantProbeConcreteData.toConcreteStratification
          (ConstantProbeConcreteData.ofConcrete
            (paramStream (Params.tail θ)) (Real.log (r : ℝ))
            p.probe.1 p.probe.2 m p.iota)).S m := by
  let tailData : ConstantProbeConcreteData
      (paramStream (Params.tail θ)) (Real.log (r : ℝ))
      p.probe.1 p.probe.2 m p.iota :=
    ConstantProbeConcreteData.ofConcrete
      (paramStream (Params.tail θ)) (Real.log (r : ℝ))
      p.probe.1 p.probe.2 m p.iota
  let tailStrat := tailData.toConcreteStratification
  have hEqOnTail :
      ∀ t : ℝ, max p.T0 0 < t ->
        tailStrat.observable (t : ℂ) =
          p.concretePrimedTierSystem.stratification.observable (t : ℂ) := by
    intro t ht
    have htailFull :
        tailStrat.observable (t : ℂ) =
          p.concreteUnprimedStratification.observable (t : ℂ) := by
      simpa [tailStrat, tailData, FixedOStarProbe.concreteUnprimedStratification,
        FixedOStarProbe.concreteUnprimedData,
        ConstantProbeConcreteData.toConcreteStratification,
        ConstantProbeConcreteData.toConcreteStratificationData] using
        (constantProbeObservable_paramStream_tail_eq_of_headValue_zero
          r θ p.probe.1 p.probe.2 p.iota t firstValue_zero).symm
    exact htailFull.trans (p.realTailObservableAgreement_concrete hr t ht)
  let A := p.concretePrimedTierSystem
  have hblow : ∀ τ, τ ∈ A.T0 ((m + 1) - 1) ->
      BlowsUpAt A.stratification.observable τ := by
    intro τ hτ
    exact (lastTier.toZeroFreeLastTierBlowup (Nat.succ_pos m)).observable_blowsUpAt hτ
  have hfreq :
      ∃ᶠ z in nhdsWithin ((max p.T0 0 + 1 : ℝ) : ℂ)
        ({((max p.T0 0 + 1 : ℝ) : ℂ)}ᶜ : Set ℂ),
        tailStrat.observable z = A.stratification.observable z :=
    frequently_equal_of_eqOn_real_tail (by linarith) hEqOnTail
  have hreg :
      ((max p.T0 0 + 1 : ℝ) : ℂ) ∈
        (tailStrat.singularSet ∪ A.stratification.singularSet)ᶜ := by
    rw [Set.mem_compl_iff, Set.mem_union]
    exact not_or.mpr
      ⟨tailStrat.singularSet_avoids_real (max p.T0 0 + 1),
        A.stratification.singularSet_avoids_real (max p.T0 0 + 1)⟩
  have hsubset :
      A.T0 ((m + 1) - 1) ⊆ tailStrat.singularSet := by
    exact transferred_tier_subset
      (E_F := tailStrat.singularSet)
      (E_G := A.stratification.singularSet)
      (T := A.T0 ((m + 1) - 1))
      (F := tailStrat.observable)
      (G := A.stratification.observable)
      (z0 := ((max p.T0 0 + 1 : ℝ) : ℂ))
      tailStrat.singularSet_closed
      tailStrat.singularSet_countable
      A.stratification.singularSet_countable
      tailStrat.observable_analyticOn_singularCompl
      A.stratification.observable_analyticOn_singularCompl
      hreg
      hfreq
      (fun τ hτ => tailStrat.observable_continuousAt_of_regular hτ)
      (by
        intro τ hτ0
        have hτ : τ ∈ A.T ((m + 1) - 1) :=
          A.T0_subset_T ((m + 1) - 1) hτ0
        have hlt : (m + 1) - 1 < m + 1 := by omega
        have hIso :
            IsPuncturedIsolated
              (partialUnion A.stratification.S (((m + 1) - 1) + 1)) τ :=
          A.punctured_isolated_partialUnion_succ
            (j := (m + 1) - 1) hlt hτ
        have hlast : ((m + 1) - 1) + 1 = m + 1 := by omega
        simpa [ConcreteStratification.singularSet, hlast] using hIso)
      hblow
  have hpartial :
      A.T0 ((m + 1) - 1) ⊆ partialUnion tailStrat.S m := by
    simpa [ConcreteStratification.singularSet] using hsubset
  simpa [A] using hpartial

/-- Data produced by rerunning the Step 1 transfer after a first-layer value drop.

In TeX Corollary `depth`, assuming `V_1 = 0` replaces the unprimed singular set by the
`L - 1` tail stratification.  The same primed tier chain then puts a nonempty first
tier inside `accIter (L - 1)` of an `(L - 1)`-stratum union, contradicting
`strataacc`. -/
structure FirstLayerValueDepthDropData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (_hStanding : Step1StandingAssumptions r L d O θ θ')
    (_step1_eq : Step1Conclusion θ θ')
    (_firstValue_zero : (θ ⟨0, _hStanding.depth_pos⟩).1 = 0) : Type where
  droppedStrata : Nat -> Set ℂ
  primedTier : Nat -> Set ℂ
  dropped_strata : StrataSystem droppedStrata (L - 1)
  firstTier_nonempty : (primedTier 0).Nonempty
  chain : ∀ j : Nat, j < L - 1 -> primedTier j ⊆ acc (primedTier (j + 1))
  last_subset : primedTier (L - 1) ⊆ partialUnion droppedStrata (L - 1)

namespace FirstLayerValueDepthDropData

/-- Compile the TeX depth-drop data into the contradiction from the
`(L - 1)`-stratum accumulation bound. -/
theorem false
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    {step1_eq : Step1Conclusion θ θ'}
    {firstValue_zero : (θ ⟨0, hStanding.depth_pos⟩).1 = 0}
    (D : FirstLayerValueDepthDropData hStanding step1_eq firstValue_zero) :
    False := by
  rcases D.firstTier_nonempty with ⟨τ, hτ⟩
  have hAccTier : τ ∈ accIter (L - 1) (D.primedTier (L - 1)) := by
    exact tier_chain_subset_accIter (T := D.primedTier) (L - 1) D.chain hτ
  have hAccDropped :
      τ ∈ accIter (L - 1) (partialUnion D.droppedStrata (L - 1)) :=
    accIter_mono D.last_subset (L - 1) hAccTier
  have hEmpty :
      accIter (L - 1) (partialUnion D.droppedStrata (L - 1)) = ∅ :=
    accIter_partialUnion_eq_empty D.dropped_strata
  rw [hEmpty] at hAccDropped
  simpa using hAccDropped

end FirstLayerValueDepthDropData

/-- TeX Corollary `depth`, reduced to the explicit depth-drop transfer data. -/
noncomputable def firstLayerValueDepthDropData_of_tex
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (claimB : FixedOStarZeroFreeLevelSetLeadData hr hStanding)
    (claimC : FixedOStarLastTierVisibleCoeffNonzeroData hr hStanding)
    (step1_eq : Step1Conclusion θ θ')
    (firstValue_zero : (θ ⟨0, hStanding.depth_pos⟩).1 = 0)
    (hDepth : 1 < L) :
    FirstLayerValueDepthDropData hStanding step1_eq firstValue_zero := by
  cases L with
  | zero =>
      exact False.elim (Nat.not_lt_zero _ hStanding.depth_pos)
  | succ m =>
      let hOStar : (O_star θ' O).Nonempty :=
        O_star_nonempty_of_generic hStanding.generic
      let probe : ProbePair d := Classical.choose hOStar
      have hprobe : probe ∈ O_star θ' O := Classical.choose_spec hOStar
      let p : FixedOStarProbe r (m + 1) d O θ θ' :=
        FixedOStarProbe.ofLocalAgreement hStanding.agreement hprobe
      let tailData : ConstantProbeConcreteData
          (paramStream (Params.tail θ)) (Real.log (r : ℝ))
          p.probe.1 p.probe.2 m p.iota :=
        ConstantProbeConcreteData.ofConcrete
          (paramStream (Params.tail θ)) (Real.log (r : ℝ))
          p.probe.1 p.probe.2 m p.iota
      let tailStrat := tailData.toConcreteStratification
      have B : FixedOStarZeroFreeAnalyticBridgeData p :=
        fixedOStar_zeroFreeAnalyticBridgeData_of_tex
          hr hStanding claimB claimC p (by omega)
      refine
        { droppedStrata := tailStrat.S
          primedTier := p.concretePrimedTierSystem.T0
          dropped_strata := ?_
          firstTier_nonempty := ?_
          chain := ?_
          last_subset := ?_ }
      · simpa [tailStrat] using tailStrat.strataSystem
      · exact fixedOStar_first_zeroFreeTier_nonempty p B.lead_nonzero_on_first_stratum
      · intro j hj
        exact B.propagation.chain j (by omega)
      · have hV0 : (θ 0).1 = 0 := by
          simpa using firstValue_zero
        have hr_pos : 0 < r := lt_of_lt_of_le (Nat.zero_lt_succ 1) hr
        have hlast :=
          fixedOStar_zeroFreeLastTier_subset_tail_partialUnion_of_headValue_zero
            hr_pos p hV0 B.lastTier
        simpa [tailStrat, tailData] using hlast

/-- No-depth-drop for the unprimed first value matrix in the TeX Step 1 setup. -/
theorem firstLayerValueNoDepthDrop_of_tex
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (claimB : FixedOStarZeroFreeLevelSetLeadData hr hStanding)
    (claimC : FixedOStarLastTierVisibleCoeffNonzeroData hr hStanding)
    (hDepth : 1 < L) :
    FirstLayerValueNoDepthDrop θ θ' hStanding.depth_pos := by
  intro step1_eq firstValue_zero
  exact (firstLayerValueDepthDropData_of_tex
    hr hStanding claimB claimC step1_eq firstValue_zero hDepth).false

/-- Local constant-path tail agreement obtained from the path/open-set IDL invariant. -/
noncomputable def localProbeTailAgreement_of_IDLData
    {L d r : Nat} {θ θ' : Params L d}
    (D : IDLData L d r θ θ') :
    LocalProbeTailAgreement r L d D.O θ θ' := by
  classical
  refine
    { T0 := fun p =>
        if hp : p ∈ D.O then
          Classical.choose (D.realTailObservableAgreementAt_of_mem hp)
        else
          0
      eqOnTail := ?_ }
  · intro p hp
    simpa [dif_pos hp] using
      (Classical.choose_spec (D.realTailObservableAgreementAt_of_mem hp)).2

/-- Step 1 plus the depth certificate, packaged from local standing assumptions. -/
theorem firstLayerEndpoint_of_step1Standing
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params (L + 1) d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r (L + 1) d O θ θ')
    (claimB : FixedOStarZeroFreeLevelSetLeadData hr hStanding)
    (claimC : FixedOStarLastTierVisibleCoeffNonzeroData hr hStanding)
    (hDepth : 0 < L) :
    FirstLayerEndpointData
      (Params.headAttention θ) (Params.headAttention θ')
      (Params.headValue θ) := by
  have hStep1Theorem :
      ConcreteStep1TheoremStatement r (L + 1) d O θ θ' :=
    zeroFreeConcreteStep1Theorem_of_openOStar_fixed_concrete_descent
      (fun hStanding p =>
        fixedOStar_zeroFreeConcreteDescent_exists_of_tex
          hr hStanding claimB claimC p (by omega))
  have hStep1 : Step1Conclusion θ θ' := hStep1Theorem hStanding
  have hAttention : Params.headAttention θ = Params.headAttention θ' := by
    have hθ : firstAttention θ = Params.headAttention θ := by
      simpa [Params.headAttention, Params.headLayer] using
        firstAttention_eq_of_pos θ (Nat.succ_pos L)
    have hθ' : firstAttention θ' = Params.headAttention θ' := by
      simpa [Params.headAttention, Params.headLayer] using
        firstAttention_eq_of_pos θ' (Nat.succ_pos L)
    calc
      Params.headAttention θ = firstAttention θ := hθ.symm
      _ = firstAttention θ' := hStep1
      _ = Params.headAttention θ' := hθ'
  have hNoDepthDrop :
      FirstLayerValueNoDepthDrop θ θ' hStanding.depth_pos :=
    firstLayerValueNoDepthDrop_of_tex hr hStanding claimB claimC (by omega)
  have hHeadValue :
      Params.headValue θ ≠ 0 := by
    have hConcrete :
        (θ ⟨0, hStanding.depth_pos⟩).1 ≠ 0 :=
      firstLayerValue_ne_zero_of_concrete_step1_noDepthDrop
        hStep1Theorem hStanding hNoDepthDrop
    simpa [Params.headValue, Params.headLayer] using hConcrete
  exact FirstLayerEndpointData.of_attention_eq hAttention hHeadValue

/-- Step 1 endpoint from the local path/open-set IDL invariant. -/
theorem firstLayerEndpoint_of_texGenericStep_of_IDLData
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (D : IDLData (L + 1) d r θ θ')
    (claimB :
      ∀ hStanding : Step1StandingAssumptions r (L + 1) d D.O θ θ',
        FixedOStarZeroFreeLevelSetLeadData hr hStanding)
    (claimC :
      ∀ hStanding : Step1StandingAssumptions r (L + 1) d D.O θ θ',
        FixedOStarLastTierVisibleCoeffNonzeroData hr hStanding) :
    FirstLayerEndpointData
      (Params.headAttention θ) (Params.headAttention θ')
      (Params.headValue θ) := by
  cases L with
  | zero =>
      have matching : FirstLayerMatchedData θ θ' :=
        IDL_depth_one_matching_of_localTailAgreement hr D
      exact FirstLayerEndpointData.of_attention_eq
        matching.headAttention_eq matching.headValue_ne_zero
  | succ L =>
      have hStanding : Step1StandingAssumptions r (L + 1 + 1) d D.O θ θ' :=
        { depth_pos := Nat.succ_pos (L + 1)
          generic := hstep.toOStarGenericAssumptions D.O_open D.O_nonempty
          agreement := localProbeTailAgreement_of_IDLData D }
      exact firstLayerEndpoint_of_step1Standing hr hStanding
        (claimB hStanding) (claimC hStanding) (Nat.succ_pos L)

/-! ## The genuine algebraic bridge: formal-phi lead nonzero at `A_gp` tier points

TeX `lem:nested` Conclusion (`n_layer_proof.tex:1413-1416`): the propagation factor
`f_{j+2} = formalLastSqCoeffPoly θ' j w` involves only `z_0,…,z_{j-1}`, so its iterated
leading coefficient down to level `j` is itself ("`p_a^{(k)} = p_a` when
`p_a ∈ ℂ[z_1,…,z_k]`").  The global-product tower already proves each factor's iterated
leading coefficient is nonvanishing on the genuine nested region `N_j`
(`globalLcTower_factor_eval_ne_on_region`); here we identify that iterated leading
coefficient with the formal-phi propagation leading coefficient, across the change of
ambient gate ring (`Fin (n+1)` for the global product versus `Fin (j+1)` for the
propagation tower).  This is the "one genuine algebraic bridge" of `STEP_1_PLAN.md`,
item 1: pure cross-`K` evaluation bookkeeping, no new analysis. -/

open Matrix in
/-- Evaluation of `formalLastSqCoeffPoly` factors through the zero-padded gate stream
`extendGate x`, hence is independent of the ambient number of gate variables `K`. -/
theorem eval_formalLastSqCoeffPoly {K d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (x : Fin K → ℂ) (w : Fin d → ℝ) :
    MvPolynomial.eval x (formalLastSqCoeffPoly θ n w) =
      -((matC (θ n).1 *ᵥ formalWVec θ n (extendGate x) w) ⬝ᵥ
        (matC (θ (n + 1)).2 *ᵥ (matC (θ n).1 *ᵥ formalWVec θ n (extendGate x) w))) := by
  rw [formalLastSqCoeffPoly, map_neg, eval_dotProduct]
  simp only [eval_mulVec, eval_matPolyC, eval_formalWVecPoly]

/-- Cross-`K` agreement of `formalLastSqCoeffPoly` evaluation: the same zero-padded gate
stream yields the same value, even at different ambient gate-ring sizes. -/
theorem eval_formalLastSqCoeffPoly_congr {K₁ K₂ d : ℕ}
    (θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (w : Fin d → ℝ) {x₁ : Fin K₁ → ℂ} {x₂ : Fin K₂ → ℂ}
    (h : extendGate x₁ = extendGate x₂) :
    MvPolynomial.eval x₁ (formalLastSqCoeffPoly θ n w) =
      MvPolynomial.eval x₂ (formalLastSqCoeffPoly θ n w) := by
  rw [eval_formalLastSqCoeffPoly, eval_formalLastSqCoeffPoly, h]

/-- `extendGate` only sees the first `j` coordinates: any `z : Fin K → ℂ` that restricts
to `extendGate x` zero-pads to the same `Nat`-indexed stream. -/
theorem extendGate_eq_of_apply_eq {K j : ℕ} {z : Fin K → ℂ} {x : Fin j → ℂ}
    (hjK : j ≤ K) (h : ∀ i : Fin K, z i = extendGate x (i : ℕ)) :
    extendGate z = extendGate x := by
  funext k
  by_cases hk : k < K
  · have hz : extendGate z k = z ⟨k, hk⟩ := by simp [extendGate, hk]
    rw [hz, h ⟨k, hk⟩]
  · have hz : extendGate z k = 0 := by simp [extendGate, hk]
    have hx : extendGate x k = 0 := by
      have hkj : ¬ k < j := by omega
      simp [extendGate, hkj]
    rw [hz, hx]

/-- A polynomial that does not involve its last variable equals, after renaming the
remaining variables up by `Fin.castSucc`, its last-variable leading coefficient.  Proven
by `MvPolynomial.funext`: both sides agree under every evaluation. -/
theorem eq_rename_castSucc_lcLast_of_degreeOf_last_zero {k : ℕ}
    {R : MvPolynomial (Fin (k + 1)) ℂ}
    (hR : MvPolynomial.degreeOf (Fin.last k) R = 0) :
    R = MvPolynomial.rename Fin.castSucc (lcLast R) := by
  apply MvPolynomial.funext
  intro z
  rw [MvPolynomial.eval_rename, eval_eq_eval_lcLast_of_degreeOf_last_zero hR z]
  rfl

/-- **TeX `lem:nested` Step 1, "`p_a^{(k)} = p_a` when `p_a ∈ ℂ[z_1,…,z_k]`".**  If `P`
has degree `0` in every gate variable strictly above index `m`, then its level-`m` iterated
leading coefficient `globalLcTower n P m`, renamed back up into `Fin (n+1)`, is `P` itself.
The proof is a downward induction on `m` (via the gap `t = n - m`): each peel drops one
genuinely-absent top variable (`eq_rename_castSucc_lcLast_of_degreeOf_last_zero`), and the
absence propagates through the rename relation. -/
theorem rename_castLE_globalLcTower_eq_of_degreeOf {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℂ) :
    ∀ (t m : ℕ) (hmle : m + 1 ≤ n + 1) (_hmt : m + t = n)
      (_hdeg : ∀ i : Fin (n + 1), m < (i : ℕ) → MvPolynomial.degreeOf i P = 0),
      MvPolynomial.rename (Fin.castLE hmle) (globalLcTower n P m) = P := by
  intro t
  induction t with
  | zero =>
      intro m hmle hmt _hdeg
      have hmn : m = n := by omega
      subst hmn
      rw [globalLcTower_self]
      have hid : (Fin.castLE hmle) = (id : Fin (m + 1) → Fin (m + 1)) := by
        funext i; exact Fin.ext rfl
      rw [hid, MvPolynomial.rename_id]
      rfl
  | succ t ih =>
      intro m hmle hmt hdeg
      have hmn : m < n := by omega
      have hmne : m ≠ n := Nat.ne_of_lt hmn
      have hmle' : m + 1 + 1 ≤ n + 1 := by omega
      have hdeg1 : ∀ i : Fin (n + 1), m + 1 < (i : ℕ) → MvPolynomial.degreeOf i P = 0 :=
        fun i hi => hdeg i (by omega)
      have IHm1 := ih (m + 1) hmle' (by omega) hdeg1
      have hinj : Function.Injective (Fin.castLE hmle') :=
        fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab)
      have hRdeg_last :
          MvPolynomial.degreeOf (Fin.last (m + 1)) (globalLcTower n P (m + 1)) = 0 := by
        have key := MvPolynomial.degreeOf_rename_of_injective
          (p := globalLcTower n P (m + 1)) hinj (Fin.last (m + 1))
        rw [IHm1] at key
        have hcast : (Fin.castLE hmle') (Fin.last (m + 1))
            = (⟨m + 1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
        rw [← key, hcast]
        exact hdeg ⟨m + 1, by omega⟩ (by simp)
      have hReq := eq_rename_castSucc_lcLast_of_degreeOf_last_zero hRdeg_last
      have hlc : lcLast (globalLcTower n P (m + 1)) = globalLcTower n P m :=
        lcLast_globalLcTower n P hmne
      have hcomp : (Fin.castLE hmle) = (Fin.castLE hmle') ∘ Fin.castSucc := by
        funext i; exact Fin.ext rfl
      rw [← hlc, hcomp, ← MvPolynomial.rename_rename, ← hReq, IHm1]

/-- **The genuine algebraic bridge (TeX `lem:nested` Conclusion, at the propagation
factor).**  At a point of the global-product nested region `N_j`, the formal-phi
propagation leading coefficient `step1PropagationLeadingCoeffPoly θ w j` is nonzero. -/
theorem eval_step1PropagationLeadingCoeffPoly_ne_zero_of_globalLcRegion {d n : ℕ}
    {θ : Nat → Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ}
    {w : Fin d → ℝ} {iota : Fin d}
    (hfam : Step1PolynomialFamilyAssumptions (n + 1) d θ w iota)
    {j : ℕ} (hjn : j < n + 1) {x : Fin j → ℂ}
    (hx : x ∈ (globalLcNestedTailData n (step1GlobalProductPoly θ w iota n)).region j) :
    MvPolynomial.eval x (step1PropagationLeadingCoeffPoly θ w j) ≠ 0 := by
  cases j with
  | zero =>
      have hkappa : step1KappaScalar θ 0 w ≠ 0 := hfam.kappa_ne ⟨0, Nat.succ_pos n⟩
      have hdtc : HasDominantTopCoeff (step1PropagationLeadingCoeffPoly θ w 0) := by
        unfold step1PropagationLeadingCoeffPoly
        rw [step1PropagationTailPoly]
        exact hasDominantTopCoeff_lcLast
          (hasDominantTopCoeff_step1LastSqCoeffPoly θ ⟨0, by omega⟩ w hkappa)
      exact eval_ne_zero_fin_zero_of_ne_zero hdtc.ne_zero x
  | succ m =>
      have hm : m ≤ n := by omega
      have hmle : m + 1 ≤ n + 1 := by omega
      have hP : HasDominantTopCoeff
          (∏ a ∈ (Finset.univ : Finset (Step1PolynomialIndex (n + 1))),
            step1PolynomialFamilyPoly (K := n + 1) θ w iota a) := by
        simpa [step1GlobalProductPoly] using hasDominantTopCoeff_step1GlobalProductPoly hfam
      have hxregion : x ∈ (globalLcNestedTailData n
          (∏ a ∈ (Finset.univ : Finset (Step1PolynomialIndex (n + 1))),
            step1PolynomialFamilyPoly (K := n + 1) θ w iota a)).region (m + 1) := by
        simpa [step1GlobalProductPoly] using hx
      have hfactor := globalLcTower_factor_eval_ne_on_region n Finset.univ
        (step1PolynomialFamilyPoly (K := n + 1) θ w iota) hP hxregion
        (a := some ⟨m + 1, hjn⟩) (Finset.mem_univ _)
      set F : MvPolynomial (Fin (n + 1)) ℂ :=
        step1LastSqCoeffPoly (K := n + 1) θ w ⟨m + 1, hjn⟩ with hFdef
      have hFdeg : ∀ i : Fin (n + 1), m < (i : ℕ) → MvPolynomial.degreeOf i F = 0 := by
        intro i hi
        rw [hFdef]
        exact degreeOf_step1LastSqCoeffPoly_eq_zero_of_le θ ⟨m + 1, hjn⟩ (j := i) w
          (Nat.succ_le_of_lt hi)
      have hren : MvPolynomial.rename (Fin.castLE hmle) (globalLcTower n F m) = F :=
        rename_castLE_globalLcTower_eq_of_degreeOf F (n - m) m hmle (by omega) hFdeg
      set y : Fin (n + 1) → ℂ := fun i => extendGate x (i : ℕ) with hydef
      have hyapp : ∀ i : Fin (n + 1), y i = extendGate x (i : ℕ) := fun i => by rw [hydef]
      have hyx : (y ∘ Fin.castLE hmle) = x := by
        funext i
        rw [Function.comp_apply, hyapp]
        have hival : ((Fin.castLE hmle i : Fin (n + 1)) : ℕ) = (i : ℕ) := rfl
        rw [hival]
        simp [extendGate, i.isLt]
      have hgl_eval : MvPolynomial.eval x (globalLcTower n F m) = MvPolynomial.eval y F := by
        conv_lhs => rw [← hyx]
        rw [← MvPolynomial.eval_rename, hren]
      have hextend_y : extendGate y = extendGate x :=
        extendGate_eq_of_apply_eq hmle hyapp
      have hextend_snoc : extendGate (Fin.snoc x (0 : ℂ)) = extendGate x := by
        apply extendGate_eq_of_apply_eq (Nat.le_succ (m + 1))
        intro i
        refine Fin.lastCases ?_ ?_ i
        · rw [Fin.snoc_last]; simp [extendGate, Fin.val_last]
        · intro i'
          rw [Fin.snoc_castSucc]; simp [extendGate, i'.isLt]
      have hcross : MvPolynomial.eval y F
          = MvPolynomial.eval (Fin.snoc x (0 : ℂ)) (step1PropagationTailPoly θ w (m + 1)) := by
        rw [hFdef, step1PropagationTailPoly, step1LastSqCoeffPoly, step1LastSqCoeffPoly]
        exact eval_formalLastSqCoeffPoly_congr θ (m + 1) w (by rw [hextend_y, hextend_snoc])
      rw [← eval_step1PropagationTailPoly_snoc_eq_leadingCoeff_eval θ w x (0 : ℂ),
        ← hcross, ← hgl_eval]
      exact hfactor

/-- **Formal-phi lead nonzero at every global-product tier point `A_gp`.**

The formal-phi leading coefficient `f_{j+2}` is nonzero at the gate prefix of any zero-free
tier point of the global-product tier system.  Unlike the formal-phi tier system (whose own
region is the unprovable exterior polydomain), the global-product regions are the genuine
nested regions `N_j` on which `lem:nested` controls the factor.  This is the global-product
analogue of `fixedOStar_formalPhiLead_ne_of_mem_propagationVisibleTierSystem_T0`. -/
theorem fixedOStar_formalPhiLead_ne_of_mem_globalProductTierSystem_T0
    {L d r : Nat} {O : Set (ProbePair d)} {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ') {n : Nat}
    (hfam : Step1PolynomialFamilyAssumptions (n + 1) d (paramStream θ') p.probe.1 p.iota)
    {j : Nat} {τ : ℂ} (hjL : j < L - 1) (hjn : j < n + 1)
    (hτ : τ ∈ (p.globalProductTierSystem n).T0 j) :
    (p.concretePrimedTierSystem.nestedFamily.step j).lead
        (gatePrefix p.concretePrimedTierSystem.stratification j τ) ≠ 0 := by
  have hxregion :
      gatePrefix p.concretePrimedTierSystem.stratification j τ ∈
        (globalLcNestedTailData n
          (step1GlobalProductPoly (paramStream θ') p.probe.1 p.iota n)).region j := by
    simpa [FixedOStarProbe.globalProductTierSystem, PolynomialNestedTailData.region,
      FixedOStarProbe.concretePrimedTierSystem_stratification] using
      (p.globalProductTierSystem n).T0_mem_region hτ
  rw [fixedOStar_concretePrimedTierSystem_stepLead_eq_step1PropagationLeadingCoeffPoly
    hStanding p hjL]
  exact eval_step1PropagationLeadingCoeffPoly_ne_zero_of_globalLcRegion hfam hjn hxregion

/-- **Blow-up of `H'_{j+1}` at every global-product tier point `A_gp` (TeX Claim B,
steps i–iii).**  Combine the formal-phi lead nonvanishing (the algebraic bridge above) with
`fixedOStar_H_blowsUpAt_of_stratum_formalPhiLead_ne`: at a zero-free tier point of the
global-product tier system, the next preactivation `H'_{j+1}` blows up. -/
theorem fixedOStar_globalProductTierSystem_H_blowsUpAt
    {L d r : Nat} {O : Set (ProbePair d)} {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ') {n : Nat}
    (hfam : Step1PolynomialFamilyAssumptions (n + 1) d (paramStream θ') p.probe.1 p.iota)
    {j : Nat} {τ : ℂ} (hj : j + 1 < L) (hjn : j < n + 1)
    (hτ : τ ∈ (p.globalProductTierSystem n).T0 j) :
    BlowsUpAt (p.concretePrimedTierSystem.stratification.H (j + 1)) τ := by
  have hτS : τ ∈ p.concretePrimedTierSystem.stratification.S j :=
    (p.globalProductTierSystem n).T0_mem_stratum hτ
  have hτ0 : τ ≠ 0 := (p.globalProductTierSystem n).T0_ne_zero (by omega) hτ
  exact fixedOStar_H_blowsUpAt_of_stratum_formalPhiLead_ne hStanding p hj hτS hτ0
    (fixedOStar_formalPhiLead_ne_of_mem_globalProductTierSystem_T0 hStanding p hfam
      (by omega) hjn hτ)

/-! ## A_gp Claim-B chain, with the lead-avoidance wall removed

Assembling the decoupled Claim-B engine on the global-product tier system.  The crucial
gain over the formal-phi tier system: on `A_gp` the next leading-coefficient avoidance is
*provable* (the lead-avoidance kernel
`fixedOStar_step1GlobalProduct_frequently_poleHit_and_leadNonzero`, whose lead control is
the algebraic bridge `lem:nested` proved above), so the level-set Claim-B input reduces to
*only* the pole-preimage (frequent regular pole hits of `H'_{j+1}`), which is supplied from
`O_star` genericity.  The whole chain `T0 j ⊆ acc (T0 (j+1))` for `A_gp` then follows. -/

/-- **A_gp removes the lead-avoidance wall.**  At a global-product tier point, frequent
regular pole hits of `H'_{j+1}` already (i) avoid the next leading-coefficient zero locus
(the lead-avoidance kernel, discharged by the algebraic bridge) and (ii) lie in the
successor stratum (the regular sigmoid level set), giving the full level-set Claim-B
conclusion from the pole-preimage alone. -/
theorem fixedOStar_globalProduct_levelSetLead_of_poleHit
    {L d r : Nat} {O : Set (ProbePair d)} {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ') {n : Nat} (hn : n + 2 = L)
    {j : Nat} {τ : ℂ} (hj : j + 1 < L)
    (hτ : τ ∈ (p.globalProductTierSystem n).T0 j)
    (hpole : ∃ᶠ z in puncturedNhds τ,
      z ∈ p.concretePrimedStratification.omega (j + 1)
        ∧ p.concretePrimedStratification.H (j + 1) z ∈ oddPiI) :
    ∃ᶠ z in puncturedNhds τ,
      z ∈ (p.globalProductTierSystem n).stratification.S (j + 1)
        ∧ ((p.globalProductTierSystem n).nestedFamily.step (j + 1)).lead
            (gatePrefix (p.globalProductTierSystem n).stratification (j + 1) z) ≠ 0 := by
  have hfam : Step1PolynomialFamilyAssumptions (n + 1) d (paramStream θ') p.probe.1 p.iota := by
    rw [show n + 1 = L - 1 by omega]
    exact p.step1PolynomialFamilyAssumptionsForDepth hStanding.depth_pos
  have hfreq :=
    fixedOStar_step1GlobalProduct_frequently_poleHit_and_leadNonzero p hfam hj hτ hpole
  refine hfreq.mono fun z hz => ?_
  rcases hz with ⟨⟨hregular, hpolez⟩, hlead⟩
  refine ⟨?_, hlead⟩
  show z ∈ p.concretePrimedStratification.S (j + 1)
  simpa [FixedOStarProbe.concretePrimedStratification,
    FixedOStarProbe.concretePrimedData,
    ConstantProbeConcreteData.toConcreteStratification,
    ConcreteStratificationData.toConcreteStratification,
    ConstantProbeConcreteData.toConcreteStratificationData,
    ConcreteStratification.omega] using
    constantProbeStratum_mem_of_notMem_previous_and_pole
      (paramStream θ') (Real.log (r : ℝ)) p.probe.1 p.probe.2
      (hprev := by
        simpa [FixedOStarProbe.concretePrimedStratification,
          FixedOStarProbe.concretePrimedData,
          ConstantProbeConcreteData.toConcreteStratification,
          ConcreteStratificationData.toConcreteStratification,
          ConstantProbeConcreteData.toConcreteStratificationData,
          ConcreteStratification.omega] using hregular)
      (hpole := by
        simpa [FixedOStarProbe.concretePrimedStratification,
          FixedOStarProbe.concretePrimedData,
          ConstantProbeConcreteData.toConcreteStratification,
          ConcreteStratificationData.toConcreteStratification,
          ConstantProbeConcreteData.toConcreteStratificationData] using hpolez)

/-- **Decoupled Claim-B data for the global-product tier system, reduced to the single
pole-preimage leaf.**  Blow-up of `H'_{j+1}` is the algebraic-bridge blow-up
(`fixedOStar_globalProductTierSystem_H_blowsUpAt`); the level-set lead is supplied from the
pole-preimage via `fixedOStar_globalProduct_levelSetLead_of_poleHit`; the remaining fields
are generic stratification / polynomial-nested-data facts. -/
theorem fixedOStar_globalProduct_zeroFreeDecoupledPropagationData_of_poleHit
    {L d r : Nat} {O : Set (ProbePair d)} {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ') {n : Nat} (hn : n + 2 = L)
    (hpolePreimage :
      ∀ {j : Nat} {τ : ℂ}, j + 1 < L → τ ∈ (p.globalProductTierSystem n).T0 j →
        BlowsUpAt (p.concretePrimedStratification.H (j + 1)) τ →
        ∃ᶠ z in puncturedNhds τ, p.concretePrimedStratification.H (j + 1) z ∈ oddPiI) :
    ZeroFreeDecoupledPropagationData (p.globalProductTierSystem n) where
  gateArgument_blowsUpAt := by
    intro j τ hj hτ
    have hfam :
        Step1PolynomialFamilyAssumptions (n + 1) d (paramStream θ') p.probe.1 p.iota := by
      rw [show n + 1 = L - 1 by omega]
      exact p.step1PolynomialFamilyAssumptionsForDepth hStanding.depth_pos
    exact fixedOStar_globalProductTierSystem_H_blowsUpAt hStanding p hfam hj (by omega) hτ
  gatePrefix_continuousAt := by
    intro j τ hj hτ
    exact fixedOStar_gatePrefix_continuousAt_of_mem_stratum p (by omega)
      ((p.globalProductTierSystem n).T0_mem_stratum hτ)
  zeroFreeRegion_isOpen := by
    intro j
    simpa [FixedOStarProbe.globalProductTierSystem,
      PolynomialNestedTailData.zeroFreeRegion] using
      (globalLcNestedTailData n
        (step1GlobalProductPoly (paramStream θ') p.probe.1 p.iota n)).isOpen_zeroFreeRegion j
  threshold_puncturedBounded := by
    intro j τ hj hτ
    have hτprefixD :
        gatePrefix p.concretePrimedStratification j τ ∈
          (globalLcNestedTailData n
            (step1GlobalProductPoly (paramStream θ') p.probe.1 p.iota n)).zeroFreeRegion j := by
      simpa [FixedOStarProbe.globalProductTierSystem,
        PolynomialNestedTailData.zeroFreeRegion] using
        (p.globalProductTierSystem n).T0_mem_zeroFreeRegion hτ
    have hprefix :
        ContinuousAt (fun z => gatePrefix p.concretePrimedStratification j z) τ :=
      fixedOStar_gatePrefix_continuousAt_of_mem_stratum p (by omega)
        ((p.globalProductTierSystem n).T0_mem_stratum hτ)
    have hthreshold_contD :
        ContinuousAt
          ((globalLcNestedTailData n
            (step1GlobalProductPoly (paramStream θ') p.probe.1 p.iota n)).threshold j)
          (gatePrefix p.concretePrimedStratification j τ) :=
      ((globalLcNestedTailData n
        (step1GlobalProductPoly (paramStream θ') p.probe.1 p.iota n)).continuousOn_thresholds_zeroFreeRegion
          j).continuousAt
        (((globalLcNestedTailData n
          (step1GlobalProductPoly (paramStream θ') p.probe.1 p.iota n)).isOpen_zeroFreeRegion
            j).mem_nhds hτprefixD)
    have hcontC :
        ContinuousAt
          (fun z : ℂ =>
            (((globalLcNestedTailData n
              (step1GlobalProductPoly (paramStream θ') p.probe.1 p.iota n)).threshold j
              (gatePrefix p.concretePrimedStratification j z) : ℝ) : ℂ)) τ :=
      Complex.continuous_ofReal.continuousAt.comp (hthreshold_contD.comp hprefix)
    simpa [FixedOStarProbe.globalProductTierSystem,
      PolynomialNestedTailData.threshold] using
      (PuncturedBoundedAt.of_continuousAt hcontC)
  levelSetLead_frequently := by
    intro j τ hj hτ hOmega hH
    have hpole : ∃ᶠ z in puncturedNhds τ,
        z ∈ p.concretePrimedStratification.omega (j + 1)
          ∧ p.concretePrimedStratification.H (j + 1) z ∈ oddPiI :=
      ((hpolePreimage hj hτ hH).and_eventually hOmega).mono fun z hz => ⟨hz.2, hz.1⟩
    exact fixedOStar_globalProduct_levelSetLead_of_poleHit hStanding p hn hj hτ hpole

/-- **Claim B for the global-product tier chain (`T0 j ⊆ acc (T0 (j+1))`), reduced to the
single pole-preimage leaf.**  This is the corrected TeX Claim-B target on the genuine nested
regions `N_j`, with the lead-avoidance discharged by the algebraic bridge. -/
theorem fixedOStar_globalProduct_zeroFreeTierPropagation_of_poleHit
    {L d r : Nat} {O : Set (ProbePair d)} {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ') {n : Nat} (hn : n + 2 = L)
    (hpolePreimage :
      ∀ {j : Nat} {τ : ℂ}, j + 1 < L → τ ∈ (p.globalProductTierSystem n).T0 j →
        BlowsUpAt (p.concretePrimedStratification.H (j + 1)) τ →
        ∃ᶠ z in puncturedNhds τ, p.concretePrimedStratification.H (j + 1) z ∈ oddPiI) :
    ZeroFreeTierPropagation (p.globalProductTierSystem n) :=
  (fixedOStar_globalProduct_zeroFreeDecoupledPropagationData_of_poleHit
    hStanding p hn hpolePreimage).toZeroFreeTierPropagation

/-! ## The pole-preimage leaf, discharged on `A_gp` from `O_star` genericity

This closes the single remaining Step-1 analytic leaf (`STEP_1_PLAN.md` item 2).  The
genericity pole-preimage chain is in fact only *stratification-deep*: the scaled-quadratic
reciprocal normal form of `H'_{j+1}` at a tier point consumes the tier hypothesis solely
through three facts about the **formal-phi** presentation —

* the gate prefix lies in the regular domain `omega j` (analytic coefficient paths);
* `τ ≠ 0` (TeX Claim B, `lem:T4` needs the pole at a nonzero point);
* the formal-phi propagation lead `f_{j+1}(s'_{<j}(τ)) ≠ 0` (TeX Claim B point (ii)).

All three hold at a zero-free tier point of the **global-product** tier system `A_gp`,
whose stratification and formal-phi presentation are shared with `concretePrimedTierSystem`:
the stratum membership and `τ ≠ 0` come from the shared stratification (`T0_mem_stratum`,
`T0_ne_zero`), and the formal-phi lead is the algebraic bridge
`fixedOStar_formalPhiLead_ne_of_mem_globalProductTierSystem_T0` (`lem:nested`, proved on the
genuine nested regions `N_j`).  Feeding these through the weakened normal form and TeX
`lem:T4` (`frequently_mem_oddPiI_of_analyticAt_eventually_reciprocal`) yields the frequent
sigmoid-pole preimages — with no boundary/no-pole hypothesis. -/

/-- **The pole-preimage leaf at every `A_gp` tier point, from `O_star` genericity.**
For a zero-free tier point of the global-product tier system, the successor preactivation
`H'_{j+1}` has frequently-many preimages of the sigmoid pole set `oddPiI` on every punctured
neighborhood.  (Blow-up of `H'_{j+1}` is not needed: it is reconstructed inside the
reciprocal normal form, so the conclusion holds for *every* such tier point.) -/
theorem fixedOStar_globalProduct_regularPolePreimage_of_OStar_genericity
    {L d r : Nat} {O : Set (ProbePair d)} {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ') {n : Nat} (hn : n + 2 = L)
    {j : Nat} {τ : ℂ} (hj : j + 1 < L)
    (hτ : τ ∈ (p.globalProductTierSystem n).T0 j) :
    ∃ᶠ z in puncturedNhds τ,
      p.concretePrimedStratification.H (j + 1) z ∈ oddPiI := by
  have hfam :
      Step1PolynomialFamilyAssumptions (n + 1) d (paramStream θ') p.probe.1 p.iota := by
    rw [show n + 1 = L - 1 by omega]
    exact p.step1PolynomialFamilyAssumptionsForDepth hStanding.depth_pos
  -- The three formal-phi facts at the global-product tier point.
  have hτS :
      τ ∈ (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ')
        p.probe p.iota).stratification.S j :=
    (p.globalProductTierSystem n).T0_mem_stratum hτ
  have hτ0 : τ ≠ 0 := (p.globalProductTierSystem n).T0_ne_zero (by omega) hτ
  have hlead0 :
      ((fixedOStarProbeCoordTierSystem (r := r) (θ' := θ')
          p.probe p.iota).nestedFamily.step j).lead
        (gatePrefix (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ')
          p.probe p.iota).stratification j τ) ≠ 0 :=
    fixedOStar_formalPhiLead_ne_of_mem_globalProductTierSystem_T0 hStanding p hfam
      (by omega) (by omega) hτ
  have hτω :
      τ ∈ (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ')
        p.probe p.iota).stratification.omega j :=
    (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ')
      p.probe p.iota).stratification.mem_omega_of_mem_stratum (by omega) hτS
  -- The scaled-quadratic reciprocal normal form of `H'_{j+1}` (formal-phi presentation).
  have hH_scaled :
      (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ') p.probe p.iota).stratification.H
          (j + 1)
        =ᶠ[puncturedNhds τ]
          scaledTierPhiPath
            (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ') p.probe p.iota) j :=
    fixedOStarProbeCoordTierSystem_H_eventuallyEq_scaledTierPhiPath p.probe p.iota j τ
  have hdegree :
      ((fixedOStarProbeCoordTierSystem (r := r) (θ' := θ')
        p.probe p.iota).nestedFamily.step j).degree = 2 :=
    fixedOStarProbeCoordTierSystem_step_degree_eq_two_of_OStar
      (r := r) p.mem_O_star p.visible_iota_ne hj
  have hcoeff :=
    fixedOStarProbeCoordTierSystem_coeffPaths_analyticAt
      (r := r) (θ' := θ') p.probe p.iota hτω
  rcases fixedOStarProbeCoord_H_localReciprocalNormalForm_of_scaled_quadratic
      (r := r) (θ' := θ') p.probe p.iota hj hτS hτ0 hlead0 hH_scaled hdegree
      hcoeff.1 hcoeff.2 with
    ⟨R, hR, hRτ, hRnonconst, hrecip⟩
  have hfreq :
      ∃ᶠ z in puncturedNhds τ,
        (fixedOStarProbeCoordTierSystem (r := r) (θ' := θ')
          p.probe p.iota).stratification.H (j + 1) z ∈ oddPiI :=
    frequently_mem_oddPiI_of_analyticAt_eventually_reciprocal hR hRτ hRnonconst hrecip
  exact hfreq

/-- **Claim B for the global-product tier chain, unconditionally from `O_star`
genericity.**  Closes `T0 j ⊆ acc (T0 (j+1))` for `A_gp` with the single pole-preimage leaf
discharged by `fixedOStar_globalProduct_regularPolePreimage_of_OStar_genericity`; the
lead-avoidance wall was already removed by the algebraic bridge.  No graph / no-pole
hypothesis. -/
theorem fixedOStar_globalProduct_zeroFreeTierPropagation_of_OStar_genericity
    {L d r : Nat} {O : Set (ProbePair d)} {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ') {n : Nat} (hn : n + 2 = L) :
    ZeroFreeTierPropagation (p.globalProductTierSystem n) :=
  fixedOStar_globalProduct_zeroFreeTierPropagation_of_poleHit hStanding p hn
    (fun hj hτ _hH =>
      fixedOStar_globalProduct_regularPolePreimage_of_OStar_genericity
        hStanding p hn hj hτ)

/-! ## A_gp Claim C and the standalone first-attention identification

With `A_gp` Claim B unconditional, the descent to `A₁ = A₁'` is now assembled on the
global-product tier system, **bypassing the formal-phi exterior-region wall entirely**.
The two genuinely new analytic inputs are the last-tier *visible*-coefficient nonvanishing
(Claim C, the `g`/`none`-factor analogue of the propagation-lead bridge) and the level-0
lead; everything else is the generic descent infrastructure
(`ZeroFreeConcreteDescentData`, transfer, `first_slope_eq_of_tier_descent`) instantiated at
`p.globalProductTierSystem n` (shared stratification with `concretePrimedTierSystem`). -/

/-- **A_gp Claim C core.**  The visible last-layer coefficient `g` is nonzero at every
last-tier point of the global-product tier system: the visible coefficient is the
evaluation of `step1VisiblePoly` at the gate prefix (a stratification-level identity), and
the prefix of a last-tier point lies in the genuine nested region `N_{L-1}`, on which the
visible factor (`none`) is nonzero by `lem:nested` (`globalLcTower_factor_eval_ne_on_region`
at the top level). -/
theorem fixedOStar_globalProduct_lastTierVisibleCoeff_ne_zero
    {L d r : Nat} {O : Set (ProbePair d)} {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ') {n : Nat} (hn : n + 2 = L)
    {τ : ℂ} (hL : 0 < L)
    (hτ : τ ∈ (p.globalProductTierSystem n).T (L - 1)) :
    (p.globalProductTierSystem n).stratification.lastLayer.coeff (L - 1) τ ≠ 0 := by
  subst hn
  have hfam :
      Step1PolynomialFamilyAssumptions (n + 1) d (paramStream θ') p.probe.1 p.iota :=
    p.step1PolynomialFamilyAssumptionsForDepth hStanding.depth_pos
  show p.concretePrimedTierSystem.stratification.lastLayer.coeff (n + 2 - 1) τ ≠ 0
  rw [fixedOStar_lastLayer_visibleCoeff_eq_step1VisiblePoly p hL τ]
  have hregion :
      gatePrefix p.concretePrimedStratification (n + 2 - 1) τ ∈
        (globalLcNestedTailData n
          (step1GlobalProductPoly (paramStream θ') p.probe.1 p.iota n)).region (n + 1) := by
    simpa [FixedOStarProbe.globalProductTierSystem, PolynomialNestedTailData.region,
      Nat.add_sub_cancel] using (p.globalProductTierSystem n).mem_region hτ
  have hP_univ : HasDominantTopCoeff
      (∏ a ∈ (Finset.univ : Finset (Step1PolynomialIndex (n + 1))),
        step1PolynomialFamilyPoly (K := n + 1) (paramStream θ') p.probe.1 p.iota a) := by
    simpa [step1GlobalProductPoly] using hasDominantTopCoeff_step1GlobalProductPoly hfam
  have hregion_univ :
      gatePrefix p.concretePrimedStratification (n + 2 - 1) τ ∈
        (globalLcNestedTailData n
          (∏ a ∈ (Finset.univ : Finset (Step1PolynomialIndex (n + 1))),
            step1PolynomialFamilyPoly (K := n + 1) (paramStream θ') p.probe.1 p.iota a)).region
          (n + 1) := by
    simpa [step1GlobalProductPoly] using hregion
  have hfactor :=
    globalLcTower_factor_eval_ne_on_region n Finset.univ
      (step1PolynomialFamilyPoly (K := n + 1) (paramStream θ') p.probe.1 p.iota)
      hP_univ hregion_univ (a := none) (Finset.mem_univ _)
  rw [globalLcTower_self] at hfactor
  simpa [step1PolynomialFamilyPoly, Nat.add_sub_cancel] using hfactor

/-- **A_gp descent base.**  The global-product nested family's level-0 leading coefficient
is a nonzero constant (`lem:nested` base case: `N_0` is a point), hence nonzero at every
first-stratum gate prefix. -/
theorem fixedOStar_globalProduct_step0_lead_ne_zero
    {L d r : Nat} {O : Set (ProbePair d)} {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ') {n : Nat} (hn : n + 2 = L) :
    ∀ τ ∈ (p.globalProductTierSystem n).stratification.S 0,
      ((p.globalProductTierSystem n).nestedFamily.step 0).lead
        (gatePrefix (p.globalProductTierSystem n).stratification 0 τ) ≠ 0 := by
  intro τ _hτS
  have hfam : Step1PolynomialFamilyAssumptions (n + 1) d (paramStream θ') p.probe.1 p.iota := by
    rw [show n + 1 = L - 1 by omega]
    exact p.step1PolynomialFamilyAssumptionsForDepth hStanding.depth_pos
  have hP : HasDominantTopCoeff (step1GlobalProductPoly (paramStream θ') p.probe.1 p.iota n) :=
    hasDominantTopCoeff_step1GlobalProductPoly hfam
  set P := step1GlobalProductPoly (paramStream θ') p.probe.1 p.iota n with hPdef
  have hmem :
      gatePrefix (p.globalProductTierSystem n).stratification 0 τ ∈
        (globalLcNestedTailData n P).region 0 := by
    simp [PolynomialNestedTailData.region]
  have hne :=
    globalLcTower_leadingCoeff_ne_on_region n hP 0 _ hmem
  simpa [FixedOStarProbe.globalProductTierSystem,
    TierSystem.ofPolynomialNestedTailData_nestedFamily,
    PolynomialNestedTailData.toNestedTailFamily_step] using hne

/-- Continuity of the visible last-layer coefficient at global-product last-tier points
(stratification-level; clone of the `concretePrimedTierSystem` version). -/
theorem fixedOStar_globalProduct_lastLayer_visibleCoeff_continuousAt_of_mem
    {L d r : Nat} {O : Set (ProbePair d)} {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ') {n : Nat} :
    ∀ {τ : ℂ}, 0 < L → τ ∈ (p.globalProductTierSystem n).T (L - 1) →
      ContinuousAt
        ((p.globalProductTierSystem n).stratification.lastLayer.coeff (L - 1)) τ := by
  intro τ hL hτ
  cases L with
  | zero =>
      omega
  | succ m =>
      let A := p.globalProductTierSystem n
      have hlast : (m + 1) - 1 < m + 1 := by omega
      have hregularLast : τ ∉ partialUnion A.stratification.S ((m + 1) - 1) := by
        have hω : τ ∈ A.stratification.omega ((m + 1) - 1) :=
          A.mem_omega hlast hτ
        simpa [ConcreteStratification.omega] using hω
      have hcont :=
        constantProbeObservableExpansion_lastCoeff_continuousAt_of_regular
          (paramStream θ') (Real.log (r : ℝ)) p.probe.1 p.probe.2
          m p.iota (τ := τ) (by
            simpa [A, FixedOStarProbe.globalProductTierSystem,
              TierSystem.ofPolynomialNestedTailData_stratification,
              FixedOStarProbe.concretePrimedStratification,
              FixedOStarProbe.concretePrimedData,
              ConstantProbeConcreteData.toConcreteStratification,
              ConcreteStratificationData.toConcreteStratification,
              ConstantProbeConcreteData.toConcreteStratificationData] using hregularLast)
      simpa [A, FixedOStarProbe.globalProductTierSystem,
        TierSystem.ofPolynomialNestedTailData_stratification,
        FixedOStarProbe.concretePrimedStratification,
        FixedOStarProbe.concretePrimedData,
        ConstantProbeConcreteData.toConcreteStratification,
        ConcreteStratificationData.toConcreteStratification,
        ConstantProbeConcreteData.toConcreteStratificationData] using hcont

/-- Continuity of the lower last-layer coefficients at global-product last-tier points
(stratification-level; clone of the `concretePrimedTierSystem` version). -/
theorem fixedOStar_globalProduct_lastLayer_lowerCoeff_continuousAt_of_mem
    {L d r : Nat} {O : Set (ProbePair d)} {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ') {n : Nat} :
    ∀ {τ : ℂ}, 0 < L → τ ∈ (p.globalProductTierSystem n).T (L - 1) →
      ∀ i, i < L - 1 →
        ContinuousAt
          ((p.globalProductTierSystem n).stratification.lastLayer.coeff i) τ := by
  intro τ hL hτ i hi
  cases L with
  | zero =>
      omega
  | succ m =>
      let A := p.globalProductTierSystem n
      have hlast : (m + 1) - 1 < m + 1 := by omega
      have hregularLast : τ ∉ partialUnion A.stratification.S ((m + 1) - 1) := by
        have hω : τ ∈ A.stratification.omega ((m + 1) - 1) :=
          A.mem_omega hlast hτ
        simpa [ConcreteStratification.omega] using hω
      have hregular_i :
          τ ∉ partialUnion A.stratification.S (i + 1) := by
        intro hmem
        exact hregularLast
          ((partialUnion_mono_right (S := A.stratification.S) (by omega)) hmem)
      have hcont :=
        constantProbeObservableExpansion_coeff_continuousAt_of_regular
          (paramStream θ') (Real.log (r : ℝ)) p.probe.1 p.probe.2
          (m + 1) i p.iota τ (by omega) (by
            simpa [A, FixedOStarProbe.globalProductTierSystem,
              TierSystem.ofPolynomialNestedTailData_stratification,
              FixedOStarProbe.concretePrimedStratification,
              FixedOStarProbe.concretePrimedData,
              ConstantProbeConcreteData.toConcreteStratification,
              ConcreteStratificationData.toConcreteStratification,
              ConstantProbeConcreteData.toConcreteStratificationData] using hregular_i)
      simpa [A, FixedOStarProbe.globalProductTierSystem,
        TierSystem.ofPolynomialNestedTailData_stratification,
        FixedOStarProbe.concretePrimedStratification,
        FixedOStarProbe.concretePrimedData,
        ConstantProbeConcreteData.toConcreteStratification,
        ConcreteStratificationData.toConcreteStratification,
        ConstantProbeConcreteData.toConcreteStratificationData] using hcont

/-- **A_gp Claim C data.**  Assemble `LastTierConcreteData` for the global-product tier
system from the visible-coefficient nonvanishing and the (shared) stratification
continuity. -/
noncomputable def fixedOStar_globalProduct_lastTierConcreteData
    {L d r : Nat} {O : Set (ProbePair d)} {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ') {n : Nat} (hn : n + 2 = L) :
    LastTierConcreteData (p.globalProductTierSystem n) :=
  LastTierConcreteData.of_continuousAt
    (LastTierVisibleCoeffData.of_continuousAt
      (fun hm hτ => fixedOStar_globalProduct_lastLayer_visibleCoeff_continuousAt_of_mem p hm hτ)
      (fun hm hτ => fixedOStar_globalProduct_lastTierVisibleCoeff_ne_zero hStanding p hn hm hτ))
    (fun hm hτ _i hi => lastTierLowerGate_continuousAt_of_mem (p.globalProductTierSystem n) hm hτ hi)
    (fun hm hτ i hi => fixedOStar_globalProduct_lastLayer_lowerCoeff_continuousAt_of_mem p hm hτ i hi)

/-- **A_gp Claim C + Claim D (transfer).**  The global-product last zero-free tier lands in
the unprimed partial singular union (`first_slope_eq_of_tier_descent`'s `lastSubset`
input). -/
theorem fixedOStar_globalProduct_zeroFreeLastTier_subset_partialUnion
    {L d r : Nat} {O : Set (ProbePair d)} {θ θ' : Params L d}
    (hr : 2 ≤ r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ') {n : Nat} (hn : n + 2 = L) :
    (p.globalProductTierSystem n).T0 (L - 1) ⊆
      partialUnion p.concreteUnprimedStratification.S L := by
  exact transferred_zeroFreeLastTier_subset_partialUnion_ofConcreteDataOnRealTail
    (unprimed := p.concreteUnprimedStratification) (A := p.globalProductTierSystem n)
    hStanding.depth_pos (max p.T0 0)
    (p.realTailObservableAgreement_concrete (by omega : (0:ℕ) < r))
    (fixedOStar_globalProduct_lastTierConcreteData hStanding p hn)

/-- **A_gp Step 4 (unprimed slope nonzero).**  The corrected global-product chain puts a
nonempty primed first tier inside the unprimed first stratum, so the unprimed first slope
cannot vanish (else that stratum is empty).  Global-product analogue of
`fixedOStar_unprimed_firstSlope_ne_of_zeroFreeBridge`. -/
theorem fixedOStar_globalProduct_unprimed_firstSlope_ne
    {L d r : Nat} {O : Set (ProbePair d)} {θ θ' : Params L d}
    (hr : 2 ≤ r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ') {n : Nat} (hn : n + 2 = L) :
    firstSlope θ p.probe.1 p.probe.2 ≠ 0 := by
  let unprimed := p.concreteUnprimedStratification
  let primed := p.globalProductTierSystem n
  have hLast : primed.T0 (L - 1) ⊆ partialUnion unprimed.S L :=
    fixedOStar_globalProduct_zeroFreeLastTier_subset_partialUnion hr hStanding p hn
  have hT0S0 : primed.T0 0 ⊆ unprimed.S 0 := by
    simpa [unprimed, primed] using
      tier_descent_to_first_set
        (S := unprimed.S) (T := primed.T0) (m := L)
        hStanding.depth_pos unprimed.strataSystem
        (fixedOStar_globalProduct_zeroFreeTierPropagation_of_OStar_genericity
          hStanding p hn).chain hLast
  have hprimedSlope :
      primed.stratification.lambda1 ≠ 0 := by
    rw [show primed.stratification.lambda1 =
        firstSlope θ' p.probe.1 p.probe.2 by
      simpa [primed] using p.concretePrimedStratification_lambda1_eq_firstSlope]
    exact p.primed_firstSlope_ne
  have hfirstSubset :
      firstPoleSet unprimed.b primed.stratification.lambda1 ⊆ primed.T0 0 := by
    intro τ hτ
    have hτT : τ ∈ primed.T 0 := by
      exact firstPoleSet_subset_tier_zero_of_tierSystem
        (A := primed) (b := unprimed.b)
        (by simp [unprimed, primed, FixedOStarProbe.globalProductTierSystem,
          TierSystem.ofPolynomialNestedTailData_stratification])
        hprimedSlope hτ
    have hτS : τ ∈ primed.stratification.S 0 := by
      simpa [primed] using hτT
    rw [primed.T0_zero_eq_stratum_of_lead_ne]
    · exact hτS
    · exact fixedOStar_globalProduct_step0_lead_ne_zero hStanding p hn
  have hT0_nonempty : (primed.T0 0).Nonempty := by
    rcases firstPoleSet_nonempty unprimed.b primed.stratification.lambda1 with ⟨τ, hτ⟩
    exact ⟨τ, hfirstSubset hτ⟩
  intro hzero
  rcases hT0_nonempty with ⟨τ, hτ⟩
  have hτS : τ ∈ unprimed.S 0 := hT0S0 hτ
  have hunprimedLambda_zero : unprimed.lambda1 = 0 := by
    rw [show unprimed.lambda1 = firstSlope θ p.probe.1 p.probe.2 by
      simpa [unprimed] using p.concreteUnprimedStratification_lambda1_eq_firstSlope]
    exact hzero
  exact unprimed.notMem_first_stratum_of_lambda_eq_zero hunprimedLambda_zero τ hτS

/-- **A_gp zero-free concrete descent existence.**  Package the corrected global-product
chain, last-tier transfer, level-0 lead, and slope facts into the descent data consumed by
`first_slope_eq_of_tier_descent`. -/
theorem fixedOStar_globalProduct_zeroFreeConcreteDescent_exists
    {L d r : Nat} {O : Set (ProbePair d)} {θ θ' : Params L d}
    (hr : 2 ≤ r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ') {n : Nat} (hn : n + 2 = L) :
    ∃ m : Nat, ∃ D : ZeroFreeConcreteDescentData m,
      D.unprimed.lambda1 = firstSlope θ p.probe.1 p.probe.2 ∧
        D.primed.stratification.lambda1 = firstSlope θ' p.probe.1 p.probe.2 := by
  refine ⟨L, ZeroFreeConcreteDescentData.ofOStarProbeChainAndLastSubset p
    p.concreteUnprimedStratification (p.globalProductTierSystem n) hStanding.depth_pos
    (by simpa using log_nat_ne_zero_of_two_le hr)
    p.concreteUnprimedStratification_lambda1_eq_firstSlope
    p.concretePrimedStratification_lambda1_eq_firstSlope
    (fixedOStar_globalProduct_unprimed_firstSlope_ne hr hStanding p hn)
    (by simp [FixedOStarProbe.globalProductTierSystem,
      TierSystem.ofPolynomialNestedTailData_stratification])
    (fixedOStar_globalProduct_step0_lead_ne_zero hStanding p hn)
    (fixedOStar_globalProduct_zeroFreeTierPropagation_of_OStar_genericity hStanding p hn).chain
    (fixedOStar_globalProduct_zeroFreeLastTier_subset_partialUnion hr hStanding p hn),
    ?_, ?_⟩
  · simpa [ZeroFreeConcreteDescentData.ofOStarProbeChainAndLastSubset] using
      p.concreteUnprimedStratification_lambda1_eq_firstSlope
  · simpa [ZeroFreeConcreteDescentData.ofOStarProbeChainAndLastSubset] using
      p.concretePrimedStratification_lambda1_eq_firstSlope

/-- **Standalone Step 1 conclusion via `A_gp` (`A₁ = A₁'`), unconditionally from `O_star`
genericity, for depth `L = n + 2 ≥ 2`.**

This is the corrected-route capstone: the first attention matrices agree, with the
lead-avoidance wall removed by the global-product tier system.  Every analytic leaf is
discharged — Claim B (`fixedOStar_globalProduct_zeroFreeTierPropagation_of_OStar_genericity`),
Claim C (`fixedOStar_globalProduct_lastTierVisibleCoeff_ne_zero`), transfer, and descent —
with no graph/no-pole hypothesis. -/
theorem fixedOStar_globalProduct_step1Conclusion_of_OStar_genericity
    {L d r : Nat} {O : Set (ProbePair d)} {θ θ' : Params L d}
    (hr : 2 ≤ r)
    (hStanding : Step1StandingAssumptions r L d O θ θ') {n : Nat} (hn : n + 2 = L) :
    Step1Conclusion θ θ' := by
  exact step1Conclusion_of_standingAssumptions_openOStar_fixed_zeroFree_concrete_descent hStanding
    (fun p => fixedOStar_globalProduct_zeroFreeConcreteDescent_exists hr hStanding p hn)

/-! ## A_gp depth certificate (`V₁ ≠ 0`), unconditionally from `O_star` genericity

The standalone capstone `fixedOStar_globalProduct_step1Conclusion_of_OStar_genericity`
yields `A₁ = A₁'` with no claimB/claimC.  To produce the full `FirstLayerEndpointData`
we also need `V₁ ≠ 0` (TeX Corollary `depth`).  The depth certificate is the same
argument as the formal-phi route (`firstLayerValueDepthDropData_of_tex`), but every
analytic leaf is taken on the **global-product** tier system, whose stratification is
shared with `concretePrimedTierSystem` (`= p.concretePrimedStratification` by `rfl`).
The three depth-drop leaves come from the already-proved A_gp Claim B / Claim C bundle:
first-tier nonemptiness (level-0 lead), the propagation chain, and — the one genuinely
new piece below — the `headValue = 0` last-tier transfer into the unprimed tail
stratification. -/

/-- **A_gp first zero-free tier nonempty.**  Global-product analogue of
`fixedOStar_first_zeroFreeTier_nonempty`: the level-0 lead is nonzero on the first
stratum (`fixedOStar_globalProduct_step0_lead_ne_zero`), so `firstPoleSet` of the (nonzero)
primed first slope sits inside `T0 0`, which is therefore nonempty. -/
theorem fixedOStar_globalProduct_first_zeroFreeTier_nonempty
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (p : FixedOStarProbe r L d O θ θ') {n : Nat} (hn : n + 2 = L) :
    ((p.globalProductTierSystem n).T0 0).Nonempty := by
  let A := p.globalProductTierSystem n
  have hprimedSlope : A.stratification.lambda1 ≠ 0 := by
    rw [show A.stratification.lambda1 =
        firstSlope θ' p.probe.1 p.probe.2 by
      simpa [A, FixedOStarProbe.globalProductTierSystem,
        TierSystem.ofPolynomialNestedTailData_stratification] using
        p.concretePrimedStratification_lambda1_eq_firstSlope]
    exact p.primed_firstSlope_ne
  have hfirstSubset :
      firstPoleSet A.stratification.b A.stratification.lambda1 ⊆ A.T0 0 := by
    intro τ hτ
    have hτT : τ ∈ A.T 0 := by
      exact firstPoleSet_subset_tier_zero_of_tierSystem
        (A := A) (b := A.stratification.b) rfl hprimedSlope hτ
    have hτS : τ ∈ A.stratification.S 0 := by
      simpa [A] using hτT
    rw [A.T0_zero_eq_stratum_of_lead_ne]
    · exact hτS
    · exact fixedOStar_globalProduct_step0_lead_ne_zero hStanding p hn
  rcases firstPoleSet_nonempty A.stratification.b A.stratification.lambda1 with ⟨τ, hτ⟩
  exact ⟨τ, hfirstSubset hτ⟩

/-- **A_gp depth-drop transfer (`headValue = 0` branch).**  Global-product analogue of
`fixedOStar_zeroFreeLastTier_subset_tail_partialUnion_of_headValue_zero`.  When the
unprimed first value vanishes, the global-product last zero-free tier transfers into the
singular union of the unprimed tail stratification.  The blow-up of a visible observable
coordinate near each last-tier point is supplied by the A_gp Claim C
`LastTierConcreteData` (`fixedOStar_globalProduct_lastTierConcreteData`), exactly as the
formal-phi version uses its `LastTierConcreteData`.  The stratification is shared with
`concretePrimedTierSystem` (`= p.concretePrimedStratification` by `rfl`), so the tail
agreement, regularity, and isolation inputs are verbatim. -/
theorem fixedOStar_globalProduct_zeroFreeLastTier_subset_tail_partialUnion_of_headValue_zero
    {m d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params (m + 1) d}
    (hr : 0 < r)
    (p : FixedOStarProbe r (m + 1) d O θ θ')
    (firstValue_zero : (θ 0).1 = 0)
    {n : Nat} (hn : n + 2 = m + 1)
    (lastTier : LastTierConcreteData (p.globalProductTierSystem n)) :
    (p.globalProductTierSystem n).T0 m ⊆
      partialUnion
        (ConstantProbeConcreteData.toConcreteStratification
          (ConstantProbeConcreteData.ofConcrete
            (paramStream (Params.tail θ)) (Real.log (r : ℝ))
            p.probe.1 p.probe.2 m p.iota)).S m := by
  let tailData : ConstantProbeConcreteData
      (paramStream (Params.tail θ)) (Real.log (r : ℝ))
      p.probe.1 p.probe.2 m p.iota :=
    ConstantProbeConcreteData.ofConcrete
      (paramStream (Params.tail θ)) (Real.log (r : ℝ))
      p.probe.1 p.probe.2 m p.iota
  let tailStrat := tailData.toConcreteStratification
  let A := p.globalProductTierSystem n
  have hEqOnTail :
      ∀ t : ℝ, max p.T0 0 < t ->
        tailStrat.observable (t : ℂ) =
          A.stratification.observable (t : ℂ) := by
    intro t ht
    have htailFull :
        tailStrat.observable (t : ℂ) =
          p.concreteUnprimedStratification.observable (t : ℂ) := by
      simpa [tailStrat, tailData, FixedOStarProbe.concreteUnprimedStratification,
        FixedOStarProbe.concreteUnprimedData,
        ConstantProbeConcreteData.toConcreteStratification,
        ConstantProbeConcreteData.toConcreteStratificationData] using
        (constantProbeObservable_paramStream_tail_eq_of_headValue_zero
          r θ p.probe.1 p.probe.2 p.iota t firstValue_zero).symm
    calc
      tailStrat.observable (t : ℂ) =
          p.concreteUnprimedStratification.observable (t : ℂ) := htailFull
      _ = p.concretePrimedStratification.observable (t : ℂ) :=
          p.realTailObservableAgreement_concrete hr t ht
      _ = A.stratification.observable (t : ℂ) := by
          simp [A, FixedOStarProbe.globalProductTierSystem,
            TierSystem.ofPolynomialNestedTailData]
  have hblow : ∀ τ, τ ∈ A.T0 ((m + 1) - 1) ->
      BlowsUpAt A.stratification.observable τ := by
    intro τ hτ
    exact (lastTier.toZeroFreeLastTierBlowup (Nat.succ_pos m)).observable_blowsUpAt hτ
  have hfreq :
      ∃ᶠ z in nhdsWithin ((max p.T0 0 + 1 : ℝ) : ℂ)
        ({((max p.T0 0 + 1 : ℝ) : ℂ)}ᶜ : Set ℂ),
        tailStrat.observable z = A.stratification.observable z :=
    frequently_equal_of_eqOn_real_tail (by linarith) hEqOnTail
  have hreg :
      ((max p.T0 0 + 1 : ℝ) : ℂ) ∈
        (tailStrat.singularSet ∪ A.stratification.singularSet)ᶜ := by
    rw [Set.mem_compl_iff, Set.mem_union]
    exact not_or.mpr
      ⟨tailStrat.singularSet_avoids_real (max p.T0 0 + 1),
        A.stratification.singularSet_avoids_real (max p.T0 0 + 1)⟩
  have hsing :
      A.T0 ((m + 1) - 1) ⊆ tailStrat.singularSet := by
    exact transferred_tier_subset
      (E_F := tailStrat.singularSet)
      (E_G := A.stratification.singularSet)
      (T := A.T0 ((m + 1) - 1))
      (F := tailStrat.observable)
      (G := A.stratification.observable)
      (z0 := ((max p.T0 0 + 1 : ℝ) : ℂ))
      tailStrat.singularSet_closed
      tailStrat.singularSet_countable
      A.stratification.singularSet_countable
      tailStrat.observable_analyticOn_singularCompl
      A.stratification.observable_analyticOn_singularCompl
      hreg
      hfreq
      (fun τ hτ => tailStrat.observable_continuousAt_of_regular hτ)
      (by
        intro τ hτ0
        have hτ : τ ∈ A.T ((m + 1) - 1) :=
          A.T0_subset_T ((m + 1) - 1) hτ0
        have hlt : (m + 1) - 1 < m + 1 := by omega
        have hIso :
            IsPuncturedIsolated
              (partialUnion A.stratification.S (((m + 1) - 1) + 1)) τ :=
          A.punctured_isolated_partialUnion_succ
            (j := (m + 1) - 1) hlt hτ
        have hlast : ((m + 1) - 1) + 1 = m + 1 := by omega
        simpa [ConcreteStratification.singularSet, hlast] using hIso)
      hblow
  have hpartial :
      A.T0 ((m + 1) - 1) ⊆ partialUnion tailStrat.S m := by
    simpa [ConcreteStratification.singularSet] using hsing
  simpa [A, tailStrat, tailData] using hpartial

/-- **A_gp depth-drop data.**  Global-product analogue of
`firstLayerValueDepthDropData_of_tex`, assuming `V₁ = 0`: the global-product tier chain
puts a nonempty first tier inside `accIter (L - 1)` of an `(L - 1)`-stratum union,
contradicting `strataacc`.  Built unconditionally from `O_star` genericity (no
claimB/claimC) for depth `L = n + 2`. -/
noncomputable def fixedOStar_globalProduct_firstLayerValueDepthDropData_of_OStar_genericity
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    {n : Nat} (hn : n + 2 = L)
    (step1_eq : Step1Conclusion θ θ')
    (firstValue_zero : (θ ⟨0, hStanding.depth_pos⟩).1 = 0) :
    FirstLayerValueDepthDropData hStanding step1_eq firstValue_zero := by
  subst hn
  let hOStar : (O_star θ' O).Nonempty :=
    O_star_nonempty_of_generic hStanding.generic
  let probe : ProbePair d := Classical.choose hOStar
  have hprobe : probe ∈ O_star θ' O := Classical.choose_spec hOStar
  let p : FixedOStarProbe r (n + 2) d O θ θ' :=
    FixedOStarProbe.ofLocalAgreement hStanding.agreement hprobe
  let tailData : ConstantProbeConcreteData
      (paramStream (Params.tail θ)) (Real.log (r : ℝ))
      p.probe.1 p.probe.2 (n + 1) p.iota :=
    ConstantProbeConcreteData.ofConcrete
      (paramStream (Params.tail θ)) (Real.log (r : ℝ))
      p.probe.1 p.probe.2 (n + 1) p.iota
  let tailStrat := tailData.toConcreteStratification
  refine
    { droppedStrata := tailStrat.S
      primedTier := (p.globalProductTierSystem n).T0
      dropped_strata := ?_
      firstTier_nonempty := ?_
      chain := ?_
      last_subset := ?_ }
  · simpa [tailStrat] using tailStrat.strataSystem
  · exact fixedOStar_globalProduct_first_zeroFreeTier_nonempty hStanding p rfl
  · intro j hj
    exact (fixedOStar_globalProduct_zeroFreeTierPropagation_of_OStar_genericity
      hStanding p rfl).chain j (by omega)
  · have hV0 : (θ 0).1 = 0 := by
      simpa using firstValue_zero
    have hr_pos : 0 < r := lt_of_lt_of_le (Nat.zero_lt_succ 1) hr
    have hlast :=
      fixedOStar_globalProduct_zeroFreeLastTier_subset_tail_partialUnion_of_headValue_zero
        (m := n + 1) (n := n) hr_pos p hV0 rfl
        (fixedOStar_globalProduct_lastTierConcreteData hStanding p rfl)
    simpa [tailStrat, tailData] using hlast

/-- **No-depth-drop for the unprimed first value matrix via the A_gp route**, for
depth `L = n + 2 ≥ 2`.  Global-product (claimB/claimC-free) analogue of
`firstLayerValueNoDepthDrop_of_tex`. -/
theorem firstLayerValueNoDepthDrop_of_globalProduct
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    {n : Nat} (hn : n + 2 = L) :
    FirstLayerValueNoDepthDrop θ θ' hStanding.depth_pos := by
  intro step1_eq firstValue_zero
  exact (fixedOStar_globalProduct_firstLayerValueDepthDropData_of_OStar_genericity
    hr hStanding hn step1_eq firstValue_zero).false

/-! ## The claimB/claimC-free Step 1 endpoint (via `A_gp`)

`firstLayerEndpoint_of_step1Standing` packages `A₁ = A₁'` plus `V₁ ≠ 0` from
`Step1StandingAssumptions`, but consumes claimB/claimC (which thread into the top-level
acknowledged debt).  The global-product capstone
(`fixedOStar_globalProduct_step1Conclusion_of_OStar_genericity`) and the A_gp depth
certificate (`firstLayerValueNoDepthDrop_of_globalProduct`) discharge both leaves
unconditionally, so the endpoint below needs **only** `Step1StandingAssumptions`. -/

/-- **Step 1 endpoint from local standing assumptions, claimB/claimC-free** (depth
`L + 1 ≥ 2`).  Global-product analogue of `firstLayerEndpoint_of_step1Standing`: the Step 1
conclusion and depth certificate are both discharged from `O_star` genericity via the
`A_gp` tier system, so no `FixedOStarZeroFreeLevelSetLeadData` /
`FixedOStarLastTierVisibleCoeffNonzeroData` arguments are required. -/
theorem firstLayerEndpoint_of_step1Standing_globalProduct
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params (L + 1) d}
    (hr : 2 <= r)
    (hStanding : Step1StandingAssumptions r (L + 1) d O θ θ')
    (hDepth : 0 < L) :
    FirstLayerEndpointData
      (Params.headAttention θ) (Params.headAttention θ')
      (Params.headValue θ) := by
  have hn : (L - 1) + 2 = L + 1 := by omega
  have hStep1Theorem :
      ConcreteStep1TheoremStatement r (L + 1) d O θ θ' :=
    fun hs => fixedOStar_globalProduct_step1Conclusion_of_OStar_genericity hr hs hn
  have hStep1 : Step1Conclusion θ θ' := hStep1Theorem hStanding
  have hAttention : Params.headAttention θ = Params.headAttention θ' := by
    have hθ : firstAttention θ = Params.headAttention θ := by
      simpa [Params.headAttention, Params.headLayer] using
        firstAttention_eq_of_pos θ (Nat.succ_pos L)
    have hθ' : firstAttention θ' = Params.headAttention θ' := by
      simpa [Params.headAttention, Params.headLayer] using
        firstAttention_eq_of_pos θ' (Nat.succ_pos L)
    calc
      Params.headAttention θ = firstAttention θ := hθ.symm
      _ = firstAttention θ' := hStep1
      _ = Params.headAttention θ' := hθ'
  have hNoDepthDrop :
      FirstLayerValueNoDepthDrop θ θ' hStanding.depth_pos :=
    firstLayerValueNoDepthDrop_of_globalProduct hr hStanding hn
  have hHeadValue :
      Params.headValue θ ≠ 0 := by
    have hConcrete :
        (θ ⟨0, hStanding.depth_pos⟩).1 ≠ 0 :=
      firstLayerValue_ne_zero_of_concrete_step1_noDepthDrop
        hStep1Theorem hStanding hNoDepthDrop
    simpa [Params.headValue, Params.headLayer] using hConcrete
  exact FirstLayerEndpointData.of_attention_eq hAttention hHeadValue

/-- **Step 1 endpoint from local path/open-set IDL data, claimB/claimC-free.**
Global-product (`A_gp`) analogue of `firstLayerEndpoint_of_texGenericStep_of_IDLData`.

`TexGenericStepClauses` contributes only the matrix-level `O_star` genericity used in
`hStanding`; every Step 1 analytic leaf (Claim B, Claim C, transfer, descent, and the
depth certificate) is discharged unconditionally by the global-product tier system.  The
depth-one (`L = 0`) branch is identical to the existing endpoint. -/
theorem firstLayerEndpoint_of_texGenericStep_of_IDLData_globalProduct
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (D : IDLData (L + 1) d r θ θ') :
    FirstLayerEndpointData
      (Params.headAttention θ) (Params.headAttention θ')
      (Params.headValue θ) := by
  cases L with
  | zero =>
      have matching : FirstLayerMatchedData θ θ' :=
        IDL_depth_one_matching_of_localTailAgreement hr D
      exact FirstLayerEndpointData.of_attention_eq
        matching.headAttention_eq matching.headValue_ne_zero
  | succ L =>
      have hStanding : Step1StandingAssumptions r (L + 1 + 1) d D.O θ θ' :=
        { depth_pos := Nat.succ_pos (L + 1)
          generic := hstep.toOStarGenericAssumptions D.O_open D.O_nonempty
          agreement := localProbeTailAgreement_of_IDLData D }
      exact firstLayerEndpoint_of_step1Standing_globalProduct hr hStanding (Nat.succ_pos L)

end TransformerIdentifiability.NLayer
