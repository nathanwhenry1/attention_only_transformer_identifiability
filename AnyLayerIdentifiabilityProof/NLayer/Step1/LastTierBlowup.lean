import AnyLayerIdentifiabilityProof.NLayer.Step1.AnalyticSupport
import AnyLayerIdentifiabilityProof.NLayer.Step1.TierSets

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Step 1 last-tier blow-up

Owner shard for Claim C: prove the last generic tier forces blow-up of the selected
observable coordinate.
-/

/-- The lower part of the last-layer observable split, in the `m - 1` indexing used by
Claim C.  At depth zero there is no last tier; the zero branch is only a totality
convenience for statements that carry a separate `0 < m` hypothesis. -/
noncomputable def lastTierLower : {m : Nat} -> TierSystem m -> ℂ -> ℂ
  | 0, _A => fun _ => 0
  | _m + 1, A => A.stratification.lastLayer.lower

/-- Claim-C data for the last tier of a concrete tier system.

The concrete stratification already supplies the last gate blow-up from tier membership.
This package records the transformer-specific obligations still needed for the observable:
boundedness of the lower last-layer contribution and convergence of the visible
coefficient to a nonzero limit. -/
structure LastTierBlowupData {m : Nat} (A : TierSystem m) where
  lower_puncturedBounded :
    ∀ {τ : ℂ}, 0 < m -> τ ∈ A.T (m - 1) ->
      PuncturedBoundedAt (lastTierLower A) τ
  visibleCoeffLimit : ℂ -> ℂ
  visibleCoeff_tendsto :
    ∀ {τ : ℂ}, 0 < m -> τ ∈ A.T (m - 1) ->
      Filter.Tendsto (A.stratification.lastLayer.coeff (m - 1))
        (puncturedNhds τ) (nhds (visibleCoeffLimit τ))
  visibleCoeff_ne_zero :
    ∀ {τ : ℂ}, 0 < m -> τ ∈ A.T (m - 1) ->
      visibleCoeffLimit τ ≠ 0

/-- Packaged Claim C conclusion for downstream transfer. -/
structure LastTierBlowup {m : Nat} (A : TierSystem m) where
  blowsUp :
    ∀ τ : ℂ, τ ∈ A.T (m - 1) ->
      BlowsUpAt A.stratification.observable τ

/-- Zero-free Claim-C data for the last tier.

This is the additive zero-free analogue of `LastTierBlowupData`: all obligations are
only requested on the zero-free last tier `A.T0 (m - 1)`. -/
structure ZeroFreeLastTierBlowupData {m : Nat} (A : TierSystem m) where
  lower_puncturedBounded :
    ∀ {τ : ℂ}, 0 < m -> τ ∈ A.T0 (m - 1) ->
      PuncturedBoundedAt (lastTierLower A) τ
  visibleCoeffLimit : ℂ -> ℂ
  visibleCoeff_tendsto :
    ∀ {τ : ℂ}, 0 < m -> τ ∈ A.T0 (m - 1) ->
      Filter.Tendsto (A.stratification.lastLayer.coeff (m - 1))
        (puncturedNhds τ) (nhds (visibleCoeffLimit τ))
  visibleCoeff_ne_zero :
    ∀ {τ : ℂ}, 0 < m -> τ ∈ A.T0 (m - 1) ->
      visibleCoeffLimit τ ≠ 0

/-- Packaged zero-free Claim C conclusion for downstream transfer. -/
structure ZeroFreeLastTierBlowup {m : Nat} (A : TierSystem m) where
  blowsUp :
    ∀ τ : ℂ, τ ∈ A.T0 (m - 1) ->
      BlowsUpAt A.stratification.observable τ

/-! ## Last-tier constructor obligations -/

/-- Build a concrete tier system from a concrete stratification and a polynomial-backed
nested tail tower.  This is a local constructor for Claim C workers that receive the
generic polynomial package from `NestedLargeness`. -/
def TierSystem.ofPolynomialNestedTailData {m : Nat}
    (P : ConcreteStratification m) (D : PolynomialNestedTailData) : TierSystem m where
  stratification := P
  nestedFamily := D.toNestedTailFamily

@[simp] theorem TierSystem.ofPolynomialNestedTailData_stratification {m : Nat}
    (P : ConcreteStratification m) (D : PolynomialNestedTailData) :
    (TierSystem.ofPolynomialNestedTailData P D).stratification = P :=
  rfl

@[simp] theorem TierSystem.ofPolynomialNestedTailData_nestedFamily {m : Nat}
    (P : ConcreteStratification m) (D : PolynomialNestedTailData) :
    (TierSystem.ofPolynomialNestedTailData P D).nestedFamily = D.toNestedTailFamily :=
  rfl

/-- Lower last-layer contribution boundedness from boundedness of each lower gate and
coefficient. -/
theorem lastTierLower_puncturedBounded_of_lower_terms {m : Nat} {A : TierSystem m}
    (hm : 0 < m) {τ : ℂ}
    (hs :
      ∀ i, i < m - 1 -> PuncturedBoundedAt (A.stratification.s i) τ)
    (hc :
      ∀ i, i < m - 1 ->
        PuncturedBoundedAt (A.stratification.lastLayer.coeff i) τ) :
    PuncturedBoundedAt (lastTierLower A) τ := by
  cases m with
  | zero =>
      omega
  | succ k =>
      have hs' :
          ∀ i, i < k -> PuncturedBoundedAt (A.stratification.s i) τ := by
        intro i hi
        exact hs i (by omega)
      have hc' :
          ∀ i, i < k ->
            PuncturedBoundedAt (A.stratification.lastLayer.coeff i) τ := by
        intro i hi
        exact hc i (by omega)
      simpa [lastTierLower] using
        A.stratification.lower_lastlayer_puncturedBounded
          (m := k) (τ := τ) hs' hc'

/-- Lower gates are continuous at a last-tier point because that point is regular for
every earlier gate. -/
theorem lastTierLowerGate_continuousAt_of_mem {m : Nat} (A : TierSystem m)
    (hm : 0 < m) {τ : ℂ} (hτ : τ ∈ A.T (m - 1)) {i : Nat}
    (hi : i < m - 1) :
    ContinuousAt (A.stratification.s i) τ := by
  have hlast : m - 1 < m := by omega
  have hlast_regular : τ ∉ partialUnion A.stratification.S (m - 1) := by
    have hω := A.mem_omega (j := m - 1) hlast hτ
    simpa [ConcreteStratification.omega] using hω
  have hi_regular : τ ∈ A.stratification.omega (i + 1) := by
    have hnot : τ ∉ partialUnion A.stratification.S (i + 1) := by
      intro hmem
      exact hlast_regular
        ((partialUnion_mono_right (S := A.stratification.S) (by omega)) hmem)
    simpa [ConcreteStratification.omega] using hnot
  exact ((A.stratification.gate_analyticOn (j := i) (by omega)) τ hi_regular).continuousAt

/-- Pointwise Claim-C constructor: lower boundedness plus a nonzero visible-coefficient
limit makes the selected observable blow up at the last tier. -/
theorem observable_blowsUpAt_of_lastTier_obligations {m : Nat} {A : TierSystem m}
    (hm : 0 < m) {τ visible0 : ℂ}
    (hτ : τ ∈ A.T (m - 1))
    (hlower : PuncturedBoundedAt (lastTierLower A) τ)
    (hvisible :
      Filter.Tendsto (A.stratification.lastLayer.coeff (m - 1))
        (puncturedNhds τ) (nhds visible0))
    (hvisible0 : visible0 ≠ 0) :
    BlowsUpAt A.stratification.observable τ := by
  cases m with
  | zero =>
      omega
  | succ k =>
      have hlower' : PuncturedBoundedAt A.stratification.lastLayer.lower τ := by
        simpa [lastTierLower] using hlower
      have hgate : BlowsUpAt (A.stratification.s k) τ := by
        exact A.stratification.gate_blowsUpAt_of_mem_stratum
          (by omega) (A.mem_stratum (by simpa using hτ))
      have hvisible' :
          Filter.Tendsto (A.stratification.lastLayer.coeff k)
            (puncturedNhds τ) (nhds visible0) := by
        simpa using hvisible
      exact A.stratification.observable_blowsUpAt_of_lastlayer
        hlower' hgate hvisible' hvisible0

/-- Pointwise zero-free Claim-C constructor: coerce the zero-free last-tier hypothesis
to the old last-tier API, then reuse the existing pointwise blow-up theorem. -/
theorem observable_blowsUpAt_of_zeroFreeLastTier_obligations {m : Nat} {A : TierSystem m}
    (hm : 0 < m) {τ visible0 : ℂ}
    (hτ0 : τ ∈ A.T0 (m - 1))
    (hlower : PuncturedBoundedAt (lastTierLower A) τ)
    (hvisible :
      Filter.Tendsto (A.stratification.lastLayer.coeff (m - 1))
        (puncturedNhds τ) (nhds visible0))
    (hvisible0 : visible0 ≠ 0) :
    BlowsUpAt A.stratification.observable τ :=
  observable_blowsUpAt_of_lastTier_obligations (A := A) hm
    (A.T0_subset_T (m - 1) hτ0) hlower hvisible hvisible0

/-- Componentwise lower-term boundedness obligations for the last-layer split. -/
structure LastTierLowerTermData {m : Nat} (A : TierSystem m) where
  lowerGate_puncturedBounded :
    ∀ {τ : ℂ}, 0 < m -> τ ∈ A.T (m - 1) ->
      ∀ i, i < m - 1 -> PuncturedBoundedAt (A.stratification.s i) τ
  lowerCoeff_puncturedBounded :
    ∀ {τ : ℂ}, 0 < m -> τ ∈ A.T (m - 1) ->
      ∀ i, i < m - 1 ->
        PuncturedBoundedAt (A.stratification.lastLayer.coeff i) τ

namespace LastTierLowerTermData

variable {m : Nat} {A : TierSystem m}

/-- Build lower-term data from continuity of every lower gate and coefficient at
last-tier points. -/
def of_continuousAt
    (hs :
      ∀ {τ : ℂ}, 0 < m -> τ ∈ A.T (m - 1) ->
        ∀ i, i < m - 1 -> ContinuousAt (A.stratification.s i) τ)
    (hc :
      ∀ {τ : ℂ}, 0 < m -> τ ∈ A.T (m - 1) ->
        ∀ i, i < m - 1 ->
          ContinuousAt (A.stratification.lastLayer.coeff i) τ) :
    LastTierLowerTermData A where
  lowerGate_puncturedBounded := fun hm hτ i hi =>
    PuncturedBoundedAt.of_continuousAt (hs hm hτ i hi)
  lowerCoeff_puncturedBounded := fun hm hτ i hi =>
    PuncturedBoundedAt.of_continuousAt (hc hm hτ i hi)

variable (D : LastTierLowerTermData A)
include D

/-- Compile componentwise lower-term boundedness into the exact lower-field required by
`LastTierBlowupData`. -/
theorem lower_puncturedBounded (hm : 0 < m) {τ : ℂ}
    (hτ : τ ∈ A.T (m - 1)) :
    PuncturedBoundedAt (lastTierLower A) τ :=
  lastTierLower_puncturedBounded_of_lower_terms (A := A) hm
    (D.lowerGate_puncturedBounded hm hτ)
    (D.lowerCoeff_puncturedBounded hm hτ)

end LastTierLowerTermData

/-- Visible-coefficient limit obligations for the final observable term. -/
structure LastTierVisibleCoeffData {m : Nat} (A : TierSystem m) where
  visibleCoeffLimit : ℂ -> ℂ
  visibleCoeff_tendsto :
    ∀ {τ : ℂ}, 0 < m -> τ ∈ A.T (m - 1) ->
      Filter.Tendsto (A.stratification.lastLayer.coeff (m - 1))
        (puncturedNhds τ) (nhds (visibleCoeffLimit τ))
  visibleCoeff_ne_zero :
    ∀ {τ : ℂ}, 0 < m -> τ ∈ A.T (m - 1) ->
      visibleCoeffLimit τ ≠ 0

namespace LastTierVisibleCoeffData

variable {m : Nat} {A : TierSystem m}

/-- Build visible-coefficient data from continuity at last-tier points and pointwise
nonvanishing there. -/
def of_continuousAt
    (hc :
      ∀ {τ : ℂ}, 0 < m -> τ ∈ A.T (m - 1) ->
        ContinuousAt (A.stratification.lastLayer.coeff (m - 1)) τ)
    (hne :
      ∀ {τ : ℂ}, 0 < m -> τ ∈ A.T (m - 1) ->
        A.stratification.lastLayer.coeff (m - 1) τ ≠ 0) :
    LastTierVisibleCoeffData A where
  visibleCoeffLimit := fun τ => A.stratification.lastLayer.coeff (m - 1) τ
  visibleCoeff_tendsto := fun hm hτ =>
    (hc hm hτ).tendsto.mono_left nhdsWithin_le_nhds
  visibleCoeff_ne_zero := fun hm hτ => hne hm hτ

end LastTierVisibleCoeffData

/-- Claim-C constructor obligations split into lower-term boundedness and visible
coefficient nonvanishing. -/
structure LastTierConcreteData {m : Nat} (A : TierSystem m) where
  lowerTerms : LastTierLowerTermData A
  visibleCoeff : LastTierVisibleCoeffData A

namespace LastTierConcreteData

variable {m : Nat} {A : TierSystem m}

/-- Combine lower-term data with visible-coefficient data. -/
def ofData (lowerTerms : LastTierLowerTermData A)
    (visibleCoeff : LastTierVisibleCoeffData A) : LastTierConcreteData A where
  lowerTerms := lowerTerms
  visibleCoeff := visibleCoeff

/-- Build concrete last-tier data from continuous lower terms and direct
visible-coefficient data. -/
def of_continuousAt
    (visibleCoeff : LastTierVisibleCoeffData A)
    (hs :
      ∀ {τ : ℂ}, 0 < m -> τ ∈ A.T (m - 1) ->
        ∀ i, i < m - 1 -> ContinuousAt (A.stratification.s i) τ)
    (hc :
      ∀ {τ : ℂ}, 0 < m -> τ ∈ A.T (m - 1) ->
        ∀ i, i < m - 1 ->
          ContinuousAt (A.stratification.lastLayer.coeff i) τ) :
    LastTierConcreteData A :=
  LastTierConcreteData.ofData
    (LastTierLowerTermData.of_continuousAt (A := A) hs hc) visibleCoeff

variable (D : LastTierConcreteData A)
include D

/-- Pointwise Claim C from the sharpened concrete obligations. -/
theorem observable_blowsUpAt (hm : 0 < m) {τ : ℂ}
    (hτ : τ ∈ A.T (m - 1)) :
    BlowsUpAt A.stratification.observable τ :=
  observable_blowsUpAt_of_lastTier_obligations (A := A) hm hτ
    (D.lowerTerms.lower_puncturedBounded hm hτ)
    (D.visibleCoeff.visibleCoeff_tendsto hm hτ)
    (D.visibleCoeff.visibleCoeff_ne_zero hm hτ)

/-- Package Claim C from the sharpened concrete obligations. -/
def toLastTierBlowup (hm : 0 < m) : LastTierBlowup A :=
  { blowsUp := fun _ hτ => D.observable_blowsUpAt hm hτ }

/-- Pointwise zero-free Claim C from the sharpened concrete obligations. -/
theorem zeroFreeObservable_blowsUpAt (hm : 0 < m) {τ : ℂ}
    (hτ0 : τ ∈ A.T0 (m - 1)) :
    BlowsUpAt A.stratification.observable τ :=
  D.observable_blowsUpAt hm (A.T0_subset_T (m - 1) hτ0)

/-- Package zero-free Claim C from the sharpened concrete obligations. -/
def toZeroFreeLastTierBlowup (hm : 0 < m) : ZeroFreeLastTierBlowup A :=
  { blowsUp := fun _ hτ0 => D.zeroFreeObservable_blowsUpAt hm hτ0 }

end LastTierConcreteData

namespace LastTierVisibleCoeffData

variable {m : Nat} {A : TierSystem m} (D : LastTierVisibleCoeffData A)
include D

/-- Combine visible-coefficient data with already packaged lower-term data. -/
def toLastTierConcreteData
    (lowerTerms : LastTierLowerTermData A) : LastTierConcreteData A :=
  LastTierConcreteData.ofData lowerTerms D

/-- Pointwise Claim C from visible-coefficient data and lower-term data. -/
theorem observable_blowsUpAt
    (lowerTerms : LastTierLowerTermData A) (hm : 0 < m) {τ : ℂ}
    (hτ : τ ∈ A.T (m - 1)) :
    BlowsUpAt A.stratification.observable τ :=
  (D.toLastTierConcreteData lowerTerms).observable_blowsUpAt hm hτ

/-- Package Claim C from visible-coefficient data and lower-term data. -/
def toLastTierBlowup
    (lowerTerms : LastTierLowerTermData A) (hm : 0 < m) : LastTierBlowup A :=
  (D.toLastTierConcreteData lowerTerms).toLastTierBlowup hm

end LastTierVisibleCoeffData

namespace LastTierBlowupData

variable {m : Nat} {A : TierSystem m}

/-- The final concrete gate blows up at every point of the last tier. -/
theorem lastGate_blowsUpAt (hm : 0 < m) {τ : ℂ}
    (hτ : τ ∈ A.T (m - 1)) :
    BlowsUpAt (A.stratification.s (m - 1)) τ := by
  have hlast : m - 1 < m := by omega
  exact A.stratification.gate_blowsUpAt_of_mem_stratum hlast (A.mem_stratum hτ)

variable (D : LastTierBlowupData A)
include D

/-- Claim C: the selected observable blows up at every point of the last tier. -/
theorem observable_blowsUpAt (hm : 0 < m) {τ : ℂ}
    (hτ : τ ∈ A.T (m - 1)) :
    BlowsUpAt A.stratification.observable τ := by
  cases m with
  | zero =>
      omega
  | succ k =>
      have hlower : PuncturedBoundedAt A.stratification.lastLayer.lower τ := by
        simpa [lastTierLower] using D.lower_puncturedBounded (by omega) hτ
      have hgate : BlowsUpAt (A.stratification.s k) τ := by
        simpa using LastTierBlowupData.lastGate_blowsUpAt
          (A := A) (by omega) hτ
      have hvisible :
          Filter.Tendsto (A.stratification.lastLayer.coeff k)
            (puncturedNhds τ) (nhds (D.visibleCoeffLimit τ)) := by
        simpa using D.visibleCoeff_tendsto (by omega) hτ
      have hvisible0 : D.visibleCoeffLimit τ ≠ 0 :=
        D.visibleCoeff_ne_zero (by omega) hτ
      exact A.stratification.observable_blowsUpAt_of_lastlayer
        hlower hgate hvisible hvisible0

/-- Package the pointwise Claim C theorem for downstream pole transfer. -/
def toLastTierBlowup (hm : 0 < m) : LastTierBlowup A where
  blowsUp := fun τ hτ => D.observable_blowsUpAt hm (τ := τ) hτ

/-- Pointwise zero-free Claim C from packaged old-tier Claim-C data. -/
theorem zeroFreeObservable_blowsUpAt (hm : 0 < m) {τ : ℂ}
    (hτ0 : τ ∈ A.T0 (m - 1)) :
    BlowsUpAt A.stratification.observable τ :=
  D.observable_blowsUpAt hm (A.T0_subset_T (m - 1) hτ0)

/-- Package zero-free Claim C from packaged old-tier Claim-C data. -/
def toZeroFreeLastTierBlowup (hm : 0 < m) : ZeroFreeLastTierBlowup A where
  blowsUp := fun τ hτ0 => D.zeroFreeObservable_blowsUpAt hm (τ := τ) hτ0

end LastTierBlowupData

namespace ZeroFreeLastTierBlowupData

variable {m : Nat} {A : TierSystem m} (D : ZeroFreeLastTierBlowupData A)
include D

/-- Claim C on the zero-free last tier from zero-free obligations. -/
theorem observable_blowsUpAt (hm : 0 < m) {τ : ℂ}
    (hτ0 : τ ∈ A.T0 (m - 1)) :
    BlowsUpAt A.stratification.observable τ :=
  observable_blowsUpAt_of_zeroFreeLastTier_obligations (A := A) hm hτ0
    (D.lower_puncturedBounded hm hτ0)
    (D.visibleCoeff_tendsto hm hτ0)
    (D.visibleCoeff_ne_zero hm hτ0)

/-- Package zero-free Claim C from zero-free obligations. -/
def toZeroFreeLastTierBlowup (hm : 0 < m) : ZeroFreeLastTierBlowup A where
  blowsUp := fun τ hτ0 => D.observable_blowsUpAt hm (τ := τ) hτ0

end ZeroFreeLastTierBlowupData

namespace LastTierBlowup

variable {m : Nat} {A : TierSystem m} (B : LastTierBlowup A)
include B

/-- Accessor theorem for the packaged last-tier blow-up conclusion. -/
theorem observable_blowsUpAt {τ : ℂ} (hτ : τ ∈ A.T (m - 1)) :
    BlowsUpAt A.stratification.observable τ :=
  B.blowsUp τ hτ

end LastTierBlowup

namespace ZeroFreeLastTierBlowup

variable {m : Nat} {A : TierSystem m} (B : ZeroFreeLastTierBlowup A)
include B

/-- Accessor theorem for the packaged zero-free last-tier blow-up conclusion. -/
theorem observable_blowsUpAt {τ : ℂ} (hτ0 : τ ∈ A.T0 (m - 1)) :
    BlowsUpAt A.stratification.observable τ :=
  B.blowsUp τ hτ0

end ZeroFreeLastTierBlowup

end TransformerIdentifiability.NLayer
