import AnyLayerIdentifiabilityProof.NLayer.Analytic.A1Identification
import AnyLayerIdentifiabilityProof.NLayer.Step1.TierSets

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Step 1 descent and matrix equality

Owner shard for instantiating the abstract descent endpoint, proving probe-level
bilinear equality on `O_star`, and extending it to `A_1 = A'_1`.
-/

/-- Concrete form of the primed first-tier inclusion.

For a `TierSystem`, tier zero is the first primed stratum.  If the concrete primed
stratification uses the same bias `b`, the first-pole set for the primed first slope
lies in `T 0`. -/
theorem firstPoleSet_subset_tier_zero_of_tierSystem {m : Nat}
    (A : TierSystem m) {b : ℝ}
    (hb : A.stratification.b = b)
    (hlambda : A.stratification.lambda1 ≠ 0) :
    firstPoleSet b A.stratification.lambda1 ⊆ A.T 0 := by
  have hsubset := A.firstPoleSet_subset_zero_of_lambda_ne_zero hlambda
  simpa [← hb] using hsubset

/-- Concrete form of the unprimed first-stratum inclusion. -/
theorem first_stratum_subset_firstPoleSet_of_concrete {m : Nat}
    (P : ConcreteStratification m)
    (hlambda : P.lambda1 ≠ 0) :
    P.S 0 ⊆ firstPoleSet P.b P.lambda1 := by
  intro τ hτ
  simpa [P.first_stratum_eq_firstPoleSet hlambda] using hτ

namespace FixedOStarProbe

/-- The primed first slope is nonzero at a fixed `O_star` probe. -/
theorem primed_firstSlope_ne {r L d : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d} (p : FixedOStarProbe r L d O θ θ') :
    firstSlope θ' p.probe.1 p.probe.2 ≠ 0 :=
  O_star_firstSlope_ne p.mem_O_star

end FixedOStarProbe

/-- Packaged concrete descent data for one probe.

The unprimed side is a concrete stratification.  The primed side is a concrete tier
system.  The remaining fields are exactly the Step 4 descent obligations and the two
first-tier identifications needed to invoke `first_slope_eq_of_tier_descent`. -/
structure ConcreteDescentData (m : Nat) where
  unprimed : ConcreteStratification m
  primed : TierSystem m
  m_pos : 0 < m
  bias_ne_zero : unprimed.b ≠ 0
  unprimedSlope_ne_zero : unprimed.lambda1 ≠ 0
  primedSlope_ne_zero : primed.stratification.lambda1 ≠ 0
  chain : ∀ j, j + 1 < m -> primed.T j ⊆ acc (primed.T (j + 1))
  lastSubset : primed.T (m - 1) ⊆ partialUnion unprimed.S m
  firstPrimed_subset_tier_zero :
    firstPoleSet unprimed.b primed.stratification.lambda1 ⊆ primed.T 0
  firstUnprimed_subset_firstPoleSet :
    unprimed.S 0 ⊆ firstPoleSet unprimed.b unprimed.lambda1

namespace ConcreteDescentData

/-- The unprimed concrete stratification supplies the `StrataSystem` needed by the
abstract descent endpoint. -/
theorem strataSystem {m : Nat} (D : ConcreteDescentData m) :
    StrataSystem D.unprimed.S m :=
  D.unprimed.strataSystem

/-- Probe-level first-slope equality obtained by compiling the concrete tier package
into the abstract descent theorem. -/
theorem first_slope_eq {m : Nat} (D : ConcreteDescentData m) :
    D.unprimed.lambda1 = D.primed.stratification.lambda1 :=
  first_slope_eq_of_tier_descent
    (S := D.unprimed.S) (T := D.primed.T) (m := m)
    (b := D.unprimed.b) (lam := D.unprimed.lambda1)
    (lam' := D.primed.stratification.lambda1)
    D.bias_ne_zero D.unprimedSlope_ne_zero D.primedSlope_ne_zero
    D.m_pos D.strataSystem D.chain D.lastSubset
    D.firstPrimed_subset_tier_zero D.firstUnprimed_subset_firstPoleSet

/-- Convenience wrapper when the packaged first slopes are known to be the concrete
parameter first-slope functions at a probe. -/
theorem firstSlope_eq_of_probe {L d m : Nat} (D : ConcreteDescentData m)
    {θ θ' : Params L d} (p : ProbePair d)
    (hunprimed : D.unprimed.lambda1 = firstSlope θ p.1 p.2)
    (hprimed : D.primed.stratification.lambda1 = firstSlope θ' p.1 p.2) :
    firstSlope θ p.1 p.2 = firstSlope θ' p.1 p.2 := by
  calc
    firstSlope θ p.1 p.2 = D.unprimed.lambda1 := hunprimed.symm
    _ = D.primed.stratification.lambda1 := D.first_slope_eq
    _ = firstSlope θ' p.1 p.2 := hprimed

/-- Constructor that fills the descent endpoint from the exact chain and transferred
last-tier obligations, while deriving both first-tier inclusions from the concrete
stratification interfaces. -/
def ofChainAndLastSubset {m : Nat}
    (unprimed : ConcreteStratification m) (primed : TierSystem m)
    (hm : 0 < m)
    (hb : unprimed.b ≠ 0)
    (hunprimedSlope : unprimed.lambda1 ≠ 0)
    (hprimedSlope : primed.stratification.lambda1 ≠ 0)
    (hbias : primed.stratification.b = unprimed.b)
    (chain : ∀ j, j + 1 < m -> primed.T j ⊆ acc (primed.T (j + 1)))
    (lastSubset : primed.T (m - 1) ⊆ partialUnion unprimed.S m) :
    ConcreteDescentData m where
  unprimed := unprimed
  primed := primed
  m_pos := hm
  bias_ne_zero := hb
  unprimedSlope_ne_zero := hunprimedSlope
  primedSlope_ne_zero := hprimedSlope
  chain := chain
  lastSubset := lastSubset
  firstPrimed_subset_tier_zero :=
    firstPoleSet_subset_tier_zero_of_tierSystem primed hbias hprimedSlope
  firstUnprimed_subset_firstPoleSet :=
    first_stratum_subset_firstPoleSet_of_concrete unprimed hunprimedSlope

/-- Constructor variant where the two packaged first slopes are identified with
already-available concrete scalar slopes.  This keeps the descent-data assembly focused
on the Step 4 chain/last-tier obligations, while deriving the nonzero packaged-slope
fields by rewriting through the supplied equalities. -/
def ofFirstSlopeEq {m : Nat}
    (unprimed : ConcreteStratification m) (primed : TierSystem m)
    (hm : 0 < m)
    (hb : unprimed.b ≠ 0)
    {lam lam' : ℝ}
    (hunprimedSlope_eq : unprimed.lambda1 = lam)
    (hprimedSlope_eq : primed.stratification.lambda1 = lam')
    (hlam : lam ≠ 0)
    (hlam' : lam' ≠ 0)
    (hbias : primed.stratification.b = unprimed.b)
    (chain : ∀ j, j + 1 < m -> primed.T j ⊆ acc (primed.T (j + 1)))
    (lastSubset : primed.T (m - 1) ⊆ partialUnion unprimed.S m) :
    ConcreteDescentData m :=
  ofChainAndLastSubset unprimed primed hm hb
    (by
      rw [hunprimedSlope_eq]
      exact hlam)
    (by
      rw [hprimedSlope_eq]
      exact hlam')
    hbias chain lastSubset

/-- Fixed-`O_star` constructor.  The primed slope nonvanishing is discharged from
`O_star`; the unprimed nonvanishing remains the exact probe-side hypothesis needed by
the abstract descent theorem. -/
noncomputable def ofOStarProbeChainAndLastSubset {r L d m : Nat}
    {O : Set (ProbePair d)} {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ')
    (unprimed : ConcreteStratification m) (primed : TierSystem m)
    (hm : 0 < m)
    (hb : unprimed.b ≠ 0)
    (hunprimedSlope_eq :
      unprimed.lambda1 = firstSlope θ p.probe.1 p.probe.2)
    (hprimedSlope_eq :
      primed.stratification.lambda1 = firstSlope θ' p.probe.1 p.probe.2)
    (hunprimedSlope_ne :
      firstSlope θ p.probe.1 p.probe.2 ≠ 0)
    (hbias : primed.stratification.b = unprimed.b)
    (chain : ∀ j, j + 1 < m -> primed.T j ⊆ acc (primed.T (j + 1)))
    (lastSubset : primed.T (m - 1) ⊆ partialUnion unprimed.S m) :
    ConcreteDescentData m :=
  ofFirstSlopeEq unprimed primed hm hb
    hunprimedSlope_eq hprimedSlope_eq
    hunprimedSlope_ne p.primed_firstSlope_ne
    hbias chain lastSubset

end ConcreteDescentData

/-- Packaged concrete descent data using the zero-free primed tier family `T0`.

This is parallel to `ConcreteDescentData`: the old-tier API is left unchanged, while
the abstract descent endpoint is instantiated with `T := primed.T0`. -/
structure ZeroFreeConcreteDescentData (m : Nat) where
  unprimed : ConcreteStratification m
  primed : TierSystem m
  m_pos : 0 < m
  bias_ne_zero : unprimed.b ≠ 0
  unprimedSlope_ne_zero : unprimed.lambda1 ≠ 0
  primedSlope_ne_zero : primed.stratification.lambda1 ≠ 0
  chain : ∀ j, j + 1 < m -> primed.T0 j ⊆ acc (primed.T0 (j + 1))
  lastSubset : primed.T0 (m - 1) ⊆ partialUnion unprimed.S m
  firstPrimed_subset_tier_zero :
    firstPoleSet unprimed.b primed.stratification.lambda1 ⊆ primed.T0 0
  firstUnprimed_subset_firstPoleSet :
    unprimed.S 0 ⊆ firstPoleSet unprimed.b unprimed.lambda1

namespace ZeroFreeConcreteDescentData

/-- The unprimed concrete stratification supplies the `StrataSystem` needed by the
abstract descent endpoint. -/
theorem strataSystem {m : Nat} (D : ZeroFreeConcreteDescentData m) :
    StrataSystem D.unprimed.S m :=
  D.unprimed.strataSystem

/-- Probe-level first-slope equality obtained by compiling the zero-free tier package
into the abstract descent theorem. -/
theorem first_slope_eq {m : Nat} (D : ZeroFreeConcreteDescentData m) :
    D.unprimed.lambda1 = D.primed.stratification.lambda1 :=
  first_slope_eq_of_tier_descent
    (S := D.unprimed.S) (T := D.primed.T0) (m := m)
    (b := D.unprimed.b) (lam := D.unprimed.lambda1)
    (lam' := D.primed.stratification.lambda1)
    D.bias_ne_zero D.unprimedSlope_ne_zero D.primedSlope_ne_zero
    D.m_pos D.strataSystem D.chain D.lastSubset
    D.firstPrimed_subset_tier_zero D.firstUnprimed_subset_firstPoleSet

/-- Convenience wrapper when the packaged first slopes are known to be the concrete
parameter first-slope functions at a probe. -/
theorem firstSlope_eq_of_probe {L d m : Nat} (D : ZeroFreeConcreteDescentData m)
    {θ θ' : Params L d} (p : ProbePair d)
    (hunprimed : D.unprimed.lambda1 = firstSlope θ p.1 p.2)
    (hprimed : D.primed.stratification.lambda1 = firstSlope θ' p.1 p.2) :
    firstSlope θ p.1 p.2 = firstSlope θ' p.1 p.2 := by
  calc
    firstSlope θ p.1 p.2 = D.unprimed.lambda1 := hunprimed.symm
    _ = D.primed.stratification.lambda1 := D.first_slope_eq
    _ = firstSlope θ' p.1 p.2 := hprimed

/-- Constructor from explicit zero-free chain, last-tier transfer, and first-pole
inclusion into `T0 0`. -/
def ofChainAndLastSubset {m : Nat}
    (unprimed : ConcreteStratification m) (primed : TierSystem m)
    (hm : 0 < m)
    (hb : unprimed.b ≠ 0)
    (hunprimedSlope : unprimed.lambda1 ≠ 0)
    (hprimedSlope : primed.stratification.lambda1 ≠ 0)
    (chain : ∀ j, j + 1 < m -> primed.T0 j ⊆ acc (primed.T0 (j + 1)))
    (lastSubset : primed.T0 (m - 1) ⊆ partialUnion unprimed.S m)
    (firstPrimed_subset_tier_zero :
      firstPoleSet unprimed.b primed.stratification.lambda1 ⊆ primed.T0 0) :
    ZeroFreeConcreteDescentData m where
  unprimed := unprimed
  primed := primed
  m_pos := hm
  bias_ne_zero := hb
  unprimedSlope_ne_zero := hunprimedSlope
  primedSlope_ne_zero := hprimedSlope
  chain := chain
  lastSubset := lastSubset
  firstPrimed_subset_tier_zero := firstPrimed_subset_tier_zero
  firstUnprimed_subset_firstPoleSet :=
    first_stratum_subset_firstPoleSet_of_concrete unprimed hunprimedSlope

/-- Constructor deriving the first-pole inclusion into `T0 0` from zero-freeness of the
lead coefficient on the first primed stratum. -/
def ofZeroFreeChainAndLastSubset {m : Nat}
    (unprimed : ConcreteStratification m) (primed : TierSystem m)
    (hm : 0 < m)
    (hb : unprimed.b ≠ 0)
    (hunprimedSlope : unprimed.lambda1 ≠ 0)
    (hprimedSlope : primed.stratification.lambda1 ≠ 0)
    (hbias : primed.stratification.b = unprimed.b)
    (hlead0 :
      ∀ τ ∈ primed.stratification.S 0,
        (primed.nestedFamily.step 0).lead
          (gatePrefix primed.stratification 0 τ) ≠ 0)
    (chain : ∀ j, j + 1 < m -> primed.T0 j ⊆ acc (primed.T0 (j + 1)))
    (lastSubset : primed.T0 (m - 1) ⊆ partialUnion unprimed.S m) :
    ZeroFreeConcreteDescentData m :=
  ofChainAndLastSubset unprimed primed hm hb hunprimedSlope hprimedSlope
    chain lastSubset
    (by
      intro τ hτ
      have hτT : τ ∈ primed.T 0 :=
        firstPoleSet_subset_tier_zero_of_tierSystem primed hbias hprimedSlope hτ
      have hτS : τ ∈ primed.stratification.S 0 := by
        simpa using hτT
      rw [primed.T0_zero_eq_stratum_of_lead_ne hlead0]
      exact hτS)

/-- Constructor variant where the two packaged first slopes are identified with
already-available concrete scalar slopes. -/
def ofFirstSlopeEq {m : Nat}
    (unprimed : ConcreteStratification m) (primed : TierSystem m)
    (hm : 0 < m)
    (hb : unprimed.b ≠ 0)
    {lam lam' : ℝ}
    (hunprimedSlope_eq : unprimed.lambda1 = lam)
    (hprimedSlope_eq : primed.stratification.lambda1 = lam')
    (hlam : lam ≠ 0)
    (hlam' : lam' ≠ 0)
    (hbias : primed.stratification.b = unprimed.b)
    (hlead0 :
      ∀ τ ∈ primed.stratification.S 0,
        (primed.nestedFamily.step 0).lead
          (gatePrefix primed.stratification 0 τ) ≠ 0)
    (chain : ∀ j, j + 1 < m -> primed.T0 j ⊆ acc (primed.T0 (j + 1)))
    (lastSubset : primed.T0 (m - 1) ⊆ partialUnion unprimed.S m) :
    ZeroFreeConcreteDescentData m :=
  ofZeroFreeChainAndLastSubset unprimed primed hm hb
    (by
      rw [hunprimedSlope_eq]
      exact hlam)
    (by
      rw [hprimedSlope_eq]
      exact hlam')
    hbias hlead0 chain lastSubset

/-- Fixed-`O_star` zero-free constructor.  The primed slope nonvanishing is discharged
from `O_star`; the unprimed nonvanishing remains the exact probe-side hypothesis needed
by the abstract descent theorem. -/
noncomputable def ofOStarProbeChainAndLastSubset {r L d m : Nat}
    {O : Set (ProbePair d)} {θ θ' : Params L d}
    (p : FixedOStarProbe r L d O θ θ')
    (unprimed : ConcreteStratification m) (primed : TierSystem m)
    (hm : 0 < m)
    (hb : unprimed.b ≠ 0)
    (hunprimedSlope_eq :
      unprimed.lambda1 = firstSlope θ p.probe.1 p.probe.2)
    (hprimedSlope_eq :
      primed.stratification.lambda1 = firstSlope θ' p.probe.1 p.probe.2)
    (hunprimedSlope_ne :
      firstSlope θ p.probe.1 p.probe.2 ≠ 0)
    (hbias : primed.stratification.b = unprimed.b)
    (hlead0 :
      ∀ τ ∈ primed.stratification.S 0,
        (primed.nestedFamily.step 0).lead
          (gatePrefix primed.stratification 0 τ) ≠ 0)
    (chain : ∀ j, j + 1 < m -> primed.T0 j ⊆ acc (primed.T0 (j + 1)))
    (lastSubset : primed.T0 (m - 1) ⊆ partialUnion unprimed.S m) :
    ZeroFreeConcreteDescentData m :=
  ofFirstSlopeEq unprimed primed hm hb
    hunprimedSlope_eq hprimedSlope_eq
    hunprimedSlope_ne p.primed_firstSlope_ne
    hbias hlead0 chain lastSubset

end ZeroFreeConcreteDescentData

namespace FixedOStarProbe

end FixedOStarProbe

/-! ## Algebraic continuation from an open probe set -/

/-- If the first slopes agree on a nonempty open probe set, then the first attention
matrices agree.

This is the Lean version of Step 5 of Proposition `A1`: the bilinear difference
`(w, v) ↦ wᵀ(A₁ - A₁')v` is a polynomial, so vanishing on a nonempty open probe set
forces it to vanish identically. -/
theorem firstAttention_eq_of_isOpen_nonempty_probe_set_firstSlope_eq {L d : Nat}
    {θ θ' : Params L d} {U : Set (ProbePair d)}
    (hOpen : IsOpen U) (hNonempty : U.Nonempty)
    (hEq :
      ∀ p : ProbePair d, p ∈ U →
        firstSlope θ p.1 p.2 = firstSlope θ' p.1 p.2) :
    firstAttention θ = firstAttention θ' := by
  let Q : MvPolynomial (ProbeVar d) ℝ :=
    matrixBilinProbePoly (firstAttention θ - firstAttention θ')
  have hOpen_image :
      IsOpen ((probeEval : ProbePair d -> ProbeVar d -> ℝ) '' U) :=
    (probeEvalHomeomorph d).isOpenMap U hOpen
  have hNonempty_image :
      (((probeEval : ProbePair d -> ProbeVar d -> ℝ) '' U) :
        Set (ProbeVar d -> ℝ)).Nonempty :=
    hNonempty.image _
  have hQzero : Q = 0 := by
    refine eq_zero_of_eval_eqOn_isOpen hOpen_image hNonempty_image ?_
    intro x hx
    rcases hx with ⟨p, hpU, rfl⟩
    have hsub :
        matrixBilin (firstAttention θ - firstAttention θ') p.1 p.2 = 0 :=
      (matrixBilin_eq_iff_sub_eq_zero
        (firstAttention θ) (firstAttention θ') p.1 p.2).mp
        (by simpa [firstSlope] using hEq p hpU)
    simpa [Q, eval_matrixBilinProbePoly] using hsub
  apply matrix_eq_of_forall_bilin_sub_eq_zero
  intro w v
  have hEval :
      MvPolynomial.eval (probeEval ((w, v) : ProbePair d)) Q = 0 := by
    simp [hQzero]
  simpa [Q, eval_matrixBilinProbePoly] using hEval

/-- Open-set version specialized to the generic Step 0 region `O_star`. -/
theorem firstAttention_eq_of_open_nonempty_OStar_firstSlope_eq {L d : Nat}
    {θ θ' : Params L d} {O : Set (ProbePair d)}
    (hOpen : IsOpen (O_star θ' O))
    (hNonempty : (O_star θ' O).Nonempty)
    (hEq :
      ∀ p : ProbePair d, p ∈ O_star θ' O →
        firstSlope θ p.1 p.2 = firstSlope θ' p.1 p.2) :
    firstAttention θ = firstAttention θ' :=
  firstAttention_eq_of_isOpen_nonempty_probe_set_firstSlope_eq
    hOpen hNonempty hEq

/-- Standing-assumption wrapper for the TeX Step 5 endpoint.  The generic package
supplies that `O_star` is open and nonempty, and algebraic continuation upgrades
first-slope equality on `O_star` to matrix equality. -/
theorem step1Conclusion_of_standingAssumptions_openOStar_firstSlope_eq {r L d : Nat}
    {θ θ' : Params L d} {O : Set (ProbePair d)}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (hEq :
      ∀ p : ProbePair d, p ∈ O_star θ' O →
        firstSlope θ p.1 p.2 = firstSlope θ' p.1 p.2) :
    Step1Conclusion θ θ' :=
  firstAttention_eq_of_open_nonempty_OStar_firstSlope_eq
    hStanding.generic.isOpen_O_star hStanding.generic.nonempty_O_star hEq

/-! ## Zero-free concrete descent final assembly -/

/-- Probe-level first-slope equality from any zero-free concrete descent package whose
first slopes are identified with the two parameter first-slope functions at that probe. -/
theorem firstSlope_eq_of_exists_zeroFree_concrete_descent {L d : Nat}
    {θ θ' : Params L d} (p : ProbePair d)
    (hDesc :
      ∃ m : Nat, ∃ D : ZeroFreeConcreteDescentData m,
        D.unprimed.lambda1 = firstSlope θ p.1 p.2 ∧
          D.primed.stratification.lambda1 = firstSlope θ' p.1 p.2) :
    firstSlope θ p.1 p.2 = firstSlope θ' p.1 p.2 := by
  rcases hDesc with ⟨m, D, hunprimed, hprimed⟩
  exact D.firstSlope_eq_of_probe p hunprimed hprimed

/-- Final Step 1 assembly from per-probe zero-free concrete descent data on the open
nonempty generic region `O_star`. -/
theorem step1Conclusion_of_standingAssumptions_openOStar_zeroFree_concrete_descent
    {r L d : Nat} {θ θ' : Params L d} {O : Set (ProbePair d)}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (hDesc :
      ∀ p : ProbePair d, p ∈ O_star θ' O →
        ∃ m : Nat, ∃ D : ZeroFreeConcreteDescentData m,
          D.unprimed.lambda1 = firstSlope θ p.1 p.2 ∧
            D.primed.stratification.lambda1 = firstSlope θ' p.1 p.2) :
    Step1Conclusion θ θ' :=
  step1Conclusion_of_standingAssumptions_openOStar_firstSlope_eq hStanding
    fun p hp => firstSlope_eq_of_exists_zeroFree_concrete_descent p (hDesc p hp)

/-- Open-`O_star` final assembly when zero-free descent data is supplied for the
packaged fixed generic probe. -/
theorem step1Conclusion_of_standingAssumptions_openOStar_fixed_zeroFree_concrete_descent
    {r L d : Nat} {θ θ' : Params L d} {O : Set (ProbePair d)}
    (hStanding : Step1StandingAssumptions r L d O θ θ')
    (hDesc :
      ∀ p : FixedOStarProbe r L d O θ θ',
        ∃ m : Nat, ∃ D : ZeroFreeConcreteDescentData m,
          D.unprimed.lambda1 = firstSlope θ p.probe.1 p.probe.2 ∧
            D.primed.stratification.lambda1 = firstSlope θ' p.probe.1 p.probe.2) :
    Step1Conclusion θ θ' :=
  step1Conclusion_of_standingAssumptions_openOStar_zeroFree_concrete_descent hStanding
    fun p hp => by
      simpa [FixedOStarProbe.ofLocalAgreement] using
        hDesc (FixedOStarProbe.ofLocalAgreement hStanding.agreement (p := p) hp)

/-- The open-`O_star` theorem-statement wrapper with packaged fixed-probe zero-free
descent data. -/
theorem zeroFreeConcreteStep1Theorem_of_openOStar_fixed_concrete_descent {r L d : Nat}
    {θ θ' : Params L d} {O : Set (ProbePair d)}
    (hDesc :
      ∀ _hStanding : Step1StandingAssumptions r L d O θ θ',
        ∀ p : FixedOStarProbe r L d O θ θ',
          ∃ m : Nat, ∃ D : ZeroFreeConcreteDescentData m,
            D.unprimed.lambda1 = firstSlope θ p.probe.1 p.probe.2 ∧
              D.primed.stratification.lambda1 = firstSlope θ' p.probe.1 p.probe.2) :
    ConcreteStep1TheoremStatement r L d O θ θ' := by
  intro hStanding
  exact step1Conclusion_of_standingAssumptions_openOStar_fixed_zeroFree_concrete_descent
    hStanding (hDesc hStanding)

end TransformerIdentifiability.NLayer
