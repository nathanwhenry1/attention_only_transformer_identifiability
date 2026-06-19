import AnyLayerIdentifiabilityProof.NLayer.Step1.DescentConclusion
import AnyLayerIdentifiabilityProof.NLayer.Step1.PolynomialFamily
import AnyLayerIdentifiabilityProof.NLayer.Step1.Propagation
import AnyLayerIdentifiabilityProof.NLayer.Step1.Transfer

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Step 1 depth certificate

Owner shard for the corollary that the first value matrix is nonzero under the Step 1
standing hypotheses.
-/

/-- The first value matrix, with the same zero-depth fallback convention as
`firstAttention`. -/
noncomputable def firstValue {L d : Nat} (θ : Params L d) :
    Matrix (Fin d) (Fin d) ℝ :=
  (paramStream θ 0).1

theorem firstValue_eq_of_pos {L d : Nat} (θ : Params L d) (hL : 0 < L) :
    firstValue θ = (θ ⟨0, hL⟩).1 := by
  simp [firstValue, hL]

/-- The transformer-specific no-depth-drop obligation for a chosen target value matrix. -/
def TargetValueNoDepthDrop {L d : Nat} (θ θ' : Params L d)
    (targetValue : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  Step1Conclusion θ θ' -> targetValue = 0 -> False

/-- The no-depth-drop obligation specialized to the concrete first layer value matrix. -/
def FirstLayerValueNoDepthDrop {L d : Nat} (θ θ' : Params L d)
    (hL : 0 < L) : Prop :=
  TargetValueNoDepthDrop θ θ' (θ ⟨0, hL⟩).1

namespace FixedOStarProbe

variable {r L d : Nat} {O : Set (ProbePair d)} {θ θ' : Params L d}

/-- Concrete constant-probe constructor data for the unprimed parameters at a fixed
`O_star` probe and visible coordinate. -/
noncomputable def concreteUnprimedData
    (p : FixedOStarProbe r L d O θ θ') :
    ConstantProbeConcreteData (paramStream θ) (Real.log (r : ℝ))
      p.probe.1 p.probe.2 L p.iota :=
  ConstantProbeConcreteData.ofConcrete (paramStream θ) (Real.log (r : ℝ))
    p.probe.1 p.probe.2 L p.iota

/-- Concrete constant-probe constructor data for the primed parameters at a fixed
`O_star` probe and visible coordinate. -/
noncomputable def concretePrimedData
    (p : FixedOStarProbe r L d O θ θ') :
    ConstantProbeConcreteData (paramStream θ') (Real.log (r : ℝ))
      p.probe.1 p.probe.2 L p.iota :=
  ConstantProbeConcreteData.ofConcrete (paramStream θ') (Real.log (r : ℝ))
    p.probe.1 p.probe.2 L p.iota

/-- The unprimed concrete stratification assembled from the fixed probe. -/
noncomputable def concreteUnprimedStratification
    (p : FixedOStarProbe r L d O θ θ') :
    ConcreteStratification L :=
  p.concreteUnprimedData.toConcreteStratification

/-- The primed concrete stratification assembled from the fixed probe. -/
noncomputable def concretePrimedStratification
    (p : FixedOStarProbe r L d O θ θ') :
    ConcreteStratification L :=
  p.concretePrimedData.toConcreteStratification

@[simp] theorem concreteUnprimedStratification_b
    (p : FixedOStarProbe r L d O θ θ') :
    p.concreteUnprimedStratification.b = Real.log (r : ℝ) :=
  rfl

@[simp] theorem concretePrimedStratification_b
    (p : FixedOStarProbe r L d O θ θ') :
    p.concretePrimedStratification.b = Real.log (r : ℝ) :=
  rfl

/-- The unprimed concrete stratification has the fixed probe's unprimed first slope. -/
theorem concreteUnprimedStratification_lambda1_eq_firstSlope
    (p : FixedOStarProbe r L d O θ θ') :
    p.concreteUnprimedStratification.lambda1 =
      firstSlope θ p.probe.1 p.probe.2 := by
  simpa [concreteUnprimedStratification] using
    ConstantProbeConcreteData.toConcreteStratificationData_lambda1_eq_firstSlope
      (D := p.concreteUnprimedData)

/-- The primed concrete stratification has the fixed probe's primed first slope. -/
theorem concretePrimedStratification_lambda1_eq_firstSlope
    (p : FixedOStarProbe r L d O θ θ') :
    p.concretePrimedStratification.lambda1 =
      firstSlope θ' p.probe.1 p.probe.2 := by
  simpa [concretePrimedStratification] using
    ConstantProbeConcreteData.toConcreteStratificationData_lambda1_eq_firstSlope
      (D := p.concretePrimedData)

/-- The primed tier system, using the concrete primed stratification and the canonical
Step 1 propagation polynomial tail tower. -/
noncomputable def concretePrimedTierSystem
    (p : FixedOStarProbe r L d O θ θ') :
    TierSystem L :=
  TierSystem.ofPolynomialNestedTailData p.concretePrimedStratification
    (step1FormalPhiPropagationPolynomialNestedTailData (paramStream θ')
      p.probe.1 p.probe.2)

@[simp] theorem concretePrimedTierSystem_stratification
    (p : FixedOStarProbe r L d O θ θ') :
    p.concretePrimedTierSystem.stratification =
      p.concretePrimedStratification :=
  rfl

/-- The primed concrete tier system has the fixed probe's primed first slope. -/
theorem concretePrimedTierSystem_lambda1_eq_firstSlope
    (p : FixedOStarProbe r L d O θ θ') :
    p.concretePrimedTierSystem.stratification.lambda1 =
      firstSlope θ' p.probe.1 p.probe.2 := by
  simpa [concretePrimedTierSystem] using
    p.concretePrimedStratification_lambda1_eq_firstSlope

/-- The formal-phi nested tail tower evaluates to the concrete constant-probe
`formalPhi` expression along the primed gate prefix. -/
theorem concretePrimedTierSystem_evalStep_eq_formalPhi
    (p : FixedOStarProbe r L d O θ θ') (m : Nat) (τ : ℂ) :
    p.concretePrimedTierSystem.nestedFamily.evalStep
        (gatePrefix p.concretePrimedTierSystem.stratification (m + 1) τ) =
      formalPhi (paramStream θ') (m + 1)
        (constantProbeGatePrefix (paramStream θ') (Real.log (r : ℝ))
          p.probe.1 p.probe.2 (m + 1) τ)
        p.probe.1 p.probe.2 := by
  rw [concretePrimedTierSystem, TierSystem.ofPolynomialNestedTailData_nestedFamily,
    step1FormalPhiPropagationPolynomialNestedTailData_toNestedTailFamily,
    step1FormalPhiPropagationNestedTailFamily_evalStep_eq_formalPhi]
  apply congrArg
    (fun z => formalPhi (paramStream θ') (m + 1) z p.probe.1 p.probe.2)
  funext k
  by_cases hk : k < m + 1
  · simp [extendGate, gatePrefix, concretePrimedStratification,
      ConstantProbeConcreteData.toConcreteStratification,
      ConcreteStratificationData.toConcreteStratification,
      ConstantProbeConcreteData.toConcreteStratificationData,
      constantProbeGatePrefix, hk]
  · simp [extendGate, constantProbeGatePrefix, hk]

/-- The `tierPhiPath` for the formal-phi primed tier system is exactly the concrete
constant-probe `formalPhi` path. -/
theorem concretePrimedTierSystem_tierPhiPath_eq_formalPhi
    (p : FixedOStarProbe r L d O θ θ') (m : Nat) (τ : ℂ) :
    tierPhiPath p.concretePrimedTierSystem m τ =
      formalPhi (paramStream θ') (m + 1)
        (constantProbeGatePrefix (paramStream θ') (Real.log (r : ℝ))
          p.probe.1 p.probe.2 (m + 1) τ)
        p.probe.1 p.probe.2 := by
  simpa [tierPhiPath] using
    p.concretePrimedTierSystem_evalStep_eq_formalPhi m τ

/-- Real-tail agreement between the two concrete constant-probe observables.  The
threshold is strengthened to `max p.T0 0` so the public observable bridge can use both
the fixed tail agreement and positive real probe parameter. -/
theorem realTailObservableAgreement_concrete
    (p : FixedOStarProbe r L d O θ θ') (hr : 0 < r) :
    ∀ τ : ℝ, max p.T0 0 < τ ->
      p.concreteUnprimedStratification.observable (τ : ℂ) =
        p.concretePrimedStratification.observable (τ : ℂ) := by
  intro τ hτ
  have htail : p.T0 < τ := lt_of_le_of_lt (le_max_left p.T0 0) hτ
  have hpos : 0 < τ := lt_of_le_of_lt (le_max_right p.T0 0) hτ
  calc
    p.concreteUnprimedStratification.observable (τ : ℂ) =
        (Fobs r θ p.probe.1 p.probe.2 τ p.iota : ℂ) := by
      simpa [concreteUnprimedStratification, concreteUnprimedData] using
        constantProbeObservable_paramStream_eq_Fobs_apply_of_pos
          r hr θ p.probe.1 p.probe.2 p.iota hpos
    _ = (Fobs r θ' p.probe.1 p.probe.2 τ p.iota : ℂ) := by
      exact congrArg (fun x : ℝ => (x : ℂ))
        (congrFun (p.tail_agreement τ htail) p.iota)
    _ = p.concretePrimedStratification.observable (τ : ℂ) := by
      symm
      simpa [concretePrimedStratification, concretePrimedData] using
        constantProbeObservable_paramStream_eq_Fobs_apply_of_pos
          r hr θ' p.probe.1 p.probe.2 p.iota hpos

/-- Claim-D endpoint for the fixed concrete probe assembly: zero-free last-tier points
of the primed tier system lie in the unprimed partial singular union. -/
theorem zeroFreeLastTier_subset_partialUnion_of_concrete
    (p : FixedOStarProbe r L d O θ θ') (hr : 0 < r) (hL : 0 < L)
    (C : LastTierConcreteData p.concretePrimedTierSystem) :
    p.concretePrimedTierSystem.T0 (L - 1) ⊆
      partialUnion p.concreteUnprimedStratification.S L :=
  transferred_zeroFreeLastTier_subset_partialUnion_ofConcreteDataOnRealTail
    (unprimed := p.concreteUnprimedStratification)
    (A := p.concretePrimedTierSystem)
    hL (max p.T0 0) (p.realTailObservableAgreement_concrete hr) C

/-- Assemble zero-free concrete descent data for one fixed `O_star` probe from the
concrete stratifications, canonical primed tier system, zero-free propagation, and
last-tier concrete data. -/
noncomputable def zeroFreeConcreteDescentData_of_concrete
    (p : FixedOStarProbe r L d O θ θ') (hr : 0 < r) (hL : 0 < L)
    (hlog : Real.log (r : ℝ) ≠ 0)
    (hunprimedSlope_ne : firstSlope θ p.probe.1 p.probe.2 ≠ 0)
    (hlead0 :
      ∀ τ ∈ p.concretePrimedTierSystem.stratification.S 0,
        (p.concretePrimedTierSystem.nestedFamily.step 0).lead
          (gatePrefix p.concretePrimedTierSystem.stratification 0 τ) ≠ 0)
    (propagation : ZeroFreeTierPropagation p.concretePrimedTierSystem)
    (lastTier : LastTierConcreteData p.concretePrimedTierSystem) :
    ZeroFreeConcreteDescentData L :=
  ZeroFreeConcreteDescentData.ofOStarProbeChainAndLastSubset p
    p.concreteUnprimedStratification p.concretePrimedTierSystem hL
    (by simpa using hlog)
    p.concreteUnprimedStratification_lambda1_eq_firstSlope
    p.concretePrimedTierSystem_lambda1_eq_firstSlope
    hunprimedSlope_ne
    (by simp)
    hlead0
    propagation.chain
    (p.zeroFreeLastTier_subset_partialUnion_of_concrete hr hL lastTier)

/-- Existential descent witness shape consumed by the final zero-free Step 1 assembly
theorems. -/
theorem fixedOStar_zeroFreeConcreteDescent_exists_of_concrete
    (p : FixedOStarProbe r L d O θ θ') (hr : 0 < r) (hL : 0 < L)
    (hlog : Real.log (r : ℝ) ≠ 0)
    (hunprimedSlope_ne : firstSlope θ p.probe.1 p.probe.2 ≠ 0)
    (hlead0 :
      ∀ τ ∈ p.concretePrimedTierSystem.stratification.S 0,
        (p.concretePrimedTierSystem.nestedFamily.step 0).lead
          (gatePrefix p.concretePrimedTierSystem.stratification 0 τ) ≠ 0)
    (propagation : ZeroFreeTierPropagation p.concretePrimedTierSystem)
    (lastTier : LastTierConcreteData p.concretePrimedTierSystem) :
    ∃ m : Nat, ∃ D : ZeroFreeConcreteDescentData m,
      D.unprimed.lambda1 = firstSlope θ p.probe.1 p.probe.2 ∧
        D.primed.stratification.lambda1 =
          firstSlope θ' p.probe.1 p.probe.2 := by
  refine
    ⟨L,
      p.zeroFreeConcreteDescentData_of_concrete
        hr hL hlog hunprimedSlope_ne hlead0 propagation lastTier,
      ?_, ?_⟩
  · simpa [zeroFreeConcreteDescentData_of_concrete] using
      p.concreteUnprimedStratification_lambda1_eq_firstSlope
  · simpa [zeroFreeConcreteDescentData_of_concrete] using
      p.concretePrimedTierSystem_lambda1_eq_firstSlope

end FixedOStarProbe

/-- Abstract depth-certificate package.

`targetValue` is usually `firstValue θ`; the separate field lets downstream code use a
definitionally convenient matrix while recording that it is the first value matrix.  The
`no_depth_drop` field is the packaged transformer-specific contradiction: once Step 1
has identified the first attention matrices, the target value matrix cannot vanish. -/
structure DepthCertificateData {L d : Nat} (θ θ' : Params L d) where
  targetValue : Matrix (Fin d) (Fin d) ℝ
  targetValue_eq_firstValue : targetValue = firstValue θ
  step1_eq : firstAttention θ = firstAttention θ'
  no_depth_drop : TargetValueNoDepthDrop θ θ' targetValue

namespace DepthCertificateData

/-- Constructor with an arbitrary target matrix, exposing exactly the target equality,
Step 1 conclusion, and target no-depth-drop obligations. -/
def ofTargetValue {L d : Nat} {θ θ' : Params L d}
    (targetValue : Matrix (Fin d) (Fin d) ℝ)
    (targetValue_eq_firstValue : targetValue = firstValue θ)
    (step1_eq : Step1Conclusion θ θ')
    (no_depth_drop : TargetValueNoDepthDrop θ θ' targetValue) :
    DepthCertificateData θ θ' where
  targetValue := targetValue
  targetValue_eq_firstValue := targetValue_eq_firstValue
  step1_eq := step1_eq
  no_depth_drop := no_depth_drop

/-- Constructor specialized to the concrete first layer value matrix. -/
noncomputable def ofFirstLayerValue {L d : Nat} {θ θ' : Params L d}
    (hL : 0 < L) (step1_eq : Step1Conclusion θ θ')
    (no_depth_drop : FirstLayerValueNoDepthDrop θ θ' hL) :
    DepthCertificateData θ θ' :=
  ofTargetValue (θ := θ) (θ' := θ') (θ ⟨0, hL⟩).1
    (firstValue_eq_of_pos θ hL).symm step1_eq no_depth_drop

/-- Concrete Step 1 constructor using the positive-depth first-layer matrix as the target. -/
noncomputable def ofConcreteStep1FirstLayer {r L d : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    (step1_theorem : ConcreteStep1TheoremStatement r L d O θ θ')
    (standing : Step1StandingAssumptions r L d O θ θ')
    (no_depth_drop : FirstLayerValueNoDepthDrop θ θ' standing.depth_pos) :
    DepthCertificateData θ θ' :=
  ofFirstLayerValue (θ := θ) (θ' := θ') standing.depth_pos
    (step1_theorem standing) no_depth_drop

/-- Contradiction form of the packaged target-value no-depth-drop field. -/
theorem targetValue_eq_zero_absurd {L d : Nat} {θ θ' : Params L d}
    (D : DepthCertificateData θ θ') (hzero : D.targetValue = 0) :
    False :=
  D.no_depth_drop D.step1_eq hzero

/-- The packaged no-depth-drop contradiction makes the target value matrix nonzero. -/
theorem targetValue_ne_zero {L d : Nat} {θ θ' : Params L d}
    (D : DepthCertificateData θ θ') :
    D.targetValue ≠ 0 := by
  exact D.targetValue_eq_zero_absurd

/-- Contradiction form of the depth certificate for the abstract first value matrix. -/
theorem firstValue_eq_zero_absurd {L d : Nat} {θ θ' : Params L d}
    (D : DepthCertificateData θ θ') (hzero : firstValue θ = 0) :
    False := by
  apply D.targetValue_eq_zero_absurd
  calc
    D.targetValue = firstValue θ := D.targetValue_eq_firstValue
    _ = 0 := hzero

/-- Positive-depth contradiction wrapper for the concrete first layer projection. -/
theorem firstLayerValue_eq_zero_absurd {L d : Nat} {θ θ' : Params L d}
    (D : DepthCertificateData θ θ') (hL : 0 < L)
    (hzero : (θ ⟨0, hL⟩).1 = 0) :
    False := by
  apply D.firstValue_eq_zero_absurd
  calc
    firstValue θ = (θ ⟨0, hL⟩).1 := firstValue_eq_of_pos θ hL
    _ = 0 := hzero

end DepthCertificateData

/-- Direct positive-depth contradiction wrapper for the concrete first layer value
matrix. -/
theorem firstLayerValue_eq_zero_absurd_of_depth_certificate {L d : Nat}
    {θ θ' : Params L d}
    (D : DepthCertificateData θ θ') (hL : 0 < L)
    (hzero : (θ ⟨0, hL⟩).1 = 0) :
    False :=
  D.firstLayerValue_eq_zero_absurd hL hzero

/-- Direct concrete first-layer contradiction from a concrete Step 1 theorem statement,
standing assumptions, and the positive-depth no-depth-drop obligation. -/
theorem firstLayerValue_eq_zero_absurd_of_concrete_step1_noDepthDrop
    {r L d : Nat} {O : Set (ProbePair d)} {θ θ' : Params L d}
    (step1_theorem : ConcreteStep1TheoremStatement r L d O θ θ')
    (standing : Step1StandingAssumptions r L d O θ θ')
    (no_depth_drop : FirstLayerValueNoDepthDrop θ θ' standing.depth_pos)
    (hzero : (θ ⟨0, standing.depth_pos⟩).1 = 0) :
    False :=
  firstLayerValue_eq_zero_absurd_of_depth_certificate
    (DepthCertificateData.ofConcreteStep1FirstLayer step1_theorem standing
      no_depth_drop)
    standing.depth_pos hzero

/-- Direct concrete first-layer endpoint from a concrete Step 1 theorem statement,
standing assumptions, and the positive-depth no-depth-drop obligation. -/
theorem firstLayerValue_ne_zero_of_concrete_step1_noDepthDrop {r L d : Nat}
    {O : Set (ProbePair d)} {θ θ' : Params L d}
    (step1_theorem : ConcreteStep1TheoremStatement r L d O θ θ')
    (standing : Step1StandingAssumptions r L d O θ θ')
    (no_depth_drop : FirstLayerValueNoDepthDrop θ θ' standing.depth_pos) :
    (θ ⟨0, standing.depth_pos⟩).1 ≠ 0 :=
  firstLayerValue_eq_zero_absurd_of_concrete_step1_noDepthDrop
    step1_theorem standing no_depth_drop

end TransformerIdentifiability.NLayer
