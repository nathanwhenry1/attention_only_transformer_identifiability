import AnyLayerIdentifiabilityProof.NLayer.IDL.IDLStatement

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Realization, sweep, and tail handoff for IDL

This file owns the TeX Step 3 construction of lower-depth IDL data after the first layer
has been matched.
-/

/-! ## Realized tail paths -/

/-- Tail paths realized by full-depth source paths through the matched first layer. -/
def realizedTailPathSet {L d : Nat} (r : Nat)
    (θ : Params (L + 1) d) (FullPaths : Set (ProbePath d)) :
    Set (ProbePath d) :=
  { target | ∃ source : ProbePath d, source ∈ FullPaths ∧
      Nonempty (RealizationData r (Params.headValue θ) (Params.headAttention θ)
        target source) }

/-- The open tail probe region where constant tail paths are realized by full-depth source
paths.  Taking the interior makes openness part of the definition; nonemptiness and anchor
intersection are the real analytic content of the TeX sweep. -/
def realizedTailRegion {L d : Nat} (r : Nat)
    (θ : Params (L + 1) d) (FullPaths : Set (ProbePath d)) :
    Set (ProbePoint d) :=
  interior {p : ProbePoint d | constantProbePath p ∈ realizedTailPathSet r θ FullPaths}

theorem realizedTailRegion_open {L d : Nat} (r : Nat)
    (θ : Params (L + 1) d) (FullPaths : Set (ProbePath d)) :
    IsOpen (realizedTailRegion r θ FullPaths) := by
  simp [realizedTailRegion]

theorem realizedTailRegion_constant_paths_available {L d r : Nat}
    {θ : Params (L + 1) d} {FullPaths : Set (ProbePath d)}
    {p : ProbePair d} (hp : p ∈ realizedTailRegion r θ FullPaths) :
    constantProbePath p ∈ realizedTailPathSet r θ FullPaths := by
  have hpInterior :
      p ∈ interior
        {q : ProbePoint d | constantProbePath q ∈ realizedTailPathSet r θ FullPaths} := by
    simpa [realizedTailRegion] using hp
  have hpSet :
      p ∈ {q : ProbePoint d | constantProbePath q ∈ realizedTailPathSet r θ FullPaths} :=
    (interior_subset :
      interior {q : ProbePoint d | constantProbePath q ∈ realizedTailPathSet r θ FullPaths} ⊆
        {q : ProbePoint d | constantProbePath q ∈ realizedTailPathSet r θ FullPaths})
      hpInterior
  exact hpSet

theorem firstLayerEffectivePoint_eq_anchorStep {d r : Nat}
    (V A : Matrix (Fin d) (Fin d) ℝ) (w v : Fin d -> ℝ) (τ : ℝ) :
    firstLayerEffectivePoint r V A w v τ =
      anchorStep (fun _ => (V, A)) 0 (firstLayerGate r A w v τ) (w, v) := by
  ext i <;>
    simp [firstLayerEffectivePoint, firstLayerDialPoint, anchorStep,
      anchorStepMatrix, skipB, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec]

/-- The fixed-gate first-layer dial map is the zero-th anchor step. -/
theorem firstLayerDialPoint_eq_anchorStep {d : Nat}
    (V A : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (p : ProbePoint d) :
    firstLayerDialPoint V t p.1 p.2 =
      anchorStep (fun _ => (V, A)) 0 t p := by
  ext i <;>
    simp [firstLayerDialPoint, anchorStep, anchorStepMatrix, skipB,
      Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec]

/-- A constant source path realizes the constant first-layer image whenever its first
gate is eventually constant. -/
noncomputable def constantSourceRealizationData_of_firstLayerGate_eq {d r : Nat}
    (V A : Matrix (Fin d) (Fin d) ℝ) (p : ProbePoint d) (t T : ℝ)
    (hT : 0 <= T)
    (hgate :
      ∀ τ : ℝ, T < τ -> firstLayerGate r A p.1 p.2 τ = t) :
    RealizationData r V A
      (constantProbePath (anchorStep (fun _ => (V, A)) 0 t p))
      (constantProbePath p) where
  threshold := T
  threshold_nonneg := hT
  effective_eq := by
    intro τ hτ
    rw [constantProbePath_apply, constantProbePath_apply,
      firstLayerEffectivePoint_eq_anchorStep, hgate τ hτ]

/-- If the first slope vanishes at a source probe, its constant path realizes the
constant image obtained with gate `sig (log r)`. -/
noncomputable def constantSourceRealizationData_of_slope_zero {d r : Nat}
    (V A : Matrix (Fin d) (Fin d) ℝ) (p : ProbePoint d)
    (hslope : matrixBilin A p.1 p.2 = 0) :
    RealizationData r V A
      (constantProbePath
        (anchorStep (fun _ => (V, A)) 0 (sig (Real.log (r : ℝ))) p))
      (constantProbePath p) :=
  constantSourceRealizationData_of_firstLayerGate_eq V A p
    (sig (Real.log (r : ℝ))) 0 (by norm_num) (by
      intro τ _hτ
      simp [firstLayerGate, hslope])

/-- A zero-first-coordinate constant tail target is realized by a constant source
whenever the first skip matrix is nonsingular.  This discharges the depth-one basis
targets in the top-level `Paths = Set.univ` case without using sweep geometry. -/
noncomputable def zeroFirstConstantRealizationData_of_firstSkip_det_ne_zero {d r : Nat}
    (V A : Matrix (Fin d) (Fin d) ℝ) (y : Fin d -> ℝ)
    (hdet : (skipB V).det ≠ 0) :
    RealizationData r V A
      (constantProbePath ((0 : Fin d -> ℝ), y))
      (constantProbePath ((0 : Fin d -> ℝ), ((skipB V)⁻¹).mulVec y)) := by
  let B : Matrix (Fin d) (Fin d) ℝ := skipB V
  have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr (by simpa [B] using hdet)
  letI : Invertible B := Matrix.invertibleOfIsUnitDet B hunit
  have hB_inv : B.mulVec ((B⁻¹).mulVec y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hskip : (skipB V).mulVec (((skipB V)⁻¹).mulVec y) = y := by
    simp [B]
  refine
    { threshold := 0
      threshold_nonneg := by norm_num
      effective_eq := ?_ }
  intro τ _hτ
  ext i
  · simp [firstLayerEffectivePoint, firstLayerDialPoint]
  · have hmat :
        (skipB V)⁻¹ + V * (skipB V)⁻¹ = (skipB V) * (skipB V)⁻¹ := by
      rw [skipB, Matrix.add_mul, Matrix.one_mul]
    have hskip_vec :
        ((skipB V)⁻¹).mulVec y + V.mulVec (((skipB V)⁻¹).mulVec y) = y := by
      calc
        ((skipB V)⁻¹).mulVec y + V.mulVec (((skipB V)⁻¹).mulVec y) =
            (((skipB V)⁻¹ + V * (skipB V)⁻¹).mulVec y) := by
          rw [Matrix.add_mulVec, Matrix.mulVec_mulVec]
        _ = (((skipB V) * (skipB V)⁻¹).mulVec y) := by
          rw [hmat]
        _ = y := by
          simp
    simpa [firstLayerEffectivePoint, firstLayerDialPoint] using congrFun hskip_vec i

theorem constant_anchorStep_mem_realizedTailPathSet_of_slope_zero
    {L d r : Nat} {θ : Params (L + 1) d}
    {FullPaths : Set (ProbePath d)} {p : ProbePoint d}
    (hp : constantProbePath p ∈ FullPaths)
    (hslope : matrixBilin (Params.headAttention θ) p.1 p.2 = 0) :
    constantProbePath
        (anchorStep (anchorParamStream θ) 0 (sig (Real.log (r : ℝ))) p) ∈
      realizedTailPathSet r θ FullPaths := by
  refine ⟨constantProbePath p, hp, ?_⟩
  refine ⟨?_⟩
  simpa [Params.headValue, Params.headAttention, Params.headLayer] using
    constantSourceRealizationData_of_slope_zero
      (r := r) (V := Params.headValue θ) (A := Params.headAttention θ) p hslope

/-- Pointwise algebraic preimage condition for realizing a constant tail probe by a
constant source path.

The source must lie on the zero first-slope quadric, so the first gate is eventually the
constant value `sig (log r)`, and the corresponding first-layer dial map must send the
source to the requested target.  This is the explicit missing algebraic/geometric
condition behind the stronger universal-region provider. -/
def FirstLayerSiglogConstantPreimageData {d : Nat} (r : Nat)
    (V A : Matrix (Fin d) (Fin d) ℝ) (target : ProbePoint d) : Prop :=
  ∃ source : ProbePoint d,
    matrixBilin A source.1 source.2 = 0 ∧
      anchorStep (fun _ => (V, A)) 0 (sig (Real.log (r : ℝ))) source = target

/-- The first-layer `sig(log r)` constant-source dial map realizes every constant tail
probe.  This is intentionally stronger than needed for an arbitrary local sweep region,
but it is the precise provider-side replacement for the old raw `all_realized` premise
when the desired swept region is `Set.univ`. -/
def FirstLayerSiglogConstantTailSurjective {d : Nat} (r : Nat)
    (V A : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ target : ProbePoint d, FirstLayerSiglogConstantPreimageData r V A target

/-- The constant gate used by zero-first-slope source probes. -/
noncomputable def firstLayerSiglogGate (r : Nat) : ℝ :=
  sig (Real.log (r : ℝ))

/-- First-layer anchor-step matrix at the zero-slope gate `sig(log r)`. -/
noncomputable def firstLayerSiglogAnchorStepMatrix {d : Nat} (r : Nat)
    (V : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  skipB V - firstLayerSiglogGate r • V

/-- The inverse candidate for a target probe under the `sig(log r)` first-layer anchor
step, assuming the two displayed matrices are invertible. -/
noncomputable def firstLayerSiglogInverseSource {d : Nat} (r : Nat)
    (V : Matrix (Fin d) (Fin d) ℝ) (target : ProbePoint d) : ProbePoint d :=
  let t : ℝ := firstLayerSiglogGate r
  let M : Matrix (Fin d) (Fin d) ℝ := firstLayerSiglogAnchorStepMatrix r V
  let w : Fin d -> ℝ := (M⁻¹).mulVec target.1
  (w, ((skipB V)⁻¹).mulVec (target.2 - t • (V.mulVec w)))

/-- The remaining algebraic condition for universal constant-tail realization when the
`sig(log r)` anchor step has the displayed inverse: every explicit inverse preimage lies
on the zero first-slope quadric. -/
def FirstLayerSiglogInverseZeroSlopeCondition {d : Nat} (r : Nat)
    (V A : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ target : ProbePoint d,
    matrixBilin A
      (firstLayerSiglogInverseSource r V target).1
      (firstLayerSiglogInverseSource r V target).2 = 0

theorem firstLayerSiglogAnchorStepMatrix_eq_anchorStepMatrix {d : Nat} (r : Nat)
    (V A : Matrix (Fin d) (Fin d) ℝ) :
    firstLayerSiglogAnchorStepMatrix r V =
      anchorStepMatrix (fun _ => (V, A)) 0 (firstLayerSiglogGate r) := by
  simp [firstLayerSiglogAnchorStepMatrix, anchorStepMatrix]

/-- The explicit inverse candidate maps back to its target under the `sig(log r)`
first-layer anchor step. -/
theorem anchorStep_firstLayerSiglogInverseSource {d : Nat} (r : Nat)
    (V A : Matrix (Fin d) (Fin d) ℝ) (target : ProbePoint d)
    (hM : (firstLayerSiglogAnchorStepMatrix r V).det ≠ 0)
    (hB : (skipB V).det ≠ 0) :
    anchorStep (fun _ => (V, A)) 0 (firstLayerSiglogGate r)
        (firstLayerSiglogInverseSource r V target) = target := by
  let t : ℝ := firstLayerSiglogGate r
  let M : Matrix (Fin d) (Fin d) ℝ := firstLayerSiglogAnchorStepMatrix r V
  let B : Matrix (Fin d) (Fin d) ℝ := skipB V
  have hunitM : IsUnit M.det := isUnit_iff_ne_zero.mpr (by simpa [M] using hM)
  letI : Invertible M := Matrix.invertibleOfIsUnitDet M hunitM
  have hunitB : IsUnit B.det := isUnit_iff_ne_zero.mpr (by simpa [B] using hB)
  letI : Invertible B := Matrix.invertibleOfIsUnitDet B hunitB
  let w : Fin d -> ℝ := (M⁻¹).mulVec target.1
  let y : Fin d -> ℝ := target.2 - t • (V.mulVec w)
  have hM_inv : M.mulVec w = target.1 := by
    change M.mulVec ((M⁻¹).mulVec target.1) = target.1
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hB_inv : B.mulVec ((B⁻¹).mulVec y) = y := by
    change
      B.mulVec ((B⁻¹).mulVec (target.2 - t • (V.mulVec w))) =
        target.2 - t • (V.mulVec w)
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hsecond : B.mulVec ((B⁻¹).mulVec y) + t • (V.mulVec w) = target.2 := by
    rw [hB_inv]
    change target.2 - t • (V.mulVec w) + t • (V.mulVec w) = target.2
    simp
  ext i
  · simpa [firstLayerSiglogInverseSource, firstLayerSiglogAnchorStepMatrix,
      anchorStep, anchorStepMatrix, t, M, w, B] using congrFun hM_inv i
  · simpa [firstLayerSiglogInverseSource, anchorStep, t, M, w, y, B] using
      congrFun hsecond i

/-- The explicit inverse candidate is also a right inverse on source probes for the
`sig(log r)` first-layer anchor step. -/
theorem firstLayerSiglogInverseSource_anchorStep {d : Nat} (r : Nat)
    (V A : Matrix (Fin d) (Fin d) ℝ) (source : ProbePoint d)
    (hM : (firstLayerSiglogAnchorStepMatrix r V).det ≠ 0)
    (hB : (skipB V).det ≠ 0) :
    firstLayerSiglogInverseSource r V
        (anchorStep (fun _ => (V, A)) 0 (firstLayerSiglogGate r) source) =
      source := by
  let t : ℝ := firstLayerSiglogGate r
  let M : Matrix (Fin d) (Fin d) ℝ := firstLayerSiglogAnchorStepMatrix r V
  let B : Matrix (Fin d) (Fin d) ℝ := skipB V
  have hunitM : IsUnit M.det := isUnit_iff_ne_zero.mpr (by simpa [M] using hM)
  letI : Invertible M := Matrix.invertibleOfIsUnitDet M hunitM
  have hunitB : IsUnit B.det := isUnit_iff_ne_zero.mpr (by simpa [B] using hB)
  letI : Invertible B := Matrix.invertibleOfIsUnitDet B hunitB
  have hfirst : (M⁻¹).mulVec (M.mulVec source.1) = source.1 := by
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  have hsecond :
      (B⁻¹).mulVec
          ((B.mulVec source.2 + t • (V.mulVec source.1)) -
            t • (V.mulVec source.1)) =
        source.2 := by
    rw [add_sub_cancel_right]
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  have hfirst' :
      ((firstLayerSiglogAnchorStepMatrix r V)⁻¹).mulVec
          (anchorStep (fun _ => (V, A)) 0 (firstLayerSiglogGate r) source).1 =
        source.1 := by
    simpa [anchorStep, anchorStepMatrix, firstLayerSiglogAnchorStepMatrix, t, M] using
      hfirst
  have hsecond' :
      ((skipB V)⁻¹).mulVec
          ((anchorStep (fun _ => (V, A)) 0 (firstLayerSiglogGate r) source).2 -
            firstLayerSiglogGate r •
              (V.mulVec
                (((firstLayerSiglogAnchorStepMatrix r V)⁻¹).mulVec
                  (anchorStep (fun _ => (V, A)) 0
                    (firstLayerSiglogGate r) source).1))) =
        source.2 := by
    rw [hfirst']
    simpa [anchorStep, t, B] using hsecond
  exact Prod.ext hfirst' hsecond'

/-- Under the same invertibility hypotheses used by the explicit inverse, the
inverse-zero-slope condition is equivalent to zero first-layer attention.  Thus the
universal constant-source inverse route cannot cover a genuinely nonzero attention
matrix. -/
theorem firstLayerSiglogInverseZeroSlopeCondition_iff_attention_eq_zero {d r : Nat}
    (V A : Matrix (Fin d) (Fin d) ℝ)
    (hM : (firstLayerSiglogAnchorStepMatrix r V).det ≠ 0)
    (hB : (skipB V).det ≠ 0) :
    FirstLayerSiglogInverseZeroSlopeCondition r V A ↔ A = 0 := by
  constructor
  · intro hzero
    apply matrix_eq_of_forall_bilin_eq
    intro w v
    let source : ProbePoint d := (w, v)
    have hz :
        matrixBilin A
          (firstLayerSiglogInverseSource r V
            (anchorStep (fun _ => (V, A)) 0 (firstLayerSiglogGate r) source)).1
          (firstLayerSiglogInverseSource r V
            (anchorStep (fun _ => (V, A)) 0 (firstLayerSiglogGate r) source)).2 = 0 :=
      hzero (anchorStep (fun _ => (V, A)) 0 (firstLayerSiglogGate r) source)
    have hinv :
        firstLayerSiglogInverseSource r V
            (anchorStep (fun _ => (V, A)) 0 (firstLayerSiglogGate r) source) =
          source :=
      firstLayerSiglogInverseSource_anchorStep r V A source hM hB
    have hAwv : matrixBilin A w v = 0 := by
      simpa [source, hinv] using hz
    simpa [matrixBilin] using hAwv
  · intro hA target
    simp [hA, matrixBilin]

/-- Contrapositive form of
`firstLayerSiglogInverseZeroSlopeCondition_iff_attention_eq_zero`, useful for exposing
the remaining nonzero-attention universal sweep obstruction. -/
theorem not_firstLayerSiglogInverseZeroSlopeCondition_of_attention_ne_zero {d r : Nat}
    (V A : Matrix (Fin d) (Fin d) ℝ)
    (hM : (firstLayerSiglogAnchorStepMatrix r V).det ≠ 0)
    (hB : (skipB V).det ≠ 0) (hA : A ≠ 0) :
    ¬ FirstLayerSiglogInverseZeroSlopeCondition r V A := by
  intro hzero
  exact hA ((firstLayerSiglogInverseZeroSlopeCondition_iff_attention_eq_zero
    V A hM hB).mp hzero)

/-- Under invertibility of the explicit `sig(log r)` first-layer anchor step, universal
constant-tail realization reduces to the inverse-zero-slope algebraic condition. -/
theorem firstLayerSiglogConstantPreimageData_of_inverse_zeroSlope {d r : Nat}
    (V A : Matrix (Fin d) (Fin d) ℝ) (target : ProbePoint d)
    (hM : (firstLayerSiglogAnchorStepMatrix r V).det ≠ 0)
    (hB : (skipB V).det ≠ 0)
    (hzero : FirstLayerSiglogInverseZeroSlopeCondition r V A) :
    FirstLayerSiglogConstantPreimageData r V A target := by
  refine ⟨firstLayerSiglogInverseSource r V target, hzero target, ?_⟩
  simpa [firstLayerSiglogGate] using
    anchorStep_firstLayerSiglogInverseSource r V A target hM hB

theorem firstLayerSiglogConstantTailSurjective_of_inverse_zeroSlope {d r : Nat}
    (V A : Matrix (Fin d) (Fin d) ℝ)
    (hM : (firstLayerSiglogAnchorStepMatrix r V).det ≠ 0)
    (hB : (skipB V).det ≠ 0)
    (hzero : FirstLayerSiglogInverseZeroSlopeCondition r V A) :
    FirstLayerSiglogConstantTailSurjective r V A := by
  intro target
  exact firstLayerSiglogConstantPreimageData_of_inverse_zeroSlope
    V A target hM hB hzero

/-- Degenerate-attention corollary of the inverse criterion.  For nonzero attention,
the inverse-zero-slope condition is the genuine remaining algebraic content. -/
theorem firstLayerSiglogConstantTailSurjective_of_attention_eq_zero {d r : Nat}
    (V A : Matrix (Fin d) (Fin d) ℝ)
    (hM : (firstLayerSiglogAnchorStepMatrix r V).det ≠ 0)
    (hB : (skipB V).det ≠ 0)
    (hA : A = 0) :
    FirstLayerSiglogConstantTailSurjective r V A := by
  refine firstLayerSiglogConstantTailSurjective_of_inverse_zeroSlope V A hM hB ?_
  intro target
  simp [matrixBilin, hA]

/-- With the explicit `sig(log r)` anchor step invertible, universal constant-tail
surjectivity by zero-slope constant sources is equivalent to zero attention.  Nonzero
attention therefore requires a genuinely nonconstant/local realization input rather
than this constant-source universal shortcut. -/
theorem firstLayerSiglogConstantTailSurjective_iff_attention_eq_zero {d r : Nat}
    (V A : Matrix (Fin d) (Fin d) ℝ)
    (hM : (firstLayerSiglogAnchorStepMatrix r V).det ≠ 0)
    (hB : (skipB V).det ≠ 0) :
    FirstLayerSiglogConstantTailSurjective r V A ↔ A = 0 := by
  constructor
  · intro hsurj
    apply matrix_eq_of_forall_bilin_eq
    intro w v
    let source : ProbePoint d := (w, v)
    let target : ProbePoint d :=
      anchorStep (fun _ => (V, A)) 0 (firstLayerSiglogGate r) source
    rcases hsurj target with ⟨pre, hslope, hmap⟩
    have hpre :
        pre = source := by
      have hmap' :
          anchorStep (fun _ => (V, A)) 0 (firstLayerSiglogGate r) pre = target := by
        simpa [firstLayerSiglogGate] using hmap
      calc
        pre =
            firstLayerSiglogInverseSource r V
              (anchorStep (fun _ => (V, A)) 0 (firstLayerSiglogGate r) pre) := by
          exact (firstLayerSiglogInverseSource_anchorStep r V A pre hM hB).symm
        _ = firstLayerSiglogInverseSource r V target := by
          rw [hmap']
        _ = source := by
          exact firstLayerSiglogInverseSource_anchorStep r V A source hM hB
    have hAwv : matrixBilin A w v = 0 := by
      simpa [source, hpre] using hslope
    simpa [matrixBilin] using hAwv
  · intro hA
    exact firstLayerSiglogConstantTailSurjective_of_attention_eq_zero V A hM hB hA

/-- Nonzero first-layer attention rules out universal constant-tail surjectivity by
zero-slope constant sources under the explicit invertibility hypotheses. -/
theorem not_firstLayerSiglogConstantTailSurjective_of_attention_ne_zero {d r : Nat}
    (V A : Matrix (Fin d) (Fin d) ℝ)
    (hM : (firstLayerSiglogAnchorStepMatrix r V).det ≠ 0)
    (hB : (skipB V).det ≠ 0) (hA : A ≠ 0) :
    ¬ FirstLayerSiglogConstantTailSurjective r V A := by
  intro hsurj
  exact hA ((firstLayerSiglogConstantTailSurjective_iff_attention_eq_zero
    V A hM hB).mp hsurj)

/-- Turn `sig(log r)` zero-slope preimage data into a concrete constant-source
realization. -/
noncomputable def constantSourceRealizationData_of_siglog_preimageData {d r : Nat}
    (V A : Matrix (Fin d) (Fin d) ℝ) (target : ProbePoint d)
    (P : FirstLayerSiglogConstantPreimageData r V A target) :
    ∃ source : ProbePath d,
      Nonempty (RealizationData r V A (constantProbePath target) source) := by
  rcases P with ⟨source, hslope, hmap⟩
  refine ⟨constantProbePath source, ?_⟩
  refine ⟨?_⟩
  simpa [hmap] using
    constantSourceRealizationData_of_slope_zero
      (r := r) (V := V) (A := A) source hslope

/-- A single `sig(log r)` zero-slope preimage gives membership in the realized tail path
set, provided the corresponding constant source path is available. -/
theorem constant_mem_realizedTailPathSet_of_siglog_preimageData
    {L d r : Nat} {θ : Params (L + 1) d}
    {FullPaths : Set (ProbePath d)} {target : ProbePoint d}
    (P : FirstLayerSiglogConstantPreimageData r
      (Params.headValue θ) (Params.headAttention θ) target)
    (hsource :
      ∀ source : ProbePoint d,
        matrixBilin (Params.headAttention θ) source.1 source.2 = 0 ->
        anchorStep (fun _ => (Params.headValue θ, Params.headAttention θ)) 0
            (sig (Real.log (r : ℝ))) source = target ->
        constantProbePath source ∈ FullPaths) :
    constantProbePath target ∈ realizedTailPathSet r θ FullPaths := by
  rcases P with ⟨source, hslope, hmap⟩
  refine ⟨constantProbePath source, hsource source hslope hmap, ?_⟩
  refine ⟨?_⟩
  simpa [Params.headValue, Params.headAttention, Params.headLayer, hmap] using
    constantSourceRealizationData_of_slope_zero
      (r := r) (V := Params.headValue θ) (A := Params.headAttention θ)
      source hslope

/-- Universal-path version of `constant_mem_realizedTailPathSet_of_siglog_preimageData`. -/
theorem constant_mem_realizedTailPathSet_of_paths_univ_of_siglog_preimageData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    {target : ProbePoint d}
    (P : FirstLayerSiglogConstantPreimageData r
      (Params.headValue θ) (Params.headAttention θ) target) :
    constantProbePath target ∈ realizedTailPathSet r θ D.Paths := by
  refine constant_mem_realizedTailPathSet_of_siglog_preimageData
    (θ := θ) (FullPaths := D.Paths) P ?_
  intro source _hslope _hmap
  rw [hPaths]
  exact Set.mem_univ _

/-- The corrected universal-region realization theorem: the old `∀ p` realized-tail
premise follows from explicit surjectivity of the zero-slope `sig(log r)` first-layer
dial map. -/
theorem allConstant_mem_realizedTailPathSet_of_paths_univ_of_siglog_surjective
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (hsurj : FirstLayerSiglogConstantTailSurjective r
      (Params.headValue θ) (Params.headAttention θ)) :
    ∀ p : ProbePoint d,
      constantProbePath p ∈ realizedTailPathSet r θ D.Paths := by
  intro p
  exact constant_mem_realizedTailPathSet_of_paths_univ_of_siglog_preimageData
    D hPaths (hsurj p)

theorem zeroFirstConstant_mem_realizedTailPathSet_of_firstSkip_det_ne_zero
    {L d r : Nat} {θ : Params (L + 1) d}
    {FullPaths : Set (ProbePath d)} (y : Fin d -> ℝ)
    (hdet : (skipB (Params.headValue θ)).det ≠ 0)
    (hsource :
      constantProbePath
          ((0 : Fin d -> ℝ), ((skipB (Params.headValue θ))⁻¹).mulVec y) ∈
        FullPaths) :
    constantProbePath ((0 : Fin d -> ℝ), y) ∈ realizedTailPathSet r θ FullPaths := by
  refine
    ⟨constantProbePath
        ((0 : Fin d -> ℝ), ((skipB (Params.headValue θ))⁻¹).mulVec y),
      hsource, ?_⟩
  refine ⟨?_⟩
  simpa [Params.headValue, Params.headAttention, Params.headLayer] using
    zeroFirstConstantRealizationData_of_firstSkip_det_ne_zero
      (r := r) (V := Params.headValue θ) (A := Params.headAttention θ) y hdet

theorem zeroFirstConstant_mem_realizedTailPathSet_of_paths_univ
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (y : Fin d -> ℝ) (hdet : (skipB (Params.headValue θ)).det ≠ 0) :
    constantProbePath ((0 : Fin d -> ℝ), y) ∈ realizedTailPathSet r θ D.Paths := by
  refine
    zeroFirstConstant_mem_realizedTailPathSet_of_firstSkip_det_ne_zero
      (θ := θ) (FullPaths := D.Paths) y hdet ?_
  rw [hPaths]
  exact Set.mem_univ _

theorem base_value_mem_realizedTailPathSet_of_paths_univ
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (j : Fin d) :
    constantProbePath ((0 : Fin d -> ℝ), Pi.single j (1 : ℝ)) ∈
      realizedTailPathSet r θ D.Paths :=
  zeroFirstConstant_mem_realizedTailPathSet_of_paths_univ D hPaths
    (Pi.single j (1 : ℝ)) (headValueSkip_det_ne_zero_of_matching hstep matching)

/-- Concrete condition needed to fill the depth-one basis realization clause after a
sweep: each basis target must already lie in the current realized-tail path class.

For arbitrary path classes this is the exact extra condition for the legacy
basis-probe route; the active local-open recursive route avoids this requirement. -/
def TexSweepDepthOneBasisRealizationCondition {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') : Prop :=
  L = 1 ->
    ∀ j : Fin d,
      constantProbePath ((0 : Fin d -> ℝ), Pi.single j (1 : ℝ)) ∈
        realizedTailPathSet r θ D.Paths

/-- Reduced depth-one basis input: the zero-first constant source paths needed by the
current first layer already belong to the current path class.

Once the current first skip matrix is nonsingular, these source paths mechanically
realize the basis targets in `realizedTailPathSet`.  For recursive swept path classes
this isolates the true remaining obstruction: membership of these source constants in
the previous path class. -/
def TexSweepDepthOneBasisSourcePathCondition {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') : Prop :=
  L = 1 ->
    ∀ j : Fin d,
      constantProbePath
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θ))⁻¹).mulVec (Pi.single j (1 : ℝ))) ∈
        D.Paths

/-- Unfold realized-tail membership into the explicit basis realization witness used by
the open-realization sweep interface. -/
theorem base_value_realized_of_mem_realizedTailPathSet
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {j : Fin d}
    (hmem :
      constantProbePath ((0 : Fin d -> ℝ), Pi.single j (1 : ℝ)) ∈
        realizedTailPathSet r θ D.Paths) :
    ∃ source : ProbePath d, source ∈ D.Paths ∧
      Nonempty (RealizationData r (Params.headValue θ) (Params.headAttention θ)
        (constantProbePath ((0 : Fin d -> ℝ), Pi.single j (1 : ℝ))) source) := by
  simpa [realizedTailPathSet] using hmem

/-- The realized-tail basis condition is exactly the explicit basis realization clause
used by arbitrary-path sweep constructors. -/
theorem base_value_realized_of_depthOneBasisRealizationCondition
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (B : TexSweepDepthOneBasisRealizationCondition D) :
    L = 1 ->
      ∀ j : Fin d,
        ∃ source : ProbePath d, source ∈ D.Paths ∧
          Nonempty (RealizationData r (Params.headValue θ) (Params.headAttention θ)
            (constantProbePath ((0 : Fin d -> ℝ), Pi.single j (1 : ℝ))) source) := by
  intro hL j
  exact base_value_realized_of_mem_realizedTailPathSet (B hL j)

/-- The explicit basis realization clause also packages back into realized-tail
membership, so no information is lost by using
`TexSweepDepthOneBasisRealizationCondition` as the arbitrary-path basis surface. -/
theorem depthOneBasisRealizationCondition_of_base_value_realized
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (base_value_realized :
      L = 1 ->
        ∀ j : Fin d,
          ∃ source : ProbePath d, source ∈ D.Paths ∧
            Nonempty (RealizationData r (Params.headValue θ) (Params.headAttention θ)
              (constantProbePath ((0 : Fin d -> ℝ), Pi.single j (1 : ℝ))) source)) :
    TexSweepDepthOneBasisRealizationCondition D := by
  intro hL j
  rcases base_value_realized hL j with ⟨source, hsource, hrealized⟩
  exact ⟨source, hsource, hrealized⟩

/-- The reduced source-path basis input implies the old realized-tail basis condition
once the current first skip matrix is nonsingular. -/
theorem depthOneBasisRealizationCondition_of_sourcePathCondition
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (hdet : (skipB (Params.headValue θ)).det ≠ 0)
    (B : TexSweepDepthOneBasisSourcePathCondition D) :
    TexSweepDepthOneBasisRealizationCondition D := by
  intro hL j
  exact
    zeroFirstConstant_mem_realizedTailPathSet_of_firstSkip_det_ne_zero
      (θ := θ) (FullPaths := D.Paths) (Pi.single j (1 : ℝ)) hdet (B hL j)

/-- In the universal-path case, the depth-one basis realization condition is mechanical
from the matched first skip matrix. -/
theorem depthOneBasisRealizationCondition_of_paths_univ
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ) :
    TexSweepDepthOneBasisRealizationCondition D := by
  intro _hL j
  exact base_value_mem_realizedTailPathSet_of_paths_univ hstep matching D hPaths j

/-- Away from the depth-one tail handoff, the basis realization condition is vacuous. -/
theorem depthOneBasisRealizationCondition_of_ne_one
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} (hL : L ≠ 1) :
    TexSweepDepthOneBasisRealizationCondition D := by
  intro hL'
  exact False.elim (hL hL')

/-- If the required zero-first source constants lie in the current open probe region,
then `IDLData.constant_paths_available` supplies the source-path basis condition. -/
theorem depthOneBasisSourcePathCondition_of_source_mem_open
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (source_mem_open :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θ))⁻¹).mulVec (Pi.single j (1 : ℝ))) ∈
            D.O) :
    TexSweepDepthOneBasisSourcePathCondition D := by
  intro hL j
  exact D.constant_paths_available _ (source_mem_open hL j)

/-- In the universal-path case, the source-path basis condition is immediate. -/
theorem depthOneBasisSourcePathCondition_of_paths_univ
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} (hPaths : D.Paths = Set.univ) :
    TexSweepDepthOneBasisSourcePathCondition D := by
  intro _hL _j
  rw [hPaths]
  exact Set.mem_univ _

/-- One-step swept-path reduction of the source-path basis input.

After rewriting the current path class as a `realizedTailPathSet`, source-path
membership reduces to the corresponding zero-first source constants in the previous
path class.  This is the formal version of the remaining genuine depth-one obstruction:
`hPaths` alone does not provide the final `FullPaths` membership premise. -/
theorem depthOneBasisSourcePathCondition_of_realizedTailPathSet
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    {D : IDLData (L + 1) d r θ θ'}
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem :
      L = 1 ->
        ∀ j : Fin d,
          constantProbePath
              ((0 : Fin d -> ℝ),
                ((skipB (Params.headValue θfull))⁻¹).mulVec
                  (((skipB (Params.headValue θ))⁻¹).mulVec
                    (Pi.single j (1 : ℝ)))) ∈
            FullPaths) :
    TexSweepDepthOneBasisSourcePathCondition D := by
  intro hL j
  rw [hPaths]
  exact
    zeroFirstConstant_mem_realizedTailPathSet_of_firstSkip_det_ne_zero
      (θ := θfull) (FullPaths := FullPaths)
      (((skipB (Params.headValue θ))⁻¹).mulVec (Pi.single j (1 : ℝ)))
      hdet_full (source_mem hL j)

/-- One-step swept-path reduction when the previous full path class is universal. -/
theorem depthOneBasisSourcePathCondition_of_realizedTailPathSet_of_fullPaths_univ
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    {D : IDLData (L + 1) d r θ θ'}
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (hFullPaths : FullPaths = Set.univ) :
    TexSweepDepthOneBasisSourcePathCondition D := by
  exact
    depthOneBasisSourcePathCondition_of_realizedTailPathSet
      (D := D) hPaths hdet_full (by
        intro _hL _j
        rw [hFullPaths]
        exact Set.mem_univ _)

/-- One-step swept-path reduction when the previous full path class is universal and the
previous first-skip determinant is supplied by matching a generic previous first layer. -/
theorem depthOneBasisSourcePathCondition_of_realizedTailPathSet_of_fullPaths_univ_matching
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    {D : IDLData (L + 1) d r θ θ'}
    (hstep_full :
      TexGenericStepClauses Lfull d (TexGeneric Lfull d)
        (fun η => TexAnchorCertificate η) θfull')
    (matching_full : FirstLayerMatchedData θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hFullPaths : FullPaths = Set.univ) :
    TexSweepDepthOneBasisSourcePathCondition D :=
  depthOneBasisSourcePathCondition_of_realizedTailPathSet_of_fullPaths_univ
    (D := D) hPaths
    (headValueSkip_det_ne_zero_of_matching hstep_full matching_full)
    hFullPaths

/-- One-step swept-path reduction discharged by the previous `IDLData` open region.

For recursive swept path classes, this is the concrete threading principle: after the
tail path equality rewrites `D.Paths` to a realized-tail path set, it is enough that the
double-inverse zero-first source points lie in the previous open set. -/
theorem depthOneBasisSourcePathCondition_of_realizedTailPathSet_of_source_mem_open
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem_open :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θfull))⁻¹).mulVec
              (((skipB (Params.headValue θ))⁻¹).mulVec
                (Pi.single j (1 : ℝ)))) ∈
            Dfull.O) :
    TexSweepDepthOneBasisSourcePathCondition D := by
  exact
    depthOneBasisSourcePathCondition_of_realizedTailPathSet
      (D := D) hPaths hdet_full (by
        intro hL j
        exact Dfull.constant_paths_available _ (source_mem_open hL j))

/-- Previous-open-set version where the previous first-skip determinant is supplied by
matching a generic previous first layer. -/
theorem depthOneBasisSourcePathCondition_of_realizedTailPathSet_of_source_mem_open_matching
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (hstep_full :
      TexGenericStepClauses Lfull d (TexGeneric Lfull d)
        (fun η => TexAnchorCertificate η) θfull')
    (matching_full : FirstLayerMatchedData θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (source_mem_open :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θfull))⁻¹).mulVec
              (((skipB (Params.headValue θ))⁻¹).mulVec
                (Pi.single j (1 : ℝ)))) ∈
            Dfull.O) :
    TexSweepDepthOneBasisSourcePathCondition D :=
  depthOneBasisSourcePathCondition_of_realizedTailPathSet_of_source_mem_open
    (D := D) Dfull hPaths
    (headValueSkip_det_ne_zero_of_matching hstep_full matching_full)
    source_mem_open

/-- Reduced basis input for recursive swept path classes.

Only the zero-first source constants are requested when the sweep produces a depth-one
tail.  The realization of the basis targets through the current first layer is then
mechanical from the current first-skip determinant.  In all higher tail depths the
condition is propositionally vacuous, so callers provide no data. -/
abbrev TexSweepDepthOneBasisRealizationInput {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') : Type :=
  if L = 1 then PLift (TexSweepDepthOneBasisSourcePathCondition D) else PUnit

/-- Package a source-path basis condition into the reduced conditional input expected by
the arbitrary-path sweep handoff.  Away from depth one the input carries no data. -/
def depthOneBasisRealizationInput_of_sourcePathCondition
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (B : TexSweepDepthOneBasisSourcePathCondition D) :
    TexSweepDepthOneBasisRealizationInput D := by
  by_cases hL : L = 1
  · simpa [TexSweepDepthOneBasisRealizationInput, hL] using (PLift.up B)
  · simpa [TexSweepDepthOneBasisRealizationInput, hL] using (PUnit.unit : PUnit)

/-- Source membership in the current open set gives the reduced depth-one basis input. -/
def depthOneBasisRealizationInput_of_source_mem_open
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (source_mem_open :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θ))⁻¹).mulVec (Pi.single j (1 : ℝ))) ∈
            D.O) :
    TexSweepDepthOneBasisRealizationInput D :=
  depthOneBasisRealizationInput_of_sourcePathCondition
    (depthOneBasisSourcePathCondition_of_source_mem_open source_mem_open)

/-- Universal paths give the reduced depth-one basis input directly. -/
def depthOneBasisRealizationInput_of_paths_univ
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} (hPaths : D.Paths = Set.univ) :
    TexSweepDepthOneBasisRealizationInput D :=
  depthOneBasisRealizationInput_of_sourcePathCondition
    (depthOneBasisSourcePathCondition_of_paths_univ (D := D) hPaths)

/-- One-step swept-path reduction for the reduced depth-one basis input. -/
def depthOneBasisRealizationInput_of_realizedTailPathSet
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    {D : IDLData (L + 1) d r θ θ'}
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem :
      L = 1 ->
        ∀ j : Fin d,
          constantProbePath
              ((0 : Fin d -> ℝ),
                ((skipB (Params.headValue θfull))⁻¹).mulVec
                  (((skipB (Params.headValue θ))⁻¹).mulVec
                    (Pi.single j (1 : ℝ)))) ∈
            FullPaths) :
    TexSweepDepthOneBasisRealizationInput D :=
  depthOneBasisRealizationInput_of_sourcePathCondition
    (depthOneBasisSourcePathCondition_of_realizedTailPathSet
      (D := D) hPaths hdet_full source_mem)

/-- One-step swept-path reduction for the reduced basis input when the previous full
path class is universal. -/
def depthOneBasisRealizationInput_of_realizedTailPathSet_of_fullPaths_univ
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    {D : IDLData (L + 1) d r θ θ'}
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (hFullPaths : FullPaths = Set.univ) :
    TexSweepDepthOneBasisRealizationInput D :=
  depthOneBasisRealizationInput_of_sourcePathCondition
    (depthOneBasisSourcePathCondition_of_realizedTailPathSet_of_fullPaths_univ
      (D := D) hPaths hdet_full hFullPaths)

/-- One-step swept-path reduction for the reduced basis input when the previous full
path class is universal and the previous determinant comes from matching. -/
def depthOneBasisRealizationInput_of_realizedTailPathSet_of_fullPaths_univ_matching
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    {D : IDLData (L + 1) d r θ θ'}
    (hstep_full :
      TexGenericStepClauses Lfull d (TexGeneric Lfull d)
        (fun η => TexAnchorCertificate η) θfull')
    (matching_full : FirstLayerMatchedData θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hFullPaths : FullPaths = Set.univ) :
    TexSweepDepthOneBasisRealizationInput D :=
  depthOneBasisRealizationInput_of_sourcePathCondition
    (depthOneBasisSourcePathCondition_of_realizedTailPathSet_of_fullPaths_univ_matching
      (D := D) hstep_full matching_full hPaths hFullPaths)

/-- One-step swept-path reduction for the reduced basis input discharged by the previous
`IDLData` open region. -/
def depthOneBasisRealizationInput_of_realizedTailPathSet_of_source_mem_open
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem_open :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θfull))⁻¹).mulVec
              (((skipB (Params.headValue θ))⁻¹).mulVec
                (Pi.single j (1 : ℝ)))) ∈
            Dfull.O) :
    TexSweepDepthOneBasisRealizationInput D :=
  depthOneBasisRealizationInput_of_sourcePathCondition
    (depthOneBasisSourcePathCondition_of_realizedTailPathSet_of_source_mem_open
      (D := D) Dfull hPaths hdet_full source_mem_open)

/-- One-step swept-path reduction for the reduced basis input discharged by the previous
open region, with the previous determinant supplied by matching. -/
def depthOneBasisRealizationInput_of_realizedTailPathSet_of_source_mem_open_matching
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (hstep_full :
      TexGenericStepClauses Lfull d (TexGeneric Lfull d)
        (fun η => TexAnchorCertificate η) θfull')
    (matching_full : FirstLayerMatchedData θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (source_mem_open :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θfull))⁻¹).mulVec
              (((skipB (Params.headValue θ))⁻¹).mulVec
                (Pi.single j (1 : ℝ)))) ∈
            Dfull.O) :
    TexSweepDepthOneBasisRealizationInput D :=
  depthOneBasisRealizationInput_of_sourcePathCondition
    (depthOneBasisSourcePathCondition_of_realizedTailPathSet_of_source_mem_open_matching
      (D := D) Dfull hstep_full matching_full hPaths source_mem_open)

/-- Realized-tail recursive reduction with the minimal remaining source-path
membership obligation.  This is just the conditional-input wrapper around
`depthOneBasisSourcePathCondition_of_realizedTailPathSet`: when the swept tail has
depth one, callers prove that the displayed zero-first source constants lie in the
previous full path class; otherwise the input is vacuous. -/
def depthOneBasisRealizationInput_of_realizedTailPathSet_sourcePath
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    {D : IDLData (L + 1) d r θ θ'}
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem :
      L = 1 ->
        ∀ j : Fin d,
          constantProbePath
              ((0 : Fin d -> ℝ),
                ((skipB (Params.headValue θfull))⁻¹).mulVec
                  (((skipB (Params.headValue θ))⁻¹).mulVec
                    (Pi.single j (1 : ℝ)))) ∈
            FullPaths) :
    TexSweepDepthOneBasisRealizationInput D :=
  depthOneBasisRealizationInput_of_realizedTailPathSet
    hPaths hdet_full source_mem

/-- Bundled form of the exact remaining depth-one source-path obligation after the
current path class has been rewritten as a one-step `realizedTailPathSet`.

The determinant is for the previous full first skip matrix.  At depth one, the source
paths are the displayed double-inverse zero-first constants in the previous full path
class; away from depth one this condition is vacuous. -/
structure TexSweepRealizedTailDepthOneBasisSourcePathData
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (θfull : Params (Lfull + 1) d)
    (FullPaths : Set (ProbePath d)) where
  paths_eq : D.Paths = realizedTailPathSet r θfull FullPaths
  det_full : (skipB (Params.headValue θfull)).det ≠ 0
  source_mem :
    L = 1 ->
      ∀ j : Fin d,
        constantProbePath
            ((0 : Fin d -> ℝ),
              ((skipB (Params.headValue θfull))⁻¹).mulVec
                (((skipB (Params.headValue θ))⁻¹).mulVec
                  (Pi.single j (1 : ℝ)))) ∈
          FullPaths

/-- Previous-open-set source wrapper for the realized-tail depth-one basis handoff.

This isolates the two facts needed to convert the displayed double-inverse zero-first
source constants into previous full paths: nonsingularity of the previous first skip
matrix, and membership of those source constants in the previous `IDLData` open set. -/
structure TexSweepRealizedTailDepthOneBasisSourceOpenData
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    {θfull θfull' : Params (Lfull + 1) d}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull') : Prop where
  det_full : (skipB (Params.headValue θfull)).det ≠ 0
  source_mem_open :
    L = 1 ->
      ∀ j : Fin d,
        ((0 : Fin d -> ℝ),
          ((skipB (Params.headValue θfull))⁻¹).mulVec
            (((skipB (Params.headValue θ))⁻¹).mulVec
              (Pi.single j (1 : ℝ)))) ∈
          Dfull.O

/-- Primitive constructor for the previous-open-set source wrapper. -/
def texSweepRealizedTailDepthOneBasisSourceOpenData_of_source_mem_open
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem_open :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θfull))⁻¹).mulVec
              (((skipB (Params.headValue θ))⁻¹).mulVec
                (Pi.single j (1 : ℝ)))) ∈
            Dfull.O) :
    TexSweepRealizedTailDepthOneBasisSourceOpenData D Dfull where
  det_full := hdet_full
  source_mem_open := source_mem_open

/-- Previous-open-set source wrapper with determinant supplied by matching the previous
full first layer. -/
def texSweepRealizedTailDepthOneBasisSourceOpenData_of_source_mem_open_matching
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (hstep_full :
      TexGenericStepClauses Lfull d (TexGeneric Lfull d)
        (fun η => TexAnchorCertificate η) θfull')
    (matching_full : FirstLayerMatchedData θfull θfull')
    (source_mem_open :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θfull))⁻¹).mulVec
              (((skipB (Params.headValue θ))⁻¹).mulVec
                (Pi.single j (1 : ℝ)))) ∈
            Dfull.O) :
    TexSweepRealizedTailDepthOneBasisSourceOpenData D Dfull where
  det_full := headValueSkip_det_ne_zero_of_matching hstep_full matching_full
  source_mem_open := source_mem_open

/-- Constructor spelling for the bundled realized-tail source-path frontier from its
three primitive fields. -/
def texSweepRealizedTailDepthOneBasisSourcePathData_of_realizedTailPathSet
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    {D : IDLData (L + 1) d r θ θ'}
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem :
      L = 1 ->
        ∀ j : Fin d,
          constantProbePath
              ((0 : Fin d -> ℝ),
                ((skipB (Params.headValue θfull))⁻¹).mulVec
                  (((skipB (Params.headValue θ))⁻¹).mulVec
                    (Pi.single j (1 : ℝ)))) ∈
            FullPaths) :
    TexSweepRealizedTailDepthOneBasisSourcePathData D θfull FullPaths where
  paths_eq := hPaths
  det_full := hdet_full
  source_mem := source_mem

/-- Lifted constructor spelling for the active recursive sweep provider field. -/
def texSweepRealizedTailDepthOneBasisSourcePathData_plift_of_realizedTailPathSet
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    {D : IDLData (L + 1) d r θ θ'}
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem :
      L = 1 ->
        ∀ j : Fin d,
          constantProbePath
              ((0 : Fin d -> ℝ),
                ((skipB (Params.headValue θfull))⁻¹).mulVec
                  (((skipB (Params.headValue θ))⁻¹).mulVec
                    (Pi.single j (1 : ℝ)))) ∈
            FullPaths) :
    PLift (TexSweepRealizedTailDepthOneBasisSourcePathData D θfull FullPaths) :=
  PLift.up
    (texSweepRealizedTailDepthOneBasisSourcePathData_of_realizedTailPathSet
      hPaths hdet_full source_mem)

/-- Away from depth-one tail handoff, the bundled realized-tail source-path frontier
only needs the path equality and previous first-skip determinant. -/
def texSweepRealizedTailDepthOneBasisSourcePathData_of_ne_one
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    {D : IDLData (L + 1) d r θ θ'}
    (hL : L ≠ 1)
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0) :
    TexSweepRealizedTailDepthOneBasisSourcePathData D θfull FullPaths :=
  texSweepRealizedTailDepthOneBasisSourcePathData_of_realizedTailPathSet
    hPaths hdet_full (by
      intro hL'
      exact False.elim (hL hL'))

/-- Lifted non-depth-one constructor for the active recursive sweep provider field. -/
def texSweepRealizedTailDepthOneBasisSourcePathData_plift_of_ne_one
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    {D : IDLData (L + 1) d r θ θ'}
    (hL : L ≠ 1)
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0) :
    PLift (TexSweepRealizedTailDepthOneBasisSourcePathData D θfull FullPaths) :=
  PLift.up
    (texSweepRealizedTailDepthOneBasisSourcePathData_of_ne_one
      hL hPaths hdet_full)

/-- If the previous full path class is universal, source-path membership in the
bundled realized-tail frontier is automatic. -/
def texSweepRealizedTailDepthOneBasisSourcePathData_of_fullPaths_univ
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    {D : IDLData (L + 1) d r θ θ'}
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (hFullPaths : FullPaths = Set.univ) :
    TexSweepRealizedTailDepthOneBasisSourcePathData D θfull FullPaths :=
  texSweepRealizedTailDepthOneBasisSourcePathData_of_realizedTailPathSet
    hPaths hdet_full (by
      intro _hL _j
      rw [hFullPaths]
      exact Set.mem_univ _)

/-- Lifted universal-previous-path constructor for the active recursive sweep provider
field. -/
def texSweepRealizedTailDepthOneBasisSourcePathData_plift_of_fullPaths_univ
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    {D : IDLData (L + 1) d r θ θ'}
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (hFullPaths : FullPaths = Set.univ) :
    PLift (TexSweepRealizedTailDepthOneBasisSourcePathData D θfull FullPaths) :=
  PLift.up
    (texSweepRealizedTailDepthOneBasisSourcePathData_of_fullPaths_univ
      hPaths hdet_full hFullPaths)

/-- If the previous first layer is already matched to a generic primed full parameter,
then the previous first-skip determinant in the source-path frontier is automatic. -/
def texSweepRealizedTailDepthOneBasisSourcePathData_of_fullPaths_univ_matching
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    {D : IDLData (L + 1) d r θ θ'}
    (hstep_full :
      TexGenericStepClauses Lfull d (TexGeneric Lfull d)
        (fun η => TexAnchorCertificate η) θfull')
    (matching_full : FirstLayerMatchedData θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hFullPaths : FullPaths = Set.univ) :
    TexSweepRealizedTailDepthOneBasisSourcePathData D θfull FullPaths :=
  texSweepRealizedTailDepthOneBasisSourcePathData_of_fullPaths_univ
    hPaths (headValueSkip_det_ne_zero_of_matching hstep_full matching_full) hFullPaths

/-- Lifted universal-previous-path constructor with determinant supplied by matching. -/
def texSweepRealizedTailDepthOneBasisSourcePathData_plift_of_fullPaths_univ_matching
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    {D : IDLData (L + 1) d r θ θ'}
    (hstep_full :
      TexGenericStepClauses Lfull d (TexGeneric Lfull d)
        (fun η => TexAnchorCertificate η) θfull')
    (matching_full : FirstLayerMatchedData θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hFullPaths : FullPaths = Set.univ) :
    PLift (TexSweepRealizedTailDepthOneBasisSourcePathData D θfull FullPaths) :=
  PLift.up
    (texSweepRealizedTailDepthOneBasisSourcePathData_of_fullPaths_univ_matching
      hstep_full matching_full hPaths hFullPaths)

/-- If the displayed double-inverse zero-first source probes lie in the previous
`IDLData` open set, `constant_paths_available` fills the source-path membership in the
bundled realized-tail frontier. -/
def texSweepRealizedTailDepthOneBasisSourcePathData_of_source_mem_open
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem_open :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θfull))⁻¹).mulVec
              (((skipB (Params.headValue θ))⁻¹).mulVec
                (Pi.single j (1 : ℝ)))) ∈
            Dfull.O) :
    TexSweepRealizedTailDepthOneBasisSourcePathData D θfull Dfull.Paths :=
  texSweepRealizedTailDepthOneBasisSourcePathData_of_realizedTailPathSet
    hPaths hdet_full (by
      intro hL j
      exact Dfull.constant_paths_available _ (source_mem_open hL j))

/-- Lifted previous-open-set constructor for the active recursive sweep provider field. -/
def texSweepRealizedTailDepthOneBasisSourcePathData_plift_of_source_mem_open
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem_open :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θfull))⁻¹).mulVec
              (((skipB (Params.headValue θ))⁻¹).mulVec
                (Pi.single j (1 : ℝ)))) ∈
            Dfull.O) :
    PLift (TexSweepRealizedTailDepthOneBasisSourcePathData D θfull Dfull.Paths) :=
  PLift.up
    (texSweepRealizedTailDepthOneBasisSourcePathData_of_source_mem_open
      Dfull hPaths hdet_full source_mem_open)

/-- Previous-open-set version with the previous first-skip determinant supplied by a
matched generic full first layer. -/
def texSweepRealizedTailDepthOneBasisSourcePathData_of_source_mem_open_matching
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (hstep_full :
      TexGenericStepClauses Lfull d (TexGeneric Lfull d)
        (fun η => TexAnchorCertificate η) θfull')
    (matching_full : FirstLayerMatchedData θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (source_mem_open :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θfull))⁻¹).mulVec
              (((skipB (Params.headValue θ))⁻¹).mulVec
                (Pi.single j (1 : ℝ)))) ∈
            Dfull.O) :
    TexSweepRealizedTailDepthOneBasisSourcePathData D θfull Dfull.Paths :=
  texSweepRealizedTailDepthOneBasisSourcePathData_of_source_mem_open Dfull hPaths
    (headValueSkip_det_ne_zero_of_matching hstep_full matching_full) source_mem_open

/-- Lifted previous-open-set constructor with determinant supplied by matching. -/
def texSweepRealizedTailDepthOneBasisSourcePathData_plift_of_source_mem_open_matching
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (hstep_full :
      TexGenericStepClauses Lfull d (TexGeneric Lfull d)
        (fun η => TexAnchorCertificate η) θfull')
    (matching_full : FirstLayerMatchedData θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (source_mem_open :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θfull))⁻¹).mulVec
              (((skipB (Params.headValue θ))⁻¹).mulVec
                (Pi.single j (1 : ℝ)))) ∈
            Dfull.O) :
    PLift (TexSweepRealizedTailDepthOneBasisSourcePathData D θfull Dfull.Paths) :=
  PLift.up
    (texSweepRealizedTailDepthOneBasisSourcePathData_of_source_mem_open_matching
      Dfull hstep_full matching_full hPaths source_mem_open)

/-- Compile the previous-open-set source wrapper to the existing realized-tail
source-path bundle. -/
def texSweepRealizedTailDepthOneBasisSourcePathData_of_sourceOpenData
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (S : TexSweepRealizedTailDepthOneBasisSourceOpenData D Dfull) :
    TexSweepRealizedTailDepthOneBasisSourcePathData D θfull Dfull.Paths :=
  texSweepRealizedTailDepthOneBasisSourcePathData_of_source_mem_open
    Dfull hPaths S.det_full S.source_mem_open

/-- Lifted compiler from the previous-open-set source wrapper to the active recursive
sweep provider field. -/
def texSweepRealizedTailDepthOneBasisSourcePathData_plift_of_sourceOpenData
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (S : TexSweepRealizedTailDepthOneBasisSourceOpenData D Dfull) :
    PLift (TexSweepRealizedTailDepthOneBasisSourcePathData D θfull Dfull.Paths) :=
  PLift.up
    (texSweepRealizedTailDepthOneBasisSourcePathData_of_sourceOpenData
      Dfull hPaths S)

/-- Previous-global-path compiler for recursive realized-tail source-path data.

When the previous `IDLData` path class is universal, the source-path membership is
automatic and the determinant is supplied by matching the previous first layer. -/
def texSweepRealizedTailDepthOneBasisSourcePathData_of_previous_IDLData_paths_univ_matching
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (hstep_full :
      TexGenericStepClauses Lfull d (TexGeneric Lfull d)
        (fun η => TexAnchorCertificate η) θfull')
    (matching_full : FirstLayerMatchedData θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (hFullPaths : Dfull.Paths = Set.univ) :
    TexSweepRealizedTailDepthOneBasisSourcePathData D θfull Dfull.Paths :=
  texSweepRealizedTailDepthOneBasisSourcePathData_of_fullPaths_univ_matching
    hstep_full matching_full hPaths hFullPaths

/-- Lifted previous-global-path compiler for the active recursive sweep provider field. -/
def texSweepRealizedTailDepthOneBasisSourcePathData_plift_of_previous_IDLData_paths_univ_matching
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (hstep_full :
      TexGenericStepClauses Lfull d (TexGeneric Lfull d)
        (fun η => TexAnchorCertificate η) θfull')
    (matching_full : FirstLayerMatchedData θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (hFullPaths : Dfull.Paths = Set.univ) :
    PLift (TexSweepRealizedTailDepthOneBasisSourcePathData D θfull Dfull.Paths) :=
  PLift.up
    (texSweepRealizedTailDepthOneBasisSourcePathData_of_previous_IDLData_paths_univ_matching
      Dfull hstep_full matching_full hPaths hFullPaths)

/-- The bundled realized-tail source-path obligation is exactly the data needed to
produce the reduced conditional depth-one basis input. -/
def depthOneBasisRealizationInput_of_realizedTailDepthOneBasisSourcePathData
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    {D : IDLData (L + 1) d r θ θ'}
    (S : TexSweepRealizedTailDepthOneBasisSourcePathData D θfull FullPaths) :
    TexSweepDepthOneBasisRealizationInput D :=
  depthOneBasisRealizationInput_of_realizedTailPathSet_sourcePath
    S.paths_eq S.det_full S.source_mem

/-- Recover the full realized-tail basis condition from the reduced conditional input
and the current first-skip determinant. -/
theorem depthOneBasisRealizationCondition_of_input
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (hdet : (skipB (Params.headValue θ)).det ≠ 0)
    (B : TexSweepDepthOneBasisRealizationInput D) :
    TexSweepDepthOneBasisRealizationCondition D := by
  classical
  by_cases hL : L = 1
  · have B' : PLift (TexSweepDepthOneBasisSourcePathCondition D) := by
      simpa [TexSweepDepthOneBasisRealizationInput, hL] using B
    exact depthOneBasisRealizationCondition_of_sourcePathCondition hdet B'.down
  · exact depthOneBasisRealizationCondition_of_ne_one hL

theorem anchorSlopeAt_zero_eq_matrixBilin_headAttention
    {L d : Nat} (θ : Params (L + 1) d) (t : Nat -> ℝ) (p : AnchorProbe d) :
    anchorSlopeAt (anchorParamStream θ) 0 t p =
      matrixBilin (Params.headAttention θ) p.1 p.2 := by
  simp [anchorSlopeAt, matrixBilin, Params.headAttention, Params.headLayer]

theorem firstLayerSlope_zero_of_unwoundAnchorSet
    {L d : Nat} (hL : 0 < L) {θ : Params (L + 1) d} {p : AnchorProbe d}
    (hp : p ∈ unwoundAnchorSet θ) :
    matrixBilin (Params.headAttention θ) p.1 p.2 = 0 := by
  rcases hp with ⟨W⟩
  have hzero : anchorSlopeAt (anchorParamStream θ) 0 W.t p = 0 :=
    W.slope_zero 0 (by omega)
  simpa [anchorSlopeAt_zero_eq_matrixBilin_headAttention] using hzero

theorem firstLayerSlope_zero_of_matched_unwoundAnchorSet
    {L d : Nat} (hL : 0 < L) {θ θ' : Params (L + 1) d}
    (matching : FirstLayerMatchedData θ θ') {p : AnchorProbe d}
    (hp : p ∈ unwoundAnchorSet θ') :
    matrixBilin (Params.headAttention θ) p.1 p.2 = 0 := by
  rw [matching.headAttention_eq]
  exact firstLayerSlope_zero_of_unwoundAnchorSet hL hp

/-- A full-depth anchor point lying in the current probe region gives an explicit
realized constant tail path, using only the available constant source path and first
layer matching.  This is the mechanical realization part of the sweep; it does not by
itself prove that such realized points contain an open neighbourhood. -/
theorem realizedTailPathSet_mem_siglog_anchorStep_of_anchor
    {L d r : Nat} (hL : 0 < L) {θ θ' : Params (L + 1) d}
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') {p : AnchorProbe d}
    (hpO : p ∈ D.O) (hpAnchor : p ∈ unwoundAnchorSet θ') :
    constantProbePath
        (anchorStep (anchorParamStream θ) 0 (sig (Real.log (r : ℝ))) p) ∈
      realizedTailPathSet r θ D.Paths :=
  constant_anchorStep_mem_realizedTailPathSet_of_slope_zero
    (D.constant_paths_available p hpO)
    (firstLayerSlope_zero_of_matched_unwoundAnchorSet hL matching hpAnchor)

theorem realizedTailPathSet_nonempty_of_IDL_anchor
    {L d r : Nat} (hL : 0 < L) {θ θ' : Params (L + 1) d}
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') :
    (realizedTailPathSet r θ D.Paths).Nonempty := by
  rcases D.anchor_nonempty with hdepth | hanchor
  · omega
  · rcases hanchor with ⟨p, hpO, hpAnchor⟩
    exact ⟨constantProbePath
        (anchorStep (anchorParamStream θ) 0 (sig (Real.log (r : ℝ))) p),
      realizedTailPathSet_mem_siglog_anchorStep_of_anchor hL matching D hpO hpAnchor⟩

/-- The tautological lift package for the path class defined by realizability. -/
def tailPathLiftData_of_realizedTailPathSet {L d r : Nat}
    {θ θ' : Params (L + 1) d} {FullPaths : Set (ProbePath d)}
    (matching : FirstLayerMatchedData θ θ') :
    TailPathLiftData r θ θ' FullPaths (realizedTailPathSet r θ FullPaths) where
  matching := matching
  realize := by
    intro target htarget
    exact htarget

/-- The analytic/geometric output of TeX Lemma `sweep` after defining the tail path class
by realizability.

The formalized mechanical part can derive the lift package from `realizedTailPathSet`.
This record is the remaining sweep interface: it supplies an explicit open set of
constant tail probes contained in the realized path class and the anchor handoff for the
primed tail. -/
structure TexSweepRegionData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') where
  U : Set (ProbePoint d)
  U_open : IsOpen U
  U_nonempty : U.Nonempty
  U_subset_realized :
    U ⊆ {p : ProbePoint d | constantProbePath p ∈ realizedTailPathSet r θ D.Paths}
  tail_anchor_nonempty :
    L = 1 ∨
      (U ∩ unwoundAnchorSet (Params.tail θ')).Nonempty

/-- Core geometric sweep region. -/
structure TexSweepRegionCoreData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') where
  U : Set (ProbePoint d)
  U_open : IsOpen U
  U_nonempty : U.Nonempty
  U_subset_realized :
    U ⊆ {p : ProbePoint d | constantProbePath p ∈ realizedTailPathSet r θ D.Paths}
  tail_anchor_nonempty :
    L = 1 ∨
      (U ∩ unwoundAnchorSet (Params.tail θ')).Nonempty

/-- Repackage a core sweep region as the main region record. -/
noncomputable def texSweepRegionData_of_regionCoreData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepRegionCoreData D) :
    TexSweepRegionData D where
  U := C.U
  U_open := C.U_open
  U_nonempty := C.U_nonempty
  U_subset_realized := C.U_subset_realized
  tail_anchor_nonempty := C.tail_anchor_nonempty

/-- Forget down to the region-core spelling. -/
def texSweepRegionCoreData_of_regionData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepRegionData D) :
    TexSweepRegionCoreData D where
  U := R.U
  U_open := R.U_open
  U_nonempty := R.U_nonempty
  U_subset_realized := R.U_subset_realized
  tail_anchor_nonempty := R.tail_anchor_nonempty

/-- Analytic local-realization input sufficient for the sweep interface.

This is the direct local-realization package: an open set of constant tail targets, each
realized by an available full-depth source path, plus the two TeX handoff clauses used by
the lower-depth induction. -/
structure TexSweepOpenRealizationData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') where
  U : Set (ProbePoint d)
  U_open : IsOpen U
  U_nonempty : U.Nonempty
  constant_tail_realized :
    ∀ p : ProbePoint d, p ∈ U ->
      ∃ source : ProbePath d, source ∈ D.Paths ∧
        Nonempty (RealizationData r (Params.headValue θ) (Params.headAttention θ)
          (constantProbePath p) source)
  tail_anchor_nonempty :
    L = 1 ∨
      (U ∩ unwoundAnchorSet (Params.tail θ')).Nonempty

/-- Local-realization input without the depth-one basis clause.

This is the path-class-local provider surface for the sweep geometry: it supplies an open
set of constant tail targets and, for each target in that set, an available full-depth
source path realizing it.  Recursive callers add the depth-one basis clause separately;
top-level `Paths = Set.univ` callers get that clause mechanically. -/
structure TexSweepLocalRealizationData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') where
  U : Set (ProbePoint d)
  U_open : IsOpen U
  U_nonempty : U.Nonempty
  constant_tail_realized :
    ∀ p : ProbePoint d, p ∈ U ->
      ∃ source : ProbePath d, source ∈ D.Paths ∧
        Nonempty (RealizationData r (Params.headValue θ) (Params.headAttention θ)
          (constantProbePath p) source)
  tail_anchor_nonempty :
    L = 1 ∨
      (U ∩ unwoundAnchorSet (Params.tail θ')).Nonempty

/-- Provider-facing local inverse-sweep package.

This isolates the hard analytic realization step: an external sweep construction supplies
the swept open set, one available source path for each swept constant tail target, the
corresponding first-layer realization witness, and the tail-anchor handoff. -/
structure TexSweepLocalInverseSweepProviderData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') where
  U : Set (ProbePoint d)
  U_open : IsOpen U
  U_nonempty : U.Nonempty
  source : ∀ η : ProbePoint d, η ∈ U -> ProbePath d
  source_mem_paths : ∀ η hη, source η hη ∈ D.Paths
  realized :
    ∀ η hη,
      Nonempty (RealizationData r (Params.headValue θ) (Params.headAttention θ)
        (constantProbePath η) (source η hη))
  tail_anchor_nonempty :
    L = 1 ∨
      (U ∩ unwoundAnchorSet (Params.tail θ')).Nonempty

/-- Forget the depth-one basis clause from a full open-realization package. -/
def texSweepLocalRealizationData_of_openRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepOpenRealizationData D) :
    TexSweepLocalRealizationData D where
  U := R.U
  U_open := R.U_open
  U_nonempty := R.U_nonempty
  constant_tail_realized := R.constant_tail_realized
  tail_anchor_nonempty := R.tail_anchor_nonempty

/-- Repackage a provider-facing local inverse-sweep witness as the downstream local
realization package used by the sweep handoff. -/
noncomputable def texSweepLocalRealizationData_of_localInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepLocalInverseSweepProviderData D) :
    TexSweepLocalRealizationData D where
  U := P.U
  U_open := P.U_open
  U_nonempty := P.U_nonempty
  constant_tail_realized := by
    intro η hη
    exact ⟨P.source η hη, P.source_mem_paths η hη, P.realized η hη⟩
  tail_anchor_nonempty := P.tail_anchor_nonempty

/-- Canonical-region sweep data after taking the interior of the pointwise realized
constant-tail targets.

The mechanical realization definitions already prove that every point in
`realizedTailRegion` has a realized constant tail path.  This package isolates the
remaining analytic sweep content for that canonical region: nonempty interior and the
tail-anchor handoff. -/
structure TexSweepRealizedTailRegionData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') : Prop where
  region_nonempty :
    (realizedTailRegion r θ D.Paths).Nonempty
  tail_anchor_nonempty :
    L = 1 ∨
      (realizedTailRegion r θ D.Paths ∩
        unwoundAnchorSet (Params.tail θ')).Nonempty

/-- Smallest currently exposed analytic support package for TeX Lemma `sweep`.

The fields after this package are mechanical in `IDLSweep`: an open set of constant
tail targets, realized by available full-depth paths, tightens to the canonical
`realizedTailRegion` by taking interiors.  The construction of `openRealization` is the
remaining inverse-function/sweep geometry from the TeX proof. -/
structure TexSweepAnalyticData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') : Type where
  openRealization : TexSweepOpenRealizationData D

/-- The canonical realized-tail region is a `TexSweepRegionData` once the remaining
nonemptiness, anchor, and basis clauses are supplied. -/
noncomputable def texSweepRegionData_of_realizedTailRegionData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepRealizedTailRegionData D) :
    TexSweepRegionData D where
  U := realizedTailRegion r θ D.Paths
  U_open := realizedTailRegion_open r θ D.Paths
  U_nonempty := R.region_nonempty
  U_subset_realized := by
    intro p hp
    exact realizedTailRegion_constant_paths_available hp
  tail_anchor_nonempty := R.tail_anchor_nonempty

/-- The canonical realized-tail region gives the core sweep region without needing the
depth-one basis-path clause. -/
noncomputable def texSweepRegionCoreData_of_realizedTailRegionData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepRealizedTailRegionData D) :
    TexSweepRegionCoreData D :=
  texSweepRegionCoreData_of_regionData
    (texSweepRegionData_of_realizedTailRegionData R)

/-- Any explicit sweep region can be tightened to the canonical realized-tail region,
because an open subset of the realized set is contained in its interior. -/
noncomputable def texSweepRealizedTailRegionData_of_regionData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepRegionData D) :
    TexSweepRealizedTailRegionData D := by
  classical
  have hU_interior :
      R.U ⊆ realizedTailRegion r θ D.Paths := by
    intro p hp
    simpa [realizedTailRegion] using
      (interior_maximal R.U_subset_realized R.U_open hp)
  refine
    { region_nonempty := ?_
      tail_anchor_nonempty := ?_ }
  · rcases R.U_nonempty with ⟨p, hp⟩
    exact ⟨p, hU_interior hp⟩
  · rcases R.tail_anchor_nonempty with hL | hanchor
    · exact Or.inl hL
    · rcases hanchor with ⟨p, hpU, hpAnchor⟩
      exact Or.inr ⟨p, hU_interior hpU, hpAnchor⟩

/-- Any open-realization package induces the canonical realized-tail-region package. -/
noncomputable def texSweepRealizedTailRegionData_of_openRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepOpenRealizationData D) :
    TexSweepRealizedTailRegionData D := by
  classical
  have hU_subset :
      R.U ⊆ {p : ProbePoint d |
        constantProbePath p ∈ realizedTailPathSet r θ D.Paths} := by
    intro p hp
    rcases R.constant_tail_realized p hp with ⟨source, hsource, hrealized⟩
    exact ⟨source, hsource, hrealized⟩
  have hU_interior :
      R.U ⊆ realizedTailRegion r θ D.Paths := by
    intro p hp
    simpa [realizedTailRegion] using
      (interior_maximal hU_subset R.U_open hp)
  refine
    { region_nonempty := ?_
      tail_anchor_nonempty := ?_ }
  · rcases R.U_nonempty with ⟨p, hp⟩
    exact ⟨p, hU_interior hp⟩
  · rcases R.tail_anchor_nonempty with hL | hanchor
    · exact Or.inl hL
    · rcases hanchor with ⟨p, hpU, hpAnchor⟩
      exact Or.inr ⟨p, hU_interior hpU, hpAnchor⟩
/-- Any local-realization package induces the canonical realized-tail-region package. -/
noncomputable def texSweepRealizedTailRegionData_of_localRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepLocalRealizationData D) :
    TexSweepRealizedTailRegionData D := by
  classical
  have hU_subset :
      R.U ⊆ {p : ProbePoint d |
        constantProbePath p ∈ realizedTailPathSet r θ D.Paths} := by
    intro p hp
    rcases R.constant_tail_realized p hp with ⟨source, hsource, hrealized⟩
    exact ⟨source, hsource, hrealized⟩
  have hU_interior :
      R.U ⊆ realizedTailRegion r θ D.Paths := by
    intro p hp
    simpa [realizedTailRegion] using
      (interior_maximal hU_subset R.U_open hp)
  refine
    { region_nonempty := ?_
      tail_anchor_nonempty := ?_ }
  · rcases R.U_nonempty with ⟨p, hp⟩
    exact ⟨p, hU_interior hp⟩
  · rcases R.tail_anchor_nonempty with hL | hanchor
    · exact Or.inl hL
    · rcases hanchor with ⟨p, hpU, hpAnchor⟩
      exact Or.inr ⟨p, hU_interior hpU, hpAnchor⟩

/-- The canonical realized-tail-region package is already an open-realization package:
membership in `realizedTailRegion` unfolds to pointwise realization, and the package
supplies the remaining handoff clauses. -/
noncomputable def texSweepOpenRealizationData_of_realizedTailRegionData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepRealizedTailRegionData D) :
    TexSweepOpenRealizationData D where
  U := realizedTailRegion r θ D.Paths
  U_open := realizedTailRegion_open r θ D.Paths
  U_nonempty := R.region_nonempty
  constant_tail_realized := by
    intro p hp
    simpa [realizedTailPathSet] using realizedTailRegion_constant_paths_available hp
  tail_anchor_nonempty := R.tail_anchor_nonempty

/-- Repackage a local-realization package as an open-realization package. -/
noncomputable def texSweepOpenRealizationData_of_localRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepLocalRealizationData D) :
    TexSweepOpenRealizationData D where
  U := R.U
  U_open := R.U_open
  U_nonempty := R.U_nonempty
  constant_tail_realized := R.constant_tail_realized
  tail_anchor_nonempty := R.tail_anchor_nonempty

/-- Repackage a provider-facing local inverse-sweep package as open-realization data. -/
noncomputable def texSweepOpenRealizationData_of_localInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepLocalInverseSweepProviderData D) :
    TexSweepOpenRealizationData D :=
  texSweepOpenRealizationData_of_localRealizationData
    (texSweepLocalRealizationData_of_localInverseSweepProviderData P)

/-- A region-level sweep package gives the open-realization package expected by the
current analytic interface. -/
noncomputable def texSweepOpenRealizationData_of_regionData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepRegionData D) :
    TexSweepOpenRealizationData D where
  U := R.U
  U_open := R.U_open
  U_nonempty := R.U_nonempty
  constant_tail_realized := by
    intro p hp
    simpa [realizedTailPathSet] using R.U_subset_realized hp
  tail_anchor_nonempty := R.tail_anchor_nonempty

/-- Any open-realization package gives the core sweep region.  This is useful for
arbitrary path classes, where the depth-one basis-path clause is intentionally supplied
separately. -/
noncomputable def texSweepRegionCoreData_of_openRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepOpenRealizationData D) :
    TexSweepRegionCoreData D where
  U := R.U
  U_open := R.U_open
  U_nonempty := R.U_nonempty
  U_subset_realized := by
    intro p hp
    rcases R.constant_tail_realized p hp with ⟨source, hsource, hrealized⟩
    exact ⟨source, hsource, hrealized⟩
  tail_anchor_nonempty := R.tail_anchor_nonempty

/-- Any local-realization package gives the core sweep region.  This is the narrow
recursive provider route before the depth-one basis clause is added. -/
noncomputable def texSweepRegionCoreData_of_localRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepLocalRealizationData D) :
    TexSweepRegionCoreData D where
  U := R.U
  U_open := R.U_open
  U_nonempty := R.U_nonempty
  U_subset_realized := by
    intro p hp
    rcases R.constant_tail_realized p hp with ⟨source, hsource, hrealized⟩
    exact ⟨source, hsource, hrealized⟩
  tail_anchor_nonempty := R.tail_anchor_nonempty

/-- Build the open local-realization package from an open set of `sig(log r)`
zero-slope preimages plus the path-class membership proof for those preimages.

This is the arbitrary-path-class local route: a geometric provider may prove preimage
data only on a selected open set `U`, not globally on all targets. -/
noncomputable def texSweepOpenRealizationData_of_siglog_preimageOpenSet
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (U : Set (ProbePoint d)) (U_open : IsOpen U) (U_nonempty : U.Nonempty)
    (preimage :
      ∀ p : ProbePoint d, p ∈ U ->
        FirstLayerSiglogConstantPreimageData r
          (Params.headValue θ) (Params.headAttention θ) p)
    (source_available :
      ∀ p : ProbePoint d, p ∈ U ->
        ∀ source : ProbePoint d,
          matrixBilin (Params.headAttention θ) source.1 source.2 = 0 ->
          anchorStep (fun _ => (Params.headValue θ, Params.headAttention θ)) 0
              (sig (Real.log (r : ℝ))) source = p ->
          constantProbePath source ∈ D.Paths)
    (tail_anchor_nonempty :
      L = 1 ∨
        (U ∩ unwoundAnchorSet (Params.tail θ')).Nonempty) :
    TexSweepOpenRealizationData D where
  U := U
  U_open := U_open
  U_nonempty := U_nonempty
  constant_tail_realized := by
    intro p hp
    rcases preimage p hp with ⟨source, hslope, hmap⟩
    refine ⟨constantProbePath source,
      source_available p hp source hslope hmap, ?_⟩
    refine ⟨?_⟩
    simpa [Params.headValue, Params.headAttention, Params.headLayer, hmap] using
      constantSourceRealizationData_of_slope_zero
        (r := r) (V := Params.headValue θ) (A := Params.headAttention θ)
        source hslope
  tail_anchor_nonempty := tail_anchor_nonempty

/-- Build the basis-free local-realization package from an open set of `sig(log r)`
zero-slope preimages plus path-class membership for those preimages. -/
noncomputable def texSweepLocalRealizationData_of_siglog_preimageOpenSet
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (U : Set (ProbePoint d)) (U_open : IsOpen U) (U_nonempty : U.Nonempty)
    (preimage :
      ∀ p : ProbePoint d, p ∈ U ->
        FirstLayerSiglogConstantPreimageData r
          (Params.headValue θ) (Params.headAttention θ) p)
    (source_available :
      ∀ p : ProbePoint d, p ∈ U ->
        ∀ source : ProbePoint d,
          matrixBilin (Params.headAttention θ) source.1 source.2 = 0 ->
          anchorStep (fun _ => (Params.headValue θ, Params.headAttention θ)) 0
              (sig (Real.log (r : ℝ))) source = p ->
          constantProbePath source ∈ D.Paths)
    (tail_anchor_nonempty :
      L = 1 ∨
        (U ∩ unwoundAnchorSet (Params.tail θ')).Nonempty) :
    TexSweepLocalRealizationData D where
  U := U
  U_open := U_open
  U_nonempty := U_nonempty
  constant_tail_realized := by
    intro p hp
    rcases preimage p hp with ⟨source, hslope, hmap⟩
    refine ⟨constantProbePath source,
      source_available p hp source hslope hmap, ?_⟩
    refine ⟨?_⟩
    simpa [Params.headValue, Params.headAttention, Params.headLayer, hmap] using
      constantSourceRealizationData_of_slope_zero
        (r := r) (V := Params.headValue θ) (A := Params.headAttention θ)
        source hslope
  tail_anchor_nonempty := tail_anchor_nonempty

/-- Direct core-region route from an open set of local `sig(log r)` zero-slope
preimages.  The depth-one basis-path clause remains outside the core package, matching
the arbitrary-path reduced sweep interface. -/
noncomputable def texSweepRegionCoreData_of_siglog_preimageOpenSet
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (U : Set (ProbePoint d)) (U_open : IsOpen U) (U_nonempty : U.Nonempty)
    (preimage :
      ∀ p : ProbePoint d, p ∈ U ->
        FirstLayerSiglogConstantPreimageData r
          (Params.headValue θ) (Params.headAttention θ) p)
    (source_available :
      ∀ p : ProbePoint d, p ∈ U ->
        ∀ source : ProbePoint d,
          matrixBilin (Params.headAttention θ) source.1 source.2 = 0 ->
          anchorStep (fun _ => (Params.headValue θ, Params.headAttention θ)) 0
              (sig (Real.log (r : ℝ))) source = p ->
          constantProbePath source ∈ D.Paths)
    (tail_anchor_nonempty :
      L = 1 ∨
        (U ∩ unwoundAnchorSet (Params.tail θ')).Nonempty) :
    TexSweepRegionCoreData D where
  U := U
  U_open := U_open
  U_nonempty := U_nonempty
  U_subset_realized := by
    intro p hp
    rcases preimage p hp with ⟨source, hslope, hmap⟩
    refine ⟨constantProbePath source,
      source_available p hp source hslope hmap, ?_⟩
    refine ⟨?_⟩
    simpa [Params.headValue, Params.headAttention, Params.headLayer, hmap] using
      constantSourceRealizationData_of_slope_zero
        (r := r) (V := Params.headValue θ) (A := Params.headAttention θ)
        source hslope
  tail_anchor_nonempty := tail_anchor_nonempty

/-- Package an explicit open-realization theorem as the analytic input expected by the
current sweep interface. -/
noncomputable def texSweepAnalyticData_of_openRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepOpenRealizationData D) :
    TexSweepAnalyticData hstep matching D where
  openRealization := R

/-- Package canonical realized-tail-region data as the analytic input expected by the
current sweep interface. -/
noncomputable def texSweepAnalyticData_of_realizedTailRegionData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepRealizedTailRegionData D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_openRealizationData hstep matching
    (texSweepOpenRealizationData_of_realizedTailRegionData R)

/-- Package a region-level sweep theorem as the analytic input expected by the current
sweep interface. -/
noncomputable def texSweepAnalyticData_of_regionData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepRegionData D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_openRealizationData hstep matching
    (texSweepOpenRealizationData_of_regionData R)

/-- Open-realization constructor from the core sweep region. -/
noncomputable def texSweepOpenRealizationData_of_regionCoreData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepRegionCoreData D) :
    TexSweepOpenRealizationData D :=
  texSweepOpenRealizationData_of_regionData
    (texSweepRegionData_of_regionCoreData C)

/-- Analytic constructor from the core sweep region. -/
noncomputable def texSweepAnalyticData_of_regionCoreData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepRegionCoreData D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_regionData hstep matching
    (texSweepRegionData_of_regionCoreData C)

/-- Analytic constructor from a local-realization package. -/
noncomputable def texSweepAnalyticData_of_localRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepLocalRealizationData D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_openRealizationData hstep matching
    (texSweepOpenRealizationData_of_localRealizationData R)

/-- Analytic constructor from a provider-facing local inverse-sweep package. -/
noncomputable def texSweepAnalyticData_of_localInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepLocalInverseSweepProviderData D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_localRealizationData hstep matching
    (texSweepLocalRealizationData_of_localInverseSweepProviderData P)

/-- Region-level top-level `Paths = Set.univ` constructor. -/
noncomputable def texSweepRegionData_of_paths_univ_regionCoreData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (C : TexSweepRegionCoreData D) :
    TexSweepRegionData D :=
  texSweepRegionData_of_regionCoreData C

/-- Open-realization top-level `Paths = Set.univ` constructor from the core geometric
sweep region. -/
noncomputable def texSweepOpenRealizationData_of_paths_univ_regionCoreData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (C : TexSweepRegionCoreData D) :
    TexSweepOpenRealizationData D :=
  texSweepOpenRealizationData_of_regionData
    (texSweepRegionData_of_paths_univ_regionCoreData hstep matching D hPaths C)

/-- Analytic top-level `Paths = Set.univ` constructor from the core geometric sweep
region. -/
noncomputable def texSweepAnalyticData_of_paths_univ_regionCoreData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (C : TexSweepRegionCoreData D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_regionData hstep matching
    (texSweepRegionData_of_paths_univ_regionCoreData hstep matching D hPaths C)

/-- Top-level `Paths = Set.univ` constructor from a local-realization package. -/
noncomputable def texSweepOpenRealizationData_of_paths_univ_localRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (R : TexSweepLocalRealizationData D) :
    TexSweepOpenRealizationData D :=
  texSweepOpenRealizationData_of_localRealizationData R

/-- Top-level `Paths = Set.univ` constructor from a provider-facing local inverse-sweep
package. -/
noncomputable def texSweepOpenRealizationData_of_paths_univ_localInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (P : TexSweepLocalInverseSweepProviderData D) :
    TexSweepOpenRealizationData D :=
  texSweepOpenRealizationData_of_paths_univ_localRealizationData
    hstep matching D hPaths
    (texSweepLocalRealizationData_of_localInverseSweepProviderData P)

/-- Top-level `Paths = Set.univ` constructor from a local-realization package, compiled
to the canonical realized-tail-region interface. -/
noncomputable def texSweepRealizedTailRegionData_of_paths_univ_localRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (R : TexSweepLocalRealizationData D) :
    TexSweepRealizedTailRegionData D :=
  texSweepRealizedTailRegionData_of_localRealizationData R

/-- Top-level universal-path analytic constructor from a local open realization, avoiding
the stronger universal all-constant-tail realization premise. -/
noncomputable def texSweepAnalyticData_of_paths_univ_localRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (R : TexSweepLocalRealizationData D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_openRealizationData hstep matching
    (texSweepOpenRealizationData_of_paths_univ_localRealizationData
      hstep matching D hPaths R)

/-- Top-level universal-path analytic constructor from a provider-facing local
inverse-sweep package. -/
noncomputable def texSweepAnalyticData_of_paths_univ_localInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (P : TexSweepLocalInverseSweepProviderData D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_paths_univ_localRealizationData
    hstep matching D hPaths
    (texSweepLocalRealizationData_of_localInverseSweepProviderData P)

/-- Top-level `Paths = Set.univ` constructor for canonical realized-tail-region data. -/
noncomputable def texSweepRealizedTailRegionData_of_paths_univ
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (region_nonempty : (realizedTailRegion r θ D.Paths).Nonempty)
    (tail_anchor_nonempty :
      L = 1 ∨
        (realizedTailRegion r θ D.Paths ∩
          unwoundAnchorSet (Params.tail θ')).Nonempty) :
    TexSweepRealizedTailRegionData D where
  region_nonempty := region_nonempty
  tail_anchor_nonempty := tail_anchor_nonempty

/-- Top-level `Paths = Set.univ` constructor for open-realization data. -/
noncomputable def texSweepOpenRealizationData_of_paths_univ
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (region_nonempty : (realizedTailRegion r θ D.Paths).Nonempty)
    (tail_anchor_nonempty :
      L = 1 ∨
        (realizedTailRegion r θ D.Paths ∩
          unwoundAnchorSet (Params.tail θ')).Nonempty) :
    TexSweepOpenRealizationData D :=
  texSweepOpenRealizationData_of_realizedTailRegionData
    (texSweepRealizedTailRegionData_of_paths_univ hstep matching D hPaths
      region_nonempty tail_anchor_nonempty)

/-- Top-level `Paths = Set.univ` constructor for the current analytic sweep interface.
The remaining analytic content is the canonical-region nonemptiness and anchor handoff. -/
noncomputable def texSweepAnalyticData_of_paths_univ
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (region_nonempty : (realizedTailRegion r θ D.Paths).Nonempty)
    (tail_anchor_nonempty :
      L = 1 ∨
        (realizedTailRegion r θ D.Paths ∩
          unwoundAnchorSet (Params.tail θ')).Nonempty) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_realizedTailRegionData hstep matching
    (texSweepRealizedTailRegionData_of_paths_univ hstep matching D hPaths
      region_nonempty tail_anchor_nonempty)

/-- Compile the explicit analytic sweep package to the canonical realized-tail region.

This is intentionally not a proof from `IDLData` alone: the TeX inverse-function
argument is represented by `S.openRealization`. -/
noncomputable def texSweepRealizedTailRegionData_of_IDLData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (S : TexSweepAnalyticData hstep matching D) :
    TexSweepRealizedTailRegionData D :=
  texSweepRealizedTailRegionData_of_openRealizationData S.openRealization

/-- Convert the local open-realization theorem into the sweep region data consumed by
the recursive IDL handoff. -/
noncomputable def texSweepRegionData_of_openRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepOpenRealizationData D) :
    TexSweepRegionData D where
  U := R.U
  U_open := R.U_open
  U_nonempty := R.U_nonempty
  U_subset_realized := by
    intro p hp
    rcases R.constant_tail_realized p hp with ⟨source, hsource, hrealized⟩
    exact ⟨source, hsource, hrealized⟩
  tail_anchor_nonempty := R.tail_anchor_nonempty

/-- Compile the explicit analytic sweep package to the explicit-region interface. -/
noncomputable def texSweepRegionData_of_IDLData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (S : TexSweepAnalyticData hstep matching D) :
    TexSweepRegionData D :=
  texSweepRegionData_of_openRealizationData S.openRealization

/-- TeX Step 3 sweep constructor.

Starting from a full-depth IDL datum whose probe region meets the primed unwound anchor
set, and after first-layer matching, the realization/sweep argument produces a lower-depth
open region and a class of tail paths.  The resulting `SweepData` packages the open swept
region, constant tail paths, anchor handoff, and realization lifts from each tail path back
to a full-depth path already available in `D.Paths`.

The open swept region is supplied explicitly by `R`; it is not obtained by taking the
interior of the pointwise realized set. -/
noncomputable def sweepData_of_texGenericStep
    {L d r : Nat} (_hd : 2 <= d) (_hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (_hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (R : TexSweepRegionData D) :
    Σ TailPaths : Set (ProbePath d), SweepData r θ θ' D.Paths TailPaths := by
  let TailPaths : Set (ProbePath d) := realizedTailPathSet r θ D.Paths
  exact
    ⟨TailPaths,
      { tailRegion := R.U
        tailRegion_open := R.U_open
        tailRegion_nonempty := R.U_nonempty
        tail_anchor_nonempty := R.tail_anchor_nonempty
        constant_paths_available := by
          intro p hp
          exact R.U_subset_realized hp
        lifts := tailPathLiftData_of_realizedTailPathSet matching }⟩

/-- Variant of `sweepData_of_texGenericStep` that takes the explicit open-realization
package and performs the mechanical conversion to `TexSweepRegionData`. -/
noncomputable def sweepData_of_texGenericStep_of_openRealizationData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (R : TexSweepOpenRealizationData D) :
    Σ TailPaths : Set (ProbePath d), SweepData r θ θ' D.Paths TailPaths :=
  sweepData_of_texGenericStep hd hr hstep matching D
    (texSweepRegionData_of_openRealizationData R)

/-- Canonical-realized-region form of the sweep constructor.  This avoids passing an
arbitrary open sweep region once the remaining canonical-region clauses have been proved. -/
noncomputable def sweepData_of_texGenericStep_of_realizedTailRegionData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (R : TexSweepRealizedTailRegionData D) :
    Σ TailPaths : Set (ProbePath d), SweepData r θ θ' D.Paths TailPaths :=
  sweepData_of_texGenericStep hd hr hstep matching D
    (texSweepRegionData_of_realizedTailRegionData R)

/-- Sweep constructor from the explicit analytic support package. -/
noncomputable def sweepData_of_texGenericStep_of_IDLData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (S : TexSweepAnalyticData hstep matching D) :
    Σ TailPaths : Set (ProbePath d), SweepData r θ θ' D.Paths TailPaths :=
  sweepData_of_texGenericStep_of_realizedTailRegionData hd hr hstep matching D
    (texSweepRealizedTailRegionData_of_IDLData hstep matching D S)

@[simp]
theorem anchorParamStream_tail_apply
    {L d : Nat} (θ : Params (L + 1) d) (n : Nat) :
    anchorParamStream (Params.tail θ) n = anchorParamStream θ (n + 1) := by
  by_cases hn : n < L
  · have hsucc : n + 1 < L + 1 := Nat.succ_lt_succ hn
    simp only [anchorParamStream, hn, hsucc, ↓reduceDIte]
    change θ (Fin.succ ⟨n, hn⟩) = θ ⟨n + 1, hsucc⟩
    rfl
  · have hsucc : ¬ n + 1 < L + 1 := by omega
    simp [anchorParamStream, hn, hsucc]

theorem anchorStep_tail_eq_shift
    {L d : Nat} (θ : Params (L + 1) d) (k : Nat) (t : ℝ)
    (p : AnchorProbe d) :
    anchorStep (anchorParamStream (Params.tail θ)) k t p =
      anchorStep (anchorParamStream θ) (k + 1) t p := by
  simp [anchorStep, anchorStepMatrix]

theorem anchorPath_tail_shift
    {L d : Nat} (θ : Params (L + 1) d) (g : Nat -> ℝ)
    (p : AnchorProbe d) :
    ∀ k : Nat,
      anchorPath (anchorParamStream (Params.tail θ)) k (fun n => g (n + 1))
          (anchorPath (anchorParamStream θ) 1 g p) =
        anchorPath (anchorParamStream θ) (k + 1) g p
  | 0 => rfl
  | k + 1 => by
      change
        anchorStep (anchorParamStream (Params.tail θ)) k (g (k + 1))
            (anchorPath (anchorParamStream (Params.tail θ)) k (fun n => g (n + 1))
              (anchorPath (anchorParamStream θ) 1 g p)) =
          anchorStep (anchorParamStream θ) (k + 1) (g (k + 1))
            (anchorPath (anchorParamStream θ) (k + 1) g p)
      rw [anchorStep_tail_eq_shift, anchorPath_tail_shift θ g p k]

theorem anchorPath_tail_shift_first_step
    {L d : Nat} (θ : Params (L + 1) d) (g : Nat -> ℝ)
    (p : AnchorProbe d) (k : Nat) :
    anchorPath (anchorParamStream (Params.tail θ)) k (fun n => g (n + 1))
        (anchorStep (anchorParamStream θ) 0 (g 0) p) =
      anchorPath (anchorParamStream θ) (k + 1) g p := by
  change
    anchorPath (anchorParamStream (Params.tail θ)) k (fun n => g (n + 1))
        (anchorPath (anchorParamStream θ) 1 g p) =
      anchorPath (anchorParamStream θ) (k + 1) g p
  exact anchorPath_tail_shift θ g p k

@[simp]
theorem anchorUnwindGate_tail_shift
    (t s : Nat -> ℝ) (k n : Nat) :
    anchorUnwindGate (fun m => t (m + 1)) (fun m => s (m + 1)) k n =
      anchorUnwindGate t s (k + 1) (n + 1) := by
  by_cases hn : n < k
  · have hsucc : n + 1 < k + 1 := Nat.succ_lt_succ hn
    simp [anchorUnwindGate, hn, hsucc]
  · by_cases hnk : n = k
    · subst hnk
      simp [anchorUnwindGate]
    · have hnot : ¬ n + 1 < k + 1 := by omega
      simp [anchorUnwindGate, hn, hnk, hnot]

theorem anchorSlopeAt_tail_shift
    {L d : Nat} (θ : Params (L + 1) d) (g : Nat -> ℝ)
    (p : AnchorProbe d) (k : Nat) :
    anchorSlopeAt (anchorParamStream (Params.tail θ)) k (fun n => g (n + 1))
        (anchorPath (anchorParamStream θ) 1 g p) =
      anchorSlopeAt (anchorParamStream θ) (k + 1) g p := by
  unfold anchorSlopeAt
  rw [anchorPath_tail_shift θ g p k, anchorParamStream_tail_apply]

theorem anchorSlopeAt_tail_shift_first_step
    {L d : Nat} (θ : Params (L + 1) d) (g : Nat -> ℝ)
    (p : AnchorProbe d) (k : Nat) :
    anchorSlopeAt (anchorParamStream (Params.tail θ)) k (fun n => g (n + 1))
        (anchorStep (anchorParamStream θ) 0 (g 0) p) =
      anchorSlopeAt (anchorParamStream θ) (k + 1) g p := by
  change
    anchorSlopeAt (anchorParamStream (Params.tail θ)) k (fun n => g (n + 1))
        (anchorPath (anchorParamStream θ) 1 g p) =
      anchorSlopeAt (anchorParamStream θ) (k + 1) g p
  exact anchorSlopeAt_tail_shift θ g p k

theorem anchorCovectorAt_tail_shift
    {L d : Nat} (θ : Params (L + 1) d) (g : Nat -> ℝ)
    (p : AnchorProbe d) (k : Nat) :
    anchorCovectorAt (anchorParamStream (Params.tail θ)) k (fun n => g (n + 1))
        (anchorPath (anchorParamStream θ) 1 g p) =
      anchorCovectorAt (anchorParamStream θ) (k + 1) g p := by
  unfold anchorCovectorAt
  rw [anchorPath_tail_shift θ g p k, anchorParamStream_tail_apply]

theorem anchorCovectorAt_tail_shift_first_step
    {L d : Nat} (θ : Params (L + 1) d) (g : Nat -> ℝ)
    (p : AnchorProbe d) (k : Nat) :
    anchorCovectorAt (anchorParamStream (Params.tail θ)) k (fun n => g (n + 1))
        (anchorStep (anchorParamStream θ) 0 (g 0) p) =
      anchorCovectorAt (anchorParamStream θ) (k + 1) g p := by
  change
    anchorCovectorAt (anchorParamStream (Params.tail θ)) k (fun n => g (n + 1))
        (anchorPath (anchorParamStream θ) 1 g p) =
      anchorCovectorAt (anchorParamStream θ) (k + 1) g p
  exact anchorCovectorAt_tail_shift θ g p k

theorem anchorStepMatrix_tail_shift
    {L d : Nat} (θ : Params (L + 1) d) (k : Nat) (t : ℝ) :
    anchorStepMatrix (anchorParamStream (Params.tail θ)) k t =
      anchorStepMatrix (anchorParamStream θ) (k + 1) t := by
  unfold anchorStepMatrix
  rw [anchorParamStream_tail_apply]

theorem anchorInverseScalarAt_tail_shift
    {L d : Nat} (θ : Params (L + 1) d) (g : Nat -> ℝ)
    (p : AnchorProbe d) (k : Nat) :
    anchorInverseScalarAt (anchorParamStream (Params.tail θ)) k (fun n => g (n + 1))
        (anchorPath (anchorParamStream θ) 1 g p) =
      anchorInverseScalarAt (anchorParamStream θ) (k + 1) g p := by
  unfold anchorInverseScalarAt
  rw [anchorCovectorAt_tail_shift, anchorPath_tail_shift θ g p k,
    anchorStepMatrix_tail_shift, anchorParamStream_tail_apply]

theorem anchorInverseScalarAt_tail_shift_first_step
    {L d : Nat} (θ : Params (L + 1) d) (g : Nat -> ℝ)
    (p : AnchorProbe d) (k : Nat) :
    anchorInverseScalarAt (anchorParamStream (Params.tail θ)) k (fun n => g (n + 1))
        (anchorStep (anchorParamStream θ) 0 (g 0) p) =
      anchorInverseScalarAt (anchorParamStream θ) (k + 1) g p := by
  change
    anchorInverseScalarAt (anchorParamStream (Params.tail θ)) k (fun n => g (n + 1))
        (anchorPath (anchorParamStream θ) 1 g p) =
      anchorInverseScalarAt (anchorParamStream θ) (k + 1) g p
  exact anchorInverseScalarAt_tail_shift θ g p k

theorem first_anchorPath_unwindGate_succ
    {d : Nat}
    (θs : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (t s : Nat -> ℝ) (k : Nat) (p : AnchorProbe d) :
    anchorPath θs 1 (anchorUnwindGate t s (k + 1)) p =
      anchorPath θs 1 t p := by
  simp [anchorUnwindGate]

theorem anchorSlopeAt_tail_shift_unwindGate
    {L d : Nat} (θ : Params (L + 1) d) (t s : Nat -> ℝ)
    (p : AnchorProbe d) (k ell : Nat) (hell : 2 <= ell) :
    anchorSlopeAt (anchorParamStream (Params.tail θ)) (k + ell - 1)
        (anchorUnwindGate (fun n => t (n + 1)) (fun n => s (n + 1)) k)
        (anchorPath (anchorParamStream θ) 1 t p) =
      anchorSlopeAt (anchorParamStream θ) (k + ell)
        (anchorUnwindGate t s (k + 1)) p := by
  let g := anchorUnwindGate t s (k + 1)
  have hstart :
      anchorPath (anchorParamStream θ) 1 t p =
        anchorPath (anchorParamStream θ) 1 g p := by
    exact (first_anchorPath_unwindGate_succ (anchorParamStream θ) t s k p).symm
  have hgate :
      anchorUnwindGate (fun n => t (n + 1)) (fun n => s (n + 1)) k =
        fun n => g (n + 1) := by
    funext n
    exact anchorUnwindGate_tail_shift t s k n
  have hidx : k + ell - 1 + 1 = k + ell := by omega
  rw [hstart, hgate]
  simpa [g, hidx] using anchorSlopeAt_tail_shift θ g p (k + ell - 1)

theorem anchorSlopeAt_tail_shift_unwindGate_first_step
    {L d : Nat} (θ : Params (L + 1) d) (t s : Nat -> ℝ)
    (p : AnchorProbe d) (k ell : Nat) (hell : 2 <= ell) :
    anchorSlopeAt (anchorParamStream (Params.tail θ)) (k + ell - 1)
        (anchorUnwindGate (fun n => t (n + 1)) (fun n => s (n + 1)) k)
        (anchorStep (anchorParamStream θ) 0 (t 0) p) =
      anchorSlopeAt (anchorParamStream θ) (k + ell)
        (anchorUnwindGate t s (k + 1)) p := by
  change
    anchorSlopeAt (anchorParamStream (Params.tail θ)) (k + ell - 1)
        (anchorUnwindGate (fun n => t (n + 1)) (fun n => s (n + 1)) k)
        (anchorPath (anchorParamStream θ) 1 t p) =
      anchorSlopeAt (anchorParamStream θ) (k + ell)
        (anchorUnwindGate t s (k + 1)) p
  exact anchorSlopeAt_tail_shift_unwindGate θ t s p k ell hell

/-- Formal tail transport for an unwound full-depth anchor.

This is the algebraic/unwinding portion of the Step 3 anchor handoff: once the sweep has
selected the first transported point, the remaining anchor clauses are exactly the
tail clauses with all gate streams shifted by one. -/
noncomputable def tailAnchorUnwindingData_of_full
    {L d : Nat} {θ : Params (L + 1) d} {p : AnchorProbe d}
    (W : AnchorUnwindingData θ p) :
    AnchorUnwindingData (Params.tail θ)
      (anchorPath (anchorParamStream θ) 1 W.t p) := by
  refine
    { t := fun n => W.t (n + 1)
      s := fun n => W.s (n + 1)
      t_mem_Ioo := ?_
      s_mem_Ioo := ?_
      slope_zero := ?_
      attention_image_ne_zero := ?_
      covector_ne_zero := ?_
      positive_later := ?_
      det_step_ne_zero := ?_
      inverse_scalar_ne_zero := ?_ }
  · intro k hk
    exact W.t_mem_Ioo (k + 1) (by omega)
  · intro k hk
    exact W.s_mem_Ioo (k + 1) (by omega)
  · intro k hk
    rw [anchorSlopeAt_tail_shift θ W.t p k]
    exact W.slope_zero (k + 1) (by omega)
  · intro k hk
    simpa [anchorPath_tail_shift_first_step θ W.t p k, anchorParamStream_tail_apply] using
      W.attention_image_ne_zero (k + 1) (by omega)
  · intro k hk
    rw [anchorCovectorAt_tail_shift θ W.t p k]
    exact W.covector_ne_zero (k + 1) (by omega)
  · intro k ell hk hell hell_le
    have hidx : k + 1 + ell - 1 = k + ell := by omega
    rw [anchorSlopeAt_tail_shift_unwindGate θ W.t W.s p k ell hell]
    simpa [hidx] using
      W.positive_later (k + 1) ell (by omega) hell (by omega)
  · intro k hk
    simpa [anchorStepMatrix_tail_shift θ k (W.t (k + 1))] using
      W.det_step_ne_zero (k + 1) (by omega)
  · intro k hk
    rw [anchorInverseScalarAt_tail_shift θ W.t p k]
    exact W.inverse_scalar_ne_zero (k + 1) (by omega)

theorem tail_unwoundAnchorSet_nonempty_of_full_anchor
    {L d : Nat} {θ : Params (L + 1) d} {p : AnchorProbe d}
    (hp : p ∈ unwoundAnchorSet θ) :
    (unwoundAnchorSet (Params.tail θ)).Nonempty := by
  rcases hp with ⟨W⟩
  exact ⟨anchorPath (anchorParamStream θ) 1 W.t p,
    ⟨tailAnchorUnwindingData_of_full W⟩⟩

theorem tail_anchor_nonempty_of_region_univ
    {L d : Nat} {θ : Params (L + 1) d}
    (hanchor : (unwoundAnchorSet θ).Nonempty) :
    (Set.univ ∩ unwoundAnchorSet (Params.tail θ)).Nonempty := by
  rcases hanchor with ⟨p, hp⟩
  rcases tail_unwoundAnchorSet_nonempty_of_full_anchor hp with ⟨ptail, hptail⟩
  exact ⟨ptail, by simp [hptail]⟩

theorem mem_unwoundAnchorSet_of_depth_le_one
    {L d : Nat} (θ : Params L d) (hL : L <= 1) (p : AnchorProbe d) :
    p ∈ unwoundAnchorSet θ := by
  refine ⟨?_⟩
  refine
    { t := fun _ => 0
      s := fun _ => 0
      t_mem_Ioo := ?_
      s_mem_Ioo := ?_
      slope_zero := ?_
      attention_image_ne_zero := ?_
      covector_ne_zero := ?_
      positive_later := ?_
      det_step_ne_zero := ?_
      inverse_scalar_ne_zero := ?_ }
  · intro k hk
    omega
  · intro k hk
    omega
  · intro k hk
    have : False := by omega
    exact False.elim this
  · intro k hk
    have : False := by omega
    exact False.elim this
  · intro k hk
    have : False := by omega
    exact False.elim this
  · intro k ell hk _hell _hle
    have : False := by omega
    exact False.elim this
  · intro k hk
    have : False := by omega
    exact False.elim this
  · intro k hk
    have : False := by omega
    exact False.elim this

theorem unwoundAnchorSet_nonempty_of_depth_le_one
    {L d : Nat} (θ : Params L d) (hL : L <= 1) :
    (unwoundAnchorSet θ).Nonempty := by
  exact ⟨(fun _ => 0, fun _ => 0),
    mem_unwoundAnchorSet_of_depth_le_one θ hL ((fun _ => 0), (fun _ => 0))⟩

/-- Point-level tail anchor data extracted before any inverse/sweep thickening.

This package records only the transported primed-tail anchor point.  It deliberately
does not assert that an analytic inverse construction realizes a neighborhood of it. -/
structure TexSweepAnchorPointData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') : Type where
  point : ProbePoint d
  point_mem_tail_anchor :
    point ∈ Set.univ ∩ unwoundAnchorSet (Params.tail θ')

/-- The tail anchor produced by transporting a full-depth unwound anchor through its
first anchor gate.  Unlike a free tail-set choice, this constructor keeps the source
point and gate available for the sweep IFT nonvanishing fields. -/
noncomputable def texSweepAnchorPointData_of_fullUnwoundAnchor
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') {p : AnchorProbe d}
    (W : AnchorUnwindingData θ' p) :
    TexSweepAnchorPointData D where
  point := anchorStep (anchorParamStream θ') 0 (W.t 0) p
  point_mem_tail_anchor := by
    refine ⟨Set.mem_univ _, ?_⟩
    exact ⟨tailAnchorUnwindingData_of_full W⟩

open Classical in
/-- A single full-depth unwound anchor chosen for `D` from `IDLData.anchor_nonempty`.

When the tail has positive depth (`L + 1 ≠ 1`), `anchor_nonempty` provides a point of
`D.O ∩ unwoundAnchorSet θ'`; its first component then lies in `D.O`
(`idlChosenFullAnchor_fst_mem_O`).  In the vacuous depth-one tail case there is no full
anchor to speak of, so a junk point is paired with the (vacuous) depth-`≤ 1` unwinding
data — the sweep never runs there.

This is the anchor the canonical sweep anchor `texSweepAnchorPointData_of_IDLData` is
*defined* to transport, so the full-anchor/canonical choice compatibility is definitional
(`texSweepFullAnchorChoiceCompatible_idlChosenFullAnchor`).  This realigns the canonical
anchor to the concrete transported anchor `Φ_{t}(p)` of the TeX proof, removing the need
for the (depth-one-false) tail-anchor uniqueness assumption. -/
noncomputable def idlChosenFullAnchor
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') :
    Σ p : AnchorProbe d, AnchorUnwindingData θ' p :=
  if h : (D.O ∩ unwoundAnchorSet θ').Nonempty then
    ⟨Classical.choose h,
      Classical.choice (mem_unwoundAnchorSet.mp (Classical.choose_spec h).2)⟩
  else
    ⟨((fun _ => 0), (fun _ => 0)),
      Classical.choice (mem_unwoundAnchorSet.mp
        (mem_unwoundAnchorSet_of_depth_le_one θ'
          (by have := D.anchor_nonempty.resolve_right h; omega)
          ((fun _ => 0), (fun _ => 0))))⟩

/-- The chosen full anchor's source point lies in `D.O` whenever the tail has positive
depth (so `IDLData.anchor_nonempty` supplies the geometric anchor disjunct). -/
theorem idlChosenFullAnchor_fst_mem_O
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (hanchor : (D.O ∩ unwoundAnchorSet θ').Nonempty) :
    (idlChosenFullAnchor D).1 ∈ D.O := by
  unfold idlChosenFullAnchor
  rw [dif_pos hanchor]
  exact (Classical.choose_spec hanchor).1

/-- Extract the canonical primed-tail anchor point from `IDLData`.

Realigned to transport the chosen full-depth unwound anchor `idlChosenFullAnchor D`
through its first anchor gate, so a realization centered at that full anchor lands exactly
on the canonical anchor.  (Previously this was an independent `Classical.choose` from the
whole tail-anchor set, which could only be matched to a concrete transported anchor under
the depth-one-false tail-anchor uniqueness hypothesis.) -/
noncomputable def texSweepAnchorPointData_of_IDLData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') :
    TexSweepAnchorPointData D :=
  texSweepAnchorPointData_of_fullUnwoundAnchor D (idlChosenFullAnchor D).2

/-- A tail anchor point chosen compatibly with a provider's swept set. -/
structure TexSweepProviderAnchorPointData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepLocalInverseSweepProviderData D) where
  anchor : TexSweepAnchorPointData D
  point_mem_provider : anchor.point ∈ P.U

/-- Choose an anchor point from a provider's swept set.

For non-depth-one tails this uses the provider's actual
`U ∩ unwoundAnchorSet (Params.tail θ')` witness.  In the `L = 1` handoff case the
provider is allowed to give only the left disjunct; then any point of `U` is already a
tail anchor because depth-one unwound anchor conditions are vacuous. -/
noncomputable def texSweepProviderAnchorPointData_of_localInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepLocalInverseSweepProviderData D) :
    TexSweepProviderAnchorPointData D P := by
  classical
  by_cases hL : L = 1
  · let p : ProbePoint d := Classical.choose P.U_nonempty
    have hpU : p ∈ P.U := Classical.choose_spec P.U_nonempty
    refine
      { anchor :=
          { point := p
            point_mem_tail_anchor := ?_ }
        point_mem_provider := hpU }
    have hpAnchor : p ∈ unwoundAnchorSet (Params.tail θ') := by
      exact mem_unwoundAnchorSet_of_depth_le_one (Params.tail θ') (by omega) p
    exact ⟨Set.mem_univ p, hpAnchor⟩
  · have hanchor : (P.U ∩ unwoundAnchorSet (Params.tail θ')).Nonempty :=
      P.tail_anchor_nonempty.resolve_left hL
    let p : ProbePoint d := Classical.choose hanchor
    have hp : p ∈ P.U ∩ unwoundAnchorSet (Params.tail θ') :=
      Classical.choose_spec hanchor
    refine
      { anchor :=
          { point := p
            point_mem_tail_anchor := ?_ }
        point_mem_provider := hp.1 }
    exact ⟨Set.mem_univ p, hp.2⟩

/-- The canonical `IDLData` anchor and the provider-selected anchor are choice-compatible
when their selected points agree. -/
noncomputable def TexSweepIDLAnchorChoiceCompatible {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepLocalInverseSweepProviderData D) : Prop :=
  (texSweepAnchorPointData_of_IDLData D).point =
    (texSweepProviderAnchorPointData_of_localInverseSweepProviderData P).anchor.point

/-- The primed tail has at most one unwound anchor point.  Under this condition, the
canonical `IDLData` choice must agree with any provider-selected tail anchor. -/
def TexSweepTailAnchorUnique {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (_D : IDLData (L + 1) d r θ θ') : Prop :=
  ∀ p q : ProbePoint d,
    p ∈ unwoundAnchorSet (Params.tail θ') ->
    q ∈ unwoundAnchorSet (Params.tail θ') ->
    p = q

/-- If the primed tail anchor is unique, a provider's anchor choice is automatically
compatible with the canonical `IDLData` anchor choice. -/
theorem texSweepIDLAnchorChoiceCompatible_of_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepLocalInverseSweepProviderData D)
    (hunique : TexSweepTailAnchorUnique D) :
    TexSweepIDLAnchorChoiceCompatible P := by
  apply hunique
  · exact (texSweepAnchorPointData_of_IDLData D).point_mem_tail_anchor.2
  · let A : TexSweepAnchorPointData D :=
      (texSweepProviderAnchorPointData_of_localInverseSweepProviderData P).anchor
    exact A.point_mem_tail_anchor.2

/-- A full-depth unwound anchor's first transported tail point agrees with the
canonical `IDLData` anchor choice whenever the primed tail anchor is unique. -/
theorem texSweepFullUnwoundAnchorPoint_eq_canonical_of_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (W : AnchorUnwindingData θ' p)
    (hunique : TexSweepTailAnchorUnique D) :
    (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point =
      (texSweepAnchorPointData_of_IDLData D).point := by
  apply hunique
  · exact (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point_mem_tail_anchor.2
  · exact (texSweepAnchorPointData_of_IDLData D).point_mem_tail_anchor.2

/-- At a depth-one tail, the unwound-anchor predicate is vacuous, so tail-anchor
uniqueness is false as soon as there is a coordinate in which two probes can differ.
This is why canonical-anchor sweep compilers below avoid threading
`TexSweepTailAnchorUnique` unless they explicitly retarget through a full-anchor choice. -/
theorem not_texSweepTailAnchorUnique_of_tail_depth_one
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (hL : L = 1) (hd : 0 < d) :
    ¬ TexSweepTailAnchorUnique D := by
  subst L
  let i : Fin d := ⟨0, hd⟩
  let p : ProbePoint d := ((fun _ => 0), (fun _ => 0))
  let q : ProbePoint d := ((fun _ => 0), Pi.single i (1 : ℝ))
  intro hunique
  have hp : p ∈ unwoundAnchorSet (Params.tail θ') :=
    mem_unwoundAnchorSet_of_depth_le_one (Params.tail θ') (by omega) p
  have hq : q ∈ unwoundAnchorSet (Params.tail θ') :=
    mem_unwoundAnchorSet_of_depth_le_one (Params.tail θ') (by omega) q
  have hpq : p = q := hunique p q hp hq
  have hcoord : (0 : ℝ) = 1 := by
    simpa [p, q, i] using congrFun (congrArg Prod.snd hpq) i
  norm_num at hcoord

/-- Canonical-anchor provider surface for the local inverse sweep.

This is narrower than `TexSweepLocalInverseSweepProviderData`: it requires the open
swept set to contain the canonical anchor selected from `IDLData`, so the tail-anchor
handoff becomes mechanical. -/
structure TexSweepCanonicalLocalInverseSweepProviderData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') where
  U : Set (ProbePoint d)
  U_open : IsOpen U
  anchor_mem : (texSweepAnchorPointData_of_IDLData D).point ∈ U
  source : ∀ η : ProbePoint d, η ∈ U -> ProbePath d
  source_mem_paths : ∀ η hη, source η hη ∈ D.Paths
  realized :
    ∀ η hη,
      Nonempty (RealizationData r (Params.headValue θ) (Params.headAttention θ)
        (constantProbePath η) (source η hη))

/-- Local inverse selector for the first-layer sweep map near the selected tail anchor.

This is the TeX `Ψ`-inverse part before adding the two independent checks needed by the
formal sweep handoff: each selected source path must belong to the current path class,
and the selected source path must realize the requested constant tail target. -/
structure TexSweepPsiLocalInverseNearAnchorData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (A : TexSweepAnchorPointData D) where
  U : Set (ProbePoint d)
  U_open : IsOpen U
  anchor_mem : A.point ∈ U
  source : ∀ η : ProbePoint d, η ∈ U -> ProbePath d

/-- The selected local inverse source paths are available in the current path class. -/
def TexSweepPsiLocalInverseSourcesAvailable {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (I : TexSweepPsiLocalInverseNearAnchorData D A) : Prop :=
  ∀ η hη, I.source η hη ∈ D.Paths

/-- The selected local inverse source paths realize the corresponding constant tail
targets through the matched first layer. -/
def TexSweepPsiLocalInverseRealizes {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (I : TexSweepPsiLocalInverseNearAnchorData D A) : Prop :=
  ∀ η hη,
    Nonempty (RealizationData r
      (Params.headValue θ) (Params.headAttention θ)
      (constantProbePath η) (I.source η hη))

/-- Bundled local `Ψ` inverse realization data.

The bundle stores the honest near-anchor realization theorem: an open neighborhood of
the selected anchor, and for each target in that neighborhood an available source path
realizing the corresponding constant tail.  The TeX-shaped source selector is derived
from this existential field by choice when a downstream compiler wants an explicit local
`Ψ` inverse. -/
structure TexSweepPsiLocalInverseRealizationData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (A : TexSweepAnchorPointData D) where
  U : Set (ProbePoint d)
  U_open : IsOpen U
  anchor_mem : A.point ∈ U
  constant_tail_realized :
    ∀ η : ProbePoint d, η ∈ U ->
      ∃ source : ProbePath d, source ∈ D.Paths ∧
        Nonempty (RealizationData r
          (Params.headValue θ) (Params.headAttention θ)
          (constantProbePath η) source)

/-- Canonical-anchor version of bundled local `Ψ` inverse realization data. -/
abbrev TexSweepCanonicalPsiLocalInverseRealizationData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') : Type :=
  TexSweepPsiLocalInverseRealizationData D (texSweepAnchorPointData_of_IDLData D)

/-- Forget the bundled realization proof, retaining the TeX-shaped local `Ψ` inverse
selector. -/
noncomputable def texSweepPsiLocalInverseNearAnchorData_of_localPsiInverseRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (R : TexSweepPsiLocalInverseRealizationData D A) :
    TexSweepPsiLocalInverseNearAnchorData D A where
  U := R.U
  U_open := R.U_open
  anchor_mem := R.anchor_mem
  source := fun η hη => Classical.choose (R.constant_tail_realized η hη)

/-- The bundled realization field proves source-path availability for the selector
extracted from the bundle. -/
theorem texSweepPsiLocalInverseSourcesAvailable_of_localPsiInverseRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (R : TexSweepPsiLocalInverseRealizationData D A) :
    TexSweepPsiLocalInverseSourcesAvailable
      (texSweepPsiLocalInverseNearAnchorData_of_localPsiInverseRealizationData R) := by
  intro η hη
  exact (Classical.choose_spec (R.constant_tail_realized η hη)).1

/-- The bundled realization field proves the existing local-`Ψ` realization predicate
for the selector extracted from the bundle. -/
theorem texSweepPsiLocalInverseRealizes_of_localPsiInverseRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (R : TexSweepPsiLocalInverseRealizationData D A) :
    TexSweepPsiLocalInverseRealizes
      (texSweepPsiLocalInverseNearAnchorData_of_localPsiInverseRealizationData R) := by
  intro η hη
  exact (Classical.choose_spec (R.constant_tail_realized η hη)).2

/-- The local analytic realization theorem needed by sweep, stated at the concrete
tail-anchor point extracted from `IDLData`.

This is the honest inverse/sweep obligation: an open neighborhood of the transported
primed-tail anchor is realized by available full-depth paths through the matched first
layer. -/
def TexSweepLocalRealizationNearAnchorPoint {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (A : TexSweepAnchorPointData D) : Prop :=
  ∃ U : Set (ProbePoint d),
    IsOpen U ∧ A.point ∈ U ∧
      ∀ η : ProbePoint d, η ∈ U ->
        ∃ source : ProbePath d, source ∈ D.Paths ∧
          Nonempty (RealizationData r
            (Params.headValue θ) (Params.headAttention θ)
            (constantProbePath η) source)

/-- The scalar `vartheta_0(w,v,t)` from the TeX sweep Jacobian computation:
`π(w,v)^T (B_1 - t V_1)^{-1} V_1 w`. -/
noncomputable def texSweepVartheta0 {d : Nat}
    (V A : Matrix (Fin d) (Fin d) ℝ) (p : ProbePoint d) (t : ℝ) : ℝ :=
  dotProduct (firstLayerPi A p)
    (((anchorStepMatrix (fun _ => (V, A)) 0 t)⁻¹).mulVec (V.mulVec p.1))

/-- The first zero-slope unwinding clause supplies the first-layer quadric equation
for the sweep source point. -/
theorem texSweepFirstLayerQuadric_of_anchorUnwindingData
    {L d : Nat} {θ : Params (L + 1) d} {p : AnchorProbe d}
    (W : AnchorUnwindingData θ p) (hL : 0 < L) :
    firstLayerQuadric (Params.headAttention θ) p := by
  have hzero : anchorSlopeAt (anchorParamStream θ) 0 W.t p = 0 :=
    W.slope_zero 0 (by omega)
  simpa [firstLayerQuadric, anchorSlopeAt, matrixBilin, Params.headAttention,
    Params.headLayer, anchorParamStream] using hzero

/-- The first nonzero-image and covector unwinding clauses supply first-layer
regularity for the sweep source point. -/
theorem texSweepFirstLayerRegular_of_anchorUnwindingData
    {L d : Nat} {θ : Params (L + 1) d} {p : AnchorProbe d}
    (W : AnchorUnwindingData θ p) (hL : 0 < L) :
    firstLayerRegular (Params.headAttention θ) p := by
  have hAwt := W.attention_image_ne_zero 0 (by omega)
  have hAwt' : (Matrix.transpose (Params.headAttention θ)).mulVec p.1 ≠ 0 := by
    simpa [Params.headAttention, Params.headLayer, anchorPath, anchorParamStream] using hAwt
  have hw_ne : p.1 ≠ 0 := by
    intro hw
    exact hAwt' (by simp [hw])
  have hcov := W.covector_ne_zero 0 (by omega)
  have hpi : firstLayerPi (Params.headAttention θ) p ≠ 0 := by
    simpa [firstLayerPi, anchorCovectorAt, Params.headAttention, Params.headLayer,
      anchorPath, anchorParamStream] using hcov
  exact ⟨hw_ne, hAwt', hpi⟩

/-- The TeX sweep scalar at the first anchor gate is the first inverse-scalar
unwinding clause. -/
theorem texSweepVartheta0_eq_anchorInverseScalarAt
    {L d : Nat} (θ : Params (L + 1) d) (t : Nat -> ℝ) (p : AnchorProbe d) :
    texSweepVartheta0 (Params.headValue θ) (Params.headAttention θ) p (t 0) =
      anchorInverseScalarAt (anchorParamStream θ) 0 t p := by
  simp [texSweepVartheta0, anchorInverseScalarAt, firstLayerPi, anchorCovectorAt,
    anchorPath, anchorStepMatrix, Params.headValue, Params.headAttention,
    Params.headLayer, anchorParamStream]

/-- The nonzero first inverse-scalar unwinding clause forces the first value image
`V_1 w` to be nonzero. -/
theorem texSweepValue_mul_source_w_ne_zero_of_anchorUnwindingData
    {L d : Nat} {θ : Params (L + 1) d} {p : AnchorProbe d}
    (W : AnchorUnwindingData θ p) (hL : 0 < L) :
    (Params.headValue θ).mulVec p.1 ≠ 0 := by
  intro hzero
  have hinv := W.inverse_scalar_ne_zero 0 (by omega)
  apply hinv
  simp [anchorInverseScalarAt, anchorPath, anchorParamStream, hzero]

/-- Local inverse-function-theorem sweep package at a specified tail anchor.

The nonzero fields are the concrete hypotheses of TeX Lemma `sweep` at the source
quadric point whose swept image is the selected tail anchor.  The `local_realization`
field is the remaining analytic IFT output: an open neighborhood of that selected
target anchor is realized by available full-depth source paths. -/
structure TexSweepLocalIFTData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (A : TexSweepAnchorPointData D) : Type where
  source_anchor : ProbePoint d
  gate : ℝ
  gate_pos : 0 < gate
  gate_lt_one : gate < 1
  source_mem_base : source_anchor ∈ D.O
  source_on_quadric :
    firstLayerQuadric (Params.headAttention θ) source_anchor
  source_regular :
    firstLayerRegular (Params.headAttention θ) source_anchor
  pi_ne_zero :
    firstLayerPi (Params.headAttention θ) source_anchor ≠ 0
  value_mul_source_w_ne_zero :
    (Params.headValue θ).mulVec source_anchor.1 ≠ 0
  det_first_skip_ne_zero :
    (skipB (Params.headValue θ)).det ≠ 0
  det_anchor_step_ne_zero :
    (anchorStepMatrix
      (fun _ => (Params.headValue θ, Params.headAttention θ)) 0 gate).det ≠ 0
  vartheta0_ne_zero :
    texSweepVartheta0 (Params.headValue θ) (Params.headAttention θ)
      source_anchor gate ≠ 0
  swept_anchor_eq :
    firstLayerDialPoint (Params.headValue θ) gate source_anchor.1 source_anchor.2 =
      A.point
  local_realization :
    TexSweepLocalRealizationNearAnchorPoint D A

/-- Canonical-anchor sweep frontier reduced to the genuinely missing local realization
theorem.

The pointwise IFT witnesses at a full unwound anchor are derivable from `IDLData`,
genericity, and matching.  Current downstream sweep handoffs only need the realized
neighborhood of the canonical tail anchor, so the canonical field keeps exactly that
local theorem and no point/gate witnesses. -/
structure TexSweepCanonicalIFTData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') : Type where
  local_realization :
    TexSweepLocalRealizationNearAnchorPoint D
      (texSweepAnchorPointData_of_IDLData D)

/-- Package the reduced canonical sweep frontier directly from the canonical
near-anchor realization theorem. -/
noncomputable def texSweepCanonicalIFTData_of_nearAnchorPoint
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D)) :
    TexSweepCanonicalIFTData D where
  local_realization := hnear

/-- Concrete source surface for the reduced canonical near-anchor frontier.

This is the same local realization theorem as `TexSweepCanonicalIFTData`, but exposed
with open-neighborhood fields so downstream providers can fill the analytic sweep
content without constructing the raw existential proposition directly. -/
structure TexSweepCanonicalNearAnchorLocalRealizationData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') where
  U : Set (ProbePoint d)
  U_open : IsOpen U
  anchor_mem : (texSweepAnchorPointData_of_IDLData D).point ∈ U
  constant_tail_realized :
    ∀ η : ProbePoint d, η ∈ U ->
      ∃ source : ProbePath d, source ∈ D.Paths ∧
        Nonempty (RealizationData r
          (Params.headValue θ) (Params.headAttention θ)
          (constantProbePath η) source)

/-- The concrete canonical near-anchor source surface proves the raw near-anchor local
realization theorem. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_canonicalNearAnchorLocalRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepCanonicalNearAnchorLocalRealizationData D) :
    TexSweepLocalRealizationNearAnchorPoint D
      (texSweepAnchorPointData_of_IDLData D) :=
  ⟨R.U, R.U_open, R.anchor_mem, R.constant_tail_realized⟩

/-- Compile the concrete canonical near-anchor source surface to the reduced canonical
IFT frontier. -/
noncomputable def texSweepCanonicalIFTData_of_canonicalNearAnchorLocalRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepCanonicalNearAnchorLocalRealizationData D) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_nearAnchorPoint D
    (texSweepLocalRealizationNearAnchorPoint_of_canonicalNearAnchorLocalRealizationData R)

/-- Package an existing canonical near-anchor realization theorem as the concrete
source surface consumed by the reduced canonical IFT compiler. -/
noncomputable def texSweepCanonicalNearAnchorLocalRealizationData_of_nearAnchorPoint
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D)) :
    TexSweepCanonicalNearAnchorLocalRealizationData D := by
  classical
  let U : Set (ProbePoint d) := Classical.choose hnear
  have hU :
      IsOpen U ∧ (texSweepAnchorPointData_of_IDLData D).point ∈ U ∧
        ∀ η : ProbePoint d, η ∈ U ->
          ∃ source : ProbePath d, source ∈ D.Paths ∧
            Nonempty (RealizationData r
              (Params.headValue θ) (Params.headAttention θ)
              (constantProbePath η) source) :=
    Classical.choose_spec hnear
  exact
    { U := U
      U_open := hU.1
      anchor_mem := hU.2.1
      constant_tail_realized := hU.2.2 }

/-- Bundled local `Ψ` realization data at the canonical `IDLData` anchor is exactly the
concrete canonical near-anchor source surface. -/
noncomputable def
    texSweepCanonicalNearAnchorLocalRealizationData_of_localPsiInverseRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepCanonicalPsiLocalInverseRealizationData D) :
    TexSweepCanonicalNearAnchorLocalRealizationData D where
  U := R.U
  U_open := R.U_open
  anchor_mem := R.anchor_mem
  constant_tail_realized := R.constant_tail_realized

/-- Bundled local `Ψ` realization data at an explicitly compatible anchor retargets to
the concrete canonical near-anchor source surface. -/
noncomputable def
    texSweepCanonicalNearAnchorLocalRealizationData_of_localPsiInverseRealizationData_anchorPointEq
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (R : TexSweepPsiLocalInverseRealizationData D A)
    (hA : A.point = (texSweepAnchorPointData_of_IDLData D).point) :
    TexSweepCanonicalNearAnchorLocalRealizationData D where
  U := R.U
  U_open := R.U_open
  anchor_mem := by
    rw [← hA]
    exact R.anchor_mem
  constant_tail_realized := R.constant_tail_realized

/-- Existing local-realization data is a canonical near-anchor source surface exactly
when its swept open set contains the canonical anchor. -/
def texSweepCanonicalNearAnchorLocalRealizationData_of_localRealizationData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepLocalRealizationData D)
    (hA : (texSweepAnchorPointData_of_IDLData D).point ∈ R.U) :
    TexSweepCanonicalNearAnchorLocalRealizationData D where
  U := R.U
  U_open := R.U_open
  anchor_mem := hA
  constant_tail_realized := R.constant_tail_realized

/-- Existing open-realization data is a canonical near-anchor source surface exactly
when its swept open set contains the canonical anchor. -/
def texSweepCanonicalNearAnchorLocalRealizationData_of_openRealizationData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepOpenRealizationData D)
    (hA : (texSweepAnchorPointData_of_IDLData D).point ∈ R.U) :
    TexSweepCanonicalNearAnchorLocalRealizationData D :=
  texSweepCanonicalNearAnchorLocalRealizationData_of_localRealizationData_mem
    (texSweepLocalRealizationData_of_openRealizationData R) hA

/-- Provider-facing local inverse-sweep data becomes a canonical near-anchor source
surface once the canonical anchor is known to lie in the provider neighborhood. -/
noncomputable def
    texSweepCanonicalNearAnchorLocalRealizationData_of_localInverseSweepProviderData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepLocalInverseSweepProviderData D)
    (hA : (texSweepAnchorPointData_of_IDLData D).point ∈ P.U) :
    TexSweepCanonicalNearAnchorLocalRealizationData D where
  U := P.U
  U_open := P.U_open
  anchor_mem := hA
  constant_tail_realized := by
    intro η hη
    exact ⟨P.source η hη, P.source_mem_paths η hη, P.realized η hη⟩

/-- A provider-facing local inverse-sweep package becomes a canonical near-anchor
source surface when its selected anchor is explicitly compatible with the canonical
`IDLData` anchor choice. -/
noncomputable def
texSweepCanonicalNearAnchorLocalRealizationData_of_localInverseSweepProviderData_choiceCompatible
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepLocalInverseSweepProviderData D)
    (hcompat : TexSweepIDLAnchorChoiceCompatible P) :
    TexSweepCanonicalNearAnchorLocalRealizationData D :=
  texSweepCanonicalNearAnchorLocalRealizationData_of_localInverseSweepProviderData_mem P
    (by
      rw [hcompat]
      exact
        (texSweepProviderAnchorPointData_of_localInverseSweepProviderData P).point_mem_provider)

/-- A canonical-anchor local inverse-sweep provider has exactly the fields needed for
the concrete canonical near-anchor source surface. -/
noncomputable def
    texSweepCanonicalNearAnchorLocalRealizationData_of_canonicalLocalInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepCanonicalLocalInverseSweepProviderData D) :
    TexSweepCanonicalNearAnchorLocalRealizationData D where
  U := C.U
  U_open := C.U_open
  anchor_mem := C.anchor_mem
  constant_tail_realized := by
    intro η hη
    exact ⟨C.source η hη, C.source_mem_paths η hη, C.realized η hη⟩

/-- One-step swept-path reduction discharged directly by a previous local realization
neighborhood.

This is separate from `TexSweepRealizedTailDepthOneBasisSourcePathData`: instead of
using the previous first-skip inverse to build a constant source path, it uses the
previous sweep package to realize the required single-inverse depth-one tail targets by
some available previous full path. -/
theorem depthOneBasisSourcePathCondition_of_realizedTailPathSet_of_previous_localRealizationData
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (R : TexSweepLocalRealizationData Dfull)
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (target_mem_region :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θ))⁻¹).mulVec
              (Pi.single j (1 : ℝ))) ∈
            R.U) :
    TexSweepDepthOneBasisSourcePathCondition D := by
  intro hL j
  rw [hPaths]
  exact R.constant_tail_realized _ (target_mem_region hL j)

/-- Conditional depth-one basis input from a previous local realization neighborhood
that contains the required single-inverse depth-one targets. -/
def depthOneBasisRealizationInput_of_realizedTailPathSet_of_previous_localRealizationData
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (R : TexSweepLocalRealizationData Dfull)
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (target_mem_region :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θ))⁻¹).mulVec
              (Pi.single j (1 : ℝ))) ∈
            R.U) :
    TexSweepDepthOneBasisRealizationInput D :=
  depthOneBasisRealizationInput_of_sourcePathCondition
    (depthOneBasisSourcePathCondition_of_realizedTailPathSet_of_previous_localRealizationData
      Dfull R hPaths target_mem_region)

/-- Canonical-near-anchor specialization of
`depthOneBasisSourcePathCondition_of_realizedTailPathSet_of_previous_localRealizationData`. -/
theorem depthOneBasisSourcePathCondition_of_previous_canonicalNearAnchor
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (R : TexSweepCanonicalNearAnchorLocalRealizationData Dfull)
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (target_mem_region :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θ))⁻¹).mulVec
              (Pi.single j (1 : ℝ))) ∈
            R.U) :
    TexSweepDepthOneBasisSourcePathCondition D := by
  intro hL j
  rw [hPaths]
  exact R.constant_tail_realized _ (target_mem_region hL j)

/-- Conditional depth-one basis input from a previous canonical near-anchor realization
neighborhood that contains the required single-inverse depth-one targets. -/
def depthOneBasisRealizationInput_of_previous_canonicalNearAnchor
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (R : TexSweepCanonicalNearAnchorLocalRealizationData Dfull)
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (target_mem_region :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θ))⁻¹).mulVec
              (Pi.single j (1 : ℝ))) ∈
            R.U) :
    TexSweepDepthOneBasisRealizationInput D :=
  depthOneBasisRealizationInput_of_sourcePathCondition
    (depthOneBasisSourcePathCondition_of_previous_canonicalNearAnchor
      Dfull R hPaths target_mem_region)

/-- Pointwise nondegenerate IFT data, separated from the local realization theorem.

These are exactly the source point, gate, determinant, regularity, and Jacobian
nonvanishing fields of `TexSweepLocalIFTData`.  Existing local-realization, region, or
provider data can then supply the final `local_realization` field mechanically. -/
structure TexSweepLocalIFTPointData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (A : TexSweepAnchorPointData D) : Type where
  source_anchor : ProbePoint d
  gate : ℝ
  gate_pos : 0 < gate
  gate_lt_one : gate < 1
  source_mem_base : source_anchor ∈ D.O
  source_on_quadric :
    firstLayerQuadric (Params.headAttention θ) source_anchor
  source_regular :
    firstLayerRegular (Params.headAttention θ) source_anchor
  pi_ne_zero :
    firstLayerPi (Params.headAttention θ) source_anchor ≠ 0
  value_mul_source_w_ne_zero :
    (Params.headValue θ).mulVec source_anchor.1 ≠ 0
  det_first_skip_ne_zero :
    (skipB (Params.headValue θ)).det ≠ 0
  det_anchor_step_ne_zero :
    (anchorStepMatrix
      (fun _ => (Params.headValue θ, Params.headAttention θ)) 0 gate).det ≠ 0
  vartheta0_ne_zero :
    texSweepVartheta0 (Params.headValue θ) (Params.headAttention θ)
      source_anchor gate ≠ 0
  swept_anchor_eq :
    firstLayerDialPoint (Params.headValue θ) gate source_anchor.1 source_anchor.2 =
      A.point

/-- Canonical-anchor version of the pointwise nondegenerate IFT data. -/
abbrev TexSweepCanonicalIFTPointData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') : Type :=
  TexSweepLocalIFTPointData D (texSweepAnchorPointData_of_IDLData D)

/-- Retarget pointwise IFT data along equality of the selected tail-anchor points. -/
def texSweepLocalIFTPointData_of_anchorPoint_eq
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A A' : TexSweepAnchorPointData D}
    (P : TexSweepLocalIFTPointData D A) (hA : A.point = A'.point) :
    TexSweepLocalIFTPointData D A' where
  source_anchor := P.source_anchor
  gate := P.gate
  gate_pos := P.gate_pos
  gate_lt_one := P.gate_lt_one
  source_mem_base := P.source_mem_base
  source_on_quadric := P.source_on_quadric
  source_regular := P.source_regular
  pi_ne_zero := P.pi_ne_zero
  value_mul_source_w_ne_zero := P.value_mul_source_w_ne_zero
  det_first_skip_ne_zero := P.det_first_skip_ne_zero
  det_anchor_step_ne_zero := P.det_anchor_step_ne_zero
  vartheta0_ne_zero := P.vartheta0_ne_zero
  swept_anchor_eq := by
    simpa [hA] using P.swept_anchor_eq

/-- Pointwise sweep IFT data from a full-depth unwound anchor.

The full anchor supplies the source point, first transport gate, first-step determinant,
regularity, and inverse-scalar nonvanishing.  The generic first-skip determinant and
first-layer matching transfer these facts from the primed first layer to the matched
unprimed first layer. -/
noncomputable def texSweepLocalIFTPointData_of_fullUnwoundAnchor
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p) :
    TexSweepLocalIFTPointData D
      (texSweepAnchorPointData_of_fullUnwoundAnchor D W) := by
  have htIoo : W.t 0 ∈ Set.Ioo (0 : ℝ) 1 := W.t_mem_Ioo 0 (by omega)
  have hquad' : firstLayerQuadric (Params.headAttention θ') p :=
    texSweepFirstLayerQuadric_of_anchorUnwindingData W hL
  have hreg' : firstLayerRegular (Params.headAttention θ') p :=
    texSweepFirstLayerRegular_of_anchorUnwindingData W hL
  have hVw' : (Params.headValue θ').mulVec p.1 ≠ 0 :=
    texSweepValue_mul_source_w_ne_zero_of_anchorUnwindingData W hL
  have hdetStep' :
      (anchorStepMatrix
        (fun _ => (Params.headValue θ', Params.headAttention θ')) 0 (W.t 0)).det ≠ 0 := by
    have hdet := W.det_step_ne_zero 0 (by omega)
    simpa [anchorStepMatrix, Params.headValue, Params.headAttention, Params.headLayer,
      anchorParamStream] using hdet
  have hvartheta' :
      texSweepVartheta0 (Params.headValue θ') (Params.headAttention θ') p (W.t 0) ≠ 0 := by
    have hinv := W.inverse_scalar_ne_zero 0 (by omega)
    simpa [texSweepVartheta0_eq_anchorInverseScalarAt] using hinv
  refine
    { source_anchor := p
      gate := W.t 0
      gate_pos := htIoo.1
      gate_lt_one := htIoo.2
      source_mem_base := hpO
      source_on_quadric := ?_
      source_regular := ?_
      pi_ne_zero := ?_
      value_mul_source_w_ne_zero := ?_
      det_first_skip_ne_zero := headValueSkip_det_ne_zero_of_matching hstep matching
      det_anchor_step_ne_zero := ?_
      vartheta0_ne_zero := ?_
      swept_anchor_eq := ?_ }
  · simpa [matching.headAttention_eq] using hquad'
  · simpa [matching.headAttention_eq] using hreg'
  · have hreg : firstLayerRegular (Params.headAttention θ) p := by
      simpa [matching.headAttention_eq] using hreg'
    exact hreg.2.2
  · simpa [matching.headValue_eq] using hVw'
  · simpa [matching.headValue_eq, matching.headAttention_eq] using hdetStep'
  · simpa [matching.headValue_eq, matching.headAttention_eq] using hvartheta'
  · calc
      firstLayerDialPoint (Params.headValue θ) (W.t 0) p.1 p.2 =
          anchorStep (fun _ => (Params.headValue θ, Params.headAttention θ)) 0
            (W.t 0) p :=
        firstLayerDialPoint_eq_anchorStep
          (Params.headValue θ) (Params.headAttention θ) (W.t 0) p
      _ = (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point := by
        simp [texSweepAnchorPointData_of_fullUnwoundAnchor, anchorStep,
          anchorStepMatrix, Params.headValue, Params.headLayer,
          anchorParamStream, matching.headValue_eq]

/-- Canonical pointwise sweep IFT data from a full-depth unwound anchor, once the
transported tail-anchor point is known to be the canonical `IDLData` anchor choice. -/
noncomputable def texSweepCanonicalIFTPointData_of_fullUnwoundAnchor
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (hcanonical :
      (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point =
        (texSweepAnchorPointData_of_IDLData D).point) :
    TexSweepCanonicalIFTPointData D :=
  texSweepLocalIFTPointData_of_anchorPoint_eq
    (texSweepLocalIFTPointData_of_fullUnwoundAnchor
      hL hstep matching D hpO W)
    hcanonical

/-- Canonical pointwise sweep IFT data from a full-depth unwound anchor when the
primed tail anchor is unique. -/
noncomputable def texSweepCanonicalIFTPointData_of_fullUnwoundAnchor_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (hunique : TexSweepTailAnchorUnique D) :
    TexSweepCanonicalIFTPointData D :=
  texSweepCanonicalIFTPointData_of_fullUnwoundAnchor
    hL hstep matching D hpO W
    (texSweepFullUnwoundAnchorPoint_eq_canonical_of_tailAnchorUnique W hunique)

/-- Assemble local IFT data from pointwise nondegenerate IFT data and an existing
near-anchor local realization theorem. -/
def texSweepLocalIFTData_of_pointData_nearAnchorPoint
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (P : TexSweepLocalIFTPointData D A)
    (hnear : TexSweepLocalRealizationNearAnchorPoint D A) :
    TexSweepLocalIFTData D A where
  source_anchor := P.source_anchor
  gate := P.gate
  gate_pos := P.gate_pos
  gate_lt_one := P.gate_lt_one
  source_mem_base := P.source_mem_base
  source_on_quadric := P.source_on_quadric
  source_regular := P.source_regular
  pi_ne_zero := P.pi_ne_zero
  value_mul_source_w_ne_zero := P.value_mul_source_w_ne_zero
  det_first_skip_ne_zero := P.det_first_skip_ne_zero
  det_anchor_step_ne_zero := P.det_anchor_step_ne_zero
  vartheta0_ne_zero := P.vartheta0_ne_zero
  swept_anchor_eq := P.swept_anchor_eq
  local_realization := hnear

/-- Canonical-anchor IFT data from canonical pointwise nondegenerate data and the
canonical near-anchor realization theorem. -/
noncomputable def texSweepCanonicalIFTData_of_pointData_nearAnchorPoint
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (_P : TexSweepCanonicalIFTPointData D)
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D)) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_nearAnchorPoint D hnear

/-- The local IFT package exposes the near-anchor local realization theorem required by
the provider compiler. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_localIFTData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (I : TexSweepLocalIFTData D A) :
    TexSweepLocalRealizationNearAnchorPoint D A :=
  I.local_realization

/-- Canonical IFT data exposes exactly the canonical near-anchor realization theorem. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_canonicalIFTData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (I : TexSweepCanonicalIFTData D) :
    TexSweepLocalRealizationNearAnchorPoint D
      (texSweepAnchorPointData_of_IDLData D) :=
  I.local_realization

/-- Retarget a near-anchor local realization theorem along equality of selected anchor
points.  The open realized neighborhood and all source-path witnesses are unchanged. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_anchorPoint_eq
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A A' : TexSweepAnchorPointData D}
    (hA : A.point = A'.point)
    (hnear : TexSweepLocalRealizationNearAnchorPoint D A) :
    TexSweepLocalRealizationNearAnchorPoint D A' := by
  rcases hnear with ⟨U, hUopen, hAmem, hrealized⟩
  exact ⟨U, hUopen, by simpa [← hA] using hAmem, hrealized⟩

/-- A local `Ψ` inverse selector, together with path availability and realization of the
selected source paths, proves the near-anchor local realization obligation. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_localPsiInverseNearAnchorData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (I : TexSweepPsiLocalInverseNearAnchorData D A)
    (hpaths : TexSweepPsiLocalInverseSourcesAvailable I)
    (hrealizes : TexSweepPsiLocalInverseRealizes I) :
    TexSweepLocalRealizationNearAnchorPoint D A := by
  refine ⟨I.U, I.U_open, I.anchor_mem, ?_⟩
  intro η hη
  exact ⟨I.source η hη, hpaths η hη, hrealizes η hη⟩

/-- Bundle a local `Ψ` inverse selector together with its selected-source obligations
as the near-anchor realization package. -/
noncomputable def texSweepPsiLocalInverseRealizationData_of_localPsiInverseNearAnchorData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (I : TexSweepPsiLocalInverseNearAnchorData D A)
    (hpaths : TexSweepPsiLocalInverseSourcesAvailable I)
    (hrealizes : TexSweepPsiLocalInverseRealizes I) :
    TexSweepPsiLocalInverseRealizationData D A where
  U := I.U
  U_open := I.U_open
  anchor_mem := I.anchor_mem
  constant_tail_realized := by
    intro η hη
    exact ⟨I.source η hη, hpaths η hη, hrealizes η hη⟩

/-- The bundled local `Ψ` realization data is exactly the near-anchor local realization
obligation. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_localPsiInverseRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (R : TexSweepPsiLocalInverseRealizationData D A) :
    TexSweepLocalRealizationNearAnchorPoint D A := by
  exact ⟨R.U, R.U_open, R.anchor_mem, R.constant_tail_realized⟩

/-- Canonical bundled local `Ψ` realization data exposes the canonical near-anchor
local realization theorem. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_canonicalPsiLocalInverseRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepCanonicalPsiLocalInverseRealizationData D) :
    TexSweepLocalRealizationNearAnchorPoint D
      (texSweepAnchorPointData_of_IDLData D) :=
  texSweepLocalRealizationNearAnchorPoint_of_localPsiInverseRealizationData R

/-- Package an existing near-anchor local realization theorem as bundled local `Ψ`
realization data. -/
noncomputable def texSweepPsiLocalInverseRealizationData_of_nearAnchorPoint
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (A : TexSweepAnchorPointData D)
    (hnear : TexSweepLocalRealizationNearAnchorPoint D A) :
    TexSweepPsiLocalInverseRealizationData D A := by
  classical
  let U : Set (ProbePoint d) := Classical.choose hnear
  have hU :
      IsOpen U ∧ A.point ∈ U ∧
        ∀ η : ProbePoint d, η ∈ U ->
          ∃ source : ProbePath d, source ∈ D.Paths ∧
            Nonempty (RealizationData r
              (Params.headValue θ) (Params.headAttention θ)
              (constantProbePath η) source) :=
    Classical.choose_spec hnear
  exact
    { U := U
      U_open := hU.1
      anchor_mem := hU.2.1
      constant_tail_realized := hU.2.2 }

/-- Canonical-anchor version of packaging an existing near-anchor local realization
theorem as bundled local `Ψ` realization data. -/
noncomputable def texSweepCanonicalPsiLocalInverseRealizationData_of_nearAnchorPoint
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D)) :
    TexSweepCanonicalPsiLocalInverseRealizationData D :=
  texSweepPsiLocalInverseRealizationData_of_nearAnchorPoint D
    (texSweepAnchorPointData_of_IDLData D) hnear

/-- In the universal current path class, every source selected by a local `Ψ` inverse
is automatically available.  Thus the top-level sweep provider only has to prove that
the selected sources realize the requested constant tail targets. -/
theorem texSweepPsiLocalInverseSourcesAvailable_of_paths_univ
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (hPaths : D.Paths = Set.univ)
    (I : TexSweepPsiLocalInverseNearAnchorData D A) :
    TexSweepPsiLocalInverseSourcesAvailable I := by
  intro η hη
  rw [hPaths]
  exact Set.mem_univ _

/-- Universal paths discharge source-path availability for a local `Ψ` inverse selector.
The remaining local obligation is the genuine realization theorem for the selected
sources. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_paths_univ_localPsiInverseNearAnchorData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (hPaths : D.Paths = Set.univ)
    (I : TexSweepPsiLocalInverseNearAnchorData D A)
    (hrealizes : TexSweepPsiLocalInverseRealizes I) :
    TexSweepLocalRealizationNearAnchorPoint D A :=
  texSweepLocalRealizationNearAnchorPoint_of_localPsiInverseNearAnchorData I
    (texSweepPsiLocalInverseSourcesAvailable_of_paths_univ hPaths I)
    hrealizes

/-- Universal-path packaging of a local `Ψ` inverse selector as bundled realization
data.  Source-path availability is filled by `D.Paths = Set.univ`; realization remains
the selector-side analytic proof. -/
noncomputable def
    texSweepPsiLocalInverseRealizationData_of_paths_univ_localPsiInverseNearAnchorData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (hPaths : D.Paths = Set.univ)
    (I : TexSweepPsiLocalInverseNearAnchorData D A)
    (hrealizes : TexSweepPsiLocalInverseRealizes I) :
    TexSweepPsiLocalInverseRealizationData D A :=
  texSweepPsiLocalInverseRealizationData_of_localPsiInverseNearAnchorData I
    (texSweepPsiLocalInverseSourcesAvailable_of_paths_univ hPaths I)
    hrealizes

/-- Compatibility wrapper: bundled local `Ψ` realization data already carries the
near-anchor local realization theorem; the universal-path assumption is not needed. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_paths_univ_localPsiInverseRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (_hPaths : D.Paths = Set.univ)
    (R : TexSweepPsiLocalInverseRealizationData D A) :
    TexSweepLocalRealizationNearAnchorPoint D A :=
  texSweepLocalRealizationNearAnchorPoint_of_localPsiInverseRealizationData R

/-- If every constant tail target is already realized by the current path class, then the
canonical near-anchor local realization obligation holds with `Set.univ` as the realized
neighborhood. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_all_realized
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (all_realized :
      ∀ η : ProbePoint d,
        constantProbePath η ∈ realizedTailPathSet r θ D.Paths) :
    TexSweepLocalRealizationNearAnchorPoint D
      (texSweepAnchorPointData_of_IDLData D) := by
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, ?_⟩
  intro η _hη
  simpa [realizedTailPathSet] using all_realized η

/-- Lifted all-realized constructor matching the active recursive sweep provider field. -/
def texSweepLocalRealizationNearAnchorPoint_plift_of_all_realized
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (all_realized :
      ∀ η : ProbePoint d,
        constantProbePath η ∈ realizedTailPathSet r θ D.Paths) :
    PLift
      (TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D)) :=
  PLift.up
    (texSweepLocalRealizationNearAnchorPoint_of_all_realized D all_realized)

/-- Existing local-realization packages prove the near-anchor obligation exactly when
their open swept set contains the selected anchor point. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_localRealizationData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (R : TexSweepLocalRealizationData D) (hA : A.point ∈ R.U) :
    TexSweepLocalRealizationNearAnchorPoint D A := by
  exact ⟨R.U, R.U_open, hA, R.constant_tail_realized⟩

/-- Existing open-realization packages prove the near-anchor obligation exactly when
their open swept set contains the selected anchor point. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_openRealizationData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (R : TexSweepOpenRealizationData D) (hA : A.point ∈ R.U) :
    TexSweepLocalRealizationNearAnchorPoint D A :=
  texSweepLocalRealizationNearAnchorPoint_of_localRealizationData_mem
    (texSweepLocalRealizationData_of_openRealizationData R) hA

/-- Region-level sweep data proves the near-anchor obligation exactly when its open
swept set contains the selected anchor point. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_regionCoreData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (C : TexSweepRegionCoreData D) (hA : A.point ∈ C.U) :
    TexSweepLocalRealizationNearAnchorPoint D A := by
  refine ⟨C.U, C.U_open, hA, ?_⟩
  intro η hη
  simpa [realizedTailPathSet] using C.U_subset_realized hη

/-- A near-anchor local realization theorem gives the basis-free local-realization
package.  The tail-anchor handoff is the selected anchor point itself. -/
noncomputable def texSweepLocalRealizationData_of_nearAnchorPoint
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (A : TexSweepAnchorPointData D)
    (hnear : TexSweepLocalRealizationNearAnchorPoint D A) :
    TexSweepLocalRealizationData D := by
  classical
  let U : Set (ProbePoint d) := Classical.choose hnear
  have hU :
      IsOpen U ∧ A.point ∈ U ∧
        ∀ η : ProbePoint d, η ∈ U ->
          ∃ source : ProbePath d, source ∈ D.Paths ∧
            Nonempty (RealizationData r
              (Params.headValue θ) (Params.headAttention θ)
              (constantProbePath η) source) :=
    Classical.choose_spec hnear
  exact
    { U := U
      U_open := hU.1
      U_nonempty := ⟨A.point, hU.2.1⟩
      constant_tail_realized := hU.2.2
      tail_anchor_nonempty := Or.inr
        ⟨A.point, hU.2.1, A.point_mem_tail_anchor.2⟩ }

/-- A near-anchor local realization theorem also gives the core realized sweep region
used by the non-canonical full-anchor handoff. -/
noncomputable def texSweepRegionCoreData_of_nearAnchorPoint
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (A : TexSweepAnchorPointData D)
    (hnear : TexSweepLocalRealizationNearAnchorPoint D A) :
    TexSweepRegionCoreData D :=
  texSweepRegionCoreData_of_localRealizationData
    (texSweepLocalRealizationData_of_nearAnchorPoint D A hnear)

/-- Local IFT data from pointwise nondegeneracy plus a local `Ψ` inverse selector and
its source-path obligations. -/
def texSweepLocalIFTData_of_pointData_localPsiInverseNearAnchorData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (P : TexSweepLocalIFTPointData D A)
    (I : TexSweepPsiLocalInverseNearAnchorData D A)
    (hpaths : TexSweepPsiLocalInverseSourcesAvailable I)
    (hrealizes : TexSweepPsiLocalInverseRealizes I) :
    TexSweepLocalIFTData D A :=
  texSweepLocalIFTData_of_pointData_nearAnchorPoint P
    (texSweepLocalRealizationNearAnchorPoint_of_localPsiInverseNearAnchorData
      I hpaths hrealizes)

/-- Canonical IFT data from canonical pointwise nondegeneracy plus a canonical local
`Ψ` inverse selector and its two selected-source obligations. -/
noncomputable def texSweepCanonicalIFTData_of_pointData_localPsiInverseNearAnchorData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (_P : TexSweepCanonicalIFTPointData D)
    (I : TexSweepPsiLocalInverseNearAnchorData D
      (texSweepAnchorPointData_of_IDLData D))
    (hpaths : TexSweepPsiLocalInverseSourcesAvailable I)
    (hrealizes : TexSweepPsiLocalInverseRealizes I) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_nearAnchorPoint D
    (texSweepLocalRealizationNearAnchorPoint_of_localPsiInverseNearAnchorData
      I hpaths hrealizes)

/-- Universal-path variant of the local IFT compiler from pointwise nondegeneracy and
a local `Ψ` inverse selector.  Path availability is mechanical from `D.Paths = Set.univ`;
the only selector-side hypothesis left is realization of the selected sources. -/
def texSweepLocalIFTData_of_pointData_paths_univ_localPsiInverseNearAnchorData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (P : TexSweepLocalIFTPointData D A)
    (hPaths : D.Paths = Set.univ)
    (I : TexSweepPsiLocalInverseNearAnchorData D A)
    (hrealizes : TexSweepPsiLocalInverseRealizes I) :
    TexSweepLocalIFTData D A :=
  texSweepLocalIFTData_of_pointData_localPsiInverseNearAnchorData P I
    (texSweepPsiLocalInverseSourcesAvailable_of_paths_univ hPaths I)
    hrealizes

/-- Canonical-anchor universal-path IFT compiler from pointwise nondegeneracy and a
canonical local `Ψ` inverse selector, with source-path availability discharged by
`D.Paths = Set.univ`. -/
noncomputable def
    texSweepCanonicalIFTData_of_pointData_paths_univ_localPsiInverseNearAnchorData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (_P : TexSweepCanonicalIFTPointData D)
    (hPaths : D.Paths = Set.univ)
    (I : TexSweepPsiLocalInverseNearAnchorData D
      (texSweepAnchorPointData_of_IDLData D))
    (hrealizes : TexSweepPsiLocalInverseRealizes I) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_nearAnchorPoint D
    (texSweepLocalRealizationNearAnchorPoint_of_paths_univ_localPsiInverseNearAnchorData
      hPaths I hrealizes)

/-- Canonical-anchor universal-path IFT compiler from pointwise nondegeneracy and
bundled local `Ψ` realization data. -/
noncomputable def
    texSweepCanonicalIFTData_of_pointData_paths_univ_localPsiInverseRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepCanonicalIFTPointData D)
    (hPaths : D.Paths = Set.univ)
    (R : TexSweepCanonicalPsiLocalInverseRealizationData D) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_pointData_paths_univ_localPsiInverseNearAnchorData
    P hPaths
    (texSweepPsiLocalInverseNearAnchorData_of_localPsiInverseRealizationData R)
    (texSweepPsiLocalInverseRealizes_of_localPsiInverseRealizationData R)

/-- Canonical-anchor IFT compiler from pointwise nondegeneracy and bundled canonical
local `Ψ` realization data.  Unlike the universal-path wrapper, this uses the source
path availability already stored in the bundled realization data. -/
noncomputable def texSweepCanonicalIFTData_of_pointData_localPsiInverseRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepCanonicalIFTPointData D)
    (R : TexSweepCanonicalPsiLocalInverseRealizationData D) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_pointData_nearAnchorPoint P
    (texSweepLocalRealizationNearAnchorPoint_of_canonicalPsiLocalInverseRealizationData R)

/-- Local IFT data from pointwise nondegeneracy plus existing local-realization data
whose open set contains the selected anchor. -/
def texSweepLocalIFTData_of_pointData_localRealizationData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (P : TexSweepLocalIFTPointData D A)
    (R : TexSweepLocalRealizationData D) (hA : A.point ∈ R.U) :
    TexSweepLocalIFTData D A :=
  texSweepLocalIFTData_of_pointData_nearAnchorPoint P
    (texSweepLocalRealizationNearAnchorPoint_of_localRealizationData_mem R hA)

/-- Local IFT data from pointwise nondegeneracy plus existing open-realization data
whose open set contains the selected anchor. -/
def texSweepLocalIFTData_of_pointData_openRealizationData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (P : TexSweepLocalIFTPointData D A)
    (R : TexSweepOpenRealizationData D) (hA : A.point ∈ R.U) :
    TexSweepLocalIFTData D A :=
  texSweepLocalIFTData_of_pointData_nearAnchorPoint P
    (texSweepLocalRealizationNearAnchorPoint_of_openRealizationData_mem R hA)

/-- Local IFT data from pointwise nondegeneracy plus region-core data whose open set
contains the selected anchor. -/
def texSweepLocalIFTData_of_pointData_regionCoreData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (P : TexSweepLocalIFTPointData D A)
    (C : TexSweepRegionCoreData D) (hA : A.point ∈ C.U) :
    TexSweepLocalIFTData D A :=
  texSweepLocalIFTData_of_pointData_nearAnchorPoint P
    (texSweepLocalRealizationNearAnchorPoint_of_regionCoreData_mem C hA)

/-- Canonical IFT data from canonical pointwise nondegeneracy plus region-core data
containing the canonical anchor. -/
noncomputable def texSweepCanonicalIFTData_of_pointData_regionCoreData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (_P : TexSweepCanonicalIFTPointData D)
    (C : TexSweepRegionCoreData D)
    (hA : (texSweepAnchorPointData_of_IDLData D).point ∈ C.U) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_nearAnchorPoint D
    (texSweepLocalRealizationNearAnchorPoint_of_regionCoreData_mem C hA)

/-- Canonical IFT data from a full-depth unwound anchor plus a core realized region
containing the canonical anchor.  The equality hypothesis records the only choice issue:
the first transported full-anchor point must be the same tail point selected by
`texSweepAnchorPointData_of_IDLData`. -/
noncomputable def texSweepCanonicalIFTData_of_fullUnwoundAnchor_regionCoreData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (C : TexSweepRegionCoreData D)
    (hcanonical :
      (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point =
        (texSweepAnchorPointData_of_IDLData D).point)
    (hA : (texSweepAnchorPointData_of_IDLData D).point ∈ C.U) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_pointData_regionCoreData_mem
    (texSweepCanonicalIFTPointData_of_fullUnwoundAnchor
      hL hstep matching D hpO W hcanonical)
    C hA

/-- Canonical IFT data from a full-depth unwound anchor plus a core realized region,
with anchor-choice compatibility discharged by uniqueness of the primed tail anchor. -/
noncomputable def texSweepCanonicalIFTData_of_fullUnwoundAnchor_regionCoreData_mem_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (C : TexSweepRegionCoreData D)
    (hunique : TexSweepTailAnchorUnique D)
    (hA : (texSweepAnchorPointData_of_IDLData D).point ∈ C.U) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_fullUnwoundAnchor_regionCoreData_mem
    hL hstep matching D hpO W C
    (texSweepFullUnwoundAnchorPoint_eq_canonical_of_tailAnchorUnique W hunique) hA

/-- Choice-compatibility between a concrete full-depth unwound anchor and the canonical
tail-anchor point selected from `IDLData`.  This is the exact equality needed only when
retargeting full-anchor IFT data to the canonical anchor. -/
noncomputable def TexSweepFullAnchorChoiceCompatible {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') {p : AnchorProbe d}
    (W : AnchorUnwindingData θ' p) : Prop :=
  (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point =
    (texSweepAnchorPointData_of_IDLData D).point

/-- Tail-anchor uniqueness is one sufficient way to prove full-anchor/canonical choice
compatibility, but the non-canonical full-anchor route below does not need uniqueness. -/
theorem texSweepFullAnchorChoiceCompatible_of_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (W : AnchorUnwindingData θ' p)
    (hunique : TexSweepTailAnchorUnique D) :
    TexSweepFullAnchorChoiceCompatible D W :=
  texSweepFullUnwoundAnchorPoint_eq_canonical_of_tailAnchorUnique W hunique

/-- The canonical anchor is, by construction, the transport of `idlChosenFullAnchor D`, so
that full anchor is choice-compatible with the canonical `IDLData` anchor **definitionally**
— no tail-anchor uniqueness required.  This is the honest replacement for the depth-one-false
`TexSweepTailAnchorUnique` route. -/
theorem texSweepFullAnchorChoiceCompatible_idlChosenFullAnchor
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') :
    TexSweepFullAnchorChoiceCompatible D (idlChosenFullAnchor D).2 :=
  rfl

/-- Local IFT data at the full unwound anchor itself, using only membership of that
transported full-anchor tail point in the realized region.  No canonical anchor choice
or tail-anchor uniqueness is involved. -/
noncomputable def texSweepLocalIFTData_of_fullUnwoundAnchor_regionCoreData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (C : TexSweepRegionCoreData D)
    (hA : (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ C.U) :
    TexSweepLocalIFTData D
      (texSweepAnchorPointData_of_fullUnwoundAnchor D W) :=
  texSweepLocalIFTData_of_pointData_regionCoreData_mem
    (texSweepLocalIFTPointData_of_fullUnwoundAnchor
      hL hstep matching D hpO W)
    C hA

/-- Compact non-canonical provider surface from a concrete full unwound anchor and a
realized region containing that transported full-anchor point. -/
structure TexSweepLocalIFTFullAnchorRegionData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') where
  point : AnchorProbe d
  point_mem_O : point ∈ D.O
  unwinding : AnchorUnwindingData θ' point
  region : TexSweepRegionCoreData D
  full_anchor_mem_region :
    (texSweepAnchorPointData_of_fullUnwoundAnchor D unwinding).point ∈ region.U

/-- Package an explicit full unwound anchor and region-membership proof into the compact
non-canonical full-anchor/region provider. -/
noncomputable def texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_regionCoreData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (C : TexSweepRegionCoreData D)
    (hA : (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ C.U) :
    TexSweepLocalIFTFullAnchorRegionData D where
  point := p
  point_mem_O := hpO
  unwinding := W
  region := C
  full_anchor_mem_region := hA

/-- Package an explicit full unwound anchor with a full sweep-region package whose
open set contains the transported full-anchor tail point. -/
noncomputable def texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_regionData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (R : TexSweepRegionData D)
    (hA : (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ R.U) :
    TexSweepLocalIFTFullAnchorRegionData D :=
  texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_regionCoreData_mem
    hpO W (texSweepRegionCoreData_of_regionData R) hA

/-- Package an explicit full unwound anchor with an open-realization package whose
open set contains the transported full-anchor tail point. -/
noncomputable def
    texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_openRealizationData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (R : TexSweepOpenRealizationData D)
    (hA : (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ R.U) :
    TexSweepLocalIFTFullAnchorRegionData D :=
  texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_regionCoreData_mem
    hpO W (texSweepRegionCoreData_of_openRealizationData R) hA

/-- Package an explicit full unwound anchor with a basis-free local-realization package
whose open set contains the transported full-anchor tail point. -/
noncomputable def
    texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_localRealizationData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (R : TexSweepLocalRealizationData D)
    (hA : (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ R.U) :
    TexSweepLocalIFTFullAnchorRegionData D :=
  texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_regionCoreData_mem
    hpO W (texSweepRegionCoreData_of_localRealizationData R) hA

/-- Package an explicit full unwound anchor with provider-facing local inverse-sweep
data whose open set contains the transported full-anchor tail point. -/
noncomputable def
    texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_localInverseSweepProviderData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (P : TexSweepLocalInverseSweepProviderData D)
    (hA : (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ P.U) :
    TexSweepLocalIFTFullAnchorRegionData D :=
  texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_localRealizationData_mem
    hpO W (texSweepLocalRealizationData_of_localInverseSweepProviderData P) hA

/-- Package an explicit full unwound anchor with canonical realized-tail-region data
when the canonical region itself contains the transported full-anchor tail point. -/
noncomputable def
    texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_realizedTailRegionData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (R : TexSweepRealizedTailRegionData D)
    (hA :
      (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈
        realizedTailRegion r θ D.Paths) :
    TexSweepLocalIFTFullAnchorRegionData D :=
  texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_regionCoreData_mem
    hpO W (texSweepRegionCoreData_of_realizedTailRegionData R) hA

/-- Package an explicit full unwound anchor with an actual local realization theorem
around its transported tail point.  The resulting region is precisely the open
neighborhood supplied by that theorem. -/
noncomputable def
    texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_nearAnchorPoint
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_fullUnwoundAnchor D W)) :
    TexSweepLocalIFTFullAnchorRegionData D := by
  classical
  let A : TexSweepAnchorPointData D := texSweepAnchorPointData_of_fullUnwoundAnchor D W
  let U : Set (ProbePoint d) := Classical.choose hnear
  have hU :
      IsOpen U ∧ A.point ∈ U ∧
        ∀ η : ProbePoint d, η ∈ U ->
          ∃ source : ProbePath d, source ∈ D.Paths ∧
            Nonempty (RealizationData r
              (Params.headValue θ) (Params.headAttention θ)
              (constantProbePath η) source) :=
    Classical.choose_spec hnear
  let R : TexSweepLocalRealizationData D :=
    { U := U
      U_open := hU.1
      U_nonempty := ⟨A.point, hU.2.1⟩
      constant_tail_realized := hU.2.2
      tail_anchor_nonempty := Or.inr
        ⟨A.point, hU.2.1, A.point_mem_tail_anchor.2⟩ }
  exact
    texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_localRealizationData_mem
      hpO W R hU.2.1

/-- Compact provider surface for the honest local swept region around a transported
full anchor.  It records the full unwound anchor and the local realization theorem at
its transported tail point, leaving the region extraction mechanical. -/
structure TexSweepFullAnchorLocalRealizationData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') where
  point : AnchorProbe d
  point_mem_O : point ∈ D.O
  unwinding : AnchorUnwindingData θ' point
  local_realization :
    TexSweepLocalRealizationNearAnchorPoint D
      (texSweepAnchorPointData_of_fullUnwoundAnchor D unwinding)

/-- Package an explicitly chosen full unwound anchor with a local realization theorem
around its transported tail point. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_fullUnwoundAnchor_nearAnchorPoint
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_fullUnwoundAnchor D W)) :
    TexSweepFullAnchorLocalRealizationData D where
  point := p
  point_mem_O := hpO
  unwinding := W
  local_realization := hnear

/-- At positive tail depth, select the full anchor supplied by `IDLData.anchor_nonempty`
and apply a uniform local-realization theorem for every full unwound anchor in `D.O`. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_IDLData_uniformNearAnchorPoint
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (hnear :
      ∀ {p : AnchorProbe d}, p ∈ D.O -> (W : AnchorUnwindingData θ' p) ->
        TexSweepLocalRealizationNearAnchorPoint D
          (texSweepAnchorPointData_of_fullUnwoundAnchor D W)) :
    TexSweepFullAnchorLocalRealizationData D := by
  classical
  have hanchor : (D.O ∩ unwoundAnchorSet θ').Nonempty := by
    rcases D.anchor_nonempty with hdepth | hanchor
    · omega
    · exact hanchor
  let p : AnchorProbe d := Classical.choose hanchor
  have hp : p ∈ D.O ∩ unwoundAnchorSet θ' := Classical.choose_spec hanchor
  let W : AnchorUnwindingData θ' p := Classical.choice hp.2
  exact
    texSweepFullAnchorLocalRealizationData_of_fullUnwoundAnchor_nearAnchorPoint
      hp.1 W (hnear hp.1 W)

/-- A canonical near-anchor local realization theorem plus uniqueness of the primed
tail anchor proves the compact full-anchor frontier.  Uniqueness is used only to
retarget the canonical realized neighborhood to whichever full anchor is selected from
`IDLData.anchor_nonempty`. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_nearAnchorPoint_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D))
    (hunique : TexSweepTailAnchorUnique D) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_IDLData_uniformNearAnchorPoint hL D
    (fun {_p} _hpO W =>
      texSweepLocalRealizationNearAnchorPoint_of_anchorPoint_eq
        (A := texSweepAnchorPointData_of_IDLData D)
        (A' := texSweepAnchorPointData_of_fullUnwoundAnchor D W)
        (texSweepFullUnwoundAnchorPoint_eq_canonical_of_tailAnchorUnique
          W hunique).symm
        hnear)

/-- A canonical IFT package contains the canonical near-anchor realization theorem, so
tail-anchor uniqueness compiles it to the compact full-anchor frontier without exposing
the canonical provider wrapper. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_canonicalIFTData_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (I : TexSweepCanonicalIFTData D)
    (hunique : TexSweepTailAnchorUnique D) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_nearAnchorPoint_tailAnchorUnique
    hL D (texSweepLocalRealizationNearAnchorPoint_of_canonicalIFTData I) hunique

/-- Existing local-realization packages produce compact full-anchor local-realization
data when their open set contains the transported full-anchor tail point. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_fullUnwoundAnchor_localRealizationData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (R : TexSweepLocalRealizationData D)
    (hA : (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ R.U) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_fullUnwoundAnchor_nearAnchorPoint hpO W
    (texSweepLocalRealizationNearAnchorPoint_of_localRealizationData_mem R hA)

/-- Existing open-realization packages produce compact full-anchor local-realization
data when their open set contains the transported full-anchor tail point. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_fullUnwoundAnchor_openRealizationData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (R : TexSweepOpenRealizationData D)
    (hA : (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ R.U) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_fullUnwoundAnchor_nearAnchorPoint hpO W
    (texSweepLocalRealizationNearAnchorPoint_of_openRealizationData_mem R hA)

/-- Region-core sweep data produces compact full-anchor local-realization data when
its open region contains the transported full-anchor tail point. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_fullUnwoundAnchor_regionCoreData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (C : TexSweepRegionCoreData D)
    (hA : (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ C.U) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_fullUnwoundAnchor_nearAnchorPoint hpO W
    (texSweepLocalRealizationNearAnchorPoint_of_regionCoreData_mem C hA)

/-- Provider-facing local inverse-sweep data produces compact full-anchor
local-realization data when the provider's open set contains the transported
full-anchor tail point. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_fullUnwoundAnchor_localInverseSweepProviderData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (P : TexSweepLocalInverseSweepProviderData D)
    (hA : (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ P.U) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_fullUnwoundAnchor_nearAnchorPoint hpO W
    (by
      refine ⟨P.U, P.U_open, hA, ?_⟩
      intro η hη
      exact ⟨P.source η hη, P.source_mem_paths η hη, P.realized η hη⟩)

/-- Select the full anchor from `IDLData.anchor_nonempty` and prove compact full-anchor
local-realization data from a core region plus the uniform membership fact for every
transported full anchor in that region. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_IDLData_regionCoreData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (C : TexSweepRegionCoreData D)
    (hmem :
      ∀ {p : AnchorProbe d}, p ∈ D.O -> (W : AnchorUnwindingData θ' p) ->
        (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ C.U) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_IDLData_uniformNearAnchorPoint hL D
    (fun hpO W =>
      texSweepLocalRealizationNearAnchorPoint_of_regionCoreData_mem C
        (hmem hpO W))

/-- Select the full anchor from `IDLData.anchor_nonempty` and prove compact full-anchor
local-realization data from a basis-free local-realization package plus the uniform
membership fact for every transported full anchor in its open set. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_IDLData_localRealizationData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (R : TexSweepLocalRealizationData D)
    (hmem :
      ∀ {p : AnchorProbe d}, p ∈ D.O -> (W : AnchorUnwindingData θ' p) ->
        (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ R.U) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_IDLData_regionCoreData_mem hL D
    (texSweepRegionCoreData_of_localRealizationData R) hmem

/-- Select the full anchor from `IDLData.anchor_nonempty` and prove compact full-anchor
local-realization data from an open-realization package plus the uniform membership fact
for every transported full anchor in its open set. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_IDLData_openRealizationData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (R : TexSweepOpenRealizationData D)
    (hmem :
      ∀ {p : AnchorProbe d}, p ∈ D.O -> (W : AnchorUnwindingData θ' p) ->
        (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ R.U) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_IDLData_regionCoreData_mem hL D
    (texSweepRegionCoreData_of_openRealizationData R) hmem

/-- A provider-facing local inverse-sweep package plus uniform membership of every
transported full anchor in its open set selects the full anchor from
`IDLData.anchor_nonempty` and proves the compact frontier. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_IDLData_localInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepLocalInverseSweepProviderData D)
    (hmem :
      ∀ {p : AnchorProbe d}, p ∈ D.O -> (W : AnchorUnwindingData θ' p) ->
        (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ P.U) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_IDLData_uniformNearAnchorPoint hL D
    (fun hpO W =>
      (texSweepFullAnchorLocalRealizationData_of_fullUnwoundAnchor_localInverseSweepProviderData_mem
        hpO W P (hmem hpO W)).local_realization)

/-- Tail-anchor uniqueness reduces the uniform full-anchor membership requirement to
membership of the canonical `IDLData` anchor in the same core region. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_IDLData_regionCoreData_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (C : TexSweepRegionCoreData D)
    (hunique : TexSweepTailAnchorUnique D)
    (hA : (texSweepAnchorPointData_of_IDLData D).point ∈ C.U) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_IDLData_regionCoreData_mem hL D C
    (fun {_p} _hpO W => by
      have hcompat :
          (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point =
            (texSweepAnchorPointData_of_IDLData D).point :=
        texSweepFullUnwoundAnchorPoint_eq_canonical_of_tailAnchorUnique W hunique
      rw [hcompat]
      exact hA)

/-- Tail-anchor uniqueness reduces full-anchor local-realization data from a
basis-free local-realization package to membership of the canonical `IDLData` anchor in
that package's open set. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_IDLData_localRealizationData_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (R : TexSweepLocalRealizationData D)
    (hunique : TexSweepTailAnchorUnique D)
    (hA : (texSweepAnchorPointData_of_IDLData D).point ∈ R.U) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_IDLData_regionCoreData_tailAnchorUnique
    hL D (texSweepRegionCoreData_of_localRealizationData R) hunique hA

/-- Tail-anchor uniqueness reduces full-anchor local-realization data from an
open-realization package to membership of the canonical `IDLData` anchor in that
package's open set. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_IDLData_openRealizationData_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (R : TexSweepOpenRealizationData D)
    (hunique : TexSweepTailAnchorUnique D)
    (hA : (texSweepAnchorPointData_of_IDLData D).point ∈ R.U) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_IDLData_regionCoreData_tailAnchorUnique
    hL D (texSweepRegionCoreData_of_openRealizationData R) hunique hA

/-- Tail-anchor uniqueness reduces full-anchor local-realization data from a
provider-facing local inverse-sweep package to membership of the canonical `IDLData`
anchor in the provider's open set. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_IDLData_localInverseSweepProviderData_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepLocalInverseSweepProviderData D)
    (hunique : TexSweepTailAnchorUnique D)
    (hA : (texSweepAnchorPointData_of_IDLData D).point ∈ P.U) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_IDLData_localInverseSweepProviderData
    hL D P
    (fun {_p} _hpO W => by
      have hcompat :
          (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point =
            (texSweepAnchorPointData_of_IDLData D).point :=
        texSweepFullUnwoundAnchorPoint_eq_canonical_of_tailAnchorUnique W hunique
      rw [hcompat]
      exact hA)

/-- A canonical local inverse-sweep provider and tail-anchor uniqueness prove the
full-anchor local-realization frontier without any separate transported-anchor
membership premise. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_canonicalProvider_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (C : TexSweepCanonicalLocalInverseSweepProviderData D)
    (hunique : TexSweepTailAnchorUnique D) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_IDLData_uniformNearAnchorPoint hL D
    (fun {_p} hpO W => by
      have hmem :
          (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ C.U := by
        have hcompat :
            (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point =
              (texSweepAnchorPointData_of_IDLData D).point :=
          texSweepFullUnwoundAnchorPoint_eq_canonical_of_tailAnchorUnique W hunique
        rw [hcompat]
        exact C.anchor_mem
      exact
        (texSweepFullAnchorLocalRealizationData_of_fullUnwoundAnchor_nearAnchorPoint
          hpO W
          ⟨C.U, C.U_open, hmem, by
            intro η hη
            exact ⟨C.source η hη, C.source_mem_paths η hη, C.realized η hη⟩⟩).local_realization)

/-- Canonical realized-tail-region data produces compact full-anchor local-realization
data when the canonical open region contains the transported full-anchor tail point. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_fullUnwoundAnchor_realizedTailRegionData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (R : TexSweepRealizedTailRegionData D)
    (hA :
      (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈
        realizedTailRegion r θ D.Paths) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_fullUnwoundAnchor_openRealizationData_mem
    hpO W (texSweepOpenRealizationData_of_realizedTailRegionData R) hA

/-- Existing full-anchor/region sweep data is equivalent to the compact
full-anchor local-realization frontier by forgetting the region and retaining the
near-anchor theorem it induces. -/
noncomputable def texSweepFullAnchorLocalRealizationData_of_fullAnchorRegionData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepLocalIFTFullAnchorRegionData D) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_fullUnwoundAnchor_regionCoreData_mem
    P.point_mem_O P.unwinding P.region P.full_anchor_mem_region

/-- Compile the compact full-anchor local-realization surface to the existing
full-anchor/region provider expected by the sweep handoff. -/
noncomputable def
    texSweepLocalIFTFullAnchorRegionData_of_fullAnchorLocalRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepFullAnchorLocalRealizationData D) :
    TexSweepLocalIFTFullAnchorRegionData D :=
  texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_nearAnchorPoint
    P.point_mem_O P.unwinding P.local_realization

/-- Forget a compact full-anchor local-realization package to the basis-free local
realization surface. -/
noncomputable def texSweepLocalRealizationData_of_fullAnchorLocalRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepFullAnchorLocalRealizationData D) :
    TexSweepLocalRealizationData D :=
  texSweepLocalRealizationData_of_nearAnchorPoint D
    (texSweepAnchorPointData_of_fullUnwoundAnchor D P.unwinding)
    P.local_realization

/-- Compact full-anchor local-realization data supplies the canonical pointwise IFT
data once the transported full-anchor point is identified with the canonical
`IDLData` anchor.  The point and gate witnesses come from the existing full-anchor
wrapper; the compatibility proof only retargets the endpoint equality. -/
noncomputable def
    texSweepCanonicalIFTPointData_of_fullAnchorLocalRealizationData_choiceCompatible
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepFullAnchorLocalRealizationData D)
    (hcompat : TexSweepFullAnchorChoiceCompatible D P.unwinding) :
    TexSweepCanonicalIFTPointData D :=
  texSweepCanonicalIFTPointData_of_fullUnwoundAnchor
    hL hstep matching D P.point_mem_O P.unwinding hcompat

/-- Tail-anchor uniqueness discharges the compatibility needed to extract canonical
pointwise IFT data from the compact full-anchor local-realization wrapper. -/
noncomputable def
    texSweepCanonicalIFTPointData_of_fullAnchorLocalRealizationData_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepFullAnchorLocalRealizationData D)
    (hunique : TexSweepTailAnchorUnique D) :
    TexSweepCanonicalIFTPointData D :=
  texSweepCanonicalIFTPointData_of_fullAnchorLocalRealizationData_choiceCompatible
    hL hstep matching D P
    (texSweepFullAnchorChoiceCompatible_of_tailAnchorUnique P.unwinding hunique)

/-- Compact full-anchor local-realization data becomes the concrete canonical
near-anchor source surface when the transported full-anchor point is explicitly
compatible with the canonical `IDLData` anchor choice. -/
noncomputable def
    texSweepCanonicalNearAnchorLocalRealizationData_of_fullAnchorLocalRealizationData_compatible
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepFullAnchorLocalRealizationData D)
    (hcompat : TexSweepFullAnchorChoiceCompatible D P.unwinding) :
    TexSweepCanonicalNearAnchorLocalRealizationData D :=
  texSweepCanonicalNearAnchorLocalRealizationData_of_nearAnchorPoint D
    (texSweepLocalRealizationNearAnchorPoint_of_anchorPoint_eq
      (A := texSweepAnchorPointData_of_fullUnwoundAnchor D P.unwinding)
      (A' := texSweepAnchorPointData_of_IDLData D)
      hcompat P.local_realization)

/-- Reduced compiler from compact full-anchor local-realization data to the canonical
sweep frontier when the transported full-anchor point agrees with the canonical anchor.
The local realization theorem is retargeted across the equality; no pointwise IFT data
or new Type-level witness is selected. -/
noncomputable def
    texSweepCanonicalIFTData_of_fullAnchorLocalRealizationData_compatible
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepFullAnchorLocalRealizationData D)
    (hcompat : TexSweepFullAnchorChoiceCompatible D P.unwinding) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_nearAnchorPoint D
    (texSweepLocalRealizationNearAnchorPoint_of_anchorPoint_eq
      (A := texSweepAnchorPointData_of_fullUnwoundAnchor D P.unwinding)
      (A' := texSweepAnchorPointData_of_IDLData D)
      hcompat P.local_realization)

/-- Reduced tail-anchor-unique compiler from compact full-anchor local-realization data
to the canonical sweep frontier.  Uniqueness supplies only the retargeting equality. -/
noncomputable def
    texSweepCanonicalIFTData_of_fullAnchorLocalRealizationData_tailAnchorUnique_reduced
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepFullAnchorLocalRealizationData D)
    (hunique : TexSweepTailAnchorUnique D) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_fullAnchorLocalRealizationData_compatible D P
    (texSweepFullAnchorChoiceCompatible_of_tailAnchorUnique P.unwinding hunique)

/-- Backward-compatible spelling of the reduced full-anchor/canonical compatibility
compiler.  The pointwise IFT inputs are now derivable elsewhere and are not part of the
canonical sweep frontier. -/
noncomputable def
    texSweepCanonicalIFTData_of_fullAnchorLocalRealizationData_choiceCompatible
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (_hL : 0 < L)
    (_hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (_matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepFullAnchorLocalRealizationData D)
    (hcompat : TexSweepFullAnchorChoiceCompatible D P.unwinding) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_fullAnchorLocalRealizationData_compatible D P hcompat

/-- Backward-compatible spelling of the reduced tail-anchor-unique compiler. -/
noncomputable def
    texSweepCanonicalIFTData_of_fullAnchorLocalRealizationData_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (_hL : 0 < L)
    (_hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (_matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepFullAnchorLocalRealizationData D)
    (hunique : TexSweepTailAnchorUnique D) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_fullAnchorLocalRealizationData_tailAnchorUnique_reduced
    D P hunique

/-- Region package plus the uniform membership clause needed after selecting any
full-depth unwound anchor already known to lie in `D.O`.  This keeps the choice of
anchor inside the constructor below while making the geometric obligation explicit. -/
structure TexSweepFullAnchorRegionMembershipData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') where
  region : TexSweepRegionCoreData D
  full_anchor_mem_region :
    ∀ {p : AnchorProbe d}, p ∈ D.O -> (W : AnchorUnwindingData θ' p) ->
      (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ region.U

/-- A core region that is propositionally `Set.univ` supplies the uniform full-anchor
membership package.  This is the honest no-extra-membership bridge for universal swept
regions: the transported full-anchor point is in the region by `Set.mem_univ`, while
all realization content remains in the supplied core region. -/
noncomputable def texSweepFullAnchorRegionMembershipData_of_regionCoreData_eq_univ
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepRegionCoreData D) (hU : C.U = Set.univ) :
    TexSweepFullAnchorRegionMembershipData D where
  region := C
  full_anchor_mem_region := by
    intro _p _hpO _W
    rw [hU]
    exact Set.mem_univ _

/-- Choose the full-depth anchor supplied by `IDLData.anchor_nonempty` at positive tail
depth, then package it with a region whose membership clause is uniform over all
unwound anchors in `D.O`. -/
noncomputable def
    texSweepLocalIFTFullAnchorRegionData_of_IDLData_anchorRegionMembership
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (M : TexSweepFullAnchorRegionMembershipData D) :
    TexSweepLocalIFTFullAnchorRegionData D := by
  classical
  have hanchor : (D.O ∩ unwoundAnchorSet θ').Nonempty := by
    rcases D.anchor_nonempty with hdepth | hanchor
    · omega
    · exact hanchor
  let p : AnchorProbe d := Classical.choose hanchor
  have hp : p ∈ D.O ∩ unwoundAnchorSet θ' := Classical.choose_spec hanchor
  let W : AnchorUnwindingData θ' p := Classical.choice hp.2
  exact
    texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_regionCoreData_mem
      hp.1 W M.region (M.full_anchor_mem_region hp.1 W)

/-- Positive-depth full-anchor local-realization data from the uniform
full-anchor/region membership package.  This is the direct constructor for the reduced
frontier used by `IdentifiabilityMain`; the region extraction remains mechanical. -/
noncomputable def
    texSweepFullAnchorLocalRealizationData_of_IDLData_anchorRegionMembership
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (M : TexSweepFullAnchorRegionMembershipData D) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_fullAnchorRegionData
    (texSweepLocalIFTFullAnchorRegionData_of_IDLData_anchorRegionMembership hL D M)

/-- Positive-depth full-anchor/region data from a core region known to be `Set.univ`.
The selected full anchor still comes from `IDLData.anchor_nonempty`; no additional
transported-anchor membership proof is needed. -/
noncomputable def texSweepLocalIFTFullAnchorRegionData_of_IDLData_regionCoreData_eq_univ
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (C : TexSweepRegionCoreData D) (hU : C.U = Set.univ) :
    TexSweepLocalIFTFullAnchorRegionData D :=
  texSweepLocalIFTFullAnchorRegionData_of_IDLData_anchorRegionMembership hL D
    (texSweepFullAnchorRegionMembershipData_of_regionCoreData_eq_univ C hU)

/-- Positive-depth full-anchor local-realization data from a core region known to be
`Set.univ`; transported full-anchor membership is automatic. -/
noncomputable def texSweepFullAnchorLocalRealizationData_of_IDLData_regionCoreData_eq_univ
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (C : TexSweepRegionCoreData D) (hU : C.U = Set.univ) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_IDLData_anchorRegionMembership hL D
    (texSweepFullAnchorRegionMembershipData_of_regionCoreData_eq_univ C hU)

/-- Fixed-region compatibility between an explicitly chosen full-depth unwound anchor
and an existing core swept region.

This is the narrow non-universal bridge: it records exactly the missing fact that the
tail point transported from the chosen full anchor lies in the chosen region, without
asserting uniqueness of tail anchors or any global membership property. -/
structure TexSweepFullAnchorRegionCompatibilityData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (C : TexSweepRegionCoreData D) where
  point : AnchorProbe d
  point_mem_O : point ∈ D.O
  unwinding : AnchorUnwindingData θ' point
  full_anchor_mem_region :
    (texSweepAnchorPointData_of_fullUnwoundAnchor D unwinding).point ∈ C.U

/-- Package an explicit full unwound anchor and core-region membership proof as fixed
full-anchor/region compatibility. -/
noncomputable def
    texSweepFullAnchorRegionCompatibilityData_of_fullUnwoundAnchor_regionCoreData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (C : TexSweepRegionCoreData D)
    (hA : (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ C.U) :
    TexSweepFullAnchorRegionCompatibilityData D C where
  point := p
  point_mem_O := hpO
  unwinding := W
  full_anchor_mem_region := hA

/-- Fixed full-anchor compatibility for the core region underlying an open-realization
package, assuming the transported full-anchor point lies in its open set. -/
noncomputable def
    texSweepFullAnchorRegionCompatibilityData_of_fullUnwoundAnchor_openRealizationData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (R : TexSweepOpenRealizationData D)
    (hA : (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ R.U) :
    TexSweepFullAnchorRegionCompatibilityData D
      (texSweepRegionCoreData_of_openRealizationData R) :=
  texSweepFullAnchorRegionCompatibilityData_of_fullUnwoundAnchor_regionCoreData_mem
    hpO W (texSweepRegionCoreData_of_openRealizationData R) hA

/-- Fixed full-anchor compatibility for the core region underlying provider-facing
local inverse-sweep data, assuming the transported full-anchor point lies in the
provider's open set. -/
noncomputable def
    texSweepFullAnchorRegionCompatibilityData_of_fullUnwoundAnchor_localInverseSweepProviderData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (P : TexSweepLocalInverseSweepProviderData D)
    (hA : (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ P.U) :
    TexSweepFullAnchorRegionCompatibilityData D
      (texSweepRegionCoreData_of_localRealizationData
        (texSweepLocalRealizationData_of_localInverseSweepProviderData P)) :=
  texSweepFullAnchorRegionCompatibilityData_of_fullUnwoundAnchor_regionCoreData_mem
    hpO W
    (texSweepRegionCoreData_of_localRealizationData
      (texSweepLocalRealizationData_of_localInverseSweepProviderData P))
    hA

/-- Fixed full-anchor compatibility for the canonical realized-tail region, assuming
that region contains the transported full-anchor point. -/
noncomputable def
    texSweepFullAnchorRegionCompatibilityData_of_fullUnwoundAnchor_realizedTailRegionData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (R : TexSweepRealizedTailRegionData D)
    (hA :
      (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈
        realizedTailRegion r θ D.Paths) :
    TexSweepFullAnchorRegionCompatibilityData D
      (texSweepRegionCoreData_of_realizedTailRegionData R) :=
  texSweepFullAnchorRegionCompatibilityData_of_fullUnwoundAnchor_regionCoreData_mem
    hpO W (texSweepRegionCoreData_of_realizedTailRegionData R) hA

/-- Turn fixed-region full-anchor compatibility into the compact full-anchor/region
provider used by the local IFT sweep handoff. -/
noncomputable def
    texSweepLocalIFTFullAnchorRegionData_of_regionCoreData_fullAnchorCompatibility
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepRegionCoreData D)
    (K : TexSweepFullAnchorRegionCompatibilityData D C) :
    TexSweepLocalIFTFullAnchorRegionData D :=
  texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_regionCoreData_mem
    K.point_mem_O K.unwinding C K.full_anchor_mem_region

/-- Constructor from an existing open-realization package plus fixed full-anchor
compatibility with its underlying core region. -/
noncomputable def
    texSweepLocalIFTFullAnchorRegionData_of_openRealizationData_fullAnchorCompatibility
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (R : TexSweepOpenRealizationData D)
    (K : TexSweepFullAnchorRegionCompatibilityData D
      (texSweepRegionCoreData_of_openRealizationData R)) :
    TexSweepLocalIFTFullAnchorRegionData D :=
  texSweepLocalIFTFullAnchorRegionData_of_regionCoreData_fullAnchorCompatibility
    (texSweepRegionCoreData_of_openRealizationData R) K

/-- Constructor from provider-facing local inverse-sweep data plus fixed full-anchor
compatibility with its underlying core region. -/
noncomputable def
    texSweepLocalIFTFullAnchorRegionData_of_localInverseSweepProviderData_fullAnchorCompatibility
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepLocalInverseSweepProviderData D)
    (K : TexSweepFullAnchorRegionCompatibilityData D
      (texSweepRegionCoreData_of_localRealizationData
        (texSweepLocalRealizationData_of_localInverseSweepProviderData P))) :
    TexSweepLocalIFTFullAnchorRegionData D :=
  texSweepLocalIFTFullAnchorRegionData_of_regionCoreData_fullAnchorCompatibility
    (texSweepRegionCoreData_of_localRealizationData
      (texSweepLocalRealizationData_of_localInverseSweepProviderData P))
    K

/-- Stronger open-region provider: every point in the current open set supplies a
full-depth unwinding and membership of its transported tail anchor in the same sweep
region.  This can be consumed directly from `D.O_nonempty`, avoiding any separate
anchor-selection obligation. -/
structure TexSweepEveryOpenPointFullAnchorRegionData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') where
  region : TexSweepRegionCoreData D
  full_anchor_mem_region :
    ∀ p : AnchorProbe d, p ∈ D.O ->
      ∃ W : AnchorUnwindingData θ' p,
        (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ region.U

/-- Select a full anchor from `D.O_nonempty` when the provider proves that every open
point has an unwinding whose transported tail anchor lies in the swept region. -/
noncomputable def
    texSweepLocalIFTFullAnchorRegionData_of_O_nonempty_everyOpenPoint
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (M : TexSweepEveryOpenPointFullAnchorRegionData D) :
    TexSweepLocalIFTFullAnchorRegionData D := by
  classical
  let p : AnchorProbe d := Classical.choose D.O_nonempty
  have hp : p ∈ D.O := Classical.choose_spec D.O_nonempty
  let hWmem := M.full_anchor_mem_region p hp
  let W : AnchorUnwindingData θ' p := Classical.choose hWmem
  have hA :
      (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point ∈ M.region.U :=
    Classical.choose_spec hWmem
  exact
    texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_regionCoreData_mem
      hp W M.region hA

/-- Compile the compact non-canonical full-anchor/region provider into local IFT data
at the transported full-anchor tail point. -/
noncomputable def texSweepLocalIFTData_of_fullAnchorRegionData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepLocalIFTFullAnchorRegionData D) :
    TexSweepLocalIFTData D
      (texSweepAnchorPointData_of_fullUnwoundAnchor D P.unwinding) :=
  texSweepLocalIFTData_of_fullUnwoundAnchor_regionCoreData_mem
    hL hstep matching D P.point_mem_O P.unwinding P.region
    P.full_anchor_mem_region

/-- Compact provider surface for canonical sweep IFT data built from a full unwound
anchor and a realized region core.

The only non-mechanical choice issue is the equality between the transported full-anchor
tail point and the canonical anchor point selected from `IDLData`. -/
structure TexSweepCanonicalIFTFullAnchorRegionData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') where
  point : AnchorProbe d
  point_mem_O : point ∈ D.O
  unwinding : AnchorUnwindingData θ' point
  region : TexSweepRegionCoreData D
  anchor_eq_canonical :
    (texSweepAnchorPointData_of_fullUnwoundAnchor D unwinding).point =
      (texSweepAnchorPointData_of_IDLData D).point
  canonical_mem_region : (texSweepAnchorPointData_of_IDLData D).point ∈ region.U

/-- Compile the compact full-anchor/region provider into canonical sweep IFT data. -/
noncomputable def texSweepCanonicalIFTData_of_fullAnchorRegionData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepCanonicalIFTFullAnchorRegionData D) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_fullUnwoundAnchor_regionCoreData_mem
    hL hstep matching D (p := P.point)
    P.point_mem_O P.unwinding P.region
    P.anchor_eq_canonical P.canonical_mem_region

/-- Convert the non-canonical full-anchor/region provider to the existing canonical
provider exactly when the transported full-anchor point agrees with the canonical
`IDLData` anchor.  The region membership is transported across that equality. -/
noncomputable def texSweepCanonicalIFTFullAnchorRegionData_of_localFullAnchorRegionData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepLocalIFTFullAnchorRegionData D)
    (hcompat : TexSweepFullAnchorChoiceCompatible D P.unwinding) :
    TexSweepCanonicalIFTFullAnchorRegionData D where
  point := P.point
  point_mem_O := P.point_mem_O
  unwinding := P.unwinding
  region := P.region
  anchor_eq_canonical := hcompat
  canonical_mem_region := by
    rw [← hcompat]
    exact P.full_anchor_mem_region

/-- Canonical IFT data from the non-canonical full-anchor/region provider plus the
minimal full-anchor/canonical choice-compatibility equality. -/
noncomputable def texSweepCanonicalIFTData_of_localFullAnchorRegionData_choiceCompatible
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepLocalIFTFullAnchorRegionData D)
    (hcompat : TexSweepFullAnchorChoiceCompatible D P.unwinding) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_fullAnchorRegionData hL hstep matching D
    (texSweepCanonicalIFTFullAnchorRegionData_of_localFullAnchorRegionData
      P hcompat)

/-- Compact provider surface using uniqueness of the primed tail anchor to discharge
canonical anchor-choice compatibility. -/
structure TexSweepCanonicalIFTFullAnchorRegionUniqueData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') where
  point : AnchorProbe d
  point_mem_O : point ∈ D.O
  unwinding : AnchorUnwindingData θ' point
  region : TexSweepRegionCoreData D
  tail_anchor_unique : TexSweepTailAnchorUnique D
  canonical_mem_region : (texSweepAnchorPointData_of_IDLData D).point ∈ region.U

/-- In positive tail depth, `IDLData.anchor_nonempty` supplies the full-depth anchor
needed by the compact canonical IFT provider.  Tail-anchor uniqueness discharges only
the canonical anchor-choice equality; the region geometry remains the explicit input. -/
noncomputable def texSweepCanonicalIFTFullAnchorRegionUniqueData_of_IDLData_regionCoreData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (C : TexSweepRegionCoreData D)
    (hunique : TexSweepTailAnchorUnique D)
    (hA : (texSweepAnchorPointData_of_IDLData D).point ∈ C.U) :
    TexSweepCanonicalIFTFullAnchorRegionUniqueData D := by
  classical
  have hanchor : (D.O ∩ unwoundAnchorSet θ').Nonempty := by
    rcases D.anchor_nonempty with hdepth | hanchor
    · omega
    · exact hanchor
  let p : AnchorProbe d := Classical.choose hanchor
  have hp : p ∈ D.O ∩ unwoundAnchorSet θ' := Classical.choose_spec hanchor
  let W : AnchorUnwindingData θ' p := Classical.choice hp.2
  exact
    { point := p
      point_mem_O := hp.1
      unwinding := W
      region := C
      tail_anchor_unique := hunique
      canonical_mem_region := hA }

/-- Tail-anchor uniqueness converts the uniqueness-based provider to the equality-based
full-anchor/region provider. -/
noncomputable def texSweepCanonicalIFTFullAnchorRegionData_of_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepCanonicalIFTFullAnchorRegionUniqueData D) :
    TexSweepCanonicalIFTFullAnchorRegionData D where
  point := P.point
  point_mem_O := P.point_mem_O
  unwinding := P.unwinding
  region := P.region
  anchor_eq_canonical :=
    texSweepFullUnwoundAnchorPoint_eq_canonical_of_tailAnchorUnique
      P.unwinding P.tail_anchor_unique
  canonical_mem_region := P.canonical_mem_region

/-- Positive-depth constructor for the equality-based full-anchor/region provider from
`IDLData.anchor_nonempty`, a realized region core containing the canonical anchor, and
uniqueness of the primed tail anchor. -/
noncomputable def
    texSweepCanonicalIFTFullAnchorRegionData_of_IDLData_regionCoreData_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (C : TexSweepRegionCoreData D)
    (hunique : TexSweepTailAnchorUnique D)
    (hA : (texSweepAnchorPointData_of_IDLData D).point ∈ C.U) :
    TexSweepCanonicalIFTFullAnchorRegionData D :=
  texSweepCanonicalIFTFullAnchorRegionData_of_tailAnchorUnique
    (texSweepCanonicalIFTFullAnchorRegionUniqueData_of_IDLData_regionCoreData
      hL D C hunique hA)

/-- Same positive-depth full-anchor/region constructor, accepting the older full region
package and forgetting its depth-one basis clause. -/
noncomputable def
    texSweepCanonicalIFTFullAnchorRegionData_of_IDLData_regionData_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (R : TexSweepRegionData D)
    (hunique : TexSweepTailAnchorUnique D)
    (hA : (texSweepAnchorPointData_of_IDLData D).point ∈ R.U) :
    TexSweepCanonicalIFTFullAnchorRegionData D :=
  texSweepCanonicalIFTFullAnchorRegionData_of_IDLData_regionCoreData_tailAnchorUnique
    hL D (texSweepRegionCoreData_of_regionData R) hunique hA

/-- Compile the compact full-anchor/region provider when canonical anchor-choice
compatibility follows from uniqueness of the primed tail anchor. -/
noncomputable def texSweepCanonicalIFTData_of_fullAnchorRegionUniqueData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepCanonicalIFTFullAnchorRegionUniqueData D) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_fullAnchorRegionData hL hstep matching D
    (texSweepCanonicalIFTFullAnchorRegionData_of_tailAnchorUnique P)

/-- Turn an existing provider-facing local inverse-sweep package into the near-anchor
`Ψ` inverse selector, assuming its swept open set contains the selected anchor point. -/
noncomputable def texSweepPsiLocalInverseNearAnchorData_of_localInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (P : TexSweepLocalInverseSweepProviderData D) (hA : A.point ∈ P.U) :
    TexSweepPsiLocalInverseNearAnchorData D A where
  U := P.U
  U_open := P.U_open
  anchor_mem := hA
  source := P.source

/-- A provider-facing local inverse-sweep package supplies the source-path availability
field for the TeX-shaped local `Ψ` inverse selector built from it. -/
theorem texSweepPsiLocalInverseSourcesAvailable_of_localInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (P : TexSweepLocalInverseSweepProviderData D) (hA : A.point ∈ P.U) :
    TexSweepPsiLocalInverseSourcesAvailable
      (texSweepPsiLocalInverseNearAnchorData_of_localInverseSweepProviderData P hA) := by
  intro η hη
  exact P.source_mem_paths η hη

/-- A provider-facing local inverse-sweep package supplies the realization field for the
TeX-shaped local `Ψ` inverse selector built from it. -/
theorem texSweepPsiLocalInverseRealizes_of_localInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (P : TexSweepLocalInverseSweepProviderData D) (hA : A.point ∈ P.U) :
    TexSweepPsiLocalInverseRealizes
      (texSweepPsiLocalInverseNearAnchorData_of_localInverseSweepProviderData P hA) := by
  intro η hη
  exact P.realized η hη

/-- Provider-facing local inverse-sweep data, plus membership of the selected anchor in
the provider neighborhood, supplies the bundled local `Ψ` realization package. -/
noncomputable def texSweepPsiLocalInverseRealizationData_of_localInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (P : TexSweepLocalInverseSweepProviderData D) (hA : A.point ∈ P.U) :
    TexSweepPsiLocalInverseRealizationData D A where
  U := P.U
  U_open := P.U_open
  anchor_mem := hA
  constant_tail_realized := by
    intro η hη
    exact ⟨P.source η hη, P.source_mem_paths η hη, P.realized η hη⟩

/-- Existing provider-facing local inverse-sweep data proves the near-anchor obligation
exactly when its swept open set contains the selected anchor point.  Its usual
tail-anchor handoff only gives some point in `U ∩ unwoundAnchorSet`; it does not identify
that point with the canonical anchor chosen from `IDLData`. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_localInverseSweepProviderData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {A : TexSweepAnchorPointData D}
    (P : TexSweepLocalInverseSweepProviderData D) (hA : A.point ∈ P.U) :
    TexSweepLocalRealizationNearAnchorPoint D A :=
  texSweepLocalRealizationNearAnchorPoint_of_localPsiInverseNearAnchorData
    (texSweepPsiLocalInverseNearAnchorData_of_localInverseSweepProviderData P hA)
    (texSweepPsiLocalInverseSourcesAvailable_of_localInverseSweepProviderData P hA)
    (texSweepPsiLocalInverseRealizes_of_localInverseSweepProviderData P hA)

/-- A provider-facing local inverse-sweep package proves local realization near the
anchor point selected from its own swept set. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_localInverseSweepProviderData_providerAnchor
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepLocalInverseSweepProviderData D) :
    TexSweepLocalRealizationNearAnchorPoint D
      (texSweepProviderAnchorPointData_of_localInverseSweepProviderData P).anchor :=
  texSweepLocalRealizationNearAnchorPoint_of_localInverseSweepProviderData_mem P
    (texSweepProviderAnchorPointData_of_localInverseSweepProviderData P).point_mem_provider

/-- A provider-facing local inverse-sweep package proves the canonical near-anchor
obligation when the provider-selected anchor point agrees with the canonical
`IDLData` choice. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_localInverseSweepProviderData_choiceCompatible
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepLocalInverseSweepProviderData D)
    (hcompat : TexSweepIDLAnchorChoiceCompatible P) :
    TexSweepLocalRealizationNearAnchorPoint D
      (texSweepAnchorPointData_of_IDLData D) := by
  have hA : (texSweepAnchorPointData_of_IDLData D).point ∈ P.U := by
    rw [hcompat]
    exact
      (texSweepProviderAnchorPointData_of_localInverseSweepProviderData P).point_mem_provider
  exact texSweepLocalRealizationNearAnchorPoint_of_localInverseSweepProviderData_mem P hA

/-- A local inverse-sweep provider becomes canonical when the primed tail anchor is
unique. -/
noncomputable def
    texSweepCanonicalLocalInverseSweepProviderData_of_localInverseSweepProviderData_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepLocalInverseSweepProviderData D)
    (hunique : TexSweepTailAnchorUnique D) :
    TexSweepCanonicalLocalInverseSweepProviderData D where
  U := P.U
  U_open := P.U_open
  anchor_mem := by
    have hcompat :
        TexSweepIDLAnchorChoiceCompatible P :=
      texSweepIDLAnchorChoiceCompatible_of_tailAnchorUnique P hunique
    rw [hcompat]
    exact
      (texSweepProviderAnchorPointData_of_localInverseSweepProviderData P).point_mem_provider
  source := P.source
  source_mem_paths := P.source_mem_paths
  realized := P.realized

/-- A canonical-anchor provider directly proves the near-anchor local realization
obligation requested by the top-level universal-path sweep surface. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_canonicalLocalInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepCanonicalLocalInverseSweepProviderData D) :
    TexSweepLocalRealizationNearAnchorPoint D
      (texSweepAnchorPointData_of_IDLData D) := by
  refine ⟨C.U, C.U_open, C.anchor_mem, ?_⟩
  intro η hη
  exact ⟨C.source η hη, C.source_mem_paths η hη, C.realized η hη⟩

/-- Canonical IFT data from canonical pointwise nondegeneracy plus an existing
canonical-anchor local inverse provider. -/
noncomputable def texSweepCanonicalIFTData_of_pointData_canonicalLocalInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepCanonicalIFTPointData D)
    (C : TexSweepCanonicalLocalInverseSweepProviderData D) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_pointData_nearAnchorPoint P
    (texSweepLocalRealizationNearAnchorPoint_of_canonicalLocalInverseSweepProviderData C)

/-- Canonical IFT data from canonical pointwise nondegeneracy plus a provider-facing
local inverse package whose selected anchor is compatible with the canonical one. -/
noncomputable def
    texSweepCanonicalIFTData_of_pointData_localInverseSweepProviderData_choiceCompatible
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepCanonicalIFTPointData D)
    (C : TexSweepLocalInverseSweepProviderData D)
    (hcompat : TexSweepIDLAnchorChoiceCompatible C) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_pointData_nearAnchorPoint P
    (texSweepLocalRealizationNearAnchorPoint_of_localInverseSweepProviderData_choiceCompatible
      C hcompat)

/-- Canonical IFT data from a full unwound anchor and a canonical local inverse
provider, with the full-anchor/canonical-anchor equality supplied explicitly. -/
noncomputable def
    texSweepCanonicalIFTData_of_fullUnwoundAnchor_canonicalLocalInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (hcanonical :
      (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point =
        (texSweepAnchorPointData_of_IDLData D).point)
    (C : TexSweepCanonicalLocalInverseSweepProviderData D) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_pointData_canonicalLocalInverseSweepProviderData
    (texSweepCanonicalIFTPointData_of_fullUnwoundAnchor
      hL hstep matching D hpO W hcanonical)
    C

/-- Canonical IFT data from a full unwound anchor and bundled canonical local `Ψ`
realization data, with the full-anchor/canonical-anchor equality supplied explicitly. -/
noncomputable def
    texSweepCanonicalIFTData_of_fullUnwoundAnchor_localPsiInverseRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (hcanonical :
      (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point =
        (texSweepAnchorPointData_of_IDLData D).point)
    (R : TexSweepCanonicalPsiLocalInverseRealizationData D) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_pointData_localPsiInverseRealizationData
    (texSweepCanonicalIFTPointData_of_fullUnwoundAnchor
      hL hstep matching D hpO W hcanonical)
    R

/-- Tail-anchor uniqueness supplies the canonical-anchor equality needed to build
canonical IFT data from a full unwound anchor and a canonical local inverse provider. -/
noncomputable def
    texSweepCanonicalIFTData_of_fullUnwoundAnchor_canonicalProvider_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (hunique : TexSweepTailAnchorUnique D)
    (C : TexSweepCanonicalLocalInverseSweepProviderData D) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_fullUnwoundAnchor_canonicalLocalInverseSweepProviderData
    hL hstep matching D hpO W
    (texSweepFullUnwoundAnchorPoint_eq_canonical_of_tailAnchorUnique W hunique)
    C

/-- Tail-anchor uniqueness supplies the canonical-anchor equality needed to build
canonical IFT data from a full unwound anchor and bundled canonical local `Ψ`
realization data. -/
noncomputable def
    texSweepCanonicalIFTData_of_fullUnwoundAnchor_localPsiInverseRealizationData_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (hunique : TexSweepTailAnchorUnique D)
    (R : TexSweepCanonicalPsiLocalInverseRealizationData D) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_fullUnwoundAnchor_localPsiInverseRealizationData
    hL hstep matching D hpO W
    (texSweepFullUnwoundAnchorPoint_eq_canonical_of_tailAnchorUnique W hunique)
    R

/-- Existing provider data plus canonical-anchor membership gives the narrower
canonical-anchor provider surface. -/
noncomputable def
    texSweepCanonicalLocalInverseSweepProviderData_of_localInverseSweepProviderData_mem
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (P : TexSweepLocalInverseSweepProviderData D)
    (hA : (texSweepAnchorPointData_of_IDLData D).point ∈ P.U) :
    TexSweepCanonicalLocalInverseSweepProviderData D where
  U := P.U
  U_open := P.U_open
  anchor_mem := hA
  source := P.source
  source_mem_paths := P.source_mem_paths
  realized := P.realized

/-- Convert a canonical-anchor provider to the TeX-shaped local `Ψ` inverse selector. -/
noncomputable def texSweepPsiLocalInverseNearAnchorData_of_canonicalLocalInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepCanonicalLocalInverseSweepProviderData D) :
    TexSweepPsiLocalInverseNearAnchorData D (texSweepAnchorPointData_of_IDLData D) where
  U := C.U
  U_open := C.U_open
  anchor_mem := C.anchor_mem
  source := C.source

/-- A canonical-anchor provider supplies source-path availability for its TeX-shaped
local `Ψ` inverse selector. -/
theorem texSweepPsiLocalInverseSourcesAvailable_of_canonicalLocalInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepCanonicalLocalInverseSweepProviderData D) :
    TexSweepPsiLocalInverseSourcesAvailable
      (texSweepPsiLocalInverseNearAnchorData_of_canonicalLocalInverseSweepProviderData C) := by
  intro η hη
  exact C.source_mem_paths η hη

/-- A canonical-anchor provider supplies realization for its TeX-shaped local `Ψ`
inverse selector. -/
theorem texSweepPsiLocalInverseRealizes_of_canonicalLocalInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepCanonicalLocalInverseSweepProviderData D) :
    TexSweepPsiLocalInverseRealizes
      (texSweepPsiLocalInverseNearAnchorData_of_canonicalLocalInverseSweepProviderData C) := by
  intro η hη
  exact C.realized η hη

/-- A canonical-anchor provider has exactly the fields needed for bundled canonical
local `Ψ` realization data. -/
noncomputable def
    texSweepCanonicalPsiLocalInverseRealizationData_of_canonicalLocalInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepCanonicalLocalInverseSweepProviderData D) :
    TexSweepCanonicalPsiLocalInverseRealizationData D where
  U := C.U
  U_open := C.U_open
  anchor_mem := C.anchor_mem
  constant_tail_realized := by
    intro η hη
    exact ⟨C.source η hη, C.source_mem_paths η hη, C.realized η hη⟩

/-- Package a near-anchor local realization theorem as the provider-facing local
inverse-sweep data consumed by the Step 3 handoff.

The tail-anchor handoff is mechanical: the chosen anchor point lies in the realized
neighborhood by hypothesis and in the primed tail anchor set by
`TexSweepAnchorPointData`. -/
noncomputable def texSweepLocalInverseSweepProviderData_of_nearAnchorPoint
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (A : TexSweepAnchorPointData D)
    (hnear : TexSweepLocalRealizationNearAnchorPoint D A) :
    TexSweepLocalInverseSweepProviderData D := by
  classical
  let U : Set (ProbePoint d) := Classical.choose hnear
  have hU :
      IsOpen U ∧ A.point ∈ U ∧
        ∀ η : ProbePoint d, η ∈ U ->
          ∃ source : ProbePath d, source ∈ D.Paths ∧
            Nonempty (RealizationData r
              (Params.headValue θ) (Params.headAttention θ)
              (constantProbePath η) source) :=
    Classical.choose_spec hnear
  refine
    { U := U
      U_open := hU.1
      U_nonempty := ⟨A.point, hU.2.1⟩
      source := fun η hη => Classical.choose (hU.2.2 η hη)
      source_mem_paths := ?_
      realized := ?_
      tail_anchor_nonempty := ?_ }
  · intro η hη
    exact (Classical.choose_spec (hU.2.2 η hη)).1
  · intro η hη
    exact (Classical.choose_spec (hU.2.2 η hη)).2
  · right
    exact ⟨A.point, ⟨hU.2.1, A.point_mem_tail_anchor.2⟩⟩

/-- Forget the canonical-anchor refinement, producing the existing provider-facing
local inverse-sweep package. -/
noncomputable def texSweepLocalInverseSweepProviderData_of_canonicalLocalInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepCanonicalLocalInverseSweepProviderData D) :
    TexSweepLocalInverseSweepProviderData D where
  U := C.U
  U_open := C.U_open
  U_nonempty := ⟨(texSweepAnchorPointData_of_IDLData D).point, C.anchor_mem⟩
  source := C.source
  source_mem_paths := C.source_mem_paths
  realized := C.realized
  tail_anchor_nonempty := by
    right
    exact ⟨(texSweepAnchorPointData_of_IDLData D).point,
      ⟨C.anchor_mem, (texSweepAnchorPointData_of_IDLData D).point_mem_tail_anchor.2⟩⟩

/-- Package the canonical near-anchor local realization theorem directly as a
canonical-anchor provider. -/
noncomputable def texSweepCanonicalLocalInverseSweepProviderData_of_nearAnchorPoint
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D)) :
    TexSweepCanonicalLocalInverseSweepProviderData D := by
  classical
  let U : Set (ProbePoint d) := Classical.choose hnear
  have hU :
      IsOpen U ∧ (texSweepAnchorPointData_of_IDLData D).point ∈ U ∧
        ∀ η : ProbePoint d, η ∈ U ->
          ∃ source : ProbePath d, source ∈ D.Paths ∧
            Nonempty (RealizationData r
              (Params.headValue θ) (Params.headAttention θ)
              (constantProbePath η) source) :=
    Classical.choose_spec hnear
  refine
    { U := U
      U_open := hU.1
      anchor_mem := hU.2.1
      source := fun η hη => Classical.choose (hU.2.2 η hη)
      source_mem_paths := ?_
      realized := ?_ }
  · intro η hη
    exact (Classical.choose_spec (hU.2.2 η hη)).1
  · intro η hη
    exact (Classical.choose_spec (hU.2.2 η hη)).2

/-- Compile a local IFT sweep package at an arbitrary selected anchor into the existing
provider-facing local inverse-sweep package. -/
noncomputable def texSweepLocalInverseSweepProviderData_of_localIFTData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (A : TexSweepAnchorPointData D)
    (I : TexSweepLocalIFTData D A) :
    TexSweepLocalInverseSweepProviderData D :=
  texSweepLocalInverseSweepProviderData_of_nearAnchorPoint D A
    (texSweepLocalRealizationNearAnchorPoint_of_localIFTData I)

/-- Compile local IFT sweep data targeted at the canonical `IDLData` anchor into the
canonical local inverse-sweep provider. -/
noncomputable def texSweepCanonicalLocalInverseSweepProviderData_of_localIFTData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (I : TexSweepLocalIFTData D (texSweepAnchorPointData_of_IDLData D)) :
    TexSweepCanonicalLocalInverseSweepProviderData D :=
  texSweepCanonicalLocalInverseSweepProviderData_of_nearAnchorPoint D
    (texSweepLocalRealizationNearAnchorPoint_of_localIFTData I)

/-- Canonical-anchor provider constructor from the named canonical IFT sweep package. -/
noncomputable def texSweepCanonicalLocalInverseSweepProviderData_of_canonicalIFTData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (I : TexSweepCanonicalIFTData D) :
    TexSweepCanonicalLocalInverseSweepProviderData D :=
  texSweepCanonicalLocalInverseSweepProviderData_of_nearAnchorPoint D
    (texSweepLocalRealizationNearAnchorPoint_of_canonicalIFTData I)

/-- Canonical local `Ψ` realization data follows from the canonical IFT sweep package.

This removes the separate bundled local-`Ψ` realization assumption at call sites that
already carry the canonical IFT data, without opening a new Prop-to-Type construction:
the compiler only composes the existing Type-level canonical provider route. -/
noncomputable def texSweepCanonicalPsiLocalInverseRealizationData_of_canonicalIFTData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (I : TexSweepCanonicalIFTData D) :
    TexSweepCanonicalPsiLocalInverseRealizationData D :=
  texSweepCanonicalPsiLocalInverseRealizationData_of_canonicalLocalInverseSweepProviderData
    (texSweepCanonicalLocalInverseSweepProviderData_of_canonicalIFTData I)

/-- Analytic constructor from a canonical-anchor local inverse-sweep provider. -/
noncomputable def texSweepAnalyticData_of_canonicalLocalInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepCanonicalLocalInverseSweepProviderData D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_localInverseSweepProviderData hstep matching
    (texSweepLocalInverseSweepProviderData_of_canonicalLocalInverseSweepProviderData C)

/-- A canonical provider contains the depth-one basis targets when the swept
neighborhood itself contains those target probe points.  This is the additional
geometric condition under which the provider fills the arbitrary-path basis clause. -/
def TexSweepCanonicalProviderContainsDepthOneBasis
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepCanonicalLocalInverseSweepProviderData D) : Prop :=
  L = 1 ->
    ∀ j : Fin d,
      ((0 : Fin d -> ℝ), Pi.single j (1 : ℝ)) ∈ C.U

/-- If a canonical provider's swept neighborhood contains the depth-one basis targets,
then its source selector supplies the exact realized-tail basis condition. -/
theorem depthOneBasisRealizationCondition_of_canonicalLocalInverseSweepProviderData_containsBasis
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepCanonicalLocalInverseSweepProviderData D)
    (hbasis : TexSweepCanonicalProviderContainsDepthOneBasis C) :
    TexSweepDepthOneBasisRealizationCondition D := by
  intro hL j
  let p : ProbePoint d := ((0 : Fin d -> ℝ), Pi.single j (1 : ℝ))
  have hp : p ∈ C.U := hbasis hL j
  exact ⟨C.source p hp, C.source_mem_paths p hp, C.realized p hp⟩

/-- Analytic constructor from a canonical provider and the realized-tail basis
condition, avoiding the unfolded existential basis clause at call sites. -/
noncomputable def
    texSweepAnalyticData_of_canonicalLocalInverseSweepProviderData_depthOneBasisCondition
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepCanonicalLocalInverseSweepProviderData D)
    (B : TexSweepDepthOneBasisRealizationCondition D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_canonicalLocalInverseSweepProviderData hstep matching C

/-- Analytic constructor from a canonical provider and the reduced conditional
depth-one basis input.  This stays on the canonical-anchor provider route and therefore
does not need tail-anchor uniqueness. -/
noncomputable def
    texSweepAnalyticData_of_canonicalLocalInverseSweepProviderData_basisInput
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepCanonicalLocalInverseSweepProviderData D)
    (B : TexSweepDepthOneBasisRealizationInput D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_canonicalLocalInverseSweepProviderData_depthOneBasisCondition
    hstep matching C
    (depthOneBasisRealizationCondition_of_input
      (headValueSkip_det_ne_zero_of_matching hstep matching) B)

/-- Analytic constructor from a canonical provider whose swept neighborhood contains
the depth-one basis targets. -/
noncomputable def
    texSweepAnalyticData_of_canonicalLocalInverseSweepProviderData_containsBasis
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepCanonicalLocalInverseSweepProviderData D)
    (hbasis : TexSweepCanonicalProviderContainsDepthOneBasis C) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_canonicalLocalInverseSweepProviderData_depthOneBasisCondition
    hstep matching C
    (depthOneBasisRealizationCondition_of_canonicalLocalInverseSweepProviderData_containsBasis
      C hbasis)

/-- Analytic constructor from the concrete canonical IFT package plus the exact
realized-tail depth-one basis condition. -/
noncomputable def texSweepAnalyticData_of_canonicalIFTData_depthOneBasisCondition
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    {D : IDLData (L + 1) d r θ θ'}
    (I : TexSweepCanonicalIFTData D)
    (B : TexSweepDepthOneBasisRealizationCondition D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_canonicalLocalInverseSweepProviderData_depthOneBasisCondition
    hstep matching
    (texSweepCanonicalLocalInverseSweepProviderData_of_canonicalIFTData I) B

/-- Analytic constructor from canonical IFT data and the reduced conditional depth-one
basis input. -/
noncomputable def texSweepAnalyticData_of_canonicalIFTData_basisInput
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    {D : IDLData (L + 1) d r θ θ'}
    (I : TexSweepCanonicalIFTData D)
    (B : TexSweepDepthOneBasisRealizationInput D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_canonicalIFTData_depthOneBasisCondition
    hstep matching I
    (depthOneBasisRealizationCondition_of_input
      (headValueSkip_det_ne_zero_of_matching hstep matching) B)

/-- Realized-tail recursive analytic constructor from canonical local inverse data.
The remaining depth-one basis obligation is only the previous-layer source-path
statement bundled in `depthOneBasisRealizationInput_of_realizedTailPathSet_sourcePath`. -/
noncomputable def
    texSweepAnalyticData_of_canonicalLocalInverseSweepProviderData_realizedTailPathSet
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    {D : IDLData (L + 1) d r θ θ'}
    (C : TexSweepCanonicalLocalInverseSweepProviderData D)
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem :
      L = 1 ->
        ∀ j : Fin d,
          constantProbePath
              ((0 : Fin d -> ℝ),
                ((skipB (Params.headValue θfull))⁻¹).mulVec
                  (((skipB (Params.headValue θ))⁻¹).mulVec
                    (Pi.single j (1 : ℝ)))) ∈
            FullPaths) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_canonicalLocalInverseSweepProviderData_basisInput
    hstep matching C
    (depthOneBasisRealizationInput_of_realizedTailPathSet_sourcePath
      hPaths hdet_full source_mem)

/-- Realized-tail recursive analytic constructor from canonical IFT data. -/
noncomputable def texSweepAnalyticData_of_canonicalIFTData_realizedTailPathSet
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    {D : IDLData (L + 1) d r θ θ'}
    (I : TexSweepCanonicalIFTData D)
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem :
      L = 1 ->
        ∀ j : Fin d,
          constantProbePath
              ((0 : Fin d -> ℝ),
                ((skipB (Params.headValue θfull))⁻¹).mulVec
                  (((skipB (Params.headValue θ))⁻¹).mulVec
                    (Pi.single j (1 : ℝ)))) ∈
            FullPaths) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_canonicalIFTData_basisInput hstep matching I
    (depthOneBasisRealizationInput_of_realizedTailPathSet_sourcePath
      hPaths hdet_full source_mem)

/-- Provider-facing local inverse-sweep data from the narrower TeX-shaped local `Ψ`
inverse selector plus the two proof obligations for selected source paths. -/
noncomputable def texSweepLocalInverseSweepProviderData_of_localPsiInverseNearAnchorData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (A : TexSweepAnchorPointData D)
    (I : TexSweepPsiLocalInverseNearAnchorData D A)
    (hpaths : TexSweepPsiLocalInverseSourcesAvailable I)
    (hrealizes : TexSweepPsiLocalInverseRealizes I) :
    TexSweepLocalInverseSweepProviderData D :=
  texSweepLocalInverseSweepProviderData_of_nearAnchorPoint D A
    (texSweepLocalRealizationNearAnchorPoint_of_localPsiInverseNearAnchorData
      I hpaths hrealizes)

/-- Canonical-anchor provider data from a TeX-shaped local `Ψ` inverse selector at the
canonical `IDLData` anchor plus the two selected-source obligations. -/
noncomputable def texSweepCanonicalLocalInverseSweepProviderData_of_localPsiInverseNearAnchorData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (I : TexSweepPsiLocalInverseNearAnchorData D
      (texSweepAnchorPointData_of_IDLData D))
    (hpaths : TexSweepPsiLocalInverseSourcesAvailable I)
    (hrealizes : TexSweepPsiLocalInverseRealizes I) :
    TexSweepCanonicalLocalInverseSweepProviderData D where
  U := I.U
  U_open := I.U_open
  anchor_mem := I.anchor_mem
  source := I.source
  source_mem_paths := hpaths
  realized := hrealizes

/-- Universal-path canonical provider from a canonical local `Ψ` inverse selector.
`D.Paths = Set.univ` supplies source-path availability, so the only remaining proof is
that the selected sources realize the requested constant tail targets. -/
noncomputable def
    texSweepCanonicalLocalInverseSweepProviderData_of_paths_univ_localPsiInverseNearAnchorData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    (hPaths : D.Paths = Set.univ)
    (I : TexSweepPsiLocalInverseNearAnchorData D
      (texSweepAnchorPointData_of_IDLData D))
    (hrealizes : TexSweepPsiLocalInverseRealizes I) :
    TexSweepCanonicalLocalInverseSweepProviderData D :=
  texSweepCanonicalLocalInverseSweepProviderData_of_localPsiInverseNearAnchorData I
    (texSweepPsiLocalInverseSourcesAvailable_of_paths_univ hPaths I)
    hrealizes

/-- Canonical `IDLData`-anchored form of the near-anchor local inverse-sweep provider.

This is the narrowed Step 3 provider surface intended for callers that already have
`IDLData`: prove local realization near the anchor extracted from `D`, then use the
existing local inverse-sweep handoff. -/
noncomputable def texSweepLocalInverseSweepProviderData_of_IDLData_nearAnchorPoint
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D)) :
    TexSweepLocalInverseSweepProviderData D :=
  texSweepLocalInverseSweepProviderData_of_canonicalLocalInverseSweepProviderData
    (texSweepCanonicalLocalInverseSweepProviderData_of_nearAnchorPoint D hnear)

/-- Top-level universal-path analytic constructor from the narrowed near-anchor local
realization obligation.  The depth-one basis paths are still filled mechanically from
`Paths = Set.univ`; the sweep geometry only has to prove local realization near the
canonical tail anchor extracted from `IDLData`. -/
noncomputable def texSweepAnalyticData_of_paths_univ_nearAnchorPoint
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D)) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_paths_univ_localInverseSweepProviderData
    hstep matching D hPaths
    (texSweepLocalInverseSweepProviderData_of_IDLData_nearAnchorPoint D hnear)

/-- Top-level universal-path analytic constructor from the concrete canonical
near-anchor source surface. -/
noncomputable def
    texSweepAnalyticData_of_paths_univ_canonicalNearAnchorLocalRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (R : TexSweepCanonicalNearAnchorLocalRealizationData D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_paths_univ_nearAnchorPoint hstep matching D hPaths
    (texSweepLocalRealizationNearAnchorPoint_of_canonicalNearAnchorLocalRealizationData
      R)

/-- Top-level universal-path analytic constructor from the TeX-shaped local `Ψ` inverse
selector near the canonical anchor.  The remaining source-path obligations are explicit:
availability in `D.Paths` and realization of each selected source path. -/
noncomputable def texSweepAnalyticData_of_paths_univ_localPsiInverseNearAnchorData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (I : TexSweepPsiLocalInverseNearAnchorData D
      (texSweepAnchorPointData_of_IDLData D))
    (hpaths : TexSweepPsiLocalInverseSourcesAvailable I)
    (hrealizes : TexSweepPsiLocalInverseRealizes I) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_paths_univ_nearAnchorPoint
    hstep matching D hPaths
    (texSweepLocalRealizationNearAnchorPoint_of_localPsiInverseNearAnchorData
      I hpaths hrealizes)

/-- Top-level universal-path analytic constructor from a canonical local `Ψ` inverse
selector.  The universal path assumption discharges the selected-source path
availability; callers only supply realization of those selected sources. -/
noncomputable def
    texSweepAnalyticData_of_paths_univ_localPsiInverseNearAnchorData_realizes
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (I : TexSweepPsiLocalInverseNearAnchorData D
      (texSweepAnchorPointData_of_IDLData D))
    (hrealizes : TexSweepPsiLocalInverseRealizes I) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_paths_univ_localPsiInverseNearAnchorData
    hstep matching D hPaths I
    (texSweepPsiLocalInverseSourcesAvailable_of_paths_univ hPaths I)
    hrealizes

/-- Top-level universal-path analytic constructor from bundled local `Ψ` realization
data at the canonical anchor. -/
noncomputable def texSweepAnalyticData_of_paths_univ_localPsiInverseRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (R : TexSweepCanonicalPsiLocalInverseRealizationData D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_paths_univ_localPsiInverseNearAnchorData_realizes
    hstep matching D hPaths
    (texSweepPsiLocalInverseNearAnchorData_of_localPsiInverseRealizationData R)
    (texSweepPsiLocalInverseRealizes_of_localPsiInverseRealizationData R)

/-- Top-level universal-path analytic constructor from the canonical-anchor provider
surface.  This is the provider-shaped version of
`texSweepAnalyticData_of_paths_univ_nearAnchorPoint`. -/
noncomputable def texSweepAnalyticData_of_paths_univ_canonicalLocalInverseSweepProviderData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (C : TexSweepCanonicalLocalInverseSweepProviderData D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_paths_univ_nearAnchorPoint hstep matching D hPaths
    (texSweepLocalRealizationNearAnchorPoint_of_canonicalLocalInverseSweepProviderData C)

/-- Top-level universal-path analytic constructor from the concrete canonical IFT
package.  Universal paths discharge the depth-one basis targets mechanically, so callers
do not need to expose the canonical provider wrapper. -/
noncomputable def texSweepAnalyticData_of_paths_univ_canonicalIFTData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (I : TexSweepCanonicalIFTData D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_paths_univ_canonicalLocalInverseSweepProviderData
    hstep matching D hPaths
    (texSweepCanonicalLocalInverseSweepProviderData_of_canonicalIFTData I)

/-- Top-level universal-path analytic constructor from canonical pointwise IFT data and
a canonical local `Ψ` inverse selector.  This exposes the nondegenerate IFT fields and
the local realization proof while keeping source-path availability mechanical. -/
noncomputable def
    texSweepAnalyticData_of_paths_univ_canonicalIFTPointData_localPsiInverseNearAnchorData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (P : TexSweepCanonicalIFTPointData D)
    (I : TexSweepPsiLocalInverseNearAnchorData D
      (texSweepAnchorPointData_of_IDLData D))
    (hrealizes : TexSweepPsiLocalInverseRealizes I) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_paths_univ_canonicalIFTData hstep matching D hPaths
    (texSweepCanonicalIFTData_of_pointData_paths_univ_localPsiInverseNearAnchorData
      P hPaths I hrealizes)

/-- Top-level universal-path analytic constructor from canonical pointwise IFT data and
bundled local `Ψ` realization data. -/
noncomputable def
    texSweepAnalyticData_of_paths_univ_canonicalIFTPointData_localPsiInverseRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (P : TexSweepCanonicalIFTPointData D)
    (R : TexSweepCanonicalPsiLocalInverseRealizationData D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_paths_univ_canonicalIFTData hstep matching D hPaths
    (texSweepCanonicalIFTData_of_pointData_paths_univ_localPsiInverseRealizationData
      P hPaths R)

/-- Compile the non-canonical full-anchor/region provider to provider-facing local
inverse-sweep data.  The resulting provider is anchored at the transported full-anchor
tail point, not at the canonical `IDLData` choice. -/
noncomputable def texSweepLocalInverseSweepProviderData_of_fullAnchorRegionData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepLocalIFTFullAnchorRegionData D) :
    TexSweepLocalInverseSweepProviderData D :=
  texSweepLocalInverseSweepProviderData_of_localIFTData D
    (texSweepAnchorPointData_of_fullUnwoundAnchor D P.unwinding)
    (texSweepLocalIFTData_of_fullAnchorRegionData
      hL hstep matching D P)

/-- Provider-facing local inverse-sweep data from the compact full-anchor
local-realization frontier. -/
noncomputable def
    texSweepLocalInverseSweepProviderData_of_fullAnchorLocalRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepFullAnchorLocalRealizationData D) :
    TexSweepLocalInverseSweepProviderData D :=
  texSweepLocalInverseSweepProviderData_of_fullAnchorRegionData
    hL hstep matching D
    (texSweepLocalIFTFullAnchorRegionData_of_fullAnchorLocalRealizationData P)

/-- Forget the selector details of the non-canonical full-anchor/region provider,
retaining only the local open realization package. -/
noncomputable def texSweepLocalRealizationData_of_fullAnchorRegionData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepLocalIFTFullAnchorRegionData D) :
    TexSweepLocalRealizationData D :=
  texSweepLocalRealizationData_of_localInverseSweepProviderData
    (texSweepLocalInverseSweepProviderData_of_fullAnchorRegionData
      hL hstep matching D P)

/-- Analytic constructor from a non-canonical full-anchor/region provider. -/
noncomputable def texSweepAnalyticData_of_fullAnchorRegionData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepLocalIFTFullAnchorRegionData D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_localInverseSweepProviderData hstep matching
    (texSweepLocalInverseSweepProviderData_of_fullAnchorRegionData
      hL hstep matching D P)

/-- Analytic constructor from a non-canonical full-anchor/region provider and the
exact realized-tail depth-one basis condition. -/
noncomputable def texSweepAnalyticData_of_fullAnchorRegionData_depthOneBasisCondition
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepLocalIFTFullAnchorRegionData D)
    (B : TexSweepDepthOneBasisRealizationCondition D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_fullAnchorRegionData hL hstep matching D P

/-- Analytic constructor from the compact full-anchor local-realization frontier and
the reduced conditional depth-one basis input.  The only determinant used to unpack the
input is the matched current first-skip determinant. -/
noncomputable def texSweepAnalyticData_of_fullAnchorLocalRealizationData_basisInput
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepFullAnchorLocalRealizationData D)
    (B : TexSweepDepthOneBasisRealizationInput D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_fullAnchorRegionData_depthOneBasisCondition
    hL hstep matching D
    (texSweepLocalIFTFullAnchorRegionData_of_fullAnchorLocalRealizationData P)
    (depthOneBasisRealizationCondition_of_input
      (headValueSkip_det_ne_zero_of_matching hstep matching) B)

/-- Analytic constructor from the canonical near-anchor realization theorem and the
reduced conditional depth-one basis input.

This route stays anchored at `texSweepAnchorPointData_of_IDLData D`; it does not
retarget through a full unwound anchor, so no tail-anchor uniqueness assumption is
needed. -/
noncomputable def texSweepAnalyticData_of_nearAnchorPoint_basisInput
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D))
    (B : TexSweepDepthOneBasisRealizationInput D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_localRealizationData hstep matching
    (texSweepLocalRealizationData_of_nearAnchorPoint D
      (texSweepAnchorPointData_of_IDLData D) hnear)

/-- Analytic constructor from the concrete canonical near-anchor source surface and the
reduced conditional depth-one basis input. -/
noncomputable def
    texSweepAnalyticData_of_canonicalNearAnchorLocalRealizationData_basisInput
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (R : TexSweepCanonicalNearAnchorLocalRealizationData D)
    (B : TexSweepDepthOneBasisRealizationInput D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_nearAnchorPoint_basisInput hstep matching D
    (texSweepLocalRealizationNearAnchorPoint_of_canonicalNearAnchorLocalRealizationData
      R)
    B

/-- Analytic constructor from the canonical near-anchor realization theorem plus
tail-anchor uniqueness.  This is the smaller surface underlying the canonical-provider
route: the provider selector is not needed once the near-anchor theorem is available. -/
noncomputable def texSweepAnalyticData_of_nearAnchorPoint_tailAnchorUnique_basisInput
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D))
    (hunique : TexSweepTailAnchorUnique D)
    (B : TexSweepDepthOneBasisRealizationInput D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_fullAnchorLocalRealizationData_basisInput
    hL hstep matching D
    (texSweepFullAnchorLocalRealizationData_of_nearAnchorPoint_tailAnchorUnique
      hL D hnear hunique)
    B

/-- Realized-tail recursive analytic constructor from the canonical near-anchor
realization theorem.  After rewriting the current path class to a realized-tail path
set, the only remaining depth-one basis obligation is the displayed source-path
membership in the previous full path class, together with the previous first-skip
determinant. -/
noncomputable def texSweepAnalyticData_of_nearAnchorPoint_realizedTailPathSet
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D))
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem :
      L = 1 ->
        ∀ j : Fin d,
          constantProbePath
              ((0 : Fin d -> ℝ),
                ((skipB (Params.headValue θfull))⁻¹).mulVec
                  (((skipB (Params.headValue θ))⁻¹).mulVec
                    (Pi.single j (1 : ℝ)))) ∈
            FullPaths) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_nearAnchorPoint_basisInput hstep matching D hnear
    (depthOneBasisRealizationInput_of_realizedTailPathSet_sourcePath
      hPaths hdet_full source_mem)

/-- Bundled-obligation version of
`texSweepAnalyticData_of_nearAnchorPoint_realizedTailPathSet`. -/
noncomputable def
    texSweepAnalyticData_of_nearAnchorPoint_realizedTailDepthOneBasisSourcePathData
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D))
    (S : TexSweepRealizedTailDepthOneBasisSourcePathData D θfull FullPaths) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_nearAnchorPoint_basisInput hstep matching D hnear
    (depthOneBasisRealizationInput_of_realizedTailDepthOneBasisSourcePathData S)

/-- Bundled-obligation analytic constructor from the concrete canonical near-anchor
source surface. -/
noncomputable def
    texSweepAnalyticData_of_canonicalNearAnchorData_realizedTailBasis
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (R : TexSweepCanonicalNearAnchorLocalRealizationData D)
    (S : TexSweepRealizedTailDepthOneBasisSourcePathData D θfull FullPaths) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_canonicalNearAnchorLocalRealizationData_basisInput
    hstep matching D R
    (depthOneBasisRealizationInput_of_realizedTailDepthOneBasisSourcePathData S)

/-- Realized-tail recursive analytic constructor from an all-realized constant-tail
premise, which supplies the canonical near-anchor realization automatically. -/
noncomputable def
    texSweepAnalyticData_of_all_realized_realizedTailDepthOneBasisSourcePathData
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (all_realized :
      ∀ η : ProbePoint d,
        constantProbePath η ∈ realizedTailPathSet r θ D.Paths)
    (S : TexSweepRealizedTailDepthOneBasisSourcePathData D θfull FullPaths) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_nearAnchorPoint_realizedTailDepthOneBasisSourcePathData
    hstep matching D
    (texSweepLocalRealizationNearAnchorPoint_of_all_realized D all_realized) S

/-- Realized-tail recursive analytic constructor when the previous full path class is
universal and the previous first-skip determinant follows from matching. -/
noncomputable def
    texSweepAnalyticData_of_nearAnchorPoint_realizedTailPathSet_fullPaths_univ_matching
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D))
    (hstep_full :
      TexGenericStepClauses Lfull d (TexGeneric Lfull d)
        (fun η => TexAnchorCertificate η) θfull')
    (matching_full : FirstLayerMatchedData θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hFullPaths : FullPaths = Set.univ) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_nearAnchorPoint_realizedTailDepthOneBasisSourcePathData
    hstep matching D hnear
    (texSweepRealizedTailDepthOneBasisSourcePathData_of_fullPaths_univ_matching
      hstep_full matching_full hPaths hFullPaths)

/-- Realized-tail recursive analytic constructor whose previous source-path membership is
discharged by the previous `IDLData` open set, with the previous determinant coming from
matching. -/
noncomputable def
    texSweepAnalyticData_of_nearAnchorPoint_realizedTailPathSet_source_mem_open_matching
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D))
    (hstep_full :
      TexGenericStepClauses Lfull d (TexGeneric Lfull d)
        (fun η => TexAnchorCertificate η) θfull')
    (matching_full : FirstLayerMatchedData θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (source_mem_open :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θfull))⁻¹).mulVec
              (((skipB (Params.headValue θ))⁻¹).mulVec
                (Pi.single j (1 : ℝ)))) ∈
            Dfull.O) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_nearAnchorPoint_realizedTailDepthOneBasisSourcePathData
    hstep matching D hnear
    (texSweepRealizedTailDepthOneBasisSourcePathData_of_source_mem_open_matching
      Dfull hstep_full matching_full hPaths source_mem_open)

/-- Realized-tail recursive analytic constructor from the compact full-anchor frontier.
After rewriting the current path class to a realized-tail path set, the only basis
obligation left at depth one is membership of the displayed source constants in the
previous full path class. -/
noncomputable def
    texSweepAnalyticData_of_fullAnchorLocalRealizationData_realizedTailPathSet
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepFullAnchorLocalRealizationData D)
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem :
      L = 1 ->
        ∀ j : Fin d,
          constantProbePath
              ((0 : Fin d -> ℝ),
                ((skipB (Params.headValue θfull))⁻¹).mulVec
                  (((skipB (Params.headValue θ))⁻¹).mulVec
                    (Pi.single j (1 : ℝ)))) ∈
            FullPaths) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_fullAnchorLocalRealizationData_basisInput
    hL hstep matching D P
    (depthOneBasisRealizationInput_of_realizedTailPathSet_sourcePath
      hPaths hdet_full source_mem)

/-- Realized-tail recursive analytic constructor from the canonical near-anchor
realization theorem and tail-anchor uniqueness.  The remaining depth-one basis
obligation is still only the displayed source-path membership in the previous full path
class. -/
noncomputable def
    texSweepAnalyticData_of_nearAnchorPoint_tailAnchorUnique_realizedTailPathSet
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D))
    (hunique : TexSweepTailAnchorUnique D)
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem :
      L = 1 ->
        ∀ j : Fin d,
          constantProbePath
              ((0 : Fin d -> ℝ),
                ((skipB (Params.headValue θfull))⁻¹).mulVec
                  (((skipB (Params.headValue θ))⁻¹).mulVec
                    (Pi.single j (1 : ℝ)))) ∈
            FullPaths) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_nearAnchorPoint_tailAnchorUnique_basisInput
    hL hstep matching D hnear hunique
    (depthOneBasisRealizationInput_of_realizedTailPathSet_sourcePath
      hPaths hdet_full source_mem)

/-- Realized-tail recursive analytic constructor whose remaining source-path
membership is discharged by the previous `IDLData` open set. -/
noncomputable def
    texSweepAnalyticData_of_fullAnchorLocalRealizationData_realizedTailPathSet_source_mem_open
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (P : TexSweepFullAnchorLocalRealizationData D)
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem_open :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θfull))⁻¹).mulVec
              (((skipB (Params.headValue θ))⁻¹).mulVec
                (Pi.single j (1 : ℝ)))) ∈
            Dfull.O) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_fullAnchorLocalRealizationData_basisInput
    hL hstep matching D P
    (depthOneBasisRealizationInput_of_realizedTailPathSet_of_source_mem_open
      Dfull hPaths hdet_full source_mem_open)

/-- Analytic constructor from canonical local inverse data plus tail-anchor uniqueness,
compiled through the compact full-anchor local-realization frontier and the reduced
depth-one basis input. -/
noncomputable def
    texSweepAnalyticData_of_canonicalProvider_tailAnchorUnique_basisInput
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (C : TexSweepCanonicalLocalInverseSweepProviderData D)
    (hunique : TexSweepTailAnchorUnique D)
    (B : TexSweepDepthOneBasisRealizationInput D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_fullAnchorLocalRealizationData_basisInput
    hL hstep matching D
    (texSweepFullAnchorLocalRealizationData_of_canonicalProvider_tailAnchorUnique
      hL D C hunique)
    B

/-- Realized-tail recursive analytic constructor from canonical local inverse data and
tail-anchor uniqueness.  The only remaining basis obligation is the source-path
membership in the previous full path class. -/
noncomputable def
    texSweepAnalyticData_of_canonicalProvider_tailAnchorUnique_realizedTailPathSet
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (C : TexSweepCanonicalLocalInverseSweepProviderData D)
    (hunique : TexSweepTailAnchorUnique D)
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem :
      L = 1 ->
        ∀ j : Fin d,
          constantProbePath
              ((0 : Fin d -> ℝ),
                ((skipB (Params.headValue θfull))⁻¹).mulVec
                  (((skipB (Params.headValue θ))⁻¹).mulVec
                    (Pi.single j (1 : ℝ)))) ∈
            FullPaths) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_canonicalProvider_tailAnchorUnique_basisInput
    hL hstep matching D C hunique
    (depthOneBasisRealizationInput_of_realizedTailPathSet_sourcePath
      hPaths hdet_full source_mem)

/-- Top-level universal-path analytic constructor from the non-canonical
full-anchor/region provider.  Universal paths discharge the depth-one basis targets
mechanically, so no canonical anchor equality is required. -/
noncomputable def texSweepAnalyticData_of_paths_univ_fullAnchorRegionData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (P : TexSweepLocalIFTFullAnchorRegionData D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_paths_univ_localInverseSweepProviderData
    hstep matching D hPaths
    (texSweepLocalInverseSweepProviderData_of_fullAnchorRegionData
      hL hstep matching D P)

/-- Top-level universal-path analytic constructor from the compact full-anchor
local-realization frontier.  Universal paths discharge the reduced depth-one basis
input, so the only sweep provider input is the compact local realization package. -/
noncomputable def texSweepAnalyticData_of_paths_univ_fullAnchorLocalRealizationData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (P : TexSweepFullAnchorLocalRealizationData D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_paths_univ_fullAnchorRegionData
    hL hstep matching D hPaths
    (texSweepLocalIFTFullAnchorRegionData_of_fullAnchorLocalRealizationData P)

/-- Top-level universal-path analytic constructor from the canonical near-anchor
realization theorem plus tail-anchor uniqueness.  Universal paths discharge the
depth-one basis targets; the canonical provider wrapper is not needed. -/
noncomputable def texSweepAnalyticData_of_paths_univ_nearAnchorPoint_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D))
    (hunique : TexSweepTailAnchorUnique D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_paths_univ_fullAnchorLocalRealizationData
    hL hstep matching D hPaths
    (texSweepFullAnchorLocalRealizationData_of_nearAnchorPoint_tailAnchorUnique
      hL D hnear hunique)

/-- Top-level universal-path analytic constructor from canonical local inverse data and
tail-anchor uniqueness, compiled through the compact full-anchor frontier. -/
noncomputable def
    texSweepAnalyticData_of_paths_univ_canonicalProvider_tailAnchorUnique
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (C : TexSweepCanonicalLocalInverseSweepProviderData D)
    (hunique : TexSweepTailAnchorUnique D) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_paths_univ_fullAnchorLocalRealizationData
    hL hstep matching D hPaths
    (texSweepFullAnchorLocalRealizationData_of_canonicalProvider_tailAnchorUnique
      hL D C hunique)

/-- If the swept tail region is all probes, the tail-anchor clause follows from the
current `IDLData` anchor clause.  The depth-zero tail case is vacuous for unwinding and
is handled by the empty-depth anchor package. -/
theorem tail_anchor_nonempty_univ_of_IDLData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') :
    L = 1 ∨ (Set.univ ∩ unwoundAnchorSet (Params.tail θ')).Nonempty := by
  rcases L with _ | L
  · right
    rcases unwoundAnchorSet_nonempty_of_depth_le_one (Params.tail θ') (by omega) with
      ⟨p, hp⟩
    exact ⟨p, by simp [hp]⟩
  · rcases L with _ | L
    · exact Or.inl rfl
    · right
      rcases D.anchor_nonempty with hdepth | hanchor
      · omega
      · rcases hanchor with ⟨p, _hpO, hpAnchor⟩
        rcases tail_unwoundAnchorSet_nonempty_of_full_anchor hpAnchor with
          ⟨ptail, hptail⟩
        exact ⟨ptail, by simp [hptail]⟩

/-- Core sweep data for the special case where every constant tail probe is realized,
so the swept region can be `Set.univ`. -/
noncomputable def texSweepRegionCoreData_univ_of_all_realized
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (all_realized :
      ∀ p : ProbePoint d,
        constantProbePath p ∈ realizedTailPathSet r θ D.Paths) :
    TexSweepRegionCoreData D where
  U := Set.univ
  U_open := isOpen_univ
  U_nonempty := ⟨((fun _ => 0), (fun _ => 0)), by simp⟩
  U_subset_realized := by
    intro p _hp
    exact all_realized p
  tail_anchor_nonempty := tail_anchor_nonempty_univ_of_IDLData D

/-- Universal core sweep data from the corrected first-layer `sig(log r)` surjectivity
obligation.  This is the provider-facing replacement for assuming raw realized-tail
membership of every constant probe. -/
noncomputable def texSweepRegionCoreData_univ_of_siglog_surjective
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (hsurj : FirstLayerSiglogConstantTailSurjective r
      (Params.headValue θ) (Params.headAttention θ)) :
    TexSweepRegionCoreData D :=
  texSweepRegionCoreData_univ_of_all_realized D
    (allConstant_mem_realizedTailPathSet_of_paths_univ_of_siglog_surjective
      D hPaths hsurj)

/-- Universal all-realized region constructor for the uniform full-anchor membership
package.  The region is exactly `Set.univ`, so transported full-anchor membership is
automatic. -/
noncomputable def texSweepFullAnchorRegionMembershipData_univ_of_all_realized
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (all_realized :
      ∀ q : ProbePoint d,
        constantProbePath q ∈ realizedTailPathSet r θ D.Paths) :
    TexSweepFullAnchorRegionMembershipData D :=
  texSweepFullAnchorRegionMembershipData_of_regionCoreData_eq_univ
    (texSweepRegionCoreData_univ_of_all_realized D all_realized) rfl

/-- Universal-path `sig(log r)` constructor for the uniform full-anchor membership
package.  This uses only the corrected siglog-surjectivity obligation and the fact that
the chosen swept region is `Set.univ`. -/
noncomputable def
    texSweepFullAnchorRegionMembershipData_paths_univ_siglog_surjective
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (hsurj : FirstLayerSiglogConstantTailSurjective r
      (Params.headValue θ) (Params.headAttention θ)) :
    TexSweepFullAnchorRegionMembershipData D :=
  texSweepFullAnchorRegionMembershipData_of_regionCoreData_eq_univ
    (texSweepRegionCoreData_univ_of_siglog_surjective D hPaths hsurj) rfl

/-- Universal all-realized constructor that selects the full anchor from
`IDLData.anchor_nonempty` and packages the resulting compact full-anchor/region data.
No caller-provided transported-anchor membership proof is needed because the region is
`Set.univ`. -/
noncomputable def texSweepLocalIFTFullAnchorRegionData_of_IDLData_univ_all_realized
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (all_realized :
      ∀ q : ProbePoint d,
        constantProbePath q ∈ realizedTailPathSet r θ D.Paths) :
    TexSweepLocalIFTFullAnchorRegionData D :=
  texSweepLocalIFTFullAnchorRegionData_of_IDLData_anchorRegionMembership hL D
    (texSweepFullAnchorRegionMembershipData_univ_of_all_realized D all_realized)

/-- Universal all-realized constructor for the compact full-anchor local-realization
frontier.  The selected full anchor comes from `IDLData.anchor_nonempty`, and
membership in the swept region is automatic because the region is `Set.univ`. -/
noncomputable def texSweepFullAnchorLocalRealizationData_of_IDLData_univ_all_realized
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (all_realized :
      ∀ q : ProbePoint d,
        constantProbePath q ∈ realizedTailPathSet r θ D.Paths) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_IDLData_anchorRegionMembership hL D
    (texSweepFullAnchorRegionMembershipData_univ_of_all_realized D all_realized)

/-- Universal-path `sig(log r)` constructor that selects the full anchor from
`IDLData.anchor_nonempty` and packages the compact full-anchor/region data. -/
noncomputable def
    texSweepLocalIFTFullAnchorRegionData_of_IDLData_paths_univ_siglog_surjective
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (hPaths : D.Paths = Set.univ)
    (hsurj : FirstLayerSiglogConstantTailSurjective r
      (Params.headValue θ) (Params.headAttention θ)) :
    TexSweepLocalIFTFullAnchorRegionData D :=
  texSweepLocalIFTFullAnchorRegionData_of_IDLData_anchorRegionMembership hL D
    (texSweepFullAnchorRegionMembershipData_paths_univ_siglog_surjective
      D hPaths hsurj)

/-- Universal all-realized region constructor for the compact non-canonical
full-anchor/region provider.  Since the swept region is `Set.univ`, no separate
membership proof for the transported full-anchor tail point is needed. -/
noncomputable def
    texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_univ_all_realized
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (all_realized :
      ∀ q : ProbePoint d,
        constantProbePath q ∈ realizedTailPathSet r θ D.Paths) :
    TexSweepLocalIFTFullAnchorRegionData D :=
  texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_regionCoreData_mem
    hpO W (texSweepRegionCoreData_univ_of_all_realized D all_realized)
    (Set.mem_univ _)

/-- Universal-path `sig(log r)` constructor for the compact non-canonical
full-anchor/region provider.  This is the non-canonical full-anchor analogue of
`texSweepRegionCoreData_univ_of_siglog_surjective`. -/
noncomputable def
    texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_paths_univ_siglog_surjective
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'} {p : AnchorProbe d}
    (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (hPaths : D.Paths = Set.univ)
    (hsurj : FirstLayerSiglogConstantTailSurjective r
      (Params.headValue θ) (Params.headAttention θ)) :
    TexSweepLocalIFTFullAnchorRegionData D :=
  texSweepLocalIFTFullAnchorRegionData_of_fullUnwoundAnchor_regionCoreData_mem
    hpO W (texSweepRegionCoreData_univ_of_siglog_surjective D hPaths hsurj)
    (Set.mem_univ _)

/-- Universal-path `sig(log r)` preimage data gives a canonical-anchor local `Ψ`
inverse selector.  Path availability is intentionally separate, since it uses
`D.Paths = Set.univ`. -/
noncomputable def texSweepPsiLocalInverseNearAnchorData_of_paths_univ_siglog_surjective
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (hsurj : FirstLayerSiglogConstantTailSurjective r
      (Params.headValue θ) (Params.headAttention θ)) :
    TexSweepPsiLocalInverseNearAnchorData D (texSweepAnchorPointData_of_IDLData D) where
  U := Set.univ
  U_open := isOpen_univ
  anchor_mem := by simp
  source := fun η _hη => constantProbePath (Classical.choose (hsurj η))

/-- In the universal-path case, every source selected by the `sig(log r)` local inverse
belongs to the current path class. -/
theorem texSweepPsiLocalInverseSourcesAvailable_of_paths_univ_siglog_surjective
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (hsurj : FirstLayerSiglogConstantTailSurjective r
      (Params.headValue θ) (Params.headAttention θ)) :
    TexSweepPsiLocalInverseSourcesAvailable
      (texSweepPsiLocalInverseNearAnchorData_of_paths_univ_siglog_surjective
        D hsurj) := by
  intro η _hη
  rw [hPaths]
  exact Set.mem_univ _

/-- The source selected by the universal-path `sig(log r)` local inverse realizes the
requested constant tail target. -/
theorem texSweepPsiLocalInverseRealizes_of_paths_univ_siglog_surjective
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (hsurj : FirstLayerSiglogConstantTailSurjective r
      (Params.headValue θ) (Params.headAttention θ)) :
    TexSweepPsiLocalInverseRealizes
      (texSweepPsiLocalInverseNearAnchorData_of_paths_univ_siglog_surjective
        D hsurj) := by
  intro η hη
  rcases Classical.choose_spec (hsurj η) with ⟨hslope, hmap⟩
  refine ⟨?_⟩
  simpa [texSweepPsiLocalInverseNearAnchorData_of_paths_univ_siglog_surjective,
    Params.headValue, Params.headAttention, Params.headLayer, hmap] using
    constantSourceRealizationData_of_slope_zero
      (r := r) (V := Params.headValue θ) (A := Params.headAttention θ)
      (Classical.choose (hsurj η)) hslope

/-- Universal paths plus first-layer `sig(log r)` constant-tail surjectivity directly
prove the canonical near-anchor local realization theorem. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_paths_univ_siglog_surjective
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (hsurj : FirstLayerSiglogConstantTailSurjective r
      (Params.headValue θ) (Params.headAttention θ)) :
    TexSweepLocalRealizationNearAnchorPoint D
      (texSweepAnchorPointData_of_IDLData D) :=
  texSweepLocalRealizationNearAnchorPoint_of_localPsiInverseNearAnchorData
    (texSweepPsiLocalInverseNearAnchorData_of_paths_univ_siglog_surjective
      D hsurj)
    (texSweepPsiLocalInverseSourcesAvailable_of_paths_univ_siglog_surjective
      D hPaths hsurj)
    (texSweepPsiLocalInverseRealizes_of_paths_univ_siglog_surjective
      D hsurj)

/-- Lifted universal-path `sig(log r)` constructor matching the active universal sweep
provider field. -/
def texSweepLocalRealizationNearAnchorPoint_plift_of_paths_univ_siglog_surjective
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (hsurj : FirstLayerSiglogConstantTailSurjective r
      (Params.headValue θ) (Params.headAttention θ)) :
    PLift
      (TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D)) :=
  PLift.up
    (texSweepLocalRealizationNearAnchorPoint_of_paths_univ_siglog_surjective
      D hPaths hsurj)

/-- Universal-path canonical provider from the corrected first-layer `sig(log r)`
constant-tail surjectivity obligation. -/
noncomputable def texSweepCanonicalLocalInverseSweepProviderData_of_paths_univ_siglog_surjective
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (hsurj : FirstLayerSiglogConstantTailSurjective r
      (Params.headValue θ) (Params.headAttention θ)) :
    TexSweepCanonicalLocalInverseSweepProviderData D :=
  texSweepCanonicalLocalInverseSweepProviderData_of_localPsiInverseNearAnchorData
    (texSweepPsiLocalInverseNearAnchorData_of_paths_univ_siglog_surjective
      D hsurj)
    (texSweepPsiLocalInverseSourcesAvailable_of_paths_univ_siglog_surjective
      D hPaths hsurj)
    (texSweepPsiLocalInverseRealizes_of_paths_univ_siglog_surjective
      D hsurj)

/-- Top-level universal-path provider data from the corrected first-layer `sig(log r)`
constant-tail surjectivity obligation. -/
noncomputable def texSweepLocalInverseSweepProviderData_of_paths_univ_siglog_surjective
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (hsurj : FirstLayerSiglogConstantTailSurjective r
      (Params.headValue θ) (Params.headAttention θ)) :
    TexSweepLocalInverseSweepProviderData D :=
  texSweepLocalInverseSweepProviderData_of_canonicalLocalInverseSweepProviderData
    (texSweepCanonicalLocalInverseSweepProviderData_of_paths_univ_siglog_surjective
      D hPaths hsurj)

/-- Analytic sweep data for a universal swept region, with the basis-path clause kept
explicit for recursive uses. -/
noncomputable def texSweepAnalyticData_of_univ_region_all_realized
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (all_realized :
      ∀ p : ProbePoint d,
        constantProbePath p ∈ realizedTailPathSet r θ D.Paths)
    (base_value_paths_available :
      L = 1 ->
        ∀ j : Fin d,
          constantProbePath ((0 : Fin d -> ℝ), Pi.single j (1 : ℝ)) ∈
            realizedTailPathSet r θ D.Paths) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_regionCoreData hstep matching
    (texSweepRegionCoreData_univ_of_all_realized D all_realized)

/-- Top-level universal-path constructor for a universal swept region.  The only
geometric input is that every constant tail probe is realized; basis targets are then
filled by `base_value_mem_realizedTailPathSet_of_paths_univ`, and the tail anchor comes
from `IDLData.anchor_nonempty`. -/
noncomputable def texSweepAnalyticData_of_paths_univ_all_realized
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (all_realized :
      ∀ p : ProbePoint d,
        constantProbePath p ∈ realizedTailPathSet r θ D.Paths) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_univ_region_all_realized hstep matching D all_realized (by
    intro _hL j
    exact base_value_mem_realizedTailPathSet_of_paths_univ hstep matching D hPaths j)

/-- Top-level universal-path constructor using the corrected `sig(log r)` constant-tail
surjectivity obligation for the first effective layer. -/
noncomputable def texSweepAnalyticData_of_paths_univ_siglog_surjective
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (hsurj : FirstLayerSiglogConstantTailSurjective r
      (Params.headValue θ) (Params.headAttention θ)) :
    TexSweepAnalyticData hstep matching D :=
  texSweepAnalyticData_of_paths_univ_canonicalLocalInverseSweepProviderData
    hstep matching D hPaths
    (texSweepCanonicalLocalInverseSweepProviderData_of_paths_univ_siglog_surjective
      D hPaths hsurj)

/-- Realization/sweep transfer: after matching the first layer, produce the lower-depth
IDL data needed by the induction hypothesis. -/
noncomputable def tail_IDLData_of_texGenericStep
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (R : TexSweepRegionData D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') := by
  let sweep := sweepData_of_texGenericStep hd hr hstep matching D R
  have hr_pos : 0 < r := Nat.lt_of_lt_of_le (by decide) hr
  exact
    { primed_generic := by
        simpa [Params.tail] using hstep.tail_generic
      O := sweep.2.tailRegion
      O_open := sweep.2.tailRegion_open
      O_nonempty := sweep.2.tailRegion_nonempty
      anchor_nonempty := sweep.2.tail_anchor_nonempty
      Paths := sweep.1
      path_agreement := sweep.2.tail_observableAgreement hr_pos D.path_agreement
      constant_paths_available := sweep.2.constant_paths_available }

/-- Open-realization form of the tail handoff.  This is the mechanical preservation
statement for the path-rich sweep invariant: explicit realization of an open set of
constant tail probes produces the lower-depth `IDLData` with tail paths defined by
`realizedTailPathSet`, and observable agreement is transported through
`SweepData.lifts`. -/
noncomputable def tail_IDLData_of_texGenericStep_of_openRealizationData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (R : TexSweepOpenRealizationData D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep hd hr hstep matching D
    (texSweepRegionData_of_openRealizationData R)

/-- Local-realization form of the tail handoff. -/
noncomputable def tail_IDLData_of_texGenericStep_of_localRealizationData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (R : TexSweepLocalRealizationData D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_openRealizationData hd hr hstep matching D
    (texSweepOpenRealizationData_of_localRealizationData R)

/-- Provider-facing local inverse-sweep form of the tail handoff. -/
noncomputable def tail_IDLData_of_texGenericStep_of_localInverseSweepProviderData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepLocalInverseSweepProviderData D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_localRealizationData hd hr hstep matching D
    (texSweepLocalRealizationData_of_localInverseSweepProviderData P)

/-- Top-level universal-path local-realization tail handoff.  The provider supplies only
the local open realization; basis targets are discharged by `Paths = Set.univ`. -/
noncomputable def tail_IDLData_of_texGenericStep_of_paths_univ_localRealizationData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (R : TexSweepLocalRealizationData D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_openRealizationData hd hr hstep matching D
    (texSweepOpenRealizationData_of_paths_univ_localRealizationData
      hstep matching D hPaths R)

/-- Top-level universal-path provider-facing local inverse-sweep tail handoff.  The
provider supplies only the local inverse-sweep package; basis targets are discharged by
`Paths = Set.univ`. -/
noncomputable def tail_IDLData_of_texGenericStep_of_paths_univ_localInverseSweepProviderData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (P : TexSweepLocalInverseSweepProviderData D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_paths_univ_localRealizationData
    hd hr hstep matching D hPaths
    (texSweepLocalRealizationData_of_localInverseSweepProviderData P)

/-- Top-level universal-path canonical-anchor provider tail handoff. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_paths_univ_canonicalLocalInverseSweepProviderData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (C : TexSweepCanonicalLocalInverseSweepProviderData D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_paths_univ_localInverseSweepProviderData
    hd hr hstep matching D hPaths
    (texSweepLocalInverseSweepProviderData_of_canonicalLocalInverseSweepProviderData C)

/-- Arbitrary-path canonical-provider tail handoff using the exact realized-tail basis
condition instead of the unfolded existential basis clause. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_canonicalLocalInverseSweepProviderData_depthOneBasisCondition
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (C : TexSweepCanonicalLocalInverseSweepProviderData D)
    (B : TexSweepDepthOneBasisRealizationCondition D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_localInverseSweepProviderData hd hr
    hstep matching D
    (texSweepLocalInverseSweepProviderData_of_canonicalLocalInverseSweepProviderData C)

/-- Arbitrary-path canonical IFT tail handoff with the exact realized-tail basis
condition exposed directly. -/
noncomputable def tail_IDLData_of_texGenericStep_of_canonicalIFTData_depthOneBasisCondition
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (I : TexSweepCanonicalIFTData D)
    (B : TexSweepDepthOneBasisRealizationCondition D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_canonicalLocalInverseSweepProviderData_depthOneBasisCondition
    hd hr hstep matching D
    (texSweepCanonicalLocalInverseSweepProviderData_of_canonicalIFTData I) B

/-- Arbitrary-path canonical-provider tail handoff using the reduced conditional
depth-one basis input. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_canonicalLocalInverseSweepProviderData_basisInput
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (C : TexSweepCanonicalLocalInverseSweepProviderData D)
    (B : TexSweepDepthOneBasisRealizationInput D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_canonicalLocalInverseSweepProviderData_depthOneBasisCondition
    hd hr hstep matching D C
    (depthOneBasisRealizationCondition_of_input
      (headValueSkip_det_ne_zero_of_matching hstep matching) B)

/-- Arbitrary-path canonical IFT tail handoff using the reduced conditional depth-one
basis input. -/
noncomputable def tail_IDLData_of_texGenericStep_of_canonicalIFTData_basisInput
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (I : TexSweepCanonicalIFTData D)
    (B : TexSweepDepthOneBasisRealizationInput D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_canonicalIFTData_depthOneBasisCondition
    hd hr hstep matching D I
    (depthOneBasisRealizationCondition_of_input
      (headValueSkip_det_ne_zero_of_matching hstep matching) B)

/-- Realized-tail recursive tail handoff from canonical local inverse data, with no
tail-anchor uniqueness assumption. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_canonicalLocalInverseSweepProviderData_realizedTailPathSet
    {L Lfull d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (C : TexSweepCanonicalLocalInverseSweepProviderData D)
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem :
      L = 1 ->
        ∀ j : Fin d,
          constantProbePath
              ((0 : Fin d -> ℝ),
                ((skipB (Params.headValue θfull))⁻¹).mulVec
                  (((skipB (Params.headValue θ))⁻¹).mulVec
                    (Pi.single j (1 : ℝ)))) ∈
            FullPaths) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_canonicalLocalInverseSweepProviderData_basisInput
    hd hr hstep matching D C
    (depthOneBasisRealizationInput_of_realizedTailPathSet_sourcePath
      hPaths hdet_full source_mem)

/-- Realized-tail recursive tail handoff from canonical IFT data, with no tail-anchor
uniqueness assumption. -/
noncomputable def tail_IDLData_of_texGenericStep_of_canonicalIFTData_realizedTailPathSet
    {L Lfull d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (I : TexSweepCanonicalIFTData D)
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem :
      L = 1 ->
        ∀ j : Fin d,
          constantProbePath
              ((0 : Fin d -> ℝ),
                ((skipB (Params.headValue θfull))⁻¹).mulVec
                  (((skipB (Params.headValue θ))⁻¹).mulVec
                    (Pi.single j (1 : ℝ)))) ∈
            FullPaths) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_canonicalIFTData_basisInput
    hd hr hstep matching D I
    (depthOneBasisRealizationInput_of_realizedTailPathSet_sourcePath
      hPaths hdet_full source_mem)

/-- Top-level universal-path canonical IFT tail handoff.  The basis targets are filled
mechanically from `Paths = Set.univ`. -/
noncomputable def tail_IDLData_of_texGenericStep_of_paths_univ_canonicalIFTData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (I : TexSweepCanonicalIFTData D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_paths_univ_canonicalLocalInverseSweepProviderData
    hd hr hstep matching D hPaths
    (texSweepCanonicalLocalInverseSweepProviderData_of_canonicalIFTData I)

/-- Arbitrary-path tail handoff from a non-canonical full-anchor/region provider, using
the exact realized-tail depth-one basis condition. -/
noncomputable def tail_IDLData_of_texGenericStep_of_fullAnchorRegionData_depthOneBasisCondition
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepLocalIFTFullAnchorRegionData D)
    (B : TexSweepDepthOneBasisRealizationCondition D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_localInverseSweepProviderData hd hr
    hstep matching D
    (texSweepLocalInverseSweepProviderData_of_fullAnchorRegionData
      hL hstep matching D P)

/-- Arbitrary-path tail handoff from the compact full-anchor local-realization frontier
and the reduced conditional depth-one basis input. -/
noncomputable def tail_IDLData_of_texGenericStep_of_fullAnchorLocalRealizationData_basisInput
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepFullAnchorLocalRealizationData D)
    (B : TexSweepDepthOneBasisRealizationInput D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_fullAnchorRegionData_depthOneBasisCondition
    hd hr hL hstep matching D
    (texSweepLocalIFTFullAnchorRegionData_of_fullAnchorLocalRealizationData P)
    (depthOneBasisRealizationCondition_of_input
      (headValueSkip_det_ne_zero_of_matching hstep matching) B)

/-- Arbitrary-path tail handoff from the canonical near-anchor realization theorem and
the reduced conditional depth-one basis input.

This is the direct canonical-anchor route: it does not retarget through a full unwound
anchor and therefore does not require `TexSweepTailAnchorUnique`. -/
noncomputable def tail_IDLData_of_texGenericStep_of_nearAnchorPoint_basisInput
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D))
    (B : TexSweepDepthOneBasisRealizationInput D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_localRealizationData hd hr hstep matching D
    (texSweepLocalRealizationData_of_nearAnchorPoint D
      (texSweepAnchorPointData_of_IDLData D) hnear)

/-- Arbitrary-path tail handoff from the concrete canonical near-anchor source surface
and the reduced conditional depth-one basis input. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_canonicalNearAnchorLocalRealizationData_basisInput
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (R : TexSweepCanonicalNearAnchorLocalRealizationData D)
    (B : TexSweepDepthOneBasisRealizationInput D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_nearAnchorPoint_basisInput
    hd hr hstep matching D
    (texSweepLocalRealizationNearAnchorPoint_of_canonicalNearAnchorLocalRealizationData
      R)
    B

/-- Arbitrary-path tail handoff from the canonical near-anchor realization theorem plus
tail-anchor uniqueness and the reduced conditional depth-one basis input. -/
noncomputable def tail_IDLData_of_texGenericStep_of_nearAnchorPoint_tailAnchorUnique_basisInput
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D))
    (hunique : TexSweepTailAnchorUnique D)
    (B : TexSweepDepthOneBasisRealizationInput D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_fullAnchorLocalRealizationData_basisInput
    hd hr hL hstep matching D
    (texSweepFullAnchorLocalRealizationData_of_nearAnchorPoint_tailAnchorUnique
      hL D hnear hunique)
    B

/-- Realized-tail recursive tail handoff from the canonical near-anchor realization
theorem.  The remaining depth-one basis obligation is the displayed source-path
membership in the previous full path class, plus the previous first-skip determinant. -/
noncomputable def tail_IDLData_of_texGenericStep_of_nearAnchorPoint_realizedTailPathSet
    {L Lfull d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D))
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem :
      L = 1 ->
        ∀ j : Fin d,
          constantProbePath
              ((0 : Fin d -> ℝ),
                ((skipB (Params.headValue θfull))⁻¹).mulVec
                  (((skipB (Params.headValue θ))⁻¹).mulVec
                    (Pi.single j (1 : ℝ)))) ∈
            FullPaths) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_nearAnchorPoint_basisInput
    hd hr hstep matching D hnear
    (depthOneBasisRealizationInput_of_realizedTailPathSet_sourcePath
      hPaths hdet_full source_mem)

/-- Bundled-obligation version of
`tail_IDLData_of_texGenericStep_of_nearAnchorPoint_realizedTailPathSet`. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_nearAnchorPoint_realizedTailDepthOneBasisSourcePathData
    {L Lfull d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D))
    (S : TexSweepRealizedTailDepthOneBasisSourcePathData D θfull FullPaths) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_nearAnchorPoint_basisInput
    hd hr hstep matching D hnear
    (depthOneBasisRealizationInput_of_realizedTailDepthOneBasisSourcePathData S)

/-- Bundled-obligation tail handoff from the concrete canonical near-anchor source
surface. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_canonicalNearAnchorData_realizedTailBasis
    {L Lfull d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (R : TexSweepCanonicalNearAnchorLocalRealizationData D)
    (S : TexSweepRealizedTailDepthOneBasisSourcePathData D θfull FullPaths) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_canonicalNearAnchorLocalRealizationData_basisInput
    hd hr hstep matching D R
    (depthOneBasisRealizationInput_of_realizedTailDepthOneBasisSourcePathData S)

/-- Realized-tail recursive tail handoff from an all-realized constant-tail premise,
which supplies the canonical near-anchor realization automatically. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_all_realized_realizedTailDepthOneBasisSourcePathData
    {L Lfull d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (all_realized :
      ∀ η : ProbePoint d,
        constantProbePath η ∈ realizedTailPathSet r θ D.Paths)
    (S : TexSweepRealizedTailDepthOneBasisSourcePathData D θfull FullPaths) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_nearAnchorPoint_realizedTailDepthOneBasisSourcePathData
    hd hr hstep matching D
    (texSweepLocalRealizationNearAnchorPoint_of_all_realized D all_realized) S

/-- Realized-tail recursive tail handoff when the previous full path class is universal
and the previous first-skip determinant follows from matching. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_nearAnchorPoint_realizedTailPathSet_fullPaths_univ_matching
    {L Lfull d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D))
    (hstep_full :
      TexGenericStepClauses Lfull d (TexGeneric Lfull d)
        (fun η => TexAnchorCertificate η) θfull')
    (matching_full : FirstLayerMatchedData θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hFullPaths : FullPaths = Set.univ) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_nearAnchorPoint_realizedTailDepthOneBasisSourcePathData
    hd hr hstep matching D hnear
    (texSweepRealizedTailDepthOneBasisSourcePathData_of_fullPaths_univ_matching
      hstep_full matching_full hPaths hFullPaths)

/-- Realized-tail recursive tail handoff whose previous source-path membership is
discharged by the previous `IDLData` open set, with the previous determinant coming from
matching. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_nearAnchorPoint_realizedTailPathSet_source_mem_open_matching
    {L Lfull d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D))
    (hstep_full :
      TexGenericStepClauses Lfull d (TexGeneric Lfull d)
        (fun η => TexAnchorCertificate η) θfull')
    (matching_full : FirstLayerMatchedData θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (source_mem_open :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θfull))⁻¹).mulVec
              (((skipB (Params.headValue θ))⁻¹).mulVec
                (Pi.single j (1 : ℝ)))) ∈
            Dfull.O) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_nearAnchorPoint_realizedTailDepthOneBasisSourcePathData
    hd hr hstep matching D hnear
    (texSweepRealizedTailDepthOneBasisSourcePathData_of_source_mem_open_matching
      Dfull hstep_full matching_full hPaths source_mem_open)

/-- Realized-tail recursive tail handoff from the compact full-anchor local-realization
frontier.  The remaining depth-one basis obligation is the displayed source-path
membership in the previous full path class. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_fullAnchorLocalRealizationData_realizedTailPathSet
    {L Lfull d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (P : TexSweepFullAnchorLocalRealizationData D)
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem :
      L = 1 ->
        ∀ j : Fin d,
          constantProbePath
              ((0 : Fin d -> ℝ),
                ((skipB (Params.headValue θfull))⁻¹).mulVec
                  (((skipB (Params.headValue θ))⁻¹).mulVec
                    (Pi.single j (1 : ℝ)))) ∈
            FullPaths) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_fullAnchorLocalRealizationData_basisInput
    hd hr hL hstep matching D P
    (depthOneBasisRealizationInput_of_realizedTailPathSet_sourcePath
      hPaths hdet_full source_mem)

/-- Realized-tail recursive tail handoff from the canonical near-anchor realization
theorem and tail-anchor uniqueness.  The remaining depth-one basis obligation is the
displayed source-path membership in the previous full path class. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_nearAnchorPoint_tailAnchorUnique_realizedTailPathSet
    {L Lfull d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D))
    (hunique : TexSweepTailAnchorUnique D)
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem :
      L = 1 ->
        ∀ j : Fin d,
          constantProbePath
              ((0 : Fin d -> ℝ),
                ((skipB (Params.headValue θfull))⁻¹).mulVec
                  (((skipB (Params.headValue θ))⁻¹).mulVec
                    (Pi.single j (1 : ℝ)))) ∈
            FullPaths) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_nearAnchorPoint_tailAnchorUnique_basisInput
    hd hr hL hstep matching D hnear hunique
    (depthOneBasisRealizationInput_of_realizedTailPathSet_sourcePath
      hPaths hdet_full source_mem)

/-- Realized-tail recursive tail handoff whose remaining source-path membership is
discharged by the previous `IDLData` open set. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_fullAnchorLocalData_realizedTail_source_mem_open
    {L Lfull d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (Dfull : IDLData (Lfull + 1) d r θfull θfull')
    (P : TexSweepFullAnchorLocalRealizationData D)
    (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths)
    (hdet_full : (skipB (Params.headValue θfull)).det ≠ 0)
    (source_mem_open :
      L = 1 ->
        ∀ j : Fin d,
          ((0 : Fin d -> ℝ),
            ((skipB (Params.headValue θfull))⁻¹).mulVec
              (((skipB (Params.headValue θ))⁻¹).mulVec
                (Pi.single j (1 : ℝ)))) ∈
            Dfull.O) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_fullAnchorLocalRealizationData_basisInput
    hd hr hL hstep matching D P
    (depthOneBasisRealizationInput_of_realizedTailPathSet_of_source_mem_open
      Dfull hPaths hdet_full source_mem_open)

/-- Arbitrary-path tail handoff from canonical local inverse data plus tail-anchor
uniqueness, compiled through the compact full-anchor frontier and reduced basis input. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_canonicalProvider_tailAnchorUnique_basisInput
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (C : TexSweepCanonicalLocalInverseSweepProviderData D)
    (hunique : TexSweepTailAnchorUnique D)
    (B : TexSweepDepthOneBasisRealizationInput D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_fullAnchorLocalRealizationData_basisInput
    hd hr hL hstep matching D
    (texSweepFullAnchorLocalRealizationData_of_canonicalProvider_tailAnchorUnique
      hL D C hunique)
    B

/-- Top-level universal-path tail handoff from a non-canonical full-anchor/region
provider.  The provider remains anchored at the transported full-anchor point; universal
paths fill the depth-one basis targets mechanically. -/
noncomputable def tail_IDLData_of_texGenericStep_of_paths_univ_fullAnchorRegionData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (P : TexSweepLocalIFTFullAnchorRegionData D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_paths_univ_localInverseSweepProviderData
    hd hr hstep matching D hPaths
    (texSweepLocalInverseSweepProviderData_of_fullAnchorRegionData
      hL hstep matching D P)

/-- Top-level universal-path tail handoff from the compact full-anchor
local-realization frontier. -/
noncomputable def tail_IDLData_of_texGenericStep_of_paths_univ_fullAnchorLocalRealizationData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (P : TexSweepFullAnchorLocalRealizationData D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_paths_univ_fullAnchorRegionData
    hd hr hL hstep matching D hPaths
    (texSweepLocalIFTFullAnchorRegionData_of_fullAnchorLocalRealizationData P)

/-- Top-level universal-path tail handoff from the canonical near-anchor realization
theorem.  Universal paths fill the depth-one basis targets, and no tail-anchor
uniqueness is needed because the local-realization package is already anchored at the
canonical `IDLData` tail point. -/
noncomputable def tail_IDLData_of_texGenericStep_of_paths_univ_nearAnchorPoint
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D)) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_paths_univ_localRealizationData
    hd hr hstep matching D hPaths
    (texSweepLocalRealizationData_of_nearAnchorPoint D
      (texSweepAnchorPointData_of_IDLData D) hnear)

/-- Top-level universal-path tail handoff from the concrete canonical near-anchor
source surface. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_paths_univ_canonicalNearAnchorLocalRealizationData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (R : TexSweepCanonicalNearAnchorLocalRealizationData D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_paths_univ_nearAnchorPoint
    hd hr hstep matching D hPaths
    (texSweepLocalRealizationNearAnchorPoint_of_canonicalNearAnchorLocalRealizationData
      R)

/-- Top-level universal-path tail handoff from a canonical local `Ψ` inverse selector.
The source-path availability side condition is discharged by `D.Paths = Set.univ`; the
remaining selector-side assumption is realization of the selected source paths. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_paths_univ_localPsiInverseNearAnchorData_realizes
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (I : TexSweepPsiLocalInverseNearAnchorData D
      (texSweepAnchorPointData_of_IDLData D))
    (hrealizes : TexSweepPsiLocalInverseRealizes I) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_paths_univ_nearAnchorPoint
    hd hr hstep matching D hPaths
    (texSweepLocalRealizationNearAnchorPoint_of_paths_univ_localPsiInverseNearAnchorData
      hPaths I hrealizes)

/-- Top-level universal-path tail handoff from bundled local `Ψ` realization data at
the canonical anchor. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_paths_univ_localPsiInverseRealizationData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (R : TexSweepCanonicalPsiLocalInverseRealizationData D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_paths_univ_localPsiInverseNearAnchorData_realizes
    hd hr hstep matching D hPaths
    (texSweepPsiLocalInverseNearAnchorData_of_localPsiInverseRealizationData R)
    (texSweepPsiLocalInverseRealizes_of_localPsiInverseRealizationData R)

/-- Top-level universal-path tail handoff from canonical pointwise IFT data and a
canonical local `Ψ` inverse selector.  This exposes the pointwise nondegenerate sweep
data and the local realization proof, with source-path availability supplied by
`D.Paths = Set.univ`. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_paths_univ_canonicalIFTPointData_localPsiInverseNearAnchorData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (P : TexSweepCanonicalIFTPointData D)
    (I : TexSweepPsiLocalInverseNearAnchorData D
      (texSweepAnchorPointData_of_IDLData D))
    (hrealizes : TexSweepPsiLocalInverseRealizes I) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_paths_univ_canonicalIFTData
    hd hr hstep matching D hPaths
    (texSweepCanonicalIFTData_of_pointData_paths_univ_localPsiInverseNearAnchorData
      P hPaths I hrealizes)

/-- Top-level universal-path tail handoff from canonical pointwise IFT data and bundled
local `Ψ` realization data. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_paths_univ_canonicalIFTPointData_localPsiRealizationData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (P : TexSweepCanonicalIFTPointData D)
    (R : TexSweepCanonicalPsiLocalInverseRealizationData D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_paths_univ_canonicalIFTData
    hd hr hstep matching D hPaths
    (texSweepCanonicalIFTData_of_pointData_paths_univ_localPsiInverseRealizationData
      P hPaths R)

/-- Top-level universal-path tail handoff from first-layer `sig(log r)` constant-tail
surjectivity.  This compiles the surjectivity premise to the canonical near-anchor
realization theorem before invoking the existing universal-path handoff. -/
noncomputable def tail_IDLData_of_texGenericStep_of_paths_univ_siglog_surjective
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (hsurj : FirstLayerSiglogConstantTailSurjective r
      (Params.headValue θ) (Params.headAttention θ)) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_paths_univ_nearAnchorPoint
    hd hr hstep matching D hPaths
    (texSweepLocalRealizationNearAnchorPoint_of_paths_univ_siglog_surjective
      D hPaths hsurj)

/-- Top-level universal-path tail handoff from the canonical near-anchor realization
theorem plus tail-anchor uniqueness. -/
noncomputable def tail_IDLData_of_texGenericStep_of_paths_univ_nearAnchorPoint_tailAnchorUnique
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (hnear :
      TexSweepLocalRealizationNearAnchorPoint D
        (texSweepAnchorPointData_of_IDLData D))
    (hunique : TexSweepTailAnchorUnique D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_paths_univ_fullAnchorLocalRealizationData
    hd hr hL hstep matching D hPaths
    (texSweepFullAnchorLocalRealizationData_of_nearAnchorPoint_tailAnchorUnique
      hL D hnear hunique)

/-- Top-level universal-path tail handoff from canonical local inverse data plus
tail-anchor uniqueness. -/
noncomputable def
    tail_IDLData_of_texGenericStep_of_paths_univ_canonicalProvider_tailAnchorUnique
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hL : 0 < L)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (C : TexSweepCanonicalLocalInverseSweepProviderData D)
    (hunique : TexSweepTailAnchorUnique D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_paths_univ_fullAnchorLocalRealizationData
    hd hr hL hstep matching D hPaths
    (texSweepFullAnchorLocalRealizationData_of_canonicalProvider_tailAnchorUnique
      hL D C hunique)

/-- Top-level universal-path tail handoff from an explicit honest all-realized
constant-tail premise.  This route intentionally keeps `all_realized` as an input and
does not use the `sig(log r)` surjectivity shortcut. -/
noncomputable def tail_IDLData_of_texGenericStep_of_paths_univ_all_realized
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ') (hPaths : D.Paths = Set.univ)
    (all_realized :
      ∀ p : ProbePoint d,
        constantProbePath p ∈ realizedTailPathSet r θ D.Paths) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep hd hr hstep matching D
    (texSweepRegionData_of_paths_univ_regionCoreData hstep matching D hPaths
      (texSweepRegionCoreData_univ_of_all_realized D all_realized))

/-- Canonical-realized-region form of the tail handoff.  The only external sweep
content is the theorem-shaped package that `realizedTailRegion` is nonempty, carries
the tail-anchor handoff, and contains the depth-one basis targets. -/
noncomputable def tail_IDLData_of_texGenericStep_of_realizedTailRegionData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (R : TexSweepRealizedTailRegionData D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep hd hr hstep matching D
    (texSweepRegionData_of_realizedTailRegionData R)

/-- Tail handoff from the explicit analytic support package for TeX Lemma `sweep`. -/
noncomputable def tail_IDLData_of_texGenericStep_of_IDLData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (S : TexSweepAnalyticData hstep matching D) :
    IDLData L d r (Params.tail θ) (Params.tail θ') :=
  tail_IDLData_of_texGenericStep_of_realizedTailRegionData hd hr hstep matching D
    (texSweepRealizedTailRegionData_of_IDLData hstep matching D S)

/-! ## Dial-inversion realization layer (Agent D sweep frontier)

This section isolates the genuine analytic content of the canonical near-anchor sweep
realization theorem `TexSweepLocalRealizationNearAnchorPoint` into a single pointwise
*dial-inversion* obligation, with fully-verified glue lemmas that assemble that pointwise
obligation into the near-anchor theorem and then into `TexSweepCanonicalIFTData`.

The TeX realization lemma (induction step) says: nearby lower-depth tail probes are
realized by full-depth source paths whose limits stay in the current region/path class.
"Realized" means, for a constant tail target `η`, there is a full-depth source path
`source ∈ D.Paths` whose matched first-layer effective point eventually (for `τ` past a
threshold) equals `η`.  Because the first-layer gate
`firstLayerGate r A w v τ = sig (τ * matrixBilin A w v + log r)` is `τ`-dependent unless
the source slope vanishes, the realization must in general use a `τ`-indexed source path
that solves the dial equation exactly at each `τ` (the scalar fixed-point / IFT inversion
in the TeX proof).  This layer states exactly that inversion obligation and discharges
everything around it.

None of the lemmas below assume the globally-false `TexSweepTailAnchorUnique`, and none
use the `sig (log r)` zero-slope surjectivity shortcut as a generic plan: the dial gate
is left free per `τ`. -/

/-- A source path realizes a constant tail target, in the exact sense required by
`RealizationData`, as soon as its matched first-layer effective point eventually equals
that target.  This is the trivial but load-bearing bridge from an explicit eventual dial
identity to the realization record. -/
noncomputable def texSweepRealizationData_of_eventually_effective_eq {L d r : Nat}
    {θ : Params (L + 1) d} (η : ProbePoint d) (source : ProbePath d) (T : ℝ)
    (hT : 0 ≤ T)
    (heff :
      ∀ τ : ℝ, T < τ ->
        firstLayerEffectivePoint r (Params.headValue θ) (Params.headAttention θ)
          (source τ).1 (source τ).2 τ = η) :
    RealizationData r (Params.headValue θ) (Params.headAttention θ)
      (constantProbePath η) source where
  threshold := T
  threshold_nonneg := hT
  effective_eq := by
    intro τ hτ
    rw [constantProbePath_apply]
    exact heff τ hτ

/-- The honest pointwise realization obligation behind the sweep near-anchor theorem: the
constant tail target `η` is realized by some available full-depth source path through the
matched first layer.  This is definitionally membership of `constantProbePath η` in
`realizedTailPathSet`, restated as a sweep-facing predicate so the residual frontier can
be named precisely. -/
def TexSweepPointwiseRealizable {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (η : ProbePoint d) : Prop :=
  ∃ source : ProbePath d, source ∈ D.Paths ∧
    Nonempty (RealizationData r (Params.headValue θ) (Params.headAttention θ)
      (constantProbePath η) source)

/-- Pointwise realizability is exactly realized-tail-path membership of the constant
target. -/
theorem texSweepPointwiseRealizable_iff_mem_realizedTailPathSet {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (η : ProbePoint d) :
    TexSweepPointwiseRealizable D η ↔
      constantProbePath η ∈ realizedTailPathSet r θ D.Paths := by
  rfl

/-- Build pointwise realizability from an available source path and an eventual exact
dial identity.  This is the form a dial-inversion argument actually produces: a source
path in the current class plus a threshold past which the matched effective point hits
the target. -/
noncomputable def texSweepPointwiseRealizable_of_source_eventually_effective_eq
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (η : ProbePoint d) (source : ProbePath d)
    (hsource : source ∈ D.Paths) (T : ℝ) (hT : 0 ≤ T)
    (heff :
      ∀ τ : ℝ, T < τ ->
        firstLayerEffectivePoint r (Params.headValue θ) (Params.headAttention θ)
          (source τ).1 (source τ).2 τ = η) :
    TexSweepPointwiseRealizable D η :=
  ⟨source, hsource,
    ⟨texSweepRealizationData_of_eventually_effective_eq η source T hT heff⟩⟩

/-- Neighborhood assembler (the core honest reduction).

If there is an open set `U` containing the canonical tail anchor on which every target is
pointwise realizable, then the canonical near-anchor local realization theorem holds.
This localizes the existing `_of_all_realized` reduction from "all of `ProbePoint d`" down
to "an open neighborhood of the anchor", which is the actual TeX statement (realization of
*nearby* tail probes), and is the strictly smaller obligation a sweep provider must
supply. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_pointwiseRealizable_on_open
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (U : Set (ProbePoint d)) (hU_open : IsOpen U)
    (hanchor : (texSweepAnchorPointData_of_IDLData D).point ∈ U)
    (hreal : ∀ η : ProbePoint d, η ∈ U -> TexSweepPointwiseRealizable D η) :
    TexSweepLocalRealizationNearAnchorPoint D
      (texSweepAnchorPointData_of_IDLData D) := by
  refine ⟨U, hU_open, hanchor, ?_⟩
  intro η hη
  exact hreal η hη

/-- Concrete canonical near-anchor source surface from uniform pointwise realizability on
an open neighborhood of the anchor.  Downstream this compiles to `TexSweepCanonicalIFTData`
via `texSweepCanonicalIFTData_of_canonicalNearAnchorLocalRealizationData`, then up through
`texSweepCanonicalPsiLocalInverseRealizationData_of_canonicalIFTData` and
`texSweepAnalyticData_of_paths_univ_localPsiInverseRealizationData`. -/
noncomputable def texSweepCanonicalNearAnchorLocalRealizationData_of_pointwiseRealizable_on_open
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (U : Set (ProbePoint d)) (hU_open : IsOpen U)
    (hanchor : (texSweepAnchorPointData_of_IDLData D).point ∈ U)
    (hreal : ∀ η : ProbePoint d, η ∈ U -> TexSweepPointwiseRealizable D η) :
    TexSweepCanonicalNearAnchorLocalRealizationData D :=
  texSweepCanonicalNearAnchorLocalRealizationData_of_nearAnchorPoint D
    (texSweepLocalRealizationNearAnchorPoint_of_pointwiseRealizable_on_open D U hU_open
      hanchor hreal)

/-- Reduced canonical sweep frontier from uniform pointwise realizability on an open
neighborhood of the anchor. -/
noncomputable def texSweepCanonicalIFTData_of_pointwiseRealizable_on_open
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (U : Set (ProbePoint d)) (hU_open : IsOpen U)
    (hanchor : (texSweepAnchorPointData_of_IDLData D).point ∈ U)
    (hreal : ∀ η : ProbePoint d, η ∈ U -> TexSweepPointwiseRealizable D η) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_nearAnchorPoint D
    (texSweepLocalRealizationNearAnchorPoint_of_pointwiseRealizable_on_open D U hU_open
      hanchor hreal)

/-! ### The pointwise dial-inversion obligation

The remaining analytic content is now a single, explicit obligation: a *uniform* family of
exact dial preimages over an open neighborhood of the anchor, whose source paths lie in the
current path class.  Concretely, for each target `η` in the neighborhood there is one
full-depth source path `source ∈ D.Paths` and a threshold `T ≥ 0` such that, for every
`τ > T`, the matched first-layer effective point of `source τ` is exactly `η`.

This is the formal Lean shape of TeX Lemma `realization`/`sweep`: the dial map
`(w, v) ↦ Φ_{firstLayerGate r A w v τ}(w, v)` is locally invertible onto a neighborhood of
the anchor, uniformly in `τ`, by source paths that stay in the path class.  No siglog
shortcut and no tail-anchor uniqueness is used. -/

/-- The uniform pointwise dial-inversion obligation over an open neighborhood `U` of the
canonical tail anchor: every target in `U` admits an available source path whose matched
effective point eventually equals it. -/
def TexSweepUniformDialInverseData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (U : Set (ProbePoint d)) : Prop :=
  ∀ η : ProbePoint d, η ∈ U ->
    ∃ source : ProbePath d, source ∈ D.Paths ∧ ∃ T : ℝ, 0 ≤ T ∧
      ∀ τ : ℝ, T < τ ->
        firstLayerEffectivePoint r (Params.headValue θ) (Params.headAttention θ)
          (source τ).1 (source τ).2 τ = η

/-- The uniform dial-inversion obligation provides uniform pointwise realizability. -/
noncomputable def texSweepPointwiseRealizable_of_uniformDialInverseData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') {U : Set (ProbePoint d)}
    (H : TexSweepUniformDialInverseData D U)
    {η : ProbePoint d} (hη : η ∈ U) :
    TexSweepPointwiseRealizable D η := by
  obtain ⟨source, hsource, T, hT, heff⟩ := H η hη
  exact texSweepPointwiseRealizable_of_source_eventually_effective_eq D η source hsource
    T hT heff

/-- The uniform dial-inversion obligation over an open neighborhood of the anchor proves
the canonical near-anchor local realization theorem.  This is the end-to-end honest
reduction: the sweep frontier `TexSweepCanonicalIFTData D` is supplied by an open
neighborhood `U` of the anchor together with the uniform exact dial inversion on `U`. -/
noncomputable def texSweepCanonicalNearAnchorLocalRealizationData_of_uniformDialInverseData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (U : Set (ProbePoint d)) (hU_open : IsOpen U)
    (hanchor : (texSweepAnchorPointData_of_IDLData D).point ∈ U)
    (H : TexSweepUniformDialInverseData D U) :
    TexSweepCanonicalNearAnchorLocalRealizationData D :=
  texSweepCanonicalNearAnchorLocalRealizationData_of_pointwiseRealizable_on_open D U
    hU_open hanchor
    (fun _η hη => texSweepPointwiseRealizable_of_uniformDialInverseData D H hη)

/-- The uniform dial-inversion obligation over an open neighborhood of the anchor directly
yields the reduced canonical sweep frontier. -/
noncomputable def texSweepCanonicalIFTData_of_uniformDialInverseData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (U : Set (ProbePoint d)) (hU_open : IsOpen U)
    (hanchor : (texSweepAnchorPointData_of_IDLData D).point ∈ U)
    (H : TexSweepUniformDialInverseData D U) :
    TexSweepCanonicalIFTData D :=
  texSweepCanonicalIFTData_of_canonicalNearAnchorLocalRealizationData
    (texSweepCanonicalNearAnchorLocalRealizationData_of_uniformDialInverseData D U hU_open
      hanchor H)

/-! ### Constant-source specialization of the dial inversion

The simplest instances of the uniform dial inversion use *constant* source paths.  A
constant source `(w, v)` has matched effective point
`firstLayerDialPoint V (firstLayerGate r A w v τ) w v`, which equals a fixed probe point
exactly when either the source slope `matrixBilin A w v` vanishes (so the gate is the
constant `sig (log r)`) or the moving part `V.mulVec w` is annihilated.  The following
lemmas package those two genuinely available cases as uniform dial-inversion witnesses, so
that any neighborhood of the anchor covered by such targets is discharged without further
analysis.  They are deliberately not claimed to cover an arbitrary anchor neighborhood;
that general case is the residual frontier. -/

/-- A constant zero-first-coordinate source realizes a zero-first-coordinate target
through the matched first layer, gate-independently, once the first skip matrix is
nonsingular.  This is the dial-inversion witness on the affine slice `{ (0, y) }`. -/
noncomputable def texSweepUniformDialInverse_constant_zeroFirst_eff_eq
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (y : Fin d -> ℝ)
    (hdet : (skipB (Params.headValue θ)).det ≠ 0)
    (hsource :
      constantProbePath
          ((0 : Fin d -> ℝ), ((skipB (Params.headValue θ))⁻¹).mulVec y) ∈ D.Paths) :
    TexSweepPointwiseRealizable D ((0 : Fin d -> ℝ), y) := by
  refine ⟨constantProbePath
      ((0 : Fin d -> ℝ), ((skipB (Params.headValue θ))⁻¹).mulVec y), hsource, ?_⟩
  refine ⟨?_⟩
  simpa [Params.headValue, Params.headAttention, Params.headLayer] using
    zeroFirstConstantRealizationData_of_firstSkip_det_ne_zero
      (r := r) (V := Params.headValue θ) (A := Params.headAttention θ) y hdet

/-- A zero-slope constant source realizes the constant tail target obtained by dialing it
at the gate `sig (log r)`, through the matched first layer.  This is the dial-inversion
witness on the zero first-slope quadric. -/
noncomputable def texSweepUniformDialInverse_constant_slopeZero_eff_eq
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') (p : ProbePoint d)
    (hslope : matrixBilin (Params.headAttention θ) p.1 p.2 = 0)
    (hsource : constantProbePath p ∈ D.Paths) :
    TexSweepPointwiseRealizable D
      (anchorStep (fun _ => (Params.headValue θ, Params.headAttention θ)) 0
        (sig (Real.log (r : ℝ))) p) := by
  refine ⟨constantProbePath p, hsource, ?_⟩
  refine ⟨?_⟩
  simpa [Params.headValue, Params.headAttention, Params.headLayer] using
    constantSourceRealizationData_of_slope_zero
      (r := r) (V := Params.headValue θ) (A := Params.headAttention θ) p hslope

end TransformerIdentifiability.NLayer
