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

/-- The fixed-gate first-layer dial map is the zero-th anchor step. -/
theorem firstLayerDialPoint_eq_anchorStep {d : Nat}
    (V A : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (p : ProbePoint d) :
    firstLayerDialPoint V t p.1 p.2 =
      anchorStep (fun _ => (V, A)) 0 t p := by
  ext i <;>
    simp [firstLayerDialPoint, anchorStep, anchorStepMatrix, skipB,
      Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec]

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

theorem anchorCovectorAt_tail_shift
    {L d : Nat} (θ : Params (L + 1) d) (g : Nat -> ℝ)
    (p : AnchorProbe d) (k : Nat) :
    anchorCovectorAt (anchorParamStream (Params.tail θ)) k (fun n => g (n + 1))
        (anchorPath (anchorParamStream θ) 1 g p) =
      anchorCovectorAt (anchorParamStream θ) (k + 1) g p := by
  unfold anchorCovectorAt
  rw [anchorPath_tail_shift θ g p k, anchorParamStream_tail_apply]

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

/-- The primed tail has at most one unwound anchor point.  Under this condition, the
canonical `IDLData` choice must agree with any provider-selected tail anchor. -/
def TexSweepTailAnchorUnique {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (_D : IDLData (L + 1) d r θ θ') : Prop :=
  ∀ p q : ProbePoint d,
    p ∈ unwoundAnchorSet (Params.tail θ') ->
    q ∈ unwoundAnchorSet (Params.tail θ') ->
    p = q

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

/-- The TeX sweep scalar at the first anchor gate is the first inverse-scalar
unwinding clause. -/
theorem texSweepVartheta0_eq_anchorInverseScalarAt
    {L d : Nat} (θ : Params (L + 1) d) (t : Nat -> ℝ) (p : AnchorProbe d) :
    texSweepVartheta0 (Params.headValue θ) (Params.headAttention θ) p (t 0) =
      anchorInverseScalarAt (anchorParamStream θ) 0 t p := by
  simp [texSweepVartheta0, anchorInverseScalarAt, firstLayerPi, anchorCovectorAt,
    anchorPath, anchorStepMatrix, Params.headValue, Params.headAttention,
    Params.headLayer, anchorParamStream]

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

/-- Choice-compatibility between a concrete full-depth unwound anchor and the canonical
tail-anchor point selected from `IDLData`.  This is the exact equality needed only when
retargeting full-anchor IFT data to the canonical anchor. -/
noncomputable def TexSweepFullAnchorChoiceCompatible {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') {p : AnchorProbe d}
    (W : AnchorUnwindingData θ' p) : Prop :=
  (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point =
    (texSweepAnchorPointData_of_IDLData D).point

/-- The canonical anchor is, by construction, the transport of `idlChosenFullAnchor D`, so
that full anchor is choice-compatible with the canonical `IDLData` anchor **definitionally**
— no tail-anchor uniqueness required.  This is the honest replacement for the depth-one-false
`TexSweepTailAnchorUnique` route. -/
theorem texSweepFullAnchorChoiceCompatible_idlChosenFullAnchor
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ') :
    TexSweepFullAnchorChoiceCompatible D (idlChosenFullAnchor D).2 :=
  rfl

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

end TransformerIdentifiability.NLayer
