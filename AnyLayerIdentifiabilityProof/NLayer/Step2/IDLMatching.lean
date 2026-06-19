import AnyLayerIdentifiabilityProof.NLayer.Step2.IDLSweep
import AnyLayerIdentifiabilityProof.NLayer.IDL.MatchingCore
import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeTrichotomyConstruction
import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeZeroBranchConnective

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Saturation and matching endpoint for IDL

This file owns the TeX Step 2 construction from first-attention identification to full
first-layer matching.
-/

/-! ## Planned Step 2 subtargets -/

/-- Constant gate data, used for constructor-level trichotomy packages. -/
def constantGateAlongBase {d : Nat} (a : ℝ) : GateAlongBase d :=
  fun _ _ _ => a

/-- The current `TrichotomyData` interface is constructor-level: it records saturation
for the gate functions supplied to it, but does not yet tie those functions to the dial
paths of `θ` or `θ'`.  Therefore constant-one gates give a valid package on any sign
region. -/
def trichotomyData_constOne_of_signRegion
    {L d : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    {A : Matrix (Fin d) (Fin d) ℝ} {b : ℝ}
    (signRegion : SignRegionData (L := L) (d := d) θ' O A b) :
    TrichotomyData (L := L) (d := d) b signRegion.U signRegion.U
      (constantGateAlongBase (d := d) 1) (constantGateAlongBase (d := d) 1) where
  subset_sign_region := fun _ hx => hx
  nonempty := signRegion.nonempty
  relatively_open_in_sign_region := by
    refine ⟨Set.univ, isOpen_univ, ?_⟩
    ext x
    simp
  connected := signRegion.connected
  varsigma := fun _ => 1
  varsigma_mem := by
    intro _n _hn _hL
    exact Or.inr (Or.inl rfl)
  unprimed_saturates := by
    intro _x _hx _n _hn _hL
    exact EventuallyExpClose.refl 1
  primed_saturates_one := by
    intro _x _hx _n _hn _hL
    exact EventuallyExpClose.refl 1

/-- Geometric/topological output of TeX Lemma `region`.

The IDL wrapper supplies genericity, endpoint, and path/open-set data, but the actual
region construction still has to choose a connected regular sign component inside the
available open probe region and prove the product-neighborhood basis used by saturation.
This package records exactly those missing facts before they are converted to the
downstream `SignRegionData` interface. -/
structure TexRegionConstructionData {L d : Nat} (θ' : Params L d)
    (O : Set (ProbePair d)) (A : Matrix (Fin d) (Fin d) ℝ) (b : ℝ) : Type where
  U : Set (ProbePair d × ℝ)
  nonempty : U.Nonempty
  relatively_open :
    ∃ W : Set (ProbePair d × ℝ),
      IsOpen W ∧
        U = W ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1}
  connected : IsPreconnected U
  point_on_quadric : ∀ x ∈ U, firstLayerQuadric A x.1
  point_regular : ∀ x ∈ U, firstLayerRegular A x.1
  point_mem_base : ∀ x ∈ U, x.1 ∈ O
  primed_positive :
    ∀ x ∈ U, ∀ n : Nat, 1 ≤ n -> n < L ->
      0 < (specializedPhi θ' n (gateAssignmentOneTail x.2) x.1).re
  product_neighborhood :
    ∀ U0 : Set (ProbePair d × ℝ), U0 ⊆ U -> U0.Nonempty ->
      (∃ W0 : Set (ProbePair d × ℝ), IsOpen W0 ∧ U0 = W0 ∩ U) ->
      CoefficientSeparatingProductPatch A U0

namespace TexRegionConstructionData

variable {L d : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
variable {A : Matrix (Fin d) (Fin d) ℝ} {b : ℝ}

/-- Convert the TeX-region construction facts to the downstream sign-region package. -/
def toSignRegionData
    (R : TexRegionConstructionData (L := L) (d := d) θ' O A b) :
    SignRegionData (L := L) (d := d) θ' O A b where
  U := R.U
  nonempty := R.nonempty
  relatively_open := R.relatively_open
  connected := R.connected
  point_on_quadric := R.point_on_quadric
  point_regular := R.point_regular
  point_mem_base := R.point_mem_base
  primed_positive := R.primed_positive
  product_neighborhood := R.product_neighborhood

end TexRegionConstructionData

/-- The finite anchor stream used by `AnchorUnwindingData` agrees with the formal
parameter stream used by `specializedPhi`.  This local copy avoids importing the
anchor-existence shard into the matching shard. -/
theorem idlMatching_anchorParamStream_eq_paramStream {L d : Nat} (θ : Params L d) :
    anchorParamStream θ = paramStream θ := by
  funext n
  by_cases h : n < L
  · simp [anchorParamStream, paramStream, h]
  · simp [anchorParamStream, paramStream, h]

/-- Real formal `w` transport is the first component of the real anchor path. -/
theorem formalWVec_realGate_eq_anchorPath_first {d : Nat}
    (θs : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (g : Nat -> ℝ) (p : AnchorProbe d) (n : Nat) :
    formalWVec θs n (fun k => (g k : ℂ)) p.1 =
      vecC ((anchorPath θs n g p).1) := by
  induction n with
  | zero =>
      simp [formalWVec_zero]
  | succ n ih =>
      rw [formalWVec_succ, ih]
      ext i
      simp [formalFactor, anchorPath_succ, anchorStep, anchorStepMatrix,
        Matrix.mulVec, dotProduct, matC, vecC, skipB]

/-- Real formal `v` transport is the second component of the real anchor path. -/
theorem formalVVec_realGate_eq_anchorPath_second {d : Nat}
    (θs : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (g : Nat -> ℝ) (p : AnchorProbe d) (n : Nat) :
    formalVVec θs n (fun k => (g k : ℂ)) p.1 p.2 =
      vecC ((anchorPath θs n g p).2) := by
  induction n with
  | zero =>
      simp [formalVVec_zero]
  | succ n ih =>
      rw [formalVVec_succ, ih, formalWVec_realGate_eq_anchorPath_first]
      ext i
      simp [anchorPath_succ, anchorStep, Matrix.mulVec, dotProduct, matC, vecC,
        skipB]

/-- On real gate assignments, `formalPhi` is the complexification of the corresponding
real anchor slope. -/
theorem formalPhi_realGate_eq_anchorSlopeAt {d : Nat}
    (θs : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (g : Nat -> ℝ) (p : AnchorProbe d) (n : Nat) :
    formalPhi θs n (fun k => (g k : ℂ)) p.1 p.2 =
      (anchorSlopeAt θs n g p : ℂ) := by
  rw [formalPhi, formalWVec_realGate_eq_anchorPath_first,
    formalVVec_realGate_eq_anchorPath_second]
  simp [anchorSlopeAt, matC, vecC, Matrix.mulVec, dotProduct]

/-- The sign-region specialization `(s_0, 1, 1, ...)` is the `k = 0` anchor unwind
gate stream. -/
theorem gateAssignmentOneTail_eq_anchorUnwindGate_zero
    (t s : Nat -> ℝ) :
    gateAssignmentOneTail (s 0) = fun n => ((anchorUnwindGate t s 0 n : ℝ) : ℂ) := by
  funext n
  cases n with
  | zero =>
      simp [gateAssignmentOneTail, gateAssignmentOfTail, complexGateAssignmentOfTail,
        anchorUnwindGate]
  | succ n =>
      simp [gateAssignmentOneTail, gateAssignmentOfTail, complexGateAssignmentOfTail,
        anchorUnwindGate]

/-- The first zero-slope anchor clause supplies the first-layer quadric equation. -/
theorem firstLayerQuadric_of_anchorUnwindingData
    {L d : Nat} {θ : Params (L + 1) d} {p : AnchorProbe d}
    (W : AnchorUnwindingData θ p) (hL : 0 < L) :
    firstLayerQuadric (Params.headAttention θ) p := by
  have hzero := W.slope_zero 0 (by omega)
  simpa [firstLayerQuadric, anchorSlopeAt, matrixBilin, Params.headAttention,
    Params.headLayer, anchorParamStream] using hzero

/-- The first nonzero-image and covector anchor clauses supply first-layer regularity. -/
theorem firstLayerRegular_of_anchorUnwindingData
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

/-- The later-positive anchor clauses give the lower-layer positivity needed at the
anchor point with first gate `s_0`. -/
theorem primedPositive_anchorPoint_of_anchorUnwindingData
    {L d : Nat} {θ : Params (L + 1) d} {p : AnchorProbe d}
    (W : AnchorUnwindingData θ p) {n : Nat} (hn1 : 1 ≤ n) (hnlt : n < L + 1) :
    0 < (specializedPhi θ n (gateAssignmentOneTail (W.s 0)) p).re := by
  have hpos :
      0 < anchorSlopeAt (anchorParamStream θ) n (anchorUnwindGate W.t W.s 0) p := by
    have hidx : 0 + (n + 1) - 1 = n := by omega
    simpa [hidx] using W.positive_later 0 (n + 1) (by omega) (by omega) (by omega)
  have hphi :
      specializedPhi θ n (gateAssignmentOneTail (W.s 0)) p =
        (anchorSlopeAt (anchorParamStream θ) n (anchorUnwindGate W.t W.s 0) p : ℂ) := by
    rw [specializedPhi, idlMatching_anchorParamStream_eq_paramStream θ,
      gateAssignmentOneTail_eq_anchorUnwindGate_zero,
      formalPhi_realGate_eq_anchorSlopeAt]
  rw [hphi]
  exact hpos

/-- Point-level content extracted from an unwound anchor for TeX Lemma `region`.

This is not yet a connected product region.  It records the actual anchor point, first
gate, quadric equation, regularity, base-region membership, and lower-layer positivity
that a future product-neighborhood construction has to thicken. -/
structure TexRegionAnchorPointData {L d : Nat} (θ' : Params (L + 1) d)
    (O : Set (ProbePair d)) : Type where
  point : ProbePair d
  t : ℝ
  point_mem_base : point ∈ O
  t_pos : 0 < t
  t_lt_one : t < 1
  point_on_quadric : firstLayerQuadric (Params.headAttention θ') point
  point_regular : firstLayerRegular (Params.headAttention θ') point
  primed_positive :
    ∀ n : Nat, 1 ≤ n -> n < L + 1 ->
      0 < (specializedPhi θ' n (gateAssignmentOneTail t) point).re

/-- Build the point-level region data from a concrete unwound anchor. -/
noncomputable def texRegionAnchorPointData_of_unwoundAnchor
    {L d : Nat} {θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (hL : 0 < L) {p : AnchorProbe d}
    (hpO : p ∈ O) (hpanchor : p ∈ unwoundAnchorSet θ') :
    TexRegionAnchorPointData θ' O := by
  classical
  let W : AnchorUnwindingData θ' p := Classical.choice hpanchor
  have hsIoo : W.s 0 ∈ Set.Ioo (0 : ℝ) 1 := W.s_mem_Ioo 0 (by omega)
  refine
    { point := p
      t := W.s 0
      point_mem_base := hpO
      t_pos := hsIoo.1
      t_lt_one := hsIoo.2
      point_on_quadric := firstLayerQuadric_of_anchorUnwindingData W hL
      point_regular := firstLayerRegular_of_anchorUnwindingData W hL
      primed_positive := ?_ }
  intro n hn1 hnlt
  exact primedPositive_anchorPoint_of_anchorUnwindingData W hn1 hnlt

/-- In positive tail depth, `IDLData.anchor_nonempty` supplies the point-level anchor
data needed by the region construction.  The missing part is thickening this point to a
connected relatively-open product patch. -/
noncomputable def texRegionAnchorPointData_of_IDLData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ') :
    TexRegionAnchorPointData θ' D.O := by
  classical
  have hanchor : (D.O ∩ unwoundAnchorSet θ').Nonempty := by
    rcases D.anchor_nonempty with hdepth | hanchor
    · omega
    · exact hanchor
  let p : ProbePair d := Classical.choose hanchor
  have hp : p ∈ D.O ∩ unwoundAnchorSet θ' := Classical.choose_spec hanchor
  exact texRegionAnchorPointData_of_unwoundAnchor hL hp.1 hp.2

/-- The ambient open-condition carrier for TeX Lemma `region`.

It records the pointwise conditions that should be preserved after shrinking around the
anchor: regularity, membership in the IDL probe region, and primed tail positivity.  The
quadric equation and the first gate interval are kept out of this set because the local
chart data below states relative openness inside `quadric x (0,1)` explicitly. -/
def texRegionSafeSet {L d : Nat} (θ' : Params (L + 1) d)
    (O : Set (ProbePair d)) : Set (ProbePair d × ℝ) :=
  {x | firstLayerRegular (Params.headAttention θ') x.1 ∧ x.1 ∈ O ∧
    ∀ n : Nat, 1 ≤ n -> n < L + 1 ->
      0 < (specializedPhi θ' n (gateAssignmentOneTail x.2) x.1).re}

/-- The anchor point lies in the ambient safe set by construction. -/
theorem texRegionAnchorPoint_mem_safeSet
    {L d : Nat} {θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (anchor : TexRegionAnchorPointData θ' O) :
    (anchor.point, anchor.t) ∈ texRegionSafeSet θ' O :=
  ⟨anchor.point_regular, anchor.point_mem_base, anchor.primed_positive⟩

/-- Continuity of the first projected matrix-vector term in the regularity predicate. -/
theorem continuous_firstLayer_transpose_mulVec_left {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) :
    Continuous fun p : ProbePair d => Matrix.mulVec (Matrix.transpose A) p.1 := by
  rw [continuous_pi_iff]
  intro i
  simp [Matrix.mulVec, dotProduct]
  exact continuous_finsetSum Finset.univ fun j _ =>
    continuous_const.mul
      ((continuous_apply j).comp
        (continuous_fst : Continuous fun p : ProbePair d => p.1))

/-- Continuity of the second projected matrix-vector term in the regularity predicate. -/
theorem continuous_firstLayer_mulVec_right {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) :
    Continuous fun p : ProbePair d => Matrix.mulVec A p.2 := by
  rw [continuous_pi_iff]
  intro i
  simp [Matrix.mulVec, dotProduct]
  exact continuous_finsetSum Finset.univ fun j _ =>
    continuous_const.mul
      ((continuous_apply j).comp
        (continuous_snd : Continuous fun p : ProbePair d => p.2))

/-- The regularity covector `pi(w,v)=transpose(A)w-Av` varies continuously with the
probe. -/
theorem continuous_firstLayerPi {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) :
    Continuous fun p : ProbePair d => firstLayerPi A p := by
  simpa [firstLayerPi] using
    (continuous_firstLayer_transpose_mulVec_left A).sub
      (continuous_firstLayer_mulVec_right A)

/-- The first-layer regular locus is open in probe space. -/
theorem isOpen_firstLayerRegular {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) :
    IsOpen {p : ProbePair d | firstLayerRegular A p} := by
  unfold firstLayerRegular
  exact
    (continuous_fst.isOpen_preimage _ isOpen_ne).inter
      (((continuous_firstLayer_transpose_mulVec_left A).isOpen_preimage _ isOpen_ne).inter
        ((continuous_firstLayerPi A).isOpen_preimage _ isOpen_ne))

/-- The one-free-gate stream `(t, 1, 1, ...)` is continuous in the displayed gate
coordinate. -/
theorem continuous_gateAssignmentOneTail_apply {d n : Nat} :
    Continuous fun x : ProbePair d × ℝ => gateAssignmentOneTail x.2 n := by
  cases n with
  | zero =>
      simpa [gateAssignmentOneTail, gateAssignmentOfTail, complexGateAssignmentOfTail]
        using Complex.continuous_ofReal.comp
          (continuous_snd : Continuous fun x : ProbePair d × ℝ => x.2)
  | succ n =>
      simpa [gateAssignmentOneTail, gateAssignmentOfTail, complexGateAssignmentOfTail]
        using (continuous_const : Continuous fun _ : ProbePair d × ℝ => (1 : ℂ))

/-- Complexification of a continuous real vector is continuous. -/
theorem continuous_vecC {X : Type*} [TopologicalSpace X] {d : Nat}
    {v : X -> Fin d -> ℝ} (hv : Continuous v) :
    Continuous fun x => vecC (v x) := by
  rw [continuous_pi_iff]
  intro i
  exact Complex.continuous_ofReal.comp ((continuous_apply i).comp hv)

/-- Continuity of complex matrix-vector multiplication. -/
theorem continuous_complex_matrix_mulVec {X : Type*} [TopologicalSpace X]
    {d : Nat} {A : X -> Matrix (Fin d) (Fin d) ℂ} {v : X -> Fin d -> ℂ}
    (hA : Continuous A) (hv : Continuous v) :
    Continuous fun x => Matrix.mulVec (A x) (v x) := by
  rw [continuous_pi_iff]
  intro i
  simpa [Matrix.mulVec, dotProduct] using
    (continuous_finsetSum Finset.univ fun j _ =>
      ((continuous_apply j).comp ((continuous_apply i).comp hA)).mul
        ((continuous_apply j).comp hv))

/-- Continuity of complex dot products. -/
theorem continuous_complex_dotProduct {X : Type*} [TopologicalSpace X]
    {d : Nat} {v w : X -> Fin d -> ℂ}
    (hv : Continuous v) (hw : Continuous w) :
    Continuous fun x => dotProduct (v x) (w x) := by
  simpa [dotProduct] using
    (continuous_finsetSum Finset.univ fun i _ =>
      ((continuous_apply i).comp hv).mul ((continuous_apply i).comp hw))

/-- The formal factor matrix is continuous in the one-free-gate stream. -/
theorem continuous_formalFactor_oneTail {d : Nat}
    (θs : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) :
    Continuous fun x : ProbePair d × ℝ =>
      formalFactor θs (gateAssignmentOneTail x.2) n := by
  refine continuous_matrix ?_
  intro i j
  simpa [formalFactor, matC] using
    (continuous_const.sub
      ((continuous_gateAssignmentOneTail_apply (d := d) (n := n)).mul continuous_const))

/-- The formal transported `w` vector is continuous in `(probe, first_gate)`. -/
theorem continuous_formalWVec_oneTail {d : Nat}
    (θs : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    ∀ n : Nat,
      Continuous fun x : ProbePair d × ℝ =>
        formalWVec θs n (gateAssignmentOneTail x.2) x.1.1
  | 0 => by
      simpa [formalWVec] using
        continuous_vecC
          ((continuous_fst : Continuous fun x : ProbePair d × ℝ => x.1).fst)
  | n + 1 => by
      simpa [formalWVec_succ] using
        continuous_complex_matrix_mulVec
          (continuous_formalFactor_oneTail θs n)
          (continuous_formalWVec_oneTail θs n)

/-- The formal transported `v` vector is continuous in `(probe, first_gate)`. -/
theorem continuous_formalVVec_oneTail {d : Nat}
    (θs : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :
    ∀ n : Nat,
      Continuous fun x : ProbePair d × ℝ =>
        formalVVec θs n (gateAssignmentOneTail x.2) x.1.1 x.1.2
  | 0 => by
      simpa [formalVVec] using
        continuous_vecC
          ((continuous_fst : Continuous fun x : ProbePair d × ℝ => x.1).snd)
  | n + 1 => by
      have hleft :
          Continuous fun x : ProbePair d × ℝ =>
            Matrix.mulVec (matC (skipB (θs n).1))
              (formalVVec θs n (gateAssignmentOneTail x.2) x.1.1 x.1.2) :=
        continuous_complex_matrix_mulVec continuous_const
          (continuous_formalVVec_oneTail θs n)
      have hright :
          Continuous fun x : ProbePair d × ℝ =>
            gateAssignmentOneTail x.2 n •
              (Matrix.mulVec (matC (θs n).1)
                (formalWVec θs n (gateAssignmentOneTail x.2) x.1.1)) :=
        (continuous_gateAssignmentOneTail_apply (d := d) (n := n)).smul
          (continuous_complex_matrix_mulVec continuous_const
            (continuous_formalWVec_oneTail θs n))
      simpa [formalVVec_succ] using hleft.add hright

/-- The formal slope under the one-free-gate stream is continuous in
`(probe, first_gate)`. -/
theorem continuous_formalPhi_oneTail {d : Nat}
    (θs : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) :
    Continuous fun x : ProbePair d × ℝ =>
      formalPhi θs n (gateAssignmentOneTail x.2) x.1.1 x.1.2 := by
  simpa [formalPhi] using
    continuous_complex_dotProduct
      (continuous_formalWVec_oneTail θs n)
      (continuous_complex_matrix_mulVec continuous_const
        (continuous_formalVVec_oneTail θs n))

/-- The real part of the specialized slope under the one-free-gate stream is
continuous in `(probe, first_gate)`. -/
theorem continuous_specializedPhi_oneTail_re {L d : Nat}
    (θ : Params L d) (n : Nat) :
    Continuous fun x : ProbePair d × ℝ =>
      (specializedPhi θ n (gateAssignmentOneTail x.2) x.1).re := by
  exact Complex.continuous_re.comp
    (by
      simpa [specializedPhi] using
        continuous_formalPhi_oneTail (paramStream θ) n)

/-- Tail-positivity part of the TeX-region safe set.  This is separated so that
finite-depth openness can be proved once from continuity of the displayed predicates. -/
def texRegionTailPositiveSet {L d : Nat} (θ' : Params (L + 1) d) :
    Set (ProbePair d × ℝ) :=
  {x | ∀ n : Nat, 1 ≤ n -> n < L + 1 ->
    0 < (specializedPhi θ' n (gateAssignmentOneTail x.2) x.1).re}

/-- Finite-depth tail positivity is open when every displayed slope predicate is
continuous. -/
theorem isOpen_texRegionTailPositiveSet_of_continuous
    {L d : Nat} {θ' : Params (L + 1) d}
    (hcont :
      ∀ n : Nat, 1 ≤ n -> n < L + 1 ->
        Continuous fun x : ProbePair d × ℝ =>
          (specializedPhi θ' n (gateAssignmentOneTail x.2) x.1).re) :
    IsOpen (texRegionTailPositiveSet θ') := by
  classical
  let S : Fin (L + 1) -> Set (ProbePair d × ℝ) := fun n =>
    if hn : 1 ≤ (n : Nat) then
      {x | 0 < (specializedPhi θ' (n : Nat) (gateAssignmentOneTail x.2) x.1).re}
    else
      Set.univ
  have hS_open : ∀ n : Fin (L + 1), IsOpen (S n) := by
    intro n
    dsimp [S]
    split_ifs with hn
    · exact (hcont (n : Nat) hn n.isLt).isOpen_preimage _ isOpen_Ioi
    · exact isOpen_univ
  have hInter_open : IsOpen (⋂ n : Fin (L + 1), S n) :=
    isOpen_iInter_of_finite hS_open
  have h_eq : texRegionTailPositiveSet θ' = ⋂ n : Fin (L + 1), S n := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iInter.mpr ?_
      intro n
      by_cases hn : 1 ≤ (n : Nat)
      · simpa [S, hn] using hx (n : Nat) hn n.isLt
      · simp [S, hn]
    · intro hx n hn_pos hn_lt
      have hxfin := Set.mem_iInter.mp hx ⟨n, hn_lt⟩
      simpa [S, hn_pos] using hxfin
  simpa [h_eq] using hInter_open

/-- The TeX-region safe set is open once the IDL probe region is open and the finitely
many tail-positivity predicates are continuous. -/
theorem isOpen_texRegionSafeSet_of_continuous
    {L d : Nat} {θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (hO_open : IsOpen O)
    (hcont :
      ∀ n : Nat, 1 ≤ n -> n < L + 1 ->
        Continuous fun x : ProbePair d × ℝ =>
          (specializedPhi θ' n (gateAssignmentOneTail x.2) x.1).re) :
    IsOpen (texRegionSafeSet θ' O) := by
  have hregular_open :
      IsOpen {x : ProbePair d × ℝ |
        firstLayerRegular (Params.headAttention θ') x.1} :=
    (isOpen_firstLayerRegular (Params.headAttention θ')).preimage continuous_fst
  have hO_pair_open : IsOpen {x : ProbePair d × ℝ | x.1 ∈ O} :=
    hO_open.preimage continuous_fst
  have hpositive_open : IsOpen (texRegionTailPositiveSet θ') :=
    isOpen_texRegionTailPositiveSet_of_continuous hcont
  simpa [texRegionSafeSet, texRegionTailPositiveSet] using
    hregular_open.inter (hO_pair_open.inter hpositive_open)

/-- Pure local quadric geometry needed by TeX Lemma `region`.

Compared with `TexRegionLocalQuadricProductPatchData`, this no longer knows about the
parameter family, base set, or positivity predicates.  It only chooses a connected
relative neighborhood in the quadric inside a supplied safe ambient set and supplies the
coefficient-separating product patches required by matching. -/
structure RegularQuadricLocalConnectedCoefficientSeparatingChartData {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (safe : Set (ProbePair d × ℝ))
    (point : ProbePair d) (t : ℝ) : Type where
  U : Set (ProbePair d × ℝ)
  anchor_mem : (point, t) ∈ U
  subset_safe : U ⊆ safe
  relatively_open :
    ∃ W : Set (ProbePair d × ℝ),
      IsOpen W ∧
        U = W ∩
          {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1}
  connected : IsPreconnected U
  product_neighborhood :
    ∀ U0 : Set (ProbePair d × ℝ), U0 ⊆ U -> U0.Nonempty ->
      (∃ W0 : Set (ProbePair d × ℝ), IsOpen W0 ∧ U0 = W0 ∩ U) ->
      CoefficientSeparatingProductPatch A U0

namespace RegularQuadricLocalConnectedCoefficientSeparatingChartData

variable {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ}
variable {safe safe' : Set (ProbePair d × ℝ)}
variable {point : ProbePair d} {t : ℝ}

/-- A chart contained in a smaller ambient safe set is also a chart for any larger safe
set. -/
def mono
    (G : RegularQuadricLocalConnectedCoefficientSeparatingChartData A safe point t)
    (hsubset : safe ⊆ safe') :
    RegularQuadricLocalConnectedCoefficientSeparatingChartData A safe' point t where
  U := G.U
  anchor_mem := G.anchor_mem
  subset_safe := fun _ hx => hsubset (G.subset_safe hx)
  relatively_open := G.relatively_open
  connected := G.connected
  product_neighborhood := G.product_neighborhood

end RegularQuadricLocalConnectedCoefficientSeparatingChartData

/-- The first-layer quadric as a probe-space set. -/
def firstLayerQuadricProbeSet {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ) :
    Set (ProbePair d) :=
  {p | firstLayerQuadric A p}

/-- Coefficient separation on a fixed product probe/gate patch.

This is the non-topological part of `CoefficientSeparatingProductPatch`: once a
product patch `Uq x J` has been found by ordinary product-neighborhood topology, the
remaining quadric-richness content is exactly this implication. -/
def QuadricProductCoefficientSeparation {d : Nat}
    (_A : Matrix (Fin d) (Fin d) ℝ) (Uq : Set (ProbePair d)) (J : Set ℝ) : Prop :=
  ∀ (M : Matrix (Fin d) (Fin d) ℝ)
    (R : ℝ -> Matrix (Fin d) (Fin d) ℝ),
    (∀ p : ProbePair d, p ∈ Uq -> ∀ t : ℝ, t ∈ J ->
      Matrix.mulVec M p.2 + Matrix.mulVec (R t) p.1 = 0) ->
      (∀ v : Fin d -> ℝ, Matrix.mulVec M v = 0) ∧
        (∀ t : ℝ, t ∈ J -> R t = 0)

/-- Scalar row form of coefficient separation on a probe slice.

This is the algebraic heart of the quadric-slice input: if a scalar linear form in
`v` plus a scalar linear form in `w` vanishes on the selected probe slice, then both
coefficient vectors vanish.  The matrix-valued product statement is a rowwise
consequence, proved below. -/
def QuadricProbeSliceLinearCoefficientSeparation {d : Nat}
    (_A : Matrix (Fin d) (Fin d) ℝ) (Uq : Set (ProbePair d)) : Prop :=
  ∀ (m r : Fin d -> ℝ),
    (∀ p : ProbePair d, p ∈ Uq ->
      dotProduct m p.2 + dotProduct r p.1 = 0) ->
      m = 0 ∧ r = 0

/-- A selected first-layer quadric slice has no scalar linear component.

Equivalently, no nonzero scalar linear form in `(w,v)` vanishes identically on this
slice.  This is the exact local algebraic condition needed for rowwise coefficient
separation. -/
def QuadricProbeSliceNoLinearComponent {d : Nat}
    (_A : Matrix (Fin d) (Fin d) ℝ) (Uq : Set (ProbePair d)) : Prop :=
  ∀ (m r : Fin d -> ℝ),
    (∀ p : ProbePair d, p ∈ Uq ->
      dotProduct m p.2 + dotProduct r p.1 = 0) ->
    m = 0 ∧ r = 0

/-- Relatively open first-layer quadric probe slices have no scalar linear component.

This is a named nondegeneracy hypothesis, not a theorem of regularity alone.  The
rank-one counterexample below shows why callers must provide such slice-separation
data explicitly for the concrete matrix, e.g. `Params.headAttention θ'`. -/
def RegularQuadricProbeSliceNoLinearComponentData {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ (P : Set (ProbePair d)),
    IsOpen P ->
    (P ∩ firstLayerQuadricProbeSet A).Nonempty ->
    QuadricProbeSliceNoLinearComponent A (P ∩ firstLayerQuadricProbeSet A)

/-- A point-level solved-coordinate chart seed inside a selected quadric slice.

If a slice already contains a point with nonzero left vector, nonsingularity of `A`
chooses a coordinate whose solved-chart coefficient is nonzero.  Deleting that
coordinate from the slice point gives a chart-base parameter whose solved-coordinate
probe is exactly the original slice point, hence still lies in the slice. -/
theorem exists_solvedCoordChartBasePoint_of_slice_point_left_ne_zero
    {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ} {P : Set (ProbePair d)}
    {p : ProbePair d}
    (hdet : A.det ≠ 0)
    (hp : p ∈ P ∩ firstLayerQuadricProbeSet A)
    (hw : p.1 ≠ 0) :
    ∃ pivot : Fin d, ∃ x : QuadricGraphBase d pivot,
      x = (p.1, eraseCoord pivot p.2) ∧
        (Matrix.mulVec (Matrix.transpose A) x.1) pivot ≠ 0 ∧
          solvedCoordProbe A pivot x ∈ P ∩ firstLayerQuadricProbeSet A := by
  rcases exists_transpose_mulVec_ne_zero_coord_of_ne_zero A hdet hw with
    ⟨pivot, hcoeff⟩
  let x : QuadricGraphBase d pivot := (p.1, eraseCoord pivot p.2)
  refine ⟨pivot, x, rfl, ?_, ?_⟩
  · simpa [x] using hcoeff
  · have hquad : matrixBilin A p.1 p.2 = 0 := by
      simpa [firstLayerQuadricProbeSet, firstLayerQuadric] using hp.2
    have hprobe : solvedCoordProbe A pivot x = p := by
      simpa [x] using solvedCoordProbe_eq_of_quadric A hcoeff hquad
    simpa [hprobe] using hp

/-- A right-nonzero point in an open nonsingular quadric slice can be replaced by a
point in the same slice whose left vector is nonzero.

In the zero-left case, choose a nonzero vector orthogonal to `A * p.2` and move a
small nonzero amount in that left direction.  The dimension hypothesis is necessary:
in dimension one, a nonsingular quadric through `(0, v)` has no such left branch. -/
theorem exists_slice_point_left_ne_zero_of_slice_point_right_ne_zero
    {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ} {P : Set (ProbePair d)}
    {p : ProbePair d}
    (hd : 2 ≤ d)
    (hdet : A.det ≠ 0)
    (hP_open : IsOpen P)
    (hp : p ∈ P ∩ firstLayerQuadricProbeSet A)
    (hv : p.2 ≠ 0) :
    ∃ q : ProbePair d,
      q ∈ P ∩ firstLayerQuadricProbeSet A ∧ q.1 ≠ 0 ∧ q.2 = p.2 := by
  by_cases hw : p.1 ≠ 0
  · exact ⟨p, hp, hw, rfl⟩
  · have hp_left_zero : p.1 = 0 := not_not.mp hw
    have hAv_ne : Matrix.mulVec A p.2 ≠ 0 := by
      intro hAv
      exact hv (matrix_mulVec_eq_zero_of_det_ne_zero A hdet hAv)
    rcases exists_ne_zero_dotProduct_eq_zero_of_two_le hd (Matrix.mulVec A p.2) with
      ⟨u, hu_ne, hu_orth⟩
    let f : ℝ -> ProbePair d := fun t => (p.1 + t • u, p.2)
    have hf_cont : Continuous f := by
      exact Continuous.prodMk
        (continuous_const.add (continuous_id.smul continuous_const))
        continuous_const
    have hf_zero : f 0 = p := by
      simp [f]
    have hP_nhds : P ∈ nhds (f 0) := by
      simpa [hf_zero] using hP_open.mem_nhds hp.1
    have hP_event : ∀ᶠ t in nhds (0 : ℝ), f t ∈ P :=
      hf_cont.continuousAt.preimage_mem_nhds hP_nhds
    have hne_freq : ∃ᶠ t in nhds (0 : ℝ), t ≠ 0 :=
      (frequently_lt_nhds (0 : ℝ)).mono fun t ht => ne_of_lt ht
    rcases (hne_freq.and_eventually hP_event).exists with ⟨t, ht_ne, htP⟩
    refine ⟨f t, ?_, ?_, rfl⟩
    · constructor
      · exact htP
      · have hquad : firstLayerQuadric A (f t) := by
          simpa [f, firstLayerQuadric, matrixBilin, hp_left_zero, smul_dotProduct,
            hu_orth]
        simpa [firstLayerQuadricProbeSet] using hquad
    · intro hleft_zero
      have htu_zero : t • u = 0 := by
        simpa [f, hp_left_zero] using hleft_zero
      rcases smul_eq_zero.mp htu_zero with ht_zero | hu_zero
      · exact ht_ne ht_zero
      · exact hu_ne hu_zero

/-- Right-coordinate version of the point-level solved-coordinate chart seed.

The theorem first moves, inside the same open quadric slice, to a point with nonzero
left vector, then applies the existing solved-right-coordinate chart seed. -/
theorem exists_solvedCoordChartBasePoint_of_slice_point_right_ne_zero
    {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ} {P : Set (ProbePair d)}
    {p : ProbePair d}
    (hd : 2 ≤ d)
    (hdet : A.det ≠ 0)
    (hP_open : IsOpen P)
    (hp : p ∈ P ∩ firstLayerQuadricProbeSet A)
    (hv : p.2 ≠ 0) :
    ∃ q : ProbePair d, q ∈ P ∩ firstLayerQuadricProbeSet A ∧ q.1 ≠ 0 ∧
      q.2 = p.2 ∧
        ∃ pivot : Fin d, ∃ x : QuadricGraphBase d pivot,
          x = (q.1, eraseCoord pivot q.2) ∧
            (Matrix.mulVec (Matrix.transpose A) x.1) pivot ≠ 0 ∧
              solvedCoordProbe A pivot x ∈ P ∩ firstLayerQuadricProbeSet A := by
  rcases exists_slice_point_left_ne_zero_of_slice_point_right_ne_zero
      (A := A) (P := P) (p := p) hd hdet hP_open hp hv with
    ⟨q, hq, hq_left, hq_right⟩
  rcases exists_solvedCoordChartBasePoint_of_slice_point_left_ne_zero
      (A := A) (P := P) (p := q) hdet hq hq_left with
    ⟨pivot, x, hx, hcoeff, hmaps⟩
  exact ⟨q, hq, hq_left, hq_right, pivot, x, hx, hcoeff, hmaps⟩

/-- Any nonzero point in an open nonsingular quadric slice supplies a point-level
solved-coordinate chart seed. -/
theorem exists_solvedCoordChartBasePoint_of_slice_point_ne_zero
    {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ} {P : Set (ProbePair d)}
    {p : ProbePair d}
    (hd : 2 ≤ d)
    (hdet : A.det ≠ 0)
    (hP_open : IsOpen P)
    (hp : p ∈ P ∩ firstLayerQuadricProbeSet A)
    (hp_ne : p ≠ 0) :
    ∃ pivot : Fin d, ∃ x : QuadricGraphBase d pivot,
      (Matrix.mulVec (Matrix.transpose A) x.1) pivot ≠ 0 ∧
        solvedCoordProbe A pivot x ∈ P ∩ firstLayerQuadricProbeSet A := by
  by_cases hw : p.1 ≠ 0
  · rcases exists_solvedCoordChartBasePoint_of_slice_point_left_ne_zero
      (A := A) (P := P) (p := p) hdet hp hw with
      ⟨pivot, x, _hx, hcoeff, hmaps⟩
    exact ⟨pivot, x, hcoeff, hmaps⟩
  · have hv : p.2 ≠ 0 := by
      intro hv_zero
      apply hp_ne
      ext i <;> simp [not_not.mp hw, hv_zero]
    rcases exists_solvedCoordChartBasePoint_of_slice_point_right_ne_zero
        (A := A) (P := P) (p := p) hd hdet hP_open hp hv with
      ⟨_q, _hq, _hq_left, _hq_right, pivot, x, _hx, hcoeff, hmaps⟩
    exact ⟨pivot, x, hcoeff, hmaps⟩

/-- Nonempty-slice wrapper for the point-level solved-coordinate seed, with the
nonzero point supplied explicitly. -/
theorem exists_solvedCoordChartBasePoint_of_nonempty_slice_of_nonzero_point
    {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ} {P : Set (ProbePair d)}
    (hd : 2 ≤ d)
    (hdet : A.det ≠ 0)
    (hP_open : IsOpen P)
    (_hslice : (P ∩ firstLayerQuadricProbeSet A).Nonempty)
    {p : ProbePair d}
    (hp : p ∈ P ∩ firstLayerQuadricProbeSet A)
    (hp_ne : p ≠ 0) :
    ∃ pivot : Fin d, ∃ x : QuadricGraphBase d pivot,
      (Matrix.mulVec (Matrix.transpose A) x.1) pivot ≠ 0 ∧
        solvedCoordProbe A pivot x ∈ P ∩ firstLayerQuadricProbeSet A :=
  exists_solvedCoordChartBasePoint_of_slice_point_ne_zero
    (A := A) (P := P) (p := p) hd hdet hP_open hp hp_ne

/-- Every nonempty ambient-open slice of the bilinear quadric in dimension at least
two contains a nonzero point.

If the selected point is zero, openness around the origin contains a small nonzero
point on the left coordinate axis, which is still on the quadric. -/
theorem exists_nonzero_point_mem_open_quadric_slice
    {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ} {P : Set (ProbePair d)}
    (hd : 2 ≤ d)
    (hP_open : IsOpen P)
    (hslice : (P ∩ firstLayerQuadricProbeSet A).Nonempty) :
    ∃ p : ProbePair d, p ∈ P ∩ firstLayerQuadricProbeSet A ∧ p ≠ 0 := by
  classical
  rcases hslice with ⟨p, hp⟩
  by_cases hp_ne : p ≠ 0
  · exact ⟨p, hp, hp_ne⟩
  · have hp_zero : p = 0 := not_not.mp hp_ne
    haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
    rcases exists_pair_ne (Fin d) with ⟨i, _j, _hij⟩
    let w0 : Fin d -> ℝ := Pi.single i (1 : ℝ)
    have hw0_ne : w0 ≠ 0 := by
      intro hzero
      have hi := congrFun hzero i
      simpa [w0] using hi
    let f : ℝ -> ProbePair d := fun t => (t • w0, 0)
    have hf_cont : Continuous f := by
      exact (continuous_id.smul continuous_const).prodMk continuous_const
    have hf_zero : f 0 = p := by
      simp [f, hp_zero]
    have hP_nhds : P ∈ nhds (f 0) := by
      simpa [hf_zero] using hP_open.mem_nhds hp.1
    have hP_event : ∀ᶠ t in nhds (0 : ℝ), f t ∈ P :=
      hf_cont.continuousAt.preimage_mem_nhds hP_nhds
    have hne_freq : ∃ᶠ t in nhds (0 : ℝ), t ≠ 0 :=
      (frequently_lt_nhds (0 : ℝ)).mono fun t ht => ne_of_lt ht
    rcases (hne_freq.and_eventually hP_event).exists with ⟨t, ht_ne, htP⟩
    refine ⟨f t, ?_, ?_⟩
    · constructor
      · exact htP
      · have hquad : firstLayerQuadric A (f t) := by
          simp [f, firstLayerQuadric, matrixBilin]
        simpa [firstLayerQuadricProbeSet] using hquad
    · intro hzero
      have hleft_zero : t • w0 = 0 := by
        simpa [f] using congrArg Prod.fst hzero
      rcases smul_eq_zero.mp hleft_zero with ht_zero | hw_zero
      · exact ht_ne ht_zero
      · exact hw0_ne hw_zero

/-- The solved-coordinate probe map is continuous at any base point where the solved
coordinate coefficient is nonzero. -/
theorem continuousAt_solvedCoordProbe_of_coeff_ne
    {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ) {pivot : Fin d}
    {x0 : QuadricGraphBase d pivot}
    (hcoeff0 : (Matrix.mulVec (Matrix.transpose A) x0.1) pivot ≠ 0) :
    ContinuousAt (fun x : QuadricGraphBase d pivot => solvedCoordProbe A pivot x) x0 := by
  have hright_zero :
      Continuous fun x : QuadricGraphBase d pivot => insertCoord pivot 0 x.2 := by
    rw [continuous_pi_iff]
    intro j
    by_cases h : j = pivot
    · simpa [insertCoord, h] using
        (continuous_const : Continuous fun _ : QuadricGraphBase d pivot => (0 : ℝ))
    · simpa [insertCoord, h] using
        ((continuous_apply (⟨j, h⟩ : {j : Fin d // j ≠ pivot})).comp
          (continuous_snd : Continuous fun x : QuadricGraphBase d pivot => x.2))
  have hmat_right :
      Continuous fun x : QuadricGraphBase d pivot =>
        Matrix.mulVec A (insertCoord pivot 0 x.2) := by
    rw [continuous_pi_iff]
    intro i
    simpa [Matrix.mulVec, dotProduct] using
      (continuous_finsetSum Finset.univ fun j _ =>
        continuous_const.mul ((continuous_apply j).comp hright_zero))
  have hbilin :
      Continuous fun x : QuadricGraphBase d pivot =>
        matrixBilin A x.1 (insertCoord pivot 0 x.2) := by
    simpa [matrixBilin, dotProduct] using
      (continuous_finsetSum Finset.univ fun i _ =>
        ((continuous_apply i).comp
            (continuous_fst : Continuous fun x : QuadricGraphBase d pivot => x.1)).mul
          ((continuous_apply i).comp hmat_right))
  have hnum :
      Continuous fun x : QuadricGraphBase d pivot =>
        -matrixBilin A x.1 (insertCoord pivot 0 x.2) :=
    hbilin.neg
  have hden :
      Continuous fun x : QuadricGraphBase d pivot =>
        (Matrix.mulVec (Matrix.transpose A) x.1) pivot := by
    have hmul :
        Continuous fun x : QuadricGraphBase d pivot =>
          Matrix.mulVec (Matrix.transpose A) x.1 := by
      rw [continuous_pi_iff]
      intro i
      simpa [Matrix.mulVec, dotProduct] using
        (continuous_finsetSum Finset.univ fun j _ =>
          continuous_const.mul
            ((continuous_apply j).comp
              (continuous_fst : Continuous fun x : QuadricGraphBase d pivot => x.1)))
    exact (continuous_apply pivot).comp hmul
  have hsolved :
      ContinuousAt
        (fun x : QuadricGraphBase d pivot => solvedCoord A pivot x.1 x.2) x0 := by
    simpa [solvedCoord] using hnum.continuousAt.div hden.continuousAt hcoeff0
  have hright :
      ContinuousAt
        (fun x : QuadricGraphBase d pivot =>
          insertCoord pivot (solvedCoord A pivot x.1 x.2) x.2) x0 := by
    rw [continuousAt_pi]
    intro j
    by_cases h : j = pivot
    · simpa [insertCoord, h] using hsolved
    · simpa [insertCoord, h] using
        (((continuous_apply (⟨j, h⟩ : {j : Fin d // j ≠ pivot})).comp
          (continuous_snd : Continuous fun x : QuadricGraphBase d pivot => x.2)).continuousAt)
  simpa [solvedCoordProbe] using
    (continuous_fst : Continuous fun x : QuadricGraphBase d pivot => x.1).continuousAt.prodMk
      hright

/-- Upgrade a point-level solved-coordinate seed to an open chart-base neighborhood
whose probes remain in the selected open quadric slice.  The returned base also keeps
the solved-coordinate coefficient nonzero, so `SolvedCoordChartLinearFormSeparationData.ofBase`
can consume it once the scalar separation theorem on this base is supplied. -/
theorem exists_open_solvedCoordChartBase_of_seed
    {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ} {P : Set (ProbePair d)}
    {pivot : Fin d} {x0 : QuadricGraphBase d pivot}
    (hP_open : IsOpen P)
    (hcoeff0 : (Matrix.mulVec (Matrix.transpose A) x0.1) pivot ≠ 0)
    (hmaps0 : solvedCoordProbe A pivot x0 ∈ P ∩ firstLayerQuadricProbeSet A) :
    ∃ B : Set (QuadricGraphBase d pivot),
      IsOpen B ∧ x0 ∈ B ∧
        (∀ x : QuadricGraphBase d pivot, x ∈ B ->
          (Matrix.mulVec (Matrix.transpose A) x.1) pivot ≠ 0) ∧
        (∀ x : QuadricGraphBase d pivot, x ∈ B ->
          solvedCoordProbe A pivot x ∈ P ∩ firstLayerQuadricProbeSet A) := by
  let C : Set (QuadricGraphBase d pivot) :=
    {x | (Matrix.mulVec (Matrix.transpose A) x.1) pivot ≠ 0}
  have hden :
      Continuous fun x : QuadricGraphBase d pivot =>
        (Matrix.mulVec (Matrix.transpose A) x.1) pivot := by
    have hmul :
        Continuous fun x : QuadricGraphBase d pivot =>
          Matrix.mulVec (Matrix.transpose A) x.1 := by
      rw [continuous_pi_iff]
      intro i
      simpa [Matrix.mulVec, dotProduct] using
        (continuous_finsetSum Finset.univ fun j _ =>
          continuous_const.mul
            ((continuous_apply j).comp
              (continuous_fst : Continuous fun x : QuadricGraphBase d pivot => x.1)))
    exact (continuous_apply pivot).comp hmul
  have hC_open : IsOpen C := by
    simpa [C] using
      (hden.isOpen_preimage {y : ℝ | y ≠ 0}
        (isOpen_ne : IsOpen {y : ℝ | y ≠ 0}))
  have hpre_nhds :
      (fun x : QuadricGraphBase d pivot => solvedCoordProbe A pivot x) ⁻¹' P ∈
        nhds x0 := by
    exact
      (continuousAt_solvedCoordProbe_of_coeff_ne A hcoeff0).preimage_mem_nhds
        (hP_open.mem_nhds hmaps0.1)
  rcases mem_nhds_iff.mp hpre_nhds with ⟨T, hT_subset, hT_open, hx0T⟩
  let B : Set (QuadricGraphBase d pivot) := C ∩ T
  refine ⟨B, hC_open.inter hT_open, ⟨hcoeff0, hx0T⟩, ?_, ?_⟩
  · intro x hx
    exact hx.1
  · intro x hx
    constructor
    · exact hT_subset hx.2
    · have hquad :
          firstLayerQuadric A (solvedCoordProbe A pivot x) := by
        simpa [firstLayerQuadric] using
          matrixBilin_solvedCoordProbe A (i := pivot) (x := x) hx.1
      simpa [firstLayerQuadricProbeSet] using hquad

/-- Nonzero-point wrapper for the local solved-coordinate chart-base neighborhood. -/
theorem exists_open_solvedCoordChartBase_of_nonzero_slice_point
    {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ} {P : Set (ProbePair d)}
    (hd : 2 ≤ d)
    (hdet : A.det ≠ 0)
    (hP_open : IsOpen P)
    (hslice : (P ∩ firstLayerQuadricProbeSet A).Nonempty)
    {p : ProbePair d}
    (hp : p ∈ P ∩ firstLayerQuadricProbeSet A)
    (hp_ne : p ≠ 0) :
    ∃ pivot : Fin d, ∃ x0 : QuadricGraphBase d pivot,
      ∃ B : Set (QuadricGraphBase d pivot),
        IsOpen B ∧ x0 ∈ B ∧
          (∀ x : QuadricGraphBase d pivot, x ∈ B ->
            (Matrix.mulVec (Matrix.transpose A) x.1) pivot ≠ 0) ∧
          (∀ x : QuadricGraphBase d pivot, x ∈ B ->
            solvedCoordProbe A pivot x ∈ P ∩ firstLayerQuadricProbeSet A) := by
  rcases exists_solvedCoordChartBasePoint_of_nonempty_slice_of_nonzero_point
      (A := A) (P := P) hd hdet hP_open hslice hp hp_ne with
    ⟨pivot, x0, hcoeff0, hmaps0⟩
  rcases exists_open_solvedCoordChartBase_of_seed
      (A := A) (P := P) (pivot := pivot) (x0 := x0)
      hP_open hcoeff0 hmaps0 with
    ⟨B, hB_open, hx0B, hcoeff, hmaps⟩
  exact ⟨pivot, x0, B, hB_open, hx0B, hcoeff, hmaps⟩

/-- A scalar linear form on `Fin d -> ℝ` that vanishes on a nonempty open set has
zero coefficient vector. -/
theorem dotProduct_eq_zero_of_forall_mem_open
    {d : Nat} {W : Set (Fin d -> ℝ)} (hW_open : IsOpen W)
    {w0 : Fin d -> ℝ} (hw0 : w0 ∈ W) {c : Fin d -> ℝ}
    (hzero : ∀ w : Fin d -> ℝ, w ∈ W -> dotProduct c w = 0) :
    c = 0 := by
  ext i
  have hline_event :
      ∀ᶠ t in nhds (0 : ℝ), w0 + t • Pi.single i (1 : ℝ) ∈ W := by
    have hcont :
        ContinuousAt (fun t : ℝ => w0 + t • Pi.single i (1 : ℝ)) 0 := by
      exact continuous_const.continuousAt.add
        (continuous_id.smul continuous_const).continuousAt
    exact hcont.preimage_mem_nhds (by simpa using hW_open.mem_nhds hw0)
  have hne_freq : ∃ᶠ t in nhds (0 : ℝ), t ≠ 0 :=
    (frequently_lt_nhds (0 : ℝ)).mono fun t ht => ne_of_lt ht
  rcases (hne_freq.and_eventually hline_event).exists with ⟨t, ht_ne, htW⟩
  have hbase := hzero w0 hw0
  have hshift := hzero (w0 + t • Pi.single i (1 : ℝ)) htW
  rw [dotProduct_add, dotProduct_smul, hbase, zero_add] at hshift
  rw [dotProduct_comm, single_dotProduct, one_mul] at hshift
  exact (mul_eq_zero.mp hshift).resolve_left ht_ne

/-- On an open solved-coordinate base, the left-vector coefficient vanishes once the
right-vector coefficient has already been shown to vanish. -/
theorem solvedCoordChartBase_r_eq_zero_of_m_eq_zero
    {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ} {pivot : Fin d}
    {B : Set (QuadricGraphBase d pivot)} (hB_open : IsOpen B)
    {x0 : QuadricGraphBase d pivot} (hx0B : x0 ∈ B)
    {m r : Fin d -> ℝ}
    (hm : m = 0)
    (hvanish :
      ∀ x : QuadricGraphBase d pivot, x ∈ B ->
        dotProduct m (solvedCoordProbe A pivot x).2 +
          dotProduct r (solvedCoordProbe A pivot x).1 = 0) :
    r = 0 := by
  have hB_nhds : B ∈ nhds x0 := hB_open.mem_nhds hx0B
  rcases mem_nhds_prod_iff.mp hB_nhds with ⟨W, hW_nhds, U, hU_nhds, hWU_subset⟩
  rcases mem_nhds_iff.mp hW_nhds with ⟨W0, hW0_subset, hW0_open, hx0W0⟩
  rcases mem_nhds_iff.mp hU_nhds with ⟨U0, hU0_subset, _hU0_open, hx0U0⟩
  refine dotProduct_eq_zero_of_forall_mem_open hW0_open hx0W0 ?_
  intro w hw
  have hxB : (w, x0.2) ∈ B :=
    hWU_subset ⟨hW0_subset hw, hU0_subset hx0U0⟩
  have h := hvanish (w, x0.2) hxB
  simpa [solvedCoordProbe, hm] using h

/-- On an open solved-coordinate base for a nonsingular quadric in dimension at least
two, erased-coordinate variations force the right-vector coefficient to vanish. -/
theorem solvedCoordChartBase_m_eq_zero_of_open_base
    {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ} (hd : 2 ≤ d) (hdet : A.det ≠ 0)
    {pivot : Fin d}
    {B : Set (QuadricGraphBase d pivot)} (hB_open : IsOpen B)
    {x0 : QuadricGraphBase d pivot} (hx0B : x0 ∈ B)
    (hcoeff :
      ∀ x : QuadricGraphBase d pivot, x ∈ B ->
        (Matrix.mulVec (Matrix.transpose A) x.1) pivot ≠ 0)
    {m r : Fin d -> ℝ}
    (hvanish :
      ∀ x : QuadricGraphBase d pivot, x ∈ B ->
        dotProduct m (solvedCoordProbe A pivot x).2 +
          dotProduct r (solvedCoordProbe A pivot x).1 = 0) :
    m = 0 := by
  classical
  have hB_nhds : B ∈ nhds x0 := hB_open.mem_nhds hx0B
  rcases mem_nhds_prod_iff.mp hB_nhds with ⟨Wn, hWn, Un, hUn, hWU_subset⟩
  rcases mem_nhds_iff.mp hWn with ⟨W, hW_subset, hW_open, hx0W⟩
  rcases mem_nhds_iff.mp hUn with ⟨U, hU_subset, hU_open, hx0U⟩
  have hprodB :
      ∀ w : Fin d -> ℝ, w ∈ W ->
        ∀ u : {j : Fin d // j ≠ pivot} -> ℝ, u ∈ U -> (w, u) ∈ B := by
    intro w hw u hu
    exact hWU_subset ⟨hW_subset hw, hU_subset hu⟩
  have hrel :
      ∀ w : Fin d -> ℝ, w ∈ W ->
        ∀ e : {j : Fin d // j ≠ pivot},
          m e.1 -
            m pivot * (Matrix.mulVec (Matrix.transpose A) w) e.1 /
              (Matrix.mulVec (Matrix.transpose A) w) pivot = 0 := by
    intro w hw e
    have hline_event :
        ∀ᶠ t in nhds (0 : ℝ),
          x0.2 + t • Pi.single e (1 : ℝ) ∈ U := by
      have hcont :
          ContinuousAt
            (fun t : ℝ => x0.2 + t • Pi.single e (1 : ℝ)) 0 := by
        exact continuous_const.continuousAt.add
          (continuous_id.smul continuous_const).continuousAt
      exact hcont.preimage_mem_nhds (by simpa using hU_open.mem_nhds hx0U)
    have hne_freq : ∃ᶠ t in nhds (0 : ℝ), t ≠ 0 :=
      (frequently_lt_nhds (0 : ℝ)).mono fun t ht => ne_of_lt ht
    rcases (hne_freq.and_eventually hline_event).exists with ⟨t, ht_ne, htU⟩
    have hx_base : (w, x0.2) ∈ B := hprodB w hw x0.2 hx0U
    have hx_shift : (w, x0.2 + t • Pi.single e (1 : ℝ)) ∈ B :=
      hprodB w hw (x0.2 + t • Pi.single e (1 : ℝ)) htU
    have hcoeff_base :
        (Matrix.mulVec (Matrix.transpose A) w) pivot ≠ 0 :=
      hcoeff (w, x0.2) hx_base
    have hbase := hvanish (w, x0.2) hx_base
    have hshift := hvanish (w, x0.2 + t • Pi.single e (1 : ℝ)) hx_shift
    rw [dotProduct_solvedCoordProbe_add_single_erased A m e t hcoeff_base] at hshift
    simp only [solvedCoordProbe] at hbase hshift
    have hdiff :
        t * (m e.1 -
          m pivot * (Matrix.mulVec (Matrix.transpose A) w) e.1 /
            (Matrix.mulVec (Matrix.transpose A) w) pivot) = 0 := by
      linarith
    exact (mul_eq_zero.mp hdiff).resolve_left ht_ne
  by_contra hm_ne
  have hmpivot_ne : m pivot ≠ 0 := by
    intro hmpivot
    apply hm_ne
    ext j
    by_cases hj : j = pivot
    · subst j
      exact hmpivot
    · have hjrel := hrel x0.1 hx0W ⟨j, hj⟩
      simp [hmpivot] at hjrel
      exact hjrel
  rcases exists_ne_zero_dotProduct_eq_zero_of_two_le hd m with
    ⟨q, hq_ne, hqm⟩
  have hqA_zero_on_W :
      ∀ w : Fin d -> ℝ, w ∈ W ->
        dotProduct q (Matrix.mulVec (Matrix.transpose A) w) = 0 := by
    intro w hw
    have hcoeff_w :
        (Matrix.mulVec (Matrix.transpose A) w) pivot ≠ 0 :=
      hcoeff (w, x0.2) (hprodB w hw x0.2 hx0U)
    have hy_eq :
        Matrix.mulVec (Matrix.transpose A) w =
          ((Matrix.mulVec (Matrix.transpose A) w) pivot / m pivot) • m := by
      ext j
      by_cases hj : j = pivot
      · subst j
        simp [Pi.smul_apply]
        field_simp [hmpivot_ne]
      · have hjrel := hrel w hw ⟨j, hj⟩
        change (Matrix.mulVec (Matrix.transpose A) w) j =
          (Matrix.mulVec (Matrix.transpose A) w) pivot / m pivot * m j
        have hjrel' :
            m j =
              m pivot * (Matrix.mulVec (Matrix.transpose A) w) j /
                (Matrix.mulVec (Matrix.transpose A) w) pivot :=
          sub_eq_zero.mp hjrel
        have hmul :
            m j * (Matrix.mulVec (Matrix.transpose A) w) pivot =
              m pivot * (Matrix.mulVec (Matrix.transpose A) w) j := by
          rw [hjrel']
          field_simp [hcoeff_w]
        field_simp [hmpivot_ne]
        nlinarith [hmul]
    rw [hy_eq, dotProduct_smul]
    simp [hqm]
  have hAq_zero : Matrix.mulVec A q = 0 := by
    refine dotProduct_eq_zero_of_forall_mem_open hW_open hx0W ?_
    intro w hw
    have hqw := hqA_zero_on_W w hw
    have hrewrite :
        dotProduct q (Matrix.mulVec (Matrix.transpose A) w) =
          dotProduct (Matrix.mulVec A q) w := by
      simpa [matrixBilin] using
        matrixBilin_eq_transpose_dot (Matrix.transpose A) q w
    rw [hrewrite] at hqw
    exact hqw
  exact hq_ne (matrix_mulVec_eq_zero_of_det_ne_zero A hdet hAq_zero)

/-- Open solved-coordinate bases for nonsingular quadrics separate scalar linear
forms. -/
theorem solvedCoordChartBase_linearForm_eq_zero_of_open_base
    {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ} (hd : 2 ≤ d) (hdet : A.det ≠ 0)
    {pivot : Fin d}
    {B : Set (QuadricGraphBase d pivot)} (hB_open : IsOpen B)
    {x0 : QuadricGraphBase d pivot} (hx0B : x0 ∈ B)
    (hcoeff :
      ∀ x : QuadricGraphBase d pivot, x ∈ B ->
        (Matrix.mulVec (Matrix.transpose A) x.1) pivot ≠ 0)
    {m r : Fin d -> ℝ}
    (hvanish :
      ∀ x : QuadricGraphBase d pivot, x ∈ B ->
        dotProduct m (solvedCoordProbe A pivot x).2 +
          dotProduct r (solvedCoordProbe A pivot x).1 = 0) :
    m = 0 ∧ r = 0 := by
  have hm :=
    solvedCoordChartBase_m_eq_zero_of_open_base (A := A) hd hdet hB_open hx0B
      hcoeff hvanish
  exact ⟨hm, solvedCoordChartBase_r_eq_zero_of_m_eq_zero hB_open hx0B hm hvanish⟩

/-- Provider-facing solved-coordinate chart data for the no-linear-component theorem.

For every nonempty ambient-open slice of the first-layer quadric, it asks for a reduced
solved-coordinate chart whose parameter base is already known to separate scalar
linear forms.  This isolates the remaining chart-existence/topological work from the
rowwise coefficient-separation wrappers below. -/
structure RegularQuadricProbeSliceSolvedChartNoLinearData {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) : Type where
  slice_chart :
    ∀ (P : Set (ProbePair d)),
      IsOpen P ->
      (P ∩ firstLayerQuadricProbeSet A).Nonempty ->
      SolvedCoordChartLinearFormSeparationData A
        (P ∩ firstLayerQuadricProbeSet A)

namespace RegularQuadricProbeSliceSolvedChartNoLinearData

variable {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ}

/-- Compile per-slice solved-coordinate chart separation into the existing
no-linear-component interface. -/
theorem noLinearComponentData
    (D : RegularQuadricProbeSliceSolvedChartNoLinearData A) :
    RegularQuadricProbeSliceNoLinearComponentData A := by
  intro P hP_open hslice_nonempty m r hvanish
  exact
    (D.slice_chart P hP_open hslice_nonempty).linearForm_eq_zero
      (m := m) (r := r) hvanish

end RegularQuadricProbeSliceSolvedChartNoLinearData

/-- Exact reduced-chart obligation left for the determinant/nondegenerate quadric
provider.  The determinant hypotheses should ultimately produce these solved charts;
this declaration keeps that missing step explicit rather than hiding it in an
unsupported global theorem. -/
abbrev RegularQuadricProbeSliceNoLinearComponentDataOfDetNeZeroObligation
    {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (_hd : 2 ≤ d) (_hdet : A.det ≠ 0) : Type :=
  RegularQuadricProbeSliceSolvedChartNoLinearData A

/-- Determinant/nondegenerate no-linear-component provider, reduced to the explicit
solved-coordinate chart obligation for every nonempty open quadric slice. -/
theorem regularQuadricProbeSliceNoLinearComponentData_of_det_ne_zero_of_solvedCoordChart
    {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ}
    {hd : 2 ≤ d} {hdet : A.det ≠ 0}
    (chart :
      RegularQuadricProbeSliceNoLinearComponentDataOfDetNeZeroObligation A hd hdet) :
    RegularQuadricProbeSliceNoLinearComponentData A :=
  chart.noLinearComponentData

/-- Determinant/nondegenerate provider for reduced solved-coordinate charts on every
nonempty ambient-open quadric slice. -/
noncomputable def regularQuadricProbeSliceSolvedChartNoLinearData_of_det_ne_zero
    {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (hd : 2 ≤ d) (hdet : A.det ≠ 0) :
    RegularQuadricProbeSliceNoLinearComponentDataOfDetNeZeroObligation A hd hdet := by
  classical
  refine
    { slice_chart := ?_ }
  intro P hP_open hslice_nonempty
  let hnonzero :=
    exists_nonzero_point_mem_open_quadric_slice
      (A := A) (P := P) hd hP_open hslice_nonempty
  let p : ProbePair d := Classical.choose hnonzero
  have hp_spec : p ∈ P ∩ firstLayerQuadricProbeSet A ∧ p ≠ 0 :=
    Classical.choose_spec hnonzero
  let hchart :=
    exists_open_solvedCoordChartBase_of_nonzero_slice_point
      (A := A) (P := P) hd hdet hP_open hslice_nonempty hp_spec.1 hp_spec.2
  let pivot : Fin d := Classical.choose hchart
  have hpivot_spec :
      ∃ x0 : QuadricGraphBase d pivot,
        ∃ B : Set (QuadricGraphBase d pivot),
          IsOpen B ∧ x0 ∈ B ∧
            (∀ x : QuadricGraphBase d pivot, x ∈ B ->
              (Matrix.mulVec (Matrix.transpose A) x.1) pivot ≠ 0) ∧
            (∀ x : QuadricGraphBase d pivot, x ∈ B ->
              solvedCoordProbe A pivot x ∈ P ∩ firstLayerQuadricProbeSet A) :=
    Classical.choose_spec hchart
  let x0 : QuadricGraphBase d pivot := Classical.choose hpivot_spec
  have hx0_spec :
      ∃ B : Set (QuadricGraphBase d pivot),
        IsOpen B ∧ x0 ∈ B ∧
          (∀ x : QuadricGraphBase d pivot, x ∈ B ->
            (Matrix.mulVec (Matrix.transpose A) x.1) pivot ≠ 0) ∧
          (∀ x : QuadricGraphBase d pivot, x ∈ B ->
            solvedCoordProbe A pivot x ∈ P ∩ firstLayerQuadricProbeSet A) :=
    Classical.choose_spec hpivot_spec
  let B : Set (QuadricGraphBase d pivot) := Classical.choose hx0_spec
  have hB_spec :
      IsOpen B ∧ x0 ∈ B ∧
        (∀ x : QuadricGraphBase d pivot, x ∈ B ->
          (Matrix.mulVec (Matrix.transpose A) x.1) pivot ≠ 0) ∧
        (∀ x : QuadricGraphBase d pivot, x ∈ B ->
          solvedCoordProbe A pivot x ∈ P ∩ firstLayerQuadricProbeSet A) :=
    Classical.choose_spec hx0_spec
  exact
    SolvedCoordChartLinearFormSeparationData.ofBase
      (A := A) (Uq := P ∩ firstLayerQuadricProbeSet A)
      (pivot := pivot) (B := B)
      hB_spec.2.2.1 hB_spec.2.2.2
      (fun m r hvanish =>
        solvedCoordChartBase_linearForm_eq_zero_of_open_base
          (A := A) hd hdet hB_spec.1 hB_spec.2.1 hB_spec.2.2.1 hvanish)

/-- Open solved-coordinate bases prove the quadratic `lem:quadA` conclusion.

The erased-coordinate fibres first force `Xᵀ w` to be parallel to `Aᵀ w` and
`wᵀYw = 0` on an ordinary open set of left vectors.  The global matrix conclusions
then follow from the open-set algebraic quadric lemmas. -/
theorem quadricProbeSliceQuadraticCoefficientSeparation_of_open_solvedCoordChartBase
    {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ}
    (hd : 2 ≤ d) (hdet : A.det ≠ 0)
    {pivot : Fin d}
    {B : Set (QuadricGraphBase d pivot)} (hB_open : IsOpen B)
    {x0 : QuadricGraphBase d pivot} (hx0B : x0 ∈ B)
    (hcoeff :
      ∀ x : QuadricGraphBase d pivot, x ∈ B ->
        (Matrix.mulVec (Matrix.transpose A) x.1) pivot ≠ 0)
    {X Y : Matrix (Fin d) (Fin d) ℝ}
    (hvanish :
      ∀ x : QuadricGraphBase d pivot, x ∈ B ->
        dotProduct (solvedCoordProbe A pivot x).1
            (Matrix.mulVec X (solvedCoordProbe A pivot x).2) +
          dotProduct (solvedCoordProbe A pivot x).1
            (Matrix.mulVec Y (solvedCoordProbe A pivot x).1) = 0) :
    ∃ c : ℝ, X = c • A ∧ Y + Matrix.transpose Y = 0 := by
  classical
  have hB_nhds : B ∈ nhds x0 := hB_open.mem_nhds hx0B
  rcases mem_nhds_prod_iff.mp hB_nhds with ⟨Wn, hWn, Un, hUn, hWU_subset⟩
  rcases mem_nhds_iff.mp hWn with ⟨W, hW_subset, hW_open, hx0W⟩
  rcases mem_nhds_iff.mp hUn with ⟨U, hU_subset, hU_open, hx0U⟩
  have hprodB :
      ∀ w : Fin d -> ℝ, w ∈ W ->
        ∀ u : {j : Fin d // j ≠ pivot} -> ℝ, u ∈ U -> (w, u) ∈ B := by
    intro w hw u hu
    exact hWU_subset ⟨hW_subset hw, hU_subset hu⟩
  have hrel :
      ∀ w : Fin d -> ℝ, w ∈ W ->
        ∀ e : {j : Fin d // j ≠ pivot},
          (Matrix.mulVec (Matrix.transpose X) w) e.1 -
            (Matrix.mulVec (Matrix.transpose X) w) pivot *
              (Matrix.mulVec (Matrix.transpose A) w) e.1 /
                (Matrix.mulVec (Matrix.transpose A) w) pivot = 0 := by
    intro w hw e
    have hline_event :
        ∀ᶠ t in nhds (0 : ℝ),
          x0.2 + t • Pi.single e (1 : ℝ) ∈ U := by
      have hcont :
          ContinuousAt
            (fun t : ℝ => x0.2 + t • Pi.single e (1 : ℝ)) 0 := by
        exact continuous_const.continuousAt.add
          (continuous_id.smul continuous_const).continuousAt
      exact hcont.preimage_mem_nhds (by simpa using hU_open.mem_nhds hx0U)
    have hne_freq : ∃ᶠ t in nhds (0 : ℝ), t ≠ 0 :=
      (frequently_lt_nhds (0 : ℝ)).mono fun t ht => ne_of_lt ht
    rcases (hne_freq.and_eventually hline_event).exists with ⟨t, ht_ne, htU⟩
    have hx_base : (w, x0.2) ∈ B := hprodB w hw x0.2 hx0U
    have hx_shift : (w, x0.2 + t • Pi.single e (1 : ℝ)) ∈ B :=
      hprodB w hw (x0.2 + t • Pi.single e (1 : ℝ)) htU
    have hcoeff_base :
        (Matrix.mulVec (Matrix.transpose A) w) pivot ≠ 0 :=
      hcoeff (w, x0.2) hx_base
    let m : Fin d -> ℝ := Matrix.mulVec (Matrix.transpose X) w
    let beta : ℝ := dotProduct w (Matrix.mulVec Y w)
    let vbase : Fin d -> ℝ := (solvedCoordProbe A pivot (w, x0.2)).2
    have hbase : dotProduct m vbase + beta = 0 := by
      have h := hvanish (w, x0.2) hx_base
      have hrewrite :
          dotProduct (solvedCoordProbe A pivot (w, x0.2)).1
              (Matrix.mulVec X (solvedCoordProbe A pivot (w, x0.2)).2) =
            dotProduct m vbase := by
        have hbil :=
          matrixBilin_eq_transpose_dot X w
            (solvedCoordProbe A pivot (w, x0.2)).2
        simpa [matrixBilin, m, vbase, solvedCoordProbe] using hbil
      rw [hrewrite] at h
      simpa [beta, vbase, solvedCoordProbe] using h
    have hshift :
        dotProduct m
            (solvedCoordProbe A pivot
              (w, x0.2 + t • Pi.single e (1 : ℝ))).2 + beta = 0 := by
      have h := hvanish (w, x0.2 + t • Pi.single e (1 : ℝ)) hx_shift
      have hrewrite :
          dotProduct
              (solvedCoordProbe A pivot
                (w, x0.2 + t • Pi.single e (1 : ℝ))).1
              (Matrix.mulVec X
                (solvedCoordProbe A pivot
                  (w, x0.2 + t • Pi.single e (1 : ℝ))).2) =
            dotProduct m
              (solvedCoordProbe A pivot
                (w, x0.2 + t • Pi.single e (1 : ℝ))).2 := by
        have hbil :=
          matrixBilin_eq_transpose_dot X w
            (solvedCoordProbe A pivot
              (w, x0.2 + t • Pi.single e (1 : ℝ))).2
        simpa [matrixBilin, m, solvedCoordProbe] using hbil
      rw [hrewrite] at h
      simpa [beta, solvedCoordProbe] using h
    rw [dotProduct_solvedCoordProbe_add_single_erased A m e t hcoeff_base] at hshift
    have hdiff :
        t * (m e.1 -
          m pivot * (Matrix.mulVec (Matrix.transpose A) w) e.1 /
            (Matrix.mulVec (Matrix.transpose A) w) pivot) = 0 := by
      linarith
    simpa [m] using (mul_eq_zero.mp hdiff).resolve_left ht_ne
  have hparallel :
      ∀ w : Fin d -> ℝ, w ∈ W ->
        ∃ c : ℝ,
          Matrix.mulVec (Matrix.transpose X) w =
            c • Matrix.mulVec (Matrix.transpose A) w := by
    intro w hw
    let m : Fin d -> ℝ := Matrix.mulVec (Matrix.transpose X) w
    let a : Fin d -> ℝ := Matrix.mulVec (Matrix.transpose A) w
    have ha_pivot : a pivot ≠ 0 := by
      simpa [a] using hcoeff (w, x0.2) (hprodB w hw x0.2 hx0U)
    refine ⟨m pivot / a pivot, ?_⟩
    ext j
    by_cases hj : j = pivot
    · subst j
      rw [Pi.smul_apply]
      change m pivot = (m pivot / a pivot) * a pivot
      field_simp [ha_pivot]
    · have hjrel := hrel w hw ⟨j, hj⟩
      have hjrel' : m j = m pivot * a j / a pivot := by
        simpa [m, a] using sub_eq_zero.mp hjrel
      rw [Pi.smul_apply]
      change m j = (m pivot / a pivot) * a j
      rw [hjrel']
      ring
  have hYzero :
      ∀ w : Fin d -> ℝ, w ∈ W -> dotProduct w (Matrix.mulVec Y w) = 0 := by
    intro w hw
    let vbase : Fin d -> ℝ := (solvedCoordProbe A pivot (w, x0.2)).2
    let m : Fin d -> ℝ := Matrix.mulVec (Matrix.transpose X) w
    let beta : ℝ := dotProduct w (Matrix.mulVec Y w)
    have hx_base : (w, x0.2) ∈ B := hprodB w hw x0.2 hx0U
    have hcoeff_base :
        (Matrix.mulVec (Matrix.transpose A) w) pivot ≠ 0 :=
      hcoeff (w, x0.2) hx_base
    have hbase : dotProduct m vbase + beta = 0 := by
      have h := hvanish (w, x0.2) hx_base
      have hrewrite :
          dotProduct (solvedCoordProbe A pivot (w, x0.2)).1
              (Matrix.mulVec X (solvedCoordProbe A pivot (w, x0.2)).2) =
            dotProduct m vbase := by
        have hbil :=
          matrixBilin_eq_transpose_dot X w
            (solvedCoordProbe A pivot (w, x0.2)).2
        simpa [matrixBilin, m, vbase, solvedCoordProbe] using hbil
      rw [hrewrite] at h
      simpa [beta, vbase, solvedCoordProbe] using h
    rcases hparallel w hw with ⟨c, hc⟩
    have hquad :
        matrixBilin A w vbase = 0 := by
      simpa [vbase, solvedCoordProbe] using
        matrixBilin_solvedCoordProbe A (i := pivot) (x := (w, x0.2)) hcoeff_base
    have hadot : dotProduct (Matrix.mulVec (Matrix.transpose A) w) vbase = 0 := by
      have hbil := matrixBilin_eq_transpose_dot A w vbase
      rwa [hbil] at hquad
    have hmdot : dotProduct m vbase = 0 := by
      change dotProduct (Matrix.mulVec (Matrix.transpose X) w) vbase = 0
      rw [hc, smul_dotProduct, hadot]
      simp
    linarith
  have hW_nonempty : W.Nonempty := ⟨x0.1, hx0W⟩
  have hYsym : Y + Matrix.transpose Y = 0 :=
    matrix_symPart_eq_zero_of_forall_quadratic_eq_zero_on_open
      hW_open hW_nonempty hYzero
  have hdetAT : (Matrix.transpose A).det ≠ 0 := by
    simpa using hdet
  rcases matrix_eq_smul_of_forall_mulVec_eq_smul_on_open
      hd hW_open hW_nonempty (M := Matrix.transpose X)
      (N := Matrix.transpose A) hdetAT hparallel with
    ⟨c, hXT⟩
  refine ⟨c, ?_, hYsym⟩
  have htranspose := congrArg Matrix.transpose hXT
  simpa using htranspose

/-- Local/open-slice quadratic version of `lem:quadA`.

Any nonempty ambient-open slice of the nonsingular first-layer quadric has enough
solved-coordinate fibre variation to force the bilinear coefficient to be a scalar
multiple of `A` and the pure quadratic coefficient to have zero symmetric part. -/
theorem quadricProbeSliceQuadraticCoefficientSeparation_of_open_slice
    {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ}
    (hd : 2 ≤ d) (hdet : A.det ≠ 0)
    {P : Set (ProbePair d)}
    (hP_open : IsOpen P)
    (hslice_nonempty : (P ∩ firstLayerQuadricProbeSet A).Nonempty) :
    QuadricProbeSliceQuadraticCoefficientSeparation A
      (P ∩ firstLayerQuadricProbeSet A) := by
  classical
  intro X Y hvanish
  rcases exists_nonzero_point_mem_open_quadric_slice
      (A := A) (P := P) hd hP_open hslice_nonempty with
    ⟨p, hp, hp_ne⟩
  rcases exists_open_solvedCoordChartBase_of_nonzero_slice_point
      (A := A) (P := P) hd hdet hP_open hslice_nonempty hp hp_ne with
    ⟨pivot, x0, B, hB_open, hx0B, hcoeff, hmaps⟩
  exact
    quadricProbeSliceQuadraticCoefficientSeparation_of_open_solvedCoordChartBase
      (A := A) hd hdet hB_open hx0B hcoeff
      (X := X) (Y := Y) (by
        intro x hx
        exact hvanish (solvedCoordProbe A pivot x) (hmaps x hx))

/-- Historical name for the false global scalar identity candidate.

Kept only to state the counterexample with its original name.  New coefficient
separation wrappers consume `RegularQuadricProbeSliceNoLinearComponentData` or
`RegularQuadricProbeSliceLinearSeparationData` instead. -/
abbrev RegularQuadricProbeSliceScalarIdentityData {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  RegularQuadricProbeSliceNoLinearComponentData A

/-- The global scalar identity is false without an additional richness/nondegeneracy
hypothesis.  For the rank-one quadric `w * v = 0` in dimension one, an open
neighborhood of `(1, 0)` sees only the local branch `v = 0`, so the nonzero linear form
`v` vanishes on that relatively open slice. -/
theorem not_regularQuadricProbeSliceScalarIdentityData_rankOne :
    ¬ RegularQuadricProbeSliceScalarIdentityData
      (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  intro hidentity
  let i : Fin 1 := 0
  let P : Set (ProbePair 1) := {p | (1 / 2 : ℝ) < p.1 i}
  let m : Fin 1 -> ℝ := Pi.single i (1 : ℝ)
  let r : Fin 1 -> ℝ := 0
  have hP_open : IsOpen P := by
    have hcont : Continuous fun p : ProbePair 1 => p.1 i :=
      (continuous_apply i).comp
        (continuous_fst : Continuous fun p : ProbePair 1 => p.1)
    simpa [P] using hcont.isOpen_preimage _ isOpen_Ioi
  have hslice_nonempty :
      (P ∩ firstLayerQuadricProbeSet (1 : Matrix (Fin 1) (Fin 1) ℝ)).Nonempty := by
    refine ⟨((fun _ => (1 : ℝ)), (0 : Fin 1 -> ℝ)), ?_⟩
    constructor
    · norm_num [P]
    · simp [firstLayerQuadricProbeSet, firstLayerQuadric, matrixBilin, Matrix.mulVec,
        dotProduct]
  have hvanish :
      ∀ p : ProbePair 1, p ∈ P ->
        firstLayerQuadric (1 : Matrix (Fin 1) (Fin 1) ℝ) p ->
        dotProduct m p.2 + dotProduct r p.1 = 0 := by
    intro p hpP hpquad
    have hp1_pos : 0 < p.1 i := by
      have hp_half : (1 / 2 : ℝ) < p.1 i := hpP
      linarith
    have hp1_ne : p.1 i ≠ 0 := ne_of_gt hp1_pos
    have hprod : p.1 i * p.2 i = 0 := by
      simpa [firstLayerQuadric, matrixBilin, Matrix.mulVec, dotProduct, i] using hpquad
    have hv0 : p.2 i = 0 :=
      (mul_eq_zero.mp hprod).resolve_left hp1_ne
    simp [m, r, dotProduct, i, hv0]
  have hzero := hidentity P hP_open hslice_nonempty m r (by
    intro p hp
    exact hvanish p hp.1 hp.2)
  have hmcoord := congrFun hzero.1 i
  norm_num [m, i] at hmcoord

/-- Relatively open first-layer quadric probe slices satisfy the scalar row
coefficient-separation theorem.  This is the reduced algebraic-geometric input left
after the routine rowwise matrix reduction has been discharged. -/
def RegularQuadricProbeSliceLinearSeparationData {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ (P : Set (ProbePair d)),
    IsOpen P ->
    (P ∩ firstLayerQuadricProbeSet A).Nonempty ->
    QuadricProbeSliceLinearCoefficientSeparation A
      (P ∩ firstLayerQuadricProbeSet A)

namespace RegularQuadricProbeSliceLinearSeparationData

variable {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ}

/-- The no-linear-component hypothesis implies the rowwise slice-separation interface. -/
theorem of_noLinearComponent
    (hnoLinear : RegularQuadricProbeSliceNoLinearComponentData A) :
    RegularQuadricProbeSliceLinearSeparationData A := by
  intro P hP_open hslice_nonempty m r hvanish
  exact hnoLinear P hP_open hslice_nonempty m r (by
    intro p hp
    exact hvanish p hp)

end RegularQuadricProbeSliceLinearSeparationData

/-- Rowwise scalar slice separation implies the matrix-valued product separation used
by the matching product patch.  The only use of `J.Nonempty` is to choose one gate
value for the `M` rows. -/
theorem quadricProductCoefficientSeparation_of_probeSliceLinear
    {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ}
    {Uq : Set (ProbePair d)} {J : Set ℝ}
    (hlinear : QuadricProbeSliceLinearCoefficientSeparation A Uq)
    (hJ_nonempty : J.Nonempty) :
    QuadricProductCoefficientSeparation A Uq J := by
  intro M R hlimit
  constructor
  · rcases hJ_nonempty with ⟨t0, ht0⟩
    intro v
    ext i
    let m : Fin d -> ℝ := fun j => M i j
    let r : Fin d -> ℝ := fun j => R t0 i j
    have hrow : m = 0 ∧ r = 0 := hlinear m r (by
      intro p hp
      have hcoord := congrFun (hlimit p hp t0 ht0) i
      simpa [m, r, Matrix.mulVec, dotProduct] using hcoord)
    simp [Matrix.mulVec, dotProduct, m, hrow.1]
  · intro t ht
    ext i j
    let m : Fin d -> ℝ := fun j => M i j
    let r : Fin d -> ℝ := fun j => R t i j
    have hrow : m = 0 ∧ r = 0 := hlinear m r (by
      intro p hp
      have hcoord := congrFun (hlimit p hp t ht) i
      simpa [m, r, Matrix.mulVec, dotProduct] using hcoord)
    exact congrFun hrow.2 j

/-- Coefficient-separation input for every relatively open probe slice of the
first-layer quadric and every nonempty open gate interval.

This deliberately asks only for the Step 4 algebraic separation on `P cap Q`; the
existence of a product subneighborhood inside a relatively open set of `(probe,t)`
pairs is proved below from `isOpen_prod_iff`. -/
structure RegularQuadricProbeSliceCoefficientSeparationData {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) : Type where
  coefficient_separation :
    ∀ (P : Set (ProbePair d)) (J : Set ℝ),
      IsOpen P ->
      (P ∩ firstLayerQuadricProbeSet A).Nonempty ->
      J.Nonempty -> IsOpen J ->
      QuadricProductCoefficientSeparation A
        (P ∩ firstLayerQuadricProbeSet A) J

namespace RegularQuadricProbeSliceCoefficientSeparationData

variable {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ}

/-- Build the existing product-slice package from the smaller scalar linear separation
theorem on relatively open quadric probe slices. -/
def of_linearSeparation
    (hlinear : RegularQuadricProbeSliceLinearSeparationData A) :
    RegularQuadricProbeSliceCoefficientSeparationData A where
  coefficient_separation := by
    intro P J hP_open hUq_nonempty hJ_nonempty _hJ_open
    exact
      quadricProductCoefficientSeparation_of_probeSliceLinear
        (hlinear P hP_open hUq_nonempty) hJ_nonempty

/-- Build the product-slice coefficient-separation package from the no-linear-component
hypothesis on relatively open quadric probe slices. -/
def of_noLinearComponent
    (hnoLinear : RegularQuadricProbeSliceNoLinearComponentData A) :
    RegularQuadricProbeSliceCoefficientSeparationData A :=
  of_linearSeparation
    (RegularQuadricProbeSliceLinearSeparationData.of_noLinearComponent hnoLinear)

end RegularQuadricProbeSliceCoefficientSeparationData

/-- The local chart core before adding coefficient-separating product patches. -/
structure RegularQuadricLocalConnectedChartCoreData {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (safe : Set (ProbePair d × ℝ))
    (point : ProbePair d) (t : ℝ) : Type where
  U : Set (ProbePair d × ℝ)
  anchor_mem : (point, t) ∈ U
  subset_safe : U ⊆ safe
  relatively_open :
    ∃ W : Set (ProbePair d × ℝ),
      IsOpen W ∧
        U = W ∩
          {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1}
  connected : IsPreconnected U

/-- Reduced local connected-chart topology input.

For every open neighborhood of the regular quadric anchor, it only asks for a smaller
open ambient set whose relative quadric slab is connected.  The wrapper below supplies
the `RegularQuadricLocalConnectedChartCoreData` fields from this basis statement. -/
structure RegularQuadricLocalConnectedRelativeOpenSliceBasisData {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (point : ProbePair d) (t : ℝ) : Type where
  chart :
    ∀ V : Set (ProbePair d × ℝ), IsOpen V -> (point, t) ∈ V ->
      firstLayerQuadric A point -> firstLayerRegular A point ->
      0 < t -> t < 1 ->
      ∃ W : Set (ProbePair d × ℝ),
        IsOpen W ∧ (point, t) ∈ W ∧ W ⊆ V ∧
          IsPreconnected
            (W ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1})

/-- Smaller probe-space connected-slice primitive.

This is the remaining implicit-function/local-connectedness input without any gate
interval or product-neighborhood bookkeeping: every open probe neighborhood of a
regular point on the first-layer quadric contains a smaller open probe neighborhood
whose relative quadric slice is preconnected. -/
structure RegularQuadricLocalConnectedProbeSliceBasisData {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (point : ProbePair d) : Type where
  chart :
    ∀ P : Set (ProbePair d), IsOpen P -> point ∈ P ->
      firstLayerQuadric A point -> firstLayerRegular A point ->
      ∃ P0 : Set (ProbePair d),
        IsOpen P0 ∧ point ∈ P0 ∧ P0 ⊆ P ∧
          IsPreconnected (P0 ∩ firstLayerQuadricProbeSet A)

/-- Point-local connectedness of the quadric subtype at a regular quadric point.

This is the smaller topological primitive behind
`RegularQuadricLocalConnectedProbeSliceBasisData`: it asks for connected open
neighborhoods inside the relative topology of the quadric subtype.  The wrapper below
converts such subtype neighborhoods back into open ambient probe neighborhoods whose
intersection with the quadric is preconnected. -/
def RegularQuadricLocalConnectedQuadricSubtypeBasisData {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (point : ProbePair d) : Prop :=
  ∀ (hquad : firstLayerQuadric A point), firstLayerRegular A point ->
    ∀ S : Set {p : ProbePair d // firstLayerQuadric A p},
      IsOpen S ->
      (⟨point, hquad⟩ : {p : ProbePair d // firstLayerQuadric A p}) ∈ S ->
      ∃ S0 : Set {p : ProbePair d // firstLayerQuadric A p},
        IsOpen S0 ∧
          (⟨point, hquad⟩ : {p : ProbePair d // firstLayerQuadric A p}) ∈ S0 ∧
            S0 ⊆ S ∧ IsPreconnected S0

/-- A point-local neighborhood version of quadric-subtype local connectedness.

This is weaker than asking for `LocallyConnectedSpace` on the whole quadric subtype:
at each regular quadric point it only requires one open neighborhood whose subtype
topology is locally connected. -/
def RegularQuadricLocalConnectedQuadricSubtypeNeighborhoodData {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (point : ProbePair d) : Prop :=
  ∀ (hquad : firstLayerQuadric A point), firstLayerRegular A point ->
    ∃ U : Set {p : ProbePair d // firstLayerQuadric A p},
      IsOpen U ∧
        (⟨point, hquad⟩ : {p : ProbePair d // firstLayerQuadric A p}) ∈ U ∧
          LocallyConnectedSpace U

/-- The denominator-nonzero quadric-subtype neighborhood for a solved-coordinate
chart. -/
def regularQuadricSolvedCoordSubtypeNeighborhood {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (pivot : Fin d) :
    Set {p : ProbePair d // firstLayerQuadric A p} :=
  {q | (Matrix.mulVec (Matrix.transpose A) q.1.1) pivot ≠ 0}

/-- The denominator-nonzero base of a solved-coordinate quadric chart. -/
def regularQuadricSolvedCoordBaseNeighborhood {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (pivot : Fin d) :
    Set (QuadricGraphBase d pivot) :=
  {x | (Matrix.mulVec (Matrix.transpose A) x.1) pivot ≠ 0}

/-- Delete-coordinate projection is continuous. -/
theorem continuous_eraseCoord {d : Nat} (i : Fin d) :
    Continuous fun v : Fin d -> ℝ => eraseCoord i v := by
  rw [continuous_pi_iff]
  intro j
  simpa [eraseCoord] using
    (continuous_apply (j : Fin d) : Continuous fun v : Fin d -> ℝ => v j)

/-- The forward solved-coordinate chart from the quadric subtype to its base. -/
noncomputable def regularQuadricSolvedCoordToBase {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (pivot : Fin d) :
    regularQuadricSolvedCoordSubtypeNeighborhood A pivot ->
      regularQuadricSolvedCoordBaseNeighborhood A pivot :=
  fun q => ⟨(q.1.1.1, eraseCoord pivot q.1.1.2), q.2⟩

/-- The inverse solved-coordinate chart from the base to the quadric subtype. -/
noncomputable def regularQuadricSolvedCoordToQuadric {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (pivot : Fin d) :
    regularQuadricSolvedCoordBaseNeighborhood A pivot ->
      regularQuadricSolvedCoordSubtypeNeighborhood A pivot :=
  fun x =>
    ⟨⟨solvedCoordProbe A pivot x.1, by
        simpa [firstLayerQuadric] using
          matrixBilin_solvedCoordProbe A (i := pivot) (x := x.1) x.2⟩, by
      exact x.2⟩

/-- On the denominator-nonzero base, the solved-coordinate probe is continuous. -/
theorem continuous_solvedCoordProbe_on_coeff_ne {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (pivot : Fin d) :
    Continuous fun x : regularQuadricSolvedCoordBaseNeighborhood A pivot =>
      solvedCoordProbe A pivot x.1 := by
  rw [continuous_iff_continuousAt]
  intro x
  have h :=
    (continuousAt_solvedCoordProbe_of_coeff_ne (A := A) (pivot := pivot)
      (x0 := x.1) x.2).comp
      (continuousAt_subtype_val : ContinuousAt Subtype.val x)
  simpa [Function.comp_def] using h

/-- The forward solved-coordinate chart is continuous. -/
theorem continuous_regularQuadricSolvedCoordToBase {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (pivot : Fin d) :
    Continuous (regularQuadricSolvedCoordToBase A pivot) := by
  have hqval :
      Continuous fun q : regularQuadricSolvedCoordSubtypeNeighborhood A pivot =>
        (q.1.1 : ProbePair d) :=
    (continuous_subtype_val :
      Continuous fun q : {p : ProbePair d // firstLayerQuadric A p} =>
        (q : ProbePair d)).comp
      (continuous_subtype_val :
        Continuous fun q : regularQuadricSolvedCoordSubtypeNeighborhood A pivot =>
          (q : {p : ProbePair d // firstLayerQuadric A p}))
  have hbase :
      Continuous fun q : regularQuadricSolvedCoordSubtypeNeighborhood A pivot =>
        (q.1.1.1, eraseCoord pivot q.1.1.2) :=
    Continuous.prodMk
      ((continuous_fst : Continuous fun p : ProbePair d => p.1).comp hqval)
      ((continuous_eraseCoord pivot).comp
        ((continuous_snd : Continuous fun p : ProbePair d => p.2).comp hqval))
  exact Continuous.subtype_mk hbase (fun q => q.2)

/-- The inverse solved-coordinate chart is continuous. -/
theorem continuous_regularQuadricSolvedCoordToQuadric {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (pivot : Fin d) :
    Continuous (regularQuadricSolvedCoordToQuadric A pivot) := by
  have hquadric :
      Continuous fun x : regularQuadricSolvedCoordBaseNeighborhood A pivot =>
        (⟨solvedCoordProbe A pivot x.1, by
          simpa [firstLayerQuadric] using
            matrixBilin_solvedCoordProbe A (i := pivot) (x := x.1) x.2⟩ :
          {p : ProbePair d // firstLayerQuadric A p}) :=
    Continuous.subtype_mk (continuous_solvedCoordProbe_on_coeff_ne A pivot)
      (fun x => by
        simpa [firstLayerQuadric] using
          matrixBilin_solvedCoordProbe A (i := pivot) (x := x.1) x.2)
  exact Continuous.subtype_mk hquadric (fun x => x.2)

/-- The denominator-nonzero quadric-subtype neighborhood is homeomorphic to the
denominator-nonzero solved-coordinate base. -/
noncomputable def regularQuadricSolvedCoordNeighborhoodHomeomorph {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (pivot : Fin d) :
    regularQuadricSolvedCoordSubtypeNeighborhood A pivot ≃ₜ
      regularQuadricSolvedCoordBaseNeighborhood A pivot where
  toFun := regularQuadricSolvedCoordToBase A pivot
  invFun := regularQuadricSolvedCoordToQuadric A pivot
  left_inv := by
    intro q
    apply Subtype.ext
    apply Subtype.ext
    have hprobe :
        solvedCoordProbe A pivot (q.1.1.1, eraseCoord pivot q.1.1.2) =
          q.1.1 := by
      simpa [firstLayerQuadric] using
        solvedCoordProbe_eq_of_quadric A (i := pivot)
          (w := q.1.1.1) (v := q.1.1.2) q.2 q.1.2
    exact hprobe
  right_inv := by
    intro x
    apply Subtype.ext
    ext j <;> simp [regularQuadricSolvedCoordToBase,
      regularQuadricSolvedCoordToQuadric, solvedCoordProbe]
  continuous_toFun := continuous_regularQuadricSolvedCoordToBase A pivot
  continuous_invFun := continuous_regularQuadricSolvedCoordToQuadric A pivot

/-- Continuity of the solved-coordinate denominator on the graph base. -/
theorem continuous_regularQuadricSolvedCoordBaseCoeff {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (pivot : Fin d) :
    Continuous fun x : QuadricGraphBase d pivot =>
      (Matrix.mulVec (Matrix.transpose A) x.1) pivot := by
  have hmul :
      Continuous fun x : QuadricGraphBase d pivot =>
        Matrix.mulVec (Matrix.transpose A) x.1 := by
    rw [continuous_pi_iff]
    intro i
    simpa [Matrix.mulVec, dotProduct] using
      (continuous_finsetSum Finset.univ fun j _ =>
        continuous_const.mul
          ((continuous_apply j).comp
            (continuous_fst : Continuous fun x : QuadricGraphBase d pivot => x.1)))
  exact (continuous_apply pivot).comp hmul

/-- The solved-coordinate denominator-nonzero base is open. -/
theorem isOpen_regularQuadricSolvedCoordBaseNeighborhood {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (pivot : Fin d) :
    IsOpen (regularQuadricSolvedCoordBaseNeighborhood A pivot) := by
  simpa [regularQuadricSolvedCoordBaseNeighborhood] using
    (continuous_regularQuadricSolvedCoordBaseCoeff A pivot).isOpen_preimage
      {y : ℝ | y ≠ 0} isOpen_ne

/-- The solved-coordinate denominator-nonzero quadric-subtype neighborhood is open. -/
theorem isOpen_regularQuadricSolvedCoordSubtypeNeighborhood {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (pivot : Fin d) :
    IsOpen (regularQuadricSolvedCoordSubtypeNeighborhood A pivot) := by
  let Q := {p : ProbePair d // firstLayerQuadric A p}
  have hqval : Continuous fun q : Q => (q : ProbePair d) := continuous_subtype_val
  have hcoeff :
      Continuous fun q : Q =>
        (Matrix.mulVec (Matrix.transpose A) q.1.1) pivot :=
    (continuous_apply pivot).comp
      ((continuous_firstLayer_transpose_mulVec_left A).comp hqval)
  simpa [regularQuadricSolvedCoordSubtypeNeighborhood, Q] using
    hcoeff.isOpen_preimage {y : ℝ | y ≠ 0} isOpen_ne

/-- The denominator-nonzero quadric-subtype solved-coordinate neighborhood is locally
connected. -/
theorem locallyConnectedSpace_regularQuadricSolvedCoordSubtypeNeighborhood {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (pivot : Fin d) :
    LocallyConnectedSpace (regularQuadricSolvedCoordSubtypeNeighborhood A pivot) := by
  have hbase_open := isOpen_regularQuadricSolvedCoordBaseNeighborhood A pivot
  haveI : LocallyConnectedSpace (regularQuadricSolvedCoordBaseNeighborhood A pivot) :=
    hbase_open.locallyConnectedSpace
  exact (regularQuadricSolvedCoordNeighborhoodHomeomorph A pivot).locallyConnectedSpace

/-- A nonzero finite coordinate vector has a nonzero coordinate. -/
theorem exists_fin_apply_ne_zero_of_ne_zero {d : Nat} {x : Fin d -> ℝ}
    (hx : x ≠ 0) :
    ∃ i : Fin d, x i ≠ 0 := by
  by_contra h
  apply hx
  ext i
  exact by_contra fun hi => h ⟨i, hi⟩

/-- Regular quadric points have a locally connected quadric-subtype neighborhood.

The proof chooses a solved-coordinate pivot where `Aᵀ * point.1` is nonzero and uses
the explicit solved-coordinate chart above. -/
theorem regularQuadricLocalConnectedQuadricSubtypeNeighborhoodData_of_solvedCoordChart
    {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ} {point : ProbePair d} :
    RegularQuadricLocalConnectedQuadricSubtypeNeighborhoodData A point := by
  intro hquad hregular
  rcases exists_fin_apply_ne_zero_of_ne_zero hregular.2.1 with ⟨pivot, hcoeff⟩
  refine ⟨regularQuadricSolvedCoordSubtypeNeighborhood A pivot,
    isOpen_regularQuadricSolvedCoordSubtypeNeighborhood A pivot, ?_, ?_⟩
  · simpa [regularQuadricSolvedCoordSubtypeNeighborhood] using hcoeff
  · exact locallyConnectedSpace_regularQuadricSolvedCoordSubtypeNeighborhood A pivot

namespace RegularQuadricLocalConnectedQuadricSubtypeBasisData

variable {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ}
variable {point : ProbePair d}

/-- An open locally connected quadric-subtype neighborhood supplies the point-local
subtype basis. -/
theorem of_locallyConnectedNeighborhood
    (hneighborhood :
      RegularQuadricLocalConnectedQuadricSubtypeNeighborhoodData A point) :
    RegularQuadricLocalConnectedQuadricSubtypeBasisData A point := by
  classical
  intro hquad hregular S hS_open hpointS
  let Q := {p : ProbePair d // firstLayerQuadric A p}
  let qpoint : Q := ⟨point, hquad⟩
  rcases hneighborhood hquad hregular with
    ⟨U, hU_open, hqpointU, hU_local⟩
  let USubtype := U
  let uPoint : USubtype := ⟨qpoint, hqpointU⟩
  let SU : Set USubtype := {u | (u : Q) ∈ S}
  have hSU_open : IsOpen SU :=
    hS_open.preimage continuous_subtype_val
  have huPointSU : uPoint ∈ SU := hpointS
  rcases (locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp hU_local)
      uPoint SU (hSU_open.mem_nhds huPointSU) with
    ⟨T, hT_subset, hT_open, huPointT, hT_connected⟩
  rcases isOpen_induced_iff.mp hT_open with ⟨TQ, hTQ_open, hTQ_preimage⟩
  let S0 : Set Q := U ∩ TQ
  have hS0_image :
      Set.image (fun u : USubtype => (u : Q)) T = S0 := by
    ext q
    constructor
    · rintro ⟨u, huT, rfl⟩
      have huTQ : (u : Q) ∈ TQ := by
        change u ∈ ((fun u : USubtype => (u : Q)) ⁻¹' TQ)
        rw [hTQ_preimage]
        exact huT
      exact ⟨u.property, huTQ⟩
    · intro hq
      refine ⟨⟨q, hq.1⟩, ?_, rfl⟩
      change (⟨q, hq.1⟩ : USubtype) ∈ T
      rw [← hTQ_preimage]
      exact hq.2
  refine ⟨S0, hU_open.inter hTQ_open, ?_, ?_, ?_⟩
  · exact ⟨hqpointU, by
      change uPoint ∈ ((fun u : USubtype => (u : Q)) ⁻¹' TQ)
      rw [hTQ_preimage]
      exact huPointT⟩
  · intro q hq
    have hqT : (⟨q, hq.1⟩ : USubtype) ∈ T := by
      change (⟨q, hq.1⟩ : USubtype) ∈ T
      rw [← hTQ_preimage]
      exact hq.2
    exact hT_subset hqT
  · rw [← hS0_image]
    exact hT_connected.isPreconnected.image
      (fun u : USubtype => (u : Q)) continuous_subtype_val.continuousOn

end RegularQuadricLocalConnectedQuadricSubtypeBasisData

namespace RegularQuadricLocalConnectedQuadricSubtypeNeighborhoodData

variable {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ}
variable {point : ProbePair d}

/-- A locally connected quadric-subtype neighborhood is the provider-facing
local-connectedness input behind the subtype-basis fact used by the reduced IDL
region wrapper. -/
theorem toBasisData
    (hneighborhood :
      RegularQuadricLocalConnectedQuadricSubtypeNeighborhoodData A point) :
    RegularQuadricLocalConnectedQuadricSubtypeBasisData A point :=
  RegularQuadricLocalConnectedQuadricSubtypeBasisData.of_locallyConnectedNeighborhood
    hneighborhood

end RegularQuadricLocalConnectedQuadricSubtypeNeighborhoodData

/-- Provider-facing reduced chart/coefficient data for a regular quadric anchor.

The coefficient field is the corrected no-linear-component condition; it is not
derived from the old global scalar identity, which is false by
`not_regularQuadricProbeSliceScalarIdentityData_rankOne`.  The topology field uses
the point-local locally connected neighborhood form, from which the existing
subtype-basis fact is recovered by a wrapper. -/
structure RegularQuadricReducedChartCoefficientData {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (point : ProbePair d) : Type where
  locally_connected_neighborhood :
    RegularQuadricLocalConnectedQuadricSubtypeNeighborhoodData A point
  no_linear_component : RegularQuadricProbeSliceNoLinearComponentData A

namespace RegularQuadricReducedChartCoefficientData

variable {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ}
variable {point : ProbePair d}

/-- Expose the local-connectedness field in the basis form currently consumed by the
reduced IDL-region constructor. -/
theorem quadricSubtypeBasisData
    (G : RegularQuadricReducedChartCoefficientData A point) :
    RegularQuadricLocalConnectedQuadricSubtypeBasisData A point :=
  G.locally_connected_neighborhood.toBasisData

/-- Expose the corrected scalar slice nondegeneracy field currently consumed by the
reduced IDL-region constructor. -/
theorem noLinearComponentData
    (G : RegularQuadricReducedChartCoefficientData A point) :
    RegularQuadricProbeSliceNoLinearComponentData A :=
  G.no_linear_component

end RegularQuadricReducedChartCoefficientData

namespace RegularQuadricLocalConnectedProbeSliceBasisData

variable {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ}
variable {point : ProbePair d} {t : ℝ}

/-- Convert the quadric-subtype local connectedness basis into the ambient probe-slice
basis required by the product-slab construction. -/
def of_quadricSubtypeBasis
    (B : RegularQuadricLocalConnectedQuadricSubtypeBasisData A point) :
    RegularQuadricLocalConnectedProbeSliceBasisData A point where
  chart := by
    classical
    intro P hP_open hpointP hquad hregular
    let Q := {p : ProbePair d // firstLayerQuadric A p}
    let qpoint : Q := ⟨point, hquad⟩
    let S : Set Q := Set.preimage (fun q : Q => (q : ProbePair d)) P
    have hS_open : IsOpen S := hP_open.preimage continuous_subtype_val
    have hqpointS : qpoint ∈ S := hpointP
    rcases B hquad hregular S hS_open hqpointS with
      ⟨S0, hS0_open, hqpointS0, hS0_subset, hS0_connected⟩
    rcases isOpen_induced_iff.mp hS0_open with ⟨P1, hP1_open, hP1_preimage⟩
    let P0 : Set (ProbePair d) := P ∩ P1
    have hpointP1 : point ∈ P1 := by
      have : qpoint ∈ Set.preimage (fun q : Q => (q : ProbePair d)) P1 := by
        simpa [hP1_preimage] using hqpointS0
      exact this
    have himage_eq :
        Set.image (fun q : Q => (q : ProbePair d)) S0 =
          P0 ∩ firstLayerQuadricProbeSet A := by
      ext x
      constructor
      · rintro ⟨q, hqS0, rfl⟩
        have hqP : (q : ProbePair d) ∈ P := hS0_subset hqS0
        have hqP1 : (q : ProbePair d) ∈ P1 := by
          have : q ∈ Set.preimage (fun q : Q => (q : ProbePair d)) P1 := by
            simpa [hP1_preimage] using hqS0
          exact this
        exact ⟨⟨hqP, hqP1⟩, q.property⟩
      · intro hx
        rcases hx with ⟨⟨hxP, hxP1⟩, hxquad⟩
        refine ⟨⟨x, hxquad⟩, ?_, rfl⟩
        have :
            (⟨x, hxquad⟩ : Q) ∈
              Set.preimage (fun q : Q => (q : ProbePair d)) P1 := hxP1
        simpa [hP1_preimage] using this
    refine ⟨P0, hP_open.inter hP1_open, ⟨hpointP, hpointP1⟩, ?_, ?_⟩
    · exact fun _ hx => hx.1
    · rw [← himage_eq]
      exact
        hS0_connected.image (fun q : Q => (q : ProbePair d))
          continuous_subtype_val.continuousOn

/-- A connected probe-slice basis gives the product connected-slab basis by shrinking
the real gate coordinate to an interval contained in the supplied open neighborhood
and in `(0, 1)`. -/
noncomputable def toRelativeOpenSliceBasisData
    (B : RegularQuadricLocalConnectedProbeSliceBasisData A point) :
    RegularQuadricLocalConnectedRelativeOpenSliceBasisData A point t where
  chart := by
    intro V hV_open hpointV hquad hregular ht_pos ht_lt
    let prodWitness := isOpen_prod_iff.mp hV_open point t hpointV
    let P : Set (ProbePair d) := Classical.choose prodWitness
    have hP_spec :
        ∃ J0 : Set ℝ,
          IsOpen P ∧ IsOpen J0 ∧ point ∈ P ∧ t ∈ J0 ∧
            P ×ˢ J0 ⊆ V :=
      Classical.choose_spec prodWitness
    let J0 : Set ℝ := Classical.choose hP_spec
    have hJ0_spec :
        IsOpen P ∧ IsOpen J0 ∧ point ∈ P ∧ t ∈ J0 ∧
          P ×ˢ J0 ⊆ V :=
      Classical.choose_spec hP_spec
    have hP_open : IsOpen P := hJ0_spec.1
    have hJ0_open : IsOpen J0 := hJ0_spec.2.1
    have hpointP : point ∈ P := hJ0_spec.2.2.1
    have htJ0 : t ∈ J0 := hJ0_spec.2.2.2.1
    have hprod_subset : P ×ˢ J0 ⊆ V := hJ0_spec.2.2.2.2
    let hprobe := B.chart P hP_open hpointP hquad hregular
    let P0 : Set (ProbePair d) := Classical.choose hprobe
    have hP0_spec :
        IsOpen P0 ∧ point ∈ P0 ∧ P0 ⊆ P ∧
          IsPreconnected (P0 ∩ firstLayerQuadricProbeSet A) :=
      Classical.choose_spec hprobe
    have hP0_open : IsOpen P0 := hP0_spec.1
    have hpointP0 : point ∈ P0 := hP0_spec.2.1
    have hP0_subset : P0 ⊆ P := hP0_spec.2.2.1
    have hP0_connected : IsPreconnected (P0 ∩ firstLayerQuadricProbeSet A) :=
      hP0_spec.2.2.2
    have hgate_mem :
        J0 ∩ Set.Ioo (0 : ℝ) 1 ∈ nhds t :=
      (hJ0_open.inter isOpen_Ioo).mem_nhds ⟨htJ0, ht_pos, ht_lt⟩
    rcases mem_nhds_iff_exists_Ioo_subset.mp hgate_mem with
      ⟨a, b, htI, hI_subset_gate⟩
    let I : Set ℝ := Set.Ioo a b
    let W : Set (ProbePair d × ℝ) := P0 ×ˢ I
    have hI_open : IsOpen I := isOpen_Ioo
    have hI_connected : IsPreconnected I := isPreconnected_Ioo
    have hI_subset_I01 : I ⊆ Set.Ioo (0 : ℝ) 1 := by
      intro s hs
      exact (hI_subset_gate hs).2
    have hslice_eq :
        W ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1} =
          (P0 ∩ firstLayerQuadricProbeSet A) ×ˢ I := by
      ext x
      constructor
      · intro hx
        exact ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
      · intro hx
        have hxI01 : x.2 ∈ Set.Ioo (0 : ℝ) 1 := hI_subset_I01 hx.2
        exact ⟨⟨hx.1.1, hx.2⟩, hx.1.2, hxI01.1, hxI01.2⟩
    refine ⟨W, hP0_open.prod hI_open, ?_, ?_, ?_⟩
    · exact ⟨hpointP0, htI⟩
    · intro x hx
      exact hprod_subset ⟨hP0_subset hx.1, (hI_subset_gate hx.2).1⟩
    · rw [hslice_eq]
      exact hP0_connected.prod hI_connected

end RegularQuadricLocalConnectedProbeSliceBasisData

/-- The solved-coordinate chart supplies the relative-open slice basis used by the
finite cascade wrappers. -/
noncomputable def regularQuadricLocalConnectedRelativeOpenSliceBasisData_of_solvedCoordChart
    {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (point : ProbePair d) (t : ℝ) :
    RegularQuadricLocalConnectedRelativeOpenSliceBasisData A point t :=
  let neighborhood :
      RegularQuadricLocalConnectedQuadricSubtypeNeighborhoodData A point :=
    regularQuadricLocalConnectedQuadricSubtypeNeighborhoodData_of_solvedCoordChart
      (A := A) (point := point)
  let quadricBasis :
      RegularQuadricLocalConnectedQuadricSubtypeBasisData A point :=
    RegularQuadricLocalConnectedQuadricSubtypeBasisData.of_locallyConnectedNeighborhood
      neighborhood
  (RegularQuadricLocalConnectedProbeSliceBasisData.of_quadricSubtypeBasis
    (A := A) (point := point) quadricBasis).toRelativeOpenSliceBasisData
      (t := t)

namespace RegularQuadricLocalConnectedChartCoreData

variable {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ}
variable {safe : Set (ProbePair d × ℝ)}
variable {point : ProbePair d} {t : ℝ}

/-- Relative openness of a nonempty subregion of a chart supplies an ordinary product
subneighborhood.  The only non-topological field is filled by
`RegularQuadricProbeSliceCoefficientSeparationData`. -/
noncomputable def productNeighborhood
    (G : RegularQuadricLocalConnectedChartCoreData A safe point t)
    (sep : RegularQuadricProbeSliceCoefficientSeparationData A)
    (hd : 2 ≤ d) (hdet : A.det ≠ 0) :
    ∀ U0 : Set (ProbePair d × ℝ), U0 ⊆ G.U -> U0.Nonempty ->
      (∃ W0 : Set (ProbePair d × ℝ), IsOpen W0 ∧ U0 = W0 ∩ G.U) ->
      CoefficientSeparatingProductPatch A U0 := by
  classical
  intro U0 hU0_subset hU0_nonempty hU0_rel
  let x : ProbePair d × ℝ := Classical.choose hU0_nonempty
  have hxU0 : x ∈ U0 := Classical.choose_spec hU0_nonempty
  let W0 : Set (ProbePair d × ℝ) := Classical.choose hU0_rel
  have hW0_spec : IsOpen W0 ∧ U0 = W0 ∩ G.U :=
    Classical.choose_spec hU0_rel
  have hW0_open : IsOpen W0 := hW0_spec.1
  have hU0_eq : U0 = W0 ∩ G.U := hW0_spec.2
  let W : Set (ProbePair d × ℝ) := Classical.choose G.relatively_open
  have hW_spec :
      IsOpen W ∧
        G.U = W ∩
          {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1} :=
    Classical.choose_spec G.relatively_open
  have hW_open : IsOpen W := hW_spec.1
  have hU_eq :
      G.U = W ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1} :=
    hW_spec.2
  have hxU : x ∈ G.U := hU0_subset hxU0
  have hxW0U : x ∈ W0 ∩ G.U := by
    simpa [hU0_eq] using hxU0
  have hxW0 : x ∈ W0 := hxW0U.1
  have hxWQ :
      x ∈ W ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1} := by
    simpa [hU_eq] using hxU
  have hxW : x ∈ W := hxWQ.1
  have hxquad : firstLayerQuadric A x.1 := hxWQ.2.1
  have hxt_pos : 0 < x.2 := hxWQ.2.2.1
  have hxt_lt : x.2 < 1 := hxWQ.2.2.2
  have hW0W_open : IsOpen (W0 ∩ W) := hW0_open.inter hW_open
  have hxW0W : x ∈ W0 ∩ W := ⟨hxW0, hxW⟩
  let prodWitness := isOpen_prod_iff.mp hW0W_open x.1 x.2 hxW0W
  let P : Set (ProbePair d) := Classical.choose prodWitness
  have hP_spec :
      ∃ J0 : Set ℝ,
        IsOpen P ∧ IsOpen J0 ∧ x.1 ∈ P ∧ x.2 ∈ J0 ∧
          P ×ˢ J0 ⊆ W0 ∩ W :=
    Classical.choose_spec prodWitness
  let J0 : Set ℝ := Classical.choose hP_spec
  have hJ0_spec :
      IsOpen P ∧ IsOpen J0 ∧ x.1 ∈ P ∧ x.2 ∈ J0 ∧
        P ×ˢ J0 ⊆ W0 ∩ W :=
    Classical.choose_spec hP_spec
  have hP_open : IsOpen P := hJ0_spec.1
  have hJ0_open : IsOpen J0 := hJ0_spec.2.1
  have hxP : x.1 ∈ P := hJ0_spec.2.2.1
  have hxJ0 : x.2 ∈ J0 := hJ0_spec.2.2.2.1
  have hprod_subset_W0W : P ×ˢ J0 ⊆ W0 ∩ W := hJ0_spec.2.2.2.2
  let Uq : Set (ProbePair d) := P ∩ firstLayerQuadricProbeSet A
  let J : Set ℝ := J0 ∩ Set.Ioo (0 : ℝ) 1
  have hUq_nonempty : Uq.Nonempty :=
    ⟨x.1, hxP, hxquad⟩
  have hJ_nonempty : J.Nonempty :=
    ⟨x.2, hxJ0, hxt_pos, hxt_lt⟩
  have hJ_open : IsOpen J := hJ0_open.inter isOpen_Ioo
  exact
    { Uq := Uq
      J := J
      Uq_nonempty := hUq_nonempty
      J_nonempty := hJ_nonempty
      J_open := hJ_open
      Uq_on_quadric := by
        intro p hp
        exact hp.2
      product_subset := by
        intro y hy
        have hyW0W : y ∈ W0 ∩ W := hprod_subset_W0W (by
          exact Set.mem_prod.mpr ⟨hy.1.1, hy.2.1⟩)
        have hyU : y ∈ G.U := by
          have hyWQ :
              y ∈ W ∩
                {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1} :=
            ⟨hyW0W.2, hy.1.2, hy.2.2.1, hy.2.2.2⟩
          simpa [hU_eq] using hyWQ
        have hyW0U : y ∈ W0 ∩ G.U := ⟨hyW0W.1, hyU⟩
        simpa [hU0_eq] using hyW0U
      quadratic_coefficient_separation :=
        quadricProbeSliceQuadraticCoefficientSeparation_of_open_slice
          hd hdet hP_open hUq_nonempty
      coefficient_separation :=
        sep.coefficient_separation P J hP_open hUq_nonempty hJ_nonempty hJ_open }

/-- Add coefficient-separating product patches to a local chart core. -/
noncomputable def withProbeSliceCoefficientSeparation
    (G : RegularQuadricLocalConnectedChartCoreData A safe point t)
    (sep : RegularQuadricProbeSliceCoefficientSeparationData A)
    (hd : 2 ≤ d) (hdet : A.det ≠ 0) :
    RegularQuadricLocalConnectedCoefficientSeparatingChartData A safe point t where
  U := G.U
  anchor_mem := G.anchor_mem
  subset_safe := G.subset_safe
  relatively_open := G.relatively_open
  connected := G.connected
  product_neighborhood := G.productNeighborhood sep hd hdet

end RegularQuadricLocalConnectedChartCoreData

/-- Open-neighborhood version of the chart core before product-patch separation. -/
structure RegularQuadricLocalConnectedOpenNeighborhoodChartCoreData {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (point : ProbePair d) (t : ℝ) : Type where
  chart :
    ∀ V : Set (ProbePair d × ℝ), IsOpen V -> (point, t) ∈ V ->
      firstLayerQuadric A point -> firstLayerRegular A point ->
      0 < t -> t < 1 ->
      RegularQuadricLocalConnectedChartCoreData A V point t

namespace RegularQuadricLocalConnectedRelativeOpenSliceBasisData

variable {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ}
variable {point : ProbePair d} {t : ℝ}

/-- Convert the reduced relative-open connected slice basis into the chart-core
interface.  This discharges the anchor membership, containment, and relative-openness
bookkeeping around the remaining local connectedness theorem. -/
noncomputable def toOpenNeighborhoodChartCoreData
    (B : RegularQuadricLocalConnectedRelativeOpenSliceBasisData A point t) :
    RegularQuadricLocalConnectedOpenNeighborhoodChartCoreData A point t where
  chart := by
    intro V hV_open hpointV hquad hregular ht_pos ht_lt
    let hchart := B.chart V hV_open hpointV hquad hregular ht_pos ht_lt
    let W : Set (ProbePair d × ℝ) := Classical.choose hchart
    have hW_spec :
        IsOpen W ∧ (point, t) ∈ W ∧ W ⊆ V ∧
          IsPreconnected
            (W ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1}) :=
      Classical.choose_spec hchart
    have hW_open : IsOpen W := hW_spec.1
    have hpointW : (point, t) ∈ W := hW_spec.2.1
    have hW_subset : W ⊆ V := hW_spec.2.2.1
    have hconnected :
        IsPreconnected
          (W ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1}) :=
      hW_spec.2.2.2
    exact
      { U := W ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1}
        anchor_mem := ⟨hpointW, hquad, ht_pos, ht_lt⟩
        subset_safe := by
          intro x hx
          exact hW_subset hx.1
        relatively_open := ⟨W, hW_open, rfl⟩
        connected := hconnected }

end RegularQuadricLocalConnectedRelativeOpenSliceBasisData

/-- Local connected sign neighborhood in the nonzero branch of the trichotomy.

Around a regular quadric-slab point where the scalar observable `Λ` is nonzero,
shrink any relatively open slab neighborhood to a nonempty relatively open
preconnected subneighborhood on which `Λ` has constant sign. -/
theorem exists_localConnectedSignNeighborhood
    {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ}
    {x0 : ProbePair d × ℝ} {U0 : Set (ProbePair d × ℝ)}
    {Λ : ProbePair d × ℝ -> ℝ}
    (basis : RegularQuadricLocalConnectedRelativeOpenSliceBasisData A x0.1 x0.2)
    (hU0_rel :
      ∃ W0 : Set (ProbePair d × ℝ), IsOpen W0 ∧
        U0 = W0 ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1})
    (hx0 : x0 ∈ U0)
    (hregular : firstLayerRegular A x0.1)
    (hΛ : Continuous Λ)
    (hΛx0 : Λ x0 ≠ 0) :
    ∃ U1 : Set (ProbePair d × ℝ),
      x0 ∈ U1 ∧
      U1 ⊆ U0 ∧
      (∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ U1 = W ∩ U0) ∧
      U1.Nonempty ∧
      IsPreconnected U1 ∧
      (∀ x ∈ U1, Λ x ≠ 0) ∧
      ((∀ x ∈ U1, 0 < Λ x) ∨ (∀ x ∈ U1, Λ x < 0)) := by
  rcases hU0_rel with ⟨W0, hW0_open, hU0_eq⟩
  let slab : Set (ProbePair d × ℝ) :=
    {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1}
  have hx0U0_slab : x0 ∈ W0 ∩ slab := by
    simpa [slab, hU0_eq] using hx0
  have hx0W0 : x0 ∈ W0 := hx0U0_slab.1
  have hquad : firstLayerQuadric A x0.1 := hx0U0_slab.2.1
  have ht_pos : 0 < x0.2 := hx0U0_slab.2.2.1
  have ht_lt : x0.2 < 1 := hx0U0_slab.2.2.2
  let V : Set (ProbePair d × ℝ) := W0 ∩ {x | Λ x ≠ 0}
  have hΛ_ne_open : IsOpen {x : ProbePair d × ℝ | Λ x ≠ 0} := by
    simpa using hΛ.isOpen_preimage {y : ℝ | y ≠ 0} isOpen_ne
  have hV_open : IsOpen V := hW0_open.inter hΛ_ne_open
  have hx0V : x0 ∈ V := ⟨hx0W0, hΛx0⟩
  rcases basis.chart V hV_open hx0V hquad hregular ht_pos ht_lt with
    ⟨W, hW_open, hx0W, hW_subsetV, hW_preconnected⟩
  let U1 : Set (ProbePair d × ℝ) := W ∩ slab
  have hx0U1 : x0 ∈ U1 := ⟨hx0W, hquad, ht_pos, ht_lt⟩
  have hU1_subset_U0 : U1 ⊆ U0 := by
    intro x hx
    have hxW0 : x ∈ W0 := (hW_subsetV hx.1).1
    have hxU0_slab : x ∈ W0 ∩ slab := ⟨hxW0, hx.2⟩
    simpa [slab, hU0_eq] using hxU0_slab
  have hU1_rel_open : ∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ U1 = W ∩ U0 := by
    refine ⟨W, hW_open, ?_⟩
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, hU1_subset_U0 hx⟩
    · intro hx
      have hxU0_slab : x ∈ W0 ∩ slab := by
        simpa [slab, hU0_eq] using hx.2
      exact ⟨hx.1, hxU0_slab.2⟩
  have hU1_nonempty : U1.Nonempty := ⟨x0, hx0U1⟩
  have hU1_preconnected : IsPreconnected U1 := by
    simpa [U1, slab] using hW_preconnected
  have hU1_zero_free : ∀ x ∈ U1, Λ x ≠ 0 := by
    intro x hx
    exact (hW_subsetV hx.1).2
  have hU1_sign :
      (∀ x ∈ U1, 0 < Λ x) ∨ (∀ x ∈ U1, Λ x < 0) := by
    by_cases hpos0 : 0 < Λ x0
    · left
      intro x hx
      exact
        hU1_preconnected.lt_of_ne hΛ.continuousOn hU1_zero_free
          ⟨x0, hx0U1, hpos0⟩ hx
    · right
      have hle0 : Λ x0 ≤ 0 := le_of_not_gt hpos0
      have hneg0 : Λ x0 < 0 := lt_of_le_of_ne hle0 hΛx0
      intro x hx
      exact
        hU1_preconnected.gt_of_ne hΛ.continuousOn hU1_zero_free
          ⟨x0, hx0U1, hneg0⟩ hx
  exact
    ⟨U1, hx0U1, hU1_subset_U0, hU1_rel_open, hU1_nonempty,
      hU1_preconnected, hU1_zero_free, hU1_sign⟩

/-- Step2-facing wrapper that uses the local connected quadric basis to supply the
connected constant-sign neighborhood required by the canonical nonzero cascade branch
choice constructor. -/
noncomputable def
    cascadeLevelBranchChoice_nonzero_of_canonicalFrecGateAlongSignRegion_point_from_basis
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (A : Matrix (Fin d) (Fin d) ℝ)
    (U0 : Set (ProbePair d × ℝ))
    (hU0 : U0 ⊆ signRegion.U)
    (hU0_rel :
      ∃ W0 : Set (ProbePair d × ℝ), IsOpen W0 ∧
        U0 = W0 ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1})
    (x0 : ProbePair d × ℝ)
    (hx0 : x0 ∈ U0)
    (basis : RegularQuadricLocalConnectedRelativeOpenSliceBasisData A x0.1 x0.2)
    (hregular : firstLayerRegular A x0.1)
    (level : Nat) (tail : Nat -> ℝ)
    (hlevel_pos : 1 ≤ level) (hlevel_lt : level < L + 1)
    (prior_saturates :
      ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n -> n < level ->
        EventuallyExpClose
          (fun τ => canonicalFrecGateAlongSignRegion r signRegion θ n x τ)
          (tail (n - 1)))
    (provider : CascadeCurveRigidityProvider θ A level tail)
    (hslope_x0 :
      specializedPhi θ level (gateAssignmentOfTail x0.2 tail) x0.1 ≠ 0) :
    CascadeLevelBranchChoice (Real.log (r : ℝ)) θ A U0
      (canonicalFrecGateAlongSignRegion r signRegion θ) level tail := by
  let Λ : ProbePair d × ℝ -> ℝ :=
    fun x => (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re
  have hΛ : Continuous Λ := by
    simpa [Λ] using continuous_specializedPhi_gateAssignmentOfTail_re θ level tail
  have hΛx0 : Λ x0 ≠ 0 := by
    have hre_ne :
        (specializedPhi θ level (gateAssignmentOfTail x0.2 tail) x0.1).re ≠ 0 :=
      specializedPhi_gateAssignmentOfTail_re_ne_zero_of_ne θ level x0.2 tail x0.1
        hslope_x0
    simpa [Λ] using hre_ne
  have localSignNeighborhood :
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
          (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re < 0)) := by
    have hlocal :=
      exists_localConnectedSignNeighborhood
        (A := A) (x0 := x0) (U0 := U0) (Λ := Λ)
        basis hU0_rel hx0 hregular hΛ hΛx0
    simpa [Λ] using hlocal
  exact
    cascadeLevelBranchChoice_nonzero_of_canonicalFrecGateAlongSignRegion_point
      signRegion hAA A U0 hU0 x0 level tail hlevel_pos hlevel_lt
      prior_saturates provider localSignNeighborhood

/-- Step2-facing nonzero branch choice from a point-local basis that does not require
a zero-branch provider.  The zero branch is unreachable because the selected point has
nonzero specialized slope. -/
noncomputable def
    cascadeLevelBranchChoice_nonzero_of_canonicalFrecGateAlongSignRegion_point_from_basis_noZeroBranchProvider
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (A : Matrix (Fin d) (Fin d) ℝ)
    (U0 : Set (ProbePair d × ℝ))
    (hU0 : U0 ⊆ signRegion.U)
    (hU0_rel :
      ∃ W0 : Set (ProbePair d × ℝ), IsOpen W0 ∧
        U0 = W0 ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1})
    (x0 : ProbePair d × ℝ)
    (hx0 : x0 ∈ U0)
    (basis : RegularQuadricLocalConnectedRelativeOpenSliceBasisData A x0.1 x0.2)
    (hregular : firstLayerRegular A x0.1)
    (level : Nat) (tail : Nat -> ℝ)
    (hlevel_pos : 1 ≤ level) (hlevel_lt : level < L + 1)
    (prior_saturates :
      ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n -> n < level ->
        EventuallyExpClose
          (fun τ => canonicalFrecGateAlongSignRegion r signRegion θ n x τ)
          (tail (n - 1)))
    (hslope_x0 :
      specializedPhi θ level (gateAssignmentOfTail x0.2 tail) x0.1 ≠ 0) :
    CascadeLevelBranchChoice (Real.log (r : ℝ)) θ A U0
      (canonicalFrecGateAlongSignRegion r signRegion θ) level tail := by
  let Λ : ProbePair d × ℝ -> ℝ :=
    fun x => (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re
  have hΛ : Continuous Λ := by
    simpa [Λ] using continuous_specializedPhi_gateAssignmentOfTail_re θ level tail
  have hΛx0 : Λ x0 ≠ 0 := by
    have hre_ne :
        (specializedPhi θ level (gateAssignmentOfTail x0.2 tail) x0.1).re ≠ 0 :=
      specializedPhi_gateAssignmentOfTail_re_ne_zero_of_ne θ level x0.2 tail x0.1
        hslope_x0
    simpa [Λ] using hre_ne
  have localSignNeighborhood :
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
          (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re < 0)) := by
    have hlocal :=
      exists_localConnectedSignNeighborhood
        (A := A) (x0 := x0) (U0 := U0) (Λ := Λ)
        basis hU0_rel hx0 hregular hΛ hΛx0
    simpa [Λ] using hlocal
  exact
    cascadeLevelBranchChoice_nonzero_of_canonicalFrecGateAlongSignRegion_point_noZeroBranchProvider
      signRegion hAA A U0 hU0 x0 level tail hlevel_pos hlevel_lt
      prior_saturates localSignNeighborhood

/-- Step2-facing one-level zero/nonzero branch choice for the canonical unprimed
actual gate.  The zero branch preserves the current component; the nonzero branch
shrinks using the local connected quadric basis at a nonzero witness. -/
noncomputable def
    cascadeLevelBranchChoice_of_canonicalFrecGateAlongSignRegion_dichotomy_from_basis
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (A : Matrix (Fin d) (Fin d) ℝ)
    (U0 : Set (ProbePair d × ℝ))
    (hU0 : U0 ⊆ signRegion.U)
    (U0_nonempty : U0.Nonempty)
    (U0_connected : IsPreconnected U0)
    (hU0_rel :
      ∃ W0 : Set (ProbePair d × ℝ), IsOpen W0 ∧
        U0 = W0 ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1})
    (basis_at :
      ∀ x ∈ U0, RegularQuadricLocalConnectedRelativeOpenSliceBasisData A x.1 x.2)
    (regular_at : ∀ x ∈ U0, firstLayerRegular A x.1)
    {levelPred : Nat} (tail : Nat -> ℝ)
    (hlevel_lt : levelPred + 1 < L + 1)
    (prior_saturates :
      ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n -> n < levelPred + 1 ->
        EventuallyExpClose
          (fun τ => canonicalFrecGateAlongSignRegion r signRegion θ n x τ)
          (tail (n - 1)))
    (provider : CascadeCurveRigidityProvider θ A (levelPred + 1) tail)
    (dimension_pos : 0 < d)
    (head_det_ne_zero : A.det ≠ 0)
    (head_sym_ne_zero : symPart A ≠ 0)
    (head_value_ne_zero : (paramStream θ 0).1 ≠ 0) :
    CascadeLevelBranchChoice (Real.log (r : ℝ)) θ A U0
      (canonicalFrecGateAlongSignRegion r signRegion θ) (levelPred + 1) tail := by
  classical
  by_cases hzero :
      ∀ x ∈ U0,
        specializedPhi θ (levelPred + 1) (gateAssignmentOfTail x.2 tail) x.1 = 0
  · exact
      cascadeLevelBranchChoice_zeroAlpha_of_canonicalFrecGateAlongSignRegion
        signRegion hAA A U0 hU0 U0_nonempty U0_connected tail hlevel_lt
        prior_saturates provider hzero dimension_pos head_det_ne_zero
        head_sym_ne_zero head_value_ne_zero
  · have hex :
        ∃ x0, x0 ∈ U0 ∧
          specializedPhi θ (levelPred + 1) (gateAssignmentOfTail x0.2 tail) x0.1 ≠ 0 := by
      by_contra hnone
      apply hzero
      intro x hx
      by_contra hne
      exact hnone ⟨x, hx, hne⟩
    let x0 : ProbePair d × ℝ := Classical.choose hex
    have hx0_spec :
        x0 ∈ U0 ∧
          specializedPhi θ (levelPred + 1) (gateAssignmentOfTail x0.2 tail) x0.1 ≠ 0 := by
      simpa [x0] using Classical.choose_spec hex
    have hx0 : x0 ∈ U0 := hx0_spec.1
    have hslope_x0 :
        specializedPhi θ (levelPred + 1) (gateAssignmentOfTail x0.2 tail) x0.1 ≠ 0 :=
      hx0_spec.2
    exact
      cascadeLevelBranchChoice_nonzero_of_canonicalFrecGateAlongSignRegion_point_from_basis
        signRegion hAA A U0 hU0 hU0_rel x0 hx0 (basis_at x0 hx0)
        (regular_at x0 hx0) (levelPred + 1) tail
        (Nat.succ_le_succ (Nat.zero_le levelPred)) hlevel_lt prior_saturates
        provider hslope_x0

/-- Conditional-provider variant of
`cascadeLevelBranchChoice_of_canonicalFrecGateAlongSignRegion_dichotomy_from_basis`.
The zero-branch provider is requested only in the all-zero slope case. -/
noncomputable def
    cascadeLevelBranchChoice_of_canonicalFrecGateAlongSignRegion_dichotomy_from_basis_conditionalZeroBranchProvider
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (A : Matrix (Fin d) (Fin d) ℝ)
    (U0 : Set (ProbePair d × ℝ))
    (hU0 : U0 ⊆ signRegion.U)
    (U0_nonempty : U0.Nonempty)
    (U0_connected : IsPreconnected U0)
    (hU0_rel :
      ∃ W0 : Set (ProbePair d × ℝ), IsOpen W0 ∧
        U0 = W0 ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1})
    (basis_at :
      ∀ x ∈ U0, RegularQuadricLocalConnectedRelativeOpenSliceBasisData A x.1 x.2)
    (regular_at : ∀ x ∈ U0, firstLayerRegular A x.1)
    {levelPred : Nat} (tail : Nat -> ℝ)
    (hlevel_lt : levelPred + 1 < L + 1)
    (prior_saturates :
      ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n -> n < levelPred + 1 ->
        EventuallyExpClose
          (fun τ => canonicalFrecGateAlongSignRegion r signRegion θ n x τ)
          (tail (n - 1)))
    (zero_provider :
      (∀ x ∈ U0,
        specializedPhi θ (levelPred + 1) (gateAssignmentOfTail x.2 tail) x.1 = 0) ->
      CascadeCurveRigidityProvider θ A (levelPred + 1) tail)
    (dimension_pos : 0 < d)
    (head_det_ne_zero : A.det ≠ 0)
    (head_sym_ne_zero : symPart A ≠ 0)
    (head_value_ne_zero : (paramStream θ 0).1 ≠ 0) :
    CascadeLevelBranchChoice (Real.log (r : ℝ)) θ A U0
      (canonicalFrecGateAlongSignRegion r signRegion θ) (levelPred + 1) tail := by
  classical
  by_cases hzero :
      ∀ x ∈ U0,
        specializedPhi θ (levelPred + 1) (gateAssignmentOfTail x.2 tail) x.1 = 0
  · exact
      cascadeLevelBranchChoice_zeroAlpha_of_canonicalFrecGateAlongSignRegion_conditionalZeroBranchProvider
        signRegion hAA A U0 hU0 U0_nonempty U0_connected tail hlevel_lt
        prior_saturates zero_provider hzero dimension_pos head_det_ne_zero
        head_sym_ne_zero head_value_ne_zero
  · have hex :
        ∃ x0, x0 ∈ U0 ∧
          specializedPhi θ (levelPred + 1) (gateAssignmentOfTail x0.2 tail) x0.1 ≠ 0 := by
      by_contra hnone
      apply hzero
      intro x hx
      by_contra hne
      exact hnone ⟨x, hx, hne⟩
    let x0 : ProbePair d × ℝ := Classical.choose hex
    have hx0_spec :
        x0 ∈ U0 ∧
          specializedPhi θ (levelPred + 1) (gateAssignmentOfTail x0.2 tail) x0.1 ≠ 0 := by
      simpa [x0] using Classical.choose_spec hex
    have hx0 : x0 ∈ U0 := hx0_spec.1
    have hslope_x0 :
        specializedPhi θ (levelPred + 1) (gateAssignmentOfTail x0.2 tail) x0.1 ≠ 0 :=
      hx0_spec.2
    exact
      cascadeLevelBranchChoice_nonzero_of_canonicalFrecGateAlongSignRegion_point_from_basis_noZeroBranchProvider
        signRegion hAA A U0 hU0 hU0_rel x0 hx0 (basis_at x0 hx0)
        (regular_at x0 hx0) (levelPred + 1) tail
        (Nat.succ_le_succ (Nat.zero_le levelPred)) hlevel_lt prior_saturates
        hslope_x0

/-- A finite cascade state inherits relative openness in the first-layer slab from the
ambient sign-region, provided the matrix is the sign-region matrix. -/
theorem cascadeInductionState_relatively_open_in_slab_of_signRegion
    {L d : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    {A : Matrix (Fin d) (Fin d) ℝ} {b : ℝ}
    (signRegion : SignRegionData (L := L) (d := d) θ' O A b)
    {θ : Params L d} {unprimed : GateAlongBase d} {level : Nat}
    (Slevel : CascadeInductionState b θ A signRegion.U unprimed level) :
    ∃ W0 : Set (ProbePair d × ℝ), IsOpen W0 ∧
      Slevel.U = W0 ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1} := by
  rcases Slevel.relatively_open_in_sign_region with ⟨Wc, hWc, hSlevel⟩
  rcases signRegion.relatively_open with ⟨Ws, hWs, hSign⟩
  refine ⟨Wc ∩ Ws, IsOpen.inter hWc hWs, ?_⟩
  ext x
  constructor
  · intro hx
    have hx_region : x ∈ Wc ∩ signRegion.U := by
      rw [← hSlevel]
      exact hx
    have hx_slab : x ∈ Ws ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1} := by
      rw [← hSign]
      exact hx_region.2
    exact ⟨⟨hx_region.1, hx_slab.1⟩, hx_slab.2⟩
  · intro hx
    have hx_sign : x ∈ signRegion.U := by
      rw [hSign]
      exact ⟨hx.1.2, hx.2⟩
    rw [hSlevel]
    exact ⟨hx.1.1, hx_sign⟩

/-- A finite cascade state inherits first-layer regularity from its ambient
sign-region. -/
theorem cascadeInductionState_regular_at_of_signRegion
    {L d : Nat} {θ' : Params L d} {O : Set (ProbePair d)}
    {A : Matrix (Fin d) (Fin d) ℝ} {b : ℝ}
    (signRegion : SignRegionData (L := L) (d := d) θ' O A b)
    {θ : Params L d} {unprimed : GateAlongBase d} {level : Nat}
    (Slevel : CascadeInductionState b θ A signRegion.U unprimed level) :
    ∀ x ∈ Slevel.U, firstLayerRegular A x.1 := by
  intro x hx
  exact signRegion.point_regular x (Slevel.subset_sign_region hx)

/-- A finite cascade state gets the relative-open slice basis from the solved-coordinate
chart at each point. -/
noncomputable def cascadeInductionState_basis_at_of_solvedCoordChart
    {L d : Nat} {θ θ' : Params L d} {O : Set (ProbePair d)}
    {A : Matrix (Fin d) (Fin d) ℝ} {b : ℝ}
    (signRegion : SignRegionData (L := L) (d := d) θ' O A b)
    {unprimed : GateAlongBase d} {level : Nat}
    (Slevel : CascadeInductionState b θ A signRegion.U unprimed level) :
    ∀ x ∈ Slevel.U,
      RegularQuadricLocalConnectedRelativeOpenSliceBasisData A x.1 x.2 := by
  intro x _hx
  exact
    regularQuadricLocalConnectedRelativeOpenSliceBasisData_of_solvedCoordChart
      A x.1 x.2

/-- Step2-facing finite trichotomy provider assembled from explicit per-state
zero/nonzero branch obligations.  The global finite induction is provided by the
canonical cascade constructor; each state is discharged by the existing one-step
dichotomy wrapper after rewriting `level` as `(level - 1) + 1`. -/
noncomputable def
    cascadeTrichotomyInductionProviderData_of_dichotomyChoices_from_basis
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion : SignRegionData (L := L + 1) (d := d) θ' O
      (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (A : Matrix (Fin d) (Fin d) ℝ)
    (tail0 : Nat -> ℝ)
    (state_rel_slab :
      ∀ {level : Nat}, 1 ≤ level -> level < L + 1 ->
        (Slevel : CascadeInductionState (Real.log (r : ℝ)) θ A signRegion.U
          (canonicalFrecGateAlongSignRegion r signRegion θ) level) ->
          ∃ W0 : Set (ProbePair d × ℝ), IsOpen W0 ∧
            Slevel.U = W0 ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1})
    (state_basis_at :
      ∀ {level : Nat}, 1 ≤ level -> level < L + 1 ->
        (Slevel : CascadeInductionState (Real.log (r : ℝ)) θ A signRegion.U
          (canonicalFrecGateAlongSignRegion r signRegion θ) level) ->
          ∀ x ∈ Slevel.U,
            RegularQuadricLocalConnectedRelativeOpenSliceBasisData A x.1 x.2)
    (state_regular_at :
      ∀ {level : Nat}, 1 ≤ level -> level < L + 1 ->
        (Slevel : CascadeInductionState (Real.log (r : ℝ)) θ A signRegion.U
          (canonicalFrecGateAlongSignRegion r signRegion θ) level) ->
          ∀ x ∈ Slevel.U, firstLayerRegular A x.1)
    (state_curve_provider :
      ∀ {level : Nat}, 1 ≤ level -> level < L + 1 ->
        (Slevel : CascadeInductionState (Real.log (r : ℝ)) θ A signRegion.U
          (canonicalFrecGateAlongSignRegion r signRegion θ) level) ->
          CascadeCurveRigidityProvider θ A level Slevel.tail)
    (dimension_pos : 0 < d)
    (head_det_ne_zero : A.det ≠ 0)
    (head_sym_ne_zero : symPart A ≠ 0)
    (head_value_ne_zero : (paramStream θ 0).1 ≠ 0) :
    CascadeTrichotomyInductionProviderData
      (L := L + 1) (d := d) (Real.log (r : ℝ)) θ A signRegion.U
      (canonicalFrecGateAlongSignRegion r signRegion θ)
      (canonicalFrecGateAlongSignRegion r signRegion θ') :=
  cascadeTrichotomyInductionProviderData_of_canonicalChoices
    signRegion A tail0 (by
      intro level hlevel_pos hlevel_lt Slevel
      have hlevel_eq : level - 1 + 1 = level :=
        Nat.sub_add_cancel hlevel_pos
      simpa [hlevel_eq] using
        (cascadeLevelBranchChoice_of_canonicalFrecGateAlongSignRegion_dichotomy_from_basis
          signRegion hAA A Slevel.U Slevel.subset_sign_region Slevel.nonempty
          Slevel.connected
          (state_rel_slab hlevel_pos hlevel_lt Slevel)
          (state_basis_at hlevel_pos hlevel_lt Slevel)
          (state_regular_at hlevel_pos hlevel_lt Slevel)
          (levelPred := level - 1) Slevel.tail
          (by simpa [hlevel_eq] using hlevel_lt)
          (by
            intro x hx n hn_pos hn_lt
            exact
              Slevel.prior_saturates x hx n hn_pos
                (by simpa [hlevel_eq] using hn_lt))
          (by
            simpa [hlevel_eq] using
              state_curve_provider hlevel_pos hlevel_lt Slevel)
          dimension_pos head_det_ne_zero head_sym_ne_zero head_value_ne_zero))

/-- Conditional-provider variant of
`cascadeTrichotomyInductionProviderData_of_dichotomyChoices_from_basis`.  The
per-state curve-rigidity provider is only requested under zero slope on that state's
current component. -/
noncomputable def
    cascadeTrichotomyInductionProviderData_of_dichotomyChoices_from_basis_conditionalZeroBranchProvider
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion : SignRegionData (L := L + 1) (d := d) θ' O
      (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (A : Matrix (Fin d) (Fin d) ℝ)
    (tail0 : Nat -> ℝ)
    (state_rel_slab :
      ∀ {level : Nat}, 1 ≤ level -> level < L + 1 ->
        (Slevel : CascadeInductionState (Real.log (r : ℝ)) θ A signRegion.U
          (canonicalFrecGateAlongSignRegion r signRegion θ) level) ->
          ∃ W0 : Set (ProbePair d × ℝ), IsOpen W0 ∧
            Slevel.U = W0 ∩ {x | firstLayerQuadric A x.1 ∧ 0 < x.2 ∧ x.2 < 1})
    (state_basis_at :
      ∀ {level : Nat}, 1 ≤ level -> level < L + 1 ->
        (Slevel : CascadeInductionState (Real.log (r : ℝ)) θ A signRegion.U
          (canonicalFrecGateAlongSignRegion r signRegion θ) level) ->
          ∀ x ∈ Slevel.U,
            RegularQuadricLocalConnectedRelativeOpenSliceBasisData A x.1 x.2)
    (state_regular_at :
      ∀ {level : Nat}, 1 ≤ level -> level < L + 1 ->
        (Slevel : CascadeInductionState (Real.log (r : ℝ)) θ A signRegion.U
          (canonicalFrecGateAlongSignRegion r signRegion θ) level) ->
          ∀ x ∈ Slevel.U, firstLayerRegular A x.1)
    (state_curve_provider :
      ∀ {level : Nat}, 1 ≤ level -> level < L + 1 ->
        (Slevel : CascadeInductionState (Real.log (r : ℝ)) θ A signRegion.U
          (canonicalFrecGateAlongSignRegion r signRegion θ) level) ->
        (∀ x ∈ Slevel.U,
          specializedPhi θ level (gateAssignmentOfTail x.2 Slevel.tail) x.1 = 0) ->
        CascadeCurveRigidityProvider θ A level Slevel.tail)
    (dimension_pos : 0 < d)
    (head_det_ne_zero : A.det ≠ 0)
    (head_sym_ne_zero : symPart A ≠ 0)
    (head_value_ne_zero : (paramStream θ 0).1 ≠ 0) :
    CascadeTrichotomyInductionProviderData
      (L := L + 1) (d := d) (Real.log (r : ℝ)) θ A signRegion.U
      (canonicalFrecGateAlongSignRegion r signRegion θ)
      (canonicalFrecGateAlongSignRegion r signRegion θ') :=
  cascadeTrichotomyInductionProviderData_of_canonicalChoices
    signRegion A tail0 (by
      intro level hlevel_pos hlevel_lt Slevel
      have hlevel_eq : level - 1 + 1 = level :=
        Nat.sub_add_cancel hlevel_pos
      simpa [hlevel_eq] using
        (cascadeLevelBranchChoice_of_canonicalFrecGateAlongSignRegion_dichotomy_from_basis_conditionalZeroBranchProvider
          signRegion hAA A Slevel.U Slevel.subset_sign_region Slevel.nonempty
          Slevel.connected
          (state_rel_slab hlevel_pos hlevel_lt Slevel)
          (state_basis_at hlevel_pos hlevel_lt Slevel)
          (state_regular_at hlevel_pos hlevel_lt Slevel)
          (levelPred := level - 1) Slevel.tail
          (by simpa [hlevel_eq] using hlevel_lt)
          (by
            intro x hx n hn_pos hn_lt
            exact
              Slevel.prior_saturates x hx n hn_pos
                (by simpa [hlevel_eq] using hn_lt))
          (by
            intro hzero
            have hzero_level :
                ∀ x ∈ Slevel.U,
                  specializedPhi θ level (gateAssignmentOfTail x.2 Slevel.tail) x.1 = 0 := by
              intro x hx
              simpa [hlevel_eq] using hzero x hx
            have hprovider :=
              state_curve_provider hlevel_pos hlevel_lt Slevel hzero_level
            simpa [hlevel_eq] using hprovider)
          dimension_pos head_det_ne_zero head_sym_ne_zero head_value_ne_zero))

/-- Step2-facing finite trichotomy provider using solved-coordinate charts for every
state-local basis obligation.  The only remaining finite-provider input is the curve
rigidity provider for each state. -/
noncomputable def
  cascadeTrichotomyInductionProviderData_of_dichotomyChoices_from_solvedCoordChart
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion : SignRegionData (L := L + 1) (d := d) θ' O
      (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (tail0 : Nat -> ℝ)
    (state_curve_provider :
      ∀ {level : Nat}, 1 ≤ level -> level < L + 1 ->
        (Slevel : CascadeInductionState (Real.log (r : ℝ)) θ
          (Params.headAttention θ') signRegion.U
          (canonicalFrecGateAlongSignRegion r signRegion θ) level) ->
        CascadeCurveRigidityProvider θ (Params.headAttention θ') level Slevel.tail)
    (dimension_pos : 0 < d)
    (head_det_ne_zero : (Params.headAttention θ').det ≠ 0)
    (head_sym_ne_zero : symPart (Params.headAttention θ') ≠ 0)
    (head_value_ne_zero : (paramStream θ 0).1 ≠ 0) :
    CascadeTrichotomyInductionProviderData
      (L := L + 1) (d := d) (Real.log (r : ℝ)) θ (Params.headAttention θ') signRegion.U
      (canonicalFrecGateAlongSignRegion r signRegion θ)
      (canonicalFrecGateAlongSignRegion r signRegion θ') :=
  cascadeTrichotomyInductionProviderData_of_dichotomyChoices_from_basis
    (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') (O := O)
    signRegion hAA (Params.headAttention θ') tail0
    (fun _hpos _hlt Slevel =>
      cascadeInductionState_relatively_open_in_slab_of_signRegion
        signRegion Slevel)
    (fun _hpos _hlt Slevel =>
      cascadeInductionState_basis_at_of_solvedCoordChart
        signRegion Slevel)
    (fun _hpos _hlt Slevel =>
      cascadeInductionState_regular_at_of_signRegion
        signRegion Slevel)
    state_curve_provider
    dimension_pos head_det_ne_zero head_sym_ne_zero head_value_ne_zero

/-- Conditional-provider variant of
`cascadeTrichotomyInductionProviderData_of_dichotomyChoices_from_solvedCoordChart`. -/
noncomputable def
  cascadeTrichotomyInductionProviderData_of_dichotomyChoices_from_solvedCoordChart_conditionalZeroBranchProvider
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion : SignRegionData (L := L + 1) (d := d) θ' O
      (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (tail0 : Nat -> ℝ)
    (state_curve_provider :
      ∀ {level : Nat}, 1 ≤ level -> level < L + 1 ->
        (Slevel : CascadeInductionState (Real.log (r : ℝ)) θ
          (Params.headAttention θ') signRegion.U
          (canonicalFrecGateAlongSignRegion r signRegion θ) level) ->
        (∀ x ∈ Slevel.U,
          specializedPhi θ level (gateAssignmentOfTail x.2 Slevel.tail) x.1 = 0) ->
        CascadeCurveRigidityProvider θ (Params.headAttention θ') level Slevel.tail)
    (dimension_pos : 0 < d)
    (head_det_ne_zero : (Params.headAttention θ').det ≠ 0)
    (head_sym_ne_zero : symPart (Params.headAttention θ') ≠ 0)
    (head_value_ne_zero : (paramStream θ 0).1 ≠ 0) :
    CascadeTrichotomyInductionProviderData
      (L := L + 1) (d := d) (Real.log (r : ℝ)) θ (Params.headAttention θ') signRegion.U
      (canonicalFrecGateAlongSignRegion r signRegion θ)
      (canonicalFrecGateAlongSignRegion r signRegion θ') :=
  cascadeTrichotomyInductionProviderData_of_dichotomyChoices_from_basis_conditionalZeroBranchProvider
    (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') (O := O)
    signRegion hAA (Params.headAttention θ') tail0
    (fun _hpos _hlt Slevel =>
      cascadeInductionState_relatively_open_in_slab_of_signRegion
        signRegion Slevel)
    (fun _hpos _hlt Slevel =>
      cascadeInductionState_basis_at_of_solvedCoordChart
        signRegion Slevel)
    (fun _hpos _hlt Slevel =>
      cascadeInductionState_regular_at_of_signRegion
        signRegion Slevel)
    state_curve_provider
    dimension_pos head_det_ne_zero head_sym_ne_zero head_value_ne_zero

/-- Build the zero-branch curve-rigidity provider for one cascade state from a
coefficient-separating product patch selected inside that state.  The all-zero slope
hypothesis is only used after the product patch has been chosen. -/
noncomputable def cascadeCurveRigidityProvider_of_state_productPatch_zeroBranch
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion : SignRegionData (L := L + 1) (d := d) θ' O
      (Params.headAttention θ') (Real.log (r : ℝ)))
    {level : Nat}
    (hlevel_pos : 1 ≤ level)
    (Slevel : CascadeInductionState (Real.log (r : ℝ)) θ
      (Params.headAttention θ') signRegion.U
      (canonicalFrecGateAlongSignRegion r signRegion θ) level)
    (head_sym_ne_zero : symPart (Params.headAttention θ') ≠ 0)
    (hzero_level :
      ∀ x ∈ Slevel.U,
        specializedPhi θ level (gateAssignmentOfTail x.2 Slevel.tail) x.1 = 0) :
    CascadeCurveRigidityProvider θ (Params.headAttention θ') level Slevel.tail := by
  classical
  have hlevel_eq : level - 1 + 1 = level :=
    Nat.sub_add_cancel hlevel_pos
  let patch : CoefficientSeparatingProductPatch (Params.headAttention θ') Slevel.U :=
    signRegion.product_neighborhood Slevel.U Slevel.subset_sign_region
      Slevel.nonempty Slevel.relatively_open_in_sign_region
  have hA : Params.headAttention θ' ≠ 0 := by
    intro hA
    exact head_sym_ne_zero (by simp [hA, symPart])
  have hzero_patch :
      ∀ p : ProbePair d, p ∈ patch.Uq → ∀ t : ℝ, t ∈ patch.J →
        specializedPhi θ (level - 1 + 1)
          (gateAssignmentOfTail t Slevel.tail) p = 0 := by
    intro p hp t ht
    have hx : (p, t) ∈ Slevel.U := patch.product_subset ⟨hp, ht⟩
    have hzero := hzero_level (p, t) hx
    simpa [hlevel_eq] using hzero
  have hprovider :
      CascadeCurveRigidityProvider θ (Params.headAttention θ')
        (level - 1 + 1) Slevel.tail :=
    cascadeCurveRigidityProvider_of_product_patch_zero_branch_level_succ
      (θ := θ) (A := Params.headAttention θ') (levelPred := level - 1)
      (tail := Slevel.tail) (U0 := Slevel.U)
      patch patch.quadratic_coefficient_separation hA hzero_patch
  simpa [hlevel_eq] using hprovider

/-- Step2-facing finite trichotomy provider whose zero branch is built on demand from
the product patch available in the current cascade state. -/
noncomputable def
  cascadeTrichotomyInductionProviderData_of_dichotomyChoices_from_solvedCoordChart_productPatchZeroBranch
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion : SignRegionData (L := L + 1) (d := d) θ' O
      (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (tail0 : Nat -> ℝ)
    (dimension_pos : 0 < d)
    (head_det_ne_zero : (Params.headAttention θ').det ≠ 0)
    (head_sym_ne_zero : symPart (Params.headAttention θ') ≠ 0)
    (head_value_ne_zero : (paramStream θ 0).1 ≠ 0) :
    CascadeTrichotomyInductionProviderData
      (L := L + 1) (d := d) (Real.log (r : ℝ)) θ (Params.headAttention θ') signRegion.U
      (canonicalFrecGateAlongSignRegion r signRegion θ)
      (canonicalFrecGateAlongSignRegion r signRegion θ') :=
  cascadeTrichotomyInductionProviderData_of_dichotomyChoices_from_solvedCoordChart_conditionalZeroBranchProvider
    (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') (O := O)
    signRegion hAA tail0
    (fun hlevel_pos _hlevel_lt Slevel hzero_level =>
      cascadeCurveRigidityProvider_of_state_productPatch_zeroBranch
        signRegion hlevel_pos Slevel head_sym_ne_zero hzero_level)
    dimension_pos head_det_ne_zero head_sym_ne_zero head_value_ne_zero

/-- Smaller pure-geometry primitive for the local region step.

For every open neighborhood of the anchor, it constructs a connected relatively-open
regular quadric chart inside that neighborhood, with coefficient-separating product
patches on all nonempty relatively-open subregions.  This removes the IDL open-set and
tail-positivity bookkeeping from the hard geometry input. -/
structure RegularQuadricLocalConnectedCoefficientSeparatingOpenNeighborhoodChartData {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (point : ProbePair d) (t : ℝ) : Type where
  chart :
    ∀ V : Set (ProbePair d × ℝ), IsOpen V -> (point, t) ∈ V ->
      firstLayerQuadric A point -> firstLayerRegular A point ->
      0 < t -> t < 1 ->
      RegularQuadricLocalConnectedCoefficientSeparatingChartData A V point t

namespace RegularQuadricLocalConnectedCoefficientSeparatingOpenNeighborhoodChartData

variable {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ}
variable {point : ProbePair d} {t : ℝ}

/-- Build the full open-neighborhood primitive from a connected relative-open chart
core and a coefficient-separation theorem for relatively open quadric probe slices. -/
noncomputable def of_core
    (core : RegularQuadricLocalConnectedOpenNeighborhoodChartCoreData A point t)
    (sep : RegularQuadricProbeSliceCoefficientSeparationData A)
    (hd : 2 ≤ d) (hdet : A.det ≠ 0) :
    RegularQuadricLocalConnectedCoefficientSeparatingOpenNeighborhoodChartData
      A point t where
  chart := by
    intro V hV_open hpointV hquad hregular ht_pos ht_lt
    let G := core.chart V hV_open hpointV hquad hregular ht_pos ht_lt
    exact G.withProbeSliceCoefficientSeparation sep hd hdet

/-- Build the full coefficient-separating open-neighborhood chart from the two reduced
local inputs: local connectedness of the quadric subtype at the anchor and the
no-linear-component theorem on relatively open quadric probe slices. -/
noncomputable def of_reduced
    (quadricBasis :
      RegularQuadricLocalConnectedQuadricSubtypeBasisData A point)
    (noLinear : RegularQuadricProbeSliceNoLinearComponentData A)
    (hd : 2 ≤ d) (hdet : A.det ≠ 0) :
    RegularQuadricLocalConnectedCoefficientSeparatingOpenNeighborhoodChartData
      A point t :=
  of_core
    ((RegularQuadricLocalConnectedProbeSliceBasisData.of_quadricSubtypeBasis
        (A := A) (point := point) quadricBasis).toRelativeOpenSliceBasisData
      (t := t)).toOpenNeighborhoodChartCoreData
    (RegularQuadricProbeSliceCoefficientSeparationData.of_noLinearComponent
      noLinear)
    hd hdet

end RegularQuadricLocalConnectedCoefficientSeparatingOpenNeighborhoodChartData

namespace RegularQuadricReducedChartCoefficientData

variable {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ}
variable {point : ProbePair d}

end RegularQuadricReducedChartCoefficientData

/-- Local geometric primitive still missing from the TeX Lemma `region` formalization.

It is intentionally anchored at the concrete point extracted from `IDLData`: the
constructor below derives nonemptiness from `anchor_mem` and derives the quadric
condition from `relatively_open`.  The remaining hard content is exactly the local
connected regular sign component, together with coefficient-separating product patches
inside every relatively open nonempty subcomponent. -/
structure TexRegionLocalQuadricProductPatchData {L d : Nat}
    (θ' : Params (L + 1) d) (O : Set (ProbePair d))
    (anchor : TexRegionAnchorPointData θ' O) : Type where
  U : Set (ProbePair d × ℝ)
  anchor_mem : (anchor.point, anchor.t) ∈ U
  relatively_open :
    ∃ W : Set (ProbePair d × ℝ),
      IsOpen W ∧
        U = W ∩
          {x | firstLayerQuadric (Params.headAttention θ') x.1 ∧
            0 < x.2 ∧ x.2 < 1}
  connected : IsPreconnected U
  point_regular : ∀ x ∈ U, firstLayerRegular (Params.headAttention θ') x.1
  point_mem_base : ∀ x ∈ U, x.1 ∈ O
  primed_positive :
    ∀ x ∈ U, ∀ n : Nat, 1 ≤ n -> n < L + 1 ->
      0 < (specializedPhi θ' n (gateAssignmentOneTail x.2) x.1).re
  product_neighborhood :
    ∀ U0 : Set (ProbePair d × ℝ), U0 ⊆ U -> U0.Nonempty ->
      (∃ W0 : Set (ProbePair d × ℝ), IsOpen W0 ∧ U0 = W0 ∩ U) ->
      CoefficientSeparatingProductPatch (Params.headAttention θ') U0

namespace TexRegionLocalQuadricProductPatchData

variable {L d : Nat} {θ' : Params (L + 1) d} {O : Set (ProbePair d)}
variable {anchor : TexRegionAnchorPointData θ' O}

/-- The relative-open representation forces every point of the local region onto the
first-layer quadric. -/
theorem point_on_quadric
    (G : TexRegionLocalQuadricProductPatchData θ' O anchor)
    {x : ProbePair d × ℝ} (hx : x ∈ G.U) :
    firstLayerQuadric (Params.headAttention θ') x.1 := by
  rcases G.relatively_open with ⟨W, _hW, hU⟩
  have hx' :
      x ∈ W ∩
        {x | firstLayerQuadric (Params.headAttention θ') x.1 ∧
          0 < x.2 ∧ x.2 < 1} := by
    simpa [hU] using hx
  exact hx'.2.1

/-- Compile the pure local quadric chart into the parameter-aware local region data. -/
noncomputable def of_regularQuadricLocalConnectedCoefficientSeparatingChart
    (G :
      RegularQuadricLocalConnectedCoefficientSeparatingChartData
        (Params.headAttention θ') (texRegionSafeSet θ' O) anchor.point anchor.t) :
    TexRegionLocalQuadricProductPatchData θ' O anchor where
  U := G.U
  anchor_mem := G.anchor_mem
  relatively_open := G.relatively_open
  connected := G.connected
  point_regular := by
    intro x hx
    exact (G.subset_safe hx).1
  point_mem_base := by
    intro x hx
    exact (G.subset_safe hx).2.1
  primed_positive := by
    intro x hx n hn_pos hn_lt
    exact (G.subset_safe hx).2.2 n hn_pos hn_lt
  product_neighborhood := G.product_neighborhood

/-- Compile the local anchored primitive to the strengthened TeX-region construction
interface consumed by saturation and matching. -/
noncomputable def toConstructionData
    (G : TexRegionLocalQuadricProductPatchData θ' O anchor) (b : ℝ) :
    TexRegionConstructionData (L := L + 1) (d := d) θ' O
      (Params.headAttention θ') b where
  U := G.U
  nonempty := ⟨(anchor.point, anchor.t), G.anchor_mem⟩
  relatively_open := G.relatively_open
  connected := G.connected
  point_on_quadric := fun _ hx => G.point_on_quadric hx
  point_regular := G.point_regular
  point_mem_base := G.point_mem_base
  primed_positive := G.primed_positive
  product_neighborhood := G.product_neighborhood

end TexRegionLocalQuadricProductPatchData

/-- Exact remaining local-geometry obligation for deriving the strengthened TeX
Lemma `region` output from `IDLData` in positive tail depth. -/
abbrev TexRegionConstructionDataOfIDLDataObligation
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ') : Type :=
  RegularQuadricLocalConnectedCoefficientSeparatingChartData
    (Params.headAttention θ') (texRegionSafeSet θ' D.O)
    (texRegionAnchorPointData_of_IDLData hL D).point
    (texRegionAnchorPointData_of_IDLData hL D).t

/-- Build the exact IDL local chart obligation from the smaller pure open-neighborhood
chart primitive.  The only non-geometric inputs discharged here are openness of `D.O`
and continuity of the finitely many tail-positivity predicates defining
`texRegionSafeSet`. -/
noncomputable def texRegionConstructionDataOfIDLDataObligation_of_openNeighborhoodChart
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ')
    (hcont :
      ∀ n : Nat, 1 ≤ n -> n < L + 1 ->
        Continuous fun x : ProbePair d × ℝ =>
          (specializedPhi θ' n (gateAssignmentOneTail x.2) x.1).re)
    (localChart :
      RegularQuadricLocalConnectedCoefficientSeparatingOpenNeighborhoodChartData
        (Params.headAttention θ')
        (texRegionAnchorPointData_of_IDLData hL D).point
        (texRegionAnchorPointData_of_IDLData hL D).t) :
    TexRegionConstructionDataOfIDLDataObligation hL D := by
  let anchor := texRegionAnchorPointData_of_IDLData hL D
  exact
    localChart.chart (texRegionSafeSet θ' D.O)
      (isOpen_texRegionSafeSet_of_continuous D.O_open hcont)
      (texRegionAnchorPoint_mem_safeSet anchor)
      anchor.point_on_quadric anchor.point_regular anchor.t_pos anchor.t_lt_one

/-- IDL-region local obligation from the current reduced local inputs: local
connectedness of the quadric subtype at the IDL anchor and the corrected
no-linear-component coefficient theorem for relatively open quadric probe slices. -/
noncomputable def texRegionConstructionDataOfIDLDataObligation_of_reduced
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (hd : 2 ≤ d)
    (hdet : (Params.headAttention θ').det ≠ 0)
    (D : IDLData (L + 1) d r θ θ')
    (quadricBasis :
      RegularQuadricLocalConnectedQuadricSubtypeBasisData
        (Params.headAttention θ')
        (texRegionAnchorPointData_of_IDLData hL D).point)
    (noLinear :
      RegularQuadricProbeSliceNoLinearComponentData
        (Params.headAttention θ')) :
    TexRegionConstructionDataOfIDLDataObligation hL D :=
  texRegionConstructionDataOfIDLDataObligation_of_openNeighborhoodChart
    hL D (fun n _hn_pos _hn_lt => continuous_specializedPhi_oneTail_re θ' n)
    (RegularQuadricLocalConnectedCoefficientSeparatingOpenNeighborhoodChartData.of_reduced
      (A := Params.headAttention θ')
      (point := (texRegionAnchorPointData_of_IDLData hL D).point)
      (t := (texRegionAnchorPointData_of_IDLData hL D).t)
      quadricBasis noLinear hd hdet)

/-- The anchored reduced chart/coefficient provider package for an IDL region
obligation. -/
abbrev TexRegionReducedChartCoefficientDataOfIDLData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ') : Type :=
  RegularQuadricReducedChartCoefficientData
    (Params.headAttention θ')
    (texRegionAnchorPointData_of_IDLData hL D).point

/-- The remaining anchored reduced chart provider after determinant genericity supplies
the no-linear-component theorem: only point-local connectedness of the quadric subtype
is external. -/
abbrev TexRegionReducedLocalConnectedChartDataOfIDLData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ') : Type :=
  PLift
    (RegularQuadricLocalConnectedQuadricSubtypeNeighborhoodData
      (Params.headAttention θ')
      (texRegionAnchorPointData_of_IDLData hL D).point)

/-- IDL-facing local-connected chart provider, obtained from the solved-coordinate
local chart around regular quadric points. -/
noncomputable def texRegionReducedLocalConnectedChartDataOfIDLData_of_solvedCoordChart
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (D : IDLData (L + 1) d r θ θ') :
    TexRegionReducedLocalConnectedChartDataOfIDLData hL D :=
  ⟨regularQuadricLocalConnectedQuadricSubtypeNeighborhoodData_of_solvedCoordChart⟩

/-- Compile the local-connected-only chart provider to the older bundled reduced chart
package, deriving the no-linear-component field from determinant genericity. -/
noncomputable def texRegionReducedChartCoefficientDataOfIDLData_of_localConnectedChart
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (hd : 2 ≤ d)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (D : IDLData (L + 1) d r θ θ')
    (provider : TexRegionReducedLocalConnectedChartDataOfIDLData hL D) :
    TexRegionReducedChartCoefficientDataOfIDLData hL D := by
  classical
  have hfirst : firstAttention θ' = Params.headAttention θ' := by
    simpa [Params.headAttention, Params.headLayer] using
      firstAttention_eq_of_pos θ' (Nat.succ_pos L)
  have hdet : (Params.headAttention θ').det ≠ 0 := by
    simpa [hfirst] using hstep.g1_det_firstAttention
  exact
    { locally_connected_neighborhood := provider.down
      no_linear_component :=
        regularQuadricProbeSliceNoLinearComponentData_of_det_ne_zero_of_solvedCoordChart
          (A := Params.headAttention θ') (hd := hd) (hdet := hdet)
          (regularQuadricProbeSliceSolvedChartNoLinearData_of_det_ne_zero
            (Params.headAttention θ') hd hdet) }

/-- IDL-region local obligation from the provider-facing reduced package: point-local
quadric-subtype connectedness plus corrected no-linear-component coefficient
separation. -/
noncomputable def texRegionConstructionDataOfIDLDataObligation_of_reducedProvider
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (hd : 2 ≤ d)
    (hdet : (Params.headAttention θ').det ≠ 0)
    (D : IDLData (L + 1) d r θ θ')
    (provider : TexRegionReducedChartCoefficientDataOfIDLData hL D) :
    TexRegionConstructionDataOfIDLDataObligation hL D :=
  texRegionConstructionDataOfIDLDataObligation_of_reduced
    hL hd hdet D provider.quadricSubtypeBasisData provider.noLinearComponentData

/-- IDL-region local obligation from the reduced local-connected-only provider, using
the determinant genericity clause to fill the no-linear-component field automatically. -/
noncomputable def texRegionConstructionDataOfIDLDataObligation_of_localConnectedChartProvider
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hL : 0 < L) (hd : 2 ≤ d)
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (D : IDLData (L + 1) d r θ θ')
    (provider : TexRegionReducedLocalConnectedChartDataOfIDLData hL D) :
    TexRegionConstructionDataOfIDLDataObligation hL D := by
  have hfirst : firstAttention θ' = Params.headAttention θ' := by
    simpa [Params.headAttention, Params.headLayer] using
      firstAttention_eq_of_pos θ' (Nat.succ_pos L)
  have hdet : (Params.headAttention θ').det ≠ 0 := by
    simpa [hfirst] using hstep.g1_det_firstAttention
  exact
    texRegionConstructionDataOfIDLDataObligation_of_reducedProvider
      hL hd hdet D
      (texRegionReducedChartCoefficientDataOfIDLData_of_localConnectedChart
        hL hd hstep D provider)

/-- Positive-tail-depth region constructor from `IDLData`, reduced to the local
connected coefficient-separating quadric product-patch primitive. -/
noncomputable def texRegionConstructionData_of_IDLData_of_localPatch
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) :
    TexRegionConstructionData (L := L + 1) (d := d) θ' D.O
      (Params.headAttention θ') (Real.log (r : ℝ)) := by
  have _ := hr
  have _ := hstep
  have _ := endpoint
  exact
    (TexRegionLocalQuadricProductPatchData.of_regularQuadricLocalConnectedCoefficientSeparatingChart
        (θ' := θ') (O := D.O)
        (anchor := texRegionAnchorPointData_of_IDLData hL D)
        localRegion).toConstructionData (Real.log (r : ℝ))

/-- The remaining analytic/geometric construction in TeX Lemma `region`.

This is the precise local blocker: from the generic step, first-attention endpoint, and
IDL open/path data, construct the regular connected sign region over `D.O`. -/
noncomputable def texRegionConstructionData_of_texGenericStep
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (b : ℝ)
    (region :
      TexRegionConstructionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') b) :
    TexRegionConstructionData (L := L + 1) (d := d) θ' D.O
      (Params.headAttention θ') b := by
  have _ := hstep
  have _ := endpoint
  have _ := D
  have hanchorPoint_if_pos :
      0 < L -> TexRegionAnchorPointData (L := L) (d := d) θ' D.O :=
    fun hL => texRegionAnchorPointData_of_IDLData hL D
  have _ := hanchorPoint_if_pos
  exact region

/-- TeX Lemma `region`, isolated from the IDL wrapper.  The hard construction is now
the explicit `TexRegionConstructionData` input; this definition only adapts it to the
`SignRegionData` interface consumed by downstream saturation code. -/
noncomputable def texRegion_signRegionData
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (b : ℝ)
    (region :
      TexRegionConstructionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') b) :
    SignRegionData (L := L + 1) (d := d) θ' D.O
      (Params.headAttention θ') b := by
  have _ := hstep
  have _ := endpoint
  exact region.toSignRegionData

/-- Coefficient-comparison output of TeX Proposition `matching`, before packaging it as
`MatchingLimitData`.  The matrix `D` is the saturated lower-layer contribution from
Step 1 of the TeX matching proof, and `realSkipBprod (Params.tail θ) L - D` is the
matrix called `K` in Step 6. -/
structure MatchingCoefficientComparisonData {L d : Nat}
    (θ θ' : Params (L + 1) d) where
  D : Matrix (Fin d) (Fin d) ℝ
  skipProduct_eq :
    realSkipBprod (paramStream θ) (L + 1) =
      realSkipBprod (paramStream θ') (L + 1)
  K_maps_headValue :
    (realSkipBprod (paramStream (Params.tail θ)) L - D) * (θ 0).1 = (θ' 0).1
  K_maps_headSkip :
    (realSkipBprod (paramStream (Params.tail θ)) L - D) * skipB (θ 0).1 =
      skipB (θ' 0).1

namespace MatchingCoefficientComparisonData

variable {L d : Nat} {θ θ' : Params (L + 1) d}

end MatchingCoefficientComparisonData

/-- The Step 2 package strong enough for matching.

The constructor-level `TrichotomyData` records saturation of supplied gate functions on a
selected component.  Matching also needs the TeX coefficient comparison tying those gates
back to the actual parameter streams of `θ` and `θ'`; without that link, constant gates
would satisfy the raw trichotomy interface but say nothing about the matrices. -/
structure TexMatchingData {L d : Nat}
    (θ θ' : Params (L + 1) d) (b : ℝ)
    (signU Ustar : Set (ProbePair d × ℝ))
    (unprimed primed : GateAlongBase d) where
  trichotomy : TrichotomyData (L := L + 1) (d := d) b signU Ustar unprimed primed
  coefficientComparison : MatchingCoefficientComparisonData θ θ'

/-- The matrix multiplying the base `w` variable after the unprimed and primed saturated
dial-path limits are subtracted in TeX matching Step 3. -/
noncomputable def texMatchingLimitDifferenceMatrix {L d : Nat}
    (θ θ' : Params (L + 1) d) (Dsat : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  t • (realSkipBprod (paramStream (Params.tail θ)) L * (θ 0).1)
    + Dsat * (skipB (θ 0).1 - t • (θ 0).1)
    - realSkipBprod (paramStream θ') (L + 1)
    + skipB (θ' 0).1 - t • (θ' 0).1

/-- The matrix multiplying the base `v` variable after the saturated dial-path limits are
subtracted in TeX matching Step 3. -/
noncomputable def texMatchingSkipProductDifferenceMatrix {L d : Nat}
    (θ θ' : Params (L + 1) d) :
    Matrix (Fin d) (Fin d) ℝ :=
  realSkipBprod (paramStream θ) (L + 1) -
    realSkipBprod (paramStream θ') (L + 1)

/-- Explicit TeX matching Steps 2--3 analytic obligation at the limit-vector level. -/
structure TexMatchingLimitVectorAgreementData {L d : Nat}
    (θ θ' : Params (L + 1) d)
    {Ustar : Set (ProbePair d × ℝ)}
    (N : TexMatchingProductNeighborhoodData (d := d)
      (Params.headAttention θ') Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma) : Prop where
  matchingLimits_eq :
    ∀ p : ProbePair d, p ∈ N.Uq -> ∀ t : ℝ, t ∈ N.J ->
      texMatchingUnprimedSaturatedLimitVector θ S.D t p =
        texMatchingPrimedTelescopedLimitVector θ' t p

/-- Explicit construction data for TeX Proposition `matching` over a fixed sign region.

This packages the analytic choices and obligations that are not consequences of the
constructor-level trichotomy interface alone. -/
structure TexMatchingConstructionData {L d : Nat}
    (θ θ' : Params (L + 1) d) (b : ℝ)
    (signU : Set (ProbePair d × ℝ)) : Type where
  T : TexTrichotomyConstructionData (L := L + 1) (d := d) b signU
  N : TexMatchingProductNeighborhoodData (d := d)
    (Params.headAttention θ') T.Ustar
  S : TexMatchingSaturatedContributionData θ T.trichotomy.varsigma
  limitAgreement : TexMatchingLimitVectorAgreementData θ θ' N S

/-- TeX matching Steps 2--3: path agreement and saturated limits give the affine
difference identity on the product neighborhood `Uq × J`. -/
structure TexMatchingDialLimitAgreementData {L d : Nat}
    (θ θ' : Params (L + 1) d)
    {Ustar : Set (ProbePair d × ℝ)}
    (N : TexMatchingProductNeighborhoodData (d := d)
      (Params.headAttention θ') Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma) : Prop where
  limit_difference_eq :
    ∀ p : ProbePair d, p ∈ N.Uq -> ∀ t : ℝ, t ∈ N.J ->
      Matrix.mulVec (texMatchingSkipProductDifferenceMatrix θ θ') p.2
        + Matrix.mulVec (texMatchingLimitDifferenceMatrix θ θ' S.D t) p.1 = 0

/-! ### Dial-path bridge for matching limits -/

/-- Explicit bridge from the IDL path class to the TeX matching limit-vector
obligation.

For every selected product-neighborhood point `(p,t)`, this package chooses the actual
dial path, proves that path is available in `D.Paths`, and records the analytic limit
theorem saying that observable agreement along that path identifies the two saturated
limit vectors.  The observable agreement itself is deliberately not a field: it is
derived from `D.path_agreement` in
`texMatchingLimitVectorAgreementData_of_dialPathLimitBridge`. -/
structure TexMatchingDialPathLimitBridgeData {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    {Ustar : Set (ProbePair d × ℝ)}
    (N : TexMatchingProductNeighborhoodData (d := d)
      (Params.headAttention θ') Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma) : Type where
  dial :
    ∀ p : ProbePair d, p ∈ N.Uq -> ∀ t : ℝ, t ∈ N.J ->
      DialPathData (Params.headAttention θ') (Real.log (r : ℝ))
  dial_base :
    ∀ p hp t ht, (dial p hp t ht).base = p
  dial_target :
    ∀ p hp t ht, (dial p hp t ht).t = t
  path_mem :
    ∀ p hp t ht, DialPathData.probe (dial p hp t ht) ∈ D.Paths
  limit_of_observable :
    ∀ p hp t ht, ∀ T0 : ℝ,
      ObservableAgreementOnPath r θ θ'
        (DialPathData.probe (dial p hp t ht)) T0 ->
      texMatchingUnprimedSaturatedLimitVector θ S.D t p =
        texMatchingPrimedTelescopedLimitVector θ' t p

/-- If the current IDL path class is all probe paths, every chosen dial path is
available.  This is the top-level case, where `D.Paths = Set.univ`; recursive uses
should prove the analogous membership by sweep/realization. -/
theorem texMatching_dialPath_mem_of_paths_univ
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (hPaths : D.Paths = Set.univ)
    {A : Matrix (Fin d) (Fin d) ℝ} {b : ℝ}
    (δ : DialPathData A b) :
    DialPathData.probe δ ∈ D.Paths := by
  rw [hPaths]
  exact Set.mem_univ _

/-- A dial path belongs to a swept recursive path class once it is realized by an
available source path from the previous depth.

This is the mechanical half of recursive path membership.  The analytic inverse-sweep
work is exactly the supplied source path, its membership in the full-depth path class,
and the realization witness. -/
theorem texMatching_dialPath_mem_of_realizedTailPathSet
    {L d r : Nat} {θ : Params (L + 1) d}
    {FullPaths : Set (ProbePath d)}
    {A : Matrix (Fin d) (Fin d) ℝ} {b : ℝ}
    (δ : DialPathData A b)
    (source : ProbePath d)
    (hsource : source ∈ FullPaths)
    (hrealized :
      Nonempty
        (RealizationData r (Params.headValue θ) (Params.headAttention θ)
          (DialPathData.probe δ) source)) :
    DialPathData.probe δ ∈ realizedTailPathSet r θ FullPaths :=
  ⟨source, hsource, hrealized⟩

/-- The tail `IDLData` produced by sweep uses the realized-tail path class.  This gives
recursive matching calls the exact path-class equality needed by
`texMatchingLocalPatchRegularQuadricDialMemObligation_of_realizedTailPathSet`. -/
@[simp] theorem texMatching_tail_IDLData_of_texGenericStep_of_IDLData_paths
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (matching : FirstLayerMatchedData θ θ')
    (D : IDLData (L + 1) d r θ θ')
    (S : TexSweepAnalyticData hstep matching D) :
    (tail_IDLData_of_texGenericStep_of_IDLData
      (L := L) (d := d) (r := r) (θ := θ) (θ' := θ')
      hd hr hstep matching D S).Paths =
      realizedTailPathSet r θ D.Paths := by
  simp [tail_IDLData_of_texGenericStep_of_IDLData,
    tail_IDLData_of_texGenericStep_of_realizedTailRegionData,
    tail_IDLData_of_texGenericStep, sweepData_of_texGenericStep]

/-- Observable agreement along the selected dial paths, obtained from the actual
`IDLData.path_agreement` field and explicit path availability. -/
theorem texMatching_observableAgreementOn_dialPath
    {L d r : Nat} {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    {A : Matrix (Fin d) (Fin d) ℝ} {b : ℝ}
    {δ : DialPathData A b}
    (hmem : DialPathData.probe δ ∈ D.Paths) :
    ∃ T0 : ℝ,
      ObservableAgreementOnPath r θ θ' (DialPathData.probe δ) T0 :=
  D.path_agreement (DialPathData.probe δ) hmem

/-- Build the TeX matching limit-vector agreement from observable agreement along the
actual dial paths.  This is the concrete bridge from `D.path_agreement`: the only
remaining analytic input is the stated limit theorem converting agreement on a chosen
dial path into equality of the two saturated endpoint vectors. -/
noncomputable def texMatchingLimitVectorAgreementData_of_dialPathLimitBridge
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    {Ustar : Set (ProbePair d × ℝ)}
    (N : TexMatchingProductNeighborhoodData (d := d)
      (Params.headAttention θ') Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma)
    (B : TexMatchingDialPathLimitBridgeData D N S) :
    TexMatchingLimitVectorAgreementData θ θ' N S := by
  refine ⟨?_⟩
  intro p hp t ht
  rcases texMatching_observableAgreementOn_dialPath D (B.path_mem p hp t ht) with
    ⟨T0, hobs⟩
  exact B.limit_of_observable p hp t ht T0 hobs

/-- TeX matching Step 3, isolated at the level of the two real limit vectors: the
unprimed saturated limit from Step 1 equals the primed telescoped limit from Step 2 on
the product neighborhood chosen in Step 0.  This is where dial-path availability,
observable agreement, convergence of the selected gates, and the primed telescoping
identity are used. -/
theorem texMatching_matchingLimits_eq_of_saturatedContribution
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (S : TexMatchingSaturatedContributionData θ T.trichotomy.varsigma)
    (limitAgreement : TexMatchingLimitVectorAgreementData θ θ' N S) :
    ∀ p : ProbePair d, p ∈ N.Uq -> ∀ t : ℝ, t ∈ N.J ->
      texMatchingUnprimedSaturatedLimitVector θ S.D t p =
        texMatchingPrimedTelescopedLimitVector θ' t p := by
  have _ := hr
  have _ := hstep
  have _ := endpoint
  have _ := D
  have _ := signRegion
  have _ := T
  exact limitAgreement.matchingLimits_eq

/-- Algebraic conversion from the matched Step 1/Step 2 limit vectors to the affine
difference identity displayed as TeX equation `(diff)`. -/
theorem texMatching_limitDifference_eq_of_matchingLimits
    {L d : Nat}
    {θ θ' : Params (L + 1) d}
    {Ustar : Set (ProbePair d × ℝ)}
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma)
    (hlimits :
      ∀ p : ProbePair d, p ∈ N.Uq -> ∀ t : ℝ, t ∈ N.J ->
        texMatchingUnprimedSaturatedLimitVector θ S.D t p =
          texMatchingPrimedTelescopedLimitVector θ' t p) :
    ∀ p : ProbePair d, p ∈ N.Uq -> ∀ t : ℝ, t ∈ N.J ->
      Matrix.mulVec (texMatchingSkipProductDifferenceMatrix θ θ') p.2
        + Matrix.mulVec (texMatchingLimitDifferenceMatrix θ θ' S.D t) p.1 = 0 := by
  intro p hp t ht
  let B := realSkipBprod (paramStream θ) (L + 1)
  let Bp := realSkipBprod (paramStream θ') (L + 1)
  let U :=
    t • (realSkipBprod (paramStream (Params.tail θ)) L * (θ 0).1)
      + S.D * (skipB (θ 0).1 - t • (θ 0).1)
  let P := Bp - skipB (θ' 0).1 + t • (θ' 0).1
  have h :
      Matrix.mulVec B p.2 + Matrix.mulVec U p.1 =
        Matrix.mulVec Bp p.2 + Matrix.mulVec P p.1 := by
    simpa [texMatchingUnprimedSaturatedLimitVector,
      texMatchingPrimedTelescopedLimitVector, B, Bp, U, P] using hlimits p hp t ht
  have hskip :
      texMatchingSkipProductDifferenceMatrix θ θ' = B - Bp := rfl
  have hlimit :
      texMatchingLimitDifferenceMatrix θ θ' S.D t = U - P := by
    change U - Bp + skipB (θ' 0).1 - t • (θ' 0).1 =
      U - (Bp - skipB (θ' 0).1 + t • (θ' 0).1)
    abel
  rw [hskip, hlimit, Matrix.sub_mulVec, Matrix.sub_mulVec]
  calc
    (Matrix.mulVec B p.2 - Matrix.mulVec Bp p.2) +
        (Matrix.mulVec U p.1 - Matrix.mulVec P p.1)
        = (Matrix.mulVec B p.2 + Matrix.mulVec U p.1) -
          (Matrix.mulVec Bp p.2 + Matrix.mulVec P p.1) := by
            abel
    _ = 0 := sub_eq_zero.mpr h

/-- TeX matching Step 4: quadric coefficient separation applied to the Step 3 affine
difference identity. -/
structure TexMatchingQuadricSeparationData {L d : Nat}
    (θ θ' : Params (L + 1) d)
    {Ustar : Set (ProbePair d × ℝ)}
    (N : TexMatchingProductNeighborhoodData (d := d)
      (Params.headAttention θ') Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma)
    (limits : TexMatchingDialLimitAgreementData θ θ' N S) : Prop where
  skipProduct_eq :
    realSkipBprod (paramStream θ) (L + 1) =
      realSkipBprod (paramStream θ') (L + 1)
  limitDifference_eq_zero :
    ∀ t : ℝ, t ∈ N.J ->
      texMatchingLimitDifferenceMatrix θ θ' S.D t = 0

/-- Linear-algebra endpoint for Step 4: if a matrix kills every vector, it is zero. -/
theorem matrix_eq_zero_of_forall_mulVec_eq_zero {d : Nat}
    {M : Matrix (Fin d) (Fin d) ℝ}
    (h : ∀ v : Fin d -> ℝ, Matrix.mulVec M v = 0) :
    M = 0 := by
  ext i j
  have hij := congrFun (h (Pi.single j (1 : ℝ))) i
  simpa [Matrix.mulVec_single_one] using hij

/-- Algebraic core of TeX matching Step 4.

This is the remaining quadric-separation obligation: a vector identity on the product
neighborhood `Uq × J`, with `Uq` lying in the first-layer quadric and `J` open,
forces both separated matrix coefficients to vanish. -/
theorem texMatching_coefficients_eq_zero_of_limit_difference
    {d : Nat}
    {A M : Matrix (Fin d) (Fin d) ℝ}
    {R : ℝ -> Matrix (Fin d) (Fin d) ℝ}
    {Uq : Set (ProbePair d)} {J : Set ℝ}
    (hUq_nonempty : Uq.Nonempty)
    (hJ_nonempty : J.Nonempty)
    (hJ_open : IsOpen J)
    (hUq_on_quadric : ∀ p ∈ Uq, firstLayerQuadric A p)
    (hlimit :
      ∀ p : ProbePair d, p ∈ Uq -> ∀ t : ℝ, t ∈ J ->
        Matrix.mulVec M p.2 + Matrix.mulVec (R t) p.1 = 0)
    (hcoefficient_separation :
      ∀ (M : Matrix (Fin d) (Fin d) ℝ)
        (R : ℝ -> Matrix (Fin d) (Fin d) ℝ),
        (∀ p : ProbePair d, p ∈ Uq -> ∀ t : ℝ, t ∈ J ->
          Matrix.mulVec M p.2 + Matrix.mulVec (R t) p.1 = 0) ->
          (∀ v : Fin d -> ℝ, Matrix.mulVec M v = 0) ∧
            (∀ t : ℝ, t ∈ J -> R t = 0)) :
    (∀ v : Fin d -> ℝ, Matrix.mulVec M v = 0) ∧
      (∀ t : ℝ, t ∈ J -> R t = 0) := by
  have _ := hUq_nonempty
  have _ := hJ_nonempty
  have _ := hJ_open
  have _ := hUq_on_quadric
  exact hcoefficient_separation M R hlimit

/-- First matrix coefficient output from Step 4. -/
theorem texMatching_forall_mulVec_skipProductDifference_eq_zero_of_limit_difference
    {d : Nat}
    {A M : Matrix (Fin d) (Fin d) ℝ}
    {R : ℝ -> Matrix (Fin d) (Fin d) ℝ}
    {Uq : Set (ProbePair d)} {J : Set ℝ}
    (hUq_nonempty : Uq.Nonempty)
    (hJ_nonempty : J.Nonempty)
    (hJ_open : IsOpen J)
    (hUq_on_quadric : ∀ p ∈ Uq, firstLayerQuadric A p)
    (hlimit :
      ∀ p : ProbePair d, p ∈ Uq -> ∀ t : ℝ, t ∈ J ->
        Matrix.mulVec M p.2 + Matrix.mulVec (R t) p.1 = 0)
    (hcoefficient_separation :
      ∀ (M : Matrix (Fin d) (Fin d) ℝ)
        (R : ℝ -> Matrix (Fin d) (Fin d) ℝ),
        (∀ p : ProbePair d, p ∈ Uq -> ∀ t : ℝ, t ∈ J ->
          Matrix.mulVec M p.2 + Matrix.mulVec (R t) p.1 = 0) ->
          (∀ v : Fin d -> ℝ, Matrix.mulVec M v = 0) ∧
            (∀ t : ℝ, t ∈ J -> R t = 0)) :
    ∀ v : Fin d -> ℝ, Matrix.mulVec M v = 0 := by
  exact
    (texMatching_coefficients_eq_zero_of_limit_difference
      (A := A) (M := M) (R := R) hUq_nonempty hJ_nonempty hJ_open
      hUq_on_quadric hlimit hcoefficient_separation).1

/-- Second matrix coefficient output from Step 4. -/
theorem texMatching_forall_limitDifference_eq_zero_of_limit_difference
    {d : Nat}
    {A M : Matrix (Fin d) (Fin d) ℝ}
    {R : ℝ -> Matrix (Fin d) (Fin d) ℝ}
    {Uq : Set (ProbePair d)} {J : Set ℝ}
    (hUq_nonempty : Uq.Nonempty)
    (hJ_nonempty : J.Nonempty)
    (hJ_open : IsOpen J)
    (hUq_on_quadric : ∀ p ∈ Uq, firstLayerQuadric A p)
    (hlimit :
      ∀ p : ProbePair d, p ∈ Uq -> ∀ t : ℝ, t ∈ J ->
        Matrix.mulVec M p.2 + Matrix.mulVec (R t) p.1 = 0)
    (hcoefficient_separation :
      ∀ (M : Matrix (Fin d) (Fin d) ℝ)
        (R : ℝ -> Matrix (Fin d) (Fin d) ℝ),
        (∀ p : ProbePair d, p ∈ Uq -> ∀ t : ℝ, t ∈ J ->
          Matrix.mulVec M p.2 + Matrix.mulVec (R t) p.1 = 0) ->
          (∀ v : Fin d -> ℝ, Matrix.mulVec M v = 0) ∧
            (∀ t : ℝ, t ∈ J -> R t = 0)) :
    ∀ t : ℝ, t ∈ J -> R t = 0 := by
  exact
    (texMatching_coefficients_eq_zero_of_limit_difference
      (A := A) (M := M) (R := R) hUq_nonempty hJ_nonempty hJ_open
      hUq_on_quadric hlimit hcoefficient_separation).2

/-- Matrix form of the Step 4 separation for the concrete TeX matching difference
matrix. -/
theorem texMatching_skipProductDifferenceMatrix_eq_zero_of_quadricSeparation
    {L d : Nat}
    {θ θ' : Params (L + 1) d}
    {Ustar : Set (ProbePair d × ℝ)}
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma)
    (limits : TexMatchingDialLimitAgreementData θ θ' N S) :
    texMatchingSkipProductDifferenceMatrix θ θ' = 0 := by
  apply matrix_eq_zero_of_forall_mulVec_eq_zero
  exact
    texMatching_forall_mulVec_skipProductDifference_eq_zero_of_limit_difference
      (A := Params.headAttention θ')
      (M := texMatchingSkipProductDifferenceMatrix θ θ')
      (R := fun t => texMatchingLimitDifferenceMatrix θ θ' S.D t)
      N.Uq_nonempty N.J_nonempty N.J_open N.Uq_on_quadric
      limits.limit_difference_eq N.coefficient_separation

/-- Matrix form of the Step 4 separation for the concrete TeX limit-difference
matrix. -/
theorem texMatching_limitDifferenceMatrix_eq_zero_of_quadricSeparation
    {L d : Nat}
    {θ θ' : Params (L + 1) d}
    {Ustar : Set (ProbePair d × ℝ)}
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma)
    (limits : TexMatchingDialLimitAgreementData θ θ' N S) :
    ∀ t : ℝ, t ∈ N.J ->
      texMatchingLimitDifferenceMatrix θ θ' S.D t = 0 := by
  exact
    texMatching_forall_limitDifference_eq_zero_of_limit_difference
      (A := Params.headAttention θ')
      (M := texMatchingSkipProductDifferenceMatrix θ θ')
      (R := fun t => texMatchingLimitDifferenceMatrix θ θ' S.D t)
      N.Uq_nonempty N.J_nonempty N.J_open N.Uq_on_quadric
      limits.limit_difference_eq N.coefficient_separation

/-- Convert the zero skip-product difference matrix into the desired matrix equality. -/
theorem texMatching_skipProduct_eq_of_skipProductDifferenceMatrix_eq_zero
    {L d : Nat} {θ θ' : Params (L + 1) d}
    (hzero : texMatchingSkipProductDifferenceMatrix θ θ' = 0) :
    realSkipBprod (paramStream θ) (L + 1) =
      realSkipBprod (paramStream θ') (L + 1) := by
  exact sub_eq_zero.mp (by
    simpa [texMatchingSkipProductDifferenceMatrix] using hzero)

/-- Analytic limit-comparison obligation for TeX matching Steps 2--3. -/
theorem texMatching_dialLimitAgreement_of_saturatedContribution
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (S : TexMatchingSaturatedContributionData θ T.trichotomy.varsigma)
    (limitAgreement : TexMatchingLimitVectorAgreementData θ θ' N S) :
    TexMatchingDialLimitAgreementData θ θ' N S := by
  let hlimits :=
    texMatching_matchingLimits_eq_of_saturatedContribution
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion T N S
      limitAgreement
  exact
    { limit_difference_eq :=
        texMatching_limitDifference_eq_of_matchingLimits N S hlimits }

/-- Algebraic quadric-separation obligation for TeX matching Step 4. -/
theorem texMatching_quadricSeparation_of_dialLimitAgreement
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (S : TexMatchingSaturatedContributionData θ T.trichotomy.varsigma)
    (limits : TexMatchingDialLimitAgreementData θ θ' N S) :
    TexMatchingQuadricSeparationData θ θ' N S limits := by
  have _ := hr
  have _ := hstep
  have _ := endpoint
  have _ := D
  have _ := signRegion
  have _ := T
  exact
    { skipProduct_eq :=
        texMatching_skipProduct_eq_of_skipProductDifferenceMatrix_eq_zero
          (texMatching_skipProductDifferenceMatrix_eq_zero_of_quadricSeparation
            (N := N) S limits)
      limitDifference_eq_zero :=
        texMatching_limitDifferenceMatrix_eq_zero_of_quadricSeparation
          (N := N) S limits }

/-- Lemma `region` from the TeX Step 2 proof, specialized to the IDL induction
interface.  The endpoint supplies the common first attention matrix and nonzero
unprimed first value; the TeX generic clauses supply `(G1)` and the anchor data. -/
noncomputable def signRegionData_of_texGenericStep
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (region :
      TexRegionConstructionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ))) :
    SignRegionData (L := L + 1) (d := d) θ' D.O
      (Params.headAttention θ') (Real.log (r : ℝ)) := by
  have _ := hr
  let region :=
    texRegionConstructionData_of_texGenericStep hstep endpoint D (Real.log (r : ℝ))
      region
  exact texRegion_signRegionData hstep endpoint D (Real.log (r : ℝ)) region

/-- TeX Proposition `trichotomy`, isolated from the coefficient comparison in
Proposition `matching`. -/
noncomputable def texTrichotomyConstructionData_of_signRegion
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ))) :
    TexTrichotomyConstructionData (L := L + 1) (d := d)
      (Real.log (r : ℝ)) signRegion.U := by
  have _ := hr
  have _ := hstep
  have _ := endpoint
  have _ := D
  exact
    { unprimed := constantGateAlongBase (d := d) 1
      primed := constantGateAlongBase (d := d) 1
      Ustar := signRegion.U
      trichotomy := trichotomyData_constOne_of_signRegion signRegion }

/-- Step 0 of TeX Proposition `matching`: choose a product neighborhood inside the
trichotomy component.  The selected sign-region patch already carries the coefficient
separation needed in matching Step 4. -/
noncomputable def texMatchingProductNeighborhoodData_of_trichotomy
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U) :
    TexMatchingProductNeighborhoodData (d := d) (Params.headAttention θ') T.Ustar := by
  have _ := hr
  have _ := hstep
  have _ := endpoint
  have _ := D
  let patch := signRegion.product_neighborhood T.Ustar
      T.trichotomy.subset_sign_region T.trichotomy.nonempty
      T.trichotomy.relatively_open_in_sign_region
  exact
    { Uq := patch.Uq
      J := patch.J
      Uq_nonempty := patch.Uq_nonempty
      J_nonempty := patch.J_nonempty
      J_open := patch.J_open
      Uq_on_quadric := patch.Uq_on_quadric
      product_subset := patch.product_subset
      coefficient_separation := patch.coefficient_separation }

/-- Step 1 of TeX Proposition `matching`: build the saturated lower-layer contribution
appearing in the unprimed limit formula. -/
noncomputable def texMatchingSaturatedContributionData_of_trichotomy
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar) :
    TexMatchingSaturatedContributionData θ T.trichotomy.varsigma := by
  have _ := hr
  have _ := hstep
  have _ := endpoint
  have _ := D
  have _ := signRegion
  have _ := T
  have _ := N
  exact
    { D := texMatchingSaturatedContributionMatrix θ T.trichotomy.varsigma
      D_eq := rfl }

/-- Steps 2--4 of TeX Proposition `matching`: equality of path limits and separation on
the quadric give equality of the full skip products. -/
theorem texMatching_skipProduct_eq_of_saturatedContribution
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (S : TexMatchingSaturatedContributionData θ T.trichotomy.varsigma)
    (limitAgreement : TexMatchingLimitVectorAgreementData θ θ' N S) :
    realSkipBprod (paramStream θ) (L + 1) =
      realSkipBprod (paramStream θ') (L + 1) := by
  have _ := hr
  have _ := hstep
  have _ := endpoint
  have _ := D
  have _ := signRegion
  have _ := T
  have _ := N
  let limits : TexMatchingDialLimitAgreementData θ θ' N S :=
    texMatching_dialLimitAgreement_of_saturatedContribution
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion T N S
      limitAgreement
  exact
    (texMatching_quadricSeparation_of_dialLimitAgreement
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion T N S
        limits).skipProduct_eq

/-- A nonempty open set of real numbers contains two distinct points. -/
theorem exists_pair_ne_of_isOpen_nonempty
    {J : Set ℝ} (hJ_open : IsOpen J) (hJ_nonempty : J.Nonempty) :
    ∃ t0 ∈ J, ∃ t1 ∈ J, t1 ≠ t0 := by
  rcases hJ_nonempty with ⟨t0, ht0⟩
  rcases Metric.isOpen_iff.mp hJ_open t0 ht0 with ⟨ε, hεpos, hball⟩
  refine ⟨t0, ht0, t0 + ε / 2, ?_, ?_⟩
  · apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have hhalfpos : 0 < ε / 2 := by linarith
    have habs : |t0 + ε / 2 - t0| = ε / 2 := by
      rw [add_sub_cancel_left]
      exact abs_of_pos hhalfpos
    rw [habs]
    linarith
  · intro h
    have hzero : ε / 2 = 0 := by linarith
    linarith

/-- Subtracting two limit-difference matrices isolates the affine `t` coefficient. -/
theorem texMatching_limitDifferenceMatrix_sub
    {L d : Nat} {θ θ' : Params (L + 1) d}
    {Dsat : Matrix (Fin d) (Fin d) ℝ}
    {t0 t1 : ℝ} :
    texMatchingLimitDifferenceMatrix θ θ' Dsat t1 -
        texMatchingLimitDifferenceMatrix θ θ' Dsat t0 =
      (t1 - t0) •
        (((realSkipBprod (paramStream (Params.tail θ)) L - Dsat) *
            (θ 0).1) - (θ' 0).1) := by
  ext i j
  simp only [texMatchingLimitDifferenceMatrix, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  repeat rw [Finset.mul_sum]
  ring_nf
  repeat rw [Finset.mul_sum]
  ring_nf
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
  ring_nf
  simp [mul_comm, mul_left_comm, mul_assoc]
  abel

/-- Step 5 affine `t`-coefficient extraction from Step 4's matrix identity
`E_t = 0` on the open set `J`. -/
theorem texMatching_affineTCoefficient_matrix_eq_of_limitDifference_eq_zero
    {L d : Nat}
    {θ θ' : Params (L + 1) d}
    {Dsat : Matrix (Fin d) (Fin d) ℝ}
    {J : Set ℝ} (hJ_open : IsOpen J) (hJ_nonempty : J.Nonempty)
    (hzero :
      ∀ t : ℝ, t ∈ J ->
        texMatchingLimitDifferenceMatrix θ θ' Dsat t = 0) :
    (realSkipBprod (paramStream (Params.tail θ)) L - Dsat) * (θ 0).1 =
      (θ' 0).1 := by
  rcases exists_pair_ne_of_isOpen_nonempty hJ_open hJ_nonempty with
    ⟨t0, ht0, t1, ht1, hne⟩
  have hdiff :
      texMatchingLimitDifferenceMatrix θ θ' Dsat t1 -
          texMatchingLimitDifferenceMatrix θ θ' Dsat t0 = 0 := by
    rw [hzero t1 ht1, hzero t0 ht0, sub_self]
  have hsmul :
      (t1 - t0) •
          (((realSkipBprod (paramStream (Params.tail θ)) L - Dsat) *
              (θ 0).1) - (θ' 0).1) = 0 := by
    simpa [texMatching_limitDifferenceMatrix_sub] using hdiff
  have hscalar : t1 - t0 ≠ 0 := sub_ne_zero.mpr hne
  have hcoeff :
      ((realSkipBprod (paramStream (Params.tail θ)) L - Dsat) *
          (θ 0).1) - (θ' 0).1 = 0 :=
    (smul_eq_zero.mp hsmul).resolve_left hscalar
  exact sub_eq_zero.mp hcoeff

/-- A skip-product over a stream factors as the shifted-tail product times the head
skip matrix. -/
theorem realSkipBprod_head_shift
    {d : Nat} (σ : LayerStream d) :
    ∀ L : Nat,
      realSkipBprod σ (L + 1) =
        realSkipBprod (fun n => σ (n + 1)) L * skipB (σ 0).1
  | 0 => by
      simp [realSkipBprod_succ]
  | L + 1 => by
      rw [realSkipBprod_succ, realSkipBprod_head_shift σ L,
        realSkipBprod_succ]
      rw [Matrix.mul_assoc]

/-- The full skip product is the tail skip product followed by the first skip matrix. -/
theorem realSkipBprod_paramStream_head_tail
    {L d : Nat} (θ : Params (L + 1) d) :
    realSkipBprod (paramStream θ) (L + 1) =
      realSkipBprod (paramStream (Params.tail θ)) L * skipB (θ 0).1 := by
  rw [realSkipBprod_head_shift]
  have hshift :
      (fun n => paramStream θ (n + 1)) = paramStream (Params.tail θ) := by
    funext n
    by_cases hn : n < L
    · have hn1 : n + 1 < L + 1 := Nat.succ_lt_succ hn
      simp [paramStream, Params.tail, Fin.tail, hn, hn1]
    · have hn1 : ¬ n + 1 < L + 1 := by omega
      simp [paramStream, hn, hn1]
  rw [hshift]
  simp [paramStream_apply_of_lt]

/-- Decompose the limit-difference matrix into its affine `t` coefficient and constant
coefficient. -/
theorem texMatching_limitDifferenceMatrix_affine_decomp
    {L d : Nat} {θ θ' : Params (L + 1) d}
    {Dsat : Matrix (Fin d) (Fin d) ℝ}
    {t : ℝ} :
    texMatchingLimitDifferenceMatrix θ θ' Dsat t =
      t • ((((realSkipBprod (paramStream (Params.tail θ)) L - Dsat) *
          (θ 0).1) - (θ' 0).1)) +
        (Dsat * skipB (θ 0).1 -
          realSkipBprod (paramStream θ') (L + 1) + skipB (θ' 0).1) := by
  ext i j
  simp only [texMatchingLimitDifferenceMatrix, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  repeat rw [Finset.mul_sum]
  ring_nf
  repeat rw [Finset.mul_sum]
  ring_nf
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring_nf
  simp [mul_comm, mul_left_comm, mul_assoc]
  abel_nf

/-- Step 5 constant-coefficient extraction from Step 4's matrix identity `E_t = 0` on
the open set `J`. -/
theorem texMatching_affineConstantCoefficient_matrix_eq_of_limitDifference_eq_zero
    {L d : Nat} {θ θ' : Params (L + 1) d}
    {Dsat : Matrix (Fin d) (Fin d) ℝ}
    {J : Set ℝ} (hJ_open : IsOpen J) (hJ_nonempty : J.Nonempty)
    (hzero :
      ∀ t : ℝ, t ∈ J ->
        texMatchingLimitDifferenceMatrix θ θ' Dsat t = 0) :
    Dsat * skipB (θ 0).1 -
        realSkipBprod (paramStream θ') (L + 1) + skipB (θ' 0).1 = 0 := by
  rcases hJ_nonempty with ⟨t0, ht0⟩
  have htcoeff :
      (realSkipBprod (paramStream (Params.tail θ)) L - Dsat) * (θ 0).1 =
        (θ' 0).1 :=
    texMatching_affineTCoefficient_matrix_eq_of_limitDifference_eq_zero
      (L := L) (d := d) (θ := θ) (θ' := θ') (Dsat := Dsat)
      hJ_open ⟨t0, ht0⟩ hzero
  have htcoeff_zero :
      (((realSkipBprod (paramStream (Params.tail θ)) L - Dsat) *
          (θ 0).1) - (θ' 0).1) = 0 := sub_eq_zero.mpr htcoeff
  have hdecomp :=
    texMatching_limitDifferenceMatrix_affine_decomp
      (L := L) (d := d) (θ := θ) (θ' := θ') (Dsat := Dsat) (t := t0)
  rw [hzero t0 ht0, htcoeff_zero] at hdecomp
  simpa using hdecomp.symm

/-- Combine the skip-product equality with the constant coefficient identity to get
the required first-skip mapping through `K`. -/
theorem texMatching_K_maps_headSkip_of_coefficients
    {L d : Nat} {θ θ' : Params (L + 1) d}
    {Dsat : Matrix (Fin d) (Fin d) ℝ}
    (hskip :
      realSkipBprod (paramStream θ) (L + 1) =
        realSkipBprod (paramStream θ') (L + 1))
    (hconst :
      Dsat * skipB (θ 0).1 -
          realSkipBprod (paramStream θ') (L + 1) + skipB (θ' 0).1 = 0) :
    (realSkipBprod (paramStream (Params.tail θ)) L - Dsat) *
        skipB (θ 0).1 =
      skipB (θ' 0).1 := by
  have htail :
      realSkipBprod (paramStream (Params.tail θ)) L * skipB (θ 0).1 =
        realSkipBprod (paramStream θ') (L + 1) := by
    rw [← realSkipBprod_paramStream_head_tail θ]
    exact hskip
  have hD :
      Dsat * skipB (θ 0).1 =
        realSkipBprod (paramStream θ') (L + 1) - skipB (θ' 0).1 := by
    apply sub_eq_zero.mp
    calc
      Dsat * skipB (θ 0).1 -
          (realSkipBprod (paramStream θ') (L + 1) - skipB (θ' 0).1)
          = Dsat * skipB (θ 0).1 -
              realSkipBprod (paramStream θ') (L + 1) + skipB (θ' 0).1 := by
              abel
      _ = 0 := hconst
  calc
    (realSkipBprod (paramStream (Params.tail θ)) L - Dsat) *
        skipB (θ 0).1
        = realSkipBprod (paramStream (Params.tail θ)) L * skipB (θ 0).1 -
          Dsat * skipB (θ 0).1 := by
            rw [Matrix.sub_mul]
    _ = realSkipBprod (paramStream θ') (L + 1) -
          (realSkipBprod (paramStream θ') (L + 1) - skipB (θ' 0).1) := by
            rw [htail, hD]
    _ = skipB (θ' 0).1 := by
      abel

/-- Step 5 of TeX Proposition `matching`: the affine coefficient of `t` maps the first
value matrix through `K`. -/
theorem texMatching_K_maps_headValue_of_saturatedContribution
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (S : TexMatchingSaturatedContributionData θ T.trichotomy.varsigma)
    (limitAgreement : TexMatchingLimitVectorAgreementData θ θ' N S) :
    (realSkipBprod (paramStream (Params.tail θ)) L - S.D) * (θ 0).1 =
      (θ' 0).1 := by
  have limits : TexMatchingDialLimitAgreementData θ θ' N S :=
    texMatching_dialLimitAgreement_of_saturatedContribution
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion T N S
      limitAgreement
  have sep : TexMatchingQuadricSeparationData θ θ' N S limits :=
    texMatching_quadricSeparation_of_dialLimitAgreement
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion T N S
      limits
  exact
    texMatching_affineTCoefficient_matrix_eq_of_limitDifference_eq_zero
      (L := L) (d := d) (θ := θ) (θ' := θ') (Dsat := S.D)
      N.J_open N.J_nonempty sep.limitDifference_eq_zero

/-- Step 5 of TeX Proposition `matching`: the affine constant coefficient maps the first
skip matrix through `K`. -/
theorem texMatching_K_maps_headSkip_of_saturatedContribution
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (S : TexMatchingSaturatedContributionData θ T.trichotomy.varsigma)
    (limitAgreement : TexMatchingLimitVectorAgreementData θ θ' N S) :
    (realSkipBprod (paramStream (Params.tail θ)) L - S.D) * skipB (θ 0).1 =
      skipB (θ' 0).1 := by
  have limits : TexMatchingDialLimitAgreementData θ θ' N S :=
    texMatching_dialLimitAgreement_of_saturatedContribution
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion T N S
      limitAgreement
  have hskip :
      realSkipBprod (paramStream θ) (L + 1) =
        realSkipBprod (paramStream θ') (L + 1) :=
    texMatching_skipProduct_eq_of_skipProductDifferenceMatrix_eq_zero
      (texMatching_skipProductDifferenceMatrix_eq_zero_of_quadricSeparation
        (N := N) S limits)
  have hzero :
      ∀ t : ℝ, t ∈ N.J ->
        texMatchingLimitDifferenceMatrix θ θ' S.D t = 0 :=
    texMatching_limitDifferenceMatrix_eq_zero_of_quadricSeparation
      (N := N) S limits
  have hconst :
      S.D * skipB (θ 0).1 -
          realSkipBprod (paramStream θ') (L + 1) + skipB (θ' 0).1 = 0 :=
    texMatching_affineConstantCoefficient_matrix_eq_of_limitDifference_eq_zero
      (L := L) (d := d) (θ := θ) (θ' := θ') (Dsat := S.D)
      N.J_open N.J_nonempty hzero
  exact
    texMatching_K_maps_headSkip_of_coefficients
      (L := L) (d := d) (θ := θ) (θ' := θ') (Dsat := S.D)
      hskip hconst

/-- Direct matching-limit endpoint from the explicit Step 2 bridge data.

This avoids packaging the path/limit bridge as a hidden field of `IDLData`: callers must
provide the sign region, trichotomy component, product patch, saturated contribution,
and the limit-vector agreement produced from actual dial-path agreement. -/
noncomputable def matchingLimitData_of_IDLData_of_saturatedLimitAgreement
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (S : TexMatchingSaturatedContributionData θ T.trichotomy.varsigma)
    (limitAgreement : TexMatchingLimitVectorAgreementData θ θ' N S) :
    MatchingLimitData θ θ' := by
  exact
    { skipProduct_eq :=
        texMatching_skipProduct_eq_of_saturatedContribution
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion T N S
          limitAgreement
      K := realSkipBprod (paramStream (Params.tail θ)) L - S.D
      K_maps_headValue :=
        texMatching_K_maps_headValue_of_saturatedContribution
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion T N S
          limitAgreement
      K_maps_headSkip :=
        texMatching_K_maps_headSkip_of_saturatedContribution
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion T N S
          limitAgreement }

/-- Direct matching-limit endpoint with the dial-path bridge expanded.  Availability of
the paths comes from the bridge; observable agreement along them is obtained from
`D.path_agreement`. -/
noncomputable def matchingLimitData_of_IDLData_of_dialPathLimitBridge
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (S : TexMatchingSaturatedContributionData θ T.trichotomy.varsigma)
    (B : TexMatchingDialPathLimitBridgeData D N S) :
    MatchingLimitData θ θ' := by
  let limitAgreement :
      TexMatchingLimitVectorAgreementData θ θ' N S :=
    texMatchingLimitVectorAgreementData_of_dialPathLimitBridge D N S B
  exact
    matchingLimitData_of_IDLData_of_saturatedLimitAgreement
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion T N S
      limitAgreement

/-- Canonical sign region obtained from the strengthened TeX region construction. -/
noncomputable def texMatchingSignRegionData_of_region
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (region :
      TexRegionConstructionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ))) :
    SignRegionData (L := L + 1) (d := d) θ' D.O
      (Params.headAttention θ') (Real.log (r : ℝ)) :=
  signRegionData_of_texGenericStep
    (L := L) (d := d) (r := r) hr hstep endpoint D region

/-- Canonical trichotomy component over the region-generated sign region. -/
noncomputable def texMatchingTrichotomyConstructionData_of_region
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (region :
      TexRegionConstructionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ))) :
    TexTrichotomyConstructionData (L := L + 1) (d := d)
      (Real.log (r : ℝ))
      (texMatchingSignRegionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region).U :=
  texTrichotomyConstructionData_of_signRegion
    (L := L) (d := d) (r := r) hr hstep endpoint D
    (texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region)

/-- Canonical matching product patch supplied by the strengthened region interface. -/
noncomputable def texMatchingProductNeighborhoodData_of_region
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (region :
      TexRegionConstructionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ))) :
    TexMatchingProductNeighborhoodData (d := d) (Params.headAttention θ')
      (texMatchingTrichotomyConstructionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region).Ustar := by
  exact
    texMatchingProductNeighborhoodData_of_trichotomy
      (L := L) (d := d) (r := r) hr hstep endpoint D
      (texMatchingSignRegionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region)
      (texMatchingTrichotomyConstructionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region)

/-- Canonical saturated lower-layer contribution over the region-generated product
patch. -/
noncomputable def texMatchingSaturatedContributionData_of_region
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (region :
      TexRegionConstructionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ))) :
    TexMatchingSaturatedContributionData θ
      (texMatchingTrichotomyConstructionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region).trichotomy.varsigma := by
  exact
    texMatchingSaturatedContributionData_of_trichotomy
      (L := L) (d := d) (r := r) hr hstep endpoint D
      (texMatchingSignRegionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region)
      (texMatchingTrichotomyConstructionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region)
      (texMatchingProductNeighborhoodData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region)

/-- Smallest currently exposed first-layer matching support package.

Everything after these fields is mechanical in `IDLMatching`: the constructor-level
trichotomy and saturated contribution are built from the sign region, and
`D.path_agreement` is consumed through the dial-path bridge.  This deliberately avoids
requiring the legacy `TexFirstLayerMatchingConstructionData` bundle while keeping the
remaining region/product/dial-limit obligations explicit. -/
structure TexFirstLayerMatchingAnalyticData {L d r : Nat}
    (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ') : Type where
  signRegion :
    SignRegionData (L := L + 1) (d := d) θ' D.O
      (Params.headAttention θ') (Real.log (r : ℝ))
  neighborhood :
    TexMatchingProductNeighborhoodData (d := d)
      (Params.headAttention θ')
      (texTrichotomyConstructionData_of_signRegion
        (L := L) (d := d) (r := r) hr hstep endpoint D signRegion).Ustar
  bridge :
    TexMatchingDialPathLimitBridgeData D neighborhood
      (texMatchingSaturatedContributionData_of_trichotomy
        (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
        (texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion)
        neighborhood)

/-- No-legacy provider for the first-layer matching support package.

The region field is the strengthened TeX Lemma `region` output: its product-neighborhood
selector returns coefficient-separating patches.  The bridge field is the remaining TeX
Proposition `matching` analytic limit input for the canonical patch selected from that
region. -/
structure TexMatchingRegionProviderData {L d r : Nat}
    (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ') : Type where
  region :
    TexRegionConstructionData (L := L + 1) (d := d) θ' D.O
      (Params.headAttention θ') (Real.log (r : ℝ))
  bridge :
    TexMatchingDialPathLimitBridgeData D
      (texMatchingProductNeighborhoodData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region)
      (texMatchingSaturatedContributionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region)

/-- Reduced matching provider after the region side is discharged by the anchored local
quadric product-patch primitive.  Its only field is the remaining dial-limit bridge for
the canonical product patch selected from the generated region. -/
structure TexMatchingRegionProviderFromLocalPatchData {L d r : Nat}
    (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Type where
  bridge :
    TexMatchingDialPathLimitBridgeData D
      (texMatchingProductNeighborhoodData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D
          (texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
      (texMatchingSaturatedContributionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D
          (texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))

/-- Pointwise limit-vector theorem for the regular-quadric dial selected at a product
patch point.

This is the saturated/telescoped vector comparison with all local-patch constructor lets
removed.  The only path appearing in the statement is the named
`texMatchingRegularQuadricDialPathData`, which is definitionally the corresponding
`DialPathData.ofRegularQuadric`. -/
abbrev TexMatchingRegularQuadricLimitVectorObligation
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma) : Prop :=
  ∀ p hp t ht, ∀ T0 : ℝ,
    ObservableAgreementOnPath r θ θ'
      (DialPathData.probe
        (texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht)) T0 ->
    texMatchingUnprimedSaturatedLimitVector θ S.D t p =
      texMatchingPrimedTelescopedLimitVector θ' t p

/-- Eventual observable agreement gives eventual equality of the closed probe recursion
on positive real tails. -/
theorem texMatching_frec_eq_on_path_of_observableAgreement
    {L d r : Nat} (hr_pos : 0 < r)
    {θ θ' : Params L d} {P : ProbePath d} {T0 : ℝ}
    (hobs : ObservableAgreementOnPath r θ θ' P T0) :
    ∀ τ : ℝ, T0 < τ ->
      Frec r θ (P τ).1 (P τ).2 τ =
        Frec r θ' (P τ).1 (P τ).2 τ := by
  intro τ hτ
  have hτ_pos : 0 < τ := lt_of_le_of_lt hobs.1 hτ
  calc
    Frec r θ (P τ).1 (P τ).2 τ =
        Fobs r θ (P τ).1 (P τ).2 τ := by
          exact (Fobs_eq_Frec_of_pos r hr_pos θ (P τ).1 (P τ).2 hτ_pos).symm
    _ = Fobs r θ' (P τ).1 (P τ).2 τ := hobs.2 τ hτ
    _ = Frec r θ' (P τ).1 (P τ).2 τ := by
          exact Fobs_eq_Frec_of_pos r hr_pos θ' (P τ).1 (P τ).2 hτ_pos

/-- The first-layer effective tail point of the unprimed recursion along a primed dial.

The dial geometry is still the one selected from the primed first attention matrix, but
the exact recursion peel uses the first layer of `θ`. -/
noncomputable def texMatchingUnprimedDialEffectiveTailPoint
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ)))
    (τ : ℝ) : ProbePair d :=
  paramsFirstLayerEffectivePoint r θ
    (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ

/-- The lower-depth path obtained by peeling the unprimed first layer along a primed
dial.  This is the path whose membership in a swept tail path class is needed by the
recursive Frec asymptotic. -/
noncomputable def texMatchingUnprimedDialEffectiveTailPath
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ))) :
    ProbePath d :=
  fun τ =>
    texMatchingUnprimedDialEffectiveTailPoint
      (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ τ

@[simp]
theorem texMatchingUnprimedDialEffectiveTailPath_apply
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ)))
    (τ : ℝ) :
    texMatchingUnprimedDialEffectiveTailPath
        (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ τ =
      texMatchingUnprimedDialEffectiveTailPoint
        (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ τ :=
  rfl

/-- The unprimed effective-tail path is realized by the original dial path through the
first layer of `θ`. -/
noncomputable def texMatchingUnprimedDialEffectiveTailRealizationData
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ))) :
    RealizationData r (Params.headValue θ) (Params.headAttention θ)
      (texMatchingUnprimedDialEffectiveTailPath
        (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ)
      (DialPathData.probe δ) where
  threshold := 0
  threshold_nonneg := by norm_num
  effective_eq := by
    intro τ _hτ
    simp [texMatchingUnprimedDialEffectiveTailPath,
      texMatchingUnprimedDialEffectiveTailPoint, paramsFirstLayerEffectivePoint]

/-- Constructor-level realization witness for the peeled effective-tail path.  Files
that own `realizedTailPathSet` can wrap this together with path-class membership. -/
theorem texMatchingUnprimedDialEffectiveTailPath_realization_nonempty
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ))) :
    Nonempty
      (RealizationData r (Params.headValue θ) (Params.headAttention θ)
        (texMatchingUnprimedDialEffectiveTailPath
          (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ)
        (DialPathData.probe δ)) :=
  ⟨texMatchingUnprimedDialEffectiveTailRealizationData
    (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ⟩

/-- Peeled unprimed Frec saturation asymptotic over the refined trichotomy component.

This is the Step 1 analytic theorem after the exact first recursion layer has been
removed.  The remaining limit is still the saturated unprimed limit vector attached to
the original dial endpoint. -/
abbrev TexMatchingUnprimedSaturatedEffectiveTailFrecAsymptotic
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {signU : Set (ProbePair d × ℝ)}
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signU)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma) : Prop :=
  ∀ δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ)),
    (δ.base, δ.t) ∈ T.Ustar ->
    Filter.Tendsto
      (fun τ : ℝ =>
        let q :=
          texMatchingUnprimedDialEffectiveTailPoint
            (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ τ
        Frec r (Params.tail θ) q.1 q.2 τ)
      Filter.atTop
      (nhds (texMatchingUnprimedSaturatedLimitVector θ S.D δ.t δ.base))

/-- The first-layer effective tail point of the primed recursion along a dial.

This is the point obtained after peeling the head layer of `θ'` at the actual first
sigmoid gate of the varying dial probe. -/
noncomputable def texMatchingPrimedDialEffectiveTailPoint
    {L d r : Nat}
    {θ' : Params (L + 1) d}
    (δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ)))
    (τ : ℝ) : ProbePair d :=
  paramsFirstLayerEffectivePoint r θ'
    (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ

/-- The lower-depth path obtained by peeling the primed first layer along a dial. -/
noncomputable def texMatchingPrimedDialEffectiveTailPath
    {L d r : Nat}
    {θ' : Params (L + 1) d}
    (δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ))) :
    ProbePath d :=
  fun τ =>
    texMatchingPrimedDialEffectiveTailPoint
      (L := L) (d := d) (r := r) (θ' := θ') δ τ

@[simp]
theorem texMatchingPrimedDialEffectiveTailPath_apply
    {L d r : Nat}
    {θ' : Params (L + 1) d}
    (δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ)))
    (τ : ℝ) :
    texMatchingPrimedDialEffectiveTailPath
        (L := L) (d := d) (r := r) (θ' := θ') δ τ =
      texMatchingPrimedDialEffectiveTailPoint
        (L := L) (d := d) (r := r) (θ' := θ') δ τ :=
  rfl

/-- The primed effective-tail path is realized by the original dial path through the
first layer of `θ'`. -/
noncomputable def texMatchingPrimedDialEffectiveTailRealizationData
    {L d r : Nat}
    {θ' : Params (L + 1) d}
    (δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ))) :
    RealizationData r (Params.headValue θ') (Params.headAttention θ')
      (texMatchingPrimedDialEffectiveTailPath
        (L := L) (d := d) (r := r) (θ' := θ') δ)
      (DialPathData.probe δ) where
  threshold := 0
  threshold_nonneg := by norm_num
  effective_eq := by
    intro τ _hτ
    simp [texMatchingPrimedDialEffectiveTailPath,
      texMatchingPrimedDialEffectiveTailPoint, paramsFirstLayerEffectivePoint]

/-- Constructor-level realization witness for the peeled primed effective-tail path. -/
theorem texMatchingPrimedDialEffectiveTailPath_realization_nonempty
    {L d r : Nat}
    {θ' : Params (L + 1) d}
    (δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ))) :
    Nonempty
      (RealizationData r (Params.headValue θ') (Params.headAttention θ')
        (texMatchingPrimedDialEffectiveTailPath
          (L := L) (d := d) (r := r) (θ' := θ') δ)
        (DialPathData.probe δ)) :=
  ⟨texMatchingPrimedDialEffectiveTailRealizationData
    (L := L) (d := d) (r := r) (θ' := θ') δ⟩

/-- Realized-tail membership for the unprimed peeled effective-tail path from source
dial-path membership. -/
theorem texMatchingUnprimedDialEffectiveTailPath_mem_realizedTailPathSet
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {FullPaths : Set (ProbePath d)}
    (δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ)))
    (hsource : DialPathData.probe δ ∈ FullPaths) :
    texMatchingUnprimedDialEffectiveTailPath
        (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ ∈
      realizedTailPathSet r θ FullPaths :=
  ⟨DialPathData.probe δ, hsource,
    texMatchingUnprimedDialEffectiveTailPath_realization_nonempty
      (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ⟩

/-- Realized-tail membership for the primed peeled effective-tail path from source
dial-path membership.  This is stated over the honest `θ'` realized-tail class; moving
it to the swept `θ` class requires first-layer matching. -/
theorem texMatchingPrimedDialEffectiveTailPath_mem_realizedTailPathSet
    {L d r : Nat}
    {θ' : Params (L + 1) d}
    {FullPaths : Set (ProbePath d)}
    (δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ)))
    (hsource : DialPathData.probe δ ∈ FullPaths) :
    texMatchingPrimedDialEffectiveTailPath
        (L := L) (d := d) (r := r) (θ' := θ') δ ∈
      realizedTailPathSet r θ' FullPaths :=
  ⟨DialPathData.probe δ, hsource,
    texMatchingPrimedDialEffectiveTailPath_realization_nonempty
      (L := L) (d := d) (r := r) (θ' := θ') δ⟩

/-- Selected-dial unprimed saturated effective-tail asymptotic for a regular-quadric
product patch.

The first unprimed recursion layer has been peeled; callers only prove convergence of
the tail recursion at the selected dial's exact first-layer effective point. -/
abbrev TexMatchingRegularQuadricUnprimedSaturatedEffectiveTailFrecAsymptotic
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma) : Prop :=
  ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    Filter.Tendsto
      (fun τ : ℝ =>
        let q :=
          texMatchingUnprimedDialEffectiveTailPoint
            (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ τ
        Frec r (Params.tail θ) q.1 q.2 τ)
      Filter.atTop
      (nhds (texMatchingUnprimedSaturatedLimitVector θ S.D t p))

/-- Selected-dial unprimed saturated tail-path asymptotic for a regular-quadric
product patch, phrased as convergence along the named lower-depth path. -/
abbrev TexMatchingRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma) : Prop :=
  ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    Filter.Tendsto
      (fun τ : ℝ =>
        let q :=
          texMatchingUnprimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ τ
        Frec r (Params.tail θ) q.1 q.2 τ)
      Filter.atTop
      (nhds (texMatchingUnprimedSaturatedLimitVector θ S.D t p))

/-- Selected-dial primed telescoped effective-tail asymptotic for a regular-quadric
product patch.

The first primed recursion layer has been peeled; callers only prove convergence of
the tail recursion at the selected dial's exact first-layer effective point. -/
abbrev TexMatchingRegularQuadricPrimedTelescopedEffectiveTailFrecAsymptotic
    {L d r : Nat}
    {θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar) : Prop :=
  ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    Filter.Tendsto
      (fun τ : ℝ =>
        let q :=
          texMatchingPrimedDialEffectiveTailPoint
            (L := L) (d := d) (r := r) (θ' := θ') δ τ
        Frec r (Params.tail θ') q.1 q.2 τ)
      Filter.atTop
      (nhds (texMatchingPrimedTelescopedLimitVector θ' t p))

/-- Selected-dial primed telescoped tail-path asymptotic for a regular-quadric product
patch, phrased as convergence along the named lower-depth path. -/
abbrev TexMatchingRegularQuadricPrimedTelescopedTailPathFrecAsymptotic
    {L d r : Nat}
    {θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar) : Prop :=
  ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    Filter.Tendsto
      (fun τ : ℝ =>
        let q :=
          texMatchingPrimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ' := θ') δ τ
        Frec r (Params.tail θ') q.1 q.2 τ)
      Filter.atTop
      (nhds (texMatchingPrimedTelescopedLimitVector θ' t p))

/-- Lower-depth `Frec` convergence data over an arbitrary path class.

This is the reusable recursive analytic surface: it does not mention first-layer
matching, local patches, or selected dials.  Callers separately identify the `limit`
field with the concrete saturated/telescoped vector for each selected tail path. -/
structure TexMatchingTailPathFrecAsymptoticData
    {L d r : Nat}
    (θtail : Params L d) (Paths : Set (ProbePath d)) : Type where
  limit : ProbePath d -> Fin d -> ℝ
  tendsto :
    ∀ P : ProbePath d, P ∈ Paths ->
      Filter.Tendsto
        (fun τ : ℝ => Frec r θtail (P τ).1 (P τ).2 τ)
        Filter.atTop
        (nhds (limit P))

/-- Selected unprimed tail-path asymptotic from lower-depth path-class convergence.

The remaining facts are exactly the selected unprimed effective-tail path membership
in the lower-depth path class and the algebraic identification of the lower-depth
limit with the saturated vector attached to the selected dial endpoint. -/
theorem texMatchingRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic_of_tailPathClass
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    {signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))}
    {T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U}
    {N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar}
    {varsigma : Nat -> ℝ}
    {S : TexMatchingSaturatedContributionData θ varsigma}
    {TailPaths : Set (ProbePath d)}
    (tailData :
      TexMatchingTailPathFrecAsymptoticData (r := r)
        (Params.tail θ) TailPaths)
    (hpath :
      ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
        let δ :=
          texMatchingRegularQuadricDialPathData
            (L := L) (d := d) (r := r) signRegion T N p hp t ht
        texMatchingUnprimedDialEffectiveTailPath
          (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ ∈ TailPaths)
    (hlimit :
      ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
        let δ :=
          texMatchingRegularQuadricDialPathData
            (L := L) (d := d) (r := r) signRegion T N p hp t ht
        tailData.limit
            (texMatchingUnprimedDialEffectiveTailPath
              (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ) =
          texMatchingUnprimedSaturatedLimitVector θ S.D t p) :
    TexMatchingRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic
      signRegion T N S := by
  intro p hp t ht
  let δ :=
    texMatchingRegularQuadricDialPathData
      (L := L) (d := d) (r := r) signRegion T N p hp t ht
  have hpath' :
      texMatchingUnprimedDialEffectiveTailPath
        (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ ∈ TailPaths := by
    simpa [δ] using hpath p hp t ht
  have hlimit' :
      tailData.limit
          (texMatchingUnprimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ) =
        texMatchingUnprimedSaturatedLimitVector θ S.D t p := by
    simpa [δ] using hlimit p hp t ht
  simpa [δ, hlimit'] using
    tailData.tendsto
      (texMatchingUnprimedDialEffectiveTailPath
        (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ)
      hpath'

/-- Selected primed tail-path asymptotic from lower-depth path-class convergence.

The recursive analytic input is independent of the selected local patch; selected
path membership and target-vector identification are the only bridge facts. -/
theorem texMatchingRegularQuadricPrimedTelescopedTailPathFrecAsymptotic_of_tailPathClass
    {L d r : Nat}
    {θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    {signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))}
    {T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U}
    {N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar}
    {TailPaths : Set (ProbePath d)}
    (tailData :
      TexMatchingTailPathFrecAsymptoticData (r := r)
        (Params.tail θ') TailPaths)
    (hpath :
      ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
        let δ :=
          texMatchingRegularQuadricDialPathData
            (L := L) (d := d) (r := r) signRegion T N p hp t ht
        texMatchingPrimedDialEffectiveTailPath
          (L := L) (d := d) (r := r) (θ' := θ') δ ∈ TailPaths)
    (hlimit :
      ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
        let δ :=
          texMatchingRegularQuadricDialPathData
            (L := L) (d := d) (r := r) signRegion T N p hp t ht
        tailData.limit
            (texMatchingPrimedDialEffectiveTailPath
              (L := L) (d := d) (r := r) (θ' := θ') δ) =
          texMatchingPrimedTelescopedLimitVector θ' t p) :
    TexMatchingRegularQuadricPrimedTelescopedTailPathFrecAsymptotic
      signRegion T N := by
  intro p hp t ht
  let δ :=
    texMatchingRegularQuadricDialPathData
      (L := L) (d := d) (r := r) signRegion T N p hp t ht
  have hpath' :
      texMatchingPrimedDialEffectiveTailPath
        (L := L) (d := d) (r := r) (θ' := θ') δ ∈ TailPaths := by
    simpa [δ] using hpath p hp t ht
  have hlimit' :
      tailData.limit
          (texMatchingPrimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ' := θ') δ) =
        texMatchingPrimedTelescopedLimitVector θ' t p := by
    simpa [δ] using hlimit p hp t ht
  simpa [δ, hlimit'] using
    tailData.tendsto
      (texMatchingPrimedDialEffectiveTailPath
        (L := L) (d := d) (r := r) (θ' := θ') δ)
      hpath'

/-- Lower-depth recursive `Frec` convergence data for the two tail path classes. -/
structure TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
    {L d r : Nat}
    (θtail θtail' : Params L d)
    (UnprimedTailPaths PrimedTailPaths : Set (ProbePath d)) : Type where
  unprimed_tail :
    TexMatchingTailPathFrecAsymptoticData (r := r)
      θtail UnprimedTailPaths
  primed_tail :
    TexMatchingTailPathFrecAsymptoticData (r := r)
      θtail' PrimedTailPaths

/-- Constructor spelling for recursive `Frec` convergence over one lower-depth path
class.  This is the smallest analytic handoff: a limit function and its convergence
proof over the chosen path class. -/
def texMatchingTailPathFrecAsymptoticData_of_tendsto
    {L d r : Nat}
    {θtail : Params L d}
    {TailPaths : Set (ProbePath d)}
    (limit : ProbePath d -> Fin d -> ℝ)
    (tendsto :
      ∀ P : ProbePath d, P ∈ TailPaths ->
        Filter.Tendsto
          (fun τ : ℝ => Frec r θtail (P τ).1 (P τ).2 τ)
          Filter.atTop
          (nhds (limit P))) :
    TexMatchingTailPathFrecAsymptoticData (r := r) θtail TailPaths where
  limit := limit
  tendsto := tendsto

/-- Bundle the two lower-depth recursive path-class convergence packages used by the
selected regular-quadric matching bridge. -/
def texMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData_of_tailData
    {L d r : Nat}
    {θtail θtail' : Params L d}
    {UnprimedTailPaths PrimedTailPaths : Set (ProbePath d)}
    (unprimed_tail :
      TexMatchingTailPathFrecAsymptoticData (r := r)
        θtail UnprimedTailPaths)
    (primed_tail :
      TexMatchingTailPathFrecAsymptoticData (r := r)
        θtail' PrimedTailPaths) :
    TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
      (r := r) θtail θtail' UnprimedTailPaths PrimedTailPaths where
  unprimed_tail := unprimed_tail
  primed_tail := primed_tail

/-- Direct constructor for the split lower-depth analytic record from two limit
functions and their recursive convergence proofs. -/
def texMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData_of_tendsto
    {L d r : Nat}
    {θtail θtail' : Params L d}
    {UnprimedTailPaths PrimedTailPaths : Set (ProbePath d)}
    (unprimedLimit : ProbePath d -> Fin d -> ℝ)
    (primedLimit : ProbePath d -> Fin d -> ℝ)
    (unprimed_tendsto :
      ∀ P : ProbePath d, P ∈ UnprimedTailPaths ->
        Filter.Tendsto
          (fun τ : ℝ => Frec r θtail (P τ).1 (P τ).2 τ)
          Filter.atTop
          (nhds (unprimedLimit P)))
    (primed_tendsto :
      ∀ P : ProbePath d, P ∈ PrimedTailPaths ->
        Filter.Tendsto
          (fun τ : ℝ => Frec r θtail' (P τ).1 (P τ).2 τ)
          Filter.atTop
          (nhds (primedLimit P))) :
    TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
      (r := r) θtail θtail' UnprimedTailPaths PrimedTailPaths :=
  texMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData_of_tailData
    (texMatchingTailPathFrecAsymptoticData_of_tendsto
      (r := r) (θtail := θtail) unprimedLimit unprimed_tendsto)
    (texMatchingTailPathFrecAsymptoticData_of_tendsto
      (r := r) (θtail := θtail') primedLimit primed_tendsto)

/-- Explicit lower-depth recursive convergence data for universal tail path classes.

This is the smallest universal analytic handoff: two limit functions and convergence
of every lower-depth path to its chosen limit. -/
structure TexMatchingRegularQuadricLowerDepthUnivTailPathFrecAnalyticData
    {L d r : Nat}
    (θtail θtail' : Params L d) : Type where
  unprimedLimit : ProbePath d -> Fin d -> ℝ
  primedLimit : ProbePath d -> Fin d -> ℝ
  unprimed_tendsto :
    ∀ P : ProbePath d,
      Filter.Tendsto
        (fun τ : ℝ => Frec r θtail (P τ).1 (P τ).2 τ)
        Filter.atTop
        (nhds (unprimedLimit P))
  primed_tendsto :
    ∀ P : ProbePath d,
      Filter.Tendsto
        (fun τ : ℝ => Frec r θtail' (P τ).1 (P τ).2 τ)
        Filter.atTop
        (nhds (primedLimit P))

/-- Compile explicit universal lower-depth convergence data to the standard split
analytic record over `Set.univ`/`Set.univ`. -/
def texMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData_of_univData
    {L d r : Nat}
    {θtail θtail' : Params L d}
    (data :
      TexMatchingRegularQuadricLowerDepthUnivTailPathFrecAnalyticData
        (r := r) θtail θtail') :
    TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
      (r := r) θtail θtail' Set.univ Set.univ :=
  texMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData_of_tendsto
    data.unprimedLimit
    data.primedLimit
    (fun P _hP => data.unprimed_tendsto P)
    (fun P _hP => data.primed_tendsto P)

/-- Restrict universal lower-depth recursive convergence to any two path classes.

This does not add arbitrary path-class convergence as a new obligation; it only reuses
the existing universal convergence proof on the path classes needed by a caller. -/
def texMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData_of_univData_restrict
    {L d r : Nat}
    {θtail θtail' : Params L d}
    {UnprimedTailPaths PrimedTailPaths : Set (ProbePath d)}
    (data :
      TexMatchingRegularQuadricLowerDepthUnivTailPathFrecAnalyticData
        (r := r) θtail θtail') :
    TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
      (r := r) θtail θtail' UnprimedTailPaths PrimedTailPaths :=
  texMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData_of_tendsto
    data.unprimedLimit
    data.primedLimit
    (fun P _hP => data.unprimed_tendsto P)
    (fun P _hP => data.primed_tendsto P)

/-- Selected effective-tail membership in the lower-depth path classes. -/
structure TexMatchingRegularQuadricLowerDepthEffectiveTailPathMemData
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (UnprimedTailPaths PrimedTailPaths : Set (ProbePath d)) : Prop where
  unprimed_path_mem :
    ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
      let δ :=
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      texMatchingUnprimedDialEffectiveTailPath
        (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ ∈ UnprimedTailPaths
  primed_path_mem :
    ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
      let δ :=
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      texMatchingPrimedDialEffectiveTailPath
        (L := L) (d := d) (r := r) (θ' := θ') δ ∈ PrimedTailPaths

/-- Selected limit-vector identification for lower-depth path-class limits. -/
structure TexMatchingRegularQuadricLowerDepthLimitIdentificationData
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma)
    (UnprimedTailPaths PrimedTailPaths : Set (ProbePath d))
    (analytic :
      TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ')
        UnprimedTailPaths PrimedTailPaths) : Prop where
  unprimed_limit_eq :
    ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
      let δ :=
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      analytic.unprimed_tail.limit
          (texMatchingUnprimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ) =
        texMatchingUnprimedSaturatedLimitVector θ S.D t p
  primed_limit_eq :
    ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
      let δ :=
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      analytic.primed_tail.limit
          (texMatchingPrimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ' := θ') δ) =
        texMatchingPrimedTelescopedLimitVector θ' t p

/-- Limit-identification constructor from selected lower-depth endpoint asymptotics.

The recursive analytic record supplies convergence to its abstract path-class limits;
the selected endpoint asymptotics supply convergence of the same effective-tail
recursions to the saturated/telescoped vectors.  Uniqueness of limits identifies the
abstract limits with the endpoint vectors. -/
theorem texMatchingRegularQuadricLowerDepthLimitIdentificationData_of_tailPathAsymptotics
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    {signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))}
    {T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U}
    {N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar}
    {varsigma : Nat -> ℝ}
    {S : TexMatchingSaturatedContributionData θ varsigma}
    {UnprimedTailPaths PrimedTailPaths : Set (ProbePath d)}
    {analytic :
      TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ')
        UnprimedTailPaths PrimedTailPaths}
    (pathMem :
      TexMatchingRegularQuadricLowerDepthEffectiveTailPathMemData
        (θ := θ) (θ' := θ') signRegion T N
        UnprimedTailPaths PrimedTailPaths)
    (hunprimed :
      TexMatchingRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic
        signRegion T N S)
    (hprimed :
      TexMatchingRegularQuadricPrimedTelescopedTailPathFrecAsymptotic
        signRegion T N) :
    TexMatchingRegularQuadricLowerDepthLimitIdentificationData
      signRegion T N S UnprimedTailPaths PrimedTailPaths analytic where
  unprimed_limit_eq := by
    intro p hp t ht
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    have hpath :
        texMatchingUnprimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ ∈
          UnprimedTailPaths := by
      simpa [δ] using pathMem.unprimed_path_mem p hp t ht
    have hanalytic :=
      analytic.unprimed_tail.tendsto
        (texMatchingUnprimedDialEffectiveTailPath
          (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ)
        hpath
    have hendpoint :
        Filter.Tendsto
          (fun τ : ℝ =>
            Frec r (Params.tail θ)
              (texMatchingUnprimedDialEffectiveTailPath
                (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ τ).1
              (texMatchingUnprimedDialEffectiveTailPath
                (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ τ).2 τ)
          Filter.atTop
          (nhds (texMatchingUnprimedSaturatedLimitVector θ S.D t p)) := by
      simpa [δ] using hunprimed p hp t ht
    exact tendsto_nhds_unique hanalytic hendpoint
  primed_limit_eq := by
    intro p hp t ht
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    have hpath :
        texMatchingPrimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ' := θ') δ ∈
          PrimedTailPaths := by
      simpa [δ] using pathMem.primed_path_mem p hp t ht
    have hanalytic :=
      analytic.primed_tail.tendsto
        (texMatchingPrimedDialEffectiveTailPath
          (L := L) (d := d) (r := r) (θ' := θ') δ)
        hpath
    have hendpoint :
        Filter.Tendsto
          (fun τ : ℝ =>
            Frec r (Params.tail θ')
              (texMatchingPrimedDialEffectiveTailPath
                (L := L) (d := d) (r := r) (θ' := θ') δ τ).1
              (texMatchingPrimedDialEffectiveTailPath
                (L := L) (d := d) (r := r) (θ' := θ') δ τ).2 τ)
          Filter.atTop
          (nhds (texMatchingPrimedTelescopedLimitVector θ' t p)) := by
      simpa [δ] using hprimed p hp t ht
    exact tendsto_nhds_unique hanalytic hendpoint

/-- Limit-identification constructor from selected peeled effective-tail endpoint
asymptotics. -/
theorem texMatchingRegularQuadricLowerDepthLimitIdentificationData_of_effectiveTailAsymptotics
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    {signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))}
    {T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U}
    {N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar}
    {varsigma : Nat -> ℝ}
    {S : TexMatchingSaturatedContributionData θ varsigma}
    {UnprimedTailPaths PrimedTailPaths : Set (ProbePath d)}
    {analytic :
      TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ')
        UnprimedTailPaths PrimedTailPaths}
    (pathMem :
      TexMatchingRegularQuadricLowerDepthEffectiveTailPathMemData
        (θ := θ) (θ' := θ') signRegion T N
        UnprimedTailPaths PrimedTailPaths)
    (hunprimed :
      TexMatchingRegularQuadricUnprimedSaturatedEffectiveTailFrecAsymptotic
        signRegion T N S)
    (hprimed :
      TexMatchingRegularQuadricPrimedTelescopedEffectiveTailFrecAsymptotic
        signRegion T N) :
    TexMatchingRegularQuadricLowerDepthLimitIdentificationData
      signRegion T N S UnprimedTailPaths PrimedTailPaths analytic :=
  texMatchingRegularQuadricLowerDepthLimitIdentificationData_of_tailPathAsymptotics
    pathMem
    (by
      intro p hp t ht
      simpa [texMatchingUnprimedDialEffectiveTailPath] using
        hunprimed p hp t ht)
    (by
      intro p hp t ht
      simpa [texMatchingPrimedDialEffectiveTailPath] using
        hprimed p hp t ht)

/-- Limit-identification constructor from selected full closed-recursion limits.  The
head recursion layer is peeled by the exact `Frec_succ` identity, then limits are
identified by uniqueness. -/
theorem texMatchingRegularQuadricLowerDepthLimitIdentificationData_of_closedRecursionLimits
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    {signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))}
    {T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U}
    {N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar}
    {varsigma : Nat -> ℝ}
    {S : TexMatchingSaturatedContributionData θ varsigma}
    {UnprimedTailPaths PrimedTailPaths : Set (ProbePath d)}
    {analytic :
      TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ')
        UnprimedTailPaths PrimedTailPaths}
    (pathMem :
      TexMatchingRegularQuadricLowerDepthEffectiveTailPathMemData
        (θ := θ) (θ' := θ') signRegion T N
        UnprimedTailPaths PrimedTailPaths)
    (hlimits :
      TexMatchingRegularQuadricClosedRecursionLimitObligation
        signRegion T N S) :
    TexMatchingRegularQuadricLowerDepthLimitIdentificationData
      signRegion T N S UnprimedTailPaths PrimedTailPaths analytic :=
  texMatchingRegularQuadricLowerDepthLimitIdentificationData_of_effectiveTailAsymptotics
    pathMem
    (by
      intro p hp t ht
      let δ :=
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      have hfull :
          Filter.Tendsto
            (fun τ : ℝ =>
              Frec r θ (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ)
            Filter.atTop
            (nhds (texMatchingUnprimedSaturatedLimitVector θ S.D t p)) := by
        simpa [δ] using hlimits.unprimed_tendsto p hp t ht
      have hfun :
          (fun τ : ℝ =>
            Frec r θ (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ) =
          (fun τ : ℝ =>
            let q :=
              texMatchingUnprimedDialEffectiveTailPoint
                (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ τ
            Frec r (Params.tail θ) q.1 q.2 τ) := by
        funext τ
        exact Frec_succ_paramsFirstLayerEffectivePoint r θ
          (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ
      simpa [hfun] using hfull)
    (by
      intro p hp t ht
      let δ :=
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      have hfull :
          Filter.Tendsto
            (fun τ : ℝ =>
              Frec r θ' (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ)
            Filter.atTop
            (nhds (texMatchingPrimedTelescopedLimitVector θ' t p)) := by
        simpa [δ] using hlimits.primed_tendsto p hp t ht
      have hfun :
          (fun τ : ℝ =>
            Frec r θ' (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ) =
          (fun τ : ℝ =>
            let q :=
              texMatchingPrimedDialEffectiveTailPoint
                (L := L) (d := d) (r := r) (θ' := θ') δ τ
            Frec r (Params.tail θ') q.1 q.2 τ) := by
        funext τ
        exact Frec_succ_paramsFirstLayerEffectivePoint r θ'
          (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ
      simpa [hfun] using hfull)

/-- Package selected lower-depth limit-vector identifications for universal path
classes.

The universal lower-depth analytic record supplies the selected `Tendsto` facts; the
two explicit equality hypotheses identify its abstract selected limits with the
saturated/telescoped matching vectors. -/
def texMatchingRegularQuadricLowerDepthLimitIdentificationData_of_univAnalytic
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    {signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))}
    {T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U}
    {N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar}
    {varsigma : Nat -> ℝ}
    {S : TexMatchingSaturatedContributionData θ varsigma}
    (analytic :
      TexMatchingRegularQuadricLowerDepthUnivTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ'))
    (unprimed_limit_eq :
      ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
        let δ :=
          texMatchingRegularQuadricDialPathData
            (L := L) (d := d) (r := r) signRegion T N p hp t ht
        analytic.unprimedLimit
            (texMatchingUnprimedDialEffectiveTailPath
              (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ) =
          texMatchingUnprimedSaturatedLimitVector θ S.D t p)
    (primed_limit_eq :
      ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
        let δ :=
          texMatchingRegularQuadricDialPathData
            (L := L) (d := d) (r := r) signRegion T N p hp t ht
        analytic.primedLimit
            (texMatchingPrimedDialEffectiveTailPath
              (L := L) (d := d) (r := r) (θ' := θ') δ) =
          texMatchingPrimedTelescopedLimitVector θ' t p) :
    TexMatchingRegularQuadricLowerDepthLimitIdentificationData
      signRegion T N S Set.univ Set.univ
      (texMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData_of_univData
        (r := r) analytic) where
  unprimed_limit_eq := by
    intro p hp t ht
    simpa using unprimed_limit_eq p hp t ht
  primed_limit_eq := by
    intro p hp t ht
    simpa using primed_limit_eq p hp t ht

/-- The universal lower-depth analytic record gives the selected unprimed tail-path
asymptotic once its selected abstract limit is identified with the saturated vector. -/
theorem texMatchingRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic_of_univAnalytic
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    {signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))}
    {T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U}
    {N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar}
    {varsigma : Nat -> ℝ}
    {S : TexMatchingSaturatedContributionData θ varsigma}
    (analytic :
      TexMatchingRegularQuadricLowerDepthUnivTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ'))
    (unprimed_limit_eq :
      ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
        let δ :=
          texMatchingRegularQuadricDialPathData
            (L := L) (d := d) (r := r) signRegion T N p hp t ht
        analytic.unprimedLimit
            (texMatchingUnprimedDialEffectiveTailPath
              (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ) =
          texMatchingUnprimedSaturatedLimitVector θ S.D t p) :
    TexMatchingRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic
      signRegion T N S := by
  intro p hp t ht
  let δ :=
    texMatchingRegularQuadricDialPathData
      (L := L) (d := d) (r := r) signRegion T N p hp t ht
  have hlimit :
      analytic.unprimedLimit
          (texMatchingUnprimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ) =
        texMatchingUnprimedSaturatedLimitVector θ S.D t p := by
    simpa [δ] using unprimed_limit_eq p hp t ht
  simpa [δ, hlimit] using
    analytic.unprimed_tendsto
      (texMatchingUnprimedDialEffectiveTailPath
        (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ)

/-- The universal lower-depth analytic record gives the selected primed tail-path
asymptotic once its selected abstract limit is identified with the telescoped vector. -/
theorem texMatchingRegularQuadricPrimedTelescopedTailPathFrecAsymptotic_of_univAnalytic
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    {signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))}
    {T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U}
    {N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar}
    (analytic :
      TexMatchingRegularQuadricLowerDepthUnivTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ'))
    (primed_limit_eq :
      ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
        let δ :=
          texMatchingRegularQuadricDialPathData
            (L := L) (d := d) (r := r) signRegion T N p hp t ht
        analytic.primedLimit
            (texMatchingPrimedDialEffectiveTailPath
              (L := L) (d := d) (r := r) (θ' := θ') δ) =
          texMatchingPrimedTelescopedLimitVector θ' t p) :
    TexMatchingRegularQuadricPrimedTelescopedTailPathFrecAsymptotic
      signRegion T N := by
  intro p hp t ht
  let δ :=
    texMatchingRegularQuadricDialPathData
      (L := L) (d := d) (r := r) signRegion T N p hp t ht
  have hlimit :
      analytic.primedLimit
          (texMatchingPrimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ' := θ') δ) =
        texMatchingPrimedTelescopedLimitVector θ' t p := by
    simpa [δ] using primed_limit_eq p hp t ht
  simpa [δ, hlimit] using
    analytic.primed_tendsto
      (texMatchingPrimedDialEffectiveTailPath
        (L := L) (d := d) (r := r) (θ' := θ') δ)

/-- Universal selected effective-tail path membership. -/
def texMatchingRegularQuadricLowerDepthEffectiveTailPathMemData_of_paths_univ
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar) :
    TexMatchingRegularQuadricLowerDepthEffectiveTailPathMemData
      (θ := θ) (θ' := θ') signRegion T N Set.univ Set.univ where
  unprimed_path_mem := by
    intro _p _hp _t _ht
    exact Set.mem_univ _
  primed_path_mem := by
    intro _p _hp _t _ht
    exact Set.mem_univ _

/-- Bundled lower-depth tail-path provider for the selected regular-quadric dials.

This isolates the non-mechanical recursive analytic input from the local-patch
constructor: lower-depth convergence is supplied over path classes, while the selected
dial bridge proves path membership and identifies the abstract limits with the concrete
matching vectors. -/
structure TexMatchingRegularQuadricLowerDepthTailPathFrecProviderData
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma)
    (UnprimedTailPaths PrimedTailPaths : Set (ProbePath d)) : Type where
  unprimed_tail :
    TexMatchingTailPathFrecAsymptoticData (r := r)
      (Params.tail θ) UnprimedTailPaths
  primed_tail :
    TexMatchingTailPathFrecAsymptoticData (r := r)
      (Params.tail θ') PrimedTailPaths
  unprimed_path_mem :
    ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
      let δ :=
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      texMatchingUnprimedDialEffectiveTailPath
        (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ ∈ UnprimedTailPaths
  primed_path_mem :
    ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
      let δ :=
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      texMatchingPrimedDialEffectiveTailPath
        (L := L) (d := d) (r := r) (θ' := θ') δ ∈ PrimedTailPaths
  unprimed_limit_eq :
    ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
      let δ :=
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      unprimed_tail.limit
          (texMatchingUnprimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ) =
        texMatchingUnprimedSaturatedLimitVector θ S.D t p
  primed_limit_eq :
    ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
      let δ :=
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      primed_tail.limit
          (texMatchingPrimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ' := θ') δ) =
        texMatchingPrimedTelescopedLimitVector θ' t p

/-- Compile the split lower-depth analytic, path-membership, and limit-identification
records into the existing bundled selected regular-quadric provider. -/
def texMatchingRegularQuadricLowerDepthTailPathFrecProviderData_of_parts
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    {signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))}
    {T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U}
    {N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar}
    {varsigma : Nat -> ℝ}
    {S : TexMatchingSaturatedContributionData θ varsigma}
    {UnprimedTailPaths PrimedTailPaths : Set (ProbePath d)}
    (analytic :
      TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ')
        UnprimedTailPaths PrimedTailPaths)
    (pathMem :
      TexMatchingRegularQuadricLowerDepthEffectiveTailPathMemData
        (θ := θ) (θ' := θ') signRegion T N
        UnprimedTailPaths PrimedTailPaths)
    (limits :
      TexMatchingRegularQuadricLowerDepthLimitIdentificationData
        signRegion T N S UnprimedTailPaths PrimedTailPaths analytic) :
    TexMatchingRegularQuadricLowerDepthTailPathFrecProviderData
      signRegion T N S UnprimedTailPaths PrimedTailPaths where
  unprimed_tail := analytic.unprimed_tail
  primed_tail := analytic.primed_tail
  unprimed_path_mem := pathMem.unprimed_path_mem
  primed_path_mem := pathMem.primed_path_mem
  unprimed_limit_eq := limits.unprimed_limit_eq
  primed_limit_eq := limits.primed_limit_eq

/-- Universal-path compiler for the selected lower-depth provider.  Only the recursive
tail `Frec` data and selected limit-vector identifications remain. -/
def texMatchingRegularQuadricLowerDepthTailPathFrecProviderData_of_paths_univ
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma)
    (analytic :
      TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ') Set.univ Set.univ)
    (limits :
      TexMatchingRegularQuadricLowerDepthLimitIdentificationData
        signRegion T N S Set.univ Set.univ analytic) :
    TexMatchingRegularQuadricLowerDepthTailPathFrecProviderData
      signRegion T N S Set.univ Set.univ :=
  texMatchingRegularQuadricLowerDepthTailPathFrecProviderData_of_parts
    analytic
    (texMatchingRegularQuadricLowerDepthEffectiveTailPathMemData_of_paths_univ
      (θ := θ) signRegion T N)
    limits

/-- Extract the selected unprimed tail-path asymptotic from a lower-depth provider. -/
theorem texMatchingRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic_of_lowerDepthProvider
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    {signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))}
    {T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U}
    {N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar}
    {varsigma : Nat -> ℝ}
    {S : TexMatchingSaturatedContributionData θ varsigma}
    {UnprimedTailPaths PrimedTailPaths : Set (ProbePath d)}
    (provider :
      TexMatchingRegularQuadricLowerDepthTailPathFrecProviderData
        signRegion T N S UnprimedTailPaths PrimedTailPaths) :
    TexMatchingRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic
      signRegion T N S :=
  texMatchingRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic_of_tailPathClass
    provider.unprimed_tail provider.unprimed_path_mem provider.unprimed_limit_eq

/-- Extract the selected primed tail-path asymptotic from a lower-depth provider. -/
theorem texMatchingRegularQuadricPrimedTelescopedTailPathFrecAsymptotic_of_lowerDepthProvider
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    {signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))}
    {T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U}
    {N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar}
    {varsigma : Nat -> ℝ}
    {S : TexMatchingSaturatedContributionData θ varsigma}
    {UnprimedTailPaths PrimedTailPaths : Set (ProbePath d)}
    (provider :
      TexMatchingRegularQuadricLowerDepthTailPathFrecProviderData
        signRegion T N S UnprimedTailPaths PrimedTailPaths) :
    TexMatchingRegularQuadricPrimedTelescopedTailPathFrecAsymptotic
      signRegion T N :=
  texMatchingRegularQuadricPrimedTelescopedTailPathFrecAsymptotic_of_tailPathClass
    provider.primed_tail provider.primed_path_mem provider.primed_limit_eq

/-- Selected effective-tail convergence data over only the regular-quadric product
neighborhood.

This is smaller than a recursive tail-path theorem over an arbitrary path class: it
records explicit limit functions only for the canonical selected effective-tail paths
indexed by `(p, t) ∈ N.Uq × N.J`. -/
structure TexMatchingRegularQuadricSelectedEffectiveTailFrecAnalyticData
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar) : Type where
  unprimedLimit :
    ∀ (p : ProbePair d), p ∈ N.Uq -> ∀ (t : ℝ), t ∈ N.J -> Fin d -> ℝ
  primedLimit :
    ∀ (p : ProbePair d), p ∈ N.Uq -> ∀ (t : ℝ), t ∈ N.J -> Fin d -> ℝ
  unprimed_tendsto :
    ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
      let δ :=
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      Filter.Tendsto
        (fun τ : ℝ =>
          let q :=
            texMatchingUnprimedDialEffectiveTailPath
              (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ τ
          Frec r (Params.tail θ) q.1 q.2 τ)
        Filter.atTop
        (nhds (unprimedLimit p hp t ht))
  primed_tendsto :
    ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
      let δ :=
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      Filter.Tendsto
        (fun τ : ℝ =>
          let q :=
            texMatchingPrimedDialEffectiveTailPath
              (L := L) (d := d) (r := r) (θ' := θ') δ τ
          Frec r (Params.tail θ') q.1 q.2 τ)
        Filter.atTop
        (nhds (primedLimit p hp t ht))

/-- Identification of the selected effective-tail analytic limits with the concrete
regular-quadric saturated/telescoped limit vectors. -/
structure TexMatchingRegularQuadricSelectedEffectiveTailLimitIdentificationData
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma)
    (analytic :
      TexMatchingRegularQuadricSelectedEffectiveTailFrecAnalyticData
        (θ := θ) (θ' := θ') signRegion T N) : Prop where
  unprimed_limit_eq :
    ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
      analytic.unprimedLimit p hp t ht =
        texMatchingUnprimedSaturatedLimitVector θ S.D t p
  primed_limit_eq :
    ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
      analytic.primedLimit p hp t ht =
        texMatchingPrimedTelescopedLimitVector θ' t p

/-- Restrict lower-depth path-class convergence to the selected effective-tail paths.

The recursive handoff may know convergence on a larger path class.  This constructor
chooses the selected effective-tail paths as the selected analytic limits, using only
path membership in those lower-depth classes. -/
noncomputable def texMatchingRegularQuadricSelectedEffectiveTailFrecAnalyticData_of_lowerDepthTailPath
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    {signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))}
    {T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U}
    {N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar}
    {UnprimedTailPaths PrimedTailPaths : Set (ProbePath d)}
    (analytic :
      TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ')
        UnprimedTailPaths PrimedTailPaths)
    (pathMem :
      TexMatchingRegularQuadricLowerDepthEffectiveTailPathMemData
        (θ := θ) (θ' := θ') signRegion T N
        UnprimedTailPaths PrimedTailPaths) :
    TexMatchingRegularQuadricSelectedEffectiveTailFrecAnalyticData
      (θ := θ) (θ' := θ') signRegion T N where
  unprimedLimit := fun p hp t ht =>
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    analytic.unprimed_tail.limit
      (texMatchingUnprimedDialEffectiveTailPath
        (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ)
  primedLimit := fun p hp t ht =>
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    analytic.primed_tail.limit
      (texMatchingPrimedDialEffectiveTailPath
        (L := L) (d := d) (r := r) (θ' := θ') δ)
  unprimed_tendsto := by
    intro p hp t ht
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    have hpath :
        texMatchingUnprimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ ∈
          UnprimedTailPaths := by
      simpa [δ] using pathMem.unprimed_path_mem p hp t ht
    simpa [δ] using
      analytic.unprimed_tail.tendsto
        (texMatchingUnprimedDialEffectiveTailPath
          (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ)
        hpath
  primed_tendsto := by
    intro p hp t ht
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    have hpath :
        texMatchingPrimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ' := θ') δ ∈
          PrimedTailPaths := by
      simpa [δ] using pathMem.primed_path_mem p hp t ht
    simpa [δ] using
      analytic.primed_tail.tendsto
        (texMatchingPrimedDialEffectiveTailPath
          (L := L) (d := d) (r := r) (θ' := θ') δ)
        hpath

/-- Selected effective-tail limit identification from selected closed-recursion
limits.  The full recursion limits are peeled by the exact first-layer identities and
then compared with the selected effective-tail analytic limits by uniqueness. -/
theorem texMatchingRegularQuadricSelectedEffectiveTailLimitIdentificationData_of_closedRecursionLimits
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    {signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))}
    {T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U}
    {N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar}
    {varsigma : Nat -> ℝ}
    {S : TexMatchingSaturatedContributionData θ varsigma}
    (analytic :
      TexMatchingRegularQuadricSelectedEffectiveTailFrecAnalyticData
        (θ := θ) (θ' := θ') signRegion T N)
    (hlimits :
      TexMatchingRegularQuadricClosedRecursionLimitObligation signRegion T N S) :
    TexMatchingRegularQuadricSelectedEffectiveTailLimitIdentificationData
      signRegion T N S analytic where
  unprimed_limit_eq := by
    intro p hp t ht
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    have hfull :
        Filter.Tendsto
          (fun τ : ℝ =>
            Frec r θ (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ)
          Filter.atTop
          (nhds (texMatchingUnprimedSaturatedLimitVector θ S.D t p)) := by
      simpa [δ] using hlimits.unprimed_tendsto p hp t ht
    have hfun :
        (fun τ : ℝ =>
          Frec r θ (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ) =
        (fun τ : ℝ =>
          let q :=
            texMatchingUnprimedDialEffectiveTailPath
              (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ τ
          Frec r (Params.tail θ) q.1 q.2 τ) := by
      funext τ
      exact Frec_succ_paramsFirstLayerEffectivePoint r θ
        (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ
    have hendpoint :
        Filter.Tendsto
          (fun τ : ℝ =>
            let q :=
              texMatchingUnprimedDialEffectiveTailPath
                (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ τ
            Frec r (Params.tail θ) q.1 q.2 τ)
          Filter.atTop
          (nhds (texMatchingUnprimedSaturatedLimitVector θ S.D t p)) := by
      simpa [hfun] using hfull
    exact tendsto_nhds_unique (analytic.unprimed_tendsto p hp t ht) hendpoint
  primed_limit_eq := by
    intro p hp t ht
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    have hfull :
        Filter.Tendsto
          (fun τ : ℝ =>
            Frec r θ' (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ)
          Filter.atTop
          (nhds (texMatchingPrimedTelescopedLimitVector θ' t p)) := by
      simpa [δ] using hlimits.primed_tendsto p hp t ht
    have hfun :
        (fun τ : ℝ =>
          Frec r θ' (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ) =
        (fun τ : ℝ =>
          let q :=
            texMatchingPrimedDialEffectiveTailPath
              (L := L) (d := d) (r := r) (θ' := θ') δ τ
          Frec r (Params.tail θ') q.1 q.2 τ) := by
      funext τ
      exact Frec_succ_paramsFirstLayerEffectivePoint r θ'
        (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ
    have hendpoint :
        Filter.Tendsto
          (fun τ : ℝ =>
            let q :=
              texMatchingPrimedDialEffectiveTailPath
                (L := L) (d := d) (r := r) (θ' := θ') δ τ
            Frec r (Params.tail θ') q.1 q.2 τ)
          Filter.atTop
          (nhds (texMatchingPrimedTelescopedLimitVector θ' t p)) := by
      simpa [hfun] using hfull
    exact tendsto_nhds_unique (analytic.primed_tendsto p hp t ht) hendpoint

/-- The closed-recursion asymptotics discharge the original regular-quadric observable
limit-vector obligation. -/
theorem texMatchingRegularQuadricLimitVectorObligation_of_closedRecursionLimits
    {L d r : Nat} (hr_pos : 0 < r)
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma)
    (hlimits :
      TexMatchingRegularQuadricClosedRecursionLimitObligation signRegion T N S) :
    TexMatchingRegularQuadricLimitVectorObligation signRegion T N S := by
  intro p hp t ht T0 hobs
  let δ :=
    texMatchingRegularQuadricDialPathData
      (L := L) (d := d) (r := r) signRegion T N p hp t ht
  have hfrec_eq :
      (fun τ : ℝ =>
        Frec r θ (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ)
        =ᶠ[Filter.atTop]
      (fun τ : ℝ =>
        Frec r θ' (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ) := by
    filter_upwards [Filter.Ioi_mem_atTop T0] with τ hτ
    exact texMatching_frec_eq_on_path_of_observableAgreement
      (L := L + 1) (d := d) (r := r) hr_pos
      (P := DialPathData.probe δ) hobs τ hτ
  have hprimed_as_unprimed :
      Filter.Tendsto
        (fun τ : ℝ =>
          Frec r θ (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ)
        Filter.atTop
        (nhds (texMatchingPrimedTelescopedLimitVector θ' t p)) := by
    intro s hs
    have hprimed_mem := (hlimits.primed_tendsto p hp t ht) hs
    rw [Filter.mem_map] at hprimed_mem ⊢
    filter_upwards [hfrec_eq, hprimed_mem] with τ hfg hmem
    simpa [hfg] using hmem
  exact tendsto_nhds_unique (hlimits.unprimed_tendsto p hp t ht) hprimed_as_unprimed

/-- Local-patch specialization of the regular-quadric limit-vector theorem. -/
abbrev TexMatchingLocalPatchRegularQuadricLimitVectorObligation
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Prop :=
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let N :=
    texMatchingProductNeighborhoodData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let S :=
    texMatchingSaturatedContributionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  TexMatchingRegularQuadricLimitVectorObligation signRegion T N S

/-- Backwards-compatible local-patch name used by first-layer matching. -/
abbrev TexMatchingLocalPatchRegularQuadricLimitObligation
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Prop :=
  TexMatchingLocalPatchRegularQuadricLimitVectorObligation
    hL hr hstep endpoint D localRegion

/-- Local-patch spelling of the unprimed saturated dial-level `Frec` tendsto theorem
over the canonical `region/signRegion/T/S` generated by the local quadric patch. -/
abbrev TexMatchingLocalPatchUnprimedSaturatedDialFrecTendsto
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Prop :=
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let S :=
    texMatchingSaturatedContributionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  TexMatchingUnprimedSaturatedDialFrecTendsto (θ := θ) (θ' := θ') T S

/-- Local-patch spelling of the peeled unprimed saturated `Frec` asymptotic.

This is the same local patch as
`TexMatchingLocalPatchUnprimedSaturatedDialFrecTendsto`, but after the exact first
recursion layer has been removed. -/
abbrev TexMatchingLocalPatchUnprimedSaturatedEffectiveTailFrecAsymptotic
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Prop :=
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let S :=
    texMatchingSaturatedContributionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  TexMatchingUnprimedSaturatedEffectiveTailFrecAsymptotic
    (θ := θ) (θ' := θ') T S

/-- Local-patch spelling of the lower-depth unprimed tail-path `Frec` limit.

This is the explicit path form of
`TexMatchingLocalPatchUnprimedSaturatedEffectiveTailFrecAsymptotic`: callers provide
the tail recursion along the peeled unprimed effective-tail path. -/
abbrev TexMatchingLocalPatchUnprimedSaturatedTailPathFrecAsymptotic
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Prop :=
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let S :=
    texMatchingSaturatedContributionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  ∀ δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ)),
    (δ.base, δ.t) ∈ T.Ustar ->
    Filter.Tendsto
      (fun τ : ℝ =>
        let q :=
          texMatchingUnprimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ τ
        Frec r (Params.tail θ) q.1 q.2 τ)
      Filter.atTop
      (nhds (texMatchingUnprimedSaturatedLimitVector θ S.D δ.t δ.base))

/-- Direct selected-regular-quadric dial bridge from path membership and the
pointwise limit theorem.

This is the non-circular bridge constructor: unlike the matched-tail provider route,
it does not require `FirstLayerMatchedData θ θ'`. -/
noncomputable def texMatchingDialPathLimitBridgeData_of_regularQuadricLimit
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma)
    (hdial_mem :
      ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
        DialPathData.probe
          (texMatchingRegularQuadricDialPathData
            (L := L) (d := d) (r := r) signRegion T N p hp t ht) ∈ D.Paths)
    (hlimit :
      TexMatchingRegularQuadricLimitVectorObligation signRegion T N S) :
    TexMatchingDialPathLimitBridgeData D N S := by
  exact
    { dial := fun p hp t ht =>
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      dial_base := by
        intro p hp t ht
        exact texMatchingRegularQuadricDialPathData_base signRegion T N p hp t ht
      dial_target := by
        intro p hp t ht
        exact texMatchingRegularQuadricDialPathData_target signRegion T N p hp t ht
      path_mem := by
        intro p hp t ht
        exact hdial_mem p hp t ht
      limit_of_observable := by
        intro p hp t ht T0 hobs
        exact hlimit p hp t ht T0 hobs }

/-- Generic selected-regular-quadric dial path-membership obligation.

This is the local-patch-independent surface for path availability: the caller only
mentions the selected `signRegion/T/N` dials and the current `IDLData.Paths`. -/
abbrev TexMatchingRegularQuadricDialMemObligation
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar) : Prop :=
  ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
    DialPathData.probe
      (texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht) ∈ D.Paths

/-- Generic selected regular-quadric membership from universal paths.

This is the local-patch-independent version of the existing local constructor: it only
mentions the selected `signRegion/T/N` dials and `D.Paths = Set.univ`. -/
theorem texMatchingRegularQuadricDialMemObligation_of_paths_univ
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (hPaths : D.Paths = Set.univ)
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar) :
    TexMatchingRegularQuadricDialMemObligation D signRegion T N := by
  intro p hp t ht
  exact
    texMatching_dialPath_mem_of_paths_univ D hPaths
      (texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht)

/-- Generic selected regular-quadric membership in a swept realized-tail path class. -/
abbrev TexMatchingRegularQuadricDialRealizedTailMemObligation
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (_D : IDLData (L + 1) d r θ θ')
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    {Lfull : Nat}
    (θfull : Params (Lfull + 1) d)
    (FullPaths : Set (ProbePath d)) : Prop :=
  ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
    DialPathData.probe
      (texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht) ∈
      realizedTailPathSet r θfull FullPaths

/-- Generic selected regular-quadric membership from direct selected membership in the
swept realized-tail class. -/
theorem texMatchingRegularQuadricDialMemObligation_of_realizedTailMem
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    {Lfull : Nat}
    (θfull : Params (Lfull + 1) d)
    (FullPaths : Set (ProbePath d))
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (realized :
      TexMatchingRegularQuadricDialRealizedTailMemObligation
        D signRegion T N θfull FullPaths) :
    TexMatchingRegularQuadricDialMemObligation D signRegion T N := by
  intro p hp t ht
  rw [hPaths]
  exact realized p hp t ht

/-- Selected effective-tail membership in realized-tail path classes from selected
dial membership.  The primed class is intentionally the `θ'` realized class; transporting
it to the swept `θ` class requires first-layer matching. -/
theorem texMatchingRegularQuadricLowerDepthEffectiveTailPathMemData_of_realizedTailPathSet
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (hdial_mem : TexMatchingRegularQuadricDialMemObligation D signRegion T N) :
    TexMatchingRegularQuadricLowerDepthEffectiveTailPathMemData
      (θ := θ) (θ' := θ') signRegion T N
      (realizedTailPathSet r θ D.Paths)
      (realizedTailPathSet r θ' D.Paths) where
  unprimed_path_mem := by
    intro p hp t ht
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    exact
      texMatchingUnprimedDialEffectiveTailPath_mem_realizedTailPathSet
        (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ
        (by simpa [δ] using hdial_mem p hp t ht)
  primed_path_mem := by
    intro p hp t ht
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    exact
      texMatchingPrimedDialEffectiveTailPath_mem_realizedTailPathSet
        (L := L) (d := d) (r := r) (θ' := θ') δ
        (by simpa [δ] using hdial_mem p hp t ht)

/-- Realized-tail path-membership compiler for selected lower-depth providers.  The
primed path class is the honest `θ'` realized class; use a separate matching transport
if the caller needs the swept `θ` class on both sides. -/
def texMatchingRegularQuadricLowerDepthTailPathFrecProviderData_of_realizedTailPathSet
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma)
    (hdial_mem : TexMatchingRegularQuadricDialMemObligation D signRegion T N)
    (analytic :
      TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ')
        (realizedTailPathSet r θ D.Paths)
        (realizedTailPathSet r θ' D.Paths))
    (limits :
      TexMatchingRegularQuadricLowerDepthLimitIdentificationData
        signRegion T N S
        (realizedTailPathSet r θ D.Paths)
        (realizedTailPathSet r θ' D.Paths)
        analytic) :
    TexMatchingRegularQuadricLowerDepthTailPathFrecProviderData
      signRegion T N S
      (realizedTailPathSet r θ D.Paths)
      (realizedTailPathSet r θ' D.Paths) :=
  texMatchingRegularQuadricLowerDepthTailPathFrecProviderData_of_parts
    analytic
    (texMatchingRegularQuadricLowerDepthEffectiveTailPathMemData_of_realizedTailPathSet
      D signRegion T N hdial_mem)
    limits

/-- Local-patch path-membership obligation for the canonical regular-quadric dials
selected by the local region/trichotomy/product constructors. -/
abbrev TexMatchingLocalPatchRegularQuadricDialMemObligation
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Prop :=
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let N :=
    texMatchingProductNeighborhoodData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
    DialPathData.probe
      (texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht) ∈ D.Paths

/-- Local-patch dial membership from the smaller generic selected-dial membership
surface over the already constructed `signRegion/T/N`. -/
theorem texMatchingLocalPatchRegularQuadricDialMemObligation_of_selectedDial
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (hmem :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      TexMatchingRegularQuadricDialMemObligation D signRegion T N) :
    TexMatchingLocalPatchRegularQuadricDialMemObligation
      hL hr hstep endpoint D localRegion := by
  dsimp [TexMatchingLocalPatchRegularQuadricDialMemObligation,
    TexMatchingRegularQuadricDialMemObligation] at hmem ⊢
  exact hmem

/-- In the top-level universal-path case, the canonical local-patch regular-quadric
dials are mechanically available in `D.Paths`. -/
theorem texMatchingLocalPatchRegularQuadricDialMemObligation_of_paths_univ
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (hPaths : D.Paths = Set.univ)
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) :
    TexMatchingLocalPatchRegularQuadricDialMemObligation
      hL hr hstep endpoint D localRegion := by
  dsimp [TexMatchingLocalPatchRegularQuadricDialMemObligation]
  intro p hp t ht
  exact
    texMatching_dialPath_mem_of_paths_univ D hPaths
      (texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r)
        (texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
        (texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texMatchingSignRegionData_of_region
            (L := L) (d := d) (r := r) hr hstep endpoint D
            (texRegionConstructionData_of_IDLData_of_localPatch
              (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion)))
        (texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
        p hp t ht)

/-- Direct realized-tail path-membership obligation for the canonical local regular-quadric
dials.

This is the smaller recursive handoff surface: instead of separately choosing source
paths and realization witnesses, a sweep provider may prove the selected dial paths
already belong to the swept `realizedTailPathSet`. -/
abbrev TexMatchingLocalPatchRegularQuadricDialRealizedTailMemObligation
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (θfull : Params (L + 2) d)
    (FullPaths : Set (ProbePath d)) : Prop :=
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let N :=
    texMatchingProductNeighborhoodData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
    DialPathData.probe
      (texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht) ∈
      realizedTailPathSet r θfull FullPaths

/-- Source-path realization data for the selected local regular-quadric dials when the
current recursive path class is a swept `realizedTailPathSet`.

For each canonical local-patch dial, the remaining inverse-sweep statement is to choose
an available source path from the previous depth and prove that the selected dial is its
realized tail path. -/
structure TexMatchingLocalPatchRegularQuadricDialRealizedTailMemData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (θfull : Params (L + 2) d)
    (FullPaths : Set (ProbePath d)) : Type where
  source :
    ∀ (p : ProbePair d), p ∈
        (let region :=
          texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
        let N :=
          texMatchingProductNeighborhoodData_of_region
            (L := L) (d := d) (r := r) hr hstep endpoint D region
        N.Uq) ->
      ∀ (t : ℝ), t ∈
        (let region :=
          texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
        let N :=
          texMatchingProductNeighborhoodData_of_region
            (L := L) (d := d) (r := r) hr hstep endpoint D region
        N.J) ->
      ProbePath d
  source_mem :
    ∀ (p : ProbePair d) hp (t : ℝ) ht, source p hp t ht ∈ FullPaths
  realized :
    ∀ (p : ProbePair d) hp (t : ℝ) ht,
      Nonempty
        (RealizationData r (Params.headValue θfull) (Params.headAttention θfull)
          (DialPathData.probe
            (let region :=
              texRegionConstructionData_of_IDLData_of_localPatch
                (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
            let signRegion :=
              texMatchingSignRegionData_of_region
                (L := L) (d := d) (r := r) hr hstep endpoint D region
            let T :=
              texTrichotomyConstructionData_of_signRegion
                (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
            let N :=
              texMatchingProductNeighborhoodData_of_region
                (L := L) (d := d) (r := r) hr hstep endpoint D region
            texMatchingRegularQuadricDialPathData
              (L := L) (d := d) (r := r) signRegion T N p hp t ht))
          (source p hp t ht))

/-- The explicit source/realization witness package implies the smaller direct
realized-tail membership obligation. -/
theorem texMatchingLocalPatchRegularQuadricDialRealizedTailMemObligation_of_data
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (θfull : Params (L + 2) d)
    (FullPaths : Set (ProbePath d))
    (realized :
      TexMatchingLocalPatchRegularQuadricDialRealizedTailMemData
        hL hr hstep endpoint D localRegion θfull FullPaths) :
    TexMatchingLocalPatchRegularQuadricDialRealizedTailMemObligation
      hL hr hstep endpoint D localRegion θfull FullPaths := by
  dsimp [TexMatchingLocalPatchRegularQuadricDialRealizedTailMemObligation]
  intro p hp t ht
  exact
    texMatching_dialPath_mem_of_realizedTailPathSet
      (texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r)
        (texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
        (texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texMatchingSignRegionData_of_region
            (L := L) (d := d) (r := r) hr hstep endpoint D
            (texRegionConstructionData_of_IDLData_of_localPatch
              (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion)))
        (texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
        p hp t ht)
      (realized.source p hp t ht)
      (realized.source_mem p hp t ht)
      (realized.realized p hp t ht)

/-- Recursive swept-path constructor from direct selected-dial membership in the swept
`realizedTailPathSet`.

This removes the source-path bookkeeping from the matching side.  The remaining analytic
statement is exactly
`TexMatchingLocalPatchRegularQuadricDialRealizedTailMemObligation`. -/
theorem texMatchingLocalPatchRegularQuadricDialMemObligation_of_realizedTailMemObligation
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (θfull : Params (L + 2) d)
    (FullPaths : Set (ProbePath d))
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (realized :
      TexMatchingLocalPatchRegularQuadricDialRealizedTailMemObligation
        hL hr hstep endpoint D localRegion θfull FullPaths) :
    TexMatchingLocalPatchRegularQuadricDialMemObligation
      hL hr hstep endpoint D localRegion := by
  dsimp [TexMatchingLocalPatchRegularQuadricDialMemObligation,
    TexMatchingLocalPatchRegularQuadricDialRealizedTailMemObligation] at realized ⊢
  intro p hp t ht
  rw [hPaths]
  exact realized p hp t ht

/-- Recursive swept-path constructor for the local-patch regular-quadric dial
membership obligation.

This is the common recursive case after sweep: if the current `D.Paths` is the realized
tail path class from the previous depth, path membership reduces to the explicit
per-dial inverse-sweep realization data. -/
theorem texMatchingLocalPatchRegularQuadricDialMemObligation_of_realizedTailPathSet
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (θfull : Params (L + 2) d)
    (FullPaths : Set (ProbePath d))
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (realized :
      TexMatchingLocalPatchRegularQuadricDialRealizedTailMemData
        hL hr hstep endpoint D localRegion θfull FullPaths) :
    TexMatchingLocalPatchRegularQuadricDialMemObligation
      hL hr hstep endpoint D localRegion := by
  exact
    texMatchingLocalPatchRegularQuadricDialMemObligation_of_realizedTailMemObligation
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      θfull FullPaths hPaths
      (texMatchingLocalPatchRegularQuadricDialRealizedTailMemObligation_of_data
        (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
        θfull FullPaths realized)

/-- Selected-dial lower-depth unprimed tail-path `Frec` limit for the canonical local
regular-quadric product patch.

This is the product-patch restriction of
`TexMatchingLocalPatchUnprimedSaturatedTailPathFrecAsymptotic`: it only asks for the
canonical dials that are actually used by matching. -/
abbrev TexMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Prop :=
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let N :=
    texMatchingProductNeighborhoodData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let S :=
    texMatchingSaturatedContributionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    Filter.Tendsto
      (fun τ : ℝ =>
        let q :=
          texMatchingUnprimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ τ
        Frec r (Params.tail θ) q.1 q.2 τ)
      Filter.atTop
      (nhds (texMatchingUnprimedSaturatedLimitVector θ S.D t p))

/-- Selected-dial lower-depth primed tail-path `Frec` limit for the canonical local
regular-quadric product patch. -/
abbrev TexMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Prop :=
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let N :=
    texMatchingProductNeighborhoodData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    Filter.Tendsto
      (fun τ : ℝ =>
        let q :=
          texMatchingPrimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ' := θ') δ τ
        Frec r (Params.tail θ') q.1 q.2 τ)
      Filter.atTop
      (nhds (texMatchingPrimedTelescopedLimitVector θ' t p))

/-- Selected-dial unprimed saturated full `Frec` limit for the canonical local
regular-quadric product patch.

This is the actual unprimed field consumed by the pre-matching regular-quadric
provider: only the canonical dials selected from the product patch are required, not a
global theorem over every point of `T.Ustar`. -/
abbrev TexMatchingLocalPatchRegularQuadricUnprimedSaturatedFrecAsymptoticObligation
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Prop :=
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let N :=
    texMatchingProductNeighborhoodData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let S :=
    texMatchingSaturatedContributionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    Filter.Tendsto
      (fun τ : ℝ =>
        Frec r θ (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ)
      Filter.atTop
      (nhds (texMatchingUnprimedSaturatedLimitVector θ S.D t p))

/-- Selected-dial primed telescoped full `Frec` limit for the canonical local
regular-quadric product patch. -/
abbrev TexMatchingLocalPatchRegularQuadricPrimedTelescopedFrecAsymptoticObligation
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Prop :=
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let N :=
    texMatchingProductNeighborhoodData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    Filter.Tendsto
      (fun τ : ℝ =>
        Frec r θ' (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ)
      Filter.atTop
      (nhds (texMatchingPrimedTelescopedLimitVector θ' t p))

/-- Selected-dial unprimed saturated peeled effective-tail `Frec` limit for the
canonical local regular-quadric product patch. -/
abbrev TexMatchingLocalPatchRegularQuadricUnprimedSaturatedEffectiveTailFrecAsymptotic
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Prop :=
  TexMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic
    hL hr hstep endpoint D localRegion

/-- Selected-dial primed telescoped peeled effective-tail `Frec` limit for the
canonical local regular-quadric product patch. -/
abbrev TexMatchingLocalPatchRegularQuadricPrimedTelescopedEffectiveTailFrecAsymptotic
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Prop :=
  TexMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic
    hL hr hstep endpoint D localRegion

/-- Local-patch spelling of selected effective-tail convergence data over the canonical
regular-quadric product neighborhood. -/
abbrev TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Type :=
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let N :=
    texMatchingProductNeighborhoodData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  TexMatchingRegularQuadricSelectedEffectiveTailFrecAnalyticData
    (θ := θ) (θ' := θ') signRegion T N

/-- Local-patch spelling of selected effective-tail limit-vector identification data. -/
abbrev TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailLimitIdentificationData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (analytic :
      TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData
        hL hr hstep endpoint D localRegion) : Prop :=
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let N :=
    texMatchingProductNeighborhoodData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let S :=
    texMatchingSaturatedContributionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  TexMatchingRegularQuadricSelectedEffectiveTailLimitIdentificationData
    signRegion T N S analytic

/-- Local-patch selected effective-tail analytic data from split lower-depth path-class
data and selected path membership. -/
noncomputable def
    texMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData_of_lowerDepthTailPath
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (UnprimedTailPaths PrimedTailPaths : Set (ProbePath d))
    (analytic :
      TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ')
        UnprimedTailPaths PrimedTailPaths)
    (pathMem :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      TexMatchingRegularQuadricLowerDepthEffectiveTailPathMemData
        (θ := θ) (θ' := θ') signRegion T N
        UnprimedTailPaths PrimedTailPaths) :
    TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData
      hL hr hstep endpoint D localRegion := by
  dsimp [TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData]
    at pathMem ⊢
  exact
    texMatchingRegularQuadricSelectedEffectiveTailFrecAnalyticData_of_lowerDepthTailPath
      analytic pathMem

/-- Universal local-patch selected effective-tail analytic data from lower-depth
path-class convergence over `Set.univ`. -/
noncomputable def
    texMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData_of_paths_univ_lowerDepthTailPath
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (analytic :
      TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ') Set.univ Set.univ) :
    TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData
      hL hr hstep endpoint D localRegion := by
  dsimp [TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData]
  exact
    texMatchingRegularQuadricSelectedEffectiveTailFrecAnalyticData_of_lowerDepthTailPath
      analytic
      (texMatchingRegularQuadricLowerDepthEffectiveTailPathMemData_of_paths_univ
        (θ := θ)
        (texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
        (texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texMatchingSignRegionData_of_region
            (L := L) (d := d) (r := r) hr hstep endpoint D
            (texRegionConstructionData_of_IDLData_of_localPatch
              (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion)))
        (texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion)))

/-- Realized-tail local-patch selected effective-tail analytic data from selected dial
membership and lower-depth convergence over the realized-tail path classes. -/
noncomputable def
    texMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData_of_realizedTailDialMem_lowerDepthTailPath
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (hdial_mem :
      TexMatchingLocalPatchRegularQuadricDialMemObligation
        hL hr hstep endpoint D localRegion)
    (analytic :
      TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ')
        (realizedTailPathSet r θ D.Paths)
        (realizedTailPathSet r θ' D.Paths)) :
    TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData
      hL hr hstep endpoint D localRegion := by
  dsimp [TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData,
    TexMatchingLocalPatchRegularQuadricDialMemObligation] at hdial_mem ⊢
  exact
    texMatchingRegularQuadricSelectedEffectiveTailFrecAnalyticData_of_lowerDepthTailPath
      analytic
      (texMatchingRegularQuadricLowerDepthEffectiveTailPathMemData_of_realizedTailPathSet
        D
        (texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
        (texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texMatchingSignRegionData_of_region
            (L := L) (d := d) (r := r) hr hstep endpoint D
            (texRegionConstructionData_of_IDLData_of_localPatch
              (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion)))
        (texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
        hdial_mem)

/-- Local selected unprimed peeled asymptotic from selected effective-tail
limit/tendsto data over the canonical product patch. -/
theorem
    texMatchingLocalPatchRegularQuadricUnprimedSaturatedEffectiveTailFrecAsymptotic_of_selectedEffectiveTailData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (analytic :
      TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData
        hL hr hstep endpoint D localRegion)
    (limits :
      TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailLimitIdentificationData
        hL hr hstep endpoint D localRegion analytic) :
    TexMatchingLocalPatchRegularQuadricUnprimedSaturatedEffectiveTailFrecAsymptotic
      hL hr hstep endpoint D localRegion := by
  dsimp [TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData,
    TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailLimitIdentificationData,
    TexMatchingLocalPatchRegularQuadricUnprimedSaturatedEffectiveTailFrecAsymptotic,
    TexMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic]
      at analytic limits ⊢
  intro p hp t ht
  have hlimit := limits.unprimed_limit_eq p hp t ht
  simpa [hlimit] using analytic.unprimed_tendsto p hp t ht

/-- Local selected primed peeled asymptotic from selected effective-tail
limit/tendsto data over the canonical product patch. -/
theorem
    texMatchingLocalPatchRegularQuadricPrimedTelescopedEffectiveTailFrecAsymptotic_of_selectedEffectiveTailData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (analytic :
      TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData
        hL hr hstep endpoint D localRegion)
    (limits :
      TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailLimitIdentificationData
        hL hr hstep endpoint D localRegion analytic) :
    TexMatchingLocalPatchRegularQuadricPrimedTelescopedEffectiveTailFrecAsymptotic
      hL hr hstep endpoint D localRegion := by
  dsimp [TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData,
    TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailLimitIdentificationData,
    TexMatchingLocalPatchRegularQuadricPrimedTelescopedEffectiveTailFrecAsymptotic,
    TexMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic]
      at analytic limits ⊢
  intro p hp t ht
  have hlimit := limits.primed_limit_eq p hp t ht
  simpa [hlimit] using analytic.primed_tendsto p hp t ht

/-- Local-patch spelling of selected canonical regular-quadric closed-recursion limits. -/
abbrev TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Prop :=
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let N :=
    texMatchingProductNeighborhoodData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let S :=
    texMatchingSaturatedContributionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  TexMatchingRegularQuadricClosedRecursionLimitObligation signRegion T N S

/-- Local selected effective-tail limit identification from selected closed-recursion
limits. -/
theorem
    texMatchingLocalPatchRegularQuadricSelectedEffectiveTailLimitIdentificationData_of_closedRecursionLimits
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (analytic :
      TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData
        hL hr hstep endpoint D localRegion)
    (hlimits :
      TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailLimitIdentificationData
      hL hr hstep endpoint D localRegion analytic := by
  dsimp [TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData,
    TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailLimitIdentificationData,
    TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation] at analytic hlimits ⊢
  exact
    texMatchingRegularQuadricSelectedEffectiveTailLimitIdentificationData_of_closedRecursionLimits
      analytic hlimits

/-- Local-patch selected primed tail-path field from the smaller generic selected-dial
tail-path theorem. -/
theorem
    texMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic_of_selectedDial
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (hprimed :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      TexMatchingRegularQuadricPrimedTelescopedTailPathFrecAsymptotic signRegion T N) :
    TexMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic
      hL hr hstep endpoint D localRegion := by
  dsimp [TexMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic,
    TexMatchingRegularQuadricPrimedTelescopedTailPathFrecAsymptotic] at hprimed ⊢
  exact hprimed

/-- Local-patch selected unprimed tail-path field from the smaller generic selected-dial
tail-path theorem. -/
theorem
    texMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic_of_selectedDial
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (hunprimed :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let S :=
        texMatchingSaturatedContributionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      TexMatchingRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic signRegion T N S) :
    TexMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic
      hL hr hstep endpoint D localRegion := by
  dsimp [TexMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic,
    TexMatchingRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic] at hunprimed ⊢
  exact hunprimed

/-- Peeling the first unprimed recursion layer reduces the selected regular-quadric
full `Frec` field to the selected lower-depth effective-tail field. -/
theorem
    texMatchingLocalPatchRegularQuadricUnprimedSaturatedFrecAsymptoticObligation_of_effectiveTail
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (hunprimed :
      TexMatchingLocalPatchRegularQuadricUnprimedSaturatedEffectiveTailFrecAsymptotic
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricUnprimedSaturatedFrecAsymptoticObligation
      hL hr hstep endpoint D localRegion := by
  dsimp [TexMatchingLocalPatchRegularQuadricUnprimedSaturatedEffectiveTailFrecAsymptotic,
    TexMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic,
    TexMatchingLocalPatchRegularQuadricUnprimedSaturatedFrecAsymptoticObligation]
      at hunprimed ⊢
  intro p hp t ht
  let δ :=
    texMatchingRegularQuadricDialPathData
      (L := L) (d := d) (r := r)
      (texMatchingSignRegionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D
        (texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
      (texTrichotomyConstructionData_of_signRegion
        (L := L) (d := d) (r := r) hr hstep endpoint D
        (texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion)))
      (texMatchingProductNeighborhoodData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D
        (texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
      p hp t ht
  have hfun :
      (fun τ : ℝ =>
        Frec r θ (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ) =
      (fun τ : ℝ =>
        let q :=
          texMatchingUnprimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ τ
        Frec r (Params.tail θ) q.1 q.2 τ) := by
    funext τ
    exact Frec_succ_paramsFirstLayerEffectivePoint r θ
      (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ
  rw [hfun]
  exact hunprimed p hp t ht

/-- Peeling the first primed recursion layer reduces the selected regular-quadric full
`Frec` field to the selected lower-depth effective-tail field. -/
theorem
    texMatchingLocalPatchRegularQuadricPrimedTelescopedFrecAsymptoticObligation_of_effectiveTail
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (hprimed :
      TexMatchingLocalPatchRegularQuadricPrimedTelescopedEffectiveTailFrecAsymptotic
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricPrimedTelescopedFrecAsymptoticObligation
      hL hr hstep endpoint D localRegion := by
  dsimp [TexMatchingLocalPatchRegularQuadricPrimedTelescopedEffectiveTailFrecAsymptotic,
    TexMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic,
    TexMatchingLocalPatchRegularQuadricPrimedTelescopedFrecAsymptoticObligation]
      at hprimed ⊢
  intro p hp t ht
  let δ :=
    texMatchingRegularQuadricDialPathData
      (L := L) (d := d) (r := r)
      (texMatchingSignRegionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D
        (texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
      (texTrichotomyConstructionData_of_signRegion
        (L := L) (d := d) (r := r) hr hstep endpoint D
        (texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion)))
      (texMatchingProductNeighborhoodData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D
        (texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
      p hp t ht
  have hfun :
      (fun τ : ℝ =>
        Frec r θ' (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ) =
      (fun τ : ℝ =>
        let q :=
          texMatchingPrimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ' := θ') δ τ
        Frec r (Params.tail θ') q.1 q.2 τ) := by
    funext τ
    exact Frec_succ_paramsFirstLayerEffectivePoint r θ'
      (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ
  rw [hfun]
  exact hprimed p hp t ht

/-- Selected unprimed full `Frec` field from the selected lower-depth tail-path field. -/
theorem
    texMatchingLocalPatchRegularQuadricUnprimedSaturatedFrecAsymptoticObligation_of_tailPath
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (htail :
      TexMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricUnprimedSaturatedFrecAsymptoticObligation
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricUnprimedSaturatedFrecAsymptoticObligation_of_effectiveTail
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion htail

/-- Selected primed full `Frec` field from the selected lower-depth tail-path field. -/
theorem
    texMatchingLocalPatchRegularQuadricPrimedTelescopedFrecAsymptoticObligation_of_tailPath
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (htail :
      TexMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricPrimedTelescopedFrecAsymptoticObligation
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricPrimedTelescopedFrecAsymptoticObligation_of_effectiveTail
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion htail

/-- Selected primed full `Frec` field from the smaller generic selected-dial
tail-path theorem.

This is the intended pre-matching reduction for the primed side: the remaining
analytic input is just the lower-depth primed recursion along each selected
regular-quadric dial path, with no `FirstLayerMatchedData` or `TexMatchingData`. -/
theorem
    texMatchingLocalPatchRegularQuadricPrimedFrecAsymptoticObligation_of_selectedTailPath
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (hprimed :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      TexMatchingRegularQuadricPrimedTelescopedTailPathFrecAsymptotic signRegion T N) :
    TexMatchingLocalPatchRegularQuadricPrimedTelescopedFrecAsymptoticObligation
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricPrimedTelescopedFrecAsymptoticObligation_of_tailPath
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    (texMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic_of_selectedDial
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion hprimed)

/-- Selected unprimed full `Frec` field from the smaller generic selected-dial
tail-path theorem.

This is the unprimed analogue of
`texMatchingLocalPatchRegularQuadricPrimedFrecAsymptoticObligation_of_selectedTailPath`:
the remaining analytic input is just the lower-depth unprimed recursion along each
selected regular-quadric dial path. -/
theorem
    texMatchingLocalPatchRegularQuadricUnprimedFrecAsymptoticObligation_of_selectedTailPath
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (hunprimed :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let S :=
        texMatchingSaturatedContributionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      TexMatchingRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic signRegion T N S) :
    TexMatchingLocalPatchRegularQuadricUnprimedSaturatedFrecAsymptoticObligation
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricUnprimedSaturatedFrecAsymptoticObligation_of_tailPath
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    (texMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic_of_selectedDial
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion hunprimed)

/-- The selected full `Frec` asymptotic fields are exactly the two selected
closed-recursion limits needed by the regular-quadric local patch. -/
theorem
    texMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation_of_regularQuadricFrec
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (hunprimed :
      TexMatchingLocalPatchRegularQuadricUnprimedSaturatedFrecAsymptoticObligation
        hL hr hstep endpoint D localRegion)
    (hprimed :
      TexMatchingLocalPatchRegularQuadricPrimedTelescopedFrecAsymptoticObligation
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
      hL hr hstep endpoint D localRegion := by
  dsimp [
    TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation,
    TexMatchingLocalPatchRegularQuadricUnprimedSaturatedFrecAsymptoticObligation,
    TexMatchingLocalPatchRegularQuadricPrimedTelescopedFrecAsymptoticObligation
  ] at hunprimed hprimed ⊢
  exact ⟨hunprimed, hprimed⟩

/-- The selected lower-depth tail-path limits give the selected full closed-recursion
limits after the exact first-layer peel. -/
theorem texMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation_of_tailPath
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (hunprimed :
      TexMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic
        hL hr hstep endpoint D localRegion)
    (hprimed :
      TexMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
      hL hr hstep endpoint D localRegion := by
  dsimp [
    TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation,
    TexMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic,
    TexMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic
  ] at hunprimed hprimed ⊢
  refine ⟨?_, ?_⟩
  · intro p hp t ht
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r)
        (texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
        (texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texMatchingSignRegionData_of_region
            (L := L) (d := d) (r := r) hr hstep endpoint D
            (texRegionConstructionData_of_IDLData_of_localPatch
              (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion)))
        (texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
        p hp t ht
    have hfun :
        (fun τ : ℝ =>
          Frec r θ (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ) =
        (fun τ : ℝ =>
          let q :=
            texMatchingUnprimedDialEffectiveTailPath
              (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ τ
          Frec r (Params.tail θ) q.1 q.2 τ) := by
      funext τ
      exact Frec_succ_paramsFirstLayerEffectivePoint r θ
        (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ
    change Filter.Tendsto
      (fun τ : ℝ =>
        Frec r θ (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ)
      Filter.atTop
      (nhds
        (texMatchingUnprimedSaturatedLimitVector θ
          (texMatchingSaturatedContributionData_of_region
            (L := L) (d := d) (r := r) hr hstep endpoint D
            (texRegionConstructionData_of_IDLData_of_localPatch
              (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion)).D
          t p))
    rw [hfun]
    exact hunprimed p hp t ht
  · intro p hp t ht
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r)
        (texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
        (texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texMatchingSignRegionData_of_region
            (L := L) (d := d) (r := r) hr hstep endpoint D
            (texRegionConstructionData_of_IDLData_of_localPatch
              (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion)))
        (texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
        p hp t ht
    have hfun :
        (fun τ : ℝ =>
          Frec r θ' (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ) =
        (fun τ : ℝ =>
          let q :=
            texMatchingPrimedDialEffectiveTailPath
              (L := L) (d := d) (r := r) (θ' := θ') δ τ
          Frec r (Params.tail θ') q.1 q.2 τ) := by
      funext τ
      exact Frec_succ_paramsFirstLayerEffectivePoint r θ'
        (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ
    change Filter.Tendsto
      (fun τ : ℝ =>
        Frec r θ' (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ)
      Filter.atTop
      (nhds (texMatchingPrimedTelescopedLimitVector θ' t p))
    rw [hfun]
    exact hprimed p hp t ht

/-- Selected closed-recursion limits discharge the canonical local regular-quadric
limit-vector obligation. -/
theorem texMatchingLocalPatchRegularQuadricLimitObligation_of_closedRecursionLimits
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (hlimits :
      TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricLimitObligation
      hL hr hstep endpoint D localRegion := by
  dsimp [TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation,
    TexMatchingLocalPatchRegularQuadricLimitObligation,
    TexMatchingLocalPatchRegularQuadricLimitVectorObligation] at hlimits ⊢
  exact
    texMatchingRegularQuadricLimitVectorObligation_of_closedRecursionLimits
      (L := L) (d := d) (r := r) (by omega)
      (texMatchingSignRegionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D
        (texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
      (texTrichotomyConstructionData_of_signRegion
        (L := L) (d := d) (r := r) hr hstep endpoint D
        (texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D
          (texRegionConstructionData_of_IDLData_of_localPatch
            (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion)))
      (texMatchingProductNeighborhoodData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D
        (texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
      (texMatchingSaturatedContributionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D
        (texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
      hlimits

/-- Local-patch region provider from selected dial membership and selected
closed-recursion limits. -/
noncomputable def texMatchingRegionProviderFromLocalPatchData_of_regularQuadricClosedRecursionLimits
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (hdial_mem :
      TexMatchingLocalPatchRegularQuadricDialMemObligation
        hL hr hstep endpoint D localRegion)
    (hlimits :
      TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
        hL hr hstep endpoint D localRegion) :
    TexMatchingRegionProviderFromLocalPatchData
      hL hr hstep endpoint D localRegion := by
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let N :=
    texMatchingProductNeighborhoodData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let S :=
    texMatchingSaturatedContributionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let hdial_mem' :
      ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
        DialPathData.probe
          (texMatchingRegularQuadricDialPathData
            (L := L) (d := d) (r := r) signRegion T N p hp t ht) ∈ D.Paths :=
    hdial_mem
  let hlimit' :
      TexMatchingRegularQuadricLimitVectorObligation signRegion T N S :=
    texMatchingLocalPatchRegularQuadricLimitObligation_of_closedRecursionLimits
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion hlimits
  exact
    { bridge :=
        texMatchingDialPathLimitBridgeData_of_regularQuadricLimit
          (L := L) (d := d) (r := r) D signRegion T N S hdial_mem' hlimit' }

/-- Minimal non-circular local-patch regular-quadric provider based on selected
regular-quadric `Frec` asymptotics.

The analytic fields only range over the canonical product-patch dials used by matching;
path membership remains explicit for non-universal recursive path classes. -/
structure TexMatchingLocalPatchRegularQuadricFrecProviderData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Prop where
  dial_mem :
    TexMatchingLocalPatchRegularQuadricDialMemObligation
      hL hr hstep endpoint D localRegion
  unprimed :
    TexMatchingLocalPatchRegularQuadricUnprimedSaturatedFrecAsymptoticObligation
      hL hr hstep endpoint D localRegion
  primed :
    TexMatchingLocalPatchRegularQuadricPrimedTelescopedFrecAsymptoticObligation
      hL hr hstep endpoint D localRegion

/-- A packed local-patch `Frec` provider discharges the currently exposed
closed-recursion limit obligation.  The dial-membership field is retained for the
downstream region-provider compiler; closed recursion itself only needs the two
selected `Frec` asymptotics. -/
theorem texMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation_of_frecProviderData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (provider :
      TexMatchingLocalPatchRegularQuadricFrecProviderData
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation_of_regularQuadricFrec
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    provider.unprimed provider.primed

/-- Local-patch regular-quadric provider whose analytic fields are selected full
`Frec` asymptotics.  This keeps the hard analytic theorems explicit before packaging
them as the exposed provider fields. -/
structure TexMatchingLocalPatchRegularQuadricFrecProviderDialData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Prop where
  dial_mem :
    TexMatchingLocalPatchRegularQuadricDialMemObligation
      hL hr hstep endpoint D localRegion
  unprimed :
    TexMatchingLocalPatchRegularQuadricUnprimedSaturatedFrecAsymptoticObligation
      hL hr hstep endpoint D localRegion
  primed :
    TexMatchingLocalPatchRegularQuadricPrimedTelescopedFrecAsymptoticObligation
      hL hr hstep endpoint D localRegion

/-- Local-patch regular-quadric provider whose analytic fields are the peeled
effective-tail `Frec` asymptotics.

This is narrower than `TexMatchingLocalPatchRegularQuadricFrecProviderDialData`: the
first recursion layer is discharged by exact identities, so callers only supply the
selected lower-depth tail limits. -/
structure TexMatchingLocalPatchRegularQuadricFrecProviderEffectiveTailData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Prop where
  dial_mem :
    TexMatchingLocalPatchRegularQuadricDialMemObligation
      hL hr hstep endpoint D localRegion
  unprimed :
    TexMatchingLocalPatchRegularQuadricUnprimedSaturatedEffectiveTailFrecAsymptotic
      hL hr hstep endpoint D localRegion
  primed :
    TexMatchingLocalPatchRegularQuadricPrimedTelescopedEffectiveTailFrecAsymptotic
      hL hr hstep endpoint D localRegion

/-- Convert a peeled effective-tail local-patch provider to the existing dial-level
provider surface. -/
def texMatchingLocalPatchRegularQuadricFrecProviderDialData_of_effectiveTailData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (provider :
      TexMatchingLocalPatchRegularQuadricFrecProviderEffectiveTailData
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricFrecProviderDialData
      hL hr hstep endpoint D localRegion where
  dial_mem := provider.dial_mem
  unprimed :=
    texMatchingLocalPatchRegularQuadricUnprimedSaturatedFrecAsymptoticObligation_of_effectiveTail
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      provider.unprimed
  primed :=
    texMatchingLocalPatchRegularQuadricPrimedTelescopedFrecAsymptoticObligation_of_effectiveTail
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      provider.primed

/-- Package selected full local-patch asymptotics into the exposed `Frec` provider
surface. -/
def texMatchingLocalPatchRegularQuadricFrecProviderData_of_dialData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (provider :
      TexMatchingLocalPatchRegularQuadricFrecProviderDialData
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricFrecProviderData
      hL hr hstep endpoint D localRegion where
  dial_mem := provider.dial_mem
  unprimed := provider.unprimed
  primed := provider.primed

/-- Package peeled effective-tail local-patch asymptotics into the existing direct
`Frec` provider surface. -/
def texMatchingLocalPatchRegularQuadricFrecProviderData_of_effectiveTailData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (provider :
      TexMatchingLocalPatchRegularQuadricFrecProviderEffectiveTailData
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricFrecProviderData
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricFrecProviderData_of_dialData
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    (texMatchingLocalPatchRegularQuadricFrecProviderDialData_of_effectiveTailData
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion provider)

/-- Package generic selected-dial membership and selected lower-depth tail-path
asymptotics into the exposed local-patch `Frec` provider surface.

This is the smallest local-patch provider constructor: all three hypotheses are
phrased over the already constructed `signRegion/T/N` objects, with the saturated
contribution `S` appearing only on the unprimed side. -/
def texMatchingLocalPatchRegularQuadricFrecProviderData_of_selectedDialTailPath
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (hdial_mem :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      TexMatchingRegularQuadricDialMemObligation D signRegion T N)
    (hunprimed :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let S :=
        texMatchingSaturatedContributionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      TexMatchingRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic signRegion T N S)
    (hprimed :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      TexMatchingRegularQuadricPrimedTelescopedTailPathFrecAsymptotic signRegion T N) :
    TexMatchingLocalPatchRegularQuadricFrecProviderData
      hL hr hstep endpoint D localRegion where
  dial_mem :=
    texMatchingLocalPatchRegularQuadricDialMemObligation_of_selectedDial
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion hdial_mem
  unprimed :=
    texMatchingLocalPatchRegularQuadricUnprimedFrecAsymptoticObligation_of_selectedTailPath
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion hunprimed
  primed :=
    texMatchingLocalPatchRegularQuadricPrimedFrecAsymptoticObligation_of_selectedTailPath
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion hprimed

/-- Package selected dial membership and lower-depth tail-path convergence data into
the exposed local-patch `Frec` provider.

This replaces the two direct selected tail-path asymptotic hypotheses with the smaller
recursive handoff: lower-depth convergence over path classes, selected effective-tail
path membership in those classes, and limit-vector identification for the selected
dials. -/
def texMatchingLocalPatchRegularQuadricFrecProviderData_of_selectedDialLowerDepthTailPath
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (hdial_mem :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      TexMatchingRegularQuadricDialMemObligation D signRegion T N)
    (UnprimedTailPaths PrimedTailPaths : Set (ProbePath d))
    (provider :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let S :=
        texMatchingSaturatedContributionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      TexMatchingRegularQuadricLowerDepthTailPathFrecProviderData
        signRegion T N S UnprimedTailPaths PrimedTailPaths) :
    TexMatchingLocalPatchRegularQuadricFrecProviderData
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricFrecProviderData_of_selectedDialTailPath
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    hdial_mem
    (texMatchingRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic_of_lowerDepthProvider
      provider)
    (texMatchingRegularQuadricPrimedTelescopedTailPathFrecAsymptotic_of_lowerDepthProvider
      provider)

/-- Local-patch realized-tail constructor from split lower-depth data.

Compared with
`texMatchingLocalPatchRegularQuadricFrecProviderData_of_selectedDialLowerDepthTailPath`,
this is narrower on the path side: direct selected-dial membership in the swept
`realizedTailPathSet` supplies both canonical dial membership and selected
effective-tail lower-depth path membership.  The remaining analytic frontier is just
lower-depth convergence over the two realized tail path classes plus identification of
their selected limits. -/
def texMatchingLocalPatchRegularQuadricFrecProviderData_of_realizedTailMem_lowerDepthTailPath
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (θfull : Params (L + 2) d)
    (FullPaths : Set (ProbePath d))
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (realized :
      TexMatchingLocalPatchRegularQuadricDialRealizedTailMemObligation
        hL hr hstep endpoint D localRegion θfull FullPaths)
    (analytic :
      TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ')
        (realizedTailPathSet r θ D.Paths)
        (realizedTailPathSet r θ' D.Paths))
    (limits :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let S :=
        texMatchingSaturatedContributionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      TexMatchingRegularQuadricLowerDepthLimitIdentificationData
        signRegion T N S
        (realizedTailPathSet r θ D.Paths)
        (realizedTailPathSet r θ' D.Paths)
        analytic) :
    TexMatchingLocalPatchRegularQuadricFrecProviderData
      hL hr hstep endpoint D localRegion :=
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let N :=
    texMatchingProductNeighborhoodData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let S :=
    texMatchingSaturatedContributionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let hdial_mem :
      TexMatchingRegularQuadricDialMemObligation D signRegion T N :=
    texMatchingRegularQuadricDialMemObligation_of_realizedTailMem
      D signRegion T N θfull FullPaths hPaths realized
  let provider :
      TexMatchingRegularQuadricLowerDepthTailPathFrecProviderData
        signRegion T N S
        (realizedTailPathSet r θ D.Paths)
        (realizedTailPathSet r θ' D.Paths) :=
    texMatchingRegularQuadricLowerDepthTailPathFrecProviderData_of_realizedTailPathSet
      D signRegion T N S hdial_mem analytic limits
  texMatchingLocalPatchRegularQuadricFrecProviderData_of_selectedDialLowerDepthTailPath
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    hdial_mem
    (realizedTailPathSet r θ D.Paths)
    (realizedTailPathSet r θ' D.Paths)
    provider

/-- Universal-path constructor from selected peeled effective-tail asymptotics.  Path
membership is still mechanical from `D.Paths = Set.univ`; the two analytic hypotheses
are the selected lower-depth tail limits. -/
def texMatchingLocalPatchRegularQuadricFrecProviderData_of_paths_univ_of_effectiveTail
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (hPaths : D.Paths = Set.univ)
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (hunprimed :
      TexMatchingLocalPatchRegularQuadricUnprimedSaturatedEffectiveTailFrecAsymptotic
        hL hr hstep endpoint D localRegion)
    (hprimed :
      TexMatchingLocalPatchRegularQuadricPrimedTelescopedEffectiveTailFrecAsymptotic
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricFrecProviderData
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricFrecProviderData_of_effectiveTailData
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    { dial_mem :=
        texMatchingLocalPatchRegularQuadricDialMemObligation_of_paths_univ
          (L := L) (d := d) (r := r) hL hr hstep endpoint D hPaths localRegion
      unprimed := hunprimed
      primed := hprimed }

/-- Universal-path constructor from selected effective-tail limit functions and
`Tendsto` proofs over the canonical product patch.  This is narrower than the
peeled-effective-tail constructor: the endpoint limits are supplied by a separate
selected limit-identification record. -/
def texMatchingLocalPatchRegularQuadricFrecProviderData_of_paths_univ_selectedEffectiveTail
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (hPaths : D.Paths = Set.univ)
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (analytic :
      TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData
        hL hr hstep endpoint D localRegion)
    (limits :
      TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailLimitIdentificationData
        hL hr hstep endpoint D localRegion analytic) :
    TexMatchingLocalPatchRegularQuadricFrecProviderData
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricFrecProviderData_of_paths_univ_of_effectiveTail
    (L := L) (d := d) (r := r) hL hr hstep endpoint D hPaths localRegion
    (texMatchingLocalPatchRegularQuadricUnprimedSaturatedEffectiveTailFrecAsymptotic_of_selectedEffectiveTailData
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      analytic limits)
    (texMatchingLocalPatchRegularQuadricPrimedTelescopedEffectiveTailFrecAsymptotic_of_selectedEffectiveTailData
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      analytic limits)

/-- Universal-path constructor from selected effective-tail limit functions and the
smaller selected closed-recursion limit obligation.

This compiles the current selected limit-identification field from
`TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation`, keeping the
effective-tail analytic data explicit but removing the need to prove the selected
limit equalities directly. -/
def
    texMatchingLocalPatchRegularQuadricFrecProviderData_of_paths_univ_selectedEffectiveTail_closedRecursionLimits
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (hPaths : D.Paths = Set.univ)
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (analytic :
      TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData
        hL hr hstep endpoint D localRegion)
    (hlimits :
      TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricFrecProviderData
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricFrecProviderData_of_paths_univ_selectedEffectiveTail
    (L := L) (d := d) (r := r) hL hr hstep endpoint D hPaths localRegion
    analytic
    (texMatchingLocalPatchRegularQuadricSelectedEffectiveTailLimitIdentificationData_of_closedRecursionLimits
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      analytic hlimits)

/-! ### Selected-tail local-patch closed-recursion boundary

The declarations in this block are the R5 migration path away from the old universal
`∀ ProbePath` lower-depth boundary.  The lower-depth analytic field below is restricted
to the selected effective-tail path classes generated by the local patch dials:
`realizedTailPathSet r θ D.Paths` and `realizedTailPathSet r θ' D.Paths`.  Universal
top-level callers may still use `D.Paths = Set.univ` to prove selected dial membership,
but they do not need a universal lower-depth convergence hypothesis.
-/

/-- Selected/path-restricted local-patch source for closed-recursion matching.

The lower-depth analytic data lives on the two effective-tail path classes selected by
the local patch.  The membership field records that each selected dial's unprimed and
primed effective-tail paths land in those classes, and the closed-recursion field is
the genuine selected R4 limit input used to identify the selected analytic limits. -/
structure TexMatchingLocalPatchRegularQuadricSelectedTailClosedRecursionSourceData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Type where
  lowerDepthAnalytic :
    TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
      (r := r) (Params.tail θ) (Params.tail θ')
      (realizedTailPathSet r θ D.Paths)
      (realizedTailPathSet r θ' D.Paths)
  effectiveTailPathMem :
    let region :=
      texRegionConstructionData_of_IDLData_of_localPatch
        (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    let signRegion :=
      texMatchingSignRegionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region
    let T :=
      texTrichotomyConstructionData_of_signRegion
        (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
    let N :=
      texMatchingProductNeighborhoodData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region
    TexMatchingRegularQuadricLowerDepthEffectiveTailPathMemData
      (θ := θ) (θ' := θ') signRegion T N
      (realizedTailPathSet r θ D.Paths)
      (realizedTailPathSet r θ' D.Paths)
  closedRecursionLimits :
    TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
      hL hr hstep endpoint D localRegion

namespace TexMatchingLocalPatchRegularQuadricSelectedTailClosedRecursionSourceData

/-- Build selected effective-tail analytic data from the path-restricted source. -/
noncomputable def selectedEffectiveTail
    {L d r : Nat} {hL : 0 < L} {hr : 2 <= r}
    {θ θ' : Params (L + 1) d}
    {hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ'}
    {endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ)}
    {D : IDLData (L + 1) d r θ θ'}
    {localRegion : TexRegionConstructionDataOfIDLDataObligation hL D}
    (P :
      TexMatchingLocalPatchRegularQuadricSelectedTailClosedRecursionSourceData
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData_of_lowerDepthTailPath
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    (realizedTailPathSet r θ D.Paths)
    (realizedTailPathSet r θ' D.Paths)
    P.lowerDepthAnalytic
    P.effectiveTailPathMem

end TexMatchingLocalPatchRegularQuadricSelectedTailClosedRecursionSourceData

/-! ### Builder-backed selected-tail closed-recursion source

The declarations below are the honest selected-tail surface for callers that already
carry a genuine trichotomy package.  They are intentionally phrased over explicit
`signRegion`, `T`, `N`, and `S` inputs, so they do not depend on the legacy local-patch
constructor-level trichotomy shortcut.
-/

/-- Explicit selected/path-restricted source for closed-recursion matching.

The trichotomy construction `T`, product patch `N`, and saturated contribution `S`
are caller-supplied.  The lower-depth analytic data is restricted to the selected
realized-tail classes generated by the current `IDLData.Paths`. -/
structure TexMatchingRegularQuadricSelectedTailClosedRecursionSourceData
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma) : Type where
  lowerDepthAnalytic :
    TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
      (r := r) (Params.tail θ) (Params.tail θ')
      (realizedTailPathSet r θ D.Paths)
      (realizedTailPathSet r θ' D.Paths)
  effectiveTailPathMem :
    TexMatchingRegularQuadricLowerDepthEffectiveTailPathMemData
      (θ := θ) (θ' := θ') signRegion T N
      (realizedTailPathSet r θ D.Paths)
      (realizedTailPathSet r θ' D.Paths)
  closedRecursionLimits :
    TexMatchingRegularQuadricClosedRecursionLimitObligation signRegion T N S

namespace TexMatchingRegularQuadricSelectedTailClosedRecursionSourceData

/-- Restrict the stored lower-depth data to the selected effective-tail dials. -/
noncomputable def selectedEffectiveTail
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    {O : Set (ProbePair d)}
    {signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))}
    {T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U}
    {N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar}
    {varsigma : Nat -> ℝ}
    {S : TexMatchingSaturatedContributionData θ varsigma}
    (P :
      TexMatchingRegularQuadricSelectedTailClosedRecursionSourceData
        D signRegion T N S) :
    TexMatchingRegularQuadricSelectedEffectiveTailFrecAnalyticData
      (θ := θ) (θ' := θ') signRegion T N :=
  texMatchingRegularQuadricSelectedEffectiveTailFrecAnalyticData_of_lowerDepthTailPath
    P.lowerDepthAnalytic
    P.effectiveTailPathMem

/-- Identify the lower-depth abstract limits for the selected realized-tail classes. -/
theorem lowerDepthLimitIdentification
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    {O : Set (ProbePair d)}
    {signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))}
    {T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U}
    {N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar}
    {varsigma : Nat -> ℝ}
    {S : TexMatchingSaturatedContributionData θ varsigma}
    (P :
      TexMatchingRegularQuadricSelectedTailClosedRecursionSourceData
        D signRegion T N S) :
    TexMatchingRegularQuadricLowerDepthLimitIdentificationData
      signRegion T N S
      (realizedTailPathSet r θ D.Paths)
      (realizedTailPathSet r θ' D.Paths)
      P.lowerDepthAnalytic :=
  texMatchingRegularQuadricLowerDepthLimitIdentificationData_of_closedRecursionLimits
    (analytic := P.lowerDepthAnalytic)
    P.effectiveTailPathMem
    P.closedRecursionLimits

/-- Compile the explicit selected-tail source to the generic lower-depth provider. -/
def lowerDepthProvider
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {D : IDLData (L + 1) d r θ θ'}
    {O : Set (ProbePair d)}
    {signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))}
    {T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U}
    {N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar}
    {varsigma : Nat -> ℝ}
    {S : TexMatchingSaturatedContributionData θ varsigma}
    (P :
      TexMatchingRegularQuadricSelectedTailClosedRecursionSourceData
        D signRegion T N S) :
    TexMatchingRegularQuadricLowerDepthTailPathFrecProviderData
      signRegion T N S
      (realizedTailPathSet r θ D.Paths)
      (realizedTailPathSet r θ' D.Paths) :=
  texMatchingRegularQuadricLowerDepthTailPathFrecProviderData_of_parts
    P.lowerDepthAnalytic
    P.effectiveTailPathMem
    P.lowerDepthLimitIdentification

end TexMatchingRegularQuadricSelectedTailClosedRecursionSourceData

/-- Universal local-patch limit identification from selected lower-depth tail-path
asymptotics.

The selected effective-tail path membership is mechanical for `Set.univ`, so this
constructor leaves only the lower-depth analytic record and the two selected endpoint
asymptotics needed to identify its abstract limits. -/
theorem
    texMatchingLocalPatchRegularQuadricLowerDepthLimitIdentificationData_of_paths_univ_tailPath
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (analytic :
      TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ') Set.univ Set.univ)
    (hunprimed :
      TexMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic
        hL hr hstep endpoint D localRegion)
    (hprimed :
      TexMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic
        hL hr hstep endpoint D localRegion) :
    let region :=
      texRegionConstructionData_of_IDLData_of_localPatch
        (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    let signRegion :=
      texMatchingSignRegionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region
    let T :=
      texTrichotomyConstructionData_of_signRegion
        (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
    let N :=
      texMatchingProductNeighborhoodData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region
    let S :=
      texMatchingSaturatedContributionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region
    TexMatchingRegularQuadricLowerDepthLimitIdentificationData
      signRegion T N S Set.univ Set.univ analytic := by
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let N :=
    texMatchingProductNeighborhoodData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let S :=
    texMatchingSaturatedContributionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  have hunprimed' :
      TexMatchingRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic
        signRegion T N S := by
    dsimp [TexMatchingRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic,
      TexMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic]
        at hunprimed ⊢
    exact hunprimed
  have hprimed' :
      TexMatchingRegularQuadricPrimedTelescopedTailPathFrecAsymptotic
        signRegion T N := by
    dsimp [TexMatchingRegularQuadricPrimedTelescopedTailPathFrecAsymptotic,
      TexMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic]
        at hprimed ⊢
    exact hprimed
  exact
    texMatchingRegularQuadricLowerDepthLimitIdentificationData_of_tailPathAsymptotics
      (analytic := analytic)
      (texMatchingRegularQuadricLowerDepthEffectiveTailPathMemData_of_paths_univ
        (θ := θ) signRegion T N)
      hunprimed'
      hprimed'

/-- Universal-path local-patch constructor from split lower-depth data.

This is the lower-depth analogue of
`texMatchingLocalPatchRegularQuadricFrecProviderData_of_realizedTailMem_lowerDepthTailPath`
for the top-level case.  The selected regular-quadric dial membership and selected
effective-tail path membership are both filled mechanically from `D.Paths = Set.univ`;
callers only supply lower-depth convergence over `Set.univ` path classes and the
selected limit-vector identifications. -/
def texMatchingLocalPatchRegularQuadricFrecProviderData_of_paths_univ_lowerDepthTailPath
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (hPaths : D.Paths = Set.univ)
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (analytic :
      TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ') Set.univ Set.univ)
    (limits :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let S :=
        texMatchingSaturatedContributionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      TexMatchingRegularQuadricLowerDepthLimitIdentificationData
        signRegion T N S Set.univ Set.univ analytic) :
    TexMatchingLocalPatchRegularQuadricFrecProviderData
      hL hr hstep endpoint D localRegion :=
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let N :=
    texMatchingProductNeighborhoodData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let S :=
    texMatchingSaturatedContributionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let hdial_mem :
      TexMatchingRegularQuadricDialMemObligation D signRegion T N :=
    texMatchingRegularQuadricDialMemObligation_of_paths_univ
      D hPaths signRegion T N
  let provider :
      TexMatchingRegularQuadricLowerDepthTailPathFrecProviderData
        signRegion T N S Set.univ Set.univ :=
    texMatchingRegularQuadricLowerDepthTailPathFrecProviderData_of_paths_univ
      signRegion T N S analytic limits
  texMatchingLocalPatchRegularQuadricFrecProviderData_of_selectedDialLowerDepthTailPath
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    hdial_mem Set.univ Set.univ provider

/-- Universal-path local-patch constructor from lower-depth analytic data and selected
tail-path asymptotics.

This is the `TexMatchingReducedUniv...`-compatible frontier: the data needed for that
record's `lowerDepthLimits` field is derived here from the two selected tail-path
asymptotic obligations. -/
def texMatchingLocalPatchRegularQuadricFrecProviderData_of_paths_univ_lowerDepthTailPath_of_tailPath
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (hPaths : D.Paths = Set.univ)
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (analytic :
      TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ') Set.univ Set.univ)
    (hunprimed :
      TexMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic
        hL hr hstep endpoint D localRegion)
    (hprimed :
      TexMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricFrecProviderData
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricFrecProviderData_of_paths_univ_lowerDepthTailPath
    (L := L) (d := d) (r := r) hL hr hstep endpoint D hPaths localRegion
    analytic
    (texMatchingLocalPatchRegularQuadricLowerDepthLimitIdentificationData_of_paths_univ_tailPath
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      analytic hunprimed hprimed)

/-- Universal-path local-patch constructor from explicit lower-depth limit functions
and selected tail-path asymptotics. -/
def texMatchingLocalPatchRegularQuadricFrecProviderData_of_paths_univ_univAnalytic_tailPath
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (hPaths : D.Paths = Set.univ)
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (analytic :
      TexMatchingRegularQuadricLowerDepthUnivTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ'))
    (hunprimed :
      TexMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic
        hL hr hstep endpoint D localRegion)
    (hprimed :
      TexMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricFrecProviderData
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricFrecProviderData_of_paths_univ_lowerDepthTailPath_of_tailPath
    (L := L) (d := d) (r := r) hL hr hstep endpoint D hPaths localRegion
    (texMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData_of_univData
      (r := r) analytic)
    hunprimed
    hprimed

/-- Universal-path local-patch constructor from universal lower-depth convergence and
selected lower-depth limit-vector identifications.

Compared with
`texMatchingLocalPatchRegularQuadricFrecProviderData_of_paths_univ_univAnalytic_tailPath`,
the caller no longer supplies selected tail-path `Tendsto` facts.  Those are projected
from the universal lower-depth analytic record; the only selected-dial data left is the
identification of the universal limit functions with the saturated/telescoped vectors. -/
def texMatchingLocalPatchRegularQuadricFrecProviderData_of_paths_univ_univAnalytic_limits
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (hPaths : D.Paths = Set.univ)
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (analytic :
      TexMatchingRegularQuadricLowerDepthUnivTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ'))
    (unprimed_limit_eq :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let S :=
        texMatchingSaturatedContributionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
        let δ :=
          texMatchingRegularQuadricDialPathData
            (L := L) (d := d) (r := r) signRegion T N p hp t ht
        analytic.unprimedLimit
            (texMatchingUnprimedDialEffectiveTailPath
              (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ) =
          texMatchingUnprimedSaturatedLimitVector θ S.D t p)
    (primed_limit_eq :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
        let δ :=
          texMatchingRegularQuadricDialPathData
            (L := L) (d := d) (r := r) signRegion T N p hp t ht
        analytic.primedLimit
            (texMatchingPrimedDialEffectiveTailPath
              (L := L) (d := d) (r := r) (θ' := θ') δ) =
          texMatchingPrimedTelescopedLimitVector θ' t p) :
    TexMatchingLocalPatchRegularQuadricFrecProviderData
      hL hr hstep endpoint D localRegion :=
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let N :=
    texMatchingProductNeighborhoodData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let S :=
    texMatchingSaturatedContributionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  texMatchingLocalPatchRegularQuadricFrecProviderData_of_paths_univ_lowerDepthTailPath
    (L := L) (d := d) (r := r) hL hr hstep endpoint D hPaths localRegion
    (texMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData_of_univData
      (r := r) analytic)
    (texMatchingRegularQuadricLowerDepthLimitIdentificationData_of_univAnalytic
      (L := L) (d := d) (r := r) (θ := θ) (θ' := θ')
      (signRegion := signRegion) (T := T) (N := N) (S := S)
      analytic unprimed_limit_eq primed_limit_eq)

/-- Local-patch selected unprimed tail-path asymptotic from universal lower-depth
convergence plus the selected unprimed abstract-limit identification.

This exposes the first half of
`texMatchingLocalPatchRegularQuadricFrecProviderData_of_paths_univ_univAnalytic_limits`
without requiring callers to build the full local-patch provider. -/
theorem
    texMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic_of_univAnalytic_limit
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (analytic :
      TexMatchingRegularQuadricLowerDepthUnivTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ'))
    (unprimed_limit_eq :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let S :=
        texMatchingSaturatedContributionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
        let δ :=
          texMatchingRegularQuadricDialPathData
            (L := L) (d := d) (r := r) signRegion T N p hp t ht
        analytic.unprimedLimit
            (texMatchingUnprimedDialEffectiveTailPath
              (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ) =
          texMatchingUnprimedSaturatedLimitVector θ S.D t p) :
    TexMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic
      hL hr hstep endpoint D localRegion := by
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let N :=
    texMatchingProductNeighborhoodData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let S :=
    texMatchingSaturatedContributionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  change TexMatchingRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic
    signRegion T N S
  exact
    texMatchingRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic_of_univAnalytic
      (L := L) (d := d) (r := r) (θ := θ) (θ' := θ')
      (signRegion := signRegion) (T := T) (N := N) (S := S)
      analytic
      (by
        intro p hp t ht
        simpa [region, signRegion, T, N, S] using
          unprimed_limit_eq p hp t ht)

/-- Local-patch selected primed tail-path asymptotic from universal lower-depth
convergence plus the selected primed abstract-limit identification. -/
theorem
    texMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic_of_univAnalytic_limit
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (analytic :
      TexMatchingRegularQuadricLowerDepthUnivTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ'))
    (primed_limit_eq :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
        let δ :=
          texMatchingRegularQuadricDialPathData
            (L := L) (d := d) (r := r) signRegion T N p hp t ht
        analytic.primedLimit
            (texMatchingPrimedDialEffectiveTailPath
              (L := L) (d := d) (r := r) (θ' := θ') δ) =
          texMatchingPrimedTelescopedLimitVector θ' t p) :
    TexMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic
      hL hr hstep endpoint D localRegion := by
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
  let N :=
    texMatchingProductNeighborhoodData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D region
  change TexMatchingRegularQuadricPrimedTelescopedTailPathFrecAsymptotic
    signRegion T N
  exact
    texMatchingRegularQuadricPrimedTelescopedTailPathFrecAsymptotic_of_univAnalytic
      (L := L) (d := d) (r := r) (θ := θ) (θ' := θ')
      (signRegion := signRegion) (T := T) (N := N)
      analytic
      (by
        intro p hp t ht
        simpa [region, signRegion, T, N] using
          primed_limit_eq p hp t ht)

/-- Selected closed-recursion limits from universal lower-depth convergence and the two
selected abstract-limit identifications.

This is the closed-recursion package behind the universal provider constructor, exposed
without the selected dial-membership field and without building a full `Frec` provider. -/
theorem
    texMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation_of_univAnalytic_limits
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (analytic :
      TexMatchingRegularQuadricLowerDepthUnivTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ'))
    (unprimed_limit_eq :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let S :=
        texMatchingSaturatedContributionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
        let δ :=
          texMatchingRegularQuadricDialPathData
            (L := L) (d := d) (r := r) signRegion T N p hp t ht
        analytic.unprimedLimit
            (texMatchingUnprimedDialEffectiveTailPath
              (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ) =
          texMatchingUnprimedSaturatedLimitVector θ S.D t p)
    (primed_limit_eq :
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      let T :=
        texTrichotomyConstructionData_of_signRegion
          (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      let N :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D region
      ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
        let δ :=
          texMatchingRegularQuadricDialPathData
            (L := L) (d := d) (r := r) signRegion T N p hp t ht
        analytic.primedLimit
            (texMatchingPrimedDialEffectiveTailPath
              (L := L) (d := d) (r := r) (θ' := θ') δ) =
          texMatchingPrimedTelescopedLimitVector θ' t p) :
    TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation_of_tailPath
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    (texMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic_of_univAnalytic_limit
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      analytic unprimed_limit_eq)
    (texMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic_of_univAnalytic_limit
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      analytic primed_limit_eq)

/-- Smaller local-patch universal matching input: arbitrary lower-depth `Frec`
convergence plus the selected identifications of its abstract limit functions.

It does not include selected dial membership and does not assume any matched-tail or
`tailReduced` data. -/
structure TexMatchingLocalPatchRegularQuadricUnivAnalyticLimitData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Type where
  lowerDepthAnalytic :
    TexMatchingRegularQuadricLowerDepthUnivTailPathFrecAnalyticData
      (r := r) (Params.tail θ) (Params.tail θ')
  unprimed_limit_eq :
    let region :=
      texRegionConstructionData_of_IDLData_of_localPatch
        (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    let signRegion :=
      texMatchingSignRegionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region
    let T :=
      texTrichotomyConstructionData_of_signRegion
        (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
    let N :=
      texMatchingProductNeighborhoodData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region
    let S :=
      texMatchingSaturatedContributionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region
    ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
      let δ :=
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      lowerDepthAnalytic.unprimedLimit
          (texMatchingUnprimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ := θ) (θ' := θ') δ) =
        texMatchingUnprimedSaturatedLimitVector θ S.D t p
  primed_limit_eq :
    let region :=
      texRegionConstructionData_of_IDLData_of_localPatch
        (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    let signRegion :=
      texMatchingSignRegionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region
    let T :=
      texTrichotomyConstructionData_of_signRegion
        (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
    let N :=
      texMatchingProductNeighborhoodData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region
    ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
      let δ :=
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      lowerDepthAnalytic.primedLimit
          (texMatchingPrimedDialEffectiveTailPath
            (L := L) (d := d) (r := r) (θ' := θ') δ) =
        texMatchingPrimedTelescopedLimitVector θ' t p

/-- Smaller universal analytic-limit source.

The closed-recursion limits are not stored here.  They are a consequence of the active
universal analytic-limit boundary, via
`texMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation_of_univAnalyticLimitData`.
This keeps the top-level matching field at the already-existing universal analytic-limit
surface and does not use recursive `tailReduced` data. -/
structure TexMatchingLocalPatchRegularQuadricUnivAnalyticClosedRecursionLimitData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Type where
  univAnalyticLimit :
    TexMatchingLocalPatchRegularQuadricUnivAnalyticLimitData
      hL hr hstep endpoint D localRegion

namespace TexMatchingLocalPatchRegularQuadricUnivAnalyticClosedRecursionLimitData

/-- Project the lower-depth analytic data from the reduced source record. -/
def lowerDepthAnalytic
    {L d r : Nat} {hL : 0 < L} {hr : 2 <= r}
    {θ θ' : Params (L + 1) d}
    {hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ'}
    {endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ)}
    {D : IDLData (L + 1) d r θ θ'}
    {localRegion : TexRegionConstructionDataOfIDLDataObligation hL D}
    (P :
      TexMatchingLocalPatchRegularQuadricUnivAnalyticClosedRecursionLimitData
        hL hr hstep endpoint D localRegion) :
    TexMatchingRegularQuadricLowerDepthUnivTailPathFrecAnalyticData
      (r := r) (Params.tail θ) (Params.tail θ') :=
  P.univAnalyticLimit.lowerDepthAnalytic

end TexMatchingLocalPatchRegularQuadricUnivAnalyticClosedRecursionLimitData

/-- Non-circular source for the active universal analytic closed-recursion boundary.

This stores the universal lower-depth analytic data directly, together with the
selected closed-recursion limits, instead of deriving either field from recursive
`tailReduced` data. -/
structure TexMatchingLocalPatchRegularQuadricUnivAnalyticClosedRecursionSourceData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Type where
  lowerDepthAnalytic :
    TexMatchingRegularQuadricLowerDepthUnivTailPathFrecAnalyticData
      (r := r) (Params.tail θ) (Params.tail θ')
  closedRecursionLimits :
    TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
      hL hr hstep endpoint D localRegion

/-- Compile the smaller universal analytic-limit input to closed-recursion limits. -/
theorem
    texMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation_of_univAnalyticLimitData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (P :
      TexMatchingLocalPatchRegularQuadricUnivAnalyticLimitData
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation_of_univAnalytic_limits
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    P.lowerDepthAnalytic P.unprimed_limit_eq P.primed_limit_eq

namespace TexMatchingLocalPatchRegularQuadricUnivAnalyticClosedRecursionSourceData

end TexMatchingLocalPatchRegularQuadricUnivAnalyticClosedRecursionSourceData

namespace TexMatchingLocalPatchRegularQuadricUnivAnalyticClosedRecursionLimitData

/-- Derive the selected closed-recursion limits from the reduced source record. -/
theorem closedRecursionLimits
    {L d r : Nat} {hL : 0 < L} {hr : 2 <= r}
    {θ θ' : Params (L + 1) d}
    {hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ'}
    {endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ)}
    {D : IDLData (L + 1) d r θ θ'}
    {localRegion : TexRegionConstructionDataOfIDLDataObligation hL D}
    (P :
      TexMatchingLocalPatchRegularQuadricUnivAnalyticClosedRecursionLimitData
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation_of_univAnalyticLimitData
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    P.univAnalyticLimit

end TexMatchingLocalPatchRegularQuadricUnivAnalyticClosedRecursionLimitData

/-- Realized-tail selected effective-tail data from universal lower-depth convergence.

The universal convergence record is only restricted to the two realized-tail path
classes used by the recursive node.  Dial membership is still supplied by the swept
realized-tail path identity, so this keeps the matching side at selected dials. -/
noncomputable def
    texMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData_of_realizedTailMem_univAnalytic
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (θfull : Params (L + 2) d)
    (FullPaths : Set (ProbePath d))
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (realized :
      TexMatchingLocalPatchRegularQuadricDialRealizedTailMemObligation
        hL hr hstep endpoint D localRegion θfull FullPaths)
    (analytic :
      TexMatchingRegularQuadricLowerDepthUnivTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ')) :
    TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData_of_realizedTailDialMem_lowerDepthTailPath
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    (texMatchingLocalPatchRegularQuadricDialMemObligation_of_realizedTailMemObligation
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      θfull FullPaths hPaths realized)
    (texMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData_of_univData_restrict
      (r := r) (θtail := Params.tail θ) (θtail' := Params.tail θ')
      (UnprimedTailPaths := realizedTailPathSet r θ D.Paths)
      (PrimedTailPaths := realizedTailPathSet r θ' D.Paths)
      analytic)

/-- Realized-tail `Frec` provider from universal lower-depth convergence and selected
closed-recursion limits.

This is the realized-tail analogue of the universal closed-recursion source compiler:
selected effective-tail convergence is obtained by restricting universal lower-depth
convergence to the realized-tail classes, while the selected limit identifications are
compiled from the closed-recursion package. -/
noncomputable def
    texMatchingLocalPatchRegularQuadricFrecProviderData_of_realizedTailMem_univAnalytic_closedRecursionLimits
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (θfull : Params (L + 2) d)
    (FullPaths : Set (ProbePath d))
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (realized :
      TexMatchingLocalPatchRegularQuadricDialRealizedTailMemObligation
        hL hr hstep endpoint D localRegion θfull FullPaths)
    (analytic :
      TexMatchingRegularQuadricLowerDepthUnivTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ'))
    (hlimits :
      TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricFrecProviderData
      hL hr hstep endpoint D localRegion :=
  let hdial_mem :
      TexMatchingLocalPatchRegularQuadricDialMemObligation
        hL hr hstep endpoint D localRegion :=
    texMatchingLocalPatchRegularQuadricDialMemObligation_of_realizedTailMemObligation
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      θfull FullPaths hPaths realized
  let selected :
      TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData
        hL hr hstep endpoint D localRegion :=
    texMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData_of_realizedTailMem_univAnalytic
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      θfull FullPaths hPaths realized analytic
  let selectedLimits :
      TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailLimitIdentificationData
        hL hr hstep endpoint D localRegion selected :=
    texMatchingLocalPatchRegularQuadricSelectedEffectiveTailLimitIdentificationData_of_closedRecursionLimits
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
      selected hlimits
  texMatchingLocalPatchRegularQuadricFrecProviderData_of_effectiveTailData
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    { dial_mem := hdial_mem
      unprimed :=
        texMatchingLocalPatchRegularQuadricUnprimedSaturatedEffectiveTailFrecAsymptotic_of_selectedEffectiveTailData
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
          selected selectedLimits
      primed :=
        texMatchingLocalPatchRegularQuadricPrimedTelescopedEffectiveTailFrecAsymptotic_of_selectedEffectiveTailData
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
          selected selectedLimits }

/-- Non-circular source for a realized-tail recursive local matching node.

The record mirrors the reduced realized-tail matching frontier without depending on the
downstream recursive record: swept selected-dial membership, universal lower-depth
convergence, and selected closed-recursion limits. -/
structure
    TexMatchingLocalPatchRegularQuadricRealizedTailUnivAnalyticClosedRecursionSourceData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (θfull : Params (L + 2) d)
    (FullPaths : Set (ProbePath d))
    (_hPaths : D.Paths = realizedTailPathSet r θfull FullPaths) : Type where
  realized :
    TexMatchingLocalPatchRegularQuadricDialRealizedTailMemObligation
      hL hr hstep endpoint D localRegion θfull FullPaths
  lowerDepthAnalytic :
    TexMatchingRegularQuadricLowerDepthUnivTailPathFrecAnalyticData
      (r := r) (Params.tail θ) (Params.tail θ')
  closedRecursionLimits :
    TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
      hL hr hstep endpoint D localRegion

namespace TexMatchingLocalPatchRegularQuadricRealizedTailUnivAnalyticClosedRecursionSourceData

/-- Project the selected dial membership needed by the downstream reduced realized-tail
matching record. -/
theorem dial_mem
    {L d r : Nat} {hL : 0 < L} {hr : 2 <= r}
    {θ θ' : Params (L + 1) d}
    {hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ'}
    {endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ)}
    {D : IDLData (L + 1) d r θ θ'}
    {localRegion : TexRegionConstructionDataOfIDLDataObligation hL D}
    {θfull : Params (L + 2) d}
    {FullPaths : Set (ProbePath d)}
    {hPaths : D.Paths = realizedTailPathSet r θfull FullPaths}
    (P :
      TexMatchingLocalPatchRegularQuadricRealizedTailUnivAnalyticClosedRecursionSourceData
        hL hr hstep endpoint D localRegion θfull FullPaths hPaths) :
    TexMatchingLocalPatchRegularQuadricDialMemObligation
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricDialMemObligation_of_realizedTailMemObligation
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    θfull FullPaths hPaths P.realized

/-- Project selected effective-tail convergence from the realized-tail source wrapper. -/
noncomputable def selectedEffectiveTail
    {L d r : Nat} {hL : 0 < L} {hr : 2 <= r}
    {θ θ' : Params (L + 1) d}
    {hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ'}
    {endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ)}
    {D : IDLData (L + 1) d r θ θ'}
    {localRegion : TexRegionConstructionDataOfIDLDataObligation hL D}
    {θfull : Params (L + 2) d}
    {FullPaths : Set (ProbePath d)}
    {hPaths : D.Paths = realizedTailPathSet r θfull FullPaths}
    (P :
      TexMatchingLocalPatchRegularQuadricRealizedTailUnivAnalyticClosedRecursionSourceData
        hL hr hstep endpoint D localRegion θfull FullPaths hPaths) :
    TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData_of_realizedTailMem_univAnalytic
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    θfull FullPaths hPaths P.realized P.lowerDepthAnalytic

/-- Compile the realized-tail source wrapper to the full local-patch `Frec` provider. -/
noncomputable def toProviderData
    {L d r : Nat} {hL : 0 < L} {hr : 2 <= r}
    {θ θ' : Params (L + 1) d}
    {hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ'}
    {endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ)}
    {D : IDLData (L + 1) d r θ θ'}
    {localRegion : TexRegionConstructionDataOfIDLDataObligation hL D}
    {θfull : Params (L + 2) d}
    {FullPaths : Set (ProbePath d)}
    {hPaths : D.Paths = realizedTailPathSet r θfull FullPaths}
    (P :
      TexMatchingLocalPatchRegularQuadricRealizedTailUnivAnalyticClosedRecursionSourceData
        hL hr hstep endpoint D localRegion θfull FullPaths hPaths) :
    TexMatchingLocalPatchRegularQuadricFrecProviderData
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricFrecProviderData_of_realizedTailMem_univAnalytic_closedRecursionLimits
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    θfull FullPaths hPaths P.realized P.lowerDepthAnalytic P.closedRecursionLimits

end TexMatchingLocalPatchRegularQuadricRealizedTailUnivAnalyticClosedRecursionSourceData

/-- Convert the reduced local-patch provider to the existing no-legacy matching provider.
This is the point where the `region` field is filled mechanically. -/
noncomputable def texMatchingRegionProviderData_of_localPatch
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (P :
      TexMatchingRegionProviderFromLocalPatchData
        hL hr hstep endpoint D localRegion) :
    TexMatchingRegionProviderData hr hstep endpoint D where
  region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
  bridge := P.bridge

/-- Compile the no-legacy region/matching provider to the analytic data consumed by
`firstLayerMatched_of_texGenericStep_of_IDLData`. -/
noncomputable def texFirstLayerMatchingAnalyticData_of_provider
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (P : TexMatchingRegionProviderData hr hstep endpoint D) :
    TexFirstLayerMatchingAnalyticData hr hstep endpoint D := by
  exact
    { signRegion :=
        texMatchingSignRegionData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D P.region
      neighborhood :=
        texMatchingProductNeighborhoodData_of_region
          (L := L) (d := d) (r := r) hr hstep endpoint D P.region
      bridge := P.bridge }

/-- First-layer matching support package with the trichotomy supplied explicitly.

This is the builder-compatible variant of `TexFirstLayerMatchingAnalyticData`: callers
choose the sign region, trichotomy construction, product patch, saturated
contribution, and dial-path bridge directly.  In particular, this record does not
rebuild `T` from `texTrichotomyConstructionData_of_signRegion`. -/
structure TexFirstLayerMatchingAnalyticDataOfTrichotomy {L d r : Nat}
    (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ') : Type where
  signRegion :
    SignRegionData (L := L + 1) (d := d) θ' D.O
      (Params.headAttention θ') (Real.log (r : ℝ))
  T :
    TexTrichotomyConstructionData (L := L + 1) (d := d)
      (Real.log (r : ℝ)) signRegion.U
  neighborhood :
    TexMatchingProductNeighborhoodData (d := d)
      (Params.headAttention θ') T.Ustar
  S : TexMatchingSaturatedContributionData θ T.trichotomy.varsigma
  bridge : TexMatchingDialPathLimitBridgeData D neighborhood S

/-- Compile the explicit sign-region/product/dial bridge package to the matching-limit
endpoint consumed by the already-formalized `K = I` extraction. -/
noncomputable def matchingLimitData_of_IDLData_of_matchingAnalyticData
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (B : TexFirstLayerMatchingAnalyticData hr hstep endpoint D) :
    MatchingLimitData θ θ' := by
  let T :=
    texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D B.signRegion
  let S :=
    texMatchingSaturatedContributionData_of_trichotomy
      (L := L) (d := d) (r := r) hr hstep endpoint D B.signRegion T
      B.neighborhood
  exact
    matchingLimitData_of_IDLData_of_dialPathLimitBridge
      (L := L) (d := d) (r := r) hr hstep endpoint D B.signRegion T
      B.neighborhood S B.bridge

/-- Compile the explicit-trichotomy first-layer matching package to matching-limit
data. -/
noncomputable def matchingLimitData_of_IDLData_of_matchingAnalyticDataOfTrichotomy
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (B : TexFirstLayerMatchingAnalyticDataOfTrichotomy hr hstep endpoint D) :
    MatchingLimitData θ θ' :=
  matchingLimitData_of_IDLData_of_dialPathLimitBridge
    (L := L) (d := d) (r := r) hr hstep endpoint D B.signRegion B.T
    B.neighborhood B.S B.bridge

/-- First-layer matching endpoint from an explicit-trichotomy IDL matching bridge. -/
theorem firstLayerMatched_of_texGenericStep_of_IDLData_trichotomy
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (B : TexFirstLayerMatchingAnalyticDataOfTrichotomy hr hstep endpoint D) :
    FirstLayerMatchedData θ θ' := by
  let limitData :=
    matchingLimitData_of_IDLData_of_matchingAnalyticDataOfTrichotomy
      (L := L) (d := d) (r := r) hr hstep endpoint D B
  let matching := limitData.toFirstLayerMatchingData
  refine FirstLayerMatchedData.ofEndpointAndHeadValueEq endpoint ?_
  simpa [Params.headValue, Params.headLayer] using matching.headValue_eq

/-- Builder-backed first-layer matching support from universal paths and canonical
actual gates.

The trichotomy is the explicit cascade-builder trichotomy, not the legacy
constructor-level sign-region shortcut. -/
noncomputable def
    texFirstLayerMatchingAnalyticDataOfTrichotomy_of_cascadeBuilder_paths_univ_lowerDepthSelectedTail
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' θB : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (hPaths : D.Paths = Set.univ)
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' D.O
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
    TexFirstLayerMatchingAnalyticDataOfTrichotomy hr hstep endpoint D := by
  let T := texTrichotomyConstructionData_of_cascadeBuilder B
  let hclosedBuilder :
      TexMatchingRegularQuadricClosedRecursionLimitObligation signRegion T N S := by
    simpa [T] using
      texMatchingRegularQuadricClosedRecursionLimitObligation_of_cascadeBuilder
        signRegion B N S hAA actual
  let hclosed :
      TexMatchingRegularQuadricClosedRecursionLimitObligation signRegion T N S :=
    hclosedBuilder
  let hlimit :
      TexMatchingRegularQuadricLimitVectorObligation signRegion T N S :=
    texMatchingRegularQuadricLimitVectorObligation_of_closedRecursionLimits
      (L := L) (d := d) (r := r) (by omega) signRegion T N S hclosed
  let hdial_mem : TexMatchingRegularQuadricDialMemObligation D signRegion T N :=
    texMatchingRegularQuadricDialMemObligation_of_paths_univ
      D hPaths signRegion T N
  let bridge : TexMatchingDialPathLimitBridgeData D N S :=
    texMatchingDialPathLimitBridgeData_of_regularQuadricLimit
      (L := L) (d := d) (r := r) D signRegion T N S hdial_mem hlimit
  exact
    { signRegion := signRegion
      T := T
      neighborhood := N
      S := S
      bridge := bridge }

/-- First-layer matching endpoint from the explicit IDL matching bridge, with no
legacy `TexFirstLayerMatchingConstructionData` argument. -/
theorem firstLayerMatched_of_texGenericStep_of_IDLData
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (B : TexFirstLayerMatchingAnalyticData hr hstep endpoint D) :
    FirstLayerMatchedData θ θ' := by
  let limitData :=
    matchingLimitData_of_IDLData_of_matchingAnalyticData
      (L := L) (d := d) (r := r) hr hstep endpoint D B
  let matching := limitData.toFirstLayerMatchingData
  refine FirstLayerMatchedData.ofEndpointAndHeadValueEq endpoint ?_
  simpa [Params.headValue, Params.headLayer] using matching.headValue_eq

/-- Provider-facing first-layer matching support from universal paths and canonical
actual gates. -/
noncomputable def
    texFirstLayerMatchingAnalyticDataOfTrichotomy_of_inductionProvider_paths_univ_lowerDepthSelectedTail
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' θB : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (hPaths : D.Paths = Set.univ)
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' D.O
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
    TexFirstLayerMatchingAnalyticDataOfTrichotomy hr hstep endpoint D :=
  texFirstLayerMatchingAnalyticDataOfTrichotomy_of_cascadeBuilder_paths_univ_lowerDepthSelectedTail
    (L := L) (d := d) (r := r) hr hstep endpoint D hPaths signRegion
    P.toBuilderData N S hAA actual

/-- Legacy explicit TeX Step 2 construction package for callers that already have the
region and matching constructions.  The mathematical boundary is
`MatchingLimitData`/`MatchingCoefficientComparisonData`; this package is only one
constructor-level route to those endpoints. -/
structure TexFirstLayerMatchingConstructionData {L d r : Nat}
    (θ θ' : Params (L + 1) d)
    (D : IDLData (L + 1) d r θ θ') : Type where
  region :
    TexRegionConstructionData (L := L + 1) (d := d) θ' D.O
      (Params.headAttention θ') (Real.log (r : ℝ))
  matching :
    TexMatchingConstructionData θ θ' (Real.log (r : ℝ)) region.U

/-! ## Gate-saturation bridge to universal lower-depth `Frec` convergence

The universal lower-depth `Frec` convergence consumed by the closed-recursion / universal
analytic matching boundary is the genuine analytic input of TeX Step 2 (the reduction of
both networks to affine saturated-limit maps).  It is *not* derivable from the
sweep/`tailReduced` package, which is only built after matching; sourcing it from there
would be circular.

The lemmas below isolate that input at its true mathematical seed — the exponential gate
saturation already produced upstream as `EventuallyExpClose` (the output shape of
`TrichotomyData`) — and compile it to the universal analytic-limit boundary.  A caller who
proves componentwise exponential saturation of the tail recursion along every probe path
(`TexMatchingLowerDepthUnivFrecSaturationObligation`) plus the two selected dial-limit
identifications obtains the active boundary with no recursive-tail dependency. -/

/-- The remaining genuinely-analytic obligation behind the universal lower-depth `Frec`
convergence, isolated as componentwise exponential saturation of the tail recursion
along every probe path.

A witness supplies, for both tail networks and every probe path, a limit vector and a
proof that each coordinate of the closed-form recursion is exponentially close to that
limit.  This is exactly the TeX "reduction to affine saturated-limit maps" content; it
is *not* derivable from the sweep/`tailReduced` package (which is built only after
matching), so it is left as a precise named obligation. -/
structure TexMatchingLowerDepthUnivFrecSaturationObligation
    {L d r : Nat} (θtail θtail' : Params L d) : Type where
  unprimedLimit : ProbePath d -> Fin d -> ℝ
  primedLimit : ProbePath d -> Fin d -> ℝ
  unprimed_expClose :
    ∀ (P : ProbePath d) (i : Fin d),
      EventuallyExpClose (fun τ => Frec r θtail (P τ).1 (P τ).2 τ i) (unprimedLimit P i)
  primed_expClose :
    ∀ (P : ProbePath d) (i : Fin d),
      EventuallyExpClose (fun τ => Frec r θtail' (P τ).1 (P τ).2 τ i) (primedLimit P i)

set_option linter.style.longLine false in
/-- **Genuine-trichotomy closed-recursion limits, derived unconditionally from
genericity.**

This is the sound replacement for the `varsigma ≡ 1` placeholder route
(`trichotomyData_constOne_of_signRegion`).  It produces the TeX Proposition `matching`
closed-recursion limit obligation — the saturated unprimed limit and the telescoped
primed limit along *every* canonical regular-quadric product-patch dial — for the
**genuine** solved-coordinate cascade trichotomy
`texTrichotomyConstructionData_of_inductionProvider`.

Every gate function is the actual `canonicalFrecGateAlongSignRegion r signRegion θ`/`θ'`
running gate, so the limit vectors are the genuine saturated/telescoped vectors (not the
constant-one placeholder) and the `TexTrichotomyMatchingCanonicalActualGateData` package
is discharged by `rfl`.  The hard cascade content — the `Λ ≠ 0` sign saturation and the
`Λ ≡ 0` zero branch — is supplied by
`cascadeTrichotomyInductionProviderData_of_dichotomyChoices_from_solvedCoordChart_productPatchZeroBranch`.

The first-layer genericity facts are taken as explicit hypotheses: `(G1)` non-degeneracy
of `A₁'` (`head_det_ne_zero`, `head_sym_ne_zero`), the depth certificate `V₁ ≠ 0`
(`head_value_ne_zero`), and the matched first attention `A₁ = A₁'` (`hAA`). -/
noncomputable def texMatchingGenuineClosedRecursionLimitObligation_of_genericity
    {L d r : Nat}
    {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (tail0 : Nat -> ℝ)
    (dimension_pos : 0 < d)
    (head_det_ne_zero : (Params.headAttention θ').det ≠ 0)
    (head_sym_ne_zero : symPart (Params.headAttention θ') ≠ 0)
    (head_value_ne_zero : (paramStream θ 0).1 ≠ 0)
    (N :
      TexMatchingProductNeighborhoodData (d := d) (Params.headAttention θ')
        (texTrichotomyConstructionData_of_inductionProvider
          (cascadeTrichotomyInductionProviderData_of_dichotomyChoices_from_solvedCoordChart_productPatchZeroBranch
            signRegion hAA tail0 dimension_pos head_det_ne_zero head_sym_ne_zero
            head_value_ne_zero)).Ustar) :
    TexMatchingRegularQuadricClosedRecursionLimitObligation
      signRegion
      (texTrichotomyConstructionData_of_inductionProvider
        (cascadeTrichotomyInductionProviderData_of_dichotomyChoices_from_solvedCoordChart_productPatchZeroBranch
          signRegion hAA tail0 dimension_pos head_det_ne_zero head_sym_ne_zero
          head_value_ne_zero))
      N
      (texMatchingSaturatedContributionData_of_inductionProvider (θ := θ)
        (cascadeTrichotomyInductionProviderData_of_dichotomyChoices_from_solvedCoordChart_productPatchZeroBranch
          signRegion hAA tail0 dimension_pos head_det_ne_zero head_sym_ne_zero
          head_value_ne_zero)) := by
  refine
    texMatchingRegularQuadricClosedRecursionLimitObligation_of_inductionProvider
      signRegion _ N _ hAA ?_
  exact
    texTrichotomyMatchingCanonicalActualGateData_of_canonicalFrecGates
      signRegion _ N rfl rfl

set_option linter.style.longLine false in
/-- The genuine solved-coordinate cascade trichotomy induction provider attached to a
sign region, assembled from the genericity step clauses `hstep` (G1 `det`/`sym` of the
first attention matrix) and the first-layer endpoint (`A₁ = A₁'`, `V₁ ≠ 0`).

This packages the three first-layer genericity facts so the genuine trichotomy
(`texTrichotomyConstructionData_of_inductionProvider`) can be referenced without
re-deriving them at each call.  Mirrors the top-node extraction in
`IdentifiabilityMain` (`firstAttention_eq_of_pos`, `hstep.g1_det_firstAttention`,
`hstep.g1_sym_firstAttention`, `endpoint.targetValue_ne_zero`). -/
noncomputable def genuineCascadeProvider_of_signRegion
    {L d r : Nat} (hd : 2 <= d)
    {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (tail0 : Nat -> ℝ) :
    CascadeTrichotomyInductionProviderData
      (L := L + 1) (d := d) (Real.log (r : ℝ)) θ (Params.headAttention θ') signRegion.U
      (canonicalFrecGateAlongSignRegion r signRegion θ)
      (canonicalFrecGateAlongSignRegion r signRegion θ') :=
  cascadeTrichotomyInductionProviderData_of_dichotomyChoices_from_solvedCoordChart_productPatchZeroBranch
    signRegion endpoint.attention_eq tail0
    (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hd)
    (by
      have hfirst : firstAttention θ' = Params.headAttention θ' := by
        simpa using firstAttention_eq_of_pos θ' (Nat.succ_pos L)
      simpa [hfirst] using hstep.g1_det_firstAttention)
    (by
      have hfirst : firstAttention θ' = Params.headAttention θ' := by
        simpa using firstAttention_eq_of_pos θ' (Nat.succ_pos L)
      simpa [hfirst] using hstep.g1_sym_firstAttention)
    (by
      simpa [Params.headValue, Params.headLayer, paramStream_apply_of_lt] using
        endpoint.targetValue_ne_zero)

set_option linter.style.longLine false in
/-- **Genuine closed-recursion limits, directly from genericity (`hstep`/`endpoint`).**

The fully assembled form of `texMatchingGenuineClosedRecursionLimitObligation_of_genericity`:
the genericity facts are extracted from `hstep` and `endpoint`, and the product
neighborhood `N` is built over the genuine trichotomy component via
`texMatchingProductNeighborhoodData_of_trichotomy`.  The result is the true
saturated/telescoped closed-recursion limit obligation for the genuine solved-coordinate
cascade trichotomy — the sound replacement for the `varsigma ≡ 1` placeholder that the
local-patch matching abbreviations currently use.

This is the term that will fill the `closedRecursionLimits` leaf field once the matching
boundary is re-typed from the placeholder trichotomy to the genuine one. -/
noncomputable def texMatchingGenuineClosedRecursionLimitObligation_of_signRegion
    {L d r : Nat} (hr : 2 <= r) (hd : 2 <= d)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (tail0 : Nat -> ℝ) :
    TexMatchingRegularQuadricClosedRecursionLimitObligation
      signRegion
      (texTrichotomyConstructionData_of_inductionProvider
        (genuineCascadeProvider_of_signRegion hd hstep endpoint signRegion tail0))
      (texMatchingProductNeighborhoodData_of_trichotomy
        (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
        (texTrichotomyConstructionData_of_inductionProvider
          (genuineCascadeProvider_of_signRegion hd hstep endpoint signRegion tail0)))
      (texMatchingSaturatedContributionData_of_inductionProvider (θ := θ)
        (genuineCascadeProvider_of_signRegion hd hstep endpoint signRegion tail0)) :=
  texMatchingGenuineClosedRecursionLimitObligation_of_genericity
    signRegion endpoint.attention_eq tail0 _ _ _ _
    (texMatchingProductNeighborhoodData_of_trichotomy
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
      (texTrichotomyConstructionData_of_inductionProvider
        (genuineCascadeProvider_of_signRegion hd hstep endpoint signRegion tail0)))

end TransformerIdentifiability.NLayer
