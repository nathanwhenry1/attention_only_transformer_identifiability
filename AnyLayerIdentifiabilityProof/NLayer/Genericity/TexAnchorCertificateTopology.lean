import AnyLayerIdentifiabilityProof.NLayer.Genericity.TexGenericOpenDense
import AnyLayerIdentifiabilityProof.NLayer.Foundations.ParamPolynomialGenericity
import AnyLayerIdentifiabilityProof.NLayer.Foundations.PolynomialGenericity

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

open Matrix

/-!
# Topology of the exact TeX anchor-certificate locus

This file isolates the `(G4)` topology obligation.  The openness part is proved
directly from the concrete certificate expression.  Density is left behind a precise
polynomial/witness bridge: a dense set of parameters admitting one nonzero certificate
evaluation.
-/

theorem texAnchorCertificate_continuous_matrix_entry {X : Type*} [TopologicalSpace X]
    {m n : Type*} {M : X -> Matrix m n ℝ} (hM : Continuous M) (i : m) (j : n) :
    Continuous fun x => M x i j :=
  (continuous_apply j).comp ((continuous_apply i).comp hM)

theorem texAnchorCertificate_continuous_vector_entry {X : Type*} [TopologicalSpace X]
    {ι : Type*} {v : X -> ι -> ℝ} (hv : Continuous v) (i : ι) :
    Continuous fun x => v x i :=
  (continuous_apply i).comp hv

theorem texAnchorCertificate_continuous_matrix_add {X : Type*} [TopologicalSpace X]
    {m n : Type*} {A B : X -> Matrix m n ℝ}
    (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => A x + B x := by
  refine continuous_matrix ?_
  intro i j
  exact
    (texAnchorCertificate_continuous_matrix_entry hA i j).add
      (texAnchorCertificate_continuous_matrix_entry hB i j)

theorem texAnchorCertificate_continuous_matrix_sub {X : Type*} [TopologicalSpace X]
    {m n : Type*} {A B : X -> Matrix m n ℝ}
    (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => A x - B x := by
  refine continuous_matrix ?_
  intro i j
  exact
    (texAnchorCertificate_continuous_matrix_entry hA i j).sub
      (texAnchorCertificate_continuous_matrix_entry hB i j)

theorem texAnchorCertificate_continuous_matrix_smul {X : Type*} [TopologicalSpace X]
    {m n : Type*} {c : X -> ℝ} {A : X -> Matrix m n ℝ}
    (hc : Continuous c) (hA : Continuous A) :
    Continuous fun x => c x • A x := by
  refine continuous_matrix ?_
  intro i j
  simpa [Matrix.smul_apply] using
    hc.mul (texAnchorCertificate_continuous_matrix_entry hA i j)

theorem texAnchorCertificate_continuous_matrix_transpose {X : Type*} [TopologicalSpace X]
    {m n : Type*} {A : X -> Matrix m n ℝ} (hA : Continuous A) :
    Continuous fun x => (A x)ᵀ := by
  refine continuous_matrix ?_
  intro i j
  simpa [Matrix.transpose_apply] using
    texAnchorCertificate_continuous_matrix_entry hA j i

theorem texAnchorCertificate_continuous_matrix_mul {X : Type*} [TopologicalSpace X]
    {m n p : Type*} [Fintype n] {A : X -> Matrix m n ℝ} {B : X -> Matrix n p ℝ}
    (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => A x * B x := by
  refine continuous_matrix ?_
  intro i j
  simpa [Matrix.mul_apply] using
    (continuous_finsetSum Finset.univ fun k _ =>
      (texAnchorCertificate_continuous_matrix_entry hA i k).mul
        (texAnchorCertificate_continuous_matrix_entry hB k j))

theorem texAnchorCertificate_continuous_matrix_det {X : Type*} [TopologicalSpace X]
    {n : Type*} [Fintype n] [DecidableEq n] {A : X -> Matrix n n ℝ}
    (hA : Continuous A) :
    Continuous fun x => (A x).det := by
  simpa [Matrix.det_apply] using
    (continuous_finsetSum Finset.univ fun σ _ => by
    have hprod : Continuous fun x => ∏ i : n, A x (σ i) i := by
      simpa using
        (continuous_finsetProd Finset.univ fun i _ =>
          texAnchorCertificate_continuous_matrix_entry hA (σ i) i)
    simpa using hprod.const_smul (Equiv.Perm.sign σ))

theorem texAnchorCertificate_continuous_updateRow_single {X : Type*}
    [TopologicalSpace X] {n : Type*} [DecidableEq n] {A : X -> Matrix n n ℝ}
    (hA : Continuous A) (i row : n) :
    Continuous fun x => (A x).updateRow row (Pi.single i (1 : ℝ)) := by
  refine continuous_matrix ?_
  intro r c
  by_cases hrow : r = row
  · subst r
    simpa [Matrix.updateRow_self] using
      (continuous_const : Continuous fun _ : X => (Pi.single i (1 : ℝ) : n -> ℝ) c)
  · simpa [Matrix.updateRow_ne hrow] using
      texAnchorCertificate_continuous_matrix_entry hA r c

theorem texAnchorCertificate_continuous_matrix_adjugate {X : Type*}
    [TopologicalSpace X] {n : Type*} [Fintype n] [DecidableEq n]
    {A : X -> Matrix n n ℝ}
    (hA : Continuous A) :
    Continuous fun x => (A x).adjugate := by
  refine continuous_matrix ?_
  intro i j
  simpa [Matrix.adjugate_apply] using
    texAnchorCertificate_continuous_matrix_det
      (texAnchorCertificate_continuous_updateRow_single hA i j)

theorem texAnchorCertificate_continuous_mulVec {X : Type*} [TopologicalSpace X]
    {m n : Type*} [Fintype n] {A : X -> Matrix m n ℝ} {v : X -> n -> ℝ}
    (hA : Continuous A) (hv : Continuous v) :
    Continuous fun x => (A x).mulVec (v x) := by
  rw [continuous_pi_iff]
  intro i
  simpa [Matrix.mulVec, dotProduct] using
    (continuous_finsetSum Finset.univ fun j _ =>
      (texAnchorCertificate_continuous_matrix_entry hA i j).mul
        (texAnchorCertificate_continuous_vector_entry hv j))

theorem texAnchorCertificate_continuous_dotProduct {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι] {v w : X -> ι -> ℝ}
    (hv : Continuous v) (hw : Continuous w) :
    Continuous fun x => v x ⬝ᵥ w x := by
  simpa [dotProduct] using
    (continuous_finsetSum Finset.univ fun i _ =>
      (texAnchorCertificate_continuous_vector_entry hv i).mul
        (texAnchorCertificate_continuous_vector_entry hw i))

theorem texAnchorCertificate_continuous_paramStream_apply {L d n : Nat} :
    Continuous (fun θ : Params L d => paramStream θ n) := by
  by_cases h : n < L
  · simpa [paramStream, h] using
      (continuous_apply (⟨n, h⟩ : Fin L) :
        Continuous fun θ : Params L d => θ ⟨n, h⟩)
  · simpa [paramStream, h] using
      (continuous_const : Continuous fun _ : Params L d =>
        ((0, 0) : Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ))

theorem texAnchorCertificate_continuous_paramStream_value {L d n : Nat} :
    Continuous (fun θ : Params L d => (paramStream θ n).1) :=
  (continuous_fst : Continuous fun p :
    Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ => p.1).comp
      texAnchorCertificate_continuous_paramStream_apply

theorem texAnchorCertificate_continuous_paramStream_attention {L d n : Nat} :
    Continuous (fun θ : Params L d => (paramStream θ n).2) :=
  (continuous_snd : Continuous fun p :
    Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ => p.2).comp
      texAnchorCertificate_continuous_paramStream_apply

theorem texAnchorCertificate_continuous_skipB {X : Type*} [TopologicalSpace X]
    {d : Nat} {V : X -> Matrix (Fin d) (Fin d) ℝ} (hV : Continuous V) :
    Continuous fun x => skipB (V x) := by
  unfold skipB
  exact texAnchorCertificate_continuous_matrix_add continuous_const hV

theorem texAnchorCertificate_continuous_anchorStepMatrix {L d k : Nat} (t : ℝ) :
    Continuous fun θ : Params L d => anchorStepMatrix (paramStream θ) k t := by
  unfold anchorStepMatrix
  exact
    texAnchorCertificate_continuous_matrix_sub
      (texAnchorCertificate_continuous_skipB
        (texAnchorCertificate_continuous_paramStream_value (L := L) (d := d) (n := k)))
      (texAnchorCertificate_continuous_matrix_smul continuous_const
        (texAnchorCertificate_continuous_paramStream_value (L := L) (d := d) (n := k)))

theorem texAnchorCertificate_continuous_anchorRealBprod {L d n : Nat} :
    Continuous (fun θ : Params L d => anchorRealBprod (paramStream θ) n) := by
  induction n with
  | zero =>
      simpa [anchorRealBprod] using
        (continuous_const : Continuous fun _ : Params L d =>
          (1 : Matrix (Fin d) (Fin d) ℝ))
  | succ n ih =>
      simpa [anchorRealBprod] using
        texAnchorCertificate_continuous_matrix_mul
          (texAnchorCertificate_continuous_skipB
            (texAnchorCertificate_continuous_paramStream_value (L := L) (d := d) (n := n)))
          ih

theorem texAnchorCertificate_continuous_anchorRealWprod {L d n : Nat}
    (t : Nat -> ℝ) :
    Continuous (fun θ : Params L d => anchorRealWprod (paramStream θ) t n) := by
  induction n with
  | zero =>
      simpa [anchorRealWprod] using
        (continuous_const : Continuous fun _ : Params L d =>
          (1 : Matrix (Fin d) (Fin d) ℝ))
  | succ n ih =>
      simpa [anchorRealWprod] using
        texAnchorCertificate_continuous_matrix_mul
          (texAnchorCertificate_continuous_anchorStepMatrix (L := L) (d := d) (k := n) (t n))
          ih

theorem texAnchorCertificate_continuous_anchorCertificateW {L d k : Nat}
    (t : AnchorGateVector L) (w0 : Fin d -> ℝ) :
    Continuous (fun θ : Params L d => anchorCertificateW θ t k w0) := by
  simpa [anchorCertificateW] using
    texAnchorCertificate_continuous_mulVec
      (texAnchorCertificate_continuous_anchorRealWprod (L := L) (d := d)
        (n := k) (anchorGateStream t))
      (continuous_const : Continuous fun _ : Params L d => w0)

theorem texAnchorCertificate_continuous_gradientE {L d : Nat}
    (t : AnchorGateVector L) (k : Fin (L - 1)) (w0 : Fin d -> ℝ) :
    Continuous (fun θ : Params L d => anchorCertificateGradientE θ t k w0) := by
  simpa [anchorCertificateGradientE] using
    texAnchorCertificate_continuous_mulVec
      (texAnchorCertificate_continuous_matrix_transpose
        (texAnchorCertificate_continuous_anchorRealBprod (L := L) (d := d) (n := k.val)))
      (texAnchorCertificate_continuous_mulVec
        (texAnchorCertificate_continuous_matrix_transpose
          (texAnchorCertificate_continuous_paramStream_attention (L := L) (d := d)
            (n := k.val)))
        (texAnchorCertificate_continuous_anchorCertificateW (L := L) (d := d)
          (k := k.val) t w0))

theorem texAnchorCertificate_continuous_gradientS {L d : Nat}
    (t s : AnchorGateVector L) (q : AnchorCertificateSIndex L) (w0 : Fin d -> ℝ) :
    Continuous (fun θ : Params L d => anchorCertificateGradientS θ t s q w0) := by
  let k : Fin (L - 1) := q.1
  let ell : Nat := q.2.1.val
  let n : Nat := k.val + ell - 1
  simpa [anchorCertificateGradientS, k, ell, n] using
    texAnchorCertificate_continuous_mulVec
      (texAnchorCertificate_continuous_matrix_transpose
        (texAnchorCertificate_continuous_anchorRealBprod (L := L) (d := d) (n := n)))
      (texAnchorCertificate_continuous_mulVec
        (texAnchorCertificate_continuous_matrix_transpose
          (texAnchorCertificate_continuous_paramStream_attention (L := L) (d := d) (n := n)))
        (texAnchorCertificate_continuous_mulVec
          (texAnchorCertificate_continuous_anchorStepMatrix (L := L) (d := d)
            (k := k.val) (s k))
          (texAnchorCertificate_continuous_anchorCertificateW (L := L) (d := d)
            (k := k.val) t w0)))

theorem texAnchorCertificate_continuous_gradientT {L d : Nat}
    (t : AnchorGateVector L) (k : Fin (L - 1)) (w0 : Fin d -> ℝ) :
    Continuous (fun θ : Params L d => anchorCertificateGradientT θ t k w0) := by
  let hM :=
    texAnchorCertificate_continuous_anchorStepMatrix (L := L) (d := d)
      (k := k.val) (t k)
  let hWB :=
    texAnchorCertificate_continuous_matrix_transpose
      (texAnchorCertificate_continuous_anchorRealBprod (L := L) (d := d) (n := k.val))
  let hAT :=
    texAnchorCertificate_continuous_matrix_transpose
      (texAnchorCertificate_continuous_paramStream_attention (L := L) (d := d) (n := k.val))
  let hy :=
    texAnchorCertificate_continuous_mulVec
      (texAnchorCertificate_continuous_paramStream_value (L := L) (d := d) (n := k.val))
      (texAnchorCertificate_continuous_anchorCertificateW (L := L) (d := d)
        (k := k.val) t w0)
  let hz :=
    texAnchorCertificate_continuous_mulVec
      (texAnchorCertificate_continuous_matrix_adjugate hM) hy
  let hu := texAnchorCertificate_continuous_mulVec hAT hz
  have hWBu := texAnchorCertificate_continuous_mulVec hWB hu
  rw [continuous_pi_iff]
  intro i
  simpa [anchorCertificateGradientT] using
    (texAnchorCertificate_continuous_vector_entry hWBu i).neg

theorem texAnchorCertificate_continuous_gradient {L d : Nat}
    (t s : AnchorGateVector L) (row : AnchorCertificateRow L) (w0 : Fin d -> ℝ) :
    Continuous (fun θ : Params L d => anchorCertificateGradient θ t s row w0) := by
  cases row with
  | inl row =>
      cases row with
      | inl k =>
          simpa [anchorCertificateGradient] using
            texAnchorCertificate_continuous_gradientE (L := L) (d := d) t k w0
      | inr q =>
          simpa [anchorCertificateGradient] using
            texAnchorCertificate_continuous_gradientS (L := L) (d := d) t s q w0
  | inr k =>
      simpa [anchorCertificateGradient] using
        texAnchorCertificate_continuous_gradientT (L := L) (d := d) t k w0

theorem texAnchorCertificate_continuous_gradientMatrix {L d : Nat}
    (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) :
    Continuous (fun θ : Params L d => anchorCertificateGradientMatrix θ t s w0) := by
  refine continuous_matrix ?_
  intro i row
  simpa [anchorCertificateGradientMatrix, Matrix.of_apply] using
    texAnchorCertificate_continuous_vector_entry
      (texAnchorCertificate_continuous_gradient (L := L) (d := d) t s row w0) i

theorem texAnchorCertificate_continuous_value {L d : Nat}
    (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) :
    Continuous (fun θ : Params L d => anchorCertificateValue θ t s w0) := by
  let hG := texAnchorCertificate_continuous_gradientMatrix (L := L) (d := d) t s w0
  let hGram :=
    texAnchorCertificate_continuous_matrix_mul
      (texAnchorCertificate_continuous_matrix_transpose hG) hG
  have hGramDet : Continuous fun θ : Params L d =>
      ((Matrix.transpose (anchorCertificateGradientMatrix θ t s w0) *
          anchorCertificateGradientMatrix θ t s w0) :
        Matrix (AnchorCertificateRow L) (AnchorCertificateRow L) ℝ).det :=
    texAnchorCertificate_continuous_matrix_det hGram
  have hStepProd : Continuous fun θ : Params L d =>
      ∏ k : Fin (L - 1), (anchorStepMatrix (paramStream θ) k.val (t k)).det := by
    simpa using
      (continuous_finsetProd Finset.univ fun k _ =>
        texAnchorCertificate_continuous_matrix_det
          (texAnchorCertificate_continuous_anchorStepMatrix (L := L) (d := d)
            (k := k.val) (t k)))
  have hNormProd : Continuous fun θ : Params L d =>
      ∏ k : Fin (L - 1),
        vectorNormSq ((Matrix.transpose (paramStream θ k.val).2).mulVec
          (anchorCertificateW θ t k.val w0)) := by
    simpa [vectorNormSq] using
      (continuous_finsetProd Finset.univ fun k _ =>
        texAnchorCertificate_continuous_dotProduct
          (texAnchorCertificate_continuous_mulVec
            (texAnchorCertificate_continuous_matrix_transpose
              (texAnchorCertificate_continuous_paramStream_attention (L := L) (d := d)
                (n := k.val)))
            (texAnchorCertificate_continuous_anchorCertificateW (L := L) (d := d)
              (k := k.val) t w0))
          (texAnchorCertificate_continuous_mulVec
            (texAnchorCertificate_continuous_matrix_transpose
              (texAnchorCertificate_continuous_paramStream_attention (L := L) (d := d)
                (n := k.val)))
            (texAnchorCertificate_continuous_anchorCertificateW (L := L) (d := d)
              (k := k.val) t w0)))
  simpa [anchorCertificateValue] using (hGramDet.mul hStepProd).mul hNormProd

theorem texAnchorCertificate_isOpen_set (L d : Nat) :
    IsOpen (TexAnchorCertificateSet L d) := by
  unfold TexAnchorCertificateSet TexAnchorCertificate
  simp only [Set.setOf_exists]
  refine isOpen_iUnion fun t => isOpen_iUnion fun s => isOpen_iUnion fun w0 => ?_
  exact (texAnchorCertificate_continuous_value (L := L) (d := d) t s w0).isOpen_preimage
    {x : ℝ | x ≠ 0} isOpen_ne

/-- Inverse to `paramFlat`, localized to the anchor-certificate topology shard. -/
noncomputable def texAnchorCertificate_paramUnflat {L d : Nat}
    (x : ParamCoord L d -> ℝ) : Params L d :=
  fun l =>
    (Matrix.of fun i j => x (l, Sum.inl (i, j)),
      Matrix.of fun i j => x (l, Sum.inr (i, j)))

/-- Flattening parameters to coordinate functions is a homeomorphism. -/
noncomputable def texAnchorCertificate_paramFlatHomeomorph (L d : Nat) :
    Params L d ≃ₜ (ParamCoord L d -> ℝ) where
  toFun := paramFlat
  invFun := texAnchorCertificate_paramUnflat
  left_inv := by
    intro θ
    funext l
    ext i j <;> rfl
  right_inv := by
    intro x
    funext c
    rcases c with ⟨l, c⟩
    cases c <;> rfl
  continuous_toFun := by
    rw [continuous_pi_iff]
    intro c
    rcases c with ⟨l, c⟩
    cases c with
    | inl ij =>
        exact
          (continuous_apply ij.2).comp
            ((continuous_apply ij.1).comp
              ((continuous_fst : Continuous fun p :
                  Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ => p.1).comp
                (continuous_apply l)))
    | inr ij =>
        exact
          (continuous_apply ij.2).comp
            ((continuous_apply ij.1).comp
              ((continuous_snd : Continuous fun p :
                  Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ => p.2).comp
                (continuous_apply l)))
  continuous_invFun := by
    rw [continuous_pi_iff]
    intro l
    refine Continuous.prodMk ?_ ?_
    · refine continuous_matrix ?_
      intro i j
      exact continuous_apply (l, Sum.inl (i, j))
    · refine continuous_matrix ?_
      intro i j
      exact continuous_apply (l, Sum.inr (i, j))

theorem texAnchorCertificate_dense_paramNonvanishingCarrier {L d : Nat} {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (D : PolynomialNonvanishingData (ParamCoord L d) κ) :
    Dense (paramNonvanishingCarrier D) := by
  simpa [paramNonvanishingCarrier] using
    (PolynomialNonvanishingData.dense_carrier D).preimage
      (texAnchorCertificate_paramFlatHomeomorph L d).isOpenMap

/-! ## Coefficient-polynomial package for the anchor certificate -/

/-- Auxiliary variables in the TeX anchor-certificate expression:
`t`, `s`, and the base vector `w^circ`. -/
abbrev TexAnchorCertificateAuxCoord (L d : Nat) : Type :=
  (Fin (L - 1) ⊕ Fin (L - 1)) ⊕ Fin d

/-- Variables for the full certificate polynomial, with auxiliary variables first so
`MvPolynomial.sumAlgEquiv` views the expression as an auxiliary polynomial whose
coefficients are parameter-coordinate polynomials. -/
abbrev TexAnchorCertificateCombinedCoord (L d : Nat) : Type :=
  TexAnchorCertificateAuxCoord L d ⊕ ParamCoord L d

/-- Coordinate ring for the full anchor-certificate expression. -/
abbrev TexAnchorCertificateCombinedRing (L d : Nat) : Type :=
  MvPolynomial (TexAnchorCertificateCombinedCoord L d) ℝ

/-- Evaluate auxiliary certificate variables from concrete `t`, `s`, and `w^circ`. -/
def texAnchorCertificate_auxEval {L d : Nat}
    (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) :
    TexAnchorCertificateAuxCoord L d -> ℝ
  | Sum.inl (Sum.inl k) => t k
  | Sum.inl (Sum.inr k) => s k
  | Sum.inr i => w0 i

/-- Evaluate the full certificate polynomial at concrete parameters and auxiliary
certificate variables. -/
def texAnchorCertificate_combinedEval {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) :
    TexAnchorCertificateCombinedCoord L d -> ℝ
  | Sum.inl a => texAnchorCertificate_auxEval t s w0 a
  | Sum.inr c => paramFlat θ c

@[simp]
theorem texAnchorCertificate_auxEval_t {L d : Nat}
    (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) (k : Fin (L - 1)) :
    texAnchorCertificate_auxEval t s w0 (Sum.inl (Sum.inl k)) = t k :=
  rfl

@[simp]
theorem texAnchorCertificate_auxEval_s {L d : Nat}
    (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) (k : Fin (L - 1)) :
    texAnchorCertificate_auxEval t s w0 (Sum.inl (Sum.inr k)) = s k :=
  rfl

@[simp]
theorem texAnchorCertificate_auxEval_w {L d : Nat}
    (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) (i : Fin d) :
    texAnchorCertificate_auxEval t s w0 (Sum.inr i) = w0 i :=
  rfl

@[simp]
theorem texAnchorCertificate_combinedEval_aux {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ)
    (a : TexAnchorCertificateAuxCoord L d) :
    texAnchorCertificate_combinedEval θ t s w0 (Sum.inl a) =
      texAnchorCertificate_auxEval t s w0 a :=
  rfl

@[simp]
theorem texAnchorCertificate_combinedEval_param {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ)
    (c : ParamCoord L d) :
    texAnchorCertificate_combinedEval θ t s w0 (Sum.inr c) = paramFlat θ c :=
  rfl

/-- Generic value matrix at a natural layer index, with zero fallback out of range. -/
noncomputable def texAnchorCertificate_genValueAt (L d : Nat) (n : Nat) :
    Matrix (Fin d) (Fin d) (TexAnchorCertificateCombinedRing L d) :=
  if h : n < L then
    Matrix.of fun i j => MvPolynomial.X (Sum.inr (⟨n, h⟩, Sum.inl (i, j)))
  else
    0

/-- Generic attention matrix at a natural layer index, with zero fallback out of range. -/
noncomputable def texAnchorCertificate_genAttentionAt (L d : Nat) (n : Nat) :
    Matrix (Fin d) (Fin d) (TexAnchorCertificateCombinedRing L d) :=
  if h : n < L then
    Matrix.of fun i j => MvPolynomial.X (Sum.inr (⟨n, h⟩, Sum.inr (i, j)))
  else
    0

@[simp]
theorem texAnchorCertificate_map_genValueAt {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) (n : Nat) :
    (texAnchorCertificate_genValueAt L d n).map
        (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)) =
      (paramStream θ n).1 := by
  by_cases h : n < L
  · ext i j
    simp [texAnchorCertificate_genValueAt, h, paramStream_apply_of_lt]
  · ext i j
    simp [texAnchorCertificate_genValueAt, h, paramStream_apply_of_not_lt]

@[simp]
theorem texAnchorCertificate_map_genAttentionAt {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) (n : Nat) :
    (texAnchorCertificate_genAttentionAt L d n).map
        (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)) =
      (paramStream θ n).2 := by
  by_cases h : n < L
  · ext i j
    simp [texAnchorCertificate_genAttentionAt, h, paramStream_apply_of_lt]
  · ext i j
    simp [texAnchorCertificate_genAttentionAt, h, paramStream_apply_of_not_lt]

/-- Generic `t_n` gate, with zero fallback outside the certificate gate range. -/
noncomputable def texAnchorCertificate_genGateT (L d : Nat) (n : Nat) :
    TexAnchorCertificateCombinedRing L d :=
  if h : n < L - 1 then
    MvPolynomial.X (Sum.inl (Sum.inl (Sum.inl ⟨n, h⟩)))
  else
    0

/-- Generic `s_n` gate, with zero fallback outside the certificate gate range. -/
noncomputable def texAnchorCertificate_genGateS (L d : Nat) (n : Nat) :
    TexAnchorCertificateCombinedRing L d :=
  if h : n < L - 1 then
    MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr ⟨n, h⟩)))
  else
    0

@[simp]
theorem texAnchorCertificate_eval_genGateT {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) (n : Nat) :
    (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))
        (texAnchorCertificate_genGateT L d n) =
      anchorGateStream t n := by
  by_cases h : n < L - 1
  · simp [texAnchorCertificate_genGateT, anchorGateStream, h]
  · simp [texAnchorCertificate_genGateT, anchorGateStream, h]

@[simp]
theorem texAnchorCertificate_eval_genGateS {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) (n : Nat) :
    (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))
        (texAnchorCertificate_genGateS L d n) =
      anchorGateStream s n := by
  by_cases h : n < L - 1
  · simp [texAnchorCertificate_genGateS, anchorGateStream, h]
  · simp [texAnchorCertificate_genGateS, anchorGateStream, h]

/-- Generic base vector `w^circ`. -/
noncomputable def texAnchorCertificate_genW0 (L d : Nat) :
    Fin d -> TexAnchorCertificateCombinedRing L d :=
  fun i => MvPolynomial.X (Sum.inl (Sum.inr i))

@[simp]
theorem texAnchorCertificate_eval_genW0 {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) :
    (fun i =>
      (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))
        (texAnchorCertificate_genW0 L d i)) = w0 := by
  funext i
  simp [texAnchorCertificate_genW0]

/-- Polynomial skip matrix `I + V`. -/
noncomputable def texAnchorCertificate_genSkipB {L d : Nat}
    (V : Matrix (Fin d) (Fin d) (TexAnchorCertificateCombinedRing L d)) :
    Matrix (Fin d) (Fin d) (TexAnchorCertificateCombinedRing L d) :=
  1 + V

theorem texAnchorCertificate_map_genSkipB {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ)
    (V : Matrix (Fin d) (Fin d) (TexAnchorCertificateCombinedRing L d)) :
    (texAnchorCertificate_genSkipB V).map
        (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)) =
      skipB (V.map (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))) := by
  ext i j
  by_cases hij : i = j
  · simp [texAnchorCertificate_genSkipB, skipB, Matrix.map_apply, Matrix.add_apply, hij]
  · simp [texAnchorCertificate_genSkipB, skipB, Matrix.map_apply, Matrix.add_apply, hij]

/-- Generic anchor step matrix `B_k - z V_k`. -/
noncomputable def texAnchorCertificate_genAnchorStepMatrix (L d k : Nat)
    (z : TexAnchorCertificateCombinedRing L d) :
    Matrix (Fin d) (Fin d) (TexAnchorCertificateCombinedRing L d) :=
  texAnchorCertificate_genSkipB (texAnchorCertificate_genValueAt L d k) -
    z • texAnchorCertificate_genValueAt L d k

theorem texAnchorCertificate_map_genAnchorStepMatrix {L d k : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ)
    (z : TexAnchorCertificateCombinedRing L d) :
    (texAnchorCertificate_genAnchorStepMatrix L d k z).map
        (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)) =
      anchorStepMatrix (paramStream θ) k
        ((MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)) z) := by
  let evalHom := MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)
  change (texAnchorCertificate_genAnchorStepMatrix L d k z).map evalHom =
    anchorStepMatrix (paramStream θ) k (evalHom z)
  rw [texAnchorCertificate_genAnchorStepMatrix, anchorStepMatrix]
  rw [Matrix.map_sub (f := evalHom) (hf := by intro a b; exact map_sub evalHom a b)]
  rw [Matrix.map_smul' (f := evalHom) (r := z)
    (A := texAnchorCertificate_genValueAt L d k)
    (hf := by intro a b; exact map_mul evalHom a b)]
  rw [texAnchorCertificate_map_genSkipB, texAnchorCertificate_map_genValueAt]

/-- Generic product `B_n ... B_1`. -/
noncomputable def texAnchorCertificate_genAnchorRealBprod (L d : Nat) :
    Nat -> Matrix (Fin d) (Fin d) (TexAnchorCertificateCombinedRing L d)
  | 0 => 1
  | n + 1 =>
      texAnchorCertificate_genSkipB (texAnchorCertificate_genValueAt L d n) *
        texAnchorCertificate_genAnchorRealBprod L d n

@[simp]
theorem texAnchorCertificate_map_genAnchorRealBprod {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) :
    ∀ n,
      (texAnchorCertificate_genAnchorRealBprod L d n).map
          (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)) =
        anchorRealBprod (paramStream θ) n
  | 0 => by
      simp [texAnchorCertificate_genAnchorRealBprod, anchorRealBprod]
  | n + 1 => by
      rw [texAnchorCertificate_genAnchorRealBprod, anchorRealBprod, Matrix.map_mul,
        texAnchorCertificate_map_genSkipB, texAnchorCertificate_map_genValueAt,
        texAnchorCertificate_map_genAnchorRealBprod θ t s w0 n]

/-- Generic product `(B_n - t_n V_n) ... (B_1 - t_1 V_1)`. -/
noncomputable def texAnchorCertificate_genAnchorRealWprod (L d : Nat) :
    Nat -> Matrix (Fin d) (Fin d) (TexAnchorCertificateCombinedRing L d)
  | 0 => 1
  | n + 1 =>
      texAnchorCertificate_genAnchorStepMatrix L d n
          (texAnchorCertificate_genGateT L d n) *
        texAnchorCertificate_genAnchorRealWprod L d n

@[simp]
theorem texAnchorCertificate_map_genAnchorRealWprod {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) :
    ∀ n,
      (texAnchorCertificate_genAnchorRealWprod L d n).map
          (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)) =
        anchorRealWprod (paramStream θ) (anchorGateStream t) n
  | 0 => by
      simp [texAnchorCertificate_genAnchorRealWprod, anchorRealWprod]
  | n + 1 => by
      rw [texAnchorCertificate_genAnchorRealWprod, anchorRealWprod, Matrix.map_mul,
        texAnchorCertificate_map_genAnchorStepMatrix,
        texAnchorCertificate_eval_genGateT,
        texAnchorCertificate_map_genAnchorRealWprod θ t s w0 n]

theorem texAnchorCertificate_eval_mulVec {L d : Nat} {m n : Type*} [Fintype n]
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ)
    (M : Matrix m n (TexAnchorCertificateCombinedRing L d))
    (v : n -> TexAnchorCertificateCombinedRing L d) :
    (fun i =>
      (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)) (M.mulVec v i)) =
      (M.map (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))).mulVec
        (fun j => (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)) (v j)) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

theorem texAnchorCertificate_eval_dotProduct {L d : Nat} {ι : Type*} [Fintype ι]
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ)
    (v w : ι -> TexAnchorCertificateCombinedRing L d) :
    (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)) (v ⬝ᵥ w) =
      (fun i => (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)) (v i)) ⬝ᵥ
        (fun i => (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)) (w i)) := by
  simp [dotProduct]

/-- Generic transported vector `w_k`. -/
noncomputable def texAnchorCertificate_genCertificateW (L d k : Nat) :
    Fin d -> TexAnchorCertificateCombinedRing L d :=
  (texAnchorCertificate_genAnchorRealWprod L d k).mulVec
    (texAnchorCertificate_genW0 L d)

@[simp]
theorem texAnchorCertificate_eval_genCertificateW {L d k : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) :
    (fun i =>
      (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))
        (texAnchorCertificate_genCertificateW L d k i)) =
      anchorCertificateW θ t k w0 := by
  rw [anchorCertificateW]
  trans
      ((texAnchorCertificate_genAnchorRealWprod L d k).map
          (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))).mulVec
        (fun i =>
          (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))
            (texAnchorCertificate_genW0 L d i))
  · exact texAnchorCertificate_eval_mulVec θ t s w0
      (texAnchorCertificate_genAnchorRealWprod L d k) (texAnchorCertificate_genW0 L d)
  · rw [texAnchorCertificate_map_genAnchorRealWprod, texAnchorCertificate_eval_genW0]

/-- Generic gradient for an `E` row. -/
noncomputable def texAnchorCertificate_genGradientE (L d : Nat)
    (k : Fin (L - 1)) : Fin d -> TexAnchorCertificateCombinedRing L d :=
  (texAnchorCertificate_genAnchorRealBprod L d k.val)ᵀ.mulVec
    ((texAnchorCertificate_genAttentionAt L d k.val)ᵀ.mulVec
      (texAnchorCertificate_genCertificateW L d k.val))

@[simp]
theorem texAnchorCertificate_eval_genGradientE {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ)
    (k : Fin (L - 1)) :
    (fun i =>
      (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))
        (texAnchorCertificate_genGradientE L d k i)) =
      anchorCertificateGradientE θ t k w0 := by
  rw [texAnchorCertificate_genGradientE, anchorCertificateGradientE]
  rw [texAnchorCertificate_eval_mulVec, Matrix.transpose_map,
    texAnchorCertificate_map_genAnchorRealBprod]
  rw [texAnchorCertificate_eval_mulVec, Matrix.transpose_map,
    texAnchorCertificate_map_genAttentionAt, texAnchorCertificate_eval_genCertificateW]

/-- Generic gradient for an `S` row. -/
noncomputable def texAnchorCertificate_genGradientS (L d : Nat)
    (q : AnchorCertificateSIndex L) : Fin d -> TexAnchorCertificateCombinedRing L d :=
  let k : Fin (L - 1) := q.1
  let ell : Nat := q.2.1.val
  let n : Nat := k.val + ell - 1
  (texAnchorCertificate_genAnchorRealBprod L d n)ᵀ.mulVec
    ((texAnchorCertificate_genAttentionAt L d n)ᵀ.mulVec
      ((texAnchorCertificate_genAnchorStepMatrix L d k.val
          (texAnchorCertificate_genGateS L d k.val)).mulVec
        (texAnchorCertificate_genCertificateW L d k.val)))

@[simp]
theorem texAnchorCertificate_eval_genGradientS {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ)
    (q : AnchorCertificateSIndex L) :
    (fun i =>
      (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))
        (texAnchorCertificate_genGradientS L d q i)) =
      anchorCertificateGradientS θ t s q w0 := by
  let k : Fin (L - 1) := q.1
  let ell : Nat := q.2.1.val
  let n : Nat := k.val + ell - 1
  rw [texAnchorCertificate_genGradientS, anchorCertificateGradientS]
  rw [texAnchorCertificate_eval_mulVec, Matrix.transpose_map,
    texAnchorCertificate_map_genAnchorRealBprod]
  rw [texAnchorCertificate_eval_mulVec, Matrix.transpose_map,
    texAnchorCertificate_map_genAttentionAt]
  rw [texAnchorCertificate_eval_mulVec, texAnchorCertificate_map_genAnchorStepMatrix,
    texAnchorCertificate_eval_genGateS, texAnchorCertificate_eval_genCertificateW]
  simp [anchorGateStream]

/-- Generic gradient for a `T` row. -/
noncomputable def texAnchorCertificate_genGradientT (L d : Nat)
    (k : Fin (L - 1)) : Fin d -> TexAnchorCertificateCombinedRing L d :=
  let M :=
    texAnchorCertificate_genAnchorStepMatrix L d k.val
      (texAnchorCertificate_genGateT L d k.val)
  let WB := (texAnchorCertificate_genAnchorRealBprod L d k.val)ᵀ
  let AT := (texAnchorCertificate_genAttentionAt L d k.val)ᵀ
  let y :=
    (texAnchorCertificate_genValueAt L d k.val).mulVec
      (texAnchorCertificate_genCertificateW L d k.val)
  let z := M.adjugate.mulVec y
  let u := AT.mulVec z
  fun i => - (WB.mulVec u i)

@[simp]
theorem texAnchorCertificate_eval_genGradientT {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ)
    (k : Fin (L - 1)) :
    (fun i =>
      (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))
        (texAnchorCertificate_genGradientT L d k i)) =
      anchorCertificateGradientT θ t k w0 := by
  let evalHom := MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)
  have hgate : anchorGateStream t k.val = t k := by
    cases k with
    | mk n hn =>
        rw [anchorGateStream, dif_pos hn]
  have hy :
      (fun i =>
        evalHom
          (((texAnchorCertificate_genValueAt L d k.val).mulVec
              (texAnchorCertificate_genCertificateW L d k.val)) i)) =
        (paramStream θ k.val).1.mulVec (anchorCertificateW θ t k.val w0) := by
    change
      (fun i =>
        (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))
          (((texAnchorCertificate_genValueAt L d k.val).mulVec
              (texAnchorCertificate_genCertificateW L d k.val)) i)) =
        (paramStream θ k.val).1.mulVec (anchorCertificateW θ t k.val w0)
    rw [texAnchorCertificate_eval_mulVec, texAnchorCertificate_map_genValueAt,
      texAnchorCertificate_eval_genCertificateW]
  have hM :
      (texAnchorCertificate_genAnchorStepMatrix L d k.val
          (texAnchorCertificate_genGateT L d k.val)).map evalHom =
        anchorStepMatrix (paramStream θ) k.val (t k) := by
    change
      (texAnchorCertificate_genAnchorStepMatrix L d k.val
          (texAnchorCertificate_genGateT L d k.val)).map
          (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)) =
        anchorStepMatrix (paramStream θ) k.val (t k)
    rw [texAnchorCertificate_map_genAnchorStepMatrix, texAnchorCertificate_eval_genGateT,
      hgate]
  have hz :
      (fun i =>
        evalHom
          ((((texAnchorCertificate_genAnchorStepMatrix L d k.val
                    (texAnchorCertificate_genGateT L d k.val)).adjugate).mulVec
              ((texAnchorCertificate_genValueAt L d k.val).mulVec
                (texAnchorCertificate_genCertificateW L d k.val))) i)) =
        (anchorStepMatrix (paramStream θ) k.val (t k)).adjugate.mulVec
          ((paramStream θ k.val).1.mulVec (anchorCertificateW θ t k.val w0)) := by
    change
      (fun i =>
        (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))
          ((((texAnchorCertificate_genAnchorStepMatrix L d k.val
                    (texAnchorCertificate_genGateT L d k.val)).adjugate).mulVec
              ((texAnchorCertificate_genValueAt L d k.val).mulVec
                (texAnchorCertificate_genCertificateW L d k.val))) i)) =
        (anchorStepMatrix (paramStream θ) k.val (t k)).adjugate.mulVec
          ((paramStream θ k.val).1.mulVec (anchorCertificateW θ t k.val w0))
    rw [texAnchorCertificate_eval_mulVec, ← RingHom.mapMatrix_apply,
      RingHom.map_adjugate, RingHom.mapMatrix_apply, hM, hy]
  have hu :
      (fun i =>
        evalHom
          ((((texAnchorCertificate_genAttentionAt L d k.val)ᵀ).mulVec
              (((texAnchorCertificate_genAnchorStepMatrix L d k.val
                    (texAnchorCertificate_genGateT L d k.val)).adjugate).mulVec
                ((texAnchorCertificate_genValueAt L d k.val).mulVec
                  (texAnchorCertificate_genCertificateW L d k.val)))) i)) =
        (paramStream θ k.val).2ᵀ.mulVec
          ((anchorStepMatrix (paramStream θ) k.val (t k)).adjugate.mulVec
            ((paramStream θ k.val).1.mulVec (anchorCertificateW θ t k.val w0))) := by
    change
      (fun i =>
        (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))
          ((((texAnchorCertificate_genAttentionAt L d k.val)ᵀ).mulVec
              (((texAnchorCertificate_genAnchorStepMatrix L d k.val
                    (texAnchorCertificate_genGateT L d k.val)).adjugate).mulVec
                ((texAnchorCertificate_genValueAt L d k.val).mulVec
                  (texAnchorCertificate_genCertificateW L d k.val)))) i)) =
        (paramStream θ k.val).2ᵀ.mulVec
          ((anchorStepMatrix (paramStream θ) k.val (t k)).adjugate.mulVec
            ((paramStream θ k.val).1.mulVec (anchorCertificateW θ t k.val w0)))
    rw [texAnchorCertificate_eval_mulVec, Matrix.transpose_map,
      texAnchorCertificate_map_genAttentionAt, hz]
  have hpos :
      (fun i =>
        evalHom
          ((((texAnchorCertificate_genAnchorRealBprod L d k.val)ᵀ).mulVec
              (((texAnchorCertificate_genAttentionAt L d k.val)ᵀ).mulVec
                (((texAnchorCertificate_genAnchorStepMatrix L d k.val
                    (texAnchorCertificate_genGateT L d k.val)).adjugate).mulVec
                  ((texAnchorCertificate_genValueAt L d k.val).mulVec
                    (texAnchorCertificate_genCertificateW L d k.val))))) i)) =
        (anchorRealBprod (paramStream θ) k.val)ᵀ.mulVec
          ((paramStream θ k.val).2ᵀ.mulVec
            ((anchorStepMatrix (paramStream θ) k.val (t k)).adjugate.mulVec
              ((paramStream θ k.val).1.mulVec
                (anchorCertificateW θ t k.val w0)))) := by
    change
      (fun i =>
        (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))
          ((((texAnchorCertificate_genAnchorRealBprod L d k.val)ᵀ).mulVec
              (((texAnchorCertificate_genAttentionAt L d k.val)ᵀ).mulVec
                (((texAnchorCertificate_genAnchorStepMatrix L d k.val
                    (texAnchorCertificate_genGateT L d k.val)).adjugate).mulVec
                  ((texAnchorCertificate_genValueAt L d k.val).mulVec
                    (texAnchorCertificate_genCertificateW L d k.val))))) i)) =
        (anchorRealBprod (paramStream θ) k.val)ᵀ.mulVec
          ((paramStream θ k.val).2ᵀ.mulVec
            ((anchorStepMatrix (paramStream θ) k.val (t k)).adjugate.mulVec
              ((paramStream θ k.val).1.mulVec
                (anchorCertificateW θ t k.val w0))))
    rw [texAnchorCertificate_eval_mulVec, Matrix.transpose_map,
      texAnchorCertificate_map_genAnchorRealBprod, hu]
  rw [texAnchorCertificate_genGradientT, anchorCertificateGradientT]
  funext i
  simp only [map_neg]
  exact congrArg Neg.neg (congrFun hpos i)

/-- Generic gradient for an arbitrary certificate row. -/
noncomputable def texAnchorCertificate_genGradient (L d : Nat)
    (row : AnchorCertificateRow L) : Fin d -> TexAnchorCertificateCombinedRing L d :=
  match row with
  | Sum.inl (Sum.inl k) => texAnchorCertificate_genGradientE L d k
  | Sum.inl (Sum.inr q) => texAnchorCertificate_genGradientS L d q
  | Sum.inr k => texAnchorCertificate_genGradientT L d k

@[simp]
theorem texAnchorCertificate_eval_genGradient {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ)
    (row : AnchorCertificateRow L) :
    (fun i =>
      (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))
        (texAnchorCertificate_genGradient L d row i)) =
      anchorCertificateGradient θ t s row w0 := by
  cases row with
  | inl row =>
      cases row with
      | inl k =>
          simp [texAnchorCertificate_genGradient, anchorCertificateGradient]
      | inr q =>
          simp [texAnchorCertificate_genGradient, anchorCertificateGradient]
  | inr k =>
      simp [texAnchorCertificate_genGradient, anchorCertificateGradient]

/-- Generic `d x N_L` gradient matrix. -/
noncomputable def texAnchorCertificate_genGradientMatrix (L d : Nat) :
    Matrix (Fin d) (AnchorCertificateRow L) (TexAnchorCertificateCombinedRing L d) :=
  Matrix.of fun i row => texAnchorCertificate_genGradient L d row i

@[simp]
theorem texAnchorCertificate_map_genGradientMatrix {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) :
    (texAnchorCertificate_genGradientMatrix L d).map
        (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)) =
      anchorCertificateGradientMatrix θ t s w0 := by
  ext i row
  have h := congrFun (texAnchorCertificate_eval_genGradient θ t s w0 row) i
  simpa [texAnchorCertificate_genGradientMatrix, anchorCertificateGradientMatrix,
    Matrix.map_apply] using h

/-- Squared norm of a polynomial vector. -/
noncomputable def texAnchorCertificate_genVectorNormSq {L d : Nat}
    (x : Fin d -> TexAnchorCertificateCombinedRing L d) :
    TexAnchorCertificateCombinedRing L d :=
  x ⬝ᵥ x

@[simp]
theorem texAnchorCertificate_eval_genVectorNormSq {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ)
    (x : Fin d -> TexAnchorCertificateCombinedRing L d) :
    (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))
        (texAnchorCertificate_genVectorNormSq x) =
      vectorNormSq
        (fun i => (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)) (x i)) := by
  simp [texAnchorCertificate_genVectorNormSq, vectorNormSq,
    texAnchorCertificate_eval_dotProduct]

@[simp]
theorem texAnchorCertificate_eval_det_matrix {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ)
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (TexAnchorCertificateCombinedRing L d)) :
    (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)) M.det =
      (M.map (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))).det := by
  simpa [RingHom.mapMatrix_apply] using
    (RingHom.map_det (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)) M)

/-- The full TeX anchor-certificate expression as a polynomial in auxiliary and
parameter coordinates. -/
noncomputable def texAnchorCertificate_polynomial (L d : Nat) :
    TexAnchorCertificateCombinedRing L d :=
  let G := texAnchorCertificate_genGradientMatrix L d
  (Matrix.transpose G * G).det *
    (∏ k : Fin (L - 1),
      (texAnchorCertificate_genAnchorStepMatrix L d k.val
        (texAnchorCertificate_genGateT L d k.val)).det) *
    (∏ k : Fin (L - 1),
      texAnchorCertificate_genVectorNormSq
        ((texAnchorCertificate_genAttentionAt L d k.val)ᵀ.mulVec
          (texAnchorCertificate_genCertificateW L d k.val)))

theorem texAnchorCertificate_eval_polynomial {L d : Nat}
    (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ) :
    (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))
        (texAnchorCertificate_polynomial L d) =
      anchorCertificateValue θ t s w0 := by
  classical
  let evalHom := MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0)
  have hGram :
      evalHom
          ((Matrix.transpose (texAnchorCertificate_genGradientMatrix L d) *
              texAnchorCertificate_genGradientMatrix L d).det) =
        ((Matrix.transpose (anchorCertificateGradientMatrix θ t s w0) *
            anchorCertificateGradientMatrix θ t s w0).det) := by
    rw [texAnchorCertificate_eval_det_matrix]
    rw [Matrix.map_mul, Matrix.transpose_map, texAnchorCertificate_map_genGradientMatrix]
  have hStep :
      evalHom
          (∏ k : Fin (L - 1),
            (texAnchorCertificate_genAnchorStepMatrix L d k.val
              (texAnchorCertificate_genGateT L d k.val)).det) =
        ∏ k : Fin (L - 1),
          (anchorStepMatrix (paramStream θ) k.val (t k)).det := by
    rw [map_prod]
    refine Finset.prod_congr rfl ?_
    intro k _hk
    rw [texAnchorCertificate_eval_det_matrix]
    rw [texAnchorCertificate_map_genAnchorStepMatrix, texAnchorCertificate_eval_genGateT]
    simp [anchorGateStream]
  have hNorm :
      evalHom
          (∏ k : Fin (L - 1),
            texAnchorCertificate_genVectorNormSq
              ((texAnchorCertificate_genAttentionAt L d k.val)ᵀ.mulVec
                (texAnchorCertificate_genCertificateW L d k.val))) =
        ∏ k : Fin (L - 1),
          vectorNormSq ((Matrix.transpose (paramStream θ k.val).2).mulVec
            (anchorCertificateW θ t k.val w0)) := by
    rw [map_prod]
    refine Finset.prod_congr rfl ?_
    intro k _hk
    rw [texAnchorCertificate_eval_genVectorNormSq]
    congr 1
    trans
      (((texAnchorCertificate_genAttentionAt L d k.val)ᵀ).map evalHom).mulVec
        (fun i =>
          evalHom (texAnchorCertificate_genCertificateW L d k.val i))
    · exact texAnchorCertificate_eval_mulVec θ t s w0
        ((texAnchorCertificate_genAttentionAt L d k.val)ᵀ)
        (texAnchorCertificate_genCertificateW L d k.val)
    · rw [Matrix.transpose_map, texAnchorCertificate_map_genAttentionAt,
        texAnchorCertificate_eval_genCertificateW]
  rw [texAnchorCertificate_polynomial, anchorCertificateValue]
  rw [map_mul, map_mul, hGram, hStep, hNorm]

/-- The certificate polynomial, viewed as an auxiliary-variable polynomial with
parameter-coordinate polynomial coefficients. -/
noncomputable def texAnchorCertificate_auxPolynomial (L d : Nat) :
    MvPolynomial (TexAnchorCertificateAuxCoord L d) (ParamRing L d) :=
  (MvPolynomial.sumAlgEquiv ℝ
    (TexAnchorCertificateAuxCoord L d) (ParamCoord L d))
      (texAnchorCertificate_polynomial L d)

/-- A coefficient polynomial of the auxiliary certificate polynomial. -/
noncomputable def texAnchorCertificate_coeffPolynomial (L d : Nat)
    (m : TexAnchorCertificateAuxCoord L d →₀ ℕ) : ParamRing L d :=
  MvPolynomial.coeff m (texAnchorCertificate_auxPolynomial L d)

/-- The finite set of auxiliary monomials with nonzero parameter-polynomial
coefficients. -/
noncomputable def texAnchorCertificate_coeffSupport (L d : Nat) :
    Finset (TexAnchorCertificateAuxCoord L d →₀ ℕ) :=
  (texAnchorCertificate_auxPolynomial L d).support

/-- Finite coefficient index type for the anchor certificate. -/
abbrev TexAnchorCertificateCoeffIndex (L d : Nat) : Type :=
  (texAnchorCertificate_coeffSupport L d : Type)

/-- Coefficient nonvanishing data for the anchor certificate polynomial. -/
noncomputable def texAnchorCertificate_coefficientNonvanishingData (L d : Nat) :
    PolynomialNonvanishingData (ParamCoord L d) (TexAnchorCertificateCoeffIndex L d) where
  indices := Finset.univ
  poly := fun a => texAnchorCertificate_coeffPolynomial L d a.1
  nonzero := by
    intro a ha
    exact (MvPolynomial.mem_support_iff.mp a.2)

theorem texAnchorCertificate_eval_sumAlgEquiv {L d : Nat}
    (x : ParamCoord L d -> ℝ) (y : TexAnchorCertificateAuxCoord L d -> ℝ)
    (p : TexAnchorCertificateCombinedRing L d) :
    (MvPolynomial.eval y)
        (MvPolynomial.map (MvPolynomial.eval x)
          ((MvPolynomial.sumAlgEquiv ℝ
            (TexAnchorCertificateAuxCoord L d) (ParamCoord L d)) p)) =
      (MvPolynomial.eval (Sum.elim y x)) p := by
  let lhs : TexAnchorCertificateCombinedRing L d →+* ℝ :=
    (MvPolynomial.eval y).comp
      ((MvPolynomial.map (MvPolynomial.eval x)).comp
        (MvPolynomial.sumAlgEquiv ℝ
          (TexAnchorCertificateAuxCoord L d) (ParamCoord L d)).toRingHom)
  let rhs : TexAnchorCertificateCombinedRing L d →+* ℝ :=
    MvPolynomial.eval (Sum.elim y x)
  change lhs p = rhs p
  apply MvPolynomial.hom_eq_hom
  · ext r
    simp [lhs, rhs]
  · intro z
    cases z with
    | inl a =>
        simp [lhs, rhs]
    | inr c =>
        simp [lhs, rhs]

theorem texAnchorCertificate_auxPolynomial_eval_eq {L d : Nat}
    (θ : Params L d) (y : TexAnchorCertificateAuxCoord L d -> ℝ) :
    (MvPolynomial.eval y)
        (MvPolynomial.map (MvPolynomial.eval (paramFlat θ))
          (texAnchorCertificate_auxPolynomial L d)) =
      (MvPolynomial.eval (Sum.elim y (paramFlat θ)))
        (texAnchorCertificate_polynomial L d) := by
  simpa [texAnchorCertificate_auxPolynomial] using
    texAnchorCertificate_eval_sumAlgEquiv (L := L) (d := d)
      (paramFlat θ) y (texAnchorCertificate_polynomial L d)

/-- A concrete nonzero certificate evaluation witnesses nontriviality of the auxiliary
certificate polynomial. -/
theorem texAnchorCertificate_auxPolynomial_ne_zero_of_eval
    {L d : Nat} (θ : Params L d) (t s : AnchorGateVector L) (w0 : Fin d -> ℝ)
    (hval : anchorCertificateValue θ t s w0 ≠ 0) :
    texAnchorCertificate_auxPolynomial L d ≠ 0 := by
  intro hzero
  let y : TexAnchorCertificateAuxCoord L d -> ℝ :=
    texAnchorCertificate_auxEval t s w0
  have hcombined :
      Sum.elim y (paramFlat θ) =
        texAnchorCertificate_combinedEval θ t s w0 := by
    funext z
    cases z <;> rfl
  have hpoly_eval :
      (MvPolynomial.eval (texAnchorCertificate_combinedEval θ t s w0))
          (texAnchorCertificate_polynomial L d) = 0 := by
    rw [← hcombined]
    rw [← texAnchorCertificate_auxPolynomial_eval_eq (θ := θ) (y := y)]
    rw [hzero]
    simp
  rw [texAnchorCertificate_eval_polynomial] at hpoly_eval
  exact hval hpoly_eval

/-- Membership in the concrete anchor-certificate locus is enough to prove the auxiliary
certificate polynomial is nonzero. -/
theorem texAnchorCertificate_auxPolynomial_ne_zero_of_mem_certificateSet
    {L d : Nat} {θ : Params L d} (hθ : θ ∈ TexAnchorCertificateSet L d) :
    texAnchorCertificate_auxPolynomial L d ≠ 0 := by
  rcases hθ with ⟨t, s, w0, hval⟩
  exact texAnchorCertificate_auxPolynomial_ne_zero_of_eval θ t s w0 hval

/-- The concrete witness obligation for the TeX anchor-certificate condition. -/
def texAnchorCertificate_hasConcreteWitness (L d : Nat) : Prop :=
  ∃ θ : Params L d, θ ∈ TexAnchorCertificateSet L d

/-- Reduction from a concrete witness to the auxiliary-polynomial nonzero statement. -/
theorem texAnchorCertificate_auxPolynomial_ne_zero_of_concreteWitness
    {L d : Nat} (hwitness : texAnchorCertificate_hasConcreteWitness L d) :
    texAnchorCertificate_auxPolynomial L d ≠ 0 := by
  rcases hwitness with ⟨θ, hθ⟩
  exact texAnchorCertificate_auxPolynomial_ne_zero_of_mem_certificateSet hθ

/-- At depth zero the certificate has no rows, so the empty Gram determinant gives a
closed concrete witness. -/
theorem texAnchorCertificate_hasConcreteWitness_zero (d : Nat) :
    texAnchorCertificate_hasConcreteWitness 0 d := by
  classical
  refine ⟨Fin.elim0, ?_⟩
  refine ⟨Fin.elim0, Fin.elim0, 0, ?_⟩
  haveI : IsEmpty (AnchorCertificateRow 0) := by
    refine ⟨?_⟩
    rintro ((k | q) | k)
    · exact Fin.elim0 k
    · exact Fin.elim0 q.1
    · exact Fin.elim0 k
  simp [anchorCertificateValue]

/-- At depth one the certificate also has no rows, so any one-layer parameter tuple is a
concrete witness. -/
theorem texAnchorCertificate_hasConcreteWitness_one (d : Nat) :
    texAnchorCertificate_hasConcreteWitness 1 d := by
  classical
  refine ⟨fun _ => (0, 0), ?_⟩
  refine ⟨Fin.elim0, Fin.elim0, 0, ?_⟩
  haveI : IsEmpty (AnchorCertificateRow 1) := by
    refine ⟨?_⟩
    rintro ((k | q) | k)
    · exact Fin.elim0 k
    · exact Fin.elim0 q.1
    · exact Fin.elim0 k
  simp [anchorCertificateValue]

/-! ### Concrete positive-depth witness bookkeeping -/

/-- Starting coordinate of the block assigned to certificate rows whose gradient uses
the attention matrix at stage `j`.  This is `sum_{r < j} (r + 2)`. -/
def texAnchorWitnessBlockStart (j : Nat) : Nat :=
  Nat.choose j 2 + 2 * j

@[simp]
theorem texAnchorWitnessBlockStart_zero :
    texAnchorWitnessBlockStart 0 = 0 := by
  simp [texAnchorWitnessBlockStart]

theorem texAnchorWitnessBlockStart_succ (j : Nat) :
    texAnchorWitnessBlockStart (j + 1) =
      texAnchorWitnessBlockStart j + (j + 2) := by
  unfold texAnchorWitnessBlockStart
  rw [Nat.choose_succ_succ]
  simp [Nat.choose_one_right]
  omega

theorem texAnchorWitnessBlockStart_mono {a b : Nat} (h : a ≤ b) :
    texAnchorWitnessBlockStart a ≤ texAnchorWitnessBlockStart b := by
  induction h with
  | refl => rfl
  | step _ ih =>
      exact le_trans ih (by
        rw [texAnchorWitnessBlockStart_succ]
        omega)

theorem genericCertificateRows_eq_texAnchorWitnessBlockEnd (L : Nat) :
    genericCertificateRows L =
      texAnchorWitnessBlockStart (L - 1) + (L - 1) := by
  cases L with
  | zero =>
      simp [genericCertificateRows, texAnchorWitnessBlockStart]
  | succ L =>
      simp [genericCertificateRows, texAnchorWitnessBlockStart, Nat.choose_succ_succ,
        Nat.choose_one_right]
      omega

/-- Attention-layer group for a certificate row. -/
def texAnchorWitnessRowGroup {L : Nat} : AnchorCertificateRow L -> Nat
  | Sum.inl (Sum.inl k) => k.val
  | Sum.inl (Sum.inr q) => q.1.val + q.2.1.val - 1
  | Sum.inr k => k.val

/-- Position of a certificate row inside its attention-layer block. -/
def texAnchorWitnessRowPos {L : Nat} : AnchorCertificateRow L -> Nat
  | Sum.inl (Sum.inl k) => k.val
  | Sum.inl (Sum.inr q) => q.1.val
  | Sum.inr k => k.val + 1

/-- Natural coordinate assigned to an anchor-certificate row in the explicit witness.
Rows are grouped by the attention layer that creates their gradient. -/
def texAnchorWitnessRowNat {L : Nat} : AnchorCertificateRow L -> Nat
  | Sum.inl (Sum.inl k) =>
      texAnchorWitnessBlockStart k.val + k.val
  | Sum.inl (Sum.inr q) =>
      texAnchorWitnessBlockStart (q.1.val + q.2.1.val - 1) + q.1.val
  | Sum.inr k =>
      texAnchorWitnessBlockStart k.val + k.val + 1

theorem texAnchorWitnessRowNat_eq_start_add_pos {L : Nat}
    (row : AnchorCertificateRow L) :
    texAnchorWitnessRowNat row =
      texAnchorWitnessBlockStart (texAnchorWitnessRowGroup row) +
        texAnchorWitnessRowPos row := by
  rcases row with ((k | q) | k) <;> rfl

theorem texAnchorWitnessRowPos_lt_group_add_two {L : Nat}
    (row : AnchorCertificateRow L) :
    texAnchorWitnessRowPos row < texAnchorWitnessRowGroup row + 2 := by
  rcases row with ((k | q) | k)
  · simp [texAnchorWitnessRowPos, texAnchorWitnessRowGroup]
  · rcases q with ⟨k, ell, hell⟩
    simp [texAnchorWitnessRowPos, texAnchorWitnessRowGroup]
    omega
  · simp [texAnchorWitnessRowPos, texAnchorWitnessRowGroup]

theorem texAnchorWitnessBlockStart_add_lt_next {g p : Nat} (hp : p < g + 2) :
    texAnchorWitnessBlockStart g + p < texAnchorWitnessBlockStart (g + 1) := by
  rw [texAnchorWitnessBlockStart_succ]
  omega

theorem texAnchorWitnessBlockStart_add_inj_of_lt_next
    {g h p q : Nat} (hp : p < g + 2) (hq : q < h + 2)
    (heq : texAnchorWitnessBlockStart g + p =
      texAnchorWitnessBlockStart h + q) :
    g = h ∧ p = q := by
  have hnot_lt : ¬ g < h := by
    intro hgh
    have hmono :
        texAnchorWitnessBlockStart (g + 1) ≤ texAnchorWitnessBlockStart h :=
      texAnchorWitnessBlockStart_mono (Nat.succ_le_of_lt hgh)
    have hnext := texAnchorWitnessBlockStart_add_lt_next (g := g) (p := p) hp
    omega
  have hnot_gt : ¬ h < g := by
    intro hhg
    have hmono :
        texAnchorWitnessBlockStart (h + 1) ≤ texAnchorWitnessBlockStart g :=
      texAnchorWitnessBlockStart_mono (Nat.succ_le_of_lt hhg)
    have hnext := texAnchorWitnessBlockStart_add_lt_next (g := h) (p := q) hq
    omega
  have hgh : g = h := by omega
  subst h
  omega

theorem texAnchorWitnessRowGroupPos_eq_of_rowNat_eq {L : Nat}
    {row row' : AnchorCertificateRow L}
    (h : texAnchorWitnessRowNat row = texAnchorWitnessRowNat row') :
    texAnchorWitnessRowGroup row = texAnchorWitnessRowGroup row' ∧
      texAnchorWitnessRowPos row = texAnchorWitnessRowPos row' := by
  rw [texAnchorWitnessRowNat_eq_start_add_pos row,
    texAnchorWitnessRowNat_eq_start_add_pos row'] at h
  exact texAnchorWitnessBlockStart_add_inj_of_lt_next
    (texAnchorWitnessRowPos_lt_group_add_two row)
    (texAnchorWitnessRowPos_lt_group_add_two row') h

theorem texAnchorWitnessRowNat_injective {L : Nat} :
    Function.Injective (texAnchorWitnessRowNat (L := L)) := by
  intro row row' h
  obtain ⟨hgroup, hpos⟩ :=
    texAnchorWitnessRowGroupPos_eq_of_rowNat_eq (L := L) h
  rcases row with ((k | q) | k) <;> rcases row' with ((k' | q') | k')
  · congr
    exact Fin.ext (by simpa [texAnchorWitnessRowGroup] using hgroup)
  · rcases q' with ⟨kq', ell', hell'⟩
    have hellpos : 2 ≤ ell'.val := hell'.1
    simp [texAnchorWitnessRowGroup, texAnchorWitnessRowPos] at hgroup hpos
    omega
  · simp [texAnchorWitnessRowGroup, texAnchorWitnessRowPos] at hgroup hpos
    omega
  · rcases q with ⟨kq, ell, hell⟩
    have hellpos : 2 ≤ ell.val := hell.1
    simp [texAnchorWitnessRowGroup, texAnchorWitnessRowPos] at hgroup hpos
    omega
  · rcases q with ⟨kq, ell, hell⟩
    rcases q' with ⟨kq', ell', hell'⟩
    simp [texAnchorWitnessRowGroup, texAnchorWitnessRowPos] at hgroup hpos
    have hk : kq = kq' := Fin.ext (by omega)
    subst kq'
    have hell_eq : ell = ell' := Fin.ext (by omega)
    subst ell'
    rfl
  · rcases q with ⟨kq, ell, hell⟩
    have hellpos : 2 ≤ ell.val := hell.1
    simp [texAnchorWitnessRowGroup, texAnchorWitnessRowPos] at hgroup hpos
    omega
  · simp [texAnchorWitnessRowGroup, texAnchorWitnessRowPos] at hgroup hpos
    omega
  · rcases q' with ⟨kq', ell', hell'⟩
    have hellpos : 2 ≤ ell'.val := hell'.1
    simp [texAnchorWitnessRowGroup, texAnchorWitnessRowPos] at hgroup hpos
    omega
  · congr
    exact Fin.ext (by simpa [texAnchorWitnessRowGroup] using hgroup)

theorem texAnchorWitness_gram_eq_one_of_basis_columns'
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : Nat}
    {G : Matrix (Fin d) ι ℝ} {e : ι -> Fin d}
    (hG : ∀ i a, G i a = (Pi.single (e a) (1 : ℝ) : Fin d -> ℝ) i)
    (he : Function.Injective e) :
    Matrix.transpose G * G = 1 := by
  ext a b
  by_cases hab : a = b
  · subst b
    rw [Matrix.one_apply_eq]
    change (fun i : Fin d => G i a) ⬝ᵥ (fun i : Fin d => G i a) = 1
    rw [show (fun i : Fin d => G i a) =
        (Pi.single (e a) (1 : ℝ) : Fin d -> ℝ) by
      funext i
      exact hG i a]
    simp
  · have he_ne : e a ≠ e b := fun h => hab (he h)
    rw [Matrix.one_apply_ne hab]
    change (fun i : Fin d => G i a) ⬝ᵥ (fun i : Fin d => G i b) = 0
    rw [show (fun i : Fin d => G i a) =
        (Pi.single (e a) (1 : ℝ) : Fin d -> ℝ) by
      funext i
      exact hG i a]
    rw [show (fun i : Fin d => G i b) =
        (Pi.single (e b) (1 : ℝ) : Fin d -> ℝ) by
      funext i
      exact hG i b]
    rw [single_dotProduct]
    simp [he_ne]

theorem texAnchorWitness_gram_det_eq_one_of_basis_columns'
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : Nat}
    {G : Matrix (Fin d) ι ℝ} {e : ι -> Fin d}
    (hG : ∀ i a, G i a = (Pi.single (e a) (1 : ℝ) : Fin d -> ℝ) i)
    (he : Function.Injective e) :
    (Matrix.transpose G * G).det = 1 := by
  rw [texAnchorWitness_gram_eq_one_of_basis_columns' hG he]
  exact Matrix.det_one

/-- The finite coordinate attached to a certificate row, using the row-count bound. -/
def texAnchorWitnessRowFin {L d : Nat}
    (hrows : genericCertificateRows L ≤ d) (row : AnchorCertificateRow L) : Fin d :=
  ⟨texAnchorWitnessRowNat row, by
    rcases row with ((k | q) | k)
    · have hk : k.val + 1 ≤ L - 1 := Nat.succ_le_of_lt k.2
      have hnext : k.val + 1 ≤ L - 1 := hk
      have hstart :
          texAnchorWitnessBlockStart (k.val + 1) ≤
            texAnchorWitnessBlockStart (L - 1) :=
        texAnchorWitnessBlockStart_mono hnext
      have hlt :
          texAnchorWitnessBlockStart k.val + k.val <
            genericCertificateRows L := by
        rw [genericCertificateRows_eq_texAnchorWitnessBlockEnd]
        have hblock :
            texAnchorWitnessBlockStart k.val + k.val <
              texAnchorWitnessBlockStart (k.val + 1) := by
          rw [texAnchorWitnessBlockStart_succ]
          omega
        omega
      exact lt_of_lt_of_le hlt hrows
    · rcases q with ⟨k, ell, hell⟩
      have hell_le : k.val + ell.val ≤ L := hell.2
      have hell_pos : 2 ≤ ell.val := hell.1
      let g := k.val + ell.val - 1
      have hg_le : g ≤ L - 1 := by omega
      have hlt :
          texAnchorWitnessBlockStart (k.val + ell.val - 1) + k.val <
            genericCertificateRows L := by
        change texAnchorWitnessBlockStart g + k.val < genericCertificateRows L
        rw [genericCertificateRows_eq_texAnchorWitnessBlockEnd]
        by_cases hg : g < L - 1
        · have hnext : g + 1 ≤ L - 1 := Nat.succ_le_of_lt hg
          have hstart :
              texAnchorWitnessBlockStart (g + 1) ≤
                texAnchorWitnessBlockStart (L - 1) :=
            texAnchorWitnessBlockStart_mono hnext
          have hblock :
              texAnchorWitnessBlockStart g + k.val <
                texAnchorWitnessBlockStart (g + 1) := by
            rw [texAnchorWitnessBlockStart_succ]
            omega
          omega
        · have hg_eq : g = L - 1 := by omega
          have hk_lt_g : k.val < g := by
            dsimp [g]
            omega
          have hstart_eq :
              texAnchorWitnessBlockStart g =
                texAnchorWitnessBlockStart (L - 1) := by
            rw [hg_eq]
          omega
      exact lt_of_lt_of_le hlt hrows
    · have hk : k.val + 1 ≤ L - 1 := Nat.succ_le_of_lt k.2
      have hstart :
          texAnchorWitnessBlockStart (k.val + 1) ≤
            texAnchorWitnessBlockStart (L - 1) :=
        texAnchorWitnessBlockStart_mono hk
      have hlt :
          texAnchorWitnessBlockStart k.val + k.val + 1 <
            genericCertificateRows L := by
        rw [genericCertificateRows_eq_texAnchorWitnessBlockEnd]
        have hblock :
            texAnchorWitnessBlockStart k.val + k.val + 1 <
              texAnchorWitnessBlockStart (k.val + 1) := by
          rw [texAnchorWitnessBlockStart_succ]
          omega
        omega
      exact lt_of_lt_of_le hlt hrows⟩

theorem texAnchorWitnessRowFin_injective {L d : Nat}
    (hrows : genericCertificateRows L ≤ d) :
    Function.Injective (texAnchorWitnessRowFin (L := L) (d := d) hrows) := by
  intro row row' h
  apply texAnchorWitnessRowNat_injective
  exact congrArg Fin.val h

/-- The dependent S-row index for `S_{k,j-k+1}`, valid whenever `k < j < L`. -/
def texAnchorWitnessSIndexOfLt {L k j : Nat} (hkj : k < j) (hjL : j < L) :
    AnchorCertificateSIndex L :=
  let ellNat := j - k + 1
  have hkL : k < L - 1 := by omega
  have hellLt : ellNat < L + 1 := by
    dsimp [ellNat]
    omega
  ⟨⟨k, hkL⟩, ⟨⟨ellNat, hellLt⟩, by
    dsimp [ellNat]
    exact ⟨by omega, by omega⟩⟩⟩

@[simp]
theorem texAnchorWitnessSIndexOfLt_fst_val {L k j : Nat}
    (hkj : k < j) (hjL : j < L) :
    (texAnchorWitnessSIndexOfLt (L := L) hkj hjL).1.val = k :=
  rfl

@[simp]
theorem texAnchorWitnessSIndexOfLt_ell_val {L k j : Nat}
    (hkj : k < j) (hjL : j < L) :
    (texAnchorWitnessSIndexOfLt (L := L) hkj hjL).2.1.val = j - k + 1 :=
  rfl

/-- Certificate row `S_{k,j-k+1}` as an `AnchorCertificateRow`. -/
def texAnchorWitnessSRowOfLt {L k j : Nat} (hkj : k < j) (hjL : j < L) :
    AnchorCertificateRow L :=
  Sum.inl (Sum.inr (texAnchorWitnessSIndexOfLt (L := L) hkj hjL))

/-- Certificate row `E_j`. -/
def texAnchorWitnessERowOfLt {L j : Nat} (hj : j < L - 1) :
    AnchorCertificateRow L :=
  Sum.inl (Sum.inl (⟨j, hj⟩ : Fin (L - 1)))

/-- Certificate row `T_j`. -/
def texAnchorWitnessTRowOfLt {L j : Nat} (hj : j < L - 1) :
    AnchorCertificateRow L :=
  Sum.inr (⟨j, hj⟩ : Fin (L - 1))

@[simp]
theorem texAnchorWitnessRowNat_sRowOfLt {L k j : Nat}
    (hkj : k < j) (hjL : j < L) :
    texAnchorWitnessRowNat (texAnchorWitnessSRowOfLt (L := L) hkj hjL) =
      texAnchorWitnessBlockStart j + k := by
  have hgroup : k + (j - k + 1) - 1 = j := by omega
  simp [texAnchorWitnessSRowOfLt, texAnchorWitnessSIndexOfLt,
    texAnchorWitnessRowNat, hgroup]

@[simp]
theorem texAnchorWitnessRowNat_eRowOfLt {L j : Nat} (hj : j < L - 1) :
    texAnchorWitnessRowNat (texAnchorWitnessERowOfLt (L := L) hj) =
      texAnchorWitnessBlockStart j + j := by
  rfl

@[simp]
theorem texAnchorWitnessRowNat_tRowOfLt {L j : Nat} (hj : j < L - 1) :
    texAnchorWitnessRowNat (texAnchorWitnessTRowOfLt (L := L) hj) =
      texAnchorWitnessBlockStart j + j + 1 := by
  rfl

theorem texAnchorWitnessS_source_lt_d {L d k j : Nat}
    (hrows : genericCertificateRows L ≤ d) (hkj : k < j) (hjL : j < L) :
    k < d := by
  have hfin :=
    (texAnchorWitnessRowFin (L := L) (d := d) hrows
      (texAnchorWitnessSRowOfLt (L := L) hkj hjL)).isLt
  change texAnchorWitnessRowNat (texAnchorWitnessSRowOfLt (L := L) hkj hjL) < d at hfin
  rw [texAnchorWitnessRowNat_sRowOfLt] at hfin
  omega

theorem texAnchorWitnessE_source_lt_d {L d j : Nat}
    (hrows : genericCertificateRows L ≤ d) (hj : j < L - 1) :
    j < d := by
  have hfin :=
    (texAnchorWitnessRowFin (L := L) (d := d) hrows
      (texAnchorWitnessERowOfLt (L := L) hj)).isLt
  change texAnchorWitnessRowNat (texAnchorWitnessERowOfLt (L := L) hj) < d at hfin
  rw [texAnchorWitnessRowNat_eRowOfLt] at hfin
  omega

theorem texAnchorWitnessT_source_lt_d {L d j : Nat}
    (hrows : genericCertificateRows L ≤ d) (hj : j < L - 1) :
    j + 1 < d := by
  have hfin :=
    (texAnchorWitnessRowFin (L := L) (d := d) hrows
      (texAnchorWitnessTRowOfLt (L := L) hj)).isLt
  change texAnchorWitnessRowNat (texAnchorWitnessTRowOfLt (L := L) hj) < d at hfin
  rw [texAnchorWitnessRowNat_tRowOfLt] at hfin
  omega

/-- Coordinate basis vector attached to a certificate row in the explicit witness. -/
def texAnchorWitnessRowBasis {L d : Nat}
    (hrows : genericCertificateRows L ≤ d) (row : AnchorCertificateRow L) :
    Fin d -> ℝ :=
  Pi.single (texAnchorWitnessRowFin (L := L) (d := d) hrows row) (1 : ℝ)

/-- Source row of the sparse attention matrix at layer/group `j`. -/
noncomputable def texAnchorWitnessAttentionRow {L d : Nat}
    (hrows : genericCertificateRows L ≤ d) (j : Nat) (hjL : j < L)
    (source : Fin d) : Fin d -> ℝ :=
  if hS : source.val < j then
    texAnchorWitnessRowBasis hrows (texAnchorWitnessSRowOfLt (L := L) hS hjL)
  else if _hEsource : source.val = j then
    if hE : j < L - 1 then
      texAnchorWitnessRowBasis hrows (texAnchorWitnessERowOfLt (L := L) hE)
    else
      0
  else if _hTsource : source.val = j + 1 then
    if hT : j < L - 1 then
      -texAnchorWitnessRowBasis hrows (texAnchorWitnessTRowOfLt (L := L) hT)
    else
      0
  else
    0

/-- Sparse attention matrix whose transpose sends source basis vectors to certificate rows. -/
noncomputable def texAnchorWitnessAttentionMatrix {L d : Nat}
    (hrows : genericCertificateRows L ≤ d) (j : Nat) (hjL : j < L) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun source target =>
    texAnchorWitnessAttentionRow hrows j hjL source target

theorem texAnchorWitnessAttentionMatrix_image_s {L d k j : Nat}
    (hrows : genericCertificateRows L ≤ d) (hkj : k < j) (hjL : j < L) :
    (texAnchorWitnessAttentionMatrix (L := L) (d := d) hrows j hjL)ᵀ *ᵥ
        Pi.single (⟨k, texAnchorWitnessS_source_lt_d hrows hkj hjL⟩ : Fin d) (1 : ℝ) =
      Pi.single
        (texAnchorWitnessRowFin (L := L) (d := d) hrows
          (texAnchorWitnessSRowOfLt (L := L) hkj hjL)) (1 : ℝ) := by
  classical
  rw [Matrix.mulVec_single_one]
  ext target
  simp [texAnchorWitnessAttentionMatrix, texAnchorWitnessAttentionRow,
    texAnchorWitnessRowBasis, Matrix.col_apply, hkj]

theorem texAnchorWitnessAttentionMatrix_image_e {L d j : Nat}
    (hrows : genericCertificateRows L ≤ d) (hjL : j < L) (hj : j < L - 1) :
    (texAnchorWitnessAttentionMatrix (L := L) (d := d) hrows j hjL)ᵀ *ᵥ
        Pi.single (⟨j, texAnchorWitnessE_source_lt_d hrows hj⟩ : Fin d) (1 : ℝ) =
      Pi.single
        (texAnchorWitnessRowFin (L := L) (d := d) hrows
          (texAnchorWitnessERowOfLt (L := L) hj)) (1 : ℝ) := by
  classical
  rw [Matrix.mulVec_single_one]
  ext target
  simp [texAnchorWitnessAttentionMatrix, texAnchorWitnessAttentionRow,
    texAnchorWitnessRowBasis, Matrix.col_apply, hj]

theorem texAnchorWitnessAttentionMatrix_image_t {L d j : Nat}
    (hrows : genericCertificateRows L ≤ d) (hjL : j < L) (hj : j < L - 1) :
    (texAnchorWitnessAttentionMatrix (L := L) (d := d) hrows j hjL)ᵀ *ᵥ
        Pi.single (⟨j + 1, texAnchorWitnessT_source_lt_d hrows hj⟩ : Fin d) (1 : ℝ) =
      -Pi.single
        (texAnchorWitnessRowFin (L := L) (d := d) hrows
          (texAnchorWitnessTRowOfLt (L := L) hj)) (1 : ℝ) := by
  classical
  have hnotS : ¬ j + 1 < j := by omega
  rw [Matrix.mulVec_single_one]
  ext target
  simp [texAnchorWitnessAttentionMatrix, texAnchorWitnessAttentionRow,
    texAnchorWitnessRowBasis, Matrix.col_apply, hnotS, hj]

/-- A determinant-one value-step matrix sending `e_j` to `e_{j+1}`.  It is the
two-transvection block `[[0,-1],[1,1]]` on coordinates `(j,j+1)` and the identity
elsewhere. -/
def texAnchorWitnessShiftSrc {d : Nat} (j : Nat) (hj : j + 1 < d) : Fin d :=
  ⟨j, Nat.lt_of_succ_lt hj⟩

def texAnchorWitnessShiftDst {d : Nat} (j : Nat) (hj : j + 1 < d) : Fin d :=
  ⟨j + 1, hj⟩

theorem texAnchorWitnessShiftSrc_ne_dst {d j : Nat} (hj : j + 1 < d) :
    texAnchorWitnessShiftSrc j hj ≠ texAnchorWitnessShiftDst j hj := by
  intro h
  have hval : j = j + 1 := congrArg Fin.val h
  omega

theorem texAnchorWitnessShiftDst_ne_src {d j : Nat} (hj : j + 1 < d) :
    texAnchorWitnessShiftDst j hj ≠ texAnchorWitnessShiftSrc j hj :=
  (texAnchorWitnessShiftSrc_ne_dst hj).symm

noncomputable def texAnchorWitnessShiftBOfLt (d j : Nat) (hj : j + 1 < d) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.transvection (texAnchorWitnessShiftSrc j hj)
      (texAnchorWitnessShiftDst j hj) (-1 : ℝ) *
    Matrix.transvection (texAnchorWitnessShiftDst j hj)
      (texAnchorWitnessShiftSrc j hj) (1 : ℝ)

noncomputable def texAnchorWitnessShiftB (d j : Nat) :
    Matrix (Fin d) (Fin d) ℝ :=
  if hj : j + 1 < d then
    texAnchorWitnessShiftBOfLt d j hj
  else 1

/-- Value matrix whose skip matrix is the explicit determinant-one shift block. -/
noncomputable def texAnchorWitnessShiftV (d j : Nat) :
    Matrix (Fin d) (Fin d) ℝ :=
  texAnchorWitnessShiftB d j - 1

theorem skipB_texAnchorWitnessShiftV (d j : Nat) :
    skipB (texAnchorWitnessShiftV d j) = texAnchorWitnessShiftB d j := by
  ext i k
  simp [skipB, texAnchorWitnessShiftV]

theorem texAnchorWitnessShift_transvection_mulVec {d : Nat}
    (i j : Fin d) (c : ℝ) (v : Fin d -> ℝ) :
    Matrix.transvection i j c *ᵥ v =
      v + (c * v j) • Pi.single i (1 : ℝ) := by
  classical
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  ext k
  by_cases hki : k = i
  · subst k
    simp
  · simp [hki]

theorem texAnchorWitnessShiftBOfLt_det {d j : Nat} (hj : j + 1 < d) :
    (texAnchorWitnessShiftBOfLt d j hj).det = 1 := by
  rw [texAnchorWitnessShiftBOfLt, Matrix.det_mul,
    Matrix.det_transvection_of_ne (texAnchorWitnessShiftSrc j hj)
      (texAnchorWitnessShiftDst j hj) (texAnchorWitnessShiftSrc_ne_dst hj) (-1 : ℝ),
    Matrix.det_transvection_of_ne (texAnchorWitnessShiftDst j hj)
      (texAnchorWitnessShiftSrc j hj) (texAnchorWitnessShiftDst_ne_src hj) (1 : ℝ)]
  norm_num

theorem texAnchorWitnessShiftB_det {d j : Nat} (hj : j + 1 < d) :
    (texAnchorWitnessShiftB d j).det = 1 := by
  rw [texAnchorWitnessShiftB, dif_pos hj, texAnchorWitnessShiftBOfLt_det hj]

theorem texAnchorWitnessShiftB_mulVec_current {d j : Nat} (hj : j + 1 < d) :
    texAnchorWitnessShiftB d j *ᵥ
        Pi.single (texAnchorWitnessShiftSrc j hj) (1 : ℝ) =
      Pi.single (texAnchorWitnessShiftDst j hj) (1 : ℝ) := by
  classical
  let src := texAnchorWitnessShiftSrc j hj
  let dst := texAnchorWitnessShiftDst j hj
  have hsrcdst : src ≠ dst := texAnchorWitnessShiftSrc_ne_dst hj
  have hdstsrc : dst ≠ src := texAnchorWitnessShiftDst_ne_src hj
  have hright :
      Matrix.transvection dst src (1 : ℝ) *ᵥ Pi.single src (1 : ℝ) =
        Pi.single src (1 : ℝ) + Pi.single dst (1 : ℝ) := by
    rw [texAnchorWitnessShift_transvection_mulVec]
    ext k
    by_cases hks : k = src
    · subst k
      simp [hsrcdst]
    · by_cases hkd : k = dst
      · subst k
        simp [hdstsrc]
      · simp [hks, hkd]
  have hleft :
      Matrix.transvection src dst (-1 : ℝ) *ᵥ
          (Pi.single src (1 : ℝ) + Pi.single dst (1 : ℝ)) =
        Pi.single dst (1 : ℝ) := by
    rw [texAnchorWitnessShift_transvection_mulVec]
    ext k
    by_cases hks : k = src
    · subst k
      simp [hsrcdst]
    · by_cases hkd : k = dst
      · subst k
        simp [hdstsrc]
      · simp [hks, hkd]
  have hchain :
      Matrix.transvection src dst (-1 : ℝ) *ᵥ
          (Matrix.transvection dst src (1 : ℝ) *ᵥ Pi.single src (1 : ℝ)) =
        Pi.single dst (1 : ℝ) := by
    rw [hright]
    exact hleft
  rw [texAnchorWitnessShiftB, dif_pos hj]
  simpa [texAnchorWitnessShiftBOfLt, src, dst, Matrix.mulVec_mulVec] using hchain

theorem texAnchorWitnessShiftBOfLt_mulVec_dst {d j : Nat} (hj : j + 1 < d) :
    texAnchorWitnessShiftBOfLt d j hj *ᵥ
        Pi.single (texAnchorWitnessShiftDst j hj) (1 : ℝ) =
      Pi.single (texAnchorWitnessShiftDst j hj) (1 : ℝ) -
        Pi.single (texAnchorWitnessShiftSrc j hj) (1 : ℝ) := by
  classical
  let src := texAnchorWitnessShiftSrc j hj
  let dst := texAnchorWitnessShiftDst j hj
  have hsrcdst : src ≠ dst := texAnchorWitnessShiftSrc_ne_dst hj
  have hdstsrc : dst ≠ src := texAnchorWitnessShiftDst_ne_src hj
  have hright :
      Matrix.transvection dst src (1 : ℝ) *ᵥ Pi.single dst (1 : ℝ) =
        Pi.single dst (1 : ℝ) := by
    rw [texAnchorWitnessShift_transvection_mulVec]
    simp [hsrcdst]
  have hleft :
      Matrix.transvection src dst (-1 : ℝ) *ᵥ Pi.single dst (1 : ℝ) =
        Pi.single dst (1 : ℝ) - Pi.single src (1 : ℝ) := by
    rw [texAnchorWitnessShift_transvection_mulVec]
    ext k
    by_cases hks : k = src
    · subst k
      simp [hsrcdst]
    · by_cases hkd : k = dst
      · subst k
        simp [hdstsrc]
      · simp [hks, hkd]
  have hchain :
      Matrix.transvection src dst (-1 : ℝ) *ᵥ
          (Matrix.transvection dst src (1 : ℝ) *ᵥ Pi.single dst (1 : ℝ)) =
        Pi.single dst (1 : ℝ) - Pi.single src (1 : ℝ) := by
    rw [hright]
    exact hleft
  simpa [texAnchorWitnessShiftBOfLt, src, dst, Matrix.mulVec_mulVec] using hchain

theorem texAnchorWitnessShiftB_mulVec_next {d j : Nat} (hj : j + 1 < d) :
    texAnchorWitnessShiftB d j *ᵥ
        Pi.single (texAnchorWitnessShiftDst j hj) (1 : ℝ) =
      Pi.single (texAnchorWitnessShiftDst j hj) (1 : ℝ) -
        Pi.single (texAnchorWitnessShiftSrc j hj) (1 : ℝ) := by
  rw [texAnchorWitnessShiftB, dif_pos hj]
  exact texAnchorWitnessShiftBOfLt_mulVec_dst hj

theorem texAnchorWitnessShiftV_mulVec_current {d j : Nat} (hj : j + 1 < d) :
    texAnchorWitnessShiftV d j *ᵥ
        Pi.single (texAnchorWitnessShiftSrc j hj) (1 : ℝ) =
      Pi.single (texAnchorWitnessShiftDst j hj) (1 : ℝ) -
        Pi.single (texAnchorWitnessShiftSrc j hj) (1 : ℝ) := by
  rw [texAnchorWitnessShiftV, Matrix.sub_mulVec, texAnchorWitnessShiftB_mulVec_current,
    Matrix.one_mulVec]

theorem texAnchorWitnessShift_adjugate_mulVec_V_current {d j : Nat} (hj : j + 1 < d) :
    (texAnchorWitnessShiftB d j).adjugate *ᵥ
        (texAnchorWitnessShiftV d j *ᵥ
          Pi.single (texAnchorWitnessShiftSrc j hj) (1 : ℝ)) =
      Pi.single (texAnchorWitnessShiftDst j hj) (1 : ℝ) := by
  classical
  let B := texAnchorWitnessShiftB d j
  let V := texAnchorWitnessShiftV d j
  let src := texAnchorWitnessShiftSrc j hj
  let dst := texAnchorWitnessShiftDst j hj
  have hdet : B.det = 1 := texAnchorWitnessShiftB_det hj
  have hVsrc : V *ᵥ Pi.single src (1 : ℝ) =
      Pi.single dst (1 : ℝ) - Pi.single src (1 : ℝ) := by
    simpa [V, src, dst] using texAnchorWitnessShiftV_mulVec_current hj
  have hBdst : B *ᵥ Pi.single dst (1 : ℝ) =
      Pi.single dst (1 : ℝ) - Pi.single src (1 : ℝ) := by
    simpa [B, src, dst] using texAnchorWitnessShiftB_mulVec_next hj
  have hleft :
      B *ᵥ (B.adjugate *ᵥ (V *ᵥ Pi.single src (1 : ℝ))) =
        Pi.single dst (1 : ℝ) - Pi.single src (1 : ℝ) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet]
    simp [hVsrc]
  have hinj : Function.Injective fun v : Fin d -> ℝ => B *ᵥ v := by
    intro x y hxy
    have hx :
        B.adjugate *ᵥ (B *ᵥ x) = B.adjugate *ᵥ (B *ᵥ y) := by
      exact congrArg (fun z : Fin d -> ℝ => B.adjugate *ᵥ z) hxy
    simpa [Matrix.mulVec_mulVec, Matrix.adjugate_mul, hdet] using hx
  have heq :
      B *ᵥ (B.adjugate *ᵥ (V *ᵥ Pi.single src (1 : ℝ))) =
        B *ᵥ Pi.single dst (1 : ℝ) := by
    rw [hleft, hBdst]
  exact hinj (by simpa [B, V, src, dst] using heq)

/-- Explicit parameter tuple for the positive-depth certificate witness.  Values are
determinant-one shift blocks; attentions are sparse block maps indexed by certificate
rows. -/
noncomputable def texAnchorWitnessParams {N d : Nat}
    (hrows : genericCertificateRows N ≤ d) : Params N d :=
  fun j =>
    (texAnchorWitnessShiftV d j.val,
      texAnchorWitnessAttentionMatrix (L := N) (d := d) hrows j.val j.isLt)

noncomputable def texAnchorWitnessT (N : Nat) : AnchorGateVector N :=
  fun _ => 0

noncomputable def texAnchorWitnessS (N : Nat) : AnchorGateVector N :=
  fun _ => 1

noncomputable def texAnchorWitnessW0 {d : Nat} (hd : 0 < d) : Fin d -> ℝ :=
  Pi.single (⟨0, hd⟩ : Fin d) (1 : ℝ)

theorem texAnchorWitness_anchorStepMatrix_T_eq_shiftB
    (N d : Nat) (hrows : genericCertificateRows N ≤ d) (k : Fin (N - 1)) :
    anchorStepMatrix
        (paramStream (texAnchorWitnessParams (N := N) (d := d) hrows))
        k.val (texAnchorWitnessT N k) =
      texAnchorWitnessShiftB d k.val := by
  have hkN : k.val < N := by omega
  rw [anchorStepMatrix, texAnchorWitnessT,
    paramStream_apply_of_lt (texAnchorWitnessParams (N := N) (d := d) hrows) hkN]
  simp [texAnchorWitnessParams, skipB_texAnchorWitnessShiftV]

theorem texAnchorWitness_anchorStepMatrix_S_eq_one
    (N d : Nat) (hrows : genericCertificateRows N ≤ d) (k : Fin (N - 1)) :
    anchorStepMatrix
        (paramStream (texAnchorWitnessParams (N := N) (d := d) hrows))
        k.val (texAnchorWitnessS N k) =
      (1 : Matrix (Fin d) (Fin d) ℝ) := by
  have hkN : k.val < N := by omega
  rw [anchorStepMatrix, texAnchorWitnessS,
    paramStream_apply_of_lt (texAnchorWitnessParams (N := N) (d := d) hrows) hkN]
  simp only [texAnchorWitnessParams, one_smul]
  rw [skipB_texAnchorWitnessShiftV, texAnchorWitnessShiftV]
  abel

theorem texAnchorWitness_anchorCertificateW_eq_current_nat
    (N d : Nat) (hd : 0 < d) (hrows : genericCertificateRows N ≤ d) :
    ∀ n : Nat, (hn : n < N - 1) ->
      anchorCertificateW
          (texAnchorWitnessParams (N := N) (d := d) hrows)
          (texAnchorWitnessT N) n (texAnchorWitnessW0 hd) =
        Pi.single
          (texAnchorWitnessShiftSrc n
            (texAnchorWitnessT_source_lt_d (L := N) (d := d) hrows hn))
          (1 : ℝ)
  | 0, _h0 => by
      rw [anchorCertificateW, anchorRealWprod, Matrix.one_mulVec]
      ext i
      simp [texAnchorWitnessW0, texAnchorWitnessShiftSrc]
  | n + 1, hsucc => by
      have hprev : n < N - 1 := by omega
      have hnN : n < N := by omega
      have hgate :
          anchorGateStream (texAnchorWitnessT N) n = 0 := by
        simp [anchorGateStream, texAnchorWitnessT, hprev]
      have hstep :
          anchorStepMatrix
              (paramStream (texAnchorWitnessParams (N := N) (d := d) hrows))
              n (anchorGateStream (texAnchorWitnessT N) n) =
            texAnchorWitnessShiftB d n := by
        rw [hgate, anchorStepMatrix,
          paramStream_apply_of_lt
            (texAnchorWitnessParams (N := N) (d := d) hrows) hnN]
        simp [texAnchorWitnessParams, skipB_texAnchorWitnessShiftV]
      rw [anchorCertificateW, anchorRealWprod, ← Matrix.mulVec_mulVec]
      change
        anchorStepMatrix
            (paramStream (texAnchorWitnessParams (N := N) (d := d) hrows))
            n (anchorGateStream (texAnchorWitnessT N) n) *ᵥ
          anchorCertificateW
            (texAnchorWitnessParams (N := N) (d := d) hrows)
            (texAnchorWitnessT N) n (texAnchorWitnessW0 hd) =
        Pi.single
          (texAnchorWitnessShiftSrc (n + 1)
            (texAnchorWitnessT_source_lt_d (L := N) (d := d) hrows hsucc))
          (1 : ℝ)
      rw [hstep, texAnchorWitness_anchorCertificateW_eq_current_nat N d hd hrows n hprev]
      simpa [texAnchorWitnessShiftSrc, texAnchorWitnessShiftDst] using
        texAnchorWitnessShiftB_mulVec_current
          (d := d) (j := n)
          (texAnchorWitnessT_source_lt_d (L := N) (d := d) hrows hprev)

theorem texAnchorWitness_anchorCertificateW_eq_current
    (N d : Nat) (hd : 0 < d) (hrows : genericCertificateRows N ≤ d)
    (k : Fin (N - 1)) :
    anchorCertificateW
        (texAnchorWitnessParams (N := N) (d := d) hrows)
        (texAnchorWitnessT N) k.val (texAnchorWitnessW0 hd) =
      Pi.single
        (texAnchorWitnessShiftSrc k.val
          (texAnchorWitnessT_source_lt_d (L := N) (d := d) hrows k.2))
        (1 : ℝ) :=
  texAnchorWitness_anchorCertificateW_eq_current_nat N d hd hrows k.val k.2

theorem texAnchorWitness_gram_det_eq_one_of_gradient_basis_columns
    {L d : Nat} (hrows : genericCertificateRows L ≤ d)
    {θ : Params L d} {t s : AnchorGateVector L} {w0 : Fin d -> ℝ}
    (hgrad :
      ∀ row : AnchorCertificateRow L,
        anchorCertificateGradient θ t s row w0 =
          texAnchorWitnessRowBasis (L := L) (d := d) hrows row) :
    ((Matrix.transpose (anchorCertificateGradientMatrix θ t s w0) *
        anchorCertificateGradientMatrix θ t s w0) :
      Matrix (AnchorCertificateRow L) (AnchorCertificateRow L) ℝ).det = 1 := by
  classical
  refine
    texAnchorWitness_gram_det_eq_one_of_basis_columns'
      (G := anchorCertificateGradientMatrix θ t s w0)
      (e := texAnchorWitnessRowFin (L := L) (d := d) hrows)
      ?_
      (texAnchorWitnessRowFin_injective (L := L) (d := d) hrows)
  intro i row
  simpa [anchorCertificateGradientMatrix, texAnchorWitnessRowBasis] using
    congrFun (hgrad row) i

theorem texAnchorWitness_vectorNormSq_rowBasis_eq_one
    {L d : Nat} (hrows : genericCertificateRows L ≤ d)
    (row : AnchorCertificateRow L) :
    vectorNormSq (texAnchorWitnessRowBasis (L := L) (d := d) hrows row) = 1 := by
  classical
  simp [vectorNormSq, texAnchorWitnessRowBasis]

theorem texAnchorWitness_normProd_ne_zero_of_attention_row_basis
    {L d : Nat} (hrows : genericCertificateRows L ≤ d)
    {θ : Params L d} {t : AnchorGateVector L} {w0 : Fin d -> ℝ}
    (hnorm :
      ∀ k : Fin (L - 1),
        ∃ row : AnchorCertificateRow L,
          (Matrix.transpose (paramStream θ k.val).2).mulVec
              (anchorCertificateW θ t k.val w0) =
            texAnchorWitnessRowBasis (L := L) (d := d) hrows row) :
    (∏ k : Fin (L - 1),
      vectorNormSq ((Matrix.transpose (paramStream θ k.val).2).mulVec
        (anchorCertificateW θ t k.val w0))) ≠ 0 := by
  classical
  have hprod : (∏ k : Fin (L - 1),
      vectorNormSq ((Matrix.transpose (paramStream θ k.val).2).mulVec
        (anchorCertificateW θ t k.val w0))) = 1 := by
    refine Finset.prod_eq_one ?_
    intro k _
    rcases hnorm k with ⟨row, hrow⟩
    rw [hrow]
    exact texAnchorWitness_vectorNormSq_rowBasis_eq_one hrows row
  rw [hprod]
  norm_num

theorem texAnchorWitness_anchorCertificateValue_ne_zero_of_assembly
    {L d : Nat} (hrows : genericCertificateRows L ≤ d)
    {θ : Params L d} {t s : AnchorGateVector L} {w0 : Fin d -> ℝ}
    (hgrad :
      ∀ row : AnchorCertificateRow L,
        anchorCertificateGradient θ t s row w0 =
          texAnchorWitnessRowBasis (L := L) (d := d) hrows row)
    (hstep :
      ∀ k : Fin (L - 1),
        (anchorStepMatrix (paramStream θ) k.val (t k)).det = 1)
    (hnorm :
      ∀ k : Fin (L - 1),
        ∃ row : AnchorCertificateRow L,
          (Matrix.transpose (paramStream θ k.val).2).mulVec
              (anchorCertificateW θ t k.val w0) =
            texAnchorWitnessRowBasis (L := L) (d := d) hrows row) :
    anchorCertificateValue θ t s w0 ≠ 0 := by
  classical
  have hgram :
      ((Matrix.transpose (anchorCertificateGradientMatrix θ t s w0) *
          anchorCertificateGradientMatrix θ t s w0) :
        Matrix (AnchorCertificateRow L) (AnchorCertificateRow L) ℝ).det ≠ 0 := by
    rw [texAnchorWitness_gram_det_eq_one_of_gradient_basis_columns hrows hgrad]
    norm_num
  have hstepProd :
      (∏ k : Fin (L - 1),
        (anchorStepMatrix (paramStream θ) k.val (t k)).det) ≠ 0 := by
    have hprod : (∏ k : Fin (L - 1),
        (anchorStepMatrix (paramStream θ) k.val (t k)).det) = 1 := by
      exact Finset.prod_eq_one fun k _ => hstep k
    rw [hprod]
    norm_num
  have hnormProd :
      (∏ k : Fin (L - 1),
        vectorNormSq ((Matrix.transpose (paramStream θ k.val).2).mulVec
          (anchorCertificateW θ t k.val w0))) ≠ 0 :=
    texAnchorWitness_normProd_ne_zero_of_attention_row_basis hrows hnorm
  rw [anchorCertificateValue]
  exact mul_ne_zero (mul_ne_zero hgram hstepProd) hnormProd

theorem texAnchorWitness_transvection_transpose_mulVec_single_of_ne_target {d : Nat}
    (target source r : Fin d) (c : ℝ) (hr : r ≠ target) :
    (Matrix.transvection target source c)ᵀ *ᵥ Pi.single r (1 : ℝ) =
      Pi.single r (1 : ℝ) := by
  ext a
  rw [Matrix.mulVec_single_one]
  have hsingle : Matrix.single source target c a r = 0 := by
    by_cases has : a = source
    · subst a
      simp [hr.symm]
    · have hsa : source ≠ a := fun h => has h.symm
      simp [Matrix.single, hsa]
  by_cases har : a = r
  · subst a
    simp [Matrix.transvection, hsingle]
  · simp [Matrix.transvection, hsingle, har]

theorem texAnchorWitnessShiftB_transpose_mulVec_other {d j : Nat} (r : Fin d)
    (hrj : r.val ≠ j) (hrj1 : r.val ≠ j + 1) :
    (texAnchorWitnessShiftB d j)ᵀ *ᵥ Pi.single r (1 : ℝ) =
      Pi.single r (1 : ℝ) := by
  classical
  by_cases hj : j + 1 < d
  · let src := texAnchorWitnessShiftSrc j hj
    let dst := texAnchorWitnessShiftDst j hj
    have hrsrc : r ≠ src := by
      intro h
      exact hrj (by simpa [src, texAnchorWitnessShiftSrc] using congrArg Fin.val h)
    have hrdst : r ≠ dst := by
      intro h
      exact hrj1 (by simpa [dst, texAnchorWitnessShiftDst] using congrArg Fin.val h)
    have hright :
        (Matrix.transvection src dst (-1 : ℝ))ᵀ *ᵥ Pi.single r (1 : ℝ) =
          Pi.single r (1 : ℝ) :=
      texAnchorWitness_transvection_transpose_mulVec_single_of_ne_target src dst r
        (-1 : ℝ) hrsrc
    have hleft :
        (Matrix.transvection dst src (1 : ℝ))ᵀ *ᵥ Pi.single r (1 : ℝ) =
          Pi.single r (1 : ℝ) :=
      texAnchorWitness_transvection_transpose_mulVec_single_of_ne_target dst src r
        (1 : ℝ) hrdst
    have hchain :
        (Matrix.transvection dst src (1 : ℝ))ᵀ *ᵥ
            ((Matrix.transvection src dst (-1 : ℝ))ᵀ *ᵥ Pi.single r (1 : ℝ)) =
          Pi.single r (1 : ℝ) := by
      rw [hright, hleft]
    simpa [texAnchorWitnessShiftB, hj, texAnchorWitnessShiftBOfLt, src, dst,
      Matrix.transpose_mul, Matrix.mulVec_mulVec] using hchain
  · rw [texAnchorWitnessShiftB, dif_neg hj, Matrix.transpose_one, Matrix.one_mulVec]

theorem texAnchorWitness_anchorRealBprod_transpose_mulVec_above {N d j : Nat}
    (hrows : genericCertificateRows N ≤ d) (r : Fin d) (hjr : j < r.val) :
    (anchorRealBprod (paramStream (texAnchorWitnessParams (N := N) (d := d) hrows)) j)ᵀ *ᵥ
        Pi.single r (1 : ℝ) =
      Pi.single r (1 : ℝ) := by
  classical
  induction j with
  | zero =>
      rw [anchorRealBprod, Matrix.transpose_one, Matrix.one_mulVec]
  | succ n ih =>
      have hnr : n < r.val := by omega
      have hfix :
          (skipB
              (paramStream (texAnchorWitnessParams (N := N) (d := d) hrows) n).1)ᵀ *ᵥ
              Pi.single r (1 : ℝ) =
            Pi.single r (1 : ℝ) := by
        by_cases hnN : n < N
        · rw [paramStream_apply_of_lt _ hnN]
          simpa [texAnchorWitnessParams, skipB_texAnchorWitnessShiftV] using
            texAnchorWitnessShiftB_transpose_mulVec_other (d := d) (j := n) r
              (by omega) (by omega)
        · rw [paramStream_apply_of_not_lt _ hnN]
          rw [show skipB ((0 : Matrix (Fin d) (Fin d) ℝ)) =
              (1 : Matrix (Fin d) (Fin d) ℝ) by
            simp [skipB]]
          rw [Matrix.transpose_one, Matrix.one_mulVec]
      change
        ((skipB
              (paramStream (texAnchorWitnessParams (N := N) (d := d) hrows) n).1 *
            anchorRealBprod
              (paramStream (texAnchorWitnessParams (N := N) (d := d) hrows)) n)ᵀ) *ᵥ
            Pi.single r (1 : ℝ) =
          Pi.single r (1 : ℝ)
      rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, hfix, ih hnr]

theorem texAnchorWitnessBlockStart_gt_self {j : Nat} (hj : 0 < j) :
    j < texAnchorWitnessBlockStart j := by
  cases j with
  | zero => omega
  | succ j =>
      rw [texAnchorWitnessBlockStart_succ]
      omega

theorem texAnchorWitnessERowFin_val_gt_group {L d j : Nat}
    (hrows : genericCertificateRows L ≤ d) (hj : j < L - 1) (hjpos : 0 < j) :
    j <
      (texAnchorWitnessRowFin (L := L) (d := d) hrows
        (texAnchorWitnessERowOfLt (L := L) hj)).val := by
  change j < texAnchorWitnessRowNat (texAnchorWitnessERowOfLt (L := L) hj)
  rw [texAnchorWitnessRowNat_eRowOfLt]
  have hstart := texAnchorWitnessBlockStart_gt_self hjpos
  omega

theorem texAnchorWitnessSRowFin_val_gt_group {L d k j : Nat}
    (hrows : genericCertificateRows L ≤ d) (hkj : k < j) (hjL : j < L) :
    j <
      (texAnchorWitnessRowFin (L := L) (d := d) hrows
        (texAnchorWitnessSRowOfLt (L := L) hkj hjL)).val := by
  change j < texAnchorWitnessRowNat (texAnchorWitnessSRowOfLt (L := L) hkj hjL)
  rw [texAnchorWitnessRowNat_sRowOfLt]
  have hstart := texAnchorWitnessBlockStart_gt_self (by omega : 0 < j)
  omega

theorem texAnchorWitness_gradientE_eq_rowBasis
    (N d : Nat) (hd : 0 < d) (hrows : genericCertificateRows N ≤ d)
    (k : Fin (N - 1)) :
    anchorCertificateGradientE
        (texAnchorWitnessParams (N := N) (d := d) hrows)
        (texAnchorWitnessT N) k (texAnchorWitnessW0 hd) =
      texAnchorWitnessRowBasis (L := N) (d := d) hrows
        (texAnchorWitnessERowOfLt (L := N) k.2) := by
  classical
  let θ := texAnchorWitnessParams (N := N) (d := d) hrows
  let row := texAnchorWitnessERowOfLt (L := N) k.2
  have hkN : k.val < N := by omega
  have hW :
      anchorCertificateW θ (texAnchorWitnessT N) k.val (texAnchorWitnessW0 hd) =
        Pi.single
          (texAnchorWitnessShiftSrc k.val
            (texAnchorWitnessT_source_lt_d (L := N) (d := d) hrows k.2))
          (1 : ℝ) := by
    simpa [θ] using
      texAnchorWitness_anchorCertificateW_eq_current N d hd hrows k
  have hA :
      (Matrix.transpose (paramStream θ k.val).2).mulVec
          (anchorCertificateW θ (texAnchorWitnessT N) k.val (texAnchorWitnessW0 hd)) =
        texAnchorWitnessRowBasis (L := N) (d := d) hrows row := by
    rw [hW]
    rw [paramStream_apply_of_lt θ hkN]
    simpa [θ, row, texAnchorWitnessParams, texAnchorWitnessRowBasis,
      texAnchorWitnessShiftSrc] using
      texAnchorWitnessAttentionMatrix_image_e (L := N) (d := d)
        hrows hkN k.2
  have hB :
      (Matrix.transpose (anchorRealBprod (paramStream θ) k.val)).mulVec
          (texAnchorWitnessRowBasis (L := N) (d := d) hrows row) =
        texAnchorWitnessRowBasis (L := N) (d := d) hrows row := by
    by_cases hk0 : k.val = 0
    · rw [hk0]
      simp [anchorRealBprod]
    · have hkpos : 0 < k.val := by omega
      exact
        texAnchorWitness_anchorRealBprod_transpose_mulVec_above
          (N := N) (d := d) (j := k.val) hrows
          (texAnchorWitnessRowFin (L := N) (d := d) hrows row)
          (by
            simpa [row] using
              texAnchorWitnessERowFin_val_gt_group
                (L := N) (d := d) hrows k.2 hkpos)
  rw [anchorCertificateGradientE]
  rw [hA]
  exact hB

theorem texAnchorWitness_gradientS_eq_rowBasis
    (N d : Nat) (hd : 0 < d) (hrows : genericCertificateRows N ≤ d)
    (q : AnchorCertificateSIndex N) :
    anchorCertificateGradientS
        (texAnchorWitnessParams (N := N) (d := d) hrows)
        (texAnchorWitnessT N) (texAnchorWitnessS N) q (texAnchorWitnessW0 hd) =
      texAnchorWitnessRowBasis (L := N) (d := d) hrows
        (Sum.inl (Sum.inr q)) := by
  classical
  let θ := texAnchorWitnessParams (N := N) (d := d) hrows
  let k : Fin (N - 1) := q.1
  let ell : Nat := q.2.1.val
  let n : Nat := k.val + ell - 1
  have hell2 : 2 ≤ ell := q.2.2.1
  have hsum : k.val + ell ≤ N := q.2.2.2
  have hkn : k.val < n := by
    dsimp [n]
    omega
  have hnN : n < N := by
    dsimp [n]
    omega
  have hrowfin :
      texAnchorWitnessRowFin (L := N) (d := d) hrows
          (texAnchorWitnessSRowOfLt (L := N) hkn hnN) =
        texAnchorWitnessRowFin (L := N) (d := d) hrows
          (Sum.inl (Sum.inr q)) := by
    apply Fin.ext
    change
      texAnchorWitnessRowNat (texAnchorWitnessSRowOfLt (L := N) hkn hnN) =
        texAnchorWitnessRowNat (Sum.inl (Sum.inr q))
    rw [texAnchorWitnessRowNat_sRowOfLt]
    simp [texAnchorWitnessRowNat, k, ell, n]
  have hrowbasis :
      texAnchorWitnessRowBasis (L := N) (d := d) hrows
          (texAnchorWitnessSRowOfLt (L := N) hkn hnN) =
        texAnchorWitnessRowBasis (L := N) (d := d) hrows
          (Sum.inl (Sum.inr q)) := by
    rw [texAnchorWitnessRowBasis, texAnchorWitnessRowBasis, hrowfin]
  have hW :
      anchorCertificateW θ (texAnchorWitnessT N) k.val (texAnchorWitnessW0 hd) =
        Pi.single
          (texAnchorWitnessShiftSrc k.val
            (texAnchorWitnessT_source_lt_d (L := N) (d := d) hrows k.2))
          (1 : ℝ) := by
    simpa [θ, k] using
      texAnchorWitness_anchorCertificateW_eq_current N d hd hrows k
  have hstepW :
      (anchorStepMatrix (paramStream θ) k.val (texAnchorWitnessS N k)).mulVec
          (anchorCertificateW θ (texAnchorWitnessT N) k.val (texAnchorWitnessW0 hd)) =
        Pi.single
          (texAnchorWitnessShiftSrc k.val
            (texAnchorWitnessT_source_lt_d (L := N) (d := d) hrows k.2))
          (1 : ℝ) := by
    rw [texAnchorWitness_anchorStepMatrix_S_eq_one N d hrows k]
    rw [Matrix.one_mulVec, hW]
  have hA :
      (Matrix.transpose (paramStream θ n).2).mulVec
          ((anchorStepMatrix (paramStream θ) k.val (texAnchorWitnessS N k)).mulVec
            (anchorCertificateW θ (texAnchorWitnessT N) k.val (texAnchorWitnessW0 hd))) =
        texAnchorWitnessRowBasis (L := N) (d := d) hrows
          (texAnchorWitnessSRowOfLt (L := N) hkn hnN) := by
    rw [hstepW]
    rw [paramStream_apply_of_lt θ hnN]
    simpa [θ, k, n, texAnchorWitnessParams, texAnchorWitnessRowBasis,
      texAnchorWitnessShiftSrc] using
      texAnchorWitnessAttentionMatrix_image_s (L := N) (d := d)
        hrows hkn hnN
  have hB :
      (Matrix.transpose (anchorRealBprod (paramStream θ) n)).mulVec
          (texAnchorWitnessRowBasis (L := N) (d := d) hrows
            (texAnchorWitnessSRowOfLt (L := N) hkn hnN)) =
        texAnchorWitnessRowBasis (L := N) (d := d) hrows
          (texAnchorWitnessSRowOfLt (L := N) hkn hnN) :=
    texAnchorWitness_anchorRealBprod_transpose_mulVec_above
      (N := N) (d := d) (j := n) hrows
      (texAnchorWitnessRowFin (L := N) (d := d) hrows
        (texAnchorWitnessSRowOfLt (L := N) hkn hnN))
      (texAnchorWitnessSRowFin_val_gt_group
        (L := N) (d := d) hrows hkn hnN)
  rw [anchorCertificateGradientS]
  change
    (Matrix.transpose (anchorRealBprod (paramStream θ) n)).mulVec
      ((Matrix.transpose (paramStream θ n).2).mulVec
        ((anchorStepMatrix (paramStream θ) k.val (texAnchorWitnessS N k)).mulVec
          (anchorCertificateW θ (texAnchorWitnessT N) k.val (texAnchorWitnessW0 hd)))) =
      texAnchorWitnessRowBasis (L := N) (d := d) hrows (Sum.inl (Sum.inr q))
  rw [hA, hB, hrowbasis]

theorem texAnchorWitnessTRowFin_val_gt_group_all {L d j : Nat}
    (hrows : genericCertificateRows L ≤ d) (hj : j < L - 1) :
    j <
      (texAnchorWitnessRowFin (L := L) (d := d) hrows
        (texAnchorWitnessTRowOfLt (L := L) hj)).val := by
  change j < texAnchorWitnessRowNat (texAnchorWitnessTRowOfLt (L := L) hj)
  rw [texAnchorWitnessRowNat_tRowOfLt]
  omega

theorem texAnchorWitness_gradientT_eq_rowBasis
    (N d : Nat) (hd : 0 < d) (hrows : genericCertificateRows N ≤ d)
    (k : Fin (N - 1)) :
    anchorCertificateGradientT
        (texAnchorWitnessParams (N := N) (d := d) hrows)
        (texAnchorWitnessT N) k (texAnchorWitnessW0 hd) =
      texAnchorWitnessRowBasis (L := N) (d := d) hrows
        (texAnchorWitnessTRowOfLt (L := N) k.2) := by
  classical
  let θ := texAnchorWitnessParams (N := N) (d := d) hrows
  let row := texAnchorWitnessTRowOfLt (L := N) k.2
  have hkN : k.val < N := by omega
  have hW :
      anchorCertificateW θ (texAnchorWitnessT N) k.val (texAnchorWitnessW0 hd) =
        Pi.single
          (texAnchorWitnessShiftSrc k.val
            (texAnchorWitnessT_source_lt_d (L := N) (d := d) hrows k.2))
          (1 : ℝ) := by
    simpa [θ] using
      texAnchorWitness_anchorCertificateW_eq_current N d hd hrows k
  have hM :
      anchorStepMatrix (paramStream θ) k.val (texAnchorWitnessT N k) =
        texAnchorWitnessShiftB d k.val := by
    simpa [θ] using
      texAnchorWitness_anchorStepMatrix_T_eq_shiftB N d hrows k
  have hZ :
      (anchorStepMatrix (paramStream θ) k.val (texAnchorWitnessT N k)).adjugate.mulVec
          ((paramStream θ k.val).1.mulVec
            (anchorCertificateW θ (texAnchorWitnessT N) k.val (texAnchorWitnessW0 hd))) =
        Pi.single
          (texAnchorWitnessShiftDst k.val
            (texAnchorWitnessT_source_lt_d (L := N) (d := d) hrows k.2))
          (1 : ℝ) := by
    rw [hM, hW]
    rw [paramStream_apply_of_lt θ hkN]
    simpa [θ, texAnchorWitnessParams, texAnchorWitnessShiftSrc] using
      texAnchorWitnessShift_adjugate_mulVec_V_current
        (d := d) (j := k.val)
        (texAnchorWitnessT_source_lt_d (L := N) (d := d) hrows k.2)
  have hA :
      (Matrix.transpose (paramStream θ k.val).2).mulVec
          ((anchorStepMatrix (paramStream θ) k.val (texAnchorWitnessT N k)).adjugate.mulVec
            ((paramStream θ k.val).1.mulVec
              (anchorCertificateW θ (texAnchorWitnessT N) k.val (texAnchorWitnessW0 hd)))) =
        -texAnchorWitnessRowBasis (L := N) (d := d) hrows row := by
    rw [hZ]
    rw [paramStream_apply_of_lt θ hkN]
    simpa [θ, row, texAnchorWitnessParams, texAnchorWitnessRowBasis,
      texAnchorWitnessShiftDst] using
      texAnchorWitnessAttentionMatrix_image_t (L := N) (d := d)
        hrows hkN k.2
  have hBbasis :
      (Matrix.transpose (anchorRealBprod (paramStream θ) k.val)).mulVec
          (texAnchorWitnessRowBasis (L := N) (d := d) hrows row) =
        texAnchorWitnessRowBasis (L := N) (d := d) hrows row :=
    texAnchorWitness_anchorRealBprod_transpose_mulVec_above
      (N := N) (d := d) (j := k.val) hrows
      (texAnchorWitnessRowFin (L := N) (d := d) hrows row)
      (by
        simpa [row] using
          texAnchorWitnessTRowFin_val_gt_group_all
            (L := N) (d := d) hrows k.2)
  have hBneg :
      (Matrix.transpose (anchorRealBprod (paramStream θ) k.val)).mulVec
          (-texAnchorWitnessRowBasis (L := N) (d := d) hrows row) =
        -texAnchorWitnessRowBasis (L := N) (d := d) hrows row := by
    rw [Matrix.mulVec_neg, hBbasis]
  rw [anchorCertificateGradientT]
  change
    (fun i =>
      -((Matrix.transpose (anchorRealBprod (paramStream θ) k.val)).mulVec
        ((Matrix.transpose (paramStream θ k.val).2).mulVec
          ((anchorStepMatrix (paramStream θ) k.val (texAnchorWitnessT N k)).adjugate.mulVec
            ((paramStream θ k.val).1.mulVec
              (anchorCertificateW θ (texAnchorWitnessT N) k.val (texAnchorWitnessW0 hd))))) i)) =
      texAnchorWitnessRowBasis (L := N) (d := d) hrows row
  rw [hA, hBneg]
  ext i
  simp

/-- Exact remaining algebraic calculation for the concrete positive-depth witness.

This statement contains no existential choices: it is the determinant-one shift value
matrices, sparse block attention maps, `t = 0`, `s = 1`, and `w0 = e_0`.
The proof is the remaining formal version of the TeX column-independence calculation. -/
theorem texAnchorWitness_value_ne_zero_succ_succ
    (L d : Nat) (hd : 0 < d)
    (hrows : genericCertificateRows (L + 2) ≤ d) :
    anchorCertificateValue (texAnchorWitnessParams (N := L + 2) (d := d) hrows)
      (texAnchorWitnessT (L + 2)) (texAnchorWitnessS (L + 2))
      (texAnchorWitnessW0 hd) ≠ 0 := by
  classical
  let N := L + 2
  let θ := texAnchorWitnessParams (N := N) (d := d) hrows
  refine
    texAnchorWitness_anchorCertificateValue_ne_zero_of_assembly
      (L := N) (d := d) hrows
      (θ := θ) (t := texAnchorWitnessT N) (s := texAnchorWitnessS N)
      (w0 := texAnchorWitnessW0 hd) ?hgrad ?hstep ?hnorm
  · intro row
    rcases row with ((k | q) | k)
    · simpa [θ, N, anchorCertificateGradient, texAnchorWitnessERowOfLt] using
        texAnchorWitness_gradientE_eq_rowBasis N d hd hrows k
    · simpa [θ, N, anchorCertificateGradient] using
        texAnchorWitness_gradientS_eq_rowBasis N d hd hrows q
    · simpa [θ, N, anchorCertificateGradient, texAnchorWitnessTRowOfLt] using
        texAnchorWitness_gradientT_eq_rowBasis N d hd hrows k
  · intro k
    rw [texAnchorWitness_anchorStepMatrix_T_eq_shiftB N d hrows k]
    exact texAnchorWitnessShiftB_det
      (d := d) (j := k.val)
      (texAnchorWitnessT_source_lt_d (L := N) (d := d) hrows k.2)
  · intro k
    refine ⟨texAnchorWitnessERowOfLt (L := N) k.2, ?_⟩
    have hkN : k.val < N := by omega
    have hW :
        anchorCertificateW θ (texAnchorWitnessT N) k.val (texAnchorWitnessW0 hd) =
          Pi.single
            (texAnchorWitnessShiftSrc k.val
              (texAnchorWitnessT_source_lt_d (L := N) (d := d) hrows k.2))
            (1 : ℝ) := by
      simpa [θ] using
        texAnchorWitness_anchorCertificateW_eq_current N d hd hrows k
    rw [hW]
    rw [paramStream_apply_of_lt θ hkN]
    simpa [θ, N, texAnchorWitnessParams, texAnchorWitnessRowBasis,
      texAnchorWitnessShiftSrc] using
      texAnchorWitnessAttentionMatrix_image_e (L := N) (d := d)
        hrows hkN k.2

/-- Remaining TeX witness construction for positive certificate depth.  This is the
formal version of the rank-one nilpotent value matrices, block attention maps,
`t = 0`, `s = 1`, and `w0 = e_0` construction from `n_layer_proof.tex`. -/
theorem texAnchorCertificate_hasConcreteWitness_succ_succ_of_row_bound
    (L d : Nat) (hd : 0 < d)
    (hrows : genericCertificateRows (L + 2) ≤ d) :
    texAnchorCertificate_hasConcreteWitness (L + 2) d := by
  refine ⟨texAnchorWitnessParams (N := L + 2) (d := d) hrows, ?_⟩
  refine ⟨texAnchorWitnessT (L + 2), texAnchorWitnessS (L + 2),
    texAnchorWitnessW0 hd, ?_⟩
  exact texAnchorWitness_value_ne_zero_succ_succ L d hd hrows

theorem texAnchorCertificate_hasConcreteWitness_of_row_bound
    (L d : Nat) (hd : 0 < d) (hrows : genericCertificateRows L ≤ d) :
    texAnchorCertificate_hasConcreteWitness L d := by
  cases L with
  | zero =>
      exact texAnchorCertificate_hasConcreteWitness_zero d
  | succ L =>
      cases L with
      | zero =>
          exact texAnchorCertificate_hasConcreteWitness_one d
      | succ L =>
          exact texAnchorCertificate_hasConcreteWitness_succ_succ_of_row_bound L d hd hrows

theorem texAnchorCertificate_exists_aux_eval_of_coeff_nonzero {L d : Nat}
    (θ : Params L d)
    (hcoeff :
      ∀ a : TexAnchorCertificateCoeffIndex L d, a ∈ (Finset.univ) ->
        (MvPolynomial.eval (paramFlat θ))
          (texAnchorCertificate_coeffPolynomial L d a.1) ≠ 0)
    (hnonzero : texAnchorCertificate_auxPolynomial L d ≠ 0) :
    θ ∈ TexAnchorCertificateSet L d := by
  classical
  haveI : Fintype (TexAnchorCertificateAuxCoord L d) := inferInstance
  haveI : DecidableEq (TexAnchorCertificateAuxCoord L d) := inferInstance
  have hsupp : (texAnchorCertificate_coeffSupport L d).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hs
    apply hnonzero
    exact MvPolynomial.support_eq_empty.mp (by
      simpa [texAnchorCertificate_coeffSupport] using hs)
  obtain ⟨m, hm⟩ := hsupp
  let a : TexAnchorCertificateCoeffIndex L d := ⟨m, hm⟩
  let pθ : MvPolynomial (TexAnchorCertificateAuxCoord L d) ℝ :=
    MvPolynomial.map (MvPolynomial.eval (paramFlat θ))
      (texAnchorCertificate_auxPolynomial L d)
  have hcoeff_eval : MvPolynomial.coeff m pθ ≠ 0 := by
    simpa [pθ, texAnchorCertificate_coeffPolynomial, a] using
      hcoeff a (Finset.mem_univ a)
  have hpθ : pθ ≠ 0 := by
    intro hpzero
    exact hcoeff_eval (by simp [hpzero])
  obtain ⟨y, _hyU, hyne⟩ :=
    (dense_compl_zero_set pθ hpθ).inter_open_nonempty Set.univ isOpen_univ
      ⟨fun _ => 0, trivial⟩
  let t : AnchorGateVector L := fun k => y (Sum.inl (Sum.inl k))
  let s : AnchorGateVector L := fun k => y (Sum.inl (Sum.inr k))
  let w0 : Fin d -> ℝ := fun i => y (Sum.inr i)
  refine ⟨t, s, w0, ?_⟩
  have hy_eq :
      y = texAnchorCertificate_auxEval t s w0 := by
    funext a
    rcases a with (⟨k | k⟩ | i) <;> rfl
  have hcombined :
      Sum.elim y (paramFlat θ) =
        texAnchorCertificate_combinedEval θ t s w0 := by
    funext z
    cases z with
    | inl a =>
        simp [hy_eq]
    | inr c =>
        rfl
  have hpoly :
      (MvPolynomial.eval y) pθ =
        anchorCertificateValue θ t s w0 := by
    change
      (MvPolynomial.eval y)
          (MvPolynomial.map (MvPolynomial.eval (paramFlat θ))
            (texAnchorCertificate_auxPolynomial L d)) =
        anchorCertificateValue θ t s w0
    rw [texAnchorCertificate_auxPolynomial_eval_eq θ y, hcombined,
      texAnchorCertificate_eval_polynomial]
  exact by
    intro hzero
    exact hyne (by simp [hpoly, hzero])

/-- Algebraic nontriviality of the auxiliary certificate polynomial.  This is the
remaining coefficient-level input: under the TeX row-count bound, the displayed
certificate expression is not the zero polynomial in the auxiliary variables. -/
theorem texAnchorCertificate_auxPolynomial_ne_zero
    (L d : Nat) (hd : 0 < d) (hrows : genericCertificateRows L ≤ d) :
    texAnchorCertificate_auxPolynomial L d ≠ 0 := by
  exact texAnchorCertificate_auxPolynomial_ne_zero_of_concreteWitness
    (texAnchorCertificate_hasConcreteWitness_of_row_bound L d hd hrows)

/--
Missing algebraic bridge for density of `(G4)`: exhibit finite coordinate-polynomial
nonvanishing data whose carrier is contained in the exact anchor-certificate locus.

The intended witness is a finite family of nonzero coefficient polynomials for the
polynomial
`anchorCertificateValue θ t s w0` in the auxiliary variables `(t, s, w0)`, or an
equivalent finite cover, together with the implication from coefficient nonvanishing to
existence of a concrete `(t, s, w0)` evaluation where the certificate value is nonzero.
-/
theorem texAnchorCertificate_exists_coefficient_polynomial_cover
    (L d : Nat) (hd : 0 < d) (hrows : genericCertificateRows L ≤ d) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ),
      ∃ D : PolynomialNonvanishingData (ParamCoord L d) κ,
        paramNonvanishingCarrier D ⊆ TexAnchorCertificateSet L d := by
  classical
  let κ := TexAnchorCertificateCoeffIndex L d
  let D := texAnchorCertificate_coefficientNonvanishingData L d
  refine ⟨κ, inferInstance, inferInstance, D, ?_⟩
  intro θ hθ
  exact texAnchorCertificate_exists_aux_eval_of_coeff_nonzero θ
    (by
      intro a ha
      exact hθ a ha)
    (texAnchorCertificate_auxPolynomial_ne_zero L d hd hrows)

theorem texAnchorCertificate_dense_set_of_polynomial_witness
    (L d : Nat) (hd : 0 < d) (hrows : genericCertificateRows L ≤ d) :
    Dense (TexAnchorCertificateSet L d) := by
  obtain ⟨κ, hκ, hκdec, D, hsubset⟩ :=
    texAnchorCertificate_exists_coefficient_polynomial_cover L d hd hrows
  letI : Fintype κ := hκ
  letI : DecidableEq κ := hκdec
  exact (texAnchorCertificate_dense_paramNonvanishingCarrier (L := L) (d := d) D).mono hsubset

theorem texAnchorCertificate_dense_set_of_polynomial_witness_of_row_bound
    (L d : Nat) (hd : 0 < d) (hrows : genericCertificateRows L ≤ d) :
    Dense (TexAnchorCertificateSet L d) :=
  texAnchorCertificate_dense_set_of_polynomial_witness L d hd hrows

/-- Row-bound anchor-certificate topology obligations.  The row-count hypothesis is
intrinsic: when the certificate row count exceeds `d`, the Gram determinant in `(G4)`
vanishes identically. -/
structure TexAnchorCertificateRowBoundTopologyObligations : Prop where
  isOpen : ∀ L d : Nat, IsOpen (TexAnchorCertificateSet L d)
  dense : ∀ L d : Nat, 0 < d -> genericCertificateRows L ≤ d ->
    Dense (TexAnchorCertificateSet L d)

theorem texAnchorCertificateRowBoundTopologyObligations_concrete :
    TexAnchorCertificateRowBoundTopologyObligations := by
  exact
    { isOpen := texAnchorCertificate_isOpen_set
      dense := texAnchorCertificate_dense_set_of_polynomial_witness_of_row_bound }

end TransformerIdentifiability.NLayer
