import AnyLayerIdentifiabilityProof.NLayer.Genericity.TexGenericNull
import AnyLayerIdentifiabilityProof.NLayer.Foundations.ParamPolynomialGenericity
import AnyLayerIdentifiabilityProof.NLayer.Foundations.PolynomialGenericity
import AnyLayerIdentifiabilityProof.NLayer.Genericity.TexAnchorCertificateTopology

set_option autoImplicit false

open Matrix MvPolynomial

namespace TransformerIdentifiability.NLayer

/-!
# Concrete polynomial covers for TeX genericity

This shard builds the finite coordinate-polynomial packages for the easy TeX clauses:
the depth-one base case and the recursive matrix clauses `(G1)`--`(G3)`.  The only
remaining algebraic input is packaged as the `(G4)` certificate cover below.
-/

/-- A finite coordinate-polynomial package whose common nonvanishing locus implies an
arbitrary predicate on `Params L d`. -/
structure ParamPolynomialPredicateCover (L d : Nat) (P : Params L d -> Prop) : Type 1 where
  κ : Type
  data : PolynomialNonvanishingData (ParamCoord L d) κ
  carrier_subset : paramNonvanishingCarrier data ⊆ {θ | P θ}

namespace ParamPolynomialPredicateCover

/-- Convert a predicate cover for `TexGeneric` into the nullness-facing cover type. -/
def toTexGenericPolynomialNonvanishingCover {L d : Nat}
    (C : ParamPolynomialPredicateCover L d (fun θ => TexGeneric L d θ)) :
    TexGenericPolynomialNonvanishingCover L d where
  κ := C.κ
  data := C.data
  carrier_subset_texGeneric := by
    intro θ hθ
    exact C.carrier_subset hθ

/-- The empty polynomial family covers the always-true predicate. -/
def trueCover (L d : Nat) :
    ParamPolynomialPredicateCover L d (fun _θ => True) where
  κ := Empty
  data :=
    { indices := ∅
      poly := Empty.elim
      nonzero := by
        intro a ha
        cases ha }
  carrier_subset := by
    intro θ hθ
    trivial

/-- Finite union/product assembly for conjunctions of predicate covers. -/
noncomputable def and {L d : Nat} {P Q : Params L d -> Prop}
    (CP : ParamPolynomialPredicateCover L d P)
    (CQ : ParamPolynomialPredicateCover L d Q) :
    ParamPolynomialPredicateCover L d (fun θ => P θ ∧ Q θ) where
  κ := CP.κ ⊕ CQ.κ
  data :=
    { indices := by
        classical
        exact CP.data.indices.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
          CQ.data.indices.map ⟨Sum.inr, Sum.inr_injective⟩
      poly := fun a =>
        match a with
        | Sum.inl i => CP.data.poly i
        | Sum.inr i => CQ.data.poly i
      nonzero := by
        intro a ha
        classical
        cases a with
        | inl i =>
            exact CP.data.nonzero i (by
              have hi : Sum.inl i ∈ CP.data.indices.map ⟨Sum.inl, Sum.inl_injective⟩ :=
                Finset.mem_union.mp ha |>.resolve_right (by
                  intro h
                  simp [Finset.mem_map] at h)
              simpa [Finset.mem_map] using hi)
        | inr i =>
            exact CQ.data.nonzero i (by
              have hi : Sum.inr i ∈ CQ.data.indices.map ⟨Sum.inr, Sum.inr_injective⟩ :=
                Finset.mem_union.mp ha |>.resolve_left (by
                  intro h
                  simp [Finset.mem_map] at h)
              simpa [Finset.mem_map] using hi) }
  carrier_subset := by
    intro θ hθ
    constructor
    · apply CP.carrier_subset
      intro a ha
      exact hθ (Sum.inl a) (by
        classical
        exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨a, ha, rfl⟩))
    · apply CQ.carrier_subset
      intro a ha
      exact hθ (Sum.inr a) (by
        classical
        exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨a, ha, rfl⟩))

end ParamPolynomialPredicateCover

/-! ## Tail-coordinate renaming -/

/-- Embed tail coordinates into one-more-layer coordinates by shifting the layer index. -/
def tailParamCoordEmbedding (L d : Nat) : ParamCoord L d -> ParamCoord (L + 1) d :=
  fun c => (Fin.succ c.1, c.2)

theorem tailParamCoordEmbedding_injective (L d : Nat) :
    Function.Injective (tailParamCoordEmbedding L d) := by
  intro a b h
  cases a with
  | mk la ca =>
  cases b with
  | mk lb cb =>
    simp [tailParamCoordEmbedding] at h
    exact Prod.ext h.1 h.2

@[simp]
theorem paramFlat_tailParamCoordEmbedding {L d : Nat}
    (θ : Params (L + 1) d) (c : ParamCoord L d) :
    paramFlat θ (tailParamCoordEmbedding L d c) = paramFlat (Fin.tail θ) c := by
  cases c with
  | mk l c =>
    cases c with
    | inl ij =>
        cases ij
        rfl
    | inr ij =>
        cases ij
        rfl

theorem eval_tail_rename {L d : Nat} (θ : Params (L + 1) d)
    (p : ParamRing L d) :
    (MvPolynomial.eval (paramFlat θ))
        (MvPolynomial.rename (tailParamCoordEmbedding L d) p) =
      (MvPolynomial.eval (paramFlat (Fin.tail θ))) p := by
  simpa [Function.comp_def] using
    (MvPolynomial.eval_rename (tailParamCoordEmbedding L d) (paramFlat θ) p)

/-- Lift a predicate cover on the tail parameters to a cover on one-more-layer
parameters. -/
noncomputable def tailLift {L d : Nat} {P : Params L d -> Prop}
    (C : ParamPolynomialPredicateCover L d P) :
    ParamPolynomialPredicateCover (L + 1) d (fun θ => P (Fin.tail θ)) where
  κ := C.κ
  data :=
    { indices := C.data.indices
      poly := fun a => MvPolynomial.rename (tailParamCoordEmbedding L d) (C.data.poly a)
      nonzero := by
        intro a ha
        exact (MvPolynomial.rename_injective (tailParamCoordEmbedding L d)
          (tailParamCoordEmbedding_injective L d)).ne (C.data.nonzero a ha) }
  carrier_subset := by
    intro θ hθ
    apply C.carrier_subset
    intro a ha
    have h := hθ a ha
    simpa [eval_tail_rename θ (C.data.poly a)] using h

/-! ## Generic parameter-polynomial matrices -/

/-- Generic value matrix at a natural layer index, with a zero fallback out of range. -/
noncomputable def genValueAt (L d : Nat) (n : Nat) :
    Matrix (Fin d) (Fin d) (ParamRing L d) :=
  if h : n < L then genValue L d ⟨n, h⟩ else 0

/-- Generic attention matrix at a natural layer index, with a zero fallback out of range. -/
noncomputable def genAttentionAt (L d : Nat) (n : Nat) :
    Matrix (Fin d) (Fin d) (ParamRing L d) :=
  if h : n < L then genAttention L d ⟨n, h⟩ else 0

@[simp]
theorem map_genValueAt {L d : Nat} (θ : Params L d) (n : Nat) :
    (genValueAt L d n).map (MvPolynomial.eval (paramFlat θ)) =
      (paramStream θ n).1 := by
  by_cases h : n < L
  · simp [genValueAt, h, map_genValue, paramStream_apply_of_lt]
  · ext i j
    simp [genValueAt, h, paramStream_apply_of_not_lt]

@[simp]
theorem map_genAttentionAt {L d : Nat} (θ : Params L d) (n : Nat) :
    (genAttentionAt L d n).map (MvPolynomial.eval (paramFlat θ)) =
      (paramStream θ n).2 := by
  by_cases h : n < L
  · simp [genAttentionAt, h, map_genAttention, paramStream_apply_of_lt]
  · ext i j
    simp [genAttentionAt, h, paramStream_apply_of_not_lt]

/-- Polynomial skip matrix `I + V`. -/
noncomputable def genSkipB {L d : Nat}
    (V : Matrix (Fin d) (Fin d) (ParamRing L d)) :
    Matrix (Fin d) (Fin d) (ParamRing L d) :=
  1 + V

@[simp]
theorem map_genSkipB {L d : Nat} (θ : Params L d)
    (V : Matrix (Fin d) (Fin d) (ParamRing L d)) :
    (genSkipB V).map (MvPolynomial.eval (paramFlat θ)) =
      skipB (V.map (MvPolynomial.eval (paramFlat θ))) := by
  ext i j
  by_cases hij : i = j
  · simp [genSkipB, skipB, Matrix.map_apply, Matrix.add_apply, hij]
  · simp [genSkipB, skipB, Matrix.map_apply, Matrix.add_apply, hij]

/-- Polynomial product `V_{n-1} ... V_0`. -/
noncomputable def genRealVprod (L d : Nat) :
    Nat -> Matrix (Fin d) (Fin d) (ParamRing L d)
  | 0 => 1
  | n + 1 => genValueAt L d n * genRealVprod L d n

@[simp]
theorem map_genRealVprod {L d : Nat} (θ : Params L d) :
    ∀ n, (genRealVprod L d n).map (MvPolynomial.eval (paramFlat θ)) =
      realVprod (paramStream θ) n
  | 0 => by
      ext i j
      by_cases hij : i = j
      · simp [genRealVprod, Matrix.map_apply, hij]
      · simp [genRealVprod, Matrix.map_apply, hij]
  | n + 1 => by
      rw [genRealVprod, realVprod_succ, Matrix.map_mul, map_genValueAt,
        map_genRealVprod θ n]

/-- Polynomial symmetric part. -/
noncomputable def genSymPart {L d : Nat}
    (M : Matrix (Fin d) (Fin d) (ParamRing L d)) :
    Matrix (Fin d) (Fin d) (ParamRing L d) :=
  (MvPolynomial.C (1 / 2 : ℝ) : ParamRing L d) • (M + Mᵀ)

@[simp]
theorem map_genSymPart {L d : Nat} (θ : Params L d)
    (M : Matrix (Fin d) (Fin d) (ParamRing L d)) :
    (genSymPart M).map (MvPolynomial.eval (paramFlat θ)) =
      symPart (M.map (MvPolynomial.eval (paramFlat θ))) := by
  ext i j
  simp [genSymPart, symPart, Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

/-- Polynomial `kappa` matrix from `(G2)`. -/
noncomputable def genKappaMatrix (L d : Nat) (n : Nat) :
    Matrix (Fin d) (Fin d) (ParamRing L d) :=
  genSymPart
    ((genRealVprod L d (n + 1))ᵀ * genAttentionAt L d (n + 1) *
      genRealVprod L d (n + 1))

@[simp]
theorem map_genKappaMatrix {L d : Nat} (θ : Params L d) (n : Nat) :
    (genKappaMatrix L d n).map (MvPolynomial.eval (paramFlat θ)) =
      kappaMatrix (paramStream θ) n := by
  rw [genKappaMatrix, kappaMatrix, map_genSymPart]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, map_genRealVprod,
    map_genAttentionAt]

theorem eval_det_matrix {L d : Nat} (θ : Params L d)
    (M : Matrix (Fin d) (Fin d) (ParamRing L d)) :
    (MvPolynomial.eval (paramFlat θ)) M.det =
      (M.map (MvPolynomial.eval (paramFlat θ))).det := by
  simpa [RingHom.mapMatrix_apply] using
    (RingHom.map_det (MvPolynomial.eval (paramFlat θ)) M)

/-! ## Algebraic nontriviality obligations -/

theorem mvPolynomial_ne_zero_of_eval_eq_one {ι : Type*} (x : ι -> ℝ)
    {p : MvPolynomial ι ℝ} (hp : (MvPolynomial.eval x) p = 1) :
    p ≠ 0 := by
  intro hzero
  have hone_zero : (1 : ℝ) = 0 := by
    rw [← hp]
    simp [hzero]
  exact one_ne_zero hone_zero

@[simp]
theorem skipB_zero_matrix (d : Nat) :
    skipB (0 : Matrix (Fin d) (Fin d) ℝ) = 1 := by
  ext i j
  simp [skipB]

@[simp]
theorem symPart_one_matrix (d : Nat) :
    symPart (1 : Matrix (Fin d) (Fin d) ℝ) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [symPart, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq]
    ring
  · simp [symPart, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_ne hij]

theorem realVprod_eq_one_of_value_eq_one_lt {d : Nat} (θ : LayerStream d) :
    ∀ n : Nat,
      (∀ k : Nat, k < n -> (θ k).1 = (1 : Matrix (Fin d) (Fin d) ℝ)) ->
        realVprod θ n = 1 := by
  intro n
  induction n with
  | zero =>
      intro _h
      simp
  | succ n ih =>
      intro h
      rw [realVprod_succ, h n (Nat.lt_succ_self n),
        ih (fun k hk => h k (Nat.lt_trans hk (Nat.lt_succ_self n)))]
      simp

theorem texGenericPolynomialCover_det_genAttentionAt_ne_zero
    (L d n : Nat) (hn : n < L) :
    (genAttentionAt L d n).det ≠ 0 := by
  let θ : Params L d := fun l =>
    ((0 : Matrix (Fin d) (Fin d) ℝ),
      if l = ⟨n, hn⟩ then (1 : Matrix (Fin d) (Fin d) ℝ) else 0)
  refine mvPolynomial_ne_zero_of_eval_eq_one (paramFlat θ) ?_
  rw [eval_det_matrix θ (genAttentionAt L d n)]
  have hmap :
      (genAttentionAt L d n).map (MvPolynomial.eval (paramFlat θ)) =
        (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [map_genAttentionAt]
    simp [θ, paramStream_apply_of_lt, hn]
  rw [hmap]
  simp

theorem texGenericPolynomialCover_det_genSkipB_ne_zero
    (L d n : Nat) (hn : n < L) :
    (genSkipB (genValueAt L d n)).det ≠ 0 := by
  let θ : Params L d := fun _l =>
    ((0 : Matrix (Fin d) (Fin d) ℝ), (0 : Matrix (Fin d) (Fin d) ℝ))
  refine mvPolynomial_ne_zero_of_eval_eq_one (paramFlat θ) ?_
  rw [eval_det_matrix θ (genSkipB (genValueAt L d n))]
  have hvalue : (paramStream θ n).1 = (0 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [paramStream_apply_of_lt θ hn]
  have hmap :
      (genSkipB (genValueAt L d n)).map (MvPolynomial.eval (paramFlat θ)) =
        (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [map_genSkipB, map_genValueAt, hvalue]
    simp
  rw [hmap]
  simp

theorem texGenericPolynomialCover_det_genRealVprod_ne_zero
    (L d n : Nat) (hn : n ≤ L) :
    (genRealVprod L d n).det ≠ 0 := by
  let θ : Params L d := fun _l =>
    ((1 : Matrix (Fin d) (Fin d) ℝ), (0 : Matrix (Fin d) (Fin d) ℝ))
  refine mvPolynomial_ne_zero_of_eval_eq_one (paramFlat θ) ?_
  rw [eval_det_matrix θ (genRealVprod L d n)]
  have hvalues :
      ∀ k : Nat, k < n -> (paramStream θ k).1 = (1 : Matrix (Fin d) (Fin d) ℝ) := by
    intro k hk
    have hkL : k < L := Nat.lt_of_lt_of_le hk hn
    rw [paramStream_apply_of_lt θ hkL]
  have hmap :
      (genRealVprod L d n).map (MvPolynomial.eval (paramFlat θ)) =
        (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [map_genRealVprod]
    exact realVprod_eq_one_of_value_eq_one_lt (paramStream θ) n hvalues
  rw [hmap]
  simp

theorem texGenericPolynomialCover_det_genKappaMatrix_ne_zero
    (L d n : Nat) (hn : n + 1 < L) :
    (genKappaMatrix L d n).det ≠ 0 := by
  let θ : Params L d := fun l =>
    ((1 : Matrix (Fin d) (Fin d) ℝ),
      if l = ⟨n + 1, hn⟩ then (1 : Matrix (Fin d) (Fin d) ℝ) else 0)
  refine mvPolynomial_ne_zero_of_eval_eq_one (paramFlat θ) ?_
  rw [eval_det_matrix θ (genKappaMatrix L d n)]
  have hvalues :
      ∀ k : Nat, k < n + 1 ->
        (paramStream θ k).1 = (1 : Matrix (Fin d) (Fin d) ℝ) := by
    intro k hk
    have hkL : k < L := Nat.lt_trans hk hn
    rw [paramStream_apply_of_lt θ hkL]
  have hV :
      realVprod (paramStream θ) (n + 1) = (1 : Matrix (Fin d) (Fin d) ℝ) :=
    realVprod_eq_one_of_value_eq_one_lt (paramStream θ) (n + 1) hvalues
  have hA : (paramStream θ (n + 1)).2 = (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [paramStream_apply_of_lt θ hn]
    simp [θ]
  have hkappa :
      kappaMatrix (paramStream θ) n = (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [kappaMatrix, hV, hA]
    simp
  have hmap :
      (genKappaMatrix L d n).map (MvPolynomial.eval (paramFlat θ)) =
        (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [map_genKappaMatrix, hkappa]
  rw [hmap]
  simp

/-! ## Base case -/

inductive TexGenericBaseIndex where
  | value
  | attention
  deriving DecidableEq

namespace TexGenericBaseIndex

instance : Fintype TexGenericBaseIndex where
  elems := {value, attention}
  complete := by
    intro a
    cases a <;> simp

end TexGenericBaseIndex

/-- Depth-one coordinate-polynomial package.  This necessarily assumes `d > 0`; for
`d = 0`, the exact base predicate asks the unique empty matrix to be nonzero. -/
noncomputable def texGenericPolynomialCover_base (d : Nat) (hd : 0 < d) :
    ParamPolynomialPredicateCover 1 d (fun θ => TexGeneric 1 d θ) where
  κ := TexGenericBaseIndex
  data :=
    { indices := Finset.univ
      poly := fun a =>
        let i0 : Fin d := ⟨0, hd⟩
        match a with
        | TexGenericBaseIndex.value => MvPolynomial.X ((0 : Fin 1), Sum.inl (i0, i0))
        | TexGenericBaseIndex.attention => MvPolynomial.X ((0 : Fin 1), Sum.inr (i0, i0))
      nonzero := by
        intro a ha
        dsimp
        cases a <;> exact MvPolynomial.X_ne_zero _ }
  carrier_subset := by
    intro θ hθ
    let i0 : Fin d := ⟨0, hd⟩
    refine ⟨?_, ?_⟩
    · intro hzero
      have hcoord :
          (MvPolynomial.eval (paramFlat θ))
              (MvPolynomial.X ((0 : Fin 1), Sum.inl (i0, i0))) ≠ 0 :=
        hθ TexGenericBaseIndex.value (Finset.mem_univ _)
      have hcoordzero : (paramStream θ 0).1 i0 i0 = 0 := by
        rw [hzero]
        rfl
      exact hcoord (by
        simpa [i0, paramStream_apply_of_lt] using hcoordzero)
    · intro hzero
      have hcoord :
          (MvPolynomial.eval (paramFlat θ))
              (MvPolynomial.X ((0 : Fin 1), Sum.inr (i0, i0))) ≠ 0 :=
        hθ TexGenericBaseIndex.attention (Finset.mem_univ _)
      have hcoordzero : (paramStream θ 0).2 i0 i0 = 0 := by
        rw [hzero]
        rfl
      exact hcoord (by
        simpa [i0, paramStream_apply_of_lt] using hcoordzero)

/-! ## Recursive matrix clauses `(G1)`--`(G3)` -/

inductive TexGenericStepMatrixIndex (L : Nat) where
  | detFirstAttention
  | symFirstAttention
  | kappa (n : Fin L)
  | visible
  | detFirstSkip
  deriving DecidableEq

namespace TexGenericStepMatrixIndex

instance (L : Nat) : Fintype (TexGenericStepMatrixIndex L) where
  elems :=
    {detFirstAttention, symFirstAttention, visible, detFirstSkip} ∪
      (Finset.univ.map
        ⟨fun n : Fin L => TexGenericStepMatrixIndex.kappa n, by
          intro a b h
          cases h
          rfl⟩)
  complete := by
    intro a
    cases a with
    | detFirstAttention => simp
    | symFirstAttention => simp
    | visible => simp
    | detFirstSkip => simp
    | kappa n =>
        simp

end TexGenericStepMatrixIndex

/-- The matrix part of a recursive TeX step, excluding the tail and `(G4)`. -/
def TexGenericStepMatrixPredicate (L d : Nat) (θ : Params (L + 1) d) : Prop :=
  (firstAttention θ).det ≠ 0 ∧
  symPart (firstAttention θ) ≠ 0 ∧
  (∀ j : Nat, 2 ≤ j -> j ≤ L + 1 ->
    kappaMatrix (paramStream θ) (j - 2) ≠ 0) ∧
  realVprod (paramStream θ) (L + 1) ≠ 0 ∧
  (skipB (paramStream θ 0).1).det ≠ 0

/-- Finite determinant/coordinate package for `(G1)`--`(G3)`. -/
noncomputable def texGenericPolynomialCover_stepMatrix (L d : Nat) (hd : 0 < d) :
    ParamPolynomialPredicateCover (L + 1) d
      (fun θ => TexGenericStepMatrixPredicate L d θ) where
  κ := TexGenericStepMatrixIndex L
  data :=
    { indices := Finset.univ
      poly := fun a =>
        let i0 : Fin d := ⟨0, hd⟩
        match a with
        | TexGenericStepMatrixIndex.detFirstAttention =>
            (genAttentionAt (L + 1) d 0).det
        | TexGenericStepMatrixIndex.symFirstAttention =>
            MvPolynomial.X ((0 : Fin (L + 1)), Sum.inr (i0, i0))
        | TexGenericStepMatrixIndex.kappa n =>
            (genKappaMatrix (L + 1) d n.val).det
        | TexGenericStepMatrixIndex.visible =>
            (genRealVprod (L + 1) d (L + 1)).det
        | TexGenericStepMatrixIndex.detFirstSkip =>
            (genSkipB (genValueAt (L + 1) d 0)).det
      nonzero := by
        intro a ha
        dsimp
        cases a with
        | detFirstAttention =>
            exact texGenericPolynomialCover_det_genAttentionAt_ne_zero
              (L + 1) d 0 (Nat.succ_pos L)
        | symFirstAttention =>
            exact MvPolynomial.X_ne_zero _
        | kappa n =>
            exact texGenericPolynomialCover_det_genKappaMatrix_ne_zero
              (L + 1) d n.val (Nat.succ_lt_succ n.isLt)
        | visible =>
            exact texGenericPolynomialCover_det_genRealVprod_ne_zero
              (L + 1) d (L + 1) le_rfl
        | detFirstSkip =>
            exact texGenericPolynomialCover_det_genSkipB_ne_zero
              (L + 1) d 0 (Nat.succ_pos L) }
  carrier_subset := by
    intro θ hθ
    let i0 : Fin d := ⟨0, hd⟩
    constructor
    · have hdet :
          (MvPolynomial.eval (paramFlat θ)) (genAttentionAt (L + 1) d 0).det ≠ 0 :=
        hθ TexGenericStepMatrixIndex.detFirstAttention (Finset.mem_univ _)
      simpa [firstAttention, eval_det_matrix θ (genAttentionAt (L + 1) d 0)] using hdet
    constructor
    · intro hsym
      have hcoord :
          (MvPolynomial.eval (paramFlat θ))
              (MvPolynomial.X ((0 : Fin (L + 1)), Sum.inr (i0, i0))) ≠ 0 :=
        hθ TexGenericStepMatrixIndex.symFirstAttention (Finset.mem_univ _)
      have hentry : symPart (firstAttention θ) i0 i0 = 0 := by
        simp [hsym]
      have hdiag : symPart (firstAttention θ) i0 i0 = firstAttention θ i0 i0 := by
        simp [symPart, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      have hAzero : firstAttention θ i0 i0 = 0 := by
        rw [← hdiag, hentry]
      exact hcoord (by
        simpa [firstAttention, paramStream_apply_of_lt] using hAzero)
    constructor
    · intro j hj2 hjle
      have hnlt : j - 2 < L := by
        omega
      have hdet :
          (MvPolynomial.eval (paramFlat θ)) (genKappaMatrix (L + 1) d (j - 2)).det ≠ 0 :=
        hθ (TexGenericStepMatrixIndex.kappa ⟨j - 2, hnlt⟩) (Finset.mem_univ _)
      intro hzero
      have hdetzero : (kappaMatrix (paramStream θ) (j - 2)).det = 0 := by
        rw [hzero]
        exact Matrix.det_zero ⟨i0⟩
      exact hdet (by
        rw [eval_det_matrix θ (genKappaMatrix (L + 1) d (j - 2)),
          map_genKappaMatrix, hdetzero])
    constructor
    · have hdet :
          (MvPolynomial.eval (paramFlat θ)) (genRealVprod (L + 1) d (L + 1)).det ≠ 0 :=
        hθ TexGenericStepMatrixIndex.visible (Finset.mem_univ _)
      intro hzero
      have hdetzero : (realVprod (paramStream θ) (L + 1)).det = 0 := by
        rw [hzero]
        exact Matrix.det_zero ⟨i0⟩
      exact hdet (by
        rw [eval_det_matrix θ (genRealVprod (L + 1) d (L + 1)),
          map_genRealVprod, hdetzero])
    · have hdet :
          (MvPolynomial.eval (paramFlat θ)) (genSkipB (genValueAt (L + 1) d 0)).det ≠ 0 :=
        hθ TexGenericStepMatrixIndex.detFirstSkip (Finset.mem_univ _)
      simpa [eval_det_matrix θ (genSkipB (genValueAt (L + 1) d 0)),
        map_genSkipB, map_genValueAt] using hdet

/-! ## `(G4)` certificate package -/

/-- TeX `(G4)` as a finite coordinate-polynomial package, obtained from the
coefficient-polynomial bridge in `TexAnchorCertificateTopology`. -/
theorem texGenericPolynomialCover_g4_exists
    (L d : Nat) (hd : 0 < d) (hrows : genericCertificateRows L ≤ d) :
    Nonempty (ParamPolynomialPredicateCover L d (fun θ => TexAnchorCertificate θ)) := by
  obtain ⟨κ, _hκ, _hκdec, D, hsubset⟩ :=
    texAnchorCertificate_exists_coefficient_polynomial_cover L d hd hrows
  exact ⟨
    { κ := κ
      data := D
      carrier_subset := by
        intro θ hθ
        exact hsubset hθ }⟩

/-! ## Recursive assembly -/

noncomputable def texGenericPolynomialCover_step {L d : Nat} (hd : 0 < d)
    (Ctail : ParamPolynomialPredicateCover L d (fun θ => TexGeneric L d θ))
    (Cg4 : ParamPolynomialPredicateCover (L + 1) d (fun θ => TexAnchorCertificate θ)) :
    ParamPolynomialPredicateCover (L + 1) d (fun θ =>
      TexGenericStepClauses L d (TexGeneric L d) (fun η => TexAnchorCertificate η) θ) :=
  let Ctail' := tailLift Ctail
  let Cmatrix := texGenericPolynomialCover_stepMatrix L d hd
  let Cboth := ParamPolynomialPredicateCover.and Ctail' Cmatrix
  let Call := ParamPolynomialPredicateCover.and Cboth Cg4
  { κ := Call.κ
    data := Call.data
    carrier_subset := by
      intro θ hθ
      rcases Call.carrier_subset hθ with ⟨⟨htail, hmatrix⟩, hg4⟩
      rcases hmatrix with ⟨hdetA, hsymA, hkappa, hvisible, hdetB⟩
      exact
        { tail_generic := htail
          g1_det_firstAttention := hdetA
          g1_sym_firstAttention := hsymA
          g2_kappa := hkappa
          g2_visible := hvisible
          g3_det_firstSkip := hdetB
          g4_certificate := hg4 } }

theorem texGenericPolynomialCover_exists_of_pos_d (d : Nat) (hd : 0 < d) :
    ∀ L : Nat, genericCertificateRows L ≤ d ->
      Nonempty (TexGenericPolynomialNonvanishingCover L d)
  | 0, _hrows =>
      ⟨(ParamPolynomialPredicateCover.trueCover 0 d).toTexGenericPolynomialNonvanishingCover⟩
  | 1, _hrows =>
      ⟨(texGenericPolynomialCover_base d hd).toTexGenericPolynomialNonvanishingCover⟩
  | L + 2, hrows =>
      by
        have htailRows : genericCertificateRows (L + 1) ≤ d :=
          (genericCertificateRows_mono_succ (L + 1)).trans hrows
        obtain ⟨CtailTex⟩ := texGenericPolynomialCover_exists_of_pos_d d hd
          (L + 1) htailRows
        let Ctail : ParamPolynomialPredicateCover (L + 1) d
            (fun θ => TexGeneric (L + 1) d θ) :=
          { κ := CtailTex.κ
            data := CtailTex.data
            carrier_subset := CtailTex.carrier_subset_texGeneric }
        obtain ⟨Cg4⟩ := texGenericPolynomialCover_g4_exists (L + 2) d hd hrows
        refine ⟨(texGenericPolynomialCover_step (L := L + 1) (d := d) hd Ctail
          Cg4).toTexGenericPolynomialNonvanishingCover⟩

/-- Concrete positive-dimensional cover existence. -/
theorem texGenericBadSet_exists_polynomialNonvanishingCover_concrete_of_pos_d
    (L d : Nat) (hd : 0 < d) (hrows : genericCertificateRows L ≤ d) :
    Nonempty (TexGenericPolynomialNonvanishingCover L d) :=
  texGenericPolynomialCover_exists_of_pos_d d hd L hrows

end TransformerIdentifiability.NLayer
