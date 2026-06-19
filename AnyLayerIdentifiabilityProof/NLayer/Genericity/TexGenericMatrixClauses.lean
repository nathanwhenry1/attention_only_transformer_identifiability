import AnyLayerIdentifiabilityProof.NLayer.Genericity.TexGenericOpenDense
import AnyLayerIdentifiabilityProof.NLayer.Foundations.ParamPolynomialGenericity
import AnyLayerIdentifiabilityProof.NLayer.Foundations.PolynomialGenericity
import AnyLayerIdentifiabilityProof.NLayer.Genericity.TexGenericPolynomialCover

set_option autoImplicit false

open MvPolynomial

namespace TransformerIdentifiability.NLayer

/-!
# Concrete topology for the TeX matrix clauses

This shard isolates the `(G1)`--`(G3)` matrix-clause topology work from the recursive
genericity assembly and from the anchor-certificate `(G4)` obligation.
-/

/-! ## Flattened-coordinate topology -/

/-- Inverse to `paramFlat`, used only as a topological coordinate chart. -/
noncomputable def texGenericMatrixClause_paramUnflat {L d : Nat}
    (x : ParamCoord L d -> ℝ) : Params L d :=
  fun l =>
    (Matrix.of fun i j => x (l, Sum.inl (i, j)),
      Matrix.of fun i j => x (l, Sum.inr (i, j)))

@[simp]
theorem texGenericMatrixClause_paramUnflat_value {L d : Nat}
    (x : ParamCoord L d -> ℝ) (l : Fin L) (i j : Fin d) :
    (texGenericMatrixClause_paramUnflat x l).1 i j = x (l, Sum.inl (i, j)) :=
  rfl

@[simp]
theorem texGenericMatrixClause_paramUnflat_attention {L d : Nat}
    (x : ParamCoord L d -> ℝ) (l : Fin L) (i j : Fin d) :
    (texGenericMatrixClause_paramUnflat x l).2 i j = x (l, Sum.inr (i, j)) :=
  rfl

/-- Flattening parameters to coordinates is a homeomorphism. -/
noncomputable def texGenericMatrixClause_paramFlatHomeomorph (L d : Nat) :
    Params L d ≃ₜ (ParamCoord L d -> ℝ) where
  toFun := paramFlat
  invFun := texGenericMatrixClause_paramUnflat
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
    refine continuous_pi ?_
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
    refine continuous_pi ?_
    intro l
    refine (continuous_pi ?_).prodMk (continuous_pi ?_)
    · intro i
      refine continuous_pi ?_
      intro j
      exact continuous_apply (l, Sum.inl (i, j))
    · intro i
      refine continuous_pi ?_
      intro j
      exact continuous_apply (l, Sum.inr (i, j))

/-- A nonzero coordinate polynomial has dense nonvanishing pullback to parameter space. -/
theorem texGenericMatrixClause_dense_param_eval_ne_zero {L d : Nat}
    (p : ParamRing L d) (hp : p ≠ 0) :
    Dense {θ : Params L d | (MvPolynomial.eval (paramFlat θ)) p ≠ 0} := by
  simpa using
    (dense_compl_zero_set p hp).preimage
      (texGenericMatrixClause_paramFlatHomeomorph L d).isOpenMap

/-- A coordinate-polynomial nonvanishing pullback is open in parameter space. -/
theorem texGenericMatrixClause_isOpen_param_eval_ne_zero {L d : Nat}
    (p : ParamRing L d) :
    IsOpen {θ : Params L d | (MvPolynomial.eval (paramFlat θ)) p ≠ 0} := by
  simpa using
    (isOpen_eval_ne_zero p).preimage
      (texGenericMatrixClause_paramFlatHomeomorph L d).continuous

/-! ## Basic continuity helpers -/

theorem texGenericMatrixClause_continuous_firstValue {L d : Nat} (hL : 0 < L) :
    Continuous (fun θ : Params L d => (paramStream θ 0).1) := by
  have hfun :
      (fun θ : Params L d => (paramStream θ 0).1) =
        fun θ : Params L d => (θ ⟨0, hL⟩).1 := by
    funext θ
    simp [paramStream, hL]
  rw [hfun]
  exact
    (continuous_fst : Continuous fun p :
        Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ => p.1).comp
      (continuous_apply (⟨0, hL⟩ : Fin L))

theorem texGenericMatrixClause_continuous_firstAttention {L d : Nat} (hL : 0 < L) :
    Continuous (fun θ : Params L d => firstAttention θ) := by
  have hfun :
      (fun θ : Params L d => firstAttention θ) =
        fun θ : Params L d => (θ ⟨0, hL⟩).2 := by
    funext θ
    simp [firstAttention, paramStream, hL]
  rw [hfun]
  exact
    (continuous_snd : Continuous fun p :
        Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ => p.2).comp
      (continuous_apply (⟨0, hL⟩ : Fin L))

theorem texGenericMatrixClause_isOpen_matrix_ne_zero {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y] [Zero Y]
    {f : X -> Y} (hf : Continuous f) :
    IsOpen {x : X | f x ≠ 0} := by
  change IsOpen (f ⁻¹' ({0}ᶜ : Set Y))
  exact
    (isClosed_singleton : IsClosed ({0} : Set Y)).isOpen_compl.preimage hf

theorem texGenericMatrixClause_continuous_paramStream_value {L d n : Nat} :
    Continuous (fun θ : Params L d => (paramStream θ n).1) := by
  by_cases hn : n < L
  · have hfun :
        (fun θ : Params L d => (paramStream θ n).1) =
          fun θ : Params L d => (θ ⟨n, hn⟩).1 := by
      funext θ
      simp [paramStream, hn]
    rw [hfun]
    exact
      (continuous_fst : Continuous fun p :
          Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ => p.1).comp
        (continuous_apply (⟨n, hn⟩ : Fin L))
  · have hfun :
        (fun θ : Params L d => (paramStream θ n).1) =
          fun _ : Params L d => (0 : Matrix (Fin d) (Fin d) ℝ) := by
      funext θ
      simp [paramStream, hn]
    rw [hfun]
    exact continuous_const

theorem texGenericMatrixClause_continuous_paramStream_attention {L d n : Nat} :
    Continuous (fun θ : Params L d => (paramStream θ n).2) := by
  by_cases hn : n < L
  · have hfun :
        (fun θ : Params L d => (paramStream θ n).2) =
          fun θ : Params L d => (θ ⟨n, hn⟩).2 := by
      funext θ
      simp [paramStream, hn]
    rw [hfun]
    exact
      (continuous_snd : Continuous fun p :
          Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ => p.2).comp
        (continuous_apply (⟨n, hn⟩ : Fin L))
  · have hfun :
        (fun θ : Params L d => (paramStream θ n).2) =
          fun _ : Params L d => (0 : Matrix (Fin d) (Fin d) ℝ) := by
      funext θ
      simp [paramStream, hn]
    rw [hfun]
    exact continuous_const

/-! ## Base clauses -/

theorem texGenericMatrixClause_base_open (d : Nat) :
    IsOpen (TexGenericBaseSet d) := by
  have hV :
      IsOpen {θ : Params 1 d | (paramStream θ 0).1 ≠ 0} :=
    texGenericMatrixClause_isOpen_matrix_ne_zero
      (texGenericMatrixClause_continuous_firstValue (L := 1) (d := d) (by norm_num))
  have hA :
      IsOpen {θ : Params 1 d | (paramStream θ 0).2 ≠ 0} :=
    texGenericMatrixClause_isOpen_matrix_ne_zero
      (texGenericMatrixClause_continuous_firstAttention (L := 1) (d := d) (by norm_num))
  have hset :
      TexGenericBaseSet d =
        {θ : Params 1 d | (paramStream θ 0).1 ≠ 0} ∩
          {θ : Params 1 d | (paramStream θ 0).2 ≠ 0} := by
    ext θ
    constructor
    · intro hθ
      exact ⟨hθ.value_ne_zero, hθ.attention_ne_zero⟩
    · rintro ⟨hVθ, hAθ⟩
      exact ⟨hVθ, hAθ⟩
  rw [hset]
  exact hV.inter hA

theorem texGenericMatrixClause_base_dense (d : Nat) (hd : 0 < d) :
    Dense (TexGenericBaseSet d) := by
  let i : Fin d := ⟨0, hd⟩
  let pV : ParamRing 1 d := MvPolynomial.X ((0 : Fin 1), Sum.inl (i, i))
  let pA : ParamRing 1 d := MvPolynomial.X ((0 : Fin 1), Sum.inr (i, i))
  let SV : Set (Params 1 d) := {θ | (MvPolynomial.eval (paramFlat θ)) pV ≠ 0}
  let SA : Set (Params 1 d) := {θ | (MvPolynomial.eval (paramFlat θ)) pA ≠ 0}
  have hSVopen : IsOpen SV :=
    texGenericMatrixClause_isOpen_param_eval_ne_zero pV
  have hSVdense : Dense SV :=
    texGenericMatrixClause_dense_param_eval_ne_zero pV (MvPolynomial.X_ne_zero _)
  have hSAdense : Dense SA :=
    texGenericMatrixClause_dense_param_eval_ne_zero pA (MvPolynomial.X_ne_zero _)
  have hSdense : Dense (SV ∩ SA) :=
    hSVdense.inter_of_isOpen_left hSAdense hSVopen
  refine hSdense.mono ?_
  intro θ hθ
  constructor
  · intro hzero
    have hentry : (θ 0).1 i i = 0 := by
      have hmatrix : (θ 0).1 = 0 := by
        simpa [paramStream] using hzero
      rw [hmatrix]
      rfl
    exact hθ.1 (by simpa [SV, pV] using hentry)
  · intro hzero
    have hentry : (θ 0).2 i i = 0 := by
      have hmatrix : (θ 0).2 = 0 := by
        simpa [paramStream] using hzero
      rw [hmatrix]
      rfl
    exact hθ.2 (by simpa [SA, pA] using hentry)

/-! ## Step clauses -/

/-- Continuity of the product of value matrices in flattened parameter coordinates.

This is the first cross-shard algebra/topology bridge needed for the exact `(G2)`
visible-tail clause. -/
theorem texGenericMatrixClause_continuous_realVprod_paramStream {L d n : Nat} :
    Continuous (fun θ : Params L d => realVprod (paramStream θ) n) := by
  induction n with
  | zero =>
      simpa [realVprod] using
        (continuous_const :
          Continuous fun _ : Params L d => (1 : Matrix (Fin d) (Fin d) ℝ))
  | succ n ih =>
      simpa [realVprod] using
        (texGenericMatrixClause_continuous_paramStream_value (L := L) (d := d) (n := n)).matrix_mul
          ih

/-- Continuity of the TeX `kappa` matrix in flattened parameter coordinates.

This is the corresponding bridge for the exact `(G2)` kappa clauses. -/
theorem texGenericMatrixClause_continuous_kappaMatrix_paramStream {L d n : Nat} :
    Continuous (fun θ : Params L d => kappaMatrix (paramStream θ) n) := by
  have hV :
      Continuous (fun θ : Params L d => realVprod (paramStream θ) (n + 1)) :=
    texGenericMatrixClause_continuous_realVprod_paramStream (L := L) (d := d) (n := n + 1)
  have hA :
      Continuous (fun θ : Params L d => (paramStream θ (n + 1)).2) :=
    texGenericMatrixClause_continuous_paramStream_attention (L := L) (d := d) (n := n + 1)
  have hCore :
      Continuous
        (fun θ : Params L d =>
          Matrix.transpose (realVprod (paramStream θ) (n + 1)) *
            (paramStream θ (n + 1)).2 *
              realVprod (paramStream θ) (n + 1)) :=
    (hV.matrix_transpose.matrix_mul hA).matrix_mul hV
  simpa [kappaMatrix, symPart] using
    (hCore.add hCore.matrix_transpose).const_smul (1 / 2 : ℝ)

theorem texGenericMatrixClause_step_open (L d : Nat) :
    IsOpen (TexGenericStepMatrixSet L d) := by
  let Sdet : Set (Params (L + 1) d) :=
    {θ | (firstAttention θ).det ≠ 0}
  let Ssym : Set (Params (L + 1) d) :=
    {θ | symPart (firstAttention θ) ≠ 0}
  let Skappa : Set (Params (L + 1) d) :=
    {θ | ∀ j : Nat, 2 ≤ j -> j ≤ L + 1 ->
      kappaMatrix (paramStream θ) (j - 2) ≠ 0}
  let Svisible : Set (Params (L + 1) d) :=
    {θ | realVprod (paramStream θ) (L + 1) ≠ 0}
  let Sskip : Set (Params (L + 1) d) :=
    {θ | (skipB (paramStream θ 0).1).det ≠ 0}
  have hA :
      Continuous (fun θ : Params (L + 1) d => firstAttention θ) :=
    texGenericMatrixClause_continuous_firstAttention (L := L + 1) (d := d) (Nat.succ_pos L)
  have hdet : IsOpen Sdet := by
    exact texGenericMatrixClause_isOpen_matrix_ne_zero hA.matrix_det
  have hsymCont :
      Continuous (fun θ : Params (L + 1) d => symPart (firstAttention θ)) := by
    simpa [symPart] using (hA.add hA.matrix_transpose).const_smul (1 / 2 : ℝ)
  have hsym : IsOpen Ssym :=
    texGenericMatrixClause_isOpen_matrix_ne_zero hsymCont
  have hkappa : IsOpen Skappa := by
    let Kset : Nat -> Set (Params (L + 1) d) :=
      fun j => {θ | kappaMatrix (paramStream θ) (j - 2) ≠ 0}
    have hfin : IsOpen (⋂ j ∈ Finset.Icc 2 (L + 1), Kset j) :=
      isOpen_biInter_finset fun j _hj =>
        texGenericMatrixClause_isOpen_matrix_ne_zero
          (texGenericMatrixClause_continuous_kappaMatrix_paramStream
            (L := L + 1) (d := d) (n := j - 2))
    have hset : Skappa = ⋂ j ∈ Finset.Icc 2 (L + 1), Kset j := by
      ext θ
      simp [Skappa, Kset, Finset.mem_Icc]
    rw [hset]
    exact hfin
  have hvisible : IsOpen Svisible :=
    texGenericMatrixClause_isOpen_matrix_ne_zero
      (texGenericMatrixClause_continuous_realVprod_paramStream
        (L := L + 1) (d := d) (n := L + 1))
  have hV :
      Continuous (fun θ : Params (L + 1) d => (paramStream θ 0).1) :=
    texGenericMatrixClause_continuous_paramStream_value (L := L + 1) (d := d) (n := 0)
  have hskipCont :
      Continuous (fun θ : Params (L + 1) d => skipB (paramStream θ 0).1) := by
    simpa [skipB] using (continuous_const.add hV)
  have hskip : IsOpen Sskip :=
    texGenericMatrixClause_isOpen_matrix_ne_zero hskipCont.matrix_det
  have hset :
      TexGenericStepMatrixSet L d =
        (((Sdet ∩ Ssym) ∩ Skappa) ∩ Svisible) ∩ Sskip := by
    ext θ
    constructor
    · intro hθ
      exact
        ⟨⟨⟨⟨hθ.g1_det_firstAttention, hθ.g1_sym_firstAttention⟩, hθ.g2_kappa⟩,
          hθ.g2_visible⟩, hθ.g3_det_firstSkip⟩
    · rintro ⟨⟨⟨⟨hdetθ, hsymθ⟩, hkappaθ⟩, hvisibleθ⟩, hskipθ⟩
      exact
        { tail_generic := trivial
          g1_det_firstAttention := hdetθ
          g1_sym_firstAttention := hsymθ
          g2_kappa := hkappaθ
          g2_visible := hvisibleθ
          g3_det_firstSkip := hskipθ
          g4_certificate := trivial }
  rw [hset]
  exact ((((hdet.inter hsym).inter hkappa).inter hvisible).inter hskip)

/-- Polynomial nonvanishing witness sufficient for density of the exact step matrix
clauses `(G1)`--`(G3)`.

The intended concrete witness uses finitely many nonzero coordinate polynomials over
`ParamRing (L + 1) d`: determinant of the first attention matrix, a diagonal coordinate
of its symmetric part, determinant of `skipB V_0`, one visible-tail product coordinate,
and one coordinate for each `kappaMatrix` in the finite range.
-/
structure TexGenericMatrixClausePolynomialCore (L d : Nat) where
  Index : Type
  fintypeIndex : Fintype Index
  decidableEqIndex : DecidableEq Index
  data : PolynomialNonvanishingData (ParamCoord (L + 1) d) Index
  carrier_subset :
    paramNonvanishingCarrier data ⊆ TexGenericStepMatrixSet L d

/-- Polynomial witness for the step matrix clauses, reusing the finite cover for
`TexGenericStepMatrixPredicate` and repackaging it for `TexGenericStepMatrixSet`.
-/
noncomputable def texGenericMatrixClause_step_polynomial_core (L d : Nat) (hd : 0 < d) :
    TexGenericMatrixClausePolynomialCore L d :=
  let C := texGenericPolynomialCover_stepMatrix L d hd
  { Index := TexGenericStepMatrixIndex L
    fintypeIndex := inferInstance
    decidableEqIndex := inferInstance
    data := C.data
    carrier_subset := by
      intro θ hθ
      rcases C.carrier_subset hθ with ⟨hdetA, hsymA, hkappa, hvisible, hdetB⟩
      exact
        { tail_generic := trivial
          g1_det_firstAttention := hdetA
          g1_sym_firstAttention := hsymA
          g2_kappa := hkappa
          g2_visible := hvisible
          g3_det_firstSkip := hdetB
          g4_certificate := trivial } }

/-- Density of the exact step matrix clauses from the polynomial nonvanishing witness. -/
theorem texGenericMatrixClause_step_dense_algebraic (L d : Nat) (hd : 0 < d) :
    Dense (TexGenericStepMatrixSet L d) := by
  classical
  let W := texGenericMatrixClause_step_polynomial_core L d hd
  letI := W.fintypeIndex
  letI := W.decidableEqIndex
  have hcarrier : Dense W.data.carrier :=
    W.data.dense_carrier
  have hparam : Dense (paramNonvanishingCarrier W.data) := by
    simpa [paramNonvanishingCarrier] using
      hcarrier.preimage
        (texGenericMatrixClause_paramFlatHomeomorph (L + 1) d).isOpenMap
  exact hparam.mono W.carrier_subset

/-- Concrete matrix-clause topology obligations for `(G1)`--`(G3)`, excluding `(G4)`. -/
theorem texGenericMatrixClauseTopologyObligations_concrete :
    TexGenericMatrixClauseTopologyObligations where
  base_open := texGenericMatrixClause_base_open
  step_open := texGenericMatrixClause_step_open
  base_dense := texGenericMatrixClause_base_dense
  step_dense := texGenericMatrixClause_step_dense_algebraic

end TransformerIdentifiability.NLayer
