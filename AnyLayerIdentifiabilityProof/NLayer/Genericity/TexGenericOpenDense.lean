import AnyLayerIdentifiabilityProof.NLayer.Genericity.GenericityMain
import AnyLayerIdentifiabilityProof.NLayer.Foundations.ParamPolynomialGenericity
import AnyLayerIdentifiabilityProof.NLayer.Foundations.PolynomialGenericity

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Open/dense assembly for exact TeX genericity

This shard keeps the recursive topology argument separate from the algebraic
coefficient-polynomial work needed for the concrete TeX clauses.

The exact all-`Nat` density statement
`Dense (TexGenericSet L d)` is not true as stated: when `d = 0`, the depth-one base
condition requires nonzero `0 x 0` matrices.  The dense interface below therefore carries
the natural positive-dimension hypothesis.
-/

/-- The exact TeX anchor-certificate locus. -/
def TexAnchorCertificateSet (L d : Nat) : Set (Params L d) :=
  {θ | TexAnchorCertificate θ}

/-- The depth-one TeX genericity locus, isolated as a set. -/
def TexGenericBaseSet (d : Nat) : Set (Params 1 d) :=
  {θ | TexGenericBaseClauses d θ}

/-- The nonrecursive matrix clauses in a TeX step, with tail genericity and the
anchor-certificate predicate replaced by `True`.

For `L`, this is a subset of `Params (L + 1) d`; it packages `(G1)`, `(G2)`, and `(G3)`.
-/
def TexGenericStepMatrixSet (L d : Nat) : Set (Params (L + 1) d) :=
  {θ | TexGenericStepClauses L d (fun _ => True) (fun _ => True) θ}

/-- Matrix-clause topology obligations that should eventually be discharged by explicit
finite polynomial nonvanishing data.  Density is stated only for positive dimension,
because the base locus is empty when `d = 0`. -/
structure TexGenericMatrixClauseTopologyObligations : Prop where
  base_open : ∀ d : Nat, IsOpen (TexGenericBaseSet d)
  step_open : ∀ L d : Nat, IsOpen (TexGenericStepMatrixSet L d)
  base_dense : ∀ d : Nat, 0 < d -> Dense (TexGenericBaseSet d)
  step_dense : ∀ L d : Nat, 0 < d -> Dense (TexGenericStepMatrixSet L d)

/-- Anchor-certificate topology obligations.  This is the place where the current
`TexAnchorCertificate` representation must be connected to an explicit nonzero
coefficient polynomial, or otherwise proved open and dense under the intrinsic
certificate-row dimension bound. -/
structure TexAnchorCertificateTopologyObligations : Prop where
  isOpen : ∀ L d : Nat, IsOpen (TexAnchorCertificateSet L d)
  dense : ∀ L d : Nat, 0 < d -> genericCertificateRows L ≤ d ->
    Dense (TexAnchorCertificateSet L d)

/-- Split a positive-depth parameter tuple into its first layer and tail. -/
noncomputable def paramsHeadTailHomeomorph (L d : Nat) :
    Params (L + 1) d ≃ₜ Layer d × Params L d where
  toFun θ := (θ 0, Fin.tail θ)
  invFun p := Fin.cons p.1 p.2
  left_inv θ := Fin.cons_self_tail θ
  right_inv p := by
    ext <;> simp
  continuous_toFun := by
    exact (continuous_apply (0 : Fin (L + 1))).prodMk (Continuous.finTail continuous_id)
  continuous_invFun := by
    refine continuous_pi ?_
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa using (continuous_fst : Continuous fun p : Layer d × Params L d => p.1)
    · intro j
      change Continuous (fun p : Layer d × Params L d => p.2 j)
      exact
        (continuous_apply j).comp
          (continuous_snd : Continuous fun p : Layer d × Params L d => p.2)

/-- The parameter tail projection is an open map. -/
theorem isOpenMap_params_tail (L d : Nat) :
    IsOpenMap (fun θ : Params (L + 1) d => Fin.tail θ) := by
  have h :
      IsOpenMap
        (Prod.snd ∘ (paramsHeadTailHomeomorph L d :
          Params (L + 1) d ≃ₜ Layer d × Params L d)) :=
    isOpenMap_snd.comp (paramsHeadTailHomeomorph L d).isOpenMap
  simpa [Function.comp_def, paramsHeadTailHomeomorph] using h

/-- The exact successor-step membership split into tail, matrix, and certificate pieces. -/
theorem mem_TexGenericSet_succ_succ {L d : Nat} {θ : Params (L + 2) d} :
    θ ∈ TexGenericSet (L + 2) d ↔
      Fin.tail θ ∈ TexGenericSet (L + 1) d ∧
        θ ∈ TexGenericStepMatrixSet (L + 1) d ∧
          θ ∈ TexAnchorCertificateSet (L + 2) d := by
  constructor
  · intro hθ
    change
      TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
        (fun η => TexAnchorCertificate η) θ at hθ
    refine ⟨hθ.tail_generic, ?_, hθ.g4_certificate⟩
    exact
      { tail_generic := trivial
        g1_det_firstAttention := hθ.g1_det_firstAttention
        g1_sym_firstAttention := hθ.g1_sym_firstAttention
        g2_kappa := hθ.g2_kappa
        g2_visible := hθ.g2_visible
        g3_det_firstSkip := hθ.g3_det_firstSkip
        g4_certificate := trivial }
  · rintro ⟨htail, hmatrix, hcert⟩
    change
      TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
        (fun η => TexAnchorCertificate η) θ
    exact
      { tail_generic := htail
        g1_det_firstAttention := hmatrix.g1_det_firstAttention
        g1_sym_firstAttention := hmatrix.g1_sym_firstAttention
        g2_kappa := hmatrix.g2_kappa
        g2_visible := hmatrix.g2_visible
        g3_det_firstSkip := hmatrix.g3_det_firstSkip
        g4_certificate := hcert }

/-- Set-level version of `mem_TexGenericSet_succ_succ`. -/
theorem TexGenericSet_succ_succ_eq (L d : Nat) :
    TexGenericSet (L + 2) d =
      (((fun θ : Params (L + 2) d => Fin.tail θ) ⁻¹' TexGenericSet (L + 1) d) ∩
        TexGenericStepMatrixSet (L + 1) d) ∩
          TexAnchorCertificateSet (L + 2) d := by
  ext θ
  constructor
  · intro hθ
    exact ⟨⟨(mem_TexGenericSet_succ_succ.mp hθ).1,
      (mem_TexGenericSet_succ_succ.mp hθ).2.1⟩,
      (mem_TexGenericSet_succ_succ.mp hθ).2.2⟩
  · rintro ⟨⟨htail, hmatrix⟩, hcert⟩
    exact mem_TexGenericSet_succ_succ.mpr ⟨htail, hmatrix, hcert⟩

/-- Open recursive TeX genericity from open matrix and certificate clause obligations. -/
theorem isOpen_TexGenericSet_of_texAnchorCertificate_open_dense
    (hmatrix : TexGenericMatrixClauseTopologyObligations)
    (hcert : TexAnchorCertificateTopologyObligations) :
    ∀ L d : Nat, IsOpen (TexGenericSet L d)
  | 0, d => by
      simp [TexGenericSet, TexGeneric]
  | 1, d => by
      simpa [TexGenericSet, TexGenericBaseSet] using hmatrix.base_open d
  | L + 2, d => by
      have htail :
          IsOpen (((fun θ : Params (L + 2) d => Fin.tail θ) ⁻¹'
            TexGenericSet (L + 1) d)) :=
        (isOpen_TexGenericSet_of_texAnchorCertificate_open_dense hmatrix hcert
          (L + 1) d).preimage (Continuous.finTail continuous_id)
      have hstep : IsOpen (TexGenericStepMatrixSet (L + 1) d) :=
        hmatrix.step_open (L + 1) d
      have hcertificate : IsOpen (TexAnchorCertificateSet (L + 2) d) :=
        hcert.isOpen (L + 2) d
      rw [TexGenericSet_succ_succ_eq L d]
      exact (htail.inter hstep).inter hcertificate

/-- Dense recursive TeX genericity in positive dimension and under the certificate-row
dimension bound. -/
theorem dense_TexGenericSet_of_texAnchorCertificate_open_dense
    (hmatrix : TexGenericMatrixClauseTopologyObligations)
    (hcert : TexAnchorCertificateTopologyObligations) :
    ∀ L d : Nat, 0 < d -> genericCertificateRows L ≤ d -> Dense (TexGenericSet L d)
  | 0, d, _hd, _hrows => by
      simp [TexGenericSet, TexGeneric]
  | 1, d, hd, _hrows => by
      simpa [TexGenericSet, TexGenericBaseSet] using hmatrix.base_dense d hd
  | L + 2, d, hd, hrows => by
      have htailRows : genericCertificateRows (L + 1) ≤ d :=
        (genericCertificateRows_mono_succ (L + 1)).trans hrows
      have htailOpen :
          IsOpen (((fun θ : Params (L + 2) d => Fin.tail θ) ⁻¹'
            TexGenericSet (L + 1) d)) :=
        (isOpen_TexGenericSet_of_texAnchorCertificate_open_dense hmatrix hcert
          (L + 1) d).preimage (Continuous.finTail continuous_id)
      have htailDense :
          Dense (((fun θ : Params (L + 2) d => Fin.tail θ) ⁻¹'
            TexGenericSet (L + 1) d)) :=
        (dense_TexGenericSet_of_texAnchorCertificate_open_dense hmatrix hcert
          (L + 1) d hd htailRows).preimage (isOpenMap_params_tail (L + 1) d)
      have hstepOpen : IsOpen (TexGenericStepMatrixSet (L + 1) d) :=
        hmatrix.step_open (L + 1) d
      have hstepDense : Dense (TexGenericStepMatrixSet (L + 1) d) :=
        hmatrix.step_dense (L + 1) d hd
      have hcertificateDense : Dense (TexAnchorCertificateSet (L + 2) d) :=
        hcert.dense (L + 2) d hd hrows
      have hmatrixTailDense :
          Dense ((((fun θ : Params (L + 2) d => Fin.tail θ) ⁻¹'
            TexGenericSet (L + 1) d) ∩ TexGenericStepMatrixSet (L + 1) d)) :=
        htailDense.inter_of_isOpen_left hstepDense htailOpen
      have hmatrixTailOpen :
          IsOpen ((((fun θ : Params (L + 2) d => Fin.tail θ) ⁻¹'
            TexGenericSet (L + 1) d) ∩ TexGenericStepMatrixSet (L + 1) d)) :=
        htailOpen.inter hstepOpen
      rw [TexGenericSet_succ_succ_eq L d]
      exact hmatrixTailDense.inter_of_isOpen_left hcertificateDense hmatrixTailOpen

/-- The exact target density statement without a positive-dimension hypothesis is false. -/
theorem TexGenericSet_one_zero_eq_empty : TexGenericSet 1 0 = ∅ := by
  ext θ
  constructor
  · intro hθ
    have hbase : TexGenericBaseClauses 0 θ := hθ
    have hzero : (paramStream θ 0).1 = 0 := by
      ext i j
      exact Fin.elim0 i
    exact False.elim (hbase.value_ne_zero hzero)
  · intro hθ
    exact False.elim hθ

/-- Consequently, `Dense (TexGenericSet 1 0)` cannot be exported. -/
theorem not_dense_TexGenericSet_one_zero : ¬ Dense (TexGenericSet 1 0) := by
  intro hdense
  have hmem := hdense (fun _ : Fin 1 => ((0 : Matrix (Fin 0) (Fin 0) ℝ), 0))
  rw [TexGenericSet_one_zero_eq_empty] at hmem
  simp at hmem

end TransformerIdentifiability.NLayer
