import AnyLayerIdentifiabilityProof.NLayer.IDL.IDLStatement
import AnyLayerIdentifiabilityProof.NLayer.Genericity.TexAnchorCertificateTopology

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

open Matrix

/-!
# Anchor existence from the TeX certificate

This file owns Proposition `anchorsexist`: `(G4)` plus the row bound produces an
unwound anchor.
-/

/-! ## Certificate evaluations and row targets -/

/-- A concrete nonzero certificate evaluation whose gate coordinates already lie in the
open box used by the unwinding lemma. -/
structure AnchorCertificateGoodEvaluation {L d : Nat} (θ : Params L d) where
  t : AnchorGateVector L
  s : AnchorGateVector L
  w0 : Fin d -> ℝ
  value_ne_zero : anchorCertificateValue θ t s w0 ≠ 0
  t_mem_Ioo : ∀ k : Fin (L - 1), t k ∈ Set.Ioo (0 : ℝ) 1
  s_mem_Ioo : ∀ k : Fin (L - 1), s k ∈ Set.Ioo (0 : ℝ) 1

/-- The `T_k(v)` row of the anchor certificate, written against the concrete transport
definitions used by `AnchorUnwindingData`. -/
noncomputable def anchorCertificateTValue {L d : Nat} (θ : Params L d)
    (t : AnchorGateVector L) (k : Fin (L - 1)) (w0 v : Fin d -> ℝ) : ℝ :=
  let τ := anchorGateStream t
  let p : AnchorProbe d := (w0, v)
  let pk := anchorPath (paramStream θ) k.val τ p
  let M := anchorStepMatrix (paramStream θ) k.val (t k)
  anchorCovectorAt (paramStream θ) k.val τ p ⬝ᵥ
    (M.adjugate.mulVec ((paramStream θ k.val).1.mulVec pk.1))

/-- The affine certificate-row evaluation at a candidate base vector `v`. -/
noncomputable def anchorCertificateRowValue {L d : Nat} (θ : Params L d)
    (t s : AnchorGateVector L) (w0 v : Fin d -> ℝ)
    (row : AnchorCertificateRow L) : ℝ :=
  match row with
  | Sum.inl (Sum.inl k) =>
      anchorSlopeAt (paramStream θ) k.val (anchorGateStream t) (w0, v)
  | Sum.inl (Sum.inr q) =>
      let k : Fin (L - 1) := q.1
      let ell : Nat := q.2.1.val
      anchorSlopeAt (paramStream θ) (k.val + ell - 1)
        (anchorUnwindGate (anchorGateStream t) (anchorGateStream s) k.val) (w0, v)
  | Sum.inr k =>
      anchorCertificateTValue θ t k w0 v

/-- Right-hand side of the affine row solve in Proposition `anchorsexist`. -/
def anchorCertificateTargetValue {L : Nat} : AnchorCertificateRow L -> ℝ
  | Sum.inl (Sum.inl _) => 0
  | Sum.inl (Sum.inr _) => 1
  | Sum.inr _ => 1

/-- The affine solve output: one vector `v` realizing all certificate-row target values. -/
structure AnchorCertificateAffineSolution {L d : Nat} {θ : Params L d}
    (D : AnchorCertificateGoodEvaluation θ) where
  v : Fin d -> ℝ
  row_value_eq_target :
    ∀ row : AnchorCertificateRow L,
      anchorCertificateRowValue θ D.t D.s D.w0 v row =
        anchorCertificateTargetValue row

namespace AnchorCertificateAffineSolution

theorem eRow_zero {L d : Nat} {θ : Params L d}
    {D : AnchorCertificateGoodEvaluation θ}
    (S : AnchorCertificateAffineSolution D) (k : Fin (L - 1)) :
    anchorCertificateRowValue θ D.t D.s D.w0 S.v (Sum.inl (Sum.inl k)) = 0 := by
  simpa [anchorCertificateTargetValue] using
    S.row_value_eq_target (Sum.inl (Sum.inl k))

theorem sRow_one {L d : Nat} {θ : Params L d}
    {D : AnchorCertificateGoodEvaluation θ}
    (S : AnchorCertificateAffineSolution D) (q : AnchorCertificateSIndex L) :
    anchorCertificateRowValue θ D.t D.s D.w0 S.v (Sum.inl (Sum.inr q)) = 1 := by
  simpa [anchorCertificateTargetValue] using
    S.row_value_eq_target (Sum.inl (Sum.inr q))

theorem tRow_one {L d : Nat} {θ : Params L d}
    {D : AnchorCertificateGoodEvaluation θ}
    (S : AnchorCertificateAffineSolution D) (k : Fin (L - 1)) :
    anchorCertificateRowValue θ D.t D.s D.w0 S.v (Sum.inr k) = 1 := by
  simpa [anchorCertificateTargetValue] using
    S.row_value_eq_target (Sum.inr k)

end AnchorCertificateAffineSolution

/-- Nonzero factors obtained by unpacking a good certificate evaluation. -/
structure AnchorCertificateGoodFactors {L d : Nat} {θ : Params L d}
    (D : AnchorCertificateGoodEvaluation θ) : Prop where
  gram_det_ne_zero :
    ((Matrix.transpose (anchorCertificateGradientMatrix θ D.t D.s D.w0) *
        anchorCertificateGradientMatrix θ D.t D.s D.w0) :
      Matrix (AnchorCertificateRow L) (AnchorCertificateRow L) ℝ).det ≠ 0
  det_step_ne_zero :
    ∀ k : Fin (L - 1), (anchorStepMatrix (paramStream θ) k.val (D.t k)).det ≠ 0
  attention_image_ne_zero :
    ∀ k : Fin (L - 1),
      (Matrix.transpose (paramStream θ k.val).2).mulVec
          (anchorCertificateW θ D.t k.val D.w0) ≠ 0

/-- The auxiliary certificate gate box. -/
def texAnchorCertificateAuxBox (L d : Nat) : Set (TexAnchorCertificateAuxCoord L d -> ℝ) :=
  {y |
    (∀ k : Fin (L - 1), y (Sum.inl (Sum.inl k)) ∈ Set.Ioo (0 : ℝ) 1) ∧
    (∀ k : Fin (L - 1), y (Sum.inl (Sum.inr k)) ∈ Set.Ioo (0 : ℝ) 1)}

theorem isOpen_texAnchorCertificateAuxBox (L d : Nat) :
    IsOpen (texAnchorCertificateAuxBox L d) := by
  dsimp [texAnchorCertificateAuxBox]
  have ht : IsOpen {y : TexAnchorCertificateAuxCoord L d -> ℝ |
      ∀ k : Fin (L - 1), y (Sum.inl (Sum.inl k)) ∈ Set.Ioo (0 : ℝ) 1} := by
    have hset :
        {y : TexAnchorCertificateAuxCoord L d -> ℝ |
          ∀ k : Fin (L - 1), y (Sum.inl (Sum.inl k)) ∈ Set.Ioo (0 : ℝ) 1} =
          ⋂ k : Fin (L - 1), {y : TexAnchorCertificateAuxCoord L d -> ℝ |
            y (Sum.inl (Sum.inl k)) ∈ Set.Ioo (0 : ℝ) 1} := by
      ext y
      simp
    rw [hset]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_Ioo.preimage (continuous_apply (Sum.inl (Sum.inl k)))
  have hs : IsOpen {y : TexAnchorCertificateAuxCoord L d -> ℝ |
      ∀ k : Fin (L - 1), y (Sum.inl (Sum.inr k)) ∈ Set.Ioo (0 : ℝ) 1} := by
    have hset :
        {y : TexAnchorCertificateAuxCoord L d -> ℝ |
          ∀ k : Fin (L - 1), y (Sum.inl (Sum.inr k)) ∈ Set.Ioo (0 : ℝ) 1} =
          ⋂ k : Fin (L - 1), {y : TexAnchorCertificateAuxCoord L d -> ℝ |
            y (Sum.inl (Sum.inr k)) ∈ Set.Ioo (0 : ℝ) 1} := by
      ext y
      simp
    rw [hset]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_Ioo.preimage (continuous_apply (Sum.inl (Sum.inr k)))
  simpa [Set.setOf_and] using ht.inter hs

theorem texAnchorCertificateAuxBox_nonempty (L d : Nat) :
    (texAnchorCertificateAuxBox L d).Nonempty := by
  refine ⟨fun _ => (1 / 2 : ℝ), ?_⟩
  constructor <;> intro k <;> constructor <;> norm_num

/-- A TeX certificate has a nonzero concrete evaluation with all gate coordinates in
`(0,1)`.  This is the formalized `(F1)` Zariski/open-box step. -/
theorem exists_goodEvaluation_of_texAnchorCertificate
    {L d : Nat} {θ : Params L d}
    (hcert : TexAnchorCertificate θ) :
    Nonempty (AnchorCertificateGoodEvaluation θ) := by
  classical
  rcases hcert with ⟨t0, s0, w00, hval0⟩
  let pθ : MvPolynomial (TexAnchorCertificateAuxCoord L d) ℝ :=
    MvPolynomial.map (MvPolynomial.eval (paramFlat θ))
      (texAnchorCertificate_auxPolynomial L d)
  have hpθ : pθ ≠ 0 := by
    intro hpzero
    let y0 : TexAnchorCertificateAuxCoord L d -> ℝ :=
      texAnchorCertificate_auxEval t0 s0 w00
    have hcombined :
        Sum.elim y0 (paramFlat θ) =
          texAnchorCertificate_combinedEval θ t0 s0 w00 := by
      funext z
      cases z <;> rfl
    have hpoly :
        (MvPolynomial.eval y0) pθ = anchorCertificateValue θ t0 s0 w00 := by
      change
        (MvPolynomial.eval y0)
            (MvPolynomial.map (MvPolynomial.eval (paramFlat θ))
              (texAnchorCertificate_auxPolynomial L d)) =
          anchorCertificateValue θ t0 s0 w00
      rw [texAnchorCertificate_auxPolynomial_eval_eq θ y0, hcombined,
        texAnchorCertificate_eval_polynomial]
    exact hval0 (by rw [← hpoly, hpzero]; simp)
  obtain ⟨y, hybox, hyne⟩ :=
    (dense_compl_zero_set pθ hpθ).inter_open_nonempty
      (texAnchorCertificateAuxBox L d)
      (isOpen_texAnchorCertificateAuxBox L d)
      (texAnchorCertificateAuxBox_nonempty L d)
  let t : AnchorGateVector L := fun k => y (Sum.inl (Sum.inl k))
  let s : AnchorGateVector L := fun k => y (Sum.inl (Sum.inr k))
  let w0 : Fin d -> ℝ := fun i => y (Sum.inr i)
  refine ⟨⟨t, s, w0, ?_, hybox.1, hybox.2⟩⟩
  have hy_eq : y = texAnchorCertificate_auxEval t s w0 := by
    funext a
    rcases a with (⟨k | k⟩ | i) <;> rfl
  have hcombined :
      Sum.elim y (paramFlat θ) =
        texAnchorCertificate_combinedEval θ t s w0 := by
    funext z
    cases z with
    | inl a => simp [hy_eq]
    | inr c => rfl
  have hpoly :
      (MvPolynomial.eval y) pθ = anchorCertificateValue θ t s w0 := by
    change
      (MvPolynomial.eval y)
          (MvPolynomial.map (MvPolynomial.eval (paramFlat θ))
            (texAnchorCertificate_auxPolynomial L d)) =
        anchorCertificateValue θ t s w0
    rw [texAnchorCertificate_auxPolynomial_eval_eq θ y, hcombined,
      texAnchorCertificate_eval_polynomial]
  intro hzero
  exact hyne (by rw [hpoly, hzero])

theorem vector_ne_zero_of_vectorNormSq_ne_zero {d : Nat} {x : Fin d -> ℝ}
    (h : vectorNormSq x ≠ 0) : x ≠ 0 := by
  intro hx
  exact h (by simp [hx, vectorNormSq])

/-- A nonzero good certificate evaluation has all the factor nonvanishing data needed
by the affine solve and the unwinding verification. -/
theorem goodFactors_of_goodEvaluation
    {L d : Nat} {θ : Params L d}
    (D : AnchorCertificateGoodEvaluation θ) :
    AnchorCertificateGoodFactors D := by
  classical
  let G := anchorCertificateGradientMatrix θ D.t D.s D.w0
  let stepProd : ℝ :=
    ∏ k : Fin (L - 1), (anchorStepMatrix (paramStream θ) k.val (D.t k)).det
  let normProd : ℝ :=
    ∏ k : Fin (L - 1),
      vectorNormSq ((Matrix.transpose (paramStream θ k.val).2).mulVec
        (anchorCertificateW θ D.t k.val D.w0))
  have hvalue : ((Matrix.transpose G * G).det * stepProd) * normProd ≠ 0 := by
    simpa [anchorCertificateValue, G, stepProd, normProd] using D.value_ne_zero
  have hleft : (Matrix.transpose G * G).det * stepProd ≠ 0 :=
    (mul_ne_zero_iff.mp hvalue).1
  have hnormProd : normProd ≠ 0 :=
    (mul_ne_zero_iff.mp hvalue).2
  have hgram : (Matrix.transpose G * G).det ≠ 0 :=
    (mul_ne_zero_iff.mp hleft).1
  have hstepProd : stepProd ≠ 0 :=
    (mul_ne_zero_iff.mp hleft).2
  refine ⟨?_, ?_, ?_⟩
  · simpa [G] using hgram
  · intro k
    exact (Finset.prod_ne_zero_iff.mp hstepProd) k (Finset.mem_univ k)
  · intro k
    apply vector_ne_zero_of_vectorNormSq_ne_zero
    exact (Finset.prod_ne_zero_iff.mp hnormProd) k (Finset.mem_univ k)

/-! ## Remaining algebraic obligations for Proposition `anchorsexist` -/

/-- The two layer-stream views of a finite parameter tuple agree. -/
theorem anchorParamStream_eq_paramStream {L d : Nat} (θ : Params L d) :
    anchorParamStream θ = paramStream θ := by
  funext n
  by_cases h : n < L
  · simp [anchorParamStream, paramStream, h]
  · simp [anchorParamStream, paramStream, h]

/-- The first component of an anchor path is the certificate transport of `w0`;
it is independent of the base vector `v`. -/
theorem anchorPath_first_eq_anchorCertificateW
    {L d : Nat} (θ : Params L d)
    (t : AnchorGateVector L) (w0 v : Fin d -> ℝ) (n : Nat) :
    (anchorPath (paramStream θ) n (anchorGateStream t) (w0, v)).1 =
      anchorCertificateW θ t n w0 := by
  induction n with
  | zero =>
      simp [anchorCertificateW, anchorRealWprod]
  | succ n ih =>
      simp [anchorPath_succ, anchorStep, ih, anchorCertificateW, anchorRealWprod,
        Matrix.mulVec_mulVec]

/-- The first component is unchanged by an anchor step whose gate is `1`. -/
theorem anchorStepMatrix_one {d : Nat}
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (k : Nat) :
    anchorStepMatrix θ k 1 = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [anchorStepMatrix, skipB]
  · simp [anchorStepMatrix, skipB, Matrix.one_apply_ne hij]

/-- The first component of an anchor path only depends on gates before the endpoint. -/
theorem anchorPath_first_congr_gates {d : Nat}
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (t u : Nat -> ℝ) (p : AnchorProbe d)
    (h : ∀ j, j < n -> t j = u j) :
    (anchorPath θ n t p).1 = (anchorPath θ n u p).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hprev : ∀ j, j < n -> t j = u j := by
        intro j hj
        exact h j (Nat.lt_trans hj (Nat.lt_succ_self n))
      have hgate : t n = u n := h n (Nat.lt_succ_self n)
      simp [anchorPath_succ, anchorStep, hgate, ih hprev]

/-- The first component of an anchor path is independent of the input base vector `v`. -/
theorem anchorPath_first_eq_base {d : Nat}
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (t : Nat -> ℝ) (w0 v : Fin d -> ℝ) :
    (anchorPath θ n t (w0, v)).1 =
      (anchorPath θ n t (w0, 0)).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [anchorPath_succ, anchorStep, ih]

/-- The second component of an anchor path is affine in the input base vector `v`. -/
theorem anchorPath_second_eq_base_add_anchorRealBprod {d : Nat}
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (t : Nat -> ℝ) (w0 v : Fin d -> ℝ) :
    (anchorPath θ n t (w0, v)).2 =
      (anchorPath θ n t (w0, 0)).2 + (anchorRealBprod θ n).mulVec v := by
  induction n with
  | zero =>
      ext i
      simp [anchorRealBprod]
  | succ n ih =>
      have hfirst := anchorPath_first_eq_base θ n t w0 v
      ext i
      simp [anchorPath_succ, anchorStep, anchorRealBprod, ih, hfirst,
        Matrix.mulVec_add, Matrix.mulVec_mulVec]
      ring

/-- Move a two-matrix linear coefficient from a dot product onto the right vector. -/
theorem transpose_mulVec_transpose_mulVec_dot
    {d : Nat} (B A : Matrix (Fin d) (Fin d) ℝ) (w v : Fin d -> ℝ) :
    (Bᵀ *ᵥ (Aᵀ *ᵥ w)) ⬝ᵥ v =
      w ⬝ᵥ (A *ᵥ (B *ᵥ v)) := by
  rw [dotProduct_comm]
  rw [Matrix.dotProduct_transpose_mulVec]
  rw [dotProduct_comm]
  rw [Matrix.dotProduct_transpose_mulVec]

/-- The signed transpose form used by the `T` rows. -/
theorem neg_mul_mulVec_dot_eq_neg_transpose_mulVec_dot
    {d : Nat} (B A C : Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d -> ℝ) :
    -(((A * B) *ᵥ v) ⬝ᵥ (C *ᵥ w)) =
      (fun i => -(((Bᵀ * (Aᵀ * C)) *ᵥ w) i)) ⬝ᵥ v := by
  rw [show (fun i => -(((Bᵀ * (Aᵀ * C)) *ᵥ w) i)) =
      -(((Bᵀ * (Aᵀ * C)) *ᵥ w)) by rfl]
  rw [neg_dotProduct]
  congr 1
  rw [dotProduct_comm]
  simpa [Matrix.mulVec_mulVec] using
    (transpose_mulVec_transpose_mulVec_dot B A (C *ᵥ w) v).symm

/-- Slope rows are affine in the input base vector with the declared linear part. -/
theorem anchorSlopeAt_eq_base_add_gradient_dot {d : Nat}
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (n : Nat) (t : Nat -> ℝ) (w0 v : Fin d -> ℝ) :
    anchorSlopeAt θ n t (w0, v) =
      anchorSlopeAt θ n t (w0, 0) +
        ((anchorRealBprod θ n)ᵀ *ᵥ
          ((θ n).2ᵀ *ᵥ (anchorPath θ n t (w0, 0)).1)) ⬝ᵥ v := by
  have hfirst := anchorPath_first_eq_base θ n t w0 v
  have hsecond := anchorPath_second_eq_base_add_anchorRealBprod θ n t w0 v
  simp [anchorSlopeAt, hfirst, hsecond, Matrix.mulVec_add,
    Matrix.mulVec_mulVec]
  simpa [Matrix.mulVec_mulVec] using
    (transpose_mulVec_transpose_mulVec_dot (anchorRealBprod θ n) (θ n).2
      (anchorPath θ n t (w0, 0)).1 v).symm

/-- If all gates in a suffix are `1`, that suffix does not change the first component. -/
theorem anchorPath_first_add_of_one_gates {d : Nat}
    (θ : Nat -> Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)
    (t : Nat -> ℝ) (m r : Nat) (p : AnchorProbe d)
    (h : ∀ j, m ≤ j -> j < m + r -> t j = 1) :
    (anchorPath θ (m + r) t p).1 = (anchorPath θ m t p).1 := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      have hprev : ∀ j, m ≤ j -> j < m + r -> t j = 1 := by
        intro j hm hj
        exact h j hm (by omega)
      have hgate : t (m + r) = 1 := h (m + r) (by omega) (by omega)
      calc
        (anchorPath θ (m + (r + 1)) t p).1
            = (anchorPath θ ((m + r) + 1) t p).1 := by
                rw [Nat.add_succ]
        _ = (anchorPath θ (m + r) t p).1 := by
                simp [anchorPath_succ, anchorStep, hgate, anchorStepMatrix_one]
        _ = (anchorPath θ m t p).1 := ih hprev

/-- The first component used by an `S` row is the substituted one-step certificate vector. -/
theorem anchorPath_first_unwind_eq_anchorCertificateSBase
    {L d : Nat} (θ : Params L d) (t s : AnchorGateVector L)
    (q : AnchorCertificateSIndex L) (w0 v : Fin d -> ℝ) :
    let k : Fin (L - 1) := q.1
    let ell : Nat := q.2.1.val
    (anchorPath (paramStream θ) (k.val + ell - 1)
        (anchorUnwindGate (anchorGateStream t) (anchorGateStream s) k.val) (w0, v)).1 =
      (anchorStepMatrix (paramStream θ) k.val (s k)).mulVec
        (anchorCertificateW θ t k.val w0) := by
  classical
  dsimp
  let k : Fin (L - 1) := q.1
  let ell : Nat := q.2.1.val
  let τ := anchorUnwindGate (anchorGateStream t) (anchorGateStream s) k.val
  have hell : 2 ≤ ell := q.2.2.1
  have hn : k.val + ell - 1 = k.val + 1 + (ell - 2) := by
    omega
  have htail : ∀ j, k.val + 1 ≤ j -> j < k.val + 1 + (ell - 2) -> τ j = 1 := by
    intro j hjge _hjlt
    have hnot_lt : ¬ j < k.val := by omega
    have hne : j ≠ k.val := by omega
    simp [τ, anchorUnwindGate, hnot_lt, hne]
  have hprefix :
      (anchorPath (paramStream θ) k.val τ (w0, v)).1 =
        (anchorPath (paramStream θ) k.val (anchorGateStream t) (w0, v)).1 := by
    apply anchorPath_first_congr_gates
    intro j hj
    simp [τ, anchorUnwindGate, hj]
  have hgate : τ k.val = s k := by
    dsimp [τ]
    rw [anchorUnwindGate, if_neg (Nat.lt_irrefl k.val), if_pos rfl]
    cases k with
    | mk n hn =>
        change anchorGateStream s n = s ⟨n, hn⟩
        rw [anchorGateStream, dif_pos hn]
  calc
    (anchorPath (paramStream θ) (k.val + ell - 1) τ (w0, v)).1
        = (anchorPath (paramStream θ) (k.val + 1 + (ell - 2)) τ (w0, v)).1 := by
            rw [hn]
    _ = (anchorPath (paramStream θ) (k.val + 1) τ (w0, v)).1 := by
            exact anchorPath_first_add_of_one_gates (paramStream θ) τ
              (k.val + 1) (ell - 2) (w0, v) htail
    _ = (anchorStepMatrix (paramStream θ) k.val (s k)).mulVec
          (anchorCertificateW θ t k.val w0) := by
            rw [anchorPath_succ]
            simp [anchorStep, hgate, hprefix,
              anchorPath_first_eq_anchorCertificateW θ t w0 v k.val]

/-- A nonsingular matrix's adjugate acts as determinant times the matrix inverse. -/
theorem matrix_adjugate_mulVec_eq_det_smul_inv_mulVec {d : Nat}
    (M : Matrix (Fin d) (Fin d) ℝ) (y : Fin d -> ℝ)
    (hdet : M.det ≠ 0) :
    M.adjugate.mulVec y = M.det • (M⁻¹ *ᵥ y) := by
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  rw [Matrix.nonsing_inv_apply M hunit]
  ext i
  simp [Matrix.smul_mulVec]
  field_simp [hdet]

/-- The certificate `T_k` row is determinant times the inverse-scalar clause from
`AnchorUnwindingData`. -/
theorem anchorCertificateTValue_eq_det_mul_anchorInverseScalar
    {L d : Nat} (θ : Params L d)
    (t : AnchorGateVector L) (k : Fin (L - 1)) (w0 v : Fin d -> ℝ)
    (hdet : (anchorStepMatrix (paramStream θ) k.val (t k)).det ≠ 0) :
    anchorCertificateTValue θ t k w0 v =
      (anchorStepMatrix (paramStream θ) k.val (t k)).det *
        anchorInverseScalarAt (paramStream θ) k.val (anchorGateStream t) (w0, v) := by
  let τ := anchorGateStream t
  let p : AnchorProbe d := (w0, v)
  let pk := anchorPath (paramStream θ) k.val τ p
  let M := anchorStepMatrix (paramStream θ) k.val (t k)
  let y := (paramStream θ k.val).1.mulVec pk.1
  have hgate : anchorGateStream t k.val = t k := by
    cases k with
    | mk n hn => simp [anchorGateStream, hn]
  have hy : M.adjugate.mulVec y = M.det • (M⁻¹ *ᵥ y) :=
    matrix_adjugate_mulVec_eq_det_smul_inv_mulVec M y (by simpa [M] using hdet)
  rw [anchorCertificateTValue, anchorInverseScalarAt, hgate]
  change anchorCovectorAt (paramStream θ) k.val τ p ⬝ᵥ M.adjugate.mulVec y =
      M.det * (anchorCovectorAt (paramStream θ) k.val τ p ⬝ᵥ (M⁻¹ *ᵥ y))
  rw [hy, dotProduct_smul]
  rfl

/-- Solving arbitrary row targets from an invertible Gram matrix. -/
theorem exists_vector_dot_eq_of_gram_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : Nat}
    (G : Matrix (Fin d) ι ℝ)
    (hdet : ((Matrix.transpose G * G) : Matrix ι ι ℝ).det ≠ 0)
    (b : ι -> ℝ) :
    ∃ v : Fin d -> ℝ, ∀ row : ι,
      (fun i => G i row) ⬝ᵥ v = b row := by
  let A : Matrix ι ι ℝ := Matrix.transpose G * G
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (by simpa [A] using hdet)
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A hunit
  refine ⟨G *ᵥ (A⁻¹ *ᵥ b), ?_⟩
  intro row
  have hvec : A *ᵥ (A⁻¹ *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hrow : (fun i => G i row) ⬝ᵥ (G *ᵥ (A⁻¹ *ᵥ b)) =
      (A *ᵥ (A⁻¹ *ᵥ b)) row := by
    change (Matrix.transpose G *ᵥ (G *ᵥ (A⁻¹ *ᵥ b))) row = _
    rw [Matrix.mulVec_mulVec]
  rw [hrow, hvec]

/-- The declared certificate gradients are the linear parts of the affine row values. -/
theorem anchorCertificateRowValue_eq_base_add_gradient_dot
    {L d : Nat} (θ : Params L d) (t s : AnchorGateVector L)
    (w0 v : Fin d -> ℝ) (row : AnchorCertificateRow L) :
    anchorCertificateRowValue θ t s w0 v row =
      anchorCertificateRowValue θ t s w0 0 row +
        anchorCertificateGradient θ t s row w0 ⬝ᵥ v := by
  rcases row with (row | k)
  · rcases row with (k | q)
    · simpa [anchorCertificateRowValue, anchorCertificateGradient,
        anchorCertificateGradientE,
        anchorPath_first_eq_anchorCertificateW θ t w0 0 k.val] using
        anchorSlopeAt_eq_base_add_gradient_dot (paramStream θ) k.val
          (anchorGateStream t) w0 v
    · simpa [anchorCertificateRowValue, anchorCertificateGradient,
        anchorCertificateGradientS,
        anchorPath_first_unwind_eq_anchorCertificateSBase θ t s q w0 0] using
        anchorSlopeAt_eq_base_add_gradient_dot (paramStream θ)
          (q.1.val + q.2.1.val - 1)
          (anchorUnwindGate (anchorGateStream t) (anchorGateStream s) q.1.val)
          w0 v
  · let τ := anchorGateStream t
    let pk0 := anchorPath (paramStream θ) k.val τ (w0, (0 : Fin d -> ℝ))
    let M := anchorStepMatrix (paramStream θ) k.val (t k)
    let y := (paramStream θ k.val).1.mulVec (anchorCertificateW θ t k.val w0)
    let z := M.adjugate.mulVec y
    have hgate : τ k.val = t k := by
      cases k with
      | mk n hn =>
          dsimp [τ]
          rw [anchorGateStream, dif_pos hn]
    have hfirstv :
        (anchorPath (paramStream θ) k.val τ (w0, v)).1 =
          anchorCertificateW θ t k.val w0 :=
      anchorPath_first_eq_anchorCertificateW θ t w0 v k.val
    have hfirst0 :
        (anchorPath (paramStream θ) k.val τ (w0, (0 : Fin d -> ℝ))).1 =
          anchorCertificateW θ t k.val w0 :=
      anchorPath_first_eq_anchorCertificateW θ t w0 0 k.val
    have hsecond :=
      anchorPath_second_eq_base_add_anchorRealBprod (paramStream θ) k.val τ w0 v
    simpa [anchorCertificateRowValue, anchorCertificateTValue, anchorCertificateGradient,
      anchorCertificateGradientT, anchorCovectorAt, τ, pk0, M, y, z, hgate,
      hfirstv, hfirst0, hsecond, Matrix.mulVec_add,
      sub_eq_add_neg, add_comm, add_left_comm] using
      (neg_mul_mulVec_dot_eq_neg_transpose_mulVec_dot
        (anchorRealBprod (paramStream θ) k.val) (paramStream θ k.val).2
        ((anchorStepMatrix (paramStream θ) k.val (t k)).adjugate *
          (paramStream θ k.val).1)
        (anchorCertificateW θ t k.val w0) v)

/-- The full-rank affine row solve from the Gram determinant and row bound. -/
theorem anchorCertificateAffineSolution_exists
    {L d : Nat} (_hrows : genericCertificateRows L <= d)
    {θ : Params L d} (D : AnchorCertificateGoodEvaluation θ)
    (F : AnchorCertificateGoodFactors D) :
    Nonempty (AnchorCertificateAffineSolution D) := by
  classical
  let G := anchorCertificateGradientMatrix θ D.t D.s D.w0
  let b : AnchorCertificateRow L -> ℝ := fun row =>
    anchorCertificateTargetValue row -
      anchorCertificateRowValue θ D.t D.s D.w0 0 row
  rcases exists_vector_dot_eq_of_gram_det_ne_zero G
      (by simpa [G] using F.gram_det_ne_zero) b with
    ⟨v, hv⟩
  refine ⟨⟨v, ?_⟩⟩
  intro row
  have haff :=
    anchorCertificateRowValue_eq_base_add_gradient_dot θ D.t D.s D.w0 v row
  have hdot : anchorCertificateGradient θ D.t D.s row D.w0 ⬝ᵥ v = b row := by
    simpa [G, anchorCertificateGradientMatrix] using hv row
  calc
    anchorCertificateRowValue θ D.t D.s D.w0 v row
        = anchorCertificateRowValue θ D.t D.s D.w0 0 row +
            anchorCertificateGradient θ D.t D.s row D.w0 ⬝ᵥ v := haff
    _ = anchorCertificateRowValue θ D.t D.s D.w0 0 row + b row := by rw [hdot]
    _ = anchorCertificateTargetValue row := by
      simp [b]

/-- Verification that solved certificate rows satisfy the unwinding-data clauses. -/
theorem anchorUnwindingData_nonempty_of_anchorCertificateSolution
    {L d : Nat} (_hL : 2 <= L)
    {θ : Params L d} (D : AnchorCertificateGoodEvaluation θ)
    (F : AnchorCertificateGoodFactors D)
    (S : AnchorCertificateAffineSolution D) :
    Nonempty (AnchorUnwindingData θ (D.w0, S.v)) := by
  refine ⟨{
    t := anchorGateStream D.t
    s := anchorGateStream D.s
    t_mem_Ioo := ?_
    s_mem_Ioo := ?_
    slope_zero := ?_
    attention_image_ne_zero := ?_
    covector_ne_zero := ?_
    positive_later := ?_
    det_step_ne_zero := ?_
    inverse_scalar_ne_zero := ?_ }⟩
  · intro k hk
    simpa [anchorGateStream, hk] using D.t_mem_Ioo ⟨k, hk⟩
  · intro k hk
    simpa [anchorGateStream, hk] using D.s_mem_Ioo ⟨k, hk⟩
  · intro k hk
    have hrow := AnchorCertificateAffineSolution.eRow_zero S ⟨k, hk⟩
    simpa [anchorCertificateRowValue, anchorParamStream_eq_paramStream θ] using hrow
  · intro k hk
    have h := F.attention_image_ne_zero ⟨k, hk⟩
    simpa [anchorParamStream_eq_paramStream θ,
      anchorPath_first_eq_anchorCertificateW θ D.t D.w0 S.v k] using h
  · intro k hk hcov
    have hrow : anchorCertificateTValue θ D.t ⟨k, hk⟩ D.w0 S.v = 1 := by
      simpa [anchorCertificateRowValue] using
        AnchorCertificateAffineSolution.tRow_one S ⟨k, hk⟩
    have hcov' :
        anchorCovectorAt (paramStream θ) k (anchorGateStream D.t) (D.w0, S.v) = 0 := by
      simpa [anchorParamStream_eq_paramStream θ] using hcov
    have hzero : anchorCertificateTValue θ D.t ⟨k, hk⟩ D.w0 S.v = 0 := by
      simp [anchorCertificateTValue, hcov']
    rw [hrow] at hzero
    norm_num at hzero
  · intro k ell hk hell hkle
    let q : AnchorCertificateSIndex L :=
      ⟨⟨k, hk⟩, ⟨⟨ell, by omega⟩, hell, hkle⟩⟩
    have hrow := AnchorCertificateAffineSolution.sRow_one S q
    have hslope :
        anchorSlopeAt (anchorParamStream θ) (k + ell - 1)
          (anchorUnwindGate (anchorGateStream D.t) (anchorGateStream D.s) k)
          (D.w0, S.v) = 1 := by
      simpa [anchorCertificateRowValue, q, anchorParamStream_eq_paramStream θ] using hrow
    rw [hslope]
    norm_num
  · intro k hk
    have h := F.det_step_ne_zero ⟨k, hk⟩
    simpa [anchorParamStream_eq_paramStream θ, anchorGateStream, hk] using h
  · intro k hk hinv
    have hdet := F.det_step_ne_zero ⟨k, hk⟩
    have hrow : anchorCertificateTValue θ D.t ⟨k, hk⟩ D.w0 S.v = 1 := by
      simpa [anchorCertificateRowValue] using
        AnchorCertificateAffineSolution.tRow_one S ⟨k, hk⟩
    have hrel :=
      anchorCertificateTValue_eq_det_mul_anchorInverseScalar θ D.t ⟨k, hk⟩
        D.w0 S.v hdet
    have hprod :
        (anchorStepMatrix (paramStream θ) k (D.t ⟨k, hk⟩)).det *
          anchorInverseScalarAt (paramStream θ) k (anchorGateStream D.t) (D.w0, S.v) = 1 := by
      rw [← hrel]
      exact hrow
    have hinv' :
        anchorInverseScalarAt (paramStream θ) k (anchorGateStream D.t) (D.w0, S.v) = 0 := by
      simpa [anchorParamStream_eq_paramStream θ] using hinv
    rw [hinv'] at hprod
    norm_num at hprod

/-- The TeX anchor certificate produces an actual unwound anchor under the certificate
row bound. -/
theorem unwoundAnchorSet_nonempty_of_texAnchorCertificate
    {L d : Nat} (hL : 2 <= L) (hrows : genericCertificateRows L <= d)
    {θ : Params L d}
    (hcert : TexAnchorCertificate θ) :
    (unwoundAnchorSet θ).Nonempty := by
  rcases exists_goodEvaluation_of_texAnchorCertificate hcert with ⟨D⟩
  let F : AnchorCertificateGoodFactors D := goodFactors_of_goodEvaluation D
  rcases anchorCertificateAffineSolution_exists hrows D F with ⟨S⟩
  refine ⟨(D.w0, S.v), ?_⟩
  exact anchorUnwindingData_nonempty_of_anchorCertificateSolution hL D F S

end TransformerIdentifiability.NLayer
