import Mathlib

set_option autoImplicit false

open MeasureTheory Matrix MvPolynomial

namespace TransformerIdentifiability.TwoLayer

noncomputable def causalSoftmax {T : ℕ} (M : Matrix (Fin T) (Fin T) ℝ) :
    Matrix (Fin T) (Fin T) ℝ :=
  Matrix.of fun i j =>
    if i ≤ j then Real.exp (M i j) / ∑ i' ∈ Finset.Iic j, Real.exp (M i' j) else 0

noncomputable def attnLayer {d T : ℕ} (V A : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin T) ℝ) : Matrix (Fin d) (Fin T) ℝ :=
  X + V * X * causalSoftmax (Xᵀ * A * X)

abbrev Params (d : ℕ) : Type :=
  (Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) ×
  (Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ)

noncomputable def network {d T : ℕ} (θ : Params d)
    (X : Matrix (Fin d) (Fin T) ℝ) : Matrix (Fin d) (Fin T) ℝ :=
  attnLayer θ.2.1 θ.2.2 (attnLayer θ.1.1 θ.1.2 X)

noncomputable instance {n m : ℕ} : MeasureSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (MeasureSpace (Fin n → Fin m → ℝ))

instance instMatrixSigmaFinite {n m : ℕ} :
    SigmaFinite (volume : Measure (Matrix (Fin n) (Fin m) ℝ)) :=
  inferInstanceAs (SigmaFinite (volume : Measure (Fin n → Fin m → ℝ)))

/-! ## A null-set lemma for zero sets of nonzero multivariate polynomials -/

/-- The zero set of a nonzero real multivariate polynomial in `n` variables has Lebesgue
measure zero. Proved by induction on `n` using Fubini. -/
theorem mvpoly_eval_null :
    ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ), p ≠ 0 →
      volume {x : Fin n → ℝ | (MvPolynomial.eval x) p = 0} = 0 := by
  intro n
  induction n with
  | zero =>
    intro p hp
    have hc0 : p.coeff 0 ≠ 0 := by
      intro h
      exact hp (by rw [eq_C_of_isEmpty p, h, map_zero])
    have hempty : {x : Fin 0 → ℝ | (MvPolynomial.eval x) p = 0} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      apply hc0
      rw [Set.mem_setOf_eq, eq_C_of_isEmpty p, eval_C] at hx
      exact hx
    rw [hempty, measure_empty]
  | succ n ih =>
    intro p hp
    set q : Polynomial (MvPolynomial (Fin n) ℝ) := finSuccEquiv ℝ n p with hq_def
    have hq : q ≠ 0 := by
      rw [hq_def, Ne, EmbeddingLike.map_eq_zero_iff]
      exact hp
    set c : MvPolynomial (Fin n) ℝ := q.leadingCoeff with hc_def
    have hc : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hq
    have hZ : volume {s : Fin n → ℝ | (MvPolynomial.eval s) c = 0} = 0 := ih c hc
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with he_def
    set G : (Fin (n + 1) → ℝ) → (Fin n → ℝ) × ℝ := fun x => (Fin.tail x, x 0) with hG_def
    have hGmp : MeasurePreserving G volume (volume.prod volume) := by
      have h1 : MeasurePreserving e volume (volume.prod volume) :=
        volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      have h2 : MeasurePreserving (Prod.swap : ℝ × (Fin n → ℝ) → (Fin n → ℝ) × ℝ)
          (volume.prod volume) (volume.prod volume) := Measure.measurePreserving_swap
      have hfun : G = Prod.swap ∘ ⇑e := by
        funext x
        have hex : (e x) = (x 0, Fin.tail x) := by
          simp only [e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_zero]
          rfl
        simp [hG_def, Function.comp_apply, hex]
      rw [hfun]
      exact h2.comp h1
    set T : Set ((Fin n → ℝ) × ℝ) :=
      {z | (MvPolynomial.eval (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ)) p = 0} with hT_def
    have hcons_meas :
        Measurable (fun z : (Fin n → ℝ) × ℝ => (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ)) := by
      rw [measurable_pi_iff]
      intro i
      refine Fin.cases ?_ ?_ i
      · simpa using measurable_snd
      · intro j; simpa using (measurable_pi_apply j).comp measurable_fst
    have hT_meas : MeasurableSet T := by
      have : Measurable (fun z : (Fin n → ℝ) × ℝ =>
          (MvPolynomial.eval (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ)) p) :=
        (MvPolynomial.continuous_eval p).measurable.comp hcons_meas
      exact this (measurableSet_singleton 0)
    have hSeq : {x : Fin (n + 1) → ℝ | (MvPolynomial.eval x) p = 0} = G ⁻¹' T := by
      ext x
      simp only [hG_def, hT_def, Set.mem_preimage, Set.mem_setOf_eq]
      rw [Fin.cons_self_tail]
    rw [hSeq, hGmp.measure_preimage hT_meas.nullMeasurableSet]
    rw [Measure.measure_prod_null hT_meas]
    have hsub : {s : Fin n → ℝ | volume (Prod.mk s ⁻¹' T) ≠ 0} ⊆
        {s : Fin n → ℝ | (MvPolynomial.eval s) c = 0} := by
      intro s hs
      simp only [Set.mem_setOf_eq] at hs ⊢
      by_contra hsc
      apply hs
      have hmap : Polynomial.map (MvPolynomial.eval s) q ≠ 0 := by
        intro h0
        apply hsc
        have hco : (Polynomial.map (MvPolynomial.eval s) q).coeff q.natDegree
            = (MvPolynomial.eval s) c := by
          rw [Polynomial.coeff_map]; rfl
        rw [h0] at hco
        simpa using hco.symm
      have hset :
          (Prod.mk s ⁻¹' T) = {y : ℝ | (Polynomial.map (MvPolynomial.eval s) q).IsRoot y} := by
        ext y
        simp only [hT_def, Set.mem_preimage, Set.mem_setOf_eq, Polynomial.IsRoot.def]
        rw [MvPolynomial.eval_eq_eval_mv_eval' s y p]
      rw [hset]
      exact (Polynomial.finite_setOf_isRoot hmap).measure_zero _
    have key : volume {s : Fin n → ℝ | volume (Prod.mk s ⁻¹' T) ≠ 0} = 0 :=
      measure_mono_null hsub hZ
    have hae : ∀ᵐ s ∂(volume : Measure (Fin n → ℝ)), volume (Prod.mk s ⁻¹' T) = 0 := by
      rw [ae_iff]; simpa using key
    filter_upwards [hae] with s hs
    simpa using hs

/-- Version for an arbitrary finite index type. -/
theorem mvpoly_eval_null' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) :
    volume {x : ι → ℝ | (MvPolynomial.eval x) p = 0} = 0 := by
  classical
  set ev : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with hev
  set Ψ := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) ev.symm with hΨdef
  have hΨ : MeasurePreserving Ψ volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) ev.symm
  have hmeas : MeasurableSet {x : ι → ℝ | (MvPolynomial.eval x) p = 0} :=
    (MvPolynomial.continuous_eval p).measurable (measurableSet_singleton 0)
  rw [← hΨ.measure_preimage hmeas.nullMeasurableSet]
  have hset : Ψ ⁻¹' {x : ι → ℝ | (MvPolynomial.eval x) p = 0}
      = {y : Fin (Fintype.card ι) → ℝ | (MvPolynomial.eval y) (rename ev p) = 0} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    have hΨy : (Ψ y) = y ∘ ⇑ev := by
      funext a
      have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => ℝ) ev.symm y (ev a)
      simpa [hΨdef] using h
    rw [hΨy, ← MvPolynomial.eval_rename]
  rw [hset]
  refine mvpoly_eval_null _ (rename ev p) ?_
  have := (rename_injective (⇑ev) ev.injective).ne hp
  simpa using this

/-- "Uncurrying" a matrix as a measure-preserving map to the flat coordinate space
`(Fin d × Fin d) → ℝ`. -/
theorem volume_preserving_uncurryMatrix (d : ℕ) :
    MeasurePreserving
      (fun (x : Fin d → Fin d → ℝ) (k : Fin d × Fin d) => x k.1 k.2)
      (volume : Measure (Fin d → Fin d → ℝ))
      (volume : Measure ((Fin d × Fin d) → ℝ)) := by
  set f : (Fin d → Fin d → ℝ) → ((Fin d × Fin d) → ℝ) := fun x k => x k.1 k.2 with hf
  have hfmeas : Measurable f := by
    rw [measurable_pi_iff]; intro k
    exact (measurable_pi_apply k.2).comp (measurable_pi_apply k.1)
  refine ⟨hfmeas, ?_⟩
  rw [volume_pi (α := fun _ : Fin d × Fin d => ℝ)]
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply hfmeas (MeasurableSet.univ_pi hs)]
  have hpre : f ⁻¹' (Set.univ.pi s)
      = Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext x
    simp only [hf, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Prod.forall]
  rw [hpre, volume_pi_pi]
  simp_rw [volume_pi_pi]
  rw [← Finset.univ_product_univ, Finset.prod_product]

/-! ## Flattening the parameter space and the genericity polynomial -/

abbrev Kidx (d : ℕ) := Fin d × Fin d
abbrev Jidx (d : ℕ) := (Kidx d ⊕ Kidx d) ⊕ (Kidx d ⊕ Kidx d)

/-- uncurry a matrix into a flat function on `Fin d × Fin d`. -/
def uncf {d : ℕ} (x : Matrix (Fin d) (Fin d) ℝ) : Kidx d → ℝ := fun k => x k.1 k.2

/-- combine two functions on `α`, `β` into one on `α ⊕ β`. -/
def combf {α β : Type*} (p : (α → ℝ) × (β → ℝ)) : (α ⊕ β) → ℝ := Sum.elim p.1 p.2

/-- The flattening map `Params d → (Jidx d → ℝ)`. -/
noncomputable def flat (d : ℕ) : Params d → (Jidx d → ℝ) :=
  combf ∘ Prod.map combf combf ∘ Prod.map (Prod.map uncf uncf) (Prod.map uncf uncf)

theorem mp_combf {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
    MeasurePreserving (combf : (α → ℝ) × (β → ℝ) → ((α ⊕ β) → ℝ)) volume volume := by
  have h := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : α ⊕ β => ℝ)
  have heq : (combf : (α → ℝ) × (β → ℝ) → ((α ⊕ β) → ℝ))
      = ⇑(MeasurableEquiv.sumPiEquivProdPi (fun _ : α ⊕ β => ℝ)).symm := by
    funext p
    rw [MeasurableEquiv.coe_sumPiEquivProdPi_symm]
    funext x
    cases x <;> rfl
  rw [heq]; exact h

theorem mp_uncf (d : ℕ) :
    MeasurePreserving (uncf : Matrix (Fin d) (Fin d) ℝ → (Kidx d → ℝ)) volume volume :=
  volume_preserving_uncurryMatrix d

theorem mp_flat (d : ℕ) : MeasurePreserving (flat d) volume volume := by
  have h1 := ((mp_uncf d).prod (mp_uncf d)).prod ((mp_uncf d).prod (mp_uncf d))
  have h2 := (mp_combf (α := Kidx d) (β := Kidx d)).prod (mp_combf (α := Kidx d) (β := Kidx d))
  have h3 := mp_combf (α := Kidx d ⊕ Kidx d) (β := Kidx d ⊕ Kidx d)
  exact h3.comp (h2.comp h1)

@[simp] theorem flat_inl_inl {d : ℕ} (θ : Params d) (k : Kidx d) :
    flat d θ (Sum.inl (Sum.inl k)) = θ.1.1 k.1 k.2 := rfl
@[simp] theorem flat_inl_inr {d : ℕ} (θ : Params d) (k : Kidx d) :
    flat d θ (Sum.inl (Sum.inr k)) = θ.1.2 k.1 k.2 := rfl
@[simp] theorem flat_inr_inl {d : ℕ} (θ : Params d) (k : Kidx d) :
    flat d θ (Sum.inr (Sum.inl k)) = θ.2.1 k.1 k.2 := rfl
@[simp] theorem flat_inr_inr {d : ℕ} (θ : Params d) (k : Kidx d) :
    flat d θ (Sum.inr (Sum.inr k)) = θ.2.2 k.1 k.2 := rfl

/-- coordinate ring of the flattened parameter space. -/
abbrev RR (d : ℕ) := MvPolynomial (Jidx d) ℝ

noncomputable def genV1 (d : ℕ) : Matrix (Fin d) (Fin d) (RR d) :=
  Matrix.of fun i j => MvPolynomial.X (Sum.inl (Sum.inl (i, j)))
noncomputable def genA1 (d : ℕ) : Matrix (Fin d) (Fin d) (RR d) :=
  Matrix.of fun i j => MvPolynomial.X (Sum.inl (Sum.inr (i, j)))
noncomputable def genV2 (d : ℕ) : Matrix (Fin d) (Fin d) (RR d) :=
  Matrix.of fun i j => MvPolynomial.X (Sum.inr (Sum.inl (i, j)))
noncomputable def genA2 (d : ℕ) : Matrix (Fin d) (Fin d) (RR d) :=
  Matrix.of fun i j => MvPolynomial.X (Sum.inr (Sum.inr (i, j)))

theorem map_genV1 {d : ℕ} (θ : Params d) :
    (genV1 d).map (MvPolynomial.eval (flat d θ)) = θ.1.1 := by
  ext i j; simp [genV1, Matrix.map_apply]
theorem map_genA1 {d : ℕ} (θ : Params d) :
    (genA1 d).map (MvPolynomial.eval (flat d θ)) = θ.1.2 := by
  ext i j; simp [genA1, Matrix.map_apply]
theorem map_genV2 {d : ℕ} (θ : Params d) :
    (genV2 d).map (MvPolynomial.eval (flat d θ)) = θ.2.1 := by
  ext i j; simp [genV2, Matrix.map_apply]
theorem map_genA2 {d : ℕ} (θ : Params d) :
    (genA2 d).map (MvPolynomial.eval (flat d θ)) = θ.2.2 := by
  ext i j; simp [genA2, Matrix.map_apply]

/-- The genericity polynomial: a product of four factors detecting the four conditions
defining `𝒢_r` (rank of `I+V₁`, `A₁≠0`, `V₂(I+βV₁)≠0`, and the quadratic-form condition).
The complement of its zero set is the generic set `𝒢_r`. -/
noncomputable def genPoly (r d : ℕ) [NeZero d] : RR d :=
  (((1 + genV1 d).submatrix (Fin.castLE (Nat.sub_le d 1))
      (Fin.castLE (Nat.sub_le d 1))).det)
    * (genA1 d 0 0)
    * ((genV2 d * (1 + (MvPolynomial.C ((r : ℝ) + 1)⁻¹ : RR d) • genV1 d) :
        Matrix (Fin d) (Fin d) (RR d)) 0 0)
    * (((1 + (MvPolynomial.C ((r : ℝ) + 1)⁻¹ : RR d) • genV1 d)ᵀ * genA2 d * genV1 d :
        Matrix (Fin d) (Fin d) (RR d)) 0 0)

theorem genPoly_ne_zero (r d : ℕ) [NeZero d] (hr : 2 ≤ r) (hd : 3 ≤ d) : genPoly r d ≠ 0 := by
  set β : ℝ := ((r : ℝ) + 1)⁻¹ with hβ
  have hβpos : 0 < β := by positivity
  have h1β : (1 : ℝ) + β ≠ 0 := by positivity
  set e : Fin (d - 1) → Fin d := Fin.castLE (Nat.sub_le d 1) with he
  have he_inj : Function.Injective e := Fin.castLE_injective _
  set θid : Params d := ((1, 1), (1, 1)) with hθid
  set w := flat d θid with hw
  set f : RR d →+* ℝ := MvPolynomial.eval w with hf
  set F : Matrix (Fin d) (Fin d) (RR d) →+* Matrix (Fin d) (Fin d) ℝ := f.mapMatrix with hFdef
  have hFV1 : F (genV1 d) = 1 := by
    rw [hFdef, RingHom.mapMatrix_apply, hf, hw, map_genV1 θid]
  have hFA1 : F (genA1 d) = 1 := by
    rw [hFdef, RingHom.mapMatrix_apply, hf, hw, map_genA1 θid]
  have hFV2 : F (genV2 d) = 1 := by
    rw [hFdef, RingHom.mapMatrix_apply, hf, hw, map_genV2 θid]
  have hFA2 : F (genA2 d) = 1 := by
    rw [hFdef, RingHom.mapMatrix_apply, hf, hw, map_genA2 θid]
  have entry : ∀ (M : Matrix (Fin d) (Fin d) (RR d)) (i j : Fin d), f (M i j) = (F M) i j := by
    intro M i j; rw [hFdef, RingHom.mapMatrix_apply, Matrix.map_apply]
  have hfC : ∀ x : ℝ, f ((MvPolynomial.C x : RR d)) = x := by
    intro x; rw [hf]; simp
  have hFsmul : ∀ (c : RR d) (M : Matrix (Fin d) (Fin d) (RR d)), F (c • M) = (f c) • (F M) := by
    intro c M; ext i j
    rw [hFdef, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      map_mul, Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply]
  have hFB : F (1 + (MvPolynomial.C β : RR d) • genV1 d)
      = 1 + β • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [map_add, map_one, hFsmul, hfC, hFV1]
  have hFt : ∀ M : Matrix (Fin d) (Fin d) (RR d), F Mᵀ = (F M)ᵀ := by
    intro M; rw [hFdef, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map]
  have hfD : f (((1 + genV1 d).submatrix e e).det) = (2 : ℝ) ^ (d - 1) := by
    have hM : (1 + genV1 d).map f = (1 : Matrix (Fin d) (Fin d) ℝ) + 1 := by
      rw [← RingHom.mapMatrix_apply, ← hFdef, map_add, map_one, hFV1]
    have hsubeq : ((1 : Matrix (Fin d) (Fin d) ℝ) + 1).submatrix e e
        = (2 : ℝ) • (1 : Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
        he_inj.eq_iff, smul_eq_mul]
      by_cases hij : i = j
      · subst hij; norm_num
      · simp [hij]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← submatrix_map, hM, hsubeq, Matrix.det_smul,
      Matrix.det_one, mul_one, Fintype.card_fin]
  have hfa : f (genA1 d 0 0) = 1 := by rw [entry, hFA1, Matrix.one_apply_eq]
  have hfp3 : f ((genV2 d * (1 + (MvPolynomial.C β : RR d) • genV1 d) :
      Matrix (Fin d) (Fin d) (RR d)) 0 0) = 1 + β := by
    rw [entry, map_mul, hFV2, one_mul, hFB]
    simp [Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply]
  have hfp4 : f (((1 + (MvPolynomial.C β : RR d) • genV1 d)ᵀ * genA2 d * genV1 d :
      Matrix (Fin d) (Fin d) (RR d)) 0 0) = 1 + β := by
    rw [entry, map_mul, map_mul, hFA2, hFV1, mul_one, mul_one, hFt, hFB]
    simp [Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply]
  have hval : f (genPoly r d) = (2 : ℝ) ^ (d - 1) * 1 * (1 + β) * (1 + β) := by
    rw [genPoly, map_mul, map_mul, map_mul, hfD, hfa, hfp3, hfp4]
  intro hP0
  rw [hP0, map_zero] at hval
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (d - 1) * 1 * (1 + β) * (1 + β) := by positivity
  exact (hpos.ne' hval.symm)

/-- The genericity null set `N` (complement of `𝒢_r`) has Lebesgue measure zero. -/
theorem genericity_null (r d : ℕ) [NeZero d] (hr : 2 ≤ r) (hd : 3 ≤ d) :
    volume {θ : Params d | (MvPolynomial.eval (flat d θ)) (genPoly r d) = 0} = 0 := by
  have hmp := mp_flat d
  have hnull := mvpoly_eval_null' (genPoly r d) (genPoly_ne_zero r d hr hd)
  have hmeas : NullMeasurableSet {z : Jidx d → ℝ | (MvPolynomial.eval z) (genPoly r d) = 0} :=
    ((MvPolynomial.continuous_eval (genPoly r d)).measurable
      (measurableSet_singleton 0)).nullMeasurableSet
  have hset : {θ : Params d | (MvPolynomial.eval (flat d θ)) (genPoly r d) = 0}
      = flat d ⁻¹' {z | (MvPolynomial.eval z) (genPoly r d) = 0} := rfl
  rw [hset, hmp.measure_preimage hmeas]
  exact hnull

/-! ## Sigmoid toolkit

`sig x = 1 / (1 + exp (-x))`.  The key analytic input for identifying the value
matrices is a linear-independence property of sigmoids with distinct slopes
(`sig_rigidity`), the `m ≤ 2` instance of Lemma `lem:app-sigmoid` of the paper.
Instead of the meromorphic-continuation argument used there, we clear
denominators to obtain an identity between real exponentials with distinct
rates, and prove linear independence of exponentials on `(0, ∞)` algebraically
via a Vandermonde determinant evaluated at `t = 1, 2, …, n`. -/

noncomputable def sig (x : ℝ) : ℝ := (1 + Real.exp (-x))⁻¹

theorem one_add_exp_pos (x : ℝ) : 0 < 1 + Real.exp (-x) := by positivity

theorem one_add_exp_ne_zero (x : ℝ) : 1 + Real.exp (-x) ≠ 0 := (one_add_exp_pos x).ne'

theorem sig_mul_denom (x : ℝ) : sig x * (1 + Real.exp (-x)) = 1 :=
  inv_mul_cancel₀ (one_add_exp_ne_zero x)

/-- Linear independence of real exponentials with pairwise distinct rates, on `(0, ∞)`:
evaluate at `t = 1, …, n` and invert a Vandermonde matrix. -/
theorem exp_sum_eq_zero {n : ℕ} {lam : Fin n → ℝ} (hlam : Function.Injective lam)
    {c : Fin n → ℝ} (h : ∀ t : ℝ, 0 < t → ∑ i, c i * Real.exp (lam i * t) = 0) (i : Fin n) :
    c i = 0 := by
  set x : Fin n → ℝ := fun i => Real.exp (lam i) with hx
  have hxinj : Function.Injective x := fun i j hij => hlam (Real.exp_eq_exp.mp hij)
  have hdet : ((Matrix.vandermonde x)ᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose, Matrix.det_vandermonde]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    exact sub_ne_zero_of_ne (hxinj.ne (Finset.mem_Ioi.mp hj).ne')
  have hmv : (Matrix.vandermonde x)ᵀ.mulVec (fun i => c i * x i) = 0 := by
    funext j
    have hj1 : (0 : ℝ) < (j : ℕ) + 1 := by positivity
    have hsum := h ((j : ℕ) + 1) hj1
    have hterm : ∀ i : Fin n, c i * Real.exp (lam i * ((j : ℕ) + 1))
        = (Matrix.vandermonde x)ᵀ j i * (c i * x i) := by
      intro i
      have harg : lam i * (((j : ℕ) : ℝ) + 1) = (((j : ℕ) + 1 : ℕ) : ℝ) * lam i := by
        push_cast; ring
      have hpow : Real.exp (lam i * (((j : ℕ) : ℝ) + 1)) = x i ^ ((j : ℕ) + 1) := by
        rw [harg, Real.exp_nat_mul]
      rw [hpow, Matrix.transpose_apply, Matrix.vandermonde_apply, pow_succ]
      ring
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← hsum]
    exact (Finset.sum_congr rfl fun i _ => (hterm i).symm)
  have hz := Matrix.eq_zero_of_mulVec_eq_zero hdet hmv
  have hzi := congrFun hz i
  simp only [Pi.zero_apply] at hzi
  rcases mul_eq_zero.mp hzi with hc0 | hx0
  · exact hc0
  · exact absurd hx0 (Real.exp_ne_zero _)

theorem exp_pair_eq_zero {l₁ l₂ c₁ c₂ : ℝ} (h12 : l₁ ≠ l₂)
    (h : ∀ t : ℝ, 0 < t → c₁ * Real.exp (l₁ * t) + c₂ * Real.exp (l₂ * t) = 0) :
    c₁ = 0 ∧ c₂ = 0 := by
  have hinj : Function.Injective ![l₁, l₂] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h' : ∀ t : ℝ, 0 < t → ∑ i, ![c₁, c₂] i * Real.exp (![l₁, l₂] i * t) = 0 := by
    intro t ht
    simpa [Fin.sum_univ_two] using h t ht
  exact ⟨by simpa using exp_sum_eq_zero hinj h' 0,
         by simpa using exp_sum_eq_zero hinj h' 1⟩

theorem exp_triple_eq_zero {l₁ l₂ l₃ c₁ c₂ c₃ : ℝ}
    (h12 : l₁ ≠ l₂) (h13 : l₁ ≠ l₃) (h23 : l₂ ≠ l₃)
    (h : ∀ t : ℝ, 0 < t →
      c₁ * Real.exp (l₁ * t) + c₂ * Real.exp (l₂ * t) + c₃ * Real.exp (l₃ * t) = 0) :
    c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  have hinj : Function.Injective ![l₁, l₂, l₃] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h' : ∀ t : ℝ, 0 < t → ∑ i, ![c₁, c₂, c₃] i * Real.exp (![l₁, l₂, l₃] i * t) = 0 := by
    intro t ht
    simpa [Fin.sum_univ_three] using h t ht
  exact ⟨by simpa using exp_sum_eq_zero hinj h' 0,
         by simpa using exp_sum_eq_zero hinj h' 1,
         by simpa using exp_sum_eq_zero hinj h' 2⟩

theorem exp_quad_eq_zero {l₁ l₂ l₃ l₄ c₁ c₂ c₃ c₄ : ℝ}
    (h12 : l₁ ≠ l₂) (h13 : l₁ ≠ l₃) (h14 : l₁ ≠ l₄)
    (h23 : l₂ ≠ l₃) (h24 : l₂ ≠ l₄) (h34 : l₃ ≠ l₄)
    (h : ∀ t : ℝ, 0 < t →
      c₁ * Real.exp (l₁ * t) + c₂ * Real.exp (l₂ * t)
        + c₃ * Real.exp (l₃ * t) + c₄ * Real.exp (l₄ * t) = 0) :
    c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 ∧ c₄ = 0 := by
  have hinj : Function.Injective ![l₁, l₂, l₃, l₄] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h' : ∀ t : ℝ, 0 < t →
      ∑ i, ![c₁, c₂, c₃, c₄] i * Real.exp (![l₁, l₂, l₃, l₄] i * t) = 0 := by
    intro t ht
    simpa [Fin.sum_univ_four] using h t ht
  exact ⟨by simpa using exp_sum_eq_zero hinj h' 0,
         by simpa using exp_sum_eq_zero hinj h' 1,
         by simpa using exp_sum_eq_zero hinj h' 2,
         by simpa using exp_sum_eq_zero hinj h' 3⟩

/-- A sigmoid with nonzero slope is not affine-constant: if `c * sig (μ t + b) = K` for
all `t > 0` and `μ ≠ 0`, then `c = 0` and `K = 0`. -/
theorem sig_mul_eq_const {b μ c K : ℝ} (hμ : μ ≠ 0)
    (h : ∀ t : ℝ, 0 < t → c * sig (μ * t + b) = K) : c = 0 ∧ K = 0 := by
  set P : ℝ := Real.exp (-b) with hP
  have key : ∀ t : ℝ, 0 < t →
      (c - K) * Real.exp (0 * t) + (-(K * P)) * Real.exp ((-μ) * t) = 0 := by
    intro t ht
    have hs := sig_mul_denom (μ * t + b)
    have e2 : Real.exp (-(μ * t + b)) = P * Real.exp ((-μ) * t) := by
      rw [hP, ← Real.exp_add]
      congr 1
      ring
    rw [e2] at hs
    have heq := h t ht
    have e0 : Real.exp (0 * t) = 1 := by rw [zero_mul, Real.exp_zero]
    rw [e0]
    linear_combination (1 + P * Real.exp ((-μ) * t)) * heq - c * hs
  have hl : (0 : ℝ) ≠ -μ := fun h0 => hμ (by linarith)
  obtain ⟨h1, h2⟩ := exp_pair_eq_zero hl key
  have hPne : P ≠ 0 := Real.exp_ne_zero _
  have hK : K = 0 := by
    have : K * P = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hPne
  exact ⟨by linarith, hK⟩

/-- Affine functions of one fixed nonconstant sigmoid have unique coefficients. -/
theorem sig_affine_inj {b μ a a' c c' : ℝ} (hμ : μ ≠ 0)
    (h : ∀ t : ℝ, 0 < t → a + c * sig (μ * t + b) = a' + c' * sig (μ * t + b)) :
    a = a' ∧ c = c' := by
  have h' : ∀ t : ℝ, 0 < t → (c - c') * sig (μ * t + b) = a' - a := by
    intro t ht
    linear_combination h t ht
  obtain ⟨h1, h2⟩ := sig_mul_eq_const hμ h'
  exact ⟨by linarith, by linarith⟩

/-- Rigidity of two-sigmoid affine identities (the `m ≤ 2` case of Lemma
`lem:app-sigmoid`): if `a + c·σ(μt+b) = a' + c'·σ(μ't+b)` for all `t > 0`, with `b ≠ 0`,
`μ' ≠ 0` and `c' ≠ 0`, then the slopes and coefficients agree. -/
theorem sig_rigidity {b a a' c c' μ μ' : ℝ} (hb : b ≠ 0) (hμ' : μ' ≠ 0) (hc' : c' ≠ 0)
    (h : ∀ t : ℝ, 0 < t → a + c * sig (μ * t + b) = a' + c' * sig (μ' * t + b)) :
    μ = μ' ∧ c = c' ∧ a = a' := by
  have hμμ' : μ = μ' := by
    by_contra hne
    by_cases hμ0 : μ = 0
    · -- the left side is constant in `t`, the right side is not
      have h' : ∀ t : ℝ, 0 < t → c' * sig (μ' * t + b) = a + c * sig b - a' := by
        intro t ht
        have ht' := h t ht
        rw [hμ0, zero_mul, zero_add] at ht'
        linarith
      exact hc' (sig_mul_eq_const hμ' h').1
    · -- clear denominators: an exponential identity with rates 0, -μ, -μ', -(μ+μ')
      set P : ℝ := Real.exp (-b) with hP
      have hPne : P ≠ 0 := Real.exp_ne_zero _
      have hPpos : 0 < P := Real.exp_pos _
      have key : ∀ t : ℝ, 0 < t →
          (a - a' + c - c')
          + ((a - a' - c') * P) * Real.exp ((-μ) * t)
          + ((a - a' + c) * P) * Real.exp ((-μ') * t)
          + ((a - a') * P ^ 2) * (Real.exp ((-μ) * t) * Real.exp ((-μ') * t)) = 0 := by
        intro t ht
        have hs1 := sig_mul_denom (μ * t + b)
        have hs2 := sig_mul_denom (μ' * t + b)
        have e1 : Real.exp (-(μ * t + b)) = P * Real.exp ((-μ) * t) := by
          rw [hP, ← Real.exp_add]
          congr 1
          ring
        have e2 : Real.exp (-(μ' * t + b)) = P * Real.exp ((-μ') * t) := by
          rw [hP, ← Real.exp_add]
          congr 1
          ring
        rw [e1] at hs1
        rw [e2] at hs2
        have heq := h t ht
        linear_combination
          ((1 + P * Real.exp ((-μ) * t)) * (1 + P * Real.exp ((-μ') * t))) * heq
          - (c * (1 + P * Real.exp ((-μ') * t))) * hs1
          + (c' * (1 + P * Real.exp ((-μ) * t))) * hs2
      by_cases hsum : μ + μ' = 0
      · -- rates collapse to {0, μ', -μ'}
        have hμval : μ = -μ' := by linarith
        subst hμval
        simp only [neg_neg] at key
        have key3 : ∀ t : ℝ, 0 < t →
            ((a - a' + c - c') + (a - a') * P ^ 2) * Real.exp (0 * t)
            + ((a - a' - c') * P) * Real.exp (μ' * t)
            + ((a - a' + c) * P) * Real.exp ((-μ') * t) = 0 := by
          intro t ht
          have hk := key t ht
          have hqr : Real.exp (μ' * t) * Real.exp ((-μ') * t) = 1 := by
            rw [← Real.exp_add]
            rw [show μ' * t + (-μ') * t = 0 by ring, Real.exp_zero]
          have e0 : Real.exp (0 * t) = 1 := by rw [zero_mul, Real.exp_zero]
          rw [e0]
          linear_combination hk - ((a - a') * P ^ 2) * hqr
        have hl1 : (0 : ℝ) ≠ μ' := Ne.symm hμ'
        have hl2 : (0 : ℝ) ≠ -μ' := fun h0 => hμ' (by linarith)
        have hl3 : μ' ≠ -μ' := fun h0 => hμ' (by linarith)
        obtain ⟨h0, h1, h2⟩ := exp_triple_eq_zero hl1 hl2 hl3 key3
        have ha1 : a - a' - c' = 0 := (mul_eq_zero.mp h1).resolve_right hPne
        have ha2 : a - a' + c = 0 := (mul_eq_zero.mp h2).resolve_right hPne
        have hc'P : c' * (P ^ 2 - 1) = 0 := by
          linear_combination h0 - ha2 - P ^ 2 * ha1
        have hP2 : P ^ 2 - 1 = 0 := (mul_eq_zero.mp hc'P).resolve_left hc'
        have hP1 : P = 1 := by nlinarith
        have hb0 : -b = 0 := by
          have h1 : Real.exp (-b) = Real.exp 0 := by
            rw [Real.exp_zero, ← hP]; exact hP1
          exact Real.exp_eq_exp.mp h1
        exact hb (by linarith)
      · -- four pairwise distinct rates
        have key4 : ∀ t : ℝ, 0 < t →
            (a - a' + c - c') * Real.exp (0 * t)
            + ((a - a' - c') * P) * Real.exp ((-μ) * t)
            + ((a - a' + c) * P) * Real.exp ((-μ') * t)
            + ((a - a') * P ^ 2) * Real.exp ((-(μ + μ')) * t) = 0 := by
          intro t ht
          have hk := key t ht
          have hqr : Real.exp ((-(μ + μ')) * t)
              = Real.exp ((-μ) * t) * Real.exp ((-μ') * t) := by
            rw [← Real.exp_add]
            congr 1
            ring
          have e0 : Real.exp (0 * t) = 1 := by rw [zero_mul, Real.exp_zero]
          rw [e0, hqr]
          linear_combination hk
        have hl12 : (0 : ℝ) ≠ -μ := fun h0 => hμ0 (by linarith)
        have hl13 : (0 : ℝ) ≠ -μ' := fun h0 => hμ' (by linarith)
        have hl14 : (0 : ℝ) ≠ -(μ + μ') := fun h0 => hsum (by linarith)
        have hl23 : -μ ≠ -μ' := fun h0 => hne (by linarith)
        have hl24 : -μ ≠ -(μ + μ') := fun h0 => hμ' (by linarith)
        have hl34 : -μ' ≠ -(μ + μ') := fun h0 => hμ0 (by linarith)
        obtain ⟨h0, h1, h2, h3⟩ := exp_quad_eq_zero hl12 hl13 hl14 hl23 hl24 hl34 key4
        have ha1 : a - a' - c' = 0 := (mul_eq_zero.mp h1).resolve_right hPne
        have ha3 : a - a' = 0 := by
          have := (mul_eq_zero.mp h3).resolve_right (pow_ne_zero 2 hPne)
          linarith
        exact hc' (by linarith)
  subst hμμ'
  obtain ⟨ha, hc⟩ := sig_affine_inj hμ' h
  exact ⟨rfl, hc, ha⟩

/-! ## Two-type inputs and the layer closure formula

A *two-type* input has `r` identical "context" columns `c • u` followed by a single
"query" column `c • v` (in the paper, `c = √τ`).  The key structural fact
(Lemma `lem:app-causal-twotype`) is that a causal attention layer maps two-type
inputs to two-type inputs, with
`u ↦ u + Vu` and `v ↦ v + Vv + σ(c²·(u-v)ᵀAv + log r) • V(u-v)`. -/

noncomputable def twoType (r d : ℕ) (u v : Fin d → ℝ) (c : ℝ) :
    Matrix (Fin d) (Fin (r + 1)) ℝ :=
  Matrix.of fun i j => if (j : ℕ) < r then c * u i else c * v i

theorem twoType_apply_lt {r d : ℕ} {u v : Fin d → ℝ} {c : ℝ} (i : Fin d) {j : Fin (r + 1)}
    (hj : (j : ℕ) < r) : twoType r d u v c i j = c * u i := if_pos hj

theorem twoType_apply_not_lt {r d : ℕ} {u v : Fin d → ℝ} {c : ℝ} (i : Fin d) {j : Fin (r + 1)}
    (hj : ¬ (j : ℕ) < r) : twoType r d u v c i j = c * v i := if_neg hj

theorem causalSoftmax_apply {T : ℕ} (M : Matrix (Fin T) (Fin T) ℝ) (i j : Fin T) :
    causalSoftmax M i j
      = if i ≤ j then Real.exp (M i j) / ∑ i' ∈ Finset.Iic j, Real.exp (M i' j) else 0 := rfl

/-- Entry of the score matrix `Xᵀ A X` as a double sum. -/
theorem quadform_apply {d T : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin T) ℝ) (i j : Fin T) :
    (Xᵀ * A * X) i j = ∑ a, ∑ b, X a i * A a b * X b j := by
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- Scores of a two-type input are determined by the column types. -/
theorem twoType_score {r d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ) (c : ℝ)
    (i j : Fin (r + 1)) :
    ((twoType r d u v c)ᵀ * A * twoType r d u v c) i j
      = c ^ 2 * ((if (i : ℕ) < r then u else v) ⬝ᵥ
          A.mulVec (if (j : ℕ) < r then u else v)) := by
  rw [quadform_apply]
  have hXi : ∀ a, twoType r d u v c a i = c * (if (i : ℕ) < r then u else v) a := by
    intro a
    by_cases h : (i : ℕ) < r
    · rw [twoType_apply_lt a h, if_pos h]
    · rw [twoType_apply_not_lt a h, if_neg h]
  have hXj : ∀ b, twoType r d u v c b j = c * (if (j : ℕ) < r then u else v) b := by
    intro b
    by_cases h : (j : ℕ) < r
    · rw [twoType_apply_lt b h, if_pos h]
    · rw [twoType_apply_not_lt b h, if_neg h]
  simp_rw [hXi, hXj, dotProduct, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Row of `V * X` for a two-type input `X`. -/
theorem mul_twoType_apply {r d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ)
    (c : ℝ) (i : Fin d) (k : Fin (r + 1)) :
    (V * twoType r d u v c) i k
      = c * (V.mulVec (if (k : ℕ) < r then u else v)) i := by
  rw [Matrix.mul_apply]
  have hXk : ∀ a, twoType r d u v c a k = c * (if (k : ℕ) < r then u else v) a := by
    intro a
    by_cases h : (k : ℕ) < r
    · rw [twoType_apply_lt a h, if_pos h]
    · rw [twoType_apply_not_lt a h, if_neg h]
  simp_rw [hXk, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- Causal softmax weights at a context column are uniform. -/
theorem causalSoftmax_twoType_lt {r d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (c : ℝ) {j : Fin (r + 1)} (hj : (j : ℕ) < r) (i : Fin (r + 1)) :
    causalSoftmax ((twoType r d u v c)ᵀ * A * twoType r d u v c) i j
      = if i ≤ j then (((j : ℕ) : ℝ) + 1)⁻¹ else 0 := by
  have hscore : ∀ i' : Fin (r + 1), i' ≤ j →
      ((twoType r d u v c)ᵀ * A * twoType r d u v c) i' j
        = c ^ 2 * (u ⬝ᵥ A.mulVec u) := by
    intro i' hi'
    have hi'r : (i' : ℕ) < r := lt_of_le_of_lt hi' hj
    rw [twoType_score, if_pos hi'r, if_pos hj]
  rw [causalSoftmax_apply]
  by_cases hij : i ≤ j
  · rw [if_pos hij, if_pos hij, hscore i hij]
    have hden : ∑ i' ∈ Finset.Iic j,
        Real.exp (((twoType r d u v c)ᵀ * A * twoType r d u v c) i' j)
        = (((j : ℕ) : ℝ) + 1) * Real.exp (c ^ 2 * (u ⬝ᵥ A.mulVec u)) := by
      rw [Finset.sum_congr rfl
        (fun i' hi' => by rw [hscore i' (Finset.mem_Iic.mp hi')])]
      rw [Finset.sum_const, Fin.card_Iic, nsmul_eq_mul]
      push_cast
      ring
    rw [hden]
    have hexp := Real.exp_ne_zero (c ^ 2 * (u ⬝ᵥ A.mulVec u))
    have hj1 : (((j : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  · rw [if_neg hij, if_neg hij]

/-- **Layer closure** (Lemma `lem:app-causal-twotype`): a causal attention layer maps a
two-type input to a two-type input. -/
theorem attnLayer_twoType {r d : ℕ} (hr : 0 < r) (V A : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (c : ℝ) :
    attnLayer V A (twoType r d u v c)
      = twoType r d (u + V.mulVec u)
          (v + V.mulVec v
            + sig (c ^ 2 * ((u - v) ⬝ᵥ A.mulVec v) + Real.log r) • V.mulVec (u - v)) c := by
  ext i j
  rw [attnLayer, Matrix.add_apply]
  by_cases hj : (j : ℕ) < r
  · -- context column: uniform causal weights over `j + 1` identical keys
    rw [twoType_apply_lt i hj, twoType_apply_lt i hj, Matrix.mul_apply]
    have hcs : ∀ k : Fin (r + 1),
        (V * twoType r d u v c) i k
          * causalSoftmax ((twoType r d u v c)ᵀ * A * twoType r d u v c) k j
        = if k ≤ j then c * (V.mulVec u) i * (((j : ℕ) : ℝ) + 1)⁻¹ else 0 := by
      intro k
      rw [causalSoftmax_twoType_lt A u v c hj k]
      by_cases hk : k ≤ j
      · have hkr : (k : ℕ) < r := lt_of_le_of_lt (Fin.le_def.mp hk) hj
        rw [if_pos hk, if_pos hk, mul_twoType_apply, if_pos hkr]
      · rw [if_neg hk, if_neg hk, mul_zero]
    simp_rw [hcs]
    have hfilter : Finset.filter (fun k : Fin (r + 1) => k ≤ j) Finset.univ
        = Finset.Iic j := by
      ext k
      simp [Finset.mem_Iic]
    rw [← Finset.sum_filter, hfilter, Finset.sum_const, Fin.card_Iic, nsmul_eq_mul]
    have hj1 : (((j : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    rw [Pi.add_apply]
    push_cast
    field_simp
    try ring
  · -- query column: `j` is the last column
    have hjlast : j = Fin.last r := by
      apply Fin.ext
      have := j.isLt
      simp only [Fin.val_last]
      omega
    subst hjlast
    rw [twoType_apply_not_lt i hj, twoType_apply_not_lt i hj, Matrix.mul_apply]
    set suv : ℝ := c ^ 2 * (u ⬝ᵥ A.mulVec v) with hsuv
    set svv : ℝ := c ^ 2 * (v ⬝ᵥ A.mulVec v) with hsvv
    have hS : ∀ k : Fin (r + 1),
        ((twoType r d u v c)ᵀ * A * twoType r d u v c) k (Fin.last r)
          = if (k : ℕ) < r then suv else svv := by
      intro k
      rw [twoType_score, if_neg hj]
      by_cases hk : (k : ℕ) < r
      · rw [if_pos hk, if_pos hk, hsuv]
      · rw [if_neg hk, if_neg hk, hsvv]
    have hIic : Finset.Iic (Fin.last r) = (Finset.univ : Finset (Fin (r + 1))) := by
      ext k
      simp [Finset.mem_Iic, Fin.le_last]
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    set D : ℝ := (r : ℝ) * Real.exp suv + Real.exp svv with hD
    have hDval : ∑ i' ∈ Finset.Iic (Fin.last r),
        Real.exp (((twoType r d u v c)ᵀ * A * twoType r d u v c) i' (Fin.last r)) = D := by
      rw [hIic, Fin.sum_univ_castSucc]
      have h1 : ∀ k : Fin r,
          Real.exp (((twoType r d u v c)ᵀ * A * twoType r d u v c) k.castSucc (Fin.last r))
            = Real.exp suv := by
        intro k
        rw [hS, if_pos (by simp)]
      have h2 : Real.exp
          (((twoType r d u v c)ᵀ * A * twoType r d u v c) (Fin.last r) (Fin.last r))
            = Real.exp svv := by
        rw [hS, if_neg (by simp)]
      simp_rw [h1]
      rw [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hD]
    set s : ℝ := sig (c ^ 2 * ((u - v) ⬝ᵥ A.mulVec v) + Real.log r) with hs
    have hsig_arg : c ^ 2 * ((u - v) ⬝ᵥ A.mulVec v) + Real.log (r : ℝ)
        = suv - svv + Real.log (r : ℝ) := by
      rw [hsuv, hsvv, sub_dotProduct]
      ring
    have hexplog : Real.exp (Real.log (r : ℝ)) = (r : ℝ) := Real.exp_log hrpos
    have hkey : Real.exp (-(suv - svv + Real.log (r : ℝ))) * ((r : ℝ) * Real.exp suv)
        = Real.exp svv := by
      rw [show -(suv - svv + Real.log (r : ℝ)) = svv + -suv + -Real.log (r : ℝ) by ring,
        Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_neg, hexplog]
      field_simp
    have hsD : s * D = (r : ℝ) * Real.exp suv := by
      rw [hs, hsig_arg, hD]
      have hd := sig_mul_denom (suv - svv + Real.log (r : ℝ))
      linear_combination ((r : ℝ) * Real.exp suv) * hd
        - sig (suv - svv + Real.log (r : ℝ)) * hkey
    have hDpos : 0 < D := by
      rw [hD]
      have h1 : 0 < (r : ℝ) * Real.exp suv := mul_pos hrpos (Real.exp_pos _)
      have h2 : 0 < Real.exp svv := Real.exp_pos _
      linarith
    have hw1 : (r : ℝ) * (Real.exp suv / D) = s := by
      rw [← mul_div_assoc, div_eq_iff hDpos.ne']
      linear_combination -hsD
    have hw2 : Real.exp svv / D = 1 - s := by
      rw [div_eq_iff hDpos.ne']
      linear_combination hsD - hD
    have hterm : ∀ k : Fin (r + 1),
        (V * twoType r d u v c) i k
          * causalSoftmax ((twoType r d u v c)ᵀ * A * twoType r d u v c) k (Fin.last r)
        = (if (k : ℕ) < r then c * (V.mulVec u) i * (Real.exp suv / D)
           else c * (V.mulVec v) i * (Real.exp svv / D)) := by
      intro k
      rw [causalSoftmax_apply, if_pos (Fin.le_last k), hDval, hS, mul_twoType_apply]
      by_cases hk : (k : ℕ) < r
      · rw [if_pos hk, if_pos hk, if_pos hk]
      · rw [if_neg hk, if_neg hk, if_neg hk]
    simp_rw [hterm]
    rw [Fin.sum_univ_castSucc]
    have hcast : ∀ k : Fin r,
        (if ((k.castSucc : Fin (r + 1)) : ℕ) < r
          then c * (V.mulVec u) i * (Real.exp suv / D)
          else c * (V.mulVec v) i * (Real.exp svv / D))
        = c * (V.mulVec u) i * (Real.exp suv / D) :=
      fun k => if_pos (by simp)
    simp_rw [hcast]
    rw [if_neg (show ¬ ((Fin.last r : Fin (r + 1)) : ℕ) < r by simp)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec_sub, Pi.sub_apply]
    linear_combination (c * (V.mulVec u) i) * hw1 + (c * (V.mulVec v) i) * hw2

/-- The complement of the zero set of a nonzero polynomial is (Euclidean) dense. -/
theorem dense_compl_zero_set {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) :
    Dense {x : ι → ℝ | (MvPolynomial.eval x) p ≠ 0} := by
  have hcompl : {x : ι → ℝ | (MvPolynomial.eval x) p ≠ 0}
      = {x : ι → ℝ | (MvPolynomial.eval x) p = 0}ᶜ := rfl
  rw [hcompl, ← interior_eq_empty_iff_dense_compl]
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hpos : 0 < volume (interior {x : ι → ℝ | (MvPolynomial.eval x) p = 0}) :=
    isOpen_interior.measure_pos volume ⟨x, hx⟩
  have hle : volume (interior {x : ι → ℝ | (MvPolynomial.eval x) p = 0})
      ≤ volume {x : ι → ℝ | (MvPolynomial.eval x) p = 0} := measure_mono interior_subset
  rw [mvpoly_eval_null' p hp, nonpos_iff_eq_zero] at hle
  exact hpos.ne' hle

/-- `sig (log r) = r / (r + 1) = α`, the uniform causal weight on the context block. -/
theorem sig_log {r : ℕ} (hr : 0 < r) : sig (Real.log r) = (r : ℝ) / ((r : ℝ) + 1) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  rw [sig, Real.exp_neg, Real.exp_log hrpos]
  rw [eq_div_iff (by positivity)]
  field_simp

/-- **Two-layer closure on two-type inputs.** Applying `attnLayer_twoType` twice gives the
full two-layer network output on a two-type input, again in two-type form. -/
theorem network_twoType {r d : ℕ} (hr : 0 < r) (V₁ A₁ V₂ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (c : ℝ) :
    network ((V₁, A₁), (V₂, A₂)) (twoType r d u v c)
      = twoType r d
          ((u + V₁.mulVec u) + V₂.mulVec (u + V₁.mulVec u))
          ((v + V₁.mulVec v
              + sig (c ^ 2 * ((u - v) ⬝ᵥ A₁.mulVec v) + Real.log r) • V₁.mulVec (u - v))
            + V₂.mulVec (v + V₁.mulVec v
                + sig (c ^ 2 * ((u - v) ⬝ᵥ A₁.mulVec v) + Real.log r) • V₁.mulVec (u - v))
            + sig (c ^ 2 * (((u + V₁.mulVec u)
                  - (v + V₁.mulVec v
                      + sig (c ^ 2 * ((u - v) ⬝ᵥ A₁.mulVec v) + Real.log r) • V₁.mulVec (u - v)))
                ⬝ᵥ A₂.mulVec (v + V₁.mulVec v
                  + sig (c ^ 2 * ((u - v) ⬝ᵥ A₁.mulVec v) + Real.log r) • V₁.mulVec (u - v)))
                + Real.log r)
              • V₂.mulVec ((u + V₁.mulVec u)
                  - (v + V₁.mulVec v
                      + sig (c ^ 2 * ((u - v) ⬝ᵥ A₁.mulVec v) + Real.log r) • V₁.mulVec (u - v))))
          c := by
  simp only [network]
  rw [attnLayer_twoType hr, attnLayer_twoType hr]

/-- The query (final) column of a two-type input is `c` times its query vector. -/
theorem twoType_query {r d : ℕ} (u v : Fin d → ℝ) (c : ℝ) (i : Fin d) :
    twoType r d u v c i (Fin.last r) = c * v i :=
  twoType_apply_not_lt i (by simp)

/-- The query column of the two-layer network on a two-type input with `v = 0`.
With `α = r/(r+1)` and `β = 1/(r+1)`, the rescaled query vector is
`α·(I+V₂)V₁ u + σ(μ(u)·c² + log r)·V₂(I+βV₁) u`, where
`μ(u) = α·⟨(I+βV₁)u, A₂ V₁ u⟩`. -/
theorem twoLayer_query_v0 {r d : ℕ} (hr : 0 < r) (V₁ A₁ V₂ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (u : Fin d → ℝ) (c : ℝ) :
    (fun i => network ((V₁, A₁), (V₂, A₂)) (twoType r d u 0 c) i (Fin.last r))
      = c • (((r : ℝ) / ((r : ℝ) + 1)) • ((1 + V₂) * V₁).mulVec u
          + sig ((r : ℝ) / ((r : ℝ) + 1)
                * ((1 + ((r : ℝ) + 1)⁻¹ • V₁).mulVec u ⬝ᵥ A₂.mulVec (V₁.mulVec u)) * c ^ 2
                + Real.log r)
              • (V₂ * (1 + ((r : ℝ) + 1)⁻¹ • V₁)).mulVec u) := by
  have hsl : sig (Real.log r) = (r : ℝ) / ((r : ℝ) + 1) := sig_log hr
  set α : ℝ := (r : ℝ) / ((r : ℝ) + 1) with hα
  set β : ℝ := ((r : ℝ) + 1)⁻¹ with hβ
  funext i
  rw [network_twoType hr, twoType_query]
  -- abbreviations after substituting `v = 0`
  simp only [Matrix.mulVec_zero, sub_zero, dotProduct_zero, mul_zero, zero_add, add_zero, hsl]
  rw [Pi.smul_apply, smul_eq_mul]
  -- the layer-1 query vector is `α • V₁ u`; assemble both terms
  have e1 : α • V₁.mulVec u + V₂.mulVec (α • V₁.mulVec u) = α • ((1 + V₂) * V₁).mulVec u := by
    rw [Matrix.mulVec_smul, ← smul_add, ← Matrix.mulVec_mulVec, Matrix.add_mulVec,
      Matrix.one_mulVec]
  have e2 : (u + V₁.mulVec u) - α • V₁.mulVec u = (1 + β • V₁).mulVec u := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    have hαβ : (1 : ℝ) - α = β := by
      rw [hα, hβ]; field_simp; ring
    rw [show u + V₁.mulVec u - α • V₁.mulVec u
        = u + ((1 : ℝ) - α) • V₁.mulVec u by module, hαβ]
  rw [e2]
  have e3 : V₂.mulVec ((1 + β • V₁).mulVec u) = (V₂ * (1 + β • V₁)).mulVec u :=
    Matrix.mulVec_mulVec u V₂ (1 + β • V₁)
  rw [e3]
  -- the sigmoid argument
  have harg : c ^ 2 * ((1 + β • V₁).mulVec u ⬝ᵥ A₂.mulVec (α • V₁.mulVec u)) + Real.log r
      = α * ((1 + β • V₁).mulVec u ⬝ᵥ A₂.mulVec (V₁.mulVec u)) * c ^ 2 + Real.log r := by
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    ring
  rw [harg, e1]

/-- The query column on a two-type input with `u = v`: the network acts linearly,
giving `(I+V₂)(I+V₁) v`. -/
theorem twoLayer_query_uv {r d : ℕ} (hr : 0 < r) (V₁ A₁ V₂ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (v : Fin d → ℝ) (c : ℝ) :
    (fun i => network ((V₁, A₁), (V₂, A₂)) (twoType r d v v c) i (Fin.last r))
      = c • ((1 + V₂) * (1 + V₁)).mulVec v := by
  funext i
  rw [network_twoType hr, twoType_query]
  simp only [sub_self, Matrix.mulVec_zero, smul_zero, add_zero]
  rw [Pi.smul_apply, smul_eq_mul]
  have hw : (1 + V₁).mulVec v = v + V₁.mulVec v := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
  have hR : ((1 + V₂) * (1 + V₁)).mulVec v
      = (v + V₁.mulVec v) + V₂.mulVec (v + V₁.mulVec v) := by
    rw [← Matrix.mulVec_mulVec, hw, Matrix.add_mulVec, Matrix.one_mulVec]
  rw [hR]

/-! ## Plumbing for the genericity/density argument in `identify_V` -/

/-- A matrix is determined by its action on all vectors. -/
theorem matrix_ext_mulVec {d : ℕ} {M N : Matrix (Fin d) (Fin d) ℝ}
    (h : ∀ u, M.mulVec u = N.mulVec u) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using this

/-- Evaluating a polynomial-matrix `(M.map C) *ᵥ w` at a real point commutes with
evaluating its vector argument `w`. -/
theorem eval_mapMat_mulVec {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → MvPolynomial (Fin d) ℝ) (u : Fin d → ℝ) (i : Fin d) :
    MvPolynomial.eval u (((M.map (MvPolynomial.C : ℝ →+* MvPolynomial (Fin d) ℝ)) *ᵥ w) i)
      = (M.mulVec (fun j => MvPolynomial.eval u (w j))) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, MvPolynomial.eval_C]

/-- Evaluation commutes with dot products of polynomial vectors. -/
theorem eval_dotProduct {d : ℕ} (u : Fin d → ℝ)
    (a b : Fin d → MvPolynomial (Fin d) ℝ) :
    MvPolynomial.eval u (a ⬝ᵥ b)
      = (fun i => MvPolynomial.eval u (a i)) ⬝ᵥ (fun i => MvPolynomial.eval u (b i)) := by
  simp only [dotProduct, map_sum, map_mul]

/-- The "double" quadratic form on standard basis vectors picks out a matrix entry. -/
theorem quadform_basis {d : ℕ} (B A V : Matrix (Fin d) (Fin d) ℝ) (j k : Fin d) :
    (B.mulVec (Pi.single j 1)) ⬝ᵥ (A.mulVec (V.mulVec (Pi.single k 1)))
      = (Bᵀ * A * V) j k := by
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.col_apply,
    Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **Identification of the value products** (Lemma `lem:app-causal-identify-v`):
if a parameter `(V₁', A₁', V₂', A₂')` satisfies the two genericity conditions
`(V₂'(1+βV₁'))₀₀ ≠ 0` and `((1+βV₁')ᵀA₂'V₁')₀₀ ≠ 0` (with `β = 1/(r+1)`), and an
arbitrary parameter induces the same network function on all two-type inputs, then the
value products agree: `V₁ = V₁'` and `V₂ = V₂'`. -/
theorem identify_V {r d : ℕ} [NeZero d] (hr : 2 ≤ r)
    {V₁ A₁ V₂ A₂ V₁' A₁' V₂' A₂' : Matrix (Fin d) (Fin d) ℝ}
    (hQ : (V₂' * (1 + (((r : ℝ) + 1)⁻¹) • V₁') : Matrix (Fin d) (Fin d) ℝ) 0 0 ≠ 0)
    (hM : ((1 + (((r : ℝ) + 1)⁻¹) • V₁')ᵀ * A₂' * V₁' : Matrix (Fin d) (Fin d) ℝ) 0 0 ≠ 0)
    (hagree : ∀ (u v : Fin d → ℝ) (c : ℝ),
      network ((V₁, A₁), (V₂, A₂)) (twoType r d u v c)
        = network ((V₁', A₁'), (V₂', A₂')) (twoType r d u v c)) :
    V₁ = V₁' ∧ V₂ = V₂' := by
  have hr0 : 0 < r := by omega
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  have hα0 : (r : ℝ) / ((r : ℝ) + 1) ≠ 0 := (div_pos hrR (by linarith)).ne'
  have hβ0 : ((r : ℝ) + 1)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  have hb : Real.log (r : ℝ) ≠ 0 := by
    have : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
    exact (Real.log_pos this).ne'
  -- ## Step 1: the scalar sigmoid identity from the `v = 0` two-type inputs.
  have hscal : ∀ (u : Fin d → ℝ) (i : Fin d) (t : ℝ), 0 < t →
      (r : ℝ) / ((r : ℝ) + 1) * (((1 + V₂) * V₁).mulVec u) i
        + (((V₂ * (1 + ((r : ℝ) + 1)⁻¹ • V₁)).mulVec u) i)
          * sig ((r : ℝ) / ((r : ℝ) + 1)
              * ((1 + ((r : ℝ) + 1)⁻¹ • V₁).mulVec u ⬝ᵥ A₂.mulVec (V₁.mulVec u)) * t + Real.log r)
      = (r : ℝ) / ((r : ℝ) + 1) * (((1 + V₂') * V₁').mulVec u) i
        + (((V₂' * (1 + ((r : ℝ) + 1)⁻¹ • V₁')).mulVec u) i)
          * sig ((r : ℝ) / ((r : ℝ) + 1)
              * ((1 + ((r : ℝ) + 1)⁻¹ • V₁').mulVec u ⬝ᵥ A₂'.mulVec (V₁'.mulVec u)) * t
              + Real.log r) := by
    intro u i t ht
    have hc0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
    have hc2 : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
    have hvec : (fun i => network ((V₁, A₁), (V₂, A₂)) (twoType r d u 0 (Real.sqrt t)) i (Fin.last r))
        = (fun i => network ((V₁', A₁'), (V₂', A₂')) (twoType r d u 0 (Real.sqrt t)) i (Fin.last r)) := by
      rw [hagree]
    rw [twoLayer_query_v0 hr0, twoLayer_query_v0 hr0] at hvec
    have hi := congrFun hvec i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    have key := mul_left_cancel₀ hc0 hi
    rw [hc2] at key
    linear_combination key
  -- ## Step 2: the genericity polynomial in the input variable `u`.
  set gen : Fin d → MvPolynomial (Fin d) ℝ := fun j => MvPolynomial.X j with hgen_def
  have hgen : ∀ u, (fun j => MvPolynomial.eval u (gen j)) = u := by
    intro u; funext j; simp [hgen_def, MvPolynomial.eval_X]
  set p_mu : MvPolynomial (Fin d) ℝ :=
    MvPolynomial.C ((r : ℝ) / ((r : ℝ) + 1))
      * (((1 + ((r : ℝ) + 1)⁻¹ • V₁').map MvPolynomial.C *ᵥ gen)
          ⬝ᵥ (A₂'.map MvPolynomial.C *ᵥ (V₁'.map MvPolynomial.C *ᵥ gen))) with hp_mu_def
  set p_q : MvPolynomial (Fin d) ℝ :=
    ((V₂' * (1 + ((r : ℝ) + 1)⁻¹ • V₁')).map MvPolynomial.C *ᵥ gen) 0 with hp_q_def
  have heval_mu : ∀ u, MvPolynomial.eval u p_mu
      = (r : ℝ) / ((r : ℝ) + 1)
          * ((1 + ((r : ℝ) + 1)⁻¹ • V₁').mulVec u ⬝ᵥ A₂'.mulVec (V₁'.mulVec u)) := by
    intro u
    have ha : (fun i => MvPolynomial.eval u
          (((1 + ((r : ℝ) + 1)⁻¹ • V₁').map MvPolynomial.C *ᵥ gen) i))
        = (1 + ((r : ℝ) + 1)⁻¹ • V₁').mulVec u := by
      funext i; rw [eval_mapMat_mulVec, hgen u]
    have hbv : (fun i => MvPolynomial.eval u
          ((A₂'.map MvPolynomial.C *ᵥ (V₁'.map MvPolynomial.C *ᵥ gen)) i))
        = A₂'.mulVec (V₁'.mulVec u) := by
      funext i; rw [eval_mapMat_mulVec]
      have hvj : (fun j => MvPolynomial.eval u ((V₁'.map MvPolynomial.C *ᵥ gen) j))
          = V₁'.mulVec u := by
        funext j; rw [eval_mapMat_mulVec, hgen u]
      rw [hvj]
    rw [hp_mu_def, map_mul, MvPolynomial.eval_C, eval_dotProduct, ha, hbv]
  have heval_q : ∀ u, MvPolynomial.eval u p_q
      = ((V₂' * (1 + ((r : ℝ) + 1)⁻¹ • V₁')).mulVec u) 0 := by
    intro u; rw [hp_q_def, eval_mapMat_mulVec, hgen u]
  have hp_mu : p_mu ≠ 0 := by
    intro h0
    apply hM
    have hz : MvPolynomial.eval (Pi.single 0 1) p_mu = 0 := by rw [h0]; simp
    rw [heval_mu, quadform_basis] at hz
    exact (mul_eq_zero.mp hz).resolve_left hα0
  have hp_q : p_q ≠ 0 := by
    intro h0
    apply hQ
    have hz : MvPolynomial.eval (Pi.single 0 1) p_q = 0 := by rw [h0]; simp
    rw [heval_q, Matrix.mulVec_single_one, Matrix.col_apply] at hz
    exact hz
  set p : MvPolynomial (Fin d) ℝ := p_mu * p_q with hp_def
  have hp : p ≠ 0 := mul_ne_zero hp_mu hp_q
  have hdense : Dense {u : Fin d → ℝ | MvPolynomial.eval u p ≠ 0} := dense_compl_zero_set p hp
  -- ## Step 3: on the dense good set, the two value products agree pointwise.
  have hfacts : ∀ u, MvPolynomial.eval u p ≠ 0 →
      (((1 + V₂) * V₁).mulVec u = ((1 + V₂') * V₁').mulVec u
        ∧ (V₂ * (1 + ((r : ℝ) + 1)⁻¹ • V₁)).mulVec u
            = (V₂' * (1 + ((r : ℝ) + 1)⁻¹ • V₁')).mulVec u) := by
    intro u hu
    rw [hp_def, map_mul, heval_mu, heval_q] at hu
    have hμ' : (r : ℝ) / ((r : ℝ) + 1)
        * ((1 + ((r : ℝ) + 1)⁻¹ • V₁').mulVec u ⬝ᵥ A₂'.mulVec (V₁'.mulVec u)) ≠ 0 :=
      fun h => hu (by rw [h, zero_mul])
    have hq' : ((V₂' * (1 + ((r : ℝ) + 1)⁻¹ • V₁')).mulVec u) 0 ≠ 0 :=
      fun h => hu (by rw [h, mul_zero])
    have hsl_eq := (sig_rigidity hb hμ' hq' (hscal u 0)).1
    constructor
    · funext i
      have hi := hscal u i
      rw [hsl_eq] at hi
      exact mul_left_cancel₀ hα0 (sig_affine_inj hμ' hi).1
    · funext i
      have hi := hscal u i
      rw [hsl_eq] at hi
      exact (sig_affine_inj hμ' hi).2
  -- ## Step 4: globalise by continuity to matrix equalities.
  have hPP : (1 + V₂) * V₁ = (1 + V₂') * V₁' := by
    apply matrix_ext_mulVec
    have hfun : (fun u => ((1 + V₂) * V₁).mulVec u) = (fun u => ((1 + V₂') * V₁').mulVec u) :=
      Continuous.ext_on hdense (Continuous.matrix_mulVec continuous_const continuous_id)
        (Continuous.matrix_mulVec continuous_const continuous_id)
        (fun u hu => (hfacts u hu).1)
    exact fun u => congrFun hfun u
  have hQQ : V₂ * (1 + ((r : ℝ) + 1)⁻¹ • V₁) = V₂' * (1 + ((r : ℝ) + 1)⁻¹ • V₁') := by
    apply matrix_ext_mulVec
    have hfun : (fun u => (V₂ * (1 + ((r : ℝ) + 1)⁻¹ • V₁)).mulVec u)
        = (fun u => (V₂' * (1 + ((r : ℝ) + 1)⁻¹ • V₁')).mulVec u) :=
      Continuous.ext_on hdense (Continuous.matrix_mulVec continuous_const continuous_id)
        (Continuous.matrix_mulVec continuous_const continuous_id)
        (fun u hu => (hfacts u hu).2)
    exact fun u => congrFun hfun u
  have hRR : (1 + V₂) * (1 + V₁) = (1 + V₂') * (1 + V₁') := by
    apply matrix_ext_mulVec
    intro v
    have hvec : (fun i => network ((V₁, A₁), (V₂, A₂)) (twoType r d v v 1) i (Fin.last r))
        = (fun i => network ((V₁', A₁'), (V₂', A₂')) (twoType r d v v 1) i (Fin.last r)) := by
      rw [hagree]
    rw [twoLayer_query_uv hr0, twoLayer_query_uv hr0] at hvec
    simpa using hvec
  -- ## Step 5: linear algebra recovers `V₁` and `V₂`.
  have hV2 : V₂ = V₂' := by
    have lhs : (1 : Matrix (Fin d) (Fin d) ℝ) + V₂ = (1 + V₂) * (1 + V₁) - (1 + V₂) * V₁ := by
      rw [mul_add, mul_one, add_sub_cancel_right]
    have rhs : (1 : Matrix (Fin d) (Fin d) ℝ) + V₂' = (1 + V₂') * (1 + V₁') - (1 + V₂') * V₁' := by
      rw [mul_add, mul_one, add_sub_cancel_right]
    have h12 : (1 : Matrix (Fin d) (Fin d) ℝ) + V₂ = 1 + V₂' := by rw [lhs, rhs, hRR, hPP]
    exact add_left_cancel h12
  have hV1 : V₁ = V₁' := by
    have hQexp : V₂ * (1 + ((r : ℝ) + 1)⁻¹ • V₁) = V₂ + ((r : ℝ) + 1)⁻¹ • (V₂ * V₁) := by
      rw [mul_add, mul_one, Matrix.mul_smul]
    have hQexp' : V₂' * (1 + ((r : ℝ) + 1)⁻¹ • V₁') = V₂' + ((r : ℝ) + 1)⁻¹ • (V₂' * V₁') := by
      rw [mul_add, mul_one, Matrix.mul_smul]
    have e1 : V₂ + ((r : ℝ) + 1)⁻¹ • (V₂ * V₁) = V₂' + ((r : ℝ) + 1)⁻¹ • (V₂' * V₁') := by
      rw [← hQexp, ← hQexp', hQQ]
    rw [hV2] at e1
    have e2 : ((r : ℝ) + 1)⁻¹ • (V₂' * V₁) = ((r : ℝ) + 1)⁻¹ • (V₂' * V₁') := add_left_cancel e1
    have hVV : V₂' * V₁ = V₂' * V₁' := by
      ext i j
      have := congrFun (congrFun e2 i) j
      simp only [Matrix.smul_apply, smul_eq_mul] at this
      exact mul_left_cancel₀ hβ0 this
    have hPexp : (1 + V₂) * V₁ = V₁ + V₂ * V₁ := by rw [add_mul, one_mul]
    have hPexp' : (1 + V₂') * V₁' = V₁' + V₂' * V₁' := by rw [add_mul, one_mul]
    have e3 : V₁ + V₂ * V₁ = V₁' + V₂' * V₁' := by rw [← hPexp, ← hPexp', hPP]
    rw [hV2, hVV] at e3
    exact add_right_cancel e3
  exact ⟨hV1, hV2⟩

/-- The sigmoid is strictly increasing. -/
theorem sig_strictMono : StrictMono sig := by
  intro a b hab
  have h1 : 1 + Real.exp (-b) < 1 + Real.exp (-a) := by
    have := Real.exp_lt_exp.mpr (show -b < -a by linarith)
    linarith
  have hb : (0 : ℝ) < 1 + Real.exp (-b) := by positivity
  rw [sig, sig]
  gcongr

/-- The sigmoid is injective on `ℝ`. -/
theorem sig_injective : Function.Injective sig := sig_strictMono.injective

/-- **Core `A₂`-difference equation.** Two second layers that differ only in the attention
product `A₂` vs `A₂'` agree on a two-type input `twoType r d a b c` iff their sigmoid weights
agree on `V₂(a-b)`.  This isolates the second-layer content used in `identify_A2`. -/
theorem attnLayer_A2_core {r d : ℕ} (hr : 0 < r) (V₂ A₂ A₂' : Matrix (Fin d) (Fin d) ℝ)
    (a b : Fin d → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hag : attnLayer V₂ A₂ (twoType r d a b c) = attnLayer V₂ A₂' (twoType r d a b c)) :
    sig (c ^ 2 * ((a - b) ⬝ᵥ A₂.mulVec b) + Real.log r) • V₂.mulVec (a - b)
      = sig (c ^ 2 * ((a - b) ⬝ᵥ A₂'.mulVec b) + Real.log r) • V₂.mulVec (a - b) := by
  rw [attnLayer_twoType hr, attnLayer_twoType hr] at hag
  funext i
  have hi := congrFun (congrFun hag i) (Fin.last r)
  rw [twoType_query, twoType_query] at hi
  have hcancel := mul_left_cancel₀ hc hi
  rw [Pi.add_apply, Pi.add_apply] at hcancel
  exact add_left_cancel hcancel

/-- A square matrix is zero iff every bilinear pairing `wᵀ M v` vanishes. -/
theorem matrix_eq_zero_of_dotProduct {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}
    (h : ∀ w v, w ⬝ᵥ M.mulVec v = 0) : M = 0 := by
  ext i j
  have hij := h (Pi.single i 1) (Pi.single j 1)
  rw [Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at hij
  simpa using hij

/-- A real matrix whose quadratic form vanishes identically is skew-symmetric. -/
theorem skew_of_quadratic_zero {d : ℕ} {Δ : Matrix (Fin d) (Fin d) ℝ}
    (h : ∀ w, w ⬝ᵥ Δ.mulVec w = 0) : Δᵀ = -Δ := by
  have hpol : ∀ u v, u ⬝ᵥ Δ.mulVec v + v ⬝ᵥ Δ.mulVec u = 0 := by
    intro u v
    have h1 := h (u + v)
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct] at h1
    linarith [h u, h v]
  ext i j
  have hij := hpol (Pi.single i 1) (Pi.single j 1)
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one, single_dotProduct, single_dotProduct,
    one_mul, one_mul, Matrix.col_apply, Matrix.col_apply] at hij
  rw [Matrix.transpose_apply, Matrix.neg_apply]
  linarith

/-- **Endgame for the second attention product.** If `Δ` is skew-symmetric, `Δ B = 0`, and a
`(d-1)×(d-1)` submatrix of `B` is invertible (so `rank B ≥ d-1`), then `Δ = 0`: indeed
`rank Δ ≤ 1`, and a skew-symmetric matrix of rank `≤ 1` vanishes (every `2×2` principal minor
is `(Δ i j)²`). -/
theorem skew_eq_zero_of_mul_eq_zero {d : ℕ} {Δ B : Matrix (Fin d) (Fin d) ℝ}
    (hskew : Δᵀ = -Δ) (hΔB : Δ * B = 0)
    (hdet : (B.submatrix (Fin.castLE (Nat.sub_le d 1))
        (Fin.castLE (Nat.sub_le d 1))).det ≠ 0) :
    Δ = 0 := by
  classical
  set e : Fin (d - 1) → Fin d := Fin.castLE (Nat.sub_le d 1) with he
  have hUnit : IsUnit (B.submatrix e e) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hrankSub : (B.submatrix e e).rank = d - 1 := by
    rw [Matrix.rank_of_isUnit _ hUnit, Fintype.card_fin]
  have hrankB : d - 1 ≤ B.rank := hrankSub ▸ Matrix.rank_submatrix_le B e e
  have hsum : Δ.rank + B.rank ≤ d := by
    have := Matrix.rank_add_rank_le_card_of_mul_eq_zero hΔB
    rwa [Fintype.card_fin] at this
  have hrankΔ : Δ.rank ≤ 1 := by omega
  have hdiag : ∀ k, Δ k k = 0 := by
    intro k
    have hk := congrFun (congrFun hskew k) k
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at hk
    linarith
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · rw [hdiag i, Matrix.zero_apply]
  · set S : Matrix (Fin 2) (Fin 2) ℝ := Δ.submatrix ![i, j] ![i, j] with hS
    have hSdet : S.det = 0 := by
      by_contra hdet0
      have hu : IsUnit S := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet0)
      have hr2 := Matrix.rank_of_isUnit S hu
      have hSrank : S.rank ≤ 1 := le_trans (Matrix.rank_submatrix_le Δ _ _) hrankΔ
      rw [Fintype.card_fin] at hr2
      omega
    have hskewji : Δ j i = -Δ i j := by
      have h := congrFun (congrFun hskew i) j
      simpa [Matrix.transpose_apply, Matrix.neg_apply] using h
    rw [Matrix.det_fin_two] at hSdet
    simp only [hS, Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      hdiag i, hdiag j, hskewji] at hSdet
    rw [Matrix.zero_apply]
    exact mul_self_eq_zero.mp (by linear_combination hSdet)

/-- Evaluation of `(M.map C) *ᵥ w` at a real point, for polynomials in an arbitrary
variable type `σ` (general-index version of `eval_mapMat_mulVec`). -/
theorem eval_mapMat_mulVec' {σ : Type*} {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → MvPolynomial σ ℝ) (x : σ → ℝ) (i : Fin d) :
    MvPolynomial.eval x (((M.map (MvPolynomial.C : ℝ →+* MvPolynomial σ ℝ)) *ᵥ w) i)
      = (M.mulVec (fun j => MvPolynomial.eval x (w j))) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, MvPolynomial.eval_C]

/-- Evaluation commutes with dot products of polynomial vectors (general-index version). -/
theorem eval_dotProduct' {σ : Type*} {d : ℕ} (x : σ → ℝ)
    (a b : Fin d → MvPolynomial σ ℝ) :
    MvPolynomial.eval x (a ⬝ᵥ b)
      = (fun i => MvPolynomial.eval x (a i)) ⬝ᵥ (fun i => MvPolynomial.eval x (b i)) := by
  simp only [dotProduct, map_sum, map_mul]

/-- A real function that agrees everywhere with a degree-`≤2` polynomial and vanishes on an
infinite set is identically zero. -/
theorem deg2_eq_zero_of_infinite {g : ℝ → ℝ}
    (hg : ∃ c₀ c₁ c₂ : ℝ, ∀ z, g z = c₀ + c₁ * z + c₂ * z ^ 2)
    (hinf : {z : ℝ | g z = 0}.Infinite) : ∀ z, g z = 0 := by
  obtain ⟨c₀, c₁, c₂, hcoef⟩ := hg
  set p : Polynomial ℝ := Polynomial.C c₀ + Polynomial.C c₁ * Polynomial.X
      + Polynomial.C c₂ * Polynomial.X ^ 2 with hp
  have heval : ∀ y, p.eval y = g y := by
    intro y; rw [hp]; simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]; rw [hcoef]
  have hroots : {y : ℝ | p.IsRoot y}.Infinite :=
    hinf.mono (fun y hy => by
      simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, heval]; simpa using hy)
  have hp0 : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p hroots
  intro z
  rw [← heval, hp0, Polynomial.eval_zero]

/-! ### Closed-form (factored) final-token function for `identify_A1`

The real-variable final-token function `F(u,v,τ) = a(s(τ)) + σ(τ·φ(s(τ))+b)·g(s(τ))` of the
paper, extracted from `network_twoType`.  `factoredTau_eq_on_pos` reduces network agreement
(with `V₁,V₂` already identified) to equality of these closed forms on `(0,∞)` — the
real-variable input to the complex-analytic core. -/

/-- First-layer sigmoid weight `s(c)`; later `c = √τ`. -/
noncomputable def firstLayerWeight {d : ℕ} (r : ℕ)
    (A₁ : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ) (c : ℝ) : ℝ :=
  sig (c ^ 2 * ((u - v) ⬝ᵥ A₁.mulVec v) + Real.log r)

/-- Substituting `c = √τ` turns the first-layer sigmoid argument into `τ λ + log r`. -/
theorem firstLayerWeight_sqrt {r d : ℕ} (A₁ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    firstLayerWeight r A₁ u v (Real.sqrt τ)
      = sig (τ * ((u - v) ⬝ᵥ A₁.mulVec v) + Real.log r) := by
  rw [firstLayerWeight, Real.sq_sqrt hτ.le]

/-- First-layer query vector `v₁`. -/
noncomputable def firstLayerQuery {d : ℕ} (r : ℕ)
    (V₁ A₁ : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ) (c : ℝ) : Fin d → ℝ :=
  v + V₁.mulVec v + firstLayerWeight r A₁ u v c • V₁.mulVec (u - v)

/-- First-layer type gap `w₁ = u₁ - v₁`. -/
noncomputable def firstLayerGap {d : ℕ} (r : ℕ)
    (V₁ A₁ : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ) (c : ℝ) : Fin d → ℝ :=
  (u + V₁.mulVec u) - firstLayerQuery r V₁ A₁ u v c

/-- Context vector in the raw `network_twoType` output. -/
def rawTwoLayerContext {d : ℕ} (V₁ V₂ : Matrix (Fin d) (Fin d) ℝ)
    (u : Fin d → ℝ) : Fin d → ℝ :=
  (u + V₁.mulVec u) + V₂.mulVec (u + V₁.mulVec u)

/-- Query vector in the raw `network_twoType` output. -/
noncomputable def rawTwoLayerQuery {d : ℕ} (r : ℕ)
    (V₁ A₁ V₂ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (c : ℝ) : Fin d → ℝ :=
  firstLayerQuery r V₁ A₁ u v c
    + V₂.mulVec (firstLayerQuery r V₁ A₁ u v c)
    + sig (c ^ 2 * (firstLayerGap r V₁ A₁ u v c ⬝ᵥ
          A₂.mulVec (firstLayerQuery r V₁ A₁ u v c)) + Real.log r)
      • V₂.mulVec (firstLayerGap r V₁ A₁ u v c)

/-- The affine-in-`z` base term `a_{u,v}(z) = (I+V₂)(Bv + z Cw)`. -/
def twoLayerA {d : ℕ} (V₁ V₂ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (z : ℝ) : Fin d → ℝ :=
  (1 + V₂).mulVec ((1 + V₁).mulVec v + z • V₁.mulVec (u - v))

/-- The affine-in-`z` visible direction `g_w(z) = V₂(Bw - z Cw)`. -/
def twoLayerG {d : ℕ} (V₁ V₂ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (z : ℝ) : Fin d → ℝ :=
  V₂.mulVec ((1 + V₁).mulVec (u - v) - z • V₁.mulVec (u - v))

/-- The quadratic second-layer argument `φ(u,v,z) = (Bw-zCw)ᵀ A₂(Bv+zCw)`. -/
def twoLayerPhi {d : ℕ} (V₁ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (z : ℝ) : ℝ :=
  ((1 + V₁).mulVec (u - v) - z • V₁.mulVec (u - v)) ⬝ᵥ
    A₂.mulVec ((1 + V₁).mulVec v + z • V₁.mulVec (u - v))

theorem twoLayerG_eq_affine {d : ℕ} (V₁ V₂ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (i : Fin d) (z : ℝ) :
    twoLayerG V₁ V₂ u v z i
      = (V₂.mulVec ((1 + V₁).mulVec (u - v))) i
        + (-(V₂.mulVec (V₁.mulVec (u - v))) i) * z := by
  rw [twoLayerG, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem twoLayerPhi_eq_quadratic {d : ℕ} (V₁ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (z : ℝ) :
    twoLayerPhi V₁ A₂ u v z
      = ((1 + V₁).mulVec (u - v)) ⬝ᵥ A₂.mulVec ((1 + V₁).mulVec v)
        + (((1 + V₁).mulVec (u - v)) ⬝ᵥ A₂.mulVec (V₁.mulVec (u - v))
            - (V₁.mulVec (u - v)) ⬝ᵥ A₂.mulVec ((1 + V₁).mulVec v)) * z
        + (-((V₁.mulVec (u - v)) ⬝ᵥ A₂.mulVec (V₁.mulVec (u - v)))) * z ^ 2 := by
  rw [twoLayerPhi, Matrix.mulVec_add, Matrix.mulVec_smul, sub_dotProduct, dotProduct_add,
    dotProduct_add, smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_dotProduct]
  ring

/-- The rescaled real-variable final-token function from the paper:
`a(s(τ)) + sig(τ φ(s(τ)) + log r) g(s(τ))`. -/
noncomputable def factoredTau {d : ℕ} (r : ℕ)
    (V₁ A₁ V₂ A₂ : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ) (τ : ℝ) :
    Fin d → ℝ :=
  let z := sig (τ * ((u - v) ⬝ᵥ A₁.mulVec v) + Real.log r)
  twoLayerA V₁ V₂ u v z
    + sig (τ * twoLayerPhi V₁ A₂ u v z + Real.log r) • twoLayerG V₁ V₂ u v z

theorem firstLayerQuery_eq_factored {r d : ℕ} (V₁ A₁ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (c : ℝ) :
    firstLayerQuery r V₁ A₁ u v c
      = (1 + V₁).mulVec v + firstLayerWeight r A₁ u v c • V₁.mulVec (u - v) := by
  rw [firstLayerQuery, Matrix.add_mulVec, Matrix.one_mulVec]

theorem firstLayerGap_eq_factored {r d : ℕ} (V₁ A₁ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (c : ℝ) :
    firstLayerGap r V₁ A₁ u v c
      = (1 + V₁).mulVec (u - v) - firstLayerWeight r A₁ u v c • V₁.mulVec (u - v) := by
  ext i
  simp only [firstLayerGap, firstLayerQuery_eq_factored, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_sub, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
  abel

/-- Algebraic factoring of the raw query vector into the paper's
`a(s) + g(s) sig(c² φ(s) + log r)` form. -/
theorem rawTwoLayerQuery_eq_factored {r d : ℕ}
    (V₁ A₁ V₂ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (c : ℝ) :
    rawTwoLayerQuery r V₁ A₁ V₂ A₂ u v c
      = (let z := firstLayerWeight r A₁ u v c
         twoLayerA V₁ V₂ u v z
          + sig (c ^ 2 * twoLayerPhi V₁ A₂ u v z + Real.log r) • twoLayerG V₁ V₂ u v z) := by
  rw [rawTwoLayerQuery, firstLayerQuery_eq_factored, firstLayerGap_eq_factored]
  dsimp only
  rw [twoLayerA, twoLayerG, twoLayerPhi]
  ext i
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply]

/-- The factored final-token formula from a `network_twoType`-style equality. -/
theorem twoLayer_query_factored_of_network_twoType {r d : ℕ}
    (V₁ A₁ V₂ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (c : ℝ)
    (hnet : network ((V₁, A₁), (V₂, A₂)) (twoType r d u v c)
      = twoType r d (rawTwoLayerContext V₁ V₂ u)
          (rawTwoLayerQuery r V₁ A₁ V₂ A₂ u v c) c) :
    (fun i => network ((V₁, A₁), (V₂, A₂)) (twoType r d u v c) i (Fin.last r))
      = c • (let z := firstLayerWeight r A₁ u v c
         twoLayerA V₁ V₂ u v z
          + sig (c ^ 2 * twoLayerPhi V₁ A₂ u v z + Real.log r) • twoLayerG V₁ V₂ u v z) := by
  funext i
  rw [hnet, twoType_query, rawTwoLayerQuery_eq_factored]
  simp [Pi.smul_apply, smul_eq_mul]

/-- The rescaled `τ`-version of the factored final-token formula (`c = √τ`, divided by `√τ`). -/
theorem twoLayer_query_tau_factored_of_network_twoType {r d : ℕ}
    (V₁ A₁ V₂ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hnet : network ((V₁, A₁), (V₂, A₂)) (twoType r d u v (Real.sqrt τ))
      = twoType r d (rawTwoLayerContext V₁ V₂ u)
          (rawTwoLayerQuery r V₁ A₁ V₂ A₂ u v (Real.sqrt τ)) (Real.sqrt τ)) :
    (Real.sqrt τ)⁻¹ •
      (fun i => network ((V₁, A₁), (V₂, A₂)) (twoType r d u v (Real.sqrt τ)) i (Fin.last r))
      = (let z := sig (τ * ((u - v) ⬝ᵥ A₁.mulVec v) + Real.log r)
         twoLayerA V₁ V₂ u v z
          + sig (τ * twoLayerPhi V₁ A₂ u v z + Real.log r) • twoLayerG V₁ V₂ u v z) := by
  have hq := twoLayer_query_factored_of_network_twoType
    (r := r) V₁ A₁ V₂ A₂ u v (Real.sqrt τ) hnet
  have hsqrt : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.mpr hτ).ne'
  rw [hq, smul_smul, inv_mul_cancel₀ hsqrt, one_smul]
  dsimp only
  rw [firstLayerWeight_sqrt (r := r) A₁ u v hτ, Real.sq_sqrt hτ.le]

/-- The factored final-token, bundled as `factoredTau`. -/
theorem twoLayer_query_tau_eq_factoredTau_of_network_twoType {r d : ℕ}
    (V₁ A₁ V₂ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hnet : network ((V₁, A₁), (V₂, A₂)) (twoType r d u v (Real.sqrt τ))
      = twoType r d (rawTwoLayerContext V₁ V₂ u)
          (rawTwoLayerQuery r V₁ A₁ V₂ A₂ u v (Real.sqrt τ)) (Real.sqrt τ)) :
    (Real.sqrt τ)⁻¹ •
      (fun i => network ((V₁, A₁), (V₂, A₂)) (twoType r d u v (Real.sqrt τ)) i (Fin.last r))
      = factoredTau r V₁ A₁ V₂ A₂ u v τ := by
  simpa [factoredTau] using
    twoLayer_query_tau_factored_of_network_twoType (r := r) V₁ A₁ V₂ A₂ u v hτ hnet

/-- Network agreement on the `√τ` input gives `factoredTau` agreement at that `τ`. -/
theorem factoredTau_eq_of_network_agree {r d : ℕ}
    (V₁ A₁ V₂ A₂ V₁' A₁' V₂' A₂' : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hnet : network ((V₁, A₁), (V₂, A₂)) (twoType r d u v (Real.sqrt τ))
      = twoType r d (rawTwoLayerContext V₁ V₂ u)
          (rawTwoLayerQuery r V₁ A₁ V₂ A₂ u v (Real.sqrt τ)) (Real.sqrt τ))
    (hnet' : network ((V₁', A₁'), (V₂', A₂')) (twoType r d u v (Real.sqrt τ))
      = twoType r d (rawTwoLayerContext V₁' V₂' u)
          (rawTwoLayerQuery r V₁' A₁' V₂' A₂' u v (Real.sqrt τ)) (Real.sqrt τ))
    (hagree : network ((V₁, A₁), (V₂, A₂)) (twoType r d u v (Real.sqrt τ))
      = network ((V₁', A₁'), (V₂', A₂')) (twoType r d u v (Real.sqrt τ))) :
    factoredTau r V₁ A₁ V₂ A₂ u v τ = factoredTau r V₁' A₁' V₂' A₂' u v τ := by
  have hleft := twoLayer_query_tau_eq_factoredTau_of_network_twoType
    (r := r) V₁ A₁ V₂ A₂ u v hτ hnet
  have hright := twoLayer_query_tau_eq_factoredTau_of_network_twoType
    (r := r) V₁' A₁' V₂' A₂' u v hτ hnet'
  have hcol :
      (fun i => network ((V₁, A₁), (V₂, A₂)) (twoType r d u v (Real.sqrt τ)) i (Fin.last r))
      = (fun i => network ((V₁', A₁'), (V₂', A₂')) (twoType r d u v (Real.sqrt τ)) i
          (Fin.last r)) := by
    ext i; exact congrFun (congrFun hagree i) (Fin.last r)
  have hscaled := congrArg (fun y : Fin d → ℝ => (Real.sqrt τ)⁻¹ • y) hcol
  change ((Real.sqrt τ)⁻¹ • (fun i => network ((V₁, A₁), (V₂, A₂)) (twoType r d u v
            (Real.sqrt τ)) i (Fin.last r)))
      = ((Real.sqrt τ)⁻¹ • (fun i => network ((V₁', A₁'), (V₂', A₂')) (twoType r d u v
            (Real.sqrt τ)) i (Fin.last r))) at hscaled
  rw [hleft, hright] at hscaled
  exact hscaled

/-- **Modelling bridge for `identify_A1`.** With `V₁,V₂` already identified, network agreement
yields equality of the real-variable final-token functions `factoredTau` on `(0,∞)`. -/
theorem factoredTau_eq_on_pos {r d : ℕ} (hr : 0 < r)
    (V₁ A₁ V₂ A₂ A₁' A₂' : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ)
    (hagree : ∀ c : ℝ, network ((V₁, A₁), (V₂, A₂)) (twoType r d u v c)
        = network ((V₁, A₁'), (V₂, A₂')) (twoType r d u v c)) :
    ∀ {τ : ℝ}, 0 < τ →
      factoredTau r V₁ A₁ V₂ A₂ u v τ = factoredTau r V₁ A₁' V₂ A₂' u v τ := by
  intro τ hτ
  exact factoredTau_eq_of_network_agree (r := r) V₁ A₁ V₂ A₂ V₁ A₁' V₂ A₂' u v hτ
    (network_twoType hr V₁ A₁ V₂ A₂ u v (Real.sqrt τ))
    (network_twoType hr V₁ A₁' V₂ A₂' u v (Real.sqrt τ))
    (hagree (Real.sqrt τ))

/-- Coordinate form of `factoredTau_eq_on_pos`, convenient for one-coordinate pole arguments. -/
theorem factoredTau_coord_eq_on_pos {r d : ℕ} (hr : 0 < r)
    (V₁ A₁ V₂ A₂ A₁' A₂' : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ) (i : Fin d)
    (hagree : ∀ c : ℝ, network ((V₁, A₁), (V₂, A₂)) (twoType r d u v c)
        = network ((V₁, A₁'), (V₂, A₂')) (twoType r d u v c)) :
    ∀ {τ : ℝ}, 0 < τ →
      factoredTau r V₁ A₁ V₂ A₂ u v τ i = factoredTau r V₁ A₁' V₂ A₂' u v τ i := by
  intro τ hτ
  exact congrFun (factoredTau_eq_on_pos hr V₁ A₁ V₂ A₂ A₁' A₂' u v hagree hτ) i

/-! ### Complex-analytic foundations for `identify_A1`

These are the verified analytic ingredients of the pole/continuation argument behind
Lemma `lem:app-causal-identify-a1`: the complex sigmoid `csig` is meromorphic with poles
exactly at the odd multiples of `πi`; near a pole of `1/g`, the poles of `csig ∘ (1/g)`
accumulate (paper Lemma `lem:app-sigmoid-poles-near-pole`, via the open mapping theorem);
and the pole locations `sigmoidPole` determine the slope via their real part.  These feed the
(not-yet-assembled) analytic core `slopes_agree_dense`. -/

section AnalyticA1
open Complex

/-- The complex sigmoid `σ(z) = 1 / (1 + exp (-z))`. -/
noncomputable def csig (z : ℂ) : ℂ := (1 + Complex.exp (-z))⁻¹

/-- The sigmoid denominator `1 + exp (-z)` vanishes exactly at the odd multiples of `π i`. -/
theorem one_add_exp_neg_eq_zero_iff (z : ℂ) :
    1 + Complex.exp (-z) = 0 ↔ ∃ k : ℤ, z = (2 * (k : ℂ) + 1) * (Real.pi : ℂ) * I := by
  rw [add_comm, add_eq_zero_iff_eq_neg,
    show (-1 : ℂ) = Complex.exp ((Real.pi : ℂ) * I) from Complex.exp_pi_mul_I.symm,
    Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-(n + 1), ?_⟩
    have : z = -((Real.pi : ℂ) * I + n * (2 * (Real.pi : ℂ) * I)) := by rw [← hn]; ring
    rw [this]; push_cast; ring
  · rintro ⟨k, hk⟩
    refine ⟨-(k + 1), ?_⟩
    rw [hk]; push_cast; ring

theorem re_eq_zero_of_one_add_exp_neg_eq_zero {z : ℂ}
    (hz : 1 + Complex.exp (-z) = 0) :
    z.re = 0 := by
  rw [one_add_exp_neg_eq_zero_iff] at hz
  obtain ⟨k, hk⟩ := hz
  rw [hk]
  simp

theorem sigmoidPoleSet_not_mem_nhds {ζ : ℂ} (hζ : 1 + Complex.exp (-ζ) = 0) :
    {z : ℂ | 1 + Complex.exp (-z) = 0} ∉ nhds ζ := by
  intro hnhds
  let seq : ℕ → ℂ := fun n => ζ + (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ)
  have htend_real : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have htend : Filter.Tendsto seq Filter.atTop (nhds ζ) := by
    simpa [seq] using tendsto_const_nhds.add ((Complex.continuous_ofReal.tendsto 0).comp htend_real)
  have hevent : ∀ᶠ n in Filter.atTop, seq n ∈ {z : ℂ | 1 + Complex.exp (-z) = 0} :=
    htend.eventually hnhds
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  have hpole_seq : 1 + Complex.exp (-(seq N)) = 0 := hN N le_rfl
  have hreζ : ζ.re = 0 := re_eq_zero_of_one_add_exp_neg_eq_zero hζ
  have hre_seq : (seq N).re = 0 := re_eq_zero_of_one_add_exp_neg_eq_zero hpole_seq
  have hstep_ne : (1 : ℝ) / ((N : ℝ) + 1) ≠ 0 := by positivity
  apply hstep_ne
  have hre : (seq N).re = ζ.re + (1 : ℝ) / ((N : ℝ) + 1) := by
    simp only [seq, Complex.add_re, Complex.ofReal_re]
  linarith

theorem outer_denom_not_eventually_zero_of_arg_not_eventually_const
    {H : ℂ → ℂ} {τ : ℂ}
    (hH : AnalyticAt ℂ H τ)
    (hHne : ¬ (∀ᶠ z in nhds τ, H z = H τ))
    (hpole : 1 + Complex.exp (-(H τ)) = 0) :
    ¬ (∀ᶠ z in nhds τ, 1 + Complex.exp (-(H z)) = 0) := by
  intro hzero
  rcases hH.eventually_constant_or_nhds_le_map_nhds with hconst | hmap
  · exact hHne hconst
  · set P : Set ℂ := {w | 1 + Complex.exp (-w) = 0} with hP
    have hPmap : P ∈ Filter.map H (nhds τ) := by
      rw [Filter.mem_map]
      simpa [P, hP] using hzero
    have hPnhds : P ∈ nhds (H τ) := hmap hPmap
    exact sigmoidPoleSet_not_mem_nhds hpole (by simpa [P, hP] using hPnhds)

/-- The sigmoid denominator is entire. -/
theorem denom_analytic (z : ℂ) : AnalyticAt ℂ (fun w => 1 + Complex.exp (-w)) z := by
  have hdiff : Differentiable ℂ (fun w : ℂ => 1 + Complex.exp (-w)) :=
    (differentiable_const 1).add (differentiable_id.neg.cexp)
  exact (analyticOnNhd_univ_iff_differentiable.mpr hdiff) z (Set.mem_univ z)

/-- The complex sigmoid is meromorphic at every point. -/
theorem csig_meromorphicAt (z : ℂ) : MeromorphicAt csig z :=
  (denom_analytic z).meromorphicAt.inv

/-- Away from its poles, the complex sigmoid is analytic. -/
theorem csig_analyticAt {z : ℂ} (hz : 1 + Complex.exp (-z) ≠ 0) : AnalyticAt ℂ csig z :=
  (denom_analytic z).inv hz

/-- **Pole accumulation** (paper Lemma `lem:app-sigmoid-poles-near-pole`, reciprocal form).
If `g` is analytic at `ζ` with `g ζ = 0` and is not locally constant, then every neighbourhood
of `ζ` contains a point `τ ≠ ζ` at which `1/g` lands on a sigmoid pole (`1 + exp (-(1/g τ)) = 0`):
the poles of `τ ↦ csig (1/g τ)` accumulate at `ζ`.  Proof via the open mapping theorem. -/
theorem sigmoid_poles_accumulate {g : ℂ → ℂ} {ζ : ℂ}
    (hg : AnalyticAt ℂ g ζ) (hg0 : g ζ = 0)
    (hgne : ¬ (∀ᶠ z in nhds ζ, g z = g ζ))
    {U : Set ℂ} (hU : U ∈ nhds ζ) :
    ∃ τ ∈ U, τ ≠ ζ ∧ 1 + Complex.exp (-(1 / g τ)) = 0 := by
  rcases hg.eventually_constant_or_nhds_le_map_nhds with hconst | hmap
  · exact absurd hconst hgne
  rw [hg0] at hmap
  have hgU : g '' U ∈ nhds (0 : ℂ) := hmap (Filter.image_mem_map hU)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hgU
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ / Real.pi)
  set c : ℂ := (2 * (m : ℂ) + 1) * (Real.pi : ℂ) * I with hc
  have hπpos : 0 < Real.pi := Real.pi_pos
  have hcnorm : ‖c‖ = (2 * (m : ℝ) + 1) * Real.pi := by
    rw [hc, show (2 * (m : ℂ) + 1) * (Real.pi : ℂ) * I
          = (((2 * (m : ℝ) + 1) * Real.pi : ℝ) : ℂ) * I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hcpos : 0 < ‖c‖ := by rw [hcnorm]; positivity
  have hcne : c ≠ 0 := by rw [← norm_pos_iff]; exact hcpos
  set p : ℂ := 1 / c with hp
  have hpne : p ≠ 0 := by rw [hp]; exact one_div_ne_zero hcne
  have hpnorm : ‖p‖ = 1 / ((2 * (m : ℝ) + 1) * Real.pi) := by
    rw [hp, norm_div, norm_one, hcnorm]
  have hbig : 1 / δ < (2 * (m : ℝ) + 1) * Real.pi := by
    rw [div_lt_iff₀ hπpos] at hm
    nlinarith [hm, mul_nonneg (show (0 : ℝ) ≤ (m : ℝ) + 1 by positivity) hπpos.le]
  have hplt : ‖p‖ < δ := by
    rw [hpnorm, div_lt_iff₀ (by positivity), mul_comm]
    exact (div_lt_iff₀ hδ).mp hbig
  have hpmem : p ∈ Metric.ball (0 : ℂ) δ := by
    rw [Metric.mem_ball, dist_zero_right]; exact hplt
  obtain ⟨τ, hτU, hτg⟩ := hball hpmem
  refine ⟨τ, hτU, ?_, ?_⟩
  · intro hτζ
    rw [hτζ, hg0] at hτg
    exact hpne hτg.symm
  · have hone : 1 / g τ = c := by rw [hτg, hp, one_div_one_div]
    rw [hone, one_add_exp_neg_eq_zero_iff]
    exact ⟨(m : ℤ), by rw [hc]; push_cast; ring⟩

/-- The poles of `τ ↦ csig (lam·τ + b)`, indexed as in the paper. -/
noncomputable def sigmoidPole (b lam : ℝ) (n : ℤ) : ℂ :=
  (((((2 * n + 1 : ℤ) : ℝ) * Real.pi : ℝ) : ℂ) * I - (b : ℂ)) / (lam : ℂ)

/-- The real part of a real-slope sigmoid pole is `-b/lam`. -/
theorem sigmoidPole_re {b lam : ℝ} (hlam : lam ≠ 0) (n : ℤ) :
    (sigmoidPole b lam n).re = -b / lam := by
  simp [sigmoidPole, Complex.div_re, Complex.normSq]
  field_simp [hlam]

theorem sigmoidPole_ne_zero_of_b_ne_zero {b lam : ℝ} (hb : b ≠ 0) (hlam : lam ≠ 0)
    (n : ℤ) :
    sigmoidPole b lam n ≠ 0 := by
  intro hζ
  have hre := congrArg Complex.re hζ
  rw [sigmoidPole_re hlam] at hre
  simp only [Complex.zero_re] at hre
  have hb0 : b = 0 := by
    field_simp [hlam] at hre
    linarith
  exact hb hb0

/-- If one primed sigmoid pole is also an unprimed sigmoid pole, comparing real parts gives
equality of the real slopes. -/
theorem slope_eq_of_sigmoidPole_eq {b lam lam' : ℝ} (hb : b ≠ 0)
    (hlam : lam ≠ 0) (hlam' : lam' ≠ 0) {n m : ℤ}
    (h : sigmoidPole b lam' n = sigmoidPole b lam m) : lam = lam' := by
  have hre := congrArg Complex.re h
  rw [sigmoidPole_re hlam', sigmoidPole_re hlam] at hre
  field_simp [hb, hlam, hlam'] at hre
  linarith

/-- If every primed sigmoid pole is an unprimed sigmoid pole, the slopes agree. -/
theorem slope_eq_of_sigmoidPole_subset {b lam lam' : ℝ} (hb : b ≠ 0)
    (hlam : lam ≠ 0) (hlam' : lam' ≠ 0)
    (hsub : ∀ n : ℤ, ∃ m : ℤ, sigmoidPole b lam' n = sigmoidPole b lam m) : lam = lam' := by
  obtain ⟨m, hm⟩ := hsub 0
  exact slope_eq_of_sigmoidPole_eq hb hlam hlam' hm

/-- On real arguments the complex sigmoid is the real sigmoid. -/
theorem csig_ofReal (x : ℝ) : csig (x : ℂ) = ((sig x : ℝ) : ℂ) := by
  have hexp : Complex.exp (-(x : ℂ)) = ((Real.exp (-x) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, Complex.ofReal_neg]
  rw [csig, sig, hexp]; norm_cast

/-- Real scalar final-token coordinate model `a(z) + sig(τ ψ(z)+b) g(z)`, `z = sig(λτ+b)`,
with `a(z) = A₀+A₁z`, `g(z) = G₀+G₁z`, `ψ(z) = Ψ₀+Ψ₁z+Ψ₂z²`. -/
noncomputable def tokenR (lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ : ℝ) (τ : ℝ) : ℝ :=
  (A₀ + A₁ * sig (lam * τ + b))
    + sig (τ * (Ψ₀ + Ψ₁ * sig (lam * τ + b) + Ψ₂ * sig (lam * τ + b) ^ 2) + b)
      * (G₀ + G₁ * sig (lam * τ + b))

/-- Complex scalar final-token coordinate model (same shape, with `csig`). -/
noncomputable def tokenC (lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ : ℝ) (τ : ℂ) : ℂ :=
  ((A₀ : ℂ) + (A₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ)))
    + csig (τ * ((Ψ₀ : ℂ) + (Ψ₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ))
        + (Ψ₂ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ)) ^ 2) + (b : ℂ))
      * ((G₀ : ℂ) + (G₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ)))

/-- The concrete outer-sigmoid argument of the scalar token model. -/
noncomputable def tokenOuterArg (lam b Ψ₀ Ψ₁ Ψ₂ : ℝ) (τ : ℂ) : ℂ :=
  τ * ((Ψ₀ : ℂ) + (Ψ₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ))
      + (Ψ₂ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ)) ^ 2) + (b : ℂ)

/-- The visible multiplier of the outer sigmoid in the scalar token model. -/
noncomputable def tokenVisibleAmp (lam b G₀ G₁ : ℝ) (τ : ℂ) : ℂ :=
  (G₀ : ℂ) + (G₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ))

noncomputable def innerDenom (lam b : ℝ) (τ : ℂ) : ℂ :=
  1 + Complex.exp (-((lam : ℂ) * τ + (b : ℂ)))

noncomputable def tokenOuterRhoLinear (lam b Ψ₀ Ψ₁ : ℝ) (τ : ℂ) : ℂ :=
  innerDenom lam b τ /
    (τ * ((Ψ₀ : ℂ) * innerDenom lam b τ + (Ψ₁ : ℂ)) + (b : ℂ) * innerDenom lam b τ)

noncomputable def tokenOuterRhoQuadratic (lam b Ψ₀ Ψ₁ Ψ₂ : ℝ) (τ : ℂ) : ℂ :=
  innerDenom lam b τ ^ 2 /
    (τ * ((Ψ₀ : ℂ) * innerDenom lam b τ ^ 2
      + (Ψ₁ : ℂ) * innerDenom lam b τ + (Ψ₂ : ℂ))
      + (b : ℂ) * innerDenom lam b τ ^ 2)

/-- On real arguments the complex token model agrees with the real one. -/
theorem tokenC_ofReal (lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ : ℝ) (τ : ℝ) :
    tokenC lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ (τ : ℂ)
      = ((tokenR lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ τ : ℝ) : ℂ) := by
  have hz : csig ((lam : ℂ) * (τ : ℂ) + (b : ℂ)) = ((sig (lam * τ + b) : ℝ) : ℂ) := by
    rw [show (lam : ℂ) * (τ : ℂ) + (b : ℂ) = ((lam * τ + b : ℝ) : ℂ) by push_cast; ring,
      csig_ofReal]
  simp only [tokenC, tokenR, hz]
  rw [show (τ : ℂ) * ((Ψ₀ : ℂ) + (Ψ₁ : ℂ) * ((sig (lam * τ + b) : ℝ) : ℂ)
          + (Ψ₂ : ℂ) * ((sig (lam * τ + b) : ℝ) : ℂ) ^ 2) + (b : ℂ)
        = (((τ * (Ψ₀ + Ψ₁ * sig (lam * τ + b) + Ψ₂ * sig (lam * τ + b) ^ 2) + b : ℝ)) : ℂ) by
      push_cast; ring, csig_ofReal]
  push_cast; ring

/-- Away from the inner-sigmoid poles (where `1 + exp(-(λz+b)) ≠ 0`), the complex token model
is meromorphic.  (At the inner poles it is *not* meromorphic — that is where its poles
accumulate.) -/
theorem tokenC_meromorphicAt (lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ : ℝ) {z : ℂ}
    (hz : 1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) ≠ 0) :
    MeromorphicAt (tokenC lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂) z := by
  have haff : AnalyticAt ℂ (fun τ : ℂ => (lam : ℂ) * τ + (b : ℂ)) z :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hzc : AnalyticAt ℂ (fun τ : ℂ => csig ((lam : ℂ) * τ + (b : ℂ))) z :=
    AnalyticAt.comp_of_eq' (csig_analyticAt hz) haff rfl
  have ha : AnalyticAt ℂ
      (fun τ : ℂ => (A₀ : ℂ) + (A₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ))) z :=
    analyticAt_const.add (analyticAt_const.mul hzc)
  have hpsi : AnalyticAt ℂ (fun τ : ℂ => (Ψ₀ : ℂ)
      + (Ψ₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ))
      + (Ψ₂ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ)) ^ 2) z :=
    (analyticAt_const.add (analyticAt_const.mul hzc)).add (analyticAt_const.mul (hzc.pow 2))
  have hinner2 : AnalyticAt ℂ (fun τ : ℂ => τ * ((Ψ₀ : ℂ)
      + (Ψ₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ))
      + (Ψ₂ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ)) ^ 2) + (b : ℂ)) z :=
    (analyticAt_id.mul hpsi).add analyticAt_const
  have houter : MeromorphicAt (fun τ : ℂ => csig (τ * ((Ψ₀ : ℂ)
      + (Ψ₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ))
      + (Ψ₂ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ)) ^ 2) + (b : ℂ))) z :=
    (csig_meromorphicAt _).comp_analyticAt hinner2
  have hg : AnalyticAt ℂ
      (fun τ : ℂ => (G₀ : ℂ) + (G₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ))) z :=
    analyticAt_const.add (analyticAt_const.mul hzc)
  exact ha.meromorphicAt.add (houter.mul hg.meromorphicAt)

theorem tokenC_analyticAt_of_inner_outer_ne
    (lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ : ℝ) {z : ℂ}
    (hinner : 1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) ≠ 0)
    (houter : 1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z)) ≠ 0) :
    AnalyticAt ℂ (tokenC lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂) z := by
  have haff : AnalyticAt ℂ (fun τ : ℂ => (lam : ℂ) * τ + (b : ℂ)) z :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hzc : AnalyticAt ℂ (fun τ : ℂ => csig ((lam : ℂ) * τ + (b : ℂ))) z :=
    AnalyticAt.comp_of_eq' (csig_analyticAt hinner) haff rfl
  have ha : AnalyticAt ℂ
      (fun τ : ℂ => (A₀ : ℂ) + (A₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ))) z :=
    analyticAt_const.add (analyticAt_const.mul hzc)
  have hpsi : AnalyticAt ℂ (fun τ : ℂ => (Ψ₀ : ℂ)
      + (Ψ₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ))
      + (Ψ₂ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ)) ^ 2) z :=
    (analyticAt_const.add (analyticAt_const.mul hzc)).add (analyticAt_const.mul (hzc.pow 2))
  have hinner2 : AnalyticAt ℂ (tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂) z := by
    simpa [tokenOuterArg] using (analyticAt_id.mul hpsi).add analyticAt_const
  have houter' : AnalyticAt ℂ
      (fun τ : ℂ => csig (tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ τ)) z :=
    AnalyticAt.comp_of_eq' (csig_analyticAt houter) hinner2 rfl
  have hg : AnalyticAt ℂ
      (fun τ : ℂ => (G₀ : ℂ) + (G₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ))) z :=
    analyticAt_const.add (analyticAt_const.mul hzc)
  simpa [tokenC, tokenOuterArg] using ha.add (houter'.mul hg)

theorem tokenOuterArg_analyticAt_of_inner_ne (lam b Ψ₀ Ψ₁ Ψ₂ : ℝ) {z : ℂ}
    (hz : 1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) ≠ 0) :
    AnalyticAt ℂ (tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂) z := by
  have haff : AnalyticAt ℂ (fun τ : ℂ => (lam : ℂ) * τ + (b : ℂ)) z :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hzc : AnalyticAt ℂ (fun τ : ℂ => csig ((lam : ℂ) * τ + (b : ℂ))) z :=
    AnalyticAt.comp_of_eq' (csig_analyticAt hz) haff rfl
  have hpsi : AnalyticAt ℂ (fun τ : ℂ => (Ψ₀ : ℂ)
      + (Ψ₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ))
      + (Ψ₂ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ)) ^ 2) z :=
    (analyticAt_const.add (analyticAt_const.mul hzc)).add (analyticAt_const.mul (hzc.pow 2))
  simpa [tokenOuterArg] using (analyticAt_id.mul hpsi).add analyticAt_const

theorem innerDenom_analyticAt (lam b : ℝ) (z : ℂ) :
    AnalyticAt ℂ (innerDenom lam b) z := by
  have haff : AnalyticAt ℂ (fun τ : ℂ => (lam : ℂ) * τ + (b : ℂ)) z :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  change AnalyticAt ℂ (fun τ : ℂ => 1 + Complex.exp (-((lam : ℂ) * τ + (b : ℂ)))) z
  exact analyticAt_const.add (haff.neg.cexp')

/-- The inner sigmoid `z ↦ csig(λz+b)` has its poles exactly at the `sigmoidPole b λ n`:
the denominator vanishes there. -/
theorem inner_denom_sigmoidPole (b lam : ℝ) (hlam : lam ≠ 0) (n : ℤ) :
    1 + Complex.exp (-((lam : ℂ) * sigmoidPole b lam n + (b : ℂ))) = 0 := by
  have hlamC : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
  rw [one_add_exp_neg_eq_zero_iff]
  refine ⟨n, ?_⟩
  rw [sigmoidPole, mul_comm, div_mul_cancel₀ _ hlamC]
  push_cast; ring

theorem inner_denom_not_eventually_zero_at_sigmoidPole (b lam : ℝ) (hlam : lam ≠ 0)
    (n : ℤ) :
    ¬ (∀ᶠ z in nhds (sigmoidPole b lam n),
      1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) = 0) := by
  intro hzero
  set ζ : ℂ := sigmoidPole b lam n
  set D : ℂ → ℂ := fun z => 1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) with hD
  have hpole : D ζ = 0 := by
    rw [hD]
    change 1 + Complex.exp (-((lam : ℂ) * sigmoidPole b lam n + (b : ℂ))) = 0
    exact inner_denom_sigmoidPole b lam hlam n
  have hexpζ : Complex.exp (-((lam : ℂ) * ζ + (b : ℂ))) = -1 := by
    linear_combination hpole
  have hlin : HasDerivAt (fun z : ℂ => (lam : ℂ) * z + (b : ℂ)) (lam : ℂ) ζ := by
    have hmul : HasDerivAt (fun z : ℂ => (lam : ℂ) * z) (lam : ℂ) ζ := by
      simpa using (hasDerivAt_id ζ).const_mul (lam : ℂ)
    have hc : HasDerivAt (fun _ : ℂ => (b : ℂ)) 0 ζ := hasDerivAt_const ζ (b : ℂ)
    convert hmul.add hc using 1 <;> ring
  have hderiv : HasDerivAt D (lam : ℂ) ζ := by
    rw [hD]
    have hneg : HasDerivAt (fun z : ℂ => -((lam : ℂ) * z + (b : ℂ))) (-(lam : ℂ)) ζ := by
      convert hlin.neg using 1
    have hexp : HasDerivAt
        (fun z : ℂ => Complex.exp (-((lam : ℂ) * z + (b : ℂ))))
        (Complex.exp (-((lam : ℂ) * ζ + (b : ℂ))) * (-(lam : ℂ))) ζ :=
      hneg.cexp
    have h := (hasDerivAt_const ζ (1 : ℂ)).add hexp
    convert h using 1
    rw [hexpζ]; ring
  have hDzero : D =ᶠ[nhds ζ] fun _ : ℂ => 0 := by
    simpa [D, ζ] using hzero
  have hderiv0 : HasDerivAt D 0 ζ :=
    (hDzero.hasDerivAt_iff).mpr (hasDerivAt_const ζ (0 : ℂ))
  have hlamC0 : (lam : ℂ) = 0 := hderiv.unique hderiv0
  exact (Complex.ofReal_ne_zero.mpr hlam) hlamC0

theorem inner_denom_eventually_ne_zero_nhdsWithin_sigmoidPole (b lam : ℝ)
    (hlam : lam ≠ 0) (n : ℤ) :
    ∀ᶠ z in nhdsWithin (sigmoidPole b lam n) ({sigmoidPole b lam n}ᶜ : Set ℂ),
      1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) ≠ 0 := by
  have hD : AnalyticAt ℂ
      (fun z : ℂ => 1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))))
      (sigmoidPole b lam n) := by
    have haff : AnalyticAt ℂ (fun z : ℂ => (lam : ℂ) * z + (b : ℂ))
        (sigmoidPole b lam n) :=
      (analyticAt_const.mul analyticAt_id).add analyticAt_const
    exact analyticAt_const.add (haff.neg.cexp')
  exact hD.eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (inner_denom_not_eventually_zero_at_sigmoidPole b lam hlam n)

theorem tokenVisibleAmp_eventually_ne_zero_nhdsWithin_sigmoidPole
    (b lam G₀ G₁ : ℝ) (hlam : lam ≠ 0) (n : ℤ)
    (hG : G₀ ≠ 0 ∨ G₁ ≠ 0) :
    ∀ᶠ z in nhdsWithin (sigmoidPole b lam n) ({sigmoidPole b lam n}ᶜ : Set ℂ),
      tokenVisibleAmp lam b G₀ G₁ z ≠ 0 := by
  by_cases hG₁ : G₁ = 0
  · have hG₀ : G₀ ≠ 0 := by
      rcases hG with hG₀ | hG₁ne
      · exact hG₀
      · exact False.elim (hG₁ne hG₁)
    filter_upwards [] with z
    simpa [tokenVisibleAmp, hG₁, hG₀]
  · set ζ : ℂ := sigmoidPole b lam n
    set D : ℂ → ℂ := fun z => 1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) with hDdef
    have hDζ : D ζ = 0 := by
      rw [hDdef]
      change 1 + Complex.exp (-((lam : ℂ) * sigmoidPole b lam n + (b : ℂ))) = 0
      exact inner_denom_sigmoidPole b lam hlam n
    have hDne := inner_denom_eventually_ne_zero_nhdsWithin_sigmoidPole b lam hlam n
    have hDanalytic : AnalyticAt ℂ D ζ := by
      rw [hDdef]
      have haff : AnalyticAt ℂ (fun z : ℂ => (lam : ℂ) * z + (b : ℂ)) ζ :=
        (analyticAt_const.mul analyticAt_id).add analyticAt_const
      exact analyticAt_const.add (haff.neg.cexp')
    have hnum : ∀ᶠ z in nhds ζ, (G₀ : ℂ) * D z + (G₁ : ℂ) ≠ 0 := by
      have han : AnalyticAt ℂ (fun z : ℂ => (G₀ : ℂ) * D z + (G₁ : ℂ)) ζ :=
        (analyticAt_const.mul hDanalytic).add analyticAt_const
      have hval : (G₀ : ℂ) * D ζ + (G₁ : ℂ) ≠ 0 := by
        rw [hDζ, mul_zero, zero_add]
        exact Complex.ofReal_ne_zero.mpr hG₁
      exact han.continuousAt.eventually_ne hval
    filter_upwards [hDne, Filter.Eventually.filter_mono nhdsWithin_le_nhds hnum] with z hDz hnumz
    intro hampz
    apply hnumz
    have hDzD : D z ≠ 0 := by
      rw [hDdef]
      exact hDz
    rw [tokenVisibleAmp, csig] at hampz
    change (G₀ : ℂ) + (G₁ : ℂ) * (D z)⁻¹ = 0 at hampz
    have hmul := congrArg (fun x : ℂ => x * D z) hampz
    field_simp [hDzD] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

theorem tokenOuterRhoQuadratic_analyticAt_sigmoidPole
    (b lam Ψ₀ Ψ₁ Ψ₂ : ℝ) {n : ℤ}
    (hlam : lam ≠ 0) (hζ : sigmoidPole b lam n ≠ 0) (hΨ₂ : Ψ₂ ≠ 0) :
    AnalyticAt ℂ (tokenOuterRhoQuadratic lam b Ψ₀ Ψ₁ Ψ₂) (sigmoidPole b lam n) := by
  set ζ : ℂ := sigmoidPole b lam n
  set D : ℂ → ℂ := innerDenom lam b with hDdef
  set Q : ℂ → ℂ :=
    fun τ => τ * ((Ψ₀ : ℂ) * D τ ^ 2 + (Ψ₁ : ℂ) * D τ + (Ψ₂ : ℂ))
      + (b : ℂ) * D τ ^ 2 with hQdef
  have hDζ : D ζ = 0 := by
    rw [hDdef, innerDenom]
    change 1 + Complex.exp (-((lam : ℂ) * sigmoidPole b lam n + (b : ℂ))) = 0
    exact inner_denom_sigmoidPole b lam hlam n
  have hQζ : Q ζ ≠ 0 := by
    have hprod : ζ * (Ψ₂ : ℂ) ≠ 0 := by
      exact mul_ne_zero (by simpa [ζ] using hζ) (Complex.ofReal_ne_zero.mpr hΨ₂)
    rw [hQdef]
    change ζ * ((Ψ₀ : ℂ) * D ζ ^ 2 + (Ψ₁ : ℂ) * D ζ + (Ψ₂ : ℂ))
      + (b : ℂ) * D ζ ^ 2 ≠ 0
    rw [hDζ]
    simpa using hprod
  have hD : AnalyticAt ℂ D ζ := by simpa [hDdef] using innerDenom_analyticAt lam b ζ
  have hQ : AnalyticAt ℂ Q ζ := by
    rw [hQdef]
    exact (analyticAt_id.mul
      (((analyticAt_const.mul (hD.pow 2)).add (analyticAt_const.mul hD)).add analyticAt_const)).add
        (analyticAt_const.mul (hD.pow 2))
  change AnalyticAt ℂ (fun τ : ℂ => D τ ^ 2 / Q τ) ζ
  exact (hD.pow 2).div hQ hQζ

theorem tokenOuterRhoQuadratic_zero_sigmoidPole
    (b lam Ψ₀ Ψ₁ Ψ₂ : ℝ) {n : ℤ}
    (hlam : lam ≠ 0) (hζ : sigmoidPole b lam n ≠ 0) (hΨ₂ : Ψ₂ ≠ 0) :
    tokenOuterRhoQuadratic lam b Ψ₀ Ψ₁ Ψ₂ (sigmoidPole b lam n) = 0 := by
  set ζ : ℂ := sigmoidPole b lam n
  set D : ℂ → ℂ := innerDenom lam b with hDdef
  have hDζ : D ζ = 0 := by
    rw [hDdef, innerDenom]
    change 1 + Complex.exp (-((lam : ℂ) * sigmoidPole b lam n + (b : ℂ))) = 0
    exact inner_denom_sigmoidPole b lam hlam n
  have hden : ζ * ((Ψ₀ : ℂ) * D ζ ^ 2 + (Ψ₁ : ℂ) * D ζ + (Ψ₂ : ℂ))
      + (b : ℂ) * D ζ ^ 2 ≠ 0 := by
    have hprod : ζ * (Ψ₂ : ℂ) ≠ 0 := by
      exact mul_ne_zero (by simpa [ζ] using hζ) (Complex.ofReal_ne_zero.mpr hΨ₂)
    rw [hDζ]
    simpa using hprod
  rw [tokenOuterRhoQuadratic]
  change D ζ ^ 2 /
      (ζ * ((Ψ₀ : ℂ) * D ζ ^ 2 + (Ψ₁ : ℂ) * D ζ + (Ψ₂ : ℂ))
        + (b : ℂ) * D ζ ^ 2) = 0
  rw [hDζ]
  simp

theorem tokenOuterRhoQuadratic_not_eventuallyConst_sigmoidPole
    (b lam Ψ₀ Ψ₁ Ψ₂ : ℝ) {n : ℤ}
    (hlam : lam ≠ 0) (hζ : sigmoidPole b lam n ≠ 0) (hΨ₂ : Ψ₂ ≠ 0) :
    ¬ (∀ᶠ z in nhds (sigmoidPole b lam n),
      tokenOuterRhoQuadratic lam b Ψ₀ Ψ₁ Ψ₂ z
        = tokenOuterRhoQuadratic lam b Ψ₀ Ψ₁ Ψ₂ (sigmoidPole b lam n)) := by
  intro hconst
  set ζ : ℂ := sigmoidPole b lam n
  set D : ℂ → ℂ := innerDenom lam b with hDdef
  set Q : ℂ → ℂ :=
    fun τ => τ * ((Ψ₀ : ℂ) * D τ ^ 2 + (Ψ₁ : ℂ) * D τ + (Ψ₂ : ℂ))
      + (b : ℂ) * D τ ^ 2 with hQdef
  have hDζ : D ζ = 0 := by
    rw [hDdef, innerDenom]
    change 1 + Complex.exp (-((lam : ℂ) * sigmoidPole b lam n + (b : ℂ))) = 0
    exact inner_denom_sigmoidPole b lam hlam n
  have hQζ : Q ζ ≠ 0 := by
    have hprod : ζ * (Ψ₂ : ℂ) ≠ 0 := by
      exact mul_ne_zero (by simpa [ζ] using hζ) (Complex.ofReal_ne_zero.mpr hΨ₂)
    rw [hQdef]
    change ζ * ((Ψ₀ : ℂ) * D ζ ^ 2 + (Ψ₁ : ℂ) * D ζ + (Ψ₂ : ℂ))
      + (b : ℂ) * D ζ ^ 2 ≠ 0
    rw [hDζ]
    simpa using hprod
  have hD : AnalyticAt ℂ D ζ := by simpa [hDdef] using innerDenom_analyticAt lam b ζ
  have hQ : AnalyticAt ℂ Q ζ := by
    rw [hQdef]
    exact (analyticAt_id.mul
      (((analyticAt_const.mul (hD.pow 2)).add (analyticAt_const.mul hD)).add analyticAt_const)).add
        (analyticAt_const.mul (hD.pow 2))
  have hQne : ∀ᶠ z in nhds ζ, Q z ≠ 0 := hQ.continuousAt.eventually_ne hQζ
  have hρ0 :
      tokenOuterRhoQuadratic lam b Ψ₀ Ψ₁ Ψ₂ ζ = 0 := by
    simpa [ζ] using tokenOuterRhoQuadratic_zero_sigmoidPole b lam Ψ₀ Ψ₁ Ψ₂ hlam hζ hΨ₂
  have hzero : ∀ᶠ z in nhds ζ, tokenOuterRhoQuadratic lam b Ψ₀ Ψ₁ Ψ₂ z = 0 := by
    filter_upwards [by simpa [ζ] using hconst] with z hz
    rwa [hρ0] at hz
  have hDzero : ∀ᶠ z in nhds ζ, D z = 0 := by
    filter_upwards [hzero, hQne] with z hz hQz
    have hz' : D z ^ 2 / Q z = 0 := by
      simpa [tokenOuterRhoQuadratic, D, Q, hDdef, hQdef] using hz
    have hpow : D z ^ 2 = 0 := by
      exact (div_eq_zero_iff.mp hz').resolve_right hQz
    exact sq_eq_zero_iff.mp hpow
  exact inner_denom_not_eventually_zero_at_sigmoidPole b lam hlam n (by
    simpa [ζ, D, hDdef, innerDenom] using hDzero)

theorem tokenOuterRhoQuadratic_outerArg_nhdsWithin_sigmoidPole
    (b lam Ψ₀ Ψ₁ Ψ₂ : ℝ) {n : ℤ} (hlam : lam ≠ 0) :
    ∀ᶠ z in nhdsWithin (sigmoidPole b lam n) ({sigmoidPole b lam n}ᶜ : Set ℂ),
      1 / tokenOuterRhoQuadratic lam b Ψ₀ Ψ₁ Ψ₂ z
        = tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z := by
  have hDne := inner_denom_eventually_ne_zero_nhdsWithin_sigmoidPole b lam hlam n
  filter_upwards [hDne] with z hDz
  rw [tokenOuterRhoQuadratic, tokenOuterArg, csig, innerDenom] at *
  field_simp [hDz]

theorem tokenOuterRhoLinear_analyticAt_sigmoidPole
    (b lam Ψ₀ Ψ₁ : ℝ) {n : ℤ}
    (hlam : lam ≠ 0) (hζ : sigmoidPole b lam n ≠ 0) (hΨ₁ : Ψ₁ ≠ 0) :
    AnalyticAt ℂ (tokenOuterRhoLinear lam b Ψ₀ Ψ₁) (sigmoidPole b lam n) := by
  set ζ : ℂ := sigmoidPole b lam n
  set D : ℂ → ℂ := innerDenom lam b with hDdef
  set Q : ℂ → ℂ := fun τ => τ * ((Ψ₀ : ℂ) * D τ + (Ψ₁ : ℂ)) + (b : ℂ) * D τ
    with hQdef
  have hDζ : D ζ = 0 := by
    rw [hDdef, innerDenom]
    change 1 + Complex.exp (-((lam : ℂ) * sigmoidPole b lam n + (b : ℂ))) = 0
    exact inner_denom_sigmoidPole b lam hlam n
  have hQζ : Q ζ ≠ 0 := by
    have hprod : ζ * (Ψ₁ : ℂ) ≠ 0 := by
      exact mul_ne_zero (by simpa [ζ] using hζ) (Complex.ofReal_ne_zero.mpr hΨ₁)
    rw [hQdef]
    change ζ * ((Ψ₀ : ℂ) * D ζ + (Ψ₁ : ℂ)) + (b : ℂ) * D ζ ≠ 0
    rw [hDζ]
    simpa using hprod
  have hD : AnalyticAt ℂ D ζ := by simpa [hDdef] using innerDenom_analyticAt lam b ζ
  have hQ : AnalyticAt ℂ Q ζ := by
    rw [hQdef]
    exact (analyticAt_id.mul ((analyticAt_const.mul hD).add analyticAt_const)).add
      (analyticAt_const.mul hD)
  change AnalyticAt ℂ (fun τ : ℂ => D τ / Q τ) ζ
  exact hD.div hQ hQζ

theorem tokenOuterRhoLinear_zero_sigmoidPole
    (b lam Ψ₀ Ψ₁ : ℝ) {n : ℤ}
    (hlam : lam ≠ 0) (hζ : sigmoidPole b lam n ≠ 0) (hΨ₁ : Ψ₁ ≠ 0) :
    tokenOuterRhoLinear lam b Ψ₀ Ψ₁ (sigmoidPole b lam n) = 0 := by
  set ζ : ℂ := sigmoidPole b lam n
  set D : ℂ → ℂ := innerDenom lam b with hDdef
  have hDζ : D ζ = 0 := by
    rw [hDdef, innerDenom]
    change 1 + Complex.exp (-((lam : ℂ) * sigmoidPole b lam n + (b : ℂ))) = 0
    exact inner_denom_sigmoidPole b lam hlam n
  rw [tokenOuterRhoLinear]
  change D ζ / (ζ * ((Ψ₀ : ℂ) * D ζ + (Ψ₁ : ℂ)) + (b : ℂ) * D ζ) = 0
  rw [hDζ]
  simp

theorem tokenOuterRhoLinear_not_eventuallyConst_sigmoidPole
    (b lam Ψ₀ Ψ₁ : ℝ) {n : ℤ}
    (hlam : lam ≠ 0) (hζ : sigmoidPole b lam n ≠ 0) (hΨ₁ : Ψ₁ ≠ 0) :
    ¬ (∀ᶠ z in nhds (sigmoidPole b lam n),
      tokenOuterRhoLinear lam b Ψ₀ Ψ₁ z
        = tokenOuterRhoLinear lam b Ψ₀ Ψ₁ (sigmoidPole b lam n)) := by
  intro hconst
  set ζ : ℂ := sigmoidPole b lam n
  set D : ℂ → ℂ := innerDenom lam b with hDdef
  set Q : ℂ → ℂ := fun τ => τ * ((Ψ₀ : ℂ) * D τ + (Ψ₁ : ℂ)) + (b : ℂ) * D τ
    with hQdef
  have hDζ : D ζ = 0 := by
    rw [hDdef, innerDenom]
    change 1 + Complex.exp (-((lam : ℂ) * sigmoidPole b lam n + (b : ℂ))) = 0
    exact inner_denom_sigmoidPole b lam hlam n
  have hQζ : Q ζ ≠ 0 := by
    have hprod : ζ * (Ψ₁ : ℂ) ≠ 0 := by
      exact mul_ne_zero (by simpa [ζ] using hζ) (Complex.ofReal_ne_zero.mpr hΨ₁)
    rw [hQdef]
    change ζ * ((Ψ₀ : ℂ) * D ζ + (Ψ₁ : ℂ)) + (b : ℂ) * D ζ ≠ 0
    rw [hDζ]
    simpa using hprod
  have hD : AnalyticAt ℂ D ζ := by simpa [hDdef] using innerDenom_analyticAt lam b ζ
  have hQ : AnalyticAt ℂ Q ζ := by
    rw [hQdef]
    exact (analyticAt_id.mul ((analyticAt_const.mul hD).add analyticAt_const)).add
      (analyticAt_const.mul hD)
  have hQne : ∀ᶠ z in nhds ζ, Q z ≠ 0 := hQ.continuousAt.eventually_ne hQζ
  have hρ0 : tokenOuterRhoLinear lam b Ψ₀ Ψ₁ ζ = 0 := by
    simpa [ζ] using tokenOuterRhoLinear_zero_sigmoidPole b lam Ψ₀ Ψ₁ hlam hζ hΨ₁
  have hzero : ∀ᶠ z in nhds ζ, tokenOuterRhoLinear lam b Ψ₀ Ψ₁ z = 0 := by
    filter_upwards [by simpa [ζ] using hconst] with z hz
    rwa [hρ0] at hz
  have hDzero : ∀ᶠ z in nhds ζ, D z = 0 := by
    filter_upwards [hzero, hQne] with z hz hQz
    have hz' : D z / Q z = 0 := by
      simpa [tokenOuterRhoLinear, D, Q, hDdef, hQdef] using hz
    exact (div_eq_zero_iff.mp hz').resolve_right hQz
  exact inner_denom_not_eventually_zero_at_sigmoidPole b lam hlam n (by
    simpa [ζ, D, hDdef, innerDenom] using hDzero)

theorem tokenOuterRhoLinear_outerArg_nhdsWithin_sigmoidPole
    (b lam Ψ₀ Ψ₁ Ψ₂ : ℝ) {n : ℤ} (hlam : lam ≠ 0) (hΨ₂ : Ψ₂ = 0) :
    ∀ᶠ z in nhdsWithin (sigmoidPole b lam n) ({sigmoidPole b lam n}ᶜ : Set ℂ),
      1 / tokenOuterRhoLinear lam b Ψ₀ Ψ₁ z
        = tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z := by
  have hDne := inner_denom_eventually_ne_zero_nhdsWithin_sigmoidPole b lam hlam n
  filter_upwards [hDne] with z hDz
  rw [tokenOuterRhoLinear, tokenOuterArg, csig, innerDenom, hΨ₂] at *
  field_simp [hDz]
  norm_num
  ring

/-- **Extraction** (step 2): the real final-token coordinate `factoredTau … i` is exactly the
scalar model `tokenR` with the affine (`a,g`) and quadratic (`ψ`) coefficients read off from
the value/attention products. -/
theorem factoredTau_eq_tokenR {r d : ℕ} (V₁ A₁ V₂ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (i : Fin d) (τ : ℝ) :
    factoredTau r V₁ A₁ V₂ A₂ u v τ i
      = tokenR ((u - v) ⬝ᵥ A₁.mulVec v) (Real.log r)
          (((1 + V₂).mulVec ((1 + V₁).mulVec v)) i)
          (((1 + V₂).mulVec (V₁.mulVec (u - v))) i)
          ((V₂.mulVec ((1 + V₁).mulVec (u - v))) i)
          (-((V₂.mulVec (V₁.mulVec (u - v))) i))
          (((1 + V₁).mulVec (u - v)) ⬝ᵥ A₂.mulVec ((1 + V₁).mulVec v))
          (((1 + V₁).mulVec (u - v)) ⬝ᵥ A₂.mulVec (V₁.mulVec (u - v))
            - (V₁.mulVec (u - v)) ⬝ᵥ A₂.mulVec ((1 + V₁).mulVec v))
          (-((V₁.mulVec (u - v)) ⬝ᵥ A₂.mulVec (V₁.mulVec (u - v))))
          τ := by
  set z : ℝ := sig (τ * ((u - v) ⬝ᵥ A₁.mulVec v) + Real.log r) with hz
  have hA : (twoLayerA V₁ V₂ u v z) i
      = ((1 + V₂).mulVec ((1 + V₁).mulVec v)) i
        + z * ((1 + V₂).mulVec (V₁.mulVec (u - v))) i := by
    rw [twoLayerA, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hG : (twoLayerG V₁ V₂ u v z) i
      = (V₂.mulVec ((1 + V₁).mulVec (u - v))) i
        - z * (V₂.mulVec (V₁.mulVec (u - v))) i := by
    rw [twoLayerG, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hPhi : twoLayerPhi V₁ A₂ u v z
      = ((1 + V₁).mulVec (u - v)) ⬝ᵥ A₂.mulVec ((1 + V₁).mulVec v)
        + (((1 + V₁).mulVec (u - v)) ⬝ᵥ A₂.mulVec (V₁.mulVec (u - v))
            - (V₁.mulVec (u - v)) ⬝ᵥ A₂.mulVec ((1 + V₁).mulVec v)) * z
        + (-((V₁.mulVec (u - v)) ⬝ᵥ A₂.mulVec (V₁.mulVec (u - v)))) * z ^ 2 := by
    rw [twoLayerPhi, Matrix.mulVec_add, Matrix.mulVec_smul, sub_dotProduct, dotProduct_add,
      dotProduct_add, smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_dotProduct]
    ring
  have hzt : sig (((u - v) ⬝ᵥ A₁.mulVec v) * τ + Real.log r) = z := by rw [hz, mul_comm]
  have hfac : factoredTau r V₁ A₁ V₂ A₂ u v τ i
      = (twoLayerA V₁ V₂ u v z) i
        + sig (τ * twoLayerPhi V₁ A₂ u v z + Real.log r) * (twoLayerG V₁ V₂ u v z) i := by
    show (twoLayerA V₁ V₂ u v z
        + sig (τ * twoLayerPhi V₁ A₂ u v z + Real.log r) • twoLayerG V₁ V₂ u v z) i = _
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfac, hA, hG, hPhi, tokenR, hzt]
  ring

/-- The complexified network final-token coordinate function (the `tokenC` model with the
network's read-off coefficients). -/
noncomputable def tokenCnet {d : ℕ} (r : ℕ) (V₁ A₁ V₂ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (i : Fin d) (τ : ℂ) : ℂ :=
  tokenC ((u - v) ⬝ᵥ A₁.mulVec v) (Real.log r)
    (((1 + V₂).mulVec ((1 + V₁).mulVec v)) i) (((1 + V₂).mulVec (V₁.mulVec (u - v))) i)
    ((V₂.mulVec ((1 + V₁).mulVec (u - v))) i) (-((V₂.mulVec (V₁.mulVec (u - v))) i))
    (((1 + V₁).mulVec (u - v)) ⬝ᵥ A₂.mulVec ((1 + V₁).mulVec v))
    (((1 + V₁).mulVec (u - v)) ⬝ᵥ A₂.mulVec (V₁.mulVec (u - v))
      - (V₁.mulVec (u - v)) ⬝ᵥ A₂.mulVec ((1 + V₁).mulVec v))
    (-((V₁.mulVec (u - v)) ⬝ᵥ A₂.mulVec (V₁.mulVec (u - v)))) τ

/-- On real arguments the complexified network coordinate is the real final-token coordinate. -/
theorem tokenCnet_ofReal {d : ℕ} (r : ℕ) (V₁ A₁ V₂ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (i : Fin d) (τ : ℝ) :
    tokenCnet r V₁ A₁ V₂ A₂ u v i (τ : ℂ)
      = ((factoredTau r V₁ A₁ V₂ A₂ u v τ i : ℝ) : ℂ) := by
  simp only [tokenCnet]
  rw [tokenC_ofReal, ← factoredTau_eq_tokenR]

/-- **`FC = FC'` on `(0,∞)`** (the real-variable input to the continuation argument): with
`V₁,V₂` identified, network agreement gives equality of the complexified final-token
coordinates on positive reals. -/
theorem tokenCnet_eq_on_pos {d : ℕ} (r : ℕ) (hr : 0 < r)
    (V₁ A₁ V₂ A₂ A₁' A₂' : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ) (i : Fin d)
    (hagree : ∀ c : ℝ, network ((V₁, A₁), (V₂, A₂)) (twoType r d u v c)
        = network ((V₁, A₁'), (V₂, A₂')) (twoType r d u v c))
    {τ : ℝ} (hτ : 0 < τ) :
    tokenCnet r V₁ A₁ V₂ A₂ u v i (τ : ℂ) = tokenCnet r V₁ A₁' V₂ A₂' u v i (τ : ℂ) := by
  rw [tokenCnet_ofReal, tokenCnet_ofReal,
    factoredTau_coord_eq_on_pos hr V₁ A₁ V₂ A₂ A₁' A₂' u v i hagree hτ]

/-! #### Step 1 (accumulation) and the analytic continuation, consolidated from `scratch2` -/

/-- A real argument is never a sigmoid pole. -/
theorem one_add_exp_neg_ofReal_ne_zero (x : ℝ) : 1 + Complex.exp (-(x : ℂ)) ≠ 0 := by
  rw [show -(x : ℂ) = ((-x : ℝ) : ℂ) by norm_num, ← Complex.ofReal_exp]
  norm_cast
  positivity

/-- At real inputs the complex token model is analytic (neither sigmoid denominator vanishes). -/
theorem tokenC_analyticAt_ofReal (lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ : ℝ) (τ₀ : ℝ) :
    AnalyticAt ℂ (tokenC lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂) (τ₀ : ℂ) := by
  have hinner_denom : 1 + Complex.exp (-((lam : ℂ) * (τ₀ : ℂ) + (b : ℂ))) ≠ 0 := by
    rw [show (lam : ℂ) * (τ₀ : ℂ) + (b : ℂ) = ((lam * τ₀ + b : ℝ) : ℂ) by push_cast; ring]
    exact one_add_exp_neg_ofReal_ne_zero _
  have haff : AnalyticAt ℂ (fun τ : ℂ => (lam : ℂ) * τ + (b : ℂ)) (τ₀ : ℂ) :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hzc : AnalyticAt ℂ (fun τ : ℂ => csig ((lam : ℂ) * τ + (b : ℂ))) (τ₀ : ℂ) :=
    AnalyticAt.comp_of_eq' (csig_analyticAt hinner_denom) haff rfl
  have ha : AnalyticAt ℂ
      (fun τ : ℂ => (A₀ : ℂ) + (A₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ))) (τ₀ : ℂ) :=
    analyticAt_const.add (analyticAt_const.mul hzc)
  have hpsi : AnalyticAt ℂ (fun τ : ℂ => (Ψ₀ : ℂ)
      + (Ψ₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ))
      + (Ψ₂ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ)) ^ 2) (τ₀ : ℂ) :=
    (analyticAt_const.add (analyticAt_const.mul hzc)).add (analyticAt_const.mul (hzc.pow 2))
  have hinner2 : AnalyticAt ℂ (fun τ : ℂ => τ * ((Ψ₀ : ℂ)
      + (Ψ₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ))
      + (Ψ₂ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ)) ^ 2) + (b : ℂ)) (τ₀ : ℂ) :=
    (analyticAt_id.mul hpsi).add analyticAt_const
  have hsig_real : csig ((lam : ℂ) * (τ₀ : ℂ) + (b : ℂ)) = ((sig (lam * τ₀ + b) : ℝ) : ℂ) := by
    rw [show (lam : ℂ) * (τ₀ : ℂ) + (b : ℂ) = ((lam * τ₀ + b : ℝ) : ℂ) by push_cast; ring,
      csig_ofReal]
  have houter_denom : 1 + Complex.exp (-((τ₀ : ℂ) * ((Ψ₀ : ℂ)
      + (Ψ₁ : ℂ) * csig ((lam : ℂ) * (τ₀ : ℂ) + (b : ℂ))
      + (Ψ₂ : ℂ) * csig ((lam : ℂ) * (τ₀ : ℂ) + (b : ℂ)) ^ 2) + (b : ℂ))) ≠ 0 := by
    rw [hsig_real,
      show (τ₀ : ℂ) * ((Ψ₀ : ℂ) + (Ψ₁ : ℂ) * ((sig (lam * τ₀ + b) : ℝ) : ℂ)
          + (Ψ₂ : ℂ) * ((sig (lam * τ₀ + b) : ℝ) : ℂ) ^ 2) + (b : ℂ)
        = (((τ₀ * (Ψ₀ + Ψ₁ * sig (lam * τ₀ + b)
              + Ψ₂ * sig (lam * τ₀ + b) ^ 2) + b : ℝ)) : ℂ) by push_cast; ring]
    exact one_add_exp_neg_ofReal_ne_zero _
  have houter : AnalyticAt ℂ (fun τ : ℂ => csig (τ * ((Ψ₀ : ℂ)
      + (Ψ₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ))
      + (Ψ₂ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ)) ^ 2) + (b : ℂ))) (τ₀ : ℂ) :=
    AnalyticAt.comp_of_eq' (csig_analyticAt houter_denom) hinner2 rfl
  have hg : AnalyticAt ℂ
      (fun τ : ℂ => (G₀ : ℂ) + (G₁ : ℂ) * csig ((lam : ℂ) * τ + (b : ℂ))) (τ₀ : ℂ) :=
    analyticAt_const.add (analyticAt_const.mul hzc)
  simpa [tokenC] using ha.add (houter.mul hg)

/-- A continuous complex visible factor nonzero at `ζ` is nonzero near `ζ`. -/
theorem eventually_ne_zero_of_continuousAt_complex {amp : ℂ → ℂ} {ζ : ℂ}
    (hamp : ContinuousAt amp ζ) (hamp0 : amp ζ ≠ 0) :
    ∀ᶠ τ in nhds ζ, amp τ ≠ 0 := by
  simpa using hamp.eventually_ne hamp0

/-- **Step 1 (visible outer-pole accumulation).**  If `ρ` (the reciprocal of an outer-sigmoid
argument) is analytic, vanishes at `ζ`, and is not locally constant, then every neighbourhood
of `ζ` contains a point `τ ≠ ζ` with the visible multiplier nonzero and an outer sigmoid pole. -/
theorem visible_outer_sigmoid_poles_accumulate {ρ amp : ℂ → ℂ} {ζ : ℂ}
    (hρ : AnalyticAt ℂ ρ ζ) (hρ0 : ρ ζ = 0)
    (hρne : ¬ (∀ᶠ z in nhds ζ, ρ z = ρ ζ))
    (hamp : ∀ᶠ z in nhds ζ, amp z ≠ 0)
    {U : Set ℂ} (hU : U ∈ nhds ζ) :
    ∃ τ ∈ U, τ ≠ ζ ∧ amp τ ≠ 0 ∧ 1 + Complex.exp (-(1 / ρ τ)) = 0 := by
  have hUamp : U ∩ {τ : ℂ | amp τ ≠ 0} ∈ nhds ζ := Filter.inter_mem hU hamp
  obtain ⟨τ, hτ, hτne, hpole⟩ := sigmoid_poles_accumulate hρ hρ0 hρne hUamp
  exact ⟨τ, hτ.1, hτne, hτ.2, hpole⟩

/-- **B1.**  Primed-token version of visible outer-pole accumulation.  The reciprocal
`ρ` is kept explicit, but the conclusion is rewritten into the concrete primed token
outer argument. -/
theorem primed_token_visible_outer_poles_accumulate
    (lam' b G₀ G₁ Ψ₀ Ψ₁ Ψ₂ : ℝ) {ρ : ℂ → ℂ} {ζ : ℂ}
    (hρ : AnalyticAt ℂ ρ ζ) (hρ0 : ρ ζ = 0)
    (hρne : ¬ (∀ᶠ z in nhds ζ, ρ z = ρ ζ))
    (hρ_outer : ∀ᶠ τ in nhdsWithin ζ ({ζ}ᶜ : Set ℂ),
      1 / ρ τ = tokenOuterArg lam' b Ψ₀ Ψ₁ Ψ₂ τ)
    (hamp : ∀ᶠ τ in nhdsWithin ζ ({ζ}ᶜ : Set ℂ),
      tokenVisibleAmp lam' b G₀ G₁ τ ≠ 0)
    {U : Set ℂ} (hU : U ∈ nhds ζ) :
    ∃ τ ∈ U, τ ≠ ζ ∧ tokenVisibleAmp lam' b G₀ G₁ τ ≠ 0 ∧
      1 + Complex.exp (-(tokenOuterArg lam' b Ψ₀ Ψ₁ Ψ₂ τ)) = 0 := by
  rw [eventually_nhdsWithin_iff] at hρ_outer
  rw [eventually_nhdsWithin_iff] at hamp
  have hside : ∀ᶠ τ in nhds ζ,
      τ ≠ ζ →
        1 / ρ τ = tokenOuterArg lam' b Ψ₀ Ψ₁ Ψ₂ τ ∧
          tokenVisibleAmp lam' b G₀ G₁ τ ≠ 0 := by
    filter_upwards [hρ_outer, hamp] with τ houterτ hampτ hτne
    exact ⟨houterτ hτne, hampτ hτne⟩
  have hUside :
      U ∩ {τ : ℂ | τ = ζ ∨
        (1 / ρ τ = tokenOuterArg lam' b Ψ₀ Ψ₁ Ψ₂ τ ∧
          tokenVisibleAmp lam' b G₀ G₁ τ ≠ 0)} ∈ nhds ζ := by
    refine Filter.inter_mem hU ?_
    filter_upwards [hside] with τ hτ
    by_cases hτζ : τ = ζ
    · exact Or.inl hτζ
    · exact Or.inr (hτ hτζ)
  obtain ⟨τ, hτ, hτne, hampτ, hpole⟩ :=
    visible_outer_sigmoid_poles_accumulate
      (ρ := ρ) (amp := fun _ : ℂ => (1 : ℂ))
      hρ hρ0 hρne (Filter.Eventually.of_forall fun _ => one_ne_zero) hUside
  have hsideτ : 1 / ρ τ = tokenOuterArg lam' b Ψ₀ Ψ₁ Ψ₂ τ ∧
      tokenVisibleAmp lam' b G₀ G₁ τ ≠ 0 := by
    rcases hτ.2 with hτζ | hsideτ
    · exact absurd hτζ hτne
    · exact hsideτ
  have houterτ : 1 / ρ τ = tokenOuterArg lam' b Ψ₀ Ψ₁ Ψ₂ τ := hsideτ.1
  have hpole' : 1 + Complex.exp (-(tokenOuterArg lam' b Ψ₀ Ψ₁ Ψ₂ τ)) = 0 := by
    rw [← houterτ]
    exact hpole
  exact ⟨τ, hτ.1, hτne, hsideτ.2, hpole'⟩

/-- At real inputs, the complexified network coordinate is analytic. -/
theorem tokenCnet_analyticAt_ofReal {d : ℕ} (r : ℕ) (V₁ A₁ V₂ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (i : Fin d) (τ₀ : ℝ) :
    AnalyticAt ℂ (tokenCnet r V₁ A₁ V₂ A₂ u v i) (τ₀ : ℂ) :=
  tokenC_analyticAt_ofReal _ _ _ _ _ _ _ _ _ τ₀

/-- Away from first-layer poles, the complexified network coordinate is meromorphic. -/
theorem tokenCnet_meromorphicAt {d : ℕ} (r : ℕ) (V₁ A₁ V₂ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d → ℝ) (i : Fin d) {z : ℂ}
    (hz : 1 + Complex.exp (-((((u - v) ⬝ᵥ A₁.mulVec v : ℝ) : ℂ) * z + (Real.log r : ℂ))) ≠ 0) :
    MeromorphicAt (tokenCnet r V₁ A₁ V₂ A₂ u v i) z :=
  tokenC_meromorphicAt _ _ _ _ _ _ _ _ _ hz

/-- **Local continuation.**  Equality on positive reals upgrades to equality on a complex
neighbourhood of any positive real input (local identity theorem). -/
theorem tokenCnet_eventuallyEq_nhds_of_eq_on_pos {d : ℕ} (r : ℕ) (hr : 0 < r)
    (V₁ A₁ V₂ A₂ A₁' A₂' : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ) (i : Fin d)
    (hagree : ∀ c : ℝ, network ((V₁, A₁), (V₂, A₂)) (twoType r d u v c)
        = network ((V₁, A₁'), (V₂, A₂')) (twoType r d u v c))
    {τ₀ : ℝ} (hτ₀ : 0 < τ₀) :
    ∀ᶠ z in nhds (τ₀ : ℂ),
      tokenCnet r V₁ A₁ V₂ A₂ u v i z = tokenCnet r V₁ A₁' V₂ A₂' u v i z := by
  have hf := tokenCnet_analyticAt_ofReal r V₁ A₁ V₂ A₂ u v i τ₀
  have hg := tokenCnet_analyticAt_ofReal r V₁ A₁' V₂ A₂' u v i τ₀
  have hfreq_nhds : ∃ᶠ z in nhds (τ₀ : ℂ),
      tokenCnet r V₁ A₁ V₂ A₂ u v i z = tokenCnet r V₁ A₁' V₂ A₂' u v i z
        ∧ z ∈ ({(τ₀ : ℂ)}ᶜ : Set ℂ) := by
    let seq : ℕ → ℂ := fun n => ((τ₀ + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
    have hreal_tend :
        Filter.Tendsto (fun n : ℕ => τ₀ + 1 / ((n : ℝ) + 1)) Filter.atTop (nhds τ₀) := by
      simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hseq_tend : Filter.Tendsto seq Filter.atTop (nhds (τ₀ : ℂ)) :=
      (Complex.continuous_ofReal.tendsto τ₀).comp hreal_tend
    refine hseq_tend.frequently (Filter.Frequently.of_forall ?_)
    intro n
    have hτn : 0 < τ₀ + 1 / ((n : ℝ) + 1) := by positivity
    have hneR : τ₀ + 1 / ((n : ℝ) + 1) ≠ τ₀ := by
      intro h
      have hnonzero : 1 / ((n : ℝ) + 1) ≠ 0 := by positivity
      exact hnonzero (by linarith)
    have hneC : ((τ₀ + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) ≠ (τ₀ : ℂ) :=
      fun h => hneR (Complex.ofReal_injective h)
    exact ⟨tokenCnet_eq_on_pos r hr V₁ A₁ V₂ A₂ A₁' A₂' u v i hagree hτn, by simpa [seq] using hneC⟩
  have hfreq : ∃ᶠ z in nhdsWithin (τ₀ : ℂ) ({(τ₀ : ℂ)}ᶜ : Set ℂ),
      tokenCnet r V₁ A₁ V₂ A₂ u v i z = tokenCnet r V₁ A₁' V₂ A₂' u v i z := by
    rw [frequently_nhdsWithin_iff]; exact hfreq_nhds
  exact (hf.frequently_eq_iff_eventually_eq hg).mp hfreq

/-- **B2.**  If non-analytic points of `F` accumulate at `ζ`, then `F` is not
meromorphic at `ζ`. -/
theorem not_meromorphicAt_of_accumulating_not_analyticAt {F : ℂ → ℂ} {ζ : ℂ}
    (hacc : ∀ U : Set ℂ, U ∈ nhds ζ → ∃ τ ∈ U, τ ≠ ζ ∧ ¬ AnalyticAt ℂ F τ) :
    ¬ MeromorphicAt F ζ := by
  intro hF
  have hnear : {τ : ℂ | AnalyticAt ℂ F τ} ∈ nhdsWithin ζ ({ζ}ᶜ : Set ℂ) :=
    hF.eventually_analyticAt
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hnear
  obtain ⟨V, hV, hsub⟩ := hnear
  obtain ⟨τ, hτV, hτne, hτbad⟩ := hacc V hV
  exact hτbad (hsub ⟨hτV, by simpa using hτne⟩)

/-- Local singularity mechanism for the outer sigmoid: if `F = A + D⁻¹G` near a point,
`A,D,G` are analytic there, `D` has an isolated zero there, and `G` is nonzero there, then
`F` cannot be analytic there. -/
theorem not_analyticAt_of_add_inv_mul_isolated_zero {F A D G : ℂ → ℂ} {τ : ℂ}
    (hF_eq : ∀ z, F z = A z + (D z)⁻¹ * G z)
    (hA : AnalyticAt ℂ A τ) (hD : AnalyticAt ℂ D τ) (hG : AnalyticAt ℂ G τ)
    (hDτ : D τ = 0) (hGτ : G τ ≠ 0)
    (hDne : ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), D z ≠ 0) :
    ¬ AnalyticAt ℂ F τ := by
  intro hF
  set L : ℂ → ℂ := fun z => (F z - A z) * D z with hLdef
  have hL : AnalyticAt ℂ L τ := by
    rw [hLdef]
    exact (hF.sub hA).mul hD
  have hLeq_eventually : ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), L z = G z := by
    filter_upwards [hDne] with z hDz
    change (F z - A z) * D z = G z
    rw [hF_eq z]
    field_simp [hDz]
    ring
  have hLeq_freq : ∃ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), L z = G z :=
    hLeq_eventually.frequently
  have hLeq_nhds : L =ᶠ[nhds τ] G :=
    (hL.frequently_eq_iff_eventually_eq hG).mp hLeq_freq
  have hvalue : L τ = G τ := hLeq_nhds.eq_of_nhds
  have hLτ : L τ = 0 := by
    change (F τ - A τ) * D τ = 0
    rw [hDτ, mul_zero]
  exact hGτ (by rw [← hvalue, hLτ])

/-- Punctured-equality variant of `not_analyticAt_of_add_inv_mul_isolated_zero`: a function
with a genuine `D⁻¹ * G` pole cannot agree off the center with an analytic function. -/
theorem no_analytic_puncturedEq_of_add_inv_mul_isolated_zero {F E A D G : ℂ → ℂ} {τ : ℂ}
    (hF_eq : ∀ z, F z = A z + (D z)⁻¹ * G z)
    (hE : AnalyticAt ℂ E τ) (heq : E =ᶠ[nhdsWithin τ ({τ}ᶜ : Set ℂ)] F)
    (hA : AnalyticAt ℂ A τ) (hD : AnalyticAt ℂ D τ) (hG : AnalyticAt ℂ G τ)
    (hDτ : D τ = 0) (hGτ : G τ ≠ 0)
    (hDne : ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), D z ≠ 0) :
    False := by
  set L : ℂ → ℂ := fun z => (E z - A z) * D z with hLdef
  have hL : AnalyticAt ℂ L τ := by
    rw [hLdef]
    exact (hE.sub hA).mul hD
  have hLeq_eventually : ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), L z = G z := by
    filter_upwards [heq, hDne] with z heqz hDz
    change (E z - A z) * D z = G z
    rw [heqz, hF_eq z]
    field_simp [hDz]
    ring
  have hLeq_freq : ∃ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), L z = G z :=
    hLeq_eventually.frequently
  have hLeq_nhds : L =ᶠ[nhds τ] G :=
    (hL.frequently_eq_iff_eventually_eq hG).mp hLeq_freq
  have hvalue : L τ = G τ := hLeq_nhds.eq_of_nhds
  have hLτ : L τ = 0 := by
    change (E τ - A τ) * D τ = 0
    rw [hDτ, mul_zero]
  exact hGτ (by rw [← hvalue, hLτ])

/-- Analytic zeros are isolated unless the analytic function is locally identically zero. -/
theorem eventually_ne_zero_nhdsWithin_of_analyticAt_not_eventually_zero {D : ℂ → ℂ} {τ : ℂ}
    (hD : AnalyticAt ℂ D τ) (hDne : ¬ (∀ᶠ z in nhds τ, D z = 0)) :
    ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), D z ≠ 0 :=
  hD.eventually_eq_zero_or_eventually_ne_zero.resolve_left hDne

/-- Concrete local singularity lemma for the scalar token: at a regular point of the inner
sigmoid, an isolated zero of the outer denominator with nonzero visible multiplier forces
non-analyticity of the token coordinate. -/
theorem tokenC_not_analyticAt_of_outer_denom_isolated_zero
    (lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ : ℝ) {τ : ℂ}
    (hinner : 1 + Complex.exp (-((lam : ℂ) * τ + (b : ℂ))) ≠ 0)
    (hpole : 1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ τ)) = 0)
    (hamp : tokenVisibleAmp lam b G₀ G₁ τ ≠ 0)
    (houter_isolated : ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ),
      1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z)) ≠ 0) :
    ¬ AnalyticAt ℂ (tokenC lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂) τ := by
  have haff : AnalyticAt ℂ (fun z : ℂ => (lam : ℂ) * z + (b : ℂ)) τ :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hzc : AnalyticAt ℂ (fun z : ℂ => csig ((lam : ℂ) * z + (b : ℂ))) τ :=
    AnalyticAt.comp_of_eq' (csig_analyticAt hinner) haff rfl
  have hA : AnalyticAt ℂ
      (fun z : ℂ => (A₀ : ℂ) + (A₁ : ℂ) * csig ((lam : ℂ) * z + (b : ℂ))) τ :=
    analyticAt_const.add (analyticAt_const.mul hzc)
  have hG : AnalyticAt ℂ (tokenVisibleAmp lam b G₀ G₁) τ := by
    simpa [tokenVisibleAmp] using analyticAt_const.add (analyticAt_const.mul hzc)
  have hpsi : AnalyticAt ℂ (fun z : ℂ => (Ψ₀ : ℂ)
      + (Ψ₁ : ℂ) * csig ((lam : ℂ) * z + (b : ℂ))
      + (Ψ₂ : ℂ) * csig ((lam : ℂ) * z + (b : ℂ)) ^ 2) τ :=
    (analyticAt_const.add (analyticAt_const.mul hzc)).add (analyticAt_const.mul (hzc.pow 2))
  have houterArg : AnalyticAt ℂ (tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂) τ := by
    simpa [tokenOuterArg] using (analyticAt_id.mul hpsi).add analyticAt_const
  have hD : AnalyticAt ℂ
      (fun z : ℂ => 1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z))) τ :=
    analyticAt_const.add (houterArg.neg.cexp')
  exact not_analyticAt_of_add_inv_mul_isolated_zero
    (F := tokenC lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂)
    (A := fun z : ℂ => (A₀ : ℂ) + (A₁ : ℂ) * csig ((lam : ℂ) * z + (b : ℂ)))
    (D := fun z : ℂ => 1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z)))
    (G := tokenVisibleAmp lam b G₀ G₁)
    (by intro z; simp [tokenC, tokenOuterArg, tokenVisibleAmp, csig])
    hA hD hG hpole hamp houter_isolated

/-- Same as `tokenC_not_analyticAt_of_outer_denom_isolated_zero`, using the analytic isolated-zero
dichotomy to produce the punctured nonvanishing of the outer denominator. -/
theorem tokenC_not_analyticAt_of_outer_denom_not_eventually_zero
    (lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ : ℝ) {τ : ℂ}
    (hinner : 1 + Complex.exp (-((lam : ℂ) * τ + (b : ℂ))) ≠ 0)
    (hpole : 1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ τ)) = 0)
    (hamp : tokenVisibleAmp lam b G₀ G₁ τ ≠ 0)
    (houter_not_zero : ¬ (∀ᶠ z in nhds τ,
      1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z)) = 0)) :
    ¬ AnalyticAt ℂ (tokenC lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂) τ := by
  have haff : AnalyticAt ℂ (fun z : ℂ => (lam : ℂ) * z + (b : ℂ)) τ :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hzc : AnalyticAt ℂ (fun z : ℂ => csig ((lam : ℂ) * z + (b : ℂ))) τ :=
    AnalyticAt.comp_of_eq' (csig_analyticAt hinner) haff rfl
  have hpsi : AnalyticAt ℂ (fun z : ℂ => (Ψ₀ : ℂ)
      + (Ψ₁ : ℂ) * csig ((lam : ℂ) * z + (b : ℂ))
      + (Ψ₂ : ℂ) * csig ((lam : ℂ) * z + (b : ℂ)) ^ 2) τ :=
    (analyticAt_const.add (analyticAt_const.mul hzc)).add (analyticAt_const.mul (hzc.pow 2))
  have houterArg : AnalyticAt ℂ (tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂) τ := by
    simpa [tokenOuterArg] using (analyticAt_id.mul hpsi).add analyticAt_const
  have hD : AnalyticAt ℂ
      (fun z : ℂ => 1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z))) τ :=
    analyticAt_const.add (houterArg.neg.cexp')
  exact tokenC_not_analyticAt_of_outer_denom_isolated_zero
    lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ hinner hpole hamp
    (eventually_ne_zero_nhdsWithin_of_analyticAt_not_eventually_zero hD houter_not_zero)

/-- A concrete scalar token with a visible outer pole cannot be punctured-equal to a function
analytic at that point. -/
theorem tokenC_no_analytic_puncturedEq_of_outer_denom_not_eventually_zero
    (lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ : ℝ) {E : ℂ → ℂ} {τ : ℂ}
    (hE : AnalyticAt ℂ E τ)
    (heq : E =ᶠ[nhdsWithin τ ({τ}ᶜ : Set ℂ)]
      tokenC lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂)
    (hinner : 1 + Complex.exp (-((lam : ℂ) * τ + (b : ℂ))) ≠ 0)
    (hpole : 1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ τ)) = 0)
    (hamp : tokenVisibleAmp lam b G₀ G₁ τ ≠ 0)
    (houter_not_zero : ¬ (∀ᶠ z in nhds τ,
      1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z)) = 0)) :
    False := by
  have haff : AnalyticAt ℂ (fun z : ℂ => (lam : ℂ) * z + (b : ℂ)) τ :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hzc : AnalyticAt ℂ (fun z : ℂ => csig ((lam : ℂ) * z + (b : ℂ))) τ :=
    AnalyticAt.comp_of_eq' (csig_analyticAt hinner) haff rfl
  have hA : AnalyticAt ℂ
      (fun z : ℂ => (A₀ : ℂ) + (A₁ : ℂ) * csig ((lam : ℂ) * z + (b : ℂ))) τ :=
    analyticAt_const.add (analyticAt_const.mul hzc)
  have hG : AnalyticAt ℂ (tokenVisibleAmp lam b G₀ G₁) τ := by
    simpa [tokenVisibleAmp] using analyticAt_const.add (analyticAt_const.mul hzc)
  have hpsi : AnalyticAt ℂ (fun z : ℂ => (Ψ₀ : ℂ)
      + (Ψ₁ : ℂ) * csig ((lam : ℂ) * z + (b : ℂ))
      + (Ψ₂ : ℂ) * csig ((lam : ℂ) * z + (b : ℂ)) ^ 2) τ :=
    (analyticAt_const.add (analyticAt_const.mul hzc)).add (analyticAt_const.mul (hzc.pow 2))
  have houterArg : AnalyticAt ℂ (tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂) τ := by
    simpa [tokenOuterArg] using (analyticAt_id.mul hpsi).add analyticAt_const
  have hD : AnalyticAt ℂ
      (fun z : ℂ => 1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z))) τ :=
    analyticAt_const.add (houterArg.neg.cexp')
  exact no_analytic_puncturedEq_of_add_inv_mul_isolated_zero
    (F := tokenC lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂)
    (E := E)
    (A := fun z : ℂ => (A₀ : ℂ) + (A₁ : ℂ) * csig ((lam : ℂ) * z + (b : ℂ)))
    (D := fun z : ℂ => 1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z)))
    (G := tokenVisibleAmp lam b G₀ G₁)
    (by intro z; simp [tokenC, tokenOuterArg, tokenVisibleAmp, csig])
    hE heq hA hD hG hpole hamp
    (eventually_ne_zero_nhdsWithin_of_analyticAt_not_eventually_zero hD houter_not_zero)

/-- Part 1 bridge: visible primed outer-pole accumulation gives non-meromorphicity of the
primed scalar token once the local fact "visible outer pole implies non-analytic token" is
available. -/
theorem primed_token_not_meromorphicAt_of_visible_outer_poles
    (lam' b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ : ℝ) {ρ : ℂ → ℂ} {ζ : ℂ}
    (hρ : AnalyticAt ℂ ρ ζ) (hρ0 : ρ ζ = 0)
    (hρne : ¬ (∀ᶠ z in nhds ζ, ρ z = ρ ζ))
    (hρ_outer : ∀ᶠ τ in nhdsWithin ζ ({ζ}ᶜ : Set ℂ),
      1 / ρ τ = tokenOuterArg lam' b Ψ₀ Ψ₁ Ψ₂ τ)
    (hamp : ∀ᶠ τ in nhdsWithin ζ ({ζ}ᶜ : Set ℂ),
      tokenVisibleAmp lam' b G₀ G₁ τ ≠ 0)
    (hpole_bad : ∀ τ : ℂ, tokenVisibleAmp lam' b G₀ G₁ τ ≠ 0 →
      1 + Complex.exp (-(tokenOuterArg lam' b Ψ₀ Ψ₁ Ψ₂ τ)) = 0 →
      ¬ AnalyticAt ℂ (tokenC lam' b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂) τ) :
    ¬ MeromorphicAt (tokenC lam' b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂) ζ := by
  apply not_meromorphicAt_of_accumulating_not_analyticAt
  intro U hU
  obtain ⟨τ, hτU, hτne, hampτ, hpoleτ⟩ :=
    primed_token_visible_outer_poles_accumulate
      lam' b G₀ G₁ Ψ₀ Ψ₁ Ψ₂ hρ hρ0 hρne hρ_outer hamp hU
  exact ⟨τ, hτU, hτne, hpole_bad τ hampτ hpoleτ⟩

/-- Part 1, with the local singularity discharged by
`tokenC_not_analyticAt_of_outer_denom_not_eventually_zero`.  The remaining inputs are the
reciprocal extension of the outer argument and the regularity/nontriviality facts used to
instantiate the visible-pole accumulation argument. -/
theorem primed_token_not_meromorphicAt_of_visible_outer_poles_regular
    (lam' b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ : ℝ) {ρ : ℂ → ℂ} {ζ : ℂ}
    (hρ : AnalyticAt ℂ ρ ζ) (hρ0 : ρ ζ = 0)
    (hρne : ¬ (∀ᶠ z in nhds ζ, ρ z = ρ ζ))
    (hρ_outer : ∀ᶠ τ in nhdsWithin ζ ({ζ}ᶜ : Set ℂ),
      1 / ρ τ = tokenOuterArg lam' b Ψ₀ Ψ₁ Ψ₂ τ)
    (hinner : ∀ᶠ τ in nhdsWithin ζ ({ζ}ᶜ : Set ℂ),
      1 + Complex.exp (-((lam' : ℂ) * τ + (b : ℂ))) ≠ 0)
    (hamp : ∀ᶠ τ in nhdsWithin ζ ({ζ}ᶜ : Set ℂ),
      tokenVisibleAmp lam' b G₀ G₁ τ ≠ 0)
    (houter_not_zero : ∀ τ : ℂ,
      1 + Complex.exp (-((lam' : ℂ) * τ + (b : ℂ))) ≠ 0 →
      tokenVisibleAmp lam' b G₀ G₁ τ ≠ 0 →
      1 + Complex.exp (-(tokenOuterArg lam' b Ψ₀ Ψ₁ Ψ₂ τ)) = 0 →
      ¬ (∀ᶠ z in nhds τ,
        1 + Complex.exp (-(tokenOuterArg lam' b Ψ₀ Ψ₁ Ψ₂ z)) = 0)) :
    ¬ MeromorphicAt (tokenC lam' b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂) ζ := by
  apply not_meromorphicAt_of_accumulating_not_analyticAt
  intro U hU
  rw [eventually_nhdsWithin_iff] at hρ_outer
  rw [eventually_nhdsWithin_iff] at hinner
  rw [eventually_nhdsWithin_iff] at hamp
  have hside : ∀ᶠ τ in nhds ζ,
      τ ≠ ζ →
        1 / ρ τ = tokenOuterArg lam' b Ψ₀ Ψ₁ Ψ₂ τ ∧
          1 + Complex.exp (-((lam' : ℂ) * τ + (b : ℂ))) ≠ 0 ∧
          tokenVisibleAmp lam' b G₀ G₁ τ ≠ 0 := by
    filter_upwards [hρ_outer, hinner, hamp] with τ houterτ hinnerτ hampτ hτne
    exact ⟨houterτ hτne, hinnerτ hτne, hampτ hτne⟩
  have hUside :
      U ∩ {τ : ℂ | τ = ζ ∨
        (1 / ρ τ = tokenOuterArg lam' b Ψ₀ Ψ₁ Ψ₂ τ ∧
          1 + Complex.exp (-((lam' : ℂ) * τ + (b : ℂ))) ≠ 0 ∧
          tokenVisibleAmp lam' b G₀ G₁ τ ≠ 0)} ∈ nhds ζ := by
    refine Filter.inter_mem hU ?_
    filter_upwards [hside] with τ hτ
    by_cases hτζ : τ = ζ
    · exact Or.inl hτζ
    · exact Or.inr (hτ hτζ)
  obtain ⟨τ, hτ, hτne, _, hpole⟩ :=
    visible_outer_sigmoid_poles_accumulate
      (ρ := ρ) (amp := fun _ : ℂ => (1 : ℂ))
      hρ hρ0 hρne (Filter.Eventually.of_forall fun _ => one_ne_zero) hUside
  have hsideτ : 1 / ρ τ = tokenOuterArg lam' b Ψ₀ Ψ₁ Ψ₂ τ ∧
      1 + Complex.exp (-((lam' : ℂ) * τ + (b : ℂ))) ≠ 0 ∧
      tokenVisibleAmp lam' b G₀ G₁ τ ≠ 0 := by
    rcases hτ.2 with hτζ | hsideτ
    · exact absurd hτζ hτne
    · exact hsideτ
  have hpole' : 1 + Complex.exp (-(tokenOuterArg lam' b Ψ₀ Ψ₁ Ψ₂ τ)) = 0 := by
    rw [← hsideτ.1]
    exact hpole
  exact ⟨τ, hτ.1, hτne,
    tokenC_not_analyticAt_of_outer_denom_not_eventually_zero
      lam' b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ hsideτ.2.1 hpole' hsideτ.2.2
      (houter_not_zero τ hsideτ.2.1 hsideτ.2.2 hpole')⟩

theorem primed_token_not_meromorphicAt_sigmoidPole_of_regular_outer
    (lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ : ℝ) {n : ℤ}
    (hlam : lam ≠ 0) (hζ : sigmoidPole b lam n ≠ 0)
    (hψ : Ψ₁ ≠ 0 ∨ Ψ₂ ≠ 0) (hG : G₀ ≠ 0 ∨ G₁ ≠ 0)
    (houter_not_zero : ∀ τ : ℂ,
      1 + Complex.exp (-((lam : ℂ) * τ + (b : ℂ))) ≠ 0 →
      tokenVisibleAmp lam b G₀ G₁ τ ≠ 0 →
      1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ τ)) = 0 →
      ¬ (∀ᶠ z in nhds τ,
        1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z)) = 0)) :
    ¬ MeromorphicAt (tokenC lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂) (sigmoidPole b lam n) := by
  by_cases hΨ₂ : Ψ₂ = 0
  · have hΨ₁ : Ψ₁ ≠ 0 := by
      rcases hψ with hΨ₁ | hΨ₂ne
      · exact hΨ₁
      · exact False.elim (hΨ₂ne hΨ₂)
    exact primed_token_not_meromorphicAt_of_visible_outer_poles_regular
      lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂
      (ρ := tokenOuterRhoLinear lam b Ψ₀ Ψ₁)
      (tokenOuterRhoLinear_analyticAt_sigmoidPole b lam Ψ₀ Ψ₁ hlam hζ hΨ₁)
      (by simpa using tokenOuterRhoLinear_zero_sigmoidPole b lam Ψ₀ Ψ₁ hlam hζ hΨ₁)
      (tokenOuterRhoLinear_not_eventuallyConst_sigmoidPole b lam Ψ₀ Ψ₁ hlam hζ hΨ₁)
      (tokenOuterRhoLinear_outerArg_nhdsWithin_sigmoidPole b lam Ψ₀ Ψ₁ Ψ₂ hlam hΨ₂)
      (inner_denom_eventually_ne_zero_nhdsWithin_sigmoidPole b lam hlam n)
      (tokenVisibleAmp_eventually_ne_zero_nhdsWithin_sigmoidPole b lam G₀ G₁ hlam n hG)
      houter_not_zero
  · exact primed_token_not_meromorphicAt_of_visible_outer_poles_regular
      lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂
      (ρ := tokenOuterRhoQuadratic lam b Ψ₀ Ψ₁ Ψ₂)
      (tokenOuterRhoQuadratic_analyticAt_sigmoidPole b lam Ψ₀ Ψ₁ Ψ₂ hlam hζ hΨ₂)
      (by simpa using tokenOuterRhoQuadratic_zero_sigmoidPole b lam Ψ₀ Ψ₁ Ψ₂ hlam hζ hΨ₂)
      (tokenOuterRhoQuadratic_not_eventuallyConst_sigmoidPole b lam Ψ₀ Ψ₁ Ψ₂ hlam hζ hΨ₂)
      (tokenOuterRhoQuadratic_outerArg_nhdsWithin_sigmoidPole b lam Ψ₀ Ψ₁ Ψ₂ hlam)
      (inner_denom_eventually_ne_zero_nhdsWithin_sigmoidPole b lam hlam n)
      (tokenVisibleAmp_eventually_ne_zero_nhdsWithin_sigmoidPole b lam G₀ G₁ hlam n hG)
      houter_not_zero

/-! #### Step 2 (isolatedness contradiction), consolidated from `scratch_step2` -/

/-- **Step 2, core (isolatedness contradiction).**  If the unprimed token is meromorphic at `ζ`
whenever `ζ` is not an inner pole, the two tokens agree on a punctured neighbourhood of `ζ`, and
the primed token is not meromorphic at `ζ`, then `ζ` is an unprimed inner pole. -/
theorem inner_pole_of_not_meromorphic {lam b : ℝ} {FC FC' : ℂ → ℂ} {ζ : ℂ}
    (hmero_FC : 1 + Complex.exp (-((lam : ℂ) * ζ + (b : ℂ))) ≠ 0 → MeromorphicAt FC ζ)
    (heq : FC =ᶠ[nhdsWithin ζ ({ζ}ᶜ : Set ℂ)] FC')
    (hnotmero' : ¬ MeromorphicAt FC' ζ) :
    1 + Complex.exp (-((lam : ℂ) * ζ + (b : ℂ))) = 0 := by
  by_contra hne
  exact hnotmero' ((hmero_FC hne).congr heq)

/-- An inner-pole equation forces a nonzero slope (its solution has nonzero imaginary part). -/
theorem lam_ne_zero_of_inner_pole {lam b : ℝ} {ζ : ℂ}
    (h : 1 + Complex.exp (-((lam : ℂ) * ζ + (b : ℂ))) = 0) : lam ≠ 0 := by
  intro hlam0
  rw [hlam0] at h
  simp only [Complex.ofReal_zero, zero_mul, zero_add] at h
  exact one_add_exp_neg_ofReal_ne_zero b h

/-- An inner-pole equation at `ζ` with nonzero slope exhibits `ζ` as a `sigmoidPole`. -/
theorem exists_sigmoidPole_eq_of_inner_pole {lam b : ℝ} {ζ : ℂ} (hlam : lam ≠ 0)
    (h : 1 + Complex.exp (-((lam : ℂ) * ζ + (b : ℂ))) = 0) :
    ∃ m : ℤ, ζ = sigmoidPole b lam m := by
  rw [one_add_exp_neg_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hlamC : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
  refine ⟨k, ?_⟩
  rw [sigmoidPole, eq_div_iff hlamC]
  push_cast at hk ⊢
  linear_combination hk

/-- **Step 2 (assembled).**  At a primed first-layer pole `sigmoidPole b lam' n`, the
isolatedness inputs give: the unprimed slope `lam` is nonzero, and the primed pole is an
unprimed pole `sigmoidPole b lam m`. -/
theorem step2_pole_inclusion {lam lam' b : ℝ} {FC FC' : ℂ → ℂ} (n : ℤ)
    (hmero_FC : ∀ ζ : ℂ, 1 + Complex.exp (-((lam : ℂ) * ζ + (b : ℂ))) ≠ 0 → MeromorphicAt FC ζ)
    (heq : FC =ᶠ[nhdsWithin (sigmoidPole b lam' n) ({sigmoidPole b lam' n}ᶜ : Set ℂ)] FC')
    (hnotmero' : ¬ MeromorphicAt FC' (sigmoidPole b lam' n)) :
    lam ≠ 0 ∧ ∃ m : ℤ, sigmoidPole b lam' n = sigmoidPole b lam m := by
  have hpole := inner_pole_of_not_meromorphic (hmero_FC _) heq hnotmero'
  have hlam := lam_ne_zero_of_inner_pole hpole
  exact ⟨hlam, exists_sigmoidPole_eq_of_inner_pole hlam hpole⟩

/-! #### (A) Global analytic continuation -/

/-- The inner-pole set of one sigmoid is countable. -/
theorem countable_innerPoleSet (b lam : ℝ) :
    {z : ℂ | 1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) = 0}.Countable := by
  by_cases hlam : lam = 0
  · have hempty : {z : ℂ | 1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) = 0} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, hlam,
        Complex.ofReal_zero, zero_mul, zero_add]
      exact one_add_exp_neg_ofReal_ne_zero b
    rw [hempty]; exact Set.countable_empty
  · refine (Set.countable_range (sigmoidPole b lam)).mono (fun z hz => ?_)
    obtain ⟨m, hm⟩ := exists_sigmoidPole_eq_of_inner_pole hlam hz
    exact ⟨m, hm.symm⟩

theorem tokenOuterArg_not_eventuallyConst_at_outerPole
    (lam b Ψ₀ Ψ₁ Ψ₂ : ℝ) {τ : ℂ}
    (hinnerτ : 1 + Complex.exp (-((lam : ℂ) * τ + (b : ℂ))) ≠ 0)
    (hpoleτ : 1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ τ)) = 0) :
    ¬ (∀ᶠ z in nhds τ,
      tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z = tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ τ) := by
  intro hconst
  set H : ℂ → ℂ := tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ with hHdef
  set U : Set ℂ := {z | 1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) ≠ 0} with hUdef
  have hUcompl :
      U = ({z : ℂ | 1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) = 0})ᶜ := by
    rw [hUdef]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
  have hUconn : IsPreconnected U := by
    rw [hUcompl]
    exact ((countable_innerPoleSet b lam).isPathConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected
  have hHU : AnalyticOnNhd ℂ H U := by
    intro z hz
    have hz' : 1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) ≠ 0 := by
      simpa [U, hUdef] using hz
    exact tokenOuterArg_analyticAt_of_inner_ne lam b Ψ₀ Ψ₁ Ψ₂ hz'
  have hCU : AnalyticOnNhd ℂ (fun _ : ℂ => H τ) U := by
    intro z hz
    exact analyticAt_const
  have hτU : τ ∈ U := by
    rw [hUdef]
    exact hinnerτ
  have heqOn : Set.EqOn H (fun _ : ℂ => H τ) U :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hHU hCU hUconn hτU (by
      simpa [H, hHdef] using hconst)
  have h1U : ((1 : ℝ) : ℂ) ∈ U := by
    rw [hUdef]
    change 1 + Complex.exp (-((lam : ℂ) * ((1 : ℝ) : ℂ) + (b : ℂ))) ≠ 0
    rw [show (lam : ℂ) * ((1 : ℝ) : ℂ) + (b : ℂ) = ((lam + b : ℝ) : ℂ) by
      push_cast; ring]
    exact one_add_exp_neg_ofReal_ne_zero _
  have hH1eq : H ((1 : ℝ) : ℂ) = H τ := heqOn h1U
  have hpole1 : 1 + Complex.exp (-(H ((1 : ℝ) : ℂ))) = 0 := by
    rw [hH1eq]
    simpa [H, hHdef] using hpoleτ
  have hH1real : H ((1 : ℝ) : ℂ)
      = (((Ψ₀ + Ψ₁ * sig (lam + b) + Ψ₂ * sig (lam + b) ^ 2) + b : ℝ) : ℂ) := by
    rw [hHdef, tokenOuterArg]
    have hz : csig ((lam : ℂ) * ((1 : ℝ) : ℂ) + (b : ℂ))
        = ((sig (lam + b) : ℝ) : ℂ) := by
      rw [show (lam : ℂ) * ((1 : ℝ) : ℂ) + (b : ℂ) = ((lam + b : ℝ) : ℂ) by
        push_cast; ring, csig_ofReal]
    rw [hz]
    push_cast
    ring
  rw [hH1real] at hpole1
  exact one_add_exp_neg_ofReal_ne_zero
    ((Ψ₀ + Ψ₁ * sig (lam + b) + Ψ₂ * sig (lam + b) ^ 2) + b) hpole1

theorem outer_denom_eventually_ne_zero_nhdsWithin_of_inner_regular
    (lam b Ψ₀ Ψ₁ Ψ₂ : ℝ) {ζ : ℂ}
    (hinnerζ : 1 + Complex.exp (-((lam : ℂ) * ζ + (b : ℂ))) ≠ 0) :
    ∀ᶠ z in nhdsWithin ζ ({ζ}ᶜ : Set ℂ),
      1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z)) ≠ 0 := by
  set D : ℂ → ℂ := fun z => 1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z)) with hDdef
  have hH : AnalyticAt ℂ (tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂) ζ :=
    tokenOuterArg_analyticAt_of_inner_ne lam b Ψ₀ Ψ₁ Ψ₂ hinnerζ
  have hD : AnalyticAt ℂ D ζ := by
    rw [hDdef]
    exact analyticAt_const.add (hH.neg.cexp')
  by_cases hDζ : D ζ = 0
  · have hDnot : ¬ (∀ᶠ z in nhds ζ, D z = 0) := by
      rw [hDdef] at hDζ ⊢
      exact outer_denom_not_eventually_zero_of_arg_not_eventually_const hH
        (tokenOuterArg_not_eventuallyConst_at_outerPole lam b Ψ₀ Ψ₁ Ψ₂ hinnerζ hDζ)
        hDζ
    simpa [D, hDdef] using
      eventually_ne_zero_nhdsWithin_of_analyticAt_not_eventually_zero hD hDnot
  · have hnear : ∀ᶠ z in nhds ζ, D z ≠ 0 := hD.continuousAt.eventually_ne hDζ
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (by
      simpa [D, hDdef] using hnear)

theorem tokenOuterArg_not_eventuallyConst_of_rho_at_innerPole
    (lam b Ψ₀ Ψ₁ Ψ₂ : ℝ) {ρ : ℂ → ℂ} {ζ τ : ℂ}
    (hρ : AnalyticAt ℂ ρ ζ) (hρ0 : ρ ζ = 0)
    (hρ_outer : ∀ᶠ z in nhdsWithin ζ ({ζ}ᶜ : Set ℂ),
      1 / ρ z = tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z)
    (hinnerζ : ∀ᶠ z in nhdsWithin ζ ({ζ}ᶜ : Set ℂ),
      1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) ≠ 0)
    (hinnerτ : 1 + Complex.exp (-((lam : ℂ) * τ + (b : ℂ))) ≠ 0)
    (hpoleτ : 1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ τ)) = 0) :
    ¬ (∀ᶠ z in nhds τ,
      tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z = tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ τ) := by
  intro hconst
  set H : ℂ → ℂ := tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ with hHdef
  set U : Set ℂ := {z | 1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) ≠ 0} with hUdef
  have hc : H τ ≠ 0 := by
    intro h0
    have hbad : 1 + Complex.exp (-(0 : ℂ)) = 0 := by
      simpa [H, hHdef, h0] using hpoleτ
    norm_num at hbad
  have hUcompl :
      U = ({z : ℂ | 1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) = 0})ᶜ := by
    rw [hUdef]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
  have hUconn : IsPreconnected U := by
    rw [hUcompl]
    exact ((countable_innerPoleSet b lam).isPathConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected
  have hHU : AnalyticOnNhd ℂ H U := by
    intro z hz
    have hz' : 1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) ≠ 0 := by
      simpa [U, hUdef] using hz
    exact tokenOuterArg_analyticAt_of_inner_ne lam b Ψ₀ Ψ₁ Ψ₂ hz'
  have hCU : AnalyticOnNhd ℂ (fun _ : ℂ => H τ) U := by
    intro z hz
    exact analyticAt_const
  have hτU : τ ∈ U := by
    rw [hUdef]
    exact hinnerτ
  have heqOn : Set.EqOn H (fun _ : ℂ => H τ) U :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hHU hCU hUconn hτU (by
      simpa [H, hHdef] using hconst)
  have hρ_const : ∀ᶠ z in nhdsWithin ζ ({ζ}ᶜ : Set ℂ), ρ z = (H τ)⁻¹ := by
    filter_upwards [hρ_outer, hinnerζ] with z hρz hinnerz
    have hzU : z ∈ U := by
      rw [hUdef]
      exact hinnerz
    have hHz : H z = H τ := heqOn hzU
    have hρz' : 1 / ρ z = H τ := by
      rw [hρz]
      simpa [H, hHdef] using hHz
    have hρzne : ρ z ≠ 0 := by
      intro h0
      rw [h0] at hρz'
      exact hc (by simpa using hρz'.symm)
    field_simp [hρzne, hc] at hρz' ⊢
    exact hρz'.symm
  have hρ_const_nhds : ρ =ᶠ[nhds ζ] fun _ : ℂ => (H τ)⁻¹ :=
    (hρ.frequently_eq_iff_eventually_eq analyticAt_const).mp hρ_const.frequently
  have hval : ρ ζ = (H τ)⁻¹ := hρ_const_nhds.eq_of_nhds
  rw [hρ0] at hval
  exact (inv_ne_zero hc) hval.symm

theorem primed_token_not_meromorphicAt_sigmoidPole
    (lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ : ℝ) {n : ℤ}
    (hlam : lam ≠ 0) (hζ : sigmoidPole b lam n ≠ 0)
    (hψ : Ψ₁ ≠ 0 ∨ Ψ₂ ≠ 0) (hG : G₀ ≠ 0 ∨ G₁ ≠ 0) :
    ¬ MeromorphicAt (tokenC lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂) (sigmoidPole b lam n) := by
  by_cases hΨ₂ : Ψ₂ = 0
  · have hΨ₁ : Ψ₁ ≠ 0 := by
      rcases hψ with hΨ₁ | hΨ₂ne
      · exact hΨ₁
      · exact False.elim (hΨ₂ne hΨ₂)
    exact primed_token_not_meromorphicAt_sigmoidPole_of_regular_outer
      lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ hlam hζ hψ hG
      (by
        intro τ hinnerτ hampτ hpoleτ
        exact outer_denom_not_eventually_zero_of_arg_not_eventually_const
          (tokenOuterArg_analyticAt_of_inner_ne lam b Ψ₀ Ψ₁ Ψ₂ hinnerτ)
          (tokenOuterArg_not_eventuallyConst_of_rho_at_innerPole
            lam b Ψ₀ Ψ₁ Ψ₂
            (ρ := tokenOuterRhoLinear lam b Ψ₀ Ψ₁)
            (ζ := sigmoidPole b lam n) (τ := τ)
            (tokenOuterRhoLinear_analyticAt_sigmoidPole b lam Ψ₀ Ψ₁ hlam hζ hΨ₁)
            (by simpa using tokenOuterRhoLinear_zero_sigmoidPole b lam Ψ₀ Ψ₁ hlam hζ hΨ₁)
            (tokenOuterRhoLinear_outerArg_nhdsWithin_sigmoidPole b lam Ψ₀ Ψ₁ Ψ₂ hlam hΨ₂)
            (inner_denom_eventually_ne_zero_nhdsWithin_sigmoidPole b lam hlam n)
            hinnerτ hpoleτ)
          hpoleτ)
  · exact primed_token_not_meromorphicAt_sigmoidPole_of_regular_outer
      lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ hlam hζ hψ hG
      (by
        intro τ hinnerτ hampτ hpoleτ
        exact outer_denom_not_eventually_zero_of_arg_not_eventually_const
          (tokenOuterArg_analyticAt_of_inner_ne lam b Ψ₀ Ψ₁ Ψ₂ hinnerτ)
          (tokenOuterArg_not_eventuallyConst_of_rho_at_innerPole
            lam b Ψ₀ Ψ₁ Ψ₂
            (ρ := tokenOuterRhoQuadratic lam b Ψ₀ Ψ₁ Ψ₂)
            (ζ := sigmoidPole b lam n) (τ := τ)
            (tokenOuterRhoQuadratic_analyticAt_sigmoidPole b lam Ψ₀ Ψ₁ Ψ₂ hlam hζ hΨ₂)
            (by simpa using tokenOuterRhoQuadratic_zero_sigmoidPole b lam Ψ₀ Ψ₁ Ψ₂ hlam hζ hΨ₂)
            (tokenOuterRhoQuadratic_outerArg_nhdsWithin_sigmoidPole b lam Ψ₀ Ψ₁ Ψ₂ hlam)
            (inner_denom_eventually_ne_zero_nhdsWithin_sigmoidPole b lam hlam n)
            hinnerτ hpoleτ)
          hpoleτ)

theorem scalar_primed_innerPole_forces_unprimed_innerPole
    (lam lam' b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ Ψ₀' Ψ₁' Ψ₂' : ℝ) {n : ℤ}
    (hlam' : lam' ≠ 0) (hζne : sigmoidPole b lam' n ≠ 0)
    (hψ' : Ψ₁' ≠ 0 ∨ Ψ₂' ≠ 0) (hG : G₀ ≠ 0 ∨ G₁ ≠ 0)
    (hcont : ∀ {η : ℂ},
      1 + Complex.exp (-((lam : ℂ) * η + (b : ℂ))) ≠ 0 →
      1 + Complex.exp (-((lam' : ℂ) * η + (b : ℂ))) ≠ 0 →
      tokenC lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂
        =ᶠ[nhdsWithin η ({η}ᶜ : Set ℂ)]
          tokenC lam' b A₀ A₁ G₀ G₁ Ψ₀' Ψ₁' Ψ₂') :
    1 + Complex.exp (-((lam : ℂ) * sigmoidPole b lam' n + (b : ℂ))) = 0 := by
  set ζ : ℂ := sigmoidPole b lam' n with hζdef
  change 1 + Complex.exp (-((lam : ℂ) * ζ + (b : ℂ))) = 0
  by_contra hinnerζ
  have hinner_un_nhds : ∀ᶠ z in nhds ζ,
      1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) ≠ 0 := by
    have hnear := (innerDenom_analyticAt lam b ζ).continuousAt.eventually_ne
      (by simpa [innerDenom] using hinnerζ)
    simpa [innerDenom] using hnear
  have hinner_un : ∀ᶠ z in nhdsWithin ζ ({ζ}ᶜ : Set ℂ),
      1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) ≠ 0 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hinner_un_nhds
  have houter_un : ∀ᶠ z in nhdsWithin ζ ({ζ}ᶜ : Set ℂ),
      1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z)) ≠ 0 := by
    simpa using outer_denom_eventually_ne_zero_nhdsWithin_of_inner_regular
      lam b Ψ₀ Ψ₁ Ψ₂ hinnerζ
  have hinner_prime : ∀ᶠ z in nhdsWithin ζ ({ζ}ᶜ : Set ℂ),
      1 + Complex.exp (-((lam' : ℂ) * z + (b : ℂ))) ≠ 0 := by
    simpa [ζ, hζdef] using inner_denom_eventually_ne_zero_nhdsWithin_sigmoidPole b lam' hlam' n
  have hside_within : ∀ᶠ z in nhdsWithin ζ ({ζ}ᶜ : Set ℂ),
      1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) ≠ 0 ∧
      1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z)) ≠ 0 ∧
      1 + Complex.exp (-((lam' : ℂ) * z + (b : ℂ))) ≠ 0 := by
    filter_upwards [hinner_un, houter_un, hinner_prime] with z hun hout hp
    exact ⟨hun, hout, hp⟩
  rw [eventually_nhdsWithin_iff] at hside_within
  have hU : {z : ℂ | z = ζ ∨
      (1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) ≠ 0 ∧
      1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ z)) ≠ 0 ∧
      1 + Complex.exp (-((lam' : ℂ) * z + (b : ℂ))) ≠ 0)} ∈ nhds ζ := by
    filter_upwards [hside_within] with z hz
    by_cases hzζ : z = ζ
    · exact Or.inl hzζ
    · exact Or.inr (hz hzζ)
  by_cases hΨ₂' : Ψ₂' = 0
  · have hΨ₁' : Ψ₁' ≠ 0 := by
      rcases hψ' with hΨ₁' | hΨ₂'ne
      · exact hΨ₁'
      · exact False.elim (hΨ₂'ne hΨ₂')
    have hρ : AnalyticAt ℂ (tokenOuterRhoLinear lam' b Ψ₀' Ψ₁') ζ := by
      simpa [ζ, hζdef] using
        tokenOuterRhoLinear_analyticAt_sigmoidPole b lam' Ψ₀' Ψ₁' hlam' hζne hΨ₁'
    have hρ0 : tokenOuterRhoLinear lam' b Ψ₀' Ψ₁' ζ = 0 := by
      simpa [ζ, hζdef] using
        tokenOuterRhoLinear_zero_sigmoidPole b lam' Ψ₀' Ψ₁' hlam' hζne hΨ₁'
    have hρne : ¬ (∀ᶠ z in nhds ζ,
        tokenOuterRhoLinear lam' b Ψ₀' Ψ₁' z = tokenOuterRhoLinear lam' b Ψ₀' Ψ₁' ζ) := by
      simpa [ζ, hζdef] using
        tokenOuterRhoLinear_not_eventuallyConst_sigmoidPole b lam' Ψ₀' Ψ₁' hlam' hζne hΨ₁'
    have hρ_outer : ∀ᶠ z in nhdsWithin ζ ({ζ}ᶜ : Set ℂ),
        1 / tokenOuterRhoLinear lam' b Ψ₀' Ψ₁' z =
          tokenOuterArg lam' b Ψ₀' Ψ₁' Ψ₂' z := by
      simpa [ζ, hζdef] using
        tokenOuterRhoLinear_outerArg_nhdsWithin_sigmoidPole b lam' Ψ₀' Ψ₁' Ψ₂' hlam' hΨ₂'
    obtain ⟨τ, hτU, hτne, hampτ, hpoleτ⟩ :=
      primed_token_visible_outer_poles_accumulate
        lam' b G₀ G₁ Ψ₀' Ψ₁' Ψ₂'
        (ρ := tokenOuterRhoLinear lam' b Ψ₀' Ψ₁')
        hρ hρ0 hρne hρ_outer
        (by
          simpa [ζ, hζdef] using
            tokenVisibleAmp_eventually_ne_zero_nhdsWithin_sigmoidPole b lam' G₀ G₁ hlam' n hG)
        hU
    have hτside :
        1 + Complex.exp (-((lam : ℂ) * τ + (b : ℂ))) ≠ 0 ∧
        1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ τ)) ≠ 0 ∧
        1 + Complex.exp (-((lam' : ℂ) * τ + (b : ℂ))) ≠ 0 := by
      rcases hτU with hτζ | hτside
      · exact False.elim (hτne hτζ)
      · exact hτside
    have houter_not_zero' : ¬ (∀ᶠ z in nhds τ,
        1 + Complex.exp (-(tokenOuterArg lam' b Ψ₀' Ψ₁' Ψ₂' z)) = 0) :=
      outer_denom_not_eventually_zero_of_arg_not_eventually_const
        (tokenOuterArg_analyticAt_of_inner_ne lam' b Ψ₀' Ψ₁' Ψ₂' hτside.2.2)
        (tokenOuterArg_not_eventuallyConst_of_rho_at_innerPole
          lam' b Ψ₀' Ψ₁' Ψ₂'
          (ρ := tokenOuterRhoLinear lam' b Ψ₀' Ψ₁') (ζ := ζ) (τ := τ)
          hρ hρ0 hρ_outer hinner_prime hτside.2.2 hpoleτ)
        hpoleτ
    exact tokenC_no_analytic_puncturedEq_of_outer_denom_not_eventually_zero
      lam' b A₀ A₁ G₀ G₁ Ψ₀' Ψ₁' Ψ₂'
      (E := tokenC lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂)
      (tokenC_analyticAt_of_inner_outer_ne lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ hτside.1 hτside.2.1)
      (hcont (η := τ) hτside.1 hτside.2.2)
      hτside.2.2 hpoleτ hampτ houter_not_zero'
  · have hρ : AnalyticAt ℂ (tokenOuterRhoQuadratic lam' b Ψ₀' Ψ₁' Ψ₂') ζ := by
      simpa [ζ, hζdef] using
        tokenOuterRhoQuadratic_analyticAt_sigmoidPole b lam' Ψ₀' Ψ₁' Ψ₂' hlam' hζne hΨ₂'
    have hρ0 : tokenOuterRhoQuadratic lam' b Ψ₀' Ψ₁' Ψ₂' ζ = 0 := by
      simpa [ζ, hζdef] using
        tokenOuterRhoQuadratic_zero_sigmoidPole b lam' Ψ₀' Ψ₁' Ψ₂' hlam' hζne hΨ₂'
    have hρne : ¬ (∀ᶠ z in nhds ζ,
        tokenOuterRhoQuadratic lam' b Ψ₀' Ψ₁' Ψ₂' z =
          tokenOuterRhoQuadratic lam' b Ψ₀' Ψ₁' Ψ₂' ζ) := by
      simpa [ζ, hζdef] using
        tokenOuterRhoQuadratic_not_eventuallyConst_sigmoidPole b lam' Ψ₀' Ψ₁' Ψ₂' hlam' hζne hΨ₂'
    have hρ_outer : ∀ᶠ z in nhdsWithin ζ ({ζ}ᶜ : Set ℂ),
        1 / tokenOuterRhoQuadratic lam' b Ψ₀' Ψ₁' Ψ₂' z =
          tokenOuterArg lam' b Ψ₀' Ψ₁' Ψ₂' z := by
      simpa [ζ, hζdef] using
        tokenOuterRhoQuadratic_outerArg_nhdsWithin_sigmoidPole b lam' Ψ₀' Ψ₁' Ψ₂' hlam'
    obtain ⟨τ, hτU, hτne, hampτ, hpoleτ⟩ :=
      primed_token_visible_outer_poles_accumulate
        lam' b G₀ G₁ Ψ₀' Ψ₁' Ψ₂'
        (ρ := tokenOuterRhoQuadratic lam' b Ψ₀' Ψ₁' Ψ₂')
        hρ hρ0 hρne hρ_outer
        (by
          simpa [ζ, hζdef] using
            tokenVisibleAmp_eventually_ne_zero_nhdsWithin_sigmoidPole b lam' G₀ G₁ hlam' n hG)
        hU
    have hτside :
        1 + Complex.exp (-((lam : ℂ) * τ + (b : ℂ))) ≠ 0 ∧
        1 + Complex.exp (-(tokenOuterArg lam b Ψ₀ Ψ₁ Ψ₂ τ)) ≠ 0 ∧
        1 + Complex.exp (-((lam' : ℂ) * τ + (b : ℂ))) ≠ 0 := by
      rcases hτU with hτζ | hτside
      · exact False.elim (hτne hτζ)
      · exact hτside
    have houter_not_zero' : ¬ (∀ᶠ z in nhds τ,
        1 + Complex.exp (-(tokenOuterArg lam' b Ψ₀' Ψ₁' Ψ₂' z)) = 0) :=
      outer_denom_not_eventually_zero_of_arg_not_eventually_const
        (tokenOuterArg_analyticAt_of_inner_ne lam' b Ψ₀' Ψ₁' Ψ₂' hτside.2.2)
        (tokenOuterArg_not_eventuallyConst_of_rho_at_innerPole
          lam' b Ψ₀' Ψ₁' Ψ₂'
          (ρ := tokenOuterRhoQuadratic lam' b Ψ₀' Ψ₁' Ψ₂') (ζ := ζ) (τ := τ)
          hρ hρ0 hρ_outer hinner_prime hτside.2.2 hpoleτ)
        hpoleτ
    exact tokenC_no_analytic_puncturedEq_of_outer_denom_not_eventually_zero
      lam' b A₀ A₁ G₀ G₁ Ψ₀' Ψ₁' Ψ₂'
      (E := tokenC lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂)
      (tokenC_analyticAt_of_inner_outer_ne lam b A₀ A₁ G₀ G₁ Ψ₀ Ψ₁ Ψ₂ hτside.1 hτside.2.1)
      (hcont (η := τ) hτside.1 hτside.2.2)
      hτside.2.2 hpoleτ hampτ houter_not_zero'

/-- **(A) Global continuation.**  For a complex point `η` that is an inner pole of *neither*
sigmoid, the two complexified network coordinates agree on a punctured neighbourhood of `η`.
Obtained by spreading the order-`⊤` (locally-zero) property of the difference from the positive
real axis across `ℂ` minus the (countable, hence connected-complement) inner-pole set. -/
theorem tokenCnet_eventuallyEq_nhdsNE_of_not_innerPole {d : ℕ} (r : ℕ) (hr : 0 < r)
    (V₁ A₁ V₂ A₂ A₁' A₂' : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ) (i : Fin d)
    (hagree : ∀ c : ℝ, network ((V₁, A₁), (V₂, A₂)) (twoType r d u v c)
        = network ((V₁, A₁'), (V₂, A₂')) (twoType r d u v c))
    {η : ℂ}
    (hη : 1 + Complex.exp (-((((u - v) ⬝ᵥ A₁.mulVec v : ℝ) : ℂ) * η + (Real.log r : ℂ))) ≠ 0)
    (hη' : 1 + Complex.exp (-((((u - v) ⬝ᵥ A₁'.mulVec v : ℝ) : ℂ) * η + (Real.log r : ℂ))) ≠ 0) :
    tokenCnet r V₁ A₁ V₂ A₂ u v i =ᶠ[nhdsWithin η ({η}ᶜ : Set ℂ)]
      tokenCnet r V₁ A₁' V₂ A₂' u v i := by
  set lam : ℝ := (u - v) ⬝ᵥ A₁.mulVec v with hlamdef
  set lam' : ℝ := (u - v) ⬝ᵥ A₁'.mulVec v with hlamdef'
  set b : ℝ := Real.log r with hbdef
  set FC := tokenCnet r V₁ A₁ V₂ A₂ u v i with hFCdef
  set FC' := tokenCnet r V₁ A₁' V₂ A₂' u v i with hFCdef'
  set U : Set ℂ := {z | 1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) ≠ 0
      ∧ 1 + Complex.exp (-((lam' : ℂ) * z + (b : ℂ))) ≠ 0} with hUdef
  have hUcompl : U = ({z : ℂ | 1 + Complex.exp (-((lam : ℂ) * z + (b : ℂ))) = 0}
      ∪ {z : ℂ | 1 + Complex.exp (-((lam' : ℂ) * z + (b : ℂ))) = 0})ᶜ := by
    rw [hUdef]; ext z; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_union, not_or]
  have hUconn : IsPreconnected U := by
    rw [hUcompl]
    exact (((countable_innerPoleSet b lam).union (countable_innerPoleSet b lam')).isPathConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected
  have hFCmero : MeromorphicOn FC U := fun z hz =>
    tokenCnet_meromorphicAt r V₁ A₁ V₂ A₂ u v i ((hUdef ▸ hz).1)
  have hFC'mero : MeromorphicOn FC' U := fun z hz =>
    tokenCnet_meromorphicAt r V₁ A₁' V₂ A₂' u v i ((hUdef ▸ hz).2)
  have hdmero : MeromorphicOn (FC - FC') U := hFCmero.sub hFC'mero
  have h1U : ((1 : ℝ) : ℂ) ∈ U := by
    rw [hUdef]
    refine ⟨?_, ?_⟩
    · rw [show (lam : ℂ) * ((1 : ℝ) : ℂ) + (b : ℂ) = ((lam * 1 + b : ℝ) : ℂ) by push_cast; ring]
      exact one_add_exp_neg_ofReal_ne_zero _
    · rw [show (lam' : ℂ) * ((1 : ℝ) : ℂ) + (b : ℂ) = ((lam' * 1 + b : ℝ) : ℂ) by push_cast; ring]
      exact one_add_exp_neg_ofReal_ne_zero _
  have hηU : η ∈ U := hUdef ▸ ⟨hη, hη'⟩
  have hd1 : ∀ᶠ z in nhdsWithin ((1 : ℝ) : ℂ) ({((1 : ℝ) : ℂ)}ᶜ), (FC - FC') z = 0 := by
    have heq1 := tokenCnet_eventuallyEq_nhds_of_eq_on_pos r hr V₁ A₁ V₂ A₂ A₁' A₂' u v i hagree
      (show (0 : ℝ) < 1 by norm_num)
    refine (Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_)
    filter_upwards [heq1] with z hz
    simp only [Pi.sub_apply, sub_eq_zero]; exact hz
  have hord1 : meromorphicOrderAt (FC - FC') ((1 : ℝ) : ℂ) = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr hd1
  have hordη : meromorphicOrderAt (FC - FC') η = ⊤ := by
    by_contra hne
    exact (hdmero.meromorphicOrderAt_ne_top_of_isPreconnected hUconn hηU h1U hne) hord1
  have hzero : ∀ᶠ z in nhdsWithin η ({η}ᶜ : Set ℂ), (FC - FC') z = 0 :=
    meromorphicOrderAt_eq_top_iff.mp hordη
  filter_upwards [hzero] with z hz
  simpa only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] using hz

end AnalyticA1

/-! ### First attention product (`identify_A1`)

The proof of Lemma `lem:app-causal-identify-a1` splits into a complex-analytic core and an
algebraic/topological endgame.  The endgame, recorded here, is fully formalised: once the
first-layer slopes `(u-v)ᵀA₁v` and `(u-v)ᵀA₁'v` are shown to agree on a (Euclidean) dense set
of pairs `(u,v)`, the matrices `A₁` and `A₁'` coincide.  The remaining gap (`slopes_agree_dense`)
is the analytic content: meromorphic continuation of the final-token function and
pole-accumulation for the sigmoid (paper Lemmas `lem:app-sigmoid-poles-near-pole`,
`lem:app-visible-accumulating-poles`, `lem:app-countable-continuation`). -/

/-- The first-layer slope-difference map `(u,v) ↦ (u-v)ᵀ Δ v` is continuous. -/
theorem continuous_slopeDiff {d : ℕ} (Δ : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (fun x : (Fin d → ℝ) × (Fin d → ℝ) => (x.1 - x.2) ⬝ᵥ Δ.mulVec x.2) :=
  (continuous_fst.sub continuous_snd).dotProduct
    (Continuous.matrix_mulVec continuous_const continuous_snd)

/-- **Endgame of `identify_A1`.** If the first-layer bilinear slopes agree on a dense set of
pairs `(u,v)`, then `A₁ = A₁'`. -/
theorem identify_A1_from_dense_slopes {d : ℕ}
    {A₁ A₁' : Matrix (Fin d) (Fin d) ℝ}
    {Ω : Set ((Fin d → ℝ) × (Fin d → ℝ))}
    (hΩdense : Dense Ω)
    (hΩ : ∀ x ∈ Ω, (x.1 - x.2) ⬝ᵥ (A₁ - A₁').mulVec x.2 = 0) :
    A₁ = A₁' := by
  set Δ : Matrix (Fin d) (Fin d) ℝ := A₁ - A₁' with hΔ
  have hzero_pairs : ∀ x : (Fin d → ℝ) × (Fin d → ℝ),
      (x.1 - x.2) ⬝ᵥ Δ.mulVec x.2 = 0 := by
    have hfun : (fun x : (Fin d → ℝ) × (Fin d → ℝ) =>
          (x.1 - x.2) ⬝ᵥ Δ.mulVec x.2) = fun _ => (0 : ℝ) :=
      Continuous.ext_on hΩdense (continuous_slopeDiff Δ) continuous_const
        (fun x hx => by rw [hΔ]; exact hΩ x hx)
    intro x; exact congrFun hfun x
  have hbilin : ∀ w v : Fin d → ℝ, w ⬝ᵥ Δ.mulVec v = 0 := by
    intro w v; simpa using hzero_pairs (w + v, v)
  have hΔ0 : Δ = 0 := matrix_eq_zero_of_dotProduct hbilin
  have hsub : A₁ - A₁' = 0 := by simpa [hΔ] using hΔ0
  exact sub_eq_zero.mp hsub

/-! #### Generic good-set for `identify_A1` (Step 6) -/

noncomputable def alpha (r : ℕ) : ℝ := (r : ℝ) / ((r : ℝ) + 1)

noncomputable def beta (r : ℕ) : ℝ := ((r : ℝ) + 1)⁻¹

theorem one_sub_alpha {r : ℕ} : (1 : ℝ) - alpha r = beta r := by
  rw [alpha, beta]; field_simp; ring

theorem alpha_ne_zero {r : ℕ} (hr : 0 < r) : alpha r ≠ 0 := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  exact (div_pos hrR (by positivity)).ne'

def firstSlope {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ) : ℝ :=
  (u - v) ⬝ᵥ A.mulVec v

theorem continuous_firstSlope {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (fun x : (Fin d → ℝ) × (Fin d → ℝ) => firstSlope A x.1 x.2) := by
  unfold firstSlope
  exact (continuous_fst.sub continuous_snd).dotProduct
    (Continuous.matrix_mulVec continuous_const continuous_snd)

theorem continuous_twoLayerG {d : ℕ} (V₁ V₂ : Matrix (Fin d) (Fin d) ℝ) (z : ℝ) :
    Continuous (fun x : (Fin d → ℝ) × (Fin d → ℝ) => twoLayerG V₁ V₂ x.1 x.2 z) := by
  unfold twoLayerG
  set w : (Fin d → ℝ) × (Fin d → ℝ) → Fin d → ℝ := fun x => x.1 - x.2
  have hw : Continuous w := continuous_fst.sub continuous_snd
  exact Continuous.matrix_mulVec continuous_const
    ((Continuous.matrix_mulVec continuous_const hw).sub
      (continuous_const.smul (Continuous.matrix_mulVec continuous_const hw)))

theorem continuous_twoLayerPhi {d : ℕ} (V₁ A₂ : Matrix (Fin d) (Fin d) ℝ) (z : ℝ) :
    Continuous (fun x : (Fin d → ℝ) × (Fin d → ℝ) => twoLayerPhi V₁ A₂ x.1 x.2 z) := by
  unfold twoLayerPhi
  set w : (Fin d → ℝ) × (Fin d → ℝ) → Fin d → ℝ := fun x => x.1 - x.2
  have hw : Continuous w := continuous_fst.sub continuous_snd
  set lhs : (Fin d → ℝ) × (Fin d → ℝ) → Fin d → ℝ :=
    fun x => (1 + V₁).mulVec (w x) - z • V₁.mulVec (w x)
  have hlhs : Continuous lhs :=
    (Continuous.matrix_mulVec continuous_const hw).sub
      (continuous_const.smul (Continuous.matrix_mulVec continuous_const hw))
  set rhs : (Fin d → ℝ) × (Fin d → ℝ) → Fin d → ℝ :=
    fun x => (1 + V₁).mulVec x.2 + z • V₁.mulVec (w x)
  have hrhs : Continuous rhs :=
    (Continuous.matrix_mulVec continuous_const continuous_snd).add
      (continuous_const.smul (Continuous.matrix_mulVec continuous_const hw))
  exact hlhs.dotProduct (Continuous.matrix_mulVec continuous_const hrhs)

def a1LambdaSet {d : ℕ} (A₁' : Matrix (Fin d) (Fin d) ℝ) :
    Set ((Fin d → ℝ) × (Fin d → ℝ)) := {x | firstSlope A₁' x.1 x.2 ≠ 0}

def a1PhiSet {d : ℕ} (r : ℕ) (V₁ A₂' : Matrix (Fin d) (Fin d) ℝ) :
    Set ((Fin d → ℝ) × (Fin d → ℝ)) :=
  {x | twoLayerPhi V₁ A₂' x.1 x.2 (alpha r) ≠ twoLayerPhi V₁ A₂' x.1 x.2 0}

def a1GSet {d : ℕ} (r : ℕ) (V₁ V₂ : Matrix (Fin d) (Fin d) ℝ) :
    Set ((Fin d → ℝ) × (Fin d → ℝ)) := {x | twoLayerG V₁ V₂ x.1 x.2 (alpha r) ≠ 0}

/-- The good set: `λ' ≠ 0`, `z ↦ φ(u,v,z)` nonconstant, and `z ↦ g(u,v,z)` not identically
zero (the second/third stated via the value at `α`). -/
def a1GoodSet {d : ℕ} (r : ℕ) (V₁ A₁' V₂ A₂' : Matrix (Fin d) (Fin d) ℝ) :
    Set ((Fin d → ℝ) × (Fin d → ℝ)) :=
  {x |
    firstSlope A₁' x.1 x.2 ≠ 0 ∧
    twoLayerPhi V₁ A₂' x.1 x.2 (alpha r) ≠ twoLayerPhi V₁ A₂' x.1 x.2 0 ∧
    twoLayerG V₁ V₂ x.1 x.2 (alpha r) ≠ 0}

theorem a1GoodSet_eq_inter {r d : ℕ} (V₁ A₁' V₂ A₂' : Matrix (Fin d) (Fin d) ℝ) :
    a1GoodSet r V₁ A₁' V₂ A₂'
      = a1LambdaSet A₁' ∩ a1PhiSet r V₁ A₂' ∩ a1GSet r V₁ V₂ := by
  ext x; simp only [a1GoodSet, a1LambdaSet, a1PhiSet, a1GSet, Set.mem_setOf_eq, Set.mem_inter_iff]
  tauto

theorem isOpen_a1LambdaSet {d : ℕ} (A₁' : Matrix (Fin d) (Fin d) ℝ) :
    IsOpen (a1LambdaSet A₁') :=
  isOpen_ne_fun (continuous_firstSlope A₁') continuous_const

theorem isOpen_a1PhiSet {r d : ℕ} (V₁ A₂' : Matrix (Fin d) (Fin d) ℝ) :
    IsOpen (a1PhiSet r V₁ A₂') :=
  isOpen_ne_fun (continuous_twoLayerPhi V₁ A₂' (alpha r)) (continuous_twoLayerPhi V₁ A₂' 0)

theorem isOpen_a1GSet {r d : ℕ} (V₁ V₂ : Matrix (Fin d) (Fin d) ℝ) :
    IsOpen (a1GSet r V₁ V₂) :=
  isOpen_ne_fun (continuous_twoLayerG V₁ V₂ (alpha r)) continuous_const

theorem dense_a1GoodSet_of_dense_components {r d : ℕ}
    (V₁ A₁' V₂ A₂' : Matrix (Fin d) (Fin d) ℝ)
    (hlam : Dense (a1LambdaSet A₁')) (hφ : Dense (a1PhiSet r V₁ A₂'))
    (hg : Dense (a1GSet r V₁ V₂)) :
    Dense (a1GoodSet r V₁ A₁' V₂ A₂') := by
  rw [a1GoodSet_eq_inter]
  exact (hlam.inter_of_isOpen_right hφ (isOpen_a1PhiSet V₁ A₂')).inter_of_isOpen_right
    hg (isOpen_a1GSet V₁ V₂)

theorem exists_firstSlope_ne_zero_of_matrix_ne_zero {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A ≠ 0) :
    ∃ u v : Fin d → ℝ, firstSlope A u v ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  apply hA
  apply matrix_eq_zero_of_dotProduct
  intro w v
  have h := hnone (w + v) v
  simpa [firstSlope] using h

theorem inside_alpha_single {r d : ℕ} [NeZero d] (V₁ : Matrix (Fin d) (Fin d) ℝ) :
    (1 + V₁).mulVec (Pi.single 0 1) - alpha r • V₁.mulVec (Pi.single 0 1)
      = (1 + beta r • V₁).mulVec (Pi.single 0 1) := by
  ext i
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply]
  rw [← one_sub_alpha (r := r)]; ring

theorem twoLayerG_alpha_single_zero {r d : ℕ} [NeZero d]
    (V₁ V₂ : Matrix (Fin d) (Fin d) ℝ) :
    twoLayerG V₁ V₂ (Pi.single 0 1) 0 (alpha r) 0
      = (V₂ * (1 + beta r • V₁) : Matrix (Fin d) (Fin d) ℝ) 0 0 := by
  rw [twoLayerG]; simp only [sub_zero]
  rw [inside_alpha_single, Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.col_apply]

theorem twoLayerPhi_alpha_single_zero {r d : ℕ} [NeZero d]
    (V₁ A₂ : Matrix (Fin d) (Fin d) ℝ) :
    twoLayerPhi V₁ A₂ (Pi.single 0 1) 0 (alpha r) - twoLayerPhi V₁ A₂ (Pi.single 0 1) 0 0
      = alpha r * (((1 + beta r • V₁)ᵀ * A₂ * V₁ : Matrix (Fin d) (Fin d) ℝ) 0 0) := by
  rw [twoLayerPhi, twoLayerPhi]
  simp only [sub_zero, zero_smul, add_zero, Matrix.mulVec_zero, dotProduct_zero]
  rw [inside_alpha_single]
  simp only [zero_add]
  rw [Matrix.mulVec_smul, dotProduct_smul, quadform_basis]
  simp [smul_eq_mul]

theorem exists_twoLayerG_alpha_ne_zero_of_hQ {r d : ℕ} [NeZero d]
    {V₁ V₂ : Matrix (Fin d) (Fin d) ℝ}
    (hQ : (V₂ * (1 + beta r • V₁) : Matrix (Fin d) (Fin d) ℝ) 0 0 ≠ 0) :
    ∃ u v : Fin d → ℝ, twoLayerG V₁ V₂ u v (alpha r) ≠ 0 := by
  refine ⟨Pi.single 0 1, 0, ?_⟩
  intro hzero
  have h0 := congrFun hzero 0
  rw [twoLayerG_alpha_single_zero] at h0
  exact hQ h0

theorem exists_twoLayerPhi_alpha_ne_zero_of_hM {r d : ℕ} [NeZero d]
    (hr : 0 < r) {V₁ A₂ : Matrix (Fin d) (Fin d) ℝ}
    (hM : ((1 + beta r • V₁)ᵀ * A₂ * V₁ : Matrix (Fin d) (Fin d) ℝ) 0 0 ≠ 0) :
    ∃ u v : Fin d → ℝ, twoLayerPhi V₁ A₂ u v (alpha r) ≠ twoLayerPhi V₁ A₂ u v 0 := by
  refine ⟨Pi.single 0 1, 0, ?_⟩
  intro h
  have hdiff : twoLayerPhi V₁ A₂ (Pi.single 0 1) 0 (alpha r)
        - twoLayerPhi V₁ A₂ (Pi.single 0 1) 0 0 = 0 := by rw [h, sub_self]
  rw [twoLayerPhi_alpha_single_zero] at hdiff
  exact hM ((mul_eq_zero.mp hdiff).resolve_left (alpha_ne_zero hr))

theorem a1GoodSet_mem_iff {r d : ℕ} {V₁ A₁' V₂ A₂' : Matrix (Fin d) (Fin d) ℝ}
    {x : (Fin d → ℝ) × (Fin d → ℝ)} :
    x ∈ a1GoodSet r V₁ A₁' V₂ A₂' ↔
      firstSlope A₁' x.1 x.2 ≠ 0 ∧
      twoLayerPhi V₁ A₂' x.1 x.2 (alpha r) ≠ twoLayerPhi V₁ A₂' x.1 x.2 0 ∧
      twoLayerG V₁ V₂ x.1 x.2 (alpha r) ≠ 0 := Iff.rfl

theorem exists_coord_ne_zero_of_ne_zero {d : ℕ} {x : Fin d → ℝ} (hx : x ≠ 0) :
    ∃ i : Fin d, x i ≠ 0 := by
  by_contra h
  apply hx
  funext i
  exact not_not.mp (not_exists.mp h i)

theorem twoLayerPhi_coeff_nonzero_of_ne {r d : ℕ}
    {V₁ A₂ : Matrix (Fin d) (Fin d) ℝ} {u v : Fin d → ℝ}
    (hφ : twoLayerPhi V₁ A₂ u v (alpha r) ≠ twoLayerPhi V₁ A₂ u v 0) :
    (((1 + V₁).mulVec (u - v)) ⬝ᵥ A₂.mulVec (V₁.mulVec (u - v))
        - (V₁.mulVec (u - v)) ⬝ᵥ A₂.mulVec ((1 + V₁).mulVec v)) ≠ 0 ∨
      (-((V₁.mulVec (u - v)) ⬝ᵥ A₂.mulVec (V₁.mulVec (u - v)))) ≠ 0 := by
  by_contra h
  rcases not_or.mp h with ⟨h₁, h₂⟩
  apply hφ
  rw [twoLayerPhi_eq_quadratic, twoLayerPhi_eq_quadratic, not_not.mp h₁, not_not.mp h₂]
  ring

theorem twoLayerG_exists_affine_coord_nonzero_of_ne {r d : ℕ}
    {V₁ V₂ : Matrix (Fin d) (Fin d) ℝ} {u v : Fin d → ℝ}
    (hg : twoLayerG V₁ V₂ u v (alpha r) ≠ 0) :
    ∃ i : Fin d,
      (V₂.mulVec ((1 + V₁).mulVec (u - v))) i ≠ 0 ∨
        (-(V₂.mulVec (V₁.mulVec (u - v))) i) ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_coord_ne_zero_of_ne_zero hg
  refine ⟨i, ?_⟩
  by_contra h
  rcases not_or.mp h with ⟨h₀, h₁⟩
  apply hi
  rw [twoLayerG_eq_affine, not_not.mp h₀, not_not.mp h₁]
  ring

/-! #### Polynomial genericity (density of the A1 good set) -/

abbrev UVIdx (d : ℕ) := Fin d ⊕ Fin d
abbrev UVPoly (d : ℕ) := MvPolynomial (UVIdx d) ℝ

def uvPoint {d : ℕ} (x : (Fin d → ℝ) × (Fin d → ℝ)) : UVIdx d → ℝ := Sum.elim x.1 x.2
noncomputable def uvU (d : ℕ) : Fin d → UVPoly d := fun i => MvPolynomial.X (Sum.inl i)
noncomputable def uvV (d : ℕ) : Fin d → UVPoly d := fun i => MvPolynomial.X (Sum.inr i)

theorem eval_uvU {d : ℕ} (x : (Fin d → ℝ) × (Fin d → ℝ)) :
    (fun i => MvPolynomial.eval (uvPoint x) (uvU d i)) = x.1 := by funext i; simp [uvPoint, uvU]
theorem eval_uvV {d : ℕ} (x : (Fin d → ℝ) × (Fin d → ℝ)) :
    (fun i => MvPolynomial.eval (uvPoint x) (uvV d i)) = x.2 := by funext i; simp [uvPoint, uvV]
theorem eval_uvSub {d : ℕ} (x : (Fin d → ℝ) × (Fin d → ℝ)) :
    (fun i => MvPolynomial.eval (uvPoint x) ((uvU d - uvV d) i)) = x.1 - x.2 := by
  funext i; simp [uvPoint, uvU, uvV]

noncomputable def firstSlopePoly {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : UVPoly d :=
  (uvU d - uvV d) ⬝ᵥ ((A.map (MvPolynomial.C : ℝ →+* UVPoly d)) *ᵥ uvV d)

theorem eval_firstSlopePoly {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (x : (Fin d → ℝ) × (Fin d → ℝ)) :
    MvPolynomial.eval (uvPoint x) (firstSlopePoly A) = firstSlope A x.1 x.2 := by
  rw [firstSlopePoly, firstSlope, eval_dotProduct', eval_uvSub x]
  congr 1; funext i; rw [eval_mapMat_mulVec', eval_uvV x]

noncomputable def twoLayerGPolyVec {d : ℕ} (V₁ V₂ : Matrix (Fin d) (Fin d) ℝ)
    (z : ℝ) : Fin d → UVPoly d :=
  (V₂.map (MvPolynomial.C : ℝ →+* UVPoly d)) *ᵥ
    (((1 + V₁).map (MvPolynomial.C : ℝ →+* UVPoly d)) *ᵥ (uvU d - uvV d)
      - (MvPolynomial.C z : UVPoly d) • ((V₁.map (MvPolynomial.C : ℝ →+* UVPoly d)) *ᵥ
        (uvU d - uvV d)))

theorem eval_twoLayerGPolyVec {d : ℕ} (V₁ V₂ : Matrix (Fin d) (Fin d) ℝ)
    (z : ℝ) (x : (Fin d → ℝ) × (Fin d → ℝ)) :
    (fun i => MvPolynomial.eval (uvPoint x) (twoLayerGPolyVec V₁ V₂ z i))
      = twoLayerG V₁ V₂ x.1 x.2 z := by
  funext i
  rw [twoLayerGPolyVec, twoLayerG, eval_mapMat_mulVec']
  congr 1; funext j
  simp only [Pi.sub_apply, Pi.smul_apply, map_sub, smul_eq_mul, map_mul, MvPolynomial.eval_C]
  rw [eval_mapMat_mulVec', eval_mapMat_mulVec', eval_uvSub x]

noncomputable def twoLayerGCoordPoly {d : ℕ} (r : ℕ)
    (V₁ V₂ : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) : UVPoly d :=
  twoLayerGPolyVec V₁ V₂ (alpha r) i

theorem eval_twoLayerGCoordPoly {r d : ℕ} (V₁ V₂ : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (x : (Fin d → ℝ) × (Fin d → ℝ)) :
    MvPolynomial.eval (uvPoint x) (twoLayerGCoordPoly r V₁ V₂ i)
      = twoLayerG V₁ V₂ x.1 x.2 (alpha r) i := by
  rw [twoLayerGCoordPoly]; exact congrFun (eval_twoLayerGPolyVec V₁ V₂ (alpha r) x) i

noncomputable def twoLayerPhiPoly {d : ℕ} (V₁ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (z : ℝ) : UVPoly d :=
  (((1 + V₁).map (MvPolynomial.C : ℝ →+* UVPoly d)) *ᵥ (uvU d - uvV d)
      - (MvPolynomial.C z : UVPoly d) • ((V₁.map (MvPolynomial.C : ℝ →+* UVPoly d)) *ᵥ
        (uvU d - uvV d)))
    ⬝ᵥ
    ((A₂.map (MvPolynomial.C : ℝ →+* UVPoly d)) *ᵥ
      (((1 + V₁).map (MvPolynomial.C : ℝ →+* UVPoly d)) *ᵥ uvV d
        + (MvPolynomial.C z : UVPoly d) • ((V₁.map (MvPolynomial.C : ℝ →+* UVPoly d)) *ᵥ
          (uvU d - uvV d))))

theorem eval_twoLayerPhiPoly {d : ℕ} (V₁ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (z : ℝ) (x : (Fin d → ℝ) × (Fin d → ℝ)) :
    MvPolynomial.eval (uvPoint x) (twoLayerPhiPoly V₁ A₂ z)
      = twoLayerPhi V₁ A₂ x.1 x.2 z := by
  rw [twoLayerPhiPoly, twoLayerPhi, eval_dotProduct']
  have hlhs :
      (fun i => MvPolynomial.eval (uvPoint x)
        ((((1 + V₁).map (MvPolynomial.C : ℝ →+* UVPoly d)) *ᵥ (uvU d - uvV d)
            - (MvPolynomial.C z : UVPoly d) • ((V₁.map (MvPolynomial.C : ℝ →+* UVPoly d)) *ᵥ
              (uvU d - uvV d))) i))
        = (1 + V₁).mulVec (x.1 - x.2) - z • V₁.mulVec (x.1 - x.2) := by
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, map_sub, smul_eq_mul, map_mul, MvPolynomial.eval_C]
    rw [eval_mapMat_mulVec', eval_mapMat_mulVec', eval_uvSub x]
  have hinner :
      (fun i => MvPolynomial.eval (uvPoint x)
        ((((1 + V₁).map (MvPolynomial.C : ℝ →+* UVPoly d)) *ᵥ uvV d
          + (MvPolynomial.C z : UVPoly d) • ((V₁.map (MvPolynomial.C : ℝ →+* UVPoly d)) *ᵥ
            (uvU d - uvV d))) i))
        = (1 + V₁).mulVec x.2 + z • V₁.mulVec (x.1 - x.2) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, map_add, smul_eq_mul, map_mul, MvPolynomial.eval_C]
    rw [eval_mapMat_mulVec', eval_mapMat_mulVec', eval_uvV x, eval_uvSub x]
  have hrhs :
      (fun i => MvPolynomial.eval (uvPoint x)
        (((A₂.map (MvPolynomial.C : ℝ →+* UVPoly d)) *ᵥ
          (((1 + V₁).map (MvPolynomial.C : ℝ →+* UVPoly d)) *ᵥ uvV d
            + (MvPolynomial.C z : UVPoly d) • ((V₁.map (MvPolynomial.C : ℝ →+* UVPoly d)) *ᵥ
              (uvU d - uvV d)))) i))
        = A₂.mulVec ((1 + V₁).mulVec x.2 + z • V₁.mulVec (x.1 - x.2)) := by
    funext i; rw [eval_mapMat_mulVec', hinner]
  rw [hlhs, hrhs]

noncomputable def twoLayerPhiDiffPoly {d : ℕ} (r : ℕ)
    (V₁ A₂ : Matrix (Fin d) (Fin d) ℝ) : UVPoly d :=
  twoLayerPhiPoly V₁ A₂ (alpha r) - twoLayerPhiPoly V₁ A₂ 0

theorem eval_twoLayerPhiDiffPoly {r d : ℕ} (V₁ A₂ : Matrix (Fin d) (Fin d) ℝ)
    (x : (Fin d → ℝ) × (Fin d → ℝ)) :
    MvPolynomial.eval (uvPoint x) (twoLayerPhiDiffPoly r V₁ A₂)
      = twoLayerPhi V₁ A₂ x.1 x.2 (alpha r) - twoLayerPhi V₁ A₂ x.1 x.2 0 := by
  rw [twoLayerPhiDiffPoly, map_sub, eval_twoLayerPhiPoly, eval_twoLayerPhiPoly]

theorem dense_uv_nonzero {d : ℕ} (p : UVPoly d) (hp : p ≠ 0) :
    Dense {x : (Fin d → ℝ) × (Fin d → ℝ) | MvPolynomial.eval (uvPoint x) p ≠ 0} := by
  classical
  let e : ((Fin d → ℝ) × (Fin d → ℝ)) ≃ₜ (UVIdx d → ℝ) :=
    (Homeomorph.sumPiEquivProdPi (Fin d) (Fin d) (fun _ : UVIdx d => ℝ)).symm
  have hd : Dense {y : UVIdx d → ℝ | MvPolynomial.eval y p ≠ 0} := dense_compl_zero_set p hp
  have hpre :
      {x : (Fin d → ℝ) × (Fin d → ℝ) | MvPolynomial.eval (uvPoint x) p ≠ 0}
        = e ⁻¹' {y : UVIdx d → ℝ | MvPolynomial.eval y p ≠ 0} := by ext x; rfl
  rw [hpre]; exact hd.preimage e.isOpenMap

theorem firstSlopePoly_ne_zero_of_matrix_ne_zero {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A ≠ 0) : firstSlopePoly A ≠ 0 := by
  obtain ⟨u, v, huv⟩ := exists_firstSlope_ne_zero_of_matrix_ne_zero hA
  intro hp; apply huv
  have hz : MvPolynomial.eval (uvPoint (u, v)) (firstSlopePoly A) = 0 := by rw [hp]; simp
  rwa [eval_firstSlopePoly] at hz

theorem dense_a1LambdaSet_of_matrix_ne_zero {d : ℕ}
    {A₁' : Matrix (Fin d) (Fin d) ℝ} (hA1' : A₁' ≠ 0) : Dense (a1LambdaSet A₁') := by
  have hd := dense_uv_nonzero (firstSlopePoly A₁')
    (firstSlopePoly_ne_zero_of_matrix_ne_zero hA1')
  simpa [a1LambdaSet, eval_firstSlopePoly] using hd

theorem twoLayerPhiDiffPoly_ne_zero_of_hM {r d : ℕ} [NeZero d] (hr : 0 < r)
    {V₁ A₂ : Matrix (Fin d) (Fin d) ℝ}
    (hM : ((1 + beta r • V₁)ᵀ * A₂ * V₁ : Matrix (Fin d) (Fin d) ℝ) 0 0 ≠ 0) :
    twoLayerPhiDiffPoly r V₁ A₂ ≠ 0 := by
  obtain ⟨u, v, huv⟩ := exists_twoLayerPhi_alpha_ne_zero_of_hM hr hM
  intro hp; apply huv
  have hz : MvPolynomial.eval (uvPoint (u, v)) (twoLayerPhiDiffPoly r V₁ A₂) = 0 := by rw [hp]; simp
  rw [eval_twoLayerPhiDiffPoly] at hz
  exact sub_eq_zero.mp hz

theorem dense_a1PhiSet_of_hM {r d : ℕ} [NeZero d] (hr : 0 < r)
    {V₁ A₂' : Matrix (Fin d) (Fin d) ℝ}
    (hM : ((1 + beta r • V₁)ᵀ * A₂' * V₁ : Matrix (Fin d) (Fin d) ℝ) 0 0 ≠ 0) :
    Dense (a1PhiSet r V₁ A₂') := by
  have hd := dense_uv_nonzero (twoLayerPhiDiffPoly r V₁ A₂')
    (twoLayerPhiDiffPoly_ne_zero_of_hM hr hM)
  simpa [a1PhiSet, eval_twoLayerPhiDiffPoly, sub_eq_zero] using hd

theorem twoLayerGCoordPoly_zero_ne_zero_of_hQ {r d : ℕ} [NeZero d]
    {V₁ V₂ : Matrix (Fin d) (Fin d) ℝ}
    (hQ : (V₂ * (1 + beta r • V₁) : Matrix (Fin d) (Fin d) ℝ) 0 0 ≠ 0) :
    twoLayerGCoordPoly r V₁ V₂ 0 ≠ 0 := by
  intro hp; apply hQ
  have hz : MvPolynomial.eval (uvPoint (Pi.single 0 1, 0))
      (twoLayerGCoordPoly r V₁ V₂ 0) = 0 := by rw [hp]; simp
  rw [eval_twoLayerGCoordPoly, twoLayerG_alpha_single_zero] at hz
  exact hz

theorem dense_a1GSet_of_hQ {r d : ℕ} [NeZero d]
    {V₁ V₂ : Matrix (Fin d) (Fin d) ℝ}
    (hQ : (V₂ * (1 + beta r • V₁) : Matrix (Fin d) (Fin d) ℝ) 0 0 ≠ 0) :
    Dense (a1GSet r V₁ V₂) := by
  have hdcoord := dense_uv_nonzero (twoLayerGCoordPoly r V₁ V₂ 0)
    (twoLayerGCoordPoly_zero_ne_zero_of_hQ hQ)
  refine Dense.mono ?_ hdcoord
  intro x hx; rw [a1GSet]; intro hzero; apply hx
  rw [eval_twoLayerGCoordPoly, hzero]; rfl

theorem dense_a1GoodSet_of_generic_conditions {r d : ℕ} [NeZero d] (hr : 0 < r)
    {V₁ A₁' V₂ A₂' : Matrix (Fin d) (Fin d) ℝ}
    (hA1' : A₁' ≠ 0)
    (hQ : (V₂ * (1 + beta r • V₁) : Matrix (Fin d) (Fin d) ℝ) 0 0 ≠ 0)
    (hM : ((1 + beta r • V₁)ᵀ * A₂' * V₁ : Matrix (Fin d) (Fin d) ℝ) 0 0 ≠ 0) :
    Dense (a1GoodSet r V₁ A₁' V₂ A₂') :=
  dense_a1GoodSet_of_dense_components V₁ A₁' V₂ A₂'
    (dense_a1LambdaSet_of_matrix_ne_zero hA1')
    (dense_a1PhiSet_of_hM hr hM) (dense_a1GSet_of_hQ hQ)

/-! #### Reduction of `identify_A1` to a dense pole-inclusion -/

/-- For a fixed `(u,v)`, pole inclusion for the two first-layer sigmoids gives the
slope-difference equation used by the dense endgame. -/
theorem slopeDiff_eq_zero_of_sigmoidPole_subset {r d : ℕ}
    {A₁ A₁' : Matrix (Fin d) (Fin d) ℝ} {u v : Fin d → ℝ}
    (hb : Real.log (r : ℝ) ≠ 0)
    (hlam : (u - v) ⬝ᵥ A₁.mulVec v ≠ 0) (hlam' : (u - v) ⬝ᵥ A₁'.mulVec v ≠ 0)
    (hsub : ∀ n : ℤ, ∃ m : ℤ,
      sigmoidPole (Real.log (r : ℝ)) ((u - v) ⬝ᵥ A₁'.mulVec v) n
        = sigmoidPole (Real.log (r : ℝ)) ((u - v) ⬝ᵥ A₁.mulVec v) m) :
    (u - v) ⬝ᵥ (A₁ - A₁').mulVec v = 0 := by
  have hslope : (u - v) ⬝ᵥ A₁.mulVec v = (u - v) ⬝ᵥ A₁'.mulVec v :=
    slope_eq_of_sigmoidPole_subset hb hlam hlam' hsub
  rw [Matrix.sub_mulVec, dotProduct_sub]; linarith

/-- If on a dense set every primed first-layer sigmoid pole is also an unprimed one (and both
slopes are nonzero), then `A₁ = A₁'`. -/
theorem identify_A1_from_dense_sigmoidPole_subsets {r d : ℕ}
    {A₁ A₁' : Matrix (Fin d) (Fin d) ℝ}
    {Ω : Set ((Fin d → ℝ) × (Fin d → ℝ))}
    (hb : Real.log (r : ℝ) ≠ 0) (hΩdense : Dense Ω)
    (hΩ : ∀ x ∈ Ω,
      (x.1 - x.2) ⬝ᵥ A₁.mulVec x.2 ≠ 0 ∧
      (x.1 - x.2) ⬝ᵥ A₁'.mulVec x.2 ≠ 0 ∧
      ∀ n : ℤ, ∃ m : ℤ,
        sigmoidPole (Real.log (r : ℝ)) ((x.1 - x.2) ⬝ᵥ A₁'.mulVec x.2) n
          = sigmoidPole (Real.log (r : ℝ)) ((x.1 - x.2) ⬝ᵥ A₁.mulVec x.2) m) :
    A₁ = A₁' := by
  apply identify_A1_from_dense_slopes hΩdense
  intro x hx
  exact slopeDiff_eq_zero_of_sigmoidPole_subset
    (r := r) (A₁ := A₁) (A₁' := A₁') (u := x.1) (v := x.2)
    hb (hΩ x hx).1 (hΩ x hx).2.1 (hΩ x hx).2.2

/-! #### The remaining analytic core for `identify_A1` -/

/-- **The single remaining analytic gap of `identify_A1`** (Lemma `lem:app-causal-identify-a1`,
the pole/continuation argument).  For a generic `(u,v)` on which the network functions agree on
`(0,∞)`, the unprimed first-layer slope is nonzero and every primed first-layer sigmoid pole is
an unprimed one.  Verified inputs available: `tokenCnet_eq_on_pos` (`FC = FC'` on `(0,∞)`),
`tokenC_meromorphicAt`, `inner_denom_sigmoidPole`, `sigmoid_poles_accumulate`. -/
theorem a1_pole_subset {r d : ℕ} [NeZero d] (hr : 2 ≤ r)
    {V₁ A₁ V₂ A₂ A₁' A₂' : Matrix (Fin d) (Fin d) ℝ} {u v : Fin d → ℝ}
    (hagree : ∀ c : ℝ, network ((V₁, A₁), (V₂, A₂)) (twoType r d u v c)
        = network ((V₁, A₁'), (V₂, A₂')) (twoType r d u v c))
    (hx : (u, v) ∈ a1GoodSet r V₁ A₁' V₂ A₂') :
    (u - v) ⬝ᵥ A₁.mulVec v ≠ 0 ∧
    ∀ n : ℤ, ∃ m : ℤ,
      sigmoidPole (Real.log (r : ℝ)) ((u - v) ⬝ᵥ A₁'.mulVec v) n
        = sigmoidPole (Real.log (r : ℝ)) ((u - v) ⬝ᵥ A₁.mulVec v) m := by
  have hr0 : 0 < r := by omega
  have hlog : Real.log (r : ℝ) ≠ 0 := by
    have h1 : (1 : ℝ) < (r : ℝ) := by exact_mod_cast (show 1 < r by omega)
    exact (Real.log_pos h1).ne'
  obtain ⟨hlam'p, hφp, hgp⟩ := a1GoodSet_mem_iff.mp hx
  obtain ⟨i, hGcoord⟩ :=
    twoLayerG_exists_affine_coord_nonzero_of_ne
      (r := r) (V₁ := V₁) (V₂ := V₂) (u := u) (v := v) hgp
  set lam : ℝ := (u - v) ⬝ᵥ A₁.mulVec v with hlamdef
  set lamp : ℝ := (u - v) ⬝ᵥ A₁'.mulVec v with hlampdef
  set b0 : ℝ := Real.log (r : ℝ) with hb0def
  set A0c : ℝ := ((1 + V₂).mulVec ((1 + V₁).mulVec v)) i with hA0cdef
  set A1c : ℝ := ((1 + V₂).mulVec (V₁.mulVec (u - v))) i with hA1cdef
  set G0c : ℝ := (V₂.mulVec ((1 + V₁).mulVec (u - v))) i with hG0cdef
  set G1c : ℝ := (-((V₂.mulVec (V₁.mulVec (u - v))) i)) with hG1cdef
  set Ψ0 : ℝ := ((1 + V₁).mulVec (u - v)) ⬝ᵥ A₂.mulVec ((1 + V₁).mulVec v)
    with hΨ0def
  set Ψ1 : ℝ :=
    ((1 + V₁).mulVec (u - v)) ⬝ᵥ A₂.mulVec (V₁.mulVec (u - v))
      - (V₁.mulVec (u - v)) ⬝ᵥ A₂.mulVec ((1 + V₁).mulVec v) with hΨ1def
  set Ψ2 : ℝ := (-((V₁.mulVec (u - v)) ⬝ᵥ A₂.mulVec (V₁.mulVec (u - v))))
    with hΨ2def
  set Ψ0p : ℝ := ((1 + V₁).mulVec (u - v)) ⬝ᵥ A₂'.mulVec ((1 + V₁).mulVec v)
    with hΨ0pdef
  set Ψ1p : ℝ :=
    ((1 + V₁).mulVec (u - v)) ⬝ᵥ A₂'.mulVec (V₁.mulVec (u - v))
      - (V₁.mulVec (u - v)) ⬝ᵥ A₂'.mulVec ((1 + V₁).mulVec v) with hΨ1pdef
  set Ψ2p : ℝ := (-((V₁.mulVec (u - v)) ⬝ᵥ A₂'.mulVec (V₁.mulVec (u - v))))
    with hΨ2pdef
  have hlamp : lamp ≠ 0 := by
    simpa [lamp, hlampdef, firstSlope] using hlam'p
  have hb0 : b0 ≠ 0 := by
    simpa [b0, hb0def] using hlog
  have hψp : Ψ1p ≠ 0 ∨ Ψ2p ≠ 0 := by
    simpa [Ψ1p, Ψ2p, hΨ1pdef, hΨ2pdef] using
      twoLayerPhi_coeff_nonzero_of_ne
        (r := r) (V₁ := V₁) (A₂ := A₂') (u := u) (v := v) hφp
  have hG : G0c ≠ 0 ∨ G1c ≠ 0 := by
    simpa [G0c, G1c, hG0cdef, hG1cdef] using hGcoord
  have hcont : ∀ {η : ℂ},
      1 + Complex.exp (-((lam : ℂ) * η + (b0 : ℂ))) ≠ 0 →
      1 + Complex.exp (-((lamp : ℂ) * η + (b0 : ℂ))) ≠ 0 →
      tokenC lam b0 A0c A1c G0c G1c Ψ0 Ψ1 Ψ2
        =ᶠ[nhdsWithin η ({η}ᶜ : Set ℂ)]
          tokenC lamp b0 A0c A1c G0c G1c Ψ0p Ψ1p Ψ2p := by
    intro η hη hηp
    have h :=
      tokenCnet_eventuallyEq_nhdsNE_of_not_innerPole (r := r) hr0
        V₁ A₁ V₂ A₂ A₁' A₂' u v i hagree
        (η := η)
        (by simpa [lam, b0, hlamdef, hb0def] using hη)
        (by simpa [lamp, b0, hlampdef, hb0def] using hηp)
    filter_upwards [h] with z hz
    simpa [tokenCnet, lam, lamp, b0, A0c, A1c, G0c, G1c,
      Ψ0, Ψ1, Ψ2, Ψ0p, Ψ1p, Ψ2p, hlamdef, hlampdef, hb0def,
      hA0cdef, hA1cdef, hG0cdef, hG1cdef,
      hΨ0def, hΨ1def, hΨ2def, hΨ0pdef, hΨ1pdef, hΨ2pdef] using hz
  have hpole_un : ∀ n : ℤ,
      1 + Complex.exp (-((lam : ℂ) * sigmoidPole b0 lamp n + (b0 : ℂ))) = 0 := by
    intro n
    exact scalar_primed_innerPole_forces_unprimed_innerPole
      lam lamp b0 A0c A1c G0c G1c Ψ0 Ψ1 Ψ2 Ψ0p Ψ1p Ψ2p
      hlamp (sigmoidPole_ne_zero_of_b_ne_zero hb0 hlamp n) hψp hG hcont
  have hlam : lam ≠ 0 := lam_ne_zero_of_inner_pole (hpole_un 0)
  refine ⟨by simpa [lam, hlamdef] using hlam, ?_⟩
  intro n
  obtain ⟨m, hm⟩ := exists_sigmoidPole_eq_of_inner_pole hlam (hpole_un n)
  exact ⟨m, by simpa [lam, lamp, b0, hlamdef, hlampdef, hb0def] using hm⟩

/-- **Identification of the first attention product** (Lemma `lem:app-causal-identify-a1`):
once the value products agree, the first-layer attention product is determined.  Reduced to the
analytic pole-inclusion `a1_pole_subset` via the verified genericity-density and the dense
pole-inclusion endgame. -/
theorem identify_A1 {r d : ℕ} [NeZero d] (hr : 2 ≤ r)
    {V₁ A₁ V₂ A₂ V₁' A₁' V₂' A₂' : Matrix (Fin d) (Fin d) ℝ}
    (hA1' : A₁' ≠ 0)
    (hQ : (V₂' * (1 + (((r : ℝ) + 1)⁻¹) • V₁') : Matrix (Fin d) (Fin d) ℝ) 0 0 ≠ 0)
    (hM : ((1 + (((r : ℝ) + 1)⁻¹) • V₁')ᵀ * A₂' * V₁' : Matrix (Fin d) (Fin d) ℝ) 0 0 ≠ 0)
    (hV1 : V₁ = V₁') (hV2 : V₂ = V₂')
    (hagree : ∀ (u v : Fin d → ℝ) (c : ℝ),
      network ((V₁, A₁), (V₂, A₂)) (twoType r d u v c)
        = network ((V₁', A₁'), (V₂', A₂')) (twoType r d u v c)) :
    A₁ = A₁' := by
  have hr0 : 0 < r := by omega
  have hb : Real.log (r : ℝ) ≠ 0 := by
    have h1 : (1 : ℝ) < (r : ℝ) := by exact_mod_cast (show 1 < r by omega)
    exact (Real.log_pos h1).ne'
  have hQ' : (V₂ * (1 + beta r • V₁) : Matrix (Fin d) (Fin d) ℝ) 0 0 ≠ 0 := by
    rw [beta, hV1, hV2]; exact hQ
  have hM' : ((1 + beta r • V₁)ᵀ * A₂' * V₁ : Matrix (Fin d) (Fin d) ℝ) 0 0 ≠ 0 := by
    rw [beta, hV1]; exact hM
  apply identify_A1_from_dense_sigmoidPole_subsets (r := r) hb
    (dense_a1GoodSet_of_generic_conditions hr0 hA1' hQ' hM')
  intro x hx
  have hagree' : ∀ c : ℝ, network ((V₁, A₁), (V₂, A₂)) (twoType r d x.1 x.2 c)
      = network ((V₁, A₁'), (V₂, A₂')) (twoType r d x.1 x.2 c) := by
    intro c; rw [hagree x.1 x.2 c, hV1, hV2]
  obtain ⟨hlam, hsub⟩ := a1_pole_subset (u := x.1) (v := x.2) hr hagree' hx
  exact ⟨hlam, (a1GoodSet_mem_iff.mp hx).1, hsub⟩

/-- **Identification of the second attention product** (Lemma `lem:app-causal-identify-a2`):
with all earlier products fixed, `A₂` is determined. -/
theorem identify_A2 {r d : ℕ} [NeZero d] (hr : 2 ≤ r) (hd : 3 ≤ d)
    {V₁ A₁ V₂ A₂ V₁' A₁' V₂' A₂' : Matrix (Fin d) (Fin d) ℝ}
    (hA1' : A₁' ≠ 0)
    (hQ : (V₂' * (1 + (((r : ℝ) + 1)⁻¹) • V₁') : Matrix (Fin d) (Fin d) ℝ) 0 0 ≠ 0)
    (hdet : ((1 + V₁').submatrix (Fin.castLE (Nat.sub_le d 1))
        (Fin.castLE (Nat.sub_le d 1))).det ≠ 0)
    (hV1 : V₁ = V₁') (hV2 : V₂ = V₂') (hA1 : A₁ = A₁')
    (hagree : ∀ (u v : Fin d → ℝ) (c : ℝ),
      network ((V₁, A₁), (V₂, A₂)) (twoType r d u v c)
        = network ((V₁', A₁'), (V₂', A₂')) (twoType r d u v c)) :
    A₂ = A₂' := by
  set B : Matrix (Fin d) (Fin d) ℝ := 1 + V₁' with hB
  set Δ : Matrix (Fin d) (Fin d) ℝ := A₂ - A₂' with hΔ
  have hr0 : 0 < r := by omega
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  set β : ℝ := ((r : ℝ) + 1)⁻¹ with hβ
  -- The analytic input (paper Lemma `lem:app-causal-identify-a2`): the second-layer sigmoid
  -- argument matching, pushed through sigmoid injectivity on the reals and Zariski density,
  -- is the vanishing of the `z`-polynomial below.
  have hpoly : ∀ (w v : Fin d → ℝ) (z : ℝ),
      ((B - z • V₁').mulVec w) ⬝ᵥ Δ.mulVec (B.mulVec v + z • V₁'.mulVec w) = 0 := by
    have hsigcont : Continuous sig := by
      unfold sig
      exact (continuous_const.add (Real.continuous_exp.comp continuous_neg)).inv₀
        (fun x => one_add_exp_ne_zero x)
    -- ## Per-input scalar extraction: agreement on one two-type input gives, when the
    -- layer-2 weight vector is nonzero, equality of the second-layer quadratic forms.
    have hextract : ∀ (u v : Fin d → ℝ) (t : ℝ), 0 < t →
        V₂'.mulVec ((B - sig (t * ((u - v) ⬝ᵥ A₁'.mulVec v) + Real.log r) • V₁').mulVec (u - v)) ≠ 0 →
        ((B - sig (t * ((u - v) ⬝ᵥ A₁'.mulVec v) + Real.log r) • V₁').mulVec (u - v))
            ⬝ᵥ Δ.mulVec (B.mulVec v
                + sig (t * ((u - v) ⬝ᵥ A₁'.mulVec v) + Real.log r) • V₁'.mulVec (u - v)) = 0 := by
      intro u v t ht hvec
      set z : ℝ := sig (t * ((u - v) ⬝ᵥ A₁'.mulVec v) + Real.log r) with hz
      set c : ℝ := Real.sqrt t with hc
      have hcne : c ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
      have hc2 : c ^ 2 = t := Real.sq_sqrt ht.le
      have hlayer1 : attnLayer V₁' A₁' (twoType r d u v c)
          = twoType r d (u + V₁'.mulVec u)
              (v + V₁'.mulVec v + z • V₁'.mulVec (u - v)) c := by
        rw [attnLayer_twoType hr0, hc2, ← hz]
      have hag := hagree u v c
      simp only [network] at hag
      rw [hV1, hV2, hA1, hlayer1] at hag
      have hcore := attnLayer_A2_core hr0 V₂' A₂ A₂'
        (u + V₁'.mulVec u) (v + V₁'.mulVec v + z • V₁'.mulVec (u - v)) c hcne hag
      have hmv_sub : V₁'.mulVec (u - v) = V₁'.mulVec u - V₁'.mulVec v := Matrix.mulVec_sub _ _ _
      have e_pq : (u + V₁'.mulVec u) - (v + V₁'.mulVec v + z • V₁'.mulVec (u - v))
          = (B - z • V₁').mulVec (u - v) := by
        rw [hB, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
          hmv_sub]
        module
      have e_q : v + V₁'.mulVec v + z • V₁'.mulVec (u - v)
          = B.mulVec v + z • V₁'.mulVec (u - v) := by
        rw [hB, Matrix.add_mulVec, Matrix.one_mulVec]
      rw [e_pq, e_q, hc2] at hcore
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hvec
      rw [Pi.zero_apply] at hi
      have hci := congrFun hcore i
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at hci
      have hsigeq := mul_right_cancel₀ hi hci
      have hargeq := sig_injective hsigeq
      have hdoteq : ((B - z • V₁').mulVec (u - v))
            ⬝ᵥ A₂.mulVec (B.mulVec v + z • V₁'.mulVec (u - v))
          = ((B - z • V₁').mulVec (u - v))
            ⬝ᵥ A₂'.mulVec (B.mulVec v + z • V₁'.mulVec (u - v)) := by
        have hμ : t * (((B - z • V₁').mulVec (u - v))
              ⬝ᵥ A₂.mulVec (B.mulVec v + z • V₁'.mulVec (u - v)))
            = t * (((B - z • V₁').mulVec (u - v))
              ⬝ᵥ A₂'.mulVec (B.mulVec v + z • V₁'.mulVec (u - v))) := by linarith [hargeq]
        exact mul_left_cancel₀ ht.ne' hμ
      rw [hΔ, show (A₂ - A₂').mulVec (B.mulVec v + z • V₁'.mulVec (u - v))
          = A₂.mulVec (B.mulVec v + z • V₁'.mulVec (u - v))
            - A₂'.mulVec (B.mulVec v + z • V₁'.mulVec (u - v)) from Matrix.sub_mulVec _ _ _,
        dotProduct_sub, hdoteq, sub_self]
    -- ## Genericity ⇒ on a "good" `(u,v)`, the `z`-polynomial vanishes for all `z`.
    have hgood : ∀ (u v : Fin d → ℝ),
        (u - v) ⬝ᵥ A₁'.mulVec v ≠ 0 →
        (V₂'.mulVec ((1 + β • V₁').mulVec (u - v))) 0 ≠ 0 →
        ∀ z : ℝ, ((B - z • V₁').mulVec (u - v))
            ⬝ᵥ Δ.mulVec (B.mulVec v + z • V₁'.mulVec (u - v)) = 0 := by
      intro u v hlam hq
      apply deg2_eq_zero_of_infinite
      · refine ⟨(B.mulVec (u - v)) ⬝ᵥ Δ.mulVec (B.mulVec v),
          (B.mulVec (u - v)) ⬝ᵥ Δ.mulVec (V₁'.mulVec (u - v))
            - (V₁'.mulVec (u - v)) ⬝ᵥ Δ.mulVec (B.mulVec v),
          -((V₁'.mulVec (u - v)) ⬝ᵥ Δ.mulVec (V₁'.mulVec (u - v))), ?_⟩
        intro z
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
          sub_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct, dotProduct_smul,
          dotProduct_smul, smul_dotProduct]
        ring
      · have hζcont : Continuous (fun t => sig (t * ((u - v) ⬝ᵥ A₁'.mulVec v) + Real.log r)) :=
          hsigcont.comp ((continuous_id.mul continuous_const).add continuous_const)
        have hζinj : Function.Injective
            (fun t => sig (t * ((u - v) ⬝ᵥ A₁'.mulVec v) + Real.log r)) := by
          intro a b hab
          have h1 := sig_injective hab
          have h2 : a * ((u - v) ⬝ᵥ A₁'.mulVec v) = b * ((u - v) ⬝ᵥ A₁'.mulVec v) := by linarith
          exact mul_right_cancel₀ hlam h2
        have hφvcont : Continuous (fun t => V₂'.mulVec
            ((B - sig (t * ((u - v) ⬝ᵥ A₁'.mulVec v) + Real.log r) • V₁').mulVec (u - v))) :=
          Continuous.matrix_mulVec continuous_const
            (Continuous.matrix_mulVec
              (continuous_const.sub (hζcont.smul continuous_const)) continuous_const)
        have hφv0 : V₂'.mulVec
            ((B - sig ((0:ℝ) * ((u - v) ⬝ᵥ A₁'.mulVec v) + Real.log r) • V₁').mulVec (u - v)) ≠ 0 := by
          simp only [zero_mul, zero_add]
          rw [sig_log hr0]
          have hmat : B - ((r : ℝ) / ((r : ℝ) + 1)) • V₁' = 1 + β • V₁' := by
            rw [hB, hβ]
            have hcoef : ((r : ℝ) / ((r : ℝ) + 1)) = 1 - ((r : ℝ) + 1)⁻¹ := by
              field_simp; ring
            rw [hcoef]; module
          rw [hmat]
          intro h0
          exact hq (by simp [h0])
        have hopen : IsOpen {t : ℝ | V₂'.mulVec
            ((B - sig (t * ((u - v) ⬝ᵥ A₁'.mulVec v) + Real.log r) • V₁').mulVec (u - v)) ≠ 0} :=
          hφvcont.isOpen_preimage {x : Fin d → ℝ | x ≠ 0} isOpen_ne
        obtain ⟨δ, hδpos, hball⟩ := Metric.isOpen_iff.mp hopen 0 hφv0
        apply Set.infinite_of_injOn_mapsTo
          (f := fun t => sig (t * ((u - v) ⬝ᵥ A₁'.mulVec v) + Real.log r))
          (hζinj.injOn) ?_ (Set.Ioo_infinite hδpos)
        intro s hs
        have hmem : s ∈ Metric.ball (0:ℝ) δ := by
          rw [Real.ball_eq_Ioo]
          exact ⟨by linarith [hs.1, hδpos], by linarith [hs.2]⟩
        have hφvs : V₂'.mulVec
            ((B - sig (s * ((u - v) ⬝ᵥ A₁'.mulVec v) + Real.log r) • V₁').mulVec (u - v)) ≠ 0 :=
          hball hmem
        exact hextract u v s hs.1 hφvs
    -- ## Density: the `z`-polynomial vanishes for all `(u,v)`, not just generic ones.
    have aux : ∀ (z : ℝ) (u v : Fin d → ℝ),
        ((B - z • V₁').mulVec (u - v))
          ⬝ᵥ Δ.mulVec (B.mulVec v + z • V₁'.mulVec (u - v)) = 0 := by
      intro z
      set lamFac : MvPolynomial (Fin d ⊕ Fin d) ℝ :=
        (fun i => MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i))
          ⬝ᵥ (A₁'.map MvPolynomial.C *ᵥ (fun i => MvPolynomial.X (Sum.inr i))) with hlamFacdef
      set qfac : MvPolynomial (Fin d ⊕ Fin d) ℝ :=
        ((V₂' * (1 + β • V₁')).map MvPolynomial.C
          *ᵥ (fun i => MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i))) 0 with hqfacdef
      have heval_lam : ∀ x : Fin d ⊕ Fin d → ℝ, MvPolynomial.eval x lamFac
          = ((fun i => x (Sum.inl i)) - (fun i => x (Sum.inr i)))
            ⬝ᵥ A₁'.mulVec (fun i => x (Sum.inr i)) := by
        intro x
        have ha : (fun i => MvPolynomial.eval x
              (MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i)))
            = (fun i => x (Sum.inl i)) - (fun i => x (Sum.inr i)) := by
          funext i; simp only [map_sub, MvPolynomial.eval_X, Pi.sub_apply]
        have hb : (fun i => MvPolynomial.eval x
              ((A₁'.map MvPolynomial.C *ᵥ (fun j => MvPolynomial.X (Sum.inr j))) i))
            = A₁'.mulVec (fun i => x (Sum.inr i)) := by
          funext i; rw [eval_mapMat_mulVec']; simp only [MvPolynomial.eval_X]
        rw [hlamFacdef, eval_dotProduct', ha, hb]
      have heval_q : ∀ x : Fin d ⊕ Fin d → ℝ, MvPolynomial.eval x qfac
          = ((V₂' * (1 + β • V₁')).mulVec
              ((fun i => x (Sum.inl i)) - (fun i => x (Sum.inr i)))) 0 := by
        intro x
        have hw : (fun j => MvPolynomial.eval x
              (MvPolynomial.X (Sum.inl j) - MvPolynomial.X (Sum.inr j)))
            = (fun i => x (Sum.inl i)) - (fun i => x (Sum.inr i)) := by
          funext j; simp only [map_sub, MvPolynomial.eval_X, Pi.sub_apply]
        rw [hqfacdef, eval_mapMat_mulVec', hw]
      have heval_Φ : ∀ x : Fin d ⊕ Fin d → ℝ, MvPolynomial.eval x (lamFac * qfac)
          = (((fun i => x (Sum.inl i)) - (fun i => x (Sum.inr i)))
                ⬝ᵥ A₁'.mulVec (fun i => x (Sum.inr i)))
            * (((V₂' * (1 + β • V₁')).mulVec
                ((fun i => x (Sum.inl i)) - (fun i => x (Sum.inr i)))) 0) := by
        intro x; rw [map_mul, heval_lam, heval_q]
      -- nonvanishing of the genericity polynomial
      obtain ⟨i, j, hij⟩ : ∃ i j, A₁' i j ≠ 0 := by
        by_contra h
        simp only [not_exists, ne_eq, not_not] at h
        exact hA1' (by ext i j; exact h i j)
      have hΦ : lamFac * qfac ≠ 0 := by
        apply mul_ne_zero
        · intro h0
          have hev : MvPolynomial.eval
              (Sum.elim (Pi.single i 1 + Pi.single j 1) (Pi.single j 1)) lamFac = 0 := by
            rw [h0]; simp
          rw [heval_lam] at hev
          simp only [Sum.elim_inl, Sum.elim_inr, add_sub_cancel_right] at hev
          rw [Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at hev
          exact hij hev
        · intro h0
          have hev : MvPolynomial.eval
              (Sum.elim (Pi.single 0 1) (0 : Fin d → ℝ)) qfac = 0 := by
            rw [h0]; simp
          rw [heval_q] at hev
          simp only [Sum.elim_inl, Sum.elim_inr, sub_zero] at hev
          rw [Matrix.mulVec_single_one, Matrix.col_apply] at hev
          exact hQ hev
      have hdense : Dense {x : Fin d ⊕ Fin d → ℝ | MvPolynomial.eval x (lamFac * qfac) ≠ 0} :=
        dense_compl_zero_set (lamFac * qfac) hΦ
      set H : (Fin d ⊕ Fin d → ℝ) → ℝ := fun x =>
        ((B - z • V₁').mulVec ((fun i => x (Sum.inl i)) - (fun i => x (Sum.inr i))))
          ⬝ᵥ Δ.mulVec (B.mulVec (fun i => x (Sum.inr i))
              + z • V₁'.mulVec ((fun i => x (Sum.inl i)) - (fun i => x (Sum.inr i)))) with hHdef
      have hUcont : Continuous (fun x : Fin d ⊕ Fin d → ℝ => (fun i => x (Sum.inl i))) :=
        continuous_pi (fun i => continuous_apply (Sum.inl i))
      have hVcont : Continuous (fun x : Fin d ⊕ Fin d → ℝ => (fun i => x (Sum.inr i))) :=
        continuous_pi (fun i => continuous_apply (Sum.inr i))
      have hWcont : Continuous (fun x : Fin d ⊕ Fin d → ℝ =>
          (fun i => x (Sum.inl i)) - (fun i => x (Sum.inr i))) := hUcont.sub hVcont
      have hHcont : Continuous H := by
        rw [hHdef]
        exact (Continuous.matrix_mulVec continuous_const hWcont).dotProduct
          (Continuous.matrix_mulVec continuous_const
            ((Continuous.matrix_mulVec continuous_const hVcont).add
              ((Continuous.matrix_mulVec continuous_const hWcont).const_smul z)))
      have hEqOn : Set.EqOn H 0 {x | MvPolynomial.eval x (lamFac * qfac) ≠ 0} := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        rw [heval_Φ] at hx
        have hlamx : ((fun i => x (Sum.inl i)) - (fun i => x (Sum.inr i)))
            ⬝ᵥ A₁'.mulVec (fun i => x (Sum.inr i)) ≠ 0 := fun h => hx (by rw [h, zero_mul])
        have hqx0 : ((V₂' * (1 + β • V₁')).mulVec
            ((fun i => x (Sum.inl i)) - (fun i => x (Sum.inr i)))) 0 ≠ 0 :=
          fun h => hx (by rw [h, mul_zero])
        have hqx : (V₂'.mulVec ((1 + β • V₁').mulVec
            ((fun i => x (Sum.inl i)) - (fun i => x (Sum.inr i)))) ) 0 ≠ 0 := by
          rwa [← Matrix.mulVec_mulVec] at hqx0
        have hkey := hgood (fun i => x (Sum.inl i)) (fun i => x (Sum.inr i)) hlamx hqx z
        simp only [hHdef, Pi.zero_apply]
        exact hkey
      have hH0 : H = 0 := Continuous.ext_on hdense hHcont continuous_const hEqOn
      intro u v
      have hcong := congrFun hH0 (Sum.elim u v)
      simpa only [hHdef, Pi.zero_apply, Sum.elim_inl, Sum.elim_inr] using hcong
    intro w v z
    have h := aux z (w + v) v
    simpa only [add_sub_cancel_right] using h
  -- `B - V₁' = I`, the identity used at `z = 1`.
  have hBC : B - V₁' = 1 := by rw [hB]; abel
  have hVB : V₁' = B - 1 := by rw [hB]; abel
  have hz1 : ∀ w v, w ⬝ᵥ Δ.mulVec (B.mulVec v + V₁'.mulVec w) = 0 := by
    intro w v
    have h := hpoly w v 1
    simp only [one_smul] at h
    rwa [hBC, Matrix.one_mulVec] at h
  have hWCW : ∀ w, w ⬝ᵥ Δ.mulVec (V₁'.mulVec w) = 0 := by
    intro w
    have h := hz1 w 0
    rwa [Matrix.mulVec_zero, zero_add] at h
  have hΔB : Δ * B = 0 := by
    apply matrix_eq_zero_of_dotProduct
    intro w v
    rw [← Matrix.mulVec_mulVec]
    have h := hz1 w v
    rwa [Matrix.mulVec_add, dotProduct_add, hWCW w, add_zero] at h
  have hskew : Δᵀ = -Δ := by
    apply skew_of_quadratic_zero
    intro w
    have hBm1 : (B - 1).mulVec w = B.mulVec w - w := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    have hv : Δ.mulVec (V₁'.mulVec w) = Δ.mulVec (B.mulVec w) - Δ.mulVec w := by
      rw [hVB, hBm1, Matrix.mulVec_sub]
    have h := hWCW w
    rw [hv, dotProduct_sub] at h
    have h2 : w ⬝ᵥ Δ.mulVec (B.mulVec w) = 0 := by
      rw [Matrix.mulVec_mulVec, hΔB, Matrix.zero_mulVec, dotProduct_zero]
    rw [h2] at h
    linarith
  have hΔ0 : Δ = 0 := skew_eq_zero_of_mul_eq_zero hskew hΔB hdet
  rw [hΔ, sub_eq_zero] at hΔ0
  exact hΔ0

/-! ## Main theorem -/

theorem identifiability (r d : ℕ) (hr : 2 ≤ r) (hd : 3 ≤ d) :
    ∃ N : Set (Params d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : Params d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ,
          network θ X = network θ' X) →
        θ = θ' := by
  haveI : NeZero d := ⟨by omega⟩
  refine ⟨{θ : Params d | (MvPolynomial.eval (flat d θ)) (genPoly r d) = 0},
    genericity_null r d hr hd, ?_⟩
  intro θ' hθ' θ hagree
  obtain ⟨⟨V₁', A₁'⟩, ⟨V₂', A₂'⟩⟩ := θ'
  obtain ⟨⟨V₁, A₁⟩, ⟨V₂, A₂⟩⟩ := θ
  rw [Set.mem_setOf_eq] at hθ'
  -- restrict agreement to two-type inputs
  have hagree_tt : ∀ (u v : Fin d → ℝ) (c : ℝ),
      network ((V₁, A₁), (V₂, A₂)) (twoType r d u v c)
        = network ((V₁', A₁'), (V₂', A₂')) (twoType r d u v c) :=
    fun u v c => hagree (twoType r d u v c)
  -- ## Extract the four genericity factors from `eval (flat θ') (genPoly r d) ≠ 0`.
  set β : ℝ := ((r : ℝ) + 1)⁻¹ with hβ
  set e : Fin (d - 1) → Fin d := Fin.castLE (Nat.sub_le d 1) with he
  set f : RR d →+* ℝ := MvPolynomial.eval (flat d ((V₁', A₁'), (V₂', A₂'))) with hf
  set F : Matrix (Fin d) (Fin d) (RR d) →+* Matrix (Fin d) (Fin d) ℝ := f.mapMatrix with hFdef
  have hFV1 : F (genV1 d) = V₁' := by
    rw [hFdef, RingHom.mapMatrix_apply, hf, map_genV1]
  have hFA1 : F (genA1 d) = A₁' := by
    rw [hFdef, RingHom.mapMatrix_apply, hf, map_genA1]
  have hFV2 : F (genV2 d) = V₂' := by
    rw [hFdef, RingHom.mapMatrix_apply, hf, map_genV2]
  have hFA2 : F (genA2 d) = A₂' := by
    rw [hFdef, RingHom.mapMatrix_apply, hf, map_genA2]
  have entry : ∀ (M : Matrix (Fin d) (Fin d) (RR d)) (i j : Fin d), f (M i j) = (F M) i j := by
    intro M i j; rw [hFdef, RingHom.mapMatrix_apply, Matrix.map_apply]
  have hFsmul : ∀ (c : RR d) (M : Matrix (Fin d) (Fin d) (RR d)),
      F (c • M) = (f c) • (F M) := by
    intro c M; ext i j
    rw [hFdef, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      map_mul, Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply]
  have hFB : F (1 + (MvPolynomial.C β : RR d) • genV1 d) = 1 + β • V₁' := by
    rw [map_add, map_one, hFsmul, hFV1]; congr 1; rw [hf]; simp
  have hFt : ∀ M : Matrix (Fin d) (Fin d) (RR d), F Mᵀ = (F M)ᵀ := by
    intro M; rw [hFdef, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map]
  have hfD : f (((1 + genV1 d).submatrix e e).det) = ((1 + V₁').submatrix e e).det := by
    have hMm : ((1 + genV1 d).submatrix e e).map f = (1 + V₁').submatrix e e := by
      rw [← submatrix_map]
      congr 1
      rw [← RingHom.mapMatrix_apply, ← hFdef, map_add, map_one, hFV1]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hMm]
  have hfa : f (genA1 d 0 0) = A₁' 0 0 := by rw [entry, hFA1]
  have hfp3 : f ((genV2 d * (1 + (MvPolynomial.C β : RR d) • genV1 d) :
      Matrix (Fin d) (Fin d) (RR d)) 0 0)
      = (V₂' * (1 + β • V₁') : Matrix (Fin d) (Fin d) ℝ) 0 0 := by
    rw [entry, map_mul, hFV2, hFB]
  have hfp4 : f (((1 + (MvPolynomial.C β : RR d) • genV1 d)ᵀ * genA2 d * genV1 d :
      Matrix (Fin d) (Fin d) (RR d)) 0 0)
      = ((1 + β • V₁')ᵀ * A₂' * V₁' : Matrix (Fin d) (Fin d) ℝ) 0 0 := by
    rw [entry, map_mul, map_mul, hFV1, hFA2, hFt, hFB]
  have hval : f (genPoly r d)
      = ((1 + V₁').submatrix e e).det * (A₁' 0 0)
        * ((V₂' * (1 + β • V₁') : Matrix (Fin d) (Fin d) ℝ) 0 0)
        * ((1 + β • V₁')ᵀ * A₂' * V₁' : Matrix (Fin d) (Fin d) ℝ) 0 0 := by
    rw [genPoly, map_mul, map_mul, map_mul, hfD, hfa, hfp3, hfp4]
  rw [hf, hval] at hθ'
  have hdet : ((1 + V₁').submatrix e e).det ≠ 0 := fun h => hθ' (by rw [h]; ring)
  have hA1factor : A₁' 0 0 ≠ 0 := fun h => hθ' (by rw [h]; ring)
  have hQ : (V₂' * (1 + β • V₁') : Matrix (Fin d) (Fin d) ℝ) 0 0 ≠ 0 :=
    fun h => hθ' (by rw [h]; ring)
  have hM : ((1 + β • V₁')ᵀ * A₂' * V₁' : Matrix (Fin d) (Fin d) ℝ) 0 0 ≠ 0 :=
    fun h => hθ' (by rw [h]; ring)
  have hA1' : A₁' ≠ 0 := fun h => hA1factor (by rw [h]; rfl)
  -- ## Chain the three identification lemmas.
  obtain ⟨hV1, hV2⟩ := identify_V hr hQ hM hagree_tt
  have hA1 : A₁ = A₁' := identify_A1 hr hA1' hQ hM hV1 hV2 hagree_tt
  have hA2 : A₂ = A₂' := identify_A2 hr hd hA1' hQ hdet hV1 hV2 hA1 hagree_tt
  rw [hV1, hV2, hA1, hA2]

end TransformerIdentifiability.TwoLayer
