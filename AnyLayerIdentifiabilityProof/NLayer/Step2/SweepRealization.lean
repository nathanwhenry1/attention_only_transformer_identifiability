import AnyLayerIdentifiabilityProof.NLayer.Step2.IDLSweep
import AnyLayerIdentifiabilityProof.NLayer.Analytic.DialAsymptotics

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

open scoped Matrix Topology
-- The Frobenius matrix norm makes `Matrix (Fin d) (Fin d) ℝ` a `NormedRing`/`NormedAlgebra`,
-- which is needed to differentiate the matrix inverse via `hasStrictFDerivAt_ringInverse`.
-- (Matrix norms are not global instances in Mathlib; we choose Frobenius here.  The choice is
-- irrelevant to the derivative *values*, which are norm-independent in finite dimension.)
open scoped Matrix.Norms.Frobenius

/-!
# Pointwise realization of the sweep frontier (abstract analytic core)

This file formalizes the analytic core of the "sweep realization" described in
`NLayer/SWEEP_PLAN.md`: starting from a first-layer anchor point with dial value
`t ∈ (0,1)`, a vanishing quadric `matrixBilin A w⁰ v⁰ = 0`, the two skip/step
matrices invertible, and the Jacobian scalar `texSweepVartheta0 ≠ 0`, every probe
point `η` in an open neighborhood of `firstLayerDialPoint V t w⁰ v⁰` is realized as
`firstLayerEffectivePoint r V A w v τ` for suitable `(w, v)` and all sufficiently
large `τ`.

The route (linear solve → scalar equation → inverse-function theorem → packaging)
follows `SWEEP_PLAN.md`. The crux derivative step (`∂_s F = ± texSweepVartheta0`) is
isolated; the main theorem is also available in a conditional form that takes the
augmented strict derivative as an explicit hypothesis.
-/

variable {d : ℕ}

/-! ## Step 1. Linear solve

`Msolve V s = skipB V − s • V = anchorStepMatrix (fun _ => (V, A)) 0 s`. For `s` with
`(Msolve V s).det ≠ 0` and `(skipB V).det ≠ 0`, the explicit preimages `wsolFun`,
`vsolFun` satisfy `firstLayerDialPoint V s (wsolFun …) (vsolFun …) = η`. -/

/-- The step matrix `B − sV` (`= anchorStepMatrix (fun _ => (V,A)) 0 s`). -/
noncomputable def Msolve (V : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  skipB V - s • V

theorem Msolve_eq_anchorStepMatrix (V A : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) :
    Msolve V s = anchorStepMatrix (fun _ => (V, A)) 0 s :=
  rfl

/-- `(B − sV) *ᵥ w` written out. -/
theorem Msolve_mulVec (V : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (w : Fin d → ℝ) :
    Msolve V s *ᵥ w = w + V.mulVec w - s • V.mulVec w := by
  simp only [Msolve, skipB, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec]

/-- `(skipB V) *ᵥ v` written out. -/
theorem skipB_mulVec (V : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    skipB V *ᵥ v = v + V.mulVec v := by
  simp only [skipB, Matrix.add_mulVec, Matrix.one_mulVec]

/-- The first preimage coordinate `w` solving the linear system. -/
noncomputable def wsolFun (V : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (η : ProbePoint d) :
    Fin d → ℝ :=
  (Msolve V s)⁻¹ *ᵥ η.1

/-- The second preimage coordinate `v` solving the linear system. -/
noncomputable def vsolFun (V : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (η : ProbePoint d) :
    Fin d → ℝ :=
  (skipB V)⁻¹ *ᵥ (η.2 - s • V.mulVec (wsolFun V s η))

/-- **Step 1 (linear solve).** The explicit preimages invert the dial map. -/
theorem firstLayerDialPoint_wsolFun_vsolFun
    (V : Matrix (Fin d) (Fin d) ℝ) (s : ℝ)
    (hB : (skipB V).det ≠ 0) (hM : (Msolve V s).det ≠ 0) (η : ProbePoint d) :
    firstLayerDialPoint V s (wsolFun V s η) (vsolFun V s η) = η := by
  set w := wsolFun V s η with hw
  set v := vsolFun V s η with hv
  apply Prod.ext
  · show w + V.mulVec w - s • V.mulVec w = η.1
    rw [← Msolve_mulVec, hw, wsolFun, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (Ne.isUnit hM), Matrix.one_mulVec]
  · show v + V.mulVec v + s • V.mulVec w = η.2
    have hskip : v + V.mulVec v = skipB V *ᵥ v := (skipB_mulVec V v).symm
    rw [show v + V.mulVec v + s • V.mulVec w = skipB V *ᵥ v + s • V.mulVec w by
          rw [hskip], hv, vsolFun]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hB), Matrix.one_mulVec]
    abel

/-! ## Step 2. Anchor base point reductions

At the anchor `p♭ := firstLayerDialPoint V t w⁰ v⁰`, the preimages return the anchor:
`wsolFun V t p♭ = w⁰` and `vsolFun V t p♭ = v⁰`. -/

theorem wsolFun_anchor
    (V : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (w0 v0 : Fin d → ℝ)
    (hM : (Msolve V t).det ≠ 0) :
    wsolFun V t (firstLayerDialPoint V t w0 v0) = w0 := by
  rw [wsolFun, firstLayerDialPoint_fst, ← Msolve_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (Ne.isUnit hM), Matrix.one_mulVec]

theorem vsolFun_anchor
    (V : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (w0 v0 : Fin d → ℝ)
    (hB : (skipB V).det ≠ 0) (hM : (Msolve V t).det ≠ 0) :
    vsolFun V t (firstLayerDialPoint V t w0 v0) = v0 := by
  rw [vsolFun, wsolFun_anchor V t w0 v0 hM, firstLayerDialPoint_snd]
  have : v0 + V.mulVec v0 + t • V.mulVec w0 - t • V.mulVec w0 = skipB V *ᵥ v0 := by
    rw [skipB_mulVec]; abel
  rw [this, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hB), Matrix.one_mulVec]

/-! ## Step 2 (cont). The scalar function `F`

`gFun s η := matrixBilin A (wsolFun V s η) (vsolFun V s η)` and
`Ffun s η u := gFun s η − (sigmoidLogit s − log r) · u`. At the anchor with `u = 0`,
`Ffun t p♭ 0 = matrixBilin A w⁰ v⁰ = 0`. -/

/-- The scalar quadric value along the linear solve. -/
noncomputable def gFun (V A : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (η : ProbePoint d) : ℝ :=
  matrixBilin A (wsolFun V s η) (vsolFun V s η)

/-- The scalar realization function. -/
noncomputable def Ffun (r : ℕ) (V A : Matrix (Fin d) (Fin d) ℝ)
    (s : ℝ) (η : ProbePoint d) (u : ℝ) : ℝ :=
  gFun V A s η - (sigmoidLogit s - Real.log r) * u

/-- **Step 2.** `Ffun` vanishes at the anchor base point with `u = 0`. -/
theorem Ffun_anchor (r : ℕ) (V A : Matrix (Fin d) (Fin d) ℝ)
    (t : ℝ) (w0 v0 : Fin d → ℝ)
    (hB : (skipB V).det ≠ 0) (hM : (Msolve V t).det ≠ 0)
    (hq : matrixBilin A w0 v0 = 0) :
    Ffun r V A t (firstLayerDialPoint V t w0 v0) 0 = 0 := by
  simp only [Ffun, mul_zero, sub_zero, gFun, wsolFun_anchor V t w0 v0 hM,
    vsolFun_anchor V t w0 v0 hB hM, hq]

/-! ## Persistence of invertibility near `t` -/

theorem eventually_Msolve_det_ne (V : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (hM : (Msolve V t).det ≠ 0) :
    ∀ᶠ s in 𝓝 t, (Msolve V s).det ≠ 0 := by
  have hc : Continuous (fun s : ℝ => (Msolve V s).det) := by
    unfold Msolve; fun_prop
  exact hc.continuousAt.eventually_ne hM

/-! ## Step 5 ingredient. Gate consistency -/

/-- If `τ · matrixBilin A w v + log r = sigmoidLogit s` with `s ∈ (0,1)`, then the
first-layer gate equals `s` (the saturation-matching step). -/
theorem firstLayerGate_eq_of_logit (r : ℕ) (A : Matrix (Fin d) (Fin d) ℝ)
    (s : ℝ) (τ : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (w v : Fin d → ℝ)
    (heq : τ * matrixBilin A w v + Real.log r = sigmoidLogit s) :
    firstLayerGate r A w v τ = s := by
  rw [firstLayerGate, heq, sig_sigmoidLogit hs0 hs1]

/-! ## Step 3. Derivative building blocks and the scalar Jacobian (CRUX)

These lemmas compute, at the anchor, the strict derivatives in the gate variable `s`:
the matrix inverse `(Msolve V s)⁻¹` (via Mathlib's `hasStrictFDerivAt_ringInverse`, which
needs the Frobenius `NormedAlgebra` structure on matrices), the linear solves `wsolFun`,
`vsolFun`, and finally the scalar `Ffun`.  The punchline (`hasStrictDerivAt_Ffun_anchor`)
is the TeX identity `∂_ς Q(0,0) = -ϑ₀`: the derivative of `s ↦ Ffun r V A s p♭ 0` at `t`
equals `- texSweepVartheta0 V A (w0,v0) t`.  The clean intermediate identity that makes the
two bilinear contributions collapse is `vsol'(t) = - wsol'(t)`. -/

theorem hasStrictDerivAt_Msolve (V : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) :
    HasStrictDerivAt (fun σ : ℝ => Msolve V σ) (-V) s := by
  unfold Msolve
  have h2 : HasStrictDerivAt (fun σ : ℝ => σ • V) V s := by
    simpa using (hasStrictDerivAt_id s).smul_const V
  simpa using (hasStrictDerivAt_const s (skipB V)).sub h2
theorem hasStrictDerivAt_Minv (V : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (hMt : (Msolve V t).det ≠ 0) :
    HasStrictDerivAt (fun σ : ℝ => (Msolve V σ)⁻¹)
      ((Msolve V t)⁻¹ * V * (Msolve V t)⁻¹) t := by
  have hunit : IsUnit (Msolve V t) := (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hMt)
  obtain ⟨u, hu⟩ := hunit
  have hconv : (fun σ : ℝ => (Msolve V σ)⁻¹) = (fun σ : ℝ => Ring.inverse (Msolve V σ)) := by
    funext σ; exact Matrix.nonsing_inv_eq_ringInverse (A := Msolve V σ)
  rw [hconv]
  have huinv : (↑u⁻¹ : Matrix (Fin d) (Fin d) ℝ) = (Msolve V t)⁻¹ := by
    rw [Matrix.coe_units_inv, hu]
  have hMs : HasStrictDerivAt (fun σ : ℝ => Msolve V σ) (-V) t := hasStrictDerivAt_Msolve V t
  have hrinv : HasStrictFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin d) (Fin d) ℝ) (↑u⁻¹) (↑u⁻¹)) (↑u) :=
    hasStrictFDerivAt_ringInverse u
  rw [hu] at hrinv
  have hchain := hrinv.comp_hasStrictDerivAt t hMs
  refine hchain.congr_deriv ?_
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply, huinv,
    mul_neg, neg_mul, neg_neg]
noncomputable def mulVecRightCLM (x : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ →L[ℝ] (Fin d → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ x
      map_add' := fun M N => by simp [Matrix.add_mulVec]
      map_smul' := fun c M => by simp [Matrix.smul_mulVec] }
@[simp] theorem mulVecRightCLM_apply (x : Fin d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    mulVecRightCLM x M = M *ᵥ x := rfl
noncomputable def mulVecLeftCLM (M : Matrix (Fin d) (Fin d) ℝ) :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)
@[simp] theorem mulVecLeftCLM_apply (M : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    mulVecLeftCLM M x = M *ᵥ x := rfl

theorem hasStrictDerivAt_wsol_anchor (V : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (w0 v0 : Fin d → ℝ) (hMt : (Msolve V t).det ≠ 0) :
    HasStrictDerivAt (fun σ : ℝ => wsolFun V σ (firstLayerDialPoint V t w0 v0))
      ((Msolve V t)⁻¹ *ᵥ (V *ᵥ w0)) t := by
  set η := firstLayerDialPoint V t w0 v0 with hη
  have hfun : (fun σ : ℝ => wsolFun V σ η) =
      (fun σ : ℝ => (mulVecRightCLM η.1) ((Msolve V σ)⁻¹)) := by
    funext σ; rw [mulVecRightCLM_apply, wsolFun]
  rw [hfun]
  have hcomp := (mulVecRightCLM η.1).hasStrictFDerivAt.comp_hasStrictDerivAt t
    (hasStrictDerivAt_Minv V t hMt)
  refine hcomp.congr_deriv ?_
  have hη1 : η.1 = Msolve V t *ᵥ w0 := by rw [hη, firstLayerDialPoint_fst, Msolve_mulVec]
  show (mulVecRightCLM η.1) ((Msolve V t)⁻¹ * V * (Msolve V t)⁻¹) = _
  rw [mulVecRightCLM_apply, hη1, Matrix.mulVec_mulVec,
    Matrix.mul_assoc (Msolve V t)⁻¹ V (Msolve V t)⁻¹,
    Matrix.mul_assoc (Msolve V t)⁻¹ (V * (Msolve V t)⁻¹) (Msolve V t),
    Matrix.mul_assoc V (Msolve V t)⁻¹ (Msolve V t),
    Matrix.nonsing_inv_mul _ (Ne.isUnit hMt), Matrix.mul_one, ← Matrix.mulVec_mulVec]

theorem hasStrictDerivAt_vsol_anchor (V : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (w0 v0 : Fin d → ℝ) (hB : (skipB V).det ≠ 0) (hMt : (Msolve V t).det ≠ 0) :
    HasStrictDerivAt (fun σ : ℝ => vsolFun V σ (firstLayerDialPoint V t w0 v0))
      (-((Msolve V t)⁻¹ *ᵥ (V *ᵥ w0))) t := by
  set η := firstLayerDialPoint V t w0 v0 with hη
  set wsolp := (Msolve V t)⁻¹ *ᵥ (V *ᵥ w0) with hwsolp
  have hVw : HasStrictDerivAt (fun σ : ℝ => V *ᵥ wsolFun V σ η) (V *ᵥ wsolp) t := by
    have h := (mulVecLeftCLM V).hasStrictFDerivAt.comp_hasStrictDerivAt t
      (hasStrictDerivAt_wsol_anchor V t w0 v0 hMt)
    refine h.congr_deriv ?_
    show (mulVecLeftCLM V) wsolp = _
    rw [mulVecLeftCLM_apply]
  have hwsol0 : wsolFun V t η = w0 := wsolFun_anchor V t w0 v0 hMt
  have hsmul : HasStrictDerivAt (fun σ : ℝ => σ • (V *ᵥ wsolFun V σ η))
      ((V *ᵥ w0) + t • (V *ᵥ wsolp)) t := by
    have h := (hasStrictDerivAt_id t).smul hVw
    refine h.congr_deriv ?_
    rw [id_eq, hwsol0, one_smul, add_comm]
  have hinner : HasStrictDerivAt (fun σ : ℝ => η.2 - σ • (V *ᵥ wsolFun V σ η))
      (-((V *ᵥ w0) + t • (V *ᵥ wsolp))) t := by
    have := (hasStrictDerivAt_const t η.2).sub hsmul
    simpa using this
  have hfun : (fun σ : ℝ => vsolFun V σ η) =
      (fun σ : ℝ => mulVecLeftCLM (skipB V)⁻¹ (η.2 - σ • (V *ᵥ wsolFun V σ η))) := by
    funext σ; rw [mulVecLeftCLM_apply, vsolFun]
  rw [hfun]
  have hcomp := (mulVecLeftCLM (skipB V)⁻¹).hasStrictFDerivAt.comp_hasStrictDerivAt t hinner
  refine hcomp.congr_deriv ?_
  show (mulVecLeftCLM (skipB V)⁻¹) (-((V *ᵥ w0) + t • (V *ᵥ wsolp))) = _
  rw [mulVecLeftCLM_apply]
  -- skipB V *ᵥ wsolp = V*ᵥw0 + t•(V*ᵥwsolp)
  have hkey : skipB V *ᵥ wsolp = V *ᵥ w0 + t • (V *ᵥ wsolp) := by
    have hM : Msolve V t *ᵥ wsolp = V *ᵥ w0 := by
      rw [hwsolp, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hMt),
        Matrix.one_mulVec]
    have : (skipB V - t • V) *ᵥ wsolp = V *ᵥ w0 := hM
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec] at this
    rw [← this, sub_add_cancel]
  rw [show -((V *ᵥ w0) + t • (V *ᵥ wsolp)) = skipB V *ᵥ (-wsolp) by
        rw [Matrix.mulVec_neg, hkey],
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hB), Matrix.one_mulVec]

noncomputable def dotRightCLM (a : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => x ⬝ᵥ a
      map_add' := fun x y => by simp [add_dotProduct]
      map_smul' := fun c x => by simp [smul_dotProduct] }
@[simp] theorem dotRightCLM_apply (a x : Fin d → ℝ) : dotRightCLM a x = x ⬝ᵥ a := rfl
noncomputable def dotRightCLM' : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := dotRightCLM
      map_add' := fun a b => by ext x; simp [dotProduct_add]
      map_smul' := fun c a => by ext x; simp [dotProduct_smul] }
@[simp] theorem dotRightCLM'_apply (a x : Fin d → ℝ) : dotRightCLM' a x = x ⬝ᵥ a := rfl

/-- **Step 3 (scalar derivative, CRUX).**  The scalar function `s ↦ Ffun r V A s p♭ 0`
has strict derivative `- texSweepVartheta0 V A (w0,v0) t` at `s = t`. -/
theorem hasStrictDerivAt_Ffun_anchor (r : ℕ) (V A : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (w0 v0 : Fin d → ℝ) (hB : (skipB V).det ≠ 0) (hMt : (Msolve V t).det ≠ 0) :
    HasStrictDerivAt (fun σ : ℝ => Ffun r V A σ (firstLayerDialPoint V t w0 v0) 0)
      (- texSweepVartheta0 V A (w0, v0) t) t := by
  set η := firstLayerDialPoint V t w0 v0 with hη
  set wsolp := (Msolve V t)⁻¹ *ᵥ (V *ᵥ w0) with hwsolp
  have hwsol' := hasStrictDerivAt_wsol_anchor V t w0 v0 hMt
  have hvsol' := hasStrictDerivAt_vsol_anchor V t w0 v0 hB hMt
  have hwsol0 : wsolFun V t η = w0 := wsolFun_anchor V t w0 v0 hMt
  have hvsol0 : vsolFun V t η = v0 := vsolFun_anchor V t w0 v0 hB hMt
  -- Ffun σ η 0 = gFun V A σ η = matrixBilin A (wsolFun V σ η)(vsolFun V σ η)
  have hFg : (fun σ : ℝ => Ffun r V A σ η 0) = (fun σ : ℝ => gFun V A σ η) := by
    funext σ; simp [Ffun]
  rw [hFg]
  -- gFun = (dotRightCLM' (A *ᵥ vsolFun V σ η)) (wsolFun V σ η)
  have hgcl : (fun σ : ℝ => gFun V A σ η) =
      (fun σ : ℝ => (dotRightCLM' (A *ᵥ vsolFun V σ η)) (wsolFun V σ η)) := by
    funext σ; rw [dotRightCLM'_apply, gFun, matrixBilin]
  rw [hgcl]
  -- c σ := dotRightCLM' (A *ᵥ vsolFun V σ η), strict deriv = dotRightCLM' (A *ᵥ vsol'(t))
  have hAv : HasStrictDerivAt (fun σ : ℝ => A *ᵥ vsolFun V σ η) (A *ᵥ (-wsolp)) t := by
    have h := (mulVecLeftCLM A).hasStrictFDerivAt.comp_hasStrictDerivAt t hvsol'
    refine h.congr_deriv ?_
    show (mulVecLeftCLM A) (-wsolp) = _
    rw [mulVecLeftCLM_apply]
  have hc : HasStrictDerivAt (fun σ : ℝ => dotRightCLM' (A *ᵥ vsolFun V σ η))
      (dotRightCLM' (A *ᵥ (-wsolp))) t := by
    have h := (dotRightCLM' ).hasStrictFDerivAt.comp_hasStrictDerivAt t hAv
    exact h
  -- clm_apply
  have hmain := hc.clm_apply hwsol'
  refine hmain.congr_deriv ?_
  simp only [dotRightCLM'_apply, hη, wsolFun_anchor V t w0 v0 hMt,
    vsolFun_anchor V t w0 v0 hB hMt]
  -- goal: w0 ⬝ᵥ (A *ᵥ -wsolp) + wsolp ⬝ᵥ (A *ᵥ v0) = - texSweepVartheta0 V A (w0,v0) t
  have hcollapse : matrixBilin A w0 (-wsolp) + matrixBilin A wsolp v0
      = - texSweepVartheta0 V A (w0, v0) t := by
    rw [texSweepVartheta0]
    have hanchor : (anchorStepMatrix (fun _ => (V, A)) 0 t)⁻¹ *ᵥ (V *ᵥ (w0, v0).1) = wsolp := by
      rw [hwsolp]; rfl
    rw [hanchor, firstLayerPi]
    simp only [matrixBilin]
    rw [sub_dotProduct, Matrix.mulVec_neg, dotProduct_neg]
    have hadj : w0 ⬝ᵥ (A *ᵥ wsolp) = (Aᵀ *ᵥ w0) ⬝ᵥ wsolp := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.transpose_transpose A, Matrix.vecMul_transpose,
        Matrix.transpose_transpose]
    rw [hadj, dotProduct_comm wsolp (A *ᵥ v0)]
    ring
  rw [← hcollapse]
  simp only [matrixBilin, hwsolp]


/-! ## Step 4. The augmented inverse-function-theorem map

`augΦ (s, η, u) = (Ffun r V A s η u, η, u)`. Its second and third components are the
identity projections, so the only nontrivial Jacobian entry is `∂_s Ffun`. Given that the
augmented strict derivative is a `ContinuousLinearEquiv` (which holds exactly when
`∂_s Ffun = ± texSweepVartheta0 ≠ 0`; see Step 3 below), the inverse function theorem
solves `Ffun = 0` for `s` on a neighborhood, which assembles into the realization. -/

/-- The augmented map used for the inverse function theorem. -/
noncomputable def augΦ (r : ℕ) (V A : Matrix (Fin d) (Fin d) ℝ) :
    ℝ × ProbePoint d × ℝ → ℝ × ProbePoint d × ℝ :=
  fun x => (Ffun r V A x.1 x.2.1 x.2.2, x.2.1, x.2.2)

@[simp] theorem augΦ_apply (r : ℕ) (V A : Matrix (Fin d) (Fin d) ℝ)
    (x : ℝ × ProbePoint d × ℝ) :
    augΦ r V A x = (Ffun r V A x.1 x.2.1 x.2.2, x.2.1, x.2.2) := rfl

/-- **Conditional realization theorem.**  Steps 1, 2, 4, 5 of `SWEEP_PLAN.md`, taking the
augmented strict derivative (packaged as a `ContinuousLinearEquiv`) as a hypothesis.  This
is the honest conditional form: the only fact deferred is that the augmented Jacobian at the
anchor is invertible, which is precisely `texSweepVartheta0 ≠ 0` (Step 3). -/
theorem sweep_pointwise_realization_open_of_strictDeriv
    (r : ℕ) (V A : Matrix (Fin d) (Fin d) ℝ) (w0 v0 : Fin d → ℝ) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hB : (skipB V).det ≠ 0) (hMt : (Msolve V t).det ≠ 0)
    (hq : matrixBilin A w0 v0 = 0)
    (E : (ℝ × ProbePoint d × ℝ) ≃L[ℝ] (ℝ × ProbePoint d × ℝ))
    (hΦ : HasStrictFDerivAt (augΦ r V A)
      (↑E : (ℝ × ProbePoint d × ℝ) →L[ℝ] (ℝ × ProbePoint d × ℝ))
      (t, firstLayerDialPoint V t w0 v0, 0)) :
    ∃ U : Set (ProbePoint d), IsOpen U ∧ firstLayerDialPoint V t w0 v0 ∈ U ∧
      ∃ T : ℝ, 0 ≤ T ∧ ∀ η ∈ U, ∀ τ : ℝ, T < τ →
        ∃ w v : Fin d → ℝ, firstLayerEffectivePoint r V A w v τ = η := by
  set p := firstLayerDialPoint V t w0 v0 with hp
  set a : ℝ × ProbePoint d × ℝ := (t, p, 0) with ha
  have hΦa : augΦ r V A a = (0, p, 0) := by
    have hF : Ffun r V A t p 0 = 0 := Ffun_anchor r V A t w0 v0 hB hMt hq
    simp only [augΦ_apply, ha]; rw [hF]
  set inv := hΦ.localInverse (augΦ r V A) E a with hinv_def
  have hval : inv (augΦ r V A a) = a := hΦ.localInverse_apply_image
  have hcont : ContinuousAt inv (augΦ r V A a) := hΦ.to_localInverse.continuousAt
  have hright : ∀ᶠ y in 𝓝 (augΦ r V A a), augΦ r V A (inv y) = y :=
    hΦ.eventually_right_inverse
  have hScont : ∀ᶠ y in 𝓝 (augΦ r V A a),
      0 < (inv y).1 ∧ (inv y).1 < 1 ∧ (Msolve V (inv y).1).det ≠ 0 := by
    have hSt : {x : ℝ | 0 < x ∧ x < 1 ∧ (Msolve V x).det ≠ 0} ∈ 𝓝 t := by
      filter_upwards [Ioo_mem_nhds ht0 ht1, eventually_Msolve_det_ne V t hMt]
        with x hx hx2 using ⟨hx.1, hx.2, hx2⟩
    have hqcont : ContinuousAt (fun y => (inv y).1) (augΦ r V A a) :=
      (continuous_fst.continuousAt).comp hcont
    have hmem : {x : ℝ | 0 < x ∧ x < 1 ∧ (Msolve V x).det ≠ 0} ∈
        𝓝 ((inv (augΦ r V A a)).1) := by
      rw [hval, ha]; exact hSt
    have := hqcont.preimage_mem_nhds hmem
    filter_upwards [this] with y hy using hy
  have hcombo : ∀ᶠ y in 𝓝 (augΦ r V A a),
      augΦ r V A (inv y) = y ∧ 0 < (inv y).1 ∧ (inv y).1 < 1 ∧
        (Msolve V (inv y).1).det ≠ 0 := hright.and hScont
  rw [hΦa] at hcombo
  rw [Filter.eventually_iff, mem_nhds_iff] at hcombo
  obtain ⟨W, hWsub, hWopen, hWmem⟩ := hcombo
  have hWnhds : W ∈ 𝓝 ((0 : ℝ), p, (0:ℝ)) := hWopen.mem_nhds hWmem
  rw [nhds_prod_eq, nhds_prod_eq] at hWnhds
  obtain ⟨A0, hA0, BC, hBC, hsub⟩ := Filter.mem_prod_iff.mp hWnhds
  obtain ⟨U0, hU0, C0, hC0, hsub2⟩ := Filter.mem_prod_iff.mp hBC
  obtain ⟨A', hA'sub, hA'open, h0A'⟩ := mem_nhds_iff.mp hA0
  obtain ⟨U', hU'sub, hU'open, hpU'⟩ := mem_nhds_iff.mp hU0
  obtain ⟨C', hC'sub, hC'open, h0C'⟩ := mem_nhds_iff.mp hC0
  obtain ⟨ε, hε, hIoo⟩ : ∃ ε > 0, Set.Ioo (-ε) ε ⊆ C' := by
    rw [Metric.isOpen_iff] at hC'open
    obtain ⟨ε, hε, hball⟩ := hC'open 0 h0C'
    exact ⟨ε, hε, fun x hx => hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact ⟨hx.1, hx.2⟩)⟩
  have hbox : A' ×ˢ U' ×ˢ C' ⊆ W := fun pt hpt =>
    hsub ⟨hA'sub hpt.1, hsub2 ⟨hU'sub hpt.2.1, hC'sub hpt.2.2⟩⟩
  refine ⟨U', hU'open, hpU', ε⁻¹, le_of_lt (inv_pos.mpr hε), ?_⟩
  intro η hηU τ hτ
  have hτpos : 0 < τ := lt_trans (inv_pos.mpr hε) hτ
  have hu_pos : 0 < τ⁻¹ := inv_pos.mpr hτpos
  have hu_lt : τ⁻¹ < ε := by rw [inv_lt_comm₀ hτpos hε]; exact hτ
  set y : ℝ × ProbePoint d × ℝ := (0, η, τ⁻¹) with hy
  have hyW : y ∈ W := hbox ⟨h0A', hηU, hIoo ⟨by linarith, hu_lt⟩⟩
  obtain ⟨hΦeq, hs0, hs1, hsdet⟩ := hWsub hyW
  set s := (inv y).1 with hs
  have hcomp2 : (inv y).2.1 = η := by
    have := congrArg (fun z => z.2.1) hΦeq; simpa [augΦ_apply, hy] using this
  have hcomp3 : (inv y).2.2 = τ⁻¹ := by
    have := congrArg (fun z => z.2.2) hΦeq; simpa [augΦ_apply, hy] using this
  have hF0 : Ffun r V A s η τ⁻¹ = 0 := by
    have h1 := congrArg (fun z => z.1) hΦeq
    simp only [augΦ_apply, hy] at h1
    rw [hcomp2, hcomp3] at h1; rw [hs]; exact h1
  set w := wsolFun V s η with hwdef
  set v := vsolFun V s η with hvdef
  have hg : matrixBilin A w v = (sigmoidLogit s - Real.log r) * τ⁻¹ := by
    have hzero : gFun V A s η - (sigmoidLogit s - Real.log r) * τ⁻¹ = 0 := hF0
    have hgF : gFun V A s η = matrixBilin A w v := by rw [gFun, hwdef, hvdef]
    rw [hgF] at hzero; linarith
  have hlogit : τ * matrixBilin A w v + Real.log r = sigmoidLogit s := by
    rw [hg, mul_comm (sigmoidLogit s - Real.log r) τ⁻¹, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hτpos), one_mul]; ring
  have hgate : firstLayerGate r A w v τ = s :=
    firstLayerGate_eq_of_logit r A s τ hs0 hs1 w v hlogit
  refine ⟨w, v, ?_⟩
  rw [firstLayerEffectivePoint, hgate]
  exact firstLayerDialPoint_wsolFun_vsolFun V s hB hsdet η

/-! ## Steps 3-5 (cont). Joint strict derivative, the equiv, and the unconditional theorem

Building on the gate-direction derivatives above, we now establish the *joint* strict
derivative of the augmented map `augΦ` in all of `(s, η, u)`.  Each ingredient
(`wsolFun`, `vsolFun`, `gFun`, `Ffun`) is a composition of continuous-(bi)linear maps and
`Ring.inverse`, so it is strictly differentiable; we record only that the joint derivatives
*exist* (their closed forms are not needed).  The scalar `s`-direction value is pinned to
`- texSweepVartheta0` by uniqueness against `hasStrictDerivAt_Ffun_anchor`.  The augmented
Jacobian then has the block form `(F', π_η, π_u)`, which is invertible exactly when
`texSweepVartheta0 ≠ 0`; we build the inverse `ContinuousLinearEquiv` explicitly and feed it
to `sweep_pointwise_realization_open_of_strictDeriv`. -/

abbrev Pdom (d : ℕ) := ℝ × ProbePoint d × ℝ

-- mulVec as CLM-valued CLM in matrix
noncomputable def mulVecBil :
    Matrix (Fin d) (Fin d) ℝ →L[ℝ] (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)
      map_add' := fun M N => by ext x; simp
      map_smul' := fun c M => by ext x; simp }
@[simp] theorem mulVecBil_apply (M : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    mulVecBil M x = M *ᵥ x := rfl

-- coordinate CLMs on Pdom
noncomputable def sCLM : Pdom d →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ProbePoint d × ℝ)
noncomputable def w1CLM : Pdom d →L[ℝ] (Fin d → ℝ) :=
  (ContinuousLinearMap.fst ℝ (Fin d → ℝ) (Fin d → ℝ)).comp
    ((ContinuousLinearMap.fst ℝ (ProbePoint d) ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ProbePoint d × ℝ)))
@[simp] theorem sCLM_apply (x : Pdom d) : sCLM x = x.1 := rfl
@[simp] theorem w1CLM_apply (x : Pdom d) : w1CLM x = x.2.1.1 := rfl

-- joint deriv of  x ↦ (Msolve V x.1)⁻¹
theorem hsfd_Minv_joint (V : Matrix (Fin d) (Fin d) ℝ) (a : Pdom d)
    (hMt : (Msolve V a.1).det ≠ 0) :
    HasStrictFDerivAt (fun x : Pdom d => (Msolve V x.1)⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((Msolve V a.1)⁻¹ * V * (Msolve V a.1)⁻¹)).comp sCLM) a := by
  have hsd : HasStrictDerivAt (fun σ : ℝ => (Msolve V σ)⁻¹)
      ((Msolve V a.1)⁻¹ * V * (Msolve V a.1)⁻¹) a.1 := hasStrictDerivAt_Minv V a.1 hMt
  exact hsd.hasStrictFDerivAt.comp a sCLM.hasStrictFDerivAt

-- joint deriv of c x = mulVecBil ((Msolve V x.1)⁻¹)
theorem hsfd_c_joint (V : Matrix (Fin d) (Fin d) ℝ) (a : Pdom d)
    (hMt : (Msolve V a.1).det ≠ 0) :
    HasStrictFDerivAt (fun x : Pdom d => mulVecBil ((Msolve V x.1)⁻¹))
      (mulVecBil.comp ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        ((Msolve V a.1)⁻¹ * V * (Msolve V a.1)⁻¹)).comp sCLM)) a :=
  mulVecBil.hasStrictFDerivAt.comp a (hsfd_Minv_joint V a hMt)

-- joint deriv of wsol:  x ↦ wsolFun V x.1 x.2.1  via clm_apply
theorem hsfd_wsol_joint (V : Matrix (Fin d) (Fin d) ℝ) (a : Pdom d)
    (hMt : (Msolve V a.1).det ≠ 0) :
    HasStrictFDerivAt (fun x : Pdom d => wsolFun V x.1 x.2.1)
      ((mulVecBil ((Msolve V a.1)⁻¹)).comp w1CLM +
        (mulVecBil.comp ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          ((Msolve V a.1)⁻¹ * V * (Msolve V a.1)⁻¹)).comp sCLM)).flip (a.2.1.1)) a := by
  have hu : HasStrictFDerivAt (fun x : Pdom d => x.2.1.1) w1CLM a := w1CLM.hasStrictFDerivAt
  have hfun : (fun x : Pdom d => wsolFun V x.1 x.2.1) =
      (fun x : Pdom d => (mulVecBil ((Msolve V x.1)⁻¹)) (x.2.1.1)) := by
    funext x; rw [mulVecBil_apply, wsolFun]
  rw [hfun]
  exact (hsfd_c_joint V a hMt).clm_apply hu

noncomputable def mulVecLeftCLM2 (M : Matrix (Fin d) (Fin d) ℝ) :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)
@[simp] theorem mulVecLeftCLM2_apply (M : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    mulVecLeftCLM2 M x = M *ᵥ x := rfl
noncomputable def w2CLM : Pdom d →L[ℝ] (Fin d → ℝ) :=
  (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin d → ℝ)).comp
    ((ContinuousLinearMap.fst ℝ (ProbePoint d) ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ProbePoint d × ℝ)))
@[simp] theorem w2CLM_apply (x : Pdom d) : w2CLM x = x.2.1.2 := rfl

-- existence-only joint deriv of vsol
theorem hsfd_vsol_joint (V : Matrix (Fin d) (Fin d) ℝ) (a : Pdom d)
    (hMt : (Msolve V a.1).det ≠ 0) :
    ∃ vsol' : Pdom d →L[ℝ] (Fin d → ℝ),
      HasStrictFDerivAt (fun x : Pdom d => vsolFun V x.1 x.2.1) vsol' a := by
  have hVwsol := (mulVecLeftCLM2 V).hasStrictFDerivAt.comp a (hsfd_wsol_joint V a hMt)
  have hs : HasStrictFDerivAt (fun x : Pdom d => x.1) sCLM a := sCLM.hasStrictFDerivAt
  have hsmul := hs.smul hVwsol
  have hη2 : HasStrictFDerivAt (fun x : Pdom d => x.2.1.2) w2CLM a := w2CLM.hasStrictFDerivAt
  have hinner := hη2.sub hsmul
  have hfin := (mulVecLeftCLM2 ((skipB V)⁻¹)).hasStrictFDerivAt.comp a hinner
  have hfun : (fun x : Pdom d => vsolFun V x.1 x.2.1) =
      (fun x : Pdom d => mulVecLeftCLM2 ((skipB V)⁻¹) (x.2.1.2 - x.1 • (V *ᵥ wsolFun V x.1 x.2.1))) := by
    funext x; rw [mulVecLeftCLM2_apply, vsolFun]
  exact ⟨_, hfun ▸ hfin⟩

-- existence-only joint deriv of gFun
theorem hsfd_gFun_joint (V A : Matrix (Fin d) (Fin d) ℝ) (a : Pdom d)
    (hMt : (Msolve V a.1).det ≠ 0) :
    ∃ g' : Pdom d →L[ℝ] ℝ, HasStrictFDerivAt (fun x : Pdom d => gFun V A x.1 x.2.1) g' a := by
  obtain ⟨vsol', hvsol'⟩ := hsfd_vsol_joint V a hMt
  -- A *ᵥ vsol  joint
  have hAv := (mulVecLeftCLM2 A).hasStrictFDerivAt.comp a hvsol'
  -- c x := dotRightCLM' (A *ᵥ vsol x)
  have hc := dotRightCLM'.hasStrictFDerivAt.comp a hAv
  -- u x := wsol x
  have hwsol := hsfd_wsol_joint V a hMt
  have hmain := hc.clm_apply hwsol
  have hfun : (fun x : Pdom d => gFun V A x.1 x.2.1) =
      (fun x : Pdom d => (dotRightCLM' (A *ᵥ vsolFun V x.1 x.2.1)) (wsolFun V x.1 x.2.1)) := by
    funext x; rw [dotRightCLM'_apply, gFun, matrixBilin]
  exact ⟨_, hfun ▸ hmain⟩

-- sigmoidLogit differentiable on (0,1)
theorem hsd_sigmoidLogit {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasStrictDerivAt sigmoidLogit ((t * (1 - t))⁻¹) t := by
  have hne : t / (1 - t) ≠ 0 := by
    apply div_ne_zero (ne_of_gt ht0); linarith
  have h1mt : (1 - t) ≠ 0 := by linarith
  -- sigmoidLogit s = log (s/(1-s))
  have : HasStrictDerivAt (fun s : ℝ => Real.log (s / (1 - s)))
      ((t * (1 - t))⁻¹) t := by
    have hdiv : HasStrictDerivAt (fun s : ℝ => s / (1 - s))
        ((1 * (1 - t) - t * (-1)) / (1 - t)^2) t := by
      have hnum : HasStrictDerivAt (fun s : ℝ => s) 1 t := hasStrictDerivAt_id t
      have hden : HasStrictDerivAt (fun s : ℝ => 1 - s) (-1) t := by
        simpa using (hasStrictDerivAt_const t (1:ℝ)).sub (hasStrictDerivAt_id t)
      exact hnum.div hden h1mt
    have hlog := (Real.hasStrictDerivAt_log hne).comp t hdiv
    refine hlog.congr_deriv ?_
    field_simp
    ring
  exact this

noncomputable def u2CLM : Pdom d →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (ProbePoint d) ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ProbePoint d × ℝ))
@[simp] theorem u2CLM_apply (x : Pdom d) : u2CLM x = x.2.2 := rfl

theorem hsfd_Ffun_joint (r : ℕ) (V A : Matrix (Fin d) (Fin d) ℝ) (a : Pdom d)
    (ht0 : 0 < a.1) (ht1 : a.1 < 1) (hMt : (Msolve V a.1).det ≠ 0) :
    ∃ F' : Pdom d →L[ℝ] ℝ,
      HasStrictFDerivAt (fun x : Pdom d => Ffun r V A x.1 x.2.1 x.2.2) F' a := by
  obtain ⟨g', hg'⟩ := hsfd_gFun_joint V A a hMt
  -- sigmoidLogit x.1  joint
  have hsig := (hsd_sigmoidLogit ht0 ht1).hasStrictFDerivAt.comp a sCLM.hasStrictFDerivAt
  -- sigmoidLogit x.1 - log r
  have hsub := hsig.sub_const (Real.log r)
  -- u2CLM x = x.2.2
  have hu2 : HasStrictFDerivAt (fun x : Pdom d => x.2.2) u2CLM a := u2CLM.hasStrictFDerivAt
  -- (sigmoidLogit x.1 - log r) * x.2.2
  have hmul := hsub.mul hu2
  -- Ffun = gFun - that
  have hFfun := hg'.sub hmul
  refine ⟨_, hFfun.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)⟩
  rfl

-- the s-direction basis vector in Pdom
-- F'(1,0,0) = ∂_s Ffun = -ϑ₀
theorem Ffun_joint_deriv_sdir (r : ℕ) (V A : Matrix (Fin d) (Fin d) ℝ)
    (t : ℝ) (w0 v0 : Fin d → ℝ)
    (hB : (skipB V).det ≠ 0) (hMt : (Msolve V t).det ≠ 0)
    (F' : Pdom d →L[ℝ] ℝ)
    (hF' : HasStrictFDerivAt (fun x : Pdom d => Ffun r V A x.1 x.2.1 x.2.2) F'
      (t, firstLayerDialPoint V t w0 v0, 0)) :
    F' (1, 0, 0) = - texSweepVartheta0 V A (w0, v0) t := by
  set p := firstLayerDialPoint V t w0 v0 with hp
  -- embedding e s := (s, p, 0)
  have he : HasStrictDerivAt (fun s : ℝ => ((s, p, 0) : Pdom d)) (1, 0, 0) t := by
    have h1 : HasStrictFDerivAt (fun s : ℝ => s)
      (ContinuousLinearMap.id ℝ ℝ) t := hasStrictFDerivAt_id t
    have h2 : HasStrictFDerivAt (fun _ : ℝ => p) (0 : ℝ →L[ℝ] ProbePoint d) t :=
      hasStrictFDerivAt_const p t
    have h3 : HasStrictFDerivAt (fun _ : ℝ => (0:ℝ)) (0 : ℝ →L[ℝ] ℝ) t :=
      hasStrictFDerivAt_const 0 t
    have hp := h1.prodMk (h2.prodMk h3)
    rw [hasStrictDerivAt_iff_hasStrictFDerivAt]
    convert hp using 1
    ext s <;> simp
  -- composition derivative
  have hcomp : HasStrictDerivAt (fun s : ℝ => Ffun r V A s p 0) (F' (1, 0, 0)) t := by
    have := hF'.comp_hasStrictDerivAt t he
    exact this
  -- uniqueness against the scalar lemma
  have hscalar : HasStrictDerivAt (fun s : ℝ => Ffun r V A s p 0)
      (- texSweepVartheta0 V A (w0, v0) t) t := hasStrictDerivAt_Ffun_anchor r V A t w0 v0 hB hMt
  exact hcomp.hasDerivAt.unique hscalar.hasDerivAt


/-! ## Step 4 derivative + equiv assembly (toward the unconditional theorem) -/

-- augΦ joint derivative
noncomputable def augΦ' (F' : Pdom d →L[ℝ] ℝ) : Pdom d →L[ℝ] Pdom d :=
  F'.prod (((ContinuousLinearMap.fst ℝ (ProbePoint d) ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ProbePoint d × ℝ))).prod
    ((ContinuousLinearMap.snd ℝ (ProbePoint d) ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ProbePoint d × ℝ))))
@[simp] theorem augΦ'_apply (F' : Pdom d →L[ℝ] ℝ) (z : Pdom d) :
    augΦ' F' z = (F' z, z.2.1, z.2.2) := rfl


theorem hsfd_augΦ (r : ℕ) (V A : Matrix (Fin d) (Fin d) ℝ) (a : Pdom d)
    (ht0 : 0 < a.1) (ht1 : a.1 < 1) (hMt : (Msolve V a.1).det ≠ 0) :
    ∃ F' : Pdom d →L[ℝ] ℝ, HasStrictFDerivAt (augΦ r V A) (augΦ' F') a ∧
      HasStrictFDerivAt (fun x : Pdom d => Ffun r V A x.1 x.2.1 x.2.2) F' a := by
  obtain ⟨F', hF'⟩ := hsfd_Ffun_joint r V A a ht0 ht1 hMt
  refine ⟨F', ?_, hF'⟩
  have hπ1 : HasStrictFDerivAt (fun x : Pdom d => x.2.1)
      ((ContinuousLinearMap.fst ℝ (ProbePoint d) ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ProbePoint d × ℝ))) a :=
    ((ContinuousLinearMap.fst ℝ (ProbePoint d) ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ProbePoint d × ℝ))).hasStrictFDerivAt
  have hπ2 : HasStrictFDerivAt (fun x : Pdom d => x.2.2)
      ((ContinuousLinearMap.snd ℝ (ProbePoint d) ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ProbePoint d × ℝ))) a :=
    ((ContinuousLinearMap.snd ℝ (ProbePoint d) ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ProbePoint d × ℝ))).hasStrictFDerivAt
  exact hF'.prodMk (hπ1.prodMk hπ2)


-- zero-out-first-coordinate CLM:  z ↦ (0, z.2.1, z.2.2)
noncomputable def zeroFirstCLM : Pdom d →L[ℝ] Pdom d :=
  (0 : Pdom d →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ (ProbePoint d × ℝ))
@[simp] theorem zeroFirstCLM_apply (z : Pdom d) : zeroFirstCLM z = (0, z.2.1, z.2.2) := rfl

-- the inverse CLM Ψ'
noncomputable def augΨ' (F' : Pdom d →L[ℝ] ℝ) (c : ℝ) : Pdom d →L[ℝ] Pdom d :=
  (c⁻¹ • ((ContinuousLinearMap.fst ℝ ℝ (ProbePoint d × ℝ)) - F'.comp zeroFirstCLM)).prod
    (ContinuousLinearMap.snd ℝ ℝ (ProbePoint d × ℝ))
@[simp] theorem augΨ'_apply (F' : Pdom d →L[ℝ] ℝ) (c : ℝ) (z : Pdom d) :
    augΨ' F' c z = (c⁻¹ * (z.1 - F' (0, z.2.1, z.2.2)), z.2.1, z.2.2) := rfl


-- F' decomposes:  F' z = z.1 * F'(1,0,0) + F'(0, z.2.1, z.2.2)
theorem F'_decomp (F' : Pdom d →L[ℝ] ℝ) (z : Pdom d) :
    F' z = z.1 * F' (1, 0, 0) + F' (0, z.2.1, z.2.2) := by
  have hsplit : F' z = F' (((z.1 : ℝ) • ((1, 0, 0) : Pdom d)) + (0, z.2.1, z.2.2)) := by
    congr 1; ext <;> simp
  rw [hsplit, map_add, map_smul, smul_eq_mul]

-- the equiv from c ≠ 0
noncomputable def augEquiv (F' : Pdom d →L[ℝ] ℝ) (hc : F' (1, 0, 0) ≠ 0) :
    Pdom d ≃L[ℝ] Pdom d :=
  ContinuousLinearEquiv.equivOfInverse (augΦ' F') (augΨ' F' (F' (1, 0, 0)))
    (by
      intro z
      rw [augΨ'_apply, augΦ'_apply]
      have hd := F'_decomp F' z
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · show (F' (1,0,0))⁻¹ * ((augΦ' F' z).1 - F' (0, (augΦ' F' z).2.1, (augΦ' F' z).2.2)) = z.1
        simp only [augΦ'_apply]
        rw [hd]; field_simp; ring
      · rfl
      · rfl)
    (by
      intro z
      rw [augΦ'_apply, augΨ'_apply]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · show F' ((F' (1,0,0))⁻¹ * (z.1 - F' (0, z.2.1, z.2.2)), z.2.1, z.2.2) = z.1
        rw [F'_decomp F' ((F' (1,0,0))⁻¹ * (z.1 - F' (0, z.2.1, z.2.2)), z.2.1, z.2.2)]
        simp only []
        field_simp; ring
      · rfl
      · rfl)
@[simp] theorem augEquiv_coe (F' : Pdom d →L[ℝ] ℝ) (hc : F' (1, 0, 0) ≠ 0) :
    (↑(augEquiv F' hc) : Pdom d →L[ℝ] Pdom d) = augΦ' F' := rfl


/-- **PRIMARY: the unconditional pointwise realization theorem.**
Steps 1-5 of `SWEEP_PLAN.md`, fully discharged.  From the anchor data and the nonzero
Jacobian scalar `texSweepVartheta0 ≠ 0`, every probe point near `firstLayerDialPoint V t w0 v0`
is realized as a first-layer effective point for all large `τ`. -/
theorem sweep_pointwise_realization_open (r : ℕ)
    (V A : Matrix (Fin d) (Fin d) ℝ) (w0 v0 : Fin d → ℝ) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hB : (skipB V).det ≠ 0)
    (hMt : (Msolve V t).det ≠ 0)
    (hq : matrixBilin A w0 v0 = 0)
    (hϑ : texSweepVartheta0 V A (w0, v0) t ≠ 0) :
    ∃ U : Set (ProbePoint d), IsOpen U ∧ firstLayerDialPoint V t w0 v0 ∈ U ∧
      ∃ T : ℝ, 0 ≤ T ∧ ∀ η ∈ U, ∀ τ : ℝ, T < τ →
        ∃ w v : Fin d → ℝ, firstLayerEffectivePoint r V A w v τ = η := by
  obtain ⟨F', hΦ', hF'⟩ := hsfd_augΦ r V A (t, firstLayerDialPoint V t w0 v0, 0) ht0 ht1 hMt
  have hc : F' (1, 0, 0) = - texSweepVartheta0 V A (w0, v0) t :=
    Ffun_joint_deriv_sdir r V A t w0 v0 hB hMt F' hF'
  have hcne : F' (1, 0, 0) ≠ 0 := by rw [hc]; exact neg_ne_zero.mpr hϑ
  have hΦeq : HasStrictFDerivAt (augΦ r V A)
      (↑(augEquiv F' hcne) : Pdom d →L[ℝ] Pdom d)
      (t, firstLayerDialPoint V t w0 v0, 0) := by
    rw [augEquiv_coe]; exact hΦ'
  exact sweep_pointwise_realization_open_of_strictDeriv r V A w0 v0 t ht0 ht1 hB hMt hq
    (augEquiv F' hcne) hΦeq

/-! ## Source control (TeX "persistence", `N ⊆ {(w,v) ∈ 𝒪}`)

For the recursive sweep, the realization sources `(w, v)` for targets near the dial center
must be confined to a prescribed neighborhood of the anchor source `(w0, v0)` — this is the
persistence clause `N ⊆ {(w,v) ∈ 𝒪}` of TeX Lemma `sweep`.  Because the realization sources
are the explicit, continuous formulas `(wsolFun V s η, vsolFun V s η)` with `s` the local
inverse gate (continuous in the target, `→ t` at the anchor), they converge to `(w0, v0)` as
the target approaches the center and `τ → ∞`; hence they can be confined to any neighborhood
of `(w0, v0)`. -/

/-- Joint continuity of the explicit realization source pair `(wsolFun, vsolFun)` in the
gate–target argument `(s, η)` at the anchor gate `t` (where `Msolve V t` is invertible). -/
theorem continuousAt_wsolFun_vsolFun
    (V : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (p : ProbePoint d)
    (hMt : (Msolve V t).det ≠ 0) :
    ContinuousAt
      (fun q : ℝ × ProbePoint d => (wsolFun V q.1 q.2, vsolFun V q.1 q.2)) (t, p) := by
  have hmulVec : Continuous
      (fun u : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) => u.1 *ᵥ u.2) :=
    Continuous.matrix_mulVec continuous_fst continuous_snd
  have hMinv : ContinuousAt (fun s : ℝ => (Msolve V s)⁻¹) t :=
    (hasStrictDerivAt_Minv V t hMt).hasDerivAt.continuousAt
  have hMinv' : ContinuousAt (fun q : ℝ × ProbePoint d => (Msolve V q.1)⁻¹) (t, p) := by
    change ContinuousAt ((fun s : ℝ => (Msolve V s)⁻¹) ∘ Prod.fst) (t, p)
    exact hMinv.comp continuousAt_fst
  have hη1 : ContinuousAt (fun q : ℝ × ProbePoint d => q.2.1) (t, p) :=
    (continuous_fst.comp continuous_snd).continuousAt
  have hη2 : ContinuousAt (fun q : ℝ × ProbePoint d => q.2.2) (t, p) :=
    (continuous_snd.comp continuous_snd).continuousAt
  have hw : ContinuousAt (fun q : ℝ × ProbePoint d => wsolFun V q.1 q.2) (t, p) :=
    hmulVec.continuousAt.comp (hMinv'.prodMk hη1)
  have hVw : ContinuousAt (fun q : ℝ × ProbePoint d => V *ᵥ wsolFun V q.1 q.2) (t, p) :=
    hmulVec.continuousAt.comp ((continuousAt_const (y := V)).prodMk hw)
  have hv : ContinuousAt (fun q : ℝ × ProbePoint d => vsolFun V q.1 q.2) (t, p) := by
    have harg : ContinuousAt
        (fun q : ℝ × ProbePoint d => q.2.2 - q.1 • (V *ᵥ wsolFun V q.1 q.2)) (t, p) :=
      hη2.sub (continuousAt_fst.smul hVw)
    exact hmulVec.continuousAt.comp ((continuousAt_const (y := (skipB V)⁻¹)).prodMk harg)
  exact hw.prodMk hv

/-- **Source-controlled realization (TeX persistence).**  Same conclusion as
`sweep_pointwise_realization_open`, but the realizing source `(w, v)` is confined to any
prescribed neighborhood `N` of the anchor source `(w0, v0)`. -/
theorem sweep_pointwise_realization_open_controlled (r : ℕ)
    (V A : Matrix (Fin d) (Fin d) ℝ) (w0 v0 : Fin d → ℝ) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hB : (skipB V).det ≠ 0)
    (hMt : (Msolve V t).det ≠ 0)
    (hq : matrixBilin A w0 v0 = 0)
    (hϑ : texSweepVartheta0 V A (w0, v0) t ≠ 0)
    (N : Set (ProbePoint d)) (hN : N ∈ nhds (w0, v0)) :
    ∃ U : Set (ProbePoint d), IsOpen U ∧ firstLayerDialPoint V t w0 v0 ∈ U ∧
      ∃ T : ℝ, 0 ≤ T ∧ ∀ η ∈ U, ∀ τ : ℝ, T < τ →
        ∃ w v : Fin d → ℝ, (w, v) ∈ N ∧
          firstLayerEffectivePoint r V A w v τ = η := by
  obtain ⟨F', hΦ', hF'⟩ := hsfd_augΦ r V A (t, firstLayerDialPoint V t w0 v0, 0) ht0 ht1 hMt
  have hc : F' (1, 0, 0) = - texSweepVartheta0 V A (w0, v0) t :=
    Ffun_joint_deriv_sdir r V A t w0 v0 hB hMt F' hF'
  have hcne : F' (1, 0, 0) ≠ 0 := by rw [hc]; exact neg_ne_zero.mpr hϑ
  have hΦeq : HasStrictFDerivAt (augΦ r V A)
      (↑(augEquiv F' hcne) : Pdom d →L[ℝ] Pdom d)
      (t, firstLayerDialPoint V t w0 v0, 0) := by
    rw [augEquiv_coe]; exact hΦ'
  -- Re-run the inverse-function construction, additionally confining the source to `N`.
  set E := augEquiv F' hcne with hE
  set p := firstLayerDialPoint V t w0 v0 with hp
  set a : ℝ × ProbePoint d × ℝ := (t, p, 0) with ha
  have hΦa : augΦ r V A a = (0, p, 0) := by
    have hF : Ffun r V A t p 0 = 0 := Ffun_anchor r V A t w0 v0 hB hMt hq
    simp only [augΦ_apply, ha]; rw [hF]
  set inv := hΦeq.localInverse (augΦ r V A) E a with hinv_def
  have hval : inv (augΦ r V A a) = a := hΦeq.localInverse_apply_image
  have hcont : ContinuousAt inv (augΦ r V A a) := hΦeq.to_localInverse.continuousAt
  have hright : ∀ᶠ y in nhds (augΦ r V A a), augΦ r V A (inv y) = y :=
    hΦeq.eventually_right_inverse
  have hScont : ∀ᶠ y in nhds (augΦ r V A a),
      0 < (inv y).1 ∧ (inv y).1 < 1 ∧ (Msolve V (inv y).1).det ≠ 0 := by
    have hSt : {x : ℝ | 0 < x ∧ x < 1 ∧ (Msolve V x).det ≠ 0} ∈ nhds t := by
      filter_upwards [Ioo_mem_nhds ht0 ht1, eventually_Msolve_det_ne V t hMt]
        with x hx hx2 using ⟨hx.1, hx.2, hx2⟩
    have hqcont : ContinuousAt (fun y => (inv y).1) (augΦ r V A a) :=
      (continuous_fst.continuousAt).comp hcont
    have hmem : {x : ℝ | 0 < x ∧ x < 1 ∧ (Msolve V x).det ≠ 0} ∈
        nhds ((inv (augΦ r V A a)).1) := by
      rw [hval, ha]; exact hSt
    have := hqcont.preimage_mem_nhds hmem
    filter_upwards [this] with y hy using hy
  -- The source-control eventual condition: the explicit source lies in `N` near the anchor.
  have hSrcN : ∀ᶠ y in nhds (augΦ r V A a),
      (wsolFun V (inv y).1 (inv y).2.1, vsolFun V (inv y).1 (inv y).2.1) ∈ N := by
    have hsp := continuousAt_wsolFun_vsolFun V t p hMt
    have hinv_s : ContinuousAt (fun y => (inv y).1) (augΦ r V A a) :=
      (continuous_fst.continuousAt).comp hcont
    have hinv_e : ContinuousAt (fun y => (inv y).2.1) (augΦ r V A a) :=
      ((continuous_fst.comp continuous_snd).continuousAt).comp hcont
    have hpair : ContinuousAt (fun y => ((inv y).1, (inv y).2.1)) (augΦ r V A a) :=
      hinv_s.prodMk hinv_e
    have hval1 : (inv (augΦ r V A a)).1 = t := by rw [hval, ha]
    have hval2 : (inv (augΦ r V A a)).2.1 = p := by rw [hval, ha]
    have hsp' : ContinuousAt (fun q : ℝ × ProbePoint d => (wsolFun V q.1 q.2, vsolFun V q.1 q.2))
        ((inv (augΦ r V A a)).1, (inv (augΦ r V A a)).2.1) := by
      rw [show ((inv (augΦ r V A a)).1, (inv (augΦ r V A a)).2.1) = (t, p) from
        Prod.ext hval1 hval2]
      exact hsp
    have hcompSrc :=
      ContinuousAt.comp (x := augΦ r V A a)
        (g := fun q : ℝ × ProbePoint d => (wsolFun V q.1 q.2, vsolFun V q.1 q.2))
        (f := fun y : ℝ × ProbePoint d × ℝ => ((inv y).1, (inv y).2.1))
        hsp' hpair
    have hbase : (wsolFun V (inv (augΦ r V A a)).1 (inv (augΦ r V A a)).2.1,
        vsolFun V (inv (augΦ r V A a)).1 (inv (augΦ r V A a)).2.1) = (w0, v0) := by
      rw [hval1, hval2, hp, wsolFun_anchor V t w0 v0 hMt, vsolFun_anchor V t w0 v0 hB hMt]
    have hNmem : N ∈ nhds ((wsolFun V (inv (augΦ r V A a)).1 (inv (augΦ r V A a)).2.1,
        vsolFun V (inv (augΦ r V A a)).1 (inv (augΦ r V A a)).2.1)) := by
      rw [hbase]; exact hN
    exact hcompSrc.preimage_mem_nhds hNmem
  have hcombo : ∀ᶠ y in nhds (augΦ r V A a),
      (augΦ r V A (inv y) = y ∧ 0 < (inv y).1 ∧ (inv y).1 < 1 ∧
        (Msolve V (inv y).1).det ≠ 0) ∧
      (wsolFun V (inv y).1 (inv y).2.1, vsolFun V (inv y).1 (inv y).2.1) ∈ N :=
    (hright.and hScont).and hSrcN
  rw [hΦa] at hcombo
  rw [Filter.eventually_iff, mem_nhds_iff] at hcombo
  obtain ⟨W, hWsub, hWopen, hWmem⟩ := hcombo
  have hWnhds : W ∈ nhds ((0 : ℝ), p, (0:ℝ)) := hWopen.mem_nhds hWmem
  rw [nhds_prod_eq, nhds_prod_eq] at hWnhds
  obtain ⟨A0, hA0, BC, hBC, hsub⟩ := Filter.mem_prod_iff.mp hWnhds
  obtain ⟨U0, hU0, C0, hC0, hsub2⟩ := Filter.mem_prod_iff.mp hBC
  obtain ⟨A', hA'sub, hA'open, h0A'⟩ := mem_nhds_iff.mp hA0
  obtain ⟨U', hU'sub, hU'open, hpU'⟩ := mem_nhds_iff.mp hU0
  obtain ⟨C', hC'sub, hC'open, h0C'⟩ := mem_nhds_iff.mp hC0
  obtain ⟨ε, hε, hIoo⟩ : ∃ ε > 0, Set.Ioo (-ε) ε ⊆ C' := by
    rw [Metric.isOpen_iff] at hC'open
    obtain ⟨ε, hε, hball⟩ := hC'open 0 h0C'
    exact ⟨ε, hε, fun x hx => hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact ⟨hx.1, hx.2⟩)⟩
  have hbox : A' ×ˢ U' ×ˢ C' ⊆ W := fun pt hpt =>
    hsub ⟨hA'sub hpt.1, hsub2 ⟨hU'sub hpt.2.1, hC'sub hpt.2.2⟩⟩
  refine ⟨U', hU'open, hpU', ε⁻¹, le_of_lt (inv_pos.mpr hε), ?_⟩
  intro η hηU τ hτ
  have hτpos : 0 < τ := lt_trans (inv_pos.mpr hε) hτ
  have hu_pos : 0 < τ⁻¹ := inv_pos.mpr hτpos
  have hu_lt : τ⁻¹ < ε := by rw [inv_lt_comm₀ hτpos hε]; exact hτ
  set y : ℝ × ProbePoint d × ℝ := (0, η, τ⁻¹) with hy
  have hyW : y ∈ W := hbox ⟨h0A', hηU, hIoo ⟨by linarith, hu_lt⟩⟩
  obtain ⟨⟨hΦeqy, hs0, hs1, hsdet⟩, hsrcN⟩ := hWsub hyW
  set s := (inv y).1 with hs
  have hcomp2 : (inv y).2.1 = η := by
    have := congrArg (fun z => z.2.1) hΦeqy; simpa [augΦ_apply, hy] using this
  have hcomp3 : (inv y).2.2 = τ⁻¹ := by
    have := congrArg (fun z => z.2.2) hΦeqy; simpa [augΦ_apply, hy] using this
  have hF0 : Ffun r V A s η τ⁻¹ = 0 := by
    have h1 := congrArg (fun z => z.1) hΦeqy
    simp only [augΦ_apply, hy] at h1
    rw [hcomp2, hcomp3] at h1; rw [hs]; exact h1
  set w := wsolFun V s η with hwdef
  set v := vsolFun V s η with hvdef
  have hg : matrixBilin A w v = (sigmoidLogit s - Real.log r) * τ⁻¹ := by
    have hzero : gFun V A s η - (sigmoidLogit s - Real.log r) * τ⁻¹ = 0 := hF0
    have hgF : gFun V A s η = matrixBilin A w v := by rw [gFun, hwdef, hvdef]
    rw [hgF] at hzero; linarith
  have hlogit : τ * matrixBilin A w v + Real.log r = sigmoidLogit s := by
    rw [hg, mul_comm (sigmoidLogit s - Real.log r) τ⁻¹, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hτpos), one_mul]; ring
  have hgate : firstLayerGate r A w v τ = s :=
    firstLayerGate_eq_of_logit r A s τ hs0 hs1 w v hlogit
  refine ⟨w, v, ?_, ?_⟩
  · -- `(w, v) ∈ N`: the source-control witness, after identifying `(inv y).2.1 = η`.
    have : (wsolFun V (inv y).1 (inv y).2.1, vsolFun V (inv y).1 (inv y).2.1) ∈ N := hsrcN
    rwa [hcomp2, ← hs, ← hwdef, ← hvdef] at this
  · rw [firstLayerEffectivePoint, hgate]
    exact firstLayerDialPoint_wsolFun_vsolFun V s hB hsdet η

/-! ## Cross-layer composition (TeX inductive-step (4): the recursive realized-tail step)

The recursive sweep node has path class `realizedTailPathSet r θfull FullPaths` rather than
`Set.univ`, so its realization sources must themselves be realizable through the *previous*
layer.  Source control makes this possible: the current-layer realization sources for targets
near the dial center can be confined to the previous layer's realization region, so they lift
one layer up.  The lemma below is the pointwise heart of that step — it composes a
source-controlled current-layer realization with a uniform previous-layer realization. -/

/-- **Cross-layer realized-tail dial inversion.**  Composing the source-controlled
realization at the current layer `(V, A)` with a uniform previous-layer realization on an
open region `Uprev` containing the current source anchor `(w0, v0)` yields, for every target
`η` near the current dial center, a source path `mid` that is (i) realized through the
previous layer `(Vfull, Afull)` and (ii) realizes `η` through the current layer.  This is the
formal Lean shape of TeX inductive-step (4): the curr-source path stays in `Uprev`, so it
lifts one layer up; chaining this is the all-depth recursion. -/
theorem realizedTail_dialInverse_of_controlled (r : ℕ)
    (V A Vfull Afull : Matrix (Fin d) (Fin d) ℝ) (w0 v0 : Fin d → ℝ) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hB : (skipB V).det ≠ 0) (hMt : (Msolve V t).det ≠ 0)
    (hq : matrixBilin A w0 v0 = 0)
    (hϑ : texSweepVartheta0 V A (w0, v0) t ≠ 0)
    (Uprev : Set (ProbePoint d)) (hUprev_open : IsOpen Uprev)
    (hanchor_mem : (w0, v0) ∈ Uprev)
    (Tprev : ℝ)
    (hprev : ∀ q ∈ Uprev, ∀ τ : ℝ, Tprev < τ →
      ∃ w' v' : Fin d → ℝ, firstLayerEffectivePoint r Vfull Afull w' v' τ = q) :
    ∃ U : Set (ProbePoint d), IsOpen U ∧ firstLayerDialPoint V t w0 v0 ∈ U ∧
      ∀ η ∈ U, ∃ mid : ProbePath d,
        (∃ src' : ProbePath d, ∃ T' : ℝ, 0 ≤ T' ∧ ∀ τ : ℝ, T' < τ →
          firstLayerEffectivePoint r Vfull Afull (src' τ).1 (src' τ).2 τ = mid τ) ∧
        (∃ T : ℝ, 0 ≤ T ∧ ∀ τ : ℝ, T < τ →
          firstLayerEffectivePoint r V A (mid τ).1 (mid τ).2 τ = η) := by
  classical
  obtain ⟨U, hUopen, hcenter, T0, hT0, hreal⟩ :=
    sweep_pointwise_realization_open_controlled r V A w0 v0 t ht0 ht1 hB hMt hq hϑ
      Uprev (hUprev_open.mem_nhds hanchor_mem)
  refine ⟨U, hUopen, hcenter, ?_⟩
  intro η hη
  have hpt : ∀ τ : ℝ, T0 < τ → ∃ pp : ProbePoint d,
      pp ∈ Uprev ∧ firstLayerEffectivePoint r V A pp.1 pp.2 τ = η := by
    intro τ hτ
    obtain ⟨w, v, hmem, heff⟩ := hreal η hη τ hτ
    exact ⟨(w, v), hmem, heff⟩
  set mid : ProbePath d := fun τ => if h : T0 < τ then (hpt τ h).choose else (0, 0) with hmid
  have hmid_mem : ∀ τ : ℝ, T0 < τ → mid τ ∈ Uprev := by
    intro τ hτ; simp only [hmid, dif_pos hτ]; exact (hpt τ hτ).choose_spec.1
  have hmid_eff : ∀ τ : ℝ, T0 < τ →
      firstLayerEffectivePoint r V A (mid τ).1 (mid τ).2 τ = η := by
    intro τ hτ; simp only [hmid, dif_pos hτ]; exact (hpt τ hτ).choose_spec.2
  refine ⟨mid, ?_, T0, hT0, hmid_eff⟩
  have hsrcpt : ∀ τ : ℝ, max T0 Tprev < τ → ∃ pp : ProbePoint d,
      firstLayerEffectivePoint r Vfull Afull pp.1 pp.2 τ = mid τ := by
    intro τ hτ
    have hτ0 : T0 < τ := lt_of_le_of_lt (le_max_left _ _) hτ
    have hτp : Tprev < τ := lt_of_le_of_lt (le_max_right _ _) hτ
    obtain ⟨w', v', heff'⟩ := hprev (mid τ) (hmid_mem τ hτ0) τ hτp
    exact ⟨(w', v'), heff'⟩
  refine ⟨fun τ => if h : max T0 Tprev < τ then (hsrcpt τ h).choose else (0, 0),
    max T0 Tprev, le_trans hT0 (le_max_left _ _), ?_⟩
  intro τ hτ
  simp only [dif_pos hτ]
  exact (hsrcpt τ hτ).choose_spec

/-- **The recursive realized-tail dial inversion (`FullPaths = univ`).**  At the first
recursive node — whose path class is `realizedTailPathSet r θfull Set.univ`, so the lifted
sources are free — the cross-layer composition assembles directly into the frontier
obligation `TexSweepUniformDialInverseData D U`.  The hypotheses are exactly: the current
node's sweep data at its anchor `(w0, v0, t)` (the same data the universal node extracts via
matching), and a uniform realization of the *previous* layer on an open region `Uprev` that
contains the current source anchor.  The lifted source path lands in
`realizedTailPathSet r θfull Set.univ` because its previous-layer realizer is unconstrained.

This is the realized-tail analogue of `texSweepUniformDialInverseData_of_realization`; closing
the deeper recursive nodes chains this with `Uprev` itself a realized-tail region. -/
theorem texSweepUniformDialInverseData_of_realizedTail_controlled
    {L Lfull d : ℕ} {r : ℕ} {θ θ' : Params (L + 1) d} {θfull : Params (Lfull + 1) d}
    (D : IDLData (L + 1) d r θ θ')
    (hPaths : D.Paths = realizedTailPathSet r θfull Set.univ)
    (w0 v0 : Fin d → ℝ) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hB : (skipB (Params.headValue θ)).det ≠ 0)
    (hMt : (Msolve (Params.headValue θ) t).det ≠ 0)
    (hq : matrixBilin (Params.headAttention θ) w0 v0 = 0)
    (hϑ : texSweepVartheta0 (Params.headValue θ) (Params.headAttention θ) (w0, v0) t ≠ 0)
    (Uprev : Set (ProbePoint d)) (hUprev_open : IsOpen Uprev)
    (hanchor_mem : (w0, v0) ∈ Uprev)
    (Tprev : ℝ)
    (hprev : ∀ q ∈ Uprev, ∀ τ : ℝ, Tprev < τ →
      ∃ w' v' : Fin d → ℝ,
        firstLayerEffectivePoint r (Params.headValue θfull) (Params.headAttention θfull)
          w' v' τ = q) :
    ∃ U : Set (ProbePoint d), IsOpen U ∧
      firstLayerDialPoint (Params.headValue θ) t w0 v0 ∈ U ∧
      TexSweepUniformDialInverseData D U := by
  obtain ⟨U, hUopen, hcenter, hcomp⟩ :=
    realizedTail_dialInverse_of_controlled r (Params.headValue θ) (Params.headAttention θ)
      (Params.headValue θfull) (Params.headAttention θfull) w0 v0 t ht0 ht1 hB hMt hq hϑ
      Uprev hUprev_open hanchor_mem Tprev hprev
  refine ⟨U, hUopen, hcenter, ?_⟩
  intro η hη
  obtain ⟨mid, ⟨src', T', hT', hsrc'⟩, T, hT, hmideff⟩ := hcomp η hη
  refine ⟨mid, ?_, T, hT, hmideff⟩
  rw [hPaths]
  exact ⟨src', Set.mem_univ _,
    ⟨{ threshold := T', threshold_nonneg := hT', effective_eq := hsrc' }⟩⟩

/-! ## Secondary: wiring toward `TexSweepCanonicalIFTData` at the top node

At the top node `D.Paths = Set.univ`, the realization conclusion of
`sweep_pointwise_realization_open` assembles (pointwise, by choice) into a
`TexSweepUniformDialInverseData D U`: each target `η ∈ U` gets a single source path
`source : ℝ → ProbePoint d` (automatically in `D.Paths = univ`) with
`firstLayerEffectivePoint r (headValue θ) (headAttention θ) (source τ) τ = η` for all `τ > T`.

Composing with `texSweepCanonicalIFTData_of_uniformDialInverseData` (`IDLSweep.lean`) then
yields `TexSweepCanonicalIFTData D`, *provided* one also supplies:
  * `IsOpen U` and `(texSweepAnchorPointData_of_IDLData D).point ∈ U` (the open neighborhood
    is produced by `sweep_pointwise_realization_open`; the membership requires identifying
    its base point `firstLayerDialPoint (headValue θ) t w0 v0` with the canonical anchor);
  * the anchor hypotheses `(skipB (headValue θ)).det ≠ 0`, `(Msolve (headValue θ) t).det ≠ 0`,
    `matrixBilin (headAttention θ) w0 v0 = 0`, and `texSweepVartheta0 … ≠ 0`, extracted from
    `texSweepAnchorPointData_of_IDLData D` / `AnchorUnwindingData`.
The latter extraction is repo-specific bookkeeping (the "canonical anchor vs. full anchor"
subtlety) and is deliberately out of scope here. -/

/-- **Pointwise-to-uniform wiring (top node).**  At `D.Paths = Set.univ`, the realization
conclusion (an open `U` on which every target is realized eventually-in-`τ` by *some*
`(w, v)`) assembles into `TexSweepUniformDialInverseData D U` via choice. -/
theorem texSweepUniformDialInverseData_of_realization
    {L : ℕ} {r : ℕ} {θ θ' : Params (L + 1) d} (D : IDLData (L + 1) d r θ θ')
    (hpaths : D.Paths = Set.univ) (U : Set (ProbePoint d))
    (hreal : ∀ η ∈ U, ∃ T : ℝ, 0 ≤ T ∧ ∀ τ : ℝ, T < τ →
      ∃ w v : Fin d → ℝ,
        firstLayerEffectivePoint r (Params.headValue θ) (Params.headAttention θ) w v τ = η) :
    TexSweepUniformDialInverseData D U := by
  classical
  intro η hη
  obtain ⟨T, hT, hTτ⟩ := hreal η hη
  have hTτ' : ∀ τ : ℝ, T < τ → ∃ p : ProbePoint d,
      firstLayerEffectivePoint r (Params.headValue θ) (Params.headAttention θ) p.1 p.2 τ = η := by
    intro τ hτ
    obtain ⟨w, v, hwv⟩ := hTτ τ hτ
    exact ⟨(w, v), hwv⟩
  refine ⟨fun τ => if h : T < τ then (hTτ' τ h).choose else (0, 0), ?_, T, hT, ?_⟩
  · rw [hpaths]; trivial
  · intro τ hτ
    simp only [hτ, dif_pos]
    exact (hTτ' τ hτ).choose_spec

/-! ## Depth induction: the path-level uniform tail realization invariant

The recursive sweep node has `D.Paths = realizedTailPathSet r θfull FullPaths` with
`FullPaths` itself a nested realized-tail class, so producing `canonicalIFT` there requires
the realizing source *path* to land in `FullPaths` — not merely to exist pointwise per `τ`.

The clean invariant that threads this through every depth is **path-level uniform
realization**: every probe path eventually confined to an open region `U` is realized
through `θ`'s matched first layer by a *single* source path lying in the path class, past a
uniform threshold.  Crucially this invariant is *preserved* by the source-controlled
current-layer realization (`sweep_pointwise_realization_open_controlled`): the current
realizer is confined to the previous region `U`, so the path-level previous invariant lifts
it one realized-tail layer up.  The earlier "the per-`τ` source is a diagonal, so it need
not lie in the class" obstacle dissolves, because the path-level quantifier covers *every*
path through `U`, diagonals included.  No holomorphy and no constant-source shortcut. -/

/-- **Path-level uniform tail realization on an open region.**  Every probe path `g`
eventually confined to `U` (for `τ > T`) is realized through `θ`'s matched first layer by a
source path `src ∈ Paths`, past a uniform threshold `T' ≥ T`. -/
def UniformTailRealize (r : ℕ) {L : ℕ} (θ : Params (L + 1) d)
    (Paths : Set (ProbePath d)) (U : Set (ProbePoint d)) (T : ℝ) : Prop :=
  ∀ g : ProbePath d, (∀ τ : ℝ, T < τ → g τ ∈ U) →
    ∃ src : ProbePath d, src ∈ Paths ∧ ∃ T' : ℝ, T ≤ T' ∧
      ∀ τ : ℝ, T' < τ →
        firstLayerEffectivePoint r (Params.headValue θ) (Params.headAttention θ)
          (src τ).1 (src τ).2 τ = g τ

/-- **Base case (`Paths = Set.univ`).**  A *uniform-threshold* per-`τ` pointwise realization
of `U` through the first layer yields the path-level invariant: the source is the per-`τ`
diagonal, which is unconstrained because the path class is `Set.univ`.  This is exactly the
output shape of `sweep_pointwise_realization_open` at the universal top node. -/
theorem uniformTailRealize_univ_of_pointwise (r : ℕ) {L : ℕ} (θ : Params (L + 1) d)
    (U : Set (ProbePoint d)) (T : ℝ)
    (hpt : ∀ q : ProbePoint d, q ∈ U → ∀ τ : ℝ, T < τ →
      ∃ w v : Fin d → ℝ,
        firstLayerEffectivePoint r (Params.headValue θ) (Params.headAttention θ) w v τ = q) :
    UniformTailRealize r θ Set.univ U T := by
  classical
  intro g hg
  have hpt' : ∀ τ : ℝ, T < τ → ∃ p : ProbePoint d,
      firstLayerEffectivePoint r (Params.headValue θ) (Params.headAttention θ) p.1 p.2 τ
        = g τ := by
    intro τ hτ
    obtain ⟨w, v, hwv⟩ := hpt (g τ) (hg τ hτ) τ hτ
    exact ⟨(w, v), hwv⟩
  refine ⟨fun τ => if h : T < τ then (hpt' τ h).choose else (0, 0), Set.mem_univ _,
    T, le_refl T, ?_⟩
  intro τ hτ
  simp only [hτ, dif_pos]
  exact (hpt' τ hτ).choose_spec

/-- **Preservation of the path-level invariant — the depth-induction step.**

Given the *previous-layer* path-level invariant on an open `Uprev` containing the current
source anchor `(w0, v0)`, together with the current node's sweep data at `(w0, v0, t)`,
produce an open neighborhood `U` of the current dial center on which the *current-layer*
path-level invariant holds with source class `realizedTailPathSet r θfull FullPaths` — i.e.
the realizing source lands one realized-tail layer deeper.

The engine is `sweep_pointwise_realization_open_controlled`, which confines the current
realizer to `Uprev`; the previous invariant `hprev` (a path-level statement) then realizes
that confined source path through `θfull`, certifying its membership in
`realizedTailPathSet r θfull FullPaths`.  Threshold gaps are filled with the anchor
`(w0, v0) ∈ Uprev`, so the lifted source path stays in `Uprev` for *all* `τ > Tprev`. -/
theorem uniformTailRealize_step (r : ℕ) {L Lfull : ℕ}
    (θ : Params (L + 1) d) (θfull : Params (Lfull + 1) d)
    (FullPaths : Set (ProbePath d))
    (w0 v0 : Fin d → ℝ) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hB : (skipB (Params.headValue θ)).det ≠ 0)
    (hMt : (Msolve (Params.headValue θ) t).det ≠ 0)
    (hq : matrixBilin (Params.headAttention θ) w0 v0 = 0)
    (hϑ : texSweepVartheta0 (Params.headValue θ) (Params.headAttention θ) (w0, v0) t ≠ 0)
    (Uprev : Set (ProbePoint d)) (hUprev_open : IsOpen Uprev)
    (hanchor_mem : (w0, v0) ∈ Uprev)
    (Tprev : ℝ)
    (hprev : UniformTailRealize r θfull FullPaths Uprev Tprev) :
    ∃ U : Set (ProbePoint d), IsOpen U ∧
      firstLayerDialPoint (Params.headValue θ) t w0 v0 ∈ U ∧
      ∃ Tcurr : ℝ, Tprev ≤ Tcurr ∧
        UniformTailRealize r θ (realizedTailPathSet r θfull FullPaths) U Tcurr := by
  classical
  obtain ⟨U, hUopen, hcenter, T0, _hT0, hreal⟩ :=
    sweep_pointwise_realization_open_controlled r (Params.headValue θ)
      (Params.headAttention θ) w0 v0 t ht0 ht1 hB hMt hq hϑ Uprev
      (hUprev_open.mem_nhds hanchor_mem)
  refine ⟨U, hUopen, hcenter, max T0 Tprev, le_max_right _ _, ?_⟩
  intro g hg
  -- For `τ > max T0 Tprev`, pick (by choice) a source point in `Uprev` realizing `g τ` at
  -- parameter `τ` through the current layer.
  have hsrcpt : ∀ τ : ℝ, max T0 Tprev < τ → ∃ pp : ProbePoint d,
      pp ∈ Uprev ∧
        firstLayerEffectivePoint r (Params.headValue θ) (Params.headAttention θ)
          pp.1 pp.2 τ = g τ := by
    intro τ hτ
    have hτU : g τ ∈ U := hg τ hτ
    have hτ0 : T0 < τ := lt_of_le_of_lt (le_max_left _ _) hτ
    obtain ⟨w, v, hmem, heff⟩ := hreal (g τ) hτU τ hτ0
    exact ⟨(w, v), hmem, heff⟩
  -- The lifted current source path: the chosen preimage past `max T0 Tprev`, the anchor on
  -- the threshold gap so it stays in `Uprev` down to `Tprev`.
  set src : ProbePath d :=
    fun τ => if h : max T0 Tprev < τ then (hsrcpt τ h).choose else (w0, v0) with hsrc
  have hsrc_mem : ∀ τ : ℝ, Tprev < τ → src τ ∈ Uprev := by
    intro τ _hτ
    by_cases h : max T0 Tprev < τ
    · simp only [hsrc, dif_pos h]; exact (hsrcpt τ h).choose_spec.1
    · simp only [hsrc, dif_neg h]; exact hanchor_mem
  have hsrc_eff : ∀ τ : ℝ, max T0 Tprev < τ →
      firstLayerEffectivePoint r (Params.headValue θ) (Params.headAttention θ)
        (src τ).1 (src τ).2 τ = g τ := by
    intro τ hτ; simp only [hsrc, dif_pos hτ]; exact (hsrcpt τ hτ).choose_spec.2
  -- `src` is eventually confined to `Uprev`, so the previous invariant realizes it through
  -- `θfull`, certifying `src ∈ realizedTailPathSet r θfull FullPaths`.
  obtain ⟨src2, hsrc2_mem, T2, _hT2, hsrc2_eff⟩ := hprev src hsrc_mem
  refine ⟨src, ?_, max (max T0 Tprev) T2, le_max_left _ _, ?_⟩
  · refine ⟨src2, hsrc2_mem, ⟨?_⟩⟩
    refine
      { threshold := max 0 T2
        threshold_nonneg := le_max_left _ _
        effective_eq := ?_ }
    intro τ hτ
    exact hsrc2_eff τ (lt_of_le_of_lt (le_max_right 0 T2) hτ)
  · intro τ hτ
    exact hsrc_eff τ (lt_of_le_of_lt (le_max_left _ _) hτ)

end TransformerIdentifiability.NLayer
