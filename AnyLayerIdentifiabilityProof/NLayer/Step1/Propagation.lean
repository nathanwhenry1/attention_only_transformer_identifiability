import AnyLayerIdentifiabilityProof.NLayer.Step1.AnalyticSupport
import AnyLayerIdentifiabilityProof.NLayer.Step1.TierSets

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Step 1 propagation

Owner shard for Claim B: propagation from tier `j` to tier `j+1` through the polynomial
decomposition and analytic level-set argument.
-/

/-! ## Local point-set and blow-up helpers -/

/-- A frequently-hit punctured neighborhood witnesses membership in the accumulation set. -/
theorem mem_acc_of_frequently_mem_punctured {A : Set ℂ} {τ : ℂ}
    (hA : ∃ᶠ z in puncturedNhds τ, z ∈ A) :
    τ ∈ acc A := by
  rw [acc, mem_derivedSet, accPt_iff_frequently_nhdsNE]
  simpa [puncturedNhds] using hA

/-- Blow-up is invariant under punctured-neighborhood eventual equality. -/
theorem BlowsUpAt.congr {F G : ℂ -> ℂ} {τ : ℂ}
    (hF : BlowsUpAt F τ)
    (hFG : F =ᶠ[puncturedNhds τ] G) :
    BlowsUpAt G τ := by
  rw [BlowsUpAt] at hF ⊢
  rw [Filter.tendsto_atTop] at hF ⊢
  intro M
  filter_upwards [hF M, hFG] with z hFz hFGz
  simpa [← hFGz] using hFz

/-- Local version of `frequently_mem_oddPiI_of_analyticAt_reciprocal`.

The open-mapping argument only uses the reciprocal identity on points sufficiently close
to the center in the punctured neighborhood, so a punctured-neighborhood eventual
identity is enough. -/
theorem frequently_mem_oddPiI_of_analyticAt_eventually_reciprocal
    {H R : ℂ -> ℂ} {τ : ℂ}
    (hR : AnalyticAt ℂ R τ)
    (hRτ : R τ = 0)
    (hRnonconst : ¬ ∀ᶠ z in nhds τ, R z = R τ)
    (hrecip : ∀ᶠ z in puncturedNhds τ, R z * H z = 1) :
    ∃ᶠ z in puncturedNhds τ, H z ∈ oddPiI := by
  classical
  have hmap : nhds 0 ≤ Filter.map R (nhds τ) := by
    simpa [hRτ] using hR.eventually_constant_or_nhds_le_map_nhds.resolve_left hRnonconst
  have hpre :
      ∀ n : Nat, ∃ k : Nat, ∃ z : ℂ,
        z ∈ Metric.ball τ (((n : ℝ) + 1)⁻¹)
          ∧ R z = (oddPiISeq k)⁻¹ := by
    intro n
    have hpos : 0 < (((n : ℝ) + 1)⁻¹) := by positivity
    have hball : Metric.ball τ (((n : ℝ) + 1)⁻¹) ∈ nhds τ :=
      Metric.ball_mem_nhds τ hpos
    have himage_nhds :
        R '' Metric.ball τ (((n : ℝ) + 1)⁻¹) ∈ nhds 0 :=
      hmap (Filter.image_mem_map hball)
    have hevent :
        ∀ᶠ k in Filter.atTop, (oddPiISeq k)⁻¹ ∈
          R '' Metric.ball τ (((n : ℝ) + 1)⁻¹) :=
      oddPiISeq_inv_tendsto_zero.eventually himage_nhds
    rcases hevent.exists with ⟨k, hk⟩
    rcases hk with ⟨z, hzball, hzR⟩
    exact ⟨k, z, hzball, hzR⟩
  choose k z hz using hpre
  have hz_ne : ∀ n, z n ≠ τ := by
    intro n hzt
    have hRz : R (z n) = (oddPiISeq (k n))⁻¹ := (hz n).2
    have htarget_ne : (oddPiISeq (k n))⁻¹ ≠ 0 := inv_ne_zero (oddPiISeq_ne_zero (k n))
    exact htarget_ne (by simpa [hzt, hRτ] using hRz.symm)
  have hz_tendsto_nhds : Filter.Tendsto z Filter.atTop (nhds τ) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hsmall :
        ∀ᶠ n : Nat in Filter.atTop, (((n : ℝ) + 1)⁻¹) < ε := by
      have htend :
          Filter.Tendsto (fun n : Nat => (1 : ℝ) / ((n : ℝ) + 1))
            Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have hmem : Set.Iio ε ∈ nhds (0 : ℝ) := Iio_mem_nhds hε
      simpa [one_div] using htend.eventually hmem
    filter_upwards [hsmall] with n hn
    have hzball := (hz n).1
    simpa [Metric.mem_ball, dist_comm] using hzball.trans hn
  have hz_eventually_ne : ∀ᶠ n in Filter.atTop, z n ∈ ({τ}ᶜ : Set ℂ) :=
    Filter.Eventually.of_forall fun n => hz_ne n
  have hz_tendsto : Filter.Tendsto z Filter.atTop (puncturedNhds τ) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within z hz_tendsto_nhds
      hz_eventually_ne
  have hrecip_seq : ∀ᶠ n in Filter.atTop, R (z n) * H (z n) = 1 :=
    hz_tendsto.eventually hrecip
  refine hz_tendsto.frequently ?_
  have hprop : ∀ᶠ n in Filter.atTop, H (z n) ∈ oddPiI := by
    filter_upwards [hrecip_seq] with n hmul
    have hRz : R (z n) = (oddPiISeq (k n))⁻¹ := (hz n).2
    have hHz : H (z n) = oddPiISeq (k n) := by
      rw [hRz] at hmul
      field_simp [oddPiISeq_ne_zero (k n)] at hmul
      exact hmul
    simpa [hHz] using oddPiISeq_mem (k n)
  exact hprop.frequently

/-! ## The last-gate polynomial path -/

/-- The polynomial `φ'_{j+1}` from the nested tail family, evaluated along the concrete
gate path.  The nested-family `TailPresentation` is the last-gate decomposition: previous
gates are the base coordinates and `s'_j` is the last variable. -/
noncomputable def tierPhiPath {m : Nat} (A : TierSystem m) (j : Nat) : ℂ -> ℂ :=
  fun τ => A.nestedFamily.evalStep (gatePrefix A.stratification (j + 1) τ)

/-- The concrete gate argument used by the Step 1 proof after isolating the last-gate
polynomial.  In the TeX notation this is `τ * φ'_{j+1}(τ) + b`, not just
`φ'_{j+1}(τ)`. -/
noncomputable def scaledTierPhiPath {m : Nat} (A : TierSystem m) (j : Nat) : ℂ -> ℂ :=
  fun τ => τ * tierPhiPath A j τ + (A.stratification.b : ℂ)

/-- The leading coefficient of the last-gate presentation along the tier path. -/
noncomputable def tierLeadingCoeffPath {m : Nat} (A : TierSystem m) (j : Nat) :
    ℂ -> ℂ :=
  fun τ => (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ)

/-- The lower-order tail of the last-gate presentation along the concrete tier path. -/
noncomputable def tierTailLowerSum {m : Nat} (A : TierSystem m) (j : Nat) :
    ℂ -> ℂ :=
  fun τ =>
    ∑ i : Fin (A.nestedFamily.step j).degree,
      (A.nestedFamily.step j).lower i (gatePrefix A.stratification j τ) *
        (A.stratification.s j τ) ^ (i : Nat)

@[simp]
theorem tierPhiPath_eq_tailPresentation {m : Nat} (A : TierSystem m) (j : Nat)
    (τ : ℂ) :
    tierPhiPath A j τ =
      (A.nestedFamily.step j).eval
        (gatePrefix A.stratification j τ) (A.stratification.s j τ) := by
  simp [tierPhiPath, NestedTailFamily.evalStep]

@[simp]
theorem tierLeadingCoeffPath_apply {m : Nat} (A : TierSystem m) (j : Nat) (τ : ℂ) :
    tierLeadingCoeffPath A j τ =
      (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ) :=
  rfl

@[simp]
theorem tierTailLowerSum_apply {m : Nat} (A : TierSystem m) (j : Nat) (τ : ℂ) :
    tierTailLowerSum A j τ =
      ∑ i : Fin (A.nestedFamily.step j).degree,
        (A.nestedFamily.step j).lower i (gatePrefix A.stratification j τ) *
          (A.stratification.s j τ) ^ (i : Nat) :=
  rfl

/-- The analytic denominator obtained after multiplying the scaled successor
preactivation by a local reciprocal `Y` of the current gate to the presentation degree.

If `Y z * s_j z = 1`, then
`Y z ^ degree * scaledTierPhiPath A j z = scaledTierPhiReciprocalDenom A j Y z`.
This is the normal-form denominator whose center value is `τ * lead(τ)` in the quadratic
zero-free case. -/
noncomputable def scaledTierPhiReciprocalDenom {m : Nat} (A : TierSystem m)
    (j : Nat) (Y : ℂ -> ℂ) : ℂ -> ℂ :=
  fun z =>
    z *
        (tierLeadingCoeffPath A j z +
          ∑ i : Fin (A.nestedFamily.step j).degree,
            (A.nestedFamily.step j).lower i (gatePrefix A.stratification j z) *
              Y z ^ ((A.nestedFamily.step j).degree - (i : Nat))) +
      (A.stratification.b : ℂ) * Y z ^ (A.nestedFamily.step j).degree

/-- The reciprocal candidate for the scaled successor preactivation from a local
reciprocal `Y` of the current gate. -/
noncomputable def scaledTierPhiReciprocal {m : Nat} (A : TierSystem m)
    (j : Nat) (Y : ℂ -> ℂ) : ℂ -> ℂ :=
  fun z =>
    Y z ^ (A.nestedFamily.step j).degree /
      scaledTierPhiReciprocalDenom A j Y z

/-- Multiplication by the tier parameter, followed by the fixed output bias, preserves
blow-up at nonzero tier points. -/
theorem scaledTierPhiPath_blowsUpAt_of_phi {m : Nat} (A : TierSystem m)
    {j : Nat} {τ : ℂ} (hτ0 : τ ≠ 0)
    (hphi : BlowsUpAt (tierPhiPath A j) τ) :
    BlowsUpAt (scaledTierPhiPath A j) τ := by
  have hId : Filter.Tendsto (fun z : ℂ => z) (puncturedNhds τ) (nhds τ) :=
    (continuous_id.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hmul : BlowsUpAt (fun z => z * tierPhiPath A j z) τ :=
    hphi.tendsto_ne_zero_mul hId hτ0
  simpa [scaledTierPhiPath] using
    hmul.add_puncturedBounded (PuncturedBoundedAt.const (A.stratification.b : ℂ) τ)

/-! ## Continuity and coefficient limits -/

/-- Coordinatewise gate continuity gives continuity of the finite gate-prefix map. -/
theorem continuousAt_gatePrefix {m j : Nat} (P : ConcreteStratification m) {τ : ℂ}
    (hs : ∀ i : Fin j, ContinuousAt (P.s i) τ) :
    ContinuousAt (fun z => gatePrefix P j z) τ := by
  unfold gatePrefix
  fun_prop

/-- The leading coefficient path tends to its center value when the concrete gate prefix
and the leading evaluator are continuous at the relevant points. -/
theorem tierLeadingCoeffPath_tendsto_of_continuousAt {m : Nat} (A : TierSystem m)
    {j : Nat} {τ : ℂ}
    (hprefix : ContinuousAt (fun z => gatePrefix A.stratification j z) τ)
    (hlead : ContinuousAt (A.nestedFamily.step j).lead
      (gatePrefix A.stratification j τ)) :
    Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
      (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ))) := by
  simpa [tierLeadingCoeffPath, Function.comp_def] using
    (hlead.comp hprefix).tendsto.mono_left nhdsWithin_le_nhds

/-- Leading-coefficient tendsto transported through packaged polynomial-tail data. -/
theorem tierLeadingCoeffPath_tendsto_of_polynomialTailData_continuousAt {m : Nat}
    (A : TierSystem m) {j : Nat} {τ : ℂ}
    (D : PolynomialTailPresentationData j)
    (hstep : A.nestedFamily.step j = D.presentation)
    (hprefix : ContinuousAt (fun z => gatePrefix A.stratification j z) τ)
    (hlead : ContinuousAt D.presentation.lead (gatePrefix A.stratification j τ)) :
    Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
      (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ))) := by
  exact tierLeadingCoeffPath_tendsto_of_continuousAt A hprefix (by
    simpa [hstep] using hlead)

/-! ## Polynomial-tail bridge helpers -/

/-- If the `j`-th nested-family step is supplied by packaged polynomial-tail data, then
the tier path is evaluation of the packaged polynomial on the concrete gate prefix. -/
theorem tierPhiPath_eq_polynomialTailData_eval {m : Nat} (A : TierSystem m)
    {j : Nat} (D : PolynomialTailPresentationData j)
    (hstep : A.nestedFamily.step j = D.presentation) (τ : ℂ) :
    tierPhiPath A j τ =
      MvPolynomial.eval (gatePrefix A.stratification (j + 1) τ) D.poly := by
  calc
    tierPhiPath A j τ =
        D.presentation.eval (gatePrefix A.stratification j τ) (A.stratification.s j τ) := by
          simp [tierPhiPath, NestedTailFamily.evalStep, hstep]
    _ = MvPolynomial.eval (gatePrefix A.stratification (j + 1) τ) D.poly := by
          simpa using D.eval_eq (gatePrefix A.stratification (j + 1) τ)

/-- Convert concrete equality with a packaged polynomial evaluator into the
`PropagationData.polynomial_decomposition` shape. -/
theorem polynomial_decomposition_of_polynomialTailData {m : Nat} (A : TierSystem m)
    {j : Nat} {τ : ℂ} (D : PolynomialTailPresentationData j)
    (hstep : A.nestedFamily.step j = D.presentation)
    (hH :
      A.stratification.H (j + 1) =ᶠ[puncturedNhds τ]
        fun z => MvPolynomial.eval (gatePrefix A.stratification (j + 1) z) D.poly) :
    A.stratification.H (j + 1) =ᶠ[puncturedNhds τ] tierPhiPath A j :=
  hH.mono fun z hz => by
    rw [hz]
    exact (tierPhiPath_eq_polynomialTailData_eval A D hstep z).symm

/-- Polynomial data sufficient to fill the `polynomial_decomposition` field of
`PropagationData`.  The remaining analytic obligations are deliberately kept out of this
package. -/
structure PropagationPolynomialData {m : Nat} (A : TierSystem m) where
  tailData : (j : Nat) -> PolynomialTailPresentationData j
  step_eq : ∀ j : Nat, A.nestedFamily.step j = (tailData j).presentation
  H_eq_poly :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      A.stratification.H (j + 1) =ᶠ[puncturedNhds τ]
        fun z => MvPolynomial.eval (gatePrefix A.stratification (j + 1) z)
          (tailData j).poly

namespace PropagationPolynomialData

/-- Fill the exact `PropagationData.polynomial_decomposition` field from packaged
polynomial-tail data and concrete `H` equality against the packaged polynomial. -/
theorem polynomial_decomposition {m : Nat} {A : TierSystem m}
    (D : PropagationPolynomialData A) :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      A.stratification.H (j + 1) =ᶠ[puncturedNhds τ] tierPhiPath A j := by
  intro j τ hj hτ
  exact polynomial_decomposition_of_polynomialTailData A (D.tailData j)
    (D.step_eq j) (D.H_eq_poly hj hτ)

/-- Fill the `PropagationData.leadingCoeff_tendsto` field from continuity of the concrete
gate prefix and the packaged polynomial-tail leading evaluator. -/
theorem leadingCoeff_tendsto_of_continuousAt {m : Nat} {A : TierSystem m}
    (D : PropagationPolynomialData A) {j : Nat} {τ : ℂ}
    (hprefix : ContinuousAt (fun z => gatePrefix A.stratification j z) τ)
    (hlead : ContinuousAt (D.tailData j).presentation.lead
      (gatePrefix A.stratification j τ)) :
    Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
      (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ))) :=
  tierLeadingCoeffPath_tendsto_of_polynomialTailData_continuousAt A
    (D.tailData j) (D.step_eq j) hprefix hlead

end PropagationPolynomialData

/-! ## Quadratic leading-term blow-up helpers -/

/-- The last-gate presentation expands into its leading term plus lower-order tail along
the concrete tier path. -/
theorem tierPhiPath_eq_leadingCoeff_mul_pow_add_tailLowerSum {m : Nat}
    (A : TierSystem m) (j : Nat) (τ : ℂ) :
    tierPhiPath A j τ =
      tierLeadingCoeffPath A j τ *
          (A.stratification.s j τ) ^ (A.nestedFamily.step j).degree +
        tierTailLowerSum A j τ := by
  simp [tierPhiPath, tierLeadingCoeffPath, tierTailLowerSum,
    NestedTailFamily.evalStep, TailPresentation.eval, tailPolynomial]

/-- Clearing a local reciprocal of the last gate turns the lower tail into a polynomial in
that reciprocal. -/
theorem pow_mul_tierTailLowerSum_eq_reciprocal_sum {m : Nat}
    (A : TierSystem m) (j : Nat) (Y : ℂ -> ℂ) (z : ℂ)
    (hY : Y z * A.stratification.s j z = 1) :
    Y z ^ (A.nestedFamily.step j).degree * tierTailLowerSum A j z =
      ∑ i : Fin (A.nestedFamily.step j).degree,
        (A.nestedFamily.step j).lower i (gatePrefix A.stratification j z) *
          Y z ^ ((A.nestedFamily.step j).degree - (i : Nat)) := by
  classical
  rw [tierTailLowerSum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  let D : Nat := (A.nestedFamily.step j).degree
  let y : ℂ := Y z
  let s : ℂ := A.stratification.s j z
  let c : ℂ := (A.nestedFamily.step j).lower i (gatePrefix A.stratification j z)
  have hi_le : (i : Nat) ≤ D := Nat.le_of_lt i.isLt
  have hyspow : y ^ D * s ^ (i : Nat) = y ^ (D - (i : Nat)) := by
    calc
      y ^ D * s ^ (i : Nat) =
          (y ^ (D - (i : Nat)) * y ^ (i : Nat)) * s ^ (i : Nat) := by
            rw [← pow_add, Nat.sub_add_cancel hi_le]
      _ = y ^ (D - (i : Nat)) * (y ^ (i : Nat) * s ^ (i : Nat)) := by ring
      _ = y ^ (D - (i : Nat)) * (y * s) ^ (i : Nat) := by rw [mul_pow]
      _ = y ^ (D - (i : Nat)) := by
            rw [show y * s = 1 by simpa [y, s] using hY, one_pow, mul_one]
  calc
    Y z ^ (A.nestedFamily.step j).degree *
        ((A.nestedFamily.step j).lower i (gatePrefix A.stratification j z) *
          (A.stratification.s j z) ^ (i : Nat)) =
        c * (y ^ D * s ^ (i : Nat)) := by
          simp [D, y, s, c]
          ring
    _ = c * y ^ (D - (i : Nat)) := by rw [hyspow]
    _ =
        (A.nestedFamily.step j).lower i (gatePrefix A.stratification j z) *
          Y z ^ ((A.nestedFamily.step j).degree - (i : Nat)) := by
          simp [D, y, c]

/-- Clearing a local reciprocal of the last gate turns `tierPhiPath` into the analytic
normal-form numerator. -/
theorem pow_mul_tierPhiPath_eq_reciprocal_numerator {m : Nat}
    (A : TierSystem m) (j : Nat) (Y : ℂ -> ℂ) (z : ℂ)
    (hY : Y z * A.stratification.s j z = 1) :
    Y z ^ (A.nestedFamily.step j).degree * tierPhiPath A j z =
      tierLeadingCoeffPath A j z +
        ∑ i : Fin (A.nestedFamily.step j).degree,
          (A.nestedFamily.step j).lower i (gatePrefix A.stratification j z) *
            Y z ^ ((A.nestedFamily.step j).degree - (i : Nat)) := by
  let D : Nat := (A.nestedFamily.step j).degree
  let y : ℂ := Y z
  let s : ℂ := A.stratification.s j z
  let a : ℂ := tierLeadingCoeffPath A j z
  have hlead : y ^ D * (a * s ^ D) = a := by
    calc
      y ^ D * (a * s ^ D) = a * (y ^ D * s ^ D) := by ring
      _ = a * (y * s) ^ D := by rw [mul_pow]
      _ = a := by
            rw [show y * s = 1 by simpa [y, s] using hY, one_pow, mul_one]
  rw [tierPhiPath_eq_leadingCoeff_mul_pow_add_tailLowerSum A j z]
  calc
    Y z ^ (A.nestedFamily.step j).degree *
        (tierLeadingCoeffPath A j z *
            (A.stratification.s j z) ^ (A.nestedFamily.step j).degree +
          tierTailLowerSum A j z) =
        y ^ D * (a * s ^ D) + y ^ D * tierTailLowerSum A j z := by
          simp [D, y, s, a]
          ring
    _ = a +
        ∑ i : Fin (A.nestedFamily.step j).degree,
          (A.nestedFamily.step j).lower i (gatePrefix A.stratification j z) *
            Y z ^ ((A.nestedFamily.step j).degree - (i : Nat)) := by
          rw [hlead, pow_mul_tierTailLowerSum_eq_reciprocal_sum A j Y z hY]
    _ = tierLeadingCoeffPath A j z +
        ∑ i : Fin (A.nestedFamily.step j).degree,
          (A.nestedFamily.step j).lower i (gatePrefix A.stratification j z) *
            Y z ^ ((A.nestedFamily.step j).degree - (i : Nat)) := by
          simp [a]

/-- The cleared scaled gate argument is exactly the reciprocal denominator. -/
theorem pow_mul_scaledTierPhiPath_eq_reciprocalDenom {m : Nat}
    (A : TierSystem m) (j : Nat) (Y : ℂ -> ℂ) (z : ℂ)
    (hY : Y z * A.stratification.s j z = 1) :
    Y z ^ (A.nestedFamily.step j).degree * scaledTierPhiPath A j z =
      scaledTierPhiReciprocalDenom A j Y z := by
  let D : Nat := (A.nestedFamily.step j).degree
  let y : ℂ := Y z
  let phi : ℂ := tierPhiPath A j z
  let num : ℂ :=
    tierLeadingCoeffPath A j z +
      ∑ i : Fin (A.nestedFamily.step j).degree,
        (A.nestedFamily.step j).lower i (gatePrefix A.stratification j z) *
          Y z ^ ((A.nestedFamily.step j).degree - (i : Nat))
  have hphi :
      y ^ D * phi = num := by
    simpa [D, y, phi, num] using
      pow_mul_tierPhiPath_eq_reciprocal_numerator A j Y z hY
  calc
    Y z ^ (A.nestedFamily.step j).degree * scaledTierPhiPath A j z =
        y ^ D * (z * phi + (A.stratification.b : ℂ)) := by
          simp [scaledTierPhiPath, D, y, phi]
    _ = z * (y ^ D * phi) + (A.stratification.b : ℂ) * y ^ D := by ring
    _ = z * num + (A.stratification.b : ℂ) * y ^ D := by rw [hphi]
    _ = scaledTierPhiReciprocalDenom A j Y z := by
          simp [scaledTierPhiReciprocalDenom, D, y, num]

/-- Analyticity of the cleared reciprocal denominator from analytic coefficient paths
and an analytic current-gate reciprocal. -/
theorem scaledTierPhiReciprocalDenom_analyticAt {m : Nat}
    (A : TierSystem m) {j : Nat} {τ : ℂ} {Y : ℂ -> ℂ}
    (hY : AnalyticAt ℂ Y τ)
    (hlead : AnalyticAt ℂ (tierLeadingCoeffPath A j) τ)
    (hlower :
      ∀ i : Fin (A.nestedFamily.step j).degree,
        AnalyticAt ℂ
          (fun z =>
            (A.nestedFamily.step j).lower i
              (gatePrefix A.stratification j z)) τ) :
    AnalyticAt ℂ (scaledTierPhiReciprocalDenom A j Y) τ := by
  classical
  unfold scaledTierPhiReciprocalDenom
  refine (analyticAt_id.mul ?_).add ?_
  · exact hlead.add
      (by
        simpa using
          (Finset.univ.analyticAt_fun_sum
            (f := fun i z =>
              (A.nestedFamily.step j).lower i
                  (gatePrefix A.stratification j z) *
                Y z ^ ((A.nestedFamily.step j).degree - (i : Nat)))
            (c := τ)
            (fun i _hi =>
              (hlower i).mul
                (hY.pow ((A.nestedFamily.step j).degree - (i : Nat))))))
  · exact analyticAt_const.mul (hY.pow (A.nestedFamily.step j).degree)

/-- At a quadratic zero-free tier point, a local reciprocal `Y` for the current gate
produces a holomorphic reciprocal normal form for the scaled successor preactivation.

The reciprocal identity is local on the punctured neighborhood.  This is the form provided
by the quadratic presentation alone; promoting it to an identity for every `z ≠ τ` needs
an additional global zero-freeness statement for the successor preactivation. -/
theorem scaledTierPhiPath_local_reciprocalNormalForm_of_quadratic
    {m : Nat} (A : TierSystem m) {j : Nat} {τ : ℂ} {Y : ℂ -> ℂ}
    (hdegree : (A.nestedFamily.step j).degree = 2)
    (hY : AnalyticAt ℂ Y τ)
    (hYτ : Y τ = 0)
    (hYrecip : ∀ᶠ z in puncturedNhds τ, Y z * A.stratification.s j z = 1)
    (hτ0 : τ ≠ 0)
    (hlead0 :
      (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ) ≠ 0)
    (hlead : AnalyticAt ℂ (tierLeadingCoeffPath A j) τ)
    (hlower :
      ∀ i : Fin (A.nestedFamily.step j).degree,
        AnalyticAt ℂ
          (fun z =>
            (A.nestedFamily.step j).lower i
              (gatePrefix A.stratification j z)) τ) :
    ∃ R : ℂ -> ℂ,
      AnalyticAt ℂ R τ
        ∧ R τ = 0
        ∧ (¬ ∀ᶠ z in nhds τ, R z = R τ)
        ∧ ∀ᶠ z in puncturedNhds τ, R z * scaledTierPhiPath A j z = 1 := by
  classical
  let den : ℂ -> ℂ := scaledTierPhiReciprocalDenom A j Y
  let R : ℂ -> ℂ := scaledTierPhiReciprocal A j Y
  have hden_an : AnalyticAt ℂ den τ := by
    simpa [den] using
      scaledTierPhiReciprocalDenom_analyticAt A hY hlead hlower
  have hdenτ :
      den τ = τ * tierLeadingCoeffPath A j τ := by
    have hsum :
        (∑ i : Fin (A.nestedFamily.step j).degree,
          (A.nestedFamily.step j).lower i (gatePrefix A.stratification j τ) *
            Y τ ^ ((A.nestedFamily.step j).degree - (i : Nat))) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i _hi
      have hpow_ne : (A.nestedFamily.step j).degree - (i : Nat) ≠ 0 := by
        have hi : (i : Nat) < (A.nestedFamily.step j).degree := i.isLt
        omega
      simp [hYτ, hpow_ne]
    calc
      den τ =
          τ *
              (tierLeadingCoeffPath A j τ +
                ∑ i : Fin (A.nestedFamily.step j).degree,
                  (A.nestedFamily.step j).lower i
                      (gatePrefix A.stratification j τ) *
                    Y τ ^ ((A.nestedFamily.step j).degree - (i : Nat))) +
            (A.stratification.b : ℂ) *
              Y τ ^ (A.nestedFamily.step j).degree := by
            simp [den, scaledTierPhiReciprocalDenom]
      _ = τ * tierLeadingCoeffPath A j τ := by
            rw [hsum, hYτ, hdegree]
            ring
  have hlead0' : tierLeadingCoeffPath A j τ ≠ 0 := by
    simpa [tierLeadingCoeffPath] using hlead0
  have hdenτ_ne : den τ ≠ 0 := by
    rw [hdenτ]
    exact mul_ne_zero hτ0 hlead0'
  have hden_ne :
      ∀ᶠ z in puncturedNhds τ, den z ≠ 0 :=
    (eventually_ne_zero_of_tendsto_nhds_ne_zero hden_an.continuousAt.tendsto
      hdenτ_ne).filter_mono nhdsWithin_le_nhds
  have hR_an : AnalyticAt ℂ R τ := by
    simpa [R, scaledTierPhiReciprocal, den] using
      (hY.pow (A.nestedFamily.step j).degree).div hden_an hdenτ_ne
  have hRτ : R τ = 0 := by
    simp [R, scaledTierPhiReciprocal, hYτ, hdegree]
  have hrecip :
      ∀ᶠ z in puncturedNhds τ, R z * scaledTierPhiPath A j z = 1 := by
    filter_upwards [hYrecip, hden_ne] with z hYz hdenz
    have hclear :
        Y z ^ (A.nestedFamily.step j).degree * scaledTierPhiPath A j z =
          den z := by
      simpa [den] using
        pow_mul_scaledTierPhiPath_eq_reciprocalDenom A j Y z hYz
    calc
      R z * scaledTierPhiPath A j z =
          (Y z ^ (A.nestedFamily.step j).degree / den z) *
            scaledTierPhiPath A j z := by
            simp [R, scaledTierPhiReciprocal, den]
      _ = (Y z ^ (A.nestedFamily.step j).degree *
            scaledTierPhiPath A j z) / den z := by
            ring
      _ = den z / den z := by rw [hclear]
      _ = 1 := div_self hdenz
  have hRnonconst : ¬ ∀ᶠ z in nhds τ, R z = R τ := by
    intro hconst
    have hconst_punctured :
        ∀ᶠ z in puncturedNhds τ, R z = 0 :=
      (eventually_nhdsWithin_of_eventually_nhds hconst).mono fun z hz => by
        simpa [hRτ] using hz
    have hfalse : ∀ᶠ z in puncturedNhds τ, False := by
      filter_upwards [hconst_punctured, hrecip] with z hRz hrecipz
      rw [hRz, zero_mul] at hrecipz
      exact zero_ne_one hrecipz
    have hbot : puncturedNhds τ = ⊥ :=
      Filter.eventually_false_iff_eq_bot.mp hfalse
    exact (Filter.NeBot.ne (f := puncturedNhds τ) inferInstance) hbot
  exact ⟨R, hR_an, hRτ, hRnonconst, hrecip⟩

/-- Transport a local reciprocal normal form across punctured-neighborhood eventual
equality of the preactivation. -/
theorem local_reciprocalNormalForm_congr {H G : ℂ -> ℂ} {τ : ℂ}
    (hHG : H =ᶠ[puncturedNhds τ] G)
    (hnormal :
      ∃ R : ℂ -> ℂ,
        AnalyticAt ℂ R τ
          ∧ R τ = 0
          ∧ (¬ ∀ᶠ z in nhds τ, R z = R τ)
          ∧ ∀ᶠ z in puncturedNhds τ, R z * G z = 1) :
    ∃ R : ℂ -> ℂ,
      AnalyticAt ℂ R τ
        ∧ R τ = 0
        ∧ (¬ ∀ᶠ z in nhds τ, R z = R τ)
        ∧ ∀ᶠ z in puncturedNhds τ, R z * H z = 1 := by
  rcases hnormal with ⟨R, hR, hRτ, hRnonconst, hrecip⟩
  refine ⟨R, hR, hRτ, hRnonconst, ?_⟩
  filter_upwards [hHG, hrecip] with z hHGz hrecipz
  simpa [hHGz] using hrecipz

/-- Version of `scaledTierPhiPath_local_reciprocalNormalForm_of_quadratic` transported
to a concrete preactivation that is eventually equal to the scaled tier path. -/
theorem H_local_reciprocalNormalForm_of_scaledTierPhiPath_quadratic
    {m : Nat} (A : TierSystem m) {j : Nat} {τ : ℂ} {Y H : ℂ -> ℂ}
    (hH_scaled : H =ᶠ[puncturedNhds τ] scaledTierPhiPath A j)
    (hdegree : (A.nestedFamily.step j).degree = 2)
    (hY : AnalyticAt ℂ Y τ)
    (hYτ : Y τ = 0)
    (hYrecip : ∀ᶠ z in puncturedNhds τ, Y z * A.stratification.s j z = 1)
    (hτ0 : τ ≠ 0)
    (hlead0 :
      (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ) ≠ 0)
    (hlead : AnalyticAt ℂ (tierLeadingCoeffPath A j) τ)
    (hlower :
      ∀ i : Fin (A.nestedFamily.step j).degree,
        AnalyticAt ℂ
          (fun z =>
            (A.nestedFamily.step j).lower i
              (gatePrefix A.stratification j z)) τ) :
    ∃ R : ℂ -> ℂ,
      AnalyticAt ℂ R τ
        ∧ R τ = 0
        ∧ (¬ ∀ᶠ z in nhds τ, R z = R τ)
        ∧ ∀ᶠ z in puncturedNhds τ, R z * H z = 1 :=
  local_reciprocalNormalForm_congr hH_scaled
    (scaledTierPhiPath_local_reciprocalNormalForm_of_quadratic
      A hdegree hY hYτ hYrecip hτ0 hlead0 hlead hlower)

/-- Quadratic-degree specialization of the last-gate presentation. -/
theorem tierPhiPath_eventuallyEq_quadratic_leading_add_tailLowerSum {m : Nat}
    (A : TierSystem m) {j : Nat} {τ : ℂ}
    (hdegree : (A.nestedFamily.step j).degree = 2) :
    tierPhiPath A j =ᶠ[puncturedNhds τ]
      fun z =>
        tierLeadingCoeffPath A j z *
            (A.stratification.s j z * A.stratification.s j z) +
          tierTailLowerSum A j z := by
  filter_upwards with z
  rw [tierPhiPath_eq_leadingCoeff_mul_pow_add_tailLowerSum A j z]
  rw [hdegree, pow_two]

/-- For a quadratic tail presentation, the lower-order tail is bounded by the explicit
threshold times the leading coefficient and one power of the last variable.

This is the quantitative form of the nested-region estimate needed for blow-up: the
linear and constant terms need not be bounded when the last gate blows up, but they are
only linear in that gate. -/
theorem norm_tailLowerSum_le_threshold_mul_lead_mul_norm {α : Type*}
    (P : TailPresentation α) {x : α} {z : ℂ}
    (hdegree : P.degree = 2) (hlead : P.lead x ≠ 0) (hz : 1 ≤ ‖z‖) :
    ‖∑ i : Fin P.degree, P.lower i x * z ^ (i : Nat)‖ ≤
      P.threshold x * ‖P.lead x‖ * ‖z‖ := by
  have hlead_norm_pos : 0 < ‖P.lead x‖ := norm_pos_iff.mpr hlead
  have htail_le :
      ‖∑ i : Fin P.degree, P.lower i x * z ^ (i : Nat)‖ ≤
        (∑ i : Fin P.degree, ‖P.lower i x‖) * ‖z‖ := by
    calc
      ‖∑ i : Fin P.degree, P.lower i x * z ^ (i : Nat)‖
          ≤ ∑ i : Fin P.degree, ‖P.lower i x * z ^ (i : Nat)‖ := norm_sum_le _ _
      _ = ∑ i : Fin P.degree, ‖P.lower i x‖ * ‖z‖ ^ (i : Nat) := by
            simp [norm_pow]
      _ ≤ ∑ i : Fin P.degree, ‖P.lower i x‖ * ‖z‖ := by
            refine Finset.sum_le_sum ?_
            intro i _hi
            have hi_le_one : (i : Nat) ≤ 1 := by
              have hi_lt : (i : Nat) < 2 := by simpa [hdegree] using i.isLt
              omega
            have hpow : ‖z‖ ^ (i : Nat) ≤ ‖z‖ ^ 1 :=
              pow_le_pow_right₀ hz hi_le_one
            simpa using mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = (∑ i : Fin P.degree, ‖P.lower i x‖) * ‖z‖ := by
            rw [Finset.sum_mul]
  have hsum_mul :
      (∑ i : Fin P.degree, ‖P.lower i x‖ / ‖P.lead x‖) * ‖P.lead x‖ =
        ∑ i : Fin P.degree, ‖P.lower i x‖ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    exact div_mul_cancel₀ _ hlead_norm_pos.ne'
  have hsum_le_threshold :
      ∑ i : Fin P.degree, ‖P.lower i x‖ ≤ P.threshold x * ‖P.lead x‖ := by
    calc
      ∑ i : Fin P.degree, ‖P.lower i x‖ =
          (∑ i : Fin P.degree, ‖P.lower i x‖ / ‖P.lead x‖) * ‖P.lead x‖ := by
            rw [hsum_mul]
      _ ≤ (1 + ∑ i : Fin P.degree, ‖P.lower i x‖ / ‖P.lead x‖) *
            ‖P.lead x‖ := by
            exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ = P.threshold x * ‖P.lead x‖ := by
            simp [TailPresentation.threshold, tailThreshold]
  calc
    ‖∑ i : Fin P.degree, P.lower i x * z ^ (i : Nat)‖
        ≤ (∑ i : Fin P.degree, ‖P.lower i x‖) * ‖z‖ := htail_le
    _ ≤ (P.threshold x * ‖P.lead x‖) * ‖z‖ :=
        mul_le_mul_of_nonneg_right hsum_le_threshold (norm_nonneg _)
    _ = P.threshold x * ‖P.lead x‖ * ‖z‖ := by ring

/-- A quadratic leading term with nonzero limiting coefficient remains blowing up after
adding a punctured-neighborhood bounded remainder. -/
theorem phi_blowsUpAt_of_quadratic_remainder {m : Nat} (A : TierSystem m)
    {j : Nat} {τ : ℂ} (R : ℂ -> ℂ)
    (hphi :
      tierPhiPath A j =ᶠ[puncturedNhds τ]
        fun z =>
          tierLeadingCoeffPath A j z *
              (A.stratification.s j z * A.stratification.s j z) + R z)
    (hR : PuncturedBoundedAt R τ)
    (hgate : BlowsUpAt (A.stratification.s j) τ)
    (hlead0 :
      (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ) ≠ 0)
    (hlead_tendsto :
      Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
        (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ)))) :
    BlowsUpAt (tierPhiPath A j) τ := by
  have hleadTerm :
      BlowsUpAt
        (fun z =>
          tierLeadingCoeffPath A j z *
            (A.stratification.s j z * A.stratification.s j z)) τ :=
    BlowsUpAt.coeff_mul_self_of_tendsto_ne_zero hgate hlead_tendsto hlead0
  have hsum :
      BlowsUpAt
        (fun z =>
          tierLeadingCoeffPath A j z *
              (A.stratification.s j z * A.stratification.s j z) + R z) τ :=
    hleadTerm.add_puncturedBounded hR
  exact hsum.congr hphi.symm

/-- A quadratic tail presentation blows up when its threshold path is bounded, the last
gate blows up, and the leading coefficient tends to a nonzero value.

Unlike `phi_blowsUpAt_of_quadratic_tailLowerSum`, this theorem allows the lower-order
tail to contain a linear term in the blowing-up gate. -/
theorem phi_blowsUpAt_of_quadratic_threshold {m : Nat} (A : TierSystem m)
    {j : Nat} {τ : ℂ}
    (hdegree : (A.nestedFamily.step j).degree = 2)
    (hthreshold :
      PuncturedBoundedAt
        (fun z : ℂ =>
          ((A.nestedFamily.threshold j (gatePrefix A.stratification j z) : ℝ) : ℂ)) τ)
    (hgate : BlowsUpAt (A.stratification.s j) τ)
    (hlead0 :
      (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ) ≠ 0)
    (hlead_tendsto :
      Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
        (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ)))) :
    BlowsUpAt (tierPhiPath A j) τ := by
  rw [BlowsUpAt, Filter.tendsto_atTop]
  rw [BlowsUpAt, Filter.tendsto_atTop] at hgate
  intro M
  let a0 : ℂ := (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ)
  have ha0_pos : 0 < ‖a0‖ := norm_pos_iff.mpr hlead0
  have hlead_ge :
      ∀ᶠ z in puncturedNhds τ, ‖a0‖ / 2 ≤ ‖tierLeadingCoeffPath A j z‖ := by
    have hnorm :
        Filter.Tendsto (fun z => ‖tierLeadingCoeffPath A j z‖)
          (puncturedNhds τ) (nhds ‖a0‖) := by
      simpa [a0] using hlead_tendsto.norm
    have hhalf : ‖a0‖ / 2 < ‖a0‖ := by linarith
    exact (hnorm.eventually (Ioi_mem_nhds hhalf)).mono fun z hz => le_of_lt hz
  rcases hthreshold with ⟨C, hC⟩
  let B : ℝ := max C 0 + 1
  have hB_pos : 0 < B := by
    dsimp [B]
    linarith [le_max_right C 0]
  let R : ℝ := max (2 * B + 1) ((8 * (max M 0 + 1)) / ‖a0‖ + 1)
  have hR_ge_one : 1 ≤ R := by
    dsimp [R]
    have hleft : 1 ≤ 2 * B + 1 := by nlinarith [hB_pos]
    exact hleft.trans (le_max_left _ _)
  have hR_ge_twoB : 2 * B ≤ R := by
    dsimp [R]
    have hle : 2 * B ≤ 2 * B + 1 := by linarith
    exact hle.trans (le_max_left _ _)
  have hR_ge_M : (8 * (max M 0 + 1)) / ‖a0‖ ≤ R := by
    dsimp [R]
    have hle : (8 * (max M 0 + 1)) / ‖a0‖ ≤
        (8 * (max M 0 + 1)) / ‖a0‖ + 1 := by linarith
    exact hle.trans (le_max_right _ _)
  filter_upwards [hgate R, hlead_ge, hC] with z hs hlead hthreshold_bound
  let sNorm : ℝ := ‖A.stratification.s j z‖
  let leadNorm : ℝ := ‖tierLeadingCoeffPath A j z‖
  let thresh : ℝ := A.nestedFamily.threshold j (gatePrefix A.stratification j z)
  have hs_one : 1 ≤ sNorm := hR_ge_one.trans hs
  have hs_twoB : 2 * B ≤ sNorm := hR_ge_twoB.trans hs
  have hthresh_le_B : thresh ≤ B := by
    have habs : |thresh| ≤ C := by
      simpa [Complex.normSq, Complex.normSq_apply, Real.norm_eq_abs, thresh] using
        hthreshold_bound
    have hleC : thresh ≤ C := (le_abs_self thresh).trans habs
    have hCB : C ≤ B := by
      dsimp [B]
      exact le_trans (le_max_left C 0) (by linarith)
    exact hleC.trans hCB
  have hlead_ne : tierLeadingCoeffPath A j z ≠ 0 := by
    exact norm_pos_iff.mp (lt_of_lt_of_le (by nlinarith [ha0_pos]) hlead)
  have hthreshold_nonneg : 0 ≤ thresh := by
    have hpos :
        0 < (A.nestedFamily.step j).threshold
          (gatePrefix A.stratification j z) := by
      exact (A.nestedFamily.step j).threshold_pos (by simpa [tierLeadingCoeffPath] using hlead_ne)
    simpa [NestedTailFamily.threshold, thresh] using le_of_lt hpos
  have htail_le :
      ‖tierTailLowerSum A j z‖ ≤ thresh * leadNorm * sNorm := by
    simpa [tierTailLowerSum, tierLeadingCoeffPath, NestedTailFamily.threshold,
      thresh, leadNorm, sNorm] using
      norm_tailLowerSum_le_threshold_mul_lead_mul_norm
        (A.nestedFamily.step j)
        (x := gatePrefix A.stratification j z)
        (z := A.stratification.s j z)
        hdegree (by simpa [tierLeadingCoeffPath] using hlead_ne) hs_one
  have htail_le_B :
      ‖tierTailLowerSum A j z‖ ≤ B * leadNorm * sNorm := by
    exact htail_le.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hthresh_le_B (norm_nonneg _))
        (norm_nonneg _))
  have hdiff :
      M + ‖tierTailLowerSum A j z‖ ≤ leadNorm * (sNorm * sNorm) := by
    have hquad_lower : M ≤ (‖a0‖ / 8) * (sNorm * sNorm) := by
      have hM_nonneg : M ≤ max M 0 + 1 := by
        exact le_trans (le_max_left M 0) (by linarith)
      have hR_M : (8 * M) / ‖a0‖ ≤ R := by
        have h8 : (8 * M) / ‖a0‖ ≤ (8 * (max M 0 + 1)) / ‖a0‖ := by
          gcongr
        exact h8.trans hR_ge_M
      have hs_M : (8 * M) / ‖a0‖ ≤ sNorm := hR_M.trans hs
      have hmul : 8 * M ≤ ‖a0‖ * sNorm := by
        simpa [mul_comm] using (div_le_iff₀ ha0_pos).mp hs_M
      have hs_nonneg : 0 ≤ sNorm := norm_nonneg _
      have hM_linear : M ≤ ‖a0‖ * sNorm / 8 := by
        nlinarith
      have hlinear_quad : ‖a0‖ * sNorm / 8 ≤ (‖a0‖ / 8) * (sNorm * sNorm) := by
        have hs_le_sq : sNorm ≤ sNorm * sNorm := by nlinarith
        have ha_nonneg : 0 ≤ ‖a0‖ / 8 := by positivity
        calc
          ‖a0‖ * sNorm / 8 = (‖a0‖ / 8) * sNorm := by ring
          _ ≤ (‖a0‖ / 8) * (sNorm * sNorm) :=
              mul_le_mul_of_nonneg_left hs_le_sq ha_nonneg
      exact hM_linear.trans hlinear_quad
    have htail_quad : ‖tierTailLowerSum A j z‖ ≤ (leadNorm / 2) * (sNorm * sNorm) := by
      have hB_le_half_s : B ≤ sNorm / 2 := by nlinarith
      calc
        ‖tierTailLowerSum A j z‖ ≤ B * leadNorm * sNorm := htail_le_B
        _ ≤ (sNorm / 2) * leadNorm * sNorm := by
              gcongr
        _ = (leadNorm / 2) * (sNorm * sNorm) := by ring
    have hlead_quad_lower :
        (‖a0‖ / 8) * (sNorm * sNorm) ≤ (leadNorm / 2) * (sNorm * sNorm) := by
      have hlead8 : ‖a0‖ / 8 ≤ leadNorm / 2 := by linarith
      exact mul_le_mul_of_nonneg_right hlead8 (by positivity)
    calc
      M + ‖tierTailLowerSum A j z‖
          ≤ (‖a0‖ / 8) * (sNorm * sNorm) +
              (leadNorm / 2) * (sNorm * sNorm) :=
            add_le_add hquad_lower htail_quad
      _ ≤ (leadNorm / 2) * (sNorm * sNorm) +
              (leadNorm / 2) * (sNorm * sNorm) :=
            by nlinarith [hlead_quad_lower]
      _ = leadNorm * (sNorm * sNorm) := by ring
  have htri :
      leadNorm * (sNorm * sNorm) ≤
        ‖tierPhiPath A j z‖ + ‖tierTailLowerSum A j z‖ := by
    have hEq := tierPhiPath_eq_leadingCoeff_mul_pow_add_tailLowerSum A j z
    rw [hdegree, pow_two] at hEq
    have hnorm_eq :
        ‖tierLeadingCoeffPath A j z *
            (A.stratification.s j z * A.stratification.s j z)‖ =
          leadNorm * (sNorm * sNorm) := by
      simp [leadNorm, sNorm]
    rw [← hnorm_eq]
    calc
      ‖tierLeadingCoeffPath A j z *
          (A.stratification.s j z * A.stratification.s j z)‖ =
          ‖tierPhiPath A j z - tierTailLowerSum A j z‖ := by
            rw [hEq]
            ring_nf
      _ ≤ ‖tierPhiPath A j z‖ + ‖tierTailLowerSum A j z‖ := norm_sub_le _ _
  linarith

/-- A quadratic last-gate presentation blows up when its lower-order tail is bounded and
the leading coefficient tends to a nonzero center value. -/
theorem phi_blowsUpAt_of_quadratic_tailLowerSum {m : Nat} (A : TierSystem m)
    {j : Nat} {τ : ℂ}
    (hdegree : (A.nestedFamily.step j).degree = 2)
    (hlower : PuncturedBoundedAt (tierTailLowerSum A j) τ)
    (hgate : BlowsUpAt (A.stratification.s j) τ)
    (hlead0 :
      (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ) ≠ 0)
    (hlead_tendsto :
      Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
        (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ)))) :
    BlowsUpAt (tierPhiPath A j) τ :=
  phi_blowsUpAt_of_quadratic_remainder A (tierTailLowerSum A j)
    (tierPhiPath_eventuallyEq_quadratic_leading_add_tailLowerSum A hdegree)
    hlower hgate hlead0 hlead_tendsto

/-! ## Propagation packages -/

/-- Claim-B-ready propagation data for a concrete tier system.

The fields are intentionally the precise interfaces used in the TeX proof:
* `polynomial_decomposition` identifies `H'_{j+1}` with the last-gate polynomial
  `φ'_{j+1}` along punctured neighborhoods of a tier point;
* `leadingCoeff_ne_on_region` records the nested-largeness nonvanishing of the leading
  coefficient;
* `leadingCoeff_tendsto` and `phi_blowsUpAt_of_gate` package the lower-term boundedness
  and dominant quadratic blow-up argument for `φ'_{j+1}`;
* `levelSet_frequently` is the analytic level-set step producing new points of
  `S'^{j+1}` that satisfy the successor-tier threshold condition. -/
structure PropagationData {m : Nat} (A : TierSystem m) where
  polynomial_decomposition :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      A.stratification.H (j + 1) =ᶠ[puncturedNhds τ] tierPhiPath A j
  leadingCoeff_ne_on_region :
    ∀ j : Nat, ∀ x : Fin j -> ℂ, x ∈ A.nestedFamily.region j ->
      (A.nestedFamily.step j).lead x ≠ 0
  leadingCoeff_tendsto :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
        (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ)))
  phi_blowsUpAt_of_gate :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      BlowsUpAt (A.stratification.s j) τ ->
      (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ) ≠ 0 ->
      Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
        (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ))) ->
      BlowsUpAt (tierPhiPath A j) τ
  levelSet_frequently :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      (∀ᶠ z in puncturedNhds τ, z ∈ A.stratification.omega (j + 1)) ->
      BlowsUpAt (A.stratification.H (j + 1)) τ ->
      ∃ᶠ z in puncturedNhds τ,
        z ∈ A.stratification.S (j + 1)
          ∧ gatePrefix A.stratification j z ∈ A.nestedFamily.region j
          ∧ A.nestedFamily.threshold j (gatePrefix A.stratification j z) <
            ‖A.stratification.s j z‖

/-- Propagation data with the polynomial-decomposition field factored through the
polynomial-tail bridge.  The four remaining fields are the analytic/nonvanishing
obligations still needed to build full `PropagationData`. -/
structure PropagationBridgeData {m : Nat} (A : TierSystem m) where
  polynomial : PropagationPolynomialData A
  leadingCoeff_ne_on_region :
    ∀ j : Nat, ∀ x : Fin j -> ℂ, x ∈ A.nestedFamily.region j ->
      (A.nestedFamily.step j).lead x ≠ 0
  leadingCoeff_tendsto :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
        (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ)))
  phi_blowsUpAt_of_gate :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      BlowsUpAt (A.stratification.s j) τ ->
      (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ) ≠ 0 ->
      Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
        (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ))) ->
      BlowsUpAt (tierPhiPath A j) τ
  levelSet_frequently :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      (∀ᶠ z in puncturedNhds τ, z ∈ A.stratification.omega (j + 1)) ->
      BlowsUpAt (A.stratification.H (j + 1)) τ ->
      ∃ᶠ z in puncturedNhds τ,
        z ∈ A.stratification.S (j + 1)
          ∧ gatePrefix A.stratification j z ∈ A.nestedFamily.region j
          ∧ A.nestedFamily.threshold j (gatePrefix A.stratification j z) <
            ‖A.stratification.s j z‖

/-- Analytic data for propagation after factoring polynomial decomposition, leading
coefficient limits, and quadratic blow-up through reusable helpers.

Compared with `PropagationBridgeData`, this package replaces the raw
`leadingCoeff_tendsto` and `phi_blowsUpAt_of_gate` fields with continuity of the gate
prefix and leading evaluator, plus a quadratic presentation whose lower-order tail is
bounded on punctured neighborhoods. -/
structure PropagationAnalyticData {m : Nat} (A : TierSystem m) where
  polynomial : PropagationPolynomialData A
  leadingCoeff_ne_on_region :
    ∀ j : Nat, ∀ x : Fin j -> ℂ, x ∈ A.nestedFamily.region j ->
      (A.nestedFamily.step j).lead x ≠ 0
  gatePrefix_continuousAt :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      ContinuousAt (fun z => gatePrefix A.stratification j z) τ
  tailLeadingCoeff_continuousAt :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      ContinuousAt (polynomial.tailData j).presentation.lead
        (gatePrefix A.stratification j τ)
  quadratic_degree :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      (A.nestedFamily.step j).degree = 2
  threshold_puncturedBounded :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      PuncturedBoundedAt
        (fun z : ℂ =>
          ((A.nestedFamily.threshold j (gatePrefix A.stratification j z) : ℝ) : ℂ)) τ
  levelSet_frequently :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      (∀ᶠ z in puncturedNhds τ, z ∈ A.stratification.omega (j + 1)) ->
      BlowsUpAt (A.stratification.H (j + 1)) τ ->
      ∃ᶠ z in puncturedNhds τ,
        z ∈ A.stratification.S (j + 1)
          ∧ gatePrefix A.stratification j z ∈ A.nestedFamily.region j
          ∧ A.nestedFamily.threshold j (gatePrefix A.stratification j z) <
            ‖A.stratification.s j z‖

/-- Polynomial data for the concrete Step 1 gate argument.

This is the corrected concrete interface: the output preactivation is eventually equal to
`z * φ'_{j+1}(z) + b`, while the nested tail presentation still supplies the leading
coefficient and lower-order tail of `φ'_{j+1}` itself. -/
structure ScaledPropagationPolynomialData {m : Nat} (A : TierSystem m) where
  tailData : (j : Nat) -> PolynomialTailPresentationData j
  step_eq : ∀ j : Nat, A.nestedFamily.step j = (tailData j).presentation
  H_eq_scaled :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      A.stratification.H (j + 1) =ᶠ[puncturedNhds τ] scaledTierPhiPath A j

/-- Bridge data for Claim B using the scaled concrete gate argument
`H'_{j+1}(z) = z * φ'_{j+1}(z) + b`. -/
structure ScaledPropagationBridgeData {m : Nat} (A : TierSystem m) where
  polynomial : ScaledPropagationPolynomialData A
  leadingCoeff_ne_on_region :
    ∀ j : Nat, ∀ x : Fin j -> ℂ, x ∈ A.nestedFamily.region j ->
      (A.nestedFamily.step j).lead x ≠ 0
  leadingCoeff_tendsto :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
        (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ)))
  phi_blowsUpAt_of_gate :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      BlowsUpAt (A.stratification.s j) τ ->
      (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ) ≠ 0 ->
      Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
        (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ))) ->
      BlowsUpAt (tierPhiPath A j) τ
  levelSet_frequently :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      (∀ᶠ z in puncturedNhds τ, z ∈ A.stratification.omega (j + 1)) ->
      BlowsUpAt (A.stratification.H (j + 1)) τ ->
      ∃ᶠ z in puncturedNhds τ,
        z ∈ A.stratification.S (j + 1)
          ∧ gatePrefix A.stratification j z ∈ A.nestedFamily.region j
          ∧ A.nestedFamily.threshold j (gatePrefix A.stratification j z) <
            ‖A.stratification.s j z‖

/-- Analytic data for the corrected scaled propagation bridge. -/
structure ScaledPropagationAnalyticData {m : Nat} (A : TierSystem m) where
  polynomial : ScaledPropagationPolynomialData A
  leadingCoeff_ne_on_region :
    ∀ j : Nat, ∀ x : Fin j -> ℂ, x ∈ A.nestedFamily.region j ->
      (A.nestedFamily.step j).lead x ≠ 0
  gatePrefix_continuousAt :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      ContinuousAt (fun z => gatePrefix A.stratification j z) τ
  tailLeadingCoeff_continuousAt :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      ContinuousAt (polynomial.tailData j).presentation.lead
        (gatePrefix A.stratification j τ)
  quadratic_degree :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      (A.nestedFamily.step j).degree = 2
  threshold_puncturedBounded :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      PuncturedBoundedAt
        (fun z : ℂ =>
          ((A.nestedFamily.threshold j (gatePrefix A.stratification j z) : ℝ) : ℂ)) τ
  levelSet_frequently :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      (∀ᶠ z in puncturedNhds τ, z ∈ A.stratification.omega (j + 1)) ->
      BlowsUpAt (A.stratification.H (j + 1)) τ ->
      ∃ᶠ z in puncturedNhds τ,
        z ∈ A.stratification.S (j + 1)
          ∧ gatePrefix A.stratification j z ∈ A.nestedFamily.region j
          ∧ A.nestedFamily.threshold j (gatePrefix A.stratification j z) <
            ‖A.stratification.s j z‖

/-- Zero-free bridge data for Claim B using the scaled concrete gate argument
`H'_{j+1}(z) = z * φ'_{j+1}(z) + b`.

Unlike `ScaledPropagationBridgeData`, the tier-point leading coefficient is obtained from
membership in `A.T0 j`, so no global nonvanishing hypothesis on the original recursive
region is needed. -/
structure ZeroFreeScaledPropagationBridgeData {m : Nat} (A : TierSystem m) where
  polynomial : ScaledPropagationPolynomialData A
  leadingCoeff_tendsto :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T0 j ->
      Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
        (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ)))
  phi_blowsUpAt_of_gate :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T0 j ->
      BlowsUpAt (A.stratification.s j) τ ->
      (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ) ≠ 0 ->
      Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
        (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ))) ->
      BlowsUpAt (tierPhiPath A j) τ
  levelSet_frequently :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T0 j ->
      (∀ᶠ z in puncturedNhds τ, z ∈ A.stratification.omega (j + 1)) ->
      BlowsUpAt (A.stratification.H (j + 1)) τ ->
      ∃ᶠ z in puncturedNhds τ,
        z ∈ A.stratification.S (j + 1)
          ∧ gatePrefix A.stratification j z ∈ A.nestedFamily.zeroFreeRegion j
          ∧ A.nestedFamily.threshold j (gatePrefix A.stratification j z) <
            ‖A.stratification.s j z‖
          ∧ (A.nestedFamily.step (j + 1)).lead
            (gatePrefix A.stratification (j + 1) z) ≠ 0

/-- Analytic data for the zero-free scaled propagation bridge.

All tier-point hypotheses are taken over `A.T0`; the successor level-set output is exactly
the `TierSystem.mem_T0_succ` shape. -/
structure ZeroFreeScaledPropagationAnalyticData {m : Nat} (A : TierSystem m) where
  polynomial : ScaledPropagationPolynomialData A
  gatePrefix_continuousAt :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T0 j ->
      ContinuousAt (fun z => gatePrefix A.stratification j z) τ
  tailLeadingCoeff_continuousAt :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T0 j ->
      ContinuousAt (polynomial.tailData j).presentation.lead
        (gatePrefix A.stratification j τ)
  quadratic_degree :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T0 j ->
      (A.nestedFamily.step j).degree = 2
  threshold_puncturedBounded :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T0 j ->
      PuncturedBoundedAt
        (fun z : ℂ =>
          ((A.nestedFamily.threshold j (gatePrefix A.stratification j z) : ℝ) : ℂ)) τ
  levelSet_frequently :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T0 j ->
      (∀ᶠ z in puncturedNhds τ, z ∈ A.stratification.omega (j + 1)) ->
      BlowsUpAt (A.stratification.H (j + 1)) τ ->
      ∃ᶠ z in puncturedNhds τ,
        z ∈ A.stratification.S (j + 1)
          ∧ gatePrefix A.stratification j z ∈ A.nestedFamily.zeroFreeRegion j
          ∧ A.nestedFamily.threshold j (gatePrefix A.stratification j z) <
            ‖A.stratification.s j z‖
          ∧ (A.nestedFamily.step (j + 1)).lead
            (gatePrefix A.stratification (j + 1) z) ≠ 0

/-! ## Zero-free level-set upgrade -/

/-- If the true analytic level-set argument supplies frequent successor-stratum points
where the next leading coefficient is nonzero, then the zero-free successor membership
shape follows from zero-free-region openness at the current tier point, continuity of the
current gate prefix, boundedness of the current threshold path, and blow-up of the current
gate.

This isolates the remaining hard Claim B input: the level-set/frequent-membership
argument must produce points of `S (j+1)` avoiding the next leading-coefficient zero
locus.  The recursive zero-free prefix and largeness inequality are then formal
topological consequences. -/
theorem zeroFreeLevelSet_frequently_of_levelSetLead_frequently {m : Nat}
    (A : TierSystem m) {j : Nat} {τ : ℂ}
    (hj : j + 1 < m) (hτ : τ ∈ A.T0 j)
    (hprefix : ContinuousAt (fun z => gatePrefix A.stratification j z) τ)
    (hzeroOpen : IsOpen (A.nestedFamily.zeroFreeRegion j))
    (hthreshold :
      PuncturedBoundedAt
        (fun z : ℂ =>
          ((A.nestedFamily.threshold j (gatePrefix A.stratification j z) : ℝ) : ℂ)) τ)
    (hlevelLead :
      (∀ᶠ z in puncturedNhds τ, z ∈ A.stratification.omega (j + 1)) ->
      BlowsUpAt (A.stratification.H (j + 1)) τ ->
      ∃ᶠ z in puncturedNhds τ,
        z ∈ A.stratification.S (j + 1)
          ∧ (A.nestedFamily.step (j + 1)).lead
            (gatePrefix A.stratification (j + 1) z) ≠ 0)
    (hOmega : ∀ᶠ z in puncturedNhds τ, z ∈ A.stratification.omega (j + 1))
    (hH : BlowsUpAt (A.stratification.H (j + 1)) τ) :
    ∃ᶠ z in puncturedNhds τ,
      z ∈ A.stratification.S (j + 1)
        ∧ gatePrefix A.stratification j z ∈ A.nestedFamily.zeroFreeRegion j
        ∧ A.nestedFamily.threshold j (gatePrefix A.stratification j z) <
          ‖A.stratification.s j z‖
        ∧ (A.nestedFamily.step (j + 1)).lead
          (gatePrefix A.stratification (j + 1) z) ≠ 0 := by
  have hpref :
      ∀ᶠ z in puncturedNhds τ,
        gatePrefix A.stratification j z ∈ A.nestedFamily.zeroFreeRegion j := by
    have hτprefix :
        gatePrefix A.stratification j τ ∈ A.nestedFamily.zeroFreeRegion j :=
      A.T0_mem_zeroFreeRegion hτ
    exact (hprefix.tendsto.eventually (hzeroOpen.mem_nhds hτprefix)).filter_mono
      nhdsWithin_le_nhds
  have hgate : BlowsUpAt (A.stratification.s j) τ := by
    have hjm : j < m := by omega
    exact A.stratification.gate_blowsUpAt_of_mem_stratum hjm (A.T0_mem_stratum hτ)
  have hlarge :
      ∀ᶠ z in puncturedNhds τ,
        A.nestedFamily.threshold j (gatePrefix A.stratification j z) <
          ‖A.stratification.s j z‖ := by
    rcases hthreshold with ⟨C, hC⟩
    rw [BlowsUpAt, Filter.tendsto_atTop] at hgate
    filter_upwards [hC, hgate (C + 1)] with z hCz hsz
    have hthreshold_abs :
        |A.nestedFamily.threshold j (gatePrefix A.stratification j z)| ≤ C := by
      simpa [Real.norm_eq_abs] using hCz
    have hthreshold_le :
        A.nestedFamily.threshold j (gatePrefix A.stratification j z) ≤ C :=
      (le_abs_self _).trans hthreshold_abs
    linarith
  have hLevel := hlevelLead hOmega hH
  have hCombined := (hLevel.and_eventually hpref).and_eventually hlarge
  exact hCombined.mono fun z hz => by
    rcases hz with ⟨⟨⟨hS, hlead⟩, hprefz⟩, hlargez⟩
    exact ⟨hS, hprefz, hlargez, hlead⟩

namespace ScaledPropagationPolynomialData

/-- Build scaled polynomial propagation data from a polynomial-backed nested tail tower.

The only concrete gate identity required here is the corrected scaled one:
`H'_{j+1}(z) = z * φ'_{j+1}(z) + b` eventually at tier points. -/
def ofPolynomialNestedTailData {m : Nat} {A : TierSystem m}
    (D : PolynomialNestedTailData)
    (hfamily : A.nestedFamily = D.toNestedTailFamily)
    (hH_scaled :
      ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
        A.stratification.H (j + 1) =ᶠ[puncturedNhds τ] scaledTierPhiPath A j) :
    ScaledPropagationPolynomialData A where
  tailData := D.tailData
  step_eq := by
    intro j
    rw [hfamily]
    rfl
  H_eq_scaled := hH_scaled

/-- Fill the scaled bridge leading-coefficient limit from continuity of the concrete
gate prefix and the packaged polynomial-tail leading evaluator. -/
theorem leadingCoeff_tendsto_of_continuousAt {m : Nat} {A : TierSystem m}
    (D : ScaledPropagationPolynomialData A) {j : Nat} {τ : ℂ}
    (hprefix : ContinuousAt (fun z => gatePrefix A.stratification j z) τ)
    (hlead : ContinuousAt (D.tailData j).presentation.lead
      (gatePrefix A.stratification j τ)) :
    Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
      (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ))) :=
  tierLeadingCoeffPath_tendsto_of_polynomialTailData_continuousAt A
    (D.tailData j) (D.step_eq j) hprefix hlead

end ScaledPropagationPolynomialData

namespace PropagationBridgeData

end PropagationBridgeData

namespace PropagationAnalyticData

/-- The leading coefficient limit supplied by the continuity fields of
`PropagationAnalyticData`. -/
theorem leadingCoeff_tendsto {m : Nat} {A : TierSystem m}
    (D : PropagationAnalyticData A) :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
        (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ))) := by
  intro j τ hj hτ
  exact PropagationPolynomialData.leadingCoeff_tendsto_of_continuousAt D.polynomial
    (D.gatePrefix_continuousAt hj hτ)
    (D.tailLeadingCoeff_continuousAt hj hτ)

/-- The quadratic blow-up field supplied by `PropagationAnalyticData`. -/
theorem phi_blowsUpAt_of_gate {m : Nat} {A : TierSystem m}
    (D : PropagationAnalyticData A) :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      BlowsUpAt (A.stratification.s j) τ ->
      (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ) ≠ 0 ->
      Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
        (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ))) ->
      BlowsUpAt (tierPhiPath A j) τ := by
  intro j τ hj hτ hgate hlead hlead_tendsto
  exact phi_blowsUpAt_of_quadratic_threshold A
    (D.quadratic_degree hj hτ)
    (D.threshold_puncturedBounded hj hτ)
    hgate hlead hlead_tendsto

end PropagationAnalyticData

/-- The final Claim B interface: every tier accumulates on the next tier. -/
structure TierPropagation {m : Nat} (A : TierSystem m) where
  chain : ∀ j : Nat, j + 1 < m -> A.T j ⊆ acc (A.T (j + 1))

/-- Zero-free Claim B interface: every zero-free tier accumulates on the next zero-free
tier. -/
structure ZeroFreeTierPropagation {m : Nat} (A : TierSystem m) where
  chain : ∀ j : Nat, j + 1 < m -> A.T0 j ⊆ acc (A.T0 (j + 1))

namespace PropagationData

variable {m : Nat} {A : TierSystem m} (D : PropagationData A)
include D

/-- The leading coefficient is nonzero at the prefix of every tier point. -/
theorem leadingCoeff_ne_at_tier {j : Nat} {τ : ℂ} (hτ : τ ∈ A.T j) :
    (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ) ≠ 0 :=
  PropagationData.leadingCoeff_ne_on_region D j
    (gatePrefix A.stratification j τ) (A.mem_region hτ)

omit D in
/-- The concrete stratum pole makes the `j`-th gate blow up at every point of `T_j`. -/
theorem gate_blowsUpAt {j : Nat} {τ : ℂ} (hj : j + 1 < m) (hτ : τ ∈ A.T j) :
    BlowsUpAt (A.stratification.s j) τ := by
  have hjm : j < m := by omega
  exact A.stratification.gate_blowsUpAt_of_mem_stratum hjm (A.mem_stratum hτ)

/-- The last-gate polynomial `φ'_{j+1}` blows up at every point of `T_j`. -/
theorem phi_blowsUpAt {j : Nat} {τ : ℂ} (hj : j + 1 < m) (hτ : τ ∈ A.T j) :
    BlowsUpAt (tierPhiPath A j) τ :=
  PropagationData.phi_blowsUpAt_of_gate D hj hτ
    (PropagationData.gate_blowsUpAt (A := A) hj hτ)
    (PropagationData.leadingCoeff_ne_at_tier D hτ)
    (PropagationData.leadingCoeff_tendsto D hj hτ)

/-- The concrete preactivation `H'_{j+1}` blows up once it is identified with
`φ'_{j+1}` on punctured neighborhoods. -/
theorem gateArgument_blowsUpAt {j : Nat} {τ : ℂ} (hj : j + 1 < m)
    (hτ : τ ∈ A.T j) :
    BlowsUpAt (A.stratification.H (j + 1)) τ :=
  (PropagationData.phi_blowsUpAt D hj hτ).congr
    (PropagationData.polynomial_decomposition D hj hτ).symm

/-- The analytic level-set step, rewritten as frequent membership in the successor tier. -/
theorem frequently_mem_tier_succ {j : Nat} {τ : ℂ} (hj : j + 1 < m)
    (hτ : τ ∈ A.T j) :
    ∃ᶠ z in puncturedNhds τ, z ∈ A.T (j + 1) := by
  have hjm : j < m := by omega
  have hOmega : ∀ᶠ z in puncturedNhds τ, z ∈ A.stratification.omega (j + 1) :=
    A.punctured_omega_succ hjm hτ
  have hLevel := PropagationData.levelSet_frequently D hj hτ hOmega
    (PropagationData.gateArgument_blowsUpAt D hj hτ)
  exact hLevel.mono fun z hz => (A.mem_succ (j := j) (τ := z)).mpr hz

/-- Claim B for one adjacent tier: `T_j ⊆ acc (T_{j+1})`. -/
theorem tier_subset_acc_succ (j : Nat) (hj : j + 1 < m) :
    A.T j ⊆ acc (A.T (j + 1)) := by
  intro τ hτ
  exact mem_acc_of_frequently_mem_punctured
    (PropagationData.frequently_mem_tier_succ D hj hτ)

/-- The full propagation chain consumed by the descent shard. -/
theorem chain :
    ∀ j : Nat, j + 1 < m -> A.T j ⊆ acc (A.T (j + 1)) :=
  PropagationData.tier_subset_acc_succ D

end PropagationData

namespace ScaledPropagationBridgeData

variable {m : Nat} {A : TierSystem m} (D : ScaledPropagationBridgeData A)
include D

/-- The leading coefficient is nonzero at the prefix of every tier point. -/
theorem leadingCoeff_ne_at_tier {j : Nat} {τ : ℂ} (hτ : τ ∈ A.T j) :
    (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ) ≠ 0 :=
  ScaledPropagationBridgeData.leadingCoeff_ne_on_region D j
    (gatePrefix A.stratification j τ) (A.mem_region hτ)

omit D in
/-- The concrete stratum pole makes the `j`-th gate blow up at every point of `T_j`. -/
theorem gate_blowsUpAt {j : Nat} {τ : ℂ} (hj : j + 1 < m) (hτ : τ ∈ A.T j) :
    BlowsUpAt (A.stratification.s j) τ := by
  have hjm : j < m := by omega
  exact A.stratification.gate_blowsUpAt_of_mem_stratum hjm (A.mem_stratum hτ)

/-- The last-gate polynomial `φ'_{j+1}` blows up at every point of `T_j`. -/
theorem phi_blowsUpAt {j : Nat} {τ : ℂ} (hj : j + 1 < m) (hτ : τ ∈ A.T j) :
    BlowsUpAt (tierPhiPath A j) τ :=
  ScaledPropagationBridgeData.phi_blowsUpAt_of_gate D hj hτ
    (ScaledPropagationBridgeData.gate_blowsUpAt (A := A) hj hτ)
    (ScaledPropagationBridgeData.leadingCoeff_ne_at_tier D hτ)
    (ScaledPropagationBridgeData.leadingCoeff_tendsto D hj hτ)

/-- The concrete preactivation `H'_{j+1}` blows up from the corrected scaled identity
`H'_{j+1}(z) = z * φ'_{j+1}(z) + b`. -/
theorem gateArgument_blowsUpAt {j : Nat} {τ : ℂ} (hj : j + 1 < m)
    (hτ : τ ∈ A.T j) :
    BlowsUpAt (A.stratification.H (j + 1)) τ := by
  have hjm : j < m := by omega
  have hτ0 : τ ≠ 0 := A.ne_zero hjm hτ
  have hscaled : BlowsUpAt (scaledTierPhiPath A j) τ :=
    scaledTierPhiPath_blowsUpAt_of_phi A hτ0
      (ScaledPropagationBridgeData.phi_blowsUpAt D hj hτ)
  exact hscaled.congr (ScaledPropagationPolynomialData.H_eq_scaled D.polynomial hj hτ).symm

/-- The analytic level-set step, rewritten as frequent membership in the successor tier. -/
theorem frequently_mem_tier_succ {j : Nat} {τ : ℂ} (hj : j + 1 < m)
    (hτ : τ ∈ A.T j) :
    ∃ᶠ z in puncturedNhds τ, z ∈ A.T (j + 1) := by
  have hjm : j < m := by omega
  have hOmega : ∀ᶠ z in puncturedNhds τ, z ∈ A.stratification.omega (j + 1) :=
    A.punctured_omega_succ hjm hτ
  have hLevel := ScaledPropagationBridgeData.levelSet_frequently D hj hτ hOmega
    (ScaledPropagationBridgeData.gateArgument_blowsUpAt D hj hτ)
  exact hLevel.mono fun z hz => (A.mem_succ (j := j) (τ := z)).mpr hz

/-- Claim B for one adjacent tier under the corrected scaled gate identity. -/
theorem tier_subset_acc_succ (j : Nat) (hj : j + 1 < m) :
    A.T j ⊆ acc (A.T (j + 1)) := by
  intro τ hτ
  exact mem_acc_of_frequently_mem_punctured
    (ScaledPropagationBridgeData.frequently_mem_tier_succ D hj hτ)

/-- The full propagation chain consumed by the descent shard. -/
theorem chain :
    ∀ j : Nat, j + 1 < m -> A.T j ⊆ acc (A.T (j + 1)) :=
  ScaledPropagationBridgeData.tier_subset_acc_succ D

end ScaledPropagationBridgeData

namespace ZeroFreeScaledPropagationBridgeData

variable {m : Nat} {A : TierSystem m} (D : ZeroFreeScaledPropagationBridgeData A)
include D

omit D in
/-- The leading coefficient is nonzero at the prefix of every zero-free tier point. -/
theorem leadingCoeff_ne_at_tier {j : Nat} {τ : ℂ} (hτ : τ ∈ A.T0 j) :
    (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ) ≠ 0 :=
  A.T0_lead_ne hτ

omit D in
/-- The concrete stratum pole makes the `j`-th gate blow up at every zero-free tier
point. -/
theorem gate_blowsUpAt {j : Nat} {τ : ℂ} (hj : j + 1 < m) (hτ : τ ∈ A.T0 j) :
    BlowsUpAt (A.stratification.s j) τ := by
  have hjm : j < m := by omega
  exact A.stratification.gate_blowsUpAt_of_mem_stratum hjm (A.T0_mem_stratum hτ)

/-- The last-gate polynomial `φ'_{j+1}` blows up at every point of `T0_j`. -/
theorem phi_blowsUpAt {j : Nat} {τ : ℂ} (hj : j + 1 < m) (hτ : τ ∈ A.T0 j) :
    BlowsUpAt (tierPhiPath A j) τ :=
  ZeroFreeScaledPropagationBridgeData.phi_blowsUpAt_of_gate D hj hτ
    (ZeroFreeScaledPropagationBridgeData.gate_blowsUpAt (A := A) hj hτ)
    (ZeroFreeScaledPropagationBridgeData.leadingCoeff_ne_at_tier (A := A) hτ)
    (ZeroFreeScaledPropagationBridgeData.leadingCoeff_tendsto D hj hτ)

/-- The concrete preactivation `H'_{j+1}` blows up from the corrected scaled identity
`H'_{j+1}(z) = z * φ'_{j+1}(z) + b` at zero-free tier points. -/
theorem gateArgument_blowsUpAt {j : Nat} {τ : ℂ} (hj : j + 1 < m)
    (hτ : τ ∈ A.T0 j) :
    BlowsUpAt (A.stratification.H (j + 1)) τ := by
  have hjm : j < m := by omega
  have hτ0 : τ ≠ 0 := A.T0_ne_zero hjm hτ
  have hτT : τ ∈ A.T j := A.T0_subset_T j hτ
  have hscaled : BlowsUpAt (scaledTierPhiPath A j) τ :=
    scaledTierPhiPath_blowsUpAt_of_phi A hτ0
      (ZeroFreeScaledPropagationBridgeData.phi_blowsUpAt D hj hτ)
  exact hscaled.congr
    (ScaledPropagationPolynomialData.H_eq_scaled D.polynomial hj hτT).symm

/-- The analytic level-set step, rewritten as frequent membership in the successor
zero-free tier. -/
theorem frequently_mem_T0_succ {j : Nat} {τ : ℂ} (hj : j + 1 < m)
    (hτ : τ ∈ A.T0 j) :
    ∃ᶠ z in puncturedNhds τ, z ∈ A.T0 (j + 1) := by
  have hjm : j < m := by omega
  have hOmega : ∀ᶠ z in puncturedNhds τ, z ∈ A.stratification.omega (j + 1) :=
    A.T0_punctured_omega_succ hjm hτ
  have hLevel := ZeroFreeScaledPropagationBridgeData.levelSet_frequently D hj hτ hOmega
    (ZeroFreeScaledPropagationBridgeData.gateArgument_blowsUpAt D hj hτ)
  exact hLevel.mono fun z hz => (A.mem_T0_succ (j := j) (τ := z)).mpr hz

/-- Claim B for one adjacent zero-free tier. -/
theorem tier_subset_acc_succ (j : Nat) (hj : j + 1 < m) :
    A.T0 j ⊆ acc (A.T0 (j + 1)) := by
  intro τ hτ
  exact mem_acc_of_frequently_mem_punctured
    (ZeroFreeScaledPropagationBridgeData.frequently_mem_T0_succ D hj hτ)

/-- The full zero-free propagation chain. -/
theorem chain :
    ∀ j : Nat, j + 1 < m -> A.T0 j ⊆ acc (A.T0 (j + 1)) :=
  ZeroFreeScaledPropagationBridgeData.tier_subset_acc_succ D

/-- Package the zero-free scaled proof as a `ZeroFreeTierPropagation`. -/
def toZeroFreeTierPropagation : ZeroFreeTierPropagation A where
  chain := fun j hj => ZeroFreeScaledPropagationBridgeData.tier_subset_acc_succ D j hj

end ZeroFreeScaledPropagationBridgeData

namespace ScaledPropagationAnalyticData

/-- Constructor for scaled analytic propagation data from a polynomial-backed nested
tail tower.  The polynomial tower supplies the tail data and leading-coefficient
continuity; the remaining hypotheses are the genuinely concrete Claim B obligations. -/
def ofPolynomialNestedTailData {m : Nat} {A : TierSystem m}
    (D : PolynomialNestedTailData)
    (hfamily : A.nestedFamily = D.toNestedTailFamily)
    (hH_scaled :
      ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
        A.stratification.H (j + 1) =ᶠ[puncturedNhds τ] scaledTierPhiPath A j)
    (hlead :
      ∀ j : Nat, ∀ x : Fin j -> ℂ, x ∈ D.region j ->
        (D.tailData j).presentation.lead x ≠ 0)
    (hprefix :
      ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
        ContinuousAt (fun z => gatePrefix A.stratification j z) τ)
    (hdegree :
      ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
        (D.tailData j).presentation.degree = 2)
    (hlevel :
      ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
        (∀ᶠ z in puncturedNhds τ, z ∈ A.stratification.omega (j + 1)) ->
        BlowsUpAt (A.stratification.H (j + 1)) τ ->
        ∃ᶠ z in puncturedNhds τ,
          z ∈ A.stratification.S (j + 1)
            ∧ gatePrefix A.stratification j z ∈ A.nestedFamily.region j
            ∧ A.nestedFamily.threshold j (gatePrefix A.stratification j z) <
              ‖A.stratification.s j z‖) :
    ScaledPropagationAnalyticData A where
  polynomial :=
    ScaledPropagationPolynomialData.ofPolynomialNestedTailData D hfamily hH_scaled
  leadingCoeff_ne_on_region := by
    intro j x hx
    have hxD : x ∈ D.region j := by
      simpa [PolynomialNestedTailData.region, hfamily] using hx
    simpa [hfamily] using hlead j x hxD
  gatePrefix_continuousAt := hprefix
  tailLeadingCoeff_continuousAt := by
    intro j τ hj hτ
    simpa [ScaledPropagationPolynomialData.ofPolynomialNestedTailData] using
      (D.lead_continuous j).continuousAt
  quadratic_degree := by
    intro j τ hj hτ
    simpa [hfamily] using hdegree hj hτ
  threshold_puncturedBounded := by
    intro j τ hj hτ
    have hτprefixA :
        gatePrefix A.stratification j τ ∈ A.nestedFamily.region j :=
      A.mem_region hτ
    have hτprefixD :
        gatePrefix A.stratification j τ ∈ D.region j := by
      simpa [PolynomialNestedTailData.region, hfamily] using hτprefixA
    have hthreshold_contD :
        ContinuousAt (D.threshold j) (gatePrefix A.stratification j τ) :=
      (D.continuousOn_thresholds_of_lead_ne
        (fun m x hx => hlead m x hx) j).continuousAt
          ((D.isOpen_region_of_lead_ne
            (fun m x hx => hlead m x hx) j).mem_nhds hτprefixD)
    have hthreshold_contR :
        ContinuousAt
          (fun z : ℂ => D.threshold j (gatePrefix A.stratification j z)) τ :=
      hthreshold_contD.comp (hprefix hj hτ)
    have hthreshold_contC :
        ContinuousAt
          (fun z : ℂ =>
            ((D.threshold j (gatePrefix A.stratification j z) : ℝ) : ℂ)) τ :=
      Complex.continuous_ofReal.continuousAt.comp hthreshold_contR
    simpa [PolynomialNestedTailData.threshold, hfamily] using
      (PuncturedBoundedAt.of_continuousAt hthreshold_contC)
  levelSet_frequently := hlevel

/-- The leading coefficient limit supplied by the continuity fields of
`ScaledPropagationAnalyticData`. -/
theorem leadingCoeff_tendsto {m : Nat} {A : TierSystem m}
    (D : ScaledPropagationAnalyticData A) :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
        (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ))) := by
  intro j τ hj hτ
  exact ScaledPropagationPolynomialData.leadingCoeff_tendsto_of_continuousAt D.polynomial
    (D.gatePrefix_continuousAt hj hτ)
    (D.tailLeadingCoeff_continuousAt hj hτ)

/-- The quadratic blow-up field supplied by `ScaledPropagationAnalyticData`. -/
theorem phi_blowsUpAt_of_gate {m : Nat} {A : TierSystem m}
    (D : ScaledPropagationAnalyticData A) :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
      BlowsUpAt (A.stratification.s j) τ ->
      (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ) ≠ 0 ->
      Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
        (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ))) ->
      BlowsUpAt (tierPhiPath A j) τ := by
  intro j τ hj hτ hgate hlead hlead_tendsto
  exact phi_blowsUpAt_of_quadratic_threshold A
    (D.quadratic_degree hj hτ)
    (D.threshold_puncturedBounded hj hτ)
    hgate hlead hlead_tendsto

end ScaledPropagationAnalyticData

namespace ZeroFreeScaledPropagationAnalyticData

/-- Constructor for zero-free scaled analytic propagation data from a polynomial-backed
nested tail tower, with the level-set field supplied in the smaller form isolated by
`zeroFreeLevelSet_frequently_of_levelSetLead_frequently`.

The polynomial tower supplies the nested family, leading-coefficient continuity, and
openness of zero-free regions.  The remaining concrete analytic inputs are prefix
continuity at zero-free tier points, quadratic degree, and the hard level-set statement
producing frequent successor-stratum points where the next leading coefficient is
nonzero. -/
def ofPolynomialNestedTailData {m : Nat} {A : TierSystem m}
    (D : PolynomialNestedTailData)
    (hfamily : A.nestedFamily = D.toNestedTailFamily)
    (hH_scaled :
      ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T j ->
        A.stratification.H (j + 1) =ᶠ[puncturedNhds τ] scaledTierPhiPath A j)
    (hprefix :
      ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T0 j ->
        ContinuousAt (fun z => gatePrefix A.stratification j z) τ)
    (hdegree :
      ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T0 j ->
        (D.tailData j).presentation.degree = 2)
    (hlevelLead :
      ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T0 j ->
        (∀ᶠ z in puncturedNhds τ, z ∈ A.stratification.omega (j + 1)) ->
        BlowsUpAt (A.stratification.H (j + 1)) τ ->
        ∃ᶠ z in puncturedNhds τ,
          z ∈ A.stratification.S (j + 1)
            ∧ (A.nestedFamily.step (j + 1)).lead
              (gatePrefix A.stratification (j + 1) z) ≠ 0) :
    ZeroFreeScaledPropagationAnalyticData A where
  polynomial :=
    ScaledPropagationPolynomialData.ofPolynomialNestedTailData D hfamily hH_scaled
  gatePrefix_continuousAt := hprefix
  tailLeadingCoeff_continuousAt := by
    intro j τ hj hτ
    simpa [ScaledPropagationPolynomialData.ofPolynomialNestedTailData] using
      (D.lead_continuous j).continuousAt
  quadratic_degree := by
    intro j τ hj hτ
    simpa [hfamily] using hdegree hj hτ
  threshold_puncturedBounded := by
    intro j τ hj hτ
    have hτprefixA :
        gatePrefix A.stratification j τ ∈ A.nestedFamily.zeroFreeRegion j :=
      A.T0_mem_zeroFreeRegion hτ
    have hτprefixD :
        gatePrefix A.stratification j τ ∈ D.zeroFreeRegion j := by
      simpa [PolynomialNestedTailData.zeroFreeRegion, hfamily] using hτprefixA
    have hthreshold_contD :
        ContinuousAt (D.threshold j) (gatePrefix A.stratification j τ) :=
      (D.continuousOn_thresholds_zeroFreeRegion j).continuousAt
        ((D.isOpen_zeroFreeRegion j).mem_nhds hτprefixD)
    have hthreshold_contR :
        ContinuousAt
          (fun z : ℂ => D.threshold j (gatePrefix A.stratification j z)) τ :=
      hthreshold_contD.comp (hprefix hj hτ)
    have hthreshold_contC :
        ContinuousAt
          (fun z : ℂ =>
            ((D.threshold j (gatePrefix A.stratification j z) : ℝ) : ℂ)) τ :=
      Complex.continuous_ofReal.continuousAt.comp hthreshold_contR
    simpa [PolynomialNestedTailData.threshold, hfamily] using
      (PuncturedBoundedAt.of_continuousAt hthreshold_contC)
  levelSet_frequently := by
    intro j τ hj hτ hOmega hH
    have hthreshold :
        PuncturedBoundedAt
          (fun z : ℂ =>
            ((A.nestedFamily.threshold j (gatePrefix A.stratification j z) : ℝ) : ℂ)) τ := by
      have hτprefixA :
          gatePrefix A.stratification j τ ∈ A.nestedFamily.zeroFreeRegion j :=
        A.T0_mem_zeroFreeRegion hτ
      have hτprefixD :
          gatePrefix A.stratification j τ ∈ D.zeroFreeRegion j := by
        simpa [PolynomialNestedTailData.zeroFreeRegion, hfamily] using hτprefixA
      have hthreshold_contD :
          ContinuousAt (D.threshold j) (gatePrefix A.stratification j τ) :=
        (D.continuousOn_thresholds_zeroFreeRegion j).continuousAt
          ((D.isOpen_zeroFreeRegion j).mem_nhds hτprefixD)
      have hthreshold_contR :
          ContinuousAt
            (fun z : ℂ => D.threshold j (gatePrefix A.stratification j z)) τ :=
        hthreshold_contD.comp (hprefix hj hτ)
      have hthreshold_contC :
          ContinuousAt
            (fun z : ℂ =>
              ((D.threshold j (gatePrefix A.stratification j z) : ℝ) : ℂ)) τ :=
        Complex.continuous_ofReal.continuousAt.comp hthreshold_contR
      simpa [PolynomialNestedTailData.threshold, hfamily] using
        (PuncturedBoundedAt.of_continuousAt hthreshold_contC)
    refine zeroFreeLevelSet_frequently_of_levelSetLead_frequently
      A hj hτ (hprefix hj hτ) ?_ hthreshold ?_ hOmega hH
    · simpa [PolynomialNestedTailData.zeroFreeRegion, hfamily] using
        (D.isOpen_zeroFreeRegion j)
    · exact hlevelLead hj hτ

/-- The leading coefficient limit supplied by the continuity fields of
`ZeroFreeScaledPropagationAnalyticData`. -/
theorem leadingCoeff_tendsto {m : Nat} {A : TierSystem m}
    (D : ZeroFreeScaledPropagationAnalyticData A) :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T0 j ->
      Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
        (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ))) := by
  intro j τ hj hτ
  exact ScaledPropagationPolynomialData.leadingCoeff_tendsto_of_continuousAt D.polynomial
    (D.gatePrefix_continuousAt hj hτ)
    (D.tailLeadingCoeff_continuousAt hj hτ)

/-- The quadratic blow-up field supplied by `ZeroFreeScaledPropagationAnalyticData`. -/
theorem phi_blowsUpAt_of_gate {m : Nat} {A : TierSystem m}
    (D : ZeroFreeScaledPropagationAnalyticData A) :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T0 j ->
      BlowsUpAt (A.stratification.s j) τ ->
      (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ) ≠ 0 ->
      Filter.Tendsto (tierLeadingCoeffPath A j) (puncturedNhds τ)
        (nhds ((A.nestedFamily.step j).lead (gatePrefix A.stratification j τ))) ->
      BlowsUpAt (tierPhiPath A j) τ := by
  intro j τ hj hτ hgate hlead hlead_tendsto
  exact phi_blowsUpAt_of_quadratic_threshold A
    (D.quadratic_degree hj hτ)
    (D.threshold_puncturedBounded hj hτ)
    hgate hlead hlead_tendsto

/-- Compile analytic zero-free scaled propagation data into the zero-free bridge package. -/
def toZeroFreeScaledPropagationBridgeData {m : Nat} {A : TierSystem m}
    (D : ZeroFreeScaledPropagationAnalyticData A) : ZeroFreeScaledPropagationBridgeData A where
  polynomial := D.polynomial
  leadingCoeff_tendsto := ZeroFreeScaledPropagationAnalyticData.leadingCoeff_tendsto D
  phi_blowsUpAt_of_gate := ZeroFreeScaledPropagationAnalyticData.phi_blowsUpAt_of_gate D
  levelSet_frequently := D.levelSet_frequently

/-- Direct compilation from analytic zero-free scaled propagation data to the final
zero-free propagation chain. -/
def toZeroFreeTierPropagation {m : Nat} {A : TierSystem m}
    (D : ZeroFreeScaledPropagationAnalyticData A) : ZeroFreeTierPropagation A :=
  D.toZeroFreeScaledPropagationBridgeData.toZeroFreeTierPropagation

end ZeroFreeScaledPropagationAnalyticData

/-! ## Decoupled zero-free propagation -/

/-- Decoupled Claim-B data for a zero-free tier system.

This is the corrected Claim-B engine for a *combined* tier system whose nested family is a
different polynomial tower from the one that drives the gate preactivation `H`.

Unlike `ZeroFreeScaledPropagationAnalyticData`/`ZeroFreeScaledPropagationBridgeData`, it
does **not** require the scaled formal-phi identity
`H'_{j+1}(z) = z * φ'_{j+1}(z) + b` for this system's *own* nested step.  That identity is
false when `A.nestedFamily` is the combined propagation-visible product tower, whose step
polynomial is `f_{j+2} · g_{j+1}`, not the actual formal-phi preactivation.

Instead the blow-up of `H'_{j+1}` is supplied directly through `gateArgument_blowsUpAt`;
the intended source is the genuine formal-phi tier system that *shares this
stratification* (so `H`, `s`, `S`, `omega` agree), proved via its own scaled identity and
the formal-phi leading-coefficient nonvanishing extracted from the combined zero-free
region.  All membership/threshold bookkeeping then uses this system's combined nested
family. -/
structure ZeroFreeDecoupledPropagationData {m : Nat} (A : TierSystem m) where
  gateArgument_blowsUpAt :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T0 j ->
      BlowsUpAt (A.stratification.H (j + 1)) τ
  gatePrefix_continuousAt :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T0 j ->
      ContinuousAt (fun z => gatePrefix A.stratification j z) τ
  zeroFreeRegion_isOpen : ∀ j : Nat, IsOpen (A.nestedFamily.zeroFreeRegion j)
  threshold_puncturedBounded :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T0 j ->
      PuncturedBoundedAt
        (fun z : ℂ =>
          ((A.nestedFamily.threshold j (gatePrefix A.stratification j z) : ℝ) : ℂ)) τ
  levelSetLead_frequently :
    ∀ {j : Nat} {τ : ℂ}, j + 1 < m -> τ ∈ A.T0 j ->
      (∀ᶠ z in puncturedNhds τ, z ∈ A.stratification.omega (j + 1)) ->
      BlowsUpAt (A.stratification.H (j + 1)) τ ->
      ∃ᶠ z in puncturedNhds τ,
        z ∈ A.stratification.S (j + 1)
          ∧ (A.nestedFamily.step (j + 1)).lead
            (gatePrefix A.stratification (j + 1) z) ≠ 0

namespace ZeroFreeDecoupledPropagationData

variable {m : Nat} {A : TierSystem m} (D : ZeroFreeDecoupledPropagationData A)
include D

/-- The decoupled level-set step, rewritten as frequent membership in the successor
zero-free tier.  The successor membership is assembled by
`zeroFreeLevelSet_frequently_of_levelSetLead_frequently`: zero-free-region openness,
prefix continuity, threshold boundedness, and gate blow-up upgrade the bare level-set
output into the full `mem_T0_succ` shape. -/
theorem frequently_mem_T0_succ {j : Nat} {τ : ℂ} (hj : j + 1 < m)
    (hτ : τ ∈ A.T0 j) :
    ∃ᶠ z in puncturedNhds τ, z ∈ A.T0 (j + 1) := by
  have hjm : j < m := by omega
  have hOmega : ∀ᶠ z in puncturedNhds τ, z ∈ A.stratification.omega (j + 1) :=
    A.T0_punctured_omega_succ hjm hτ
  have hH : BlowsUpAt (A.stratification.H (j + 1)) τ :=
    D.gateArgument_blowsUpAt hj hτ
  have hLevel :=
    zeroFreeLevelSet_frequently_of_levelSetLead_frequently A hj hτ
      (D.gatePrefix_continuousAt hj hτ)
      (D.zeroFreeRegion_isOpen j)
      (D.threshold_puncturedBounded hj hτ)
      (D.levelSetLead_frequently hj hτ) hOmega hH
  exact hLevel.mono fun z hz => (A.mem_T0_succ (j := j) (τ := z)).mpr hz

/-- Claim B for one adjacent zero-free tier of a decoupled system. -/
theorem tier_subset_acc_succ (j : Nat) (hj : j + 1 < m) :
    A.T0 j ⊆ acc (A.T0 (j + 1)) := by
  intro τ hτ
  exact mem_acc_of_frequently_mem_punctured
    (D.frequently_mem_T0_succ hj hτ)

/-- The full zero-free propagation chain from decoupled Claim-B data. -/
theorem chain :
    ∀ j : Nat, j + 1 < m -> A.T0 j ⊆ acc (A.T0 (j + 1)) :=
  D.tier_subset_acc_succ

/-- Package the decoupled proof as a `ZeroFreeTierPropagation`. -/
def toZeroFreeTierPropagation : ZeroFreeTierPropagation A where
  chain := fun j hj => D.tier_subset_acc_succ j hj

end ZeroFreeDecoupledPropagationData

namespace TierPropagation

variable {m : Nat} {A : TierSystem m} (P : TierPropagation A)
include P

end TierPropagation

namespace ZeroFreeTierPropagation

variable {m : Nat} {A : TierSystem m} (P : ZeroFreeTierPropagation A)
include P

end ZeroFreeTierPropagation

end TransformerIdentifiability.NLayer
