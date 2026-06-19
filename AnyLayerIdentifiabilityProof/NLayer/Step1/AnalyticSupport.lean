import AnyLayerIdentifiabilityProof.NLayer.Analytic.AnalyticToolkit
import Mathlib.Analysis.Complex.OpenMapping

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Step 1 analytic support

Owner shard for Step 1-specific analytic helpers used by propagation and blow-up
arguments. Generic reusable lemmas can later be moved into `AnalyticToolkit.lean` by the
integration owner.
-/

/-! ## Punctured-neighborhood boundedness -/

/-- Short name for the punctured-neighborhood filter at a complex point. -/
noncomputable abbrev puncturedNhds (τ : ℂ) : Filter ℂ :=
  nhdsWithin τ ({τ}ᶜ : Set ℂ)

/-- If a function tends to a finite complex limit along punctured neighborhoods, it is
bounded along those punctured neighborhoods. -/
theorem PuncturedBoundedAt.of_tendsto {G : ℂ -> ℂ} {τ g0 : ℂ}
    (hG : Filter.Tendsto G (puncturedNhds τ) (nhds g0)) :
    PuncturedBoundedAt G τ := by
  refine ⟨‖g0‖ + 1, ?_⟩
  have hnorm : Filter.Tendsto (fun z => ‖G z‖) (puncturedNhds τ) (nhds ‖g0‖) := hG.norm
  have hlt : ‖g0‖ < ‖g0‖ + 1 := by linarith
  exact (hnorm.eventually (Iio_mem_nhds hlt)).mono fun _ hz => le_of_lt hz

/-- A function continuous at the center is bounded on punctured neighborhoods of the
center. -/
theorem PuncturedBoundedAt.of_continuousAt {G : ℂ -> ℂ} {τ : ℂ}
    (hG : ContinuousAt G τ) :
    PuncturedBoundedAt G τ :=
  PuncturedBoundedAt.of_tendsto (τ := τ) (g0 := G τ)
    (hG.tendsto.mono_left nhdsWithin_le_nhds)

/-- Constant functions are punctured-neighborhood bounded. -/
theorem PuncturedBoundedAt.const (c τ : ℂ) :
    PuncturedBoundedAt (fun _ : ℂ => c) τ := by
  refine ⟨‖c‖, ?_⟩
  filter_upwards with _z
  rfl

/-- Replace a punctured-neighborhood bounded function by an eventually equal one. -/
theorem PuncturedBoundedAt.congr {F G : ℂ -> ℂ} {τ : ℂ}
    (hF : PuncturedBoundedAt F τ)
    (hFG : F =ᶠ[puncturedNhds τ] G) :
    PuncturedBoundedAt G τ := by
  rcases hF with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  filter_upwards [hC, hFG] with z hCz hFGz
  simpa [← hFGz] using hCz

theorem PuncturedBoundedAt.neg {F : ℂ -> ℂ} {τ : ℂ}
    (hF : PuncturedBoundedAt F τ) :
    PuncturedBoundedAt (fun z => -F z) τ := by
  rcases hF with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  filter_upwards [hC] with z hCz
  simpa using hCz

theorem PuncturedBoundedAt.add {F G : ℂ -> ℂ} {τ : ℂ}
    (hF : PuncturedBoundedAt F τ)
    (hG : PuncturedBoundedAt G τ) :
    PuncturedBoundedAt (fun z => F z + G z) τ := by
  rcases hF with ⟨CF, hCF⟩
  rcases hG with ⟨CG, hCG⟩
  refine ⟨CF + CG, ?_⟩
  filter_upwards [hCF, hCG] with z hFz hGz
  calc
    ‖F z + G z‖ ≤ ‖F z‖ + ‖G z‖ := norm_add_le _ _
    _ ≤ CF + CG := add_le_add hFz hGz

theorem PuncturedBoundedAt.sub {F G : ℂ -> ℂ} {τ : ℂ}
    (hF : PuncturedBoundedAt F τ)
    (hG : PuncturedBoundedAt G τ) :
    PuncturedBoundedAt (fun z => F z - G z) τ := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

theorem PuncturedBoundedAt.mul {F G : ℂ -> ℂ} {τ : ℂ}
    (hF : PuncturedBoundedAt F τ)
    (hG : PuncturedBoundedAt G τ) :
    PuncturedBoundedAt (fun z => F z * G z) τ := by
  rcases hF with ⟨CF, hCF⟩
  rcases hG with ⟨CG, hCG⟩
  let BF : ℝ := max CF 0
  let BG : ℝ := max CG 0
  refine ⟨BF * BG, ?_⟩
  have hBF_nonneg : 0 ≤ BF := by
    dsimp [BF]
    exact le_max_right CF 0
  filter_upwards [hCF, hCG] with z hFz hGz
  have hFz' : ‖F z‖ ≤ BF := hFz.trans (by dsimp [BF]; exact le_max_left CF 0)
  have hGz' : ‖G z‖ ≤ BG := hGz.trans (by dsimp [BG]; exact le_max_left CG 0)
  rw [norm_mul]
  exact mul_le_mul hFz' hGz' (norm_nonneg _) hBF_nonneg

theorem PuncturedBoundedAt.const_mul {F : ℂ -> ℂ} {τ c : ℂ}
    (hF : PuncturedBoundedAt F τ) :
    PuncturedBoundedAt (fun z => c * F z) τ :=
  (PuncturedBoundedAt.const c τ).mul hF

theorem PuncturedBoundedAt.mul_const {F : ℂ -> ℂ} {τ c : ℂ}
    (hF : PuncturedBoundedAt F τ) :
    PuncturedBoundedAt (fun z => F z * c) τ :=
  hF.mul (PuncturedBoundedAt.const c τ)

/-- Finite sums of punctured-neighborhood bounded functions are bounded. -/
theorem PuncturedBoundedAt.finset_sum {ι : Type*} (s : Finset ι) {F : ι -> ℂ -> ℂ}
    {τ : ℂ} (hF : ∀ i, i ∈ s -> PuncturedBoundedAt (F i) τ) :
    PuncturedBoundedAt (fun z => ∑ i ∈ s, F i z) τ := by
  classical
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _hF
    simpa using PuncturedBoundedAt.const (0 : ℂ) τ
  · intro a s ha ih hF
    have ha_bound : PuncturedBoundedAt (F a) τ := hF a (Finset.mem_insert_self a s)
    have hs_bound : PuncturedBoundedAt (fun z => ∑ i ∈ s, F i z) τ := by
      exact ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    simpa [Finset.sum_insert ha] using ha_bound.add hs_bound

/-- Fintype version of finite-sum boundedness. -/
theorem PuncturedBoundedAt.fintype_sum {ι : Type*} [Fintype ι] {F : ι -> ℂ -> ℂ}
    {τ : ℂ} (hF : ∀ i, PuncturedBoundedAt (F i) τ) :
    PuncturedBoundedAt (fun z => ∑ i, F i z) τ := by
  classical
  simpa using
    PuncturedBoundedAt.finset_sum (Finset.univ : Finset ι) (τ := τ)
      (F := F) (fun i _hi => hF i)

/-! ## Finite-family boundedness and tendsto -/

/-- Finite products of punctured-neighborhood bounded functions are bounded. -/
theorem PuncturedBoundedAt.finset_prod {ι : Type*} (s : Finset ι) {F : ι -> ℂ -> ℂ}
    {τ : ℂ} (hF : ∀ i, i ∈ s -> PuncturedBoundedAt (F i) τ) :
    PuncturedBoundedAt (fun z => ∏ i ∈ s, F i z) τ := by
  classical
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _hF
    simpa using PuncturedBoundedAt.const (1 : ℂ) τ
  · intro a s ha ih hF
    have ha_bound : PuncturedBoundedAt (F a) τ := hF a (Finset.mem_insert_self a s)
    have hs_bound : PuncturedBoundedAt (fun z => ∏ i ∈ s, F i z) τ := by
      exact ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    simpa [Finset.prod_insert ha] using ha_bound.mul hs_bound

/-- Fintype version of finite-product boundedness. -/
theorem PuncturedBoundedAt.fintype_prod {ι : Type*} [Fintype ι] {F : ι -> ℂ -> ℂ}
    {τ : ℂ} (hF : ∀ i, PuncturedBoundedAt (F i) τ) :
    PuncturedBoundedAt (fun z => ∏ i, F i z) τ := by
  classical
  simpa using
    PuncturedBoundedAt.finset_prod (Finset.univ : Finset ι) (τ := τ)
      (F := F) (fun i _hi => hF i)

/-- Finite sums of functions with finite punctured limits are punctured-neighborhood
bounded. -/
theorem PuncturedBoundedAt.finset_sum_of_tendsto {ι : Type*} (s : Finset ι)
    {F : ι -> ℂ -> ℂ} {τ : ℂ} {a : ι -> ℂ}
    (hF : ∀ i, i ∈ s -> Filter.Tendsto (F i) (puncturedNhds τ) (nhds (a i))) :
    PuncturedBoundedAt (fun z => ∑ i ∈ s, F i z) τ :=
  PuncturedBoundedAt.finset_sum s fun i hi =>
    PuncturedBoundedAt.of_tendsto (hF i hi)

/-- Fintype version of finite-sum boundedness from finite punctured limits. -/
theorem PuncturedBoundedAt.fintype_sum_of_tendsto {ι : Type*} [Fintype ι]
    {F : ι -> ℂ -> ℂ} {τ : ℂ} {a : ι -> ℂ}
    (hF : ∀ i, Filter.Tendsto (F i) (puncturedNhds τ) (nhds (a i))) :
    PuncturedBoundedAt (fun z => ∑ i, F i z) τ := by
  classical
  simpa using
    PuncturedBoundedAt.finset_sum_of_tendsto (Finset.univ : Finset ι)
      (τ := τ) (F := F) (a := a) (fun i _hi => hF i)

/-- Finite products of functions with finite punctured limits are punctured-neighborhood
bounded. -/
theorem PuncturedBoundedAt.finset_prod_of_tendsto {ι : Type*} (s : Finset ι)
    {F : ι -> ℂ -> ℂ} {τ : ℂ} {a : ι -> ℂ}
    (hF : ∀ i, i ∈ s -> Filter.Tendsto (F i) (puncturedNhds τ) (nhds (a i))) :
    PuncturedBoundedAt (fun z => ∏ i ∈ s, F i z) τ :=
  PuncturedBoundedAt.finset_prod s fun i hi =>
    PuncturedBoundedAt.of_tendsto (hF i hi)

/-- Fintype version of finite-product boundedness from finite punctured limits. -/
theorem PuncturedBoundedAt.fintype_prod_of_tendsto {ι : Type*} [Fintype ι]
    {F : ι -> ℂ -> ℂ} {τ : ℂ} {a : ι -> ℂ}
    (hF : ∀ i, Filter.Tendsto (F i) (puncturedNhds τ) (nhds (a i))) :
    PuncturedBoundedAt (fun z => ∏ i, F i z) τ := by
  classical
  simpa using
    PuncturedBoundedAt.finset_prod_of_tendsto (Finset.univ : Finset ι)
      (τ := τ) (F := F) (a := a) (fun i _hi => hF i)

/-- Finite sums of functions continuous at the center are punctured-neighborhood
bounded. -/
theorem PuncturedBoundedAt.finset_sum_of_continuousAt {ι : Type*} (s : Finset ι)
    {F : ι -> ℂ -> ℂ} {τ : ℂ}
    (hF : ∀ i, i ∈ s -> ContinuousAt (F i) τ) :
    PuncturedBoundedAt (fun z => ∑ i ∈ s, F i z) τ :=
  PuncturedBoundedAt.finset_sum s fun i hi =>
    PuncturedBoundedAt.of_continuousAt (hF i hi)

/-- Fintype version of finite-sum boundedness from continuity at the center. -/
theorem PuncturedBoundedAt.fintype_sum_of_continuousAt {ι : Type*} [Fintype ι]
    {F : ι -> ℂ -> ℂ} {τ : ℂ}
    (hF : ∀ i, ContinuousAt (F i) τ) :
    PuncturedBoundedAt (fun z => ∑ i, F i z) τ := by
  classical
  simpa using
    PuncturedBoundedAt.finset_sum_of_continuousAt (Finset.univ : Finset ι)
      (τ := τ) (F := F) (fun i _hi => hF i)

/-- Finite products of functions continuous at the center are punctured-neighborhood
bounded. -/
theorem PuncturedBoundedAt.finset_prod_of_continuousAt {ι : Type*} (s : Finset ι)
    {F : ι -> ℂ -> ℂ} {τ : ℂ}
    (hF : ∀ i, i ∈ s -> ContinuousAt (F i) τ) :
    PuncturedBoundedAt (fun z => ∏ i ∈ s, F i z) τ :=
  PuncturedBoundedAt.finset_prod s fun i hi =>
    PuncturedBoundedAt.of_continuousAt (hF i hi)

/-- Fintype version of finite-product boundedness from continuity at the center. -/
theorem PuncturedBoundedAt.fintype_prod_of_continuousAt {ι : Type*} [Fintype ι]
    {F : ι -> ℂ -> ℂ} {τ : ℂ}
    (hF : ∀ i, ContinuousAt (F i) τ) :
    PuncturedBoundedAt (fun z => ∏ i, F i z) τ := by
  classical
  simpa using
    PuncturedBoundedAt.finset_prod_of_continuousAt (Finset.univ : Finset ι)
      (τ := τ) (F := F) (fun i _hi => hF i)

/-- Finite sums of products are bounded when the left factors are continuous and the
right factors are punctured-neighborhood bounded. -/
theorem PuncturedBoundedAt.finset_sum_mul_of_left_continuousAt {ι : Type*}
    (s : Finset ι) {F G : ι -> ℂ -> ℂ} {τ : ℂ}
    (hF : ∀ i, i ∈ s -> ContinuousAt (F i) τ)
    (hG : ∀ i, i ∈ s -> PuncturedBoundedAt (G i) τ) :
    PuncturedBoundedAt (fun z => ∑ i ∈ s, F i z * G i z) τ :=
  PuncturedBoundedAt.finset_sum s fun i hi =>
    (PuncturedBoundedAt.of_continuousAt (hF i hi)).mul (hG i hi)

/-- Finite sums of products are bounded when the left factors are punctured-neighborhood
bounded and the right factors are continuous. -/
theorem PuncturedBoundedAt.finset_sum_mul_of_right_continuousAt {ι : Type*}
    (s : Finset ι) {F G : ι -> ℂ -> ℂ} {τ : ℂ}
    (hF : ∀ i, i ∈ s -> PuncturedBoundedAt (F i) τ)
    (hG : ∀ i, i ∈ s -> ContinuousAt (G i) τ) :
    PuncturedBoundedAt (fun z => ∑ i ∈ s, F i z * G i z) τ :=
  PuncturedBoundedAt.finset_sum s fun i hi =>
    (hF i hi).mul (PuncturedBoundedAt.of_continuousAt (hG i hi))

/-- Fintype version of bounded finite sums of products with continuous left factors. -/
theorem PuncturedBoundedAt.fintype_sum_mul_of_left_continuousAt {ι : Type*}
    [Fintype ι] {F G : ι -> ℂ -> ℂ} {τ : ℂ}
    (hF : ∀ i, ContinuousAt (F i) τ)
    (hG : ∀ i, PuncturedBoundedAt (G i) τ) :
    PuncturedBoundedAt (fun z => ∑ i, F i z * G i z) τ := by
  classical
  simpa using
    PuncturedBoundedAt.finset_sum_mul_of_left_continuousAt
      (Finset.univ : Finset ι) (τ := τ) (F := F) (G := G)
      (fun i _hi => hF i) (fun i _hi => hG i)

/-- Fintype version of bounded finite sums of products with continuous right factors. -/
theorem PuncturedBoundedAt.fintype_sum_mul_of_right_continuousAt {ι : Type*}
    [Fintype ι] {F G : ι -> ℂ -> ℂ} {τ : ℂ}
    (hF : ∀ i, PuncturedBoundedAt (F i) τ)
    (hG : ∀ i, ContinuousAt (G i) τ) :
    PuncturedBoundedAt (fun z => ∑ i, F i z * G i z) τ := by
  classical
  simpa using
    PuncturedBoundedAt.finset_sum_mul_of_right_continuousAt
      (Finset.univ : Finset ι) (τ := τ) (F := F) (G := G)
      (fun i _hi => hF i) (fun i _hi => hG i)

/-- Punctured-neighborhood tendsto for finite sums. -/
theorem tendsto_punctured_finset_sum {ι : Type*} (s : Finset ι)
    {F : ι -> ℂ -> ℂ} {τ : ℂ} {a : ι -> ℂ}
    (hF : ∀ i, i ∈ s -> Filter.Tendsto (F i) (puncturedNhds τ) (nhds (a i))) :
    Filter.Tendsto (fun z => ∑ i ∈ s, F i z) (puncturedNhds τ)
      (nhds (∑ i ∈ s, a i)) := by
  simpa using tendsto_finsetSum s hF

/-- Punctured-neighborhood tendsto for finite products. -/
theorem tendsto_punctured_finset_prod {ι : Type*} (s : Finset ι)
    {F : ι -> ℂ -> ℂ} {τ : ℂ} {a : ι -> ℂ}
    (hF : ∀ i, i ∈ s -> Filter.Tendsto (F i) (puncturedNhds τ) (nhds (a i))) :
    Filter.Tendsto (fun z => ∏ i ∈ s, F i z) (puncturedNhds τ)
      (nhds (∏ i ∈ s, a i)) := by
  simpa using tendsto_finsetProd s hF

/-- Fintype version of punctured-neighborhood tendsto for finite sums. -/
theorem tendsto_punctured_fintype_sum {ι : Type*} [Fintype ι]
    {F : ι -> ℂ -> ℂ} {τ : ℂ} {a : ι -> ℂ}
    (hF : ∀ i, Filter.Tendsto (F i) (puncturedNhds τ) (nhds (a i))) :
    Filter.Tendsto (fun z => ∑ i, F i z) (puncturedNhds τ)
      (nhds (∑ i, a i)) := by
  classical
  simpa using
    tendsto_punctured_finset_sum (Finset.univ : Finset ι)
      (τ := τ) (F := F) (a := a) (fun i _hi => hF i)

/-- Fintype version of punctured-neighborhood tendsto for finite products. -/
theorem tendsto_punctured_fintype_prod {ι : Type*} [Fintype ι]
    {F : ι -> ℂ -> ℂ} {τ : ℂ} {a : ι -> ℂ}
    (hF : ∀ i, Filter.Tendsto (F i) (puncturedNhds τ) (nhds (a i))) :
    Filter.Tendsto (fun z => ∏ i, F i z) (puncturedNhds τ)
      (nhds (∏ i, a i)) := by
  classical
  simpa using
    tendsto_punctured_finset_prod (Finset.univ : Finset ι)
      (τ := τ) (F := F) (a := a) (fun i _hi => hF i)

/-- Punctured-neighborhood tendsto for finite sums of functions continuous at the
center. -/
theorem tendsto_punctured_finset_sum_of_continuousAt {ι : Type*} (s : Finset ι)
    {F : ι -> ℂ -> ℂ} {τ : ℂ}
    (hF : ∀ i, i ∈ s -> ContinuousAt (F i) τ) :
    Filter.Tendsto (fun z => ∑ i ∈ s, F i z) (puncturedNhds τ)
      (nhds (∑ i ∈ s, F i τ)) := by
  refine tendsto_punctured_finset_sum s ?_
  intro i hi
  exact (hF i hi).tendsto.mono_left nhdsWithin_le_nhds

/-- Punctured-neighborhood tendsto for finite products of functions continuous at the
center. -/
theorem tendsto_punctured_finset_prod_of_continuousAt {ι : Type*} (s : Finset ι)
    {F : ι -> ℂ -> ℂ} {τ : ℂ}
    (hF : ∀ i, i ∈ s -> ContinuousAt (F i) τ) :
    Filter.Tendsto (fun z => ∏ i ∈ s, F i z) (puncturedNhds τ)
      (nhds (∏ i ∈ s, F i τ)) := by
  refine tendsto_punctured_finset_prod s ?_
  intro i hi
  exact (hF i hi).tendsto.mono_left nhdsWithin_le_nhds

/-- Fintype version of punctured-neighborhood tendsto for sums of functions continuous
at the center. -/
theorem tendsto_punctured_fintype_sum_of_continuousAt {ι : Type*} [Fintype ι]
    {F : ι -> ℂ -> ℂ} {τ : ℂ}
    (hF : ∀ i, ContinuousAt (F i) τ) :
    Filter.Tendsto (fun z => ∑ i, F i z) (puncturedNhds τ)
      (nhds (∑ i, F i τ)) := by
  classical
  simpa using
    tendsto_punctured_finset_sum_of_continuousAt (Finset.univ : Finset ι)
      (τ := τ) (F := F) (fun i _hi => hF i)

/-- Fintype version of punctured-neighborhood tendsto for products of functions
continuous at the center. -/
theorem tendsto_punctured_fintype_prod_of_continuousAt {ι : Type*} [Fintype ι]
    {F : ι -> ℂ -> ℂ} {τ : ℂ}
    (hF : ∀ i, ContinuousAt (F i) τ) :
    Filter.Tendsto (fun z => ∏ i, F i z) (puncturedNhds τ)
      (nhds (∏ i, F i τ)) := by
  classical
  simpa using
    tendsto_punctured_finset_prod_of_continuousAt (Finset.univ : Finset ι)
      (τ := τ) (F := F) (fun i _hi => hF i)

/-! ## Real-tail frequent equality -/

/-- If two complex functions agree on all sufficiently large real points, then they agree
frequently in the punctured complex neighborhood of any real point strictly inside that
tail.  This is the local input expected by the countable-complement identity theorem. -/
theorem frequently_eq_punctured_of_forall_real_tail_eq {F G : ℂ -> ℂ} {T0 t0 : ℝ}
    (ht0 : T0 < t0)
    (hFG : ∀ t : ℝ, T0 < t -> F (t : ℂ) = G (t : ℂ)) :
    ∃ᶠ z in puncturedNhds (t0 : ℂ), F z = G z := by
  let seq : Nat -> ℂ := fun n => ((t0 + (1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hsmall : Filter.Tendsto (fun n : Nat => (1 : ℝ) / ((n : ℝ) + 1))
      Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hreal : Filter.Tendsto (fun n : Nat => t0 + (1 : ℝ) / ((n : ℝ) + 1))
      Filter.atTop (nhds t0) := by
    simpa using tendsto_const_nhds.add hsmall
  have hseq_nhds : Filter.Tendsto seq Filter.atTop (nhds (t0 : ℂ)) := by
    change Filter.Tendsto
      (fun n : Nat => ((t0 + (1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ))
      Filter.atTop (nhds (t0 : ℂ))
    exact (Complex.continuous_ofReal.tendsto t0).comp hreal
  have hseq_ne : ∀ᶠ n in Filter.atTop, seq n ∈ ({(t0 : ℂ)}ᶜ : Set ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro n hneq
    have hreal_eq : t0 + (1 : ℝ) / ((n : ℝ) + 1) = t0 := by
      exact Complex.ofReal_inj.mp hneq
    have hpos : (0 : ℝ) < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have hseq : Filter.Tendsto seq Filter.atTop (puncturedNhds (t0 : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within seq hseq_nhds hseq_ne
  refine hseq.frequently ?_
  refine Filter.Eventually.frequently ?_
  refine Filter.Eventually.of_forall ?_
  intro n
  have htail : T0 < t0 + (1 : ℝ) / ((n : ℝ) + 1) := by
    have hpos : (0 : ℝ) < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  simpa [seq] using hFG (t0 + (1 : ℝ) / ((n : ℝ) + 1)) htail

/-! ## Punctured pole preimages -/

/-- A concrete sequence of positive-indexed points in `oddPiI`. -/
noncomputable def oddPiISeq (n : Nat) : ℂ :=
  (2 * ((n : ℤ) : ℂ) + 1) * (Real.pi : ℂ) * Complex.I

theorem oddPiISeq_mem (n : Nat) : oddPiISeq n ∈ oddPiI := by
  refine ⟨(n : ℤ), ?_⟩
  simp [oddPiISeq]

theorem oddPiISeq_ne_zero (n : Nat) : oddPiISeq n ≠ 0 := by
  intro h
  have hre := congrArg Complex.im h
  have hpos : (0 : ℝ) < (2 * (n : ℝ) + 1) * Real.pi := by positivity
  simp [oddPiISeq] at hre
  linarith

/-- The inverses of positive-indexed odd multiples of `π i` accumulate at `0`. -/
theorem oddPiISeq_inv_tendsto_zero :
    Filter.Tendsto (fun n : Nat => (oddPiISeq n)⁻¹) Filter.atTop (nhds 0) := by
  have hreal :
      Filter.Tendsto (fun n : Nat => (((2 : ℝ) * (n : ℝ) + 1) * Real.pi)⁻¹)
        Filter.atTop (nhds 0) := by
    have hlin : Filter.Tendsto (fun n : Nat => (2 : ℝ) * (n : ℝ) + 1)
        Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop]
      intro a
      rw [Filter.eventually_atTop]
      obtain ⟨N, hN⟩ := exists_nat_gt a
      refine ⟨N, ?_⟩
      intro n hn
      have hN_le_n : (N : ℝ) <= n := by exact_mod_cast hn
      have hn_nonneg : (0 : ℝ) <= n := by exact_mod_cast Nat.zero_le n
      nlinarith [le_of_lt hN, hN_le_n, hn_nonneg]
    have hpi : Filter.Tendsto (fun n : Nat => ((2 : ℝ) * (n : ℝ) + 1) * Real.pi)
        Filter.atTop Filter.atTop := by
      exact hlin.atTop_mul_const Real.pi_pos
    exact tendsto_inv_atTop_zero.comp hpi
  have hcomplex :
      Filter.Tendsto
        (fun n : Nat => (((((2 : ℝ) * (n : ℝ) + 1) * Real.pi)⁻¹ : ℝ) : ℂ))
        Filter.atTop (nhds 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp hreal
  have hmul :
      Filter.Tendsto
        (fun n : Nat => (((((2 : ℝ) * (n : ℝ) + 1) * Real.pi)⁻¹ : ℝ) : ℂ) *
          (-Complex.I))
        Filter.atTop (nhds 0) := by
    have hmul0 :
        Filter.Tendsto
          (fun n : Nat => (((((2 : ℝ) * (n : ℝ) + 1) * Real.pi)⁻¹ : ℝ) : ℂ) *
            (-Complex.I))
          Filter.atTop (nhds (0 * (-Complex.I))) :=
      hcomplex.mul tendsto_const_nhds
    simpa using hmul0
  refine hmul.congr' ?_
  filter_upwards with n
  simp [oddPiISeq]
  field_simp [Real.pi_ne_zero]

/-- Pole-preimage lemma for a holomorphic reciprocal normal form.

If `R` is analytic at `τ`, vanishes nontrivially at `τ`, and is a reciprocal for `H`
away from `τ`, then `H` hits the sigmoid pole set `oddPiI` frequently in punctured
neighborhoods of `τ`.  This is the local analytic source needed by the regular-pole
preimage branch once a concrete preactivation has been put in reciprocal pole normal
form. -/
theorem frequently_mem_oddPiI_of_analyticAt_reciprocal
    {H R : ℂ -> ℂ} {τ : ℂ}
    (hR : AnalyticAt ℂ R τ)
    (hRτ : R τ = 0)
    (hRnonconst : ¬ ∀ᶠ z in nhds τ, R z = R τ)
    (hrecip : ∀ z, z ≠ τ -> R z * H z = 1) :
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
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within z hz_tendsto_nhds hz_eventually_ne
  refine hz_tendsto.frequently ?_
  refine (Filter.Eventually.of_forall ?_).frequently
  intro n
  have hmul : R (z n) * H (z n) = 1 := hrecip (z n) (hz_ne n)
  have hRz : R (z n) = (oddPiISeq (k n))⁻¹ := (hz n).2
  have hHz : H (z n) = oddPiISeq (k n) := by
    rw [hRz] at hmul
    field_simp [oddPiISeq_ne_zero (k n)] at hmul
    exact hmul
  rw [hHz]
  exact oddPiISeq_mem (k n)

/-! ## Nonzero limits and blow-up interfaces -/

/-- A complex-valued function tending to a nonzero limit is eventually nonzero. -/
theorem eventually_ne_zero_of_tendsto_nhds_ne_zero {α : Type*} {l : Filter α}
    {G : α -> ℂ} {g0 : ℂ}
    (hG : Filter.Tendsto G l (nhds g0)) (hg0 : g0 ≠ 0) :
    ∀ᶠ x in l, G x ≠ 0 := by
  have hnhds : ({0}ᶜ : Set ℂ) ∈ nhds g0 := isClosed_singleton.isOpen_compl.mem_nhds hg0
  exact (hG.eventually hnhds).mono fun _ hx => hx

/-- Punctured-neighborhood specialization of eventual nonvanishing from a nonzero limit. -/
theorem eventually_ne_zero_at_punctured_of_tendsto_ne_zero {G : ℂ -> ℂ} {τ g0 : ℂ}
    (hG : Filter.Tendsto G (puncturedNhds τ) (nhds g0)) (hg0 : g0 ≠ 0) :
    ∀ᶠ z in puncturedNhds τ, G z ≠ 0 :=
  eventually_ne_zero_of_tendsto_nhds_ne_zero hG hg0

/-- Multiplication on the left by a factor tending to a nonzero limit preserves blow-up. -/
theorem BlowsUpAt.tendsto_ne_zero_mul {A G : ℂ -> ℂ} {τ g0 : ℂ}
    (hA : BlowsUpAt A τ)
    (hG : Filter.Tendsto G (puncturedNhds τ) (nhds g0))
    (hg0 : g0 ≠ 0) :
    BlowsUpAt (fun z => G z * A z) τ := by
  simpa [mul_comm] using hA.mul_tendsto_ne_zero hG hg0

/-- A function that blows up still blows up after multiplying it by itself. -/
theorem BlowsUpAt.mul_self {A : ℂ -> ℂ} {τ : ℂ}
    (hA : BlowsUpAt A τ) :
    BlowsUpAt (fun z => A z * A z) τ := by
  rw [BlowsUpAt] at hA ⊢
  rw [Filter.tendsto_atTop] at hA ⊢
  intro M
  let R : ℝ := max M 1
  filter_upwards [hA R] with z hz
  have hR_M : M ≤ R := by
    dsimp [R]
    exact le_max_left M 1
  have hR_one : 1 ≤ R := by
    dsimp [R]
    exact le_max_right M 1
  have hM_norm : M ≤ ‖A z‖ := hR_M.trans hz
  have hone_norm : 1 ≤ ‖A z‖ := hR_one.trans hz
  rw [norm_mul]
  nlinarith [norm_nonneg (A z)]

/-- The leading quadratic term in Claim B blows up when the gate blows up and its
coefficient tends to a nonzero limit. -/
theorem BlowsUpAt.coeff_mul_self_of_tendsto_ne_zero {A coeff : ℂ -> ℂ} {τ coeff0 : ℂ}
    (hA : BlowsUpAt A τ)
    (hcoeff : Filter.Tendsto coeff (puncturedNhds τ) (nhds coeff0))
    (hcoeff0 : coeff0 ≠ 0) :
    BlowsUpAt (fun z => coeff z * (A z * A z)) τ := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    hA.mul_self.mul_tendsto_ne_zero hcoeff hcoeff0

/-- Dominance interface for Claim B: if a leading term eventually dominates the norm of
the remainder by an arbitrary margin, then their sum blows up. -/
theorem BlowsUpAt.add_of_eventually_norm_add_le {A R : ℂ -> ℂ} {τ : ℂ}
    (hdom : ∀ M : ℝ, ∀ᶠ z in puncturedNhds τ, M + ‖R z‖ ≤ ‖A z‖) :
    BlowsUpAt (fun z => A z + R z) τ := by
  rw [BlowsUpAt]
  rw [Filter.tendsto_atTop]
  intro M
  filter_upwards [hdom M] with z hz
  have htri : ‖A z‖ ≤ ‖A z + R z‖ + ‖R z‖ := by
    calc
      ‖A z‖ = ‖(A z + R z) - R z‖ := by ring_nf
      _ ≤ ‖A z + R z‖ + ‖R z‖ := norm_sub_le _ _
  linarith

end TransformerIdentifiability.NLayer
