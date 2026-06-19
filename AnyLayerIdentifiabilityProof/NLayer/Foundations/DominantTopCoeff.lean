import Mathlib

set_option autoImplicit false
-- Several lemmas do not need every ambient `[Fintype σ]`/`[DecidableEq σ]` in their type
-- (those instances are used in the proofs or by sibling lemmas); silence the style linters
-- that only inspect statement types.
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open MvPolynomial

namespace TransformerIdentifiability.NLayer

/-!
# Dominant top coefficients (`def:dtc`) and product closure (`lem:nested`, Step 0)

Self-contained foundation file (depends only on Mathlib; imported by no other module
yet).  This is the scoped first deliverable toward `n_layer_proof.tex`, Lemma
`lem:nested` ("Nested largeness with continuous thresholds").

A multivariate polynomial `p ∈ R[z_i : i ∈ σ]` has a *dominant top coefficient* when the
coefficient of the monomial `∏_i z_i^{deg_{z_i} p}` is nonzero (`def:dtc`).  The main
result here is **Step 0** of `lem:nested`: over an integral domain, a product of
polynomials with dominant top coefficients again has a dominant top coefficient, and the
top coefficients multiply.  Consequently `P := ∏_a p_a` has a dominant top coefficient.

The remaining steps of `lem:nested` (iterated leading coefficients and the construction
of the nested regions with continuous thresholds) build on this.
-/

variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {R : Type*} [CommRing R]

/-- The top exponent vector of `p`: the monomial `∏_i z_i^{deg_{z_i} p}`, recorded as the
finitely-supported degree map `i ↦ deg_{z_i} p`. -/
noncomputable def topMonomial (p : MvPolynomial σ R) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => p.degreeOf i

@[simp] theorem topMonomial_apply (p : MvPolynomial σ R) (i : σ) :
    topMonomial p i = p.degreeOf i :=
  Finsupp.equivFunOnFinite_symm_apply_apply _ i

/-- `p` has a *dominant top coefficient* (`def:dtc`): the coefficient of
`∏_i z_i^{deg_{z_i} p}` is nonzero. -/
def HasDominantTopCoeff (p : MvPolynomial σ R) : Prop :=
  p.coeff (topMonomial p) ≠ 0

/-- Every exponent vector occurring in `p` is `≤` the top exponent vector, componentwise. -/
theorem le_topMonomial_of_mem_support {p : MvPolynomial σ R} {m : σ →₀ ℕ}
    (hm : m ∈ p.support) (i : σ) : m i ≤ topMonomial p i := by
  rw [topMonomial_apply]; exact le_degreeOf_of_mem_support i hm

/-- The support of `p` lies below its top monomial, componentwise. -/
theorem support_subset_Iic_topMonomial (p : MvPolynomial σ R) :
    ↑p.support ⊆ Set.Iic (topMonomial p) := by
  intro m hm i
  exact le_topMonomial_of_mem_support hm i

/-- A monomial strictly outside the top degree box is not in the support. -/
theorem notMem_support_of_not_le_topMonomial {p : MvPolynomial σ R} {m : σ →₀ ℕ}
    (hm : ¬ m ≤ topMonomial p) : m ∉ p.support := by
  intro hmem
  exact hm fun i => le_topMonomial_of_mem_support hmem i

/-- Coefficients outside the top degree box vanish. -/
theorem coeff_eq_zero_of_not_le_topMonomial {p : MvPolynomial σ R} {m : σ →₀ ℕ}
    (hm : ¬ m ≤ topMonomial p) : p.coeff m = 0 := by
  exact notMem_support_iff.mp (notMem_support_of_not_le_topMonomial hm)

/-- If a support monomial is componentwise at least the top monomial, it is the top monomial. -/
theorem eq_topMonomial_of_mem_support_of_topMonomial_le {p : MvPolynomial σ R}
    {m : σ →₀ ℕ} (hm : m ∈ p.support) (hle : topMonomial p ≤ m) :
    m = topMonomial p :=
  le_antisymm (fun i => le_topMonomial_of_mem_support hm i) hle

/-- Dominant top coefficient is exactly membership of `topMonomial p` in the support. -/
theorem hasDominantTopCoeff_iff_topMonomial_mem_support {p : MvPolynomial σ R} :
    HasDominantTopCoeff p ↔ topMonomial p ∈ p.support :=
  Iff.symm mem_support_iff

/-- The top monomial of a polynomial with dominant top coefficient lies in its support. -/
theorem topMonomial_mem_support {p : MvPolynomial σ R} (hp : HasDominantTopCoeff p) :
    topMonomial p ∈ p.support :=
  hasDominantTopCoeff_iff_topMonomial_mem_support.mp hp

/-- Accessor for the nonzero coefficient in a dominant-top-coefficient hypothesis. -/
theorem HasDominantTopCoeff.coeff_topMonomial_ne {p : MvPolynomial σ R}
    (hp : HasDominantTopCoeff p) :
    p.coeff (topMonomial p) ≠ 0 :=
  hp

/-- A polynomial with a dominant top coefficient is nonzero. -/
theorem HasDominantTopCoeff.ne_zero {p : MvPolynomial σ R} (hp : HasDominantTopCoeff p) :
    p ≠ 0 := by
  rintro rfl
  exact hp (MvPolynomial.coeff_zero _)

/-- If a displayed monomial has nonzero coefficient and all per-variable degrees are
bounded by it, then it is the top monomial. -/
theorem topMonomial_eq_of_coeff_ne_of_degreeOf_le {p : MvPolynomial σ R}
    {m : σ →₀ ℕ}
    (hm : p.coeff m ≠ 0)
    (hle : ∀ i : σ, p.degreeOf i ≤ m i) :
    topMonomial p = m := by
  ext i
  apply le_antisymm
  · simpa [topMonomial_apply] using hle i
  · have hmem : m ∈ p.support := mem_support_iff.mpr hm
    have hdeg := le_degreeOf_of_mem_support i hmem
    simpa [topMonomial_apply] using hdeg

/-- Certify dominant top coefficient from a displayed top monomial, its nonzero
coefficient, and matching per-variable degree bounds. -/
theorem hasDominantTopCoeff_of_coeff_ne_of_degreeOf_le {p : MvPolynomial σ R}
    {m : σ →₀ ℕ}
    (hm : p.coeff m ≠ 0)
    (hle : ∀ i : σ, p.degreeOf i ≤ m i) :
    HasDominantTopCoeff p := by
  have htop := topMonomial_eq_of_coeff_ne_of_degreeOf_le (p := p) hm hle
  simpa [HasDominantTopCoeff, htop] using hm

/-- If a displayed monomial has nonzero coefficient and the whole support lies below it,
then it is the top monomial. -/
theorem topMonomial_eq_of_coeff_ne_of_support_subset_Iic {p : MvPolynomial σ R}
    {m : σ →₀ ℕ}
    (hm : p.coeff m ≠ 0)
    (hle : ↑p.support ⊆ Set.Iic m) :
    topMonomial p = m :=
  topMonomial_eq_of_coeff_ne_of_degreeOf_le (p := p) hm fun i => by
    rw [degreeOf_le_iff]
    intro n hn
    exact hle hn i

/-- Support-bounded version of `hasDominantTopCoeff_of_coeff_ne_of_degreeOf_le`. -/
theorem hasDominantTopCoeff_of_coeff_ne_of_support_subset_Iic {p : MvPolynomial σ R}
    {m : σ →₀ ℕ}
    (hm : p.coeff m ≠ 0)
    (hle : ↑p.support ⊆ Set.Iic m) :
    HasDominantTopCoeff p := by
  have htop := topMonomial_eq_of_coeff_ne_of_support_subset_Iic (p := p) hm hle
  simpa [HasDominantTopCoeff, htop] using hm

/-- The constant polynomial `C a` has a dominant top coefficient iff `a ≠ 0`. -/
theorem hasDominantTopCoeff_C {a : R} (ha : a ≠ 0) :
    HasDominantTopCoeff (C a : MvPolynomial σ R) := by
  have htop : topMonomial (C a : MvPolynomial σ R) = 0 := by
    ext i; simp [degreeOf_C]
  unfold HasDominantTopCoeff
  rw [htop]
  simpa using ha

/-- `1` has a dominant top coefficient. -/
theorem hasDominantTopCoeff_one [Nontrivial R] :
    HasDominantTopCoeff (1 : MvPolynomial σ R) := by
  have h := hasDominantTopCoeff_C (σ := σ) (R := R) (a := (1 : R)) one_ne_zero
  rwa [map_one] at h

variable {τ : Type*}

/-- Renaming into a larger variable type has degree zero at variables outside the image. -/
theorem degreeOf_rename_eq_zero_of_not_mem_range [DecidableEq τ] {p : MvPolynomial σ R}
    {f : σ → τ} (hf : Function.Injective f) {j : τ} (hj : j ∉ Set.range f) :
    (rename f p).degreeOf j = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [degreeOf_le_iff]
  intro m hm
  rw [support_rename_of_injective hf] at hm
  rcases Finset.mem_image.mp hm with ⟨u, _hu, rfl⟩
  exact Nat.le_of_eq (Finsupp.mapDomain_notin_range u j hj)

/-- The top monomial is functorial for injective variable renamings. -/
theorem topMonomial_rename_of_injective [Fintype τ] [DecidableEq τ] {p : MvPolynomial σ R}
    {f : σ → τ} (hf : Function.Injective f) :
    topMonomial (rename f p) = (topMonomial p).mapDomain f := by
  ext j
  rw [topMonomial_apply]
  by_cases hj : j ∈ Set.range f
  · rcases hj with ⟨i, rfl⟩
    rw [degreeOf_rename_of_injective hf, Finsupp.mapDomain_apply hf, topMonomial_apply]
  · rw [degreeOf_rename_eq_zero_of_not_mem_range (p := p) hf hj,
      Finsupp.mapDomain_notin_range (topMonomial p) j hj]

/-- The top coefficient is preserved by injective variable renaming. -/
theorem coeff_topMonomial_rename_of_injective [Fintype τ] [DecidableEq τ]
    {p : MvPolynomial σ R} {f : σ → τ} (hf : Function.Injective f) :
    (rename f p).coeff (topMonomial (rename f p)) = p.coeff (topMonomial p) := by
  rw [topMonomial_rename_of_injective (p := p) hf]
  exact coeff_rename_mapDomain f hf p (topMonomial p)

/-- Dominant top coefficient is preserved and reflected by injective variable renaming. -/
theorem hasDominantTopCoeff_rename_iff_of_injective [Fintype τ] [DecidableEq τ]
    {p : MvPolynomial σ R} {f : σ → τ} (hf : Function.Injective f) :
    HasDominantTopCoeff (rename f p) ↔ HasDominantTopCoeff p := by
  unfold HasDominantTopCoeff
  rw [topMonomial_rename_of_injective (p := p) hf,
    coeff_rename_mapDomain f hf p (topMonomial p)]

/-- Dominant top coefficient is preserved by injective variable renaming. -/
theorem HasDominantTopCoeff.rename_of_injective [Fintype τ] [DecidableEq τ]
    {p : MvPolynomial σ R} {f : σ → τ} (hp : HasDominantTopCoeff p)
    (hf : Function.Injective f) :
    HasDominantTopCoeff (rename f p) :=
  (hasDominantTopCoeff_rename_iff_of_injective (p := p) hf).mpr hp

/-- Dominant top coefficient is reflected by injective variable renaming. -/
theorem HasDominantTopCoeff.of_rename_of_injective [Fintype τ] [DecidableEq τ]
    {p : MvPolynomial σ R} {f : σ → τ}
    (hp : HasDominantTopCoeff (rename f p)) (hf : Function.Injective f) :
    HasDominantTopCoeff p :=
  (hasDominantTopCoeff_rename_iff_of_injective (p := p) hf).mp hp

/-- Rebuild the option-index top monomial from its `some` projection and `none` degree. -/
theorem topMonomial_optionElim_some_degreeOf_none (p : MvPolynomial (Option σ) R) :
    (topMonomial p).some.optionElim (p.degreeOf (none : Option σ)) = topMonomial p := by
  ext i
  cases i with
  | none => simp [topMonomial_apply]
  | some i => simp [topMonomial_apply]

/-- Rebuild the `Fin (n+1)` top monomial from its tail and zero-th degree. -/
theorem topMonomial_cons_tail_degreeOf_zero {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) R) :
    Finsupp.cons (p.degreeOf 0) (topMonomial p).tail = topMonomial p := by
  simpa [topMonomial_apply] using (Finsupp.cons_tail (t := topMonomial p))

/-- The leading coefficient, viewed via `optionEquivLeft`, is the coefficient at
`degreeOf none`. -/
theorem leadingCoeff_optionEquivLeft_eq_coeff_degreeOf_none
    (p : MvPolynomial (Option σ) R) :
    (optionEquivLeft R σ p).leadingCoeff =
      (optionEquivLeft R σ p).coeff (p.degreeOf (none : Option σ)) := by
  rw [Polynomial.leadingCoeff, natDegree_optionEquivLeft]

/-- Peeling the `none` variable preserves the remaining top monomial under DTC. -/
theorem topMonomial_coeff_optionEquivLeft_degreeOf_none_of_dtc
    {p : MvPolynomial (Option σ) R} (hp : HasDominantTopCoeff p) :
    topMonomial ((optionEquivLeft R σ p).coeff (p.degreeOf (none : Option σ))) =
      (topMonomial p).some := by
  let q := (optionEquivLeft R σ p).coeff (p.degreeOf (none : Option σ))
  ext i
  apply le_antisymm
  · rw [topMonomial_apply]
    rw [degreeOf_le_iff]
    intro m hm
    have hm' : m.optionElim (p.degreeOf (none : Option σ)) ∈ p.support :=
      (mem_support_coeff_optionEquivLeft (R := R) (σ := σ) (f := p)
        (i := p.degreeOf (none : Option σ)) (m := m)).mp hm
    have hle := le_degreeOf_of_mem_support (Option.some i) hm'
    simpa [topMonomial_apply] using hle
  · have hmem : (topMonomial p).some ∈ q.support := by
      rw [mem_support_coeff_optionEquivLeft]
      simpa [topMonomial_optionElim_some_degreeOf_none p] using topMonomial_mem_support hp
    have hle := le_degreeOf_of_mem_support i hmem
    simpa [q, topMonomial_apply] using hle

/-- The top coefficient of the peeled `none`-leading coefficient is the original top
coefficient. -/
theorem coeff_topMonomial_coeff_optionEquivLeft_degreeOf_none
    {p : MvPolynomial (Option σ) R} (hp : HasDominantTopCoeff p) :
    ((optionEquivLeft R σ p).coeff (p.degreeOf (none : Option σ))).coeff
        (topMonomial ((optionEquivLeft R σ p).coeff (p.degreeOf (none : Option σ)))) =
      p.coeff (topMonomial p) := by
  rw [topMonomial_coeff_optionEquivLeft_degreeOf_none_of_dtc hp]
  rw [optionEquivLeft_coeff_coeff]
  rw [topMonomial_optionElim_some_degreeOf_none p]

/-- The coefficient at `degreeOf none` has dominant top coefficient. -/
theorem HasDominantTopCoeff.coeff_optionEquivLeft_degreeOf_none
    {p : MvPolynomial (Option σ) R} (hp : HasDominantTopCoeff p) :
    HasDominantTopCoeff
      ((optionEquivLeft R σ p).coeff (p.degreeOf (none : Option σ))) := by
  unfold HasDominantTopCoeff
  rw [coeff_topMonomial_coeff_optionEquivLeft_degreeOf_none hp]
  exact hp

/-- The leading coefficient in the peeled `none` variable has dominant top coefficient. -/
theorem HasDominantTopCoeff.leadingCoeff_optionEquivLeft
    {p : MvPolynomial (Option σ) R} (hp : HasDominantTopCoeff p) :
    HasDominantTopCoeff (optionEquivLeft R σ p).leadingCoeff := by
  simpa [leadingCoeff_optionEquivLeft_eq_coeff_degreeOf_none] using
    hp.coeff_optionEquivLeft_degreeOf_none

/-- The peeled `none`-leading coefficient is a nonzero polynomial under DTC. -/
theorem HasDominantTopCoeff.leadingCoeff_optionEquivLeft_ne_zero
    {p : MvPolynomial (Option σ) R} (hp : HasDominantTopCoeff p) :
    (optionEquivLeft R σ p).leadingCoeff ≠ 0 :=
  hp.leadingCoeff_optionEquivLeft.ne_zero

/-- The leading coefficient, viewed via `finSuccEquiv`, is the coefficient at
`degreeOf 0`. -/
theorem leadingCoeff_finSuccEquiv_eq_coeff_degreeOf_zero {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquiv R n p).leadingCoeff = (finSuccEquiv R n p).coeff (p.degreeOf 0) := by
  rw [Polynomial.leadingCoeff, natDegree_finSuccEquiv]

/-- Peeling variable `0` from `Fin (n+1)` preserves the tail of the top monomial under DTC. -/
theorem topMonomial_coeff_finSuccEquiv_degreeOf_zero_of_dtc {n : ℕ}
    {p : MvPolynomial (Fin (n + 1)) R} (hp : HasDominantTopCoeff p) :
    topMonomial ((finSuccEquiv R n p).coeff (p.degreeOf 0)) = (topMonomial p).tail := by
  let q := (finSuccEquiv R n p).coeff (p.degreeOf 0)
  ext i
  apply le_antisymm
  · rw [topMonomial_apply]
    rw [degreeOf_le_iff]
    intro m hm
    have hm' : m.cons (p.degreeOf 0) ∈ p.support :=
      (mem_support_coeff_finSuccEquiv (R := R) (n := n) (f := p)
        (i := p.degreeOf 0) (m := m)).mp hm
    have hle := le_degreeOf_of_mem_support i.succ hm'
    simpa [topMonomial_apply] using hle
  · have hmem : (topMonomial p).tail ∈ q.support := by
      rw [mem_support_coeff_finSuccEquiv]
      simpa [topMonomial_cons_tail_degreeOf_zero p] using topMonomial_mem_support hp
    have hle := le_degreeOf_of_mem_support i hmem
    simpa [q, topMonomial_apply] using hle

/-- The top coefficient of the peeled `Fin` leading coefficient is the original top
coefficient. -/
theorem coeff_topMonomial_coeff_finSuccEquiv_degreeOf_zero {n : ℕ}
    {p : MvPolynomial (Fin (n + 1)) R} (hp : HasDominantTopCoeff p) :
    ((finSuccEquiv R n p).coeff (p.degreeOf 0)).coeff
        (topMonomial ((finSuccEquiv R n p).coeff (p.degreeOf 0))) =
      p.coeff (topMonomial p) := by
  rw [topMonomial_coeff_finSuccEquiv_degreeOf_zero_of_dtc hp]
  rw [finSuccEquiv_coeff_coeff]
  rw [topMonomial_cons_tail_degreeOf_zero p]

/-- The coefficient at `degreeOf 0` in `finSuccEquiv` has dominant top coefficient. -/
theorem HasDominantTopCoeff.coeff_finSuccEquiv_degreeOf_zero {n : ℕ}
    {p : MvPolynomial (Fin (n + 1)) R} (hp : HasDominantTopCoeff p) :
    HasDominantTopCoeff ((finSuccEquiv R n p).coeff (p.degreeOf 0)) := by
  unfold HasDominantTopCoeff
  rw [coeff_topMonomial_coeff_finSuccEquiv_degreeOf_zero hp]
  exact hp

/-- The leading coefficient in the peeled zero-th `Fin` variable has dominant top
coefficient. -/
theorem HasDominantTopCoeff.leadingCoeff_finSuccEquiv {n : ℕ}
    {p : MvPolynomial (Fin (n + 1)) R} (hp : HasDominantTopCoeff p) :
    HasDominantTopCoeff (finSuccEquiv R n p).leadingCoeff := by
  simpa [leadingCoeff_finSuccEquiv_eq_coeff_degreeOf_zero] using
    hp.coeff_finSuccEquiv_degreeOf_zero

/-- The peeled zero-th `Fin` leading coefficient is a nonzero polynomial under DTC. -/
theorem HasDominantTopCoeff.leadingCoeff_finSuccEquiv_ne_zero {n : ℕ}
    {p : MvPolynomial (Fin (n + 1)) R} (hp : HasDominantTopCoeff p) :
    (finSuccEquiv R n p).leadingCoeff ≠ 0 :=
  hp.leadingCoeff_finSuccEquiv.ne_zero

/-- The coefficient of the product top monomial `∏_i z_i^{D_i + E_i}` in `p * q` is the
product of the two top coefficients: every other antidiagonal split forces one factor to
exceed its per-variable degree, so contributes `0`. (No domain assumption needed.) -/
theorem coeff_topMonomial_add_mul (p q : MvPolynomial σ R) :
    (p * q).coeff (topMonomial p + topMonomial q)
      = p.coeff (topMonomial p) * q.coeff (topMonomial q) := by
  rw [coeff_mul]
  refine Finset.sum_eq_single_of_mem (topMonomial p, topMonomial q)
    (Finset.mem_antidiagonal.mpr rfl) ?_
  intro b hb hbne
  rw [Finset.mem_antidiagonal] at hb
  by_contra hprod
  apply hbne
  have h1 : p.coeff b.1 ≠ 0 := fun h => hprod (by rw [h, zero_mul])
  have h2 : q.coeff b.2 ≠ 0 := fun h => hprod (by rw [h, mul_zero])
  have hm1 := mem_support_iff.mpr h1
  have hm2 := mem_support_iff.mpr h2
  have hsum : ∀ i, b.1 i + b.2 i = topMonomial p i + topMonomial q i := by
    intro i
    have h := DFunLike.congr_fun hb i
    rw [Finsupp.add_apply, Finsupp.add_apply] at h
    exact h
  have e1 : b.1 = topMonomial p := by
    ext i
    have l1 := le_topMonomial_of_mem_support hm1 i
    have l2 := le_topMonomial_of_mem_support hm2 i
    have := hsum i; omega
  have e2 : b.2 = topMonomial q := by
    ext i
    have l1 := le_topMonomial_of_mem_support hm1 i
    have l2 := le_topMonomial_of_mem_support hm2 i
    have := hsum i; omega
  exact Prod.ext e1 e2

variable [IsDomain R]

/-- Over a domain, the product top coefficient is nonzero when both factors have dominant
top coefficients. -/
theorem coeff_topMonomial_mul_ne_zero {p q : MvPolynomial σ R}
    (hp : HasDominantTopCoeff p) (hq : HasDominantTopCoeff q) :
    (p * q).coeff (topMonomial p + topMonomial q) ≠ 0 := by
  rw [coeff_topMonomial_add_mul]
  exact mul_ne_zero hp hq

/-- Over a domain, per-variable degrees add under multiplication of polynomials with
dominant top coefficients. -/
theorem degreeOf_mul_of_dtc {p q : MvPolynomial σ R}
    (hp : HasDominantTopCoeff p) (hq : HasDominantTopCoeff q) (i : σ) :
    (p * q).degreeOf i = p.degreeOf i + q.degreeOf i := by
  refine le_antisymm (degreeOf_mul_le i p q) ?_
  have hmem : (topMonomial p + topMonomial q) ∈ (p * q).support :=
    mem_support_iff.mpr (coeff_topMonomial_mul_ne_zero hp hq)
  have h := le_degreeOf_of_mem_support i hmem
  simpa using h

/-- The product top monomial is the sum of the top monomials. -/
theorem topMonomial_mul_of_dtc {p q : MvPolynomial σ R}
    (hp : HasDominantTopCoeff p) (hq : HasDominantTopCoeff q) :
    topMonomial (p * q) = topMonomial p + topMonomial q := by
  ext i
  rw [topMonomial_apply, Finsupp.add_apply, topMonomial_apply, topMonomial_apply,
    degreeOf_mul_of_dtc hp hq]

/-- **Step 0 of `lem:nested`.** A product of two polynomials with dominant top
coefficients has a dominant top coefficient (over an integral domain). -/
theorem HasDominantTopCoeff.mul {p q : MvPolynomial σ R}
    (hp : HasDominantTopCoeff p) (hq : HasDominantTopCoeff q) :
    HasDominantTopCoeff (p * q) := by
  unfold HasDominantTopCoeff
  rw [topMonomial_mul_of_dtc hp hq]
  exact coeff_topMonomial_mul_ne_zero hp hq

/-- A product of two DTC polynomials is nonzero. -/
theorem HasDominantTopCoeff.mul_ne_zero {p q : MvPolynomial σ R}
    (hp : HasDominantTopCoeff p) (hq : HasDominantTopCoeff q) :
    p * q ≠ 0 :=
  (hp.mul hq).ne_zero

/-- The top coefficients are multiplicative. -/
theorem coeff_topMonomial_mul {p q : MvPolynomial σ R}
    (hp : HasDominantTopCoeff p) (hq : HasDominantTopCoeff q) :
    (p * q).coeff (topMonomial (p * q))
      = p.coeff (topMonomial p) * q.coeff (topMonomial q) := by
  rw [topMonomial_mul_of_dtc hp hq, coeff_topMonomial_add_mul]

/-- A finite product of polynomials with dominant top coefficients has a dominant top
coefficient. This membership-indexed form is convenient for local finite families. -/
theorem HasDominantTopCoeff.prod_of_mem {ι : Type*} (s : Finset ι)
    {p : ι → MvPolynomial σ R} (hp : ∀ a ∈ s, HasDominantTopCoeff (p a)) :
    HasDominantTopCoeff (∏ a ∈ s, p a) := by
  classical
  revert hp
  refine Finset.induction_on s ?_ (fun a s ha ih => ?_)
  · intro hp
    simpa using hasDominantTopCoeff_one
  · intro hp
    rw [Finset.prod_insert ha]
    exact (hp a (Finset.mem_insert_self a s)).mul
      (ih fun b hb => hp b (Finset.mem_insert_of_mem hb))

/-- **Step 0, iterated.** A finite product of polynomials with dominant top coefficients
has a dominant top coefficient; in particular `P := ∏_a p_a` does. -/
theorem HasDominantTopCoeff.prod {ι : Type*} (s : Finset ι) {p : ι → MvPolynomial σ R}
    (hp : ∀ a, HasDominantTopCoeff (p a)) :
    HasDominantTopCoeff (∏ a ∈ s, p a) :=
  HasDominantTopCoeff.prod_of_mem s fun a _ => hp a

/-- A finite product of DTC polynomials is nonzero. -/
theorem HasDominantTopCoeff.prod_ne_zero_of_mem {ι : Type*} (s : Finset ι)
    {p : ι → MvPolynomial σ R} (hp : ∀ a ∈ s, HasDominantTopCoeff (p a)) :
    (∏ a ∈ s, p a) ≠ 0 :=
  (HasDominantTopCoeff.prod_of_mem s hp).ne_zero

/-- Unrestricted-index version of `HasDominantTopCoeff.prod_ne_zero_of_mem`. -/
theorem HasDominantTopCoeff.prod_ne_zero {ι : Type*} (s : Finset ι)
    {p : ι → MvPolynomial σ R} (hp : ∀ a, HasDominantTopCoeff (p a)) :
    (∏ a ∈ s, p a) ≠ 0 :=
  (HasDominantTopCoeff.prod s hp).ne_zero

/-- Fintype product wrapper for DTC families. -/
theorem HasDominantTopCoeff.fintype_prod {ι : Type*} [Fintype ι]
    {p : ι → MvPolynomial σ R} (hp : ∀ a, HasDominantTopCoeff (p a)) :
    HasDominantTopCoeff (∏ a, p a) := by
  simpa using HasDominantTopCoeff.prod (Finset.univ : Finset ι) hp

/-- Fintype product nonzero wrapper for DTC families. -/
theorem HasDominantTopCoeff.fintype_prod_ne_zero {ι : Type*} [Fintype ι]
    {p : ι → MvPolynomial σ R} (hp : ∀ a, HasDominantTopCoeff (p a)) :
    (∏ a, p a) ≠ 0 :=
  (HasDominantTopCoeff.fintype_prod hp).ne_zero

/-- Per-variable degrees of finite products add under dominant top coefficient hypotheses. -/
theorem degreeOf_prod_of_dtc {ι : Type*} (s : Finset ι) {p : ι → MvPolynomial σ R}
    (hp : ∀ a ∈ s, HasDominantTopCoeff (p a)) (i : σ) :
    (∏ a ∈ s, p a).degreeOf i = ∑ a ∈ s, (p a).degreeOf i := by
  exact degreeOf_prod_eq s p (fun a ha => (hp a ha).ne_zero)

/-- The top monomial of a finite product is the sum of the top monomials. -/
theorem topMonomial_prod_of_dtc {ι : Type*} (s : Finset ι)
    {p : ι → MvPolynomial σ R} (hp : ∀ a ∈ s, HasDominantTopCoeff (p a)) :
    topMonomial (∏ a ∈ s, p a) = ∑ a ∈ s, topMonomial (p a) := by
  ext i
  rw [topMonomial_apply, degreeOf_prod_of_dtc s hp i]
  simp [topMonomial_apply]

/-- The top coefficient of a finite product is the product of top coefficients. -/
theorem coeff_topMonomial_prod_of_dtc {ι : Type*} (s : Finset ι)
    {p : ι → MvPolynomial σ R} (hp : ∀ a ∈ s, HasDominantTopCoeff (p a)) :
    (∏ a ∈ s, p a).coeff (topMonomial (∏ a ∈ s, p a)) =
      ∏ a ∈ s, (p a).coeff (topMonomial (p a)) := by
  classical
  revert hp
  refine Finset.induction_on s ?_ ?_
  · intro hp
    have htop : topMonomial (1 : MvPolynomial σ R) = 0 := by
      ext i
      simp [topMonomial_apply, degreeOf_one]
    simp [htop]
  · intro a s ha ih hp
    have hpa : HasDominantTopCoeff (p a) := hp a (Finset.mem_insert_self a s)
    have hps : ∀ b ∈ s, HasDominantTopCoeff (p b) :=
      fun b hb => hp b (Finset.mem_insert_of_mem hb)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    rw [coeff_topMonomial_mul hpa (HasDominantTopCoeff.prod_of_mem s hps), ih hps]

/-- The top coefficient of a finite product of DTC polynomials is nonzero. -/
theorem coeff_topMonomial_prod_ne_zero_of_dtc {ι : Type*} (s : Finset ι)
    {p : ι → MvPolynomial σ R} (hp : ∀ a ∈ s, HasDominantTopCoeff (p a)) :
    (∏ a ∈ s, p a).coeff (topMonomial (∏ a ∈ s, p a)) ≠ 0 :=
  (HasDominantTopCoeff.prod_of_mem s hp).coeff_topMonomial_ne

/-- The coefficient at the displayed sum of top monomials in a finite product of DTC
polynomials is nonzero. -/
theorem coeff_sum_topMonomial_prod_ne_zero_of_dtc {ι : Type*} (s : Finset ι)
    {p : ι → MvPolynomial σ R} (hp : ∀ a ∈ s, HasDominantTopCoeff (p a)) :
    (∏ a ∈ s, p a).coeff (∑ a ∈ s, topMonomial (p a)) ≠ 0 := by
  simpa [topMonomial_prod_of_dtc s hp] using
    coeff_topMonomial_prod_ne_zero_of_dtc (s := s) hp

end TransformerIdentifiability.NLayer
