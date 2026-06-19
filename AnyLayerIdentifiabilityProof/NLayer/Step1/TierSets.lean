import AnyLayerIdentifiabilityProof.NLayer.Step1.ConcreteStratification
import AnyLayerIdentifiabilityProof.NLayer.Step1.NestedLargeness
import AnyLayerIdentifiabilityProof.NLayer.Step1.OStar

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Step 1 tier sets

Owner shard for the concrete tier sets `T_j`, the `T_1 = S'^1` fact, first-tier
nonemptiness/infinity, and pointwise tier regularity facts.
-/

/-! ## Gate-prefix coordinates and tier sets -/

/-- The previously constructed gates, evaluated at one complex point, as a length-`j`
coordinate vector.  This is the zero-based Lean form of `s'_{<j}`. -/
def gatePrefix {m : Nat} (P : ConcreteStratification m) (j : Nat) (τ : ℂ) :
    Fin j -> ℂ :=
  fun i => P.s i τ

@[simp]
theorem gatePrefix_apply {m : Nat} (P : ConcreteStratification m) (j : Nat)
    (τ : ℂ) (i : Fin j) :
    gatePrefix P j τ i = P.s i τ :=
  rfl

@[simp]
theorem nestedInit_gatePrefix {m j : Nat} (P : ConcreteStratification m) (τ : ℂ) :
    nestedInit (gatePrefix P (j + 1) τ) = gatePrefix P j τ := by
  ext i
  simp [nestedInit, gatePrefix]

@[simp]
theorem nestedLast_gatePrefix {m j : Nat} (P : ConcreteStratification m) (τ : ℂ) :
    nestedLast (gatePrefix P (j + 1) τ) = P.s j τ := by
  simp [nestedLast, gatePrefix]

/-- Zero-based tier sets.

`tierSet P F 0` is TeX `T_1 = S'^1`; for `j + 1`, membership says
`τ ∈ S'^{j+2}` and the previous gate vector lies in the nested largeness region
`N_{j+1}`. -/
noncomputable def tierSet {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) (j : Nat) : Set ℂ :=
  {τ | τ ∈ P.S j ∧ gatePrefix P j τ ∈ F.region j}

/-- Zero-free tier sets using the strengthened nested largeness regions.

This keeps `tierSet` unchanged while adding the leading-coefficient nonvanishing
recorded by `NestedTailFamily.zeroFreeRegion`. -/
noncomputable def zeroFreeTierSet {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) (j : Nat) : Set ℂ :=
  {τ | τ ∈ P.S j ∧ gatePrefix P j τ ∈ F.zeroFreeRegion j}

/-- Packaged tier data for downstream shards.  The actual tier sets are computed from
the concrete stratification and nested-largeness family, while the hard stratum
regularity hypotheses remain in `ConcreteStratification`. -/
structure TierSystem (m : Nat) where
  stratification : ConcreteStratification m
  nestedFamily : NestedTailFamily

namespace TierSystem

/-- The tier tower associated to a packaged tier system. -/
noncomputable def T {m : Nat} (A : TierSystem m) : Nat -> Set ℂ :=
  tierSet A.stratification A.nestedFamily

@[simp]
theorem T_apply {m : Nat} (A : TierSystem m) (j : Nat) :
    A.T j = tierSet A.stratification A.nestedFamily j :=
  rfl

/-- The zero-free tier tower associated to a packaged tier system. -/
noncomputable def T0 {m : Nat} (A : TierSystem m) : Nat -> Set ℂ :=
  zeroFreeTierSet A.stratification A.nestedFamily

@[simp]
theorem T0_apply {m : Nat} (A : TierSystem m) (j : Nat) :
    A.T0 j = zeroFreeTierSet A.stratification A.nestedFamily j :=
  rfl

end TierSystem

/-! ## Partial-union support -/

/-- Membership in one indexed set gives membership in any later partial union. -/
theorem mem_partialUnion_of_mem {S : Nat -> Set ℂ} {j n : Nat} {τ : ℂ}
    (hj : j < n) (hτ : τ ∈ S j) :
    τ ∈ partialUnion S n :=
  ⟨j, hj, hτ⟩

/-- An indexed set is contained in any partial union whose range includes its index. -/
theorem subset_partialUnion_of_lt {S : Nat -> Set ℂ} {j n : Nat} (hj : j < n) :
    S j ⊆ partialUnion S n :=
  fun _ hτ => mem_partialUnion_of_mem hj hτ

/-- Partial unions are monotone in the cutoff. -/
theorem partialUnion_mono_right {S : Nat -> Set ℂ} {n k : Nat} (hnk : n ≤ k) :
    partialUnion S n ⊆ partialUnion S k := by
  rintro τ ⟨j, hj, hτ⟩
  exact ⟨j, Nat.lt_of_lt_of_le hj hnk, hτ⟩

/-- The `n`-th partial union is contained in the successor partial union. -/
theorem partialUnion_subset_succ (S : Nat -> Set ℂ) (n : Nat) :
    partialUnion S n ⊆ partialUnion S (n + 1) :=
  partialUnion_mono_right (S := S) (Nat.le_succ n)

/-- To prove a partial union is contained in a set, it suffices to prove each included
indexed set is contained in that set. -/
theorem partialUnion_subset_of_forall_subset {S : Nat -> Set ℂ} {n : Nat}
    {U : Set ℂ} (hU : ∀ j, j < n -> S j ⊆ U) :
    partialUnion S n ⊆ U := by
  rintro τ ⟨j, hj, hτ⟩
  exact hU j hj hτ

/-! ## Shape and access lemmas -/

theorem mem_tierSet_iff {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} {τ : ℂ} :
    τ ∈ tierSet P F j ↔ τ ∈ P.S j ∧ gatePrefix P j τ ∈ F.region j :=
  Iff.rfl

theorem tierSet_mem_stratum {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} {τ : ℂ} (hτ : τ ∈ tierSet P F j) :
    τ ∈ P.S j :=
  hτ.1

theorem tierSet_mem_region {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} {τ : ℂ} (hτ : τ ∈ tierSet P F j) :
    gatePrefix P j τ ∈ F.region j :=
  hτ.2

theorem tierSet_subset_stratum {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) (j : Nat) :
    tierSet P F j ⊆ P.S j :=
  fun _ hτ => tierSet_mem_stratum P F hτ

theorem mem_zeroFreeTierSet_iff {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} {τ : ℂ} :
    τ ∈ zeroFreeTierSet P F j ↔
      τ ∈ P.S j ∧ gatePrefix P j τ ∈ F.zeroFreeRegion j :=
  Iff.rfl

theorem zeroFreeTierSet_mem_stratum {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} {τ : ℂ} (hτ : τ ∈ zeroFreeTierSet P F j) :
    τ ∈ P.S j :=
  hτ.1

theorem zeroFreeTierSet_mem_zeroFreeRegion {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} {τ : ℂ} (hτ : τ ∈ zeroFreeTierSet P F j) :
    gatePrefix P j τ ∈ F.zeroFreeRegion j :=
  hτ.2

theorem zeroFreeTierSet_subset_stratum {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) (j : Nat) :
    zeroFreeTierSet P F j ⊆ P.S j :=
  fun _ hτ => zeroFreeTierSet_mem_stratum P F hτ

theorem zeroFreeTierSet_subset_tierSet {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) (j : Nat) :
    zeroFreeTierSet P F j ⊆ tierSet P F j := by
  rintro τ ⟨hS, hzfree⟩
  exact ⟨hS, (F.zeroFreeRegion_subset_region j) hzfree⟩

theorem zeroFreeTierSet_mem_region {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} {τ : ℂ} (hτ : τ ∈ zeroFreeTierSet P F j) :
    gatePrefix P j τ ∈ F.region j :=
  tierSet_mem_region P F (zeroFreeTierSet_subset_tierSet P F j hτ)

theorem zeroFreeTierSet_lead_ne {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} {τ : ℂ} (hτ : τ ∈ zeroFreeTierSet P F j) :
    (F.step j).lead (gatePrefix P j τ) ≠ 0 :=
  F.lead_ne_of_mem_zeroFreeRegion (zeroFreeTierSet_mem_zeroFreeRegion P F hτ)

/-- Zero-based form of `T_1 = S'^1`. -/
@[simp]
theorem tierSet_zero_eq_stratum {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) :
    tierSet P F 0 = P.S 0 := by
  ext τ
  simp [tierSet]

@[simp]
theorem mem_tierSet_zero {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {τ : ℂ} :
    τ ∈ tierSet P F 0 ↔ τ ∈ P.S 0 := by
  rw [tierSet_zero_eq_stratum]

@[simp]
theorem mem_zeroFreeTierSet_zero {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {τ : ℂ} :
    τ ∈ zeroFreeTierSet P F 0 ↔
      τ ∈ P.S 0 ∧ (F.step 0).lead (gatePrefix P 0 τ) ≠ 0 := by
  simp [zeroFreeTierSet]

theorem zeroFreeTierSet_zero_eq_stratum_of_lead_ne {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily)
    (hlead : ∀ τ ∈ P.S 0, (F.step 0).lead (gatePrefix P 0 τ) ≠ 0) :
    zeroFreeTierSet P F 0 = P.S 0 := by
  ext τ
  constructor
  · intro hτ
    exact hτ.1
  · intro hτ
    exact ⟨hτ, by simpa using hlead τ hτ⟩

/-- The successor-tier membership decomposition against the recursive nested region. -/
theorem mem_tierSet_succ {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} {τ : ℂ} :
    τ ∈ tierSet P F (j + 1) ↔
      τ ∈ P.S (j + 1)
        ∧ gatePrefix P j τ ∈ F.region j
        ∧ F.threshold j (gatePrefix P j τ) < ‖P.s j τ‖ := by
  constructor
  · rintro ⟨hS, hregion⟩
    have hregion' :=
      (NestedTailFamily.mem_region_succ F
        (m := j) (z := gatePrefix P (j + 1) τ)).mp hregion
    exact ⟨hS, by simpa using hregion'.1, by simpa using hregion'.2⟩
  · rintro ⟨hS, hprefix, hlarge⟩
    refine ⟨hS, ?_⟩
    refine (NestedTailFamily.mem_region_succ F
      (m := j) (z := gatePrefix P (j + 1) τ)).mpr ?_
    exact ⟨by simpa using hprefix, by simpa using hlarge⟩

theorem tierSet_succ_prefix_mem_region {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} {τ : ℂ}
    (hτ : τ ∈ tierSet P F (j + 1)) :
    gatePrefix P j τ ∈ F.region j :=
  (mem_tierSet_succ P F).mp hτ |>.2.1

theorem tierSet_succ_threshold_lt_norm {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} {τ : ℂ}
    (hτ : τ ∈ tierSet P F (j + 1)) :
    F.threshold j (gatePrefix P j τ) < ‖P.s j τ‖ :=
  (mem_tierSet_succ P F).mp hτ |>.2.2

theorem mem_zeroFreeTierSet_succ {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} {τ : ℂ} :
    τ ∈ zeroFreeTierSet P F (j + 1) ↔
      τ ∈ P.S (j + 1)
        ∧ gatePrefix P j τ ∈ F.zeroFreeRegion j
        ∧ F.threshold j (gatePrefix P j τ) < ‖P.s j τ‖
        ∧ (F.step (j + 1)).lead (gatePrefix P (j + 1) τ) ≠ 0 := by
  constructor
  · rintro ⟨hS, hregion⟩
    have hregion' :=
      (NestedTailFamily.mem_zeroFreeRegion_succ F
        (m := j) (z := gatePrefix P (j + 1) τ)).mp hregion
    exact ⟨hS, by simpa using hregion'.1, by simpa using hregion'.2.1, hregion'.2.2⟩
  · rintro ⟨hS, hprefix, hlarge, hlead⟩
    refine ⟨hS, ?_⟩
    refine (NestedTailFamily.mem_zeroFreeRegion_succ F
      (m := j) (z := gatePrefix P (j + 1) τ)).mpr ?_
    exact ⟨by simpa using hprefix, by simpa using hlarge, hlead⟩

theorem zeroFreeTierSet_succ_prefix_mem_zeroFreeRegion {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) {j : Nat} {τ : ℂ}
    (hτ : τ ∈ zeroFreeTierSet P F (j + 1)) :
    gatePrefix P j τ ∈ F.zeroFreeRegion j :=
  (mem_zeroFreeTierSet_succ P F).mp hτ |>.2.1

theorem zeroFreeTierSet_succ_threshold_lt_norm {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) {j : Nat} {τ : ℂ}
    (hτ : τ ∈ zeroFreeTierSet P F (j + 1)) :
    F.threshold j (gatePrefix P j τ) < ‖P.s j τ‖ :=
  (mem_zeroFreeTierSet_succ P F).mp hτ |>.2.2.1

theorem zeroFreeTierSet_succ_lead_ne {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) {j : Nat} {τ : ℂ}
    (hτ : τ ∈ zeroFreeTierSet P F (j + 1)) :
    (F.step (j + 1)).lead (gatePrefix P (j + 1) τ) ≠ 0 :=
  (mem_zeroFreeTierSet_succ P F).mp hτ |>.2.2.2

namespace TierSystem

theorem mem_iff {m : Nat} (A : TierSystem m) {j : Nat} {τ : ℂ} :
    τ ∈ A.T j ↔
      τ ∈ A.stratification.S j
        ∧ gatePrefix A.stratification j τ ∈ A.nestedFamily.region j :=
  Iff.rfl

theorem mem_stratum {m : Nat} (A : TierSystem m) {j : Nat} {τ : ℂ}
    (hτ : τ ∈ A.T j) :
    τ ∈ A.stratification.S j :=
  tierSet_mem_stratum A.stratification A.nestedFamily hτ

theorem mem_region {m : Nat} (A : TierSystem m) {j : Nat} {τ : ℂ}
    (hτ : τ ∈ A.T j) :
    gatePrefix A.stratification j τ ∈ A.nestedFamily.region j :=
  tierSet_mem_region A.stratification A.nestedFamily hτ

theorem subset_stratum {m : Nat} (A : TierSystem m) (j : Nat) :
    A.T j ⊆ A.stratification.S j :=
  tierSet_subset_stratum A.stratification A.nestedFamily j

@[simp]
theorem zero_eq_stratum {m : Nat} (A : TierSystem m) :
    A.T 0 = A.stratification.S 0 :=
  tierSet_zero_eq_stratum A.stratification A.nestedFamily

@[simp]
theorem mem_zero {m : Nat} (A : TierSystem m) {τ : ℂ} :
    τ ∈ A.T 0 ↔ τ ∈ A.stratification.S 0 := by
  rw [zero_eq_stratum]

theorem mem_succ {m : Nat} (A : TierSystem m) {j : Nat} {τ : ℂ} :
    τ ∈ A.T (j + 1) ↔
      τ ∈ A.stratification.S (j + 1)
        ∧ gatePrefix A.stratification j τ ∈ A.nestedFamily.region j
        ∧ A.nestedFamily.threshold j (gatePrefix A.stratification j τ) <
          ‖A.stratification.s j τ‖ :=
  mem_tierSet_succ A.stratification A.nestedFamily

theorem mem_T0_iff {m : Nat} (A : TierSystem m) {j : Nat} {τ : ℂ} :
    τ ∈ A.T0 j ↔
      τ ∈ A.stratification.S j
        ∧ gatePrefix A.stratification j τ ∈ A.nestedFamily.zeroFreeRegion j :=
  Iff.rfl

theorem T0_subset_T {m : Nat} (A : TierSystem m) (j : Nat) :
    A.T0 j ⊆ A.T j :=
  zeroFreeTierSet_subset_tierSet A.stratification A.nestedFamily j

theorem T0_mem_stratum {m : Nat} (A : TierSystem m) {j : Nat} {τ : ℂ}
    (hτ : τ ∈ A.T0 j) :
    τ ∈ A.stratification.S j :=
  zeroFreeTierSet_mem_stratum A.stratification A.nestedFamily hτ

theorem T0_mem_zeroFreeRegion {m : Nat} (A : TierSystem m) {j : Nat} {τ : ℂ}
    (hτ : τ ∈ A.T0 j) :
    gatePrefix A.stratification j τ ∈ A.nestedFamily.zeroFreeRegion j :=
  zeroFreeTierSet_mem_zeroFreeRegion A.stratification A.nestedFamily hτ

theorem T0_mem_region {m : Nat} (A : TierSystem m) {j : Nat} {τ : ℂ}
    (hτ : τ ∈ A.T0 j) :
    gatePrefix A.stratification j τ ∈ A.nestedFamily.region j :=
  zeroFreeTierSet_mem_region A.stratification A.nestedFamily hτ

theorem T0_subset_stratum {m : Nat} (A : TierSystem m) (j : Nat) :
    A.T0 j ⊆ A.stratification.S j :=
  zeroFreeTierSet_subset_stratum A.stratification A.nestedFamily j

theorem T0_lead_ne {m : Nat} (A : TierSystem m) {j : Nat} {τ : ℂ}
    (hτ : τ ∈ A.T0 j) :
    (A.nestedFamily.step j).lead (gatePrefix A.stratification j τ) ≠ 0 :=
  zeroFreeTierSet_lead_ne A.stratification A.nestedFamily hτ

@[simp]
theorem mem_T0_zero {m : Nat} (A : TierSystem m) {τ : ℂ} :
    τ ∈ A.T0 0 ↔
      τ ∈ A.stratification.S 0
        ∧ (A.nestedFamily.step 0).lead (gatePrefix A.stratification 0 τ) ≠ 0 :=
  mem_zeroFreeTierSet_zero A.stratification A.nestedFamily

theorem T0_zero_eq_stratum_of_lead_ne {m : Nat} (A : TierSystem m)
    (hlead :
      ∀ τ ∈ A.stratification.S 0,
        (A.nestedFamily.step 0).lead (gatePrefix A.stratification 0 τ) ≠ 0) :
    A.T0 0 = A.stratification.S 0 :=
  zeroFreeTierSet_zero_eq_stratum_of_lead_ne
    A.stratification A.nestedFamily hlead

theorem mem_T0_succ {m : Nat} (A : TierSystem m) {j : Nat} {τ : ℂ} :
    τ ∈ A.T0 (j + 1) ↔
      τ ∈ A.stratification.S (j + 1)
        ∧ gatePrefix A.stratification j τ ∈ A.nestedFamily.zeroFreeRegion j
        ∧ A.nestedFamily.threshold j (gatePrefix A.stratification j τ) <
          ‖A.stratification.s j τ‖
        ∧ (A.nestedFamily.step (j + 1)).lead
          (gatePrefix A.stratification (j + 1) τ) ≠ 0 :=
  mem_zeroFreeTierSet_succ A.stratification A.nestedFamily

theorem T0_succ_prefix_mem_zeroFreeRegion {m : Nat}
    (A : TierSystem m) {j : Nat} {τ : ℂ} (hτ : τ ∈ A.T0 (j + 1)) :
    gatePrefix A.stratification j τ ∈ A.nestedFamily.zeroFreeRegion j :=
  zeroFreeTierSet_succ_prefix_mem_zeroFreeRegion
    A.stratification A.nestedFamily hτ

theorem T0_succ_threshold_lt_norm {m : Nat}
    (A : TierSystem m) {j : Nat} {τ : ℂ} (hτ : τ ∈ A.T0 (j + 1)) :
    A.nestedFamily.threshold j (gatePrefix A.stratification j τ) <
      ‖A.stratification.s j τ‖ :=
  zeroFreeTierSet_succ_threshold_lt_norm A.stratification A.nestedFamily hτ

theorem T0_succ_lead_ne {m : Nat}
    (A : TierSystem m) {j : Nat} {τ : ℂ} (hτ : τ ∈ A.T0 (j + 1)) :
    (A.nestedFamily.step (j + 1)).lead
      (gatePrefix A.stratification (j + 1) τ) ≠ 0 :=
  zeroFreeTierSet_succ_lead_ne A.stratification A.nestedFamily hτ

end TierSystem

/-! ## First-tier nonemptiness and infinitude -/

theorem sigmoidPole_injective {b lambda : ℝ} (hlambda : lambda ≠ 0) :
    Function.Injective (sigmoidPole b lambda) := by
  intro n k hnk
  let numerator : ℤ -> ℂ := fun q =>
    (((((2 * q + 1 : ℤ) : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I - (b : ℂ))
  have hlambdaC : (lambda : ℂ) ≠ 0 := by
    exact_mod_cast hlambda
  have hnum : numerator n = numerator k := by
    calc
      numerator n = sigmoidPole b lambda n * (lambda : ℂ) := by
        simp [numerator, sigmoidPole, hlambdaC]
      _ = sigmoidPole b lambda k * (lambda : ℂ) := by
        rw [hnk]
      _ = numerator k := by
        simp [numerator, sigmoidPole, hlambdaC]
  have him := congrArg Complex.im hnum
  have hreal :
      (((2 * n + 1 : ℤ) : ℝ) * Real.pi) =
        (((2 * k + 1 : ℤ) : ℝ) * Real.pi) := by
    simpa [numerator] using him
  have hcoeff : ((2 * n + 1 : ℤ) : ℝ) = ((2 * k + 1 : ℤ) : ℝ) := by
    nlinarith [Real.pi_pos]
  have hint : (2 * n + 1 : ℤ) = 2 * k + 1 := by
    exact_mod_cast hcoeff
  omega

theorem firstPoleSet_nonempty (b lambda : ℝ) :
    (firstPoleSet b lambda).Nonempty :=
  ⟨sigmoidPole b lambda 0, sigmoidPole_mem_firstPoleSet b lambda 0⟩

theorem firstPoleSet_infinite {b lambda : ℝ} (hlambda : lambda ≠ 0) :
    (firstPoleSet b lambda).Infinite := by
  rw [firstPoleSet]
  exact Set.infinite_range_of_injective (sigmoidPole_injective (b := b) hlambda)

theorem tierSet_zero_eq_firstPoleSet_of_lambda_ne_zero {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) (hlambda : P.lambda1 ≠ 0) :
    tierSet P F 0 = firstPoleSet P.b P.lambda1 := by
  rw [tierSet_zero_eq_stratum, P.first_stratum_eq_firstPoleSet hlambda]

theorem tierSet_zero_subset_firstPoleSet_of_lambda_ne_zero {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) (hlambda : P.lambda1 ≠ 0) :
    tierSet P F 0 ⊆ firstPoleSet P.b P.lambda1 := by
  rw [tierSet_zero_eq_firstPoleSet_of_lambda_ne_zero P F hlambda]

theorem firstPoleSet_subset_tierSet_zero_of_lambda_ne_zero {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) (hlambda : P.lambda1 ≠ 0) :
    firstPoleSet P.b P.lambda1 ⊆ tierSet P F 0 := by
  rw [tierSet_zero_eq_firstPoleSet_of_lambda_ne_zero P F hlambda]

theorem mem_tierSet_zero_iff_sigmoidPole_of_lambda_ne_zero {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) (hlambda : P.lambda1 ≠ 0)
    {τ : ℂ} :
    τ ∈ tierSet P F 0 ↔ ∃ n : ℤ, τ = sigmoidPole P.b P.lambda1 n := by
  rw [tierSet_zero_eq_firstPoleSet_of_lambda_ne_zero P F hlambda]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.symm⟩

theorem tierSet_zero_nonempty_of_lambda_ne_zero {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) (hlambda : P.lambda1 ≠ 0) :
    (tierSet P F 0).Nonempty := by
  rw [tierSet_zero_eq_firstPoleSet_of_lambda_ne_zero P F hlambda]
  exact firstPoleSet_nonempty P.b P.lambda1

theorem tierSet_zero_infinite_of_lambda_ne_zero {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) (hlambda : P.lambda1 ≠ 0) :
    (tierSet P F 0).Infinite := by
  rw [tierSet_zero_eq_firstPoleSet_of_lambda_ne_zero P F hlambda]
  exact firstPoleSet_infinite hlambda

namespace TierSystem

theorem zero_eq_firstPoleSet_of_lambda_ne_zero {m : Nat} (A : TierSystem m)
    (hlambda : A.stratification.lambda1 ≠ 0) :
    A.T 0 = firstPoleSet A.stratification.b A.stratification.lambda1 :=
  tierSet_zero_eq_firstPoleSet_of_lambda_ne_zero
    A.stratification A.nestedFamily hlambda

theorem zero_subset_firstPoleSet_of_lambda_ne_zero {m : Nat} (A : TierSystem m)
    (hlambda : A.stratification.lambda1 ≠ 0) :
    A.T 0 ⊆ firstPoleSet A.stratification.b A.stratification.lambda1 :=
  tierSet_zero_subset_firstPoleSet_of_lambda_ne_zero
    A.stratification A.nestedFamily hlambda

theorem firstPoleSet_subset_zero_of_lambda_ne_zero {m : Nat} (A : TierSystem m)
    (hlambda : A.stratification.lambda1 ≠ 0) :
    firstPoleSet A.stratification.b A.stratification.lambda1 ⊆ A.T 0 :=
  firstPoleSet_subset_tierSet_zero_of_lambda_ne_zero
    A.stratification A.nestedFamily hlambda

theorem mem_zero_iff_sigmoidPole_of_lambda_ne_zero {m : Nat} (A : TierSystem m)
    (hlambda : A.stratification.lambda1 ≠ 0) {τ : ℂ} :
    τ ∈ A.T 0 ↔
      ∃ n : ℤ, τ = sigmoidPole A.stratification.b A.stratification.lambda1 n :=
  mem_tierSet_zero_iff_sigmoidPole_of_lambda_ne_zero
    A.stratification A.nestedFamily hlambda

theorem zero_nonempty_of_lambda_ne_zero {m : Nat} (A : TierSystem m)
    (hlambda : A.stratification.lambda1 ≠ 0) :
    (A.T 0).Nonempty :=
  tierSet_zero_nonempty_of_lambda_ne_zero A.stratification A.nestedFamily hlambda

theorem zero_infinite_of_lambda_ne_zero {m : Nat} (A : TierSystem m)
    (hlambda : A.stratification.lambda1 ≠ 0) :
    (A.T 0).Infinite :=
  tierSet_zero_infinite_of_lambda_ne_zero A.stratification A.nestedFamily hlambda

end TierSystem

/-! ## Tier regularity facts -/

theorem tierSet_subset_partialUnion_succ {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} (hj : j < m) :
    tierSet P F j ⊆ partialUnion P.S (j + 1) := by
  intro τ hτ
  exact P.stratum_subset_singular_through hj (tierSet_mem_stratum P F hτ)

theorem tierSet_subset_partialUnion_of_lt {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j n : Nat} (hjn : j < n) :
    tierSet P F j ⊆ partialUnion P.S n := by
  intro τ hτ
  exact mem_partialUnion_of_mem hjn (tierSet_mem_stratum P F hτ)

theorem tierSet_subset_singularSet {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} (hj : j < m) :
    tierSet P F j ⊆ P.singularSet := by
  intro τ hτ
  exact ⟨j, hj, tierSet_mem_stratum P F hτ⟩

theorem tierSet_last_subset_singularSet {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) (hm : 0 < m) :
    tierSet P F (m - 1) ⊆ P.singularSet :=
  tierSet_subset_singularSet P F (by omega)

theorem tierSet_ne_real {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} (hj : j < m) {τ : ℂ}
    (hτ : τ ∈ tierSet P F j) (x : ℝ) :
    τ ≠ (x : ℂ) := by
  intro hτx
  have hx : (x : ℂ) ∈ P.S j := by
    simpa [hτx] using tierSet_mem_stratum P F hτ
  exact P.stratum_avoids_real hj x hx

theorem tierSet_notMem_realRange {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} (hj : j < m) {τ : ℂ}
    (hτ : τ ∈ tierSet P F j) :
    τ ∉ Set.range (fun x : ℝ => (x : ℂ)) := by
  rintro ⟨x, rfl⟩
  exact tierSet_ne_real P F hj hτ x rfl

theorem tierSet_ne_zero {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} (hj : j < m) {τ : ℂ}
    (hτ : τ ∈ tierSet P F j) :
    τ ≠ 0 := by
  simpa using tierSet_ne_real P F hj hτ 0

theorem tierSet_punctured_isolated_partialUnion_succ {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) {j : Nat} (hj : j < m)
    {τ : ℂ} (hτ : τ ∈ tierSet P F j) :
    IsPuncturedIsolated (partialUnion P.S (j + 1)) τ :=
  P.sigmoid.punctured_isolated hj (tierSet_mem_stratum P F hτ)

theorem tierSet_punctured_omega_succ {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} (hj : j < m) {τ : ℂ}
    (hτ : τ ∈ tierSet P F j) :
    ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∈ P.omega (j + 1) := by
  exact P.punctured_omega_succ_of_mem_stratum hj (tierSet_mem_stratum P F hτ)

theorem tierSet_mem_omega {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} (hj : j < m) {τ : ℂ}
    (hτ : τ ∈ tierSet P F j) :
    τ ∈ P.omega j :=
  P.mem_omega_of_mem_stratum hj (tierSet_mem_stratum P F hτ)

theorem tierSet_notMem_omega_of_lt {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j n : Nat} (hjn : j < n) {τ : ℂ}
    (hτ : τ ∈ tierSet P F j) :
    τ ∉ P.omega n := by
  simpa [ConcreteStratification.omega] using
    mem_partialUnion_of_mem (S := P.S) hjn (tierSet_mem_stratum P F hτ)

theorem tierSet_notMem_omega_succ {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} {τ : ℂ}
    (hτ : τ ∈ tierSet P F j) :
    τ ∉ P.omega (j + 1) :=
  tierSet_notMem_omega_of_lt P F (Nat.lt_succ_self j) hτ

theorem zeroFreeTierSet_subset_partialUnion_succ {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) {j : Nat} (hj : j < m) :
    zeroFreeTierSet P F j ⊆ partialUnion P.S (j + 1) := by
  intro τ hτ
  exact tierSet_subset_partialUnion_succ P F hj
    (zeroFreeTierSet_subset_tierSet P F j hτ)

theorem zeroFreeTierSet_subset_partialUnion_of_lt {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) {j n : Nat}
    (hjn : j < n) :
    zeroFreeTierSet P F j ⊆ partialUnion P.S n := by
  intro τ hτ
  exact tierSet_subset_partialUnion_of_lt P F hjn
    (zeroFreeTierSet_subset_tierSet P F j hτ)

theorem zeroFreeTierSet_subset_singularSet {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} (hj : j < m) :
    zeroFreeTierSet P F j ⊆ P.singularSet := by
  intro τ hτ
  exact tierSet_subset_singularSet P F hj
    (zeroFreeTierSet_subset_tierSet P F j hτ)

theorem zeroFreeTierSet_last_subset_singularSet {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) (hm : 0 < m) :
    zeroFreeTierSet P F (m - 1) ⊆ P.singularSet :=
  zeroFreeTierSet_subset_singularSet P F (by omega)

theorem zeroFreeTierSet_ne_real {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} (hj : j < m) {τ : ℂ}
    (hτ : τ ∈ zeroFreeTierSet P F j) (x : ℝ) :
    τ ≠ (x : ℂ) :=
  tierSet_ne_real P F hj (zeroFreeTierSet_subset_tierSet P F j hτ) x

theorem zeroFreeTierSet_notMem_realRange {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} (hj : j < m) {τ : ℂ}
    (hτ : τ ∈ zeroFreeTierSet P F j) :
    τ ∉ Set.range (fun x : ℝ => (x : ℂ)) :=
  tierSet_notMem_realRange P F hj (zeroFreeTierSet_subset_tierSet P F j hτ)

theorem zeroFreeTierSet_ne_zero {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} (hj : j < m) {τ : ℂ}
    (hτ : τ ∈ zeroFreeTierSet P F j) :
    τ ≠ 0 :=
  tierSet_ne_zero P F hj (zeroFreeTierSet_subset_tierSet P F j hτ)

theorem zeroFreeTierSet_punctured_isolated_partialUnion_succ {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) {j : Nat} (hj : j < m)
    {τ : ℂ} (hτ : τ ∈ zeroFreeTierSet P F j) :
    IsPuncturedIsolated (partialUnion P.S (j + 1)) τ :=
  tierSet_punctured_isolated_partialUnion_succ P F hj
    (zeroFreeTierSet_subset_tierSet P F j hτ)

theorem zeroFreeTierSet_punctured_omega_succ {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) {j : Nat} (hj : j < m)
    {τ : ℂ} (hτ : τ ∈ zeroFreeTierSet P F j) :
    ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∈ P.omega (j + 1) :=
  tierSet_punctured_omega_succ P F hj
    (zeroFreeTierSet_subset_tierSet P F j hτ)

theorem zeroFreeTierSet_mem_omega {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} (hj : j < m) {τ : ℂ}
    (hτ : τ ∈ zeroFreeTierSet P F j) :
    τ ∈ P.omega j :=
  tierSet_mem_omega P F hj (zeroFreeTierSet_subset_tierSet P F j hτ)

theorem zeroFreeTierSet_notMem_omega_of_lt {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) {j n : Nat}
    (hjn : j < n) {τ : ℂ} (hτ : τ ∈ zeroFreeTierSet P F j) :
    τ ∉ P.omega n :=
  tierSet_notMem_omega_of_lt P F hjn (zeroFreeTierSet_subset_tierSet P F j hτ)

theorem zeroFreeTierSet_notMem_omega_succ {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) {j : Nat} {τ : ℂ}
    (hτ : τ ∈ zeroFreeTierSet P F j) :
    τ ∉ P.omega (j + 1) :=
  tierSet_notMem_omega_succ P F (zeroFreeTierSet_subset_tierSet P F j hτ)

theorem tierSet_subset_acc_stratum_of_subset_acc_tier {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) {j k : Nat}
    (hchain : tierSet P F j ⊆ acc (tierSet P F k)) :
    tierSet P F j ⊆ acc (P.S k) := by
  intro τ hτ
  exact acc_mono (tierSet_subset_stratum P F k) (hchain hτ)

namespace TierSystem

theorem subset_partialUnion_succ {m : Nat} (A : TierSystem m) {j : Nat}
    (hj : j < m) :
    A.T j ⊆ partialUnion A.stratification.S (j + 1) :=
  tierSet_subset_partialUnion_succ A.stratification A.nestedFamily hj

theorem subset_partialUnion_of_lt {m : Nat} (A : TierSystem m) {j n : Nat}
    (hjn : j < n) :
    A.T j ⊆ partialUnion A.stratification.S n :=
  tierSet_subset_partialUnion_of_lt A.stratification A.nestedFamily hjn

theorem subset_singularSet {m : Nat} (A : TierSystem m) {j : Nat} (hj : j < m) :
    A.T j ⊆ A.stratification.singularSet :=
  tierSet_subset_singularSet A.stratification A.nestedFamily hj

theorem last_subset_singularSet {m : Nat} (A : TierSystem m) (hm : 0 < m) :
    A.T (m - 1) ⊆ A.stratification.singularSet :=
  tierSet_last_subset_singularSet A.stratification A.nestedFamily hm

theorem ne_real {m : Nat} (A : TierSystem m) {j : Nat} (hj : j < m)
    {τ : ℂ} (hτ : τ ∈ A.T j) (x : ℝ) :
    τ ≠ (x : ℂ) :=
  tierSet_ne_real A.stratification A.nestedFamily hj hτ x

theorem notMem_realRange {m : Nat} (A : TierSystem m) {j : Nat} (hj : j < m)
    {τ : ℂ} (hτ : τ ∈ A.T j) :
    τ ∉ Set.range (fun x : ℝ => (x : ℂ)) :=
  tierSet_notMem_realRange A.stratification A.nestedFamily hj hτ

theorem ne_zero {m : Nat} (A : TierSystem m) {j : Nat} (hj : j < m)
    {τ : ℂ} (hτ : τ ∈ A.T j) :
    τ ≠ 0 :=
  tierSet_ne_zero A.stratification A.nestedFamily hj hτ

theorem punctured_isolated_partialUnion_succ {m : Nat} (A : TierSystem m)
    {j : Nat} (hj : j < m) {τ : ℂ} (hτ : τ ∈ A.T j) :
    IsPuncturedIsolated (partialUnion A.stratification.S (j + 1)) τ :=
  tierSet_punctured_isolated_partialUnion_succ
    A.stratification A.nestedFamily hj hτ

theorem punctured_omega_succ {m : Nat} (A : TierSystem m) {j : Nat}
    (hj : j < m) {τ : ℂ} (hτ : τ ∈ A.T j) :
    ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∈ A.stratification.omega (j + 1) :=
  tierSet_punctured_omega_succ A.stratification A.nestedFamily hj hτ

theorem mem_omega {m : Nat} (A : TierSystem m) {j : Nat} (hj : j < m)
    {τ : ℂ} (hτ : τ ∈ A.T j) :
    τ ∈ A.stratification.omega j :=
  tierSet_mem_omega A.stratification A.nestedFamily hj hτ

theorem notMem_omega_of_lt {m : Nat} (A : TierSystem m) {j n : Nat}
    (hjn : j < n) {τ : ℂ} (hτ : τ ∈ A.T j) :
    τ ∉ A.stratification.omega n :=
  tierSet_notMem_omega_of_lt A.stratification A.nestedFamily hjn hτ

theorem notMem_omega_succ {m : Nat} (A : TierSystem m) {j : Nat}
    {τ : ℂ} (hτ : τ ∈ A.T j) :
    τ ∉ A.stratification.omega (j + 1) :=
  tierSet_notMem_omega_succ A.stratification A.nestedFamily hτ

theorem T0_subset_partialUnion_succ {m : Nat} (A : TierSystem m) {j : Nat}
    (hj : j < m) :
    A.T0 j ⊆ partialUnion A.stratification.S (j + 1) :=
  zeroFreeTierSet_subset_partialUnion_succ A.stratification A.nestedFamily hj

theorem T0_subset_partialUnion_of_lt {m : Nat} (A : TierSystem m) {j n : Nat}
    (hjn : j < n) :
    A.T0 j ⊆ partialUnion A.stratification.S n :=
  zeroFreeTierSet_subset_partialUnion_of_lt A.stratification A.nestedFamily hjn

theorem T0_subset_singularSet {m : Nat} (A : TierSystem m) {j : Nat}
    (hj : j < m) :
    A.T0 j ⊆ A.stratification.singularSet :=
  zeroFreeTierSet_subset_singularSet A.stratification A.nestedFamily hj

theorem T0_last_subset_singularSet {m : Nat} (A : TierSystem m) (hm : 0 < m) :
    A.T0 (m - 1) ⊆ A.stratification.singularSet :=
  zeroFreeTierSet_last_subset_singularSet A.stratification A.nestedFamily hm

theorem T0_ne_real {m : Nat} (A : TierSystem m) {j : Nat} (hj : j < m)
    {τ : ℂ} (hτ : τ ∈ A.T0 j) (x : ℝ) :
    τ ≠ (x : ℂ) :=
  zeroFreeTierSet_ne_real A.stratification A.nestedFamily hj hτ x

theorem T0_notMem_realRange {m : Nat} (A : TierSystem m) {j : Nat} (hj : j < m)
    {τ : ℂ} (hτ : τ ∈ A.T0 j) :
    τ ∉ Set.range (fun x : ℝ => (x : ℂ)) :=
  zeroFreeTierSet_notMem_realRange A.stratification A.nestedFamily hj hτ

theorem T0_ne_zero {m : Nat} (A : TierSystem m) {j : Nat} (hj : j < m)
    {τ : ℂ} (hτ : τ ∈ A.T0 j) :
    τ ≠ 0 :=
  zeroFreeTierSet_ne_zero A.stratification A.nestedFamily hj hτ

theorem T0_punctured_isolated_partialUnion_succ {m : Nat} (A : TierSystem m)
    {j : Nat} (hj : j < m) {τ : ℂ} (hτ : τ ∈ A.T0 j) :
    IsPuncturedIsolated (partialUnion A.stratification.S (j + 1)) τ :=
  zeroFreeTierSet_punctured_isolated_partialUnion_succ
    A.stratification A.nestedFamily hj hτ

theorem T0_punctured_omega_succ {m : Nat} (A : TierSystem m) {j : Nat}
    (hj : j < m) {τ : ℂ} (hτ : τ ∈ A.T0 j) :
    ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∈ A.stratification.omega (j + 1) :=
  zeroFreeTierSet_punctured_omega_succ A.stratification A.nestedFamily hj hτ

theorem T0_mem_omega {m : Nat} (A : TierSystem m) {j : Nat} (hj : j < m)
    {τ : ℂ} (hτ : τ ∈ A.T0 j) :
    τ ∈ A.stratification.omega j :=
  zeroFreeTierSet_mem_omega A.stratification A.nestedFamily hj hτ

theorem T0_notMem_omega_of_lt {m : Nat} (A : TierSystem m) {j n : Nat}
    (hjn : j < n) {τ : ℂ} (hτ : τ ∈ A.T0 j) :
    τ ∉ A.stratification.omega n :=
  zeroFreeTierSet_notMem_omega_of_lt A.stratification A.nestedFamily hjn hτ

theorem T0_notMem_omega_succ {m : Nat} (A : TierSystem m) {j : Nat}
    {τ : ℂ} (hτ : τ ∈ A.T0 j) :
    τ ∉ A.stratification.omega (j + 1) :=
  zeroFreeTierSet_notMem_omega_succ A.stratification A.nestedFamily hτ

theorem strataSystem {m : Nat} (A : TierSystem m) :
    StrataSystem A.stratification.S m :=
  A.stratification.strataSystem

theorem closed_partialUnion {m : Nat} (A : TierSystem m) {n : Nat} (hn : n ≤ m) :
    IsClosed (partialUnion A.stratification.S n) :=
  A.stratification.closed_partialUnion hn

theorem singularSet_closed {m : Nat} (A : TierSystem m) :
    IsClosed A.stratification.singularSet :=
  A.stratification.singularSet_closed

theorem singularSet_countable {m : Nat} (A : TierSystem m) :
    A.stratification.singularSet.Countable :=
  A.stratification.singularSet_countable

theorem singularSet_avoids_real {m : Nat} (A : TierSystem m) (x : ℝ) :
    (x : ℂ) ∉ A.stratification.singularSet :=
  A.stratification.singularSet_avoids_real x

theorem acc_tier_subset_acc_stratum {m : Nat} (A : TierSystem m) (j : Nat) :
    acc (A.T j) ⊆ acc (A.stratification.S j) :=
  acc_mono (A.subset_stratum j)

theorem acc_tier_subset_acc_partialUnion_of_lt {m : Nat} (A : TierSystem m)
    {j n : Nat} (hjn : j < n) :
    acc (A.T j) ⊆ acc (partialUnion A.stratification.S n) :=
  acc_mono (A.subset_partialUnion_of_lt hjn)

theorem acc_tier_subset_acc_singularSet {m : Nat} (A : TierSystem m)
    {j : Nat} (hj : j < m) :
    acc (A.T j) ⊆ acc A.stratification.singularSet :=
  acc_mono (A.subset_singularSet hj)

theorem subset_acc_stratum_of_subset_acc_tier {m : Nat} (A : TierSystem m)
    {j k : Nat} (hchain : A.T j ⊆ acc (A.T k)) :
    A.T j ⊆ acc (A.stratification.S k) := by
  intro τ hτ
  exact acc_mono (A.subset_stratum k) (hchain hτ)

theorem subset_acc_stratum_succ_of_subset_acc_succ {m : Nat} (A : TierSystem m)
    {j : Nat} (hchain : A.T j ⊆ acc (A.T (j + 1))) :
    A.T j ⊆ acc (A.stratification.S (j + 1)) :=
  A.subset_acc_stratum_of_subset_acc_tier hchain

end TierSystem

end TransformerIdentifiability.NLayer
