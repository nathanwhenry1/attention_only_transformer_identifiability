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

/-- Partial unions are monotone in the cutoff. -/
theorem partialUnion_mono_right {S : Nat -> Set ℂ} {n k : Nat} (hnk : n ≤ k) :
    partialUnion S n ⊆ partialUnion S k := by
  rintro τ ⟨j, hj, hτ⟩
  exact ⟨j, Nat.lt_of_lt_of_le hj hnk, hτ⟩

/-! ## Shape and access lemmas -/

theorem tierSet_mem_stratum {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} {τ : ℂ} (hτ : τ ∈ tierSet P F j) :
    τ ∈ P.S j :=
  hτ.1

theorem tierSet_mem_region {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} {τ : ℂ} (hτ : τ ∈ tierSet P F j) :
    gatePrefix P j τ ∈ F.region j :=
  hτ.2

theorem zeroFreeTierSet_mem_stratum {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} {τ : ℂ} (hτ : τ ∈ zeroFreeTierSet P F j) :
    τ ∈ P.S j :=
  hτ.1

theorem zeroFreeTierSet_mem_zeroFreeRegion {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} {τ : ℂ} (hτ : τ ∈ zeroFreeTierSet P F j) :
    gatePrefix P j τ ∈ F.zeroFreeRegion j :=
  hτ.2

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

namespace TierSystem

theorem mem_stratum {m : Nat} (A : TierSystem m) {j : Nat} {τ : ℂ}
    (hτ : τ ∈ A.T j) :
    τ ∈ A.stratification.S j :=
  tierSet_mem_stratum A.stratification A.nestedFamily hτ

theorem mem_region {m : Nat} (A : TierSystem m) {j : Nat} {τ : ℂ}
    (hτ : τ ∈ A.T j) :
    gatePrefix A.stratification j τ ∈ A.nestedFamily.region j :=
  tierSet_mem_region A.stratification A.nestedFamily hτ

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

end TierSystem

/-! ## First-tier nonemptiness and infinitude -/

theorem firstPoleSet_nonempty (b lambda : ℝ) :
    (firstPoleSet b lambda).Nonempty :=
  ⟨sigmoidPole b lambda 0, sigmoidPole_mem_firstPoleSet b lambda 0⟩

theorem tierSet_zero_eq_firstPoleSet_of_lambda_ne_zero {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) (hlambda : P.lambda1 ≠ 0) :
    tierSet P F 0 = firstPoleSet P.b P.lambda1 := by
  rw [tierSet_zero_eq_stratum, P.first_stratum_eq_firstPoleSet hlambda]

theorem firstPoleSet_subset_tierSet_zero_of_lambda_ne_zero {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) (hlambda : P.lambda1 ≠ 0) :
    firstPoleSet P.b P.lambda1 ⊆ tierSet P F 0 := by
  rw [tierSet_zero_eq_firstPoleSet_of_lambda_ne_zero P F hlambda]

namespace TierSystem

theorem firstPoleSet_subset_zero_of_lambda_ne_zero {m : Nat} (A : TierSystem m)
    (hlambda : A.stratification.lambda1 ≠ 0) :
    firstPoleSet A.stratification.b A.stratification.lambda1 ⊆ A.T 0 :=
  firstPoleSet_subset_tierSet_zero_of_lambda_ne_zero
    A.stratification A.nestedFamily hlambda

end TierSystem

/-! ## Tier regularity facts -/

theorem tierSet_subset_singularSet {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} (hj : j < m) :
    tierSet P F j ⊆ P.singularSet := by
  intro τ hτ
  exact ⟨j, hj, tierSet_mem_stratum P F hτ⟩

theorem tierSet_ne_real {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} (hj : j < m) {τ : ℂ}
    (hτ : τ ∈ tierSet P F j) (x : ℝ) :
    τ ≠ (x : ℂ) := by
  intro hτx
  have hx : (x : ℂ) ∈ P.S j := by
    simpa [hτx] using tierSet_mem_stratum P F hτ
  exact P.stratum_avoids_real hj x hx

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

theorem zeroFreeTierSet_ne_zero {m : Nat} (P : ConcreteStratification m)
    (F : NestedTailFamily) {j : Nat} (hj : j < m) {τ : ℂ}
    (hτ : τ ∈ zeroFreeTierSet P F j) :
    τ ≠ 0 :=
  tierSet_ne_zero P F hj (zeroFreeTierSet_subset_tierSet P F j hτ)

theorem zeroFreeTierSet_punctured_omega_succ {m : Nat}
    (P : ConcreteStratification m) (F : NestedTailFamily) {j : Nat} (hj : j < m)
    {τ : ℂ} (hτ : τ ∈ zeroFreeTierSet P F j) :
    ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∈ P.omega (j + 1) :=
  tierSet_punctured_omega_succ P F hj
    (zeroFreeTierSet_subset_tierSet P F j hτ)

namespace TierSystem

theorem subset_singularSet {m : Nat} (A : TierSystem m) {j : Nat} (hj : j < m) :
    A.T j ⊆ A.stratification.singularSet :=
  tierSet_subset_singularSet A.stratification A.nestedFamily hj

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

theorem T0_ne_zero {m : Nat} (A : TierSystem m) {j : Nat} (hj : j < m)
    {τ : ℂ} (hτ : τ ∈ A.T0 j) :
    τ ≠ 0 :=
  zeroFreeTierSet_ne_zero A.stratification A.nestedFamily hj hτ

theorem T0_punctured_omega_succ {m : Nat} (A : TierSystem m) {j : Nat}
    (hj : j < m) {τ : ℂ} (hτ : τ ∈ A.T0 j) :
    ∀ᶠ z in nhdsWithin τ ({τ}ᶜ : Set ℂ), z ∈ A.stratification.omega (j + 1) :=
  zeroFreeTierSet_punctured_omega_succ A.stratification A.nestedFamily hj hτ

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

end TierSystem

end TransformerIdentifiability.NLayer
