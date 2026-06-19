import AnyLayerIdentifiabilityProof.NLayer.Analytic.A1Identification
import AnyLayerIdentifiabilityProof.NLayer.Step1.LastTierBlowup

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Step 1 pole transfer

Owner shard for Claim D: transfer last-tier generic blow-up to the unknown singular set
using tail agreement and pole transfer.
-/

/-- Agreement on a real tail gives the punctured local frequent equality required by
the pole-transfer interface at any real basepoint inside that tail. -/
theorem frequently_equal_of_eqOn_real_tail {F G : ℂ -> ℂ} {T0 x0 : ℝ}
    (hx0 : T0 < x0)
    (hEq : ∀ t : ℝ, T0 < t -> F (t : ℂ) = G (t : ℂ)) :
    ∃ᶠ z in nhdsWithin (x0 : ℂ) ({(x0 : ℂ)}ᶜ : Set ℂ), F z = G z := by
  rw [frequently_nhdsWithin_iff]
  refine mem_closure_iff_frequently.mp ?_
  have hx_real : x0 ∈ closure (Set.Ioi x0 : Set ℝ) := by
    rw [closure_Ioi (α := ℝ) x0]
    simp [Set.mem_Ici]
  have hx_complex :
      (x0 : ℂ) ∈ closure (((fun t : ℝ => (t : ℂ)) '' (Set.Ioi x0 : Set ℝ))) := by
    simpa using mem_closure_image (Complex.continuous_ofReal.continuousAt) hx_real
  refine closure_mono ?_ hx_complex
  intro z hz
  rcases hz with ⟨t, ht, rfl⟩
  have hxt : x0 < t := Set.mem_Ioi.mp ht
  constructor
  · exact hEq t (lt_trans hx0 hxt)
  · simp [hxt.ne']

/-- Claim-D transfer package for the last generic tier.

`unprimed` is the unknown stratification whose singular set will receive the transferred
poles, while `A` is the generic/primed tier system.  The final field records the Claim C
observable blow-up conclusion, either directly or via `LastTierBlowup`. -/
structure LastTierTransferData {m : Nat} (unprimed : ConcreteStratification m)
    (A : TierSystem m) where
  basepoint : ℂ
  unprimed_closed : IsClosed unprimed.singularSet
  unprimed_countable : unprimed.singularSet.Countable
  primed_countable : A.stratification.singularSet.Countable
  unprimed_analytic :
    AnalyticOnNhd ℂ unprimed.observable unprimed.singularSetᶜ
  primed_analytic :
    AnalyticOnNhd ℂ A.stratification.observable A.stratification.singularSetᶜ
  basepoint_regular :
    basepoint ∈ (unprimed.singularSet ∪ A.stratification.singularSet)ᶜ
  frequently_equal :
    ∃ᶠ z in nhdsWithin basepoint ({basepoint}ᶜ : Set ℂ),
      unprimed.observable z = A.stratification.observable z
  unprimed_continuousAt_regular :
    ∀ τ, τ ∉ unprimed.singularSet -> ContinuousAt unprimed.observable τ
  last_tier_isolated :
    ∀ τ, τ ∈ A.T (m - 1) -> IsPuncturedIsolated A.stratification.singularSet τ
  last_tier_blowsUp :
    ∀ τ, τ ∈ A.T (m - 1) -> BlowsUpAt A.stratification.observable τ

namespace LastTierTransferData

variable {m : Nat} {unprimed : ConcreteStratification m} {A : TierSystem m}

/-- Any real basepoint is regular for both concrete stratifications. -/
theorem real_basepoint_regular (basepoint : ℝ) :
    (basepoint : ℂ) ∈
      (unprimed.singularSet ∪ A.stratification.singularSet)ᶜ := by
  rw [Set.mem_compl_iff, Set.mem_union]
  exact not_or.mpr
    ⟨unprimed.singularSet_avoids_real basepoint,
      A.stratification.singularSet_avoids_real basepoint⟩

/-- Build the transfer package from the concrete stratification interfaces, leaving only
the real-tail agreement point and Claim-C blow-up conclusion as inputs. -/
def ofConcrete (hm : 0 < m) (basepoint : ℂ)
    (basepoint_regular :
      basepoint ∈ (unprimed.singularSet ∪ A.stratification.singularSet)ᶜ)
    (frequently_equal :
      ∃ᶠ z in nhdsWithin basepoint ({basepoint}ᶜ : Set ℂ),
        unprimed.observable z = A.stratification.observable z)
    (last_tier_blowsUp :
      ∀ τ, τ ∈ A.T (m - 1) -> BlowsUpAt A.stratification.observable τ) :
    LastTierTransferData unprimed A where
  basepoint := basepoint
  unprimed_closed := unprimed.singularSet_closed
  unprimed_countable := unprimed.singularSet_countable
  primed_countable := A.stratification.singularSet_countable
  unprimed_analytic := unprimed.observable_analyticOn_singularCompl
  primed_analytic := A.stratification.observable_analyticOn_singularCompl
  basepoint_regular := basepoint_regular
  frequently_equal := frequently_equal
  unprimed_continuousAt_regular := fun τ hτ =>
    unprimed.observable_continuousAt_of_regular hτ
  last_tier_isolated := by
    intro τ hτ
    have hlt : m - 1 < m := by omega
    have hIso :
        IsPuncturedIsolated
          (partialUnion A.stratification.S ((m - 1) + 1)) τ :=
      A.punctured_isolated_partialUnion_succ (j := m - 1) hlt hτ
    have hlast : (m - 1) + 1 = m := by omega
    simpa [ConcreteStratification.singularSet, hlast] using hIso
  last_tier_blowsUp := last_tier_blowsUp

/-- Build the transfer package from the concrete stratification interfaces and the
packaged Claim C last-tier blow-up result. -/
def ofConcreteWithBlowup (hm : 0 < m) (basepoint : ℂ)
    (basepoint_regular :
      basepoint ∈ (unprimed.singularSet ∪ A.stratification.singularSet)ᶜ)
    (frequently_equal :
      ∃ᶠ z in nhdsWithin basepoint ({basepoint}ᶜ : Set ℂ),
        unprimed.observable z = A.stratification.observable z)
    (B : LastTierBlowup A) :
    LastTierTransferData unprimed A :=
  LastTierTransferData.ofConcrete (unprimed := unprimed) (A := A)
    hm basepoint basepoint_regular frequently_equal
    (fun _ hτ => B.observable_blowsUpAt hτ)

/-- Build the transfer package from real-tail agreement and the packaged Claim C
last-tier blow-up result. -/
def ofConcreteWithBlowupRealTail (hm : 0 < m) (basepoint T0 : ℝ)
    (tail_basepoint : T0 < basepoint)
    (basepoint_regular :
      (basepoint : ℂ) ∈ (unprimed.singularSet ∪ A.stratification.singularSet)ᶜ)
    (eqOnTail :
      ∀ t : ℝ, T0 < t ->
        unprimed.observable (t : ℂ) = A.stratification.observable (t : ℂ))
    (B : LastTierBlowup A) :
    LastTierTransferData unprimed A :=
  LastTierTransferData.ofConcreteWithBlowup (unprimed := unprimed) (A := A)
    hm (basepoint : ℂ) basepoint_regular
    (frequently_equal_of_eqOn_real_tail tail_basepoint eqOnTail)
    B

/-- Build the transfer package from only real-tail equality and packaged Claim C
blow-up, choosing `T0 + 1` as a regular real basepoint. -/
def ofConcreteWithBlowupOnRealTail (hm : 0 < m) (T0 : ℝ)
    (eqOnTail :
      ∀ t : ℝ, T0 < t ->
        unprimed.observable (t : ℂ) = A.stratification.observable (t : ℂ))
    (B : LastTierBlowup A) :
    LastTierTransferData unprimed A :=
  LastTierTransferData.ofConcreteWithBlowupRealTail
    (unprimed := unprimed) (A := A)
    hm (T0 + 1) T0 (by linarith)
    (LastTierTransferData.real_basepoint_regular
      (unprimed := unprimed) (A := A) (T0 + 1))
    eqOnTail B

/-- Build the transfer package from only real-tail equality and concrete Claim C
obligations, choosing `T0 + 1` as a regular real basepoint. -/
def ofConcreteWithConcreteDataOnRealTail (hm : 0 < m) (T0 : ℝ)
    (eqOnTail :
      ∀ t : ℝ, T0 < t ->
        unprimed.observable (t : ℂ) = A.stratification.observable (t : ℂ))
    (C : LastTierConcreteData A) :
    LastTierTransferData unprimed A :=
  LastTierTransferData.ofConcreteWithBlowupOnRealTail
    (unprimed := unprimed) (A := A)
    hm T0 eqOnTail (C.toLastTierBlowup hm)

/-- Apply the abstract pole-transfer lemma to the packaged last-tier data. -/
theorem subset_singularSet (D : LastTierTransferData unprimed A) :
    A.T (m - 1) ⊆ unprimed.singularSet := by
  exact TransformerIdentifiability.NLayer.transferred_tier_subset
    (E_F := unprimed.singularSet)
    (E_G := A.stratification.singularSet)
    (T := A.T (m - 1))
    (F := unprimed.observable)
    (G := A.stratification.observable)
    (z0 := D.basepoint)
    D.unprimed_closed
    D.unprimed_countable
    D.primed_countable
    D.unprimed_analytic
    D.primed_analytic
    D.basepoint_regular
    D.frequently_equal
    D.unprimed_continuousAt_regular
    D.last_tier_isolated
    D.last_tier_blowsUp

/-- The same transfer conclusion, unfolded to the concrete partial-union notation. -/
theorem subset_partialUnion (D : LastTierTransferData unprimed A) :
    A.T (m - 1) ⊆ partialUnion unprimed.S m := by
  simpa [ConcreteStratification.singularSet] using D.subset_singularSet

/-- Direct Claim-D partial-union conclusion from only real-tail agreement and concrete
Claim C obligations. -/
theorem subset_partialUnion_ofConcreteDataOnRealTail (hm : 0 < m) (T0 : ℝ)
    (eqOnTail :
      ∀ t : ℝ, T0 < t ->
        unprimed.observable (t : ℂ) = A.stratification.observable (t : ℂ))
    (C : LastTierConcreteData A) :
    A.T (m - 1) ⊆ partialUnion unprimed.S m :=
  (LastTierTransferData.ofConcreteWithConcreteDataOnRealTail
    (unprimed := unprimed) (A := A)
    hm T0 eqOnTail C).subset_partialUnion

end LastTierTransferData

/-! ## Additive zero-free last-tier transfer -/

/-- Claim-D transfer package for the additive zero-free last generic tier.

This is the zero-free analogue of `LastTierTransferData`: all last-tier hypotheses are
restricted to `A.T0 (m - 1)`, while the analytic transfer interface and target
unprimed singular set are unchanged. -/
structure ZeroFreeLastTierTransferData {m : Nat} (unprimed : ConcreteStratification m)
    (A : TierSystem m) where
  basepoint : ℂ
  unprimed_closed : IsClosed unprimed.singularSet
  unprimed_countable : unprimed.singularSet.Countable
  primed_countable : A.stratification.singularSet.Countable
  unprimed_analytic :
    AnalyticOnNhd ℂ unprimed.observable unprimed.singularSetᶜ
  primed_analytic :
    AnalyticOnNhd ℂ A.stratification.observable A.stratification.singularSetᶜ
  basepoint_regular :
    basepoint ∈ (unprimed.singularSet ∪ A.stratification.singularSet)ᶜ
  frequently_equal :
    ∃ᶠ z in nhdsWithin basepoint ({basepoint}ᶜ : Set ℂ),
      unprimed.observable z = A.stratification.observable z
  unprimed_continuousAt_regular :
    ∀ τ, τ ∉ unprimed.singularSet -> ContinuousAt unprimed.observable τ
  last_tier_isolated :
    ∀ τ, τ ∈ A.T0 (m - 1) -> IsPuncturedIsolated A.stratification.singularSet τ
  last_tier_blowsUp :
    ∀ τ, τ ∈ A.T0 (m - 1) -> BlowsUpAt A.stratification.observable τ

namespace ZeroFreeLastTierTransferData

variable {m : Nat} {unprimed : ConcreteStratification m} {A : TierSystem m}

/-- Build the zero-free transfer package from the concrete stratification interfaces,
leaving only the agreement point and zero-free Claim-C blow-up conclusion as inputs. -/
def ofConcrete (hm : 0 < m) (basepoint : ℂ)
    (basepoint_regular :
      basepoint ∈ (unprimed.singularSet ∪ A.stratification.singularSet)ᶜ)
    (frequently_equal :
      ∃ᶠ z in nhdsWithin basepoint ({basepoint}ᶜ : Set ℂ),
        unprimed.observable z = A.stratification.observable z)
    (last_tier_blowsUp :
      ∀ τ, τ ∈ A.T0 (m - 1) -> BlowsUpAt A.stratification.observable τ) :
    ZeroFreeLastTierTransferData unprimed A where
  basepoint := basepoint
  unprimed_closed := unprimed.singularSet_closed
  unprimed_countable := unprimed.singularSet_countable
  primed_countable := A.stratification.singularSet_countable
  unprimed_analytic := unprimed.observable_analyticOn_singularCompl
  primed_analytic := A.stratification.observable_analyticOn_singularCompl
  basepoint_regular := basepoint_regular
  frequently_equal := frequently_equal
  unprimed_continuousAt_regular := fun τ hτ =>
    unprimed.observable_continuousAt_of_regular hτ
  last_tier_isolated := by
    intro τ hτ0
    have hτ : τ ∈ A.T (m - 1) := A.T0_subset_T (m - 1) hτ0
    have hlt : m - 1 < m := by omega
    have hIso :
        IsPuncturedIsolated
          (partialUnion A.stratification.S ((m - 1) + 1)) τ :=
      A.punctured_isolated_partialUnion_succ (j := m - 1) hlt hτ
    have hlast : (m - 1) + 1 = m := by omega
    simpa [ConcreteStratification.singularSet, hlast] using hIso
  last_tier_blowsUp := last_tier_blowsUp

/-- Build the zero-free transfer package from packaged zero-free Claim C blow-up. -/
def ofConcreteWithBlowup (hm : 0 < m) (basepoint : ℂ)
    (basepoint_regular :
      basepoint ∈ (unprimed.singularSet ∪ A.stratification.singularSet)ᶜ)
    (frequently_equal :
      ∃ᶠ z in nhdsWithin basepoint ({basepoint}ᶜ : Set ℂ),
        unprimed.observable z = A.stratification.observable z)
    (B : ZeroFreeLastTierBlowup A) :
    ZeroFreeLastTierTransferData unprimed A :=
  ZeroFreeLastTierTransferData.ofConcrete (unprimed := unprimed) (A := A)
    hm basepoint basepoint_regular frequently_equal
    (fun _ hτ0 => B.observable_blowsUpAt hτ0)

/-- Build the zero-free transfer package from real-tail agreement and packaged
zero-free Claim C blow-up. -/
def ofConcreteWithBlowupRealTail (hm : 0 < m) (basepoint T0 : ℝ)
    (tail_basepoint : T0 < basepoint)
    (basepoint_regular :
      (basepoint : ℂ) ∈ (unprimed.singularSet ∪ A.stratification.singularSet)ᶜ)
    (eqOnTail :
      ∀ t : ℝ, T0 < t ->
        unprimed.observable (t : ℂ) = A.stratification.observable (t : ℂ))
    (B : ZeroFreeLastTierBlowup A) :
    ZeroFreeLastTierTransferData unprimed A :=
  ZeroFreeLastTierTransferData.ofConcreteWithBlowup
    (unprimed := unprimed) (A := A)
    hm (basepoint : ℂ) basepoint_regular
    (frequently_equal_of_eqOn_real_tail tail_basepoint eqOnTail)
    B

/-- Build the zero-free transfer package from only real-tail equality and packaged
zero-free Claim C blow-up, choosing `T0 + 1` as a regular real basepoint. -/
def ofConcreteWithBlowupOnRealTail (hm : 0 < m) (T0 : ℝ)
    (eqOnTail :
      ∀ t : ℝ, T0 < t ->
        unprimed.observable (t : ℂ) = A.stratification.observable (t : ℂ))
    (B : ZeroFreeLastTierBlowup A) :
    ZeroFreeLastTierTransferData unprimed A :=
  ZeroFreeLastTierTransferData.ofConcreteWithBlowupRealTail
    (unprimed := unprimed) (A := A)
    hm (T0 + 1) T0 (by linarith)
    (LastTierTransferData.real_basepoint_regular
      (unprimed := unprimed) (A := A) (T0 + 1))
    eqOnTail B

/-- Build the zero-free transfer package from only real-tail equality and concrete
Claim C obligations, choosing `T0 + 1` as a regular real basepoint. -/
def ofConcreteWithConcreteDataOnRealTail (hm : 0 < m) (T0 : ℝ)
    (eqOnTail :
      ∀ t : ℝ, T0 < t ->
        unprimed.observable (t : ℂ) = A.stratification.observable (t : ℂ))
    (C : LastTierConcreteData A) :
    ZeroFreeLastTierTransferData unprimed A :=
  ZeroFreeLastTierTransferData.ofConcreteWithBlowupOnRealTail
    (unprimed := unprimed) (A := A)
    hm T0 eqOnTail (C.toZeroFreeLastTierBlowup hm)

/-- Apply the abstract pole-transfer lemma to the packaged zero-free last-tier data. -/
theorem subset_singularSet (D : ZeroFreeLastTierTransferData unprimed A) :
    A.T0 (m - 1) ⊆ unprimed.singularSet := by
  exact TransformerIdentifiability.NLayer.transferred_tier_subset
    (E_F := unprimed.singularSet)
    (E_G := A.stratification.singularSet)
    (T := A.T0 (m - 1))
    (F := unprimed.observable)
    (G := A.stratification.observable)
    (z0 := D.basepoint)
    D.unprimed_closed
    D.unprimed_countable
    D.primed_countable
    D.unprimed_analytic
    D.primed_analytic
    D.basepoint_regular
    D.frequently_equal
    D.unprimed_continuousAt_regular
    D.last_tier_isolated
    D.last_tier_blowsUp

/-- The zero-free transfer conclusion, unfolded to the concrete partial-union notation. -/
theorem subset_partialUnion (D : ZeroFreeLastTierTransferData unprimed A) :
    A.T0 (m - 1) ⊆ partialUnion unprimed.S m := by
  simpa [ConcreteStratification.singularSet] using D.subset_singularSet

/-- Direct zero-free Claim-D partial-union conclusion from only real-tail agreement and
concrete Claim C obligations. -/
theorem subset_partialUnion_ofConcreteDataOnRealTail (hm : 0 < m) (T0 : ℝ)
    (eqOnTail :
      ∀ t : ℝ, T0 < t ->
        unprimed.observable (t : ℂ) = A.stratification.observable (t : ℂ))
    (C : LastTierConcreteData A) :
    A.T0 (m - 1) ⊆ partialUnion unprimed.S m :=
  (ZeroFreeLastTierTransferData.ofConcreteWithConcreteDataOnRealTail
    (unprimed := unprimed) (A := A)
    hm T0 eqOnTail C).subset_partialUnion

end ZeroFreeLastTierTransferData

/-- Zero-free Claim D endpoint from real-tail agreement and concrete Claim C
obligations, unfolded to the concrete partial-union notation. -/
theorem transferred_zeroFreeLastTier_subset_partialUnion_ofConcreteDataOnRealTail
    {m : Nat} {unprimed : ConcreteStratification m} {A : TierSystem m}
    (hm : 0 < m) (T0 : ℝ)
    (eqOnTail :
      ∀ t : ℝ, T0 < t ->
        unprimed.observable (t : ℂ) = A.stratification.observable (t : ℂ))
    (C : LastTierConcreteData A) :
    A.T0 (m - 1) ⊆ partialUnion unprimed.S m :=
  ZeroFreeLastTierTransferData.subset_partialUnion_ofConcreteDataOnRealTail
    (unprimed := unprimed) (A := A)
    hm T0 eqOnTail C

end TransformerIdentifiability.NLayer
