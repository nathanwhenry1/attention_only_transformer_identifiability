import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeTrichotomyMatching

set_option autoImplicit false

open Filter Topology Matrix

namespace TransformerIdentifiability.NLayer

/-!
# R4: canonical regular-quadric trichotomy matching gates

The all-dial actual-gate bridge in `CascadeTrichotomyMatching` is stronger than the
regular-quadric matching step needs.  This module records actual gate agreement only
for the canonical product-patch dials selected by
`texMatchingRegularQuadricDialPathData`, then builds the closed-recursion obligation
directly from those canonical dials.
-/

/-- Actual running gate agreement along the canonical regular-quadric dials used by
matching.  This avoids requiring the same agreement for arbitrary dial directions with
the same endpoint. -/
structure TexTrichotomyMatchingCanonicalActualGateData
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar) : Prop where
  unprimed_gate_eventuallyEq :
    ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
      let δ :=
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      ∀ n : Nat, 1 ≤ n → n < L + 1 →
        (fun τ : ℝ => frecRunningGate r θ (DialPathData.probe δ) n τ)
          =ᶠ[atTop]
        (fun τ : ℝ => T.unprimed n (p, t) τ)
  primed_gate_eventuallyEq :
    ∀ (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J),
      let δ :=
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      ∀ n : Nat, 1 ≤ n → n < L + 1 →
        (fun τ : ℝ => frecRunningGate r θ' (DialPathData.probe δ) n τ)
          =ᶠ[atTop]
        (fun τ : ℝ => T.primed n (p, t) τ)

/-- Canonical actual running gates over a sign region.

For points of the sign region, this evaluates the actual recursive Frec gate along the
canonical regular-quadric dial through that point.  Outside the sign region the value is
irrelevant to the matching product patch, so we set it to `0`. -/
noncomputable def canonicalFrecGateAlongSignRegion
    (r : Nat) {L d : Nat} {θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (θrun : Params (L + 1) d) : GateAlongBase d := by
  classical
  exact fun n x τ =>
    if hx : x ∈ signRegion.U then
      let δ :=
        DialPathData.ofRegularQuadric
          (Params.headAttention θ') (Real.log (r : ℝ)) x.1 x.2
          (signRegion.point_on_quadric x hx)
          (signRegion.point_regular x hx)
          (signRegion.t_pos hx)
          (signRegion.t_lt_one hx)
      frecRunningGate r θrun (DialPathData.probe δ) n τ
    else
      0

/-- Each `w` coordinate of a regular-quadric dial is eventually bounded. -/
noncomputable def eventuallyBoundedReal_dialW_coord {d : Nat}
    (p : ProbePair d) (c : ℝ) (y : Fin d -> ℝ) (i : Fin d) :
    EventuallyBoundedReal (fun τ : ℝ => dialW p c y τ i) :=
  EventuallyBoundedReal.of_bound (|p.1 i| + |c * y i|)
    (add_nonneg (abs_nonneg (p.1 i)) (abs_nonneg (c * y i))) 1 (by
      intro τ hτ
      have hterm : |(c / τ) * y i| ≤ |c * y i| := by
        have hτ_nonneg : 0 ≤ τ := le_trans zero_le_one hτ
        calc
          |c / τ * y i| = |c * y i| / τ := by
            rw [abs_mul, abs_div, abs_mul, abs_of_nonneg hτ_nonneg]
            ring
          _ ≤ |c * y i| := div_le_self (abs_nonneg (c * y i)) hτ
      calc
        |dialW p c y τ i| = |p.1 i - (c / τ) * y i| := by
          simp [dialW]
        _ = |p.1 i + -((c / τ) * y i)| := by ring_nf
        _ ≤ |p.1 i| + |-((c / τ) * y i)| := abs_add_le (p.1 i) (-((c / τ) * y i))
        _ = |p.1 i| + |(c / τ) * y i| := by rw [abs_neg]
        _ ≤ |p.1 i| + |c * y i| := add_le_add (le_refl |p.1 i|) hterm)

/-- Each `v` coordinate of a regular-quadric dial is eventually bounded. -/
noncomputable def eventuallyBoundedReal_dialV_coord {d : Nat}
    (p : ProbePair d) (c : ℝ) (y : Fin d -> ℝ) (i : Fin d) :
    EventuallyBoundedReal (fun τ : ℝ => dialV p c y τ i) :=
  EventuallyBoundedReal.of_bound (|p.2 i| + |c * y i|)
    (add_nonneg (abs_nonneg (p.2 i)) (abs_nonneg (c * y i))) 1 (by
      intro τ hτ
      have hterm : |(c / τ) * y i| ≤ |c * y i| := by
        have hτ_nonneg : 0 ≤ τ := le_trans zero_le_one hτ
        calc
          |c / τ * y i| = |c * y i| / τ := by
            rw [abs_mul, abs_div, abs_mul, abs_of_nonneg hτ_nonneg]
            ring
          _ ≤ |c * y i| := div_le_self (abs_nonneg (c * y i)) hτ
      calc
        |dialV p c y τ i| = |p.2 i + (c / τ) * y i| := by
          simp [dialV]
        _ ≤ |p.2 i| + |(c / τ) * y i| := abs_add_le (p.2 i) ((c / τ) * y i)
        _ ≤ |p.2 i| + |c * y i| := add_le_add (le_refl |p.2 i|) hterm)

/-- The probe path packaged by `DialPathData` is componentwise eventually bounded. -/
noncomputable def DialPathData.eventuallyBounded_probe
    {d : Nat} {A : Matrix (Fin d) (Fin d) ℝ} {b : ℝ}
    (δ : DialPathData A b) :
    EventuallyBoundedProbePair (DialPathData.probe δ) where
  fst i := by
    simpa [DialPathData.probe, dialProbe] using
      eventuallyBoundedReal_dialW_coord δ.base δ.c δ.y i
  snd i := by
    simpa [DialPathData.probe, dialProbe] using
      eventuallyBoundedReal_dialV_coord δ.base δ.c δ.y i

/-- The head gate used in the canonical alpha-branch input. -/
noncomputable def canonicalFrecHeadGateAlongSignRegion
    (r : Nat) {L d : Nat} {θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (θrun : Params (L + 1) d) :
    ProbePair d × ℝ -> ℝ -> ℝ :=
  fun x τ => canonicalFrecGateAlongSignRegion r signRegion θrun 0 x τ

/-- The canonical dial probe used as the alpha-branch path input. -/
noncomputable def canonicalDialProbeAlongSignRegion
    (r : Nat) {L d : Nat} {θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))) :
    ProbePair d × ℝ -> ℝ -> ProbePair d := by
  classical
  exact fun x τ =>
    if hx : x ∈ signRegion.U then
      let δ :=
        DialPathData.ofRegularQuadric
          (Params.headAttention θ') (Real.log (r : ℝ)) x.1 x.2
          (signRegion.point_on_quadric x hx)
          (signRegion.point_regular x hx)
          (signRegion.t_pos hx)
          (signRegion.t_lt_one hx)
      DialPathData.probe δ τ
    else
      x.1

/-- The actual alpha slope obtained from the canonical head gate and dial path. -/
noncomputable def canonicalAlphaSlopeAlongSignRegion
    (r : Nat) {L d : Nat} {θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (θrun : Params (L + 1) d) (level : Nat) (tail : Nat -> ℝ) :
    ProbePair d × ℝ -> ℝ -> ℝ :=
  fun x τ =>
    (specializedPhi θrun level
      (alphaGateAssignmentPrefix
        (canonicalFrecHeadGateAlongSignRegion r signRegion θrun x τ)
        (fun n => canonicalFrecGateAlongSignRegion r signRegion θrun n x τ)
        tail level)
      (canonicalDialProbeAlongSignRegion r signRegion x τ)).re

/-- Canonical head gates are eventually bounded on any subset of the sign region. -/
noncomputable def canonicalFrecHeadGateAlongSignRegion_eventuallyBounded
    {L d r : Nat} {θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (θrun : Params (L + 1) d)
    (Ustar : Set (ProbePair d × ℝ)) (hsubset : Ustar ⊆ signRegion.U) :
    ∀ x ∈ Ustar,
      EventuallyBoundedReal
        (fun τ => canonicalFrecHeadGateAlongSignRegion r signRegion θrun x τ) := by
  intro x hxU
  classical
  have hx : x ∈ signRegion.U := hsubset hxU
  let δ :=
    DialPathData.ofRegularQuadric
      (Params.headAttention θ') (Real.log (r : ℝ)) x.1 x.2
      (signRegion.point_on_quadric x hx)
      (signRegion.point_regular x hx)
      (signRegion.t_pos hx)
      (signRegion.t_lt_one hx)
  let f : ℝ -> ℝ :=
    fun τ =>
      τ * matrixBilin (Params.headAttention θrun)
        (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 + Real.log (r : ℝ)
  exact (EventuallyBoundedReal.sig_comp f).congr_of_forall_eq (by
    intro τ
    simp [canonicalFrecHeadGateAlongSignRegion, canonicalFrecGateAlongSignRegion,
      δ, f, hx, frecRunningGate, firstLayerGate])

/-- Canonical dial probes are eventually bounded on any subset of the sign region. -/
noncomputable def canonicalDialProbeAlongSignRegion_eventuallyBounded
    {L d r : Nat} {θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (Ustar : Set (ProbePair d × ℝ)) (hsubset : Ustar ⊆ signRegion.U) :
    ∀ x ∈ Ustar,
      EventuallyBoundedProbePair (canonicalDialProbeAlongSignRegion r signRegion x) := by
  intro x hxU
  classical
  have hx : x ∈ signRegion.U := hsubset hxU
  let δ :=
    DialPathData.ofRegularQuadric
      (Params.headAttention θ') (Real.log (r : ℝ)) x.1 x.2
      (signRegion.point_on_quadric x hx)
      (signRegion.point_regular x hx)
      (signRegion.t_pos hx)
      (signRegion.t_lt_one hx)
  refine
    { fst := ?_
      snd := ?_ }
  · intro i
    exact ((DialPathData.eventuallyBounded_probe δ).fst i).congr_of_forall_eq (by
      intro τ
      simp [canonicalDialProbeAlongSignRegion, δ, hx])
  · intro i
    exact ((DialPathData.eventuallyBounded_probe δ).snd i).congr_of_forall_eq (by
      intro τ
      simp [canonicalDialProbeAlongSignRegion, δ, hx])

/-- The canonical actual gate has the exact sigmoid form with the canonical alpha slope. -/
theorem canonicalFrecGateAlongSignRegion_eq_sig_alphaSlope
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    {level : Nat} (hlevel_pos : 1 ≤ level) (hlevel_lt : level < L + 1)
    (tail : Nat -> ℝ) :
    ∀ x ∈ signRegion.U, ∀ τ : ℝ,
      canonicalFrecGateAlongSignRegion r signRegion θ level x τ =
        sig (τ * canonicalAlphaSlopeAlongSignRegion r signRegion θ level tail x τ
          + Real.log (r : ℝ)) := by
  intro x hx τ
  classical
  let δ :=
    DialPathData.ofRegularQuadric
      (Params.headAttention θ') (Real.log (r : ℝ)) x.1 x.2
      (signRegion.point_on_quadric x hx)
      (signRegion.point_regular x hx)
      (signRegion.t_pos hx)
      (signRegion.t_lt_one hx)
  have hgate :=
    frecRunningGate_eq_sig_specializedPhi_alphaGateAssignmentPrefix
      (L := L + 1) (d := d) r θ (DialPathData.probe δ)
      hlevel_pos hlevel_lt tail τ
  simpa [canonicalFrecGateAlongSignRegion, canonicalFrecHeadGateAlongSignRegion,
    canonicalDialProbeAlongSignRegion, canonicalAlphaSlopeAlongSignRegion, δ, hx]
    using hgate

/-- Canonical alpha-branch inputs satisfy the reusable alpha-error package. -/
noncomputable def canonicalFrecGateAlongSignRegion_alphaSlopeErrorBound
    {L d r : Nat} {θ θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (Ustar : Set (ProbePair d × ℝ)) (hsubset : Ustar ⊆ signRegion.U)
    (level : Nat) (tail : Nat -> ℝ) :
    CascadeAlphaSlopeErrorBound θ A level tail Ustar
      (canonicalFrecGateAlongSignRegion r signRegion θ)
      (canonicalFrecHeadGateAlongSignRegion r signRegion θ)
      (canonicalDialProbeAlongSignRegion r signRegion)
      (canonicalAlphaSlopeAlongSignRegion r signRegion θ level tail) :=
  cascadeAlphaSlopeErrorBound_of_specializedPhi_prefix θ A level tail Ustar
    (canonicalFrecGateAlongSignRegion r signRegion θ)
    (canonicalFrecHeadGateAlongSignRegion r signRegion θ)
    (canonicalDialProbeAlongSignRegion r signRegion)
    (canonicalAlphaSlopeAlongSignRegion r signRegion θ level tail)
    (canonicalFrecHeadGateAlongSignRegion_eventuallyBounded signRegion θ Ustar hsubset)
    (canonicalDialProbeAlongSignRegion_eventuallyBounded signRegion Ustar hsubset)
    (by
      intro x hx τ
      rfl)

@[simp] theorem canonicalFrecGateAlongSignRegion_apply_product
    {L d r : Nat}
    {θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (θrun : Params (L + 1) d)
    (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J)
    (n : Nat) (τ : ℝ) :
    canonicalFrecGateAlongSignRegion r signRegion θrun n (p, t) τ =
      frecRunningGate r θrun
        (DialPathData.probe
          (texMatchingRegularQuadricDialPathData
            (L := L) (d := d) (r := r) signRegion T N p hp t ht))
        n τ := by
  let hx := texMatching_product_mem_signRegion signRegion T N hp ht
  simp [canonicalFrecGateAlongSignRegion, texMatchingRegularQuadricDialPathData, hx]

/-- If the primed formal slopes are positive at every deeper level of a dial, then the
actual primed running gates at those deeper levels are exponentially close to `1`. -/
noncomputable def frecRunningGate_primed_saturates_one_of_positivity
    {L d r : Nat}
    {θ' : Params (L + 1) d}
    (δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ)))
    (hpos :
      ∀ n : Nat, 1 ≤ n → n < L + 1 →
        0 < (specializedPhi θ' n (gateAssignmentOneTail δ.t) δ.base).re) :
    ∀ n : Nat, 1 ≤ n → n < L + 1 →
      EventuallyExpClose
        (fun τ : ℝ => frecRunningGate r θ' (DialPathData.probe δ) n τ) 1 := by
  intro n
  refine Nat.strongRecOn (motive := fun n =>
    1 ≤ n → n < L + 1 →
      EventuallyExpClose
        (fun τ : ℝ => frecRunningGate r θ' (DialPathData.probe δ) n τ) 1) n ?_
  intro n ih hn_pos hn_lt
  have hP0 : Tendsto (DialPathData.probe δ) atTop (𝓝 δ.base) :=
    tendsto_dialPathData_probe δ
  have hgate0 :
      Tendsto
        (fun τ : ℝ =>
          firstLayerGate r (Params.headAttention θ') (δ.probe τ).1 (δ.probe τ).2 τ)
        atTop (𝓝 δ.t) :=
    tendsto_firstLayerGate_dialPathData δ
  have hP :
      Tendsto
        (fun τ : ℝ => frecRunningPath r θ' (DialPathData.probe δ) n τ)
        atTop
        (𝓝 (peelPoint (paramStream θ') (realGateOfTail δ.t (fun _ => 1)) n
          δ.base)) := by
    refine
      tendsto_frecRunningPath_of_prior_frecRunningGate r θ' (DialPathData.probe δ)
        (realGateOfTail δ.t (fun _ => 1)) δ.base n hP0 (Nat.le_of_lt hn_lt) ?_
    intro k hk
    cases k with
    | zero =>
        simpa [frecRunningGate, realGateOfTail] using hgate0
    | succ k =>
        have hk_pos : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
        have hk_lt : k + 1 < L + 1 := lt_trans hk hn_lt
        have hsat := ih (k + 1) hk hk_pos hk_lt
        simpa [realGateOfTail] using hsat.tendsto
  have hΛ :
      0 < matrixBilin (paramStream θ' n).2
        (peelPoint (paramStream θ') (realGateOfTail δ.t (fun _ => 1)) n δ.base).1
        (peelPoint (paramStream θ') (realGateOfTail δ.t (fun _ => 1)) n δ.base).2 := by
    have hbridge :=
      re_specializedPhi_eq_matrixBilin_peelPoint θ' n δ.t (fun _ => 1) δ.base
    rw [← hbridge]
    have h := hpos n hn_pos hn_lt
    simpa only [gateAssignmentOneTail] using h
  have hfirst :
      EventuallyExpClose
        (fun τ : ℝ =>
          firstLayerGate r (paramStream θ' n).2
            (frecRunningPath r θ' (DialPathData.probe δ) n τ).1
            (frecRunningPath r θ' (DialPathData.probe δ) n τ).2 τ)
        1 :=
    eventuallyExpClose_firstLayerGate_of_tendsto_pos r (paramStream θ' n).2
      (fun τ : ℝ => frecRunningPath r θ' (DialPathData.probe δ) n τ)
      (peelPoint (paramStream θ') (realGateOfTail δ.t (fun _ => 1)) n δ.base)
      hP hΛ
  refine hfirst.congr_of_forall_eq ?_ rfl
  intro τ
  exact (frecRunningGate_eq_firstLayerGate_frecRunningPath r θ'
    (DialPathData.probe δ) hn_lt τ).symm

/-- Canonical primed actual gates over a sign region saturate exponentially to `1` at every
deeper layer. -/
noncomputable def canonicalFrecGateAlongSignRegion_primed_saturates_one
    {L d r : Nat}
    {θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))) :
    ∀ x ∈ signRegion.U, ∀ n : Nat, 1 ≤ n → n < L + 1 →
      EventuallyExpClose
        (fun τ : ℝ => canonicalFrecGateAlongSignRegion r signRegion θ' n x τ) 1 := by
  intro x hx n hn_pos hn_lt
  let δ :=
    DialPathData.ofRegularQuadric
      (Params.headAttention θ') (Real.log (r : ℝ)) x.1 x.2
      (signRegion.point_on_quadric x hx)
      (signRegion.point_regular x hx)
      (signRegion.t_pos hx)
      (signRegion.t_lt_one hx)
  have hsat :
      EventuallyExpClose
        (fun τ : ℝ => frecRunningGate r θ' (DialPathData.probe δ) n τ) 1 :=
    frecRunningGate_primed_saturates_one_of_positivity
      (L := L) (d := d) (r := r) (θ' := θ') δ ?_ n hn_pos hn_lt
  · refine hsat.congr_of_forall_eq ?_ rfl
    intro τ
    symm
    simp [canonicalFrecGateAlongSignRegion, δ, hx]
  · intro k hk_pos hk_lt
    simpa [δ, DialPathData.ofRegularQuadric] using
      signRegion.primed_positive x hx k hk_pos hk_lt

/-- Canonical unprimed actual gate saturation at one level of a sign region.

Assuming prior canonical unprimed gates are exponentially close to the supplied tail
constants, a nonzero specialised formal slope at `level` forces the actual canonical
gate at that level to saturate exponentially to its sign. -/
noncomputable def canonicalFrecGateAlongSignRegion_unprimed_saturates_of_nonzero
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (level : Nat) (tail : Nat → ℝ)
    (hlevel_pos : 1 ≤ level) (hlevel_lt : level < L + 1)
    (hprior :
      ∀ x ∈ signRegion.U, ∀ n : Nat, 1 ≤ n → n < level →
        EventuallyExpClose
          (fun τ : ℝ => canonicalFrecGateAlongSignRegion r signRegion θ n x τ)
          (tail (n - 1))) :
    ∀ x ∈ signRegion.U,
      specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1 ≠ 0 →
        EventuallyExpClose
          (fun τ : ℝ => canonicalFrecGateAlongSignRegion r signRegion θ level x τ)
          (if 0 < (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re
            then 1 else 0) := by
  intro x hx hne
  have _hlevel_ne : level ≠ 0 := Nat.ne_of_gt hlevel_pos
  let δ :=
    DialPathData.ofRegularQuadric
      (Params.headAttention θ') (Real.log (r : ℝ)) x.1 x.2
      (signRegion.point_on_quadric x hx)
      (signRegion.point_regular x hx)
      (signRegion.t_pos hx)
      (signRegion.t_lt_one hx)
  have hP0 : Tendsto (DialPathData.probe δ) atTop (𝓝 x.1) := by
    have hPδ : Tendsto (DialPathData.probe δ) atTop (𝓝 δ.base) :=
      tendsto_dialPathData_probe δ
    simpa [δ, DialPathData.ofRegularQuadric] using hPδ
  have hgate0 :
      Tendsto
        (fun τ : ℝ =>
          firstLayerGate r (Params.headAttention θ) (δ.probe τ).1 (δ.probe τ).2 τ)
        atTop (𝓝 (realGateOfTail x.2 tail 0)) := by
    have h := tendsto_firstLayerGate_dialPathData δ
    rw [hAA]
    simpa [δ, DialPathData.ofRegularQuadric, realGateOfTail] using h
  have hPath :
      Tendsto
        (fun τ : ℝ => frecRunningPath r θ (DialPathData.probe δ) level τ)
        atTop
        (𝓝 (peelPoint (paramStream θ) (realGateOfTail x.2 tail) level x.1)) := by
    refine
      tendsto_frecRunningPath_of_prior_frecRunningGate r θ (DialPathData.probe δ)
        (realGateOfTail x.2 tail) x.1 level hP0 (Nat.le_of_lt hlevel_lt) ?_
    intro k hk
    cases k with
    | zero =>
        simpa [frecRunningGate] using hgate0
    | succ k =>
        have hk_pos : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
        have hclose := hprior x hx (k + 1) hk_pos hk
        have htend :
            Tendsto
              (fun τ : ℝ => frecRunningGate r θ (DialPathData.probe δ) (k + 1) τ)
              atTop (𝓝 (tail k)) := by
          refine hclose.tendsto.congr' ?_
          filter_upwards with τ
          symm
          simp [canonicalFrecGateAlongSignRegion, δ, hx]
        simpa [realGateOfTail] using htend
  have hReNe :
      (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re ≠ 0 :=
    specializedPhi_gateAssignmentOfTail_re_ne_zero_of_ne θ level x.2 tail x.1 hne
  have hbridge :=
    re_specializedPhi_eq_matrixBilin_peelPoint θ level x.2 tail x.1
  by_cases hpos :
      0 < (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re
  · have hΛ :
        0 < matrixBilin (paramStream θ level).2
          (peelPoint (paramStream θ) (realGateOfTail x.2 tail) level x.1).1
          (peelPoint (paramStream θ) (realGateOfTail x.2 tail) level x.1).2 := by
      simpa [hbridge] using hpos
    have hfirst :
        EventuallyExpClose
          (fun τ : ℝ =>
            firstLayerGate r (paramStream θ level).2
              (frecRunningPath r θ (DialPathData.probe δ) level τ).1
              (frecRunningPath r θ (DialPathData.probe δ) level τ).2 τ)
          1 :=
      eventuallyExpClose_firstLayerGate_of_tendsto_pos r (paramStream θ level).2
        (fun τ : ℝ => frecRunningPath r θ (DialPathData.probe δ) level τ)
        (peelPoint (paramStream θ) (realGateOfTail x.2 tail) level x.1)
        hPath hΛ
    rw [if_pos hpos]
    refine hfirst.congr_of_forall_eq ?_ rfl
    intro τ
    rw [← frecRunningGate_eq_firstLayerGate_frecRunningPath r θ
      (DialPathData.probe δ) hlevel_lt τ]
    simp [canonicalFrecGateAlongSignRegion, δ, hx]
  · have hneg :
        (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re < 0 := by
      exact lt_of_le_of_ne (le_of_not_gt hpos) hReNe
    have hΛ :
        matrixBilin (paramStream θ level).2
          (peelPoint (paramStream θ) (realGateOfTail x.2 tail) level x.1).1
          (peelPoint (paramStream θ) (realGateOfTail x.2 tail) level x.1).2 < 0 := by
      simpa [hbridge] using hneg
    have hfirst :
        EventuallyExpClose
          (fun τ : ℝ =>
            firstLayerGate r (paramStream θ level).2
              (frecRunningPath r θ (DialPathData.probe δ) level τ).1
              (frecRunningPath r θ (DialPathData.probe δ) level τ).2 τ)
          0 :=
      eventuallyExpClose_firstLayerGate_of_tendsto_neg r (paramStream θ level).2
        (fun τ : ℝ => frecRunningPath r θ (DialPathData.probe δ) level τ)
        (peelPoint (paramStream θ) (realGateOfTail x.2 tail) level x.1)
        hPath hΛ
    rw [if_neg hpos]
    refine hfirst.congr_of_forall_eq ?_ rfl
    intro τ
    rw [← frecRunningGate_eq_firstLayerGate_frecRunningPath r θ
      (DialPathData.probe δ) hlevel_lt τ]
    simp [canonicalFrecGateAlongSignRegion, δ, hx]

/-- The all-dial actual gate package restricts to the canonical regular-quadric
matching dials. -/
theorem texTrichotomyMatchingCanonicalActualGateData_of_actualGateData
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (actual : TexTrichotomyMatchingActualGateData (θ := θ) (θ' := θ') T) :
    TexTrichotomyMatchingCanonicalActualGateData (θ := θ) (θ' := θ') signRegion T N := by
  rcases actual with ⟨hUnprimed, hPrimed⟩
  refine ⟨?_, ?_⟩
  · intro p hp t ht
    change ∀ n : Nat, 1 ≤ n → n < L + 1 →
      (fun τ : ℝ =>
        frecRunningGate r θ
          (DialPathData.probe
            (texMatchingRegularQuadricDialPathData
              (L := L) (d := d) (r := r) signRegion T N p hp t ht))
          n τ)
          =ᶠ[atTop]
        (fun τ : ℝ => T.unprimed n (p, t) τ)
    intro n hn_pos hn_lt
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    have hδ : (δ.base, δ.t) ∈ T.Ustar := by
      simpa [δ] using
        texMatchingRegularQuadricDialPathData_mem_Ustar
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
    have hactual := hUnprimed δ hδ n hn_pos hn_lt
    simpa [δ] using hactual
  · intro p hp t ht
    change ∀ n : Nat, 1 ≤ n → n < L + 1 →
      (fun τ : ℝ =>
        frecRunningGate r θ'
          (DialPathData.probe
            (texMatchingRegularQuadricDialPathData
              (L := L) (d := d) (r := r) signRegion T N p hp t ht))
          n τ)
          =ᶠ[atTop]
        (fun τ : ℝ => T.primed n (p, t) τ)
    intro n hn_pos hn_lt
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    have hδ : (δ.base, δ.t) ∈ T.Ustar := by
      simpa [δ] using
        texMatchingRegularQuadricDialPathData_mem_Ustar
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
    have hactual := hPrimed δ hδ n hn_pos hn_lt
    simpa [δ] using hactual

/-- If the trichotomy construction uses the canonical Frec gates on the sign region,
then the canonical actual-gate package is discharged by unfolding. -/
theorem texTrichotomyMatchingCanonicalActualGateData_of_canonicalFrecGates
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (hunprimed : T.unprimed = canonicalFrecGateAlongSignRegion r signRegion θ)
    (hprimed : T.primed = canonicalFrecGateAlongSignRegion r signRegion θ') :
    TexTrichotomyMatchingCanonicalActualGateData (θ := θ) (θ' := θ') signRegion T N := by
  refine ⟨?_, ?_⟩
  · intro p hp t ht
    change ∀ n : Nat, 1 ≤ n → n < L + 1 →
      (fun τ : ℝ =>
        frecRunningGate r θ
          (DialPathData.probe
            (texMatchingRegularQuadricDialPathData
              (L := L) (d := d) (r := r) signRegion T N p hp t ht))
          n τ)
          =ᶠ[atTop]
        (fun τ : ℝ => T.unprimed n (p, t) τ)
    intro n _hn_pos _hn_lt
    apply Filter.EventuallyEq.of_eq
    funext τ
    rw [hunprimed]
    exact
      (canonicalFrecGateAlongSignRegion_apply_product
        (L := L) (d := d) (r := r) signRegion T N θ p hp t ht n τ).symm
  · intro p hp t ht
    change ∀ n : Nat, 1 ≤ n → n < L + 1 →
      (fun τ : ℝ =>
        frecRunningGate r θ'
          (DialPathData.probe
            (texMatchingRegularQuadricDialPathData
              (L := L) (d := d) (r := r) signRegion T N p hp t ht))
          n τ)
          =ᶠ[atTop]
        (fun τ : ℝ => T.primed n (p, t) τ)
    intro n _hn_pos _hn_lt
    apply Filter.EventuallyEq.of_eq
    funext τ
    rw [hprimed]
    exact
      (canonicalFrecGateAlongSignRegion_apply_product
        (L := L) (d := d) (r := r) signRegion T N θ' p hp t ht n τ).symm

/-- Unprimed saturated `Frec` limit along one canonical regular-quadric product-patch
dial, from canonical actual trichotomy gate agreement. -/
theorem texMatchingUnprimedSaturatedRegularQuadricFrecTendsto_of_canonicalActualTrichotomyGates
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (S : TexMatchingSaturatedContributionData θ T.trichotomy.varsigma)
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (actual :
      TexTrichotomyMatchingCanonicalActualGateData
        (θ := θ) (θ' := θ') signRegion T N)
    (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J) :
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    Filter.Tendsto
      (fun τ : ℝ =>
        Frec r θ (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ)
      Filter.atTop
      (nhds (texMatchingUnprimedSaturatedLimitVector θ S.D t p)) := by
  let δ :=
    texMatchingRegularQuadricDialPathData
      (L := L) (d := d) (r := r) signRegion T N p hp t ht
  let ς := trichotomyDialGateConstants T t
  have hmem : (p, t) ∈ T.Ustar := by
    simpa [δ] using
      texMatchingRegularQuadricDialPathData_mem_Ustar
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
  have hP : Tendsto (DialPathData.probe δ) atTop (𝓝 δ.base) :=
    tendsto_dialPathData_probe δ
  have hgate0 :
      Tendsto
        (fun τ : ℝ =>
          firstLayerGate r (Params.headAttention θ) (DialPathData.probe δ τ).1
            (DialPathData.probe δ τ).2 τ)
        atTop (𝓝 (ς 0)) := by
    have h := tendsto_firstLayerGate_dialPathData δ
    rw [hAA]
    simpa [ς, δ] using h
  have hgates :
      ∀ n : Nat, n < L + 1 →
        Tendsto
          (fun τ : ℝ => frecRunningGate r θ (DialPathData.probe δ) n τ)
          atTop (𝓝 (ς n)) := by
    intro n hn
    cases n with
    | zero =>
        simpa [frecRunningGate, ς] using hgate0
    | succ k =>
        have hn_pos : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
        have hsat :=
          T.trichotomy.unprimed_saturates (p, t) hmem (k + 1) hn_pos hn
        have hactual :=
          actual.unprimed_gate_eventuallyEq p hp t ht (k + 1) hn_pos hn
        have htend :
            Tendsto
              (fun τ : ℝ => frecRunningGate r θ (DialPathData.probe δ) (k + 1) τ)
              atTop (𝓝 (T.trichotomy.varsigma (k + 1))) :=
          hsat.tendsto.congr' hactual.symm
        simpa [ς] using htend
  have hGL : GateLimits r θ (DialPathData.probe δ) ς δ.base :=
    gateLimits_of_frecRunningGate_tendsto r θ (DialPathData.probe δ) ς δ.base hP hgates
  have hfrec :=
    frec_tendsto_of_gateLimits r θ (DialPathData.probe δ) ς δ.base hP hGL
  have hlimit :
      frecLimit r θ ς δ.base =
        texMatchingUnprimedSaturatedLimitVector θ S.D t p := by
    rw [frecLimit_eq_texMatchingUnprimedSaturatedLimitVector r θ ς δ.base]
    have hmatrix :
        texMatchingSaturatedContributionMatrix θ ς = S.D := by
      rw [texMatchingSaturatedContributionMatrix_trichotomyDialGateConstants θ T t,
        ← S.D_eq]
    simp [ς, δ, hmatrix]
  simpa [hlimit] using hfrec

/-- Primed telescoped `Frec` limit along one canonical regular-quadric product-patch
dial, from canonical actual trichotomy gate agreement. -/
theorem texMatchingPrimedTelescopedRegularQuadricFrecTendsto_of_canonicalActualTrichotomyGates
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (actual :
      TexTrichotomyMatchingCanonicalActualGateData
        (θ := θ) (θ' := θ') signRegion T N)
    (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J) :
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    Filter.Tendsto
      (fun τ : ℝ =>
        Frec r θ' (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ)
      Filter.atTop
      (nhds (texMatchingPrimedTelescopedLimitVector θ' t p)) := by
  let δ :=
    texMatchingRegularQuadricDialPathData
      (L := L) (d := d) (r := r) signRegion T N p hp t ht
  let ς := realGateOfTail t (fun _ => (1 : ℝ))
  have hmem : (p, t) ∈ T.Ustar := by
    simpa [δ] using
      texMatchingRegularQuadricDialPathData_mem_Ustar
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
  have hP : Tendsto (DialPathData.probe δ) atTop (𝓝 δ.base) :=
    tendsto_dialPathData_probe δ
  have hgate0 :
      Tendsto
        (fun τ : ℝ =>
          firstLayerGate r (Params.headAttention θ') (DialPathData.probe δ τ).1
            (DialPathData.probe δ τ).2 τ)
        atTop (𝓝 (ς 0)) := by
    simpa [ς, δ] using tendsto_firstLayerGate_dialPathData δ
  have hgates :
      ∀ n : Nat, n < L + 1 →
        Tendsto
          (fun τ : ℝ => frecRunningGate r θ' (DialPathData.probe δ) n τ)
          atTop (𝓝 (ς n)) := by
    intro n hn
    cases n with
    | zero =>
        simpa [frecRunningGate, ς] using hgate0
    | succ k =>
        have hn_pos : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
        have hsat :=
          T.trichotomy.primed_saturates_one (p, t) hmem (k + 1) hn_pos hn
        have hactual :=
          actual.primed_gate_eventuallyEq p hp t ht (k + 1) hn_pos hn
        have htend :
            Tendsto
              (fun τ : ℝ => frecRunningGate r θ' (DialPathData.probe δ) (k + 1) τ)
              atTop (𝓝 (1 : ℝ)) :=
          hsat.tendsto.congr' hactual.symm
        simpa [ς, realGateOfTail] using htend
  have hGL : GateLimits r θ' (DialPathData.probe δ) ς δ.base :=
    gateLimits_of_frecRunningGate_tendsto r θ' (DialPathData.probe δ) ς δ.base hP hgates
  have hfrec :=
    frec_tendsto_of_gateLimits r θ' (DialPathData.probe δ) ς δ.base hP hGL
  have hlimit :
      frecLimit r θ' ς δ.base =
        texMatchingPrimedTelescopedLimitVector θ' t p := by
    have htail : ∀ k : Nat, ς (k + 1) = 1 := by
      intro k
      rfl
    rw [frecLimit_eq_texMatchingPrimedTelescopedLimitVector r θ' ς htail δ.base]
    simp [ς, realGateOfTail, δ]
  simpa [hlimit] using hfrec

/-- R4 package: canonical actual trichotomy gate saturation discharges the
regular-quadric closed-recursion Frec obligations consumed by matching. -/
theorem texMatchingRegularQuadricClosedRecursionLimitObligation_of_canonicalActualTrichotomyGates
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (S : TexMatchingSaturatedContributionData θ T.trichotomy.varsigma)
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (actual :
      TexTrichotomyMatchingCanonicalActualGateData
        (θ := θ) (θ' := θ') signRegion T N) :
    TexMatchingRegularQuadricClosedRecursionLimitObligation signRegion T N S := by
  refine ⟨?_, ?_⟩
  · intro p hp t ht
    exact
      texMatchingUnprimedSaturatedRegularQuadricFrecTendsto_of_canonicalActualTrichotomyGates
        signRegion T N S hAA actual p hp t ht
  · intro p hp t ht
    exact
      texMatchingPrimedTelescopedRegularQuadricFrecTendsto_of_canonicalActualTrichotomyGates
        signRegion T N actual p hp t ht

end TransformerIdentifiability.NLayer
