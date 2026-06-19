import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeUnprimedMatching
import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeAlphaError

set_option autoImplicit false

open Filter Topology Matrix

namespace TransformerIdentifiability.NLayer

/-!
# R4: matching `Frec` asymptotics from genuine trichotomy gates

`TrichotomyData` records saturation for constructor-supplied `GateAlongBase` functions.
This file adds the downstream bridge used by matching once those gate functions have
been identified with the actual recursive gates along the Frec dial paths.

The fake constant-gate trichotomy remains untouched: callers must provide
`TexTrichotomyMatchingActualGateData`, which is exactly the missing equality between the
trichotomy gate package and the running gates consumed by `GateLimits`.
-/

/-- The actual level-`n` gate seen by `Frec` along a running probe path. -/
noncomputable def frecRunningGate {d : Nat} (r : Nat) :
    {m : Nat} → Params m d → (ℝ → ProbePoint d) → Nat → ℝ → ℝ
  | 0, _θ, _P, _n, _τ => 0
  | _m + 1, θ, P, 0, τ =>
      firstLayerGate r (Params.headAttention θ) (P τ).1 (P τ).2 τ
  | _m + 1, θ, P, n + 1, τ =>
      frecRunningGate r (Params.tail θ) (effectivePath r θ P) n τ

/-- The probe point seen by the first gate at a running level of the `Frec` recursion. -/
noncomputable def frecRunningPath {d : Nat} (r : Nat) :
    {m : Nat} → Params m d → (ℝ → ProbePoint d) → Nat → ℝ → ProbePoint d
  | 0, _θ, P, _n, τ => P τ
  | _m + 1, _θ, P, 0, τ => P τ
  | _m + 1, θ, P, n + 1, τ =>
      frecRunningPath r (Params.tail θ) (effectivePath r θ P) n τ

@[simp]
theorem frecRunningPath_zero_depth {d : Nat} (r : Nat) (θ : Params 0 d)
    (P : ℝ → ProbePoint d) (level : Nat) (τ : ℝ) :
    frecRunningPath r θ P level τ = P τ :=
  rfl

@[simp]
theorem frecRunningPath_zero_level {m d : Nat} (r : Nat) (θ : Params (m + 1) d)
    (P : ℝ → ProbePoint d) (τ : ℝ) :
    frecRunningPath r θ P 0 τ = P τ :=
  rfl

@[simp]
theorem frecRunningPath_succ_level {m d : Nat} (r : Nat) (θ : Params (m + 1) d)
    (P : ℝ → ProbePoint d) (level : Nat) (τ : ℝ) :
    frecRunningPath r θ P (level + 1) τ =
      frecRunningPath r (Params.tail θ) (effectivePath r θ P) level τ :=
  rfl

/-- `peelPoint` only reads gate coordinates below the number of peels. -/
theorem peelPoint_congr_of_eqOn_lt {d : Nat} (η : LayerStream d)
    {ς ς' : Nat → ℝ} (level : Nat) (pt : ProbePoint d)
    (hς : ∀ k : Nat, k < level → ς k = ς' k) :
    peelPoint η ς level pt = peelPoint η ς' level pt := by
  revert η ς ς' pt
  induction level with
  | zero =>
      intro η ς ς' pt hς
      rfl
  | succ level ih =>
      intro η ς ς' pt hς
      have h0 : ς 0 = ς' 0 := hς 0 (Nat.succ_pos level)
      have htail : ∀ k : Nat, k < level → ς (k + 1) = ς' (k + 1) := by
        intro k hk
        exact hς (k + 1) (Nat.succ_lt_succ hk)
      rw [peelPoint_succ, peelPoint_succ, h0]
      exact ih (fun k => η (k + 1)) (ς := fun k => ς (k + 1))
        (ς' := fun k => ς' (k + 1)) (pt := effLimitPoint (η 0).1 (ς' 0) pt)
        htail

/-- Shifting an alpha-prefix assignment drops the live head gate and exposes the tail
running-gate assignment on all coordinates read by an `level`-fold peel. -/
theorem alphaGateAssignmentPrefixReal_tail_eq_shift_eqOn_lt
    (head : ℝ) (live tail : Nat → ℝ) {level : Nat} :
    ∀ k : Nat, k < level →
      alphaGateAssignmentPrefixReal (live 1) (fun n => live (n + 1))
          (fun n => tail (n + 1)) level k =
        alphaGateAssignmentPrefixReal head live tail (level + 1) (k + 1) := by
  intro k hk
  cases k with
  | zero =>
      have hsucc : 1 < level + 1 := by omega
      simp [alphaGateAssignmentPrefixReal, hsucc]
  | succ k =>
      have hksucc : k + 1 < level := hk
      have hshift : k + 1 + 1 < level + 1 := by omega
      simp [alphaGateAssignmentPrefixReal, hksucc, hshift]

/-- The actual running point after finitely many `Frec` peels is the closed `peelPoint`
for the alpha-prefix assignment formed from the live running gates. -/
theorem frecRunningPath_eq_peelPoint_alphaGateAssignmentPrefixReal
    {d m : Nat} (r : Nat) (θ : Params m d) (P : ℝ → ProbePoint d)
    {level : Nat} (hlevel : level ≤ m) (tail : Nat → ℝ) (τ : ℝ) :
    frecRunningPath r θ P level τ =
      peelPoint (paramStream θ)
        (alphaGateAssignmentPrefixReal
          (frecRunningGate r θ P 0 τ)
          (fun n => frecRunningGate r θ P n τ)
          tail level)
        level (P τ) := by
  revert θ P level tail τ
  induction m with
  | zero =>
      intro θ P level hlevel tail τ
      have hlevel_zero : level = 0 := by omega
      subst level
      simp
  | succ m ih =>
      intro θ P level hlevel tail τ
      cases level with
      | zero =>
          simp
      | succ level =>
          have htail_level : level ≤ m := by omega
          have hrec :=
            ih (Params.tail θ) (effectivePath r θ P) (level := level) htail_level
              (fun n => tail (n + 1)) τ
          let ς : Nat → ℝ :=
            alphaGateAssignmentPrefixReal
              (frecRunningGate r θ P 0 τ)
              (fun n => frecRunningGate r θ P n τ)
              tail (level + 1)
          have hpoint :
              effectivePath r θ P τ =
                effLimitPoint (Params.headValue θ) (ς 0) (P τ) := by
            simp [ς, effectivePath, paramsFirstLayerEffectivePoint,
              firstLayerEffectivePoint, effLimitPoint, frecRunningGate,
              alphaGateAssignmentPrefixReal]
          have hprefix :
              ∀ k : Nat, k < level →
                alphaGateAssignmentPrefixReal
                    (frecRunningGate r (Params.tail θ) (effectivePath r θ P) 0 τ)
                    (fun n => frecRunningGate r (Params.tail θ) (effectivePath r θ P) n τ)
                    (fun n => tail (n + 1)) level k =
                  (fun k => ς (k + 1)) k := by
            intro k hk
            simpa [ς, frecRunningGate] using
              alphaGateAssignmentPrefixReal_tail_eq_shift_eqOn_lt
                (frecRunningGate r θ P 0 τ)
                (fun n => frecRunningGate r θ P n τ) tail k hk
          rw [frecRunningPath_succ_level, hrec]
          rw [peelPoint_paramStream_succ θ ς level (P τ)]
          rw [hpoint]
          exact peelPoint_congr_of_eqOn_lt (paramStream (Params.tail θ)) level
            (effLimitPoint (Params.headValue θ) (ς 0) (P τ)) hprefix

/-- A running recursive gate is the first-layer gate of the corresponding running path. -/
theorem frecRunningGate_eq_firstLayerGate_frecRunningPath
    {d m : Nat} (r : Nat) (θ : Params m d) (P : ℝ → ProbePoint d)
    {level : Nat} (hlevel : level < m) (τ : ℝ) :
    frecRunningGate r θ P level τ =
      firstLayerGate r (paramStream θ level).2 (frecRunningPath r θ P level τ).1
        (frecRunningPath r θ P level τ).2 τ := by
  revert θ P level
  induction m with
  | zero =>
      intro θ P level hlevel
      omega
  | succ m ih =>
      intro θ P level hlevel
      cases level with
      | zero =>
          simp [frecRunningGate, paramStream, Params.headAttention, Params.headLayer]
      | succ level =>
      have htail : level < m := Nat.lt_of_succ_lt_succ hlevel
      simpa [frecRunningGate, paramStream_tail_apply θ htail] using
        ih (Params.tail θ) (effectivePath r θ P) (level := level) htail

/-- Pointwise bridge from the actual running gate to the alpha-prefix formal slope. -/
theorem frecRunningGate_eq_sig_specializedPhi_alphaGateAssignmentPrefix
    {L d : Nat} (r : Nat) (θ : Params L d) (P : ℝ → ProbePoint d)
    {level : Nat} (hlevel_pos : 1 ≤ level) (hlevel_lt : level < L)
    (tail : Nat → ℝ) (τ : ℝ) :
    frecRunningGate r θ P level τ =
      sig (τ *
        (specializedPhi θ level
          (alphaGateAssignmentPrefix
            (frecRunningGate r θ P 0 τ)
            (fun n => frecRunningGate r θ P n τ)
            tail level)
          (P τ)).re + Real.log (r : ℝ)) := by
  have _ : level ≠ 0 := by omega
  rw [frecRunningGate_eq_firstLayerGate_frecRunningPath r θ P hlevel_lt τ, firstLayerGate]
  rw [re_specializedPhi_alphaGateAssignmentPrefix_eq_matrixBilin_peelPoint]
  rw [← frecRunningPath_eq_peelPoint_alphaGateAssignmentPrefixReal r θ P
    (Nat.le_of_lt hlevel_lt) tail τ]

/-- The running path at any finite level converges to the corresponding recursively peeled
point, assuming all prior running gates converge to their peel constants. -/
theorem tendsto_frecRunningPath_of_prior_frecRunningGate
    {d : Nat} (r : Nat) :
    ∀ {m : Nat} (θ : Params m d) (P : ℝ → ProbePoint d)
      (ς : Nat → ℝ) (pt : ProbePoint d) (level : Nat),
      Tendsto P atTop (𝓝 pt) →
      level ≤ m →
      (∀ k : Nat, k < level →
        Tendsto (fun τ : ℝ => frecRunningGate r θ P k τ) atTop (𝓝 (ς k))) →
      Tendsto (fun τ : ℝ => frecRunningPath r θ P level τ) atTop
        (𝓝 (peelPoint (paramStream θ) ς level pt)) := by
  intro m
  induction m with
  | zero =>
      intro θ P ς pt level hP hlevel _hgates
      have hlevel_zero : level = 0 := by omega
      subst level
      simpa using hP
  | succ m ih =>
      intro θ P ς pt level hP hlevel hgates
      cases level with
      | zero =>
          simpa using hP
      | succ level =>
          have htail_level : level ≤ m := by omega
          have hgate0 :
              Tendsto
                (fun τ : ℝ =>
                  firstLayerGate r (Params.headAttention θ) (P τ).1 (P τ).2 τ)
                atTop (𝓝 (ς 0)) := by
            simpa [frecRunningGate] using hgates 0 (Nat.succ_pos level)
          have heff :
              Tendsto (effectivePath r θ P) atTop
                (𝓝 (effLimitPoint (Params.headValue θ) (ς 0) pt)) :=
            tendsto_effectivePath r θ P (ς 0) pt hP hgate0
          have htail :
              Tendsto
                (fun τ : ℝ =>
                  frecRunningPath r (Params.tail θ) (effectivePath r θ P) level τ)
                atTop
                (𝓝
                  (peelPoint (paramStream (Params.tail θ)) (fun n => ς (n + 1)) level
                    (effLimitPoint (Params.headValue θ) (ς 0) pt))) := by
            refine ih (Params.tail θ) (effectivePath r θ P) (fun n => ς (n + 1))
              (effLimitPoint (Params.headValue θ) (ς 0) pt) level heff htail_level ?_
            intro k hk
            simpa [frecRunningGate] using hgates (k + 1) (Nat.succ_lt_succ hk)
          simpa [peelPoint_paramStream_succ θ ς level pt] using htail

/-- Topological gate convergence of the actual running gates compiles to `GateLimits`. -/
theorem gateLimits_of_frecRunningGate_tendsto {d : Nat} (r : Nat) :
    ∀ {m : Nat} (θ : Params m d) (P : ℝ → ProbePoint d) (ς : Nat → ℝ)
      (pt : ProbePoint d),
      Tendsto P atTop (𝓝 pt) →
      (∀ n : Nat, n < m →
        Tendsto (fun τ : ℝ => frecRunningGate r θ P n τ) atTop (𝓝 (ς n))) →
      GateLimits r θ P ς pt := by
  intro m
  induction m with
  | zero =>
      intro θ P ς pt _hP _hgates
      exact True.intro
  | succ m ih =>
      intro θ P ς pt hP hgates
      have hgate0 :
          Tendsto
            (fun τ : ℝ =>
              firstLayerGate r (Params.headAttention θ) (P τ).1 (P τ).2 τ)
            atTop (𝓝 (ς 0)) := by
        simpa [frecRunningGate] using hgates 0 (Nat.succ_pos m)
      refine ⟨hgate0, ?_⟩
      have heff :
          Tendsto (effectivePath r θ P) atTop
            (𝓝 (effLimitPoint (Params.headValue θ) (ς 0) pt)) :=
        tendsto_effectivePath r θ P (ς 0) pt hP hgate0
      refine ih (Params.tail θ) (effectivePath r θ P) (fun n => ς (n + 1))
        (effLimitPoint (Params.headValue θ) (ς 0) pt) heff ?_
      intro n hn
      simpa [frecRunningGate] using hgates (n + 1) (Nat.succ_lt_succ hn)

/-- Gate constants for a dial endpoint: the level-`0` gate is the dial target, and all
deeper levels use the trichotomy constants. -/
noncomputable def trichotomyDialGateConstants {L d : Nat} {b : ℝ}
    {signU : Set (ProbePair d × ℝ)}
    (T : TexTrichotomyConstructionData (L := L + 1) (d := d) b signU) (t : ℝ) :
    Nat → ℝ :=
  realGateOfTail t (fun n => T.trichotomy.varsigma (n + 1))

@[simp]
theorem trichotomyDialGateConstants_zero {L d : Nat} {b : ℝ}
    {signU : Set (ProbePair d × ℝ)}
    (T : TexTrichotomyConstructionData (L := L + 1) (d := d) b signU) (t : ℝ) :
    trichotomyDialGateConstants T t 0 = t := rfl

@[simp]
theorem trichotomyDialGateConstants_succ {L d : Nat} {b : ℝ}
    {signU : Set (ProbePair d × ℝ)}
    (T : TexTrichotomyConstructionData (L := L + 1) (d := d) b signU)
    (t : ℝ) (n : Nat) :
    trichotomyDialGateConstants T t (n + 1) = T.trichotomy.varsigma (n + 1) := rfl

/-- The dial target at level `0` does not affect the lower-layer saturated matrix. -/
theorem texMatchingSaturatedContributionMatrix_trichotomyDialGateConstants
    {L d : Nat} {b : ℝ} {signU : Set (ProbePair d × ℝ)}
    (θ : Params (L + 1) d)
    (T : TexTrichotomyConstructionData (L := L + 1) (d := d) b signU)
    (t : ℝ) :
    texMatchingSaturatedContributionMatrix θ (trichotomyDialGateConstants T t) =
      texMatchingSaturatedContributionMatrix θ T.trichotomy.varsigma := by
  simp [texMatchingSaturatedContributionMatrix, trichotomyDialGateConstants, realGateOfTail]

/-- The missing interface assertion: the trichotomy gates are the actual running Frec
gates along every matching dial, up to eventual equality at `atTop`.

This is intentionally a separate package.  `TrichotomyData` alone is constructor-level
and permits fake gates; this package is what a genuine trichotomy/cascade construction
must provide before the Frec obligations can be discharged from its saturation fields. -/
structure TexTrichotomyMatchingActualGateData
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {signU : Set (ProbePair d × ℝ)}
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signU) : Prop where
  unprimed_gate_eventuallyEq :
    ∀ δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ)),
      (δ.base, δ.t) ∈ T.Ustar → ∀ n : Nat, 1 ≤ n → n < L + 1 →
        (fun τ : ℝ => frecRunningGate r θ (DialPathData.probe δ) n τ)
          =ᶠ[atTop]
        (fun τ : ℝ => T.unprimed n (δ.base, δ.t) τ)
  primed_gate_eventuallyEq :
    ∀ δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ)),
      (δ.base, δ.t) ∈ T.Ustar → ∀ n : Nat, 1 ≤ n → n < L + 1 →
        (fun τ : ℝ => frecRunningGate r θ' (DialPathData.probe δ) n τ)
          =ᶠ[atTop]
        (fun τ : ℝ => T.primed n (δ.base, δ.t) τ)

/-- The genuine trichotomy unprimed saturation fields give the unprimed saturated Frec
dial asymptotic, once the trichotomy gates are identified with the actual running gates. -/
theorem texMatchingUnprimedSaturatedDialFrecTendsto_of_actualTrichotomyGates
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {signU : Set (ProbePair d × ℝ)}
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signU)
    (S : TexMatchingSaturatedContributionData θ T.trichotomy.varsigma)
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (actual : TexTrichotomyMatchingActualGateData (θ := θ) (θ' := θ') T) :
    TexMatchingUnprimedSaturatedDialFrecTendsto
      (θ := θ) (θ' := θ') T S := by
  intro δ hδ
  let ς := trichotomyDialGateConstants T δ.t
  have hP : Tendsto δ.probe atTop (𝓝 δ.base) := tendsto_dialPathData_probe δ
  have hgate0 :
      Tendsto
        (fun τ : ℝ =>
          firstLayerGate r (Params.headAttention θ) (DialPathData.probe δ τ).1
            (DialPathData.probe δ τ).2 τ)
        atTop (𝓝 (ς 0)) := by
    have h := tendsto_firstLayerGate_dialPathData δ
    rw [hAA]
    simpa [ς] using h
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
          T.trichotomy.unprimed_saturates (δ.base, δ.t) hδ (k + 1) hn_pos hn
        have hactual :=
          actual.unprimed_gate_eventuallyEq δ hδ (k + 1) hn_pos hn
        have htend :
            Tendsto
              (fun τ : ℝ => frecRunningGate r θ (DialPathData.probe δ) (k + 1) τ)
              atTop (𝓝 (T.trichotomy.varsigma (k + 1))) :=
          hsat.tendsto.congr' hactual.symm
        simpa [ς] using htend
  have hGL : GateLimits r θ δ.probe ς δ.base :=
    gateLimits_of_frecRunningGate_tendsto r θ δ.probe ς δ.base hP hgates
  have hfrec :=
    frec_tendsto_of_gateLimits r θ δ.probe ς δ.base hP hGL
  have hlimit :
      frecLimit r θ ς δ.base =
        texMatchingUnprimedSaturatedLimitVector θ S.D δ.t δ.base := by
    rw [frecLimit_eq_texMatchingUnprimedSaturatedLimitVector r θ ς δ.base]
    have hmatrix :
        texMatchingSaturatedContributionMatrix θ ς = S.D := by
      rw [texMatchingSaturatedContributionMatrix_trichotomyDialGateConstants θ T δ.t,
        ← S.D_eq]
    simp [ς, hmatrix]
  simpa [hlimit] using hfrec

/-- The genuine trichotomy primed saturation fields give the primed telescoped Frec dial
asymptotic, once the trichotomy gates are identified with the actual running gates. -/
theorem texMatchingPrimedTelescopedFrecDialAsymptotic_of_actualTrichotomyGates
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (actual : TexTrichotomyMatchingActualGateData (θ := θ) (θ' := θ') T) :
    TexMatchingPrimedTelescopedFrecDialAsymptotic signRegion T := by
  intro δ hδ
  let ς := realGateOfTail δ.t (fun _ => (1 : ℝ))
  have hP : Tendsto δ.probe atTop (𝓝 δ.base) := tendsto_dialPathData_probe δ
  have hgate0 :
      Tendsto
        (fun τ : ℝ =>
          firstLayerGate r (Params.headAttention θ') (DialPathData.probe δ τ).1
            (DialPathData.probe δ τ).2 τ)
        atTop (𝓝 (ς 0)) := by
    simpa [ς] using tendsto_firstLayerGate_dialPathData δ
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
          T.trichotomy.primed_saturates_one (δ.base, δ.t) hδ (k + 1) hn_pos hn
        have hactual :=
          actual.primed_gate_eventuallyEq δ hδ (k + 1) hn_pos hn
        have htend :
            Tendsto
              (fun τ : ℝ => frecRunningGate r θ' (DialPathData.probe δ) (k + 1) τ)
              atTop (𝓝 (1 : ℝ)) :=
          hsat.tendsto.congr' hactual.symm
        simpa [ς, realGateOfTail] using htend
  have hGL : GateLimits r θ' δ.probe ς δ.base :=
    gateLimits_of_frecRunningGate_tendsto r θ' δ.probe ς δ.base hP hgates
  have hfrec :=
    frec_tendsto_of_gateLimits r θ' δ.probe ς δ.base hP hGL
  have hlimit :
      frecLimit r θ' ς δ.base =
        texMatchingPrimedTelescopedLimitVector θ' δ.t δ.base := by
    have htail : ∀ k : Nat, ς (k + 1) = 1 := by
      intro k
      rfl
    rw [frecLimit_eq_texMatchingPrimedTelescopedLimitVector r θ' ς htail δ.base]
    simp [ς, realGateOfTail]
  simpa [hlimit] using hfrec

/-- Packaged unprimed Frec obligation from genuine trichotomy gates. -/
theorem texMatchingUnprimedSaturatedFrecAsymptoticObligation_of_actualTrichotomyGates
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (S : TexMatchingSaturatedContributionData θ T.trichotomy.varsigma)
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (actual : TexTrichotomyMatchingActualGateData (θ := θ) (θ' := θ') T) :
    TexMatchingUnprimedSaturatedFrecAsymptoticObligation signRegion T S :=
  texMatchingUnprimedSaturatedFrecAsymptoticObligation_of_dialFrecTendsto
    signRegion T S
    (texMatchingUnprimedSaturatedDialFrecTendsto_of_actualTrichotomyGates
      T S hAA actual)

/-- Packaged primed Frec obligation from genuine trichotomy gates. -/
theorem texMatchingPrimedTelescopedFrecAsymptoticObligation_of_actualTrichotomyGates
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (actual : TexTrichotomyMatchingActualGateData (θ := θ) (θ' := θ') T) :
    TexMatchingPrimedTelescopedFrecAsymptoticObligation signRegion T :=
  texMatchingPrimedTelescopedFrecAsymptoticObligation_of_dialAsymptotic
    (texMatchingPrimedTelescopedFrecDialAsymptotic_of_actualTrichotomyGates
      signRegion T actual)

/-- R4 package: actual trichotomy gate saturation discharges the regular-quadric closed
recursion Frec obligations consumed by the later matching rewire. -/
theorem texMatchingRegularQuadricClosedRecursionLimitObligation_of_actualTrichotomyGates
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
    (actual : TexTrichotomyMatchingActualGateData (θ := θ) (θ' := θ') T) :
    TexMatchingRegularQuadricClosedRecursionLimitObligation signRegion T N S :=
  texMatchingRegularQuadricClosedRecursionLimitObligation_of_frecAsymptotics
    (L := L) (d := d) (r := r) signRegion T N S
    (texMatchingUnprimedSaturatedFrecAsymptoticObligation_of_actualTrichotomyGates
      signRegion T S hAA actual)
    (texMatchingPrimedTelescopedFrecAsymptoticObligation_of_actualTrichotomyGates
      signRegion T actual)

end TransformerIdentifiability.NLayer
