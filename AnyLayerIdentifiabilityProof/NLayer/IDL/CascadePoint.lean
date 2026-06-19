import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeStep
import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeBridge

set_option autoImplicit false

open Filter Topology Matrix

namespace TransformerIdentifiability.NLayer

/-!
# Coupled point/gate convergence: building `GateLimits` from per-level slope facts

`FrecConvergence` proved that `GateLimits` (every running gate saturates) implies the
`Frec` limit.  This file proves `GateLimits` *itself* from purely per-level limiting-slope
information, by the same coupled induction:

* `gateLimits_ones_of_slopePos` — if at every peeled level the limiting bilinear slope is
  positive, then every running gate saturates to `1` (the primed-side cascade, all `Λ>0`).
* `primed_gateLimits` — the primed dial path: a free first gate (the dial limit `t`) followed
  by an all-positive tail cascade.
* `gateLimits_of_slopeSigns` — the mixed `Λ ≠ 0` cascade: each gate saturates to `1[Λ>0]`.

The limiting running point after `n` head-peels is `peelPoint` (from `CascadeBridge`); the
one-step convergence is `tendsto_effectivePath` (from `FrecConvergence`) and the gate
saturation is `CascadeStep`.  These three combine here.
-/

/-- One head-peel of `peelPoint` along a `paramStream`, in terms of the `Params` tail and the
dial-limit advance `effLimitPoint`.  This is the bridge between the `LayerStream`-level
`peelPoint` recursion and the `Params`-level `effectivePath`/`effLimitPoint` recursion. -/
theorem peelPoint_paramStream_succ {m d : Nat} (θ : Params (m + 1) d) (ς : Nat -> ℝ)
    (n : Nat) (pt : ProbePoint d) :
    peelPoint (paramStream θ) ς (n + 1) pt =
      peelPoint (paramStream (Params.tail θ)) (fun k => ς (k + 1)) n
        (effLimitPoint (Params.headValue θ) (ς 0) pt) := by
  rw [peelPoint_succ, paramStream_tail_eq_shift θ, paramStream_zero θ]

/-- **The primed-side cascade.**  If at every peeled level the limiting bilinear slope
`matrixBilin A_n` of the peeled running point is positive, then along `P → pt` every running
gate saturates to `1`, i.e. `GateLimits` holds with `ς ≡ 1`. -/
theorem gateLimits_ones_of_slopePos {d : Nat} (r : Nat) :
    ∀ {m : Nat} (θ : Params m d) (P : ℝ → ProbePoint d) (pt : ProbePoint d),
      Tendsto P atTop (𝓝 pt) →
      (∀ n : Nat, n < m →
        0 < matrixBilin (paramStream θ n).2
          (peelPoint (paramStream θ) (fun _ => 1) n pt).1
          (peelPoint (paramStream θ) (fun _ => 1) n pt).2) →
      GateLimits r θ P (fun _ => 1) pt := by
  intro m
  induction m with
  | zero => intro θ P pt _ _; exact True.intro
  | succ m ih =>
      intro θ P pt hP hpos
      -- head gate: positive slope at the base point `pt`
      have hΛ0 : 0 < matrixBilin (Params.headAttention θ) pt.1 pt.2 := by
        have h := hpos 0 (Nat.succ_pos m)
        rw [paramStream_zero θ, peelPoint_zero] at h
        exact h
      have hgate :
          Tendsto (fun τ => firstLayerGate r (Params.headAttention θ) (P τ).1 (P τ).2 τ)
            atTop (𝓝 (1 : ℝ)) :=
        (eventuallyExpClose_firstLayerGate_of_tendsto_pos r (Params.headAttention θ) P pt
          hP hΛ0).tendsto
      refine ⟨hgate, ?_⟩
      -- recurse on the tail along the effective path
      have heff :
          Tendsto (effectivePath r θ P) atTop
            (𝓝 (effLimitPoint (Params.headValue θ) 1 pt)) :=
        tendsto_effectivePath r θ P 1 pt hP hgate
      refine ih (Params.tail θ) (effectivePath r θ P)
        (effLimitPoint (Params.headValue θ) 1 pt) heff ?_
      intro n hn
      have h := hpos (n + 1) (Nat.succ_lt_succ hn)
      rw [peelPoint_paramStream_succ θ (fun _ => 1) n pt,
        paramStream_tail_eq_shift θ] at h
      rw [paramStream_tail_eq_shift θ]
      exact h

/-- **The primed dial path cascade.**  Level `0` is the dial first gate, converging to the
free dial limit `t`; levels `≥ 1` are the all-positive cascade.  Produces `GateLimits` with
saturation constants `realGateOfTail t (fun _ => 1)` (i.e. `(t, 1, 1, …)`). -/
theorem primed_gateLimits {m d : Nat} (r : Nat) (θ : Params (m + 1) d)
    (P : ℝ → ProbePoint d) (pt : ProbePoint d) (t : ℝ)
    (hP : Tendsto P atTop (𝓝 pt))
    (hgate0 :
      Tendsto (fun τ => firstLayerGate r (Params.headAttention θ) (P τ).1 (P τ).2 τ)
        atTop (𝓝 t))
    (hpos :
      ∀ n : Nat, 1 ≤ n → n < m + 1 →
        0 < matrixBilin (paramStream θ n).2
          (peelPoint (paramStream θ) (realGateOfTail t (fun _ => 1)) n pt).1
          (peelPoint (paramStream θ) (realGateOfTail t (fun _ => 1)) n pt).2) :
    GateLimits r θ P (realGateOfTail t (fun _ => 1)) pt := by
  refine ⟨hgate0, ?_⟩
  -- after one peel the gate stream is all-ones
  have hshift : (fun k => realGateOfTail t (fun _ => 1) (k + 1)) = (fun _ => (1 : ℝ)) := by
    funext k; rfl
  have heff :
      Tendsto (effectivePath r θ P) atTop
        (𝓝 (effLimitPoint (Params.headValue θ) t pt)) :=
    tendsto_effectivePath r θ P t pt hP hgate0
  rw [hshift]
  refine gateLimits_ones_of_slopePos r (Params.tail θ) (effectivePath r θ P)
    (effLimitPoint (Params.headValue θ) t pt) heff ?_
  intro n hn
  have h := hpos (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (Nat.succ_lt_succ hn)
  rw [peelPoint_paramStream_succ θ (realGateOfTail t (fun _ => 1)) n pt,
    paramStream_tail_eq_shift θ] at h
  rw [paramStream_tail_eq_shift θ]
  -- `realGateOfTail t (fun _ => 1) 0 = t` and the shifted tail is all-ones
  simpa only [realGateOfTail, hshift] using h

/-- **The mixed `Λ ≠ 0` cascade.**  If at every peeled level the limiting bilinear slope is
nonzero, then each running gate saturates to `1[Λ>0]`; `GateLimits` holds with
`ς n = if 0 < Λ_n then 1 else 0`.  (Used for the unprimed `Λ ≠ 0` branch of the trichotomy.)

The saturation constants are computed from the peeled slopes recursively via `ς`. -/
theorem gateLimits_of_slopeSigns {d : Nat} (r : Nat) :
    ∀ {m : Nat} (θ : Params m d) (P : ℝ → ProbePoint d) (pt : ProbePoint d)
      (ς : Nat -> ℝ),
      Tendsto P atTop (𝓝 pt) →
      (∀ n : Nat, n < m →
        matrixBilin (paramStream θ n).2
            (peelPoint (paramStream θ) ς n pt).1
            (peelPoint (paramStream θ) ς n pt).2 ≠ 0 ∧
          ς n =
            if 0 < matrixBilin (paramStream θ n).2
                (peelPoint (paramStream θ) ς n pt).1
                (peelPoint (paramStream θ) ς n pt).2 then 1 else 0) →
      GateLimits r θ P ς pt := by
  intro m
  induction m with
  | zero => intro θ P pt ς _ _; exact True.intro
  | succ m ih =>
      intro θ P pt ς hP hsign
      obtain ⟨hΛ0_ne, hς0⟩ := hsign 0 (Nat.succ_pos m)
      rw [paramStream_zero θ, peelPoint_zero] at hΛ0_ne hς0
      have hgate :
          Tendsto (fun τ => firstLayerGate r (Params.headAttention θ) (P τ).1 (P τ).2 τ)
            atTop (𝓝 (ς 0)) := by
        rw [hς0]
        exact tendsto_firstLayerGate_of_tendsto_ne r (Params.headAttention θ) P pt hP hΛ0_ne
      refine ⟨hgate, ?_⟩
      have heff :
          Tendsto (effectivePath r θ P) atTop
            (𝓝 (effLimitPoint (Params.headValue θ) (ς 0) pt)) :=
        tendsto_effectivePath r θ P (ς 0) pt hP hgate
      refine ih (Params.tail θ) (effectivePath r θ P)
        (effLimitPoint (Params.headValue θ) (ς 0) pt) (fun k => ς (k + 1)) heff ?_
      intro n hn
      have h := hsign (n + 1) (Nat.succ_lt_succ hn)
      rw [peelPoint_paramStream_succ θ ς n pt, paramStream_tail_eq_shift θ] at h
      rw [paramStream_tail_eq_shift θ]
      exact h

/-- **The unprimed dial cascade (`Λ ≠ 0` branch).**  A free first gate (the dial limit `t`)
followed by a mixed-sign tail cascade: levels `≥ 1` saturate to `1[Λ>0]`, the genuine
trichotomy constants on the `Λ ≠ 0` side.  Produces `GateLimits` with `ς 0 = t` and
`ς n = if 0 < Λ_n then 1 else 0` for `n ≥ 1`. -/
theorem gateLimits_dialHead_of_slopeSigns {m d : Nat} (r : Nat) (θ : Params (m + 1) d)
    (P : ℝ → ProbePoint d) (pt : ProbePoint d) (t : ℝ) (ς : Nat -> ℝ)
    (hς0 : ς 0 = t)
    (hP : Tendsto P atTop (𝓝 pt))
    (hgate0 :
      Tendsto (fun τ => firstLayerGate r (Params.headAttention θ) (P τ).1 (P τ).2 τ)
        atTop (𝓝 t))
    (hsign :
      ∀ n : Nat, 1 ≤ n → n < m + 1 →
        matrixBilin (paramStream θ n).2
            (peelPoint (paramStream θ) ς n pt).1
            (peelPoint (paramStream θ) ς n pt).2 ≠ 0 ∧
          ς n =
            if 0 < matrixBilin (paramStream θ n).2
                (peelPoint (paramStream θ) ς n pt).1
                (peelPoint (paramStream θ) ς n pt).2 then 1 else 0) :
    GateLimits r θ P ς pt := by
  refine ⟨by rw [hς0]; exact hgate0, ?_⟩
  have heff :
      Tendsto (effectivePath r θ P) atTop
        (𝓝 (effLimitPoint (Params.headValue θ) (ς 0) pt)) :=
    tendsto_effectivePath r θ P (ς 0) pt hP (by rw [hς0]; exact hgate0)
  refine gateLimits_of_slopeSigns r (Params.tail θ) (effectivePath r θ P)
    (effLimitPoint (Params.headValue θ) (ς 0) pt) (fun k => ς (k + 1)) heff ?_
  intro n hn
  have h := hsign (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (Nat.succ_lt_succ hn)
  rw [peelPoint_paramStream_succ θ ς n pt, paramStream_tail_eq_shift θ] at h
  rw [paramStream_tail_eq_shift θ]
  exact h

end TransformerIdentifiability.NLayer
