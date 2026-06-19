import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeAlphaBranch
import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeCurveRigidity

set_option autoImplicit false

open Matrix

namespace TransformerIdentifiability.NLayer

/-!
# R3 trichotomy builder from cascade branch data

This module is the constructor-level handoff for Proposition `trichotomy`.
It does not manufacture constant gates.  Instead, each unprimed level is supplied by
one of the two cascade branches from the paper proof:

* Case 1 (`Lambda != 0` on a selected component): `CascadeStepData.gate_saturates_of_nonzero`
  gives saturation to the constant sign choice `0` or `1`.
* Case 2 (`Lambda == 0` on the current component): `CascadeStepData.zero_branch`, the
  zero-branch connective, and the alpha branch estimate give saturation to `sig b`.

The remaining geometric/topological work is intentionally explicit in the provider
records: callers must select components and prove the advertised containment/sign data.
-/

/-- Extend the cascade tail after saturating `level` to `value`.

The formal tail is indexed one below the zero-based formal level: `tail (n - 1)` is the
constant used for gate `n`. -/
def cascadeTailExtend (tail : Nat → ℝ) (level : Nat) (value : ℝ) : Nat → ℝ :=
  fun k => if k + 1 = level then value else tail k

@[simp]
theorem cascadeTailExtend_level {tail : Nat → ℝ} {level : Nat} (hlevel : 1 ≤ level)
    (value : ℝ) :
    cascadeTailExtend tail level value (level - 1) = value := by
  simp [cascadeTailExtend, Nat.sub_add_cancel hlevel]

theorem cascadeTailExtend_prior {tail : Nat → ℝ} {level n : Nat}
    (hn_pos : 1 ≤ n) (hn_lt : n < level) (value : ℝ) :
    cascadeTailExtend tail level value (n - 1) = tail (n - 1) := by
  have hn_add : n - 1 + 1 = n := Nat.sub_add_cancel hn_pos
  have hne : n - 1 + 1 ≠ level := by
    intro h
    have hn_eq_level : n = level := by
      rw [← hn_add, h]
    have hlt_self : n < n := by
      rw [hn_eq_level.symm] at hn_lt
      exact hn_lt
    exact (Nat.lt_irrefl n) hlt_self
  simp [cascadeTailExtend, hne]

namespace CascadeStepData

variable {L d : Nat} {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ}
variable {U0 : Set (ProbePair d × ℝ)} {level : Nat} {tail : Nat → ℝ}
variable {unprimed : GateAlongBase d}

/-- Constructor for a cascade step whose zero branch is supplied by the polynomial
curve-rigidity provider.

The limit slope is the honest formal slope specialized to the current first-gate
coordinate and the prior tail.  The caller still supplies the genuine nonzero-slope
saturation theorem; this wrapper only packages it with the already-proved
curve-rigidity constructor for the zero branch. -/
noncomputable def ofZeroBranchProvider
    (level_pos : 1 ≤ level) (level_lt_depth : level < L)
    (prior_saturates :
      ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n → n < level →
        EventuallyExpClose (fun τ => unprimed n x τ) (tail (n - 1)))
    (gate_saturates_of_nonzero :
      ∀ x ∈ U0,
        specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1 ≠ 0 →
          EventuallyExpClose (fun τ => unprimed level x τ)
            (if 0 < (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re
              then 1 else 0))
    (provider : CascadeCurveRigidityProvider θ A level tail) :
    CascadeStepData θ A U0 level tail unprimed where
  level_pos := level_pos
  level_lt_depth := level_lt_depth
  prior_saturates := prior_saturates
  limit_slope := fun x =>
    specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1
  limit_slope_eq := by
    intro x _hx
    rfl
  gate_saturates_of_nonzero := by
    intro x hx hslope
    exact gate_saturates_of_nonzero x hx hslope
  zero_branch := fun _hzero =>
    cascadeCurveRigidityData_of_provider provider

/-- Constructor for a cascade step whose zero-branch provider is only supplied under
the zero-slope hypothesis needed by `CascadeStepData.zero_branch`. -/
noncomputable def ofConditionalZeroBranchProvider
    (level_pos : 1 ≤ level) (level_lt_depth : level < L)
    (prior_saturates :
      ∀ x ∈ U0, ∀ n : Nat, 1 ≤ n → n < level →
        EventuallyExpClose (fun τ => unprimed n x τ) (tail (n - 1)))
    (gate_saturates_of_nonzero :
      ∀ x ∈ U0,
        specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1 ≠ 0 →
          EventuallyExpClose (fun τ => unprimed level x τ)
            (if 0 < (specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1).re
              then 1 else 0))
    (provider :
      (∀ x ∈ U0,
        specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1 = 0) →
      CascadeCurveRigidityProvider θ A level tail) :
    CascadeStepData θ A U0 level tail unprimed where
  level_pos := level_pos
  level_lt_depth := level_lt_depth
  prior_saturates := prior_saturates
  limit_slope := fun x =>
    specializedPhi θ level (gateAssignmentOfTail x.2 tail) x.1
  limit_slope_eq := by
    intro x _hx
    rfl
  gate_saturates_of_nonzero := by
    intro x hx hslope
    exact gate_saturates_of_nonzero x hx hslope
  zero_branch := fun hzero =>
    cascadeCurveRigidityData_of_provider (provider hzero)

end CascadeStepData

/-- Case 1 data for a level: a nonzero component with a constant sign choice.

`selected` is the chosen trichotomy constant for this level.  The field
`selected_matches_slope` is the formal constant-sign datum on the selected component. -/
structure CascadeNonzeroBranchData {L d : Nat} (θ : Params L d)
    (A : Matrix (Fin d) (Fin d) ℝ) (Ustar U0 : Set (ProbePair d × ℝ))
    (level : Nat) (tail : Nat → ℝ) (unprimed : GateAlongBase d) where
  step : CascadeStepData θ A U0 level tail unprimed
  U1 : Set (ProbePair d × ℝ)
  U1_subset_current : U1 ⊆ U0
  Ustar_subset_component : Ustar ⊆ U1
  component_nonempty : U1.Nonempty
  component_relatively_open_in_current :
    ∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ U1 = W ∩ U0
  component_connected : IsPreconnected U1
  slope_nonzero : ∀ x ∈ U1, step.limit_slope x ≠ 0
  selected : ℝ
  selected_zero_or_one : selected = 0 ∨ selected = 1
  selected_matches_slope :
    ∀ x ∈ U1, (if 0 < (step.limit_slope x).re then 1 else 0) = selected

namespace CascadeNonzeroBranchData

variable {L d : Nat} {θ : Params L d} {A : Matrix (Fin d) (Fin d) ℝ}
variable {Ustar U0 : Set (ProbePair d × ℝ)} {level : Nat} {tail : Nat → ℝ}
variable {unprimed : GateAlongBase d}

/-- Constructor from a prepared cascade step and the nonzero-component data. -/
def ofStep
    (step : CascadeStepData θ A U0 level tail unprimed)
    (U1 : Set (ProbePair d × ℝ))
    (U1_subset_current : U1 ⊆ U0)
    (Ustar_subset_component : Ustar ⊆ U1)
    (component_nonempty : U1.Nonempty)
    (component_relatively_open_in_current :
      ∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ U1 = W ∩ U0)
    (component_connected : IsPreconnected U1)
    (slope_nonzero : ∀ x ∈ U1, step.limit_slope x ≠ 0)
    (selected : ℝ)
    (selected_zero_or_one : selected = 0 ∨ selected = 1)
    (selected_matches_slope :
      ∀ x ∈ U1, (if 0 < (step.limit_slope x).re then 1 else 0) = selected) :
    CascadeNonzeroBranchData θ A Ustar U0 level tail unprimed where
  step := step
  U1 := U1
  U1_subset_current := U1_subset_current
  Ustar_subset_component := Ustar_subset_component
  component_nonempty := component_nonempty
  component_relatively_open_in_current := component_relatively_open_in_current
  component_connected := component_connected
  slope_nonzero := slope_nonzero
  selected := selected
  selected_zero_or_one := selected_zero_or_one
  selected_matches_slope := selected_matches_slope

theorem selected_mem_trichotomy {b : ℝ}
    (B : CascadeNonzeroBranchData θ A Ustar U0 level tail unprimed) :
    IsTrichotomyConstant b B.selected := by
  rcases B.selected_zero_or_one with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- Case 1 level saturation, directly from `CascadeStepData.gate_saturates_of_nonzero`. -/
noncomputable def saturates_selected
    (B : CascadeNonzeroBranchData θ A Ustar U0 level tail unprimed) :
    ∀ x ∈ Ustar,
      EventuallyExpClose (fun τ => unprimed level x τ) B.selected := by
  intro x hx
  have hxU1 : x ∈ B.U1 := B.Ustar_subset_component hx
  have hstep :=
    B.step.gate_saturates_of_nonzero x (B.U1_subset_current hxU1)
      (B.slope_nonzero x hxU1)
  simpa [B.selected_matches_slope x hxU1] using hstep

end CascadeNonzeroBranchData

/-- Case 2 data for a level: zero formal slope on the current component, plus the
explicit generic and analytic packages needed to turn curve rigidity into alpha
saturation. -/
structure CascadeZeroAlphaBranchData {L d : Nat} (b : ℝ) (θ : Params L d)
    (A : Matrix (Fin d) (Fin d) ℝ) (Ustar U0 : Set (ProbePair d × ℝ))
    (levelPred : Nat) (tail : Nat → ℝ) (unprimed : GateAlongBase d) where
  step : CascadeStepData θ A U0 (levelPred + 1) tail unprimed
  Ustar_subset_current : Ustar ⊆ U0
  slope_zero_on_current : ∀ x ∈ U0, step.limit_slope x = 0
  dimension_pos : 0 < d
  head_det_ne_zero : A.det ≠ 0
  head_sym_ne_zero : symPart A ≠ 0
  head_value_ne_zero : (paramStream θ 0).1 ≠ 0
  headGate : ProbePair d × ℝ → ℝ → ℝ
  path : ProbePair d × ℝ → ℝ → ProbePair d
  lam : ProbePair d × ℝ → ℝ → ℝ
  gate_sigmoid :
    ∀ x ∈ Ustar, ∀ τ : ℝ,
      unprimed (levelPred + 1) x τ = sig (τ * lam x τ + b)
  alpha_error :
    CascadeAlphaSlopeErrorBound θ A (levelPred + 1) tail Ustar unprimed headGate path lam

namespace CascadeZeroAlphaBranchData

variable {L d : Nat} {b : ℝ} {θ : Params L d}
variable {A : Matrix (Fin d) (Fin d) ℝ}
variable {Ustar U0 : Set (ProbePair d × ℝ)} {levelPred : Nat} {tail : Nat → ℝ}
variable {unprimed : GateAlongBase d}

/-- Constructor from a prepared zero-branch cascade step and the alpha-branch inputs. -/
def ofStep
    (step : CascadeStepData θ A U0 (levelPred + 1) tail unprimed)
    (Ustar_subset_current : Ustar ⊆ U0)
    (slope_zero_on_current : ∀ x ∈ U0, step.limit_slope x = 0)
    (dimension_pos : 0 < d)
    (head_det_ne_zero : A.det ≠ 0)
    (head_sym_ne_zero : symPart A ≠ 0)
    (head_value_ne_zero : (paramStream θ 0).1 ≠ 0)
    (headGate : ProbePair d × ℝ → ℝ → ℝ)
    (path : ProbePair d × ℝ → ℝ → ProbePair d)
    (lam : ProbePair d × ℝ → ℝ → ℝ)
    (gate_sigmoid :
      ∀ x ∈ Ustar, ∀ τ : ℝ,
        unprimed (levelPred + 1) x τ = sig (τ * lam x τ + b))
    (alpha_error :
      CascadeAlphaSlopeErrorBound θ A (levelPred + 1) tail Ustar unprimed
        headGate path lam) :
    CascadeZeroAlphaBranchData b θ A Ustar U0 levelPred tail unprimed where
  step := step
  Ustar_subset_current := Ustar_subset_current
  slope_zero_on_current := slope_zero_on_current
  dimension_pos := dimension_pos
  head_det_ne_zero := head_det_ne_zero
  head_sym_ne_zero := head_sym_ne_zero
  head_value_ne_zero := head_value_ne_zero
  headGate := headGate
  path := path
  lam := lam
  gate_sigmoid := gate_sigmoid
  alpha_error := alpha_error

/-- The curve-rigidity data supplied by the cascade zero branch. -/
noncomputable def rigidity
    (B : CascadeZeroAlphaBranchData b θ A Ustar U0 levelPred tail unprimed) :
    CascadeCurveRigidityData θ A (levelPred + 1) tail :=
  B.step.zero_branch B.slope_zero_on_current

/-- Case 2 zero-branch connective: `gamma` vanishes at `0` and `1`.
The connective is stated for levels of the form `k + 1`, so the zero-branch provider is
indexed by that predecessor. -/
theorem gamma_eval_zero_one
    (B : CascadeZeroAlphaBranchData b θ A Ustar U0 levelPred tail unprimed) :
    (B.rigidity.gamma 0 = 0 ∧ B.rigidity.gamma 1 = 0) := by
  exact
    cascadeCurveRigidity_gamma_eval_zero_one_of_zeroBranch
      (θ := θ) (A1 := A) (level := levelPred) (tail := tail)
      B.dimension_pos B.rigidity B.head_det_ne_zero B.head_sym_ne_zero
      B.head_value_ne_zero

/-- Case 2 level saturation, using the existing zero-branch and alpha-branch APIs. -/
noncomputable def saturates_alpha
    (B : CascadeZeroAlphaBranchData b θ A Ustar U0 levelPred tail unprimed) :
    ∀ x ∈ Ustar,
      EventuallyExpClose (fun τ => unprimed (levelPred + 1) x τ) (sig b) :=
  trichotomyData_unprimed_saturates_alphaBranchAt_of_curveRigidity
    (θ := θ) (A := A) (b := b) (level := levelPred + 1) (tail := tail)
    (Ustar := Ustar) (unprimed := unprimed)
    (varsigma := fun _ => sig b)
    (headGate := B.headGate) (path := B.path) (lam := B.lam)
    rfl
    B.gate_sigmoid
    B.rigidity
    B.gamma_eval_zero_one
    B.alpha_error
    (fun x hx n hn_pos hn_lt =>
      B.step.prior_saturates x (B.Ustar_subset_current hx) n hn_pos hn_lt)

end CascadeZeroAlphaBranchData

/-- A level-local source for the unprimed trichotomy saturation constant. -/
inductive CascadeLevelBranchSource {L d : Nat} (b : ℝ) (θ : Params L d)
    (A : Matrix (Fin d) (Fin d) ℝ) (Ustar : Set (ProbePair d × ℝ))
    (unprimed : GateAlongBase d) (level : Nat) (value : ℝ) : Type where
  | nonzero {U0 : Set (ProbePair d × ℝ)} {tail : Nat → ℝ}
      (B : CascadeNonzeroBranchData θ A Ustar U0 level tail unprimed)
      (hvalue : value = B.selected) :
      CascadeLevelBranchSource b θ A Ustar unprimed level value
  | alpha {U0 : Set (ProbePair d × ℝ)} {tail : Nat → ℝ} {levelPred : Nat}
      (B : CascadeZeroAlphaBranchData b θ A Ustar U0 levelPred tail unprimed)
      (hlevel : level = levelPred + 1)
      (hvalue : value = sig b) :
      CascadeLevelBranchSource b θ A Ustar unprimed level value

namespace CascadeLevelBranchSource

variable {L d : Nat} {b : ℝ} {θ : Params L d}
variable {A : Matrix (Fin d) (Fin d) ℝ}
variable {Ustar : Set (ProbePair d × ℝ)} {unprimed : GateAlongBase d}
variable {level : Nat} {value : ℝ}

/-- Build a nonzero branch source directly from a prepared cascade step and the
selected nonzero component. -/
def ofNonzeroStep {U0 : Set (ProbePair d × ℝ)} {tail : Nat → ℝ}
    (step : CascadeStepData θ A U0 level tail unprimed)
    (U1 : Set (ProbePair d × ℝ))
    (U1_subset_current : U1 ⊆ U0)
    (Ustar_subset_component : Ustar ⊆ U1)
    (component_nonempty : U1.Nonempty)
    (component_relatively_open_in_current :
      ∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ U1 = W ∩ U0)
    (component_connected : IsPreconnected U1)
    (slope_nonzero : ∀ x ∈ U1, step.limit_slope x ≠ 0)
    (selected : ℝ)
    (selected_zero_or_one : selected = 0 ∨ selected = 1)
    (selected_matches_slope :
      ∀ x ∈ U1, (if 0 < (step.limit_slope x).re then 1 else 0) = selected) :
    CascadeLevelBranchSource b θ A Ustar unprimed level selected :=
  CascadeLevelBranchSource.nonzero
    (CascadeNonzeroBranchData.ofStep
      (θ := θ) (A := A) (Ustar := Ustar) (U0 := U0) (level := level)
      (tail := tail) (unprimed := unprimed)
      step U1 U1_subset_current Ustar_subset_component component_nonempty
      component_relatively_open_in_current component_connected slope_nonzero
      selected selected_zero_or_one selected_matches_slope)
    rfl

/-- Package zero/alpha-branch data as a level source at `sig b`. -/
def ofZeroAlphaBranchData {U0 : Set (ProbePair d × ℝ)} {tail : Nat → ℝ}
    {levelPred : Nat}
    (B : CascadeZeroAlphaBranchData b θ A Ustar U0 levelPred tail unprimed) :
    CascadeLevelBranchSource b θ A Ustar unprimed (levelPred + 1) (sig b) :=
  CascadeLevelBranchSource.alpha B rfl rfl

/-- Build a zero/alpha branch source directly from a prepared zero-branch cascade step
and the alpha-branch analytic inputs. -/
def ofZeroAlphaStep {U0 : Set (ProbePair d × ℝ)} {tail : Nat → ℝ}
    {levelPred : Nat}
    (step : CascadeStepData θ A U0 (levelPred + 1) tail unprimed)
    (Ustar_subset_current : Ustar ⊆ U0)
    (slope_zero_on_current : ∀ x ∈ U0, step.limit_slope x = 0)
    (dimension_pos : 0 < d)
    (head_det_ne_zero : A.det ≠ 0)
    (head_sym_ne_zero : symPart A ≠ 0)
    (head_value_ne_zero : (paramStream θ 0).1 ≠ 0)
    (headGate : ProbePair d × ℝ → ℝ → ℝ)
    (path : ProbePair d × ℝ → ℝ → ProbePair d)
    (lam : ProbePair d × ℝ → ℝ → ℝ)
    (gate_sigmoid :
      ∀ x ∈ Ustar, ∀ τ : ℝ,
        unprimed (levelPred + 1) x τ = sig (τ * lam x τ + b))
    (alpha_error :
      CascadeAlphaSlopeErrorBound θ A (levelPred + 1) tail Ustar unprimed
        headGate path lam) :
    CascadeLevelBranchSource b θ A Ustar unprimed (levelPred + 1) (sig b) :=
  CascadeLevelBranchSource.ofZeroAlphaBranchData
    (CascadeZeroAlphaBranchData.ofStep
      (b := b) (θ := θ) (A := A) (Ustar := Ustar) (U0 := U0)
      (levelPred := levelPred) (tail := tail) (unprimed := unprimed)
      step Ustar_subset_current slope_zero_on_current dimension_pos
      head_det_ne_zero head_sym_ne_zero head_value_ne_zero headGate path lam
      gate_sigmoid alpha_error)

theorem value_mem
    (S : CascadeLevelBranchSource b θ A Ustar unprimed level value) :
    IsTrichotomyConstant b value := by
  cases S with
  | nonzero B hvalue =>
      rw [hvalue]
      exact B.selected_mem_trichotomy
  | alpha _B _hlevel hvalue =>
      rw [hvalue]
      exact Or.inr (Or.inr rfl)

/-- Per-level unprimed saturation derived from the selected cascade branch. -/
noncomputable def saturates
    (S : CascadeLevelBranchSource b θ A Ustar unprimed level value) :
    ∀ x ∈ Ustar,
      EventuallyExpClose (fun τ => unprimed level x τ) value := by
  cases S with
  | nonzero B hvalue =>
      subst hvalue
      exact B.saturates_selected
  | alpha B hlevel hvalue =>
      subst hlevel
      subst hvalue
      exact B.saturates_alpha

/-- Extend a prior-saturation invariant using the level-local branch source. -/
noncomputable def extend_prior_saturates
    (S : CascadeLevelBranchSource b θ A Ustar unprimed level value)
    (tail : Nat → ℝ) (hlevel : 1 ≤ level)
    (hprior :
      ∀ x ∈ Ustar, ∀ n : Nat, 1 ≤ n → n < level →
        EventuallyExpClose (fun τ => unprimed n x τ) (tail (n - 1))) :
    ∀ x ∈ Ustar, ∀ n : Nat, 1 ≤ n → n < level + 1 →
      EventuallyExpClose (fun τ => unprimed n x τ)
        (cascadeTailExtend tail level value (n - 1)) := by
  intro x hx n hn_pos hn_lt
  by_cases hn_prior : n < level
  · rw [cascadeTailExtend_prior hn_pos hn_prior value]
    exact hprior x hx n hn_pos hn_prior
  · have hn_le : n ≤ level := Nat.lt_succ_iff.mp hn_lt
    have hlevel_le : level ≤ n := Nat.le_of_not_gt hn_prior
    have hn_eq : n = level := Nat.le_antisymm hn_le hlevel_le
    subst n
    rw [cascadeTailExtend_level hlevel value]
    exact S.saturates x hx

end CascadeLevelBranchSource

/-- The selected next branch for one finite-induction level. -/
structure CascadeLevelBranchChoice {L d : Nat}
    (b : ℝ) (θ : Params L d) (A : Matrix (Fin d) (Fin d) ℝ)
    (U0 : Set (ProbePair d × ℝ)) (unprimed : GateAlongBase d)
    (level : Nat) (tail : Nat → ℝ) where
  Unext : Set (ProbePair d × ℝ)
  Unext_subset_current : Unext ⊆ U0
  nonempty : Unext.Nonempty
  relatively_open_in_current :
    ∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ Unext = W ∩ U0
  connected : IsPreconnected Unext
  value : ℝ
  source_on_subset :
    ∀ {Ufinal : Set (ProbePair d × ℝ)}, Ufinal ⊆ Unext →
      CascadeLevelBranchSource b θ A Ufinal unprimed level value

/-- Pure builder-layer state for the finite cascade induction. -/
structure CascadeInductionState {L d : Nat}
    (b : ℝ) (θ : Params L d) (A : Matrix (Fin d) (Fin d) ℝ)
    (signU : Set (ProbePair d × ℝ)) (unprimed : GateAlongBase d)
    (nextLevel : Nat) where
  U : Set (ProbePair d × ℝ)
  subset_sign_region : U ⊆ signU
  nonempty : U.Nonempty
  relatively_open_in_sign_region :
    ∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ U = W ∩ signU
  connected : IsPreconnected U
  tail : Nat → ℝ
  prior_saturates :
    ∀ x ∈ U, ∀ n : Nat, 1 ≤ n → n < nextLevel →
      EventuallyExpClose (fun τ => unprimed n x τ) (tail (n - 1))
  branches_on_subset :
    ∀ {Ufinal : Set (ProbePair d × ℝ)}, Ufinal ⊆ U →
      ∀ n : Nat, 1 ≤ n → n < nextLevel →
        CascadeLevelBranchSource b θ A Ufinal unprimed n (tail (n - 1))

namespace CascadeInductionState

variable {L d : Nat} {b : ℝ} {θ : Params L d}
variable {A : Matrix (Fin d) (Fin d) ℝ}
variable {signU : Set (ProbePair d × ℝ)}
variable {unprimed : GateAlongBase d} {level : Nat}

/-- Initial pure finite-induction state before any cascade level has been selected. -/
noncomputable def initial
    {L d : Nat} {b : ℝ} {θ : Params L d}
    {A : Matrix (Fin d) (Fin d) ℝ}
    {signU : Set (ProbePair d × ℝ)}
    (unprimed : GateAlongBase d)
    (hnonempty : signU.Nonempty)
    (hrel : ∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ signU = W ∩ signU)
    (hconn : IsPreconnected signU)
    (tail0 : Nat → ℝ) :
    CascadeInductionState b θ A signU unprimed 1 where
  U := signU
  subset_sign_region := fun _ hx => hx
  nonempty := hnonempty
  relatively_open_in_sign_region := hrel
  connected := hconn
  tail := tail0
  prior_saturates := by
    intro _x _hx n hn_pos hn_lt
    have hlt : 1 < 1 := lt_of_le_of_lt hn_pos hn_lt
    exact False.elim ((Nat.lt_irrefl 1) hlt)
  branches_on_subset := by
    intro _Ufinal _hUfinal n hn_pos hn_lt
    have hlt : 1 < 1 := lt_of_le_of_lt hn_pos hn_lt
    exact False.elim ((Nat.lt_irrefl 1) hlt)

/-- Advance the pure finite-induction state by one selected branch. -/
noncomputable def extend
    (S : CascadeInductionState b θ A signU unprimed level)
    (hlevel : 1 ≤ level)
    (C : CascadeLevelBranchChoice b θ A S.U unprimed level S.tail) :
    CascadeInductionState b θ A signU unprimed (level + 1) where
  U := C.Unext
  subset_sign_region := fun x hx => S.subset_sign_region (C.Unext_subset_current hx)
  nonempty := C.nonempty
  relatively_open_in_sign_region := by
    rcases C.relatively_open_in_current with ⟨Wc, hWc, hC⟩
    rcases S.relatively_open_in_sign_region with ⟨Ws, hWs, hS⟩
    refine ⟨Wc ∩ Ws, IsOpen.inter hWc hWs, ?_⟩
    ext x
    constructor
    · intro hx
      have hx_current : x ∈ Wc ∩ S.U := by
        rw [← hC]
        exact hx
      have hx_sign : x ∈ Ws ∩ signU := by
        rw [← hS]
        exact hx_current.2
      exact ⟨⟨hx_current.1, hx_sign.1⟩, hx_sign.2⟩
    · intro hx
      have hx_current : x ∈ S.U := by
        rw [hS]
        exact ⟨hx.1.2, hx.2⟩
      rw [hC]
      exact ⟨hx.1.1, hx_current⟩
  connected := C.connected
  tail := cascadeTailExtend S.tail level C.value
  prior_saturates := by
    have hsource :
        CascadeLevelBranchSource b θ A C.Unext unprimed level C.value :=
      C.source_on_subset (Ufinal := C.Unext) (fun _ hx => hx)
    exact hsource.extend_prior_saturates S.tail hlevel
      (fun x hx n hn_pos hn_lt =>
        S.prior_saturates x (C.Unext_subset_current hx) n hn_pos hn_lt)
  branches_on_subset := by
    intro Ufinal hUfinal n hn_pos hn_lt
    by_cases hn_prior : n < level
    · rw [cascadeTailExtend_prior hn_pos hn_prior C.value]
      exact S.branches_on_subset
        (Ufinal := Ufinal)
        (fun x hx => C.Unext_subset_current (hUfinal hx))
        n hn_pos hn_prior
    · have hn_le : n ≤ level := Nat.lt_succ_iff.mp hn_lt
      have hlevel_le : level ≤ n := Nat.le_of_not_gt hn_prior
      have hn_eq : n = level := Nat.le_antisymm hn_le hlevel_le
      subst n
      rw [cascadeTailExtend_level hlevel C.value]
      exact C.source_on_subset hUfinal

/-- Iterate the pure finite-induction state from an arbitrary positive start level. -/
noncomputable def iterateFrom
    {L d : Nat} {b : ℝ} {θ : Params L d}
    {A : Matrix (Fin d) (Fin d) ℝ}
    {signU : Set (ProbePair d × ℝ)} {unprimed : GateAlongBase d}
    {start : Nat}
    (hstart : 1 ≤ start)
    (S : CascadeInductionState b θ A signU unprimed start)
    (steps : Nat)
    (choose :
      ∀ {level : Nat}, start ≤ level -> level < steps + start ->
        (Slevel : CascadeInductionState b θ A signU unprimed level) ->
          CascadeLevelBranchChoice b θ A Slevel.U unprimed level Slevel.tail) :
    CascadeInductionState b θ A signU unprimed (steps + start) := by
  induction steps with
  | zero =>
      simpa using S
  | succ k ih =>
      have prev :
          CascadeInductionState b θ A signU unprimed (k + start) :=
        ih (fun {level} hstart_le hlevel_lt Slevel =>
          choose hstart_le (by omega) Slevel)
      have hlevel : 1 ≤ k + start := by omega
      have hstart_le_level : start ≤ k + start := by omega
      have hlevel_lt_final : k + start < (k + 1) + start := by omega
      have next :
          CascadeInductionState b θ A signU unprimed ((k + start) + 1) :=
        extend prev hlevel (choose hstart_le_level hlevel_lt_final prev)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next

/-- Iterate the pure finite-induction state from the initial cascade frontier. -/
noncomputable def iterateFromInitial
    {L d : Nat} {b : ℝ} {θ : Params L d}
    {A : Matrix (Fin d) (Fin d) ℝ}
    {signU : Set (ProbePair d × ℝ)}
    (unprimed : GateAlongBase d)
    (hnonempty : signU.Nonempty)
    (hrel : ∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ signU = W ∩ signU)
    (hconn : IsPreconnected signU)
    (tail0 : Nat → ℝ)
    (steps : Nat)
    (choose :
      ∀ {level : Nat}, 1 ≤ level -> level < steps + 1 ->
        (Slevel : CascadeInductionState b θ A signU unprimed level) ->
          CascadeLevelBranchChoice b θ A Slevel.U unprimed level Slevel.tail) :
    CascadeInductionState b θ A signU unprimed (steps + 1) :=
  iterateFrom (start := 1) (by rfl)
    (CascadeInductionState.initial unprimed hnonempty hrel hconn tail0)
    steps choose

end CascadeInductionState

/-- Finite-family trichotomy builder data.

The branch family supplies one honest cascade branch for every trichotomy level
`1 ≤ n < L`; the primed side is supplied separately, matching the proof's independent
primed induction. -/
structure CascadeTrichotomyBuilderData {L d : Nat} (b : ℝ)
    (θ : Params L d) (A : Matrix (Fin d) (Fin d) ℝ)
    (signU Ustar : Set (ProbePair d × ℝ))
    (unprimed primed : GateAlongBase d) where
  subset_sign_region : Ustar ⊆ signU
  nonempty : Ustar.Nonempty
  relatively_open_in_sign_region :
    ∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ Ustar = W ∩ signU
  connected : IsPreconnected Ustar
  varsigma : Nat → ℝ
  unprimed_branch :
    ∀ n : Nat, 1 ≤ n → n < L →
      CascadeLevelBranchSource b θ A Ustar unprimed n (varsigma n)
  primed_saturates_one :
    ∀ x ∈ Ustar, ∀ n : Nat, 1 ≤ n → n < L →
      EventuallyExpClose (fun τ => primed n x τ) 1

namespace CascadeTrichotomyBuilderData

variable {L d : Nat} {b : ℝ} {θ : Params L d}
variable {A : Matrix (Fin d) (Fin d) ℝ}
variable {signU Ustar : Set (ProbePair d × ℝ)}
variable {unprimed primed : GateAlongBase d}

/-- Build the constructor-level `TrichotomyData` from honest branch sources. -/
noncomputable def toTrichotomyData
    (B : CascadeTrichotomyBuilderData b θ A signU Ustar unprimed primed) :
    TrichotomyData (L := L) (d := d) b signU Ustar unprimed primed where
  subset_sign_region := B.subset_sign_region
  nonempty := B.nonempty
  relatively_open_in_sign_region := B.relatively_open_in_sign_region
  connected := B.connected
  varsigma := B.varsigma
  varsigma_mem := by
    intro n hn_pos hn_lt
    exact (B.unprimed_branch n hn_pos hn_lt).value_mem
  unprimed_saturates := by
    intro x hx n hn_pos hn_lt
    exact (B.unprimed_branch n hn_pos hn_lt).saturates x hx
  primed_saturates_one := B.primed_saturates_one

end CascadeTrichotomyBuilderData

/-- Provider-facing package for the honest cascade induction frontier.

Unlike `CascadeTrichotomyBuilderData`, this record owns the selected subregion `Ustar`.
Its fields are exactly the leaves needed to assemble the builder data: the
geometric/topological region data, the unprimed branch source chosen at each level, and
the independently supplied primed saturation. -/
structure CascadeTrichotomyInductionProviderData {L d : Nat} (b : ℝ)
    (θ : Params L d) (A : Matrix (Fin d) (Fin d) ℝ)
    (signU : Set (ProbePair d × ℝ))
    (unprimed primed : GateAlongBase d) where
  Ustar : Set (ProbePair d × ℝ)
  subset_sign_region : Ustar ⊆ signU
  nonempty : Ustar.Nonempty
  relatively_open_in_sign_region :
    ∃ W : Set (ProbePair d × ℝ), IsOpen W ∧ Ustar = W ∩ signU
  connected : IsPreconnected Ustar
  varsigma : Nat → ℝ
  unprimed_branch :
    ∀ n : Nat, 1 ≤ n → n < L →
      CascadeLevelBranchSource b θ A Ustar unprimed n (varsigma n)
  primed_saturates_one :
    ∀ x ∈ Ustar, ∀ n : Nat, 1 ≤ n → n < L →
      EventuallyExpClose (fun τ => primed n x τ) 1

namespace CascadeTrichotomyInductionProviderData

variable {L d : Nat} {b : ℝ} {θ : Params L d}
variable {A : Matrix (Fin d) (Fin d) ℝ}
variable {signU : Set (ProbePair d × ℝ)}
variable {unprimed primed : GateAlongBase d}

/-- Compile the provider-facing induction package to the constructor-level builder data. -/
noncomputable def toBuilderData
    (P : CascadeTrichotomyInductionProviderData b θ A signU unprimed primed) :
    CascadeTrichotomyBuilderData b θ A signU P.Ustar unprimed primed where
  subset_sign_region := P.subset_sign_region
  nonempty := P.nonempty
  relatively_open_in_sign_region := P.relatively_open_in_sign_region
  connected := P.connected
  varsigma := P.varsigma
  unprimed_branch := P.unprimed_branch
  primed_saturates_one := P.primed_saturates_one

end CascadeTrichotomyInductionProviderData

namespace CascadeInductionState

variable {L d : Nat} {b : ℝ} {θ : Params L d}
variable {A : Matrix (Fin d) (Fin d) ℝ}
variable {signU : Set (ProbePair d × ℝ)}
variable {unprimed : GateAlongBase d}

/-- Finalize a depth-`L` pure induction state into provider-facing trichotomy data. -/
noncomputable def toProviderData
    (S : CascadeInductionState b θ A signU unprimed L)
    (primed : GateAlongBase d)
    (primed_saturates_one :
      ∀ x ∈ S.U, ∀ n : Nat, 1 ≤ n → n < L →
        EventuallyExpClose (fun τ => primed n x τ) 1) :
    CascadeTrichotomyInductionProviderData b θ A signU unprimed primed where
  Ustar := S.U
  subset_sign_region := S.subset_sign_region
  nonempty := S.nonempty
  relatively_open_in_sign_region := S.relatively_open_in_sign_region
  connected := S.connected
  varsigma := fun n => S.tail (n - 1)
  unprimed_branch := by
    intro n hn_pos hn_lt
    exact S.branches_on_subset (Ufinal := S.U) (fun _ hx => hx) n hn_pos hn_lt
  primed_saturates_one := primed_saturates_one

end CascadeInductionState

end TransformerIdentifiability.NLayer
