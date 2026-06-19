import AnyLayerIdentifiabilityProof.NLayer.Genericity.GenericityMain
import AnyLayerIdentifiabilityProof.NLayer.IDL.DescentIDL

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Path/open-set IDL statement

This shard contains the path/open-set induction data for the TeX theorem `ID_L`.
The final all-depth identifiability wrapper specializes this data to the global
constant-probe agreement used in `Theorem main`.
-/

/-- Data for the path/open-set strengthened identifiability theorem `ID_L`.

The `Paths` field is intentionally explicit: the TeX induction does not use global
constant-probe agreement as the induction hypothesis.  It uses agreement on a class of
paths over an open probe region, then realization/sweep constructs a lower-depth open
region and path class. -/
structure IDLData (L d r : Nat) (θ θ' : Params L d) where
  primed_generic : TexGeneric L d θ'
  O : Set (ProbePair d)
  O_open : IsOpen O
  O_nonempty : O.Nonempty
  anchor_nonempty : L = 1 ∨ (O ∩ unwoundAnchorSet θ').Nonempty
  Paths : Set (ProbePath d)
  path_agreement : ObservableAgreementForPaths r θ θ' Paths
  constant_paths_available : ∀ p : ProbePair d, p ∈ O -> constantProbePath p ∈ Paths

namespace IDLData

theorem constantProbePath_mem
    {L d r : Nat} {θ θ' : Params L d}
    (D : IDLData L d r θ θ') {p : ProbePair d} (hp : p ∈ D.O) :
    constantProbePath p ∈ D.Paths :=
  D.constant_paths_available p hp

theorem observableAgreementOn_constantProbePath
    {L d r : Nat} {θ θ' : Params L d}
    (D : IDLData L d r θ θ') {p : ProbePair d} (hp : p ∈ D.O) :
    ∃ T : ℝ, ObservableAgreementOnPath r θ θ' (constantProbePath p) T :=
  D.path_agreement (constantProbePath p) (D.constantProbePath_mem hp)

theorem realTailObservableAgreementAt_of_mem
    {L d r : Nat} {θ θ' : Params L d}
    (D : IDLData L d r θ θ') {p : ProbePair d} (hp : p ∈ D.O) :
    ∃ T : ℝ, 0 ≤ T ∧ RealTailObservableAgreementAt r θ θ' p T := by
  rcases D.observableAgreementOn_constantProbePath hp with ⟨T, hT_nonneg, hT_eq⟩
  exact ⟨T, hT_nonneg, by
    intro τ hτ
    simpa [constantProbePath] using hT_eq τ hτ⟩

end IDLData

end TransformerIdentifiability.NLayer
