import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeBridge
import AnyLayerIdentifiabilityProof.NLayer.IDL.MatchingCore

set_option autoImplicit false

open Filter Topology Matrix

namespace TransformerIdentifiability.NLayer

/-!
# R1a, concluded: the peeled limit vector *is* the matching limit vector

`CascadeBridge` proved the head-peeling closed form of `frecLimit` in terms of the real
`realSkipBprod`/`realT` recursions.  Here we close the loop with the objects the TeX
matching step (`Step2.IDLMatching`) actually speaks:

* `frecLimit_eq_texMatchingUnprimedSaturatedLimitVector` — along a dial-effective tail path
  with saturation constants `ς`, the limit of `Frec` is exactly
  `texMatchingUnprimedSaturatedLimitVector` with the *genuine* saturation matrix
  `D = realPartMatrix (formalT …)`;
* `frecLimit_eq_texMatchingPrimedTelescopedLimitVector` — on the primed side, where every
  deeper gate saturates to `1`, the limit telescopes to
  `texMatchingPrimedTelescopedLimitVector`.

These are the two limit-vector identities of TeX matching Steps 1–2 (`eq:limtheta`,
`eq:limthetaprime`), now unconditional and complete.
-/

/-- Real parts undo the `matC` embedding. -/
theorem realPartMatrix_matC {d : Nat} (M : Matrix (Fin d) (Fin d) ℝ) :
    realPartMatrix (matC M) = M := by
  ext i j
  simp [realPartMatrix, matC]

/-- `paramStream` of the parameter tail is the shifted stream. -/
theorem paramStream_paramsTail_eq_shift {m d : Nat} (θ : Params (m + 1) d) :
    paramStream (Params.tail θ) = fun j => paramStream θ (j + 1) :=
  paramStream_tail_eq_shift θ

/-- The matching constant `D` is the real transfer matrix `realT` at the saturation
constants: `realPartMatrix (formalT …) = realT …`. -/
theorem texMatchingSaturatedContributionMatrix_eq_realT {L d : Nat}
    (θ : Params (L + 1) d) (ς : Nat -> ℝ) :
    texMatchingSaturatedContributionMatrix θ ς =
      realT (paramStream (Params.tail θ)) (fun k => ς (k + 1)) L := by
  simp only [texMatchingSaturatedContributionMatrix, formalT_matC, realPartMatrix_matC]

/-- **TeX matching Step 1 (`eq:limtheta`).**  The recursively-peeled limit of `Frec`
along a dial-effective tail path equals the unprimed saturated limit vector with the
genuine saturation matrix `D`. -/
theorem frecLimit_eq_texMatchingUnprimedSaturatedLimitVector {L d : Nat} (r : Nat)
    (θ : Params (L + 1) d) (ς : Nat -> ℝ) (pt : ProbePair d) :
    frecLimit r θ ς pt =
      texMatchingUnprimedSaturatedLimitVector θ
        (texMatchingSaturatedContributionMatrix θ ς) (ς 0) pt := by
  rw [frecLimit_eq, realT_head_peel (paramStream θ) ς L, paramStream_zero θ,
    ← paramStream_paramsTail_eq_shift θ,
    ← texMatchingSaturatedContributionMatrix_eq_realT θ ς]
  simp only [texMatchingUnprimedSaturatedLimitVector]

/-- **TeX matching Step 2 (`eq:limthetaprime`).**  On the primed side every deeper gate
saturates to `1`, so the limit telescopes to the primed telescoped limit vector. -/
theorem frecLimit_eq_texMatchingPrimedTelescopedLimitVector {L d : Nat} (r : Nat)
    (θ' : Params (L + 1) d) (g : Nat -> ℝ) (hg : ∀ k, g (k + 1) = 1)
    (pt : ProbePair d) :
    frecLimit r θ' g pt =
      texMatchingPrimedTelescopedLimitVector θ' (g 0) pt := by
  rw [frecLimit_eq, realT_telescope (paramStream θ') g hg L, paramStream_zero θ']
  simp only [texMatchingPrimedTelescopedLimitVector]

end TransformerIdentifiability.NLayer
