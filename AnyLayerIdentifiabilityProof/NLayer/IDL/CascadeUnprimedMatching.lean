import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadePrimedMatching

set_option autoImplicit false

open Filter Topology Matrix

namespace TransformerIdentifiability.NLayer

/-!
# R3 (`Λ ≠ 0` branch): the unprimed saturated `Frec` convergence

This is the unprimed analogue of R2 (`CascadePrimedMatching`), for the `Λ ≠ 0` case of the
trichotomy (`prop:trichotomy`, Case 1).  Given that every deeper limiting slope of the
*unprimed* recursion is nonzero along the dial path, each running gate saturates to its sign
`1[Λ>0]`, and the closed recursion `Frec` converges to the **genuine** unprimed saturated
limit vector `texMatchingUnprimedSaturatedLimitVector θ (texMatchingSaturatedContributionMatrix
θ ς) δ.t δ.base` (TeX matching Step 1, `eq:limtheta`), where the saturation matrix `D` is
built from the *actual* per-level constants `ς`.

The first-layer gate uses the unprimed first attention `headAttention θ`; in the matching
context this equals the primed `headAttention θ'` (`FirstLayerEndpointData.attention_eq`), so
the dial first gate converges to the same dial limit `δ.t` as in R2.

The genuine `Λ ≡ 0` (`α`) branch needs the quadric-rigidity analysis (`lem:cascade`(b),
K2/K3) and is **not** covered here — see `CASCADE_PROGRESS.md` R3.
-/

end TransformerIdentifiability.NLayer
