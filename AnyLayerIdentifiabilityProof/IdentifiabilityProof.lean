import Mathlib
import AnyLayerIdentifiabilityProof.TwoLayerIdentifiability
import AnyLayerIdentifiabilityProof.NLayer.Genericity.GenericityMain
import AnyLayerIdentifiabilityProof.NLayer.Genericity.TexGenericOpenDense
import AnyLayerIdentifiabilityProof.NLayer.Genericity.TexGenericNull
import AnyLayerIdentifiabilityProof.NLayer.Genericity.TexGenericConcrete
import AnyLayerIdentifiabilityProof.NLayer.Foundations.ParamPolynomialGenericity
import AnyLayerIdentifiabilityProof.NLayer.IdentifiabilityMain

set_option autoImplicit false

open MeasureTheory Matrix MvPolynomial

namespace TransformerIdentifiability
namespace IdentifiabilityProof

/-!
Proof-side infrastructure for the public `identifiability.lean` wrapper.

This module is allowed to import the larger project proof files.  The public file is
kept to the trusted model definitions and, once the all-depth theorem is available, a
one-line reference to the theorem exported from this module.
-/

/-! ## Depth-two bridge -/

@[simp] theorem attnLayer_eq_twoLayer {d T : ℕ}
    (V A : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin T) ℝ) :
    NLayer.attnLayer V A X = TwoLayer.attnLayer V A X := by
  rfl

/-! ## All-depth wrap-up bridge -/

/-- The exact TeX generic set packaged as the open-dense carrier expected by
`MainTheoremData`.  Openness/density are the remaining algebraic-genericity proof
obligations from Proposition `genericnonempty`. -/
noncomputable def texGenericAnchorGenericData
    (L d : ℕ) (_hL : 1 ≤ L) (hd₁ : 2 ≤ d)
    (hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d) :
    NLayer.AnchorGenericData L d where
  carrier := NLayer.TexGenericSet L d
  isOpen_carrier := NLayer.isOpen_TexGenericSet L d
  dense_carrier := by
    have hrows : NLayer.genericCertificateRows L ≤ d := by
      simpa [NLayer.genericCertificateRows] using hd₂
    exact NLayer.dense_TexGenericSet L d
      (lt_of_lt_of_le (by norm_num : 0 < 2) hd₁) hrows

/-- Threaded reduced spelling of the parallel builder-selected-tail analytic provider.

This exposes the raw NLayer threaded reduced package for the top-level IDL data
assembled from TeX genericity and probe agreement. -/
abbrev texGenericMainBuilderSelectedTailThreadedReducedAnalyticProvider
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d) : Type :=
  ∀ {θ θ' : NLayer.Params L d},
    (hθ' : θ' ∈ NLayer.TexGenericSet L d) ->
      (hagree : NLayer.ProbeObservableAgreement r θ θ') ->
        NLayer.IDLRecursiveThreadedReducedAnalyticDataOfUnivPathsBuilderSelectedTail
          L d r hd₁ hr
          (NLayer.texGenericIDLData_from_probeAgreement hL hr hd₁ hrows hθ' hagree)
          (NLayer.texGenericIDLData_from_probeAgreement_paths hL hr hd₁ hrows hθ' hagree)

/-- Provider frontier using the threaded builder-selected-tail split base-tail
zero-free concrete data and canonical IFT sweep constructors. -/
abbrev
    texGenericMainProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTThreadedCurrentConstructorProvider :
    (L r d : ℕ) -> (hL : 1 ≤ L) -> (hr : 2 ≤ r) -> (hd₁ : 2 ≤ d) ->
      (hrows : NLayer.genericCertificateRows L ≤ d) -> Type
  | 0, _r, _d, _hL, _hr, _hd₁, _hrows => PUnit
  | 1, _r, _d, _hL, _hr, _hd₁, _hrows => PUnit
  | L + 2, r, d, hL, hr, hd₁, hrows =>
      ∀ {θ θ' : NLayer.Params (L + 2) d},
        (hθ' : θ' ∈ NLayer.TexGenericSet (L + 2) d) ->
          (hagree : NLayer.ProbeObservableAgreement r θ θ') ->
            NLayer.IDLReducedUnivCurrentProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTThreadedRecursiveConstructorData
              hd₁ hr
              (NLayer.texGenericIDLData_from_probeAgreement
                hL hr hd₁ hrows hθ' hagree)
              (NLayer.texGenericIDLData_from_probeAgreement_paths
                hL hr hd₁ hrows hθ' hagree)

/-- Compile the threaded builder-selected-tail current-constructor provider to the
threaded reduced analytic provider. -/
noncomputable def
    texGenericMainBuilderSelectedTailThreadedReducedAnalyticProvider_of_probeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTThreaded
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d)
    (constructors :
      texGenericMainProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTThreadedCurrentConstructorProvider
        L r d hL hr hd₁ hrows) :
    texGenericMainBuilderSelectedTailThreadedReducedAnalyticProvider L r d hL hr hd₁ hrows := by
  cases L with
  | zero =>
      intro _θ _θ' _hθ' _hagree
      exact PUnit.unit
  | succ L =>
      cases L with
      | zero =>
          intro _θ _θ' _hθ' _hagree
          exact PUnit.unit
      | succ L =>
          intro θ θ' hθ' hagree
          exact
            NLayer.idlReducedUnivCurrentProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTThreadedConstructorData_to_threadedReduced
              (L := L) (d := d) (r := r) hd₁ hr
              (NLayer.texGenericIDLData_from_probeAgreement
                hL hr hd₁ hrows hθ' hagree)
              (NLayer.texGenericIDLData_from_probeAgreement_paths
                hL hr hd₁ hrows hθ' hagree)
              (constructors hθ' hagree)

/-- The specific exceptional set chosen in the all-depth theorem: the complement of the
exact TeX genericity conditions `(G1)`--`(G4)`. -/
noncomputable def mainTheoremExceptionalSet
    (L r d : ℕ) (_hL : 1 ≤ L) (_hr : 2 ≤ r)
    (_hd₁ : 2 ≤ d) (_hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d) :
    Set (NLayer.Params L d) :=
  NLayer.TexGenericBadSet L d

/-- The exact TeX bad set is Lebesgue-null.  This is the formal target for
`n_layer_proof.tex`, Proposition `genericnonempty` plus the polynomial zero-set lemma. -/
theorem mainTheoremExceptionalSet_null
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r)
    (hd₁ : 2 ≤ d) (hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d) :
    volume (mainTheoremExceptionalSet L r d hL hr hd₁ hd₂ :
      Set (NLayer.Params L d)) = 0 := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 2) hd₁
  have hrows : NLayer.genericCertificateRows L ≤ d := by
    simpa [NLayer.genericCertificateRows] using hd₂
  simpa [mainTheoremExceptionalSet] using NLayer.texGenericBadSet_null L d hdpos hrows

/-! ## All-depth wrap-up bridge -/

/-- All-depth proof reduction from the threaded builder-selected-tail reduced
analytic-provider frontier.

This uses the threaded builder-selected-tail reduced-data identifiability compiler
directly in the `MainTheoremData.identify_of_probe` path. -/
theorem identifiability_all_depth_of_builderSelectedTailThreadedReducedAnalyticData
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r)
    (hd₁ : 2 ≤ d) (hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d)
    (reduced :
      texGenericMainBuilderSelectedTailThreadedReducedAnalyticProvider L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂)) :
    ∃ N : Set (NLayer.Params L d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : NLayer.Params L d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ,
          NLayer.transformer θ X = NLayer.transformer θ' X) →
        θ = θ' := by
  refine ⟨mainTheoremExceptionalSet L r d hL hr hd₁ hd₂,
    mainTheoremExceptionalSet_null L r d hL hr hd₁ hd₂, ?_⟩
  intro θ' hθ' θ hagree
  have hθ'_generic : θ' ∈ NLayer.TexGenericSet L d := by
    simpa [mainTheoremExceptionalSet, NLayer.TexGenericBadSet] using hθ'
  let Dmain : NLayer.MainTheoremData L d r := {
    generic := texGenericAnchorGenericData L d hL hd₁ hd₂
    identify_of_probe := by
      intro θ θ' hθ' hagree
      exact
        NLayer.IDL_of_univBuilderSelectedTailThreadedReduced
          hL hd₁ hr
          (NLayer.texGenericIDLData_from_probeAgreement
            hL hr hd₁ (by simpa [NLayer.genericCertificateRows] using hd₂)
            hθ' hagree)
          (NLayer.texGenericIDLData_from_probeAgreement_paths
            hL hr hd₁ (by simpa [NLayer.genericCertificateRows] using hd₂)
            hθ' hagree)
          (reduced hθ' hagree)
  }
  exact Dmain.identify_of_full hθ'_generic hagree

/-- All-depth proof reduction from the threaded split base-tail zero-free /
builder-selected-tail / canonical-IFT current-constructor frontier.

The threaded constructor provider is compiled through the NLayer threaded compiler to
the threaded builder-selected-tail reduced analytic provider and then consumed by
`identifiability_all_depth_of_builderSelectedTailThreadedReducedAnalyticData`. -/
theorem
    identifiability_all_depth_of_probeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTThreadedData
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r)
    (hd₁ : 2 ≤ d) (hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d)
    (constructors :
      texGenericMainProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTThreadedCurrentConstructorProvider
        L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂)) :
    ∃ N : Set (NLayer.Params L d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : NLayer.Params L d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ,
          NLayer.transformer θ X = NLayer.transformer θ' X) →
        θ = θ' := by
  exact
    identifiability_all_depth_of_builderSelectedTailThreadedReducedAnalyticData
      L r d hL hr hd₁ hd₂
      (texGenericMainBuilderSelectedTailThreadedReducedAnalyticProvider_of_probeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTThreaded
        L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂) constructors)

/-! ## Explicit genericity-to-analytic frontier -/

set_option linter.style.longLine false

/-- Threaded positive-depth leaves left by the builder-selected-tail current
constructor frontier after the solved-coordinate canonical-gates route has discharged
the current-layer construction.

  Depths `0` and `1` are vacuous.  At depth `L + 2`, the remaining input is the
  realized-tail matching provider. -/
abbrev texGenericMainBuilderSelectedTailThreadedCurrentConstructorLeaves :
    (L r d : ℕ) -> (hL : 1 ≤ L) -> (hr : 2 ≤ r) -> (hd₁ : 2 ≤ d) ->
      (hrows : NLayer.genericCertificateRows L ≤ d) -> Type
  | 0, _r, _d, _hL, _hr, _hd₁, _hrows => PUnit
  | 1, _r, _d, _hL, _hr, _hd₁, _hrows => PUnit
  | _L + 2, r, d, _hL, hr, hd₁, _hrows =>
      NLayer.IDLReducedRealizedTailMatchingFrecProvider d r hd₁ hr

/-- Once the positive-depth threaded leaves are supplied, the threaded
builder-selected-tail current constructor provider follows by the same structural
depth split and solved-coordinate canonical-gates construction, with
`tail0 := fun _ => 0`. -/
noncomputable def texGenericMainThreadedCurrentConstructorProvider_of_builderSelectedTailLeaves
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d)
    (leaves :
      texGenericMainBuilderSelectedTailThreadedCurrentConstructorLeaves
        L r d hL hr hd₁ hrows) :
    texGenericMainProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTThreadedCurrentConstructorProvider
      L r d hL hr hd₁ hrows := by
  cases L with
  | zero =>
      exact PUnit.unit
  | succ L =>
      cases L with
      | zero =>
          exact PUnit.unit
      | succ L =>
          intro θ θ' hθ' hagree
          exact
            NLayer.texGenericProbeAgreementProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTThreadedCurrentConstructorData_of_localRegion_solvedCoordChartCanonicalGates_lowerDepthSelectedTail
              hL hr hd₁ hrows hθ' hagree (fun _ => 0)
              leaves

/-- The remaining genericity-to-analytic constructor theorem for the exact TeX generic set.

This is the formal place where the genericity clauses `(G1)`--`(G4)` must be used to
produce the Step 1 singular-tier data, Step 2 builder-selected-tail matching data,
Step 3 canonical sweep/realization data, and the recursive realized-tail local
providers.
The target is intentionally the current low-level constructor provider, not the final
identifiability conclusion, so the remaining proof debt is visible by unfolding the
current builder-selected-tail current-constructor data in `NLayer.IdentifiabilityMain`.
-/
noncomputable def texGenericMainCurrentConstructorProvider
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d) :
    texGenericMainProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTThreadedCurrentConstructorProvider
      L r d hL hr hd₁ hrows := by
  -- All of Step 1 is discharged from `O_star` genericity, depths `0`/`1` are vacuous, and
  -- the helper discharges the depth split + current-layer canonical-gates wrapper.  The only
  -- positive-depth leaf is the realized-tail matching `Frec` provider, supplied genuinely by
  -- `idlReducedRealizedTailMatchingFrecProvider_genuine` (the parking-trick `dial_mem` plus the
  -- genuine trichotomy, axiom-clean in `Step2/RealizedTailMatching`).
  exact
    texGenericMainThreadedCurrentConstructorProvider_of_builderSelectedTailLeaves
      L r d hL hr hd₁ hrows
      (match L, hL, hrows with
        | 0, _, _ => PUnit.unit
        | 1, _, _ => PUnit.unit
        | _ + 2, _, _ =>
            NLayer.idlReducedRealizedTailMatchingFrecProvider_genuine hd₁ hr)

/-- All-depth identifiability in the null-set form used by `identifiability.lean`.

The null exceptional set and the reduction from full-transformer agreement to the IDL
proof now route through the builder-selected-tail current-constructor frontier.  The
only remaining mathematical gap is the explicit
genericity-to-current-constructor provider `texGenericMainCurrentConstructorProvider`
above. -/
theorem identifiability_all_depth
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r)
    (hd₁ : 2 ≤ d) (hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d) :
    ∃ N : Set (NLayer.Params L d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : NLayer.Params L d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ,
          NLayer.transformer θ X = NLayer.transformer θ' X) →
        θ = θ' := by
  exact
    identifiability_all_depth_of_probeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTThreadedData
      L r d hL hr hd₁ hd₂
      (texGenericMainCurrentConstructorProvider L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂))

set_option linter.style.longLine true

end IdentifiabilityProof
end TransformerIdentifiability
