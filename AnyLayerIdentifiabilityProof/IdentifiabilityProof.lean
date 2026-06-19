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

/-- TeX `d_*(L) = \binom L2 + 2(L-1)`, the certificate-row lower bound used in the
all-depth main theorem. -/
abbrev dStar (L : ℕ) : ℕ :=
  NLayer.genericCertificateRows L

/-- Dimension lower bound from the all-depth main theorem. -/
abbrev mainTheoremDimensionBound (L : ℕ) : ℕ :=
  max 2 (dStar L)

abbrev LayerParams (d : ℕ) : Type :=
  Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ

instance instMatrixSigmaFinite {n m : ℕ} :
    SigmaFinite (volume : Measure (Matrix (Fin n) (Fin m) ℝ)) :=
  inferInstanceAs (SigmaFinite (volume : Measure (Fin n → Fin m → ℝ)))

instance instLayerParamsSigmaFinite {d : ℕ} :
    SigmaFinite (volume : Measure (LayerParams d)) := by
  infer_instance

/-! ## Depth-two bridge -/

/-- The depth-two `Fin 2 → layer` parameter shape is the same product coordinate
space as the completed two-layer proof's nested-pair parameter shape. -/
noncomputable def depthTwoParamMeasurableEquiv (d : ℕ) :
    NLayer.Params 2 d ≃ᵐ TwoLayer.Params d :=
  MeasurableEquiv.finTwoArrow

/-- Convert a depth-two N-layer parameter to the completed two-layer proof's shape. -/
noncomputable def depthTwoToTwoLayer {d : ℕ} (θ : NLayer.Params 2 d) :
    TwoLayer.Params d :=
  depthTwoParamMeasurableEquiv d θ

/-- Convert the completed two-layer proof's parameter shape to depth-two N-layer
parameters. -/
noncomputable def twoLayerToDepthTwo {d : ℕ} (θ : TwoLayer.Params d) :
    NLayer.Params 2 d :=
  (depthTwoParamMeasurableEquiv d).symm θ

@[simp] theorem depthTwoToTwoLayer_fst {d : ℕ} (θ : NLayer.Params 2 d) :
    (depthTwoToTwoLayer θ).1 = θ 0 := by
  rfl

@[simp] theorem depthTwoToTwoLayer_snd {d : ℕ} (θ : NLayer.Params 2 d) :
    (depthTwoToTwoLayer θ).2 = θ 1 := by
  rfl

@[simp] theorem twoLayerToDepthTwo_zero {d : ℕ} (θ : TwoLayer.Params d) :
    twoLayerToDepthTwo θ 0 = θ.1 := by
  rfl

@[simp] theorem twoLayerToDepthTwo_one {d : ℕ} (θ : TwoLayer.Params d) :
    twoLayerToDepthTwo θ 1 = θ.2 := by
  rfl

theorem depthTwoToTwoLayer_left_inverse {d : ℕ} :
    Function.LeftInverse (twoLayerToDepthTwo (d := d)) depthTwoToTwoLayer := by
  exact (depthTwoParamMeasurableEquiv d).left_inv

theorem depthTwoToTwoLayer_right_inverse {d : ℕ} :
    Function.RightInverse (twoLayerToDepthTwo (d := d)) depthTwoToTwoLayer := by
  exact (depthTwoParamMeasurableEquiv d).right_inv

/-- The depth-two coordinate conversion preserves the finite product Lebesgue measure. -/
theorem measurePreserving_depthTwoToTwoLayer (d : ℕ) :
    MeasurePreserving
      (depthTwoToTwoLayer (d := d))
      (volume : Measure (NLayer.Params 2 d))
      (volume : Measure (TwoLayer.Params d)) := by
  simpa [depthTwoToTwoLayer, depthTwoParamMeasurableEquiv, NLayer.Params,
    TwoLayer.Params, LayerParams] using
    (volume_preserving_piFinTwo
      (fun _ : Fin 2 => LayerParams d))

@[simp] theorem causalSoftmax_eq_twoLayer {T : ℕ}
    (M : Matrix (Fin T) (Fin T) ℝ) :
    NLayer.causalSoftmax M = TwoLayer.causalSoftmax M := by
  rfl

@[simp] theorem attnLayer_eq_twoLayer {d T : ℕ}
    (V A : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin T) ℝ) :
    NLayer.attnLayer V A X = TwoLayer.attnLayer V A X := by
  rfl

/-- Under the depth-two coordinate conversion, the recursive N-layer transformer is
exactly the completed two-layer proof's `network`. -/
theorem transformer_depth_two_eq_twoLayer_network {d T : ℕ}
    (θ : NLayer.Params 2 d) (X : Matrix (Fin d) (Fin T) ℝ) :
    NLayer.transformer θ X = TwoLayer.network (depthTwoToTwoLayer θ) X := by
  change
    NLayer.attnLayer (Fin.tail θ 0).1 (Fin.tail θ 0).2
        (NLayer.attnLayer (θ 0).1 (θ 0).2 X) =
      TwoLayer.attnLayer (θ 1).1 (θ 1).2
        (TwoLayer.attnLayer (θ 0).1 (θ 0).2 X)
  simp only [Fin.tail, attnLayer_eq_twoLayer]
  norm_num

/-- Depth-two specialization of identifiability, pulled back along the depth-two
coordinate equivalence from the completed two-layer proof. -/
theorem identifiability_depth_two (r d : ℕ) (hr : 2 ≤ r) (hd : 3 ≤ d) :
    ∃ N : Set (NLayer.Params 2 d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : NLayer.Params 2 d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ,
          NLayer.transformer θ X = NLayer.transformer θ' X) →
        θ = θ' := by
  obtain ⟨N₂, hN₂_null, hN₂_identifies⟩ :=
    TwoLayer.identifiability r d hr hd
  refine ⟨depthTwoToTwoLayer ⁻¹' N₂, ?_, ?_⟩
  · have hmp := measurePreserving_depthTwoToTwoLayer d
    have hN₂_meas :
        NullMeasurableSet N₂ (volume : Measure (TwoLayer.Params d)) :=
      NullMeasurableSet.of_null hN₂_null
    calc
      volume (depthTwoToTwoLayer ⁻¹' N₂ : Set (NLayer.Params 2 d)) =
          volume N₂ := hmp.measure_preimage hN₂_meas
      _ = 0 := hN₂_null
  · intro θ' hθ' θ hagree
    apply (depthTwoParamMeasurableEquiv d).injective
    apply hN₂_identifies (depthTwoToTwoLayer θ') hθ' (depthTwoToTwoLayer θ)
    intro X
    rw [← transformer_depth_two_eq_twoLayer_network θ X,
      ← transformer_depth_two_eq_twoLayer_network θ' X]
    exact hagree X

/-- Public proof-module endpoint currently backed by the completed depth-two proof. -/
theorem identifiability (r d : ℕ) (hr : 2 ≤ r) (hd : 3 ≤ d) :
    ∃ N : Set (NLayer.Params 2 d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : NLayer.Params 2 d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ,
          NLayer.transformer θ X = NLayer.transformer θ' X) →
        θ = θ' :=
  identifiability_depth_two r d hr hd

/-! ## Polynomial generic exceptional sets -/

/-- The null set cut out by a finite family of coordinate-polynomial nonvanishing
conditions on `Params L d`. -/
def polynomialGenericNullSet {L d : ℕ} {κ : Type*}
    (D : NLayer.PolynomialNonvanishingData (NLayer.ParamCoord L d) κ) :
    Set (NLayer.Params L d) :=
  (NLayer.paramNonvanishingCarrier D)ᶜ

/-- The polynomial generic exceptional set is genuinely Lebesgue-null in parameter
space. -/
theorem polynomialGenericNullSet_null {L d : ℕ} {κ : Type*}
    (D : NLayer.PolynomialNonvanishingData (NLayer.ParamCoord L d) κ) :
    volume (polynomialGenericNullSet D : Set (NLayer.Params L d)) = 0 := by
  simpa [polynomialGenericNullSet] using
    (NLayer.paramNonvanishingCarrier_compl_null D)

/-- Nonmembership in `polynomialGenericNullSet` extracts the polynomial nonvanishing
facts. -/
theorem polynomialGeneric_nonzero_of_not_mem_nullSet {L d : ℕ} {κ : Type*}
    (D : NLayer.PolynomialNonvanishingData (NLayer.ParamCoord L d) κ)
    {θ : NLayer.Params L d} (hθ : θ ∉ polynomialGenericNullSet D) :
    ∀ a, a ∈ D.indices →
      (MvPolynomial.eval (NLayer.paramFlat θ)) (D.poly a) ≠ 0 := by
  simpa [polynomialGenericNullSet] using hθ

/-- All-depth wrap-up bridge matching `n_layer_proof.tex` lines 3516--3541:
if a finite polynomial nonvanishing package is known to imply the generic set consumed by
`MainTheoremData`, then its null complement is an exceptional set for full-transformer
identifiability. -/
theorem identifiability_of_polynomial_generic_mainTheoremData
    {L d r : ℕ} {κ : Type*}
    (Dpoly : NLayer.PolynomialNonvanishingData (NLayer.ParamCoord L d) κ)
    (Dmain : NLayer.MainTheoremData L d r)
    (hsubset : NLayer.paramNonvanishingCarrier Dpoly ⊆ Dmain.generic.carrier) :
    ∃ N : Set (NLayer.Params L d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : NLayer.Params L d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ,
          NLayer.transformer θ X = NLayer.transformer θ' X) →
        θ = θ' := by
  refine ⟨polynomialGenericNullSet Dpoly, polynomialGenericNullSet_null Dpoly, ?_⟩
  intro θ' hθ' θ hagree
  exact Dmain.identify_of_full
    (hsubset (by simpa [polynomialGenericNullSet] using hθ')) hagree

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

/-- Analytic provider still needed to turn exact TeX genericity and probe agreement
into the recursive IDL matching/sweep data.

This is deliberately separate from `TexGenericSet`: the current formal genericity
predicate proves the algebraic/open-dense conditions, but not yet the Claim B/C,
matching-region, matching-limit, and sweep-realization constructors required by the
no-legacy IDL path. -/
abbrev texGenericMainAnalyticProvider
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d) : Type :=
  ∀ {θ θ' : NLayer.Params L d},
    (hθ' : θ' ∈ NLayer.TexGenericSet L d) ->
      (hagree : NLayer.ProbeObservableAgreement r θ θ') ->
        NLayer.TexGenericProbeAgreementAnalyticData hL hr hd₁ hrows hθ' hagree

/-- Reduced spelling of the analytic provider for the all-depth TeX wrap-up.

This exposes the smaller provider assembled in `NLayer.IdentifiabilityMain`: at the
global entry point, matching is stated by the regular-quadric local-patch limit
obligation and sweep by all-realized constant tail probes. -/
abbrev texGenericMainReducedAnalyticProvider
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d) : Type :=
  ∀ {θ θ' : NLayer.Params L d},
    (hθ' : θ' ∈ NLayer.TexGenericSet L d) ->
      (hagree : NLayer.ProbeObservableAgreement r θ θ') ->
        NLayer.TexGenericProbeAgreementReducedAnalyticData hL hr hd₁ hrows hθ' hagree

/-- Reduced spelling of the parallel builder-selected-tail analytic provider.

This intentionally targets the builder-selected-tail reduced data, which is parallel to
the reduced data consumed by `identifiability_all_depth_of_reducedAnalyticData`. -/
abbrev texGenericMainBuilderSelectedTailReducedAnalyticProvider
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d) : Type :=
  ∀ {θ θ' : NLayer.Params L d},
    (hθ' : θ' ∈ NLayer.TexGenericSet L d) ->
      (hagree : NLayer.ProbeObservableAgreement r θ θ') ->
        NLayer.TexGenericProbeAgreementBuilderSelectedTailReducedAnalyticData
          hL hr hd₁ hrows hθ' hagree

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

/-- Provider frontier using the newest bundled local-`Ψ` realization current
constructors. -/
abbrev texGenericMainProbeCoordConcreteLocalPsiRealizationCurrentConstructorProvider
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d) : Type :=
  ∀ {θ θ' : NLayer.Params L d},
    (hθ' : θ' ∈ NLayer.TexGenericSet L d) ->
      (hagree : NLayer.ProbeObservableAgreement r θ θ') ->
        NLayer.TexGenericProbeAgreementProbeCoordConcreteLocalPsiRealizationCurrentConstructorData
          hL hr hd₁ hrows hθ' hagree

/-- Provider frontier using the newest bundled local-`Ψ` realization current
constructors with universal analytic-limit data. -/
abbrev texGenericMainProbeCoordConcreteLocalPsiRealizationUnivAnalyticLimitCurrentConstructorProvider
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d) : Type :=
  ∀ {θ θ' : NLayer.Params L d},
    (hθ' : θ' ∈ NLayer.TexGenericSet L d) ->
      (hagree : NLayer.ProbeObservableAgreement r θ θ') ->
        NLayer.TexGenericProbeAgreementProbeCoordConcreteLocalPsiRealizationUnivAnalyticLimitCurrentConstructorData
          hL hr hd₁ hrows hθ' hagree

/-- Provider frontier using base-tail zero-free concrete data, universal tail-path
asymptotics, and canonical IFT sweep constructors. -/
abbrev
    texGenericMainProbeCoordBaseTailZeroFreeConcreteUnivTailPathAsymptoticCanonicalIFTCurrentConstructorProvider
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d) : Type :=
  ∀ {θ θ' : NLayer.Params L d},
    (hθ' : θ' ∈ NLayer.TexGenericSet L d) ->
      (hagree : NLayer.ProbeObservableAgreement r θ θ') ->
        NLayer.TexGenericProbeAgreementProbeCoordBaseTailZeroFreeConcreteUnivTailPathAsymptoticCanonicalIFTCurrentConstructorData
          hL hr hd₁ hrows hθ' hagree

/-- Provider frontier using split base-tail zero-free concrete data, lower-depth-limits
matching, and canonical IFT sweep constructors. -/
abbrev
    texGenericMainProbeCoordSplitBaseTailZeroFreeConcreteLowerDepthLimitsCanonicalIFTCurrentConstructorProvider
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d) : Type :=
  ∀ {θ θ' : NLayer.Params L d},
    (hθ' : θ' ∈ NLayer.TexGenericSet L d) ->
      (hagree : NLayer.ProbeObservableAgreement r θ θ') ->
        NLayer.TexGenericProbeAgreementProbeCoordSplitBaseTailZeroFreeConcreteLowerDepthLimitsCanonicalIFTCurrentConstructorData
          hL hr hd₁ hrows hθ' hagree

/-- Provider frontier using split base-tail zero-free concrete data,
closed-recursion matching, and canonical IFT sweep constructors. -/
abbrev
    texGenericMainProbeCoordSplitBaseTailZeroFreeConcreteClosedRecursionCanonicalIFTCurrentConstructorProvider
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d) : Type :=
  ∀ {θ θ' : NLayer.Params L d},
    (hθ' : θ' ∈ NLayer.TexGenericSet L d) ->
      (hagree : NLayer.ProbeObservableAgreement r θ θ') ->
        NLayer.TexGenericProbeAgreementProbeCoordSplitBaseTailZeroFreeConcreteClosedRecursionCanonicalIFTCurrentConstructorData
          hL hr hd₁ hrows hθ' hagree

/-- Provider frontier using split base-tail zero-free concrete data,
selected-tail closed-recursion matching, and canonical IFT sweep constructors. -/
abbrev
    texGenericMainProbeCoordSplitBaseTailZeroFreeConcreteSelectedTailClosedRecursionCanonicalIFTCurrentConstructorProvider
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d) : Type :=
  ∀ {θ θ' : NLayer.Params L d},
    (hθ' : θ' ∈ NLayer.TexGenericSet L d) ->
      (hagree : NLayer.ProbeObservableAgreement r θ θ') ->
        NLayer.TexGenericProbeAgreementProbeCoordSplitBaseTailZeroFreeConcreteSelectedTailClosedRecursionCanonicalIFTCurrentConstructorData
          hL hr hd₁ hrows hθ' hagree

/-- Provider frontier using split base-tail zero-free concrete data,
builder-selected-tail matching, and canonical IFT sweep constructors. -/
abbrev
    texGenericMainProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTCurrentConstructorProvider
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d) : Type :=
  ∀ {θ θ' : NLayer.Params L d},
    (hθ' : θ' ∈ NLayer.TexGenericSet L d) ->
      (hagree : NLayer.ProbeObservableAgreement r θ θ') ->
        NLayer.TexGenericProbeAgreementProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTCurrentConstructorData
          hL hr hd₁ hrows hθ' hagree

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

/-- Compile the reduced all-depth analytic provider to the existing provider argument
accepted by `mainTheoremData` and `identifiability_all_depth_of_analyticData`. -/
noncomputable def texGenericMainAnalyticProvider_of_reduced
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d)
    (reduced : texGenericMainReducedAnalyticProvider L r d hL hr hd₁ hrows) :
    texGenericMainAnalyticProvider L r d hL hr hd₁ hrows := by
  intro θ θ' hθ' hagree
  exact
    NLayer.texGenericProbeAgreementAnalyticData_of_reduced
      hL hr hd₁ hrows hθ' hagree (reduced hθ' hagree)

/-- Compile the bundled local-`Ψ` realization current-constructor provider to the
reduced all-depth analytic provider. -/
noncomputable def
    texGenericMainReducedAnalyticProvider_of_probeCoordConcreteLocalPsiRealization
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d)
    (constructors :
      texGenericMainProbeCoordConcreteLocalPsiRealizationCurrentConstructorProvider
        L r d hL hr hd₁ hrows) :
    texGenericMainReducedAnalyticProvider L r d hL hr hd₁ hrows := by
  intro θ θ' hθ' hagree
  exact
    NLayer.texGenericProbeAgreementReducedAnalyticData_of_probeCoordConcreteLocalPsiRealization_current_constructors
      hL hr hd₁ hrows hθ' hagree (constructors hθ' hagree)

/-- Compile the universal analytic-limit bundled local-`Ψ` realization
current-constructor provider to the reduced all-depth analytic provider. -/
noncomputable def
    texGenericMainReducedAnalyticProvider_of_probeCoordConcreteLocalPsiRealizationUnivAnalyticLimit
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d)
    (constructors :
      texGenericMainProbeCoordConcreteLocalPsiRealizationUnivAnalyticLimitCurrentConstructorProvider
        L r d hL hr hd₁ hrows) :
    texGenericMainReducedAnalyticProvider L r d hL hr hd₁ hrows := by
  intro θ θ' hθ' hagree
  exact
    NLayer.texGenericProbeAgreementReducedAnalyticData_of_probeCoordConcreteLocalPsiRealizationUnivAnalyticLimit_current_constructors
      hL hr hd₁ hrows hθ' hagree (constructors hθ' hagree)

/-- Compile the base-tail zero-free / universal tail-path asymptotic / canonical-IFT
current-constructor provider to the reduced all-depth analytic provider. -/
noncomputable def
    texGenericMainReducedAnalyticProvider_of_probeCoordBaseTailZeroFreeConcreteUnivTailPathAsymptoticCanonicalIFT
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d)
    (constructors :
      texGenericMainProbeCoordBaseTailZeroFreeConcreteUnivTailPathAsymptoticCanonicalIFTCurrentConstructorProvider
        L r d hL hr hd₁ hrows) :
    texGenericMainReducedAnalyticProvider L r d hL hr hd₁ hrows := by
  intro θ θ' hθ' hagree
  exact
    NLayer.texGenericProbeAgreementReducedAnalyticData_of_probeCoordBaseTailZeroFreeConcreteUnivTailPathAsymptoticCanonicalIFT_current_constructors
      hL hr hd₁ hrows hθ' hagree (constructors hθ' hagree)

/-- Compile the split base-tail zero-free / lower-depth-limits / canonical-IFT
current-constructor provider to the reduced all-depth analytic provider. -/
noncomputable def
    texGenericMainReducedAnalyticProvider_of_probeCoordSplitBaseTailZeroFreeConcreteLowerDepthLimitsCanonicalIFT
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d)
    (constructors :
      texGenericMainProbeCoordSplitBaseTailZeroFreeConcreteLowerDepthLimitsCanonicalIFTCurrentConstructorProvider
        L r d hL hr hd₁ hrows) :
    texGenericMainReducedAnalyticProvider L r d hL hr hd₁ hrows := by
  intro θ θ' hθ' hagree
  exact
    NLayer.texGenericProbeAgreementReducedAnalyticData_of_probeCoordSplitBaseTailZeroFreeConcreteLowerDepthLimitsCanonicalIFT_current_constructors
      hL hr hd₁ hrows hθ' hagree (constructors hθ' hagree)

/-- Compile the split base-tail zero-free / closed-recursion / canonical-IFT
current-constructor provider to the reduced all-depth analytic provider. -/
noncomputable def
    texGenericMainReducedAnalyticProvider_of_probeCoordSplitBaseTailZeroFreeConcreteClosedRecursionCanonicalIFT
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d)
    (constructors :
      texGenericMainProbeCoordSplitBaseTailZeroFreeConcreteClosedRecursionCanonicalIFTCurrentConstructorProvider
        L r d hL hr hd₁ hrows) :
    texGenericMainReducedAnalyticProvider L r d hL hr hd₁ hrows := by
  intro θ θ' hθ' hagree
  exact
    NLayer.texGenericProbeAgreementReducedAnalyticData_of_probeCoordSplitBaseTailZeroFreeConcreteClosedRecursionCanonicalIFT_current_constructors
      hL hr hd₁ hrows hθ' hagree (constructors hθ' hagree)

/-- Compile the split base-tail zero-free / selected-tail closed-recursion /
canonical-IFT current-constructor provider to the reduced all-depth analytic provider. -/
noncomputable def
    texGenericMainReducedAnalyticProvider_of_probeCoordSplitBaseTailZeroFreeConcreteSelectedTailClosedRecursionCanonicalIFT
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d)
    (constructors :
      texGenericMainProbeCoordSplitBaseTailZeroFreeConcreteSelectedTailClosedRecursionCanonicalIFTCurrentConstructorProvider
        L r d hL hr hd₁ hrows) :
    texGenericMainReducedAnalyticProvider L r d hL hr hd₁ hrows := by
  intro θ θ' hθ' hagree
  exact
    NLayer.texGenericProbeAgreementReducedAnalyticData_of_probeCoordSplitBaseTailZeroFreeConcreteSelectedTailClosedRecursionCanonicalIFT_current_constructors
      hL hr hd₁ hrows hθ' hagree (constructors hθ' hagree)

/-- Compile the split base-tail zero-free / builder-selected-tail / canonical-IFT
current-constructor provider to the parallel builder-selected-tail reduced analytic
provider. -/
noncomputable def
    texGenericMainBuilderSelectedTailReducedAnalyticProvider_of_probeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFT
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d)
    (constructors :
      texGenericMainProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTCurrentConstructorProvider
        L r d hL hr hd₁ hrows) :
    texGenericMainBuilderSelectedTailReducedAnalyticProvider L r d hL hr hd₁ hrows := by
  intro θ θ' hθ' hagree
  exact
    NLayer.texGenericProbeAgreementBuilderSelectedTailReducedAnalyticData_of_probeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFT_current_constructors
      hL hr hd₁ hrows hθ' hagree (constructors hθ' hagree)

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

/-- The Step 1--3 and induction package consumed by the TeX wrap-up proof of
Theorem `main`, now using the exact recursive genericity predicate `𝓖^(L)` and an
explicit analytic provider for the not-yet-derived Step 1--3 data. -/
noncomputable def mainTheoremData
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r)
    (hd₁ : 2 ≤ d) (hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d)
    (analytic :
      texGenericMainAnalyticProvider L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂)) :
    NLayer.MainTheoremData L d r where
  generic := texGenericAnchorGenericData L d hL hd₁ hd₂
  identify_of_probe := by
    intro θ θ' hθ' hagree
    exact NLayer.texGeneric_identifies_from_probeAgreement_of_analyticData
      hL hr hd₁ (by simpa [NLayer.genericCertificateRows] using hd₂) hθ'
      hagree (analytic hθ' hagree)

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

/-- A concrete first-layer value-entry nonvanishing polynomial. -/
noncomputable def firstValueEntryPoly (L d : ℕ) :
    NLayer.ParamRing (L + 1) (d + 1) :=
  MvPolynomial.X (0, Sum.inl (0, 0))

/-- A concrete first-layer attention-entry nonvanishing polynomial. -/
noncomputable def firstAttentionEntryPoly (L d : ℕ) :
    NLayer.ParamRing (L + 1) (d + 1) :=
  MvPolynomial.X (0, Sum.inr (0, 0))

@[simp] theorem firstValueEntryPoly_ne_zero (L d : ℕ) :
    firstValueEntryPoly L d ≠ 0 := by
  simp [firstValueEntryPoly]

@[simp] theorem firstAttentionEntryPoly_ne_zero (L d : ℕ) :
    firstAttentionEntryPoly L d ≠ 0 := by
  simp [firstAttentionEntryPoly]

/-- A concrete starter genericity package: the `(0,0)` entries of the first value and
attention matrices are both nonzero.  Its complement is a finite union of polynomial
zero sets. -/
noncomputable def firstLayerEntryGenericData (L d : ℕ) :
    NLayer.PolynomialNonvanishingData (NLayer.ParamCoord (L + 1) (d + 1)) Bool where
  indices := Finset.univ
  poly b := if b then firstValueEntryPoly L d else firstAttentionEntryPoly L d
  nonzero := by
    intro b _
    cases b <;> simp [firstValueEntryPoly, firstAttentionEntryPoly]

/-- The concrete starter exceptional set. -/
noncomputable def firstLayerEntryGenericNullSet (L d : ℕ) :
    Set (NLayer.Params (L + 1) (d + 1)) :=
  polynomialGenericNullSet (firstLayerEntryGenericData L d)

/-- The concrete starter exceptional set has Lebesgue measure zero. -/
theorem firstLayerEntryGenericNullSet_null (L d : ℕ) :
    volume (firstLayerEntryGenericNullSet L d :
      Set (NLayer.Params (L + 1) (d + 1))) = 0 := by
  simpa [firstLayerEntryGenericNullSet] using
    (polynomialGenericNullSet_null (firstLayerEntryGenericData L d))

theorem first_value_entry_ne_zero_of_not_mem_firstLayerEntryGenericNullSet
    {L d : ℕ} {θ : NLayer.Params (L + 1) (d + 1)}
    (hθ : θ ∉ firstLayerEntryGenericNullSet L d) :
    (θ 0).1 0 0 ≠ 0 := by
  have h :=
    polynomialGeneric_nonzero_of_not_mem_nullSet
      (firstLayerEntryGenericData L d) hθ true (by simp [firstLayerEntryGenericData])
  simpa [firstLayerEntryGenericData, firstValueEntryPoly] using h

theorem first_attention_entry_ne_zero_of_not_mem_firstLayerEntryGenericNullSet
    {L d : ℕ} {θ : NLayer.Params (L + 1) (d + 1)}
    (hθ : θ ∉ firstLayerEntryGenericNullSet L d) :
    (θ 0).2 0 0 ≠ 0 := by
  have h :=
    polynomialGeneric_nonzero_of_not_mem_nullSet
      (firstLayerEntryGenericData L d) hθ false (by simp [firstLayerEntryGenericData])
  simpa [firstLayerEntryGenericData, firstAttentionEntryPoly] using h

/-! ## All-depth wrap-up bridge -/

/-- All-depth proof reduction matching `n_layer_proof.tex`, Theorem `main`, conditional
on the remaining explicit analytic provider.

This is not exported as the completed public theorem: the provider argument records the
precise unfinished Step 1--3 analytic data rather than hiding it in `TexGenericSet`. -/
theorem identifiability_all_depth_of_analyticData
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r)
    (hd₁ : 2 ≤ d) (hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d)
    (analytic :
      texGenericMainAnalyticProvider L r d hL hr hd₁
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
  exact (mainTheoremData L r d hL hr hd₁ hd₂ analytic).identify_of_full
    hθ'_generic hagree

/-- All-depth proof reduction from the reduced analytic-provider frontier.

This is the strongest current wrapper without hiding the remaining Step 1--3 analytic
obligations: the reduced provider is compiled through
`texGenericMainAnalyticProvider_of_reduced` and then consumed by
`identifiability_all_depth_of_analyticData`. -/
theorem identifiability_all_depth_of_reducedAnalyticData
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r)
    (hd₁ : 2 ≤ d) (hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d)
    (reduced :
      texGenericMainReducedAnalyticProvider L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂)) :
    ∃ N : Set (NLayer.Params L d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : NLayer.Params L d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ,
          NLayer.transformer θ X = NLayer.transformer θ' X) →
        θ = θ' := by
  exact
    identifiability_all_depth_of_analyticData L r d hL hr hd₁ hd₂
      (texGenericMainAnalyticProvider_of_reduced L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂) reduced)

/-- All-depth proof reduction from the parallel builder-selected-tail reduced
analytic-provider frontier.

This uses the builder-selected-tail reduced-data identifiability compiler directly in
the `MainTheoremData.identify_of_probe` path, instead of compiling through the legacy
reduced analytic package. -/
theorem identifiability_all_depth_of_builderSelectedTailReducedAnalyticData
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r)
    (hd₁ : 2 ≤ d) (hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d)
    (reduced :
      texGenericMainBuilderSelectedTailReducedAnalyticProvider L r d hL hr hd₁
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
        NLayer.texGeneric_identifies_from_probeAgreement_of_builderSelectedTailReducedAnalyticData
          hL hr hd₁ (by simpa [NLayer.genericCertificateRows] using hd₂)
          hθ' hagree (reduced hθ' hagree)
  }
  exact Dmain.identify_of_full hθ'_generic hagree

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

/-- All-depth proof reduction from the newest bundled local-`Ψ` realization
current-constructor frontier.

The constructor provider is compiled through the NLayer current-constructor compiler to
the reduced analytic provider and then consumed by
`identifiability_all_depth_of_reducedAnalyticData`. -/
theorem identifiability_all_depth_of_probeCoordConcreteLocalPsiRealizationData
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r)
    (hd₁ : 2 ≤ d) (hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d)
    (constructors :
      texGenericMainProbeCoordConcreteLocalPsiRealizationCurrentConstructorProvider
        L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂)) :
    ∃ N : Set (NLayer.Params L d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : NLayer.Params L d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ,
          NLayer.transformer θ X = NLayer.transformer θ' X) →
        θ = θ' := by
  exact
    identifiability_all_depth_of_reducedAnalyticData L r d hL hr hd₁ hd₂
      (texGenericMainReducedAnalyticProvider_of_probeCoordConcreteLocalPsiRealization
        L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂) constructors)

/-- All-depth proof reduction from the universal analytic-limit bundled local-`Ψ`
realization current-constructor frontier.

The constructor provider is compiled through the NLayer universal analytic-limit
current-constructor compiler to the reduced analytic provider and then consumed by
`identifiability_all_depth_of_reducedAnalyticData`. -/
theorem identifiability_all_depth_of_probeCoordConcreteLocalPsiRealizationUnivAnalyticLimitData
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r)
    (hd₁ : 2 ≤ d) (hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d)
    (constructors :
      texGenericMainProbeCoordConcreteLocalPsiRealizationUnivAnalyticLimitCurrentConstructorProvider
        L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂)) :
    ∃ N : Set (NLayer.Params L d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : NLayer.Params L d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ,
          NLayer.transformer θ X = NLayer.transformer θ' X) →
        θ = θ' := by
  exact
    identifiability_all_depth_of_reducedAnalyticData L r d hL hr hd₁ hd₂
      (texGenericMainReducedAnalyticProvider_of_probeCoordConcreteLocalPsiRealizationUnivAnalyticLimit
        L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂) constructors)

/-- All-depth proof reduction from the base-tail zero-free / universal tail-path
asymptotic / canonical-IFT current-constructor frontier.

The constructor provider is compiled through the NLayer base-tail zero-free compiler
to the reduced analytic provider and then consumed by
`identifiability_all_depth_of_reducedAnalyticData`. -/
theorem
    identifiability_all_depth_of_probeCoordBaseTailZeroFreeConcreteUnivTailPathAsymptoticCanonicalIFTData
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r)
    (hd₁ : 2 ≤ d) (hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d)
    (constructors :
      texGenericMainProbeCoordBaseTailZeroFreeConcreteUnivTailPathAsymptoticCanonicalIFTCurrentConstructorProvider
        L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂)) :
    ∃ N : Set (NLayer.Params L d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : NLayer.Params L d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ,
          NLayer.transformer θ X = NLayer.transformer θ' X) →
        θ = θ' := by
  exact
    identifiability_all_depth_of_reducedAnalyticData L r d hL hr hd₁ hd₂
      (texGenericMainReducedAnalyticProvider_of_probeCoordBaseTailZeroFreeConcreteUnivTailPathAsymptoticCanonicalIFT
        L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂) constructors)

/-- All-depth proof reduction from the split base-tail zero-free /
lower-depth-limits / canonical-IFT current-constructor frontier.

The constructor provider is compiled through the NLayer split base-tail compiler
to the reduced analytic provider and then consumed by
`identifiability_all_depth_of_reducedAnalyticData`. -/
theorem
    identifiability_all_depth_of_probeCoordSplitBaseTailZeroFreeConcreteLowerDepthLimitsCanonicalIFTData
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r)
    (hd₁ : 2 ≤ d) (hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d)
    (constructors :
      texGenericMainProbeCoordSplitBaseTailZeroFreeConcreteLowerDepthLimitsCanonicalIFTCurrentConstructorProvider
        L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂)) :
    ∃ N : Set (NLayer.Params L d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : NLayer.Params L d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ,
          NLayer.transformer θ X = NLayer.transformer θ' X) →
        θ = θ' := by
  exact
    identifiability_all_depth_of_reducedAnalyticData L r d hL hr hd₁ hd₂
      (texGenericMainReducedAnalyticProvider_of_probeCoordSplitBaseTailZeroFreeConcreteLowerDepthLimitsCanonicalIFT
        L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂) constructors)

/-- All-depth proof reduction from the split base-tail zero-free /
closed-recursion / canonical-IFT current-constructor frontier.

The constructor provider is compiled through the NLayer split base-tail
closed-recursion compiler to the reduced analytic provider and then consumed by
`identifiability_all_depth_of_reducedAnalyticData`. -/
theorem
    identifiability_all_depth_of_probeCoordSplitBaseTailZeroFreeConcreteClosedRecursionCanonicalIFTData
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r)
    (hd₁ : 2 ≤ d) (hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d)
    (constructors :
      texGenericMainProbeCoordSplitBaseTailZeroFreeConcreteClosedRecursionCanonicalIFTCurrentConstructorProvider
        L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂)) :
    ∃ N : Set (NLayer.Params L d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : NLayer.Params L d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ,
          NLayer.transformer θ X = NLayer.transformer θ' X) →
        θ = θ' := by
  exact
    identifiability_all_depth_of_reducedAnalyticData L r d hL hr hd₁ hd₂
      (texGenericMainReducedAnalyticProvider_of_probeCoordSplitBaseTailZeroFreeConcreteClosedRecursionCanonicalIFT
        L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂) constructors)

/-- All-depth proof reduction from the split base-tail zero-free /
selected-tail closed-recursion / canonical-IFT current-constructor frontier.

The constructor provider is compiled through the NLayer selected-tail split base-tail
compiler to the reduced analytic provider and then consumed by
`identifiability_all_depth_of_reducedAnalyticData`. -/
theorem
    identifiability_all_depth_of_probeCoordSplitBaseTailZeroFreeConcreteSelectedTailClosedRecursionCanonicalIFTData
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r)
    (hd₁ : 2 ≤ d) (hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d)
    (constructors :
      texGenericMainProbeCoordSplitBaseTailZeroFreeConcreteSelectedTailClosedRecursionCanonicalIFTCurrentConstructorProvider
        L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂)) :
    ∃ N : Set (NLayer.Params L d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : NLayer.Params L d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ,
          NLayer.transformer θ X = NLayer.transformer θ' X) →
        θ = θ' := by
  exact
    identifiability_all_depth_of_reducedAnalyticData L r d hL hr hd₁ hd₂
      (texGenericMainReducedAnalyticProvider_of_probeCoordSplitBaseTailZeroFreeConcreteSelectedTailClosedRecursionCanonicalIFT
        L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂) constructors)

/-- All-depth proof reduction from the split base-tail zero-free /
builder-selected-tail / canonical-IFT current-constructor frontier.

The constructor provider is compiled through the NLayer builder-selected-tail split
base-tail compiler to the parallel builder-selected-tail reduced analytic provider and
then consumed by
`identifiability_all_depth_of_builderSelectedTailReducedAnalyticData`. -/
theorem
    identifiability_all_depth_of_probeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTData
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r)
    (hd₁ : 2 ≤ d) (hd₂ : Nat.choose L 2 + 2 * (L - 1) ≤ d)
    (constructors :
      texGenericMainProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTCurrentConstructorProvider
        L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂)) :
    ∃ N : Set (NLayer.Params L d), volume N = 0 ∧
      ∀ θ' ∉ N, ∀ θ : NLayer.Params L d,
        (∀ X : Matrix (Fin d) (Fin (r + 1)) ℝ,
          NLayer.transformer θ X = NLayer.transformer θ' X) →
        θ = θ' := by
  exact
    identifiability_all_depth_of_builderSelectedTailReducedAnalyticData
      L r d hL hr hd₁ hd₂
      (texGenericMainBuilderSelectedTailReducedAnalyticProvider_of_probeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFT
        L r d hL hr hd₁
        (by simpa [NLayer.genericCertificateRows] using hd₂) constructors)

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

/-- The two genuine positive-depth leaves left by the builder-selected-tail current
constructor frontier after the solved-coordinate canonical-gates route has discharged
the current-layer construction.

Depths `0` and `1` are vacuous.  At depth `L + 2`, the remaining input is exactly
the all-depth realized-tail local constructor provider. -/
noncomputable def texGenericMainBuilderSelectedTailCurrentConstructorLeaves :
    (L r d : ℕ) -> (hL : 1 ≤ L) -> (hr : 2 ≤ r) -> (hd₁ : 2 ≤ d) ->
      (hrows : NLayer.genericCertificateRows L ≤ d) -> Type
  | 0, _r, _d, _hL, _hr, _hd₁, _hrows => PUnit
  | 1, _r, _d, _hL, _hr, _hd₁, _hrows => PUnit
  | _L + 2, r, d, _hL, hr, hd₁, _hrows =>
      NLayer.IDLReducedRealizedTailLocalConstructorProvider d r hd₁ hr

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

/-- Once the positive-depth leaf is supplied, the builder-selected-tail current
constructor provider follows by a structural depth split and the direct NLayer
canonical-gates constructor, with `tail0 := fun _ => 0`. -/
noncomputable def texGenericMainCurrentConstructorProvider_of_builderSelectedTailLeaves
    (L r d : ℕ) (hL : 1 ≤ L) (hr : 2 ≤ r) (hd₁ : 2 ≤ d)
    (hrows : NLayer.genericCertificateRows L ≤ d)
    (leaves :
      texGenericMainBuilderSelectedTailCurrentConstructorLeaves
        L r d hL hr hd₁ hrows) :
    texGenericMainProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTCurrentConstructorProvider
      L r d hL hr hd₁ hrows := by
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
            NLayer.texGenericProbeAgreementProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTCurrentConstructorData_of_localRegion_solvedCoordChartCanonicalGates_lowerDepthSelectedTail
              hL hr hd₁ hrows hθ' hagree (fun _ => 0)
              leaves

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

/-- Positive-depth spelling of the first-layer value-entry nonvanishing polynomial. -/
noncomputable def firstValueEntryPolyOfPos (L d : ℕ) (hL : 0 < L) (hd : 0 < d) :
    NLayer.ParamRing L d :=
  MvPolynomial.X (⟨0, hL⟩, Sum.inl (⟨0, hd⟩, ⟨0, hd⟩))

/-- Positive-depth spelling of the first-layer attention-entry nonvanishing polynomial. -/
noncomputable def firstAttentionEntryPolyOfPos (L d : ℕ) (hL : 0 < L) (hd : 0 < d) :
    NLayer.ParamRing L d :=
  MvPolynomial.X (⟨0, hL⟩, Sum.inr (⟨0, hd⟩, ⟨0, hd⟩))

@[simp] theorem firstValueEntryPolyOfPos_ne_zero
    (L d : ℕ) (hL : 0 < L) (hd : 0 < d) :
    firstValueEntryPolyOfPos L d hL hd ≠ 0 := by
  simp [firstValueEntryPolyOfPos]

@[simp] theorem firstAttentionEntryPolyOfPos_ne_zero
    (L d : ℕ) (hL : 0 < L) (hd : 0 < d) :
    firstAttentionEntryPolyOfPos L d hL hd ≠ 0 := by
  simp [firstAttentionEntryPolyOfPos]

/-- Concrete positive-depth genericity package: the `(0,0)` entries of the first value
and attention matrices are both nonzero. -/
noncomputable def firstLayerEntryGenericDataOfPos
    (L d : ℕ) (hL : 0 < L) (hd : 0 < d) :
    NLayer.PolynomialNonvanishingData (NLayer.ParamCoord L d) Bool where
  indices := Finset.univ
  poly b :=
    if b then firstValueEntryPolyOfPos L d hL hd
    else firstAttentionEntryPolyOfPos L d hL hd
  nonzero := by
    intro b _
    cases b <;> simp [firstValueEntryPolyOfPos, firstAttentionEntryPolyOfPos]

/-- Concrete positive-depth exceptional set cut out by two first-layer coordinate
polynomials. -/
noncomputable def firstLayerEntryGenericNullSetOfPos
    (L d : ℕ) (hL : 0 < L) (hd : 0 < d) :
    Set (NLayer.Params L d) :=
  polynomialGenericNullSet (firstLayerEntryGenericDataOfPos L d hL hd)

/-- The concrete positive-depth first-layer exceptional set has Lebesgue measure zero. -/
theorem firstLayerEntryGenericNullSetOfPos_null
    (L d : ℕ) (hL : 0 < L) (hd : 0 < d) :
    volume (firstLayerEntryGenericNullSetOfPos L d hL hd :
      Set (NLayer.Params L d)) = 0 := by
  simpa [firstLayerEntryGenericNullSetOfPos] using
    (polynomialGenericNullSet_null (firstLayerEntryGenericDataOfPos L d hL hd))

theorem first_value_entry_ne_zero_of_not_mem_firstLayerEntryGenericNullSetOfPos
    {L d : ℕ} {hL : 0 < L} {hd : 0 < d} {θ : NLayer.Params L d}
    (hθ : θ ∉ firstLayerEntryGenericNullSetOfPos L d hL hd) :
    (θ ⟨0, hL⟩).1 ⟨0, hd⟩ ⟨0, hd⟩ ≠ 0 := by
  have h :=
    polynomialGeneric_nonzero_of_not_mem_nullSet
      (firstLayerEntryGenericDataOfPos L d hL hd) hθ true
      (by simp [firstLayerEntryGenericDataOfPos])
  simpa [firstLayerEntryGenericDataOfPos, firstValueEntryPolyOfPos] using h

theorem first_attention_entry_ne_zero_of_not_mem_firstLayerEntryGenericNullSetOfPos
    {L d : ℕ} {hL : 0 < L} {hd : 0 < d} {θ : NLayer.Params L d}
    (hθ : θ ∉ firstLayerEntryGenericNullSetOfPos L d hL hd) :
    (θ ⟨0, hL⟩).2 ⟨0, hd⟩ ⟨0, hd⟩ ≠ 0 := by
  have h :=
    polynomialGeneric_nonzero_of_not_mem_nullSet
      (firstLayerEntryGenericDataOfPos L d hL hd) hθ false
      (by simp [firstLayerEntryGenericDataOfPos])
  simpa [firstLayerEntryGenericDataOfPos, firstAttentionEntryPolyOfPos] using h

end IdentifiabilityProof
end TransformerIdentifiability
