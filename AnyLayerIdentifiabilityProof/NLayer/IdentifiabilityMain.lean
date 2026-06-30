import AnyLayerIdentifiabilityProof.NLayer.IDL.IDLBase
import AnyLayerIdentifiabilityProof.NLayer.IDL.IDLStep1
import AnyLayerIdentifiabilityProof.NLayer.Step2.IDLMatching
import AnyLayerIdentifiabilityProof.NLayer.Step2.IDLSweep
import AnyLayerIdentifiabilityProof.NLayer.Step2.SweepWiring
import AnyLayerIdentifiabilityProof.NLayer.Step2.RealizedTailMatching
import AnyLayerIdentifiabilityProof.NLayer.IDL.AnchorExistence

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# All-depth identifiability bridge

This file owns the formal route from exact TeX genericity and probe agreement to
parameter equality.  `IdentifiabilityProof.lean` should only call the final theorem
from this file.
-/

namespace IDLData

/-- The recursive genericity clauses exposed by a positive-depth `IDLData`. -/
theorem texGenericStepClauses
    {L d r : Nat} {θ θ' : Params (L + 2) d}
    (D : IDLData (L + 2) d r θ θ') :
    TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
      (fun η => TexAnchorCertificate η) θ' := by
  simpa [TexGeneric] using D.primed_generic

/-- The Step 1 endpoint obtained from `IDLData` via the global-product (`A_gp`) tier
system.  All Step 1 analytic leaves (Claim B, Claim C, transfer, descent, depth
certificate) are discharged unconditionally; no `claimB`/`claimC` providers are needed. -/
theorem firstLayerEndpoint
    {L d r : Nat} (hr : 2 <= r) {θ θ' : Params (L + 2) d}
    (D : IDLData (L + 2) d r θ θ') :
    FirstLayerEndpointData
      (Params.headAttention θ) (Params.headAttention θ')
      (Params.headValue θ) :=
  firstLayerEndpoint_of_texGenericStep_of_IDLData_globalProduct
    (L := L + 1) (d := d) (r := r)
    (θ := θ) (θ' := θ') hr D.texGenericStepClauses D

end IDLData

/-! ## Reduced analytic-provider assembly -/

set_option linter.style.longLine false in
private theorem projectionGraphReducedStep1ProviderData_to_step1ProviderData
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    {hStanding : Step1StandingAssumptions r L d O θ θ'}
    (D :
      FixedOStarGraphBoundaryBaseTailLeadAtTierProjectionGraphReducedStep1ProviderData
        hr hStanding) :
    FixedOStarStep1ProviderData hr hStanding :=
  fixedOStarStep1ProviderData_of_graphBoundaryBaseTailLeadAtTierProjectionGraphReducedStep1ProviderData D

set_option linter.style.longLine false in
private theorem projectionGraphReducedStep1ProviderData_of_reducedStep1Fields
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    (regularPolePreimage :
      Step1OStarRegularPolePreimageFamilyData
        (L := L) (d := d) (r := r) (O := O) (θ := θ) (θ' := θ') hr)
    (genericPolynomials :
      Step1OStarProjectionGraphGenericPolynomialWitnessData L d r θ' O)
    (hStanding : Step1StandingAssumptions r L d O θ θ') :
    FixedOStarGraphBoundaryBaseTailLeadAtTierProjectionGraphReducedStep1ProviderData
      hr hStanding :=
  let regularPoleLeadAtTier :
      ∀ hStanding : Step1StandingAssumptions r L d O θ θ',
        FixedOStarRegularPoleLeadAtTierData hr hStanding :=
    fixedOStarRegularPoleLeadAtTierData_family_of_regularPolePreimage_and_genericPolynomials
      regularPolePreimage genericPolynomials
  fixedOStarProjectionGraphReducedProviderData_of_regularPole_and_genericPolynomials
    (regularPoleLeadAtTier hStanding) genericPolynomials

set_option linter.style.longLine false in
private theorem step1ProviderData_of_reducedStep1Fields
    {L d r : Nat} {O : Set (ProbePair d)}
    {θ θ' : Params L d}
    {hr : 2 <= r}
    (regularPolePreimage :
      Step1OStarRegularPolePreimageFamilyData
        (L := L) (d := d) (r := r) (O := O) (θ := θ) (θ' := θ') hr)
    (genericPolynomials :
      Step1OStarProjectionGraphGenericPolynomialWitnessData L d r θ' O)
    (hStanding : Step1StandingAssumptions r L d O θ θ') :
    FixedOStarStep1ProviderData hr hStanding :=
  projectionGraphReducedStep1ProviderData_to_step1ProviderData
    (projectionGraphReducedStep1ProviderData_of_reducedStep1Fields
      regularPolePreimage genericPolynomials hStanding)

private theorem step1SplitBaseTailGraphObligations_of_IDLData_formalPhiNoPole
    {L d r : Nat} {θ θ' : Params (L + 2) d}
    {hr : 2 <= r}
    (hstep :
      TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
        (fun η => TexAnchorCertificate η) θ')
    (D : IDLData (L + 2) d r θ θ')
    (splitBaseTailZeroFree :
      Step1OStarProjectionSplitBaseTailZeroFreeWitnessData (L + 2) d θ' D.O)
    (lastBoundaryFormalPhiNoPole :
      ∀ hStanding : Step1StandingAssumptions r (L + 2) d D.O θ θ',
        FixedOStarRegularPoleLastBoundaryFormalPhiNoPoleDataOfDepthGTOne
          hr hStanding) :
    Step1OStarProjectionGraphSplitBaseTailZeroFreeConcreteObligations
      (L + 2) d r θ' D.O := by
  let hStanding : Step1StandingAssumptions r (L + 2) d D.O θ θ' :=
    { depth_pos := Nat.succ_pos (L + 1)
      generic := hstep.toOStarGenericAssumptions D.O_open D.O_nonempty
      agreement := localProbeTailAgreement_of_IDLData D }
  exact
    step1SplitBaseTailGraphObligations_of_formalPhiNoPole
      (hStanding := hStanding) splitBaseTailZeroFree
      (lastBoundaryFormalPhiNoPole hStanding)

private theorem step1SplitBaseTailGraphObligations_of_IDLData_graphNoPole
    {L d r : Nat} {θ θ' : Params (L + 2) d}
    (D : IDLData (L + 2) d r θ θ')
    (splitBaseTailZeroFree :
      Step1OStarProjectionSplitBaseTailZeroFreeWitnessData (L + 2) d θ' D.O)
    (lastBoundaryNoPole :
      Step1LastBoundaryFormalPhiNoPoleOnOStarProbeCoordGraphData
        (L := L + 2) (d := d) (O := D.O) (r := r) θ') :
    Step1OStarProjectionGraphSplitBaseTailZeroFreeConcreteObligations
      (L + 2) d r θ' D.O :=
  step1SplitBaseTailGraphObligations_of_graphNoPole
    splitBaseTailZeroFree lastBoundaryNoPole

private theorem step1GenericPolynomials_of_IDLData_splitBaseTail_formalPhiNoPole
    {L d r : Nat} {θ θ' : Params (L + 2) d}
    {hr : 2 <= r}
    (hstep :
      TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
        (fun η => TexAnchorCertificate η) θ')
    (D : IDLData (L + 2) d r θ θ')
    (splitBaseTailZeroFree :
      Step1OStarProjectionSplitBaseTailZeroFreeWitnessData (L + 2) d θ' D.O)
    (lastBoundaryFormalPhiNoPole :
      ∀ hStanding : Step1StandingAssumptions r (L + 2) d D.O θ θ',
        FixedOStarRegularPoleLastBoundaryFormalPhiNoPoleDataOfDepthGTOne
          hr hStanding) :
    Step1OStarProjectionGraphGenericPolynomialWitnessData (L + 2) d r θ' D.O :=
  step1OStarProjectionGraphGenericPolynomialWitnessData_of_splitBaseTailZeroFreeConcrete
    (step1SplitBaseTailGraphObligations_of_IDLData_formalPhiNoPole
      hstep D splitBaseTailZeroFree lastBoundaryFormalPhiNoPole)

private theorem step1GenericPolynomials_of_IDLData_splitBaseTail_graphNoPole
    {L d r : Nat} {θ θ' : Params (L + 2) d}
    (D : IDLData (L + 2) d r θ θ')
    (splitBaseTailZeroFree :
      Step1OStarProjectionSplitBaseTailZeroFreeWitnessData (L + 2) d θ' D.O)
    (lastBoundaryNoPole :
      Step1LastBoundaryFormalPhiNoPoleOnOStarProbeCoordGraphData
        (L := L + 2) (d := d) (O := D.O) (r := r) θ') :
    Step1OStarProjectionGraphGenericPolynomialWitnessData (L + 2) d r θ' D.O :=
  step1OStarProjectionGraphGenericPolynomialWitnessData_of_splitBaseTail_graphNoPole
    splitBaseTailZeroFree lastBoundaryNoPole

/-- Reduced matching surface exposed by the recursive package.

It stores the selected regular-quadric dial membership plus split lower-depth
tail-path `Frec` data for chosen unprimed and primed tail path classes.  The bundled
local-patch provider record is rebuilt locally by
`reducedMatchingProviderData_to_frecProviderData`. -/
structure TexMatchingReducedLocalPatchRegularQuadricFrecProviderData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Type where
  dial_mem :
    let region :=
      texRegionConstructionData_of_IDLData_of_localPatch
        (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    let signRegion :=
      texMatchingSignRegionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region
    let T :=
      texTrichotomyConstructionData_of_signRegion
        (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
    let N :=
      texMatchingProductNeighborhoodData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region
    TexMatchingRegularQuadricDialMemObligation D signRegion T N
  unprimedTailPaths : Set (ProbePath d)
  primedTailPaths : Set (ProbePath d)
  lowerDepthAnalytic :
    TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
      (r := r) (Params.tail θ) (Params.tail θ')
      unprimedTailPaths primedTailPaths
  lowerDepthPathMem :
    let region :=
      texRegionConstructionData_of_IDLData_of_localPatch
        (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    let signRegion :=
      texMatchingSignRegionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region
    let T :=
      texTrichotomyConstructionData_of_signRegion
        (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
    let N :=
      texMatchingProductNeighborhoodData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region
    TexMatchingRegularQuadricLowerDepthEffectiveTailPathMemData
      (θ := θ) (θ' := θ') signRegion T N unprimedTailPaths primedTailPaths
  lowerDepthLimits :
    let region :=
      texRegionConstructionData_of_IDLData_of_localPatch
        (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    let signRegion :=
      texMatchingSignRegionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region
    let T :=
      texTrichotomyConstructionData_of_signRegion
        (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
    let N :=
      texMatchingProductNeighborhoodData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region
    let S :=
      texMatchingSaturatedContributionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D region
    TexMatchingRegularQuadricLowerDepthLimitIdentificationData
      signRegion T N S unprimedTailPaths primedTailPaths lowerDepthAnalytic

private def reducedMatchingProviderData_to_frecProviderData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (P :
      TexMatchingReducedLocalPatchRegularQuadricFrecProviderData
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricFrecProviderData
      hL hr hstep endpoint D localRegion :=
  let lowerDepthProvider :=
    texMatchingRegularQuadricLowerDepthTailPathFrecProviderData_of_parts
      P.lowerDepthAnalytic P.lowerDepthPathMem P.lowerDepthLimits
  texMatchingLocalPatchRegularQuadricFrecProviderData_of_selectedDialLowerDepthTailPath
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    P.dial_mem P.unprimedTailPaths P.primedTailPaths lowerDepthProvider

/-- Universal-path reduced matching surface.

The active matching frontier is selected product-neighborhood effective-tail analytic
data plus closed-recursion limit identification; dial membership is still derived from
`D.Paths = Set.univ`. -/
structure TexMatchingReducedUnivLocalPatchRegularQuadricFrecProviderData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Type where
  selectedEffectiveTail :
    TexMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData
      hL hr hstep endpoint D localRegion
  closedRecursionLimits :
    TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
      hL hr hstep endpoint D localRegion

set_option linter.style.longLine false in
private def reducedUnivMatchingProviderData_to_frecProviderData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (hPaths : D.Paths = Set.univ)
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (P :
      TexMatchingReducedUnivLocalPatchRegularQuadricFrecProviderData
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricFrecProviderData
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricFrecProviderData_of_paths_univ_selectedEffectiveTail_closedRecursionLimits
    (L := L) (d := d) (r := r) hL hr hstep endpoint D hPaths localRegion
    P.selectedEffectiveTail P.closedRecursionLimits

set_option linter.style.longLine false in
private def closedRecursionLimitObligation_of_reducedUnivMatchingProviderData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (_hPaths : D.Paths = Set.univ)
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (P :
      TexMatchingReducedUnivLocalPatchRegularQuadricFrecProviderData
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
      hL hr hstep endpoint D localRegion :=
  P.closedRecursionLimits

private noncomputable def reducedUnivMatchingProviderData_to_firstLayerAnalytic
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (hPaths : D.Paths = Set.univ)
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (P :
      TexMatchingReducedUnivLocalPatchRegularQuadricFrecProviderData
        hL hr hstep endpoint D localRegion) :
    TexFirstLayerMatchingAnalyticData hr hstep endpoint D :=
  let matchingProvider :
      TexMatchingLocalPatchRegularQuadricFrecProviderData
        hL hr hstep endpoint D localRegion :=
    reducedUnivMatchingProviderData_to_frecProviderData
      hL hr hstep endpoint D hPaths localRegion P
  let matchingClosed :
      TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
        hL hr hstep endpoint D localRegion :=
    closedRecursionLimitObligation_of_reducedUnivMatchingProviderData
      hL hr hstep endpoint D hPaths localRegion P
  let matchingRegionProvider :
      TexMatchingRegionProviderFromLocalPatchData
        hL hr hstep endpoint D localRegion :=
    texMatchingRegionProviderFromLocalPatchData_of_regularQuadricClosedRecursionLimits
      (L := L) (d := d) (r := r)
      hL hr hstep endpoint D localRegion
      matchingProvider.dial_mem matchingClosed
  texFirstLayerMatchingAnalyticData_of_provider
    (L := L) (d := d) (r := r) hr hstep endpoint D
    (texMatchingRegionProviderData_of_localPatch
      (L := L) (d := d) (r := r)
      hL hr hstep endpoint D localRegion matchingRegionProvider)

/-- Universal-path matching constructor reduced to lower-depth tail-path data.

This avoids exposing the bundled `TexMatchingReducedUniv...` record at the current
constructor boundary.  Universal lower-depth convergence supplies the selected
effective-tail analytic data, while the two selected tail-path asymptotics supply the
closed-recursion limits.  The `lowerDepthAnalytic` field is an actual convergence
input: it is not derivable from `tailReduced`, since `tailReduced` is only available
after this matching package has built the first-layer matching and sweep tail data. -/
structure TexMatchingReducedUnivLocalPatchRegularQuadricTailPathConstructorData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D) : Type where
  lowerDepthAnalytic :
    TexMatchingRegularQuadricLowerDepthUnivTailPathFrecAnalyticData
      (r := r) (Params.tail θ) (Params.tail θ')
  unprimedTailPath :
    TexMatchingLocalPatchRegularQuadricUnprimedSaturatedTailPathFrecAsymptotic
      hL hr hstep endpoint D localRegion
  primedTailPath :
    TexMatchingLocalPatchRegularQuadricPrimedTelescopedTailPathFrecAsymptotic
      hL hr hstep endpoint D localRegion

set_option linter.style.longLine false in
private noncomputable def reducedUnivMatchingProviderData_of_tailPathConstructorData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (P :
      TexMatchingReducedUnivLocalPatchRegularQuadricTailPathConstructorData
        hL hr hstep endpoint D localRegion) :
    TexMatchingReducedUnivLocalPatchRegularQuadricFrecProviderData
      hL hr hstep endpoint D localRegion :=
  let analytic :
      TexMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData
        (r := r) (Params.tail θ) (Params.tail θ') Set.univ Set.univ :=
    texMatchingRegularQuadricLowerDepthTailPathFrecAnalyticData_of_univData
      (r := r) P.lowerDepthAnalytic
  { selectedEffectiveTail :=
      texMatchingLocalPatchRegularQuadricSelectedEffectiveTailFrecAnalyticData_of_paths_univ_lowerDepthTailPath
        (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
        analytic
    closedRecursionLimits :=
      texMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation_of_tailPath
        (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
        P.unprimedTailPath P.primedTailPath }

/-- Reduced matching surface for recursive path classes known to be swept realized-tail
sets.

The active matching frontier carries only selected dial membership and canonical
closed-recursion limits.  Selected effective-tail convergence is compiled internally
from those closed-recursion limits, without any universal lower-depth tail-path
convergence field. -/
structure TexMatchingReducedRealizedTailLocalPatchRegularQuadricFrecProviderData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (θfull : Params (L + 2) d)
    (FullPaths : Set (ProbePath d))
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths) : Type where
  matching : FirstLayerMatchedData θ θ'

set_option linter.style.longLine false in
private def closedRecursionLimitObligation_of_reducedMatchingProviderData
    {L d r : Nat} (hL : 0 < L) (hr : 2 <= r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (localRegion : TexRegionConstructionDataOfIDLDataObligation hL D)
    (P :
      TexMatchingReducedLocalPatchRegularQuadricFrecProviderData
        hL hr hstep endpoint D localRegion) :
    TexMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricClosedRecursionLimitObligation_of_frecProviderData
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion
    (reducedMatchingProviderData_to_frecProviderData
      hL hr hstep endpoint D localRegion P)

/-- Reduced recursive analytic data for swept realized-tail IDL path classes.

This is the package consumed after the first sweep handoff, where `D.Paths` is generally
  the realized-tail path class rather than `Set.univ`.  Its Step 1 surface exposes the
  regular-pole preimage family plus one shared projection/graph generic polynomial
  witness, while matching exposes selected product-neighborhood effective-tail
  analytic data plus closed-recursion limits;
chart local connectedness is built internally from the solved-coordinate chart.
Non-universal sweep carries the canonical near-anchor realization plus the realized-tail
source-path bundle needed to expose the conditional depth-one basis data.
Tail-anchor uniqueness is no longer part of the active
canonical-near sweep frontier and should not be targeted as globally derivable. -/
noncomputable def IDLRecursiveReducedAnalyticData :
    (L d r : Nat) -> (hd : 2 <= d) -> (hr : 2 <= r) ->
      {θ θ' : Params L d} -> (D : IDLData L d r θ θ') ->
        (θfull : Params (L + 1) d) -> (FullPaths : Set (ProbePath d)) ->
          D.Paths = realizedTailPathSet r θfull FullPaths -> Type
  | 0, _d, _r, _hd, _hr, _θ, _θ', _D, _θfull, _FullPaths, _hPaths => PUnit
  | 1, _d, _r, _hd, _hr, _θ, _θ', _D, _θfull, _FullPaths, _hPaths => PUnit
  | L + 2, d, r, hd, hr, θ, θ', D, θfull, FullPaths, hPaths =>
      let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
          (fun η => TexAnchorCertificate η) θ' :=
        D.texGenericStepClauses
      let endpoint :
          FirstLayerEndpointData
            (Params.headAttention θ) (Params.headAttention θ')
            (Params.headValue θ) :=
        D.firstLayerEndpoint hr
      let htail : 0 < L + 1 := Nat.succ_pos L
      let reducedLocalConnectedChart :
          TexRegionReducedLocalConnectedChartDataOfIDLData htail D :=
        texRegionReducedLocalConnectedChartDataOfIDLData_of_solvedCoordChart htail D
      let localRegion :
          TexRegionConstructionDataOfIDLDataObligation htail D :=
        texRegionConstructionDataOfIDLDataObligation_of_localConnectedChartProvider
          (L := L + 1) (d := d) (r := r)
          (θ := θ) (θ' := θ') htail hd hstep D
          reducedLocalConnectedChart
      @Sigma
        (TexMatchingReducedRealizedTailLocalPatchRegularQuadricFrecProviderData
          htail hr hstep endpoint D localRegion θfull FullPaths hPaths)
        (fun matchingFrec =>
              let matching : FirstLayerMatchedData θ θ' :=
                matchingFrec.matching
              @Sigma
                (PLift
                  (TexSweepLocalRealizationNearAnchorPoint D
                    (texSweepAnchorPointData_of_IDLData D)))
                (fun sweepNear =>
              @Sigma
                (PLift
                  (TexSweepRealizedTailDepthOneBasisSourcePathData D θfull FullPaths))
                (fun sweepSourcePathData =>
                  let sweepAnalytic :
                      TexSweepAnalyticData hstep matching D :=
                    texSweepAnalyticData_of_nearAnchorPoint_realizedTailDepthOneBasisSourcePathData
                      hstep matching D sweepNear.down sweepSourcePathData.down
                  IDLRecursiveReducedAnalyticData (L + 1) d r hd hr
                    (tail_IDLData_of_texGenericStep_of_IDLData
                      (L := L + 1) (d := d) (r := r)
                      (θ := θ) (θ' := θ') hd hr hstep matching D sweepAnalytic)
                    θ D.Paths
                    (texMatching_tail_IDLData_of_texGenericStep_of_IDLData_paths
                      (L := L + 1) (d := d) (r := r)
                      (θ := θ) (θ' := θ') hd hr hstep matching D sweepAnalytic))))

/-- Reduced recursive analytic data for an entry point whose current path class is
universal.

This is the global-probe-agreement front end: universal paths make the matching dial
membership mechanical, and chart local connectedness is now built internally from the
  solved-coordinate chart.  Its Step 1 surface asks for the regular-pole preimage
family plus one shared projection/graph generic polynomial witness, and its
matching provider asks for selected
product-neighborhood effective-tail analytic data plus closed-recursion limits.
Universal sweep asks for canonical near-anchor realization only; tail-anchor uniqueness
is not part of the active
canonical-near sweep frontier and should not be targeted as globally derivable.
The recursive tail then uses `IDLRecursiveReducedAnalyticData`, because sweep changes
the path class to the realized tail paths. -/
noncomputable def IDLRecursiveReducedAnalyticDataOfUnivPaths :
    (L d r : Nat) -> (hd : 2 <= d) -> (hr : 2 <= r) ->
      {θ θ' : Params L d} -> (D : IDLData L d r θ θ') ->
        D.Paths = Set.univ -> Type
  | 0, _d, _r, _hd, _hr, _θ, _θ', _D, _hPaths => PUnit
  | 1, _d, _r, _hd, _hr, _θ, _θ', _D, _hPaths => PUnit
  | L + 2, d, r, hd, hr, θ, θ', D, hPaths =>
      let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
          (fun η => TexAnchorCertificate η) θ' :=
        D.texGenericStepClauses
      let endpoint :
          FirstLayerEndpointData
            (Params.headAttention θ) (Params.headAttention θ')
            (Params.headValue θ) :=
        D.firstLayerEndpoint hr
      let htail : 0 < L + 1 := Nat.succ_pos L
      let reducedLocalConnectedChart :
          TexRegionReducedLocalConnectedChartDataOfIDLData htail D :=
        texRegionReducedLocalConnectedChartDataOfIDLData_of_solvedCoordChart htail D
      let localRegion :
          TexRegionConstructionDataOfIDLDataObligation htail D :=
        texRegionConstructionDataOfIDLDataObligation_of_localConnectedChartProvider
          (L := L + 1) (d := d) (r := r)
          (θ := θ) (θ' := θ') htail hd hstep D
          reducedLocalConnectedChart
      @Sigma
        (TexMatchingReducedUnivLocalPatchRegularQuadricFrecProviderData
          htail hr hstep endpoint D localRegion)
        (fun matchingFrec =>
              let matchingAnalytic :
                  TexFirstLayerMatchingAnalyticData hr hstep endpoint D :=
                reducedUnivMatchingProviderData_to_firstLayerAnalytic
                  htail hr hstep endpoint D hPaths localRegion matchingFrec
              let matching : FirstLayerMatchedData θ θ' :=
                firstLayerMatched_of_texGenericStep_of_IDLData
                  (L := L + 1) (d := d) (r := r)
                  (θ := θ) (θ' := θ') hr hstep endpoint D matchingAnalytic
              @Sigma
                (PLift
                  (TexSweepLocalRealizationNearAnchorPoint D
                    (texSweepAnchorPointData_of_IDLData D)))
                (fun sweepNear =>
                let sweepAnalytic :
                    TexSweepAnalyticData hstep matching D :=
                  texSweepAnalyticData_of_paths_univ_nearAnchorPoint
                    hstep matching D hPaths sweepNear.down
                IDLRecursiveReducedAnalyticData (L + 1) d r hd hr
                  (tail_IDLData_of_texGenericStep_of_IDLData
                    (L := L + 1) (d := d) (r := r)
                    (θ := θ) (θ' := θ') hd hr hstep matching D sweepAnalytic)
                  θ D.Paths
                    (texMatching_tail_IDLData_of_texGenericStep_of_IDLData_paths
                      (L := L + 1) (d := d) (r := r)
                      (θ := θ) (θ' := θ') hd hr hstep matching D sweepAnalytic)))

/-! ## Recursive local-provider assembly -/

/-- The reduced source-path part of the realized-tail sweep frontier.

The recursive assembler supplies the determinant from the previous full node's
matching data; this wrapper only records the depth-one source paths that cannot be
generated from matching alone. -/
structure IDLReducedRealizedTailSourcePathMembershipData
    {L Lfull d : Nat} {θ : Params (L + 1) d}
    (θfull : Params (Lfull + 1) d)
    (FullPaths : Set (ProbePath d)) : Type where
  source_mem :
    L = 1 ->
      ∀ j : Fin d,
        constantProbePath
            ((0 : Fin d -> ℝ),
              ((skipB (Params.headValue θfull))⁻¹).mulVec
                (((skipB (Params.headValue θ))⁻¹).mulVec
                  (Pi.single j (1 : ℝ)))) ∈
          FullPaths

/-- Rebuild the full sweep source bundle from reduced source membership and the
previous full node's matching data. -/
def texSweepRealizedTailDepthOneBasisSourcePathData_of_matching_sourcePathMembership
    {L Lfull d r : Nat} {θ θ' : Params (L + 1) d}
    {θfull θfull' : Params (Lfull + 1) d}
    {FullPaths : Set (ProbePath d)}
    {D : IDLData (L + 1) d r θ θ'}
    (hstep_full :
      TexGenericStepClauses Lfull d (TexGeneric Lfull d)
        (fun η => TexAnchorCertificate η) θfull')
    (matching_full : FirstLayerMatchedData θfull θfull')
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (source_mem :
      IDLReducedRealizedTailSourcePathMembershipData
        (θ := θ) θfull FullPaths) :
    TexSweepRealizedTailDepthOneBasisSourcePathData D θfull FullPaths :=
  texSweepRealizedTailDepthOneBasisSourcePathData_of_realizedTailPathSet
    hPaths
    (headValueSkip_det_ne_zero_of_matching hstep_full matching_full)
    source_mem.source_mem

/-- Local positive-depth data for a swept realized-tail recursive node, excluding the
recursive tail package.

Supplying this at each positive realized-tail node is enough to build
`IDLRecursiveReducedAnalyticData` recursively; the tail itself is generated by
descent.  The sweep source field is only the source-path membership part; the
determinant is generated during descent from the previous full node's matching data. -/
structure IDLReducedRealizedTailLocalConstructorData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 2) d}
    (D : IDLData (L + 2) d r θ θ')
    (θfull : Params (L + 3) d) (FullPaths : Set (ProbePath d))
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths) : Type where
  matchingFrec :
    let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
        (fun η => TexAnchorCertificate η) θ' :=
      D.texGenericStepClauses
    let endpoint :
        FirstLayerEndpointData
          (Params.headAttention θ) (Params.headAttention θ')
          (Params.headValue θ) :=
      D.firstLayerEndpoint hr
    let htail : 0 < L + 1 := Nat.succ_pos L
    let reducedLocalConnectedChart :
        TexRegionReducedLocalConnectedChartDataOfIDLData htail D :=
      texRegionReducedLocalConnectedChartDataOfIDLData_of_solvedCoordChart htail D
    let localRegion :
        TexRegionConstructionDataOfIDLDataObligation htail D :=
      texRegionConstructionDataOfIDLDataObligation_of_localConnectedChartProvider
        (L := L + 1) (d := d) (r := r)
        (θ := θ) (θ' := θ') htail hd hstep D
        reducedLocalConnectedChart
    TexMatchingReducedRealizedTailLocalPatchRegularQuadricFrecProviderData
      htail hr hstep endpoint D localRegion θfull FullPaths hPaths
  canonicalIFT :
    TexSweepCanonicalIFTData D
  sweepSourcePathMem :
    IDLReducedRealizedTailSourcePathMembershipData
      (θ := θ) θfull FullPaths

/-- A provider for the local realized-tail fields at every positive recursive depth. -/
abbrev IDLReducedRealizedTailLocalConstructorProvider
    (d r : Nat) (hd : 2 <= d) (hr : 2 <= r) : Type :=
  ∀ {L : Nat} {θ θ' : Params (L + 2) d},
    (D : IDLData (L + 2) d r θ θ') ->
      (θfull : Params (L + 3) d) -> (FullPaths : Set (ProbePath d)) ->
        (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths) ->
          IDLReducedRealizedTailLocalConstructorData hd hr D θfull FullPaths hPaths

/-- Output of a threaded realized-tail local provider. -/
structure IDLReducedRealizedTailThreadedLocalConstructorOutput
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 2) d}
    (D : IDLData (L + 2) d r θ θ')
    (θfull : Params (L + 3) d) (FullPaths : Set (ProbePath d))
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths) : Type where
  matchingFrec :
    let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
        (fun η => TexAnchorCertificate η) θ' :=
      D.texGenericStepClauses
    let endpoint :
        FirstLayerEndpointData
          (Params.headAttention θ) (Params.headAttention θ')
          (Params.headValue θ) :=
      D.firstLayerEndpoint hr
    let htail : 0 < L + 1 := Nat.succ_pos L
    let reducedLocalConnectedChart :
        TexRegionReducedLocalConnectedChartDataOfIDLData htail D :=
      texRegionReducedLocalConnectedChartDataOfIDLData_of_solvedCoordChart htail D
    let localRegion :
        TexRegionConstructionDataOfIDLDataObligation htail D :=
      texRegionConstructionDataOfIDLDataObligation_of_localConnectedChartProvider
        (L := L + 1) (d := d) (r := r)
        (θ := θ) (θ' := θ') htail hd hstep D
        reducedLocalConnectedChart
    TexMatchingReducedRealizedTailLocalPatchRegularQuadricFrecProviderData
      htail hr hstep endpoint D localRegion θfull FullPaths hPaths
  canonicalIFT :
    TexSweepCanonicalIFTData D
  U : Set (ProbePoint d)
  U_open : IsOpen U
  anchor_mem : (texSweepAnchorPointData_of_IDLData D).point ∈ U
  Tcurr : ℝ
  currentUniform : UniformTailRealize r θ D.Paths U Tcurr

/-- Universal top-node sweep package.

For a matched first layer whose current path class is universal, the pointwise sweep
realization around the canonical full anchor gives an open-realization package and the
path-level uniform invariant on the same open set. -/
noncomputable def texSweepOpenRealizationUniformData_of_IDLData_matching_univ
    {L d r : Nat} {θ θ' : Params (L + 2) d}
    (D : IDLData (L + 2) d r θ θ')
    (matching : FirstLayerMatchedData θ θ')
    (hPaths : D.Paths = Set.univ) :
    Σ R : TexSweepOpenRealizationData D,
      { T : ℝ //
        (texSweepAnchorPointData_of_IDLData D).point ∈ R.U ∧
          UniformTailRealize r θ D.Paths R.U T } := by
  classical
  set p : AnchorProbe d := (idlChosenFullAnchor D).1 with hp
  set W : AnchorUnwindingData θ' p := (idlChosenFullAnchor D).2 with hW
  have htIoo : W.t 0 ∈ Set.Ioo (0 : ℝ) 1 := W.t_mem_Ioo 0 (by omega)
  have hq' : matrixBilin (Params.headAttention θ') p.1 p.2 = 0 :=
    texSweepFirstLayerQuadric_of_anchorUnwindingData W (by omega)
  have hvartheta' :
      texSweepVartheta0 (Params.headValue θ') (Params.headAttention θ') p (W.t 0) ≠ 0 := by
    have hinv := W.inverse_scalar_ne_zero 0 (by omega)
    simpa [texSweepVartheta0_eq_anchorInverseScalarAt] using hinv
  have hdetStep' :
      (anchorStepMatrix
        (fun _ => (Params.headValue θ', Params.headAttention θ')) 0 (W.t 0)).det ≠ 0 := by
    have hdet := W.det_step_ne_zero 0 (by omega)
    simpa [anchorStepMatrix, Params.headValue, Params.headAttention, Params.headLayer,
      anchorParamStream] using hdet
  have hq : matrixBilin (Params.headAttention θ) p.1 p.2 = 0 := by
    simpa [matching.headAttention_eq] using hq'
  have hvartheta :
      texSweepVartheta0 (Params.headValue θ) (Params.headAttention θ) p (W.t 0) ≠ 0 := by
    simpa [matching.headValue_eq, matching.headAttention_eq] using hvartheta'
  have hMt : (Msolve (Params.headValue θ) (W.t 0)).det ≠ 0 := by
    change (anchorStepMatrix
      (fun _ => (Params.headValue θ, Params.headAttention θ)) 0 (W.t 0)).det ≠ 0
    simpa [matching.headValue_eq, matching.headAttention_eq] using hdetStep'
  have hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
      (fun η => TexAnchorCertificate η) θ' := D.primed_generic
  have hB : (skipB (Params.headValue θ)).det ≠ 0 :=
    headValueSkip_det_ne_zero_of_matching hstep matching
  have hcenter_eq : firstLayerDialPoint (Params.headValue θ) (W.t 0) p.1 p.2 =
      (texSweepAnchorPointData_of_IDLData D).point := by
    have h1 : (texSweepAnchorPointData_of_IDLData D).point =
        (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point := rfl
    rw [h1]
    calc
      firstLayerDialPoint (Params.headValue θ) (W.t 0) p.1 p.2 =
          anchorStep (fun _ => (Params.headValue θ, Params.headAttention θ)) 0
            (W.t 0) p :=
        firstLayerDialPoint_eq_anchorStep
          (Params.headValue θ) (Params.headAttention θ) (W.t 0) p
      _ = (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point := by
        simp [texSweepAnchorPointData_of_fullUnwoundAnchor, anchorStep,
          anchorStepMatrix, Params.headValue, Params.headLayer,
          anchorParamStream, matching.headValue_eq]
  have hex :
      ∃ U : Set (ProbePoint d), IsOpen U ∧
        firstLayerDialPoint (Params.headValue θ) (W.t 0) p.1 p.2 ∈ U ∧
          ∃ T : ℝ, 0 ≤ T ∧
            ∀ η : ProbePoint d, η ∈ U -> ∀ τ : ℝ, T < τ ->
              ∃ w v : Fin d -> ℝ,
                firstLayerEffectivePoint r (Params.headValue θ) (Params.headAttention θ)
                  w v τ = η :=
    sweep_pointwise_realization_open r (Params.headValue θ) (Params.headAttention θ)
      p.1 p.2 (W.t 0) htIoo.1 htIoo.2 hB hMt hq hvartheta
  let U : Set (ProbePoint d) := Classical.choose hex
  have hUspec :
      IsOpen U ∧ firstLayerDialPoint (Params.headValue θ) (W.t 0) p.1 p.2 ∈ U ∧
        ∃ T : ℝ, 0 ≤ T ∧
          ∀ η : ProbePoint d, η ∈ U -> ∀ τ : ℝ, T < τ ->
            ∃ w v : Fin d -> ℝ,
              firstLayerEffectivePoint r (Params.headValue θ) (Params.headAttention θ)
                w v τ = η :=
    Classical.choose_spec hex
  have hUopen : IsOpen U := hUspec.1
  have hcenter : firstLayerDialPoint (Params.headValue θ) (W.t 0) p.1 p.2 ∈ U :=
    hUspec.2.1
  let T : ℝ := Classical.choose hUspec.2.2
  have hTspec :
      0 ≤ T ∧
        ∀ η : ProbePoint d, η ∈ U -> ∀ τ : ℝ, T < τ ->
          ∃ w v : Fin d -> ℝ,
            firstLayerEffectivePoint r (Params.headValue θ) (Params.headAttention θ)
              w v τ = η :=
    Classical.choose_spec hUspec.2.2
  have hreal :
      ∀ η : ProbePoint d, η ∈ U -> ∀ τ : ℝ, T < τ ->
        ∃ w v : Fin d -> ℝ,
          firstLayerEffectivePoint r (Params.headValue θ) (Params.headAttention θ)
            w v τ = η :=
    hTspec.2
  have hanchor : (texSweepAnchorPointData_of_IDLData D).point ∈ U := hcenter_eq ▸ hcenter
  have huniformUniv : UniformTailRealize r θ Set.univ U T :=
    uniformTailRealize_univ_of_pointwise r θ U T hreal
  have huniformD : UniformTailRealize r θ D.Paths U T := by
    rw [hPaths]
    exact huniformUniv
  let R : TexSweepOpenRealizationData D :=
    { U := U
      U_open := hUopen
      U_nonempty := ⟨(texSweepAnchorPointData_of_IDLData D).point, hanchor⟩
      constant_tail_realized := by
        intro η hη
        rcases huniformD (constantProbePath η)
            (by
              intro τ _hτ
              simpa [constantProbePath_apply] using hη) with
          ⟨source, hsource, T', _hT', heff⟩
        refine
          texSweepPointwiseRealizable_of_source_eventually_effective_eq
            D η source hsource (max T' 0) (le_max_right _ _) ?_
        intro τ hτ
        have hT'τ : T' < τ := lt_of_le_of_lt (le_max_left _ _) hτ
        simpa [constantProbePath_apply] using heff τ hT'τ
      tail_anchor_nonempty := by
        exact Or.inr
          ⟨(texSweepAnchorPointData_of_IDLData D).point,
            ⟨hanchor, (texSweepAnchorPointData_of_IDLData D).point_mem_tail_anchor.2⟩⟩
      }
  exact ⟨R, ⟨T, hanchor, huniformD⟩⟩

/-- A threaded provider for realized-tail local fields.

Compared with `IDLReducedRealizedTailLocalConstructorProvider`, this surface receives the
previous recursive sweep realization invariant.  It returns the matching, canonical-IFT,
and reduced depth-one basis fields for the current node together with the current node's
uniform realization invariant on some open neighborhood of the current canonical sweep
anchor. -/
abbrev IDLReducedRealizedTailThreadedLocalConstructorProvider
    (d r : Nat) (hd : 2 <= d) (hr : 2 <= r) : Type :=
  ∀ {L : Nat} {θ θ' : Params (L + 2) d},
    (D : IDLData (L + 2) d r θ θ') ->
      {θfull θfull' : Params (L + 3) d} ->
        (Dfull : IDLData (L + 3) d r θfull θfull') ->
          (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths) ->
            (Uprev : Set (ProbePoint d)) -> IsOpen Uprev ->
              (idlChosenFullAnchor D).1 ∈ Uprev ->
                (Tprev : ℝ) ->
                  UniformTailRealize r θfull Dfull.Paths Uprev Tprev ->
                    D.O ⊆ Uprev ->
                    IDLReducedRealizedTailThreadedLocalConstructorOutput
                      hd hr D θfull Dfull.Paths hPaths

/-- Threaded reduced recursive data indexed by the actual open-realization tail node.

This mirrors `IDLRecursiveReducedAnalyticData`, but the recursive tail is built from an
explicit `TexSweepOpenRealizationData`.  The threaded assembler can therefore recurse on
the same open set that carries its `UniformTailRealize` invariant, without coercing that
invariant to the canonical realized-tail region used by the older unthreaded package. -/
noncomputable def IDLThreadedRecursiveReducedAnalyticData :
    (L d r : Nat) -> (hd : 2 <= d) -> (hr : 2 <= r) ->
      {θ θ' : Params L d} -> (D : IDLData L d r θ θ') ->
        (θfull : Params (L + 1) d) -> (FullPaths : Set (ProbePath d)) ->
          D.Paths = realizedTailPathSet r θfull FullPaths -> Type
  | 0, _d, _r, _hd, _hr, _θ, _θ', _D, _θfull, _FullPaths, _hPaths => PUnit
  | 1, _d, _r, _hd, _hr, _θ, _θ', _D, _θfull, _FullPaths, _hPaths => PUnit
  | L + 2, d, r, hd, hr, θ, θ', D, θfull, FullPaths, hPaths =>
      let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
          (fun η => TexAnchorCertificate η) θ' :=
        D.texGenericStepClauses
      let endpoint :
          FirstLayerEndpointData
            (Params.headAttention θ) (Params.headAttention θ')
            (Params.headValue θ) :=
        D.firstLayerEndpoint hr
      let htail : 0 < L + 1 := Nat.succ_pos L
      let reducedLocalConnectedChart :
          TexRegionReducedLocalConnectedChartDataOfIDLData htail D :=
        texRegionReducedLocalConnectedChartDataOfIDLData_of_solvedCoordChart htail D
      let localRegion :
          TexRegionConstructionDataOfIDLDataObligation htail D :=
        texRegionConstructionDataOfIDLDataObligation_of_localConnectedChartProvider
          (L := L + 1) (d := d) (r := r)
          (θ := θ) (θ' := θ') htail hd hstep D
          reducedLocalConnectedChart
      @Sigma
        (TexMatchingReducedRealizedTailLocalPatchRegularQuadricFrecProviderData
          htail hr hstep endpoint D localRegion θfull FullPaths hPaths)
        (fun matchingFrec =>
              let matching : FirstLayerMatchedData θ θ' :=
                matchingFrec.matching
              @Sigma
                (PLift
                  (TexSweepLocalRealizationNearAnchorPoint D
                    (texSweepAnchorPointData_of_IDLData D)))
                (fun sweepNear =>
              @Sigma
                (TexSweepOpenRealizationData D)
                (fun openRealization =>
                  IDLThreadedRecursiveReducedAnalyticData (L + 1) d r hd hr
                    (tail_IDLData_of_texGenericStep_of_openRealizationData
                      (L := L + 1) (d := d) (r := r)
                      (θ := θ) (θ' := θ') hd hr hstep matching D openRealization)
                    θ D.Paths
                    (by
                      simp [tail_IDLData_of_texGenericStep_of_openRealizationData,
                        tail_IDLData_of_texGenericStep,
                        sweepData_of_texGenericStep]))))

/-- Provider for the exact reduced realized-tail matching record at each threaded
recursive node. -/
abbrev IDLReducedRealizedTailMatchingFrecProvider
    (d r : Nat) (hd : 2 <= d) (hr : 2 <= r) : Type :=
  ∀ {L : Nat} {θ θ' : Params (L + 2) d},
    (D : IDLData (L + 2) d r θ θ') ->
      {θfull θfull' : Params (L + 3) d} ->
        (Dfull : IDLData (L + 3) d r θfull θfull') ->
          (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths) ->
            (Uprev : Set (ProbePoint d)) -> IsOpen Uprev -> (Tprev : ℝ) ->
              UniformTailRealize r θfull Dfull.Paths Uprev Tprev -> D.O ⊆ Uprev ->
            let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
                (fun η => TexAnchorCertificate η) θ' :=
              D.texGenericStepClauses
            let endpoint : FirstLayerEndpointData
                (Params.headAttention θ) (Params.headAttention θ')
                (Params.headValue θ) :=
              D.firstLayerEndpoint hr
            let htail : 0 < L + 1 := Nat.succ_pos L
            let reducedLocalConnectedChart :
                TexRegionReducedLocalConnectedChartDataOfIDLData htail D :=
              texRegionReducedLocalConnectedChartDataOfIDLData_of_solvedCoordChart
                htail D
            let localRegion : TexRegionConstructionDataOfIDLDataObligation htail D :=
              texRegionConstructionDataOfIDLDataObligation_of_localConnectedChartProvider
                (L := L + 1) (d := d) (r := r)
                (θ := θ) (θ' := θ') htail hd hstep D reducedLocalConnectedChart
            TexMatchingReducedRealizedTailLocalPatchRegularQuadricFrecProviderData
              htail hr hstep endpoint D localRegion θfull Dfull.Paths hPaths

set_option linter.style.longLine false in
/-- Genuine realized-tail matching leaf provider.  At every recursive (depth ≥ 3) node
the single matching field is produced from the parent's path-level uniform-tail
realization invariant via the parking trick
(`realizedTailMatchedData_of_uniformTailRealize`), with `D.O ⊆ Uprev` discharged by
`Set.Subset.refl` at each recursion site (every node has `Uprev = D.O`). -/
noncomputable def idlReducedRealizedTailMatchingFrecProvider_genuine
    {d r : Nat} (hd : 2 <= d) (hr : 2 <= r) :
    IDLReducedRealizedTailMatchingFrecProvider d r hd hr :=
  fun {L} {θ} {θ'} D {θfull} {_θfull'} Dfull hPaths Uprev hUprev Tprev hprev hDO => by
    let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
        (fun η => TexAnchorCertificate η) θ' :=
      D.texGenericStepClauses
    let endpoint : FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ) :=
      D.firstLayerEndpoint hr
    let htail : 0 < L + 1 := Nat.succ_pos L
    let reducedLocalConnectedChart :
        TexRegionReducedLocalConnectedChartDataOfIDLData htail D :=
      texRegionReducedLocalConnectedChartDataOfIDLData_of_solvedCoordChart htail D
    let localRegion : TexRegionConstructionDataOfIDLDataObligation htail D :=
      texRegionConstructionDataOfIDLDataObligation_of_localConnectedChartProvider
        (L := L + 1) (d := d) (r := r)
        (θ := θ) (θ' := θ') htail hd hstep D reducedLocalConnectedChart
    let region :=
      texRegionConstructionData_of_IDLData_of_localPatch
        (L := L + 1) (d := d) (r := r) htail hr hstep endpoint D localRegion
    let signRegion :=
      texMatchingSignRegionData_of_region
        (L := L + 1) (d := d) (r := r) hr hstep endpoint D region
    exact
      { matching :=
          realizedTailMatchedData_of_uniformTailRealize
            hd hr hstep endpoint D signRegion hPaths Uprev hUprev Tprev hprev hDO }

set_option linter.style.longLine false in
noncomputable def idlReducedRealizedTailThreadedLocalConstructorProvider_of_matchingFrecProvider
    {d r : Nat} {hd : 2 <= d} {hr : 2 <= r}
    (matchingProvider : IDLReducedRealizedTailMatchingFrecProvider d r hd hr) :
    IDLReducedRealizedTailThreadedLocalConstructorProvider d r hd hr :=
  fun {L} {θ} {θ'} D {θfull} {_θfull'} Dfull hPaths
      Uprev hUprev hanchor Tprev hprev hDO => by
    let matchingFrec := matchingProvider D Dfull hPaths Uprev hUprev Tprev hprev hDO
    let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
        (fun η => TexAnchorCertificate η) θ' :=
      D.texGenericStepClauses
    let endpoint :
        FirstLayerEndpointData
          (Params.headAttention θ) (Params.headAttention θ')
          (Params.headValue θ) :=
      D.firstLayerEndpoint hr
    let htail : 0 < L + 1 := Nat.succ_pos L
    let reducedLocalConnectedChart :
        TexRegionReducedLocalConnectedChartDataOfIDLData htail D :=
      texRegionReducedLocalConnectedChartDataOfIDLData_of_solvedCoordChart htail D
    let localRegion :
        TexRegionConstructionDataOfIDLDataObligation htail D :=
      texRegionConstructionDataOfIDLDataObligation_of_localConnectedChartProvider
        (L := L + 1) (d := d) (r := r)
        (θ := θ) (θ' := θ') htail hd hstep D
        reducedLocalConnectedChart
    let matching : FirstLayerMatchedData θ θ' :=
      matchingFrec.matching
    let canonicalIFT : TexSweepCanonicalIFTData D :=
      texSweepCanonicalIFTData_of_IDLData_matching_realizedTail
        hr D matching hPaths Uprev hUprev hanchor Tprev hprev
    let currentUniform :
        ∃ U : Set (ProbePoint d), IsOpen U ∧
          (texSweepAnchorPointData_of_IDLData D).point ∈ U ∧
          ∃ Tcurr : ℝ, UniformTailRealize r θ D.Paths U Tcurr :=
      uniformTailRealize_currentNode_of_IDLData_matching hr D matching hPaths
        Uprev hUprev hanchor Tprev hprev
    let U := Classical.choose currentUniform
    let hU_spec := Classical.choose_spec currentUniform
    let hUopen := hU_spec.1
    let hanchorU := hU_spec.2.1
    let hT := hU_spec.2.2
    let Tcurr := Classical.choose hT
    let hcurr := Classical.choose_spec hT
    exact
      { matchingFrec := matchingFrec
        canonicalIFT := canonicalIFT
        U := U
        U_open := hUopen
        anchor_mem := hanchorU
        Tcurr := Tcurr
        currentUniform := hcurr }

/-- Assemble the swept-tail recursive reduced package from local data at each depth,
carrying the previous full node's matching context.

The positive branch consumes exactly the local Step 1, matching, and sweep fields for
the current realized-tail node.  The full realized-tail source bundle is rebuilt from
the reduced source membership plus the previous full node's matching/generic data.
Its `tailReduced` component is generated by the recursive call. -/
noncomputable def idlRecursiveReducedAnalyticData_of_realizedTailLocalProvider
    {d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    (localProvider : IDLReducedRealizedTailLocalConstructorProvider d r hd hr) :
    (L : Nat) -> {θ θ' : Params L d} -> (D : IDLData L d r θ θ') ->
      {θfull θfull' : Params (L + 1) d} ->
        (Dfull : IDLData (L + 1) d r θfull θfull') ->
          (hstep_full :
            TexGenericStepClauses L d (TexGeneric L d)
              (fun η => TexAnchorCertificate η) θfull') ->
            (matching_full : FirstLayerMatchedData θfull θfull') ->
              (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths) ->
                IDLRecursiveReducedAnalyticData L d r hd hr
                  D θfull Dfull.Paths hPaths
  | 0, _θ, _θ', _D, _θfull, _θfull', _Dfull, _hstep_full, _matching_full,
      _hPaths => PUnit.unit
  | 1, _θ, _θ', _D, _θfull, _θfull', _Dfull, _hstep_full, _matching_full,
      _hPaths => PUnit.unit
  | L + 2, θ, θ', D, θfull, _θfull', Dfull, hstep_full, matching_full,
      hPaths => by
      let A :
          IDLReducedRealizedTailLocalConstructorData
            hd hr D θfull Dfull.Paths hPaths :=
        localProvider D θfull Dfull.Paths hPaths
      let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
          (fun η => TexAnchorCertificate η) θ' :=
        D.texGenericStepClauses
      let endpoint :
          FirstLayerEndpointData
            (Params.headAttention θ) (Params.headAttention θ')
            (Params.headValue θ) :=
        D.firstLayerEndpoint hr
      let htail : 0 < L + 1 := Nat.succ_pos L
      let reducedLocalConnectedChart :
          TexRegionReducedLocalConnectedChartDataOfIDLData htail D :=
        texRegionReducedLocalConnectedChartDataOfIDLData_of_solvedCoordChart htail D
      let localRegion :
          TexRegionConstructionDataOfIDLDataObligation htail D :=
        texRegionConstructionDataOfIDLDataObligation_of_localConnectedChartProvider
          (L := L + 1) (d := d) (r := r)
          (θ := θ) (θ' := θ') htail hd hstep D
          reducedLocalConnectedChart
      let matching : FirstLayerMatchedData θ θ' :=
        A.matchingFrec.matching
      let sweepNear :
          TexSweepLocalRealizationNearAnchorPoint D
            (texSweepAnchorPointData_of_IDLData D) :=
        texSweepLocalRealizationNearAnchorPoint_of_canonicalIFTData
          A.canonicalIFT
      let sweepSourcePathData :
          TexSweepRealizedTailDepthOneBasisSourcePathData D θfull Dfull.Paths :=
        texSweepRealizedTailDepthOneBasisSourcePathData_of_matching_sourcePathMembership
          hstep_full matching_full hPaths A.sweepSourcePathMem
      let sweepAnalytic :
          TexSweepAnalyticData hstep matching D :=
        texSweepAnalyticData_of_nearAnchorPoint_realizedTailDepthOneBasisSourcePathData
          hstep matching D sweepNear sweepSourcePathData
      let tailData :
          IDLData (L + 1) d r (Params.tail θ) (Params.tail θ') :=
        tail_IDLData_of_texGenericStep_of_IDLData
          (L := L + 1) (d := d) (r := r)
          (θ := θ) (θ' := θ') hd hr hstep matching D sweepAnalytic
      let tailPaths :
          tailData.Paths = realizedTailPathSet r θ D.Paths :=
        texMatching_tail_IDLData_of_texGenericStep_of_IDLData_paths
          (L := L + 1) (d := d) (r := r)
          (θ := θ) (θ' := θ') hd hr hstep matching D sweepAnalytic
      exact
        ⟨A.matchingFrec, PLift.up sweepNear, PLift.up sweepSourcePathData,
          idlRecursiveReducedAnalyticData_of_realizedTailLocalProvider
            hd hr localProvider (L + 1) tailData
            (Dfull := D) hstep matching tailPaths⟩

/-- Threaded realized-tail recursive assembler.

This is structurally parallel to
`idlRecursiveReducedAnalyticData_of_realizedTailLocalProvider`, but the local constructor
receives the previous `UniformTailRealize` invariant and returns the current reduced
depth-one basis input.  The current node's returned open set is threaded directly into
the tail datum, so recursive descent uses the same region carrying the current uniform
invariant. -/
noncomputable def idlRecursiveReducedAnalyticData_of_threadedRealizedTailLocalProvider
    {d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    (localProvider :
      IDLReducedRealizedTailThreadedLocalConstructorProvider d r hd hr) :
    (L : Nat) -> {θ θ' : Params (L + 2) d} ->
      (D : IDLData (L + 2) d r θ θ') ->
      {θfull θfull' : Params (L + 3) d} ->
        (Dfull : IDLData (L + 3) d r θfull θfull') ->
          (hstep_full :
            TexGenericStepClauses (L + 2) d (TexGeneric (L + 2) d)
              (fun η => TexAnchorCertificate η) θfull') ->
            (matching_full : FirstLayerMatchedData θfull θfull') ->
              (hPaths : D.Paths = realizedTailPathSet r θfull Dfull.Paths) ->
                (Uprev : Set (ProbePoint d)) -> IsOpen Uprev ->
                  (idlChosenFullAnchor D).1 ∈ Uprev ->
                    (Tprev : ℝ) ->
                      UniformTailRealize r θfull Dfull.Paths Uprev Tprev ->
                        D.O ⊆ Uprev ->
                        IDLThreadedRecursiveReducedAnalyticData (L + 2) d r hd hr
                          D θfull Dfull.Paths hPaths
  | L, θ, θ', D, θfull, θfull', Dfull, hstep_full, matching_full,
      hPaths, Uprev, hUprev_open, hanchor_mem, Tprev, hprev, hDO => by
      let P :
          IDLReducedRealizedTailThreadedLocalConstructorOutput
            hd hr D θfull Dfull.Paths hPaths :=
        localProvider D Dfull hPaths Uprev hUprev_open hanchor_mem Tprev hprev hDO
      let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
          (fun η => TexAnchorCertificate η) θ' :=
        D.texGenericStepClauses
      let endpoint :
          FirstLayerEndpointData
            (Params.headAttention θ) (Params.headAttention θ')
            (Params.headValue θ) :=
        D.firstLayerEndpoint hr
      let htail : 0 < L + 1 := Nat.succ_pos L
      let reducedLocalConnectedChart :
          TexRegionReducedLocalConnectedChartDataOfIDLData htail D :=
        texRegionReducedLocalConnectedChartDataOfIDLData_of_solvedCoordChart htail D
      let localRegion :
          TexRegionConstructionDataOfIDLDataObligation htail D :=
        texRegionConstructionDataOfIDLDataObligation_of_localConnectedChartProvider
          (L := L + 1) (d := d) (r := r)
          (θ := θ) (θ' := θ') htail hd hstep D
          reducedLocalConnectedChart
      let matching : FirstLayerMatchedData θ θ' :=
        P.matchingFrec.matching
      let sweepNear :
          TexSweepLocalRealizationNearAnchorPoint D
            (texSweepAnchorPointData_of_IDLData D) :=
        texSweepLocalRealizationNearAnchorPoint_of_canonicalIFTData
          P.canonicalIFT
      let openRealization : TexSweepOpenRealizationData D :=
        { U := P.U
          U_open := P.U_open
          U_nonempty := ⟨(texSweepAnchorPointData_of_IDLData D).point, P.anchor_mem⟩
          constant_tail_realized := by
            intro η hη
            rcases P.currentUniform (constantProbePath η)
                (by
                  intro τ _hτ
                  simpa [constantProbePath_apply] using hη) with
              ⟨source, hsource, T', _hT', heff⟩
            refine
              texSweepPointwiseRealizable_of_source_eventually_effective_eq
                D η source hsource (max T' 0) (le_max_right _ _) ?_
            intro τ hτ
            have hT'τ : T' < τ := lt_of_le_of_lt (le_max_left _ _) hτ
            simpa [constantProbePath_apply] using heff τ hT'τ
          tail_anchor_nonempty := by
            exact Or.inr
              ⟨(texSweepAnchorPointData_of_IDLData D).point,
                ⟨P.anchor_mem,
                  (texSweepAnchorPointData_of_IDLData D).point_mem_tail_anchor.2⟩⟩ }
      let sweepAnalytic :
          TexSweepAnalyticData hstep matching D :=
        texSweepAnalyticData_of_openRealizationData hstep matching openRealization
      let tailData :
          IDLData (L + 1) d r (Params.tail θ) (Params.tail θ') :=
        tail_IDLData_of_texGenericStep_of_openRealizationData
          (L := L + 1) (d := d) (r := r)
          (θ := θ) (θ' := θ') hd hr hstep matching D openRealization
      let tailPaths :
          tailData.Paths = realizedTailPathSet r θ D.Paths :=
        by
          simp [tailData, tail_IDLData_of_texGenericStep_of_openRealizationData,
            tail_IDLData_of_texGenericStep, sweepData_of_texGenericStep]
      cases L with
      | zero =>
          exact
            ⟨P.matchingFrec, PLift.up sweepNear, openRealization,
              PUnit.unit⟩
      | succ L =>
          have htailAnchorNonempty :
              (tailData.O ∩ unwoundAnchorSet (Params.tail θ')).Nonempty :=
            tailData.anchor_nonempty.resolve_left (by omega)
          let htailAnchorMem : (idlChosenFullAnchor tailData).1 ∈ tailData.O :=
            idlChosenFullAnchor_fst_mem_O tailData htailAnchorNonempty
          exact
            ⟨P.matchingFrec, PLift.up sweepNear, openRealization,
              idlRecursiveReducedAnalyticData_of_threadedRealizedTailLocalProvider
                hd hr localProvider
                L tailData
                (Dfull := D) hstep matching tailPaths
                tailData.O tailData.O_open htailAnchorMem
                P.Tcurr
                (by
                  simpa [tailData, openRealization,
                    tail_IDLData_of_texGenericStep_of_openRealizationData,
                    tail_IDLData_of_texGenericStep, sweepData_of_texGenericStep]
                    using P.currentUniform)
                (Set.Subset.refl _)⟩

/-- Identifiability directly from the threaded reduced recursive provider package. -/
theorem IDL_of_threadedReduced
    {L d r : Nat} (hL : 1 <= L) (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params L d} :
    (D : IDLData L d r θ θ') ->
      (θfull : Params (L + 1) d) ->
        (FullPaths : Set (ProbePath d)) ->
          (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths) ->
            IDLThreadedRecursiveReducedAnalyticData L d r hd hr D θfull FullPaths hPaths ->
              θ = θ' := by
  revert hL θ θ'
  induction L with
  | zero =>
      intro hL θ θ' _D _θfull _FullPaths _hPaths _A
      omega
  | succ L ih =>
      intro _hL θ θ' D θfull FullPaths hPaths A
      cases L with
      | zero =>
          exact IDL_depth_one hd hr D
      | succ L =>
          let hstep :
              TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
                (fun η => TexAnchorCertificate η) θ' :=
            D.texGenericStepClauses
          rcases A with
            ⟨matchingFrec, _sweepNear, openRealization, tailThreaded⟩
          let endpoint :
              FirstLayerEndpointData
                (Params.headAttention θ) (Params.headAttention θ')
                (Params.headValue θ) :=
            D.firstLayerEndpoint hr
          let htail : 0 < L + 1 := Nat.succ_pos L
          let reducedLocalConnectedChart :
              TexRegionReducedLocalConnectedChartDataOfIDLData htail D :=
            texRegionReducedLocalConnectedChartDataOfIDLData_of_solvedCoordChart htail D
          let localRegion :
              TexRegionConstructionDataOfIDLDataObligation htail D :=
            texRegionConstructionDataOfIDLDataObligation_of_localConnectedChartProvider
              (L := L + 1) (d := d) (r := r)
              (θ := θ) (θ' := θ') htail hd hstep D
              reducedLocalConnectedChart
          let matching : FirstLayerMatchedData θ θ' :=
            matchingFrec.matching
          let tailData :
              IDLData (L + 1) d r (Params.tail θ) (Params.tail θ') :=
            tail_IDLData_of_texGenericStep_of_openRealizationData
              (L := L + 1) (d := d) (r := r)
              (θ := θ) (θ' := θ') hd hr hstep matching D openRealization
          let tailPaths :
              tailData.Paths = realizedTailPathSet r θ D.Paths :=
            by
              simp [tailData, tail_IDLData_of_texGenericStep_of_openRealizationData,
                tail_IDLData_of_texGenericStep, sweepData_of_texGenericStep]
          have htailEq : Params.tail θ = Params.tail θ' :=
            ih (hL := by omega) (θ := Params.tail θ) (θ' := Params.tail θ')
              tailData θ D.Paths tailPaths tailThreaded
          exact IDL_nLayer_induction_step matching htailEq

/-- The top-level `IDLData` obtained from global positive-ray probe agreement. -/
noncomputable def texGenericIDLData_from_probeAgreement
    {L d r : Nat} (hL : 1 <= L) (hr : 2 <= r) (_hd : 2 <= d)
    (hrows : genericCertificateRows L <= d)
    {θ θ' : Params L d}
    (hθ' : θ' ∈ TexGenericSet L d)
    (hagree : ProbeObservableAgreement r θ θ') :
    IDLData L d r θ θ' := by
  have _ := hr
  have hgeneric : TexGeneric L d θ' := by
    simpa [TexGenericSet] using hθ'
  have hpaths : ObservableAgreementForPaths r θ θ' (Set.univ : Set (ProbePath d)) := by
    intro P _hP
    refine ⟨0, ?_, ?_⟩
    · norm_num
    · intro τ hτ
      exact hagree (P τ).1 (P τ).2 τ hτ
  have hanchor : L = 1 ∨ (Set.univ ∩ unwoundAnchorSet θ').Nonempty := by
    rcases L with _ | L
    · omega
    rcases L with _ | L
    · exact Or.inl rfl
    · right
      have hstep :
          TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
            (fun η => TexAnchorCertificate η) θ' := by
        simpa [TexGenericSet, TexGeneric] using hθ'
      have hanchor' : (unwoundAnchorSet θ').Nonempty :=
        unwoundAnchorSet_nonempty_of_texAnchorCertificate
          (L := L + 2) (d := d) (hL := by omega) hrows hstep.g4_certificate
      rcases hanchor' with ⟨p, hp⟩
      exact ⟨p, by simp [hp]⟩
  exact
    { primed_generic := hgeneric
      O := Set.univ
      O_open := isOpen_univ
      O_nonempty := ⟨(fun _ => 0, fun _ => 0), by simp⟩
      anchor_nonempty := hanchor
      Paths := Set.univ
      path_agreement := hpaths
      constant_paths_available := by
        intro p _hp
        exact Set.mem_univ (constantProbePath p) }

/-- The top-level probe-agreement datum starts with the universal path class. -/
@[simp] theorem texGenericIDLData_from_probeAgreement_paths
    {L d r : Nat} (hL : 1 <= L) (hr : 2 <= r) (hd : 2 <= d)
    (hrows : genericCertificateRows L <= d)
    {θ θ' : Params L d}
    (hθ' : θ' ∈ TexGenericSet L d)
    (hagree : ProbeObservableAgreement r θ θ') :
    (texGenericIDLData_from_probeAgreement hL hr hd hrows hθ' hagree).Paths =
      Set.univ :=
  rfl

set_option linter.style.longLine false

set_option linter.style.longLine true

set_option linter.style.longLine false

/-- Builder-selected-tail local top-level constructor data, excluding the recursive
swept tail.

This is the explicit-trichotomy analogue of the selected-tail local frontier above.
It exposes the first-layer matching package directly, so the current-layer matching
does not pass through the legacy local-patch `matchingFrec` wrapper. -/
structure
    IDLReducedUnivCurrentProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTLocalConstructorData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 2) d}
    (D : IDLData (L + 2) d r θ θ')
    (hPaths : D.Paths = Set.univ) : Type where
  matchingTrichotomy :
    let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
        (fun η => TexAnchorCertificate η) θ' :=
      D.texGenericStepClauses
    let endpoint :
        FirstLayerEndpointData
          (Params.headAttention θ) (Params.headAttention θ')
          (Params.headValue θ) :=
      D.firstLayerEndpoint hr
    TexFirstLayerMatchingAnalyticDataOfTrichotomy hr hstep endpoint D

/-- Convenience local constructor from the provider-facing cascade induction API. -/
noncomputable def
    idlReducedUnivCurrentProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTLocalConstructorData_of_inductionProvider_paths_univ_lowerDepthSelectedTail
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' θB : Params (L + 2) d}
    (D : IDLData (L + 2) d r θ θ')
    (hPaths : D.Paths = Set.univ)
    (signRegion :
      SignRegionData (L := L + 2) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    {A : Matrix (Fin d) (Fin d) ℝ}
    {unprimed primed : GateAlongBase d}
    (P : CascadeTrichotomyInductionProviderData
      (L := L + 2) (d := d) (Real.log (r : ℝ)) θB A signRegion.U
        unprimed primed)
    (actual :
      let T := texTrichotomyConstructionData_of_inductionProvider P
      let N :=
        texMatchingProductNeighborhoodData_of_trichotomy
          (L := L + 1) (d := d) (r := r) hr D.texGenericStepClauses
          (D.firstLayerEndpoint hr) D signRegion T
      TexTrichotomyMatchingCanonicalActualGateData
        (θ := θ) (θ' := θ') signRegion T N) :
    IDLReducedUnivCurrentProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTLocalConstructorData
      hd hr D hPaths where
  matchingTrichotomy :=
    let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
        (fun η => TexAnchorCertificate η) θ' :=
      D.texGenericStepClauses
    let endpoint :
        FirstLayerEndpointData
          (Params.headAttention θ) (Params.headAttention θ')
          (Params.headValue θ) :=
      D.firstLayerEndpoint hr
    let T := texTrichotomyConstructionData_of_inductionProvider P
    let N :=
      texMatchingProductNeighborhoodData_of_trichotomy
        (L := L + 1) (d := d) (r := r) hr hstep endpoint D signRegion T
    let S :=
      texMatchingSaturatedContributionData_of_inductionProvider
        (L := L + 1) (d := d) (θ := θ) P
    let hAA : Params.headAttention θ = Params.headAttention θ' :=
      endpoint.attention_eq
    texFirstLayerMatchingAnalyticDataOfTrichotomy_of_inductionProvider_paths_univ_lowerDepthSelectedTail
      (L := L + 1) (d := d) (r := r) hr hstep endpoint D hPaths signRegion
      P N S hAA actual

/-- Builder-selected-tail explicit-trichotomy top-level constructor package whose
recursive tail is generated from all-depth realized-tail local providers. -/
abbrev
    IDLReducedUnivCurrentProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTRecursiveConstructorData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 2) d}
    (D : IDLData (L + 2) d r θ θ')
    (hPaths : D.Paths = Set.univ) : Type :=
  Σ _ :
      IDLReducedUnivCurrentProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTLocalConstructorData
        hd hr D hPaths,
    IDLReducedRealizedTailLocalConstructorProvider d r hd hr

/-- Universal-path reduced Sigma package for the explicit-trichotomy current layer.

This is parallel to `IDLRecursiveReducedAnalyticDataOfUnivPaths`, but its current
matching component is `TexFirstLayerMatchingAnalyticDataOfTrichotomy`.  The swept
tail continues to use the existing realized-tail reduced package. -/
noncomputable def IDLRecursiveReducedAnalyticDataOfUnivPathsBuilderSelectedTail :
    (L d r : Nat) -> (hd : 2 <= d) -> (hr : 2 <= r) ->
      {θ θ' : Params L d} -> (D : IDLData L d r θ θ') ->
        D.Paths = Set.univ -> Type
  | 0, _d, _r, _hd, _hr, _θ, _θ', _D, _hPaths => PUnit
  | 1, _d, _r, _hd, _hr, _θ, _θ', _D, _hPaths => PUnit
  | L + 2, d, r, hd, hr, θ, θ', D, hPaths =>
      let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
          (fun η => TexAnchorCertificate η) θ' :=
        D.texGenericStepClauses
      let endpoint :
          FirstLayerEndpointData
            (Params.headAttention θ) (Params.headAttention θ')
            (Params.headValue θ) :=
        D.firstLayerEndpoint hr
      @Sigma
        (TexFirstLayerMatchingAnalyticDataOfTrichotomy hr hstep endpoint D)
        (fun matchingAnalytic =>
          let matching : FirstLayerMatchedData θ θ' :=
            firstLayerMatched_of_texGenericStep_of_IDLData_trichotomy
              (L := L + 1) (d := d) (r := r)
              (θ := θ) (θ' := θ') hr hstep endpoint D matchingAnalytic
          @Sigma
            (PLift
              (TexSweepLocalRealizationNearAnchorPoint D
                (texSweepAnchorPointData_of_IDLData D)))
            (fun sweepNear =>
              let sweepAnalytic :
                  TexSweepAnalyticData hstep matching D :=
                texSweepAnalyticData_of_paths_univ_nearAnchorPoint
                  hstep matching D hPaths sweepNear.down
              IDLRecursiveReducedAnalyticData (L + 1) d r hd hr
                (tail_IDLData_of_texGenericStep_of_IDLData
                  (L := L + 1) (d := d) (r := r)
                  (θ := θ) (θ' := θ') hd hr hstep matching D sweepAnalytic)
                θ D.Paths
                (texMatching_tail_IDLData_of_texGenericStep_of_IDLData_paths
                  (L := L + 1) (d := d) (r := r)
                  (θ := θ) (θ' := θ') hd hr hstep matching D sweepAnalytic)))

/-- Universal-path threaded reduced Sigma package for the explicit-trichotomy current
layer.

This is parallel to `IDLRecursiveReducedAnalyticDataOfUnivPathsBuilderSelectedTail`,
but the universal top-node sweep chooses an open-realization tail and the recursive
tail is the threaded reduced package over that same open set. -/
noncomputable def IDLRecursiveThreadedReducedAnalyticDataOfUnivPathsBuilderSelectedTail :
    (L d r : Nat) -> (hd : 2 <= d) -> (hr : 2 <= r) ->
      {θ θ' : Params L d} -> (D : IDLData L d r θ θ') ->
        D.Paths = Set.univ -> Type
  | 0, _d, _r, _hd, _hr, _θ, _θ', _D, _hPaths => PUnit
  | 1, _d, _r, _hd, _hr, _θ, _θ', _D, _hPaths => PUnit
  | L + 2, d, r, hd, hr, θ, θ', D, hPaths =>
      let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
          (fun η => TexAnchorCertificate η) θ' :=
        D.texGenericStepClauses
      let endpoint :
          FirstLayerEndpointData
            (Params.headAttention θ) (Params.headAttention θ')
            (Params.headValue θ) :=
        D.firstLayerEndpoint hr
      @Sigma
        (TexFirstLayerMatchingAnalyticDataOfTrichotomy hr hstep endpoint D)
        (fun matchingAnalytic =>
          let matching : FirstLayerMatchedData θ θ' :=
            firstLayerMatched_of_texGenericStep_of_IDLData_trichotomy
              (L := L + 1) (d := d) (r := r)
              (θ := θ) (θ' := θ') hr hstep endpoint D matchingAnalytic
          let seed := texSweepOpenRealizationUniformData_of_IDLData_matching_univ
            D matching hPaths
          let R : TexSweepOpenRealizationData D := seed.1
          IDLThreadedRecursiveReducedAnalyticData (L + 1) d r hd hr
            (tail_IDLData_of_texGenericStep_of_openRealizationData
              (L := L + 1) (d := d) (r := r)
              (θ := θ) (θ' := θ') hd hr hstep matching D R)
            θ D.Paths
            (by
              simp [tail_IDLData_of_texGenericStep_of_openRealizationData,
                tail_IDLData_of_texGenericStep, sweepData_of_texGenericStep]))

/-- Builder-selected-tail explicit-trichotomy top-level constructor package whose
recursive open-realization tail is generated from threaded realized-tail providers. -/
abbrev
    IDLReducedUnivCurrentProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTThreadedRecursiveConstructorData
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 2) d}
    (D : IDLData (L + 2) d r θ θ')
    (hPaths : D.Paths = Set.univ) : Type :=
  Σ _ :
      IDLReducedUnivCurrentProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTLocalConstructorData
        hd hr D hPaths,
    IDLReducedRealizedTailMatchingFrecProvider d r hd hr

/-- Direct compiler from the builder-selected-tail threaded local-provider package to
the threaded explicit-trichotomy reduced Sigma package. -/
noncomputable def
    idlReducedUnivCurrentProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTThreadedConstructorData_to_threadedReduced
    {L d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params (L + 2) d}
    (D : IDLData (L + 2) d r θ θ')
    (hPaths : D.Paths = Set.univ)
    (A :
      IDLReducedUnivCurrentProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTThreadedRecursiveConstructorData
        hd hr D hPaths) :
    IDLRecursiveThreadedReducedAnalyticDataOfUnivPathsBuilderSelectedTail
      (L + 2) d r hd hr D hPaths := by
  let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
      (fun η => TexAnchorCertificate η) θ' :=
    D.texGenericStepClauses
  let endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ) :=
    D.firstLayerEndpoint hr
  let matchingAnalytic :
      TexFirstLayerMatchingAnalyticDataOfTrichotomy hr hstep endpoint D :=
    A.1.matchingTrichotomy
  let matching : FirstLayerMatchedData θ θ' :=
    firstLayerMatched_of_texGenericStep_of_IDLData_trichotomy
      (L := L + 1) (d := d) (r := r)
      (θ := θ) (θ' := θ') hr hstep endpoint D matchingAnalytic
  let seed := texSweepOpenRealizationUniformData_of_IDLData_matching_univ
    D matching hPaths
  let R : TexSweepOpenRealizationData D := seed.1
  let tailData :
      IDLData (L + 1) d r (Params.tail θ) (Params.tail θ') :=
    tail_IDLData_of_texGenericStep_of_openRealizationData
      (L := L + 1) (d := d) (r := r)
      (θ := θ) (θ' := θ') hd hr hstep matching D R
  let tailPaths :
      tailData.Paths = realizedTailPathSet r θ D.Paths :=
    by
      simp [tailData, tail_IDLData_of_texGenericStep_of_openRealizationData,
        tail_IDLData_of_texGenericStep, sweepData_of_texGenericStep]
  let localProvider : IDLReducedRealizedTailThreadedLocalConstructorProvider d r hd hr :=
    idlReducedRealizedTailThreadedLocalConstructorProvider_of_matchingFrecProvider
      A.2
  cases L with
  | zero =>
      exact ⟨matchingAnalytic, PUnit.unit⟩
  | succ L =>
      have htailAnchorNonempty :
          (tailData.O ∩ unwoundAnchorSet (Params.tail θ')).Nonempty :=
        tailData.anchor_nonempty.resolve_left (by omega)
      let htailAnchorMem : (idlChosenFullAnchor tailData).1 ∈ tailData.O :=
        idlChosenFullAnchor_fst_mem_O tailData htailAnchorNonempty
      let tailThreaded :
          IDLThreadedRecursiveReducedAnalyticData (L + 2) d r hd hr
            tailData θ D.Paths tailPaths :=
        idlRecursiveReducedAnalyticData_of_threadedRealizedTailLocalProvider
          hd hr localProvider
          L tailData
          (Dfull := D) hstep matching tailPaths
          tailData.O tailData.O_open htailAnchorMem
          seed.2.val
          (by
            simpa [tailData, R, tail_IDLData_of_texGenericStep_of_openRealizationData,
              tail_IDLData_of_texGenericStep, sweepData_of_texGenericStep]
              using seed.2.property.2)
          (Set.Subset.refl _)
      exact ⟨matchingAnalytic, tailThreaded⟩

set_option linter.style.longLine true

set_option linter.style.longLine false

set_option linter.style.longLine true

set_option linter.style.longLine false

/-- Top-level current-constructor provider using explicit-trichotomy builder-selected
matching and internally derived canonical IFT sweep data.

Depths `0` and `1` remain vacuous.  At depth at least `2`, this unfolds to the
explicit-trichotomy local matching field plus an all-depth realized-tail local
provider. -/
noncomputable def
    TexGenericProbeAgreementProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTCurrentConstructorData :
    {L d r : Nat} -> (hL : 1 <= L) -> (hr : 2 <= r) -> (hd : 2 <= d) ->
      (hrows : genericCertificateRows L <= d) ->
      {θ θ' : Params L d} ->
        (hθ' : θ' ∈ TexGenericSet L d) ->
          (hagree : ProbeObservableAgreement r θ θ') -> Type
  | 0, _d, _r, _hL, _hr, _hd, _hrows, _θ, _θ', _hθ', _hagree => PUnit
  | 1, _d, _r, _hL, _hr, _hd, _hrows, _θ, _θ', _hθ', _hagree => PUnit
  | _L + 2, _d, _r, hL, hr, hd, hrows, _θ, _θ', hθ', hagree =>
      IDLReducedUnivCurrentProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTRecursiveConstructorData
        hd hr
        (texGenericIDLData_from_probeAgreement hL hr hd hrows hθ' hagree)
        (texGenericIDLData_from_probeAgreement_paths hL hr hd hrows hθ' hagree)

/-- Assemble the top-level builder-selected-tail current-constructor provider from the
provider-facing cascade induction route and canonical actual-gate data. -/
noncomputable def
    texGenericProbeAgreementProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTCurrentConstructorData_of_inductionProvider_lowerDepthSelectedTail
    {L d r : Nat} (hL : 1 <= L + 2) (hr : 2 <= r) (hd : 2 <= d)
    (hrows : genericCertificateRows (L + 2) <= d)
    {θ θ' θB : Params (L + 2) d}
    (hθ' : θ' ∈ TexGenericSet (L + 2) d)
    (hagree : ProbeObservableAgreement r θ θ')
    (signRegion :
      SignRegionData (L := L + 2) (d := d) θ'
        (texGenericIDLData_from_probeAgreement hL hr hd hrows hθ' hagree).O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    {A : Matrix (Fin d) (Fin d) ℝ}
    {unprimed primed : GateAlongBase d}
    (P : CascadeTrichotomyInductionProviderData
      (L := L + 2) (d := d) (Real.log (r : ℝ)) θB A signRegion.U
        unprimed primed)
    (actual :
      let D := texGenericIDLData_from_probeAgreement hL hr hd hrows hθ' hagree
      let T := texTrichotomyConstructionData_of_inductionProvider P
      let N :=
        texMatchingProductNeighborhoodData_of_trichotomy
          (L := L + 1) (d := d) (r := r) hr D.texGenericStepClauses
          (D.firstLayerEndpoint hr) D signRegion T
      TexTrichotomyMatchingCanonicalActualGateData
        (θ := θ) (θ' := θ') signRegion T N)
    (tailLocal : IDLReducedRealizedTailLocalConstructorProvider d r hd hr) :
    TexGenericProbeAgreementProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTCurrentConstructorData
      hL hr hd hrows hθ' hagree :=
  let D := texGenericIDLData_from_probeAgreement hL hr hd hrows hθ' hagree
  let hPaths := texGenericIDLData_from_probeAgreement_paths hL hr hd hrows hθ' hagree
  ⟨
    idlReducedUnivCurrentProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTLocalConstructorData_of_inductionProvider_paths_univ_lowerDepthSelectedTail
      hd hr D hPaths signRegion P actual,
    tailLocal
  ⟩

/-- Assemble the top-level builder-selected-tail current-constructor provider while
deriving the canonical sign-region package from the local chart/region construction. -/
noncomputable def
    texGenericProbeAgreementProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTCurrentConstructorData_of_localRegion_inductionProvider_lowerDepthSelectedTail
    {L d r : Nat} (hL : 1 <= L + 2) (hr : 2 <= r) (hd : 2 <= d)
    (hrows : genericCertificateRows (L + 2) <= d)
    {θ θ' θB : Params (L + 2) d}
    (hθ' : θ' ∈ TexGenericSet (L + 2) d)
    (hagree : ProbeObservableAgreement r θ θ')
    {A : Matrix (Fin d) (Fin d) ℝ}
    {unprimed primed : GateAlongBase d}
    (P :
      let D := texGenericIDLData_from_probeAgreement hL hr hd hrows hθ' hagree
      let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
          (fun η => TexAnchorCertificate η) θ' :=
        D.texGenericStepClauses
      let endpoint :
          FirstLayerEndpointData
            (Params.headAttention θ) (Params.headAttention θ')
            (Params.headValue θ) :=
        D.firstLayerEndpoint hr
      let htail : 0 < L + 1 := Nat.succ_pos L
      let reducedLocalConnectedChart :
          TexRegionReducedLocalConnectedChartDataOfIDLData htail D :=
        texRegionReducedLocalConnectedChartDataOfIDLData_of_solvedCoordChart htail D
      let localRegion :
          TexRegionConstructionDataOfIDLDataObligation htail D :=
        texRegionConstructionDataOfIDLDataObligation_of_localConnectedChartProvider
          (L := L + 1) (d := d) (r := r)
          (θ := θ) (θ' := θ') htail hd hstep D
          reducedLocalConnectedChart
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L + 1) (d := d) (r := r) htail hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L + 1) (d := d) (r := r) hr hstep endpoint D region
      CascadeTrichotomyInductionProviderData
        (L := L + 2) (d := d) (Real.log (r : ℝ)) θB A signRegion.U
          unprimed primed)
    (actual :
      let D := texGenericIDLData_from_probeAgreement hL hr hd hrows hθ' hagree
      let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
          (fun η => TexAnchorCertificate η) θ' :=
        D.texGenericStepClauses
      let endpoint :
          FirstLayerEndpointData
            (Params.headAttention θ) (Params.headAttention θ')
            (Params.headValue θ) :=
        D.firstLayerEndpoint hr
      let htail : 0 < L + 1 := Nat.succ_pos L
      let reducedLocalConnectedChart :
          TexRegionReducedLocalConnectedChartDataOfIDLData htail D :=
        texRegionReducedLocalConnectedChartDataOfIDLData_of_solvedCoordChart htail D
      let localRegion :
          TexRegionConstructionDataOfIDLDataObligation htail D :=
        texRegionConstructionDataOfIDLDataObligation_of_localConnectedChartProvider
          (L := L + 1) (d := d) (r := r)
          (θ := θ) (θ' := θ') htail hd hstep D
          reducedLocalConnectedChart
      let region :=
        texRegionConstructionData_of_IDLData_of_localPatch
          (L := L + 1) (d := d) (r := r) htail hr hstep endpoint D localRegion
      let signRegion :=
        texMatchingSignRegionData_of_region
          (L := L + 1) (d := d) (r := r) hr hstep endpoint D region
      let T := texTrichotomyConstructionData_of_inductionProvider P
      let N :=
        texMatchingProductNeighborhoodData_of_trichotomy
          (L := L + 1) (d := d) (r := r) hr hstep endpoint D signRegion T
      TexTrichotomyMatchingCanonicalActualGateData
        (θ := θ) (θ' := θ') signRegion T N)
    (tailLocal : IDLReducedRealizedTailLocalConstructorProvider d r hd hr) :
    TexGenericProbeAgreementProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTCurrentConstructorData
      hL hr hd hrows hθ' hagree :=
  let D := texGenericIDLData_from_probeAgreement hL hr hd hrows hθ' hagree
  let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
      (fun η => TexAnchorCertificate η) θ' :=
    D.texGenericStepClauses
  let endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ) :=
    D.firstLayerEndpoint hr
  let htail : 0 < L + 1 := Nat.succ_pos L
  let reducedLocalConnectedChart :
      TexRegionReducedLocalConnectedChartDataOfIDLData htail D :=
    texRegionReducedLocalConnectedChartDataOfIDLData_of_solvedCoordChart htail D
  let localRegion :
      TexRegionConstructionDataOfIDLDataObligation htail D :=
    texRegionConstructionDataOfIDLDataObligation_of_localConnectedChartProvider
      (L := L + 1) (d := d) (r := r)
      (θ := θ) (θ' := θ') htail hd hstep D
      reducedLocalConnectedChart
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L + 1) (d := d) (r := r) htail hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L + 1) (d := d) (r := r) hr hstep endpoint D region
  texGenericProbeAgreementProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTCurrentConstructorData_of_inductionProvider_lowerDepthSelectedTail
    hL hr hd hrows hθ' hagree signRegion P actual tailLocal

/-- Assemble the top-level builder-selected-tail current-constructor provider from the
canonical solved-coordinate trichotomy route.

This is the current-constructor surface closest to the final proof: the local region,
canonical cascade provider, product-neighborhood actual-gate data, and generic matrix
facts are derived internally from the existing canonical pieces.  The remaining inputs
are the genuine external leaves: the selected initial tail and the realized-tail local
provider. -/
noncomputable def
    texGenericProbeAgreementProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTCurrentConstructorData_of_localRegion_solvedCoordChartCanonicalGates_lowerDepthSelectedTail
    {L d r : Nat} (hL : 1 <= L + 2) (hr : 2 <= r) (hd : 2 <= d)
    (hrows : genericCertificateRows (L + 2) <= d)
    {θ θ' : Params (L + 2) d}
    (hθ' : θ' ∈ TexGenericSet (L + 2) d)
    (hagree : ProbeObservableAgreement r θ θ')
    (tail0 : Nat -> ℝ)
    (tailLocal : IDLReducedRealizedTailLocalConstructorProvider d r hd hr) :
    TexGenericProbeAgreementProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTCurrentConstructorData
      hL hr hd hrows hθ' hagree :=
  let D := texGenericIDLData_from_probeAgreement hL hr hd hrows hθ' hagree
  let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
      (fun η => TexAnchorCertificate η) θ' :=
    D.texGenericStepClauses
  let endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ) :=
    D.firstLayerEndpoint hr
  let htail : 0 < L + 1 := Nat.succ_pos L
  let reducedLocalConnectedChart :
      TexRegionReducedLocalConnectedChartDataOfIDLData htail D :=
    texRegionReducedLocalConnectedChartDataOfIDLData_of_solvedCoordChart htail D
  let localRegion :
      TexRegionConstructionDataOfIDLDataObligation htail D :=
    texRegionConstructionDataOfIDLDataObligation_of_localConnectedChartProvider
      (L := L + 1) (d := d) (r := r)
      (θ := θ) (θ' := θ') htail hd hstep D
      reducedLocalConnectedChart
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L + 1) (d := d) (r := r) htail hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L + 1) (d := d) (r := r) hr hstep endpoint D region
  let dimension_pos : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 2) hd
  let head_det_ne_zero : (Params.headAttention θ').det ≠ 0 := by
    have hfirst : firstAttention θ' = Params.headAttention θ' := by
      simpa using firstAttention_eq_of_pos θ' (Nat.succ_pos (L + 1))
    simpa [hfirst] using hstep.g1_det_firstAttention
  let head_sym_ne_zero : symPart (Params.headAttention θ') ≠ 0 := by
    have hfirst : firstAttention θ' = Params.headAttention θ' := by
      simpa using firstAttention_eq_of_pos θ' (Nat.succ_pos (L + 1))
    simpa [hfirst] using hstep.g1_sym_firstAttention
  let head_value_ne_zero : (paramStream θ 0).1 ≠ 0 := by
    simpa [Params.headValue, Params.headLayer, paramStream_apply_of_lt] using
      endpoint.targetValue_ne_zero
  let P :=
    cascadeTrichotomyInductionProviderData_of_dichotomyChoices_from_solvedCoordChart_productPatchZeroBranch
      (L := L + 1) (d := d) (r := r) (θ := θ) (θ' := θ')
      (O := D.O) signRegion endpoint.attention_eq tail0
      dimension_pos head_det_ne_zero head_sym_ne_zero head_value_ne_zero
  let actual :
      let T := texTrichotomyConstructionData_of_inductionProvider P
      let N :=
        texMatchingProductNeighborhoodData_of_trichotomy
          (L := L + 1) (d := d) (r := r) hr hstep endpoint D signRegion T
      TexTrichotomyMatchingCanonicalActualGateData
        (θ := θ) (θ' := θ') signRegion T N :=
    let T := texTrichotomyConstructionData_of_inductionProvider P
    let N :=
      texMatchingProductNeighborhoodData_of_trichotomy
        (L := L + 1) (d := d) (r := r) hr hstep endpoint D signRegion T
    texTrichotomyMatchingCanonicalActualGateData_of_canonicalFrecGates
      (L := L + 1) (d := d) (r := r) signRegion T N rfl rfl
  texGenericProbeAgreementProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTCurrentConstructorData_of_localRegion_inductionProvider_lowerDepthSelectedTail
    hL hr hd hrows hθ' hagree P actual tailLocal

/-- Assemble the threaded top-level builder-selected-tail current-constructor package
from the canonical solved-coordinate trichotomy route.

This mirrors
`texGenericProbeAgreementProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTCurrentConstructorData_of_localRegion_solvedCoordChartCanonicalGates_lowerDepthSelectedTail`,
but keeps the remaining recursive leaf as the threaded matching provider. -/
noncomputable def
    texGenericProbeAgreementProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTThreadedCurrentConstructorData_of_localRegion_solvedCoordChartCanonicalGates_lowerDepthSelectedTail
    {L d r : Nat} (hL : 1 <= L + 2) (hr : 2 <= r) (hd : 2 <= d)
    (hrows : genericCertificateRows (L + 2) <= d)
    {θ θ' : Params (L + 2) d}
    (hθ' : θ' ∈ TexGenericSet (L + 2) d)
    (hagree : ProbeObservableAgreement r θ θ')
    (tail0 : Nat -> ℝ)
    (matchingProvider : IDLReducedRealizedTailMatchingFrecProvider d r hd hr) :
    IDLReducedUnivCurrentProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTThreadedRecursiveConstructorData
      hd hr
      (texGenericIDLData_from_probeAgreement hL hr hd hrows hθ' hagree)
      (texGenericIDLData_from_probeAgreement_paths hL hr hd hrows hθ' hagree) :=
  let D := texGenericIDLData_from_probeAgreement hL hr hd hrows hθ' hagree
  let hPaths := texGenericIDLData_from_probeAgreement_paths hL hr hd hrows hθ' hagree
  let hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
      (fun η => TexAnchorCertificate η) θ' :=
    D.texGenericStepClauses
  let endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ) :=
    D.firstLayerEndpoint hr
  let htail : 0 < L + 1 := Nat.succ_pos L
  let reducedLocalConnectedChart :
      TexRegionReducedLocalConnectedChartDataOfIDLData htail D :=
    texRegionReducedLocalConnectedChartDataOfIDLData_of_solvedCoordChart htail D
  let localRegion :
      TexRegionConstructionDataOfIDLDataObligation htail D :=
    texRegionConstructionDataOfIDLDataObligation_of_localConnectedChartProvider
      (L := L + 1) (d := d) (r := r)
      (θ := θ) (θ' := θ') htail hd hstep D
      reducedLocalConnectedChart
  let region :=
    texRegionConstructionData_of_IDLData_of_localPatch
      (L := L + 1) (d := d) (r := r) htail hr hstep endpoint D localRegion
  let signRegion :=
    texMatchingSignRegionData_of_region
      (L := L + 1) (d := d) (r := r) hr hstep endpoint D region
  let dimension_pos : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 2) hd
  let head_det_ne_zero : (Params.headAttention θ').det ≠ 0 := by
    have hfirst : firstAttention θ' = Params.headAttention θ' := by
      simpa using firstAttention_eq_of_pos θ' (Nat.succ_pos (L + 1))
    simpa [hfirst] using hstep.g1_det_firstAttention
  let head_sym_ne_zero : symPart (Params.headAttention θ') ≠ 0 := by
    have hfirst : firstAttention θ' = Params.headAttention θ' := by
      simpa using firstAttention_eq_of_pos θ' (Nat.succ_pos (L + 1))
    simpa [hfirst] using hstep.g1_sym_firstAttention
  let head_value_ne_zero : (paramStream θ 0).1 ≠ 0 := by
    simpa [Params.headValue, Params.headLayer, paramStream_apply_of_lt] using
      endpoint.targetValue_ne_zero
  let P :=
    cascadeTrichotomyInductionProviderData_of_dichotomyChoices_from_solvedCoordChart_productPatchZeroBranch
      (L := L + 1) (d := d) (r := r) (θ := θ) (θ' := θ')
      (O := D.O) signRegion endpoint.attention_eq tail0
      dimension_pos head_det_ne_zero head_sym_ne_zero head_value_ne_zero
  let actual :
      let T := texTrichotomyConstructionData_of_inductionProvider P
      let N :=
        texMatchingProductNeighborhoodData_of_trichotomy
          (L := L + 1) (d := d) (r := r) hr hstep endpoint D signRegion T
      TexTrichotomyMatchingCanonicalActualGateData
        (θ := θ) (θ' := θ') signRegion T N :=
    let T := texTrichotomyConstructionData_of_inductionProvider P
    let N :=
      texMatchingProductNeighborhoodData_of_trichotomy
        (L := L + 1) (d := d) (r := r) hr hstep endpoint D signRegion T
    texTrichotomyMatchingCanonicalActualGateData_of_canonicalFrecGates
      (L := L + 1) (d := d) (r := r) signRegion T N rfl rfl
  let localTop :
      IDLReducedUnivCurrentProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTLocalConstructorData
        hd hr D hPaths :=
    idlReducedUnivCurrentProbeCoordSplitBaseTailZeroFreeConcreteBuilderSelectedTailCanonicalIFTLocalConstructorData_of_inductionProvider_paths_univ_lowerDepthSelectedTail
      hd hr D hPaths signRegion P actual
  ⟨localTop, matchingProvider⟩

set_option linter.style.longLine true

/-- Identifiability from the builder-selected-tail explicit-trichotomy universal-path
threaded reduced package. -/
theorem IDL_of_univBuilderSelectedTailThreadedReduced
    {L d r : Nat} (hL : 1 <= L) (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params L d} :
    (D : IDLData L d r θ θ') ->
      (hPaths : D.Paths = Set.univ) ->
        IDLRecursiveThreadedReducedAnalyticDataOfUnivPathsBuilderSelectedTail
          L d r hd hr D hPaths ->
          θ = θ' := by
  cases L with
  | zero =>
      intro _D _hPaths _A
      omega
  | succ L =>
      cases L with
      | zero =>
          intro D _hPaths _A
          exact IDL_depth_one hd hr D
      | succ L =>
          intro D hPaths A
          let hstep :
              TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
                (fun η => TexAnchorCertificate η) θ' :=
            D.texGenericStepClauses
          rcases A with ⟨matchingAnalytic, tailThreaded⟩
          let endpoint :
              FirstLayerEndpointData
                (Params.headAttention θ) (Params.headAttention θ')
                (Params.headValue θ) :=
            D.firstLayerEndpoint hr
          let matching : FirstLayerMatchedData θ θ' :=
            firstLayerMatched_of_texGenericStep_of_IDLData_trichotomy
              (L := L + 1) (d := d) (r := r)
              (θ := θ) (θ' := θ') hr hstep endpoint D matchingAnalytic
          let seed := texSweepOpenRealizationUniformData_of_IDLData_matching_univ
            D matching hPaths
          let R : TexSweepOpenRealizationData D := seed.1
          let tailData :
              IDLData (L + 1) d r (Params.tail θ) (Params.tail θ') :=
            tail_IDLData_of_texGenericStep_of_openRealizationData
              (L := L + 1) (d := d) (r := r)
              (θ := θ) (θ' := θ') hd hr hstep matching D R
          let tailPaths :
              tailData.Paths = realizedTailPathSet r θ D.Paths :=
            by
              simp [tailData, tail_IDLData_of_texGenericStep_of_openRealizationData,
                tail_IDLData_of_texGenericStep, sweepData_of_texGenericStep]
          have htail : Params.tail θ = Params.tail θ' :=
            IDL_of_threadedReduced (by omega) hd hr
              tailData θ D.Paths tailPaths tailThreaded
          exact IDL_nLayer_induction_step matching htail

end TransformerIdentifiability.NLayer
