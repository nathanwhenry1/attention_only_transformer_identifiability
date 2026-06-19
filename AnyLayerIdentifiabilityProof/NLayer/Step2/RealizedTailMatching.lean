import AnyLayerIdentifiabilityProof.NLayer.Step2.IDLMatching
import AnyLayerIdentifiabilityProof.NLayer.Step2.SweepRealization

/-!
# Realized-tail matching boundary — the `dial_mem` endgame

This module isolates the single remaining open obligation of the all-depth
identifiability proof, `dial_mem`, for the recursive (realized-tail) nodes.

The matching-side reduction chain already built in `Step2/IDLMatching` reduces `dial_mem`
(`TexMatchingLocalPatchRegularQuadricDialMemObligation`) to the per-dial realized-tail
membership `TexMatchingLocalPatchRegularQuadricDialRealizedTailMemObligation`, given
`D.Paths = realizedTailPathSet r θfull FullPaths`
(`texMatchingLocalPatchRegularQuadricDialMemObligation_of_realizedTailMemObligation`).

The bridge here discharges that membership from the *parent's* path-level realization
invariant `UniformTailRealize` (`Step2/SweepRealization`).  The key device — mirroring the
engine's own `uniformTailRealize_step` — is the **parking trick**: the dial path converges
to its base point `p` (`tendsto_dialPathData_probe`, TeX `lem:dial`(c)), so once `p ∈ Uprev`
(open) the dial eventually enters `Uprev`; we then feed `hprev` the modified path that equals
the dial above its entry time and is *parked at* `p ∈ Uprev` below.  That modified path is in
`Uprev` for **all** `τ` (not merely past a fixed threshold), so `hprev` realizes it through
`θfull`, and the realizer agrees with the dial asymptotically — certifying the dial as a
realized tail.

Net effect: the threshold coupling created by the fixed-`T` shape of `UniformTailRealize`
*dissolves*, and "the whole remaining math" of the proof reduces to the genuine paper content
— that the canonical dial bases lie in the parent region, `N.Uq ⊆ Uprev`
(TeX `𝒫(Õ)` membership / anchor-threading).
-/

set_option linter.style.longLine false

namespace TransformerIdentifiability.NLayer

open Filter Topology

variable {d r : Nat}

/-- **The parking trick.**  Any `DialPathData` path whose base point lies in an open set
`Uprev` carrying the parent realization invariant `UniformTailRealize r θfull FullPaths Uprev
Tprev` is a realized tail of `FullPaths` through `θfull`'s first layer.

The dial converges to its base (`tendsto_dialPathData_probe`), hence eventually enters the
open `Uprev`; the path that follows the dial after that entry time and sits at the base point
before it is in `Uprev` everywhere, so `hprev` realizes it, and its realizer agrees with the
dial for all large `τ`. -/
theorem dialProbe_mem_realizedTailPathSet_of_uniformTailRealize
    {Lθ Lfull : Nat} {θ'dial : Params (Lθ + 1) d} {b : ℝ}
    (δ : DialPathData (Params.headAttention θ'dial) b)
    {θfull : Params (Lfull + 1) d} {FullPaths : Set (ProbePath d)}
    (Uprev : Set (ProbePoint d)) (hUprev_open : IsOpen Uprev) (Tprev : ℝ)
    (hprev : UniformTailRealize r θfull FullPaths Uprev Tprev)
    (hbase : δ.base ∈ Uprev) :
    DialPathData.probe δ ∈ realizedTailPathSet r θfull FullPaths := by
  classical
  -- The dial converges to its base, which is interior to `Uprev`, so it eventually enters.
  have hev : ∀ᶠ τ in atTop, DialPathData.probe δ τ ∈ Uprev :=
    (tendsto_dialPathData_probe δ).eventually_mem (hUprev_open.mem_nhds hbase)
  obtain ⟨Tdial, hTdial⟩ := eventually_atTop.mp hev
  -- The parked path: follow the dial past its entry time, sit at the base point before it.
  set src : ProbePath d :=
    fun τ => if Tdial < τ then DialPathData.probe δ τ else δ.base with hsrc
  have hsrc_mem : ∀ τ : ℝ, Tprev < τ → src τ ∈ Uprev := by
    intro τ _hτ
    by_cases h : Tdial < τ
    · simp only [hsrc, if_pos h]; exact hTdial τ (le_of_lt h)
    · simp only [hsrc, if_neg h]; exact hbase
  obtain ⟨src2, hsrc2_mem, T2, _hT2, hsrc2_eff⟩ := hprev src hsrc_mem
  -- The realizer of the parked path realizes the dial itself past `max (max T2 Tdial) 0`.
  refine ⟨src2, hsrc2_mem,
    ⟨{ threshold := max (max T2 Tdial) 0
       threshold_nonneg := le_max_right _ _
       effective_eq := ?_ }⟩⟩
  intro τ hτ
  have hτT2 : T2 < τ :=
    lt_of_le_of_lt (le_trans (le_max_left T2 Tdial) (le_max_left _ _)) hτ
  have hτTd : Tdial < τ :=
    lt_of_le_of_lt (le_trans (le_max_right T2 Tdial) (le_max_left _ _)) hτ
  rw [hsrc2_eff τ hτT2]
  simp only [hsrc, if_pos hτTd]

/-- The base set `N.Uq` of a canonical product neighborhood lies in the node region `O`:
every `p ∈ N.Uq` pairs with some `t ∈ N.J` into the sign region (`texMatching_product_mem_signRegion`),
whose bases lie in `O` (`SignRegionData.point_mem_base`). -/
theorem texMatchingProductNeighborhood_Uq_subset_O
    {L : Nat} {θ' : Params (L + 1) d} {O : Set (ProbePair d)} {b : ℝ}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O (Params.headAttention θ') b)
    (T : TexTrichotomyConstructionData (L := L + 1) (d := d) b signRegion.U)
    (N : TexMatchingProductNeighborhoodData (d := d) (Params.headAttention θ') T.Ustar)
    {p : ProbePair d} (hp : p ∈ N.Uq) :
    p ∈ O := by
  obtain ⟨t, ht⟩ := N.J_nonempty
  exact signRegion.point_mem_base (p, t)
    (texMatching_product_mem_signRegion signRegion T N hp ht)

/-- **Realized-tail dial membership from the parent invariant.**  Every canonical
regular-quadric dial of a recursive node is a realized tail of `FullPaths`, provided the node
region `D.O` lies in the parent region `Uprev`.

In the threaded recursion every node satisfies `Uprev = D.O` definitionally (the parent passes
`tailData.O` as the child's `Uprev`), so the hypothesis `hDO` is discharged by `subset_rfl` at
each recursion site.  The dial bases live in `N.Uq ⊆ D.O` (`texMatchingProductNeighborhood_Uq_subset_O`),
hence in `Uprev`, and the parking trick finishes. -/
theorem texMatchingLocalPatchRegularQuadricDialRealizedTailMemObligation_of_uniformTailRealize_of_region_subset
    {L : Nat} (hL : 0 < L) (hr : 2 ≤ r)
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
    (Uprev : Set (ProbePoint d)) (hUprev_open : IsOpen Uprev) (Tprev : ℝ)
    (hprev : UniformTailRealize r θfull FullPaths Uprev Tprev)
    (hDO : D.O ⊆ Uprev) :
    TexMatchingLocalPatchRegularQuadricDialRealizedTailMemObligation
      hL hr hstep endpoint D localRegion θfull FullPaths := by
  dsimp [TexMatchingLocalPatchRegularQuadricDialRealizedTailMemObligation]
  intro p hp t ht
  refine dialProbe_mem_realizedTailPathSet_of_uniformTailRealize
    _ Uprev hUprev_open Tprev hprev ?_
  simp only [texMatchingRegularQuadricDialPathData_base]
  refine hDO ?_
  exact texMatchingProductNeighborhood_Uq_subset_O
    (texMatchingSignRegionData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D
      (texRegionConstructionData_of_IDLData_of_localPatch
        (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
    (texTrichotomyConstructionData_of_signRegion
      (L := L) (d := d) (r := r) hr hstep endpoint D
      (texMatchingSignRegionData_of_region
        (L := L) (d := d) (r := r) hr hstep endpoint D
        (texRegionConstructionData_of_IDLData_of_localPatch
          (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion)))
    (texMatchingProductNeighborhoodData_of_region
      (L := L) (d := d) (r := r) hr hstep endpoint D
      (texRegionConstructionData_of_IDLData_of_localPatch
        (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion))
    hp

/-- **`dial_mem` from the parent invariant.**  Composes the bridge with the existing
matching-side reduction to produce the local-patch dial-membership obligation `dial_mem`
itself, at a recursive realized-tail node where `D.Paths = realizedTailPathSet r θfull FullPaths`.
The only hypothesis beyond the threaded invariant is `D.O ⊆ Uprev` (`subset_rfl` in the threaded
recursion). -/
theorem texMatchingLocalPatchRegularQuadricDialMemObligation_of_uniformTailRealize_of_region_subset
    {L : Nat} (hL : 0 < L) (hr : 2 ≤ r)
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
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (Uprev : Set (ProbePoint d)) (hUprev_open : IsOpen Uprev) (Tprev : ℝ)
    (hprev : UniformTailRealize r θfull FullPaths Uprev Tprev)
    (hDO : D.O ⊆ Uprev) :
    TexMatchingLocalPatchRegularQuadricDialMemObligation
      hL hr hstep endpoint D localRegion :=
  texMatchingLocalPatchRegularQuadricDialMemObligation_of_realizedTailMemObligation
    (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion θfull FullPaths hPaths
    (texMatchingLocalPatchRegularQuadricDialRealizedTailMemObligation_of_uniformTailRealize_of_region_subset
      (L := L) (d := d) (r := r) hL hr hstep endpoint D localRegion θfull FullPaths
      Uprev hUprev_open Tprev hprev hDO)

/-- **Raw (trichotomy-explicit) realized-tail dial membership.**  The same parking-trick
content as `…_of_region_subset`, but for the raw `TexMatchingRegularQuadricDialMemObligation`
with an *explicit* trichotomy `T` and neighborhood `N`.  This is what feeds the genuine
matching bridge (`texMatchingDialPathLimitBridgeData_of_regularQuadricLimit`) for a genuine
`T`, mirroring the universal node's `texMatchingRegularQuadricDialMemObligation_of_paths_univ`
but for `D.Paths = realizedTailPathSet …`. -/
theorem texMatchingRegularQuadricDialMemObligation_of_uniformTailRealize_of_region_subset
    {L : Nat} {θ θ' : Params (L + 1) d} (D : IDLData (L + 1) d r θ θ')
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d) (Params.headAttention θ') T.Ustar)
    {θfull : Params (L + 2) d} {FullPaths : Set (ProbePath d)}
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (Uprev : Set (ProbePoint d)) (hUprev_open : IsOpen Uprev) (Tprev : ℝ)
    (hprev : UniformTailRealize r θfull FullPaths Uprev Tprev)
    (hDO : O ⊆ Uprev) :
    TexMatchingRegularQuadricDialMemObligation D signRegion T N := by
  intro p hp t ht
  rw [hPaths]
  refine dialProbe_mem_realizedTailPathSet_of_uniformTailRealize
    (texMatchingRegularQuadricDialPathData signRegion T N p hp t ht)
    Uprev hUprev_open Tprev hprev ?_
  simp only [texMatchingRegularQuadricDialPathData_base]
  exact hDO (texMatchingProductNeighborhood_Uq_subset_O signRegion T N hp)

/-- **Realized-tail first-layer matching support via the genuine trichotomy path.**  A copy of
`texFirstLayerMatchingAnalyticDataOfTrichotomy_of_cascadeBuilder_paths_univ_lowerDepthSelectedTail`
that takes the regular-quadric dial-membership obligation as a *parameter* `hdial_mem` rather than
deriving it from `D.Paths = Set.univ`.  This lets a recursive realized-tail node feed its own
`hdial_mem` (from `texMatchingRegularQuadricDialMemObligation_of_uniformTailRealize_of_region_subset`)
through the genuine matching bridge, exactly as the universal node does. -/
noncomputable def
    texFirstLayerMatchingAnalyticDataOfTrichotomy_of_cascadeBuilder_dialMem
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' θB : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    {A : Matrix (Fin d) (Fin d) ℝ}
    {Ustar : Set (ProbePair d × ℝ)}
    {unprimed primed : GateAlongBase d}
    (B : CascadeTrichotomyBuilderData
      (L := L + 1) (d := d) (Real.log (r : ℝ)) θB A signRegion.U Ustar
        unprimed primed)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ')
        (texTrichotomyConstructionData_of_cascadeBuilder B).Ustar)
    (S : TexMatchingSaturatedContributionData (L := L) (d := d) θ
      (texTrichotomyConstructionData_of_cascadeBuilder B).trichotomy.varsigma)
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (actual :
      TexTrichotomyMatchingCanonicalActualGateData
        (θ := θ) (θ' := θ') signRegion
        (texTrichotomyConstructionData_of_cascadeBuilder B) N)
    (hdial_mem :
      TexMatchingRegularQuadricDialMemObligation D signRegion
        (texTrichotomyConstructionData_of_cascadeBuilder B) N) :
    TexFirstLayerMatchingAnalyticDataOfTrichotomy hr hstep endpoint D := by
  let T := texTrichotomyConstructionData_of_cascadeBuilder B
  let hclosedBuilder :
      TexMatchingRegularQuadricClosedRecursionLimitObligation signRegion T N S := by
    simpa [T] using
      texMatchingRegularQuadricClosedRecursionLimitObligation_of_cascadeBuilder
        signRegion B N S hAA actual
  let hclosed :
      TexMatchingRegularQuadricClosedRecursionLimitObligation signRegion T N S :=
    hclosedBuilder
  let hlimit :
      TexMatchingRegularQuadricLimitVectorObligation signRegion T N S :=
    texMatchingRegularQuadricLimitVectorObligation_of_closedRecursionLimits
      (L := L) (d := d) (r := r) (by omega) signRegion T N S hclosed
  let bridge : TexMatchingDialPathLimitBridgeData D N S :=
    texMatchingDialPathLimitBridgeData_of_regularQuadricLimit
      (L := L) (d := d) (r := r) D signRegion T N S hdial_mem hlimit
  exact
    { signRegion := signRegion
      T := T
      neighborhood := N
      S := S
      bridge := bridge }

/-- Provider-facing realized-tail variant of
`texFirstLayerMatchingAnalyticDataOfTrichotomy_of_cascadeBuilder_dialMem`, mirroring
`texFirstLayerMatchingAnalyticDataOfTrichotomy_of_inductionProvider_paths_univ_lowerDepthSelectedTail`:
takes the dial-membership obligation as a parameter and delegates to the cascade-builder variant
through `P.toBuilderData`. -/
noncomputable def
    texFirstLayerMatchingAnalyticDataOfTrichotomy_of_inductionProvider_dialMem
    {L d r : Nat} (hr : 2 <= r)
    {θ θ' θB : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    {A : Matrix (Fin d) (Fin d) ℝ}
    {unprimed primed : GateAlongBase d}
    (P : CascadeTrichotomyInductionProviderData
      (L := L + 1) (d := d) (Real.log (r : ℝ)) θB A signRegion.U
        unprimed primed)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ')
        (texTrichotomyConstructionData_of_inductionProvider P).Ustar)
    (S : TexMatchingSaturatedContributionData (L := L) (d := d) θ
      (texTrichotomyConstructionData_of_inductionProvider P).trichotomy.varsigma)
    (hAA : Params.headAttention θ = Params.headAttention θ')
    (actual :
      TexTrichotomyMatchingCanonicalActualGateData
        (θ := θ) (θ' := θ') signRegion
        (texTrichotomyConstructionData_of_inductionProvider P) N)
    (hdial_mem :
      TexMatchingRegularQuadricDialMemObligation D signRegion
        (texTrichotomyConstructionData_of_inductionProvider P) N) :
    TexFirstLayerMatchingAnalyticDataOfTrichotomy hr hstep endpoint D :=
  texFirstLayerMatchingAnalyticDataOfTrichotomy_of_cascadeBuilder_dialMem
    (L := L) (d := d) (r := r) hr hstep endpoint D signRegion
    P.toBuilderData N S hAA actual hdial_mem

/-- **Genuine first-layer matching for a realized-tail node.**  Builds `FirstLayerMatchedData`
on the genuine induction-provider trichotomy — exactly the universal node's route
(`firstLayerMatched_of_texGenericStep_of_IDLData_trichotomy`) — but with the realized-tail dial
membership (our parking-trick `dial_mem`) supplied to the bridge instead of `_of_paths_univ`.

The genuine cascade `P`/`T`/`N`/`S`/`actual` are built from genericity alone (Paths-independent),
mirroring `texMatchingGenuineClosedRecursionLimitObligation_of_signRegion`; the only Paths-specific
input is `hdial_mem`, which our parking trick supplies from `hPaths` + `hprev` + `D.O ⊆ Uprev`. -/
noncomputable def realizedTailMatchedData_of_uniformTailRealize
    {L : Nat} (hd : 2 ≤ d) (hr : 2 ≤ r)
    {θ θ' : Params (L + 1) d}
    (hstep :
      TexGenericStepClauses L d (TexGeneric L d)
        (fun η => TexAnchorCertificate η) θ')
    (endpoint :
      FirstLayerEndpointData
        (Params.headAttention θ) (Params.headAttention θ')
        (Params.headValue θ))
    (D : IDLData (L + 1) d r θ θ')
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' D.O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    {θfull : Params (L + 2) d} {FullPaths : Set (ProbePath d)}
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (Uprev : Set (ProbePoint d)) (hUprev_open : IsOpen Uprev) (Tprev : ℝ)
    (hprev : UniformTailRealize r θfull FullPaths Uprev Tprev)
    (hDO : D.O ⊆ Uprev) :
    FirstLayerMatchedData θ θ' := by
  let P := genuineCascadeProvider_of_signRegion hd hstep endpoint signRegion (fun _ => 0)
  let T := texTrichotomyConstructionData_of_inductionProvider P
  let N :=
    texMatchingProductNeighborhoodData_of_trichotomy
      (L := L) (d := d) (r := r) hr hstep endpoint D signRegion T
  let S :=
    texMatchingSaturatedContributionData_of_inductionProvider
      (L := L) (d := d) (θ := θ) P
  let actual :=
    texTrichotomyMatchingCanonicalActualGateData_of_canonicalFrecGates
      (L := L) (d := d) (r := r) signRegion T N rfl rfl
  let hdial_mem :
      TexMatchingRegularQuadricDialMemObligation D signRegion T N :=
    texMatchingRegularQuadricDialMemObligation_of_uniformTailRealize_of_region_subset
      D signRegion T N hPaths Uprev hUprev_open Tprev hprev hDO
  let matchingTri :
      TexFirstLayerMatchingAnalyticDataOfTrichotomy hr hstep endpoint D :=
    texFirstLayerMatchingAnalyticDataOfTrichotomy_of_inductionProvider_dialMem
      hr hstep endpoint D signRegion P N S endpoint.attention_eq actual hdial_mem
  exact
    firstLayerMatched_of_texGenericStep_of_IDLData_trichotomy
      (L := L) (d := d) (r := r) hr hstep endpoint D matchingTri

end TransformerIdentifiability.NLayer
