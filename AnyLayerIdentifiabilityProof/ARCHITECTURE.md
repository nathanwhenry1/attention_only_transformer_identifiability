# Architecture & black-box guide

Map of the all-depth transformer-identifiability formalization, written so an agent can
orient **without opening the big files**. Read this first; for current status and the
remaining work see **`PLAN.md`** (these are the only two docs).

Namespace everywhere: `TransformerIdentifiability` / `TransformerIdentifiability.NLayer`.
Module *paths* carry the folder (e.g. `import AnyLayerIdentifiabilityProof.NLayer.Genericity.GenericityMain`)
but every `theorem`/`def` is referenced by its **bare name**. Build & audit commands are in
`PLAN.md`.

## What is proved

The natural-language proof is `n_layer_proof.tex` (Lean source root, ~3685 lines). The
public Lean theorem is `TransformerIdentifiability.identifiability` in `identifiability.lean`:

> For depth `L ≥ 1`, context multiplicity `r ≥ 2` (sequence length `r+1`), and dimension
> `d ≥ max 2 (C(L,2) + 2(L−1))`, there is a Lebesgue-null set `N` of parameters such that
> every `θ' ∉ N` is identified, among **all** parameters, by its network's input–output map.

This matches TeX `thm:main` exactly: same trusted model (`causalSoftmax`/`attnLayer`/
`transformer`/`Params` in `identifiability.lean`), same bound `d ≥ C(L,2)+2(L−1)`, same
null-set conclusion, and the exceptional set is the **exact** TeX generic set
`TexGenericBadSet` (complement of (G1)–(G4)), not an inflated cheat set. `identifiability.lean`
is the trusted base — verify that file by hand; everything else is proof infrastructure.

## The proof in one paragraph

Induction on depth `L`. For a TeX-generic `θ'` and an arbitrary `θ` agreeing with it on
probe observables: **Step 1** identifies the first attention matrix `A₁ = A₁'` (complex-
analytic singularity hierarchy); **Step 2** identifies the first value matrix `V₁ = V₁'` and
`B₁ = B₁'` (real-variable saturated-limit *trichotomy* + matching); **Step 3** *sweeps* the
first layer via an implicit-function/realization argument to produce a depth-`(L−1)` instance
on a fresh open region, and recurses. Genericity (the null exceptional set, anchors exist)
is a logically independent block. The spine is `IDL` (the strengthened inductive statement,
TeX `thm:IDL`).

## TeX proof structure (`n_layer_proof.tex`)

| Phase | TeX | Establishes |
|---|---|---|
| Model, probe family, recursion | §2 (`prop:probe` 216, `lem:peeling` 355, `lem:phi` 417) | probe input ⇒ 2D scalar recursion with sigmoid gates `s_ℓ = σ(τλ_ℓ+b)`; one-layer peeling; slope polynomials |
| Setup & main results | §3 (`def:anchor` 671, `def:generic` 688, `thm:main` 726, `thm:IDL` 712, `cor:factors` 767) | anchor sets `M_m`, genericity `𝒢^(L)` via (G1)–(G4), the theorems |
| Toolkit | §4 (`prop:strat` 1114, `lem:quadA` 1557, `lem:quadB` 1594, `lem:zariski` 1283) | stratification, quadric rigidity, Zariski lemmas |
| **Step 1** identify `A₁` | §5 (`prop:A1` 1751, `cor:depth` 1952) | (H) ⇒ `A₁=A₁'`; depth certificate `V₁≠0` |
| **Step 2** trichotomy & matching | §6 (`lem:cascade` 2164, `prop:trichotomy` 2323, `prop:matching` 2459) | gate limits `ς_j ∈ {0,1,α}`; `V₁=V₁'`, `B₁=B₁'`, `B_{L:1}=B'_{L:1}` |
| **Step 3** realization, sweep, induction | §7 (`lem:realization` 2598, `lem:sweep` 2858, proof of `thm:IDL` 2945) | every nearby path is realized; dial map covers an open set; the depth recursion |
| Genericity | §8 (`prop:anchorsexist` 3257, `prop:genericnonempty` 3304, `lem:witness` 3362) | anchors exist when `d ≥ N`; `𝒢^(L)` complement is null |

The crux is the **inductive step of `thm:IDL`** (3007–3062): genericity (G1)–(G4) + probe
agreement ⇒ matching data ⇒ sweep/realization ⇒ recurse one layer deeper.

## Lean directory layout = dependency layers (bottom → top)

Each subdirectory of `NLayer/` is one dependency layer; imports point downward.

| `NLayer/` dir | Modules | Status | What it gives you |
|---|---|---|---|
| `Foundations/` | `Core`, `PolynomialGenericity`, `ParamPolynomialGenericity`, `DominantTopCoeff` | 🔒 | Zariski/measure-zero lemmas (`mvpoly_eval_null'`), dominant-top-coefficient algebra (`HasDominantTopCoeff` + product closure) |
| `Analytic/` | `SlopePaths`, `AnchorGeneric`, `AnalyticToolkit`, `Stratification`, `AlgebraicQuadric`, `A1Identification`, `DivDiff`/`SigmoidTail`/`WeierstrassClosed`/`ExteriorConnected` (banked) | 🔒 | `BlowsUpAt`, pole-preimage, probe recursion / slope polynomials, skew-quadric endgame, `first_slope_eq_of_tier_descent` |
| `Genericity/` | `GenericityMain`, `TexGenericOpenDense`, `TexGenericNull`, `TexGenericMatrixClauses`, `TexGenericPolynomialCover`, `TexGenericConcrete`, `TexAnchorCertificateTopology` | 🔒 | `TexGenericSet` open/dense/co-null; `O_star`; `OStarGenericAssumptions` |
| `Step1/` | tier machinery — see **Step 1 detail** | 🔒 | the singularity hierarchy → `A₁=A₁'` (now discharged via the `A_gp` global-product route, see PLAN) |
| `IDL/` | `IDLStatement`, `IDLBase`, `DescentIDL`, `SaturationMatching`, `AnchorExistence`, `IDLStep1`, `MatchingCore`, `Cascade*` | 🔒 | IDL recursion data; Step-1 endpoint (`FirstLayerEndpointData`, `firstLayerEndpoint_of_texGenericStep_of_IDLData_globalProduct`); cascade trichotomy builders |
| `Step2/` | `IDLMatching` (~17.8k), `IDLSweep` (~7.7k), `SweepRealization`, `SweepWiring`; `RealizedTailMatching` (endgame) | 🔒 / 🔌 | `firstLayerMatched_*` (V₁=V₁'), sweep/realization wiring, the matching leaf machinery; **`RealizedTailMatching`** is the active frontier — holds the full genuine matching pipeline (`dial_mem` → `FirstLayerMatchedData`), axiom-clean; the remaining 3b wiring lives in `IdentifiabilityMain` (small top module, ~10s rebuild) |
| `NLayer/` root | `IdentifiabilityMain` (~5.6k), `NLayer.lean`, `Step1.lean` | 🔌 | `IDL_of_data` (induction on L), the leaf providers; the two `.lean` are import aggregators |

`NLayer.lean`, `NLayer/Step1.lean` are import aggregators (don't edit unless integrating).
Top-level entry: `identifiability.lean` → `IdentifiabilityProof` → `IdentifiabilityMain`.

## Keystone wiring (entry → conclusion) — COMPLETE

`identifiability.lean` (trusted model + public theorem)
→ `IdentifiabilityProof.identifiability_all_depth`
→ a chain of `identifiability_all_depth_of_*` reductions (all sorry-free)
→ `texGenericMainCurrentConstructorProvider` (`IdentifiabilityProof.lean`) — **now sorry-free**
→ (via helper `…_of_builderSelectedTailLeaves`) the leaf
   `NLayer.IDLReducedRealizedTailMatchingFrecProvider` (`IdentifiabilityMain.lean`), now holding a
   single `matching : FirstLayerMatchedData θ θ'` field, supplied by the leaf value
   `idlReducedRealizedTailMatchingFrecProvider_genuine`.

**The proof is complete and axiom-clean** (`#print axioms identifiability` =
`[propext, Classical.choice, Quot.sound]`). The genuine matching is built in
`Step2/RealizedTailMatching.lean`: `realizedTailMatchedData_of_uniformTailRealize` produces
`FirstLayerMatchedData` for a realized-tail node directly (parking-trick `dial_mem` + the genuine
trichotomy). The R5 step-3b refactor collapsed the leaf record's two fake-`T` fields to that single
`matching`, rewired all consumers to read it (`FirstLayerMatchedData` is a Prop, so this is
proof-irrelevance-safe), and discharged the `sorry`. See `PLAN.md` for the closing detail.

## TeX ↔ Lean correspondence (Step 1)

| TeX (`n_layer_proof.tex`) | File | Key declarations |
|---|---|---|
| Good probe selection, `O_star` | Genericity cluster + `Step1/OStar` | `FixedOStarProbe`, `OStarGenericAssumptions` |
| Nested polynomial regions, family `{f,g}` | `Step1/NestedLargeness`, `Step1/PolynomialFamily` | `NestedTailFamily`, `PolynomialNestedTailData`, `step1GlobalProductPoly` |
| Tier sets `T_j`, `T_j^0` | `Step1/TierSets` | `TierSystem`, `tierSet`/`zeroFreeTierSet`, `mem_T0_succ` |
| Claim B (tier accumulation) | `Step1/Propagation`, `IDL/IDLStep1` | `ZeroFreeDecoupledPropagationData`, the `A_gp` global-product chain |
| Claim C (last-tier blow-up) | `Step1/LastTierBlowup` + `IDL/IDLStep1` | `ZeroFreeLastTierBlowup`, `fixedOStar_globalProductTierSystem_H_blowsUpAt` |
| Claim D (transfer) | `Step1/Transfer` | `transferred_zeroFreeLastTier_subset_partialUnion_*` |
| Descent → `A₁=A₁'` | `A1Identification`, `Step1/DescentConclusion`, `IDL/IDLStep1` | `first_slope_eq_of_tier_descent`, `fixedOStar_globalProduct_step1Conclusion_of_OStar_genericity` |
| Depth certificate `V₁≠0` | `Step1/DepthCertificate` | depth-drop wrappers |

## TeX ↔ Lean correspondence (Steps 2–3)

| TeX | File | Key declarations |
|---|---|---|
| `lem:cascade` / `prop:trichotomy` (gate limits) | `IDL/CascadeTrichotomy*`, `Step2/IDLMatching` (genuine route at `:3159`) | `cascadeTrichotomyInductionProviderData_of_…_productPatchZeroBranch`, `texTrichotomyConstructionData_of_inductionProvider` |
| `prop:matching` closed-recursion limits | `IDL/MatchingCore`, `Step2/IDLMatching` | `TexMatchingRegularQuadricClosedRecursionLimitObligation`, `texMatchingGenuineClosedRecursionLimitObligation_of_signRegion` |
| `lem:realization` / `lem:sweep` | `Step2/SweepRealization`, `Step2/SweepWiring`, `Step2/IDLSweep` | `UniformTailRealize`, `texSweepCanonicalIFTData_of_IDLData_matching_realizedTail` |
| `dial_mem` (realized-tail dial membership; parking trick) | `Step2/RealizedTailMatching` | `dialProbe_mem_realizedTailPathSet_of_uniformTailRealize`, `texMatchingRegularQuadricDialMemObligation_of_uniformTailRealize_of_region_subset` |
| genuine first-layer matching — univ route | `Step2/IDLMatching` | `TexFirstLayerMatchingAnalyticDataOfTrichotomy`, `firstLayerMatched_of_texGenericStep_of_IDLData_trichotomy` |
| genuine first-layer matching — realized-tail route | `Step2/RealizedTailMatching` | `realizedTailMatchedData_of_uniformTailRealize` (→ `FirstLayerMatchedData`), `…AnalyticDataOfTrichotomy_of_{cascadeBuilder,inductionProvider}_dialMem` |
| anchors / null genericity (§8) | `IDL/AnchorExistence`, `Genericity/*` | `mainTheoremExceptionalSet_null`, `texGenericBadSet_null` |

## Step 1 detail (`Step1/`)

| File | Role / interface |
|---|---|
| `OStar` | `FixedOStarProbe r L d O θ θ'` — the fixed generic probe; standing-assumption accessors |
| `ConcreteStratification` | geometric stratification `ConcreteStratification m` (~2.5k lines behind ~15 lemmas) |
| `NestedLargeness` | `TailPresentation`, `PolynomialNestedTailData`, `lastVariablePolynomial` |
| `PolynomialFamily` | the `f`/`g` polynomials + leading coeffs; `step1GlobalProductPoly` (global-product tower) |
| `TierSets` | `TierSystem = (stratification, nestedFamily)`; `T`/`T0` access API |
| `Propagation` | Claim-B engine; `ZeroFreeDecoupledPropagationData` ⇒ `ZeroFreeTierPropagation` |
| `LastTierBlowup` | Claim C: `ZeroFreeLastTierBlowup`, `TierSystem.ofPolynomialNestedTailData` |
| `Transfer` | Claim D: real-tail-agreement transfer into the unprimed singular set |
| `DescentConclusion` | `ZeroFreeConcreteDescentData`, the Zariski wrappers up to `Step1Conclusion`/`firstAttention_eq` |
| `DepthCertificate` | depth-drop / `V₁=0` machinery |

## "If your task is …, read / skip"

- **Step 2 matching / cascade** → `Step2/IDLMatching`, `IDL/Cascade*`, `IDL/MatchingCore`,
  `IDL/IDLStatement`. Black-box: `Step1/` internals (consume `FirstLayerEndpointData`).
- **Step 3 sweep / realization** → `Step2/{SweepRealization,SweepWiring,IDLSweep}`. Black-box: the rest.
- **Top-level / recursion / the leaf** → `IdentifiabilityMain`, `IdentifiabilityProof`. Black-box: per-step proofs.
- **Genericity / `O_star`** → `Genericity/`. Black-box: everything else.

## Navigation pain points

- Very large files: `Step2/IDLMatching` (~17.8k), `IDL/IDLStep1` & `Step2/IDLSweep` (~7.7–9k),
  `IdentifiabilityMain` (~5.6k). Editing any triggers a slow rebuild. Navigate by signature:
  `grep -n "^theorem\|^def\|^structure\|^noncomputable def\|^/-! " <file>`.
  **Endgame frontier:** `Step2/RealizedTailMatching.lean` (a small *top* module, ~10s rebuild) holds
  the full genuine matching pipeline (`dial_mem` → `FirstLayerMatchedData`, axiom-clean). The only
  remaining work is the **3b wiring refactor in `IdentifiabilityMain`** (change the leaf record to hold
  `matching`, rewire the ~7 fake-`T`-chain consumers to read it, fill the `sorry`) — see `PLAN.md`
  §Wiring / work order step 4. The clean route keeps the big files whole (no in-place fake-`T` retype).
- Stray files NOT on the `identifiability` build path — ignore: `AnyLayerIdentifiabilityProof/{2_layer_identifiability,TwoLayerIdentifiability,Basic}.lean`, repo-root `2_layer_*`, `1_layer_proof.tex`, `proof.tex`.
- Two parallel cascade developments exist: the **integrated** route in `Step2/IDLMatching`
  (`…productPatchZeroBranch`, used by the proof) vs. the **separate, currently-unimported**
  `IDL/Cascade*.lean` additive files. The proof depends only on the integrated route.
