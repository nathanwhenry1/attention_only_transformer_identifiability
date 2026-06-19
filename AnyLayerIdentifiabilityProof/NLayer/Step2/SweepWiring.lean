import AnyLayerIdentifiabilityProof.NLayer.Step2.SweepRealization

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

open scoped Matrix Topology
open scoped Matrix.Norms.Frobenius

/-!
# Wiring the sweep frontier at the top (universal-path) node

This file connects the analytic core proved in
`AnyLayerIdentifiabilityProof/NLayer/Step2/SweepRealization.lean`
(`sweep_pointwise_realization_open`, sorry-free) to the sweep frontier data structure
`TexSweepCanonicalIFTData` consumed by the descent assembly.

Given an `IDLData (L + 2) d r θ θ'` whose first layers match (`FirstLayerMatchedData θ θ'`)
and whose path class is universal (`D.Paths = Set.univ`), together with a full-depth
unwound anchor `p` (`hpO : p ∈ D.O`, `W : AnchorUnwindingData θ' p`), we:

1. read off, at the first anchor gate `k = 0`, the hypotheses of
   `sweep_pointwise_realization_open` for `θ'` (vanishing quadric, nonzero Jacobian scalar,
   nonsingular step matrix; the first-skip determinant comes from `D.primed_generic`'s
   `(G3)` clause);
2. transfer them across `matching` to `V := Params.headValue θ`,
   `A := Params.headAttention θ`;
3. apply `sweep_pointwise_realization_open` to obtain an open neighborhood `U` of the full
   anchor's transported tail point `firstLayerDialPoint V (W.t 0) p.1 p.2`, on which every
   target is realized for all large `τ`;
4. assemble this into the near-anchor realization theorem
   (`texSweepLocalRealizationNearAnchorPoint_of_IDLData_matching`), with `D.Paths = Set.univ`
   making the source-path-membership obligation automatic.

The frontier `TexSweepCanonicalIFTData D` is then produced by bridging the full-anchor data
through `texSweepCanonicalIFTData_of_fullAnchorLocalRealizationData_compatible`.

## The full-anchor / canonical-anchor compatibility (the one added hypothesis)

`TexSweepCanonicalIFTData D` is *defined* at the canonical tail anchor
`texSweepAnchorPointData_of_IDLData D`, whose point is obtained by `Classical.choose` from
`Set.univ ∩ unwoundAnchorSet (Params.tail θ')`.  Our realization neighborhood is instead
centered at the transport of the supplied full anchor `W`.  Identifying these two
tail-anchor points is the "canonical anchor vs. full anchor" subtlety flagged as out of
scope in `SweepRealization.lean`.

We discharge everything *except* this identification.  The identification is exposed as the
explicit hypothesis `TexSweepFullAnchorChoiceCompatible D W`
(`= (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point =
     (texSweepAnchorPointData_of_IDLData D).point`).  This is exactly the witness the
repository's bridge `texSweepCanonicalIFTData_of_fullAnchorLocalRealizationData_compatible`
consumes, and it is the honest hypothesis used elsewhere in the descent (the alternative
`TexSweepTailAnchorUnique D` is *provably false* at a depth-one tail, so it can never be
discharged at the base of the recursion and is deliberately avoided here).

The genuinely unconditional content — realization of a neighborhood of the *full* anchor's
transported tail point — is the lemma
`texSweepLocalRealizationNearAnchorPoint_of_IDLData_matching` (and the packaged
`texSweepFullAnchorLocalRealizationData_of_IDLData_matching*`), which take no compatibility
or uniqueness hypothesis at all.
-/

/-- **Unconditional near-anchor realization at an explicit full anchor.**

From a matched first layer, a universal path class, and an explicitly supplied full-depth
unwound anchor `W : AnchorUnwindingData θ' p` with `p ∈ D.O`, the sweep realization is
realized on an open neighborhood of `W`'s transported tail point.  This is the honest
analytic output, with no compatibility or uniqueness hypothesis.

The proof reads the `sweep_pointwise_realization_open` hypotheses off `W` at gate `k = 0`,
transfers them across `matching`, applies the realization theorem, and — using
`D.Paths = Set.univ` to discharge source-path membership — packages each pointwise preimage
into the required realization record. -/
theorem texSweepLocalRealizationNearAnchorPoint_of_IDLData_matching
    {L d r : ℕ} {θ θ' : Params (L + 2) d}
    (D : IDLData (L + 2) d r θ θ')
    (matching : FirstLayerMatchedData θ θ')
    (hPaths : D.Paths = Set.univ)
    {p : AnchorProbe d} (W : AnchorUnwindingData θ' p) :
    TexSweepLocalRealizationNearAnchorPoint D
      (texSweepAnchorPointData_of_fullUnwoundAnchor D W) := by
  classical
  -- Step 1: realization hypotheses for `θ'` at the first anchor gate `k = 0`.
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
  -- Step 2: transfer the hypotheses across `matching` to the unprimed first layer.
  have hq : matrixBilin (Params.headAttention θ) p.1 p.2 = 0 := by
    simpa [matching.headAttention_eq] using hq'
  have hvartheta :
      texSweepVartheta0 (Params.headValue θ) (Params.headAttention θ) p (W.t 0) ≠ 0 := by
    simpa [matching.headValue_eq, matching.headAttention_eq] using hvartheta'
  -- `Msolve V t` is defeq `anchorStepMatrix (fun _ => (V, A)) 0 t`.
  have hMt : (Msolve (Params.headValue θ) (W.t 0)).det ≠ 0 := by
    change (anchorStepMatrix
      (fun _ => (Params.headValue θ, Params.headAttention θ)) 0 (W.t 0)).det ≠ 0
    simpa [matching.headValue_eq, matching.headAttention_eq] using hdetStep'
  -- The first-skip determinant is the generic `(G3)` clause of `D.primed_generic`,
  -- transferred to the matched first value matrix.
  have hstep : TexGenericStepClauses (L + 1) d (TexGeneric (L + 1) d)
      (fun η => TexAnchorCertificate η) θ' := D.primed_generic
  have hB : (skipB (Params.headValue θ)).det ≠ 0 :=
    headValueSkip_det_ne_zero_of_matching hstep matching
  -- The full anchor's transported tail point is the dial center of the realization.
  have hcenter_eq : firstLayerDialPoint (Params.headValue θ) (W.t 0) p.1 p.2 =
      (texSweepAnchorPointData_of_fullUnwoundAnchor D W).point := by
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
  -- Steps 3-4: apply `sweep_pointwise_realization_open` and assemble the near-anchor
  -- realization theorem.
  obtain ⟨U, hUopen, hcenter, T, hT, hreal⟩ :=
    sweep_pointwise_realization_open r (Params.headValue θ) (Params.headAttention θ)
      p.1 p.2 (W.t 0) htIoo.1 htIoo.2 hB hMt hq hvartheta
  refine ⟨U, hUopen, hcenter_eq ▸ hcenter, ?_⟩
  intro η hη
  -- A pointwise preimage `(w, v)` exists for every large `τ`; choose one per `τ`.
  have hTτ' : ∀ τ : ℝ, T < τ → ∃ pp : ProbePoint d,
      firstLayerEffectivePoint r (Params.headValue θ) (Params.headAttention θ)
        pp.1 pp.2 τ = η := by
    intro τ hτ
    obtain ⟨w, v, hwv⟩ := hreal η hη τ hτ
    exact ⟨(w, v), hwv⟩
  refine ⟨fun τ => if h : T < τ then (hTτ' τ h).choose else (0, 0), ?_, ?_⟩
  · -- source ∈ D.Paths is automatic since `D.Paths = Set.univ`.
    rw [hPaths]; trivial
  · refine ⟨texSweepRealizationData_of_eventually_effective_eq (θ := θ) η _ T hT ?_⟩
    intro τ hτ
    simp only [hτ, dif_pos]
    exact (hTτ' τ hτ).choose_spec

/-- **Unconditional full-anchor sweep frontier from an explicit anchor.**

Packages `texSweepLocalRealizationNearAnchorPoint_of_IDLData_matching` as
`TexSweepFullAnchorLocalRealizationData D` carrying `unwinding := W`, so callers can pair it
with a `TexSweepFullAnchorChoiceCompatible D W` witness for that same anchor.  Still fully
unconditional. -/
noncomputable def texSweepFullAnchorLocalRealizationData_of_IDLData_matching_of_anchor
    {L d r : ℕ} {θ θ' : Params (L + 2) d}
    (D : IDLData (L + 2) d r θ θ')
    (matching : FirstLayerMatchedData θ θ')
    (hPaths : D.Paths = Set.univ)
    {p : AnchorProbe d} (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p) :
    TexSweepFullAnchorLocalRealizationData D :=
  texSweepFullAnchorLocalRealizationData_of_fullUnwoundAnchor_nearAnchorPoint hpO W
    (texSweepLocalRealizationNearAnchorPoint_of_IDLData_matching D matching hPaths W)

/-- **Unconditional full-anchor sweep frontier (anchor selected internally).**

Specialization that selects a full anchor from `D.anchor_nonempty` (the `L + 2 ≠ 1`
branch).  Still fully unconditional; the selected anchor is internal, so to bridge to the
canonical frontier one should instead use `texSweepCanonicalIFTData_of_IDLData_matching`
with the explicit anchor and its compatibility witness. -/
noncomputable def texSweepFullAnchorLocalRealizationData_of_IDLData_matching
    {L d r : ℕ} {θ θ' : Params (L + 2) d}
    (D : IDLData (L + 2) d r θ θ')
    (matching : FirstLayerMatchedData θ θ')
    (hPaths : D.Paths = Set.univ) :
    TexSweepFullAnchorLocalRealizationData D := by
  classical
  have hanchor : (D.O ∩ unwoundAnchorSet θ').Nonempty := by
    rcases D.anchor_nonempty with h | h
    · omega
    · exact h
  have hp : Classical.choose hanchor ∈ D.O ∩ unwoundAnchorSet θ' := Classical.choose_spec hanchor
  exact texSweepFullAnchorLocalRealizationData_of_IDLData_matching_of_anchor D matching hPaths
    hp.1 (Classical.choice (mem_unwoundAnchorSet.mp hp.2))

/-- **The sweep frontier at the top (universal-path) node.**

From a matched first layer (`FirstLayerMatchedData θ θ'`), a universal path class
(`D.Paths = Set.univ`), an explicit full-depth unwound anchor `W : AnchorUnwindingData θ' p`
with `p ∈ D.O`, and the full-anchor/canonical compatibility witness
`TexSweepFullAnchorChoiceCompatible D W`, the analytic sweep realization assembles into the
canonical sweep frontier `TexSweepCanonicalIFTData D`.

All hypotheses except the compatibility witness are discharged by
`texSweepLocalRealizationNearAnchorPoint_of_IDLData_matching` (see its docstring and the
module docstring for why the compatibility witness is the single honest addition).
`hr : 2 ≤ r` is part of the intended interface but is not needed by the analytic core. -/
noncomputable def texSweepCanonicalIFTData_of_IDLData_matching
    {L d r : ℕ} (_hr : 2 ≤ r) {θ θ' : Params (L + 2) d}
    (D : IDLData (L + 2) d r θ θ')
    (matching : FirstLayerMatchedData θ θ')
    (hPaths : D.Paths = Set.univ)
    {p : AnchorProbe d} (hpO : p ∈ D.O) (W : AnchorUnwindingData θ' p)
    (hcompat : TexSweepFullAnchorChoiceCompatible D W) :
    TexSweepCanonicalIFTData D :=
  -- The full-anchor package is passed directly (not via a `have`), so its `.unwinding`
  -- projection reduces to `W` and `hcompat` is accepted verbatim.
  texSweepCanonicalIFTData_of_fullAnchorLocalRealizationData_compatible D
    (texSweepFullAnchorLocalRealizationData_of_fullUnwoundAnchor_nearAnchorPoint hpO W
      (texSweepLocalRealizationNearAnchorPoint_of_IDLData_matching D matching hPaths W))
    hcompat

/-- **The sweep frontier at the top (universal-path) node — fully unconditional.**

From a matched first layer (`FirstLayerMatchedData θ θ'`) and a universal path class
(`D.Paths = Set.univ`) alone, the analytic sweep realization assembles into the canonical
sweep frontier `TexSweepCanonicalIFTData D`.  No anchor, compatibility, or tail-anchor
uniqueness witness is needed:

* the explicit anchor is the canonical `idlChosenFullAnchor D`, whose source point lies in
  `D.O` by `idlChosenFullAnchor_fst_mem_O` (the geometric disjunct of `D.anchor_nonempty`,
  available since the tail depth `L + 1 ≥ 1`);
* the full-anchor/canonical compatibility is definitional
  (`texSweepFullAnchorChoiceCompatible_idlChosenFullAnchor`), because the canonical anchor is
  *defined* to transport `idlChosenFullAnchor D` — this is the item-1 realignment of
  `SWEEP_PLAN.md`, faithful to the TeX (concrete transported anchor `Φ_t(p)`), and it avoids
  the depth-one-false `TexSweepTailAnchorUnique`.

This is the honest top-node entry point that discharges the canonical sweep frontier from
matching, ready to fill the `canonicalIFT` field at the universal current node. -/
noncomputable def texSweepCanonicalIFTData_of_IDLData_matching_univ
    {L d r : ℕ} (hr : 2 ≤ r) {θ θ' : Params (L + 2) d}
    (D : IDLData (L + 2) d r θ θ')
    (matching : FirstLayerMatchedData θ θ')
    (hPaths : D.Paths = Set.univ) :
    TexSweepCanonicalIFTData D := by
  classical
  have hanchor : (D.O ∩ unwoundAnchorSet θ').Nonempty :=
    D.anchor_nonempty.resolve_left (by omega)
  exact
    texSweepCanonicalIFTData_of_IDLData_matching hr D matching hPaths
      (idlChosenFullAnchor_fst_mem_O D hanchor) (idlChosenFullAnchor D).2
      (texSweepFullAnchorChoiceCompatible_idlChosenFullAnchor D)

/-! ## The sweep frontier at a recursive realized-tail node (`FullPaths = univ`)

The realized-tail analogue of `texSweepCanonicalIFTData_of_IDLData_matching_univ`.  At the
first recursive node the path class is `realizedTailPathSet r θfull Set.univ`, so the
realization's lifted sources are free.  The current-node sweep data is extracted from the
chosen full anchor and `matching` exactly as at the universal node; the genuinely recursive
input is a uniform realization of the *previous* layer `θfull` on an open region `Uprev`
containing the chosen anchor's source point.  The cross-layer composition
(`texSweepUniformDialInverseData_of_realizedTail_controlled`, built on the source-controlled
realization `sweep_pointwise_realization_open_controlled`) then closes the frontier. -/

/-- **The sweep frontier at a recursive realized-tail node (`FullPaths = univ`).**

Produces `TexSweepCanonicalIFTData D` for a node with
`D.Paths = realizedTailPathSet r θfull Set.univ` from the matched first layer plus a uniform
realization of the previous layer `θfull` on an open `Uprev ∋` the chosen anchor's source.
The remaining hypotheses (`Uprev` realizing the previous layer; the anchor lying in `Uprev`)
are the *recursive* input — they come from the previous node's realization and the threaded
anchor.  All current-node sweep data is discharged unconditionally (item-1 realignment). -/
noncomputable def texSweepCanonicalIFTData_of_IDLData_matching_realizedTail_univ
    {L Lfull d r : ℕ} (_hr : 2 ≤ r) {θ θ' : Params (L + 2) d}
    {θfull : Params (Lfull + 1) d}
    (D : IDLData (L + 2) d r θ θ')
    (matching : FirstLayerMatchedData θ θ')
    (hPaths : D.Paths = realizedTailPathSet r θfull Set.univ)
    (Uprev : Set (ProbePoint d)) (hUprev_open : IsOpen Uprev)
    (hanchor_mem : (idlChosenFullAnchor D).1 ∈ Uprev)
    (Tprev : ℝ)
    (hprev : ∀ q ∈ Uprev, ∀ τ : ℝ, Tprev < τ →
      ∃ w' v' : Fin d → ℝ,
        firstLayerEffectivePoint r (Params.headValue θfull) (Params.headAttention θfull)
          w' v' τ = q) :
    TexSweepCanonicalIFTData D := by
  classical
  set p : AnchorProbe d := (idlChosenFullAnchor D).1 with hp
  set W : AnchorUnwindingData θ' p := (idlChosenFullAnchor D).2 with hW
  -- Current-node sweep hypotheses at the chosen anchor, transferred across `matching`.
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
  -- The current dial center is the canonical anchor (item-1 realignment makes this so).
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
  -- Compose the source-controlled current realization with the previous realization.
  -- (The conclusion of the wiring lemma is a `Prop` existential, so extract by choice.)
  have hex :=
    texSweepUniformDialInverseData_of_realizedTail_controlled D hPaths p.1 p.2 (W.t 0)
      htIoo.1 htIoo.2 hB hMt hq hvartheta Uprev hUprev_open hanchor_mem Tprev hprev
  let U : Set (ProbePoint d) := Classical.choose hex
  have hspec :
      IsOpen U ∧ firstLayerDialPoint (Params.headValue θ) (W.t 0) p.1 p.2 ∈ U ∧
        TexSweepUniformDialInverseData D U :=
    Classical.choose_spec hex
  exact texSweepCanonicalIFTData_of_uniformDialInverseData D U hspec.1
    (hcenter_eq ▸ hspec.2.1) hspec.2.2

/-! ## The sweep frontier at a recursive realized-tail node (arbitrary `FullPaths`)

The depth-induction generalization of
`texSweepCanonicalIFTData_of_IDLData_matching_realizedTail_univ`
from `FullPaths = Set.univ` (the first recursive node) to **arbitrary** `FullPaths` (every
recursive depth).  The genuinely recursive input is the *path-level* previous-layer
realization invariant `UniformTailRealize r θfull FullPaths Uprev Tprev` (proved in
`SweepRealization.lean` to be preserved by the source-controlled current-layer realization),
together with the threaded anchor membership `(idlChosenFullAnchor D).1 ∈ Uprev`.  All
current-node sweep data is discharged unconditionally from `matching` and the chosen anchor
exactly as at the universal node (item-1 realignment).

The producer threads the invariant: alongside `TexSweepCanonicalIFTData D` it exposes the
*current* node's invariant `UniformTailRealize r θ D.Paths U Tcurr` on an open `U` containing
the canonical anchor point, ready to feed the next recursive depth (the only residual being
the anchor membership `(idlChosenFullAnchor tailNode).1 ∈ U`, TeX step (3)'s `p♭ ∈ Õ`). -/

/-- **Threaded current-node invariant at a recursive realized-tail node.**

From the matched first layer, `D.Paths = realizedTailPathSet r θfull FullPaths`, and the
*path-level* previous-layer invariant on `Uprev ∋ (idlChosenFullAnchor D).1`, produce an open
`U` containing the canonical anchor point on which the current node's path-level invariant
`UniformTailRealize r θ D.Paths U Tcurr` holds.  This is the object threaded through the
recursion: the current node's `U`/invariant becomes the next node's `Uprev`/`hprev`.

The proof reads the current node's sweep hypotheses off the chosen full anchor (transferred
across `matching`) exactly as the universal node does, then applies the preservation step
`uniformTailRealize_step`. -/
theorem uniformTailRealize_currentNode_of_IDLData_matching
    {L Lfull d r : ℕ} (_hr : 2 ≤ r) {θ θ' : Params (L + 2) d}
    {θfull : Params (Lfull + 1) d}
    (D : IDLData (L + 2) d r θ θ')
    (matching : FirstLayerMatchedData θ θ')
    {FullPaths : Set (ProbePath d)}
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (Uprev : Set (ProbePoint d)) (hUprev_open : IsOpen Uprev)
    (hanchor_mem : (idlChosenFullAnchor D).1 ∈ Uprev)
    (Tprev : ℝ)
    (hprev : UniformTailRealize r θfull FullPaths Uprev Tprev) :
    ∃ U : Set (ProbePoint d), IsOpen U ∧
      (texSweepAnchorPointData_of_IDLData D).point ∈ U ∧
      ∃ Tcurr : ℝ, UniformTailRealize r θ D.Paths U Tcurr := by
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
  obtain ⟨U, hUopen, hcenter, Tcurr, _hTcurr, hinv⟩ :=
    uniformTailRealize_step r θ θfull FullPaths p.1 p.2 (W.t 0)
      htIoo.1 htIoo.2 hB hMt hq hvartheta Uprev hUprev_open hanchor_mem Tprev hprev
  refine ⟨U, hUopen, hcenter_eq ▸ hcenter, Tcurr, ?_⟩
  rw [hPaths]
  exact hinv

/-- **The sweep frontier at a recursive realized-tail node (arbitrary `FullPaths`).**

Produces `TexSweepCanonicalIFTData D` for a node with
`D.Paths = realizedTailPathSet r θfull FullPaths` (any `FullPaths`) from the matched first
layer plus the path-level previous-layer realization invariant on `Uprev ∋
(idlChosenFullAnchor D).1`.  Specializes the threaded current-node invariant
(`uniformTailRealize_currentNode_of_IDLData_matching`) to constant targets and packages it
through `texSweepCanonicalIFTData_of_uniformDialInverseData`.

This is the depth-induction generalization of
`texSweepCanonicalIFTData_of_IDLData_matching_realizedTail_univ` (its `FullPaths = Set.univ`
special case, whose path-level invariant is supplied by `uniformTailRealize_univ_of_pointwise`). -/
noncomputable def texSweepCanonicalIFTData_of_IDLData_matching_realizedTail
    {L Lfull d r : ℕ} (hr : 2 ≤ r) {θ θ' : Params (L + 2) d}
    {θfull : Params (Lfull + 1) d}
    (D : IDLData (L + 2) d r θ θ')
    (matching : FirstLayerMatchedData θ θ')
    {FullPaths : Set (ProbePath d)}
    (hPaths : D.Paths = realizedTailPathSet r θfull FullPaths)
    (Uprev : Set (ProbePoint d)) (hUprev_open : IsOpen Uprev)
    (hanchor_mem : (idlChosenFullAnchor D).1 ∈ Uprev)
    (Tprev : ℝ)
    (hprev : UniformTailRealize r θfull FullPaths Uprev Tprev) :
    TexSweepCanonicalIFTData D := by
  classical
  -- The threaded current-node invariant is a `Prop` existential, so extract `U` by choice.
  have hex :=
    uniformTailRealize_currentNode_of_IDLData_matching hr D matching hPaths
      Uprev hUprev_open hanchor_mem Tprev hprev
  set U : Set (ProbePoint d) := Classical.choose hex with hU
  have hspec :
      IsOpen U ∧ (texSweepAnchorPointData_of_IDLData D).point ∈ U ∧
        ∃ Tcurr : ℝ, UniformTailRealize r θ D.Paths U Tcurr :=
    Classical.choose_spec hex
  refine texSweepCanonicalIFTData_of_uniformDialInverseData D U hspec.1 hspec.2.1 ?_
  intro η hη
  obtain ⟨_Tcurr, hinv⟩ := hspec.2.2
  obtain ⟨src, hsrc_mem, T', _hT', heff⟩ :=
    hinv (constantProbePath η) (fun τ _ => by rw [constantProbePath_apply]; exact hη)
  refine ⟨src, hsrc_mem, max 0 T', le_max_left _ _, fun τ hτ => ?_⟩
  have h := heff τ (lt_of_le_of_lt (le_max_right 0 T') hτ)
  rwa [constantProbePath_apply] at h

end TransformerIdentifiability.NLayer
