import AnyLayerIdentifiabilityProof.NLayer.IDL.CascadeBridge

set_option autoImplicit false

open Filter Topology Matrix

namespace TransformerIdentifiability.NLayer

/-!
# Shared matching core for IDL cascade modules

This file owns the lightweight matching-vector definitions and Frec asymptotic
obligation interfaces needed by the cascade matching layer.  It deliberately stays
upstream of `Step2.IDLMatching`.
-/

/-- Output of TeX Proposition `trichotomy`, separated from the later coefficient
comparison.  This selects the actual gate functions, the refined component `Ustar`,
and the trichotomy constants/asymptotics on that component. -/
structure TexTrichotomyConstructionData {L d : Nat} (b : ℝ)
    (signU : Set (ProbePair d × ℝ)) where
  unprimed : GateAlongBase d
  primed : GateAlongBase d
  Ustar : Set (ProbePair d × ℝ)
  trichotomy : TrichotomyData (L := L) (d := d) b signU Ustar unprimed primed

/-- Product neighborhood chosen in Step 0 of TeX Proposition `matching`. -/
structure TexMatchingProductNeighborhoodData {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (Ustar : Set (ProbePair d × ℝ)) where
  Uq : Set (ProbePair d)
  J : Set ℝ
  Uq_nonempty : Uq.Nonempty
  J_nonempty : J.Nonempty
  J_open : IsOpen J
  Uq_on_quadric : ∀ p ∈ Uq, firstLayerQuadric A p
  product_subset :
    {x : ProbePair d × ℝ | x.1 ∈ Uq ∧ x.2 ∈ J} ⊆ Ustar
  coefficient_separation :
    ∀ (M : Matrix (Fin d) (Fin d) ℝ)
      (R : ℝ -> Matrix (Fin d) (Fin d) ℝ),
      (∀ p : ProbePair d, p ∈ Uq -> ∀ t : ℝ, t ∈ J ->
        Matrix.mulVec M p.2 + Matrix.mulVec (R t) p.1 = 0) ->
        (∀ v : Fin d -> ℝ, Matrix.mulVec M v = 0) ∧
          (∀ t : ℝ, t ∈ J -> R t = 0)

/-- Real matrix obtained by taking entrywise real parts of a complex matrix. -/
noncomputable def realPartMatrix {d : Nat} (M : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (M i j).re

/-- The saturated lower-layer matrix `D` from Step 1 of TeX Proposition `matching`,
expressed as the formal accumulated transfer through the tail at the trichotomy
constants. -/
noncomputable def texMatchingSaturatedContributionMatrix {L d : Nat}
    (θ : Params (L + 1) d) (varsigma : Nat -> ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  realPartMatrix
    (formalT (paramStream (Params.tail θ)) L fun n => (varsigma (n + 1) : ℂ))

/-- The saturated lower-layer matrix `D` from Step 1 of TeX Proposition `matching`.
The later coefficient lemmas use `realSkipBprod (Params.tail θ) L - D` as the matrix
called `K` in Step 6. -/
structure TexMatchingSaturatedContributionData {L d : Nat}
    (θ : Params (L + 1) d) (varsigma : Nat -> ℝ) where
  D : Matrix (Fin d) (Fin d) ℝ
  D_eq : D = texMatchingSaturatedContributionMatrix θ varsigma

/-- The unprimed saturated limit vector from TeX matching Step 1:
`B_{L:1} v^0 + [t B_{L:2} V_1 + D(B_1 - t V_1)] w^0`. -/
noncomputable def texMatchingUnprimedSaturatedLimitVector {L d : Nat}
    (θ : Params (L + 1) d) (Dsat : Matrix (Fin d) (Fin d) ℝ)
    (t : ℝ) (p : ProbePair d) : Fin d -> ℝ :=
  Matrix.mulVec (realSkipBprod (paramStream θ) (L + 1)) p.2
    + Matrix.mulVec
        (t • (realSkipBprod (paramStream (Params.tail θ)) L * (θ 0).1)
          + Dsat * (skipB (θ 0).1 - t • (θ 0).1)) p.1

/-- The primed telescoped limit vector from TeX matching Step 2:
`B'_{L:1} v^0 + [B'_{L:1} - B'_1 + t V'_1] w^0`. -/
noncomputable def texMatchingPrimedTelescopedLimitVector {L d : Nat}
    (θ' : Params (L + 1) d) (t : ℝ) (p : ProbePair d) :
    Fin d -> ℝ :=
  Matrix.mulVec (realSkipBprod (paramStream θ') (L + 1)) p.2
    + Matrix.mulVec
        (realSkipBprod (paramStream θ') (L + 1)
          - skipB (θ' 0).1 + t • (θ' 0).1) p.1

/-- A point in the chosen product neighborhood lies in the refined trichotomy
component. -/
theorem texMatching_product_mem_Ustar
    {L d : Nat}
    {θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    {b : ℝ}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') b)
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d) b signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    {p : ProbePair d} (hp : p ∈ N.Uq) {t : ℝ} (ht : t ∈ N.J) :
    (p, t) ∈ T.Ustar := by
  exact N.product_subset ⟨hp, ht⟩

/-- A point in the chosen product neighborhood lies in the original sign region. -/
theorem texMatching_product_mem_signRegion
    {L d : Nat}
    {θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    {b : ℝ}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') b)
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d) b signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    {p : ProbePair d} (hp : p ∈ N.Uq) {t : ℝ} (ht : t ∈ N.J) :
    (p, t) ∈ signRegion.U :=
  T.trichotomy.subset_sign_region
    (texMatching_product_mem_Ustar signRegion T N hp ht)

/-- Canonical dial path through a point of the selected matching product patch.  The
sign-region and product-neighborhood fields provide the quadric, regularity, and
`t ∈ (0, 1)` hypotheses needed by `DialPathData.ofRegularQuadric`. -/
noncomputable def texMatchingRegularQuadricDialPathData
    {L d r : Nat}
    {θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J) :
    DialPathData (Params.headAttention θ') (Real.log (r : ℝ)) :=
  let hx := texMatching_product_mem_signRegion signRegion T N hp ht
  DialPathData.ofRegularQuadric
    (Params.headAttention θ') (Real.log (r : ℝ)) p t
    (signRegion.point_on_quadric (p, t) hx)
    (signRegion.point_regular (p, t) hx)
    (signRegion.t_pos hx)
    (signRegion.t_lt_one hx)

@[simp] theorem texMatchingRegularQuadricDialPathData_base
    {L d r : Nat}
    {θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J) :
    (texMatchingRegularQuadricDialPathData
      (L := L) (d := d) (r := r) signRegion T N p hp t ht).base = p := by
  simp [texMatchingRegularQuadricDialPathData, DialPathData.ofRegularQuadric]

@[simp] theorem texMatchingRegularQuadricDialPathData_target
    {L d r : Nat}
    {θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J) :
    (texMatchingRegularQuadricDialPathData
      (L := L) (d := d) (r := r) signRegion T N p hp t ht).t = t := by
  simp [texMatchingRegularQuadricDialPathData, DialPathData.ofRegularQuadric]

/-- The canonical regular-quadric dial selected from a product patch lands back in the
refined trichotomy component. -/
theorem texMatchingRegularQuadricDialPathData_mem_Ustar
    {L d r : Nat}
    {θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J) :
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    (δ.base, δ.t) ∈ T.Ustar := by
  simp [texMatching_product_mem_Ustar signRegion T N hp ht]

/-- Backwards-compatible name for the canonical product-patch dial. -/
noncomputable def texMatchingDialPathData_of_product
    {L d r : Nat}
    {θ' : Params (L + 1) d} {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    (p : ProbePair d) (hp : p ∈ N.Uq) (t : ℝ) (ht : t ∈ N.J) :
    DialPathData (Params.headAttention θ') (Real.log (r : ℝ)) :=
  texMatchingRegularQuadricDialPathData
    (L := L) (d := d) (r := r) signRegion T N p hp t ht

/-- Smaller asymptotic input for the regular-quadric limit-vector theorem.

It no longer mentions observable agreement or `Fobs`: it only states the two closed
recursion limits along the canonical regular-quadric dial path. -/
structure TexMatchingRegularQuadricClosedRecursionLimitObligation
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma) : Prop where
  unprimed_tendsto :
    ∀ p hp t ht,
      let δ :=
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      Filter.Tendsto
        (fun τ : ℝ =>
          Frec r θ (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ)
        Filter.atTop
        (nhds (texMatchingUnprimedSaturatedLimitVector θ S.D t p))
  primed_tendsto :
    ∀ p hp t ht,
      let δ :=
        texMatchingRegularQuadricDialPathData
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
      Filter.Tendsto
        (fun τ : ℝ =>
          Frec r θ' (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ)
        Filter.atTop
        (nhds (texMatchingPrimedTelescopedLimitVector θ' t p))

/-- Unprimed Frec saturation asymptotic over the refined trichotomy component.

This is the analytic Step 1 gap after all product-patch bookkeeping is removed: every
dial whose `(base, target)` lies in `T.Ustar` has the saturated unprimed closed-recursion
limit. -/
abbrev TexMatchingUnprimedSaturatedDialFrecTendsto
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {signU : Set (ProbePair d × ℝ)}
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signU)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma) : Prop :=
  ∀ δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ)),
    (δ.base, δ.t) ∈ T.Ustar ->
    Filter.Tendsto
      (fun τ : ℝ =>
        Frec r θ (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ)
      Filter.atTop
      (nhds (texMatchingUnprimedSaturatedLimitVector θ S.D δ.t δ.base))

/-- Structure wrapper for the unprimed dial `Frec` saturation theorem. -/
structure TexMatchingUnprimedSaturatedFrecAsymptoticObligation
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma) : Prop where
  tendsto :
    TexMatchingUnprimedSaturatedDialFrecTendsto
      (θ := θ) (θ' := θ') T S

/-- A pointwise unprimed dial `Frec` saturation theorem is exactly the analytic
obligation package expected by the closed-recursion matching bridge. -/
theorem texMatchingUnprimedSaturatedFrecAsymptoticObligation_of_dialFrecTendsto
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma)
    (h :
      TexMatchingUnprimedSaturatedDialFrecTendsto
        (θ := θ) (θ' := θ') T S) :
    TexMatchingUnprimedSaturatedFrecAsymptoticObligation signRegion T S := by
  exact ⟨h⟩

/-- Primed Frec telescoping asymptotic over the refined trichotomy component.

This is the analytic Step 2 gap after all product-patch bookkeeping is removed: every
dial whose `(base, target)` lies in `T.Ustar` has the primed telescoped closed-recursion
limit. -/
structure TexMatchingPrimedTelescopedFrecAsymptoticObligation
    {L d r : Nat}
    {θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U) : Prop where
  tendsto :
    ∀ δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ)),
      (δ.base, δ.t) ∈ T.Ustar ->
      Filter.Tendsto
        (fun τ : ℝ =>
          Frec r θ' (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ)
        Filter.atTop
        (nhds (texMatchingPrimedTelescopedLimitVector θ' δ.t δ.base))

/-- Pointwise primed closed-recursion asymptotic after all matching/product-patch
bookkeeping has been removed.

This is the remaining analytic Step 2 theorem: along every dial whose endpoint belongs
to the refined trichotomy component, the primed `Frec` recursion tends to the telescoped
limit vector. -/
abbrev TexMatchingPrimedTelescopedFrecDialAsymptotic
    {L d r : Nat}
    {θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U) : Prop :=
  ∀ δ : DialPathData (Params.headAttention θ') (Real.log (r : ℝ)),
    (δ.base, δ.t) ∈ T.Ustar ->
    Filter.Tendsto
      (fun τ : ℝ =>
        Frec r θ' (DialPathData.probe δ τ).1 (DialPathData.probe δ τ).2 τ)
      Filter.atTop
      (nhds (texMatchingPrimedTelescopedLimitVector θ' δ.t δ.base))

/-- The named pointwise primed dial asymptotic is exactly the field needed by the
packaged primed asymptotic obligation. -/
theorem texMatchingPrimedTelescopedFrecAsymptoticObligation_of_dialAsymptotic
    {L d r : Nat}
    {θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    {signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ))}
    {T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U}
    (hprimed : TexMatchingPrimedTelescopedFrecDialAsymptotic signRegion T) :
    TexMatchingPrimedTelescopedFrecAsymptoticObligation signRegion T :=
  ⟨hprimed⟩

/-- The two named Frec asymptotics discharge the closed-recursion limit package for the
canonical regular-quadric product-patch dials. -/
theorem texMatchingRegularQuadricClosedRecursionLimitObligation_of_frecAsymptotics
    {L d r : Nat}
    {θ θ' : Params (L + 1) d}
    {O : Set (ProbePair d)}
    (signRegion :
      SignRegionData (L := L + 1) (d := d) θ' O
        (Params.headAttention θ') (Real.log (r : ℝ)))
    (T :
      TexTrichotomyConstructionData (L := L + 1) (d := d)
        (Real.log (r : ℝ)) signRegion.U)
    (N :
      TexMatchingProductNeighborhoodData (d := d)
        (Params.headAttention θ') T.Ustar)
    {varsigma : Nat -> ℝ}
    (S : TexMatchingSaturatedContributionData θ varsigma)
    (hunprimed :
      TexMatchingUnprimedSaturatedFrecAsymptoticObligation signRegion T S)
    (hprimed :
      TexMatchingPrimedTelescopedFrecAsymptoticObligation signRegion T) :
    TexMatchingRegularQuadricClosedRecursionLimitObligation signRegion T N S := by
  refine ⟨?_, ?_⟩
  · intro p hp t ht
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    have hmem : (δ.base, δ.t) ∈ T.Ustar := by
      simpa [δ] using
        texMatchingRegularQuadricDialPathData_mem_Ustar
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
    have hbase : δ.base = p := by
      simp [δ]
    have htarget : δ.t = t := by
      simp [δ]
    simpa [hbase, htarget] using hunprimed.tendsto δ hmem
  · intro p hp t ht
    let δ :=
      texMatchingRegularQuadricDialPathData
        (L := L) (d := d) (r := r) signRegion T N p hp t ht
    have hmem : (δ.base, δ.t) ∈ T.Ustar := by
      simpa [δ] using
        texMatchingRegularQuadricDialPathData_mem_Ustar
          (L := L) (d := d) (r := r) signRegion T N p hp t ht
    have hbase : δ.base = p := by
      simp [δ]
    have htarget : δ.t = t := by
      simp [δ]
    simpa [hbase, htarget] using hprimed.tendsto δ hmem

end TransformerIdentifiability.NLayer
