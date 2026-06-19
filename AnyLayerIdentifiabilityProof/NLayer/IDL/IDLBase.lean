import AnyLayerIdentifiabilityProof.NLayer.IDL.IDLStatement
import AnyLayerIdentifiabilityProof.NLayer.Step1.DescentConclusion

set_option autoImplicit false

namespace TransformerIdentifiability.NLayer

/-!
# Depth-one IDL base case

This file owns the base case of the TeX theorem `ID_L`.
-/

theorem sig_strictMono : StrictMono sig := by
  intro a b hab
  have hden : 1 + Real.exp (-b) < 1 + Real.exp (-a) := by
    have hexp : Real.exp (-b) < Real.exp (-a) :=
      Real.exp_lt_exp.mpr (by linarith)
    linarith
  have hpos : 0 < 1 + Real.exp (-b) := by positivity
  rw [sig, sig]
  gcongr

theorem sig_injective : Function.Injective sig :=
  sig_strictMono.injective

/-- The closed recursion at depth one is the single first-layer update. -/
theorem Frec_depth_one
    {d r : Nat} (θ : Params 1 d) (w v : Fin d -> ℝ) (τ : ℝ) :
    Frec r θ w v τ =
      v + (Params.headValue θ).mulVec v
        + sig (τ * firstSlope θ w v + Real.log r) •
          (Params.headValue θ).mulVec w := by
  simp [Frec, Params.headValue, Params.headLayer, firstSlope, firstAttention,
    matrixBilin, paramStream_apply_of_lt]

theorem Fobs_depth_one_of_pos
    {d r : Nat} (hr_pos : 0 < r) (θ : Params 1 d)
    (w v : Fin d -> ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Fobs r θ w v τ =
      v + (Params.headValue θ).mulVec v
        + sig (τ * firstSlope θ w v + Real.log r) •
          (Params.headValue θ).mulVec w := by
  rw [Fobs_eq_Frec_of_pos r hr_pos θ w v hτ, Frec_depth_one]

/-- At depth one, constant-probe agreement with `w = 0` identifies the value matrix. -/
theorem IDL_depth_one_headValue_eq_of_probeAgreement
    {d r : Nat} (hr_pos : 0 < r)
    {θ θ' : Params 1 d}
    (hagree : ProbeObservableAgreement r θ θ') :
    Params.headValue θ = Params.headValue θ' := by
  apply Matrix.ext
  intro i j
  let w : Fin d -> ℝ := 0
  let v : Fin d -> ℝ := Pi.single j 1
  have hobs := hagree w v 1 (by norm_num)
  rw [Fobs_depth_one_of_pos hr_pos θ w v (by norm_num),
    Fobs_depth_one_of_pos hr_pos θ' w v (by norm_num)] at hobs
  have hcoord := congrFun hobs i
  have hcoord0 :
      (v + (Params.headValue θ).mulVec v) i =
        (v + (Params.headValue θ').mulVec v) i := by
    simpa [w] using hcoord
  have hmul :
      (Params.headValue θ).mulVec v i =
        (Params.headValue θ').mulVec v i := by
    exact add_left_cancel hcoord0
  simpa [v, matrix_mulVec_single_one] using hmul

/-- At depth one, after the value matrix is identified and nonzero, probe agreement
identifies the attention matrix. -/
theorem IDL_depth_one_headAttention_eq_of_probeAgreement
    {d r : Nat} (hr_pos : 0 < r)
    {θ θ' : Params 1 d}
    (hagree : ProbeObservableAgreement r θ θ')
    (hvalue : Params.headValue θ = Params.headValue θ')
    (hvalue_ne : Params.headValue θ ≠ 0) :
    Params.headAttention θ = Params.headAttention θ' := by
  classical
  rcases exists_matrix_entry_ne_zero_of_ne_zero hvalue_ne with ⟨i, j, hij⟩
  let U : Set (ProbePair d) :=
    {p | (Params.headValue θ).mulVec p.1 i ≠ 0}
  have hOpen : IsOpen U := by
    have hpoly :
        IsProbePolynomial d
          (fun p : ProbePair d => (Params.headValue θ).mulVec p.1 i) :=
      ⟨matrixMulVecCoordProbePoly (Params.headValue θ) i, by
        intro p
        simpa using eval_matrixMulVecCoordProbePoly (Params.headValue θ) i p⟩
    simpa [U] using hpoly.isOpen_ne_zero
  have hNonempty : U.Nonempty := by
    refine ⟨((Pi.single j 1), 0), ?_⟩
    simpa [U, matrix_mulVec_single_one] using hij
  have hFirstAttention :
      firstAttention θ = firstAttention θ' := by
    refine firstAttention_eq_of_isOpen_nonempty_probe_set_firstSlope_eq
      (U := U) hOpen hNonempty ?_
    intro p hp
    have hobs := hagree p.1 p.2 1 (by norm_num)
    rw [Fobs_depth_one_of_pos hr_pos θ p.1 p.2 (by norm_num),
      Fobs_depth_one_of_pos hr_pos θ' p.1 p.2 (by norm_num)] at hobs
    have hcoord := congrFun hobs i
    rw [← hvalue] at hcoord
    have hgate_coord :
        (sig (1 * firstSlope θ p.1 p.2 + Real.log r) •
            (Params.headValue θ).mulVec p.1) i =
          (sig (1 * firstSlope θ' p.1 p.2 + Real.log r) •
            (Params.headValue θ).mulVec p.1) i := by
      simpa [Pi.add_apply] using add_left_cancel hcoord
    have hgate :
        sig (1 * firstSlope θ p.1 p.2 + Real.log r)
            * (Params.headValue θ).mulVec p.1 i =
          sig (1 * firstSlope θ' p.1 p.2 + Real.log r)
            * (Params.headValue θ).mulVec p.1 i := by
      simpa [Pi.smul_apply, smul_eq_mul] using hgate_coord
    have hsig :
        sig (1 * firstSlope θ p.1 p.2 + Real.log r) =
          sig (1 * firstSlope θ' p.1 p.2 + Real.log r) :=
      mul_right_cancel₀ hp hgate
    have harg :
        1 * firstSlope θ p.1 p.2 + Real.log r =
          1 * firstSlope θ' p.1 p.2 + Real.log r :=
      sig_injective hsig
    linarith
  have hθ : firstAttention θ = Params.headAttention θ := by
    simpa [Params.headAttention, Params.headLayer] using
      firstAttention_eq_of_pos θ (by norm_num : 0 < 1)
  have hθ' : firstAttention θ' = Params.headAttention θ' := by
    simpa [Params.headAttention, Params.headLayer] using
      firstAttention_eq_of_pos θ' (by norm_num : 0 < 1)
  calc
    Params.headAttention θ = firstAttention θ := hθ.symm
    _ = firstAttention θ' := hFirstAttention
    _ = Params.headAttention θ' := hθ'

/-- At depth one, eventual agreement on the finitely many basis value probes identifies
the value matrix. -/
theorem IDL_depth_one_headValue_eq_of_basisTailAgreement
    {d r : Nat} (hr_pos : 0 < r)
    {θ θ' : Params 1 d}
    (hagree :
      ∀ j : Fin d, ∃ T : ℝ, 0 ≤ T ∧
        RealTailObservableAgreementAt r θ θ'
          ((0 : Fin d -> ℝ), Pi.single j (1 : ℝ)) T) :
    Params.headValue θ = Params.headValue θ' := by
  apply Matrix.ext
  intro i j
  let w : Fin d -> ℝ := 0
  let v : Fin d -> ℝ := Pi.single j 1
  rcases hagree j with ⟨T, hT_nonneg, hAgree⟩
  let τ : ℝ := T + 1
  have hτ_gt : T < τ := by
    dsimp [τ]
    linarith
  have hτ_pos : 0 < τ := by
    dsimp [τ]
    linarith
  have hobs := hAgree τ hτ_gt
  rw [Fobs_depth_one_of_pos hr_pos θ w v hτ_pos,
    Fobs_depth_one_of_pos hr_pos θ' w v hτ_pos] at hobs
  have hcoord := congrFun hobs i
  have hcoord0 :
      (v + (Params.headValue θ).mulVec v) i =
        (v + (Params.headValue θ').mulVec v) i := by
    simpa [w] using hcoord
  have hmul :
      (Params.headValue θ).mulVec v i =
        (Params.headValue θ').mulVec v i := by
    exact add_left_cancel hcoord0
  simpa [v, matrix_mulVec_single_one] using hmul

/-- At depth one, the visible-tail coordinate is exactly a first-value coordinate. -/
theorem visibleTailCoord_depth_one
    {d : Nat} (θ : Params 1 d) (w : Fin d -> ℝ) (i : Fin d) :
    visibleTailCoord θ w i = (Params.headValue θ).mulVec w i := by
  simp [visibleTailCoord, visibleTailVector, Params.headValue, Params.headLayer,
    paramStream_apply_of_lt]

/-- The complex one-layer coordinate observable attached to a fixed probe. -/
noncomputable def depthOneComplexObservableCoord
    {d : Nat} (V : Matrix (Fin d) (Fin d) ℝ)
    (lambda b : ℝ) (w v : Fin d -> ℝ) (i : Fin d) : ℂ -> ℂ :=
  fun z =>
    ((v + V.mulVec v) i : ℂ) +
      csig ((lambda : ℂ) * z + (b : ℂ)) * ((V.mulVec w i : ℝ) : ℂ)

theorem depthOneComplexObservableCoord_analyticOn_affineRegular
    {d : Nat} (V : Matrix (Fin d) (Fin d) ℝ)
    (lambda b : ℝ) (w v : Fin d -> ℝ) (i : Fin d) :
    AnalyticOnNhd ℂ
      (depthOneComplexObservableCoord V lambda b w v i)
      (affineOddPiIStratum b lambda)ᶜ := by
  intro z hz
  have hden : 1 + Complex.exp (-((lambda : ℂ) * z + (b : ℂ))) ≠ 0 := by
    intro hzero
    exact hz (by
      rw [affineOddPiIStratum_eq_denom_zero]
      exact hzero)
  have haff : AnalyticAt ℂ (fun z : ℂ => (lambda : ℂ) * z + (b : ℂ)) z :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hsig :
      AnalyticAt ℂ (fun z : ℂ => csig ((lambda : ℂ) * z + (b : ℂ))) z :=
    AnalyticAt.comp_of_eq' (csig_analyticAt hden) haff rfl
  simpa [depthOneComplexObservableCoord] using
    analyticAt_const.add (hsig.mul analyticAt_const)

theorem depthOneComplexObservableCoord_continuousAt_affineRegular
    {d : Nat} (V : Matrix (Fin d) (Fin d) ℝ)
    (lambda b : ℝ) (w v : Fin d -> ℝ) (i : Fin d)
    {z : ℂ} (hz : z ∉ affineOddPiIStratum b lambda) :
    ContinuousAt
      (depthOneComplexObservableCoord V lambda b w v i) z :=
  (depthOneComplexObservableCoord_analyticOn_affineRegular
    V lambda b w v i z hz).continuousAt

theorem depthOneComplexObservableCoord_eq_ofReal_Fobs
    {d r : Nat} (hr_pos : 0 < r)
    {θ : Params 1 d} (w v : Fin d -> ℝ) (i : Fin d)
    {τ : ℝ} (hτ : 0 < τ) :
    depthOneComplexObservableCoord (Params.headValue θ)
        (firstSlope θ w v) (Real.log r) w v i (τ : ℂ)
      = ((Fobs r θ w v τ i : ℝ) : ℂ) := by
  rw [Fobs_depth_one_of_pos hr_pos θ w v hτ]
  have harg :
      ((firstSlope θ w v : ℂ) * (τ : ℂ) + (Real.log r : ℂ))
        = ((τ * firstSlope θ w v + Real.log r : ℝ) : ℂ) := by
    norm_num [mul_comm, mul_left_comm, mul_assoc]
  dsimp [depthOneComplexObservableCoord]
  rw [harg, csig_ofReal]
  simp

/-- Local one-layer pole transfer identifies the first slope at any probe where the
primed slope and a primed visible value coordinate are nonzero. -/
theorem IDL_depth_one_firstSlope_eq_of_localTailAgreement_at
    {d r : Nat} (hr : 2 <= r)
    {θ θ' : Params 1 d} {p : ProbePair d} {i : Fin d}
    (hagree : ∃ T : ℝ, 0 ≤ T ∧ RealTailObservableAgreementAt r θ θ' p T)
    (hprimedSlope : firstSlope θ' p.1 p.2 ≠ 0)
    (hvisible : visibleTailCoord θ' p.1 i ≠ 0) :
    firstSlope θ p.1 p.2 = firstSlope θ' p.1 p.2 := by
  classical
  have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num : 0 < 2) hr
  let lambda : ℝ := firstSlope θ p.1 p.2
  let lambda' : ℝ := firstSlope θ' p.1 p.2
  let b : ℝ := Real.log r
  let F : ℂ -> ℂ :=
    depthOneComplexObservableCoord (Params.headValue θ) lambda b p.1 p.2 i
  let G : ℂ -> ℂ :=
    depthOneComplexObservableCoord (Params.headValue θ') lambda' b p.1 p.2 i
  have hb_pos : 0 < b := by
    dsimp [b]
    exact Real.log_pos (by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hr : 1 < r))
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  rcases hagree with ⟨T, hT_nonneg, hAgree⟩
  have htail : ∀ t : ℝ, T < t -> F (t : ℂ) = G (t : ℂ) := by
    intro t ht
    have ht_pos : 0 < t := by linarith
    have hobs := congrFun (hAgree t ht) i
    calc
      F (t : ℂ)
          = ((Fobs r θ p.1 p.2 t i : ℝ) : ℂ) := by
              simpa [F, lambda, b] using
                depthOneComplexObservableCoord_eq_ofReal_Fobs
                  (θ := θ) hr_pos p.1 p.2 i ht_pos
      _ = ((Fobs r θ' p.1 p.2 t i : ℝ) : ℂ) := by
              exact congrArg (fun x : ℝ => ((x : ℝ) : ℂ)) hobs
      _ = G (t : ℂ) := by
              simpa [G, lambda', b] using
                (depthOneComplexObservableCoord_eq_ofReal_Fobs
                  (θ := θ') hr_pos p.1 p.2 i ht_pos).symm
  have hsub :
      affineOddPiIStratum b lambda' ⊆ affineOddPiIStratum b lambda := by
    intro τ hτ
    have hGisol : IsPuncturedIsolated (affineOddPiIStratum b lambda') τ :=
      eventually_notMem_of_not_mem_acc
        ((affineOddPiIStratum_noAccumIn_univ b lambda') τ trivial)
    rcases (affine_mem_oddPiI_iff_sigmoidPole (b := b) (lambda := lambda')
        (by simpa [lambda'] using hprimedSlope)).mp
        (by simpa [affineOddPiIStratum] using hτ) with ⟨n, rfl⟩
    have hcoef : ((Params.headValue θ').mulVec p.1 i : ℂ) ≠ 0 := by
      exact_mod_cast (by
        simpa [visibleTailCoord_depth_one] using hvisible)
    have hgate :
        BlowsUpAt
          (fun z : ℂ => csig ((lambda' : ℂ) * z + (b : ℂ)))
          (sigmoidPole b lambda' n) :=
      affine_csig_blowsUpAt_sigmoidPole b lambda'
        (by simpa [lambda'] using hprimedSlope) n
    have hbounded :
        PuncturedBoundedAt
          (fun _ : ℂ => (((p.2 + (Params.headValue θ').mulVec p.2) i : ℝ) : ℂ))
          (sigmoidPole b lambda' n) :=
      PuncturedBoundedAt.const _ _
    have hGblow :
        BlowsUpAt G (sigmoidPole b lambda' n) := by
      have hbase :
          BlowsUpAt
            (depthOneComplexObservableCoord
              (Params.headValue θ') lambda' b p.1 p.2 i)
            (sigmoidPole b lambda' n) :=
        hgate.bounded_add_mul_tendsto_ne_zero hbounded
          tendsto_const_nhds hcoef
      simpa [G] using hbase
    have hx0 : T < T + 1 := by linarith
    have hz0 : ((T + 1 : ℝ) : ℂ) ∈
        (affineOddPiIStratum b lambda ∪ affineOddPiIStratum b lambda')ᶜ := by
      have hFnot : ((T + 1 : ℝ) : ℂ) ∉ affineOddPiIStratum b lambda :=
        affineOddPiIStratum_avoids_real b lambda (T + 1)
      have hGnot : ((T + 1 : ℝ) : ℂ) ∉ affineOddPiIStratum b lambda' :=
        affineOddPiIStratum_avoids_real b lambda' (T + 1)
      simpa using And.intro hFnot hGnot
    exact pole_transfer_of_real_tail_eq
      (E_F := affineOddPiIStratum b lambda)
      (E_G := affineOddPiIStratum b lambda')
      (F := F) (G := G) (T0 := T) (x0 := T + 1)
      (τ := sigmoidPole b lambda' n)
      (affineOddPiIStratum_closed b lambda)
      (affineOddPiIStratum_countable b lambda)
      (affineOddPiIStratum_countable b lambda')
      (by
        simpa [F] using
          depthOneComplexObservableCoord_analyticOn_affineRegular
            (Params.headValue θ) lambda b p.1 p.2 i)
      (by
        simpa [G] using
          depthOneComplexObservableCoord_analyticOn_affineRegular
            (Params.headValue θ') lambda' b p.1 p.2 i)
      hx0 hz0 htail
      (by
        intro hnot
        have han :
            AnalyticOnNhd ℂ F (affineOddPiIStratum b lambda)ᶜ := by
          simpa [F] using
            depthOneComplexObservableCoord_analyticOn_affineRegular
              (Params.headValue θ) lambda b p.1 p.2 i
        have hcont := (han (sigmoidPole b lambda' n) hnot).continuousAt
        simpa [F] using hcont)
      hGisol hGblow
  have hsubFirst :
      firstPoleSet b lambda' ⊆ firstPoleSet b lambda := by
    intro τ hτ
    have hτaff : τ ∈ affineOddPiIStratum b lambda' := by
      rw [affineOddPiIStratum_eq_firstPoleSet_of_lambda_ne_zero
        (by simpa [lambda'] using hprimedSlope)]
      exact hτ
    have hτF := hsub hτaff
    by_cases hlambda : lambda = 0
    · rw [affineOddPiIStratum_eq_empty_of_lambda_eq_zero hlambda] at hτF
      simp at hτF
    · rw [affineOddPiIStratum_eq_firstPoleSet_of_lambda_ne_zero hlambda] at hτF
      exact hτF
  have hlambda_ne : lambda ≠ 0 := by
    intro hlambda
    have hpole_mem : sigmoidPole b lambda' 0 ∈ firstPoleSet b lambda :=
      hsubFirst (sigmoidPole_mem_firstPoleSet b lambda' 0)
    rw [show firstPoleSet b lambda = ({0} : Set ℂ) by
      ext z
      simp [firstPoleSet, sigmoidPole, hlambda, eq_comm]] at hpole_mem
    have hpole_ne : sigmoidPole b lambda' 0 ≠ 0 :=
      sigmoidPole_ne_zero_of_b_ne_zero hb_ne (by simpa [lambda'] using hprimedSlope) 0
    exact hpole_ne hpole_mem
  have hslope : lambda = lambda' :=
    slope_eq_of_firstPoleSet_subset hb_ne hlambda_ne
      (by simpa [lambda'] using hprimedSlope) hsubFirst
  simpa [lambda, lambda'] using hslope

/-- Local eventual agreement on a nonempty open depth-one region identifies the value
matrix.  The proof uses only probes from the open region, not fixed basis probes. -/
theorem IDL_depth_one_headValue_eq_of_localTailAgreement
    {d r : Nat} (hr : 2 <= r)
    {θ θ' : Params 1 d} {O : Set (ProbePair d)}
    (hO_open : IsOpen O) (hO_nonempty : O.Nonempty)
    (hagree :
      ∀ p : ProbePair d, p ∈ O ->
        ∃ T : ℝ, 0 ≤ T ∧ RealTailObservableAgreementAt r θ θ' p T)
    (hprimed_generic : TexGeneric 1 d θ') :
    Params.headValue θ = Params.headValue θ' := by
  classical
  have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num : 0 < 2) hr
  have hbase : TexGenericBaseClauses d θ' := by
    simpa using hprimed_generic
  have hprimedValue_ne : Params.headValue θ' ≠ 0 := by
    simpa [Params.headValue, Params.headLayer, paramStream_apply_of_lt] using
      hbase.value_ne_zero
  have hprimedAttention_ne : Params.headAttention θ' ≠ 0 := by
    simpa [Params.headAttention, Params.headLayer, paramStream_apply_of_lt] using
      hbase.attention_ne_zero
  rcases exists_matrix_entry_ne_zero_of_ne_zero hprimedValue_ne with ⟨i, j, hij⟩
  let Urow : Set (ProbePair d) :=
    {p | (Params.headValue θ').mulVec p.1 i ≠ 0}
  have hrowPoly :
      IsNonzeroProbePolynomial d
        (fun p : ProbePair d => (Params.headValue θ').mulVec p.1 i) :=
    ⟨matrixMulVecCoordProbePoly (Params.headValue θ') i,
      matrixMulVecCoordProbePoly_ne_zero_of_entry_ne_zero hij,
      by
        intro p
        simpa using eval_matrixMulVecCoordProbePoly (Params.headValue θ') i p⟩
  have hUrow_open : IsOpen Urow := by
    simpa [Urow] using hrowPoly.isOpen_ne_zero
  have hUrow_dense : Dense Urow := by
    simpa [Urow] using hrowPoly.dense_ne_zero
  let Uslope : Set (ProbePair d) :=
    {p | firstSlope θ' p.1 p.2 ≠ 0}
  have hslopePoly :
      IsNonzeroProbePolynomial d
        (fun p : ProbePair d => firstSlope θ' p.1 p.2) :=
    firstSlope_isNonzeroProbePolynomial_of_firstAttention_ne_zero
      hprimedAttention_ne
  have hUslope_open : IsOpen Uslope := by
    simpa [Uslope] using hslopePoly.isOpen_ne_zero
  have hUslope_dense : Dense Uslope := by
    simpa [Uslope] using hslopePoly.dense_ne_zero
  let U : Set (ProbePair d) := O ∩ Uslope ∩ Urow
  have hU_open : IsOpen U := (hO_open.inter hUslope_open).inter hUrow_open
  have hU_nonempty : U.Nonempty := by
    have hdense : Dense (Uslope ∩ Urow) :=
      hUslope_dense.inter_of_isOpen_right hUrow_dense hUrow_open
    rcases hdense.inter_open_nonempty O hO_open hO_nonempty with
      ⟨p, hpO, hpSlope, hpRow⟩
    exact ⟨p, ⟨⟨hpO, hpSlope⟩, hpRow⟩⟩
  have hslopeEq :
      ∀ p : ProbePair d, p ∈ U ->
        firstSlope θ p.1 p.2 = firstSlope θ' p.1 p.2 := by
    intro p hp
    exact IDL_depth_one_firstSlope_eq_of_localTailAgreement_at hr
      (hagree p hp.1.1) hp.1.2
      (by simpa [visibleTailCoord_depth_one, Urow] using hp.2)
  have hattention : Params.headAttention θ = Params.headAttention θ' := by
    have hfirst :
        firstAttention θ = firstAttention θ' :=
      firstAttention_eq_of_isOpen_nonempty_probe_set_firstSlope_eq
        hU_open hU_nonempty hslopeEq
    have hθ : firstAttention θ = Params.headAttention θ := by
      simpa [Params.headAttention, Params.headLayer] using
        firstAttention_eq_of_pos θ (by norm_num : 0 < 1)
    have hθ' : firstAttention θ' = Params.headAttention θ' := by
      simpa [Params.headAttention, Params.headLayer] using
        firstAttention_eq_of_pos θ' (by norm_num : 0 < 1)
    calc
      Params.headAttention θ = firstAttention θ := hθ.symm
      _ = firstAttention θ' := hfirst
      _ = Params.headAttention θ' := hθ'
  apply Matrix.ext
  intro a bidx
  have hvanish_open :
      ∀ p : ProbePair d, p ∈ U ->
        (Params.headValue θ - Params.headValue θ').mulVec p.1 a = 0 := by
    intro p hp
    rcases hagree p hp.1.1 with ⟨T, _hT_nonneg, hAgree⟩
    let τ : ℝ := T + 1
    have hτ_gt : T < τ := by dsimp [τ]; linarith
    have hτ_pos : 0 < τ := by dsimp [τ]; linarith
    have hobs := hAgree τ hτ_gt
    rw [Fobs_depth_one_of_pos hr_pos θ p.1 p.2 hτ_pos,
      Fobs_depth_one_of_pos hr_pos θ' p.1 p.2 hτ_pos] at hobs
    have hcoord := congrFun hobs a
    have hslope := hslopeEq p hp
    have hsig :
        sig (τ * firstSlope θ p.1 p.2 + Real.log r) =
          sig (τ * firstSlope θ' p.1 p.2 + Real.log r) := by
      rw [hslope]
    have hgate :
        (sig (τ * firstSlope θ p.1 p.2 + Real.log r) •
            (Params.headValue θ).mulVec p.1) a
          -
        (sig (τ * firstSlope θ' p.1 p.2 + Real.log r) •
            (Params.headValue θ').mulVec p.1) a
          =
        sig (τ * firstSlope θ' p.1 p.2 + Real.log r) *
          ((Params.headValue θ - Params.headValue θ').mulVec p.1 a) := by
      rw [Matrix.sub_mulVec]
      simp [Pi.smul_apply, smul_eq_mul, hsig, Pi.sub_apply]
      ring_nf
    have hbase :
        ((Params.headValue θ - Params.headValue θ').mulVec p.2 a) +
        sig (τ * firstSlope θ' p.1 p.2 + Real.log r) *
          ((Params.headValue θ - Params.headValue θ').mulVec p.1 a) = 0 := by
      have hcoord' :
          (p.2 + (Params.headValue θ).mulVec p.2) a
              + (sig (τ * firstSlope θ p.1 p.2 + Real.log r) •
                  (Params.headValue θ).mulVec p.1) a
            =
          (p.2 + (Params.headValue θ').mulVec p.2) a
              + (sig (τ * firstSlope θ' p.1 p.2 + Real.log r) •
                  (Params.headValue θ').mulVec p.1) a := by
        simpa [Pi.add_apply] using hcoord
      have hsub :
          ((Params.headValue θ).mulVec p.2 a -
              (Params.headValue θ').mulVec p.2 a) +
            ((sig (τ * firstSlope θ p.1 p.2 + Real.log r) •
                (Params.headValue θ).mulVec p.1) a -
              (sig (τ * firstSlope θ' p.1 p.2 + Real.log r) •
                (Params.headValue θ').mulVec p.1) a) = 0 := by
        calc
          ((Params.headValue θ).mulVec p.2 a -
                (Params.headValue θ').mulVec p.2 a) +
              ((sig (τ * firstSlope θ p.1 p.2 + Real.log r) •
                  (Params.headValue θ).mulVec p.1) a -
                (sig (τ * firstSlope θ' p.1 p.2 + Real.log r) •
                  (Params.headValue θ').mulVec p.1) a)
              =
            ((p.2 + (Params.headValue θ).mulVec p.2) a
                + (sig (τ * firstSlope θ p.1 p.2 + Real.log r) •
                    (Params.headValue θ).mulVec p.1) a)
              -
            ((p.2 + (Params.headValue θ').mulVec p.2) a
                + (sig (τ * firstSlope θ' p.1 p.2 + Real.log r) •
                    (Params.headValue θ').mulVec p.1) a) := by
                simp [Pi.add_apply]
                ring
          _ = 0 := sub_eq_zero.mpr hcoord'
      rw [hgate] at hsub
      rw [Matrix.sub_mulVec]
      simpa [Pi.sub_apply] using hsub
    have hbase_two :
        ((Params.headValue θ - Params.headValue θ').mulVec p.2 a) +
        sig ((τ + 1) * firstSlope θ' p.1 p.2 + Real.log r) *
          ((Params.headValue θ - Params.headValue θ').mulVec p.1 a) = 0 := by
      have hAgree2 := hAgree (τ + 1) (by linarith)
      have hτ2_pos : 0 < τ + 1 := by linarith
      have hobs2 := hAgree2
      rw [Fobs_depth_one_of_pos hr_pos θ p.1 p.2 hτ2_pos,
        Fobs_depth_one_of_pos hr_pos θ' p.1 p.2 hτ2_pos] at hobs2
      have hcoord2 := congrFun hobs2 a
      have hsig2 :
          sig ((τ + 1) * firstSlope θ p.1 p.2 + Real.log r) =
            sig ((τ + 1) * firstSlope θ' p.1 p.2 + Real.log r) := by
        rw [hslope]
      have hgate2 :
          (sig ((τ + 1) * firstSlope θ p.1 p.2 + Real.log r) •
              (Params.headValue θ).mulVec p.1) a
            -
          (sig ((τ + 1) * firstSlope θ' p.1 p.2 + Real.log r) •
              (Params.headValue θ').mulVec p.1) a
            =
          sig ((τ + 1) * firstSlope θ' p.1 p.2 + Real.log r) *
            ((Params.headValue θ - Params.headValue θ').mulVec p.1 a) := by
        rw [Matrix.sub_mulVec]
        simp [Pi.smul_apply, smul_eq_mul, hsig2, Pi.sub_apply]
        ring_nf
      have hcoord2' :
          (p.2 + (Params.headValue θ).mulVec p.2) a
              + (sig ((τ + 1) * firstSlope θ p.1 p.2 + Real.log r) •
                  (Params.headValue θ).mulVec p.1) a
            =
          (p.2 + (Params.headValue θ').mulVec p.2) a
              + (sig ((τ + 1) * firstSlope θ' p.1 p.2 + Real.log r) •
                  (Params.headValue θ').mulVec p.1) a := by
        simpa [Pi.add_apply] using hcoord2
      have hsub2 :
          ((Params.headValue θ).mulVec p.2 a -
              (Params.headValue θ').mulVec p.2 a) +
            ((sig ((τ + 1) * firstSlope θ p.1 p.2 + Real.log r) •
                (Params.headValue θ).mulVec p.1) a -
              (sig ((τ + 1) * firstSlope θ' p.1 p.2 + Real.log r) •
                (Params.headValue θ').mulVec p.1) a) = 0 := by
        calc
          ((Params.headValue θ).mulVec p.2 a -
                (Params.headValue θ').mulVec p.2 a) +
              ((sig ((τ + 1) * firstSlope θ p.1 p.2 + Real.log r) •
                  (Params.headValue θ).mulVec p.1) a -
                (sig ((τ + 1) * firstSlope θ' p.1 p.2 + Real.log r) •
                  (Params.headValue θ').mulVec p.1) a)
              =
            ((p.2 + (Params.headValue θ).mulVec p.2) a
                + (sig ((τ + 1) * firstSlope θ p.1 p.2 + Real.log r) •
                    (Params.headValue θ).mulVec p.1) a)
              -
            ((p.2 + (Params.headValue θ').mulVec p.2) a
                + (sig ((τ + 1) * firstSlope θ' p.1 p.2 + Real.log r) •
                    (Params.headValue θ').mulVec p.1) a) := by
                simp [Pi.add_apply]
                ring
          _ = 0 := sub_eq_zero.mpr hcoord2'
      rw [hgate2] at hsub2
      rw [Matrix.sub_mulVec]
      simpa [Pi.sub_apply] using hsub2
    have hdiff :
        (sig (τ * firstSlope θ' p.1 p.2 + Real.log r) -
          sig ((τ + 1) * firstSlope θ' p.1 p.2 + Real.log r)) *
          ((Params.headValue θ - Params.headValue θ').mulVec p.1 a) = 0 := by
      linear_combination hbase - hbase_two
    have hsig_ne :
        sig (τ * firstSlope θ' p.1 p.2 + Real.log r) -
          sig ((τ + 1) * firstSlope θ' p.1 p.2 + Real.log r) ≠ 0 := by
      intro hzero
      have hsig_eq :
          sig (τ * firstSlope θ' p.1 p.2 + Real.log r) =
            sig ((τ + 1) * firstSlope θ' p.1 p.2 + Real.log r) := by
        linarith
      have harg := sig_injective hsig_eq
      have hslope_zero : firstSlope θ' p.1 p.2 = 0 := by
        linarith
      exact hp.1.2 hslope_zero
    exact mul_eq_zero.mp hdiff |>.resolve_left hsig_ne
  let Q : MvPolynomial (ProbeVar d) ℝ :=
    matrixMulVecCoordProbePoly (Params.headValue θ - Params.headValue θ') a
  have hQzero : Q = 0 := by
    refine eq_zero_of_eval_eqOn_isOpen
      ((probeEvalHomeomorph d).isOpenMap U hU_open)
      (hU_nonempty.image _) ?_
    intro x hx
    rcases hx with ⟨p, hpU, rfl⟩
    change MvPolynomial.eval (probeEval p) Q = 0
    simpa [Q, eval_matrixMulVecCoordProbePoly] using hvanish_open p hpU
  have hEval :
      MvPolynomial.eval (probeEval ((Pi.single bidx 1, 0) : ProbePair d)) Q = 0 := by
    simp [hQzero]
  have hentry :
      (Params.headValue θ - Params.headValue θ') a bidx = 0 := by
    simpa [Q, eval_matrixMulVecCoordProbePoly, matrix_mulVec_single_one]
      using hEval
  exact sub_eq_zero.mp (by simpa [Matrix.sub_apply] using hentry)

/-- At depth one, local eventual agreement on a nonempty open probe region identifies the
attention matrix once the value matrix has been identified. -/
theorem IDL_depth_one_headAttention_eq_of_localTailAgreement
    {d r : Nat} (hr_pos : 0 < r)
    {θ θ' : Params 1 d} {O : Set (ProbePair d)}
    (hO_open : IsOpen O) (hO_nonempty : O.Nonempty)
    (hagree :
      ∀ p : ProbePair d, p ∈ O ->
        ∃ T : ℝ, 0 ≤ T ∧ RealTailObservableAgreementAt r θ θ' p T)
    (hvalue : Params.headValue θ = Params.headValue θ')
    (hvalue_ne : Params.headValue θ ≠ 0) :
    Params.headAttention θ = Params.headAttention θ' := by
  classical
  rcases exists_matrix_entry_ne_zero_of_ne_zero hvalue_ne with ⟨i, j, hij⟩
  let Urow : Set (ProbePair d) :=
    {p | (Params.headValue θ).mulVec p.1 i ≠ 0}
  have hrowPoly :
      IsNonzeroProbePolynomial d
        (fun p : ProbePair d => (Params.headValue θ).mulVec p.1 i) :=
    ⟨matrixMulVecCoordProbePoly (Params.headValue θ) i,
      matrixMulVecCoordProbePoly_ne_zero_of_entry_ne_zero hij,
      by
        intro p
        simpa using eval_matrixMulVecCoordProbePoly (Params.headValue θ) i p⟩
  have hUrow_open : IsOpen Urow := by
    simpa [Urow] using hrowPoly.isOpen_ne_zero
  have hUrow_dense : Dense Urow := by
    simpa [Urow] using hrowPoly.dense_ne_zero
  let U : Set (ProbePair d) := O ∩ Urow
  have hOpen : IsOpen U := hO_open.inter hUrow_open
  have hNonempty : U.Nonempty := by
    simpa [U] using hUrow_dense.inter_open_nonempty O hO_open hO_nonempty
  have hFirstAttention :
      firstAttention θ = firstAttention θ' := by
    refine firstAttention_eq_of_isOpen_nonempty_probe_set_firstSlope_eq
      (U := U) hOpen hNonempty ?_
    intro p hp
    rcases hagree p hp.1 with ⟨T, hT_nonneg, hAgree⟩
    let τ : ℝ := T + 1
    have hτ_gt : T < τ := by
      dsimp [τ]
      linarith
    have hτ_pos : 0 < τ := by
      dsimp [τ]
      linarith
    have hobs := hAgree τ hτ_gt
    rw [Fobs_depth_one_of_pos hr_pos θ p.1 p.2 hτ_pos,
      Fobs_depth_one_of_pos hr_pos θ' p.1 p.2 hτ_pos] at hobs
    have hcoord := congrFun hobs i
    rw [← hvalue] at hcoord
    have hgate_coord :
        (sig (τ * firstSlope θ p.1 p.2 + Real.log r) •
            (Params.headValue θ).mulVec p.1) i =
          (sig (τ * firstSlope θ' p.1 p.2 + Real.log r) •
            (Params.headValue θ).mulVec p.1) i := by
      simpa [Pi.add_apply] using add_left_cancel hcoord
    have hgate :
        sig (τ * firstSlope θ p.1 p.2 + Real.log r)
            * (Params.headValue θ).mulVec p.1 i =
          sig (τ * firstSlope θ' p.1 p.2 + Real.log r)
            * (Params.headValue θ).mulVec p.1 i := by
      simpa [Pi.smul_apply, smul_eq_mul] using hgate_coord
    have hsig :
        sig (τ * firstSlope θ p.1 p.2 + Real.log r) =
          sig (τ * firstSlope θ' p.1 p.2 + Real.log r) :=
      mul_right_cancel₀ hp.2 hgate
    have harg :
        τ * firstSlope θ p.1 p.2 + Real.log r =
          τ * firstSlope θ' p.1 p.2 + Real.log r :=
      sig_injective hsig
    have hmul :
        τ * firstSlope θ p.1 p.2 =
          τ * firstSlope θ' p.1 p.2 :=
      add_right_cancel harg
    exact mul_left_cancel₀ (ne_of_gt hτ_pos) hmul
  have hθ : firstAttention θ = Params.headAttention θ := by
    simpa [Params.headAttention, Params.headLayer] using
      firstAttention_eq_of_pos θ (by norm_num : 0 < 1)
  have hθ' : firstAttention θ' = Params.headAttention θ' := by
    simpa [Params.headAttention, Params.headLayer] using
      firstAttention_eq_of_pos θ' (by norm_num : 0 < 1)
  calc
    Params.headAttention θ = firstAttention θ := hθ.symm
    _ = firstAttention θ' := hFirstAttention
    _ = Params.headAttention θ' := hθ'

/-- Depth-one genericity, unpacked as the nonzero first value matrix. -/
theorem texGenericBase_headValue_ne_zero {d : Nat} {θ : Params 1 d}
    (hθ : TexGeneric 1 d θ) :
    Params.headValue θ ≠ 0 := by
  have hbase : TexGenericBaseClauses d θ := by
    simpa using hθ
  simpa [Params.headValue, Params.headLayer, paramStream_apply_of_lt] using
    hbase.value_ne_zero

/-- Depth-one genericity, unpacked as the nonzero first attention matrix. -/
theorem texGenericBase_headAttention_ne_zero {d : Nat} {θ : Params 1 d}
    (hθ : TexGeneric 1 d θ) :
    Params.headAttention θ ≠ 0 := by
  have hbase : TexGenericBaseClauses d θ := by
    simpa using hθ
  simpa [Params.headAttention, Params.headLayer, paramStream_apply_of_lt] using
    hbase.attention_ne_zero

/-- Depth-one genericity gives the nonzero visible-tail matrix used to build `O_star`. -/
theorem texGenericBase_visibleTailMatrix_ne_zero {d : Nat} {θ : Params 1 d}
    (hθ : TexGeneric 1 d θ) :
    realVprod (paramStream θ) 1 ≠ 0 := by
  have hbase : TexGenericBaseClauses d θ := by
    simpa using hθ
  simpa [realVprod, paramStream_apply_of_lt] using hbase.value_ne_zero

/-- A concrete nonzero entry of the first value matrix supplied by depth-one
genericity.  This is the row/coordinate chosen in the TeX base case. -/
theorem texGenericBase_exists_headValue_entry_ne_zero {d : Nat} {θ : Params 1 d}
    (hθ : TexGeneric 1 d θ) :
    ∃ i j : Fin d, Params.headValue θ i j ≠ 0 :=
  exists_matrix_entry_ne_zero_of_ne_zero (texGenericBase_headValue_ne_zero hθ)

/-- A concrete nonzero entry of the first attention matrix supplied by depth-one
genericity. -/
theorem texGenericBase_exists_headAttention_entry_ne_zero {d : Nat} {θ : Params 1 d}
    (hθ : TexGeneric 1 d θ) :
    ∃ i j : Fin d, Params.headAttention θ i j ≠ 0 :=
  exists_matrix_entry_ne_zero_of_ne_zero (texGenericBase_headAttention_ne_zero hθ)

/-- The open dense probe-genericity package specialized to the depth-one base case. -/
def texGenericBase_oStarGenericAssumptions
    {d r : Nat} {θ θ' : Params 1 d}
    (D : IDLData 1 d r θ θ') :
    OStarGenericAssumptions 1 d θ' D.O :=
  OStarGenericAssumptions.ofMatrixNonzero D.O_open D.O_nonempty
    (by
      simpa [Params.headAttention, Params.headLayer, firstAttention,
        paramStream_apply_of_lt] using
        texGenericBase_headAttention_ne_zero D.primed_generic)
    (by
      intro j hj2 hj1
      omega)
    (texGenericBase_visibleTailMatrix_ne_zero D.primed_generic)

/-- The TeX base-case generic probe set `O_g`: probes in `O` for which the primed
first slope and visible first value row are both nonzero. -/
abbrev IDLDepthOneGenericProbeSet
    {d r : Nat} {θ θ' : Params 1 d}
    (D : IDLData 1 d r θ θ') : Set (ProbePair d) :=
  O_star θ' D.O

theorem IDLDepthOneGenericProbeSet_isOpen
    {d r : Nat} {θ θ' : Params 1 d}
    (D : IDLData 1 d r θ θ') :
    IsOpen (IDLDepthOneGenericProbeSet D) :=
  O_star_isOpen_of_generic (texGenericBase_oStarGenericAssumptions D)

theorem IDLDepthOneGenericProbeSet_nonempty
    {d r : Nat} {θ θ' : Params 1 d}
    (D : IDLData 1 d r θ θ') :
    (IDLDepthOneGenericProbeSet D).Nonempty :=
  O_star_nonempty_of_generic (texGenericBase_oStarGenericAssumptions D)

/-- A selected depth-one probe carrying the nonzero primed slope and visible-coordinate
facts needed by the pole-transfer and two-time arguments. -/
structure IDLDepthOneProbeData
    {d r : Nat} {θ θ' : Params 1 d}
    (D : IDLData 1 d r θ θ') where
  probe : ProbePair d
  mem_generic_probe : probe ∈ IDLDepthOneGenericProbeSet D
  iota : Fin d
  visible_iota_ne : visibleTailCoord θ' probe.1 iota ≠ 0

namespace IDLDepthOneProbeData

variable {d r : Nat} {θ θ' : Params 1 d}
variable {D : IDLData 1 d r θ θ'}

theorem mem_O (P : IDLDepthOneProbeData D) :
    P.probe ∈ D.O :=
  O_star_mem_base P.mem_generic_probe

theorem primed_firstSlope_ne (P : IDLDepthOneProbeData D) :
    firstSlope θ' P.probe.1 P.probe.2 ≠ 0 :=
  O_star_firstSlope_ne P.mem_generic_probe

theorem primed_visibleTailVector_ne (P : IDLDepthOneProbeData D) :
    visibleTailVector θ' P.probe.1 ≠ 0 :=
  O_star_visibleTailVector_ne P.mem_generic_probe

end IDLDepthOneProbeData

/-- The matrix-matching content of the depth-one base case from only the local open
tail-agreement invariant. -/
theorem IDL_depth_one_matching_of_localTailAgreement
    {d r : Nat} (hr : 2 <= r)
    {θ θ' : Params 1 d}
    (D : IDLData 1 d r θ θ') :
    FirstLayerMatchedData θ θ' := by
  have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num : 0 < 2) hr
  have hvalue : Params.headValue θ = Params.headValue θ' :=
    IDL_depth_one_headValue_eq_of_localTailAgreement hr
      D.O_open D.O_nonempty
      (fun p hp => D.realTailObservableAgreementAt_of_mem hp)
      D.primed_generic
  have hvalue_ne : Params.headValue θ ≠ 0 := by
    rw [hvalue]
    exact texGenericBase_headValue_ne_zero D.primed_generic
  have hattention : Params.headAttention θ = Params.headAttention θ' :=
    IDL_depth_one_headAttention_eq_of_localTailAgreement hr_pos
      D.O_open D.O_nonempty
      (fun p hp => D.realTailObservableAgreementAt_of_mem hp)
      hvalue hvalue_ne
  exact FirstLayerMatchedData.ofComponentEq hvalue hattention hvalue_ne

/-- The matrix-matching content of the depth-one base case.

The path/open-set IDL invariant supplies eventual agreement for constant paths whose
probes lie in the current open region `D.O`.  The depth-one analytic base case must turn
that local eventual agreement into equality of the first value and attention matrices. -/
theorem IDL_depth_one_matching_of_probeData
    {d r : Nat} (_hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params 1 d}
    (D : IDLData 1 d r θ θ')
    (_P : IDLDepthOneProbeData D) :
    FirstLayerMatchedData θ θ' := by
  exact IDL_depth_one_matching_of_localTailAgreement hr D

/-- Depth-one case of the path/open-set identifiability theorem. -/
theorem IDL_depth_one
    {d r : Nat} (hd : 2 <= d) (hr : 2 <= r)
    {θ θ' : Params 1 d} :
    IDLData 1 d r θ θ' -> θ = θ' := by
  intro D
  classical
  let p : ProbePair d := Classical.choose (IDLDepthOneGenericProbeSet_nonempty D)
  have hp : p ∈ IDLDepthOneGenericProbeSet D :=
    Classical.choose_spec (IDLDepthOneGenericProbeSet_nonempty D)
  let c := visibleCoordinateChoiceOfOStar hp
  let P : IDLDepthOneProbeData D :=
    { probe := p
      mem_generic_probe := hp
      iota := c.iota
      visible_iota_ne := c.nonzero }
  exact IDL_nLayer_depth_one_stitch
    (IDL_depth_one_matching_of_probeData hd hr D P)

end TransformerIdentifiability.NLayer
