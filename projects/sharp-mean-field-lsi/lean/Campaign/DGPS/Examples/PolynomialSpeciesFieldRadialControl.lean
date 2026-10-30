import DGPS.Examples.PolynomialSpeciesDeficitTaylor
import DGPS.Examples.PolynomialSpeciesReducedRadial
import Mathlib.Analysis.Calculus.TaylorIntegral

/-! Field and independent-reference control for the SAME actual reduced
physical deficit. Derivatives retain the moving graph. No selected-reference
root is differentiated and no radial estimate is a premise. -/

noncomputable section
open Filter Topology NormedSpace MeasureTheory
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private abbrev Theta := (ℝ × ℝ) × ℝ
private abbrev Amp := ℝ × ℝ
private abbrev Joint := Theta × Amp

-- Cache the canonical operator-space instances for the iterated derivative.
local instance fieldRadialOperatorInstance0 : NormedAddCommGroup (Amp →L[ℝ] ℝ) := inferInstance
local instance fieldRadialOperatorInstance1 : NormedSpace ℝ (Amp →L[ℝ] ℝ) := inferInstance
local instance fieldRadialOperatorInstance2 : NormedAddCommGroup (Amp →L[ℝ] Amp →L[ℝ] ℝ) := inferInstance
local instance fieldRadialOperatorInstance3 : NormedSpace ℝ (Amp →L[ℝ] Amp →L[ℝ] ℝ) := inferInstance

/-- The actual physical reduced deficit's amplitude Hessian, with all other parameters free. -/
def polynomialReducedDeficitAmplitudeHessian (ψ : PolynomialRangeParameters → E_STR02969)
    (z : ((ℝ × ℝ) × ℝ) × (ℝ × ℝ)) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ ((fun x => polynomialReducedDeficit ψ (polynomialGapSlice z.1 x)))) z.2

private def jointMap (z : Joint) : PolynomialRangeParameters := polynomialGapSlice z.1 z.2

private theorem jointMap_smooth : ContDiff ℝ ∞ jointMap := by
  exact contDiff_snd.fst.prodMk (contDiff_snd.snd.prodMk
    (contDiff_fst.fst.prodMk contDiff_fst.snd))

private theorem jointMap_zero : jointMap 0 = 0 := by ext <;> rfl

private theorem joint_smooth {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hψ : ContDiffOn ℝ ∞ ψ U) :
    ContDiffOn ℝ ∞ (fun z : Joint =>
      polynomialReducedDeficit ψ (polynomialGapSlice z.1 z.2)) (jointMap ⁻¹' U) := by
  exact (polynomialReducedDeficit_smooth hψ).comp jointMap_smooth.contDiffOn
    (fun _ hz => hz)

/-- Genuine joint regularity of the partial amplitude Hessian near the origin. -/
theorem polynomialReducedDeficitAmplitudeHessian_smooth_at_zero {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hψ : ContDiffOn ℝ ∞ ψ U) :
    ContDiffAt ℝ ∞ (polynomialReducedDeficitAmplitudeHessian ψ) 0 := by
  have hW : IsOpen (jointMap ⁻¹' U) := hU.preimage jointMap_smooth.continuous
  have h0W : (0 : Joint) ∈ jointMap ⁻¹' U := by
    change jointMap 0 ∈ U
    rw [jointMap_zero]
    exact h0U
  have hJ : ContDiffAt ℝ ∞ (fun z : Joint => polynomialReducedDeficit ψ (polynomialGapSlice z.1 z.2)) 0 :=
    (joint_smooth hψ).contDiffAt (hW.mem_nhds h0W)
  let q := fun z : Joint × Amp => (z.1.1, z.2)
  have hq : ContDiff ℝ ∞ q := by dsimp only [q]; fun_prop
  have hq0 : q (0 : Joint × Amp) = 0 := by ext <;> rfl
  have hF : ContDiffAt ℝ ∞
      (Function.uncurry (fun (z : Joint) (y : Amp) => (fun x => polynomialReducedDeficit ψ (polynomialGapSlice z.1 x)) y)) (0, 0) := by
    have h := hJ.comp (0 : Joint × Amp) hq.contDiffAt
    have he : (Function.uncurry (fun (z : Joint) (y : Amp) => (fun x => polynomialReducedDeficit ψ (polynomialGapSlice z.1 x)) y)) =
        (fun z : Joint × Amp => polynomialReducedDeficit ψ (polynomialGapSlice z.1.1 z.2)) := rfl
    rw [he]
    convert h using 1 <;> rfl
  have hD : ContDiffAt ℝ ∞ (fun z : Joint =>
      fderiv ℝ ((fun x => polynomialReducedDeficit ψ (polynomialGapSlice z.1 x))) z.2) 0 :=
    ContDiffAt.fderiv hF contDiffAt_snd (by simp)
  have hDF : ContDiffAt ℝ ∞
      (Function.uncurry (fun (z : Joint) (y : Amp) =>
        fderiv ℝ ((fun x => polynomialReducedDeficit ψ (polynomialGapSlice z.1 x))) y)) (0, 0) := by
    have h := hD.comp (0 : Joint × Amp) hq.contDiffAt
    have he : (Function.uncurry (fun (z : Joint) (y : Amp) =>
        fderiv ℝ ((fun x => polynomialReducedDeficit ψ (polynomialGapSlice z.1 x))) y)) =
        (fun z : Joint × Amp => fderiv ℝ ((fun x => polynomialReducedDeficit ψ (polynomialGapSlice z.1.1 x))) z.2) := rfl
    rw [he]
    convert h using 1 <;> rfl
  exact ContDiffAt.fderiv hDF contDiffAt_snd (by simp)

private theorem radial_integral (F : ℝ × ℝ → ℝ) (W : Set (ℝ × ℝ))
    (hW : IsOpen W) (hF : ContDiffOn ℝ ∞ F W) (x : ℝ × ℝ)
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • x ∈ W) (hd0 : fderiv ℝ F 0 = 0) :
    fderiv ℝ F x x = ∫ t in (0 : ℝ)..1, fderiv ℝ (fderiv ℝ F) (t • x) x x := by
  have hDF : ContDiffOn ℝ 1 (fderiv ℝ F) W := hF.fderiv_of_isOpen hW (by simp)
  have hD2 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ F)) W :=
    hDF.fderiv_of_isOpen hW (by simp)
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => fderiv ℝ F (s • x) x)
        (fderiv ℝ (fderiv ℝ F) (t • x) x x) t := by
    intro t ht
    have hFd := (hDF.contDiffAt (hW.mem_nhds (hmem t ht))).differentiableAt (by simp)
    have hs : HasDerivAt (fun s : ℝ => s • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    have hh := hFd.hasFDerivAt.comp_hasDerivAt t hs
    simpa using hh.clm_apply (hasDerivAt_const t x)
  have hc : ContinuousOn (fun t : ℝ => fderiv ℝ (fderiv ℝ F) (t • x) x x)
      (Set.Icc (0 : ℝ) 1) := by
    have hh := hD2.continuousOn.comp (continuous_id.smul continuous_const).continuousOn hmem
    exact (hh.clm_apply continuousOn_const).clm_apply continuousOn_const
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t ht => hd t (by simpa only [Set.uIcc_of_le zero_le_one] using ht))
    (hc.intervalIntegrable_of_Icc zero_le_one)
  simpa only [one_smul, zero_smul, hd0, zero_apply, sub_zero] using he.symm

/-- Exact FTC factor of the actual radial deficit, before choosing field,
reference or amplitude. Universal zero-amplitude stationarity is obtained from
the actual DeficitTaylor producer, rather than added as a radial premise. -/
theorem polynomialReducedDeficitRadial_integral
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (θ : (ℝ × ℝ) × ℝ) (x : ℝ × ℝ)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, polynomialGapSlice θ (t • x) ∈ U) :
    polynomialReducedDeficitRadial ψ θ x = ∫ t in (0 : ℝ)..1,
      polynomialReducedDeficitAmplitudeHessian ψ (θ, t • x) x x := by
  let q := polynomialGapSlice θ
  let W := q ⁻¹' U
  let F := fun y : ℝ × ℝ => polynomialReducedDeficit ψ (q y)
  have hq : ContDiff ℝ ∞ q :=
    contDiff_fst.prodMk (contDiff_snd.prodMk (contDiff_const.prodMk contDiff_const))
  have hW : IsOpen W := hU.preimage hq.continuous
  have hF : ContDiffOn ℝ ∞ F W :=
    (polynomialReducedDeficit_smooth hψ).comp hq.contDiffOn (fun _ hz => hz)
  have hd0 := (polynomialReducedDeficit_quadratic_factor hU hψ hzero θ x hseg).2.1
  exact radial_integral F W hW hF x hseg hd0

private theorem second_neg_comp (f : Amp → ℝ) (x y z : Amp) :
    fderiv ℝ (fderiv ℝ (fun q : Amp => f (-q))) x y z =
      fderiv ℝ (fderiv ℝ f) (-x) y z := by
  let n : Amp ≃L[ℝ] Amp := (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv
  have hn := n.iteratedFDerivWithin_comp_right f
    (s := Set.univ) uniqueDiffOn_univ (Set.mem_univ (n x)) 2
  have he := congrArg (fun L => L ![y, z]) hn
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, Function.comp_def,
    iteratedFDeriv_two_apply, Fin.init, Fin.last,
    Matrix.cons_val_zero, Matrix.cons_val_one, n,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.coe_neg] at he
  change fderiv ℝ (fderiv ℝ (fun q : Amp => f (-q))) x y z =
    fderiv ℝ (fderiv ℝ f) (-x) (-y) (-z) at he
  simpa only [map_neg, ContinuousLinearMap.neg_apply, neg_neg] using he

private def fieldHessian (ψ : PolynomialRangeParameters → E_STR02969)
    (q : ℝ × Amp) : Amp →L[ℝ] Amp →L[ℝ] ℝ :=
  polynomialReducedDeficitAmplitudeHessian ψ (((q.1, 0), 0), q.2)

private theorem fieldHessian_smooth_at_zero {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hψ : ContDiffOn ℝ ∞ ψ U) :
    ContDiffAt ℝ ∞ (fieldHessian ψ) 0 := by
  have hq : ContDiff ℝ ∞ (fun q : ℝ × Amp => ((((q.1, 0), 0), q.2) : Joint)) := by fun_prop
  have hc := (polynomialReducedDeficitAmplitudeHessian_smooth_at_zero hU h0U hψ).comp
    (0 : ℝ × Amp) hq.contDiffAt
  exact hc

/-- The field/amplitude Hessian is genuinely even near the actual origin.
Two amplitude derivatives preserve the sign of the joint half-turn, so no
pointwise eigenfeature relation or selected-root derivative enters. -/
private theorem fieldHessian_even_near {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ (0 : PolynomialRangeParameters) = 0)
    (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w) :
    (fun q : ℝ × Amp => fieldHessian ψ (-q)) =ᶠ[𝓝 0] fieldHessian ψ := by
  obtain ⟨δ, hδ, hparity⟩ := polynomial_reduced_deficit_half_turn
    hU h0U hN h0N hψ hψ0 hψN hgraph
  have he : ∀ᶠ q : ℝ × Amp in 𝓝 0,
      ‖((q.2.1, q.2.2, (q.1, 0), 0) : PolynomialRangeParameters)‖ < δ := by
    have hc : Continuous (fun q : ℝ × Amp =>
        ‖((q.2.1, q.2.2, (q.1, 0), 0) : PolynomialRangeParameters)‖) := by fun_prop
    exact (hc.continuousAt (x := (0 : ℝ × Amp))).eventually (gt_mem_nhds (by simpa using hδ))
  filter_upwards [he] with q hq
  let fp := fun x : Amp => polynomialReducedDeficit ψ (polynomialGapSlice ((q.1, 0), 0) x)
  let fm := fun x : Amp => polynomialReducedDeficit ψ (polynomialGapSlice ((-q.1, 0), 0) x)
  have hlocal : (fun x : Amp => fm (-x)) =ᶠ[𝓝 q.2] fp := by
    have hc : Continuous (fun x : Amp =>
        ‖((x.1, x.2, (q.1, 0), 0) : PolynomialRangeParameters)‖) := by fun_prop
    filter_upwards [(hc.continuousAt (x := q.2)).eventually (gt_mem_nhds hq)] with x hx
    exact hparity x.1 x.2 q.1 0 0 hx
  have hd := ((hlocal.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).self_of_nhds
  apply ContinuousLinearMap.ext
  intro y
  apply ContinuousLinearMap.ext
  intro z
  have hh := congrArg (fun L : Amp →L[ℝ] Amp →L[ℝ] ℝ => L y z) hd
  rw [second_neg_comp] at hh
  exact hh

/-- Actual joint half-turn symmetry forces the first field/amplitude derivative
of the amplitude Hessian to vanish at the origin. This is the cancellation
behind the cubic field-amplitude term, proved from the SAME graph. -/
theorem polynomialFieldHessian_fderiv_origin_zero
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ (0 : PolynomialRangeParameters) = 0)
    (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w) :
    fderiv ℝ (fieldHessian ψ) 0 = 0 := by
  have he := fieldHessian_even_near hU h0U hN h0N hψ hψ0 hψN hgraph
  let n : (ℝ × Amp) ≃L[ℝ] (ℝ × Amp) := (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv
  have hn := n.comp_right_fderiv (f := fieldHessian ψ) (x := 0)
  have hd := he.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (fieldHessian ψ ∘ n) 0 = _ at hd
  rw [hn] at hd
  apply ContinuousLinearMap.ext
  intro q
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  have hh := congrArg (fun L : (ℝ × Amp) →L[ℝ] Amp →L[ℝ] Amp →L[ℝ] ℝ => L q x y) hd
  simp only [n, ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.coe_neg, neg_zero, map_neg, ContinuousLinearMap.neg_apply] at hh
  change (fderiv ℝ (fieldHessian ψ) 0) (-q) x y =
    (fderiv ℝ (fieldHessian ψ) 0) q x y at hh
  simp only [map_neg, ContinuousLinearMap.neg_apply] at hh
  change fderiv ℝ (fieldHessian ψ) 0 q x y = 0
  linarith only [hh]

/-- A uniform actual Hessian bound with the field-linear amplitude gain.
Local C2 regularity of this Hessian and its proved even-origin cancellation
supply the bound by the stock convex mean-value theorem. -/
theorem polynomialDeficitHessian_field_control
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ (0 : PolynomialRangeParameters) = 0)
    (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (h s : ℝ) (x : Amp),
      ‖((((h, s), 0), x) : Joint)‖ < δ →
      ‖polynomialReducedDeficitAmplitudeHessian ψ (((h, s), 0), x) -
        polynomialReducedDeficitAmplitudeHessian ψ (((0, 0), 0), x)‖ ≤
          C * (|h| * ‖x‖ + h ^ 2 + |s|) := by
  have hHs := polynomialReducedDeficitAmplitudeHessian_smooth_at_zero hU h0U hψ
  have hFs := fieldHessian_smooth_at_zero hU h0U hψ
  have hD0 := polynomialFieldHessian_fderiv_origin_zero hU h0U hN h0N hψ hψ0 hψN hgraph
  have hDFs := hFs.fderiv_right (m := 1) (by simp)
  obtain ⟨K, V, hV, hLipD⟩ := hDFs.exists_lipschitzOnWith
  obtain ⟨L, W, hW, hLipH⟩ := (hHs.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).exists_lipschitzOnWith
  have hDiff : ∀ᶠ q : ℝ × Amp in 𝓝 0, DifferentiableAt ℝ (fieldHessian ψ) q :=
    ((hFs.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun _ hc => hc.differentiableAt (by simp))
  obtain ⟨dF, hdF, hballF⟩ := Metric.mem_nhds_iff.1 (inter_mem hV hDiff)
  obtain ⟨dH, hdH, hballH⟩ := Metric.mem_nhds_iff.1 hW
  let δ := min dF dH
  let C : ℝ := (K : ℝ) + (L : ℝ) + 1
  have hδ : 0 < δ := lt_min hdF hdH
  have hC : 0 < C := by dsimp only [C]; positivity
  have hKC : (K : ℝ) ≤ C := by dsimp only [C]; linarith [L.coe_nonneg]
  have hLC : (L : ℝ) ≤ C := by dsimp only [C]; linarith [K.coe_nonneg]
  have hDiffBound (q : ℝ × Amp) (hq : ‖q‖ < δ) :
      DifferentiableAt ℝ (fieldHessian ψ) q ∧
        ‖fderiv ℝ (fieldHessian ψ) q‖ ≤ (K : ℝ) * ‖q‖ := by
    have hqm : q ∈ Metric.ball 0 dF := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hq.trans_le (min_le_left _ _)
    have h0m : (0 : ℝ × Amp) ∈ Metric.ball 0 dF := by simpa using hdF
    refine ⟨(hballF hqm).2, ?_⟩
    have hb := hLipD.dist_le_mul q (hballF hqm).1 0 (hballF h0m).1
    simpa only [dist_eq_norm, hD0, sub_zero] using hb
  refine ⟨δ, C, hδ, hC, fun h s x hsmall => ?_⟩
  have hfieldNorm : ‖(h, x)‖ ≤ ‖((((h, s), 0), x) : Joint)‖ := by
    change max ‖h‖ ‖x‖ ≤ max ‖(((h, s), (0 : ℝ)))‖ ‖x‖
    exact max_le_max ((norm_fst_le (h, s)).trans (norm_fst_le ((h, s), (0 : ℝ)))) le_rfl
  let R := max |h| ‖x‖
  have hR : 0 ≤ R := le_trans (norm_nonneg x) (le_max_right _ _)
  have hRd : R < δ := by
    change ‖(h, x)‖ < δ
    exact hfieldNorm.trans_lt hsmall
  have hfield : ‖fieldHessian ψ (h, x) - fieldHessian ψ (0, x)‖ ≤
      (K : ℝ) * (|h| * ‖x‖ + h ^ 2) := by
    have hd (q : ℝ × Amp) (hq : q ∈ Metric.closedBall 0 R) :
        DifferentiableAt ℝ (fieldHessian ψ) q :=
      (hDiffBound q ((by simpa only [Metric.mem_closedBall, dist_zero_right] using hq : ‖q‖ ≤ R).trans_lt hRd)).1
    have hb (q : ℝ × Amp) (hq : q ∈ Metric.closedBall 0 R) :
        ‖fderiv ℝ (fieldHessian ψ) q‖ ≤ (K : ℝ) * R := by
      have hqn : ‖q‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hq
      exact (hDiffBound q (hqn.trans_lt hRd)).2.trans
        (mul_le_mul_of_nonneg_left hqn K.coe_nonneg)
    have h0x : ((0 : ℝ), x) ∈ Metric.closedBall 0 R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      change max ‖(0 : ℝ)‖ ‖x‖ ≤ R
      rw [norm_zero, max_eq_right (norm_nonneg x)]
      exact le_max_right _ _
    have hhx : (h, x) ∈ Metric.closedBall 0 R := by
      simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs]
      exact le_rfl
    have hm := (convex_closedBall (0 : ℝ × Amp) R).norm_image_sub_le_of_norm_fderiv_le hd hb h0x hhx
    have hn : ‖(h, x) - ((0 : ℝ), x)‖ = |h| := by
      simp only [Prod.mk_sub_mk, sub_zero, sub_self, Prod.norm_def, norm_zero,
        Real.norm_eq_abs, max_eq_left (abs_nonneg h)]
    rw [hn] at hm
    apply hm.trans
    have hRu : R ≤ |h| + ‖x‖ := max_le (le_add_of_nonneg_right (norm_nonneg x))
      (le_add_of_nonneg_left (abs_nonneg h))
    have he := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hRu K.coe_nonneg) (abs_nonneg h)
    calc _ ≤ (K : ℝ) * (|h| + ‖x‖) * |h| := he
      _ = (K : ℝ) * (|h| * ‖x‖ + h ^ 2) := by nlinarith only [sq_abs h]
  have hHnorm : ‖((((h, 0), 0), x) : Joint)‖ ≤ ‖((((h, s), 0), x) : Joint)‖ := by
    change max (max ‖(h, (0 : ℝ))‖ ‖(0 : ℝ)‖) ‖x‖ ≤ max (max ‖(h, s)‖ ‖(0 : ℝ)‖) ‖x‖
    apply max_le_max _ le_rfl
    apply max_le_max _ le_rfl
    change max ‖h‖ ‖(0 : ℝ)‖ ≤ max ‖h‖ ‖s‖
    rw [norm_zero]
    exact max_le_max le_rfl (norm_nonneg s)
  have hH0 : ((((h, s), 0), x) : Joint) ∈ W :=
    hballH (by rw [Metric.mem_ball, dist_zero_right]; exact hsmall.trans_le (min_le_right _ _))
  have hH1 : ((((h, 0), 0), x) : Joint) ∈ W :=
    hballH (by
      rw [Metric.mem_ball, dist_zero_right]
      exact hHnorm.trans_lt (hsmall.trans_le (min_le_right _ _)))
  have hs := hLipH.dist_le_mul (((((h, s), 0), x)) : Joint) hH0 (((((h, 0), 0), x)) : Joint) hH1
  have hsd : ‖((((h, s), 0), x) : Joint) - ((((h, 0), 0), x) : Joint)‖ = |s| := by
    simp only [Prod.mk_sub_mk, sub_self, sub_zero, Prod.norm_def, norm_zero, Real.norm_eq_abs,
      max_self, max_eq_left (abs_nonneg s), max_eq_right (abs_nonneg s)]
  rw [dist_eq_norm, dist_eq_norm, hsd] at hs
  calc
    _ ≤ ‖polynomialReducedDeficitAmplitudeHessian ψ (((h, s), 0), x) -
        polynomialReducedDeficitAmplitudeHessian ψ (((h, 0), 0), x)‖ +
      ‖fieldHessian ψ (h, x) - fieldHessian ψ (0, x)‖ := by
        exact norm_sub_le_norm_sub_add_norm_sub
          (polynomialReducedDeficitAmplitudeHessian ψ (((h, s), 0), x))
          (polynomialReducedDeficitAmplitudeHessian ψ (((h, 0), 0), x))
          (polynomialReducedDeficitAmplitudeHessian ψ (((0, 0), 0), x))
    _ ≤ (L : ℝ) * |s| + (K : ℝ) * (|h| * ‖x‖ + h ^ 2) := add_le_add hs hfield
    _ ≤ C * (|h| * ‖x‖ + h ^ 2 + |s|) := by
      have hk := mul_le_mul_of_nonneg_right hKC (show 0 ≤ |h| * ‖x‖ + h ^ 2 by positivity)
      have hl := mul_le_mul_of_nonneg_right hLC (abs_nonneg s)
      nlinarith only [hk, hl]

private theorem amplitude_segment_norm (θ : Theta) (x : Amp) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖(θ, t • x)‖ ≤ ‖(θ, x)‖ := by
  change max ‖θ‖ ‖t • x‖ ≤ max ‖θ‖ ‖x‖
  apply max_le_max le_rfl
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg x) ht.2

private theorem amplitude_hessian_segment_integrable
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ ∞ ψ U) (θ : Theta) (x : Amp)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, polynomialGapSlice θ (t • x) ∈ U) :
    IntervalIntegrable (fun t : ℝ =>
      polynomialReducedDeficitAmplitudeHessian ψ (θ, t • x) x x) volume 0 1 := by
  let W := polynomialGapSlice θ ⁻¹' U
  let F := fun y : Amp => polynomialReducedDeficit ψ (polynomialGapSlice θ y)
  have hq : ContDiff ℝ ∞ (polynomialGapSlice θ) :=
    contDiff_fst.prodMk (contDiff_snd.prodMk (contDiff_const.prodMk contDiff_const))
  have hW : IsOpen W := hU.preimage hq.continuous
  have hF : ContDiffOn ℝ ∞ F W :=
    (polynomialReducedDeficit_smooth hψ).comp hq.contDiffOn (fun _ hz => hz)
  have hd : ContDiffOn ℝ 1 (fderiv ℝ F) W := hF.fderiv_of_isOpen hW (by simp)
  have hdd : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ F)) W := hd.fderiv_of_isOpen hW (by simp)
  have hc := hdd.continuousOn.comp (continuous_id.smul continuous_const).continuousOn hseg
  exact ((hc.clm_apply continuousOn_const).clm_apply continuousOn_const).intervalIntegrable_of_Icc zero_le_one

/-- Uniform actual field/reference radial error. The graph assumptions are
exact factual outputs of Common. No radial estimate, derivative bound or
selected-reference-root differentiability is a hypothesis. -/
theorem polynomialReducedDeficitRadial_field_error
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ (0 : PolynomialRangeParameters) = 0)
    (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      (∀ (h s : ℝ) (x : ℝ × ℝ), ‖((((h, s), 0), x) : Joint)‖ < δ →
        polynomialGapSlice ((h, s), 0) x ∈ U) ∧
      ∀ (h s : ℝ) (x : ℝ × ℝ), ‖((((h, s), 0), x) : Joint)‖ < δ →
        |polynomialReducedDeficitRadial ψ ((h, s), 0) x -
          polynomialReducedDeficitRadial ψ ((0, 0), 0) x| ≤
          C * (|h| * ‖x‖ ^ 3 + (h ^ 2 + |s|) * ‖x‖ ^ 2) := by
  obtain ⟨dH, C, hdH, hC, hbound⟩ := polynomialDeficitHessian_field_control
    hU h0U hN h0N hψ hψ0 hψN hgraph
  have hW : IsOpen (jointMap ⁻¹' U) := hU.preimage jointMap_smooth.continuous
  have h0W : (0 : Joint) ∈ jointMap ⁻¹' U := by change jointMap 0 ∈ U; rw [jointMap_zero]; exact h0U
  obtain ⟨dU, hdU, hball⟩ := Metric.mem_nhds_iff.1 (hW.mem_nhds h0W)
  let δ := min dH dU
  have hδ : 0 < δ := lt_min hdH hdU
  have hmem (z : Joint) (hz : ‖z‖ < δ) : polynomialGapSlice z.1 z.2 ∈ U :=
    hball (by rw [Metric.mem_ball, dist_zero_right]; exact hz.trans_le (min_le_right _ _))
  refine ⟨δ, C, hδ, hC, (fun h s x hx => hmem _ hx), fun h s x hx => ?_⟩
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, polynomialGapSlice ((h, s), 0) (t • x) ∈ U :=
    fun t ht => hmem _ ((amplitude_segment_norm ((h, s), 0) x t ht).trans_lt hx)
  have hbaseNorm (y : Amp) : ‖((((0, 0), 0), y) : Joint)‖ ≤ ‖((((h, s), 0), y) : Joint)‖ := by
    change max ‖(0 : Theta)‖ ‖y‖ ≤ max ‖(((h, s), 0) : Theta)‖ ‖y‖
    rw [norm_zero]
    exact max_le_max (norm_nonneg _) le_rfl
  have hseg0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, polynomialGapSlice ((0, 0), 0) (t • x) ∈ U :=
    fun t ht => hmem _ ((hbaseNorm (t • x)).trans
      (amplitude_segment_norm ((h, s), 0) x t ht) |>.trans_lt hx)
  have hi := amplitude_hessian_segment_integrable hU hψ ((h, s), 0) x hseg
  have hi0 := amplitude_hessian_segment_integrable hU hψ ((0, 0), 0) x hseg0
  have hFTC := polynomialReducedDeficitRadial_integral hU hψ hzero ((h, s), 0) x hseg
  have hFTC0 := polynomialReducedDeficitRadial_integral hU hψ hzero ((0, 0), 0) x hseg0
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖polynomialReducedDeficitAmplitudeHessian ψ (((h, s), 0), t • x) x x -
        polynomialReducedDeficitAmplitudeHessian ψ (((0, 0), 0), t • x) x x‖ ≤
      C * (|h| * ‖x‖ ^ 3 + (h ^ 2 + |s|) * ‖x‖ ^ 2) := by
    let A := polynomialReducedDeficitAmplitudeHessian ψ (((h, s), 0), t • x) -
      polynomialReducedDeficitAmplitudeHessian ψ (((0, 0), 0), t • x)
    have htNorm : ‖t • x‖ ≤ ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg x) ht.2
    have hA : ‖A‖ ≤ C * (|h| * ‖x‖ + h ^ 2 + |s|) :=
      (hbound h s (t • x) (((amplitude_segment_norm ((h, s), 0) x t ht).trans_lt hx).trans_le
        (min_le_left _ _))).trans
        (mul_le_mul_of_nonneg_left (by gcongr) hC.le)
    calc
      _ = ‖A x x‖ := rfl
      _ ≤ ‖A x‖ * ‖x‖ := (A x).le_opNorm x
      _ ≤ (‖A‖ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right (A.le_opNorm x) (norm_nonneg x)
      _ ≤ (C * (|h| * ‖x‖ + h ^ 2 + |s|) * ‖x‖) * ‖x‖ := by gcongr
      _ = _ := by ring
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1)
    (C := C * (|h| * ‖x‖ ^ 3 + (h ^ 2 + |s|) * ‖x‖ ^ 2))
    (f := fun t : ℝ =>
      polynomialReducedDeficitAmplitudeHessian ψ (((h, s), 0), t • x) x x -
        polynomialReducedDeficitAmplitudeHessian ψ (((0, 0), 0), t • x) x x) (by
      intro t ht
      apply hpoint t
      have he : t ∈ Set.Ioc (0 : ℝ) 1 := by simpa only [Set.uIoc_of_le zero_le_one] using ht
      exact ⟨he.1.le, he.2⟩)
  rw [intervalIntegral.integral_sub hi hi0, ← hFTC, ← hFTC0] at hb
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hb

/-- The same actual error in the Euclidean amplitude convention of the
bootstrap. All constants precede independent h,s,x and no selected root occurs. -/
theorem polynomialReducedDeficitRadial_field_lower
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ (0 : PolynomialRangeParameters) = 0)
    (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (h s : ℝ) (x : ℝ × ℝ),
      ‖((((h, s), 0), x) : Joint)‖ < δ →
      let R := Real.sqrt (x.1 ^ 2 + x.2 ^ 2)
      polynomialReducedDeficitRadial ψ ((0, 0), 0) x - C * |h| * R ^ 3 -
        C * (h ^ 2 + |s|) * R ^ 2 ≤ polynomialReducedDeficitRadial ψ ((h, s), 0) x := by
  obtain ⟨δ, C, hδ, hC, _, hbound⟩ := polynomialReducedDeficitRadial_field_error
    hU h0U hN h0N hψ hψ0 hψN hgraph hzero
  refine ⟨δ, C, hδ, hC, fun h s x hx => ?_⟩
  let R := Real.sqrt (x.1 ^ 2 + x.2 ^ 2)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hn : ‖x‖ ≤ R := by
    apply (Real.le_sqrt (norm_nonneg x) (add_nonneg (sq_nonneg _) (sq_nonneg _))).2
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_total |x.1| |x.2| with he | he
    · rw [max_eq_right he, sq_abs]
      nlinarith only [sq_nonneg x.1]
    · rw [max_eq_left he, sq_abs]
      nlinarith only [sq_nonneg x.2]
  have he := (abs_le.mp (hbound h s x hx)).1
  have hb : C * (|h| * ‖x‖ ^ 3 + (h ^ 2 + |s|) * ‖x‖ ^ 2) ≤
      C * |h| * R ^ 3 + C * (h ^ 2 + |s|) * R ^ 2 := by
    have h2 := pow_le_pow_left₀ (norm_nonneg x) hn 2
    have h3 := pow_le_pow_left₀ (norm_nonneg x) hn 3
    have hh := mul_le_mul_of_nonneg_left h3 (show 0 ≤ C * |h| by positivity)
    have hs := mul_le_mul_of_nonneg_left h2 (show 0 ≤ C * (h ^ 2 + |s|) by positivity)
    nlinarith only [hh, hs]
  change _ ≤ _
  linarith only [he, hb]

end DGPS.Examples.PolynomialSpecies
