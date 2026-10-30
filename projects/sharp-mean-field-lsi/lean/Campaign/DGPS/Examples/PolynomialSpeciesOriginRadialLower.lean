import DGPS.Examples.PolynomialSpeciesOriginValueLower
import DGPS.Examples.PolynomialSpeciesOriginDeficitHessian
import DGPS.Examples.PolynomialSpeciesJointOddJet
import DGPS.Examples.PolynomialSpeciesReducedRadial
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! The actual pure-origin radial quartic lower bound on ONE supplied graph.
Stock Taylor formulas are applied separately to the value and its derivative;
no value remainder is differentiated and no quartic/radial premise is assumed. -/

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.PolynomialSpecies

private def originValue (ψ : PolynomialRangeParameters → E_STR02969) (x : ℝ × ℝ) : ℝ :=
  polynomialRangeDeficit (0, 0) DGPS.Circle.AngularNormalization.a0 (polynomialGapLift ψ ((0, 0), 0) x)

private theorem origin_lift_smooth {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hψ : ContDiffOn ℝ ∞ ψ U) :
    ContDiffOn ℝ ∞ (polynomialGapLift ψ ((0, 0), 0))
      (polynomialGapSlice ((0, 0), 0) ⁻¹' U) := by
  have hq : ContDiff ℝ ∞ (polynomialGapSlice ((0, 0), 0)) := by
    unfold polynomialGapSlice
    fun_prop
  have hΦ := hψ.comp hq.contDiffOn (fun _ hx => hx)
  have hE := E_STR02969.subtypeL.contDiff.comp_contDiffOn hΦ
  have hlin : ContDiff ℝ ∞ (fun x : ℝ × ℝ =>
      x.1 • cosC2_STR02915 + x.2 • sinC2_STR02915) := by fun_prop
  exact hlin.contDiffOn.add hE

private theorem origin_outer_smooth :
    ContDiff ℝ ∞ (fun u : PeriodicC2_STR02969 => polynomialRangeDeficit (0, 0) DGPS.Circle.AngularNormalization.a0 u) :=
  by
    let V : PolynomialEulerInput → ℝ := fun q => polynomialRangeDeficit q.1 q.2.1 q.2.2
    let q : PeriodicC2_STR02969 → PolynomialEulerInput := fun u =>
      ((0, 0), DGPS.Circle.AngularNormalization.a0, u)
    have hV : ContDiff ℝ ∞ V := polynomialRangeDeficit_smooth
    have hq : ContDiff ℝ ∞ q := contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
    change ContDiff ℝ ∞ (V ∘ q)
    exact hV.comp hq

private theorem origin_smooth {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hψ : ContDiffOn ℝ ∞ ψ U) :
    ContDiffOn ℝ ∞ (originValue ψ) (polynomialGapSlice ((0, 0), 0) ⁻¹' U) :=
  origin_outer_smooth.comp_contDiffOn (origin_lift_smooth hψ)

private theorem origin_lower_jets {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ (0 : PolynomialRangeParameters) = 0)
    (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hamp : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0) :
    originValue ψ 0 = 0 ∧ fderiv ℝ (originValue ψ) 0 = 0 ∧
      fderiv ℝ (fderiv ℝ (originValue ψ)) 0 = 0 ∧
      ∀ x : ℝ × ℝ, iteratedFDeriv ℝ 3 (originValue ψ) 0 (fun _ => x) = 0 := by
  let W := polynomialGapSlice ((0, 0), 0) ⁻¹' U
  have hq : Continuous (polynomialGapSlice ((0, 0), 0)) := by
    unfold polynomialGapSlice
    fun_prop
  have hW : IsOpen W := hU.preimage hq
  have h0W : (0 : ℝ × ℝ) ∈ W := h0U
  have hL0 : polynomialGapLift ψ ((0, 0), 0) 0 = 0 := by
    have hz : ψ (0, 0, (0, 0), 0) = 0 := hψ0
    simp [polynomialGapLift, polynomialGapSlice, hz]
  have hL := ((origin_lift_smooth hψ).contDiffAt (hW.mem_nhds h0W)).differentiableAt (by simp)
  have hDF : fderiv ℝ (originValue ψ) 0 = 0 := by
    change fderiv ℝ ((fun u : PeriodicC2_STR02969 => polynomialRangeDeficit (0, 0) DGPS.Circle.AngularNormalization.a0 u) ∘
      polynomialGapLift ψ ((0, 0), 0)) 0 = 0
    rw [fderiv_comp 0 (origin_outer_smooth.differentiable (by simp) _) hL, hL0,
      polynomialRangeDeficit_fderiv_zero]
    exact ContinuousLinearMap.zero_comp _
  have hD2 : fderiv ℝ (fderiv ℝ (originValue ψ)) 0 = 0 := by
    change fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ =>
      polynomialRangeDeficit (0, 0) DGPS.Circle.AngularNormalization.a0
        (x.1 • cosC2_STR02915 + x.2 • sinC2_STR02915 +
          (ψ (x.1, x.2, (0, 0), 0) : PeriodicC2_STR02969)))) 0 = 0
    exact polynomialReducedDeficit_amplitude_hessian_origin_zero hU h0U hψ hψ0 hamp
  refine ⟨?_, hDF, hD2, fun x => ?_⟩
  · change polynomialRangeDeficit (0, 0) DGPS.Circle.AngularNormalization.a0 (polynomialGapLift ψ ((0, 0), 0) 0) = 0
    rw [hL0, polynomialRangeDeficit_zero]
  · let line := fun t : ℝ => t • x
    have hline : ContDiffAt ℝ 3 line 0 := by dsimp only [line]; fun_prop
    have hFc : ContDiffAt ℝ 3 (originValue ψ) 0 :=
      ((origin_smooth hψ).contDiffAt (hW.mem_nhds h0W)).of_le (by simp)
    have hline0 : line 0 = 0 := by simp only [line, zero_smul]
    have hFc' : ContDiffAt ℝ 3 (originValue ψ) (line 0) := by rw [hline0]; exact hFc
    have hd := iteratedDeriv_vcomp_three hFc' hline
    have hline1 : deriv line 0 = x := by
      simpa only [line, one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const x).deriv
    simp only [hline0, hline1, iteratedFDeriv_two_apply, hD2, hDF,
      ContinuousLinearMap.zero_apply, zero_smul, smul_zero, zero_add, add_zero] at hd
    have hj := polynomial_reduced_deficit_joint_third_zero hU h0U hN h0N hψ hψ0 hψN hgraph
      x.1 x.2 0
    have he : (originValue ψ ∘ line) = (fun t : ℝ => polynomialReducedDeficit ψ
        (t * x.1, t * x.2, (t * 0, 0), 0)) := by
      funext t
      simp only [originValue, Function.comp_def, line, polynomialReducedDeficit,
        polynomialGapLift, polynomialGapSlice, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, mul_zero, zero_add, add_zero, mul_one]
    rw [← he] at hj
    exact hd.symm.trans hj

/-- Only the norm estimate for the stock Taylor integral: no Taylor formula,
jet hypothesis or remainder construction is introduced by this helper. -/
private theorem norm_stock_integral {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] (n k : ℕ)
    (T : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × ℝ) V)
    (x : ℝ × ℝ) (C : ℝ)
    (hT : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖T t‖ ≤ C) :
    ‖∫ t in (0 : ℝ)..1, (1 - t) ^ k • T t (fun _ => x)‖ ≤ C * ‖x‖ ^ n := by
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖(1 - t) ^ k • T t (fun _ => x)‖ ≤ C * ‖x‖ ^ n := by
    intro t ht
    have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa only [Set.uIoc_of_le zero_le_one] using ht
    have hwt : |1 - t| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr ht'.2)]
      linarith only [ht'.1]
    have hw : ‖(1 - t) ^ k‖ ≤ 1 := by
      simpa only [Real.norm_eq_abs, abs_pow, one_pow] using
        pow_le_pow_left₀ (abs_nonneg (1 - t)) hwt k
    have hM : ‖T t (fun _ => x)‖ ≤ C * ‖x‖ ^ n := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le
          (hT t ⟨ht'.1.le, ht'.2⟩) (fun _ => le_rfl : ∀ _ : Fin n, ‖x‖ ≤ ‖x‖)
    calc
      ‖(1 - t) ^ k • T t (fun _ => x)‖ = ‖(1 - t) ^ k‖ * ‖T t (fun _ => x)‖ := norm_smul _ _
      _ ≤ 1 * ‖T t (fun _ => x)‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg _)
      _ = ‖T t (fun _ => x)‖ := one_mul _
      _ ≤ _ := hM
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa only [sub_zero, abs_one, mul_one] using hi

/-- The two STOCK Banach Taylor formulas have compatible leading fourth
coefficients. Their remainders, separately estimated in value and derivative,
give an actual radial-versus-value error; no value error is differentiated. -/
private theorem origin_euler_value_error {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ (0 : PolynomialRangeParameters) = 0)
    (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hamp : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ x : ℝ × ℝ, ‖x‖ < δ →
      |polynomialReducedDeficitRadial ψ ((0, 0), 0) x - 4 * originValue ψ x| ≤ K * ‖x‖ ^ 5 := by
  let f := originValue ψ
  let W := polynomialGapSlice ((0, 0), 0) ⁻¹' U
  have hW : IsOpen W := hU.preimage (by unfold polynomialGapSlice; fun_prop)
  have h0W : (0 : ℝ × ℝ) ∈ W := h0U
  have hF : ContDiffOn ℝ ∞ f W := origin_smooth hψ
  have hFc : ContDiffAt ℝ ∞ f 0 := hF.contDiffAt (hW.mem_nhds h0W)
  let C := ‖iteratedFDeriv ℝ 5 f 0‖ + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hc : ContinuousAt (fun z => ‖iteratedFDeriv ℝ 5 f z‖) 0 :=
    ((hFc.iteratedFDeriv_right (i := 5) (m := 0) (by simp)).continuousAt).norm
  have he : ∀ᶠ z in 𝓝 (0 : ℝ × ℝ), z ∈ W ∧ ‖iteratedFDeriv ℝ 5 f z‖ < C := by
    apply Filter.Eventually.and (hW.mem_nhds h0W)
    exact hc.tendsto.eventually (gt_mem_nhds (by dsimp only [C]; linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 he
  obtain ⟨hf0, hdf0, hd20, hd30⟩ := origin_lower_jets hU h0U hN h0N hψ hψ0 hψN hgraph hamp
  change f 0 = 0 at hf0
  change fderiv ℝ f 0 = 0 at hdf0
  change fderiv ℝ (fderiv ℝ f) 0 = 0 at hd20
  change ∀ x : ℝ × ℝ, iteratedFDeriv ℝ 3 f 0 (fun _ => x) = 0 at hd30
  refine ⟨δ, 5 * C, hδ, mul_pos (by norm_num) hC, fun x hx => ?_⟩
  have hseg (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      t • x ∈ W ∧ ‖iteratedFDeriv ℝ 5 f (t • x)‖ ≤ C := by
    have hnorm : ‖t • x‖ ≤ ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (norm_nonneg x)
    have hb := hball (show t • x ∈ Metric.ball 0 δ by
      simpa only [Metric.mem_ball, dist_zero_right] using hnorm.trans_lt hx)
    exact ⟨hb.1, hb.2.le⟩
  have hFs (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ContDiffAt ℝ (4 + 1) f (0 + t • x) := by
    simpa only [zero_add] using (hF.contDiffAt (hW.mem_nhds (hseg t ht).1)).of_le (by simp)
  have hGs (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ContDiffAt ℝ (3 + 1) (fderiv ℝ f) (0 + t • x) := by
    convert ((hF.fderiv_of_isOpen hW (m := 4) (by simp)).contDiffAt (hW.mem_nhds (hseg t ht).1)) using 1 <;> norm_num
  let PF : ℝ := ∑ k ∈ Finset.range 5,
    ((Nat.factorial k : ℕ) : ℝ)⁻¹ • iteratedFDeriv ℝ k f 0 (fun _ => x)
  let PG : (ℝ × ℝ) →L[ℝ] ℝ := ∑ k ∈ Finset.range 4,
    ((Nat.factorial k : ℕ) : ℝ)⁻¹ • iteratedFDeriv ℝ k (fderiv ℝ f) 0 (fun _ => x)
  have hTF := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := 0) (y := x) (n := 4) hFs
  have hTG := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := fderiv ℝ f) (x := 0) (y := x) (n := 3) hGs
  simp only [zero_add] at hTF hTG
  have hRF := norm_stock_integral 5 4 (fun t => iteratedFDeriv ℝ 5 f (t • x)) x C
    (fun t ht => (hseg t ht).2)
  have hRG := norm_stock_integral 4 3
    (fun t => iteratedFDeriv ℝ 4 (fderiv ℝ f) (t • x)) x C (fun t ht => by
      rw [norm_iteratedFDeriv_fderiv]
      exact (hseg t ht).2)
  have hFrem : ‖f x - PF‖ ≤ C * ‖x‖ ^ 5 := by
    rw [hTF, add_sub_cancel_left, norm_smul]
    have hfac : ‖(((Nat.factorial 4 : ℕ) : ℝ)⁻¹)‖ ≤ 1 := by norm_num
    exact (mul_le_mul_of_nonneg_right hfac (norm_nonneg _)).trans
      (by simpa only [one_mul] using hRF)
  have hGrem : ‖fderiv ℝ f x - PG‖ ≤ C * ‖x‖ ^ 4 := by
    rw [hTG, add_sub_cancel_left, norm_smul]
    have hfac : ‖(((Nat.factorial 3 : ℕ) : ℝ)⁻¹)‖ ≤ 1 := by norm_num
    exact (mul_le_mul_of_nonneg_right hfac (norm_nonneg _)).trans
      (by simpa only [one_mul] using hRG)
  have h2diag : iteratedFDeriv ℝ 2 f 0 (fun _ => x) = 0 := by
    rw [iteratedFDeriv_two_apply, hd20] <;> rfl
  have hg1 : iteratedFDeriv ℝ 1 (fderiv ℝ f) 0 (fun _ => x) = 0 := by
    rw [iteratedFDeriv_one_apply, hd20] <;> rfl
  have hg2 : (iteratedFDeriv ℝ 2 (fderiv ℝ f) 0 (fun _ => x)) x = 0 := by
    have hh := iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (f := f) (x := 0)
      (fun _ : Fin 3 => x)
    change iteratedFDeriv ℝ 3 f 0 (fun _ => x) =
      (iteratedFDeriv ℝ 2 (fderiv ℝ f) 0 (fun _ => x)) x at hh
    rw [hd30 x] at hh
    exact hh.symm
  have hg3 : (iteratedFDeriv ℝ 3 (fderiv ℝ f) 0 (fun _ => x)) x =
      iteratedFDeriv ℝ 4 f 0 (fun _ => x) := by
    exact (iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (f := f) (x := 0)
      (fun _ : Fin 4 => x)).symm
  have hpoly : PG x = 4 * PF := by
    dsimp only [PG, PF]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.zero_apply, iteratedFDeriv_zero_apply,
      iteratedFDeriv_one_apply, hf0, hdf0, hd20, h2diag, hd30 x, hg1, hg2, hg3,
      zero_smul, smul_eq_mul, zero_add, add_zero, mul_zero, zero_mul]
    norm_num
    <;> ring
  have hpair : |fderiv ℝ f x x - PG x| ≤ C * ‖x‖ ^ 5 := by
    have ht := (fderiv ℝ f x - PG).le_opNorm x
    have hs := mul_le_mul_of_nonneg_right hGrem (norm_nonneg x)
    calc
      |fderiv ℝ f x x - PG x| = ‖(fderiv ℝ f x - PG) x‖ := by
        rw [ContinuousLinearMap.sub_apply, Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ f x - PG‖ * ‖x‖ := ht
      _ ≤ (C * ‖x‖ ^ 4) * ‖x‖ := hs
      _ = C * ‖x‖ ^ 5 := by ring
  have hFabs : |f x - PF| ≤ C * ‖x‖ ^ 5 := by
    simpa only [Real.norm_eq_abs] using hFrem
  have hE : polynomialReducedDeficitRadial ψ ((0, 0), 0) x = fderiv ℝ f x x := by
    simp only [polynomialReducedDeficitRadial, add_zero, mul_one]
    rfl
  rw [hE]
  change |fderiv ℝ f x x - 4 * f x| ≤ (5 * C) * ‖x‖ ^ 5
  calc
    _ = |(fderiv ℝ f x x - PG x) - 4 * (f x - PF)| := by rw [hpoly]; congr 1 <;> ring
    _ ≤ |fderiv ℝ f x x - PG x| + |4 * (f x - PF)| := abs_sub _ _
    _ = |fderiv ℝ f x x - PG x| + 4 * |f x - PF| := by rw [abs_mul]; norm_num
    _ ≤ C * ‖x‖ ^ 5 + 4 * (C * ‖x‖ ^ 5) :=
      add_le_add hpair (mul_le_mul_of_nonneg_left hFabs (by norm_num))
    _ = _ := by ring

/-- The actual pure-origin radial quartic lower bound, on the SAME supplied
Common graph. All inputs are factual graph outputs. The value lower bound,
zero jets and derivative remainder are proved from the actual model internally. -/
theorem polynomial_origin_same_graph_radial_quartic_lower
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hamp : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ × ℝ, ‖x‖ < δ →
      DGPS.Circle.AngularNormalization.a0 / 768 * (x.1 ^ 2 + x.2 ^ 2) ^ 2 ≤
        polynomialReducedDeficitRadial ψ ((0, 0), 0) x := by
  have hψ0 : ψ (0 : PolynomialRangeParameters) = 0 := hzero 0 0 0 h0U
  obtain ⟨δE, K, hδE, hK, hError⟩ := origin_euler_value_error hU h0U hN h0N hψ hψ0 hψN hgraph hamp
  obtain ⟨δV, hδV, hValue⟩ := polynomial_origin_same_graph_value_quartic_lower hU h0U hψ hzero hamp
  let c := DGPS.Circle.AngularNormalization.a0 / 768
  have hc : 0 < c := div_pos a0_pos (by norm_num)
  let δ := min δE (min δV (c / (K + 1)))
  have hδ : 0 < δ := lt_min hδE (lt_min hδV (div_pos hc (by positivity)))
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have hxE : ‖x‖ < δE := hx.trans_le (min_le_left _ _)
  have hxV : ‖x‖ < δV := hx.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hxK : ‖x‖ < c / (K + 1) := hx.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hKx : K * ‖x‖ ≤ c := by
    have ht := (lt_div_iff₀ (by positivity : 0 < K + 1)).mp hxK
    nlinarith only [ht, norm_nonneg x]
  have hn2 : ‖x‖ ^ 2 ≤ x.1 ^ 2 + x.2 ^ 2 := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases h12 : |x.1| ≤ |x.2|
    · rw [max_eq_right h12, sq_abs]
      linarith only [sq_nonneg x.1]
    · rw [max_eq_left (le_of_not_ge h12), sq_abs]
      linarith only [sq_nonneg x.2]
  have hn4 : ‖x‖ ^ 4 ≤ (x.1 ^ 2 + x.2 ^ 2) ^ 2 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg ‖x‖) hn2 2
  have hRem : K * ‖x‖ ^ 5 ≤ c * (x.1 ^ 2 + x.2 ^ 2) ^ 2 := by
    calc
      _ = (K * ‖x‖) * ‖x‖ ^ 4 := by ring
      _ ≤ c * ‖x‖ ^ 4 := mul_le_mul_of_nonneg_right hKx (pow_nonneg (norm_nonneg x) 4)
      _ ≤ _ := mul_le_mul_of_nonneg_left hn4 hc.le
  have hv := hValue x hxV
  change c * (x.1 ^ 2 + x.2 ^ 2) ^ 2 ≤ originValue ψ x at hv
  have he := (abs_le.mp (hError x hxE)).1
  have hnonneg : 0 ≤ c * (x.1 ^ 2 + x.2 ^ 2) ^ 2 := mul_nonneg hc.le (sq_nonneg _)
  change c * (x.1 ^ 2 + x.2 ^ 2) ^ 2 ≤ _
  nlinarith only [he, hv, hRem, hnonneg]

end DGPS.Examples.PolynomialSpecies
