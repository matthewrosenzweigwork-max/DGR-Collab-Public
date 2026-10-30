import DGPS.Examples.PolynomialSpeciesGapHessianControl
import DGPS.Examples.PolynomialSpeciesReducedHessian
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The actual same-graph gap is uniformly comparable to squared amplitude.
Constants precede all small independent reference and rate parameters. The proof
derives its Hessian bound and uses the existing exact segment Taylor formula. -/

noncomputable section
open Filter Topology NormedSpace MeasureTheory
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem segment_norm (θ : (ℝ × ℝ) × ℝ) (x : ℝ × ℝ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖(θ, t • x)‖ ≤ ‖(θ, x)‖ := by
  change max ‖θ‖ ‖t • x‖ ≤ max ‖θ‖ ‖x‖
  apply max_le_max le_rfl
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg x) ht.2

private theorem amp_norm_sq (x : ℝ × ℝ) : ‖x‖ ^ 2 ≤ x.1 ^ 2 + x.2 ^ 2 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  rcases le_total |x.1| |x.2| with h | h
  · rw [max_eq_right h, sq_abs]
    nlinarith [sq_nonneg x.1]
  · rw [max_eq_left h, sq_abs]
    nlinarith [sq_nonneg x.2]

private theorem integral_model (r : ℝ) :
    (∫ t in (0 : ℝ)..1, (1 - t) * (r / 2)) = r / 4 := by
  have he : (∫ t in (0 : ℝ)..1, (1 - t)) =
      (∫ t in (0 : ℝ)..1, (1 : ℝ)) - (∫ t in (0 : ℝ)..1, t) :=
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable 0 1)
      (continuous_id.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_mul_const, he, intervalIntegral.integral_const,
    integral_id]
  norm_num <;> ring

/-- A genuine uniform quantitative remainder for the ACTUAL reduced gap.
The norm includes amplitude, both reference parameters and the rate parameter.
All graph hypotheses are conclusions of the actual common graph producer. -/
theorem polynomialReducedGap_uniform_quadratic_error {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hamp : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 ≤ K ∧
      (∀ (θ : (ℝ × ℝ) × ℝ) (x : ℝ × ℝ), ‖(θ, x)‖ < δ → polynomialGapSlice θ x ∈ U) ∧
      ∀ (θ : (ℝ × ℝ) × ℝ) (x : ℝ × ℝ), ‖(θ, x)‖ < δ →
        |polynomialReducedGap ψ θ x - (x.1 ^ 2 + x.2 ^ 2) / 4| ≤
          K * ‖(θ, x)‖ * (x.1 ^ 2 + x.2 ^ 2) := by
  obtain ⟨δ, K, hδ, hK, hball, hLip⟩ := polynomialReducedGapHessian_lipschitz hU h0U hψ
  refine ⟨δ, K, hδ, hK, (fun θ x hx => hball (θ, x) hx), ?_⟩
  intro θ x hx
  let r := x.1 ^ 2 + x.2 ^ 2
  have hr : 0 ≤ r := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, polynomialGapSlice θ (t • x) ∈ U := by
    intro t ht
    exact hball _ ((segment_norm θ x t ht).trans_lt hx)
  have hψ0 : ψ (0 : PolynomialRangeParameters) = 0 := by
    have hp : ((0, 0, (0, 0), 0) : PolynomialRangeParameters) = 0 := by ext <;> rfl
    rw [← hp]
    exact hzero 0 0 0 (by rw [hp]; exact h0U)
  have hH0 : polynomialReducedGapHessian ψ 0 x x = r / 2 :=
    polynomialReducedGap_hessian_origin hU h0U hψ hψ0 hamp x.1 x.2
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |polynomialReducedGapHessian ψ (θ, t • x) x x - r / 2| ≤ K * ‖(θ, x)‖ * r := by
    intro t ht
    let A := polynomialReducedGapHessian ψ (θ, t • x) - polynomialReducedGapHessian ψ 0
    have hA : ‖A‖ ≤ K * ‖(θ, x)‖ :=
      (hLip _ ((segment_norm θ x t ht).trans_lt hx)).trans
        (mul_le_mul_of_nonneg_left (segment_norm θ x t ht) hK)
    calc
      |polynomialReducedGapHessian ψ (θ, t • x) x x - r / 2| = ‖A x x‖ := by
        rw [← hH0]
        rfl
      _ ≤ ‖A x‖ * ‖x‖ := (A x).le_opNorm x
      _ ≤ (‖A‖ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right (A.le_opNorm x) (norm_nonneg _)
      _ ≤ (K * ‖(θ, x)‖ * ‖x‖) * ‖x‖ := by gcongr
      _ = K * ‖(θ, x)‖ * ‖x‖ ^ 2 := by ring
      _ ≤ K * ‖(θ, x)‖ * r := mul_le_mul_of_nonneg_left (amp_norm_sq x)
        (mul_nonneg hK (norm_nonneg _))
  let W := polynomialGapSlice θ ⁻¹' U
  have hW : IsOpen W := hU.preimage (by
    have hs : ContDiff ℝ ∞ (polynomialGapSlice θ) :=
      contDiff_fst.prodMk (contDiff_snd.prodMk (contDiff_const.prodMk contDiff_const))
    exact hs.continuous)
  have hF := polynomialReducedGap_smooth hψ θ
  have hD : ContDiffOn ℝ 1 (fderiv ℝ (polynomialReducedGap ψ θ)) W :=
    hF.fderiv_of_isOpen hW (by simp)
  have hDD : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ (polynomialReducedGap ψ θ))) W :=
    hD.fderiv_of_isOpen hW (by simp)
  have hcont : ContinuousOn (fun t : ℝ => polynomialReducedGapHessian ψ (θ, t • x) x x)
      (Set.Icc (0 : ℝ) 1) := by
    have hc : ContinuousOn (fun t : ℝ => fderiv ℝ (fderiv ℝ (polynomialReducedGap ψ θ)) (t • x))
        (Set.Icc (0 : ℝ) 1) :=
      hDD.continuousOn.comp (continuous_id.smul continuous_const).continuousOn hseg
    exact (hc.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hi : IntervalIntegrable (fun t : ℝ =>
      (1 - t) * polynomialReducedGapHessian ψ (θ, t • x) x x) volume 0 1 :=
    ((continuous_const.sub continuous_id).continuousOn.mul hcont).intervalIntegrable_of_Icc zero_le_one
  have hi0 : IntervalIntegrable (fun t : ℝ => (1 - t) * (r / 2)) volume 0 1 :=
    ((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable 0 1
  have hTaylor := (polynomialReducedGap_quadratic_factor hU hψ hzero θ x hseg).2.2
  have he : (∫ t in (0 : ℝ)..1,
      (1 - t) * (polynomialReducedGapHessian ψ (θ, t • x) x x - r / 2)) =
      polynomialReducedGap ψ θ x - r / 4 := by
    calc
      _ = ∫ t in (0 : ℝ)..1,
          ((1 - t) * polynomialReducedGapHessian ψ (θ, t • x) x x - (1 - t) * (r / 2)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      _ = (∫ t in (0 : ℝ)..1, (1 - t) * polynomialReducedGapHessian ψ (θ, t • x) x x) -
          (∫ t in (0 : ℝ)..1, (1 - t) * (r / 2)) := intervalIntegral.integral_sub hi hi0
      _ = polynomialReducedGap ψ θ x - r / 4 := by
        change (∫ t in (0 : ℝ)..1, (1 - t) * (fderiv ℝ (fderiv ℝ (polynomialReducedGap ψ θ)) (t • x)) x x) - _ = _
        rw [← hTaylor, integral_model]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := K * ‖(θ, x)‖ * r)
    (f := fun t : ℝ => (1 - t) * (polynomialReducedGapHessian ψ (θ, t • x) x x - r / 2)) (by
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        have h : t ∈ Set.Ioc (0 : ℝ) 1 := by simpa only [Set.uIoc_of_le zero_le_one] using ht
        exact ⟨h.1.le, h.2⟩
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht'.2)]
      calc
        (1 - t) * |polynomialReducedGapHessian ψ (θ, t • x) x x - r / 2| ≤
            1 * |polynomialReducedGapHessian ψ (θ, t • x) x x - r / 2| := by
          gcongr
          linarith [ht'.1]
        _ ≤ K * ‖(θ, x)‖ * r := by simpa only [one_mul] using hbound t ht')
  rw [he] at hb
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hb

/-- A fixed neighborhood gives genuine positive quadratic comparability. No
positive gap or minimizer assumption is used, and all constants precede parameters. -/
theorem polynomialReducedGap_uniform_comparison {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hamp : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (θ : (ℝ × ℝ) × ℝ) (x : ℝ × ℝ), ‖(θ, x)‖ < δ →
      polynomialGapSlice θ x ∈ U ∧
      (x.1 ^ 2 + x.2 ^ 2) / 8 ≤ polynomialReducedGap ψ θ x ∧
      polynomialReducedGap ψ θ x ≤ 3 * (x.1 ^ 2 + x.2 ^ 2) / 8 := by
  obtain ⟨δ, K, hδ, hK, hball, hError⟩ := polynomialReducedGap_uniform_quadratic_error hU h0U hψ hzero hamp
  have hK1 : 0 < K + 1 := by linarith
  let ε := min δ (1 / (8 * (K + 1)))
  have hε : 0 < ε := lt_min hδ (div_pos zero_lt_one (mul_pos (by norm_num) hK1))
  refine ⟨ε, hε, ?_⟩
  intro θ x hx
  have hxδ : ‖(θ, x)‖ < δ := hx.trans_le (min_le_left _ _)
  have hxK : ‖(θ, x)‖ < 1 / (8 * (K + 1)) := hx.trans_le (min_le_right _ _)
  have hsmall := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8) hK1)).mp hxK
  have hk : K * ‖(θ, x)‖ ≤ 1 / 8 := by nlinarith [norm_nonneg (θ, x)]
  have hr : 0 ≤ x.1 ^ 2 + x.2 ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have he := (hError θ x hxδ).trans (mul_le_mul_of_nonneg_right hk hr)
  obtain ⟨hl, hu⟩ := abs_le.mp he
  refine ⟨hball θ x hxδ, ?_, ?_⟩ <;> linarith

end DGPS.Examples.PolynomialSpecies
