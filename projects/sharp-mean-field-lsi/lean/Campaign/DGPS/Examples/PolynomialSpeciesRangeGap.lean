import DGPS.Examples.PolynomialSpeciesRangeEnvelope

/-! The actual gap in the independent-(h,s) chart. Joint smoothness is proved before
restriction to the selected root; that root is never differentiated. -/

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

/-- The normalized relative-entropy gap of the same centered independent reference. -/
def polynomialRangeGap (p : ℝ × ℝ) (u : PeriodicC2_STR02969) : ℝ :=
  let L := e0_STR02955 (polynomialRangeLogWeight p)
  let m := eulerMean L u (e0_STR02955 (polynomialRangeFeature p))
  eulerEntropy L u + eta * m ^ 2 / 2

private abbrev GapInput := (ℝ × ℝ) × PeriodicC2_STR02969

private theorem mean_smooth : ContDiff ℝ ∞ (fun x : GapInput =>
    eulerMean (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2
      (e0_STR02955 (polynomialRangeFeature x.1))) := by
  have hL : ContDiff ℝ ∞ (fun x : GapInput =>
      e0_STR02955 (polynomialRangeLogWeight x.1)) :=
    e0_STR02955.contDiff.comp (polynomialRange_data_smooth.1.comp
      (contDiff_fst : ContDiff ℝ ∞ (fun x : GapInput => x.1)))
  have hφ : ContDiff ℝ ∞ (fun x : GapInput =>
      e0_STR02955 (polynomialRangeFeature x.1)) :=
    e0_STR02955.contDiff.comp (polynomialRange_data_smooth.2.2.2.1.comp
      (contDiff_fst : ContDiff ℝ ∞ (fun x : GapInput => x.1)))
  have hρ : ContDiff ℝ ∞ (fun x : GapInput =>
      eulerDensity (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2) :=
    rho_smooth_STR02954.comp (contDiff_const.prodMk
      (hL.add (e0_STR02955.contDiff.comp contDiff_snd)))
  exact meanCLM_STR02954.contDiff.comp (hφ.mul hρ)

private theorem entropy_smooth : ContDiff ℝ ∞ (fun x : GapInput =>
    eulerEntropy (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2) := by
  have hL : ContDiff ℝ ∞ (fun x : GapInput =>
      e0_STR02955 (polynomialRangeLogWeight x.1)) :=
    e0_STR02955.contDiff.comp (polynomialRange_data_smooth.1.comp
      (contDiff_fst : ContDiff ℝ ∞ (fun x : GapInput => x.1)))
  have hu := e0_STR02955.contDiff.comp (contDiff_snd : ContDiff ℝ ∞ (fun x : GapInput => x.2))
  have hρ : ContDiff ℝ ∞ (fun x : GapInput =>
      eulerDensity (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2) :=
    rho_smooth_STR02954.comp (contDiff_const.prodMk (hL.add hu))
  exact ((meanCLM_STR02954.contDiff.comp (hu.mul hρ)).sub
    (logZ_smooth_STR02954.comp (contDiff_const.prodMk (hL.add hu)))).add
    (logZ_smooth_STR02954.comp (contDiff_const.prodMk hL))

/-- Genuine joint smoothness of the actual independent-parameter gap. -/
theorem polynomialRangeGap_smooth : ContDiff ℝ ∞ (fun x : (ℝ × ℝ) × PeriodicC2_STR02969 => polynomialRangeGap x.1 x.2) :=
  entropy_smooth.add ((contDiff_const.mul (mean_smooth.pow 2)).div_const 2)

private theorem mean_zero (p : ℝ × ℝ) :
    eulerMean (e0_STR02955 (polynomialRangeLogWeight p)) 0
      (e0_STR02955 (polynomialRangeFeature p)) = 0 := by
  have hρ : eulerDensity (e0_STR02955 (polynomialRangeLogWeight p)) 0 = polynomialRangeReference p := by
    simp only [eulerDensity, map_zero, add_zero, polynomialRangeReference]
  rw [eulerMean, hρ]
  exact polynomialRangeFeature_centered p

/-- The true centered equilibrium has zero gap for every independent parameter. -/
theorem polynomialRangeGap_zero (p : ℝ × ℝ) : polynomialRangeGap p 0 = 0 := by
  simp only [polynomialRangeGap, mean_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_div, add_zero]
  simp [eulerEntropy, eulerMean]

private theorem centered_gap_critical (L φ : PeriodicHolder_STR02968) (c : ℝ)
    (hc : eulerMean L 0 φ = 0) :
    fderiv ℝ (fun u : PeriodicC2_STR02969 =>
      eulerEntropy L u + (c / 2) * (eulerMean L u φ) ^ 2) 0 = 0 := by
  have hρ : ContDiff ℝ ∞ (eulerDensity L) :=
    rho_smooth_STR02954.comp (contDiff_const.prodMk (contDiff_const.add e0_STR02955.contDiff))
  have hm : ContDiff ℝ ∞ (fun u : PeriodicC2_STR02969 => eulerMean L u φ) :=
    meanCLM_STR02954.contDiff.comp (contDiff_const.mul hρ)
  have hH : ContDiff ℝ ∞ (eulerEntropy L) :=
    ((meanCLM_STR02954.contDiff.comp (e0_STR02955.contDiff.mul hρ)).sub
      (logZ_smooth_STR02954.comp (contDiff_const.prodMk
        (contDiff_const.add e0_STR02955.contDiff)))).add contDiff_const
  have hd := ((hH.differentiable (by simp) 0).hasFDerivAt).add
    ((((hm.differentiable (by simp) 0).hasFDerivAt.pow 2).const_mul (c / 2)))
  change HasFDerivAt (fun u : PeriodicC2_STR02969 =>
    eulerEntropy L u + (c / 2) * (eulerMean L u φ) ^ 2) _ 0 at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    hc, show (2 : ℕ) - 1 = 1 from rfl, pow_one, mul_zero, zero_mul, zero_smul, zero_add, add_zero]
  rw [eulerEntropy_fderiv]
  simp [eulerCov, eulerMean]

/-- Its full chart derivative vanishes for every independent parameter, by centering. -/
theorem polynomialRangeGap_fderiv_zero (p : ℝ × ℝ) : fderiv ℝ (polynomialRangeGap p) 0 = 0 := by
  let L := e0_STR02955 (polynomialRangeLogWeight p)
  let φ := e0_STR02955 (polynomialRangeFeature p)
  have he : polynomialRangeGap p = fun u : PeriodicC2_STR02969 =>
      eulerEntropy L u + (eta / 2) * (eulerMean L u φ) ^ 2 := by
    funext u
    change eulerEntropy L u + eta * (eulerMean L u φ) ^ 2 / 2 = _
    ring
  rw [he]
  exact centered_gap_critical L φ eta (mean_zero p)

private theorem density_log (L : PeriodicHolder_STR02968) (u : PeriodicC2_STR02969) (t : ℝ) :
    Real.log ((eulerDensity L u).val t) = L.val t + u.val t - Real.log (Z_STR02954 (0, L + e0_STR02955 u)) := by
  have he : (eulerDensity L u).val t = Real.exp (L.val t + u.val t) / Z_STR02954 (0, L + e0_STR02955 u) := by
    rw [eulerDensity, rho_val_STR02954]
    simp only [rhoT_STR02901, zero_mul, zero_add, PeriodicHolder_STR02968.val_add,
      Pi.add_apply, e0_val_STR02955, Z_eq_meanT_STR02954]
  rw [he, Real.log_div (Real.exp_pos _).ne' (Z_pos_STR02954 _).ne', Real.log_exp]

private theorem entropy_eq_of_density_eq (L₁ L₂ : PeriodicHolder_STR02968) (u : PeriodicC2_STR02969)
    (h0 : eulerDensity L₁ 0 = eulerDensity L₂ 0) (hu : eulerDensity L₁ u = eulerDensity L₂ u) :
    eulerEntropy L₁ u = eulerEntropy L₂ u := by
  have hz := congrArg (fun R : PeriodicHolder_STR02968 => Real.log (R.val 0)) h0
  have ht := congrArg (fun R : PeriodicHolder_STR02968 => Real.log (R.val 0)) hu
  rw [density_log, density_log] at hz ht
  simp only [show (0 : PeriodicC2_STR02969).val 0 = 0 from rfl, add_zero, map_zero, add_zero] at hz
  unfold eulerEntropy eulerMean
  rw [hu]
  linarith

/-- The independent gap restricts to the exact actual canonical chart gap. -/
theorem polynomialRangeGap_actual (h : ℝ) (u : PeriodicC2_STR02969) :
    polynomialRangeGap (h, root_EX054 h) u = polynomialChartGap h u := by
  have hH := entropy_eq_of_density_eq
    (e0_STR02955 (polynomialRangeLogWeight (h, root_EX054 h))) (polynomialLogReference h) u
    (polynomialRangeDensity_actual h 0) (polynomialRangeDensity_actual h u)
  change eulerEntropy (e0_STR02955 (polynomialRangeLogWeight (h, root_EX054 h))) u +
      eta * (eulerMean (e0_STR02955 (polynomialRangeLogWeight (h, root_EX054 h))) u
        (e0_STR02955 (polynomialRangeFeature (h, root_EX054 h)))) ^ 2 / 2 =
    eulerEntropy (polynomialLogReference h) u +
      eta * (eulerMean (polynomialLogReference h) u (polynomialEulerFeature h)) ^ 2 / 2
  rw [hH]
  unfold eulerMean
  rw [polynomialRangeFeature_actual, polynomialRangeDensity_actual]

/-- The chart competitor belongs to the original absolute domain and has this actual gap. -/
theorem polynomialChartAbsolute_gap_eq_rangeGap (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (u : PeriodicC2_STR02969) :
    (scalarGap (canonical_elementary_polynomial_model h) (polynomialChartAbsolute h u) : ℝ) =
      polynomialRangeGap (h, root_EX054 h) u := by
  rw [polynomialRangeGap_actual]
  exact (polynomialChartAbsolute_gap_and_dissipation h b u).1

end DGPS.Examples.PolynomialSpecies
