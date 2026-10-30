import DGPS.Examples.PolynomialSpeciesRangeRestriction
import DGPS.Examples.PolynomialSpeciesRangeOrigin

/-! Uniform original-space data for the actual moving polynomial reference near
zero field. Joint smoothness belongs to the existing independent-parameter chart;
the selected root enters it by its genuine sixth-order bound. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Frontier.STR029 DGPS.PositiveRankOne
open DGPS.Circle.AngularNormalization DGPS.Circle.FirstClusterPerturbation DGPS.Circle.StationaryFlux
open DGPS.Examples.PolynomialEquilibrium DGPS.Examples.PolynomialExactGap

namespace DGPS.Examples.PolynomialSpecies

private theorem holder_bound (F : PeriodicHolder_STR02968) (t : ℝ) : |F.val t| ≤ ‖F‖ := by
  have hb := F.isPerHolder.abs_le_supNorm t
  rw [PeriodicHolder_STR02968.norm_def]
  linarith [holderSemi_nonneg_STR02968 (1 / 2) F.val]

private theorem selected_root_tendsto : Tendsto root_EX054 (𝓝 (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, δ, _, hδ, hb⟩ := abs_root_le_sixth_EX054
  have hs : ∀ᶠ h : ℝ in 𝓝 0, |h| < δ := by
    have ht : Tendsto (fun h : ℝ => |h|) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using continuous_abs.tendsto (0 : ℝ)
    exact ht.eventually (gt_mem_nhds hδ)
  have ht : Tendsto (fun h : ℝ => C * h ^ 6) (𝓝 0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0)).pow 6).const_mul C
  refine squeeze_zero_norm' ?_ ht
  filter_upwards [hs] with h hh
  rw [Real.norm_eq_abs]
  exact hb h hh.le

private def normalizedLog (p : ℝ × ℝ) : PeriodicHolder_STR02968 :=
  e0_STR02955 (polynomialRangeLogWeight p) -
    Real.log (Z_STR02954 (0, e0_STR02955 (polynomialRangeLogWeight p))) •
      (1 : PeriodicHolder_STR02968)

private theorem normalizedLog_actual (h : ℝ) :
    normalizedLog (h, root_EX054 h) = polynomialLogReference h := by
  apply ext_STR02954
  funext t
  have hq := congrFun (congrArg PeriodicHolder_STR02968.val
    (polynomialRangeReference_actual h)) t
  rw [polynomialEuler_density_zero] at hq
  change (polynomialRangeReference (h, root_EX054 h)).val t =
    (polynomialRankOne h).q (angEquiv.symm (t : AngCircle)) at hq
  change (normalizedLog (h, root_EX054 h)).val t =
    Real.log ((polynomialRankOne h).q (angEquiv.symm (t : AngCircle)))
  rw [← hq, polynomialRangeReference, rho_val_STR02954]
  simp only [normalizedLog, rhoT_STR02901, zero_mul, zero_add,
    PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_smul,
    val_one_STR02954, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e0_val_STR02955, mul_one]
  have hZ := Z_pos_STR02954 (0, e0_STR02955 (polynomialRangeLogWeight (h, root_EX054 h)))
  rw [Z_eq_meanT_STR02954] at hZ
  simp only [zero_mul, zero_add, e0_val_STR02955] at hZ
  rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp, Z_eq_meanT_STR02954]
  simp only [zero_mul, zero_add, e0_val_STR02955]

private theorem physical_first (f : Torus 1 → ℝ) (hf : IsSmoothPeriodic f) (t : ℝ) :
    coordPartial 0 f (angEquiv.symm (t : AngCircle)) =
      (2 * Real.pi) * deriv (fun s : ℝ => f (angEquiv.symm (s : AngCircle))) t := by
  let ψ : AngCircle → ℝ := f ∘ angEquiv.symm
  have hs : IsSmoothAngular ψ := by
    apply (isSmoothPeriodic_comp_iff ψ).1
    convert hf using 1
    ext x
    simp only [ψ, Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  have he : ψ ∘ angEquiv = f := by ext x; simp [ψ]
  have hh := physical_first_derivative_EX009 ψ hs (t / (2 * Real.pi))
  rw [he] at hh
  have hp : torusLift (fun _ : Fin 1 => t / (2 * Real.pi)) = angEquiv.symm (t : AngCircle) := by
    apply angEquiv.injective
    rw [MeasurableEquiv.apply_symm_apply, angEquiv_apply]
    change angRescale ((t / (2 * Real.pi) : ℝ) : UnitAddCircle) = (t : AngCircle)
    rw [angRescale_mk]
    congr 1
    field_simp [Real.pi_ne_zero]
  rw [hp] at hh
  have ht : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp [Real.pi_ne_zero]
  simpa only [ht, ψ, Function.comp_apply] using hh

private def featureData (h : ℝ) : PeriodicHolder_STR02968 :=
  e0_STR02955 (polynomialRangeFeature (h, root_EX054 h))
private def generatorData (h : ℝ) : PeriodicHolder_STR02968 :=
  polynomialRangeGenerator (h, root_EX054 h)
private def logData (h : ℝ) : PeriodicHolder_STR02968 := normalizedLog (h, root_EX054 h)
private def scoreData (h : ℝ) : PeriodicHolder_STR02968 :=
  (2 * Real.pi) • e1_STR02955 (polynomialRangeLogWeight (h, root_EX054 h))
private def gradientData (h : ℝ) : PeriodicHolder_STR02968 :=
  (2 * Real.pi) • e1_STR02955 (polynomialRangeFeature (h, root_EX054 h))

private theorem data_actual (h t : ℝ) :
    (featureData h).val t = (polynomialRankOne h).φ (angEquiv.symm (t : AngCircle)) ∧
    (generatorData h).val t = (polynomialRankOne h).Aq (angEquiv.symm (t : AngCircle)) ∧
    (logData h).val t = Real.log ((polynomialRankOne h).q (angEquiv.symm (t : AngCircle))) ∧
    (scoreData h).val t = (polynomialRankOne h).dlogq (angEquiv.symm (t : AngCircle)) ∧
    (gradientData h).val t = (polynomialRankOne h).dφ (angEquiv.symm (t : AngCircle)) := by
  have hφ (s : ℝ) : (polynomialRangeFeature (h, root_EX054 h)).val s =
      (polynomialRankOne h).φ (angEquiv.symm (s : AngCircle)) := by
    have hh := congrFun (congrArg PeriodicHolder_STR02968.val (polynomialRangeFeature_actual h)) s
    rw [e0_val_STR02955] at hh
    exact hh
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hφ t
  · have hh := congrFun (congrArg PeriodicHolder_STR02968.val (polynomialRangeGenerator_actual h)) t
    exact hh
  · rw [logData, normalizedLog_actual]
    rfl
  · rw [scoreData, polynomialRangeLogDerivative_actual]
    change (2 * Real.pi) * deriv (polynomialLogReference h).val t = _
    exact (physical_first _ (polynomialRankOne h).log_smooth t).symm
  · change (2 * Real.pi) * deriv (polynomialRangeFeature (h, root_EX054 h)).val t = _
    rw [show (polynomialRangeFeature (h, root_EX054 h)).val =
      (fun s : ℝ => (polynomialRankOne h).φ (angEquiv.symm (s : AngCircle))) from funext hφ]
    exact (physical_first _ (polynomialRankOne h).φ_smooth t).symm

private theorem data_tendsto :
    Tendsto featureData (𝓝 (0 : ℝ)) (𝓝 (featureData 0)) ∧
    Tendsto generatorData (𝓝 (0 : ℝ)) (𝓝 (generatorData 0)) ∧
    Tendsto logData (𝓝 (0 : ℝ)) (𝓝 (logData 0)) ∧
    Tendsto scoreData (𝓝 (0 : ℝ)) (𝓝 (scoreData 0)) ∧
    Tendsto gradientData (𝓝 (0 : ℝ)) (𝓝 (gradientData 0)) := by
  obtain ⟨hL, _, _, hφ, hA, _⟩ := polynomialRange_data_smooth
  have hp : Tendsto (fun h : ℝ => (h, root_EX054 h)) (𝓝 0) (𝓝 ((0, 0) : ℝ × ℝ)) :=
    tendsto_id.prodMk_nhds selected_root_tendsto
  have hp' : Tendsto (fun h : ℝ => (h, root_EX054 h)) (𝓝 0) (𝓝 (0, root_EX054 0)) := by
    simpa only [polynomial_root_origin] using hp
  have hn : Continuous normalizedLog := by
    have hz : Continuous (fun p : ℝ × ℝ => Z_STR02954 (0, e0_STR02955 (polynomialRangeLogWeight p))) :=
      Z_smooth_STR02954.continuous.comp (continuous_const.prodMk (e0_STR02955.continuous.comp hL.continuous))
    exact (e0_STR02955.continuous.comp hL.continuous).sub
      ((hz.log (fun p => (Z_pos_STR02954 _).ne')).smul continuous_const)
  refine ⟨?_, ?_, hn.continuousAt.tendsto.comp hp', ?_, ?_⟩
  · exact (e0_STR02955.continuous.comp hφ.continuous).continuousAt.tendsto.comp hp'
  · exact hA.continuous.continuousAt.tendsto.comp hp'
  · exact ((e1_STR02955.continuous.comp hL.continuous).const_smul (2 * Real.pi)).continuousAt.tendsto.comp hp'
  · exact ((e1_STR02955.continuous.comp hφ.continuous).const_smul (2 * Real.pi)).continuousAt.tendsto.comp hp'

/-- One genuine uniform error controls all five actual original-space data at
the moving reference as h tends to zero. The rate is derived from the actual
independent-parameter chart and sixth-order selected-root bound. -/
theorem polynomial_uniform_data_at_origin :
    ∃ ε : ℝ → ℝ, Tendsto ε (𝓝 0) (𝓝 0) ∧ ∀ h : ℝ, ∀ x : Torus 1,
      |(polynomialRankOne h).φ x - (polynomialRankOne 0).φ x| +
      |(polynomialRankOne h).Aq x - (polynomialRankOne 0).Aq x| +
      |Real.log ((polynomialRankOne h).q x)| + |(polynomialRankOne h).dlogq x| +
      |(polynomialRankOne h).dφ x - (polynomialRankOne 0).dφ x| ≤ ε h := by
  let ε := fun h : ℝ => ‖featureData h - featureData 0‖ + ‖generatorData h - generatorData 0‖ +
    ‖logData h - logData 0‖ + ‖scoreData h - scoreData 0‖ + ‖gradientData h - gradientData 0‖
  obtain ⟨hφ, hA, hL, hS, hG⟩ := data_tendsto
  have hn (F : ℝ → PeriodicHolder_STR02968) (hF : Tendsto F (𝓝 (0 : ℝ)) (𝓝 (F 0))) :
      Tendsto (fun h => ‖F h - F 0‖) (𝓝 0) (𝓝 (0 : ℝ)) := by
    have hc : Tendsto (fun _ : ℝ => F 0) (𝓝 (0 : ℝ)) (𝓝 (F 0)) := tendsto_const_nhds
    simpa only [sub_self, norm_zero] using (hF.sub hc).norm
  refine ⟨ε, by simpa only [zero_add] using
    ((((hn _ hφ).add (hn _ hA)).add (hn _ hL)).add (hn _ hS)).add (hn _ hG), fun h x => ?_⟩
  let t := angSec (angEquiv x)
  have hx : angEquiv.symm (t : AngCircle) = x := by
    dsimp only [t]
    rw [coe_angSec, MeasurableEquiv.symm_apply_apply]
  have hnow := data_actual h t
  have hzero := data_actual 0 t
  rw [hx] at hnow hzero
  have hscore0 : (polynomialRankOne 0).dlogq x = 0 := by
    unfold RankOneModel.dlogq
    simp_rw [polynomial_reference_origin, Real.log_one]
    simp [coordPartial, Function.comp_def]
  have hb (F : ℝ → PeriodicHolder_STR02968) :
      |(F h).val t - (F 0).val t| ≤ ‖F h - F 0‖ := by
    exact holder_bound (F h - F 0) t
  have hbφ := hb featureData
  have hbA := hb generatorData
  have hbL := hb logData
  have hbS := hb scoreData
  have hbG := hb gradientData
  rw [hnow.1, hzero.1] at hbφ
  rw [hnow.2.1, hzero.2.1] at hbA
  rw [hnow.2.2.1, hzero.2.2.1, polynomial_reference_origin, Real.log_one, sub_zero] at hbL
  rw [hnow.2.2.2.1, hzero.2.2.2.1, hscore0, sub_zero] at hbS
  rw [hnow.2.2.2.2, hzero.2.2.2.2] at hbG
  dsimp only [ε]
  linarith

/-- A common constant and interval precede the field and every spatial point.
They bound the genuine moving feature, generator, log reference and gradients;
there is no assumed uniform-data factory. -/
theorem polynomial_uniform_data_bound :
    ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧ δ ≤ 1 ∧ ∀ h : ℝ, |h| ≤ δ → ∀ x : Torus 1,
      |(polynomialRankOne h).φ x| ≤ K ∧ |(polynomialRankOne h).Aq x| ≤ K ∧
      |Real.log ((polynomialRankOne h).q x)| ≤ K ∧ |(polynomialRankOne h).dlogq x| ≤ K ∧
      |(polynomialRankOne h).dφ x| ≤ K := by
  obtain ⟨ε, hε, hb⟩ := polynomial_uniform_data_at_origin
  have he := hε.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨r, hr, hsmall⟩ := Metric.eventually_nhds_iff.1 he
  let K := 2 + ‖featureData 0‖ + ‖generatorData 0‖ + ‖gradientData 0‖
  refine ⟨K, min 1 (r / 2), by dsimp [K]; positivity,
    lt_min one_pos (by positivity), min_le_left _ _, fun h hh x => ?_⟩
  have hs : ε h < 1 := hsmall (by
    rw [Real.dist_eq, sub_zero]
    exact hh.trans_lt (lt_of_le_of_lt (min_le_right _ _) (by linarith : r / 2 < r)))
  let t := angSec (angEquiv x)
  have hx : angEquiv.symm (t : AngCircle) = x := by
    dsimp only [t]
    rw [coe_angSec, MeasurableEquiv.symm_apply_apply]
  have hz := data_actual 0 t
  rw [hx] at hz
  have hφ0 : |(polynomialRankOne 0).φ x| ≤ ‖featureData 0‖ := by rw [← hz.1]; exact holder_bound _ _
  have hA0 : |(polynomialRankOne 0).Aq x| ≤ ‖generatorData 0‖ := by rw [← hz.2.1]; exact holder_bound _ _
  have hG0 : |(polynomialRankOne 0).dφ x| ≤ ‖gradientData 0‖ := by rw [← hz.2.2.2.2]; exact holder_bound _ _
  have ht := hb h x
  have hφ := abs_sub_le ((polynomialRankOne h).φ x) ((polynomialRankOne 0).φ x) 0
  have hA := abs_sub_le ((polynomialRankOne h).Aq x) ((polynomialRankOne 0).Aq x) 0
  have hG := abs_sub_le ((polynomialRankOne h).dφ x) ((polynomialRankOne 0).dφ x) 0
  simp only [sub_zero] at hφ hA hG
  dsimp only [K]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith [abs_nonneg ((polynomialRankOne h).φ x - (polynomialRankOne 0).φ x),
      abs_nonneg ((polynomialRankOne h).Aq x - (polynomialRankOne 0).Aq x),
      abs_nonneg (Real.log ((polynomialRankOne h).q x)), abs_nonneg ((polynomialRankOne h).dlogq x),
      abs_nonneg ((polynomialRankOne h).dφ x - (polynomialRankOne 0).dφ x),
      norm_nonneg (featureData 0), norm_nonneg (generatorData 0), norm_nonneg (gradientData 0)]

end DGPS.Examples.PolynomialSpecies
