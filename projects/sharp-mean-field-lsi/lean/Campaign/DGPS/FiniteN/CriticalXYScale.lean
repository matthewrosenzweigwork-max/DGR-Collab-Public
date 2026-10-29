import DGPS.FiniteN.CriticalXYCorrection
import DGPS.FiniteN.Tools.StrongConvexityLSIFinal

/-!
# Critical auxiliary LSI scale (FIN029)

For `N ≥ 1` the auxiliary law `η_N(dz) ∝ exp[-N(|z|²/4 - log I₀(|z|))] dz` on `ℝ²` has Euclidean
log-Sobolev rate at least `c₁ √N`, `c₁ = a e^{-1/2-a}`, `a = c₀/2`, `c₀ = (16 e^{1/4})⁻¹`.
-/
open MeasureTheory

namespace DGPS.FiniteN

/-- the law `η_N ∝ exp(-N (‖z‖²/4 - log I₀ ‖z‖))` on `ℝ²` -/
noncomputable def criticalAuxiliaryLaw (N : ℝ) : Measure (EuclideanSpace ℝ (Fin 2)) :=
  Tools.StrongConvexityLSI.gibbs (fun z : EuclideanSpace ℝ (Fin 2) => N * criticalPotential z)

/-- the constant `c₁ = a e^{-1/2-a}` with `a = c₀/2`, `c₀ = (16 e^{1/4})⁻¹` -/
noncomputable def criticalAuxiliaryRate : ℝ :=
  ((16 * Real.exp (1 / 4))⁻¹ / 2) *
    Real.exp (-(1 / 2) - (16 * Real.exp (1 / 4))⁻¹ / 2)

theorem criticalAuxiliaryRate_pos : 0 < criticalAuxiliaryRate := by
  unfold criticalAuxiliaryRate; positivity

theorem criticalAuxiliaryLaw_eq_map (N : ℝ) (hN : 1 ≤ N) :
    criticalAuxiliaryLaw N =
      (Tools.StrongConvexityLSI.gibbs
        (criticalScaledPotential (E := EuclideanSpace ℝ (Fin 2)) N)).map
        (Tools.StrongConvexityLSI.dil (N ^ (1 / 4 : ℝ)) (by positivity)).symm := by
  have hN0 : 0 < N := by linarith
  set s : ℝ := N ^ (1 / 4 : ℝ) with hs
  have hspos : 0 < s := by positivity
  have hc : N ^ (-(1 / 4 : ℝ)) = s⁻¹ := by
    rw [hs, Real.rpow_neg hN0.le]
  set Φ : EuclideanSpace ℝ (Fin 2) → ℝ := fun z => N * criticalPotential z with hΦ
  have hU : criticalScaledPotential (E := EuclideanSpace ℝ (Fin 2)) N =
      fun y => Φ (s⁻¹ • y) := by
    rw [criticalScaledPotential_eq N hN, hc]
  set Zz : ℝ := ∫ z, Real.exp (-Φ z) with hZz
  have hZy : ∫ y, Real.exp (-criticalScaledPotential (E := EuclideanSpace ℝ (Fin 2)) N y) =
      s ^ 2 * Zz := by
    rw [hU]
    have := Measure.integral_comp_smul (μ := (volume : Measure (EuclideanSpace ℝ (Fin 2))))
      (fun z => Real.exp (-Φ z)) s⁻¹
    rw [this]
    simp only [finrank_euclideanSpace_fin, smul_eq_mul]
    rw [inv_pow, inv_inv, abs_of_pos (by positivity)]
  ext A hA
  unfold criticalAuxiliaryLaw Tools.StrongConvexityLSI.gibbs
  rw [Measure.map_apply (Tools.StrongConvexityLSI.dil s hspos).symm.measurable hA,
    withDensity_apply _ hA, withDensity_apply _ ((Tools.StrongConvexityLSI.dil s hspos).symm.measurable hA)]
  rw [hZy, hU]
  have hdil : ∀ y : EuclideanSpace ℝ (Fin 2), (Tools.StrongConvexityLSI.dil s hspos).symm y = s⁻¹ • y := fun y => rfl
  have hpre : (Tools.StrongConvexityLSI.dil s hspos).symm ⁻¹' A = (fun y => s⁻¹ • y) ⁻¹' A := by
    ext y; simp [hdil]
  rw [hpre]
  set G : EuclideanSpace ℝ (Fin 2) → ENNReal := fun z =>
    ENNReal.ofReal (Real.exp (-Φ z) / (s ^ 2 * Zz)) with hG
  have h1 : ∫⁻ y in (fun y => s⁻¹ • y) ⁻¹' A,
      ENNReal.ofReal (Real.exp (-Φ (s⁻¹ • y)) / (s ^ 2 * Zz)) =
      ∫⁻ y, A.indicator G (s⁻¹ • y) := by
    rw [← lintegral_indicator (measurable_const_smul s⁻¹ hA)]
    refine lintegral_congr fun y => ?_
    by_cases hy : s⁻¹ • y ∈ A <;> simp [Set.indicator, hy, hG]
  rw [h1, ← lintegral_indicator hA]
  have h2 : ∫⁻ y, A.indicator G (s⁻¹ • y) = ENNReal.ofReal (s ^ 2) * ∫⁻ z, A.indicator G z := by
    have hm : Measurable (A.indicator G) := by
      refine Measurable.indicator ?_ hA
      refine ENNReal.measurable_ofReal.comp ?_
      refine Measurable.div_const (Real.measurable_exp.comp ?_) _
      exact (continuous_const.mul ((critical_radial_hessian_coercivity
        (E := EuclideanSpace ℝ (Fin 2))).1.continuous.comp continuous_id)).measurable.neg
    have := lintegral_map (μ := (volume : Measure (EuclideanSpace ℝ (Fin 2))))
      hm (measurable_const_smul s⁻¹)
    have hmap := Measure.map_addHaar_smul (volume : Measure (EuclideanSpace ℝ (Fin 2)))
      (inv_ne_zero hspos.ne')
    rw [← this]
    rw [hmap, lintegral_smul_measure]
    simp only [finrank_euclideanSpace_fin, smul_eq_mul]
    rw [inv_pow, inv_inv, abs_of_pos (by positivity)]
  rw [h2, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ A
  · simp only [Set.indicator, hz, ite_true, hG]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hs2 : s ^ 2 ≠ 0 := by positivity
    field_simp
    rfl
  · simp [Set.indicator, hz]

/-- **FIN029.** The auxiliary law `η_N` has Euclidean LSI rate `c₁ √N` for every `N ≥ 1`
(`Ent(f²) ≤ (2/(c₁√N)) ∫ |∇f|² dη_N`), with `c₁ = a e^{-1/2-a} > 0`, `a = c₀/2`. -/
theorem critical_auxiliary_lsi_scale :
    criticalAuxiliaryRate =
      ((16 * Real.exp (1 / 4))⁻¹ / 2) * Real.exp (-(1 / 2) - (16 * Real.exp (1 / 4))⁻¹ / 2) ∧
    0 < criticalAuxiliaryRate ∧
    ∀ N : ℝ, 1 ≤ N →
      Tools.StrongConvexityLSI.HasLSIRate (criticalAuxiliaryLaw N)
        (criticalAuxiliaryRate * Real.sqrt N) := by
  refine ⟨rfl, criticalAuxiliaryRate_pos, fun N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  obtain ⟨hU, -, hq, hosc, hconv⟩ :=
    critical_scaled_bounded_correction (E := EuclideanSpace ℝ (Fin 2))
  set a : ℝ := (16 * Real.exp (1 / 4))⁻¹ / 2 with ha
  have hapos : 0 < a := by rw [ha]; positivity
  have hUq : ContDiff ℝ 2 (fun x => criticalScaledPotential (E := EuclideanSpace ℝ (Fin 2)) N x +
      criticalBoundedCorrection x) :=
    ((hU N hN).add hq).of_le (by simp)
  have h1 := (Tools.strong_convexity_lsi_and_bounded_correction).2.1 2
    (criticalScaledPotential (E := EuclideanSpace ℝ (Fin 2)) N) criticalBoundedCorrection a
    (a * Real.exp (-(1 / 2))) (by positivity)
    ((hU N hN).continuous) hq.continuous.measurable
    (fun x y => (le_abs_self _).trans (hosc x y)) hUq
    (fun x v => hconv N hN x v)
  have h2 := (Tools.strong_convexity_lsi_and_bounded_correction).2.2 2 (N ^ (1 / 4 : ℝ))
    (by positivity) _ _ (by positivity) h1
  rw [criticalAuxiliaryLaw_eq_map N hN]
  convert h2 using 1
  have hs : (N ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, Real.sqrt_eq_rpow]
    norm_num
  rw [hs, criticalAuxiliaryRate, ← ha, Real.exp_sub, Real.exp_neg, Real.exp_neg]
  ring

end DGPS.FiniteN
