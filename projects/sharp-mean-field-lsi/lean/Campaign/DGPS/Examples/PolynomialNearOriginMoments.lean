import DGPS.Examples.PolynomialUniformData
import DGPS.Examples.PolynomialSpeciesResidualBound

/-! Genuine quantitative feature and generator moment control near the Haar
root. Constants come from actual moving-reference data; the competitor keeps
its original absolute-H1 domain and AE root convention. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.PositiveRankOne

namespace DGPS.Examples.PolynomialSpecies

private theorem exp_error {q E : ℝ} (hq : 0 < q) (hE : 0 ≤ E) (hE1 : E ≤ 1)
    (hl : |Real.log q| ≤ E) : |q - 1| ≤ 2 * E := by
  have hh := Real.norm_exp_sub_one_sub_id_le (show ‖Real.log q‖ ≤ 1 from by
    simpa only [Real.norm_eq_abs] using hl.trans hE1)
  simp only [Real.norm_eq_abs, Real.exp_log hq] at hh
  have ht := abs_add_le (q - 1 - Real.log q) (Real.log q)
  rw [show q - 1 - Real.log q + Real.log q = q - 1 by ring] at ht
  have hs : |Real.log q| ^ 2 ≤ |Real.log q| := by
    nlinarith [abs_nonneg (Real.log q)]
  linarith

private theorem centered_moment_bound (ρ : AbsoluteDensity 1) (q f : Torus 1 → ℝ)
    (hq : Continuous q) (hf : Continuous f) {B T : ℝ} (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hb : ∀ x, |f x| ≤ B) (hc : ∫ x, q x * f x ∂haar 1 = 0)
    (hnear : ∀ᵐ x ∂haar 1, |ρ.density x - q x| ≤ T) :
    |∫ x, f x ∂(densityMeasure ρ : Measure (Torus 1))| ≤ T * B := by
  have i1 : Integrable (fun x => ρ.density x * f x) (haar 1) :=
    ρ.integrable_density.mul_bdd hf.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have i2 : Integrable (fun x => q x * f x) (haar 1) :=
    (hq.mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : (∫ x, f x ∂(densityMeasure ρ : Measure (Torus 1))) =
      ∫ x, (ρ.density x - q x) * f x ∂haar 1 := by
    rw [RankOneModel.integral_densityMeasure]
    have hh : (fun x => (ρ.density x - q x) * f x) =
        fun x => ρ.density x * f x - q x * f x := by funext x; ring
    rw [hh, integral_sub i1 i2, hc, sub_zero]
  rw [he]
  have hi := norm_integral_le_of_norm_le_const (μ := haar 1)
    (f := fun x => (ρ.density x - q x) * f x) (C := T * B) (by
    filter_upwards [hnear] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hx (hb x) (abs_nonneg _) hT)
  simpa only [Real.norm_eq_abs, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using hi

/-- A common interval, constant and vanishing actual-reference error precede
all original competitors and every AE root-nearness tolerance. Both moments
are true changing-law moments, including the generator expectation. -/
theorem polynomial_near_origin_moment_bound :
    ∃ C δ : ℝ, ∃ ε : ℝ → ℝ, 0 < C ∧ 0 < δ ∧ Tendsto ε (𝓝 0) (𝓝 0) ∧
      ∀ h : ℝ, |h| ≤ δ → ∀ ρ : AbsoluteDensity 1, ∀ θ : ℝ,
        0 ≤ θ → θ ≤ 1 → (∀ᵐ x ∂haar 1, |ρ.sqrt x - 1| ≤ θ) →
        |∫ x, (polynomialRankOne h).φ x ∂(densityMeasure ρ : Measure (Torus 1))| +
          |∫ x, (polynomialRankOne h).Aq x ∂(densityMeasure ρ : Measure (Torus 1))| ≤ C * (θ + ε h) := by
  obtain ⟨ε, hε, hb⟩ := polynomial_uniform_data_at_origin
  obtain ⟨K, δK, hK, hδK, _, hdata⟩ := polynomial_uniform_data_bound
  have hlog (h : ℝ) (x : Torus 1) : |Real.log ((polynomialRankOne h).q x)| ≤ ε h := by
    have hh := hb h x
    nlinarith [abs_nonneg ((polynomialRankOne h).φ x - (polynomialRankOne 0).φ x),
      abs_nonneg ((polynomialRankOne h).Aq x - (polynomialRankOne 0).Aq x),
      abs_nonneg ((polynomialRankOne h).dlogq x),
      abs_nonneg ((polynomialRankOne h).dφ x - (polynomialRankOne 0).dφ x)]
  have hε0 (h : ℝ) : 0 ≤ ε h := (abs_nonneg _).trans (hlog h 0)
  have he : ∀ᶠ h : ℝ in 𝓝 0, ε h ≤ 1 := hε.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨a, ha, hab⟩ := Metric.eventually_nhds_iff.1 he
  let δ := min δK (a / 2)
  refine ⟨6 * K, δ, ε, by positivity, lt_min hδK (half_pos ha), hε,
    fun h hh ρ θ hθ hθ1 hroot => ?_⟩
  let M := polynomialRankOne h
  have hεh0 : 0 ≤ ε h := hε0 h
  have hε1 : ε h ≤ 1 := hab (by
    rw [Real.dist_eq, sub_zero]
    exact hh.trans_lt ((min_le_right _ _).trans_lt (by linarith)))
  have hq (x : Torus 1) : |M.q x - 1| ≤ 2 * ε h := exp_error (M.q_pos x) (hε0 h) hε1 (hlog h x)
  have hd : ∀ᵐ x ∂haar 1, |ρ.density x - M.q x| ≤ 3 * θ + 2 * ε h := by
    filter_upwards [hroot] with x hx
    have hv : |ρ.sqrt x + 1| ≤ 3 := by
      have ht := abs_add_le (ρ.sqrt x - 1) 2
      rw [show ρ.sqrt x - 1 + 2 = ρ.sqrt x + 1 by ring, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
      linarith
    have hs : |ρ.sqrt x ^ 2 - 1| ≤ 3 * θ := by
      rw [show ρ.sqrt x ^ 2 - 1 = (ρ.sqrt x - 1) * (ρ.sqrt x + 1) by ring, abs_mul]
      have hi := mul_le_mul hx hv (abs_nonneg _) hθ
      nlinarith
    have ht := abs_add_le (ρ.sqrt x ^ 2 - 1) (1 - M.q x)
    rw [show ρ.sqrt x ^ 2 - 1 + (1 - M.q x) = ρ.sqrt x ^ 2 - M.q x by ring,
      abs_sub_comm 1 (M.q x)] at ht
    change |ρ.sqrt x ^ 2 - M.q x| ≤ _
    linarith [hq x]
  have hp (x : Torus 1) : |M.φ x| ≤ K := (hdata h (hh.trans (min_le_left _ _)) x).1
  have hA (x : Torus 1) : |M.Aq x| ≤ K := (hdata h (hh.trans (min_le_left _ _)) x).2.1
  have hcφ : ∫ x, M.q x * M.φ x ∂haar 1 = 0 := by
    have hh := M.φ_centered
    simpa only [mul_comm] using hh
  have hcA : ∫ x, M.q x * M.Aq x ∂haar 1 = 0 := by
    have hh := polynomial_residual_centered h 0
    simpa only [zero_mul, sub_zero, LocalGaussianEndpoint.integral_ref_eq] using hh
  have hm := centered_moment_bound ρ M.q M.φ M.q_cont M.φ_cont hK.le
    (by positivity : 0 ≤ 3 * θ + 2 * ε h) hp hcφ hd
  have hAq := centered_moment_bound ρ M.q M.Aq M.q_cont M.Aq_cont hK.le
    (by positivity : 0 ≤ 3 * θ + 2 * ε h) hA hcA hd
  have hi := mul_nonneg hK.le (hε0 h)
  nlinarith

end DGPS.Examples.PolynomialSpecies
