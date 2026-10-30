import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootSixAngularMoments
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootNativeMoments
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootBinaryMargin

/-! Eventual signs of the actual two correction coefficients. The actual
six-moment estimates and original native integral identities discharge every
coefficient condition. No parity, parallelism or kernel-generator commutation
is used. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private def alphaPolynomial (x : Fin 7 → ℝ) : ℝ :=
  (2 * x 3 * x 6 - x 0 * x 3 ^ 2) / (17 * a0)

private def betaPolynomial (x : Fin 7 → ℝ) : ℝ :=
  (16 * (x 1 * x 4 + x 2 * x 5) - 8 * x 0 * (x 1 ^ 2 + x 2 ^ 2)) / a0

private theorem coefficient_neighborhood :
    ∃ r : ℝ, 0 < r ∧ ∀ x : Fin 7 → ℝ,
      dist x (![a0, 1, 0, 1, a0, 0, 9 * a0] : Fin 7 → ℝ) < r →
      0 < alphaPolynomial x ∧ alphaPolynomial x < 5 / 4 ∧ 7 < betaPolynomial x := by
  let p : Fin 7 → ℝ := ![a0, 1, 0, 1, a0, 0, 9 * a0]
  have hα : alphaPolynomial p = 1 := by
    dsimp [alphaPolynomial, p]
    field_simp [a0_pos.ne']
    <;> ring
  have hβ : betaPolynomial p = 8 := by
    dsimp [betaPolynomial, p]
    field_simp [a0_pos.ne']
    <;> ring
  have hcα : ContinuousAt alphaPolynomial p := by unfold alphaPolynomial; fun_prop
  have hcβ : ContinuousAt betaPolynomial p := by unfold betaPolynomial; fun_prop
  have heα : ∀ᶠ x in 𝓝 p, alphaPolynomial x ∈ Set.Ioo (0 : ℝ) (5 / 4) := by
    apply hcα.eventually
    exact Ioo_mem_nhds (by rw [hα]; norm_num) (by rw [hα]; norm_num)
  have hβgt : (7 : ℝ) < betaPolynomial p := by rw [hβ]; norm_num
  have heβ : ∀ᶠ x in 𝓝 p, 7 < betaPolynomial x :=
    hcβ.eventually (lt_mem_nhds hβgt)
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.1 (heα.and heβ)
  refine ⟨r, hr, fun x hx => ?_⟩
  have ht := hb hx
  exact ⟨ht.1.1, ht.1.2, ht.2⟩

/-- The SAME actual native root coefficients have the required strict margins
on one interval chosen before h and before every represented root triple. -/
theorem ordinaryRoot_correction_coefficient_signs (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧
      ∀ h : ℝ, 0 < h → h < δ → ∀ σ : Fin 3 → AbsoluteDensity 1,
        (∀ j θ, (σ j).density (angEquiv.symm θ) =
          rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) →
        0 < ordinaryRootCorrectionAlpha h (ordinaryLSRate (ordinaryReference h)).toReal σ ∧
        ordinaryRootCorrectionAlpha h (ordinaryLSRate (ordinaryReference h)).toReal σ < 5 / 4 ∧
        7 < ordinaryRootCorrectionBeta h (ordinaryLSRate (ordinaryReference h)).toReal σ := by
  obtain ⟨r, hr, hpoly⟩ := coefficient_neighborhood
  obtain ⟨K, δK, hK, hδK, hδKr, _, hKb⟩ := ordinaryRoot_sixAngularMoment_estimates D
  have hz : ContinuousAt (fun h : ℝ => D.Z 0 h 2) 0 :=
    (continuous_apply 2).continuousAt.comp ((D.smoothZ 0).continuousOn.continuousAt
      (Ioo_mem_nhds (by linarith [D.radius_pos]) D.radius_pos))
  have ha : ContinuousAt (fun h : ℝ => a0 * (1 + h ^ 2 * D.Z 0 h 2)) 0 := by fun_prop
  have hae : ∀ᶠ h in 𝓝 (0 : ℝ), |a0 * (1 + h ^ 2 * D.Z 0 h 2) - a0| < r := by
    have ht := ha.eventually (Metric.ball_mem_nhds (a0 * (1 + 0 ^ 2 * D.Z 0 0 2)) hr)
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, add_zero, mul_one,
      Metric.mem_ball, Real.dist_eq] using ht
  obtain ⟨δa, hδa, hab⟩ := Metric.eventually_nhds_iff.1 hae
  let δ := min δK (min δa (r / K))
  have hδ : 0 < δ := lt_min hδK (lt_min hδa (div_pos hr hK))
  refine ⟨δ, hδ, (min_le_left _ _).trans hδKr, fun h hh hhd σ hσ => ?_⟩
  have hhK : h < δK := hhd.trans_le (min_le_left _ _)
  have hha : h < δa := hhd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhr : h < D.radius := hhK.trans_le hδKr
  have hKh : K * h < r := by
    have ht := hhd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    nlinarith [(lt_div_iff₀ hK).mp ht]
  obtain ⟨_, _, _, _, _, _, _, _, hrate⟩ := D.roots h hh hhr
  have har : |(ordinaryLSRate (ordinaryReference h)).toReal - a0| < r := by
    rw [hrate 0]
    exact hab (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hh] using hha)
  obtain ⟨hc, hs, hb, hac, has, habb⟩ := hKb h hh hhK
  obtain ⟨nc, ns, nb, nac, nas, nab⟩ := ordinaryChart_native_six_moments hh
    (chartU_STR02924 D.ψ h (D.Z 0 h)) (σ 0) (hσ 0)
  let x : Fin 7 → ℝ := ![(ordinaryLSRate (ordinaryReference h)).toReal,
    momC h (densityMeasure (σ 0)), momS h (densityMeasure (σ 0)), momB h (densityMeasure (σ 0)),
    ∫ y, elementaryFeatureGenerator h (featureC h) y ∂(densityMeasure (σ 0) : Measure (Torus 1)),
    ∫ y, elementaryFeatureGenerator h (featureS h) y ∂(densityMeasure (σ 0) : Measure (Torus 1)),
    ∫ y, elementaryFeatureGenerator h (featureB h) y ∂(densityMeasure (σ 0) : Measure (Torus 1))]
  have hd : dist x (![a0, 1, 0, 1, a0, 0, 9 * a0] : Fin 7 → ℝ) < r := by
    apply (dist_pi_lt_iff hr).2
    intro i
    fin_cases i <;> rw [Real.dist_eq]
    · change |(ordinaryLSRate (ordinaryReference h)).toReal - a0| < r
      exact har
    · change |momC h (densityMeasure (σ 0)) - 1| < r
      rw [nc]
      exact hc.trans_lt hKh
    · change |momS h (densityMeasure (σ 0)) - 0| < r
      rw [ns, sub_zero]
      exact hs.trans_lt hKh
    · change |momB h (densityMeasure (σ 0)) - 1| < r
      rw [nb]
      exact hb.trans_lt hKh
    · change |(∫ y, elementaryFeatureGenerator h (featureC h) y
          ∂(densityMeasure (σ 0) : Measure (Torus 1))) - a0| < r
      rw [nac]
      simpa only [DGPS.a0, a0] using hac.trans_lt hKh
    · change |(∫ y, elementaryFeatureGenerator h (featureS h) y
          ∂(densityMeasure (σ 0) : Measure (Torus 1))) - 0| < r
      rw [nas, sub_zero]
      simpa only [DGPS.a0, a0] using has.trans_lt hKh
    · change |(∫ y, elementaryFeatureGenerator h (featureB h) y
          ∂(densityMeasure (σ 0) : Measure (Torus 1))) - 9 * a0| < r
      rw [nab]
      simpa only [DGPS.a0, a0] using habb.trans_lt hKh
  have ht := hpoly x hd
  simpa only [alphaPolynomial, betaPolynomial, x, ordinaryRootCorrectionAlpha,
    ordinaryRootCorrectionBeta, threefoldAlpha, threefoldBeta, planeDot,
    Complex.normSq_apply, pow_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] using ht

end DGPS.Examples.ThreeSpeciesCircle
