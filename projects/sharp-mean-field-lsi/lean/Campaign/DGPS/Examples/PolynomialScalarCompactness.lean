import DGPS.Examples.PolynomialSpeciesDescentBridge
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryOptimizers
import DGPS.Variational.SpeciesInclusion

/-! Fixed-field bounded scalar quotients for the actual polynomial model imply
genuine compactness on the original absolute square-root H1 domain. The limit
is allowed to have zero gap. No information bound is an input. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace DGPS.Examples.PolynomialSpecies
open DGPS.PositiveRankOne DGPS.Examples.PolynomialExactGap
open DGPS.Examples.ThreeSpeciesCircle

private def bcf (f : Torus 1 → ℝ) (hf : Continuous f) : Torus 1 →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩

private theorem moment_bound (f : Torus 1 → ℝ) (hf : Continuous f)
    (ν : ProbabilityMeasure (Torus 1)) :
    |∫ x, f x ∂(ν : Measure (Torus 1))| ≤ ‖bcf f hf‖ := by
  have hb := norm_integral_le_of_norm_le_const (μ := (ν : Measure (Torus 1)))
    (Eventually.of_forall fun x => (bcf f hf).norm_coe_le_norm x)
  change |∫ x, f x ∂(ν : Measure (Torus 1))| ≤ ‖bcf f hf‖ *
    (ν : Measure (Torus 1)).real Set.univ at hb
  simpa only [probReal_univ, mul_one] using hb

private theorem scalar_identities (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (ρ : AbsoluteDensity 1) :
    let M := polynomialRankOne h
    (scalarGap (canonical_elementary_polynomial_model h) ρ : ℝ) =
      (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) M.ref.measure).toReal +
        eta / 2 * (∫ x, M.φ x ∂(densityMeasure ρ : Measure (Torus 1))) ^ 2 ∧
    ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) M.ref ≠ ⊤ ∧
    scalarDissipation (canonical_elementary_polynomial_model h) b ρ ≠ ⊤ ∧
    (scalarDissipation (canonical_elementary_polynomial_model h) b ρ).toReal =
      (ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) M.ref).toReal +
        2 * eta * (∫ x, M.φ x ∂(densityMeasure ρ : Measure (Torus 1))) *
          (∫ x, M.Aq x ∂(densityMeasure ρ : Measure (Torus 1))) +
        eta ^ 2 * (∫ x, M.φ x ∂(densityMeasure ρ : Measure (Torus 1))) ^ 2 *
          (∫ x, M.dφ x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))) := by
  obtain ⟨hg, hI, hD, hv⟩ := polynomial_family_gap_and_dissipation h b (SpeciesFamily.single ρ)
  refine ⟨?_, hI 0, ?_, ?_⟩
  · simpa only [speciesGap_single, densityMeasure_barycenter_single, sum_single_count,
      SpeciesFamily.single_weight, SpeciesFamily.single_density, one_mul,
      polynomialRankOne_reference] using hg
  · simpa only [speciesDissipation_single] using hD
  · simpa only [speciesDissipation_single, densityMeasure_barycenter_single, sum_single_count,
      SpeciesFamily.single_weight, SpeciesFamily.single_density, one_mul] using hv

private theorem haar_entropy (ρ : AbsoluteDensity 1) :
    (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (haar 1)).toReal =
      DGPS.Analysis.circleEntropy ρ := by
  have he : relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (haar 1) =
      homogeneousEntropy (haar 1) ρ.density := by
    rw [densityMeasure_coe]
    exact relativeEntropy_withDensity (Eventually.of_forall ρ.density_nonneg)
      ρ.integrable_density.aemeasurable
  rw [he]
  rfl

private theorem haar_fisher_bound (M : RankOneModel) (ρ : AbsoluteDensity 1) :
    DGPS.Analysis.circleFisherInformation ρ ≤
      2 * (ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) M.ref).toReal +
        2 * ‖bcf M.dlogq M.dlogq_cont‖ ^ 2 := by
  let B := ‖bcf M.dlogq M.dlogq_cont‖
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  have hi := (M.dissipation_integral hw 0).1
  have hg := (memLp_coord hw.memLp_grad 0).integrable_sq
  have hd := ρ.integrable_density.const_mul (2 * B ^ 2)
  have he : DGPS.Analysis.circleFisherInformation ρ =
      ∫ x, 4 * (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ∂haar 1 := by
    unfold DGPS.Analysis.circleFisherInformation
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by
      change 4 * ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 =
        4 * (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2
      rw [RankOneModel.norm_sq_tangent])
  rw [he, M.fisher_eq, ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  have hpt (x : Torus 1) : 4 * (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ≤
      2 * (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x) ^ 2 +
        2 * B ^ 2 * ρ.density x := by
    have hq : |M.dlogq x| ≤ B := by
      have ht := (bcf M.dlogq M.dlogq_cont).norm_coe_le_norm x
      change ‖M.dlogq x‖ ≤ B at ht
      simpa only [Real.norm_eq_abs] using ht
    have hs := pow_le_pow_left₀ (abs_nonneg _) hq 2
    rw [sq_abs] at hs
    have ht := mul_le_mul_of_nonneg_left hs (sq_nonneg (ρ.sqrt x))
    change 4 * (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ≤
      2 * (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x) ^ 2 +
        2 * B ^ 2 * ρ.sqrt x ^ 2
    nlinarith [sq_nonneg (weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x)]
  have hb := integral_mono (hg.const_mul 4) ((hi.const_mul 2).add hd) hpt
  change (∫ x, 4 * (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ∂haar 1) ≤
    ∫ x, 2 * (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x) ^ 2 +
      2 * B ^ 2 * ρ.density x ∂haar 1 at hb
  have hm : (∫ x, 2 * B ^ 2 * ρ.density x ∂haar 1) = 2 * B ^ 2 := by
    rw [integral_const_mul, ρ.integral_density, mul_one]
  rw [integral_add (hi.const_mul 2) hd, hm] at hb
  simpa only [integral_const_mul] using hb

/-- Constants are chosen at the fixed field and quotient bound before every
original absolute density. No bound on information, density, or a limiting gap
is imposed. -/
theorem polynomial_scalar_boundedQuotient_information (h Mq : ℝ) (hMq : 0 ≤ Mq)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ρ : AbsoluteDensity 1,
      0 < scalarGap (canonical_elementary_polynomial_model h) ρ →
      scalarQuotient (canonical_elementary_polynomial_model h) b ρ ≤ ENNReal.ofReal Mq →
      DGPS.Analysis.circleFisherInformation ρ ≤ B ∧ DGPS.Analysis.circleEntropy ρ ≤ B := by
  let M := polynomialRankOne h
  have hη := eta_pos
  let P := ‖bcf M.φ M.φ_cont‖
  let A := ‖bcf M.Aq M.Aq_cont‖
  let L := ‖bcf (fun x => Real.log (M.q x)) M.log_smooth.continuous_torus‖
  let S := ‖bcf M.dlogq M.dlogq_cont‖
  let C := 4 * Mq * (L + eta / 2 * P ^ 2) + 4 * eta * P * A + 2 * S ^ 2
  have hC : 0 ≤ C := by dsimp only [C, P, A, L, S]; positivity
  let Hmax := 2 * (6 * ((1 + (C + 1)) / (12 * (4 * Mq) + 1) - 1 +
    Real.log (12 * (4 * Mq) + 1)))
  refine ⟨max (4 * Mq * Hmax + C) (max Hmax 0),
    (le_max_right _ _).trans' (le_max_right _ _), fun ρ hG hQ => ?_⟩
  obtain ⟨hgap, hIfin, hDfin, hD⟩ := scalar_identities h b ρ
  have hm := moment_bound M.φ M.φ_cont (densityMeasure ρ)
  have ha := moment_bound M.Aq M.Aq_cont (densityMeasure ρ)
  have hl := moment_bound (fun x => Real.log (M.q x)) M.log_smooth.continuous_torus (densityMeasure ρ)
  have hsq : (∫ x, M.φ x ∂(densityMeasure ρ : Measure (Torus 1))) ^ 2 ≤ P ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hm 2
  have hprod : |(∫ x, M.φ x ∂(densityMeasure ρ : Measure (Torus 1))) *
      (∫ x, M.Aq x ∂(densityMeasure ρ : Measure (Torus 1)))| ≤ P * A := by
    rw [abs_mul]
    exact mul_le_mul hm ha (abs_nonneg _) (norm_nonneg _)
  have hHaar := M.entropy_ref_eq (densityMeasure ρ) (absoluteDensity_entropy_finite ρ).2.2.1
  rw [haar_entropy] at hHaar
  have hgapBound : (scalarGap (canonical_elementary_polynomial_model h) ρ : ℝ) ≤
      DGPS.Analysis.circleEntropy ρ + L + eta / 2 * P ^ 2 := by
    rw [hgap, hHaar]
    have hsq' := mul_le_mul_of_nonneg_left hsq (show 0 ≤ eta / 2 by positivity)
    linarith [(abs_le.mp hl).1]
  have hDq : (scalarDissipation (canonical_elementary_polynomial_model h) b ρ).toReal ≤
      2 * Mq * (scalarGap (canonical_elementary_polynomial_model h) ρ : ℝ) := by
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hQ
    unfold scalarQuotient at hr
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.coe_toReal, ENNReal.toReal_ofReal hMq] at hr
    have hp : (0 : ℝ) < (scalarGap (canonical_elementary_polynomial_model h) ρ : ℝ) := by exact_mod_cast hG
    have ht := (div_le_iff₀ (by positivity : 0 < 2 * (scalarGap (canonical_elementary_polynomial_model h) ρ : ℝ))).1 hr
    nlinarith
  have hIrel : (ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) M.ref).toReal ≤
      (scalarDissipation (canonical_elementary_polynomial_model h) b ρ).toReal + 2 * eta * P * A := by
    have hj : 0 ≤ ∫ x, M.dφ x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1)) := integral_nonneg fun _ => sq_nonneg _
    have ht := mul_le_mul_of_nonneg_left (abs_le.mp hprod).1 (show 0 ≤ 2 * eta by positivity)
    have hn := mul_nonneg (mul_nonneg (sq_nonneg eta)
      (sq_nonneg (∫ x, M.φ x ∂(densityMeasure ρ : Measure (Torus 1))))) hj
    nlinarith
  have hIH : DGPS.Analysis.circleFisherInformation ρ ≤ 4 * Mq * DGPS.Analysis.circleEntropy ρ + C := by
    have hf := haar_fisher_bound M ρ
    have ht := mul_le_mul_of_nonneg_left hgapBound (show 0 ≤ 2 * Mq by positivity)
    dsimp only [C, S]
    nlinarith
  have hH0 := circleEntropy_nonneg ρ
  have hI0 := circleFisherInformation_nonneg ρ
  have hHlog : DGPS.Analysis.circleEntropy ρ ≤
      6 * Real.log (1 + (4 * Mq) * DGPS.Analysis.circleEntropy ρ + (C + 1)) := by
    have ht := Real.log_le_log (by positivity : 0 < 2 + DGPS.Analysis.circleFisherInformation ρ)
      (show 2 + DGPS.Analysis.circleFisherInformation ρ ≤
        1 + (4 * Mq) * DGPS.Analysis.circleEntropy ρ + (C + 1) by linarith)
    linarith [circleEntropy_le_log_information ρ]
  have hHmax : DGPS.Analysis.circleEntropy ρ ≤ Hmax :=
    solve_entropy_log (by positivity) (by positivity) hH0 hHlog
  refine ⟨?_, hHmax.trans ((le_max_left _ _).trans (le_max_right _ _))⟩
  exact (hIH.trans (add_le_add
    (mul_le_mul_of_nonneg_left hHmax (show 0 ≤ 4 * Mq by positivity)) le_rfl)).trans (le_max_left _ _)

/-- Actual fixed-field scalar sublevels are compact in the original root topology,
with entropy convergence and native Haar Fisher lower semicontinuity. The limit
is not required or asserted to have positive gap. -/
theorem polynomial_scalar_boundedQuotient_compactness (h Mq : ℝ) (hMq : 0 ≤ Mq)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h))
    (ρ : ℕ → AbsoluteDensity 1)
    (hG : ∀ n, 0 < scalarGap (canonical_elementary_polynomial_model h) (ρ n))
    (hQ : ∀ n, scalarQuotient (canonical_elementary_polynomial_model h) b (ρ n) ≤ ENNReal.ofReal Mq) :
    ∃ (B : ℝ), 0 ≤ B ∧
      (∀ n, DGPS.Analysis.circleFisherInformation (ρ n) ≤ B ∧ DGPS.Analysis.circleEntropy (ρ n) ≤ B) ∧
      ∃ (φ : ℕ → ℕ) (ρL : AbsoluteDensity 1) (η : ℕ → ℝ) (R : ℝ),
        StrictMono φ ∧ Tendsto η atTop (𝓝 0) ∧
        (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n)).sqrt x - ρL.sqrt x| ≤ η n) ∧
        (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n)).sqrt x| ≤ R) ∧
        (∀ x, |ρL.sqrt x| ≤ R) ∧
        Tendsto (fun n => DGPS.Analysis.circleEntropy (ρ (φ n))) atTop
          (𝓝 (DGPS.Analysis.circleEntropy ρL)) ∧
        ENNReal.ofReal (DGPS.Analysis.circleFisherInformation ρL) ≤
          liminf (fun n => ENNReal.ofReal (DGPS.Analysis.circleFisherInformation (ρ (φ n)))) atTop := by
  obtain ⟨B, hB, hbound⟩ := polynomial_scalar_boundedQuotient_information h Mq hMq b
  have hBn := fun n => hbound (ρ n) (hG n) (hQ n)
  obtain ⟨φ, ρL, η, R, hφ, hη, hae, hub, hRL, hlsc⟩ :=
    exists_limit_of_bounded_fisher ρ (fun n => (hBn n).1)
  have hpt : ∀ᵐ x ∂haar 1, Tendsto (fun n => (ρ (φ n)).sqrt x) atTop (𝓝 (ρL.sqrt x)) := by
    filter_upwards [ae_all_iff.mpr hae] with x hx
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by simpa only [Real.norm_eq_abs] using hx n) hη
  exact ⟨B, hB, hBn, φ, ρL, η, R, hφ, hη, hae, hub, hRL,
    tendsto_circleEntropy hub hpt, hlsc⟩

private theorem roots_pointwise (ρ : ℕ → AbsoluteDensity 1) (ρL : AbsoluteDensity 1)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - ρL.sqrt x| ≤ η n) :
    ∀ᵐ x ∂haar 1, Tendsto (fun n => (ρ n).sqrt x) atTop (𝓝 (ρL.sqrt x)) := by
  filter_upwards [ae_all_iff.mpr hae] with x hx
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by
    simpa only [Real.norm_eq_abs] using hx n) hη

private theorem moments_uniform (ρ : ℕ → AbsoluteDensity 1) (ρL : AbsoluteDensity 1)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - ρL.sqrt x| ≤ η n)
    (R : ℝ) (hub : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x| ≤ R)
    (f : Torus 1 → ℝ) (hf : Continuous f) :
    Tendsto (fun n => ∫ x, f x ∂(densityMeasure (ρ n) : Measure (Torus 1))) atTop
      (𝓝 (∫ x, f x ∂(densityMeasure ρL : Measure (Torus 1)))) := by
  have ht := tendsto_integral_comp_mul (T := fun t : ℝ => t ^ 2) (continuous_pow 2)
    hf (Cc := ‖bcf f hf‖) (fun x => by
      have ht := (bcf f hf).norm_coe_le_norm x
      change ‖f x‖ ≤ ‖bcf f hf‖ at ht
      simpa only [Real.norm_eq_abs] using ht)
    (fun n => (ρ n).memLp_sqrt.aestronglyMeasurable) hub (roots_pointwise ρ ρL hη hae)
  simpa only [RankOneModel.integral_densityMeasure, AbsoluteDensity.density] using ht

/-- Actual gap continuity at a fixed field, including a possibly zero limiting gap. -/
theorem polynomial_scalarGap_tendsto (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h))
    (ρ : ℕ → AbsoluteDensity 1) (ρL : AbsoluteDensity 1)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - ρL.sqrt x| ≤ η n)
    (R : ℝ) (hub : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x| ≤ R) :
    Tendsto (fun n => (scalarGap (canonical_elementary_polynomial_model h) (ρ n) : ℝ≥0∞)) atTop
      (𝓝 (scalarGap (canonical_elementary_polynomial_model h) ρL : ℝ≥0∞)) := by
  let M := polynomialRankOne h
  have hm := moments_uniform ρ ρL hη hae R hub M.φ M.φ_cont
  have hl := moments_uniform ρ ρL hη hae R hub (fun x => Real.log (M.q x)) M.log_smooth.continuous_torus
  have hH := tendsto_circleEntropy hub (roots_pointwise ρ ρL hη hae)
  have he (τ : AbsoluteDensity 1) : (scalarGap (canonical_elementary_polynomial_model h) τ : ℝ) =
      DGPS.Analysis.circleEntropy τ -
        (∫ x, Real.log (M.q x) ∂(densityMeasure τ : Measure (Torus 1))) +
          eta / 2 * (∫ x, M.φ x ∂(densityMeasure τ : Measure (Torus 1))) ^ 2 := by
    rw [(scalar_identities h b τ).1,
      M.entropy_ref_eq (densityMeasure τ) (absoluteDensity_entropy_finite τ).2.2.1, haar_entropy]
  have ht := (hH.sub hl).add ((hm.pow 2).const_mul (eta / 2))
  have hr : Tendsto (fun n => (scalarGap (canonical_elementary_polynomial_model h) (ρ n) : ℝ)) atTop
      (𝓝 (scalarGap (canonical_elementary_polynomial_model h) ρL : ℝ)) := by simpa only [he] using ht
  simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.tendsto_ofReal hr

private theorem scalar_square (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (ρ : AbsoluteDensity 1) :
    let M := polynomialRankOne h
    scalarDissipation (canonical_elementary_polynomial_model h) b ρ =
      ENNReal.ofReal (∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x +
        (eta * ∫ y, M.φ y ∂(densityMeasure ρ : Measure (Torus 1))) * (ρ.sqrt x * M.dφ x)) ^ 2 ∂haar 1) := by
  let M := polynomialRankOne h
  let bM := polynomialRankOneDrift h b
  have he : scalarDissipation (canonical_elementary_polynomial_model h) b ρ =
      scalarDissipation M.data bM ρ := rfl
  rw [he]
  unfold scalarDissipation scalarScore
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  have hi := (M.dissipation_integral hw
    (eta * ∫ y, M.φ y ∂(densityMeasure ρ : Measure (Torus 1)))).2.1
  have hi' : Integrable (fun x => (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x +
      (eta * ∫ y, M.φ y ∂(densityMeasure ρ : Measure (Torus 1))) * (ρ.sqrt x * M.dφ x)) ^ 2) (haar 1) := by
    convert hi using 1 <;> funext x <;> congr 1 <;> ring
  change (∫⁻ x, ENNReal.ofReal
      (‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • bM.force ρ x‖ ^ 2) ∂haar 1) =
    ENNReal.ofReal (∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x +
      (eta * ∫ y, M.φ y ∂(densityMeasure ρ : Measure (Torus 1))) * (ρ.sqrt x * M.dφ x)) ^ 2 ∂haar 1)
  rw [RankOneModel.ofReal_integral_eq hi' (fun _ => sq_nonneg _)]
  refine lintegral_congr_ae ?_
  filter_upwards [M.force_coord bM ρ] with x hx
  rw [RankOneModel.norm_sq_tangent]
  congr 2
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hx]
  change 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 + ρ.sqrt x *
      (-M.dlogq x + eta * (∫ y, M.φ y ∂(densityMeasure ρ : Measure (Torus 1))) * M.dφ x) = _
  ring

private theorem weighted_root_fourier (ρ : ℕ → AbsoluteDensity 1) (ρL : AbsoluteDensity 1)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - ρL.sqrt x| ≤ η n)
    (c : Torus 1 → ℝ) (hc : Continuous c) (k : Fin 1 → ℤ) :
    Tendsto (fun n => DGPS.fourierCoeff (fun x => (ρ n).sqrt x * c x) k) atTop
      (𝓝 (DGPS.fourierCoeff (fun x => ρL.sqrt x * c x) k)) := by
  let C := ‖bcf c hc‖
  refine tendsto_fourierCoeff_of_ae_bound
    (fun n => RankOneModel.memLp_mul_cont hc (ρ n).memLp_sqrt)
    (RankOneModel.memLp_mul_cont hc ρL.memLp_sqrt)
    (ε := fun n => |η n| * C) (by simpa using hη.abs.mul_const C) (fun n => ?_) k
  filter_upwards [hae n] with x hx
  rw [← sub_mul, abs_mul]
  have hb : |c x| ≤ C := by
    have ht := (bcf c hc).norm_coe_le_norm x
    change ‖c x‖ ≤ C at ht
    simpa only [Real.norm_eq_abs] using ht
  exact mul_le_mul (hx.trans (le_abs_self _)) hb (abs_nonneg _) (abs_nonneg _)

private theorem coefficient_add {f g : Torus 1 → ℝ} (hf : MemLp f 2 (haar 1))
    (hg : MemLp g 2 (haar 1)) (k : Fin 1 → ℤ) :
    DGPS.fourierCoeff (fun x => f x + g x) k = DGPS.fourierCoeff f k + DGPS.fourierCoeff g k := by
  have he : (fun x => f x + g x) = fun x => f x - (-1 : ℝ) * g x := by funext x; ring
  rw [he, fourierCoeff_sub' hf (hg.const_mul (-1)), fourierCoeff_const_mul]
  simp

/-- Genuine changing-mean-field scalar dissipation lower semicontinuity. Weak
derivatives are identified through their Fourier integration-by-parts identity;
no derivative convergence or desired lower semicontinuity is an input. -/
theorem polynomial_scalarDissipation_le_liminf (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h))
    (ρ : ℕ → AbsoluteDensity 1) (ρL : AbsoluteDensity 1)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - ρL.sqrt x| ≤ η n)
    (R : ℝ) (hub : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x| ≤ R) :
    scalarDissipation (canonical_elementary_polynomial_model h) b ρL ≤
      liminf (fun n => scalarDissipation (canonical_elementary_polynomial_model h) b (ρ n)) atTop := by
  let M := polynomialRankOne h
  let S := fun τ : AbsoluteDensity 1 => fun x =>
    2 * weakGradient τ.sqrt τ.sqrt_mem x 0 - τ.sqrt x * M.dlogq x +
      (eta * ∫ y, M.φ y ∂(densityMeasure τ : Measure (Torus 1))) * (τ.sqrt x * M.dφ x)
  have hs (τ : AbsoluteDensity 1) : MemLp (S τ) 2 (haar 1) :=
    (((memLp_coord (isWeakGradient_weakGradient τ.sqrt_mem).memLp_grad 0).const_mul 2).sub
      (RankOneModel.memLp_mul_cont M.dlogq_cont τ.memLp_sqrt)).add
        ((RankOneModel.memLp_mul_cont M.dφ_cont τ.memLp_sqrt).const_mul _)
  simp_rw [scalar_square]
  change ENNReal.ofReal (∫ x, S ρL x ^ 2 ∂haar 1) ≤
    liminf (fun n => ENNReal.ofReal (∫ x, S (ρ n) x ^ 2 ∂haar 1)) atTop
  refine ofReal_integral_sq_le_liminf (fun n => hs (ρ n)) (hs ρL) fun k => ?_
  have hu := tendsto_fourierCoeff_of_ae_bound (fun n => (ρ n).memLp_sqrt) ρL.memLp_sqrt hη hae k
  have hl := weighted_root_fourier ρ ρL hη hae M.dlogq M.dlogq_cont k
  have hd := weighted_root_fourier ρ ρL hη hae M.dφ M.dφ_cont k
  have hm := moments_uniform ρ ρL hη hae R hub M.φ M.φ_cont
  have hid (τ : AbsoluteDensity 1) : DGPS.fourierCoeff (S τ) k =
      2 * (2 * Real.pi * Complex.I * (k 0 : ℂ) * DGPS.fourierCoeff τ.sqrt k) -
        DGPS.fourierCoeff (fun x => τ.sqrt x * M.dlogq x) k +
        ((eta * ∫ y, M.φ y ∂(densityMeasure τ : Measure (Torus 1))) : ℂ) *
          DGPS.fourierCoeff (fun x => τ.sqrt x * M.dφ x) k := by
    calc
      DGPS.fourierCoeff (S τ) k =
          DGPS.fourierCoeff (fun x => 2 * weakGradient τ.sqrt τ.sqrt_mem x 0 - τ.sqrt x * M.dlogq x) k +
          DGPS.fourierCoeff (fun x =>
            (eta * ∫ y, M.φ y ∂(densityMeasure τ : Measure (Torus 1))) * (τ.sqrt x * M.dφ x)) k :=
        coefficient_add
          (((memLp_coord (isWeakGradient_weakGradient τ.sqrt_mem).memLp_grad 0).const_mul 2).sub
            (RankOneModel.memLp_mul_cont M.dlogq_cont τ.memLp_sqrt))
          ((RankOneModel.memLp_mul_cont M.dφ_cont τ.memLp_sqrt).const_mul _) k
      _ = _ := by
        rw [fourierCoeff_sub' ((memLp_coord (isWeakGradient_weakGradient τ.sqrt_mem).memLp_grad 0).const_mul 2)
          (RankOneModel.memLp_mul_cont M.dlogq_cont τ.memLp_sqrt), fourierCoeff_const_mul,
          fourierCoeff_weakGradient (isWeakGradient_weakGradient τ.sqrt_mem) 0 k, fourierCoeff_const_mul]
        simp
  simp_rw [hid]
  simpa only [Function.comp_apply, Complex.ofReal_mul] using
    (((hu.const_mul _).const_mul _).sub hl).add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp (hm.const_mul eta)).mul hd)

/-- Full actual scalar-sublevel compactness, retaining moments, the genuine gap
limit, and genuine dissipation lower semicontinuity on the same subsequence. -/
theorem polynomial_scalar_sublevel_compactness (h Mq : ℝ) (hMq : 0 ≤ Mq)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h))
    (ρ : ℕ → AbsoluteDensity 1)
    (hG : ∀ n, 0 < scalarGap (canonical_elementary_polynomial_model h) (ρ n))
    (hQ : ∀ n, scalarQuotient (canonical_elementary_polynomial_model h) b (ρ n) ≤ ENNReal.ofReal Mq) :
    ∃ (B : ℝ), 0 ≤ B ∧
      (∀ n, DGPS.Analysis.circleFisherInformation (ρ n) ≤ B ∧ DGPS.Analysis.circleEntropy (ρ n) ≤ B) ∧
      ∃ (φ : ℕ → ℕ) (ρL : AbsoluteDensity 1) (η : ℕ → ℝ) (R : ℝ),
        StrictMono φ ∧ Tendsto η atTop (𝓝 0) ∧
        (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n)).sqrt x - ρL.sqrt x| ≤ η n) ∧
        (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n)).sqrt x| ≤ R) ∧
        (∀ x, |ρL.sqrt x| ≤ R) ∧
        Tendsto (fun n => DGPS.Analysis.circleEntropy (ρ (φ n))) atTop (𝓝 (DGPS.Analysis.circleEntropy ρL)) ∧
        (∀ g : Torus 1 →ᵇ ℝ, Tendsto (fun n => ∫ x, g x ∂(densityMeasure (ρ (φ n)) : Measure (Torus 1))) atTop
          (𝓝 (∫ x, g x ∂(densityMeasure ρL : Measure (Torus 1))))) ∧
        Tendsto (fun n => (scalarGap (canonical_elementary_polynomial_model h) (ρ (φ n)) : ℝ≥0∞)) atTop
          (𝓝 (scalarGap (canonical_elementary_polynomial_model h) ρL : ℝ≥0∞)) ∧
        scalarDissipation (canonical_elementary_polynomial_model h) b ρL ≤
          liminf (fun n => scalarDissipation (canonical_elementary_polynomial_model h) b (ρ (φ n))) atTop := by
  obtain ⟨B, hB, hBn, φ, ρL, η, R, hφ, hη, hae, hub, hRL, hH, _⟩ :=
    polynomial_scalar_boundedQuotient_compactness h Mq hMq b ρ hG hQ
  exact ⟨B, hB, hBn, φ, ρL, η, R, hφ, hη, hae, hub, hRL, hH,
    (fun g => moments_uniform _ _ hη hae R hub g g.continuous),
    polynomial_scalarGap_tendsto h b _ _ hη hae R hub,
    polynomial_scalarDissipation_le_liminf h b _ _ hη hae R hub⟩

end DGPS.Examples.PolynomialSpecies
