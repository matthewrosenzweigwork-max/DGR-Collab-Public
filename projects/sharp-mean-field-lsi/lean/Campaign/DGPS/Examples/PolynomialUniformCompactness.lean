import DGPS.Examples.PolynomialUniformData
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryOptimizers
import DGPS.Variational.SpeciesInclusion

/-! Genuine scalar-sublevel information control uniformly as the actual field
tends to zero. The constants come from actual moving-reference data, not an
assumed uniform information or compactness estimate. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.PositiveRankOne DGPS.Examples.PolynomialExactGap
open DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Examples.PolynomialSpecies

private theorem moment_le (ν : ProbabilityMeasure (Torus 1)) (f : Torus 1 → ℝ)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) : |∫ x, f x ∂(ν : Measure (Torus 1))| ≤ K := by
  have hb := norm_integral_le_of_norm_le_const (μ := (ν : Measure (Torus 1))) (f := f) (C := K)
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hK x)
  simpa only [Real.norm_eq_abs, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using hb

private theorem fisher_comparison (M : RankOneModel) {K : ℝ}
    (hK : ∀ x, |M.dlogq x| ≤ K) (ρ : AbsoluteDensity 1) :
    DGPS.Analysis.circleFisherInformation ρ ≤
      2 * (ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) M.ref).toReal + 2 * K ^ 2 := by
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  have hi := (M.dissipation_integral hw 0).1
  have hg := (memLp_coord hw.memLp_grad 0).integrable_sq
  have hd := ρ.integrable_density.const_mul (2 * K ^ 2)
  have hpt (x : Torus 1) : 4 * (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ≤
      2 * (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x) ^ 2 +
        2 * K ^ 2 * ρ.density x := by
    have hs := pow_le_pow_left₀ (abs_nonneg _) (hK x) 2
    rw [sq_abs] at hs
    have ht := mul_le_mul_of_nonneg_left hs (sq_nonneg (ρ.sqrt x))
    change 4 * (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ≤
      2 * (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x) ^ 2 +
        2 * K ^ 2 * ρ.sqrt x ^ 2
    nlinarith [sq_nonneg (weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x)]
  have hb := integral_mono (hg.const_mul 4) ((hi.const_mul 2).add hd) hpt
  change (∫ x, 4 * (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ∂haar 1) ≤
    ∫ x, 2 * (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x) ^ 2 +
      2 * K ^ 2 * ρ.density x ∂haar 1 at hb
  have hm : (∫ x, 2 * K ^ 2 * ρ.density x ∂haar 1) = 2 * K ^ 2 := by
    rw [integral_const_mul, ρ.integral_density, mul_one]
  rw [integral_add (hi.const_mul 2) hd, hm] at hb
  rw [M.fisher_eq, ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  have he : DGPS.Analysis.circleFisherInformation ρ =
      ∫ x, 4 * (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ∂haar 1 := by
    unfold DGPS.Analysis.circleFisherInformation
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change 4 * ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 =
        4 * (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2
      rw [RankOneModel.norm_sq_tangent]
  rw [he]
  simpa only [integral_const_mul] using hb

/-- The interval and information/entropy constant precede the actual field,
drift and every full-domain competitor. This is genuine uniform control near
zero field, derived from the original scalar quotient. -/
theorem polynomial_uniform_scalar_information (Mq : ℝ) (hMq : 0 ≤ Mq) :
    ∃ δ B : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 ≤ B ∧ ∀ h : ℝ, |h| ≤ δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h), ∀ ρ : AbsoluteDensity 1,
        0 < scalarGap (canonical_elementary_polynomial_model h) ρ →
        scalarQuotient (canonical_elementary_polynomial_model h) b ρ ≤ ENNReal.ofReal Mq →
        DGPS.Analysis.circleFisherInformation ρ ≤ B ∧ DGPS.Analysis.circleEntropy ρ ≤ B := by
  obtain ⟨K, δ, hK, hδ, hδ1, hdata⟩ := polynomial_uniform_data_bound
  have hη := eta_pos
  let C := 4 * Mq * (K + eta / 2 * K ^ 2) + 4 * eta * K ^ 2 + 2 * K ^ 2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let Hmax := 2 * (6 * ((1 + (C + 1)) / (12 * (4 * Mq) + 1) - 1 + Real.log (12 * (4 * Mq) + 1)))
  let B := max (4 * Mq * Hmax + C) (max Hmax 0)
  refine ⟨δ, B, hδ, hδ1, (le_max_right _ _).trans' (le_max_right _ _), fun h hh b ρ hG hQ => ?_⟩
  let M := polynomialRankOne h
  have hd := hdata h hh
  have hm := moment_le (densityMeasure ρ) M.φ (fun x => (hd x).1)
  have ha := moment_le (densityMeasure ρ) M.Aq (fun x => (hd x).2.1)
  have hl := moment_le (densityMeasure ρ) (fun x => Real.log (M.q x)) (fun x => (hd x).2.2.1)
  have hid := positive_rank_one_scalar_case M (polynomialRankOneDrift h b) ρ
  rw [polynomialRankOne_speciesGap, polynomialRankOne_speciesDissipation,
    speciesGap_single, speciesDissipation_single] at hid
  obtain ⟨hgap, hIfin, hDfin, hD⟩ := hid
  have hsq : (∫ x, M.φ x ∂(densityMeasure ρ : Measure (Torus 1))) ^ 2 ≤ K ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hm 2
  have hp : |(∫ x, M.φ x ∂(densityMeasure ρ : Measure (Torus 1))) *
      (∫ x, M.Aq x ∂(densityMeasure ρ : Measure (Torus 1)))| ≤ K ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hm ha (abs_nonneg _) hK.le
  have hHaar := M.entropy_ref_eq (densityMeasure ρ) (absoluteDensity_entropy_finite ρ).2.2.1
  rw [← circleEntropy_eq_relativeEntropy] at hHaar
  have hgapBound : (scalarGap (canonical_elementary_polynomial_model h) ρ : ℝ) ≤
      DGPS.Analysis.circleEntropy ρ + K + eta / 2 * K ^ 2 := by
    rw [hgap, hHaar]
    change DGPS.Analysis.circleEntropy ρ - _ + eta / 2 * _ ≤ _
    linarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ eta / 2 by positivity), (abs_le.mp hl).1]
  have hDq : (scalarDissipation (canonical_elementary_polynomial_model h) b ρ).toReal ≤
      2 * Mq * (scalarGap (canonical_elementary_polynomial_model h) ρ : ℝ) := by
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hQ
    unfold scalarQuotient at hr
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.coe_toReal, ENNReal.toReal_ofReal hMq] at hr
    have hGr : (0 : ℝ) < (scalarGap (canonical_elementary_polynomial_model h) ρ : ℝ) := by exact_mod_cast hG
    have ht := (div_le_iff₀ (by positivity : 0 < 2 * (scalarGap (canonical_elementary_polynomial_model h) ρ : ℝ))).1 hr
    nlinarith
  have hIrel : (ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) M.ref).toReal ≤
      (scalarDissipation (canonical_elementary_polynomial_model h) b ρ).toReal + 2 * eta * K ^ 2 := by
    have hJ : 0 ≤ ∫ x, M.dφ x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1)) := integral_nonneg fun _ => sq_nonneg _
    have ht := mul_le_mul_of_nonneg_left (abs_le.mp hp).1 (show 0 ≤ 2 * eta by positivity)
    have hn := mul_nonneg (mul_nonneg (sq_nonneg eta)
      (sq_nonneg (∫ x, M.φ x ∂(densityMeasure ρ : Measure (Torus 1))))) hJ
    change _ = _ + 2 * eta * _ * _ + eta ^ 2 * _ * _ at hD
    nlinarith
  have hIH : DGPS.Analysis.circleFisherInformation ρ ≤ 4 * Mq * DGPS.Analysis.circleEntropy ρ + C := by
    have hf := fisher_comparison M (fun x => (hd x).2.2.2.1) ρ
    have ht := mul_le_mul_of_nonneg_left hgapBound (show 0 ≤ 2 * Mq by positivity)
    dsimp only [C]
    nlinarith
  have hH0 := circleEntropy_nonneg ρ
  have hI0 := circleFisherInformation_nonneg ρ
  have hHlog : DGPS.Analysis.circleEntropy ρ ≤
      6 * Real.log (1 + 4 * Mq * DGPS.Analysis.circleEntropy ρ + (C + 1)) := by
    have ht := Real.log_le_log (by positivity : 0 < 2 + DGPS.Analysis.circleFisherInformation ρ)
      (show 2 + DGPS.Analysis.circleFisherInformation ρ ≤
        1 + 4 * Mq * DGPS.Analysis.circleEntropy ρ + (C + 1) by linarith)
    linarith [circleEntropy_le_log_information ρ]
  have hHmax : DGPS.Analysis.circleEntropy ρ ≤ Hmax :=
    solve_entropy_log (by positivity) (by positivity) hH0 hHlog
  refine ⟨?_, hHmax.trans ((le_max_left _ _).trans (le_max_right _ _))⟩
  exact (hIH.trans (add_le_add
    (mul_le_mul_of_nonneg_left hHmax (show 0 ≤ 4 * Mq by positivity)) le_rfl)).trans (le_max_left _ _)

/-- A field sequence tending to zero and bounded actual scalar quotients yield
genuine original-root compactness. No uniform information bound or positive
limiting gap is a premise. Finite prefixes are removed by an explicit tail. -/
theorem polynomial_varying_scalar_root_compactness (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (b : ∀ n, AbsoluteDrift (canonical_elementary_polynomial_model (h n)))
    (Mq : ℝ) (hMq : 0 ≤ Mq) (ρ : ℕ → AbsoluteDensity 1)
    (hG : ∀ n, 0 < scalarGap (canonical_elementary_polynomial_model (h n)) (ρ n))
    (hQ : ∀ n, scalarQuotient (canonical_elementary_polynomial_model (h n)) (b n) (ρ n) ≤ ENNReal.ofReal Mq) :
    ∃ (φ : ℕ → ℕ) (ρL : AbsoluteDensity 1) (η : ℕ → ℝ) (R : ℝ),
      StrictMono φ ∧ Tendsto η atTop (𝓝 0) ∧
      (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n)).sqrt x - ρL.sqrt x| ≤ η n) ∧
      (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n)).sqrt x| ≤ R) ∧
      (∀ x, |ρL.sqrt x| ≤ R) ∧
      Tendsto (fun n => DGPS.Analysis.circleEntropy (ρ (φ n))) atTop (𝓝 (DGPS.Analysis.circleEntropy ρL)) ∧
      ENNReal.ofReal (DGPS.Analysis.circleFisherInformation ρL) ≤
        liminf (fun n => ENNReal.ofReal (DGPS.Analysis.circleFisherInformation (ρ (φ n)))) atTop := by
  obtain ⟨δ, B, hδ, _, hB, hbound⟩ := polynomial_uniform_scalar_information Mq hMq
  have hs : ∀ᶠ n in atTop, |h n| ≤ δ := by
    have ht : Tendsto (fun n => |h n|) atTop (𝓝 0) := by simpa using hh.abs
    exact (ht.eventually (gt_mem_nhds hδ)).mono fun _ hn => hn.le
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hs
  have hinfo (n : ℕ) : DGPS.Analysis.circleFisherInformation (ρ (n + N)) ≤ B :=
    (hbound (h (n + N)) (hN (n + N) (Nat.le_add_left _ _)) (b (n + N)) (ρ (n + N))
      (hG (n + N)) (hQ (n + N))).1
  obtain ⟨φ, ρL, η, R, hφ, hη, hae, hub, hRL, hlsc⟩ :=
    exists_limit_of_bounded_fisher (fun n => ρ (n + N)) hinfo
  have hmono : StrictMono (fun n => φ n + N) := fun i j hij => Nat.add_lt_add_right (hφ hij) N
  have hpt : ∀ᵐ x ∂haar 1, Tendsto (fun n => (ρ (φ n + N)).sqrt x) atTop (𝓝 (ρL.sqrt x)) := by
    filter_upwards [ae_all_iff.mpr hae] with x hx
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by
      simpa only [Real.norm_eq_abs] using hx n) hη
  exact ⟨(fun n => φ n + N), ρL, η, R, hmono, hη, hae, hub, hRL,
    tendsto_circleEntropy hub hpt, hlsc⟩

end DGPS.Examples.PolynomialSpecies
