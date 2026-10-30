import DGPS.Examples.PolynomialWeakEuler
import DGPS.Examples.PolynomialNearOriginMoments
import DGPS.Examples.PolynomialGeneratorDerivativeBounds
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryBootstrap

/-! Actual nonlinear Euler corrections become uniformly small along original
root-near-Haar sequences. All moment and spatial coefficient controls are
proved actual-model inputs; no correction-smallness or C2 premise is supplied. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.PositiveRankOne DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Examples.PolynomialSpecies

theorem polynomial_eulerCorrection_derivative (h r : ℝ) (ρ : AbsoluteDensity 1) (x : Torus 1) :
    let M := polynomialRankOne h
    let m := ∫ y, M.φ y ∂(densityMeasure ρ : Measure (Torus 1))
    let a := ∫ y, M.Aq y ∂(densityMeasure ρ : Measure (Torus 1))
    let j := ∫ y, M.dφ y ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))
    coordPartial 0 (polynomialEulerCorrection h r ρ) x =
      (2 * eta * (a + eta * m * j - r * m)) * M.dφ x +
        (2 * eta * m) * coordPartial 0 M.Aq x +
          (eta ^ 2 * m ^ 2) * (2 * M.dφ x * coordPartial 0 M.dφ x) := by
  let M := polynomialRankOne h
  let m := ∫ y, M.φ y ∂(densityMeasure ρ : Measure (Torus 1))
  let a := ∫ y, M.Aq y ∂(densityMeasure ρ : Measure (Torus 1))
  let j := ∫ y, M.dφ y ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))
  let c1 := 2 * eta * (a + eta * m * j - r * m)
  let c2 := 2 * eta * m
  let c3 := eta ^ 2 * m ^ 2
  have hA : IsSmoothPeriodic M.Aq :=
    (M.dφ_smooth.isSmoothPeriodic_coordPartial 0).neg.sub
      ((M.log_smooth.isSmoothPeriodic_coordPartial 0).mul M.dφ_smooth)
  have hp : coordPartial 0 (fun y => M.dφ y ^ 2) x = 2 * M.dφ x * coordPartial 0 M.dφ x := by
    have he : (fun y => M.dφ y ^ 2) = fun y => M.dφ y * M.dφ y := by funext y; ring
    rw [he, coordPartial_mul M.dφ_smooth M.dφ_smooth]
    ring
  have hpair : (fun y => c1 * M.φ y + c2 * M.Aq y) =
      fun y => c1 * M.φ y + c2 * M.Aq y + 0 := by funext y; ring
  have he : polynomialEulerCorrection h r ρ = fun y =>
      1 * (c1 * M.φ y + c2 * M.Aq y) + c3 * (M.dφ y ^ 2) + 0 := by
    funext y
    dsimp only [polynomialEulerCorrection, c1, c2, c3, M, m, a, j]
    ring
  have hs : IsSmoothPeriodic (fun y => c1 * M.φ y + c2 * M.Aq y) :=
    (contDiff_const.mul M.φ_smooth).add (contDiff_const.mul hA)
  have hsq : IsSmoothPeriodic (fun y => M.dφ y ^ 2) := M.dφ_smooth.pow 2
  rw [he, RankOneModel.coordPartial_lin hs hsq,
    hpair, RankOneModel.coordPartial_lin M.φ_smooth hA, hp]
  change 1 * (c1 * M.dφ x + c2 * coordPartial 0 M.Aq x) +
    c3 * (2 * M.dφ x * coordPartial 0 M.dφ x) = _
  ring

/-- Actual feature feedbacks, their first physical spatial derivative, and
the mass multiplier are uniformly small. The original absolute-H1 competitors
may vanish; AE root nearness is factual sequence data, not a regularity input. -/
theorem polynomial_varying_euler_corrections_small (h : ℕ → ℝ)
    (hh : Tendsto h atTop (𝓝 0)) (ρ : ℕ → AbsoluteDensity 1)
    (θ : ℕ → ℝ) (hθ : Tendsto θ atTop (𝓝 0))
    (hroot : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - 1| ≤ θ n)
    (r : ℕ → ℝ) (R : ℝ) (hr : ∀ᶠ n in atTop, |r n| ≤ R) :
    USmall (fun n t => polynomialEulerCorrection (h n) (r n) (ρ n) (pt t)) ∧
      USmall (fun n t => coordPartial 0 (polynomialEulerCorrection (h n) (r n) (ρ n)) (pt t)) ∧
        USmall (fun n _ => polynomialEulerMultiplier (h n) (r n) (ρ n)) := by
  let M := fun n => polynomialRankOne (h n)
  let m := fun n => ∫ x, (M n).φ x ∂(densityMeasure (ρ n) : Measure (Torus 1))
  let a := fun n => ∫ x, (M n).Aq x ∂(densityMeasure (ρ n) : Measure (Torus 1))
  let j := fun n => ∫ x, (M n).dφ x ^ 2 ∂(densityMeasure (ρ n) : Measure (Torus 1))
  obtain ⟨C, δm, ε, hC, hδm, hε, hmom⟩ := polynomial_near_origin_moment_bound
  have habs : Tendsto (fun n => |h n|) atTop (𝓝 0) := by simpa using hh.abs
  have hθabs : Tendsto (fun n => |θ n|) atTop (𝓝 0) := by simpa using hθ.abs
  have hbound : ∀ᶠ n in atTop, |m n| + |a n| ≤ C * (|θ n| + ε (h n)) := by
    filter_upwards [habs.eventually (ge_mem_nhds hδm),
      hθabs.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn htn
    exact hmom (h n) hn (ρ n) |θ n| (abs_nonneg _) htn
      ((hroot n).mono fun x hx => hx.trans (le_abs_self _))
  have hlim : Tendsto (fun n => C * (|θ n| + ε (h n))) atTop (𝓝 0) := by
    simpa using (hθabs.add (hε.comp hh)).const_mul C
  have hm : Tendsto m atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hbound] with n hn
    exact (le_add_of_nonneg_right (abs_nonneg (a n))).trans hn
  have ha : Tendsto a atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hbound] with n hn
    exact (le_add_of_nonneg_left (abs_nonneg (m n))).trans hn
  obtain ⟨K, δK, hK, hδK, _, hdata⟩ := polynomial_uniform_data_bound
  have hbase : ∀ᶠ n in atTop, ∀ x : Torus 1,
      |(M n).φ x| ≤ K ∧ |(M n).Aq x| ≤ K ∧ |(M n).dφ x| ≤ K := by
    filter_upwards [habs.eventually (ge_mem_nhds hδK)] with n hn x
    have he := hdata (h n) hn x
    exact ⟨he.1, he.2.1, he.2.2.2.2⟩
  have hj : ∀ᶠ n in atTop, |j n| ≤ K ^ 2 := by
    filter_upwards [hbase] with n hn
    have hb : ∀ x, ‖(M n).dφ x ^ 2‖ ≤ K ^ 2 := by
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hn x).2.2 2
    have he := norm_integral_le_of_norm_le_const (μ := (densityMeasure (ρ n) : Measure (Torus 1)))
      (f := fun x => (M n).dφ x ^ 2) (C := K ^ 2) (Eventually.of_forall hb)
    simpa only [Real.norm_eq_abs, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using he
  have hm0 : USmall (fun n (_ : ℝ) => m n) := USmall.of_seq hm
  have ha0 : USmall (fun n (_ : ℝ) => a n) := USmall.of_seq ha
  have hrb : ∀ᶠ n in atTop, ∀ _ : ℝ, |r n| ≤ R := hr.mono fun n hn _ => hn
  have hjb : ∀ᶠ n in atTop, ∀ _ : ℝ, |j n| ≤ K ^ 2 := hj.mono fun n hn _ => hn
  have hm2 : USmall (fun n (_ : ℝ) => m n ^ 2) :=
    USmall.congr (fun n t => by ring) (hm0.mul_bdd 1 hm0.bdd)
  let c1 := fun n => 2 * eta * (a n + eta * m n * j n - r n * m n)
  let c2 := fun n => 2 * eta * m n
  let c3 := fun n => eta ^ 2 * m n ^ 2
  have hc1 : USmall (fun n (_ : ℝ) => c1 n) := by
    have he := ((ha0.add ((hm0.mul_bdd (K ^ 2) hjb).const_mul eta)).sub (hm0.mul_bdd R hrb)).const_mul (2 * eta)
    exact USmall.congr (fun n t => by dsimp only [c1]; ring) he
  have hc2 : USmall (fun n (_ : ℝ) => c2 n) := hm0.const_mul (2 * eta)
  have hc3 : USmall (fun n (_ : ℝ) => c3 n) := hm2.const_mul (eta ^ 2)
  have hφb : ∀ᶠ n in atTop, ∀ t : ℝ, |(M n).φ (pt t)| ≤ K :=
    hbase.mono fun n hn t => (hn (pt t)).1
  have hAb : ∀ᶠ n in atTop, ∀ t : ℝ, |(M n).Aq (pt t)| ≤ K :=
    hbase.mono fun n hn t => (hn (pt t)).2.1
  have hdb : ∀ᶠ n in atTop, ∀ t : ℝ, |(M n).dφ (pt t)| ≤ K :=
    hbase.mono fun n hn t => (hn (pt t)).2.2
  have hdsq : ∀ᶠ n in atTop, ∀ t : ℝ, |(M n).dφ (pt t) ^ 2| ≤ K ^ 2 := by
    filter_upwards [hdb] with n hn t
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hn t) 2
  have hXi : USmall (fun n t => polynomialEulerCorrection (h n) (r n) (ρ n) (pt t)) := by
    apply USmall.congr (fun n t => ?_) (((hc1.mul_bdd K hφb).add (hc2.mul_bdd K hAb)).add
      (hc3.mul_bdd (K ^ 2) hdsq))
    rfl
  obtain ⟨KG, δG, hKG, hδG, _, hgen⟩ := polynomial_uniform_generator_derivative_bound
  obtain ⟨KF, hKF, hfeature⟩ := polynomial_uniform_feature_derivative_bound
  have hAg : ∀ᶠ n in atTop, ∀ t : ℝ, |coordPartial 0 (M n).Aq (pt t)| ≤ KG := by
    filter_upwards [habs.eventually (ge_mem_nhds hδG)] with n hn t
    exact hgen (h n) hn (pt t)
  have hf2 : ∀ᶠ n in atTop, ∀ t : ℝ, |coordPartial 0 (M n).dφ (pt t)| ≤ KF := by
    filter_upwards [habs.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn t
    have he := hfeature (h n) hn (pt t)
    nlinarith [abs_nonneg ((M n).dφ (pt t)),
      abs_nonneg (coordPartial 0 (fun x => coordPartial 0 (M n).dφ x) (pt t))]
  have hprod : ∀ᶠ n in atTop, ∀ t : ℝ,
      |2 * (M n).dφ (pt t) * coordPartial 0 (M n).dφ (pt t)| ≤ 2 * K * KF := by
    filter_upwards [hdb, hf2] with n hn hf t
    rw [abs_mul, abs_mul, abs_two]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hn t) two_pos.le) (hf t)
      (abs_nonneg _) (by positivity)
  have hXid : USmall (fun n t => coordPartial 0 (polynomialEulerCorrection (h n) (r n) (ρ n)) (pt t)) := by
    apply USmall.congr (fun n t => ?_) (((hc1.mul_bdd K hdb).add (hc2.mul_bdd KG hAg)).add
      (hc3.mul_bdd (2 * K * KF) hprod))
    exact polynomial_eulerCorrection_derivative (h n) (r n) (ρ n) (pt t)
  have hLambda : USmall (fun n (_ : ℝ) => polynomialEulerMultiplier (h n) (r n) (ρ n)) := by
    have he := (((hm0.mul_bdd 1 ha0.bdd).const_mul (2 * eta)).sub
      ((hm2.mul_bdd R hrb).const_mul eta)).add ((hm2.mul_bdd (K ^ 2) hjb).const_mul (2 * eta ^ 2))
    exact USmall.congr (fun n t => by dsimp only [polynomialEulerMultiplier, M, m, a, j]; ring) he
  exact ⟨hXi, hXid, hLambda⟩

end DGPS.Examples.PolynomialSpecies
