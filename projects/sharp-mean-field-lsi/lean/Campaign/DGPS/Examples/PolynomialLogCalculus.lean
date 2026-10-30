import DGPS.Examples.PolynomialSmooth

/-! Physical real-variable derivative identities for the actual polynomial
root/score system. These are calculus consequences of the proved classical
system, not an optimizer equation imposed as a final hypothesis. -/

noncomputable section
open MeasureTheory
open DGPS.PositiveRankOne DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Examples.PolynomialSpecies

/-- First derivative of the actual relative logarithmic root profile. -/
theorem polynomial_log_profile_hasDerivAt (h : ℝ)
    {v S : Torus 1 → ℝ} (hvpos : ∀ x, 0 < v x)
    (hvd : ∀ t : ℝ, HasDerivAt (fun s => v (pt s))
      ((S (pt t) + v (pt t) * (polynomialRankOne h).dlogq (pt t)) / 2) t) (t : ℝ) :
    HasDerivAt (fun s => Real.log (v (pt s) ^ 2) - Real.log ((polynomialRankOne h).q (pt s)))
      (S (pt t) / v (pt t)) t := by
  have hl := hasDerivAt_smooth_one (polynomialRankOne h).log_smooth t
  have hd := ((hvd t).pow 2).log (pow_ne_zero 2 (hvpos (pt t)).ne')
  have he := hd.sub hl
  convert he using 1
  change S (pt t) / v (pt t) =
    (2 * v (pt t) ^ (2 - 1) * ((S (pt t) + v (pt t) * (polynomialRankOne h).dlogq (pt t)) / 2)) /
      v (pt t) ^ 2 - (polynomialRankOne h).dlogq (pt t)
  norm_num
  field_simp [(hvpos (pt t)).ne']
  ring

/-- The true second-derivative log equation includes the actual nonlocal
correction and mass multiplier. No feature eigenfunction substitution. -/
theorem polynomial_log_profile_second_hasDerivAt (h r : ℝ) (ρ : AbsoluteDensity 1)
    {v S : Torus 1 → ℝ} (hvpos : ∀ x, 0 < v x)
    (hvd : ∀ t : ℝ, HasDerivAt (fun s => v (pt s))
      ((S (pt t) + v (pt t) * (polynomialRankOne h).dlogq (pt t)) / 2) t)
    (hSd : ∀ t : ℝ, HasDerivAt (fun s => S (pt s))
      (-(S (pt t) * (polynomialRankOne h).dlogq (pt t)) / 2 +
        v (pt t) * polynomialEulerCorrection h r ρ (pt t) / 2 -
          r * (v (pt t) * (Real.log (v (pt t) ^ 2) - Real.log ((polynomialRankOne h).q (pt t)))) -
            polynomialEulerMultiplier h r ρ * v (pt t) / 2) t) (t : ℝ) :
    HasDerivAt (fun s => S (pt s) / v (pt s))
      (-(polynomialRankOne h).dlogq (pt t) * (S (pt t) / v (pt t)) -
        (S (pt t) / v (pt t)) ^ 2 / 2 -
          r * (Real.log (v (pt t) ^ 2) - Real.log ((polynomialRankOne h).q (pt t))) +
            polynomialEulerCorrection h r ρ (pt t) / 2 - polynomialEulerMultiplier h r ρ / 2) t := by
  have he := (hSd t).div (hvd t) (hvpos (pt t)).ne'
  convert he using 1
  field_simp [(hvpos (pt t)).ne']
  ring

/-- Differentiate the actual logarithmic equation once more in physical
space. Only actual spatial data derivatives occur. -/
theorem polynomial_log_profile_third_hasDerivAt (h r : ℝ) (ρ : AbsoluteDensity 1)
    {v S : Torus 1 → ℝ} (hvpos : ∀ x, 0 < v x)
    (hvd : ∀ t : ℝ, HasDerivAt (fun s => v (pt s))
      ((S (pt t) + v (pt t) * (polynomialRankOne h).dlogq (pt t)) / 2) t)
    (hSd : ∀ t : ℝ, HasDerivAt (fun s => S (pt s))
      (-(S (pt t) * (polynomialRankOne h).dlogq (pt t)) / 2 +
        v (pt t) * polynomialEulerCorrection h r ρ (pt t) / 2 -
          r * (v (pt t) * (Real.log (v (pt t) ^ 2) - Real.log ((polynomialRankOne h).q (pt t)))) -
            polynomialEulerMultiplier h r ρ * v (pt t) / 2) t) (t : ℝ) :
    let f1 := S (pt t) / v (pt t)
    let f2 := -(polynomialRankOne h).dlogq (pt t) * f1 - f1 ^ 2 / 2 -
      r * (Real.log (v (pt t) ^ 2) - Real.log ((polynomialRankOne h).q (pt t))) +
        polynomialEulerCorrection h r ρ (pt t) / 2 - polynomialEulerMultiplier h r ρ / 2
    HasDerivAt (fun s => -(polynomialRankOne h).dlogq (pt s) * (S (pt s) / v (pt s)) -
        (S (pt s) / v (pt s)) ^ 2 / 2 -
          r * (Real.log (v (pt s) ^ 2) - Real.log ((polynomialRankOne h).q (pt s))) +
            polynomialEulerCorrection h r ρ (pt s) / 2 - polynomialEulerMultiplier h r ρ / 2)
      (-coordPartial 0 (polynomialRankOne h).dlogq (pt t) * f1 -
        (polynomialRankOne h).dlogq (pt t) * f2 - f1 * f2 - r * f1 +
          coordPartial 0 (polynomialEulerCorrection h r ρ) (pt t) / 2) t := by
  let M := polynomialRankOne h
  let f1 := S (pt t) / v (pt t)
  let f2 := -M.dlogq (pt t) * f1 - f1 ^ 2 / 2 -
    r * (Real.log (v (pt t) ^ 2) - Real.log (M.q (pt t))) +
      polynomialEulerCorrection h r ρ (pt t) / 2 - polynomialEulerMultiplier h r ρ / 2
  have h1 := polynomial_log_profile_hasDerivAt h hvpos hvd t
  have h2 := polynomial_log_profile_second_hasDerivAt h r ρ hvpos hvd hSd t
  have hs : HasDerivAt (fun s => M.dlogq (pt s))
      (coordPartial 0 M.dlogq (pt t)) t :=
    hasDerivAt_smooth_one (M.log_smooth.isSmoothPeriodic_coordPartial 0) t
  have hX := hasDerivAt_smooth_one (isSmooth_polynomialEulerCorrection h r ρ) t
  have he := (((((hs.neg.mul h2).sub ((h2.pow 2).div_const 2)).sub
    (h1.const_mul r)).add (hX.div_const 2)).sub_const (polynomialEulerMultiplier h r ρ / 2))
  convert he using 1 <;> simp only [Pi.neg_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply]
  all_goals dsimp only [M, f1, f2]
  all_goals first | (funext s; ring) | ring

end DGPS.Examples.PolynomialSpecies
