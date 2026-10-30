import DGPS.Examples.ThreeSpeciesCircle.Model
import DGPS.Examples.SixthOrderCentering
import DGPS.Frontier.STR029.T62

/-! The canonical reference moments from the existing rigorous Bessel-series engine.
The angular and real-period definitions are identified before any bound is imported. -/

noncomputable section
open MeasureTheory Filter Set Real
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The two existing Bessel definitions are the same normalized periodic integral. -/
theorem ordinaryBessel_eq_angularBessel (n : ℕ) (h : ℝ) :
    besselI n h = DGPS.Circle.BesselMoments.besselI n h := by
  have hmode (k : ℕ) (θ : AngCircle) :
      DGPS.Circle.BesselMoments.angMode k θ = Real.cos ((k : ℝ) * angSec θ) := by
    calc
      _ = DGPS.Circle.BesselMoments.angMode k ((angSec θ : ℝ) : AngCircle) := by
        rw [coe_angSec_STR02962]
      _ = _ := DGPS.Circle.BesselMoments.angMode_coe k (angSec θ)
  symm
  unfold DGPS.Circle.BesselMoments.besselI besselI
  have he : (fun θ : AngCircle => Real.exp (h * DGPS.Circle.BesselMoments.angCos θ) *
      DGPS.Circle.BesselMoments.angMode n θ) =
      fun θ => (fun t : ℝ => Real.exp (h * Real.cos t) * Real.cos ((n : ℝ) * t)) (angSec θ) := by
    funext θ
    simp only [DGPS.Circle.BesselMoments.angCos, hmode, Nat.cast_one, one_mul]
  rw [he, integral_angSec_STR02962 (fun t => Real.exp (h * Real.cos t) * Real.cos ((n : ℝ) * t))]
  simp only [one_div]

private theorem reference_quotient_error (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) :
    |DGPS.Circle.BesselMoments.besselI1Over h / DGPS.Circle.BesselMoments.besselI 0 h -
      DGPS.Examples.SixthOrderCentering.quotientPoly (h ^ 2 / 4)| ≤ h ^ 8 / 64 := by
  have hhabs : |h| ≤ 1 := by rwa [abs_of_pos hh]
  obtain ⟨e0, e0'⟩ := DGPS.Examples.SixthOrderCentering.besselI_zero_expand h hhabs
  obtain ⟨e1, e1'⟩ := DGPS.Examples.SixthOrderCentering.besselI1Over_expand h hhabs
  have h2 : h ^ 2 ≤ 1 := by nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hh1)]
  have ha0 : 0 ≤ h ^ 2 / 4 := by positivity
  have ha : h ^ 2 / 4 ≤ 1 / 4 := by linarith
  have he := (DGPS.Examples.SixthOrderCentering.quotient_core (h ^ 2 / 4)
    (DGPS.Circle.BesselMoments.besselI 0 h) (DGPS.Circle.BesselMoments.besselI1Over h)
    ha0 ha e0 e0' e1 e1').2
  convert he using 1 <;> ring

/-- Genuine estimates for the actual reference centering and sixth-harmonic moment.
The explicit bounds hold on the fixed positive interval h≤1. -/
theorem ordinaryReference_moment_estimates (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) :
    |referenceMean h - (h / 2 - h ^ 3 / 16)| ≤ h ^ 5 ∧
      |besselI 2 h / besselI 0 h - h ^ 2 / 8| ≤ h ^ 4 := by
  let R := DGPS.Circle.BesselMoments.besselI1Over h / DGPS.Circle.BesselMoments.besselI 0 h
  let Q := DGPS.Examples.SixthOrderCentering.quotientPoly (h ^ 2 / 4)
  have hR : |R - Q| ≤ h ^ 8 / 64 := reference_quotient_error h hh hh1
  have hg : referenceMean h = h * R := by
    unfold referenceMean
    rw [ordinaryBessel_eq_angularBessel, ordinaryBessel_eq_angularBessel,
      DGPS.Examples.SixthOrderCentering.besselI_one_eq_mul]
    dsimp [R]
    ring
  have hI : besselI 2 h / besselI 0 h = 1 - 2 * R := by
    rw [ordinaryBessel_eq_angularBessel, ordinaryBessel_eq_angularBessel]
    exact (DGPS.Examples.SixthOrderCentering.quotient_ratio_identities h
      (DGPS.Circle.BesselMoments.besselI_zero_pos h)).1
  have p75 : h ^ 7 ≤ h ^ 5 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
  have p95 : h ^ 9 ≤ h ^ 5 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
  have p64 : h ^ 6 ≤ h ^ 4 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
  have p84 : h ^ 8 ≤ h ^ 4 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
  constructor
  · have he : referenceMean h - (h / 2 - h ^ 3 / 16) =
        h * (R - Q) + (h ^ 5 / 96 - 11 * h ^ 7 / 6144) := by
      rw [hg]
      dsimp [Q, DGPS.Examples.SixthOrderCentering.quotientPoly]
      ring
    have herror : |h * (R - Q)| ≤ h ^ 9 / 64 := by
      rw [abs_mul, abs_of_pos hh]
      nlinarith [mul_le_mul_of_nonneg_left hR hh.le]
    have htail : |h ^ 5 / 96 - 11 * h ^ 7 / 6144| ≤ h ^ 5 / 96 + 11 * h ^ 7 / 6144 := by
      have ht := abs_sub (h ^ 5 / 96) (11 * h ^ 7 / 6144)
      rw [abs_of_nonneg (by positivity : 0 ≤ h ^ 5 / 96),
        abs_of_nonneg (by positivity : 0 ≤ 11 * h ^ 7 / 6144)] at ht
      exact ht
    rw [he]
    have ht := abs_add_le (h * (R - Q)) (h ^ 5 / 96 - 11 * h ^ 7 / 6144)
    nlinarith
  · have he : besselI 2 h / besselI 0 h - h ^ 2 / 8 =
        -2 * (R - Q) - h ^ 4 / 48 + 11 * h ^ 6 / 3072 := by
      rw [hI]
      dsimp [Q, DGPS.Examples.SixthOrderCentering.quotientPoly]
      ring
    have he0 : |-2 * (R - Q)| ≤ h ^ 8 / 32 := by
      rw [abs_mul]
      norm_num
      linarith
    have ht1 := abs_sub (-2 * (R - Q)) (h ^ 4 / 48)
    have ht2 := abs_add_le (-2 * (R - Q) - h ^ 4 / 48) (11 * h ^ 6 / 3072)
    rw [abs_of_nonneg (by positivity : 0 ≤ h ^ 4 / 48)] at ht1
    rw [abs_of_nonneg (by positivity : 0 ≤ 11 * h ^ 6 / 3072)] at ht2
    rw [he]
    nlinarith

end DGPS.Examples.ThreeSpeciesCircle
