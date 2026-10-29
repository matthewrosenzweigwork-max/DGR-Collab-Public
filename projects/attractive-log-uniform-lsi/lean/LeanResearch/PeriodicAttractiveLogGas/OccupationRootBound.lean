import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! The supplied numerical occupation-root bound, source 2037–2052.
The balanced-ratio tangent argument and the unbalanced Young argument retain
the exact final error 5 E, including zero rates. -/
noncomputable section
namespace PeriodicAttractiveLogGas.OccupationRootBound

/-- Concavity in the form needed here, proved directly from the square. -/
theorem sqrt_increment_tangent {v E : ℝ} (hE : 0 ≤ E) :
    2 * v * (Real.sqrt (v ^ 2 + E) - v) ≤ E := by
  have hs := Real.sq_sqrt (show 0 ≤ v ^ 2 + E by positivity)
  nlinarith [sq_nonneg (Real.sqrt (v ^ 2 + E) - v)]

theorem sqrt_shift_le {v E : ℝ} (hv : 0 ≤ v) (hE : 0 ≤ E) :
    Real.sqrt (v ^ 2 + E) ≤ v + Real.sqrt E := by
  have hs := Real.sq_sqrt (show 0 ≤ v ^ 2 + E by positivity)
  have he := Real.sq_sqrt hE
  have hse := Real.sqrt_nonneg E
  have hsv := Real.sqrt_nonneg (v ^ 2 + E)
  nlinarith [mul_nonneg hv hse]

/-- The source balanced-ratio estimate, with its sharper 5 E / 4 constant.
The closed ratio conditions also include the both-zero case. -/
theorem balanced_increment_le {u v E : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hE : 0 ≤ E) (hvu : v ≤ 2 * u) (huv : u ≤ 2 * v) :
    u * Real.sqrt (v ^ 2 + E) + v * Real.sqrt (u ^ 2 + E) - 2 * u * v ≤
      5 * E / 4 := by
  by_cases hu0 : u = 0
  · have hv0 : v = 0 := by linarith
    simp only [hu0, hv0, zero_mul, add_zero]
    linarith
  have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have hvp : 0 < v := by linarith
  let A := Real.sqrt (v ^ 2 + E) - v
  let B := Real.sqrt (u ^ 2 + E) - u
  have ha : 2 * v * A ≤ E := sqrt_increment_tangent hE
  have hb : 2 * u * B ≤ E := sqrt_increment_tangent hE
  have ha' := mul_le_mul_of_nonneg_left ha (sq_nonneg u)
  have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg v)
  have hr := mul_nonneg (sub_nonneg.mpr hvu) (sub_nonneg.mpr huv)
  have hr' := mul_nonneg hE hr
  have hh : (2 * (u * v)) * (u * A + v * B) ≤
      (2 * (u * v)) * (5 * E / 4) := by nlinarith only [ha', hb', hr']
  have hc : u * A + v * B ≤ 5 * E / 4 := by
    by_contra hn
    have hp := mul_pos (show 0 < 2 * (u * v) by positivity)
      (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith only [hh, hp]
  dsimp only [A, B] at hc
  nlinarith only [hc]

/-- Outside the balanced ratio window the sum is controlled by the difference. -/
theorem sum_le_three_abs {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : ¬ (v ≤ 2 * u ∧ u ≤ 2 * v)) : u + v ≤ 3 * |u - v| := by
  by_cases hvu : v ≤ 2 * u
  · have huv : 2 * v < u := lt_of_not_ge (fun h' => h ⟨hvu, h'⟩)
    rw [abs_of_nonneg (show 0 ≤ u - v by linarith)]
    linarith
  · have hvu' : 2 * u < v := lt_of_not_ge hvu
    rw [abs_of_nonpos (show u - v ≤ 0 by linarith)]
    linarith

/-- Exact Young estimate used in the unbalanced case. -/
theorem unbalanced_young {d E : ℝ} (hE : 0 ≤ E) :
    d ^ 2 - 3 * Real.sqrt E * |d| ≥ d ^ 2 / 2 - 9 * E / 2 := by
  have he := Real.sq_sqrt hE
  nlinarith [sq_nonneg (|d| - 3 * Real.sqrt E), sq_abs d]

/-- The two source cases combined, before replacing the perturbed rates. -/
theorem root_bound_shifted {u v E : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hE : 0 ≤ E) :
    u ^ 2 + v ^ 2 - u * Real.sqrt (v ^ 2 + E) - v * Real.sqrt (u ^ 2 + E) ≥
      (u - v) ^ 2 / 2 - 5 * E := by
  by_cases hb : v ≤ 2 * u ∧ u ≤ 2 * v
  · have hh := balanced_increment_le hu hv hE hb.1 hb.2
    nlinarith [sq_nonneg (u - v)]
  · have hh := sum_le_three_abs hu hv hb
    have ha := mul_le_mul_of_nonneg_left (sqrt_shift_le hv hE) hu
    have hb' := mul_le_mul_of_nonneg_left (sqrt_shift_le hu hE) hv
    have hc := mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg E)
    have hy := unbalanced_young (d := u - v) hE
    nlinarith only [ha, hb', hc, hy, hE]

/-- Literal source numerical estimate. E nonnegativity follows from either
actual absolute-error bound; no separate positive-error assumption is needed. -/
theorem occupation_root_bound {a b a' b' E : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b')
    (hea : |a' - b| ≤ E) (heb : |b' - a| ≤ E) :
    a + b - Real.sqrt (a * a') - Real.sqrt (b * b') ≥
      (Real.sqrt a - Real.sqrt b) ^ 2 / 2 - 5 * E := by
  have hE : 0 ≤ E := (abs_nonneg _).trans hea
  have hae : a' ≤ b + E := by have := (abs_le.mp hea).2; linarith
  have hbe : b' ≤ a + E := by have := (abs_le.mp heb).2; linarith
  have hs := root_bound_shifted (Real.sqrt_nonneg a) (Real.sqrt_nonneg b) hE
  rw [Real.sq_sqrt ha, Real.sq_sqrt hb] at hs
  have hma := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hae) (Real.sqrt_nonneg a)
  have hmb := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbe) (Real.sqrt_nonneg b)
  rw [Real.sqrt_mul' a ha', Real.sqrt_mul' b hb']
  linarith only [hs, hma, hmb]

end PeriodicAttractiveLogGas.OccupationRootBound
