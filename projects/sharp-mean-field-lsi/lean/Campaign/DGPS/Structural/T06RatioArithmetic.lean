import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace DGPS.Lipschitz

/-- Pure real arithmetic for the sharp scalar/species amplitude comparison.
No sign assumption on `a0` is needed beyond the displayed bounds. -/
theorem t06_scalar_species_ratio_arithmetic
    {rs rm ell a0 B M : ℝ}
    (hrs : 0 < rs) (hrm : 0 < rm) (hell : 0 < ell)
    (hm : rm ≤ rs)
    (hharm : rs * ell / (rs + ell) ≤ rm)
    (hlower : a0 * Real.exp (-M) ≤ ell)
    (hupper : rs ≤ a0 * (1 + B / 2) * Real.exp M)
    (hB : 0 ≤ B) :
    1 ≤ rs / rm ∧ rs / rm ≤ 1 + (1 + B / 2) * Real.exp (2 * M) := by
  have hC : 0 ≤ 1 + B / 2 := by linarith
  have hexp : Real.exp (2 * M) * Real.exp (-M) = Real.exp M := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hscale : rs ≤ ((1 + B / 2) * Real.exp (2 * M)) * ell := by
    calc
      rs ≤ a0 * (1 + B / 2) * Real.exp M := hupper
      _ = a0 * (1 + B / 2) *
          (Real.exp (2 * M) * Real.exp (-M)) := by rw [hexp]
      _ = ((1 + B / 2) * Real.exp (2 * M)) *
          (a0 * Real.exp (-M)) := by ring
      _ ≤ ((1 + B / 2) * Real.exp (2 * M)) * ell :=
        mul_le_mul_of_nonneg_left hlower
          (mul_nonneg hC (Real.exp_pos _).le)
  have hprod : rs * ell ≤ rm * (rs + ell) :=
    (div_le_iff₀ (add_pos hrs hell)).mp hharm
  have hfinal : rs ≤ (1 + (1 + B / 2) * Real.exp (2 * M)) * rm := by
    apply (mul_le_mul_iff_right₀ hell).mp
    nlinarith [mul_le_mul_of_nonneg_left hscale hrm.le]
  constructor
  · exact (le_div_iff₀ hrm).mpr (by simpa using hm)
  · exact (div_le_iff₀ hrm).mpr hfinal

end DGPS.Lipschitz
