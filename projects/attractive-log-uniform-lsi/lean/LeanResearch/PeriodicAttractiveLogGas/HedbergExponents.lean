import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The radius and exponent identities in the source Hedberg argument.
Only scalar algebra appears here; the potential estimates are separate. -/
set_option autoImplicit false
noncomputable section
namespace PeriodicAttractiveLogGas.HedbergExponents

lemma radius_balance {d E M : ℝ} (hd : 0 < d) (hE : 0 < E) (hM : 0 < M) :
    (E / M) ^ (2 / d) * M = E ^ (2 / d) * M ^ (1 - 2 / d) ∧
    ((E / M) ^ (2 / d)) ^ (1 - d / 2) * E = E ^ (2 / d) * M ^ (1 - 2 / d) := by
  have hMpow : M ^ (2 / d) ≠ 0 := (Real.rpow_pos_of_pos hM _).ne'
  have hMsplit : M ^ (1 - 2 / d) * M ^ (2 / d) = M := by
    rw [← Real.rpow_add hM, sub_add_cancel, Real.rpow_one]
  constructor
  · rw [Real.div_rpow hE.le hM.le]
    calc
      E ^ (2 / d) / M ^ (2 / d) * M = (E ^ (2 / d) * M) / M ^ (2 / d) := by ring
      _ = E ^ (2 / d) * M ^ (1 - 2 / d) :=
        (div_eq_iff hMpow).mpr (by rw [mul_assoc, hMsplit])
  · rw [← Real.rpow_mul (div_pos hE hM).le,
      show (2 / d) * (1 - d / 2) = 2 / d - 1 by field_simp [hd.ne'],
      Real.div_rpow hE.le hM.le]
    have hEsplit : E ^ (2 / d - 1) * E = E ^ (2 / d) := by
      calc
        E ^ (2 / d - 1) * E = E ^ (2 / d - 1) * E ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = E ^ (2 / d) := by rw [← Real.rpow_add hE, sub_add_cancel]
    have hMinv : (M ^ (2 / d - 1))⁻¹ = M ^ (1 - 2 / d) := by
      rw [← Real.rpow_neg hM.le]
      congr 1
      ring
    calc
      E ^ (2 / d - 1) / M ^ (2 / d - 1) * E =
          (E ^ (2 / d - 1) * E) * (M ^ (2 / d - 1))⁻¹ := by ring
      _ = _ := by rw [hEsplit, hMinv]

lemma sobolev_exponent {d : ℝ} (hd : 2 < d) :
    2 < 2 * d / (d - 2) ∧
    (1 - 2 / d) * (2 * d / (d - 2)) = 2 ∧
    (2 * d / (d - 2)) / d + 1 = (2 * d / (d - 2)) / 2 := by
  have hd0 : d ≠ 0 := (show 0 < d by linarith).ne'
  have hd2 : d - 2 ≠ 0 := (sub_pos.mpr hd).ne'
  refine ⟨(lt_div_iff₀ (sub_pos.mpr hd)).mpr (by linarith), ?_, ?_⟩ <;>
    field_simp <;> ring

end PeriodicAttractiveLogGas.HedbergExponents
