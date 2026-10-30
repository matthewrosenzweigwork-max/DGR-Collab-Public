import DGPS.FiniteN.AnisotropicQuarticRareTest

/-! Actual core and support identities for the concrete symmetric rare test. -/

open DGPS.Models DGPS.FiniteN.ScalarFoldFIN064

namespace DGPS.FiniteN

theorem quarticRareTest_one (δ : ℝ) (hδ : 0 < δ) (N : ℕ+) (x : ParticleSpace 1 N)
    (hx : |quarticEmpiricalCos N x + 4| ≤ δ / 2)
    (hy : |quarticEmpiricalSin N x| ≤ (N : ℝ) ^ (-(1 / 4 : ℝ))) :
    quarticRareTest δ N x = 1 := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast N.pos
  have ha : 0 < (N : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hN _
  have hlong : |(2 / δ) * (quarticEmpiricalCos N x + 4)| ≤ 1 := by
    rw [abs_mul, abs_of_pos (div_pos (by norm_num) hδ)]
    have hm := mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ 2 / δ)
    have he : (2 / δ) * (δ / 2) = 1 := by field_simp [hδ.ne']
    exact he ▸ hm
  have htrans : |(N : ℝ) ^ (1 / 4 : ℝ) * quarticEmpiricalSin N x| ≤ 1 := by
    rw [abs_mul, abs_of_pos ha]
    rw [Real.rpow_neg hN.le] at hy
    have hm := mul_le_mul_of_nonneg_left hy ha.le
    rwa [mul_inv_cancel₀ ha.ne'] at hm
  unfold quarticRareTest
  rw [chi_one_FIN064 hlong, chi_one_FIN064 htrans, mul_one]

theorem quarticRareTest_zero (δ : ℝ) (hδ : 0 < δ) (N : ℕ+) (x : ParticleSpace 1 N)
    (hout : ¬ (|quarticEmpiricalCos N x + 4| ≤ δ ∧
      |quarticEmpiricalSin N x| ≤ 2 * (N : ℝ) ^ (-(1 / 4 : ℝ)))) :
    quarticRareTest δ N x = 0 := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast N.pos
  have ha : 0 < (N : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hN _
  by_cases hx : |quarticEmpiricalCos N x + 4| ≤ δ
  · have hy : 2 * (N : ℝ) ^ (-(1 / 4 : ℝ)) < |quarticEmpiricalSin N x| :=
      lt_of_not_ge fun h => hout ⟨hx, h⟩
    have htrans : 2 < |(N : ℝ) ^ (1 / 4 : ℝ) * quarticEmpiricalSin N x| := by
      rw [abs_mul, abs_of_pos ha]
      rw [Real.rpow_neg hN.le] at hy
      have hm := mul_lt_mul_of_pos_left hy ha
      have he : (N : ℝ) ^ (1 / 4 : ℝ) * (2 * ((N : ℝ) ^ (1 / 4 : ℝ))⁻¹) = 2 := by
        field_simp [ha.ne']
      rwa [he] at hm
    unfold quarticRareTest
    rw [chi_zero_FIN064 htrans, mul_zero]
  · have hlong : 2 < |(2 / δ) * (quarticEmpiricalCos N x + 4)| := by
      rw [abs_mul, abs_of_pos (div_pos (by norm_num) hδ)]
      have hm := mul_lt_mul_of_pos_left (lt_of_not_ge hx)
        (show (0 : ℝ) < 2 / δ from div_pos (by norm_num) hδ)
      have he : (2 / δ) * δ = 2 := by field_simp [hδ.ne']
      rwa [he] at hm
    unfold quarticRareTest
    rw [chi_zero_FIN064 hlong, zero_mul]

end DGPS.FiniteN
