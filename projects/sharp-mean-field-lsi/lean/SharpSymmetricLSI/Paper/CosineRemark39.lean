import SharpSymmetricLSI.Paper.CosineSharpPoincare

/-!
# Remark 3.9: explicit constants (Phase 3, lane C; R43)
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal Real

namespace SharpLSI

/-- `r^all ≥ 2aλ/(4λ+b) ≥ 2ac/(4c+b)` for `c ≤ λ`. -/
theorem rAll_ge_of_lam_ge {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) {c : ℝ} (hc0 : 0 < c)
    (hcl : ENNReal.ofReal c ≤ lamAll cosV (cosW κ) N) :
    ENNReal.ofReal (2 * aCos * c / (4 * c + (2 * κ + 8) * aCos)) ≤ rAll cosV (cosW κ) N := by
  have ha0 : 0 < aCos := by unfold aCos; positivity
  set b := (2 * κ + 8) * aCos with hb
  have hb0 : 0 < b := by positivity
  refine le_trans ?_ (rAll_ge_of_lamAll hκ hN)
  have hLt := lamAll_lt_top (κ := κ) hN
  set l := (lamAll cosV (cosW κ) N).toReal
  have hLl : lamAll cosV (cosW κ) N = ENNReal.ofReal l := (ENNReal.ofReal_toReal hLt.ne).symm
  have hcl' : c ≤ l := (ENNReal.ofReal_le_iff_le_toReal hLt.ne).mp hcl
  rw [hLl]
  have hXe : 2 * ENNReal.ofReal aCos * ENNReal.ofReal l /
      (4 * ENNReal.ofReal l + ENNReal.ofReal ((2 * κ + 8) * aCos)) =
      ENNReal.ofReal (2 * aCos * l / (4 * l + (2 * κ + 8) * aCos)) := by
    rw [ENNReal.ofReal_div_of_pos (by nlinarith)]
    congr 1
    · rw [ENNReal.ofReal_mul (by nlinarith), ENNReal.ofReal_mul (by norm_num)]; simp
    · rw [ENNReal.ofReal_add (by nlinarith) hb0.le, ENNReal.ofReal_mul (p := 4) (by norm_num)]
      simp [hb]
  rw [hXe]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
  nlinarith [mul_le_mul_of_nonneg_left hcl' (by positivity : (0 : ℝ) ≤ 2 * aCos * b)]

theorem cosine_labeled_constants_aux {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N)
    (hNκ : 2 * κ * Real.exp (2 * κ) ≤ N) :
    ENNReal.ofReal (aCos * Real.exp (-2 * κ) / 2) ≤ lamAll cosV (cosW κ) N ∧
      ENNReal.ofReal (aCos / (2 + (2 * κ + 8) * Real.exp (2 * κ))) ≤ rAll cosV (cosW κ) N := by
  have ha0 : 0 < aCos := by unfold aCos; positivity
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have he : Real.exp (-2 * κ) * Real.exp (2 * κ) = 1 := by rw [← Real.exp_add]; simp
  have hep := Real.exp_pos (-2 * κ)
  have hep2 := Real.exp_pos (2 * κ)
  have h1 : Real.exp (-2 * κ) / 2 ≤ max (Real.exp (-κ * N / 2)) (Real.exp (-2 * κ) - κ / N) := by
    refine le_trans ?_ (le_max_right _ _)
    have : κ / N ≤ Real.exp (-2 * κ) / 2 := by
      rw [div_le_div_iff₀ hN' (by norm_num)]; nlinarith
    linarith
  have hlam : ENNReal.ofReal (aCos * Real.exp (-2 * κ) / 2) ≤ lamAll cosV (cosW κ) N :=
    (ENNReal.ofReal_le_ofReal (by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h1 ha0.le)).trans
      (cosine_labeled_poincare_aux hκ hN)
  refine ⟨hlam, ?_⟩
  have := rAll_ge_of_lam_ge hκ hN (by positivity) hlam
  convert this using 2
  field_simp
  have he' : Real.exp (-(2 * κ)) * Real.exp (2 * κ) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [he']

end SharpLSI
