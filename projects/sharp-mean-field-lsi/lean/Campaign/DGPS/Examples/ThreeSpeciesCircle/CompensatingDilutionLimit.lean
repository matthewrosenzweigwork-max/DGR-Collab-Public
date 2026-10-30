import DGPS.Examples.ThreeSpeciesCircle.CompensatingOrdinaryModel

/-! Sequential dilution algebra for the actual full-H1 compensating pair.
No smooth carrier or desired quotient limit is imported. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

def compensatingDilutionWeight (M : ℝ) (n : ℕ) : ℝ :=
  1 / (2 * (M ^ 2 + 1) * ((n : ℝ) + 2))

theorem compensatingDilutionWeight_bounds (M : ℝ) (n : ℕ) :
    0 < compensatingDilutionWeight M n ∧
      compensatingDilutionWeight M n ≤ 1 / 2 ∧
      compensatingDilutionWeight M n * M ^ 2 ≤ 1 / 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm : 0 < M ^ 2 + 1 := by positivity
  have hd : 0 < 2 * (M ^ 2 + 1) * ((n : ℝ) + 2) := by positivity
  have hlo : 4 * (M ^ 2 + 1) ≤ 2 * (M ^ 2 + 1) * ((n : ℝ) + 2) := by
    nlinarith [mul_nonneg hm.le hn]
  refine ⟨by unfold compensatingDilutionWeight; positivity, ?_, ?_⟩
  · unfold compensatingDilutionWeight
    apply (div_le_iff₀ hd).2
    nlinarith [sq_nonneg M]
  · unfold compensatingDilutionWeight
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hd).2
    nlinarith [sq_nonneg M]

theorem compensatingDilutionWeight_tendsto (M : ℝ) :
    Tendsto (compensatingDilutionWeight M) atTop (𝓝 (0 : ℝ)) := by
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, one_div] using
      (tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (2 : ℝ)
          (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)))
  have hh := ht.const_mul (1 / (2 * (M ^ 2 + 1)))
  convert hh using 1
  · funext n
    simp only [compensatingDilutionWeight, one_div, mul_inv_rev]
    ring
  · simp

/-- Quadratically small complement entropy and information give the TRUE
sequential quotient limit for positive weights tending to zero. -/
theorem compensating_binary_real_limit {i H C : ℝ} (hH : 0 < H)
    (w a b : ℕ → ℝ) (hw : ∀ n, 0 < w n) (hwlim : Tendsto w atTop (𝓝 0))
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ C * w n ^ 2)
    (hb : ∀ n, 0 ≤ b n ∧ b n ≤ C * w n ^ 2) :
    Tendsto (fun n => (w n * i + (1 - w n) * a n) /
      (2 * (w n * H + (1 - w n) * b n))) atTop (𝓝 (i / (2 * H))) := by
  have hsmall (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n ∧ v n ≤ C * w n ^ 2) :
      Tendsto (fun n => v n / w n) atTop (𝓝 (0 : ℝ)) := by
    refine squeeze_zero (fun n => div_nonneg (hv n).1 (hw n).le) (fun n => ?_)
      (by simpa using hwlim.const_mul C)
    apply (div_le_iff₀ (hw n)).2
    nlinarith [(hv n).2]
  have hAlim := hsmall a ha
  have hBlim := hsmall b hb
  have ht : Tendsto (fun n => (i + (1 - w n) * (a n / w n)) /
      (2 * (H + (1 - w n) * (b n / w n)))) atTop (𝓝 (i / (2 * H))) := by
    have hh := ((tendsto_const_nhds (x := i)).add
      (((tendsto_const_nhds (x := (1 : ℝ))).sub hwlim).mul hAlim)).div
      (((tendsto_const_nhds (x := H)).add
        (((tendsto_const_nhds (x := (1 : ℝ))).sub hwlim).mul hBlim)).const_mul 2)
      (by simpa using (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hH.ne'))
    convert hh using 1 <;> first | (funext n; rfl) | simp
  apply ht.congr
  intro n
  have hnum : w n * i + (1 - w n) * a n =
      w n * (i + (1 - w n) * (a n / w n)) := by field_simp [(hw n).ne'] <;> ring
  have hden : 2 * (w n * H + (1 - w n) * b n) =
      w n * (2 * (H + (1 - w n) * (b n / w n))) := by field_simp [(hw n).ne'] <;> ring
  rw [hnum, hden, mul_div_mul_left _ _ (hw n).ne']

end DGPS.Examples.ThreeSpeciesCircle
