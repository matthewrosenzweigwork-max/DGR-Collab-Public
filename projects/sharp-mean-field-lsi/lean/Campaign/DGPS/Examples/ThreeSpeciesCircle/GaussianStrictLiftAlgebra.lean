import DGPS.Examples.ThreeSpeciesCircle.GaussianDefectMassControl
import DGPS.Examples.ThreeSpeciesCircle.GaussianFeatureCovariance

/-! Quantitative absorption of the genuine signed covariance correction.
This scalar support lemma is not the final native Gaussian theorem. Its two
form estimates are supplied by the actual preceding full-domain proofs. -/

noncomputable section

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Explicit positive gain from the true reference defect, the actual
first-feature coordinates, and the controlled invariant-feature correction. -/
theorem gaussian_strict_lift_absorption
    (a P h A B C L X Z d D : ℝ) (ha : 0 < a) (hP : 0 < P) (hh : 0 < h)
    (hA : 0 < A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hX : 0 ≤ X) (hd : 0 ≤ d)
    (hmass : a * L ≤ 2 * d + 6 * a * h ^ 2 * X)
    (hthird : Z ≤ (C / a) * d) (hpenalty : P * B * C / a ≤ 1 / 2)
    (hD : D = L - A * X + B * Z) (hDupper : D ≤ 2 * L) :
    let k := min (a / 4) (P * A / (6 * h ^ 2))
    0 < k ∧ (P + k / 2) * D ≤ d + P * L := by
  let k := min (a / 4) (P * A / (6 * h ^ 2))
  have hk : 0 < k := lt_min (by positivity) (by positivity)
  have hk1 : k ≤ a / 4 := min_le_left _ _
  have hk2 : k ≤ P * A / (6 * h ^ 2) := min_le_right _ _
  have hkdiv : 2 * (k / a) ≤ 1 / 2 := by
    have ht : k / a ≤ 1 / 4 := (div_le_iff₀ ha).2 (by linarith only [hk1])
    linarith only [ht]
  have hkX : 6 * k * h ^ 2 ≤ P * A := by
    have ht := (le_div_iff₀ (by positivity : 0 < 6 * h ^ 2)).1 hk2
    nlinarith only [ht]
  have hcontrol : k * L ≤ d / 2 + P * A * X := by
    calc
      _ = (k / a) * (a * L) := by field_simp [ha.ne']
      _ ≤ (k / a) * (2 * d + 6 * a * h ^ 2 * X) :=
        mul_le_mul_of_nonneg_left hmass (div_nonneg hk.le ha.le)
      _ = (2 * (k / a)) * d + (6 * k * h ^ 2) * X := by field_simp [ha.ne']
      _ ≤ (1 / 2 : ℝ) * d + (P * A) * X :=
        add_le_add (mul_le_mul_of_nonneg_right hkdiv hd) (mul_le_mul_of_nonneg_right hkX hX)
      _ = _ := by ring
  have hbad : P * B * Z ≤ d / 2 := by
    calc
      _ ≤ (P * B) * ((C / a) * d) :=
        mul_le_mul_of_nonneg_left hthird (mul_nonneg hP.le hB)
      _ = (P * B * C / a) * d := by ring
      _ ≤ (1 / 2 : ℝ) * d := mul_le_mul_of_nonneg_right hpenalty hd
      _ = _ := by ring
  have hgain : k * L ≤ d + P * L - P * D := by
    rw [hD]
    nlinarith only [hcontrol, hbad]
  have hhalf : (k / 2) * D ≤ k * L := by
    have ht := mul_le_mul_of_nonneg_left hDupper (by positivity : 0 ≤ k / 2)
    nlinarith only [ht]
  refine ⟨hk, ?_⟩
  change (P + k / 2) * D ≤ _
  nlinarith only [hgain, hhalf]

end DGPS.Examples.ThreeSpeciesCircle
