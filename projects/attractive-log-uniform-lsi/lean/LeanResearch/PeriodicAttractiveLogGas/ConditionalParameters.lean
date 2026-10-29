import LeanResearch.PeriodicAttractiveLogGas.PointWeightDensity
import LeanResearch.PeriodicAttractiveLogGas.PoleLogMoments

/-! The fixed radius and positive occupation parameter in source lines 523–540.
The logarithmic constant is the actual bounded supremum. No division by the
coupling is used, and all choices precede particle number and mesh size. -/

noncomputable section
open scoped ENNReal NNReal

namespace PeriodicAttractiveLogGas.ConditionalParameters

open PointWeightDensity PoleLogMoments

def nearRadius (β₀ C₁ : ℝ) : ℕ := max 1 ⌈4 * Real.sqrt 5 * β₀ * C₁⌉₊

theorem nearRadius_one_le (β₀ C₁ : ℝ) : 1 ≤ nearRadius β₀ C₁ := le_max_left _ _

theorem nearRadius_int_eq {β₀ C₁ : ℝ} (hβ : 0 ≤ β₀) (hC : 0 ≤ C₁) :
    (nearRadius β₀ C₁ : ℤ) = max 1 ⌈4 * Real.sqrt 5 * β₀ * C₁⌉ := by
  unfold nearRadius
  rw [Nat.cast_max, Nat.cast_one, Int.natCast_ceil_eq_ceil (by positivity)]

theorem nearRadius_lower (β₀ C₁ : ℝ) :
    4 * Real.sqrt 5 * β₀ * C₁ ≤ (nearRadius β₀ C₁ : ℝ) :=
  (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈4 * Real.sqrt 5 * β₀ * C₁⌉₊)

def distanceBound (R : ℕ) : ℝ := Real.sqrt 2 * ((R : ℝ) + 2)

def oscillationBound (β₀ C₁ : ℝ) (R : ℕ) : ℝ := Real.sqrt 5 * β₀ * C₁ / R

theorem distanceBound_one_le {R : ℕ} (hR : 1 ≤ R) : 1 ≤ distanceBound R := by
  have hr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hs : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
  unfold distanceBound
  nlinarith

theorem distanceBound_lt_half {R J : ℕ} (hR : 1 ≤ R) (hJ : 8 * (R + 4) ≤ J) :
    distanceBound R < (J : ℝ) / 2 := by
  have hr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hj : 8 * ((R : ℝ) + 4) ≤ J := by exact_mod_cast hJ
  have hs : Real.sqrt 2 < (2 : ℝ) := by norm_num
  unfold distanceBound
  nlinarith

theorem oscillationBound_nonneg {β₀ C₁ : ℝ} (hβ : 0 ≤ β₀) (hC : 0 ≤ C₁) (R : ℕ) :
    0 ≤ oscillationBound β₀ C₁ R := by unfold oscillationBound; positivity

theorem oscillationBound_nearRadius_le (β₀ C₁ : ℝ) :
    oscillationBound β₀ C₁ (nearRadius β₀ C₁) ≤ 1 / 4 := by
  have hr : (0 : ℝ) < nearRadius β₀ C₁ := by exact_mod_cast (nearRadius_one_le β₀ C₁)
  unfold oscillationBound
  apply (div_le_iff₀ hr).mpr
  linarith [nearRadius_lower β₀ C₁]

theorem sourceLowerConstant_pos {D : ℝ} (hD : 0 < D) (ω C₀ : ℝ) :
    0 < sourceLowerConstant D ω C₀ := by unfold sourceLowerConstant; positivity

theorem sourceNormConstant_pos {D : ℝ} (hD : 0 < D) (ω C₀ : ℝ) :
    0 < sourceNormConstant D ω C₀ := by unfold sourceNormConstant; positivity

/-- A concrete admissible choice. Its denominator is at least two, even when β₀=0. -/
def occupationDelta (β₀ : ℝ) (R : ℕ) (K Λ C₀ : ℝ) : ℝ :=
  (2 + 16 * (β₀ * (2 * (R : ℝ) + 2) ^ 2) +
    4 * (4 * β₀ * (2 * (R : ℝ) + 5) ^ 2 * K * (Λ + C₀)))⁻¹

theorem occupationDelta_bounds {β₀ K Λ C₀ : ℝ} (hβ : 0 ≤ β₀) (hK : 0 ≤ K)
    (hΛ : 0 ≤ Λ) (hC : 0 ≤ C₀) (R : ℕ) :
    0 < occupationDelta β₀ R K Λ C₀ ∧ occupationDelta β₀ R K Λ C₀ ≤ 1 / 2 ∧
      β₀ * (2 * (R : ℝ) + 2) ^ 2 * occupationDelta β₀ R K Λ C₀ ≤ 1 / 16 ∧
      4 * β₀ * (2 * (R : ℝ) + 5) ^ 2 * occupationDelta β₀ R K Λ C₀ * K * (Λ + C₀) ≤ 1 / 4 := by
  let A := β₀ * (2 * (R : ℝ) + 2) ^ 2
  let B := 4 * β₀ * (2 * (R : ℝ) + 5) ^ 2 * K * (Λ + C₀)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hd : 0 < 2 + 16 * A + 4 * B := by positivity
  have he : occupationDelta β₀ R K Λ C₀ = (2 + 16 * A + 4 * B)⁻¹ := rfl
  have hδ := inv_pos.mpr hd
  have hδ2 : (2 + 16 * A + 4 * B)⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (show 2 ≤ 2 + 16 * A + 4 * B by linarith)
  have hδA : A * (2 + 16 * A + 4 * B)⁻¹ ≤ 1 / 16 := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hd).mpr
    linarith
  have hδB : B * (2 + 16 * A + 4 * B)⁻¹ ≤ 1 / 4 := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hd).mpr
    linarith
  rw [he]
  refine ⟨hδ, hδ2, hδA, ?_⟩
  calc
    _ = B * (2 + 16 * A + 4 * B)⁻¹ := by dsimp [B]; ring
    _ ≤ _ := hδB

@[simp] theorem occupationDelta_zero (R : ℕ) (K Λ C₀ : ℝ) :
    occupationDelta 0 R K Λ C₀ = 1 / 2 := by simp [occupationDelta]

def fixedLower (β₀ C₀ C₁ : ℝ) : ℝ :=
  sourceLowerConstant (distanceBound (nearRadius β₀ C₁))
    (oscillationBound β₀ C₁ (nearRadius β₀ C₁)) C₀

def fixedNorm (β₀ C₀ C₁ : ℝ) : ℝ :=
  sourceNormConstant (distanceBound (nearRadius β₀ C₁))
    (oscillationBound β₀ C₁ (nearRadius β₀ C₁)) C₀

def fixedDelta (β₀ C₀ C₁ : ℝ) : ℝ := occupationDelta β₀ (nearRadius β₀ C₁)
  (fixedNorm β₀ C₀ C₁) (lambdaStar (nearRadius β₀ C₁)) C₀

/-- Both requested restrictions, with the actual Lambda_* and exact K_*,
hold for one positive choice independent of N and J. -/
theorem fixedDelta_bounds {β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β₀) (hC₀ : 0 ≤ C₀) :
    0 < fixedDelta β₀ C₀ C₁ ∧ fixedDelta β₀ C₀ C₁ ≤ 1 / 2 ∧
      β₀ * (2 * (nearRadius β₀ C₁ : ℝ) + 2) ^ 2 * fixedDelta β₀ C₀ C₁ ≤ 1 / 16 ∧
      4 * β₀ * (2 * (nearRadius β₀ C₁ : ℝ) + 5) ^ 2 * fixedDelta β₀ C₀ C₁ *
        fixedNorm β₀ C₀ C₁ * (lambdaStar (nearRadius β₀ C₁) + C₀) ≤ 1 / 4 := by
  have hr := nearRadius_one_le β₀ C₁
  have hdr : 0 < distanceBound (nearRadius β₀ C₁) :=
    lt_of_lt_of_le zero_lt_one (distanceBound_one_le hr)
  exact occupationDelta_bounds hβ (sourceNormConstant_pos hdr _ _).le
    (lambdaStar_nonneg (by exact_mod_cast hr)) hC₀ _

@[simp] theorem fixedDelta_zero (C₀ C₁ : ℝ) : fixedDelta 0 C₀ C₁ = 1 / 2 :=
  occupationDelta_zero _ _ _ _

end PeriodicAttractiveLogGas.ConditionalParameters
