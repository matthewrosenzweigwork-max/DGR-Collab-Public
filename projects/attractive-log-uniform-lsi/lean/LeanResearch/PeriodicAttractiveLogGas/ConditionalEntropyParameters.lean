import LeanResearch.PeriodicAttractiveLogGas.ConditionalLawEstimates
import LeanResearch.PeriodicAttractiveLogGas.ResidualExponential

/-! Uniform numerical parameter choice for source lines 2347–2358,
2580–2588 and the hypotheses of Theorem conditional-entropy. The occupation
parameter is chosen before the resolution and particle number. All constants
are the existing source constants, including the zero-temperature endpoint. -/

noncomputable section
open scoped NNReal

namespace PeriodicAttractiveLogGas.ConditionalEntropyParameters

open ConditionalLawEstimates ReferenceResidual ResidualNearExponential ResidualFarExponential

/-- A single occupation parameter satisfies both actual source smallness
conditions and is strictly below the original microscopic cap. -/
theorem exists_occupation_parameter {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (C₂ : ℝ) :
    ∃ t : ℝ, 0 < t ∧ t < occupationBound β₀ ∧
      4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1 ∧
      24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
        nearScale (chosenRadius β₀ C₂) * t ≤ 1 := by
  let A := (4 * β₀ * kernelConstant) ^ 2 * (Real.pi * Real.exp 1)
  let B := 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
    nearScale (chosenRadius β₀ C₂)
  have hδ := (chosen_parameters β₀ hβ₀).1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by
    have hC := universalConstant_pos.le
    have hL := nearScale_nonneg (chosenRadius β₀ C₂)
    dsimp [B]
    positivity
  let t := min (occupationBound β₀ / 2) (min (1 / (1 + A)) (1 / (1 + B)))
  have ht : 0 < t := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have htδ : t < occupationBound β₀ := (min_le_left _ _).trans_lt (by linarith)
  have htA : t ≤ 1 / (1 + A) := (min_le_right _ _).trans (min_le_left _ _)
  have htB : t ≤ 1 / (1 + B) := (min_le_right _ _).trans (min_le_right _ _)
  have hAt : A * t ≤ 1 := by
    have h := (le_div_iff₀ (show 0 < 1 + A by linarith)).mp htA
    nlinarith
  have hBt : B * t ≤ 1 := by
    have h := (le_div_iff₀ (show 0 < 1 + B by linarith)).mp htB
    nlinarith
  refine ⟨t, ht, htδ, ?_, hBt⟩
  have hx : 0 ≤ 4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) := by
    have hK := kernelConstant_pos.le
    positivity
  have hs : (4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t)) ^ 2 = A * t := by
    rw [mul_pow, Real.sq_sqrt (show 0 ≤ Real.pi * Real.exp 1 * t by positivity)]
    dsimp [A]
    ring
  nlinarith

/-- Every larger natural resolution satisfies both actual geometric mesh
gates and the source reference scale condition. No coupling is divided by. -/
theorem exists_mesh_threshold (β₀ C₂ : ℝ) {t : ℝ} (ht : 0 < t) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      8 * (radius β₀ + 4) ≤ J ∧ 8 * (chosenRadius β₀ C₂ + 1) ≤ J ∧
      2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t) := by
  let s := Real.sqrt (2 * Real.pi * Real.exp 1 * t)
  have hs : 0 < s := by dsimp [s]; positivity
  let J₀ := max (8 * (radius β₀ + 4))
    (max (8 * (chosenRadius β₀ C₂ + 1)) (Nat.ceil (2 / s)))
  refine ⟨J₀, fun J hJ => ?_⟩
  have hm : 8 * (radius β₀ + 4) ≤ J := (le_max_left _ _).trans hJ
  have hr : 8 * (chosenRadius β₀ C₂ + 1) ≤ J :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hJ)
  have hc : Nat.ceil (2 / s) ≤ J := (le_max_right _ _).trans ((le_max_right _ _).trans hJ)
  have hc' : (Nat.ceil (2 / s) : ℝ) ≤ J := by exact_mod_cast hc
  have hscale := (Nat.le_ceil (2 / s)).trans hc'
  exact ⟨hm, hr, (div_le_iff₀ hs).mp hscale⟩

/-- Uniform source parameter order: first one positive t, then one natural
threshold, then every later J and every particle number. The analytic kernel
and subcriticality hypotheses are not needed merely to choose these numbers. -/
theorem exists_uniform_parameters {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (C₂ : ℝ) :
    ∃ t : ℝ, ∃ J₀ : ℕ,
      0 < t ∧ t < occupationBound β₀ ∧
      4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1 ∧
      24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
        nearScale (chosenRadius β₀ C₂) * t ≤ 1 ∧
      ∀ J : ℕ, J₀ ≤ J →
        8 * (radius β₀ + 4) ≤ J ∧ 8 * (chosenRadius β₀ C₂ + 1) ≤ J ∧
        2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t) := by
  obtain ⟨t, ht, hδ, hosc, hcap⟩ := exists_occupation_parameter hβ₀ C₂
  obtain ⟨J₀, hJ₀⟩ := exists_mesh_threshold β₀ C₂ ht
  exact ⟨t, J₀, ht, hδ, hosc, hcap, hJ₀⟩

/-- Explicit zero-inverse-temperature occupation choice. It retains both
mesh conditions and the positive reference scale at every later resolution. -/
theorem zero_temperature_parameters (C₂ : ℝ) :
    ∃ J₀ : ℕ, (0 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) < occupationBound 0 ∧
      4 * (0 : ℝ) * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * (1 / 4)) ≤ 1 ∧
      24 * (0 : ℝ) * (colorCount (chosenRadius 0 C₂) : ℝ) * universalConstant *
        nearScale (chosenRadius 0 C₂) * (1 / 4) ≤ 1 ∧
      ∀ J : ℕ, J₀ ≤ J →
        8 * (radius 0 + 4) ≤ J ∧ 8 * (chosenRadius 0 C₂ + 1) ≤ J ∧
        2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * (1 / 4)) := by
  obtain ⟨J₀, hJ₀⟩ := exists_mesh_threshold 0 C₂ (t := 1 / 4) (by norm_num)
  exact ⟨J₀, by norm_num, by norm_num, by norm_num, by norm_num, hJ₀⟩

end PeriodicAttractiveLogGas.ConditionalEntropyParameters
