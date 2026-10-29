import LeanResearch.PeriodicAttractiveLogGas.HeavyPartition

/-! Exact constants and resolution-uniform absorption in source
`thm:heavy-coercivity`, equations (heavy-constant)--(heavy-particle-threshold). -/

noncomputable section
open scoped NNReal

namespace PeriodicAttractiveLogGas.HeavyCoercivityConstants
open HeavyScales HeavyPartition SeparatedRadius

def coercivityConstant (β₀ δ : ℝ) : ℝ :=
  52428800 * (2 * separationRadius β₀) ^ (2 * sourceScaleCount β₀ δ - 2) /
    ((4 - β₀) ^ 2 * δ ^ 4)

def particleThreshold (β₀ δ : ℝ) : ℕ :=
  max ⌈8 / δ⌉₊
    ⌈Real.sqrt (32 * coercivityConstant β₀ δ) * sourceScaleCount β₀ δ *
      scaleGradientConstant β₀ δ / δ ^ (3 / 2 : ℝ)⌉₊

theorem coercivityConstant_pos {β₀ δ : ℝ} (hβ : β₀ < 4) (hδ : 0 < δ) :
    0 < coercivityConstant β₀ δ := by
  have hK : 0 < separationRadius β₀ := by linarith [separationRadius_ge_eight β₀]
  have hgap : 0 < 4 - β₀ := sub_pos.mpr hβ
  unfold coercivityConstant
  positivity

theorem scaleGradientConstant_pos {β₀ δ : ℝ} (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) :
    0 < scaleGradientConstant β₀ δ := by
  have hc := separationConstant_pos hβ₀
  have hgap : 0 < 4 - β₀ := sub_pos.mpr hβ
  unfold scaleGradientConstant
  positivity

theorem threshold_eight {N : ℕ} {β₀ δ : ℝ}
    (hN : particleThreshold β₀ δ ≤ N) : 8 / δ ≤ (N : ℝ) := by
  exact Nat.ceil_le.mp ((le_max_left _ _).trans hN)

theorem threshold_positive {N : ℕ} {β₀ δ : ℝ} (hδ : 0 < δ)
    (hN : particleThreshold β₀ δ ≤ N) : 0 < N := by
  have h : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) (threshold_eight hN)
  exact_mod_cast h

/-- Keep the factor J^-2 when comparing any selected radius with the largest scale. -/
theorem scale_squared_le {J M m : ℕ} {K : ℝ} (hK : 1 ≤ 2 * K) (hm : m < M) :
    scaleRadius J K m ^ 2 ≤ 4 * (2 * K) ^ (2 * M - 2) / (J : ℝ) ^ 2 := by
  have he : 2 * m ≤ 2 * M - 2 := by omega
  have hp := pow_le_pow_right₀ hK he
  have hsq : scaleRadius J K m ^ 2 = (4 / (J : ℝ) ^ 2) * (2 * K) ^ (2 * m) := by
    simp only [scaleRadius, mul_pow, div_pow, ← pow_mul]
    rw [Nat.mul_comm m 2]
    norm_num
  rw [hsq]
  calc
    (4 / (J : ℝ) ^ 2) * (2 * K) ^ (2 * m) ≤
        (4 / (J : ℝ) ^ 2) * (2 * K) ^ (2 * M - 2) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

theorem separated_scale_coefficient_le {N J m : ℕ} {β₀ δ : ℝ}
    (hN : 0 < N) (hJ : 0 < J) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hm : m < sourceScaleCount β₀ δ) :
    409600 * scaleRadius J (separationRadius β₀) m ^ 2 /
        ((4 - β₀) ^ 2 * (δ / 2) ^ 4 * N) ≤
      coercivityConstant β₀ δ / (2 * (J : ℝ) ^ 2 * N) := by
  have hgap : 0 < 4 - β₀ := sub_pos.mpr hβ
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := scale_squared_le (J := J) (K := separationRadius β₀)
    (by linarith [separationRadius_ge_eight β₀]) hm
  calc
    409600 * scaleRadius J (separationRadius β₀) m ^ 2 /
        ((4 - β₀) ^ 2 * (δ / 2) ^ 4 * N) ≤
      409600 * (4 * (2 * separationRadius β₀) ^ (2 * sourceScaleCount β₀ δ - 2) /
        (J : ℝ) ^ 2) / ((4 - β₀) ^ 2 * (δ / 2) ^ 4 * N) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) (by positivity)
    _ = coercivityConstant β₀ δ / (2 * (J : ℝ) ^ 2 * N) := by
      unfold coercivityConstant
      field_simp
      ring

theorem rpow_three_halves_sq {δ : ℝ} (hδ : 0 < δ) :
    (δ ^ (3 / 2 : ℝ)) ^ 2 = δ ^ 3 := by
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hδ.le]
  norm_num

/-- The source particle threshold bounds the absorption coefficient uniformly in J. -/
theorem absorption_coefficient_le {N : ℕ} {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hN : particleThreshold β₀ δ ≤ N) :
    16 * coercivityConstant β₀ δ * (sourceScaleCount β₀ δ : ℝ) ^ 2 *
        scaleGradientConstant β₀ δ ^ 2 / (δ ^ 3 * (N : ℝ) ^ 2) ≤ 1 / 2 := by
  have hC := coercivityConstant_pos hβ hδ
  have hA := scaleGradientConstant_pos (δ := δ) hβ₀ hβ
  have hNr : (0 : ℝ) < N := by exact_mod_cast threshold_positive hδ hN
  have hr := Real.rpow_pos_of_pos hδ (3 / 2 : ℝ)
  have ht : Real.sqrt (32 * coercivityConstant β₀ δ) * sourceScaleCount β₀ δ *
      scaleGradientConstant β₀ δ / δ ^ (3 / 2 : ℝ) ≤ (N : ℝ) :=
    Nat.ceil_le.mp ((le_max_right _ _).trans hN)
  have ht' := (div_le_iff₀ hr).mp ht
  have hs : (Real.sqrt (32 * coercivityConstant β₀ δ) * sourceScaleCount β₀ δ *
      scaleGradientConstant β₀ δ) ^ 2 ≤ ((N : ℝ) * δ ^ (3 / 2 : ℝ)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr ht'
  simp only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 32 * coercivityConstant β₀ δ),
    rpow_three_halves_sq hδ] at hs
  apply (div_le_iff₀ (by positivity : 0 < δ ^ 3 * (N : ℝ) ^ 2)).mpr
  nlinarith

theorem spatial_partition_coefficient_identity {N J : ℕ} {β₀ δ : ℝ} (hJ : 0 < J) :
    (coercivityConstant β₀ δ / (2 * (J : ℝ) ^ 2 * N)) *
        (32 * (sourceScaleCount β₀ δ : ℝ) ^ 2 * scaleGradientConstant β₀ δ ^ 2 *
          (J : ℝ) ^ 2 / (δ ^ 3 * N)) =
      16 * coercivityConstant β₀ δ * (sourceScaleCount β₀ δ : ℝ) ^ 2 *
        scaleGradientConstant β₀ δ ^ 2 / (δ ^ 3 * (N : ℝ) ^ 2) := by
  have hJr : (J : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hJ
  field_simp
  ring

theorem absorb_half {A E C : ℝ} (h : A ≤ C / 2 * E + (1 / 2) * A) :
    A ≤ C * E := by nlinarith

end PeriodicAttractiveLogGas.HeavyCoercivityConstants
