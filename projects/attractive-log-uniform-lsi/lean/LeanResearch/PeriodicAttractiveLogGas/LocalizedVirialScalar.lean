import LeanResearch.PeriodicAttractiveLogGas.HeavyScales

/-! Exact scalar arithmetic in the localized virial argument (source
1195–1338). The differential and pair-class estimates remain separate
obligations. In particular these coefficient lemmas do not assert a
generator inequality for an unconstructed observable. -/

noncomputable section

namespace PeriodicAttractiveLogGas.LocalizedVirialScalar

open HeavyScales

def insideCoefficient (β s : ℝ) : ℝ :=
  β * (1 + 8 * remainderGradientBound * s)

def annulusCoefficient (β K : ℝ) : ℝ :=
  224 + 160 * β * ConditionalLawEstimates.kernelConstant +
    64 * β * ConditionalLawEstimates.kernelConstant / K

def farCoefficient (β K : ℝ) : ℝ :=
  320 * β * GreenCovarianceBounds.hessianConstant / (K - 4) ^ 2

theorem insideCoefficient_nonneg {β s : ℝ} (hβ : 0 ≤ β) (hs : 0 ≤ s) :
    0 ≤ insideCoefficient β s := by
  have hCh := remainderGradientBound_nonneg
  unfold insideCoefficient
  positivity

theorem insideCoefficient_le {β β₀ s : ℝ} (hβ : β ≤ β₀) (hs : 0 ≤ s)
    (hsmall : 16 * β₀ * remainderGradientBound * s ≤ 4 - β₀) :
    insideCoefficient β s ≤ (4 + β₀) / 2 := by
  have hCh := remainderGradientBound_nonneg
  have h := mul_le_mul_of_nonneg_right hβ
    (show 0 ≤ 1 + 8 * remainderGradientBound * s by positivity)
  unfold insideCoefficient
  nlinarith

theorem annulus_add_inside_le {β β₀ s K : ℝ} (hβ : 0 ≤ β)
    (hβ₀ : β ≤ β₀) (hβ4 : β₀ < 4) (hs : 0 ≤ s) (hK : 8 ≤ K)
    (hsmall : 16 * β₀ * remainderGradientBound * s ≤ 4 - β₀) :
    annulusCoefficient β K + insideCoefficient β s ≤ virialConstant β₀ := by
  have hC := ConditionalLawEstimates.kernelConstant_pos
  have hKp : 0 < K := by linarith
  have htail : 64 * β * ConditionalLawEstimates.kernelConstant / K ≤
      8 * β * ConditionalLawEstimates.kernelConstant := by
    apply (div_le_iff₀ hKp).mpr
    nlinarith [mul_nonneg (show 0 ≤ 8 * β * ConditionalLawEstimates.kernelConstant by
      positivity) (show 0 ≤ K - 8 by linarith)]
  have hb := insideCoefficient_le hβ₀ hs hsmall
  have hmono := mul_le_mul_of_nonneg_right hβ₀ hC.le
  unfold annulusCoefficient virialConstant
  nlinarith

theorem next_coefficient_le {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) :
    162 * β * ConditionalLawEstimates.kernelConstant ≤ virialConstant β₀ := by
  have hC := ConditionalLawEstimates.kernelConstant_pos
  have hm := mul_le_mul_of_nonneg_right hβ₀ hC.le
  have hp : 0 ≤ β * ConditionalLawEstimates.kernelConstant := by positivity
  unfold virialConstant
  nlinarith

theorem farCoefficient_nonneg {β K : ℝ} (hβ : 0 ≤ β) : 0 ≤ farCoefficient β K := by
  have hC := GreenCovarianceBounds.hessianConstant_pos
  unfold farCoefficient
  positivity

theorem farCoefficient_mono {β β₀ K : ℝ} (hβ : β ≤ β₀) :
    farCoefficient β K ≤ farCoefficient β₀ K := by
  have hC := GreenCovarianceBounds.hessianConstant_pos
  unfold farCoefficient
  exact div_le_div_of_nonneg_right
    (by nlinarith [mul_le_mul_of_nonneg_right hβ hC.le]) (sq_nonneg _)

/-- The source large-mass branch: the sign of M-1 is used explicitly. -/
theorem large_mass_bracket {β β₀ s K M n₂ ann nx : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hβ4 : β₀ < 4) (hs : 0 ≤ s) (hK : 8 ≤ K)
    (hsmall : 16 * β₀ * remainderGradientBound * s ≤ 4 - β₀)
    (hM : 1 ≤ M) (hn₂ : 0 ≤ n₂) (hann : 0 ≤ ann) (hnx : 0 ≤ nx)
    (hcount : n₂ ≤ M + ann) :
    (4 - β₀) / 2 * (M - 1) - virialConstant β₀ * (ann + nx) -
        farCoefficient β₀ K * n₂ ≤
      4 * (M - 1) - insideCoefficient β s * (n₂ - 1) - annulusCoefficient β K * ann -
        162 * β * ConditionalLawEstimates.kernelConstant * nx - farCoefficient β K * n₂ := by
  have hb0 := insideCoefficient_nonneg hβ hs
  have hb := insideCoefficient_le hβ₀ hs hsmall
  have hab := mul_le_mul_of_nonneg_right
    (annulus_add_inside_le hβ hβ₀ hβ4 hs hK hsmall) hann
  have hnx' := mul_le_mul_of_nonneg_right (next_coefficient_le hβ hβ₀) hnx
  have hfar := mul_le_mul_of_nonneg_right (farCoefficient_mono (K := K) hβ₀) hn₂
  have hc := mul_le_mul_of_nonneg_left (sub_le_sub_right hcount 1) hb0
  have hm := mul_le_mul_of_nonneg_right
    (show (4 - β₀) / 2 ≤ 4 - insideCoefficient β s by linarith)
    (show 0 ≤ M - 1 by linarith)
  nlinarith

/-- When M<1 the nonnegative first Laplacian sum is retained. Reusing
the large-mass bound would reverse a coefficient comparison. -/
theorem small_mass_bracket {β β₀ s K M n₂ ann nx : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hβ4 : β₀ < 4) (hs : 0 ≤ s) (hK : 8 ≤ K)
    (hsmall : 16 * β₀ * remainderGradientBound * s ≤ 4 - β₀)
    (hM : M < 1) (hn₂ : 0 ≤ n₂) (hann : 0 ≤ ann) (hnx : 0 ≤ nx) :
    (4 - β₀) / 2 * (M - 1) - virialConstant β₀ * (ann + nx) -
        farCoefficient β₀ K * n₂ ≤
      insideCoefficient β s - (annulusCoefficient β K + insideCoefficient β s) * ann -
        162 * β * ConditionalLawEstimates.kernelConstant * nx - farCoefficient β K * n₂ := by
  have hb0 := insideCoefficient_nonneg hβ hs
  have hab := mul_le_mul_of_nonneg_right
    (annulus_add_inside_le hβ hβ₀ hβ4 hs hK hsmall) hann
  have hnx' := mul_le_mul_of_nonneg_right (next_coefficient_le hβ hβ₀) hnx
  have hfar := mul_le_mul_of_nonneg_right (farCoefficient_mono (K := K) hβ₀) hn₂
  have hm : (4 - β₀) / 2 * (M - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  nlinarith

/-- The exact two error estimates in separated positivity, including
the source constant 13/128. No pair-distance separation is assumed. -/
theorem separated_bracket {β₀ K M n₂ sh : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ4 : β₀ < 4) (hK : separationRadius β₀ ≤ K)
    (hM : 4 ≤ M) (hn₂ : 0 ≤ n₂) (hcount : n₂ ≤ M + sh)
    (hsh : sh < 2 * separationConstant β₀ * (4 - β₀) * M) :
    (4 - β₀) / 4 * M ≤
      (4 - β₀) / 2 * (M - 1) - virialConstant β₀ * sh - farCoefficient β₀ K * n₂ := by
  have hM0 : 0 ≤ M := by linarith
  have hc0 : 0 < virialConstant β₀ := lt_of_lt_of_le (by norm_num) (virialConstant_ge hβ₀)
  have hc := mul_le_mul_of_nonneg_left hsh.le hc0.le
  have he : virialConstant β₀ *
      (2 * separationConstant β₀ * (4 - β₀) * M) = (4 - β₀) * M / 32 := by
    unfold separationConstant
    field_simp
    ring
  rw [he] at hc
  have hfrac := mul_le_mul_of_nonneg_right (separation_fraction_lt hβ₀).le hM0
  have hn₂' : n₂ ≤ 9 * M / 8 := by nlinarith
  have hf := mul_le_mul_of_nonneg_right (far_error_bound hβ₀ hβ4 hK) hn₂
  change farCoefficient β₀ K * n₂ ≤ (4 - β₀) / 16 * n₂ at hf
  have hf' := mul_le_mul_of_nonneg_left hn₂' (show 0 ≤ (4 - β₀) / 16 by linarith)
  have hm : (M - 1) / 2 - 13 * M / 128 ≥ M / 4 := by linarith
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 4 - β₀ by linarith)
  nlinarith

/-- Multiplication by the actual unscaled M/N factor in the generator
estimate gives precisely the source positive lower bound. -/
theorem separated_positive_scalar {N : ℕ} {β₀ K M n₂ sh L : ℝ}
    (hN : 0 < N) (hβ₀ : 0 ≤ β₀) (hβ4 : β₀ < 4) (hK : separationRadius β₀ ≤ K)
    (hM : 4 ≤ M) (hn₂ : 0 ≤ n₂) (hcount : n₂ ≤ M + sh)
    (hsh : sh < 2 * separationConstant β₀ * (4 - β₀) * M)
    (hvirial : M / N * ((4 - β₀) / 2 * (M - 1) - virialConstant β₀ * sh -
      farCoefficient β₀ K * n₂) ≤ L) :
    (4 - β₀) / (4 * N) * M ^ 2 ≤ L := by
  have h := mul_le_mul_of_nonneg_left (separated_bracket hβ₀ hβ4 hK hM hn₂ hcount hsh)
    (show 0 ≤ M / (N : ℝ) by positivity)
  calc
    _ = M / N * ((4 - β₀) / 4 * M) := by ring
    _ ≤ _ := h.trans hvirial

/-- Square completion for the actual choice gamma=ell/(2*g). -/
theorem exponential_generator_rate {ell g q r : ℝ} (hell : 0 < ell) (hg : 0 < g)
    (hq : ell ≤ q) (hr : r ≤ g) :
    ell ^ 2 / (4 * g) ≤ ell / (2 * g) * q - (ell / (2 * g)) ^ 2 * r := by
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ ell / (2 * g) by positivity)
  have hr' := mul_le_mul_of_nonneg_left hr (sq_nonneg (ell / (2 * g)))
  have he : ell / (2 * g) * ell - (ell / (2 * g)) ^ 2 * g = ell ^ 2 / (4 * g) := by
    field_simp
    ring
  linarith

/-- Exact reciprocal rate in source Proposition separated-coercivity. -/
theorem separated_coercivity_constant {N : ℕ} {β₀ δ s : ℝ}
    (hN : 0 < N) (hβ : β₀ < 4) (hδ : 0 < δ) (hs : 0 < s) :
    1 / (((4 - β₀) * δ ^ 2 * N / 4) ^ 2 / (4 * (6400 * N * s ^ 2))) =
      409600 * s ^ 2 / ((4 - β₀) ^ 2 * δ ^ 4 * N) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hgap : 4 - β₀ ≠ 0 := by linarith
  field_simp
  ring

end PeriodicAttractiveLogGas.LocalizedVirialScalar
