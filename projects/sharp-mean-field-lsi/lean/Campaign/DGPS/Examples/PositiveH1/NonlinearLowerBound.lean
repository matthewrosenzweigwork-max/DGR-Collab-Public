import DGPS.Examples.PositiveH1.Dissipation
import DGPS.Analysis.CircleLSI
import DGPS.Variational.SpeciesInclusion

/-!
# H1012: uniform nonlinear lower bound

For every finite species family, with `a0 = 4π²`, `I_s = 4 ∫ |∇u_s|²` and `H_s = H(ρ_s | m)`,
`D_θ − 2 a0 G_θ = ∑ θ_s (I_s − 2 a0 H_s) + κ ∑_{n ≥ 2} [2 (2πn)² − a0] a_n |ρ̄^(n)|²
  + κ² ∫ ρ̄ |R′ * ρ̄|² ≥ 0` (with `D_θ`, `G_θ` the exact real expansions of H1011), hence
`r_ms ≥ a0`, `r_k ≥ a0` for every `k` and `r_* ≥ a0`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DGPS.Examples.PositiveH1.Nonlinear
open DGPS DGPS.Examples.PositiveH1.Fourier DGPS.Examples.PositiveH1.Model
  DGPS.Examples.PositiveH1.CrossTerm

theorem h1012_term_nonneg (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ (2 * (2 * Real.pi * n) ^ 2 - 4 * Real.pi ^ 2) * a n * x := by
  by_cases hn : n < 2
  · rw [a_zero_of_lt hn]; simp
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast (not_lt.mp hn)
    have hp := Real.pi_gt_three
    have h1 : (1 : ℝ) ≤ n ^ 2 := by nlinarith
    have : 0 ≤ 2 * (2 * Real.pi * n) ^ 2 - 4 * Real.pi ^ 2 := by
      have : (2 * Real.pi * n) ^ 2 = 4 * Real.pi ^ 2 * n ^ 2 := by ring
      rw [this]; nlinarith [sq_nonneg Real.pi]
    exact mul_nonneg (mul_nonneg this (a_nonneg n)) hx

/-- **H1012.** Uniform nonlinear lower bound with `a0 = 4π²`: for every finite species family the
exact expansion of `D_θ − 2 a0 G_θ` (H1011 real forms) is a sum of nonnegative terms; consequently
`r_ms`, every `r_k` (at most `k` species) and `r_*` are at least `a0`. -/
theorem uniform_nonlinear_lower_bound :
    (∀ F : SpeciesFamily 1,
      (∑ s, F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1)
          + 2 * kappa * Q (barycenter F)
          + kappa ^ 2 * ∫ x, (barycenter F).density x * (conv dR (barycenter F).density x) ^ 2
            ∂haar 1)
        - 2 * (4 * Real.pi ^ 2) *
          (∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s)) (haar 1)).toReal
            + kappa / 2 * P (barycenter F))
        = ∑ s, F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1
            - 2 * (4 * Real.pi ^ 2) *
              (relativeEntropy (densityMeasure (F.density s)) (haar 1)).toReal)
          + kappa * ∑' n : ℕ, (2 * (2 * Real.pi * n) ^ 2 - 4 * Real.pi ^ 2) * a n *
              ‖fourierCoeff (barycenter F).density (freq n)‖ ^ 2
          + kappa ^ 2 * ∫ x, (barycenter F).density x * (conv dR (barycenter F).density x) ^ 2
            ∂haar 1 ∧
      0 ≤ ∑ s, F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1
            - 2 * (4 * Real.pi ^ 2) *
              (relativeEntropy (densityMeasure (F.density s)) (haar 1)).toReal)
          + kappa * ∑' n : ℕ, (2 * (2 * Real.pi * n) ^ 2 - 4 * Real.pi ^ 2) * a n *
              ‖fourierCoeff (barycenter F).density (freq n)‖ ^ 2
          + kappa ^ 2 * ∫ x, (barycenter F).density x * (conv dR (barycenter F).density x) ^ 2
            ∂haar 1) ∧
    (∀ b : AbsoluteDrift positiveH1,
      ENNReal.ofReal (4 * Real.pi ^ 2) ≤ speciesRate positiveH1 b ∧
      (∀ k : ℕ, ENNReal.ofReal (4 * Real.pi ^ 2) ≤ speciesRateAtMost positiveH1 b k) ∧
      ENNReal.ofReal (4 * Real.pi ^ 2) ≤ scalarRate positiveH1 b) := by
  have hmain : ∀ F : SpeciesFamily 1,
      (∑ s, F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1)
          + 2 * kappa * Q (barycenter F)
          + kappa ^ 2 * ∫ x, (barycenter F).density x * (conv dR (barycenter F).density x) ^ 2
            ∂haar 1)
        - 2 * (4 * Real.pi ^ 2) *
          (∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s)) (haar 1)).toReal
            + kappa / 2 * P (barycenter F))
        = ∑ s, F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1
            - 2 * (4 * Real.pi ^ 2) *
              (relativeEntropy (densityMeasure (F.density s)) (haar 1)).toReal)
          + kappa * ∑' n : ℕ, (2 * (2 * Real.pi * n) ^ 2 - 4 * Real.pi ^ 2) * a n *
              ‖fourierCoeff (barycenter F).density (freq n)‖ ^ 2
          + kappa ^ 2 * ∫ x, (barycenter F).density x * (conv dR (barycenter F).density x) ^ 2
            ∂haar 1 ∧
      0 ≤ ∑ s, F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1
            - 2 * (4 * Real.pi ^ 2) *
              (relativeEntropy (densityMeasure (F.density s)) (haar 1)).toReal)
          + kappa * ∑' n : ℕ, (2 * (2 * Real.pi * n) ^ 2 - 4 * Real.pi ^ 2) * a n *
              ‖fourierCoeff (barycenter F).density (freq n)‖ ^ 2
          + kappa ^ 2 * ∫ x, (barycenter F).density x * (conv dR (barycenter F).density x) ^ 2
            ∂haar 1 := by
    intro F
    obtain ⟨hP, hQ, -⟩ := weak_fourier_cross_term (barycenter F)
    have hS : ∑' n : ℕ, (2 * (2 * Real.pi * n) ^ 2 - 4 * Real.pi ^ 2) * a n *
        ‖fourierCoeff (barycenter F).density (freq n)‖ ^ 2
        = 2 * Q (barycenter F) - 4 * Real.pi ^ 2 * P (barycenter F) := by
      have e : (fun n : ℕ => (2 * (2 * Real.pi * n) ^ 2 - 4 * Real.pi ^ 2) * a n *
          ‖fourierCoeff (barycenter F).density (freq n)‖ ^ 2)
          = fun n : ℕ => 2 * ((2 * Real.pi * n) ^ 2 * a n *
              ‖fourierCoeff (barycenter F).density (freq n)‖ ^ 2)
            - 4 * Real.pi ^ 2 * (a n * ‖fourierCoeff (barycenter F).density (freq n)‖ ^ 2) := by
        funext n; ring
      rw [e, Summable.tsum_sub (hQ.mul_left 2) (hP.mul_left _), tsum_mul_left, tsum_mul_left]
      rfl
    have hsp : ∑ s, F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1
            - 2 * (4 * Real.pi ^ 2) *
              (relativeEntropy (densityMeasure (F.density s)) (haar 1)).toReal)
        = ∑ s, F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1)
          - 2 * (4 * Real.pi ^ 2) *
            ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s)) (haar 1)).toReal := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    refine ⟨?_, ?_⟩
    · rw [hsp, hS]; ring
    · refine add_nonneg (add_nonneg ?_ ?_) ?_
      · refine Finset.sum_nonneg fun s _ => mul_nonneg (F.weight_nonneg s) ?_
        obtain ⟨-, -, h⟩ := haar_circle_lsi (F.density s)
        rw [circleEntropy_eq_relativeEntropy] at h
        have : 4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1
            = Analysis.circleFisherInformation (F.density s) := rfl
        linarith
      · refine mul_nonneg (by unfold kappa; norm_num) (tsum_nonneg fun n => ?_)
        exact h1012_term_nonneg n _ (sq_nonneg _)
      · refine mul_nonneg (sq_nonneg _) (integral_nonneg fun x => ?_)
        exact mul_nonneg ((barycenter F).density_nonneg x) (sq_nonneg _)
  refine ⟨hmain, fun b => ?_⟩
  have hms : ENNReal.ofReal (4 * Real.pi ^ 2) ≤ speciesRate positiveH1 b := by
    refine le_iInf fun F => ?_
    obtain ⟨-, -, hD⟩ := (exact_scalar_and_species_dissipation_expansion.2 b F.1)
    have hG := (exact_scalar_and_species_dissipation_expansion.2 b F.1).1
    have hm := (hmain F.1).2
    have h1 := (hmain F.1).1
    have hpos : (0 : ℝ) < (speciesGap positiveH1 F.1 : ℝ) := by exact_mod_cast F.2
    unfold speciesQuotient
    rw [hD]
    have hne : (2 * (speciesGap positiveH1 F.1 : ℝ≥0∞)) ≠ 0 := by
      have := F.2
      simpa using this.ne'
    rw [ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl (ENNReal.mul_ne_top (by simp)
      ENNReal.coe_ne_top))]
    have e : ENNReal.ofReal (4 * Real.pi ^ 2) * (2 * (speciesGap positiveH1 F.1 : ℝ≥0∞))
        = ENNReal.ofReal (4 * Real.pi ^ 2 * (2 * (speciesGap positiveH1 F.1 : ℝ))) := by
      have h2 : ENNReal.ofReal (2 * (speciesGap positiveH1 F.1 : ℝ))
          = 2 * (speciesGap positiveH1 F.1 : ℝ≥0∞) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_coe_nnreal]
        simp
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2), h2]
    rw [e]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hG]
    linarith
  refine ⟨hms, fun k => ?_, ?_⟩
  · exact hms.trans (speciesRate_le_speciesRateAtMost _ b k)
  · exact hms.trans (speciesRate_le_scalarRate _ b)

end DGPS.Examples.PositiveH1.Nonlinear
