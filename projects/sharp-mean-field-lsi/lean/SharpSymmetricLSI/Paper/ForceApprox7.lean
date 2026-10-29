import SharpSymmetricLSI.Paper.ForceApprox5

/-!
# R31 groundwork: exponential moments of particle force sums (the proof of (5.13), generalized)

For measurable `c` with `|c| ≤ M`, `∫ c(x,y) dμ(y) = 0` for every `x`, and `|c_Δ| ≤ C_Δ`:
`∫ exp(a₀ ∑ᵢ |N⁻¹(∑_{l≠i} c(Xᵢ,X_l) + c_Δ(Xᵢ))|²) dμ^{⊗N} ≤ e^{2a₀dC_Δ²} · gaussSqConst`,
`a₀ = 1/(8d(M²+1))`, uniformly in `N`.
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

theorem exp_moment_forceSum (hd : 1 ≤ d) {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (n : ℕ)
    {c : Torus d → Torus d → Fin d → ℝ} {cΔ : Torus d → Fin d → ℝ}
    (hcm : ∀ k, Measurable (Function.uncurry fun x y => c x y k)) {M CΔ : ℝ}
    (hcb : ∀ x y k, |c x y k| ≤ M) (hΔb : ∀ x k, |cΔ x k| ≤ CΔ)
    (hcent : ∀ x k, ∫ y, c x y k ∂μ = 0) :
    ∫⁻ X, ENNReal.ofReal (exp ((1 / (8 * d * (M ^ 2 + 1))) * ∑ i, ∑ k, ((((n + 1 : ℕ) : ℝ))⁻¹ *
        (∑ l ∈ Finset.univ.erase i, c (X i) (X l) k + cΔ (X i) k)) ^ 2))
        ∂(Measure.pi fun _ : Fin (n + 1) => μ) ≤
      ENNReal.ofReal (exp (2 * (1 / (8 * d * (M ^ 2 + 1))) * d * CΔ ^ 2) * gaussSqConst.toReal) := by
  set a₀ := 1 / (8 * d * (M ^ 2 + 1)) with ha₀
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ha₀0 : 0 < a₀ := by rw [ha₀]; positivity
  have hc0 : 0 ≤ 2 * a₀ * d := by positivity
  have hcM : 2 * a₀ * d * M ^ 2 ≤ 1 / 4 := by
    rw [ha₀]
    have h1 : 0 < M ^ 2 + 1 := by positivity
    rw [show 2 * (1 / (8 * d * (M ^ 2 + 1))) * d * M ^ 2 = M ^ 2 / (4 * (M ^ 2 + 1)) by
      field_simp; ring]
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hSm : ∀ q : Fin (n + 1) × Fin d, Measurable fun X : Fin (n + 1) → Torus d =>
      ENNReal.ofReal (exp (2 * a₀ * d * (∑ l ∈ Finset.univ.erase q.1, c (X q.1) (X l) q.2) ^ 2 /
          ((n + 1 : ℕ) : ℝ))) := fun q =>
    measurable_exp_Sik (F := fun x y => c x y q.2) (hcm q.2) q.1 _ _
  have hw1 : ∑ _q : Fin (n + 1) × Fin d, ENNReal.ofReal (1 / (((n + 1 : ℕ) : ℝ) * d)) = 1 := by
    have hr : ∑ _q : Fin (n + 1) × Fin d, (1 / (((n + 1 : ℕ) : ℝ) * d)) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      field_simp
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), hr, ENNReal.ofReal_one]
  calc ∫⁻ X, ENNReal.ofReal (exp (a₀ * ∑ i, ∑ k, ((((n + 1 : ℕ) : ℝ))⁻¹ *
        (∑ l ∈ Finset.univ.erase i, c (X i) (X l) k + cΔ (X i) k)) ^ 2))
        ∂(Measure.pi fun _ : Fin (n + 1) => μ)
      ≤ ∫⁻ X, ENNReal.ofReal (exp (2 * a₀ * d * CΔ ^ 2)) * ∑ q : Fin (n + 1) × Fin d,
          ENNReal.ofReal (1 / (((n + 1 : ℕ) : ℝ) * d)) *
          ENNReal.ofReal (exp (2 * a₀ * d * (∑ l ∈ Finset.univ.erase q.1, c (X q.1) (X l) q.2) ^ 2 /
              ((n + 1 : ℕ) : ℝ))) ∂(Measure.pi fun _ : Fin (n + 1) => μ) := by
        refine lintegral_mono fun X => ?_
        have hX : ∑ i, ∑ k, ((((n + 1 : ℕ) : ℝ))⁻¹ *
            (∑ l ∈ Finset.univ.erase i, c (X i) (X l) k + cΔ (X i) k)) ^ 2 =
            ∑ i, ∑ k, ((((n + 1 : ℕ) : ℝ))⁻¹ *
            (∑ l ∈ Finset.univ.erase i, c (X i) (X l) k + -(-cΔ (X i) k))) ^ 2 := by
          simp only [neg_neg]
        rw [hX]
        refine (ENNReal.ofReal_le_ofReal (exp_gradSq_le hd ha₀0.le _ (fun i k => -cΔ (X i) k)
          fun i k => by rw [abs_neg]; exact hΔb (X i) k)).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul (exp_pos _).le, ENNReal.ofReal_sum_of_nonneg
          (fun q _ => by positivity)]
        congr 1
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (exp (2 * a₀ * d * CΔ ^ 2)) * ∑ q : Fin (n + 1) × Fin d,
          ENNReal.ofReal (1 / (((n + 1 : ℕ) : ℝ) * d)) *
          ∫⁻ X, ENNReal.ofReal (exp (2 * a₀ * d * (∑ l ∈ Finset.univ.erase q.1,
            c (X q.1) (X l) q.2) ^ 2 / ((n + 1 : ℕ) : ℝ))) ∂(Measure.pi fun _ : Fin (n + 1) => μ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finset_sum' _ fun q _ =>
          ((hSm q).const_mul _).aemeasurable]
        congr 1
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (exp (2 * a₀ * d * CΔ ^ 2)) * ∑ _q : Fin (n + 1) × Fin d,
          ENNReal.ofReal (1 / (((n + 1 : ℕ) : ℝ) * d)) * gaussSqConst := by
        gcongr with q
        exact lintegral_exp_Sik μ n q.1 (hcm q.2) (fun x y => hcb x y q.2)
          (fun x => hcent x q.2) hc0 hcM
    _ = ENNReal.ofReal (exp (2 * a₀ * d * CΔ ^ 2) * gaussSqConst.toReal) := by
        rw [← Finset.sum_mul, hw1, one_mul, ENNReal.ofReal_mul (exp_pos _).le,
          ENNReal.ofReal_toReal gaussSqConst_ne_top]

end SharpLSI
