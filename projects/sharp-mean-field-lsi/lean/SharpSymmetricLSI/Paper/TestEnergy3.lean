import SharpSymmetricLSI.Paper.ULimit3
import SharpSymmetricLSI.Paper.ULimit1
import SharpSymmetricLSI.Paper.CondForce1

/-!
# R33 groundwork: the `L²` law of large numbers for empirical averages

`∫ (N⁻¹∑_l g(X_l) - ∫g dμ)² dμ^{⊗N} ≤ (2B)²/N` for `|g| ≤ B` (used for the empirical mobility
`A_{N,ij}` of (8.13)).
-/

open MeasureTheory Filter Topology Real

namespace SharpLSI

variable {d : ℕ}

theorem integral_avg_sub_sq {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {g : Torus d → ℝ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) {N : ℕ} (hN : 1 ≤ N) :
    ∫ X, ((N : ℝ)⁻¹ * ∑ l, g (X l) - ∫ x, g x ∂μ) ^ 2 ∂Measure.pi (fun _ : Fin N => μ) ≤
      (2 * B) ^ 2 / N := by
  set m := ∫ x, g x ∂μ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hm : |m| ≤ B := abs_integral_le_of_bdd hB
  have hF : ∀ x, |g x - m| ≤ 2 * B := fun x => by
    have := hB x
    calc |g x - m| ≤ |g x| + |m| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  have hrw : ∀ X : Fin N → Torus d, (N : ℝ)⁻¹ * ∑ l, g (X l) - m =
      ∑ l, (N : ℝ)⁻¹ * (g (X l) - m) := fun X => by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_sub, ← mul_assoc, inv_mul_cancel₀ hNr.ne', one_mul]
  simp_rw [hrw]
  have hmeas : ∀ l : Fin N, Measurable fun X : Fin N → Torus d => g (X l) - m := fun l =>
    (hg.comp (measurable_pi_apply l)).sub_const _
  have hL2 : ∀ l : Fin N, MemLp (fun X : Fin N → Torus d => g (X l) - m) 2
      (Measure.pi fun _ : Fin N => μ) := fun l =>
    MemLp.of_bound (hmeas l).aestronglyMeasurable (2 * B)
      (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hF _)
  rw [integral_sq_sum_orth Finset.univ (fun _ => (N : ℝ)⁻¹) _ hL2]
  · have hone : ∀ l : Fin N, ∫ X, (g (X l) - m) ^ 2 ∂(Measure.pi fun _ : Fin N => μ) ≤
        (2 * B) ^ 2 := fun l =>
      calc _ ≤ ∫ _X, (2 * B) ^ 2 ∂(Measure.pi fun _ : Fin N => μ) :=
            integral_mono_of_nonneg (Eventually.of_forall fun X => sq_nonneg _)
              (integrable_const _) (Eventually.of_forall fun X => by
                rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hF _) 2)
        _ = (2 * B) ^ 2 := by simp
    calc ∑ l : Fin N, ((N : ℝ)⁻¹) ^ 2 * ∫ X, (g (X l) - m) ^ 2 ∂(Measure.pi fun _ : Fin N => μ)
        ≤ ∑ _l : Fin N, ((N : ℝ)⁻¹) ^ 2 * (2 * B) ^ 2 :=
          Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hone l) (sq_nonneg _)
      _ = (2 * B) ^ 2 / N := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  · intro a _ b _ hab
    have hmap := map_pair_pi_gen (μ := μ) (N := N) hab
    have hint : Integrable (fun q : Torus d × Torus d => (g q.1 - m) * (g q.2 - m)) (μ.prod μ) :=
      integrable_of_bdd (((hg.comp measurable_fst).sub_const _).mul
        ((hg.comp measurable_snd).sub_const _)) (C := (2 * B) * (2 * B)) fun q => by
          rw [abs_mul]; exact mul_le_mul (hF _) (hF _) (abs_nonneg _) (by linarith [hF q.1, abs_nonneg (g q.1 - m)])
    have h1 : ∫ X, (g (X a) - m) * (g (X b) - m) ∂(Measure.pi fun _ : Fin N => μ) =
        ∫ q, (g q.1 - m) * (g q.2 - m) ∂(μ.prod μ) := by
      rw [← hmap, integral_map (by fun_prop) (hmap ▸ hint.aestronglyMeasurable)]
    rw [h1, integral_prod_mul (f := fun x => g x - m) (g := fun y => g y - m)]
    have h0 : ∫ x, (g x - m) ∂μ = 0 := by
      rw [integral_sub (integrable_of_bdd hg hB) (integrable_const _), integral_const,
        probReal_univ, one_smul, sub_self]
    rw [h0, zero_mul]

end SharpLSI
