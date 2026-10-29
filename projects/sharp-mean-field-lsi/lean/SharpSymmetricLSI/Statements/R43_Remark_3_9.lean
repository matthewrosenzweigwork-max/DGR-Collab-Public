import SharpSymmetricLSI.Defs.D12_Cosine
import SharpSymmetricLSI.Paper.CosineRemark39
import SharpSymmetricLSI.Paper.CosineRothaus

/-!
# R43: Remark 3.9 (`rem:cosine-labeled-constants`)

Manuscript Remark 3.9:
* For `N ≥ 2κe^{2κ}`: `λ^all_{N,κ} ≥ ae^{-2κ}/2` and `r^all_{N,κ} ≥ a/(2 + (2κ+8)e^{2κ})`.
* Rothaus variant: `r^all_{N,κ} ≥ 2aλ^all_{N,κ}/(2λ^all_{N,κ} + (κ+2)a)`, hence
  `r^all_{N,κ} ≥ a/(1 + (κ+2)e^{2κ})` for `N ≥ 2κe^{2κ}`.
* For `κ ≥ 2` and `N ≥ 2` no diagonal `D` makes `M + D`, `M = (κ/N) 𝟙𝟙ᵀ`, positive definite with
  largest eigenvalue `< 2` (encoded: `M + D` and `2I - (M + D)` positive definite).
That [BB, Theorem 1] applies for `κ < 2` is a documented remark, not a Lean statement.
-/

open Matrix
open scoped ENNReal

namespace SharpLSI

/-- Remark 3.9: explicit constants for `N ≥ 2κe^{2κ}`. -/
theorem cosine_labeled_constants {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N)
    (hNκ : 2 * κ * Real.exp (2 * κ) ≤ N) :
    ENNReal.ofReal (aCos * Real.exp (-2 * κ) / 2) ≤ lamAll cosV (cosW κ) N ∧
      ENNReal.ofReal (aCos / (2 + (2 * κ + 8) * Real.exp (2 * κ))) ≤ rAll cosV (cosW κ) N := by
  exact cosine_labeled_constants_aux hκ hN hNκ

/-- Remark 3.9: the Rothaus variant. -/
theorem cosine_labeled_lsi_rothaus {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) :
    2 * ENNReal.ofReal aCos * lamAll cosV (cosW κ) N /
        (2 * lamAll cosV (cosW κ) N + ENNReal.ofReal ((κ + 2) * aCos)) ≤
      rAll cosV (cosW κ) N ∧
    (2 * κ * Real.exp (2 * κ) ≤ N →
      ENNReal.ofReal (aCos / (1 + (κ + 2) * Real.exp (2 * κ))) ≤ rAll cosV (cosW κ) N) := by
  exact cosine_labeled_lsi_rothaus_aux hκ hN

/-- Remark 3.9: the hypothesis of [BB, Theorem 1] fails for `κ ≥ 2`, `N ≥ 2`. -/
theorem bb_hypothesis_fails {κ : ℝ} (hκ : 2 ≤ κ) {N : ℕ} (hN : 2 ≤ N) :
    ¬ ∃ δ : Fin N → ℝ,
      ((κ / N) • (Matrix.of fun _ _ => (1 : ℝ)) + Matrix.diagonal δ).PosDef ∧
      ((2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ) -
        ((κ / N) • (Matrix.of fun _ _ => (1 : ℝ)) + Matrix.diagonal δ)).PosDef := by
  rintro ⟨δ, hA, hB⟩
  set A := (κ / N) • (Matrix.of fun _ _ => (1 : ℝ)) + Matrix.diagonal δ with hAdef
  have hmul : ∀ x : Fin N → ℝ, A *ᵥ x = fun i => κ / N * ∑ j, x j + δ i * x i := by
    intro x; ext i
    simp [hAdef, mulVec, dotProduct, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
      diagonal_apply]
  have hQ : ∀ x : Fin N → ℝ, star x ⬝ᵥ (A *ᵥ x) =
      κ / N * (∑ i, x i) ^ 2 + ∑ i, δ i * x i ^ 2 := by
    intro x
    rw [hmul, star_trivial]
    simp only [dotProduct, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.sum_mul, sq]; ring
    · apply Finset.sum_congr rfl; intro i _; ring
  have hQ2 : ∀ x : Fin N → ℝ,
      star x ⬝ᵥ (((2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ) - A) *ᵥ x) =
        2 * ∑ i, x i ^ 2 - (κ / N * (∑ i, x i) ^ 2 + ∑ i, δ i * x i ^ 2) := by
    intro x
    rw [Matrix.sub_mulVec, dotProduct_sub, hQ, Matrix.smul_mulVec, Matrix.one_mulVec,
      star_trivial, dotProduct_smul, smul_eq_mul]
    congr 2
    simp [dotProduct, sq]
  -- `δ i + δ j > 0` for `i ≠ j`
  have hpair : ∀ i j : Fin N, i ≠ j → 0 < δ i + δ j := by
    intro i j hij
    set x : Fin N → ℝ := Pi.single i 1 - Pi.single j 1
    have hx : x ≠ 0 := by
      intro h
      have := congrFun h i
      simp [x, hij] at this
    have := hA.dotProduct_mulVec_pos hx
    rw [hQ] at this
    have hs : ∑ k, x k = 0 := by simp [x, Finset.sum_sub_distrib]
    have hd : ∑ k, δ k * x k ^ 2 = δ i + δ j := by
      have : ∀ k, δ k * x k ^ 2 = (Pi.single i (δ i) : Fin N → ℝ) k + (Pi.single j (δ j) : Fin N → ℝ) k := by
        intro k
        by_cases hki : k = i
        · subst hki; simp [x, hij]
        · by_cases hkj : k = j
          · subst hkj; simp [x, hki]
          · simp [x, hki, hkj]
      simp_rw [this, Finset.sum_add_distrib]; simp
    rw [hs, hd] at this; simpa using this
  -- `∑ δ < (2 - κ) N`
  have hone : ∑ i, δ i < (2 - κ) * N := by
    have hx : (fun _ => (1 : ℝ)) ≠ (0 : Fin N → ℝ) := by
      intro h
      have := congrFun h ⟨0, by omega⟩
      simp at this
    have := hB.dotProduct_mulVec_pos hx
    rw [hQ2] at this
    have hN0 : (0 : ℝ) < N := by positivity
    simp only [one_pow, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at this
    have : κ / N * (N : ℝ) ^ 2 = κ * N := by field_simp
    nlinarith
  -- summing the pairs: `2 (N - 1) ∑ δ > 0`
  have hsum : 0 < ∑ i, ∑ j ∈ Finset.univ.erase i, (δ i + δ j) := by
    apply Finset.sum_pos
    · intro i _
      apply Finset.sum_pos
      · intro j hj; exact hpair i j (Finset.ne_of_mem_erase hj).symm
      · have : 1 < (Finset.univ : Finset (Fin N)).card := by simp; omega
        obtain ⟨a, ha, hai⟩ := Finset.exists_mem_ne this i
        exact ⟨a, Finset.mem_erase.mpr ⟨hai, ha⟩⟩
    · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩
  have hcalc : ∑ i, ∑ j ∈ Finset.univ.erase i, (δ i + δ j) = 2 * ((N : ℝ) - 1) * ∑ i, δ i := by
    have : ∀ i, ∑ j ∈ Finset.univ.erase i, (δ i + δ j) =
        ((N : ℝ) - 1) * δ i + (∑ j, δ j - δ i) := by
      intro i
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.sum_erase_eq_sub (Finset.mem_univ _)]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Nat.cast_sub (by omega)]; simp
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hcalc] at hsum
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hpos : 0 < ∑ i, δ i := by
    by_contra h; push Not at h; nlinarith
  have : (2 - κ) * (N : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

end SharpLSI
