import Mathlib

/-!
# Compactness in `ℓ²` under an energy bound (Phase 3, lane D; R29)

If `∑ xₖ(α)² ≤ B` and `∑ Λ_α xₖ(α)² ≤ B` with `{Λ ≤ L}` finite for every `L`, a subsequence
converges in `ℓ²` (tightness from the energy, pointwise convergence by compactness).
-/

noncomputable section
open Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {A : Type*} [Countable A]

theorem tsum_ofReal_le_of_sum_le {g : A → ℝ} (hg : ∀ a, 0 ≤ g a) {B : ℝ}
    (h : ∀ S : Finset A, ∑ a ∈ S, g a ≤ B) : ∑' a, ENNReal.ofReal (g a) ≤ ENNReal.ofReal B := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => hg a]
  exact ENNReal.ofReal_le_ofReal (h S)

/-- **`ℓ²` compactness.** -/
theorem exists_l2_subseq {x : ℕ → A → ℝ} {Λ : A → ℝ} (hΛ : ∀ a, 0 ≤ Λ a)
    (hfin : ∀ L, {a | Λ a ≤ L}.Finite) {B : ℝ} (hB : 0 ≤ B)
    (h1 : ∀ k (S : Finset A), ∑ a ∈ S, x k a ^ 2 ≤ B)
    (h2 : ∀ k (S : Finset A), ∑ a ∈ S, Λ a * x k a ^ 2 ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x0 : A → ℝ, (∀ S : Finset A, ∑ a ∈ S, x0 a ^ 2 ≤ B) ∧
      (∀ S : Finset A, ∑ a ∈ S, Λ a * x0 a ^ 2 ≤ B) ∧
      (∀ a, Tendsto (fun k => x (φ k) a) atTop (𝓝 (x0 a))) ∧
      Tendsto (fun k => ∑' a, ENNReal.ofReal ((x (φ k) a - x0 a) ^ 2)) atTop (𝓝 0) := by
  -- pointwise convergence along a subsequence
  set K : Set (A → ℝ) := Set.univ.pi fun _ => Set.Icc (-Real.sqrt B) (Real.sqrt B)
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ k, x k ∈ K := fun k a _ => by
    have := h1 k {a}
    rw [Finset.sum_singleton] at this
    exact abs_le.mp (Real.abs_le_sqrt this)
  obtain ⟨x0, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hpt : ∀ a, Tendsto (fun k => x (φ k) a) atTop (𝓝 (x0 a)) := fun a =>
    (continuous_apply a).continuousAt.tendsto.comp hlim
  have hx01 : ∀ S : Finset A, ∑ a ∈ S, x0 a ^ 2 ≤ B := fun S =>
    le_of_tendsto' (tendsto_finsetSum _ fun a _ => (hpt a).pow 2) fun k => h1 (φ k) S
  have hx02 : ∀ S : Finset A, ∑ a ∈ S, Λ a * x0 a ^ 2 ≤ B := fun S =>
    le_of_tendsto' (tendsto_finsetSum _ fun a _ => ((hpt a).pow 2).const_mul _) fun k =>
      h2 (φ k) S
  refine ⟨φ, hφ, x0, hx01, hx02, hpt, ?_⟩
  -- tightness
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ0, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal (2 * δ) ≤ ε := by
    rcases eq_or_ne ε ⊤ with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · refine ⟨ε.toReal / 2, by have := ENNReal.toReal_pos hε.ne' h; positivity, ?_⟩
      rw [show 2 * (ε.toReal / 2) = ε.toReal by ring, ENNReal.ofReal_toReal h]
  set L : ℝ := 4 * B / δ + 1
  have hL : 0 < L := by positivity
  set F := (hfin L).toFinset
  have hF : ∀ a, a ∉ F → L < Λ a := fun a ha => by
    simp only [F, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_le] at ha; exact ha
  -- the head
  have hhead : Tendsto (fun k => ∑ a ∈ F, (x (φ k) a - x0 a) ^ 2) atTop (𝓝 0) := by
    have := tendsto_finsetSum F fun a _ =>
      ((hpt a).sub (tendsto_const_nhds (x := x0 a))).pow 2
    simpa using this
  filter_upwards [(tendsto_order.mp hhead).2 δ hδ0] with k hk
  -- split the sum
  have hsplit : ∑' a, ENNReal.ofReal ((x (φ k) a - x0 a) ^ 2) ≤
      ENNReal.ofReal (∑ a ∈ F, (x (φ k) a - x0 a) ^ 2) +
        ∑' a, ENNReal.ofReal (2 / L * (Λ a * x (φ k) a ^ 2 + Λ a * x0 a ^ 2)) := by
    calc ∑' a, ENNReal.ofReal ((x (φ k) a - x0 a) ^ 2)
        ≤ ∑' a, ((F : Set A).indicator (fun a => ENNReal.ofReal ((x (φ k) a - x0 a) ^ 2)) a +
            ENNReal.ofReal (2 / L * (Λ a * x (φ k) a ^ 2 + Λ a * x0 a ^ 2))) := by
          refine ENNReal.tsum_le_tsum fun a => ?_
          by_cases ha : a ∈ F
          · rw [Set.indicator_of_mem (Finset.mem_coe.mpr ha)]; exact le_self_add
          · rw [Set.indicator_of_notMem (fun h => ha (Finset.mem_coe.mp h)), zero_add]
            refine ENNReal.ofReal_le_ofReal ?_
            have hΛa := hF a ha
            have h2' : (x (φ k) a - x0 a) ^ 2 ≤ 2 * x (φ k) a ^ 2 + 2 * x0 a ^ 2 := by
              nlinarith [sq_nonneg (x (φ k) a + x0 a)]
            rw [div_mul_eq_mul_div, le_div_iff₀ hL]
            nlinarith [sq_nonneg (x (φ k) a), sq_nonneg (x0 a)]
      _ = _ := by
          rw [ENNReal.tsum_add, tsum_eq_sum (s := F) fun a ha =>
            Set.indicator_of_notMem (fun h => ha (Finset.mem_coe.mp h)) _]
          congr 1
          rw [ENNReal.ofReal_sum_of_nonneg fun a _ => sq_nonneg _]
          exact Finset.sum_congr rfl fun a ha =>
            Set.indicator_of_mem (Finset.mem_coe.mpr ha) _
  have htail : ∑' a, ENNReal.ofReal (2 / L * (Λ a * x (φ k) a ^ 2 + Λ a * x0 a ^ 2)) ≤
      ENNReal.ofReal (2 / L * (B + B)) := by
    refine tsum_ofReal_le_of_sum_le (fun a => by
      have := hΛ a; positivity) fun S => ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    exact mul_le_mul_of_nonneg_left (add_le_add (h2 _ S) (hx02 S)) (by positivity)
  have hsmall : 2 / L * (B + B) ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hL]
    simp only [L]
    have : δ * (4 * B / δ + 1) = 4 * B + δ := by field_simp
    linarith
  calc ∑' a, ENNReal.ofReal ((x (φ k) a - x0 a) ^ 2)
      ≤ ENNReal.ofReal (∑ a ∈ F, (x (φ k) a - x0 a) ^ 2) + ENNReal.ofReal (2 / L * (B + B)) :=
        hsplit.trans (add_le_add (le_refl _) htail)
    _ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ := by
        gcongr
    _ = ENNReal.ofReal (2 * δ) := by
        rw [← ENNReal.ofReal_add hδ0.le hδ0.le, two_mul]
    _ ≤ ε := hδε

end SharpLSI
