import LeanResearch.PeriodicAttractiveLogGas.GreenNormalization
import LeanResearch.PeriodicAttractiveLogGas.GreenMollifierConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The regularized domination and simultaneous parameter limits of source
Proposition 2.4. This module is under development; each final limit concerns
the actual specified weights and normalizers. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace PeriodicAttractiveLogGas

theorem gibbsWeight_le_mul_of_kernel_le_add {g h : Torus → ℝ} {c : ℝ}
    (hgh : ∀ z : Torus, z ≠ 0 → g z ≤ h z + c)
    (N : ℕ) (hN : 2 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {x : Configuration N} (hx : x ∉ collisionSet N) :
    gibbsWeight g N β x ≤ Real.exp (β * c * ((N : ℝ) - 1) / 2) * gibbsWeight h N β x := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hp : pairEnergy g N x ≤ pairEnergy h N x + ((N : ℝ) * ((N : ℝ) - 1) / 2) * c := by
    rw [pairEnergy_eq_sum_orderedPairs, pairEnergy_eq_sum_orderedPairs]
    calc
      (∑ ij ∈ planarOrderedPairs N, g (x ij.1 - x ij.2)) ≤
          ∑ ij ∈ planarOrderedPairs N, (h (x ij.1 - x ij.2) + c) := by
        apply Finset.sum_le_sum
        intro ij hij
        apply hgh
        intro heq
        exact hx ⟨ij.1, ij.2, ne_of_lt ((mem_planarOrderedPairs ij).mp hij), sub_eq_zero.mp heq⟩
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, card_planarOrderedPairs,
          Nat.cast_choose_two]
  have heq : (β / (N : ℝ)) *
      (pairEnergy h N x + ((N : ℝ) * ((N : ℝ) - 1) / 2) * c) =
      β * c * ((N : ℝ) - 1) / 2 + (β / (N : ℝ)) * pairEnergy h N x := by
    field_simp
    ring
  calc
    gibbsWeight g N β x ≤ Real.exp ((β / (N : ℝ)) *
        (pairEnergy h N x + ((N : ℝ) * ((N : ℝ) - 1) / 2) * c)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp (div_nonneg hβ hn.le))
    _ = Real.exp (β * c * ((N : ℝ) - 1) / 2) * gibbsWeight h N β x := by
      rw [heq, Real.exp_add]
      rfl

theorem regularized_gibbsWeight_dominance {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ (1 / 16 : ℝ) → ∀ z : Torus, z ≠ 0 →
      regularizedGreen ε hε z ≤ regularGreenRepresentative z + C * ε ^ 2)
    (N : ℕ) (hN : 2 ≤ N) {β β₀ : ℝ} (hβ : 0 ≤ β) (hle : β ≤ β₀)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ))
    {x : Configuration N} (hx : x ∉ collisionSet N) :
    gibbsWeight (regularizedGreen ε hε) N β x ≤
      Real.exp (C * β₀ * ((N : ℝ) - 1) * ε ^ 2 / 2) *
        gibbsWeight regularGreenRepresentative N β x := by
  apply (gibbsWeight_le_mul_of_kernel_le_add (hb ε hε hs) N hN hβ hx).trans
  apply mul_le_mul_of_nonneg_right _ (gibbsWeight_pos _ _ _ _).le
  apply Real.exp_le_exp.mpr
  have hn : 0 ≤ (N : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ N by omega))
  have hm := mul_le_mul_of_nonneg_right hle (mul_nonneg (mul_nonneg hC hn) (sq_nonneg ε))
  nlinarith

/-- One common majorant for all scales and all couplings in the prescribed
closed subcritical interval. It also dominates the unregularized weights. -/
theorem exists_regularized_green_common_majorant (N : ℕ) (hN : 2 ≤ N) {β₀ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsubcritical : β₀ < 4) :
    ∃ M : Configuration N → ℝ,
      Integrable M (referenceMeasure N) ∧ (∀ x, 0 ≤ M x) ∧
      (∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
        ∀ᵐ x ∂referenceMeasure N, gibbsWeight regularGreenRepresentative N β x ≤ M x) ∧
      ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ (1 / 16 : ℝ) →
        ∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
          ∀ᵐ x ∂referenceMeasure N, gibbsWeight (regularizedGreen ε hε) N β x ≤ M x := by
  obtain ⟨C, hC, hb⟩ := exists_regularizedGreen_upper_bound
  obtain ⟨B, _, hBi, hB⟩ := exists_green_common_integrable_majorant N hN hβ₀ hsubcritical
  let A : ℝ := Real.exp (C * β₀ * ((N : ℝ) - 1) / 2)
  have hn : 0 ≤ (N : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ N by omega))
  have hA : 1 ≤ A := Real.one_le_exp_iff.mpr (by positivity)
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  refine ⟨fun x ↦ A * greenFixedMajorant N β₀ B x, hBi.const_mul A,
    fun x ↦ mul_nonneg hA0 (greenFixedMajorant_nonneg N β₀ B x), ?_, ?_⟩
  · intro β hβ hle
    exact (hB β hβ hle).mono (fun x hx ↦ hx.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hA (greenFixedMajorant_nonneg N β₀ B x)))
  · intro ε hε hs β hβ hle
    have hae : ∀ᵐ x ∂referenceMeasure N, x ∉ collisionSet N := by
      simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using collisionSet_null N
    filter_upwards [hae, hB β hβ hle] with x hx hxb
    apply (regularized_gibbsWeight_dominance hC.le hb N hN hβ hle ε hε hs hx).trans
    apply mul_le_mul _ hxb (gibbsWeight_pos _ _ _ _).le hA0
    apply Real.exp_le_exp.mpr
    have he2 : ε ^ 2 ≤ 1 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left he2 (show 0 ≤ C * β₀ * ((N : ℝ) - 1) by positivity)
    nlinarith

theorem integrable_regularizedGreen_gibbsWeight (N : ℕ) (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 ≤ β) (hsubcritical : β < 4) (ε : ℝ) (hε : 0 < ε)
    (hs : ε ≤ (1 / 16 : ℝ)) :
    Integrable (gibbsWeight (regularizedGreen ε hε) N β) (referenceMeasure N) := by
  obtain ⟨M, hi, _, _, hb⟩ := exists_regularized_green_common_majorant N hN hβ hsubcritical
  exact hi.mono_nonneg
    (measurable_gibbsWeight (continuous_regularizedGreen ε hε).measurable N β).aestronglyMeasurable
    (Eventually.of_forall (fun x ↦ (gibbsWeight_pos _ _ _ x).le)) (hb ε hε hs β hβ le_rfl)

theorem regularizedGreen_partitionFunction_ne_top (N : ℕ) (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 ≤ β) (hsubcritical : β < 4) (ε : ℝ) (hε : 0 < ε)
    (hs : ε ≤ (1 / 16 : ℝ)) : partitionFunction (regularizedGreen ε hε) N β ≠ ⊤ :=
  (integrable_gibbsWeight_iff (continuous_regularizedGreen ε hε).measurable N β).mp
    (integrable_regularizedGreen_gibbsWeight N hN hβ hsubcritical ε hε hs)

theorem one_le_regularizedGreen_partitionFunction (N : ℕ) (β ε : ℝ) (hε : 0 < ε) :
    1 ≤ partitionFunction (regularizedGreen ε hε) N β :=
  one_le_partitionFunction_of_mean_zero (continuous_regularizedGreen ε hε).measurable
    (integrable_regularizedGreen ε hε) (regularizedGreen_integral_zero ε hε) N β

theorem partitionFunction_toReal_eq_integral_weight {g : Torus → ℝ}
    (N : ℕ) (β : ℝ) (hi : Integrable (gibbsWeight g N β) (referenceMeasure N)) :
    (partitionFunction g N β).toReal = ∫ x, gibbsWeight g N β x ∂referenceMeasure N := by
  rw [partitionFunction, ← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun x ↦ (gibbsWeight_pos g N β x).le)), ENNReal.toReal_ofReal]
  exact integral_nonneg (fun x ↦ (gibbsWeight_pos g N β x).le)

theorem tendsto_regularizedGreen_gibbsWeight {ι : Type*} {l : Filter ι}
    (N : ℕ) {βs εs : ι → ℝ} {β : ℝ} (hβ : Tendsto βs l (𝓝 β))
    (hε : ∀ i, 0 < εs i) (hs : ∀ i, εs i ≤ (1 / 16 : ℝ))
    (ht : Tendsto εs l (𝓝 0)) {x : Configuration N} (hx : x ∉ collisionSet N) :
    Tendsto (fun i ↦ gibbsWeight (regularizedGreen (εs i) (hε i)) N (βs i) x)
      l (𝓝 (gibbsWeight regularGreenRepresentative N β x)) := by
  have hp : Tendsto (fun i ↦ pairEnergy (regularizedGreen (εs i) (hε i)) N x) l
      (𝓝 (pairEnergy regularGreenRepresentative N x)) := by
    unfold pairEnergy
    apply tendsto_finsetSum
    intro j _
    apply tendsto_finsetSum
    intro k hk
    apply tendsto_regularizedGreen hε hs ht
    intro heq
    exact hx ⟨j, k, (Finset.mem_Ioi.mp hk).ne, sub_eq_zero.mp heq⟩
  exact Real.continuous_exp.tendsto _ |>.comp ((hβ.div_const (N : ℝ)).mul hp)

/-- The source simultaneous convergence of unnormalized weights in genuine
L1, written as the nonnegative integral of their absolute difference. -/
theorem tendsto_lintegral_regularizedGreen_weight_sub (N : ℕ) (hN : 2 ≤ N)
    {β₀ β : ℝ} (hβ₀ : 0 ≤ β₀) (hsubcritical : β₀ < 4)
    (βs εs : ℕ → ℝ) (hβs : ∀ j, 0 ≤ βs j ∧ βs j ≤ β₀)
    (hβ : Tendsto βs atTop (𝓝 β))
    (hε : ∀ j, 0 < εs j) (hs : ∀ j, εs j ≤ (1 / 16 : ℝ))
    (ht : Tendsto εs atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫⁻ x, ENNReal.ofReal
      ‖gibbsWeight (regularizedGreen (εs j) (hε j)) N (βs j) x -
        gibbsWeight regularGreenRepresentative N β x‖ ∂referenceMeasure N) atTop (𝓝 0) := by
  obtain ⟨M, hi, _, _, hb⟩ := exists_regularized_green_common_majorant N hN hβ₀ hsubcritical
  apply tendsto_lintegral_norm_of_dominated_convergence
    (fun j ↦ (measurable_gibbsWeight (continuous_regularizedGreen (εs j) (hε j)).measurable N
      (βs j)).aestronglyMeasurable) hi.hasFiniteIntegral
  · intro j
    exact (hb (εs j) (hε j) (hs j) (βs j) (hβs j).1 (hβs j).2).mono
      (fun x hx ↦ by simpa only [Real.norm_eq_abs, abs_of_pos (gibbsWeight_pos _ _ _ _)] using hx)
  · have hae : ∀ᵐ x ∂referenceMeasure N, x ∉ collisionSet N := by
      simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using collisionSet_null N
    exact hae.mono (fun _ hx ↦ tendsto_regularizedGreen_gibbsWeight N hβ hε hs ht hx)

theorem tendsto_integral_regularizedGreen_weight (N : ℕ) (hN : 2 ≤ N)
    {β₀ β : ℝ} (hβ₀ : 0 ≤ β₀) (hsubcritical : β₀ < 4)
    (βs εs : ℕ → ℝ) (hβs : ∀ j, 0 ≤ βs j ∧ βs j ≤ β₀)
    (hβ : Tendsto βs atTop (𝓝 β))
    (hε : ∀ j, 0 < εs j) (hs : ∀ j, εs j ≤ (1 / 16 : ℝ))
    (ht : Tendsto εs atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x, gibbsWeight (regularizedGreen (εs j) (hε j)) N (βs j) x ∂referenceMeasure N)
      atTop (𝓝 (∫ x, gibbsWeight regularGreenRepresentative N β x ∂referenceMeasure N)) := by
  obtain ⟨M, hi, _, _, hb⟩ := exists_regularized_green_common_majorant N hN hβ₀ hsubcritical
  apply tendsto_integral_of_dominated_convergence M
    (fun j ↦ (measurable_gibbsWeight (continuous_regularizedGreen (εs j) (hε j)).measurable N
      (βs j)).aestronglyMeasurable) hi
  · intro j
    exact (hb (εs j) (hε j) (hs j) (βs j) (hβs j).1 (hβs j).2).mono
      (fun x hx ↦ by simpa only [Real.norm_eq_abs, abs_of_pos (gibbsWeight_pos _ _ _ _)] using hx)
  · have hae : ∀ᵐ x ∂referenceMeasure N, x ∉ collisionSet N := by
      simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using collisionSet_null N
    exact hae.mono (fun _ hx ↦ tendsto_regularizedGreen_gibbsWeight N hβ hε hs ht hx)

theorem exists_regularizedGreenPartitionFunction_uniform_bound (N : ℕ) (hN : 2 ≤ N)
    {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (hsubcritical : β₀ < 4) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ (1 / 16 : ℝ) →
      ∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
        1 ≤ partitionFunction (regularizedGreen ε hε) N β ∧
          partitionFunction (regularizedGreen ε hε) N β ≤ ENNReal.ofReal K := by
  obtain ⟨M, hi, hM, _, hb⟩ := exists_regularized_green_common_majorant N hN hβ₀ hsubcritical
  let K : ℝ := max 1 (∫ x, M x ∂referenceMeasure N)
  refine ⟨K, le_max_left _ _, ?_⟩
  intro ε hε hs β hβ hle
  refine ⟨one_le_regularizedGreen_partitionFunction N β ε hε, ?_⟩
  calc
    partitionFunction (regularizedGreen ε hε) N β ≤
        ∫⁻ x, ENNReal.ofReal (M x) ∂referenceMeasure N :=
      lintegral_mono_ae ((hb ε hε hs β hβ hle).mono (fun _ hx ↦ ENNReal.ofReal_le_ofReal hx))
    _ = ENNReal.ofReal (∫ x, M x ∂referenceMeasure N) :=
      (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hM)).symm
    _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal (le_max_right _ _)

theorem gibbsDensity_toReal (g : Torus → ℝ) (N : ℕ) (β : ℝ) (x : Configuration N) :
    (gibbsDensity g N β x).toReal =
      gibbsWeight g N β x / (partitionFunction g N β).toReal := by
  rw [gibbsDensity, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (gibbsWeight_pos g N β x).le, div_eq_mul_inv, mul_comm]

theorem integrable_gibbsDensity_toReal {g : Torus → ℝ} (N : ℕ) (β : ℝ)
    (hi : Integrable (gibbsWeight g N β) (referenceMeasure N)) :
    Integrable (fun x ↦ (gibbsDensity g N β x).toReal) (referenceMeasure N) := by
  simp_rw [gibbsDensity_toReal]
  exact hi.div_const _

theorem one_le_regularGreen_partitionFunction_toReal (N : ℕ) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hsubcritical : β < 4) :
    1 ≤ (partitionFunction regularGreenRepresentative N β).toReal := by
  have h := one_le_greenPartitionFunction N β
  rw [← regularGreen_partitionFunction_eq] at h
  simpa only [ENNReal.toReal_one] using
    ENNReal.toReal_mono (regularGreen_partitionFunction_ne_top N hN hβ hsubcritical) h

theorem one_le_regularizedGreen_partitionFunction_toReal (N : ℕ) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hsubcritical : β < 4) (ε : ℝ) (hε : 0 < ε)
    (hs : ε ≤ (1 / 16 : ℝ)) :
    1 ≤ (partitionFunction (regularizedGreen ε hε) N β).toReal := by
  simpa only [ENNReal.toReal_one] using
    ENNReal.toReal_mono (regularizedGreen_partitionFunction_ne_top N hN hβ hsubcritical ε hε hs)
      (one_le_regularizedGreen_partitionFunction N β ε hε)

theorem tendsto_regularizedGreen_partitionFunction_toReal (N : ℕ) (hN : 2 ≤ N)
    {β₀ β : ℝ} (hβ₀ : 0 ≤ β₀) (hsubcritical : β₀ < 4)
    (βs εs : ℕ → ℝ) (hβs : ∀ j, 0 ≤ βs j ∧ βs j ≤ β₀)
    (hβ : Tendsto βs atTop (𝓝 β))
    (hε : ∀ j, 0 < εs j) (hs : ∀ j, εs j ≤ (1 / 16 : ℝ))
    (ht : Tendsto εs atTop (𝓝 0)) :
    Tendsto (fun j ↦ (partitionFunction (regularizedGreen (εs j) (hε j)) N (βs j)).toReal)
      atTop (𝓝 (partitionFunction regularGreenRepresentative N β).toReal) := by
  have hβnonneg : 0 ≤ β := ge_of_tendsto' hβ (fun j ↦ (hβs j).1)
  have hβle : β ≤ β₀ := le_of_tendsto' hβ (fun j ↦ (hβs j).2)
  have hseq : ∀ j, (partitionFunction (regularizedGreen (εs j) (hε j)) N (βs j)).toReal =
      ∫ x, gibbsWeight (regularizedGreen (εs j) (hε j)) N (βs j) x ∂referenceMeasure N :=
    fun j ↦ partitionFunction_toReal_eq_integral_weight N (βs j)
      (integrable_regularizedGreen_gibbsWeight N hN (hβs j).1 ((hβs j).2.trans_lt hsubcritical)
        (εs j) (hε j) (hs j))
  have hlim := partitionFunction_toReal_eq_integral_weight N β
    (integrable_regularGreen_gibbsWeight N hN hβnonneg (hβle.trans_lt hsubcritical))
  simp_rw [hseq, hlim]
  exact tendsto_integral_regularizedGreen_weight N hN hβ₀ hsubcritical βs εs hβs hβ hε hs ht

/-- The genuine normalized densities converge in L1. The same fixed-particle
majorant works because Jensen's lower bound is one for every actual normalizer;
the denominator is proved finite and positive before taking its limit. -/
theorem tendsto_lintegral_regularizedGreen_density_sub (N : ℕ) (hN : 2 ≤ N)
    {β₀ β : ℝ} (hβ₀ : 0 ≤ β₀) (hsubcritical : β₀ < 4)
    (βs εs : ℕ → ℝ) (hβs : ∀ j, 0 ≤ βs j ∧ βs j ≤ β₀)
    (hβ : Tendsto βs atTop (𝓝 β))
    (hε : ∀ j, 0 < εs j) (hs : ∀ j, εs j ≤ (1 / 16 : ℝ))
    (ht : Tendsto εs atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫⁻ x, ENNReal.ofReal
      ‖(gibbsDensity (regularizedGreen (εs j) (hε j)) N (βs j) x).toReal -
        (gibbsDensity regularGreenRepresentative N β x).toReal‖ ∂referenceMeasure N)
      atTop (𝓝 0) := by
  have hβnonneg : 0 ≤ β := ge_of_tendsto' hβ (fun j ↦ (hβs j).1)
  have hβle : β ≤ β₀ := le_of_tendsto' hβ (fun j ↦ (hβs j).2)
  have hZ : 1 ≤ (partitionFunction regularGreenRepresentative N β).toReal :=
    one_le_regularGreen_partitionFunction_toReal N hN hβnonneg (hβle.trans_lt hsubcritical)
  have hZs : ∀ j, 1 ≤ (partitionFunction (regularizedGreen (εs j) (hε j)) N (βs j)).toReal :=
    fun j ↦ one_le_regularizedGreen_partitionFunction_toReal N hN
      (hβs j).1 ((hβs j).2.trans_lt hsubcritical) (εs j) (hε j) (hs j)
  have hZlim := tendsto_regularizedGreen_partitionFunction_toReal N hN hβ₀ hsubcritical
    βs εs hβs hβ hε hs ht
  obtain ⟨M, hi, _, _, hb⟩ := exists_regularized_green_common_majorant N hN hβ₀ hsubcritical
  have hmeas : ∀ j, AEStronglyMeasurable
      (fun x ↦ (gibbsDensity (regularizedGreen (εs j) (hε j)) N (βs j) x).toReal)
      (referenceMeasure N) := by
    intro j
    simp_rw [gibbsDensity_toReal]
    exact ((measurable_gibbsWeight (continuous_regularizedGreen (εs j) (hε j)).measurable
      N (βs j)).div_const _).aestronglyMeasurable
  apply tendsto_lintegral_norm_of_dominated_convergence hmeas hi.hasFiniteIntegral
  · intro j
    filter_upwards [hb (εs j) (hε j) (hs j) (βs j) (hβs j).1 (hβs j).2] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, gibbsDensity_toReal]
    exact (div_le_self (gibbsWeight_pos _ _ _ x).le (hZs j)).trans hx
  · have hae : ∀ᵐ x ∂referenceMeasure N, x ∉ collisionSet N := by
      simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using collisionSet_null N
    filter_upwards [hae] with x hx
    simp_rw [gibbsDensity_toReal]
    exact (tendsto_regularizedGreen_gibbsWeight N hβ hε hs ht hx).div hZlim
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hZ))

theorem gibbsDensity_congr_ae_kernel {g h : Torus → ℝ} (hgh : g =ᵐ[torusMeasure] h)
    (N : ℕ) (β : ℝ) :
    gibbsDensity g N β =ᵐ[referenceMeasure N] gibbsDensity h N β := by
  filter_upwards [gibbsWeight_congr_ae_kernel hgh N β] with x hx
  simp only [gibbsDensity, partitionFunction_congr_ae_kernel hgh N β, hx]

/-- The normalized-density limit also holds for the Fourier representative
used in the final target: this transfer is actual Haar-a.e. kernel invariance. -/
theorem tendsto_lintegral_regularizedGreen_targetDensity_sub (N : ℕ) (hN : 2 ≤ N)
    {β₀ β : ℝ} (hβ₀ : 0 ≤ β₀) (hsubcritical : β₀ < 4)
    (βs εs : ℕ → ℝ) (hβs : ∀ j, 0 ≤ βs j ∧ βs j ≤ β₀)
    (hβ : Tendsto βs atTop (𝓝 β))
    (hε : ∀ j, 0 < εs j) (hs : ∀ j, εs j ≤ (1 / 16 : ℝ))
    (ht : Tendsto εs atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫⁻ x, ENNReal.ofReal
      ‖(gibbsDensity (regularizedGreen (εs j) (hε j)) N (βs j) x).toReal -
        (gibbsDensity greenRealRepresentative N β x).toReal‖ ∂referenceMeasure N)
      atTop (𝓝 0) := by
  have heq (j : ℕ) :
      (∫⁻ x, ENNReal.ofReal
        ‖(gibbsDensity (regularizedGreen (εs j) (hε j)) N (βs j) x).toReal -
          (gibbsDensity regularGreenRepresentative N β x).toReal‖ ∂referenceMeasure N) =
      ∫⁻ x, ENNReal.ofReal
        ‖(gibbsDensity (regularizedGreen (εs j) (hε j)) N (βs j) x).toReal -
          (gibbsDensity greenRealRepresentative N β x).toReal‖ ∂referenceMeasure N := by
    apply lintegral_congr_ae
    filter_upwards [gibbsDensity_congr_ae_kernel regularGreenRepresentative_ae N β] with x hx
    rw [hx]
  simpa only [heq] using
    tendsto_lintegral_regularizedGreen_density_sub N hN hβ₀ hsubcritical βs εs hβs hβ hε hs ht

end PeriodicAttractiveLogGas
