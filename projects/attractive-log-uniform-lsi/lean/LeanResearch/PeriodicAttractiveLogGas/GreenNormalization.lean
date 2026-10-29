import LeanResearch.PeriodicAttractiveLogGas.TorusCollisionIntegrability
import LeanResearch.PeriodicAttractiveLogGas.GreenEnsemble
import LeanResearch.PeriodicAttractiveLogGas.Target

/-! The actual singular Gibbs normalization and fixed-particle common
majorant from source Proposition 2.4. The estimates use the labelled pair
sum with its exact one-half combinatorial factor. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas

theorem pairEnergy_eq_sum_orderedPairs (g : Torus → ℝ) (N : ℕ) (x : Configuration N) :
    pairEnergy g N x = ∑ ij ∈ planarOrderedPairs N, g (x ij.1 - x ij.2) := by
  unfold pairEnergy planarOrderedPairs
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _
  have heq : Finset.Ioi i = Finset.univ.filter (fun j : Fin N ↦ i < j) := by
    ext j
    simp
  rw [heq, Finset.sum_filter]

theorem gibbsWeight_eq_prod_orderedPairs (g : Torus → ℝ) (N : ℕ) (β : ℝ)
    (x : Configuration N) :
    gibbsWeight g N β x =
      ∏ ij ∈ planarOrderedPairs N, Real.exp ((β / (N : ℝ)) * g (x ij.1 - x ij.2)) := by
  rw [gibbsWeight, pairEnergy_eq_sum_orderedPairs, Finset.mul_sum, Real.exp_sum]

theorem exp_mul_green_le_rpow {C a a₀ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z : Torus, z ≠ 0 → |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C)
    (ha : 0 ≤ a) (haa : a ≤ a₀) {z : Torus} (hz : z ≠ 0) :
    Real.exp (a * regularGreenRepresentative z) ≤
      Real.exp (a₀ * C) * torusEuclideanNorm z ^ (-a₀) := by
  have hr : 0 < torusEuclideanNorm z :=
    lt_of_le_of_ne (torusEuclideanNorm_nonneg z)
      (fun h ↦ hz ((torusEuclideanNorm_eq_zero_iff z).mp h.symm))
  have hl : Real.log (torusEuclideanNorm z) ≤ 0 :=
    Real.log_nonpos hr.le (torusEuclideanNorm_le_one z)
  have hg : regularGreenRepresentative z ≤ C - Real.log (torusEuclideanNorm z) := by
    have hu := (le_abs_self (regularGreenRepresentative z + Real.log (torusEuclideanNorm z))).trans (hb z hz)
    linarith
  have hbound : a * regularGreenRepresentative z ≤ a₀ * (C - Real.log (torusEuclideanNorm z)) :=
    (mul_le_mul_of_nonneg_left hg ha).trans
      (mul_le_mul_of_nonneg_right haa (by linarith))
  calc
    Real.exp (a * regularGreenRepresentative z) ≤
        Real.exp (a₀ * (C - Real.log (torusEuclideanNorm z))) := Real.exp_le_exp.mpr hbound
    _ = Real.exp (a₀ * C) * torusEuclideanNorm z ^ (-a₀) := by
      rw [Real.rpow_def_of_pos hr, ← Real.exp_add]
      congr 1
      ring

def greenFixedMajorant (N : ℕ) (β₀ C : ℝ) (x : Configuration N) : ℝ :=
  Real.exp (β₀ * C * ((N : ℝ) - 1) / 2) * torusPairWeight N (β₀ / (N : ℝ)) x

theorem greenFixedMajorant_nonneg (N : ℕ) (β₀ C : ℝ) (x : Configuration N) :
    0 ≤ greenFixedMajorant N β₀ C x :=
  mul_nonneg (Real.exp_pos _).le (torusPairWeight_nonneg N _ x)

theorem gibbsWeight_le_greenFixedMajorant {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z : Torus, z ≠ 0 → |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C)
    (N : ℕ) (hN : 2 ≤ N) {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    {x : Configuration N} (hx : x ∉ collisionSet N) :
    gibbsWeight regularGreenRepresentative N β x ≤ greenFixedMajorant N β₀ C x := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hp : ∀ ij ∈ planarOrderedPairs N,
      Real.exp ((β / (N : ℝ)) * regularGreenRepresentative (x ij.1 - x ij.2)) ≤
        Real.exp ((β₀ / (N : ℝ)) * C) * torusEuclideanDist (x ij.1) (x ij.2) ^ (-(β₀ / (N : ℝ))) := by
    intro ij hij
    apply exp_mul_green_le_rpow hC hb (div_nonneg hβ hn.le) (div_le_div_of_nonneg_right hβ₀ hn.le)
    intro heq
    exact hx ⟨ij.1, ij.2, (ne_of_lt ((mem_planarOrderedPairs ij).mp hij)), sub_eq_zero.mp heq⟩
  rw [gibbsWeight_eq_prod_orderedPairs]
  calc
    (∏ ij ∈ planarOrderedPairs N, Real.exp ((β / (N : ℝ)) * regularGreenRepresentative (x ij.1 - x ij.2))) ≤
        ∏ ij ∈ planarOrderedPairs N, Real.exp ((β₀ / (N : ℝ)) * C) *
          torusEuclideanDist (x ij.1) (x ij.2) ^ (-(β₀ / (N : ℝ))) :=
      Finset.prod_le_prod₀ (fun _ _ ↦ (Real.exp_pos _).le) hp
    _ = greenFixedMajorant N β₀ C x := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, card_planarOrderedPairs, ← Real.exp_nat_mul,
        Nat.cast_choose_two]
      unfold greenFixedMajorant torusPairWeight
      congr 2
      field_simp

theorem ae_gibbsWeight_le_greenFixedMajorant {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z : Torus, z ≠ 0 → |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C)
    (N : ℕ) (hN : 2 ≤ N) {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) :
    ∀ᵐ x ∂referenceMeasure N,
      gibbsWeight regularGreenRepresentative N β x ≤ greenFixedMajorant N β₀ C x := by
  have hae : ∀ᵐ x ∂referenceMeasure N, x ∉ collisionSet N := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using collisionSet_null N
  exact hae.mono (fun _ hx ↦ gibbsWeight_le_greenFixedMajorant hC hb N hN hβ hβ₀ hx)

theorem integrable_greenFixedMajorant (N : ℕ) (hN : 2 ≤ N) {β₀ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsubcritical : β₀ < 4) (C : ℝ) :
    Integrable (greenFixedMajorant N β₀ C) (referenceMeasure N) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have ha : 0 ≤ β₀ / (N : ℝ) := div_nonneg hβ₀ hn.le
  have hs : (β₀ / (N : ℝ)) * (N : ℝ) < 4 := by
    simpa only [div_mul_cancel₀ _ hn.ne'] using hsubcritical
  exact (integrable_torusPairWeight N hN ha hs).const_mul _

theorem integrable_regularGreen_gibbsWeight (N : ℕ) (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 ≤ β) (hsubcritical : β < 4) :
    Integrable (gibbsWeight regularGreenRepresentative N β) (referenceMeasure N) := by
  obtain ⟨C, hC, hb⟩ := exists_regularGreenRepresentative_bounds
  exact (integrable_greenFixedMajorant N hN hβ hsubcritical C).mono_nonneg
    (measurable_gibbsWeight regularGreenRepresentative_measurable N β).aestronglyMeasurable
    (Eventually.of_forall (fun x ↦ (gibbsWeight_pos _ N β x).le))
    (ae_gibbsWeight_le_greenFixedMajorant hC.le (fun z hz ↦ (hb z hz).1) N hN hβ le_rfl)

theorem regularGreen_partitionFunction_ne_top (N : ℕ) (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 ≤ β) (hsubcritical : β < 4) :
    partitionFunction regularGreenRepresentative N β ≠ ⊤ :=
  (integrable_gibbsWeight_iff regularGreenRepresentative_measurable N β).mp
    (integrable_regularGreen_gibbsWeight N hN hβ hsubcritical)

theorem green_partitionFunction_ne_top (N : ℕ) (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 ≤ β) (hsubcritical : β < 4) :
    partitionFunction greenRealRepresentative N β ≠ ⊤ := by
  rw [← regularGreen_partitionFunction_eq]
  exact regularGreen_partitionFunction_ne_top N hN hβ hsubcritical

/-- The separate nonvacuity obligation attached to the exact target is now
proved for every actual subcritical singular Green law. -/
theorem green_normalization : greenNormalizationStatement :=
  fun N hN _ hβ hs ↦ green_partitionFunction_ne_top N hN hβ hs

theorem isProbabilityMeasure_greenGibbs (N : ℕ) (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 ≤ β) (hsubcritical : β < 4) :
    IsProbabilityMeasure (gibbsMeasure greenRealRepresentative N β) :=
  isProbabilityMeasure_gibbsMeasure greenRealRepresentative_measurable N β
    (green_partitionFunction_ne_top N hN hβ hsubcritical)

theorem exists_reference_le_greenGibbs (N : ℕ) (hN : 2 ≤ N) {β : ℝ}
    (hβ : 0 ≤ β) (hsubcritical : β < 4) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ referenceMeasure N ≤ c • gibbsMeasure greenRealRepresentative N β :=
  exists_reference_le_greenGibbs_of_partition_finite N hβ
    (green_partitionFunction_ne_top N hN hβ hsubcritical)

/-- One actual integrable function dominates every coupling in the closed
subcritical interval; no particle-number uniformity is asserted. -/
theorem exists_green_common_integrable_majorant (N : ℕ) (hN : 2 ≤ N) {β₀ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsubcritical : β₀ < 4) :
    ∃ C : ℝ, 0 < C ∧ Integrable (greenFixedMajorant N β₀ C) (referenceMeasure N) ∧
      ∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
        ∀ᵐ x ∂referenceMeasure N,
          gibbsWeight regularGreenRepresentative N β x ≤ greenFixedMajorant N β₀ C x := by
  obtain ⟨C, hC, hb⟩ := exists_regularGreenRepresentative_bounds
  exact ⟨C, hC, integrable_greenFixedMajorant N hN hβ₀ hsubcritical C,
    fun _ hβ hle ↦ ae_gibbsWeight_le_greenFixedMajorant hC.le (fun z hz ↦ (hb z hz).1) N hN hβ hle⟩

theorem exists_greenPartitionFunction_uniform_bound (N : ℕ) (hN : 2 ≤ N) {β₀ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsubcritical : β₀ < 4) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
      1 ≤ partitionFunction greenRealRepresentative N β ∧
        partitionFunction greenRealRepresentative N β ≤ ENNReal.ofReal K := by
  obtain ⟨C, _, hi, hb⟩ := exists_green_common_integrable_majorant N hN hβ₀ hsubcritical
  let K : ℝ := max 1 (∫ x, greenFixedMajorant N β₀ C x ∂referenceMeasure N)
  refine ⟨K, le_max_left _ _, ?_⟩
  intro β hβ hle
  refine ⟨one_le_greenPartitionFunction N β, ?_⟩
  rw [← regularGreen_partitionFunction_eq]
  calc
    partitionFunction regularGreenRepresentative N β ≤
        ∫⁻ x, ENNReal.ofReal (greenFixedMajorant N β₀ C x) ∂referenceMeasure N :=
      lintegral_mono_ae ((hb β hβ hle).mono (fun _ hx ↦ ENNReal.ofReal_le_ofReal hx))
    _ = ENNReal.ofReal (∫ x, greenFixedMajorant N β₀ C x ∂referenceMeasure N) :=
      (ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall (greenFixedMajorant_nonneg N β₀ C))).symm
    _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal (le_max_right _ _)

theorem lowerWeight_eq_exp (N : ℕ) (hN : 0 < N) (β m : ℝ) :
    lowerWeight N β m = Real.exp (β * m * ((N : ℝ) - 1) / 2) := by
  have hcount : (∑ i : Fin N, ∑ _j ∈ Finset.Ioi i, m) = ((N : ℝ) * ((N : ℝ) - 1) / 2) * m := by
    have h := pairEnergy_eq_sum_orderedPairs (fun _ ↦ m) N 0
    simpa only [pairEnergy, Finset.sum_const, nsmul_eq_mul, card_planarOrderedPairs,
      Nat.cast_choose_two] using h
  rw [lowerWeight, hcount]
  congr 1
  have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  field_simp

theorem green_uniform_lower_weight {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hg : ∀ z : Torus, -Cg ≤ regularGreenRepresentative z)
    (N : ℕ) (hN : 2 ≤ N) {β β₀ : ℝ} (hβ : 0 ≤ β) (hle : β ≤ β₀)
    (x : Configuration N) :
    Real.exp (-β₀ * ((N : ℝ) - 1) * Cg / 2) ≤ gibbsWeight regularGreenRepresentative N β x := by
  apply le_trans _ (lowerWeight_le_gibbsWeight hg N hβ x)
  rw [lowerWeight_eq_exp N (by omega)]
  apply Real.exp_le_exp.mpr
  have hn : 0 ≤ (N : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ N by omega))
  have hm := mul_le_mul_of_nonneg_right hle (mul_nonneg hn hCg)
  nlinarith

theorem exists_green_uniform_density_lower_bound (N : ℕ) (hN : 2 ≤ N) {β₀ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsubcritical : β₀ < 4) :
    ∃ K Cg : ℝ, 1 ≤ K ∧ 0 < Cg ∧
      0 < (ENNReal.ofReal K)⁻¹ * ENNReal.ofReal (Real.exp (-β₀ * ((N : ℝ) - 1) * Cg / 2)) ∧
      ∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
        partitionFunction greenRealRepresentative N β ≤ ENNReal.ofReal K ∧
        ∀ x : Configuration N,
          (ENNReal.ofReal K)⁻¹ * ENNReal.ofReal (Real.exp (-β₀ * ((N : ℝ) - 1) * Cg / 2)) ≤
            gibbsDensity regularGreenRepresentative N β x := by
  obtain ⟨K, hK, hb⟩ := exists_greenPartitionFunction_uniform_bound N hN hβ₀ hsubcritical
  obtain ⟨Cg, hCg, hg⟩ := exists_regularGreenRepresentative_lower_bound
  refine ⟨K, Cg, hK, hCg, ?_, ?_⟩
  · exact pos_iff_ne_zero.mpr (mul_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))))
  · intro β hβ hle
    refine ⟨(hb β hβ hle).2, ?_⟩
    intro x
    apply mul_le_mul _ (ENNReal.ofReal_le_ofReal (green_uniform_lower_weight hCg.le hg N hN hβ hle x))
      zero_le zero_le
    exact ENNReal.inv_le_inv.mpr (by simpa only [regularGreen_partitionFunction_eq] using (hb β hβ hle).2)

end PeriodicAttractiveLogGas
