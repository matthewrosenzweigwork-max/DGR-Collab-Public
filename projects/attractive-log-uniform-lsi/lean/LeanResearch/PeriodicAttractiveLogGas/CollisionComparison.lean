import LeanResearch.PeriodicAttractiveLogGas.CollisionWeights
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Collision nullity and the uniform exponent comparison in source Lemma 2.3.
Real powers at zero are totalized, so the pointwise comparison is used only
after the actual anchored collision diagonals have been proved null. -/

noncomputable section
open MeasureTheory Set Metric
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas

theorem ae_planar_pair_ne (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    ∀ᵐ w : Fin n → PlanarSpace ∂volume, w i ≠ w j := by
  let D : Submodule ℝ (Fin n → PlanarSpace) :=
    { carrier := {w | w i = w j}
      zero_mem' := rfl
      add_mem' := by
        intro u v hu hv
        change u i + v i = u j + v j
        rw [hu, hv]
      smul_mem' := by
        intro c w hw
        change c • w i = c • w j
        rw [hw] }
  have hD : D ≠ ⊤ := by
    let v : PlanarSpace := WithLp.toLp 2 (fun _ : Fin 2 => (1 : ℝ))
    have hv : v ≠ 0 := by
      intro h
      have h0 := congrArg (fun x : PlanarSpace => x (0 : Fin 2)) h
      norm_num [v] at h0
    let w : Fin n → PlanarSpace := Function.update 0 i v
    intro htop
    have hw : w ∈ D := by rw [htop]; trivial
    change w i = w j at hw
    exact hv (by simpa [w, hij, hij.symm] using hw)
  have hm : (volume : Measure (Fin n → PlanarSpace)) {w | w i = w j} = 0 :=
    Measure.addHaar_submodule volume D hD
  simpa only [ae_iff, not_not] using hm

theorem ae_anchoredCluster_pair_ne (n : ℕ) (i j : Fin (n + 1)) :
    ∀ᵐ w : Fin n → PlanarSpace ∂volume,
      i ≠ j → anchoredCluster n w i ≠ anchoredCluster n w j := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · have h := Measure.ae_eval_ne (μ := fun _ : Fin n => (volume : Measure PlanarSpace)) j 0
      filter_upwards [h] with w hw
      intro _
      exact hw.symm
  · refine Fin.cases ?_ (fun j => ?_) j
    · have h := Measure.ae_eval_ne (μ := fun _ : Fin n => (volume : Measure PlanarSpace)) i 0
      filter_upwards [h] with w hw
      intro _
      exact hw
    · by_cases hij : i = j
      · subst j
        simp
      · filter_upwards [ae_planar_pair_ne n hij] with w hw
        intro _
        exact hw

theorem ae_anchoredCluster_pairwise_ne (n : ℕ) :
    ∀ᵐ w : Fin n → PlanarSpace ∂volume,
      ∀ i j : Fin (n + 1), i ≠ j → anchoredCluster n w i ≠ anchoredCluster n w j :=
  ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => ae_anchoredCluster_pair_ne n i j))

theorem measurableSet_clusterBox (n : ℕ) (ρ : ℝ) : MeasurableSet (clusterBox n ρ) := by
  exact MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_ball)

theorem anchoredCluster_norm_lt_of_mem_clusterBox (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    {w : Fin n → PlanarSpace} (hw : w ∈ clusterBox n ρ) (i : Fin (n + 1)) :
    ‖anchoredCluster n w i‖ < ρ := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hρ
  · simpa only [anchoredCluster_succ, mem_ball, dist_zero_right] using hw j (mem_univ j)

/-- The source uniform comparison, for the actual extended cluster integrals.
It does not assume or conclude finiteness. The exponent is the number of
unordered pairs among the anchor and the n free particles. -/
theorem clusterIntegral_exponent_comparison (n : ℕ) {a a₀ ρ : ℝ}
    (ha : 0 ≤ a) (haa : a ≤ a₀) (hρ : 0 < ρ) :
    clusterIntegral n ρ a ≤
      ENNReal.ofReal ((max 1 (2 * ρ)) ^ (a₀ * (n : ℝ) * ((n : ℝ) + 1) / 2)) *
        clusterIntegral n ρ a₀ := by
  let C : ℝ := (max 1 (2 * ρ)) ^ (a₀ * (n : ℝ) * ((n : ℝ) + 1) / 2)
  have hC : 0 ≤ C := Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  have hpoint : ∀ᵐ w ∂(volume.restrict (clusterBox n ρ)),
      clusterWeight n a w ≤ C * clusterWeight n a₀ w := by
    filter_upwards [ae_restrict_of_ae (ae_anchoredCluster_pairwise_ne n),
      ae_restrict_mem (measurableSet_clusterBox n ρ)] with w hne hw
    have hpos : ∀ ij ∈ planarOrderedPairs (n + 1),
        0 < ‖anchoredCluster n w ij.1 - anchoredCluster n w ij.2‖ := by
      intro ij hij
      apply norm_pos_iff.mpr
      exact sub_ne_zero.mpr (hne _ _ (ne_of_lt ((mem_planarOrderedPairs ij).mp hij)))
    have hbound : ∀ ij ∈ planarOrderedPairs (n + 1),
        ‖anchoredCluster n w ij.1 - anchoredCluster n w ij.2‖ ≤ max 1 (2 * ρ) := by
      intro ij _
      apply (norm_sub_le _ _).trans
      apply le_trans _ (le_max_right _ _)
      have h1 := anchoredCluster_norm_lt_of_mem_clusterBox n hρ hw ij.1
      have h2 := anchoredCluster_norm_lt_of_mem_clusterBox n hρ hw ij.2
      linarith
    have h := planarPairWeight_exponent_comparison (n + 1) ha haa (le_max_left 1 (2 * ρ))
      (anchoredCluster n w) hpos hbound
    have he : a₀ * ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1) / 2 =
        a₀ * (n : ℝ) * ((n : ℝ) + 1) / 2 := by push_cast; ring
    simpa only [clusterWeight, C, he] using h
  calc
    clusterIntegral n ρ a ≤ ∫⁻ w in clusterBox n ρ,
        ENNReal.ofReal (C * clusterWeight n a₀ w) :=
      lintegral_mono_ae (hpoint.mono (fun _ h => ENNReal.ofReal_le_ofReal h))
    _ = ENNReal.ofReal C * clusterIntegral n ρ a₀ := by
      simp_rw [ENNReal.ofReal_mul hC]
      exact lintegral_const_mul _ (measurable_clusterWeight n a₀).ennreal_ofReal

end PeriodicAttractiveLogGas
