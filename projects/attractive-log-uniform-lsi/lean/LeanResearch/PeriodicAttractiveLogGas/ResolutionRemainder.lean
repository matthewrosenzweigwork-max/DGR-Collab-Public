import LeanResearch.PeriodicAttractiveLogGas.ResolutionCutoffs
import LeanResearch.PeriodicAttractiveLogGas.Collisions
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The successive remainder vanishes off collisions. The geometric claim is
proved for the actual cell supports; no refinement monotonicity is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PeriodicAttractiveLogGas.ResolutionRemainder
open ResolutionCutoffs SmoothOccupations SquaredLocalization

theorem finite_positive_lower_bound {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ s, 0 < r i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ r i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨δ, hδ, hb⟩ := ih (fun j hj => hr j (Finset.mem_insert_of_mem hj))
    refine ⟨min (r i) δ, lt_min (hr i (Finset.mem_insert_self i s)) hδ, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hb j hj)

theorem exists_pair_separation {N : ℕ} {X : Configuration N} (hX : X ∉ collisionSet N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j : Fin N, i ≠ j → δ ≤ torusEuclideanDist (X i) (X j) := by
  classical
  let s : Finset (Fin N × Fin N) := Finset.univ.filter (fun p => p.1 ≠ p.2)
  have hp (p : Fin N × Fin N) (h : p ∈ s) : 0 < torusEuclideanDist (X p.1) (X p.2) := by
    have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp h).2
    apply lt_of_le_of_ne (torusEuclideanDist_nonneg _ _)
    intro he
    apply hX
    exact ⟨p.1, p.2, hij, (torusEuclideanDist_eq_zero_iff _ _).mp he.symm⟩
  obtain ⟨δ, hδ, hb⟩ := finite_positive_lower_bound s (fun p => torusEuclideanDist (X p.1) (X p.2)) hp
  exact ⟨δ, hδ, fun i j hij => hb (i, j) (by simp [s, hij])⟩

theorem active_pair_distance {N J : ℕ} (hJ : 3 ≤ J) (a : MeshCells.MeshIndex J)
    (X : Configuration N) {i j : Fin N}
    (hi : cellCutoff J (by omega) a (X i) ≠ 0)
    (hj : cellCutoff J (by omega) a (X j) ≠ 0) :
    torusEuclideanDist (X i) (X j) ≤ 2 * Real.sqrt 2 / J := by
  have hbi := cellCutoff_tsupport_ball J hJ a
    (subset_closure (Function.mem_support.mpr hi))
  have hbj := cellCutoff_tsupport_ball J hJ a
    (subset_closure (Function.mem_support.mpr hj))
  have hh := torusEuclideanDist_triangle (X i) (cellCenter J a) (X j)
  rw [torusEuclideanDist_comm (cellCenter J a) (X j)] at hh
  change torusEuclideanDist (X i) (cellCenter J a) ≤ _ at hbi
  change torusEuclideanDist (X j) (cellCenter J a) ≤ _ at hbj
  calc
    _ ≤ Real.sqrt 2 / J + Real.sqrt 2 / J := hh.trans (add_le_add hbi hbj)
    _ = _ := by ring

theorem maximumOccupation_le_single_particle {N J : ℕ} (hJ : 3 ≤ J) {X : Configuration N}
    {δ : ℝ} (hsep : ∀ i j : Fin N, i ≠ j → δ ≤ torusEuclideanDist (X i) (X j))
    (hsmall : 2 * Real.sqrt 2 / (J : ℝ) < δ) :
    maximumOccupation N J (by omega) X ≤ 1 / (N : ℝ) := by
  classical
  apply (maximumOccupation_le_iff N J (by omega) X _).mpr
  intro a
  have hs : (∑ i : Fin N, cellCutoff J (by omega) a (X i)) ≤ 1 := by
    by_cases ha : ∃ i : Fin N, cellCutoff J (by omega) a (X i) ≠ 0
    · obtain ⟨i, hi⟩ := ha
      have hz : ∀ j : Fin N, j ≠ i → cellCutoff J (by omega) a (X j) = 0 := by
        intro j hji
        by_contra hj
        exact (not_lt_of_ge (hsep i j (Ne.symm hji)))
          ((active_pair_distance hJ a X hi hj).trans_lt hsmall)
      rw [Finset.sum_eq_single i (fun j _ hji => hz j hji) (by simp)]
      exact cellCutoff_le_one J hJ a (X i)
    · have hz : ∀ i : Fin N, cellCutoff J (by omega) a (X i) = 0 := by simpa using ha
      simp only [hz, Finset.sum_const_zero, zero_le_one]
  exact div_le_div_of_nonneg_right hs (Nat.cast_nonneg N)

theorem mesh_tendsto_atTop {J : ℕ} (hJ : 3 ≤ J) :
    Tendsto (fun m => (mesh J m : ℝ)) atTop atTop := by
  have h : (1 : ℝ) < J := by exact_mod_cast (show 1 < J by omega)
  simpa only [mesh, Nat.cast_pow, Function.comp_def] using
    (tendsto_pow_atTop_atTop_of_one_lt h).comp (tendsto_add_atTop_nat 1)

/-- The original heavy particle threshold also makes a single particle light. -/
theorem single_particle_le_inner {N : ℕ} {β₀ t : ℝ} (ht : 0 < t)
    (hlarge : HeavyCoercivityConstants.particleThreshold β₀ (t / 4) ≤ N) :
    1 / (N : ℝ) ≤ t / 4 := by
  have hn : (0 : ℝ) < N := by
    exact_mod_cast HeavyCoercivityConstants.threshold_positive (by linarith : 0 < t / 4) hlarge
  have he := HeavyCoercivityConstants.threshold_eight hlarge
  have hh := (div_le_iff₀ (by linarith : 0 < t / 4)).mp he
  apply (div_le_iff₀ hn).mpr
  nlinarith only [hh]

/-- A collision-free configuration has an eventually zero remainder. The
vanishing persists because every later remainder contains the same zero factor. -/
theorem eventually_remainder_zero {N J : ℕ} (hJ : 3 ≤ J) {t : ℝ}
    (ht : 0 < t) (hNt : 1 / (N : ℝ) ≤ t / 4)
    (f : C(Configuration N, ℝ)) {X : Configuration N} (hX : X ∉ collisionSet N) :
    ∀ᶠ m in atTop, remainder N J (by omega) t f m X = 0 := by
  obtain ⟨δ, hδ, hsep⟩ := exists_pair_separation hX
  have he : ∀ᶠ m in atTop, 2 * Real.sqrt 2 / δ < (mesh J m : ℝ) :=
    (mesh_tendsto_atTop hJ).eventually (eventually_gt_atTop _)
  obtain ⟨m, hm⟩ := eventually_atTop.mp he
  have hmp : (0 : ℝ) < mesh J m := by exact_mod_cast mesh_pos (by omega : 0 < J) m
  have hsmall : 2 * Real.sqrt 2 / (mesh J m : ℝ) < δ := by
    apply (div_lt_iff₀ hmp).mpr
    have hh := (div_lt_iff₀ hδ).mp (hm m le_rfl)
    nlinarith only [hh]
  have hl := (maximumOccupation_le_single_particle (mesh_three hJ m) hsep hsmall).trans hNt
  have hz := remainder_succ_zero_low N J (by omega) ht f m hl
  refine eventually_atTop.mpr ⟨m + 1, fun n hn => ?_⟩
  have hp := remainder_persistent_zero N J (by omega) t f hz (n - (m + 1))
  simpa only [Nat.add_sub_of_le hn] using hp

theorem ae_eventually_remainder_zero {N J : ℕ} (hJ : 3 ≤ J) {t : ℝ}
    (ht : 0 < t) (hNt : 1 / (N : ℝ) ≤ t / 4) (β : ℝ)
    (f : C(Configuration N, ℝ)) :
    ∀ᵐ X ∂gibbsMeasure greenRealRepresentative N β,
      ∀ᶠ m in atTop, remainder N J (by omega) t f m X = 0 := by
  have hn : ∀ᵐ X ∂gibbsMeasure greenRealRepresentative N β, X ∉ collisionSet N := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using
      gibbs_collisionSet_null greenRealRepresentative N β
  exact hn.mono fun X hX => eventually_remainder_zero hJ ht hNt f hX

theorem remainder_square_bound (N J : ℕ) (hJ : 0 < J) (t : ℝ)
    (f : C(Configuration N, ℝ)) (m : ℕ) (X : Configuration N) :
    remainder N J hJ t f m X ^ 2 ≤ ‖f‖ ^ 2 := by
  have hh := (abs_remainder_le N J hJ t f m X).trans
    (show |f X| ≤ ‖f‖ by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm X)
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hh 2

/-- Both terms in the entropy formula converge, with one bound for every
resolution; no Lipschitz constant uniform in the resolution is needed. -/
theorem remainder_integrals_tendsto_zero {N J : ℕ} (hJ : 3 ≤ J) {t : ℝ}
    (ht : 0 < t) (hNt : 1 / (N : ℝ) ≤ t / 4) (β : ℝ)
    (f : C(Configuration N, ℝ)) :
    Tendsto (fun m => ∫ X, remainder N J (by omega) t f m X ^ 2
      ∂gibbsMeasure greenRealRepresentative N β) atTop (𝓝 0) ∧
    Tendsto (fun m => ∫ X, remainder N J (by omega) t f m X ^ 2 *
      Real.log (remainder N J (by omega) t f m X ^ 2)
      ∂gibbsMeasure greenRealRepresentative N β) atTop (𝓝 0) := by
  have hz := ae_eventually_remainder_zero hJ ht hNt β f
  constructor
  · have hh := tendsto_integral_of_dominated_convergence
      (μ := gibbsMeasure greenRealRepresentative N β)
      (F := fun m X => remainder N J (by omega) t f m X ^ 2)
      (f := fun _ => (0 : ℝ)) (fun _ => ‖f‖ ^ 2)
      (fun m => ((remainder N J (by omega) t f m).continuous.measurable.pow_const 2).aestronglyMeasurable)
      (integrable_const _) (fun m => Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact remainder_square_bound N J (by omega) t f m X) (by
        filter_upwards [hz] with X hX
        apply (tendsto_congr' (f₂ := fun _ : ℕ => (0 : ℝ)) (hX.mono fun m hm => by simp only [hm, zero_pow (by decide : 2 ≠ 0)])).mpr
        exact tendsto_const_nhds)
    simpa only [integral_zero] using hh
  · have hh := tendsto_integral_of_dominated_convergence
      (μ := gibbsMeasure greenRealRepresentative N β)
      (F := fun m X => remainder N J (by omega) t f m X ^ 2 *
        Real.log (remainder N J (by omega) t f m X ^ 2))
      (f := fun _ => (0 : ℝ)) (fun _ => 1 + (‖f‖ ^ 2) ^ 2)
      (fun m => (Real.continuous_mul_log.measurable.comp
        ((remainder N J (by omega) t f m).continuous.measurable.pow_const 2)).aestronglyMeasurable)
      (integrable_const _) (fun m => Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]
        exact (RelativeEntropyVariational.abs_mul_log_le_one_add_sq (sq_nonneg _)).trans
          (add_le_add (le_refl (1 : ℝ)) (pow_le_pow_left₀ (sq_nonneg _)
            (remainder_square_bound N J (by omega) t f m X) 2))) (by
        filter_upwards [hz] with X hX
        apply (tendsto_congr' (f₂ := fun _ : ℕ => (0 : ℝ)) (hX.mono fun m hm => by simp only [hm, zero_pow (by decide : 2 ≠ 0), zero_mul])).mpr
        exact tendsto_const_nhds)
    simpa only [integral_zero] using hh

theorem remainder_entropy_tendsto_zero {N J : ℕ} (hJ : 3 ≤ J) {t : ℝ}
    (ht : 0 < t) (hNt : 1 / (N : ℝ) ≤ t / 4) (β : ℝ)
    (f : C(Configuration N, ℝ)) :
    Tendsto (fun m => Rothaus.squareEntropy (gibbsMeasure greenRealRepresentative N β)
      (remainder N J (by omega) t f m)) atTop (𝓝 0) := by
  obtain ⟨hs, hl⟩ := remainder_integrals_tendsto_zero hJ ht hNt β f
  have hm := Real.continuous_mul_log.continuousAt.tendsto.comp hs
  simpa only [Rothaus.squareEntropy, Function.comp_def, zero_mul, sub_zero] using hl.sub hm

end PeriodicAttractiveLogGas.ResolutionRemainder
