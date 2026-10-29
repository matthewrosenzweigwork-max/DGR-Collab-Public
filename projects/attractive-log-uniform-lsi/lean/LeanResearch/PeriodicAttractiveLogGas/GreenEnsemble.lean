import LeanResearch.PeriodicAttractiveLogGas.GreenBounds
import LeanResearch.PeriodicAttractiveLogGas.KernelRepresentatives
import LeanResearch.PeriodicAttractiveLogGas.Density

/-! Exact ensemble consequences of the constructed regular Green kernel.
The lower partition bound is unconditional; the finite-normalizer hypothesis
in the measure comparison is explicitly retained until collision integrability
is proved. No positive-coupling normalization is asserted in this module. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas

theorem measurePreserving_pair_difference (N : ℕ) {i j : Fin N} (hij : i ≠ j) :
    MeasurePreserving (fun x : Configuration N ↦ x i - x j)
      (referenceMeasure N) torusMeasure :=
  ((measurePreserving_fst (μ := torusMeasure) (ν := torusMeasure)).comp
    (measurePreserving_sub_prod torusMeasure torusMeasure)).comp
      (measurePreserving_pair_evaluation N hij)

theorem integrable_pair_kernel {g : Torus → ℝ} (hg : Integrable g torusMeasure)
    (N : ℕ) {i j : Fin N} (hij : i ≠ j) :
    Integrable (fun x : Configuration N ↦ g (x i - x j)) (referenceMeasure N) :=
  (measurePreserving_pair_difference N hij).integrable_comp_of_integrable hg

theorem integral_pair_kernel {g : Torus → ℝ} (hg : Integrable g torusMeasure)
    (N : ℕ) {i j : Fin N} (hij : i ≠ j) :
    (∫ x, g (x i - x j) ∂referenceMeasure N) = ∫ z, g z ∂torusMeasure := by
  have hmp := measurePreserving_pair_difference N hij
  have hm : AEStronglyMeasurable g (Measure.map (fun x : Configuration N ↦ x i - x j)
      (referenceMeasure N)) := by
    simpa only [hmp.map_eq] using hg.aestronglyMeasurable
  exact (integral_map hmp.aemeasurable hm).symm.trans (by rw [hmp.map_eq])

theorem integrable_pairEnergy {g : Torus → ℝ} (hg : Integrable g torusMeasure) (N : ℕ) :
    Integrable (pairEnergy g N) (referenceMeasure N) := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j hj
  exact integrable_pair_kernel hg N (Finset.mem_Ioi.mp hj).ne

theorem integral_pairEnergy_eq_zero {g : Torus → ℝ} (hg : Integrable g torusMeasure)
    (hzero : (∫ z, g z ∂torusMeasure) = 0) (N : ℕ) :
    (∫ x, pairEnergy g N x ∂referenceMeasure N) = 0 := by
  unfold pairEnergy
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro j hj
      exact (integral_pair_kernel hg N (Finset.mem_Ioi.mp hj).ne).trans hzero
    · intro j hj
      exact integrable_pair_kernel hg N (Finset.mem_Ioi.mp hj).ne
  · intro i _
    apply integrable_finsetSum
    intro j hj
    exact integrable_pair_kernel hg N (Finset.mem_Ioi.mp hj).ne

theorem integrable_gibbsWeight_iff {g : Torus → ℝ} (hg : Measurable g) (N : ℕ) (β : ℝ) :
    Integrable (gibbsWeight g N β) (referenceMeasure N) ↔ partitionFunction g N β ≠ ⊤ :=
  (lintegral_ofReal_ne_top_iff_integrable
    (measurable_gibbsWeight hg N β).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x ↦ (gibbsWeight_pos g N β x).le))).symm

/-- Jensen's lower bound proved by integrating the supporting affine function
of the exponential. Infinite partition functions are handled as extended values. -/
theorem one_le_partitionFunction_of_mean_zero {g : Torus → ℝ} (hg : Measurable g)
    (hgi : Integrable g torusMeasure) (hzero : (∫ z, g z ∂torusMeasure) = 0)
    (N : ℕ) (β : ℝ) : 1 ≤ partitionFunction g N β := by
  by_cases hfin : partitionFunction g N β ≠ ⊤
  · have hw := (integrable_gibbsWeight_iff hg N β).mpr hfin
    have hp := (integrable_pairEnergy hgi N).const_mul (β / (N : ℝ))
    have ha := hp.add (integrable_const (1 : ℝ))
    have hbound : (∫ x, (β / (N : ℝ)) * pairEnergy g N x + 1 ∂referenceMeasure N) ≤
        ∫ x, gibbsWeight g N β x ∂referenceMeasure N :=
      integral_mono ha hw (fun x ↦ Real.add_one_le_exp _)
    have ha0 : (∫ x, (β / (N : ℝ)) * pairEnergy g N x + 1 ∂referenceMeasure N) = 1 := by
      rw [integral_add hp (integrable_const _), integral_const_mul,
        integral_pairEnergy_eq_zero hgi hzero]
      simp
    rw [ha0] at hbound
    have hid := ofReal_integral_eq_lintegral_ofReal hw
      (Filter.Eventually.of_forall (fun x ↦ (gibbsWeight_pos g N β x).le))
    calc
      (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) := by norm_num
      _ ≤ ENNReal.ofReal (∫ x, gibbsWeight g N β x ∂referenceMeasure N) :=
        ENNReal.ofReal_le_ofReal hbound
      _ = partitionFunction g N β := hid
  · simp only [not_ne_iff] at hfin
    rw [hfin]
    exact le_top

theorem regularGreen_partitionFunction_eq (N : ℕ) (β : ℝ) :
    partitionFunction regularGreenRepresentative N β =
      partitionFunction greenRealRepresentative N β :=
  partitionFunction_congr_ae_kernel regularGreenRepresentative_ae N β

theorem regularGreen_gibbsMeasure_eq (N : ℕ) (β : ℝ) :
    gibbsMeasure regularGreenRepresentative N β = gibbsMeasure greenRealRepresentative N β :=
  gibbsMeasure_congr_ae_kernel regularGreenRepresentative_ae N β

theorem one_le_greenPartitionFunction (N : ℕ) (β : ℝ) :
    1 ≤ partitionFunction greenRealRepresentative N β :=
  one_le_partitionFunction_of_mean_zero greenRealRepresentative_measurable
    greenRealRepresentative_integrable greenRealRepresentative_integral_zero N β

theorem exists_reference_le_greenGibbs_of_partition_finite (N : ℕ) {β : ℝ} (hβ : 0 ≤ β)
    (hfin : partitionFunction greenRealRepresentative N β ≠ ⊤) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ referenceMeasure N ≤ c • gibbsMeasure greenRealRepresentative N β := by
  obtain ⟨C, _, hC⟩ := exists_regularGreenRepresentative_lower_bound
  have hfin' : partitionFunction regularGreenRepresentative N β ≠ ⊤ := by
    rwa [regularGreen_partitionFunction_eq]
  obtain ⟨c, hc, hb⟩ := exists_referenceMeasure_le_finite_smul_gibbsMeasure
    regularGreenRepresentative_measurable hC N hβ hfin'
  exact ⟨c, hc, by simpa only [regularGreen_gibbsMeasure_eq] using hb⟩

end PeriodicAttractiveLogGas
