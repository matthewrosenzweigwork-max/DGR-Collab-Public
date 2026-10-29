import LeanResearch.PeriodicAttractiveLogGas.Collisions
import LeanResearch.PeriodicAttractiveLogGas.PeriodicCalculus
import Mathlib.MeasureTheory.Group.Prod

/-! The Gibbs construction depends only on the Haar almost-everywhere class of
the pair kernel. This permits passing from the constructed Green L2 class to
a later locally smooth representative without changing the ensemble. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace PeriodicAttractiveLogGas

theorem measurePreserving_pair_evaluation (N : ℕ) {i j : Fin N} (hij : i ≠ j) :
    MeasurePreserving (fun x : Configuration N ↦ (x i, x j))
      (referenceMeasure N) (torusMeasure.prod torusMeasure) := by
  have hind := (iIndepFun_pi (μ := fun _ : Fin N ↦ torusMeasure)
    (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)).indepFun hij
  have hmap := hind.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  rw [(measurePreserving_eval (fun _ : Fin N ↦ torusMeasure) i).map_eq,
    (measurePreserving_eval (fun _ : Fin N ↦ torusMeasure) j).map_eq] at hmap
  exact ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), hmap⟩

theorem quasiMeasurePreserving_pair_difference (N : ℕ) {i j : Fin N} (hij : i ≠ j) :
    Measure.QuasiMeasurePreserving (fun x : Configuration N ↦ x i - x j)
      (referenceMeasure N) torusMeasure :=
  (quasiMeasurePreserving_sub torusMeasure torusMeasure).comp
    (measurePreserving_pair_evaluation N hij).quasiMeasurePreserving

theorem gibbsWeight_congr_ae_kernel {g h : Torus → ℝ} (hgh : g =ᵐ[torusMeasure] h)
    (N : ℕ) (β : ℝ) :
    gibbsWeight g N β =ᵐ[referenceMeasure N] gibbsWeight h N β := by
  have hp : ∀ᵐ x ∂referenceMeasure N, ∀ i j : Fin N,
      i ≠ j → g (x i - x j) = h (x i - x j) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ hne ↦ (hne hij).elim
    · filter_upwards [(quasiMeasurePreserving_pair_difference N hij).ae_eq_comp hgh] with x hx
      exact fun _ ↦ hx
  filter_upwards [hp] with x hx
  have he : pairEnergy g N x = pairEnergy h N x := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    exact hx i j (Finset.mem_Ioi.mp hj).ne
  simp only [gibbsWeight, he]

theorem partitionFunction_congr_ae_kernel {g h : Torus → ℝ} (hgh : g =ᵐ[torusMeasure] h)
    (N : ℕ) (β : ℝ) : partitionFunction g N β = partitionFunction h N β :=
  lintegral_congr_ae ((gibbsWeight_congr_ae_kernel hgh N β).mono fun _ hx ↦ congrArg _ hx)

theorem gibbsMeasure_congr_ae_kernel {g h : Torus → ℝ} (hgh : g =ᵐ[torusMeasure] h)
    (N : ℕ) (β : ℝ) : gibbsMeasure g N β = gibbsMeasure h N β := by
  unfold gibbsMeasure
  rw [partitionFunction_congr_ae_kernel hgh N β]
  congr 1
  exact withDensity_congr_ae
    ((gibbsWeight_congr_ae_kernel hgh N β).mono fun _ hx ↦ congrArg _ hx)

end PeriodicAttractiveLogGas
