import DGRHS.Gaussian.SharpnessNormalizedAtom
import DGRHS.Gaussian.FeatureRateSourceKernel

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {X α J : Type*} [MeasurableSpace X] [Fintype J]

lemma sharpness_normalized_pair_preserving (μ : Measure X) [IsFiniteMeasure μ]
    (A : α → Set X) (hm : ∀ i, 0 < (μ (A i)).toReal)
    (l : J → α) (i j : J) (hij : i ≠ j) :
    MeasurePreserving (fun x : J → X => (x i,x j))
      (Measure.pi (fun i => sharpnessNormalizedAtom μ (A (l i))))
      ((sharpnessNormalizedAtom μ (A (l i))).prod (sharpnessNormalizedAtom μ (A (l j)))) := by
  let ν := fun i : J => sharpnessNormalizedAtom μ (A (l i))
  haveI : ∀ i,IsProbabilityMeasure (ν i) := fun i => sharpnessNormalizedAtom_probability μ _ (hm _)
  have hi := measurePreserving_eval ν i
  have hj := measurePreserving_eval ν j
  have hind : iIndepFun (fun i (x : J → X) => x i) (Measure.pi ν) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j),?_⟩
  simpa only [hi.map_eq,hj.map_eq] using
    (hind.indepFun hij).map_prod_eq_prod_map_map hi.measurable.aemeasurable hj.measurable.aemeasurable

lemma sharpness_conditional_pair_integrable (μ : Measure X) [IsFiniteMeasure μ]
    (H : X × X → ℝ) (hH : Integrable H (μ.prod μ))
    (A : α → Set X) (hA : ∀ i, MeasurableSet (A i)) (hm : ∀ i, 0 < (μ (A i)).toReal)
    (l : J → α) (i j : J) (hij : i ≠ j) :
    Integrable (fun x : J → X => H (x i,x j))
      (Measure.pi (fun i => sharpnessNormalizedAtom μ (A (l i)))) := by
  exact (sharpness_normalized_pair_preserving μ A hm l i j hij).integrable_comp_of_integrable
    (sharpnessNormalizedAtom_pair_integrable μ H hH _ _ (hA _) (hA _) (hm _) (hm _))

lemma sharpness_conditional_pair_integral (μ : Measure X) [IsFiniteMeasure μ]
    (H : X × X → ℝ) (hH : Integrable H (μ.prod μ))
    (A : α → Set X) (hA : ∀ i, MeasurableSet (A i)) (hm : ∀ i, 0 < (μ (A i)).toReal)
    (l : J → α) (i j : J) (hij : i ≠ j) :
    (∫ x : J → X,H (x i,x j) ∂Measure.pi (fun i => sharpnessNormalizedAtom μ (A (l i)))) =
      sharpnessAtomAverage μ H (A (l i)) (A (l j)) := by
  have hp := sharpness_normalized_pair_preserving μ A hm l i j hij
  have hh := sharpnessNormalizedAtom_pair_integrable μ H hH (A (l i)) (A (l j)) (hA (l i)) (hA (l j)) (hm (l i)) (hm (l j))
  calc
    _ = ∫ p,H p ∂(sharpnessNormalizedAtom μ (A (l i))).prod (sharpnessNormalizedAtom μ (A (l j))) := by
      have he := integral_map hp.measurable.aemeasurable (by rw [hp.map_eq]; exact hh.aestronglyMeasurable)
      rw [hp.map_eq] at he
      exact he.symm
    _ = _ := sharpnessNormalizedAtom_pair_integral μ H _ _

/-- Actual proper conditional expectation of the entire off-diagonal array.
Independence is between positions, even when two positions share an atom. -/
theorem sharpness_conditional_particle_mean (μ : Measure X) [IsFiniteMeasure μ]
    (H : X × X → ℝ) (hH : Integrable H (μ.prod μ))
    (A : α → Set X) (hA : ∀ i, MeasurableSet (A i)) (hm : ∀ i, 0 < (μ (A i)).toReal)
    (N : ℕ) (l : Fin N → α) :
    Integrable (sourceKernelParticleStatistic H N)
      (Measure.pi (fun i => sharpnessNormalizedAtom μ (A (l i)))) ∧
      (∫ x,sourceKernelParticleStatistic H N x
        ∂Measure.pi (fun i => sharpnessNormalizedAtom μ (A (l i)))) =
        sourceKernelParticleStatistic (fun p : α × α => sharpnessAtomAverage μ H (A p.1) (A p.2)) N l := by
  let ν := Measure.pi (fun i => sharpnessNormalizedAtom μ (A (l i)))
  have ht (i j : Fin N) : Integrable (fun x : Fin N → X => if i = j then 0 else H (x i,x j)) ν := by
    by_cases hij : i = j
    · simp only [hij,if_true]
      exact (integrable_zero (Fin N → X) ℝ ν)
    · simp only [hij,if_false]
      exact sharpness_conditional_pair_integrable μ H hH A hA hm l i j hij
  have hsum : Integrable (fun x : Fin N → X => ∑ i,∑ j,if i = j then 0 else H (x i,x j)) ν := by
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ht i j))
  refine ⟨hsum.const_mul _,?_⟩
  unfold sourceKernelParticleStatistic
  rw [integral_const_mul,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ht i j))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => ht i j)]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij,if_false]
    exact sharpness_conditional_pair_integral μ H hH A hA hm l i j hij

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_conditional_particle_mean
#check @DGRHS.Gaussian.sharpness_conditional_particle_mean
