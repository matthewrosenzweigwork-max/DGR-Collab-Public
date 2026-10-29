import DGRHS.Concentration.ReplacementEntropy

noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace DGRHS.Concentration

lemma measurePreserving_pi_coordinate {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n) :
    MeasurePreserving (fun ω : Fin n → Ω ↦ ω i) (Measure.pi μ) (μ i) := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    have he := measurePreserving_piFinSuccAbove μ i
    have h := (measurePreserving_fst (μ := μ i)
      (ν := Measure.pi fun j ↦ μ (i.succAbove j))).comp he
    exact h

lemma measurePreserving_copy_coordinate {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n) :
    MeasurePreserving (fun p : (Fin n → Ω) × (Fin n → Ω) ↦ (p.1,p.2 i))
      ((Measure.pi μ).prod (Measure.pi μ)) ((Measure.pi μ).prod (μ i)) :=
  (MeasurePreserving.id (Measure.pi μ)).prod (measurePreserving_pi_coordinate μ i)

/-- A genuine independent full vector supplies each fresh coordinate with its exact law. -/
lemma full_copy_replacement_integrable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    {Z : (Fin n → Ω) → ℝ} {B : ℝ}
    (hZ : AEStronglyMeasurable Z (Measure.pi μ))
    (hB : ∀ᵐ ω ∂Measure.pi μ, |Z ω| ≤ B) (lam : ℝ) (i : Fin n) :
    Integrable (fun p : (Fin n → Ω) × (Fin n → Ω) ↦ Real.exp (lam*Z p.1)*
      (max (Z p.1-Z (Function.update p.1 i (p.2 i))) 0)^2)
      ((Measure.pi μ).prod (Measure.pi μ)) := by
  exact (measurePreserving_copy_coordinate μ i).integrable_comp_of_integrable
    (bounded_spliced_pair_integrable μ hZ hB lam i)

lemma full_copy_replacement_integral {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    {Z : (Fin n → Ω) → ℝ} {B : ℝ}
    (hZ : AEStronglyMeasurable Z (Measure.pi μ))
    (hB : ∀ᵐ ω ∂Measure.pi μ, |Z ω| ≤ B) (lam : ℝ) (i : Fin n) :
    (∫ p : (Fin n → Ω) × (Fin n → Ω), Real.exp (lam*Z p.1)*
      (max (Z p.1-Z (Function.update p.1 i (p.2 i))) 0)^2
      ∂((Measure.pi μ).prod (Measure.pi μ))) =
    ∫ p : (Fin n → Ω) × Ω, Real.exp (lam*Z p.1)*
      (max (Z p.1-Z (Function.update p.1 i p.2)) 0)^2
      ∂((Measure.pi μ).prod (μ i)) := by
  let φ := fun p : (Fin n → Ω) × (Fin n → Ω) ↦ (p.1,p.2 i)
  let g := fun p : (Fin n → Ω) × Ω ↦ Real.exp (lam*Z p.1)*
    (max (Z p.1-Z (Function.update p.1 i p.2)) 0)^2
  have hp : MeasurePreserving φ ((Measure.pi μ).prod (Measure.pi μ))
      ((Measure.pi μ).prod (μ i)) := measurePreserving_copy_coordinate μ i
  have hg : AEStronglyMeasurable g
      (Measure.map φ ((Measure.pi μ).prod (Measure.pi μ))) := by
    rw [hp.map_eq]
    exact (bounded_spliced_pair_integrable μ hZ hB lam i).aestronglyMeasurable
  have hi := integral_map hp.aemeasurable hg
  rw [hp.map_eq] at hi
  exact hi.symm

lemma full_copy_replacement_sum_integrable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    {Z : (Fin n → Ω) → ℝ} {B : ℝ}
    (hZ : AEStronglyMeasurable Z (Measure.pi μ))
    (hB : ∀ᵐ ω ∂Measure.pi μ, |Z ω| ≤ B) (lam : ℝ) :
    Integrable (fun p : (Fin n → Ω) × (Fin n → Ω) ↦ Real.exp (lam*Z p.1)*
      (∑ i, (max (Z p.1-Z (Function.update p.1 i (p.2 i))) 0)^2))
      ((Measure.pi μ).prod (Measure.pi μ)) := by
  have h := integrable_finsetSum Finset.univ
    (fun i _ ↦ full_copy_replacement_integrable μ hZ hB lam i)
  exact h.congr (Filter.Eventually.of_forall fun p ↦ by simp only [Finset.mul_sum])

/-- One-sided replacement entropy on the actual product of two full independent vector laws. -/
theorem finite_product_full_copy_replacement_entropy {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : (Fin n → Ω) → ℝ) (B : ℝ)
    (hZ : AEStronglyMeasurable Z (Measure.pi μ))
    (hB : ∀ᵐ ω ∂Measure.pi μ, |Z ω| ≤ B) (lam : ℝ) (hlam : 0 ≤ lam) :
    functionalEntropy (Measure.pi μ) (fun ω ↦ Real.exp (lam*Z ω)) ≤
      lam^2 * (∫ p : (Fin n → Ω) × (Fin n → Ω), Real.exp (lam*Z p.1)*
        (∑ i, (max (Z p.1-Z (Function.update p.1 i (p.2 i))) 0)^2)
        ∂((Measure.pi μ).prod (Measure.pi μ))) := by
  have h := finite_product_replacement_entropy n μ Z B hZ hB lam hlam
  have hi : (∑ i, ∫ p : (Fin n → Ω) × Ω, Real.exp (lam*Z p.1)*
      (max (Z p.1-Z (Function.update p.1 i p.2)) 0)^2
      ∂((Measure.pi μ).prod (μ i))) =
      ∫ p : (Fin n → Ω) × (Fin n → Ω), Real.exp (lam*Z p.1)*
        (∑ i, (max (Z p.1-Z (Function.update p.1 i (p.2 i))) 0)^2)
        ∂((Measure.pi μ).prod (Measure.pi μ)) := by
    calc
      _ = ∑ i, ∫ p : (Fin n → Ω) × (Fin n → Ω), Real.exp (lam*Z p.1)*
          (max (Z p.1-Z (Function.update p.1 i (p.2 i))) 0)^2
          ∂((Measure.pi μ).prod (Measure.pi μ)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (full_copy_replacement_integral μ hZ hB lam i).symm
      _ = ∫ p : (Fin n → Ω) × (Fin n → Ω), ∑ i, Real.exp (lam*Z p.1)*
          (max (Z p.1-Z (Function.update p.1 i (p.2 i))) 0)^2
          ∂((Measure.pi μ).prod (Measure.pi μ)) := by
        rw [integral_finsetSum Finset.univ
          (fun i _ ↦ full_copy_replacement_integrable μ hZ hB lam i)]
      _ = _ := by congr 1; funext p; rw [Finset.mul_sum]
  rw [hi] at h
  exact h

#print axioms DGRHS.Concentration.measurePreserving_pi_coordinate
#print axioms DGRHS.Concentration.measurePreserving_copy_coordinate
#print axioms DGRHS.Concentration.full_copy_replacement_integral
#print axioms DGRHS.Concentration.full_copy_replacement_sum_integrable
#print axioms DGRHS.Concentration.finite_product_full_copy_replacement_entropy
#check @DGRHS.Concentration.finite_product_full_copy_replacement_entropy

end DGRHS.Concentration
