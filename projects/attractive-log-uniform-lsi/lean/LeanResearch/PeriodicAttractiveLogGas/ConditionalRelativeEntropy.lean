import LeanResearch.PeriodicAttractiveLogGas.ProductRelativeEntropy
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! The finite joint-law conditional KL cost equals the integral of the
genuine conditional KL costs. This fills the conditional-integral bridge for
source eq:product-conditional-entropy. Joint finiteness yields, rather than
assumes, almost-everywhere conditional finiteness and outer integrability.
The jointly measurable kernel RN derivative supplies the measurable version.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal

namespace PeriodicAttractiveLogGas.ConditionalRelativeEntropy

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace.CountableOrCountablyGenerated α β]

def kernelLog (κ η : Kernel α β) (p : α × β) : ℝ :=
  Real.log (κ.rnDeriv η p.1 p.2).toReal

theorem measurable_kernelLog (κ η : Kernel α β) :
    Measurable (kernelLog κ η) :=
  (Kernel.measurable_rnDeriv κ η).ennreal_toReal.log

variable (μ : Measure α) [IsProbabilityMeasure μ]
  (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]

theorem joint_llr_eq_kernelLog (hac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    llr (μ ⊗ₘ κ) (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ κ] kernelLog κ η := by
  filter_upwards [hac.ae_eq (rnDeriv_measure_compProd_right μ κ η)] with p hp
  simp only [llr, kernelLog, hp]

theorem section_llr_eq_kernelLog {a : α} (hac : κ a ≪ η a) :
    llr (κ a) (η a) =ᵐ[κ a] fun b => kernelLog κ η (a, b) := by
  filter_upwards [hac.ae_eq (Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a))]
    with b hb
  simp only [llr, kernelLog, hb]

/-- Actual conditional relative entropy, including all needed finiteness
and integrability, follows from finite relative entropy of the joint laws. -/
theorem compProd_conditional_entropy
    (hfin : klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) ≠ ∞) :
    (∀ᵐ a ∂μ, klDiv (κ a) (η a) ≠ ∞) ∧
    Integrable (fun a => (klDiv (κ a) (η a)).toReal) μ ∧
    (klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal =
      ∫ a, (klDiv (κ a) (η a)).toReal ∂μ := by
  obtain ⟨hac, hi⟩ := klDiv_ne_top_iff.mp hfin
  have heq := joint_llr_eq_kernelLog μ κ η hac
  have hlog : Integrable (kernelLog κ η) (μ ⊗ₘ κ) := hi.congr heq
  have hsections := (Measure.integrable_compProd_iff hlog.aestronglyMeasurable).mp hlog
  have hdata : ∀ᵐ a ∂μ, klDiv (κ a) (η a) ≠ ∞ ∧
      (klDiv (κ a) (η a)).toReal = ∫ b, kernelLog κ η (a, b) ∂κ a := by
    filter_upwards [hac.kernel_of_compProd, hsections.1] with a ha hia
    have heqa := section_llr_eq_kernelLog κ η ha
    have hllr : Integrable (llr (κ a) (η a)) (κ a) := hia.congr heqa.symm
    refine ⟨klDiv_ne_top ha hllr, ?_⟩
    simpa only [toReal_klDiv ha hllr, probReal_univ, add_sub_cancel_right] using
      integral_congr_ae heqa
  have hout : Integrable (fun a => ∫ b, kernelLog κ η (a, b) ∂κ a) μ := by
    exact hlog.integral_compProd
  refine ⟨hdata.mono fun a ha => ha.1, hout.congr (hdata.mono fun a ha => ha.2.symm), ?_⟩
  calc
    (klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal =
        ∫ p, llr (μ ⊗ₘ κ) (μ ⊗ₘ η) p ∂(μ ⊗ₘ κ) := by
      simp only [toReal_klDiv hac hi, probReal_univ, add_sub_cancel_right]
    _ = ∫ p, kernelLog κ η p ∂(μ ⊗ₘ κ) := integral_congr_ae heq
    _ = ∫ a, ∫ b, kernelLog κ η (a, b) ∂κ a ∂μ := Measure.integral_compProd hlog
    _ = ∫ a, (klDiv (κ a) (η a)).toReal ∂μ :=
      integral_congr_ae (hdata.mono fun a ha => ha.2.symm)


section Product
open ProductRelativeEntropy

variable [StandardBorelSpace α] [Nonempty α] {n : ℕ}
  (Q : Measure (Fin (n + 1) → α)) [IsProbabilityMeasure Q]
  (ν : Fin (n + 1) → Measure α) [∀ i, IsProbabilityMeasure (ν i)]

/-- Each full-conditioning cost is finite when the total product-reference
entropy is finite. This uses the exact split chain rule, not tensorization
in the wrong direction. -/
theorem conditional_cost_finite (hfin : klDiv Q (Measure.pi ν) ≠ ∞)
    (i : Fin (n + 1)) :
    klDiv (Q.map (coordinateSplit i)) ((Q.map (outside i)).prod (ν i)) ≠ ∞ := by
  have hc := klDiv_prod_chain (Q.map (coordinateSplit i))
    (Measure.pi fun j => ν (i.succAbove j)) (ν i)
  rw [← map_pi_coordinateSplit i ν, klDiv_map_equiv, coordinateSplit_fst] at hc
  have hle : klDiv (Q.map (coordinateSplit i)) ((Q.map (outside i)).prod (ν i)) ≤
      klDiv Q (Measure.pi ν) := by
    rw [hc]
    exact le_add_left le_rfl
  exact ne_top_of_le_ne_top hfin hle

/-- Product-reference tensorization in the manuscript's conditional-integral
form for any genuine disintegration. All conditional finiteness and outer
integrability assertions are conclusions. -/
theorem product_tensorization_integral
    (κ : (i : Fin (n + 1)) → Kernel (Fin n → α) α)
    [∀ i, IsMarkovKernel (κ i)]
    (hκ : ∀ i, (Q.map (outside i)) ⊗ₘ (κ i) = Q.map (coordinateSplit i))
    (hfin : klDiv Q (Measure.pi ν) ≠ ∞) :
    (∀ i, ∀ᵐ Y ∂Q.map (outside i), klDiv (κ i Y) (ν i) ≠ ∞) ∧
    (∀ i, Integrable (fun Y => (klDiv (κ i Y) (ν i)).toReal) (Q.map (outside i))) ∧
    (klDiv Q (Measure.pi ν)).toReal ≤
      ∑ i, ∫ Y, (klDiv (κ i Y) (ν i)).toReal ∂Q.map (outside i) := by
  have hj i := conditional_cost_finite Q ν hfin i
  have hd i := compProd_conditional_entropy (Q.map (outside i)) (κ i)
    (Kernel.const (Fin n → α) (ν i)) (by
      simpa only [hκ i, Measure.compProd_const] using hj i)
  have he i :
      (klDiv (Q.map (coordinateSplit i)) ((Q.map (outside i)).prod (ν i))).toReal =
      ∫ Y, (klDiv (κ i Y) (ν i)).toReal ∂Q.map (outside i) := by
    simpa only [hκ i, Measure.compProd_const, Kernel.const_apply] using (hd i).2.2
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · simpa only [Kernel.const_apply] using (hd i).1
  · simpa only [Kernel.const_apply] using (hd i).2.1
  · have ht := ENNReal.toReal_mono
        (ENNReal.sum_ne_top.mpr fun i _ => hj i) (product_tensorization_joint Q ν)
    rw [ENNReal.toReal_sum (fun i _ => hj i)] at ht
    simpa only [he] using ht

end Product

end PeriodicAttractiveLogGas.ConditionalRelativeEntropy
