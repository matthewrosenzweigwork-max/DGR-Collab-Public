import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DGRHS.Decoupling

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι]
variable (μ : Measure S) [IsProbabilityMeasure μ]

/-- Two independent copies of every sample coordinate. -/
def productSamples : Measure (ι → S × S) :=
  Measure.pi (fun _ ↦ μ.prod μ)

instance : IsProbabilityMeasure (productSamples (ι := ι) μ) := by
  unfold productSamples; infer_instance

/-- Distinct coordinates of an iid finite product have the actual product law. -/
theorem pair_eval_measurePreserving (i j : ι) (hij : i ≠ j) :
    MeasurePreserving (fun x : ι → S ↦ (x i, x j))
      (Measure.pi (fun _ ↦ μ)) (μ.prod μ) := by
  have hi : iIndepFun (fun i (x : ι → S) ↦ x i) (Measure.pi (fun _ ↦ μ)) :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  rw [(hi.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable,
    (measurePreserving_eval (fun _ : ι ↦ μ) i).map_eq,
    (measurePreserving_eval (fun _ : ι ↦ μ) j).map_eq]

/-- Different-index first/second copies also have exactly `μ.prod μ` law. -/
theorem decoupled_pair_measurePreserving (i j : ι) (hij : i ≠ j) :
    MeasurePreserving (fun x : ι → S × S ↦ ((x i).1, (x j).2))
      (productSamples μ) (μ.prod μ) := by
  have hi : iIndepFun (fun i (x : ι → S × S) ↦ x i) (productSamples μ) :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have h := (hi.indepFun hij).comp measurable_fst measurable_snd
  have hfst : MeasurePreserving (fun x : ι → S × S ↦ (x i).1)
      (productSamples μ) μ :=
    measurePreserving_fst.comp (measurePreserving_eval (fun _ : ι ↦ μ.prod μ) i)
  have hsnd : MeasurePreserving (fun x : ι → S × S ↦ (x j).2)
      (productSamples μ) μ :=
    measurePreserving_snd.comp (measurePreserving_eval (fun _ : ι ↦ μ.prod μ) j)
  refine ⟨hfst.measurable.prodMk hsnd.measurable, ?_⟩
  have hh := h.map_prod_eq_prod_map_map hfst.aemeasurable hsnd.aemeasurable
  simpa only [Function.comp_def, hfst.map_eq, hsnd.map_eq] using hh

/-- Swapping the two copies separately at chosen indices preserves the full law. -/
def swapSelected (s : ι → Bool) (x : ι → S × S) (i : ι) : S × S :=
  if s i then x i else (x i).swap

theorem swapSelected_measurePreserving (s : ι → Bool) :
    MeasurePreserving (swapSelected s) (productSamples μ) (productSamples μ) := by
  unfold productSamples swapSelected
  apply measurePreserving_pi (fun _ : ι ↦ μ.prod μ) (fun _ : ι ↦ μ.prod μ)
    (f := fun i z ↦ if s i then z else z.swap)
  intro i
  cases hs : s i
  · simpa only [hs, Bool.false_eq_true, ↓reduceIte] using
      (Measure.measurePreserving_swap (μ := μ) (ν := μ))
  · convert MeasurePreserving.id (μ.prod μ) using 1
    ext z <;> simp [hs]

lemma swapSelected_involutive (s : ι → Bool) : Function.Involutive (swapSelected (S := S) s) := by
  intro x
  funext i
  cases hs : s i <;> simp [swapSelected, hs]

/-- A measurable equivalence makes the copy-exchange change of variables valid for all integrands. -/
def swapSelectedEquiv (s : ι → Bool) : (ι → S × S) ≃ᵐ (ι → S × S) where
  toFun := swapSelected s
  invFun := swapSelected s
  left_inv := swapSelected_involutive s
  right_inv := swapSelected_involutive s
  measurable_toFun := (swapSelected_measurePreserving μ s).measurable
  measurable_invFun := (swapSelected_measurePreserving μ s).measurable

/-- Retain exactly one side at each index and integrate fresh copies of the omitted sides. -/
def spliceCoordinate (b : Bool) (z : (S × S) × (S × S)) : S × S :=
  if b then (z.1.1, z.2.2) else (z.2.1, z.1.2)

lemma spliceCoordinate_true_measurePreserving :
    MeasurePreserving (spliceCoordinate (S := S) true)
      ((μ.prod μ).prod (μ.prod μ)) (μ.prod μ) := by
  change MeasurePreserving (fun z : (S × S) × (S × S) ↦ (z.1.1, z.2.2))
    ((μ.prod μ).prod (μ.prod μ)) (μ.prod μ)
  have h := indepFun_prod (μ := μ.prod μ) (ν := μ.prod μ)
    (X := Prod.fst) (Y := Prod.snd) measurable_fst measurable_snd
  have hfst : MeasurePreserving (fun z : (S × S) × (S × S) ↦ z.1.1)
      ((μ.prod μ).prod (μ.prod μ)) μ :=
    measurePreserving_fst.comp measurePreserving_fst
  have hsnd : MeasurePreserving (fun z : (S × S) × (S × S) ↦ z.2.2)
      ((μ.prod μ).prod (μ.prod μ)) μ :=
    measurePreserving_snd.comp measurePreserving_snd
  refine ⟨by fun_prop, ?_⟩
  have hh := h.map_prod_eq_prod_map_map hfst.aemeasurable hsnd.aemeasurable
  simpa only [spliceCoordinate, ↓reduceIte, Function.comp_def, hfst.map_eq, hsnd.map_eq] using hh

lemma spliceCoordinate_measurePreserving (b : Bool) :
    MeasurePreserving (spliceCoordinate (S := S) b)
      ((μ.prod μ).prod (μ.prod μ)) (μ.prod μ) := by
  cases b
  · change MeasurePreserving (fun z : (S × S) × (S × S) ↦ (z.2.1, z.1.2))
      ((μ.prod μ).prod (μ.prod μ)) (μ.prod μ)
    have h := (spliceCoordinate_true_measurePreserving μ).comp
      (Measure.measurePreserving_swap (μ := μ.prod μ) (ν := μ.prod μ))
    simpa only [spliceCoordinate, ↓reduceIte, Function.comp_def, Prod.swap] using h
  · exact spliceCoordinate_true_measurePreserving μ

def spliceSamples (s : ι → Bool) (z : (ι → S × S) × (ι → S × S)) (i : ι) : S × S :=
  spliceCoordinate (s i) (z.1 i, z.2 i)

/-- The spliced array has the complete original product law, without any extra sample hypothesis. -/
theorem spliceSamples_measurePreserving (s : ι → Bool) :
    MeasurePreserving (spliceSamples s) ((productSamples μ).prod (productSamples μ))
      (productSamples μ) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow (S × S) (S × S) ι
  have he : MeasurePreserving e
      (Measure.pi (fun _ : ι ↦ (μ.prod μ).prod (μ.prod μ)))
      ((productSamples μ).prod (productSamples μ)) :=
    measurePreserving_arrowProdEquivProdArrow (S × S) (S × S) ι
      (fun _ ↦ μ.prod μ) (fun _ ↦ μ.prod μ)
  have hp := measurePreserving_pi
    (fun _ : ι ↦ (μ.prod μ).prod (μ.prod μ)) (fun _ : ι ↦ μ.prod μ)
    (f := fun i ↦ spliceCoordinate (s i)) (fun i ↦ spliceCoordinate_measurePreserving μ (s i))
  exact hp.comp (he.symm e)

/-- The finite high moment hypothesis lifts to the coupled distinct-index term. -/
theorem memLp_coupled_term (h : S × S → ℝ) (p : ℝ≥0∞)
    (hh : MemLp h p (μ.prod μ)) (i j : ι) (hij : i ≠ j) :
    MemLp (fun x : ι → S ↦ h (x i, x j)) p (Measure.pi (fun _ ↦ μ)) := by
  exact hh.comp_measurePreserving (pair_eval_measurePreserving μ i j hij)

/-- The same hypothesis lifts to the independent-copy distinct-index term. -/
theorem memLp_decoupled_term (h : S × S → ℝ) (p : ℝ≥0∞)
    (hh : MemLp h p (μ.prod μ)) (i j : ι) (hij : i ≠ j) :
    MemLp (fun x : ι → S × S ↦ h ((x i).1, (x j).2)) p (productSamples μ) := by
  exact hh.comp_measurePreserving (decoupled_pair_measurePreserving μ i j hij)

#print axioms DGRHS.Decoupling.spliceSamples_measurePreserving
#print axioms DGRHS.Decoupling.pair_eval_measurePreserving
#print axioms DGRHS.Decoupling.decoupled_pair_measurePreserving
#print axioms DGRHS.Decoupling.swapSelected_measurePreserving
#print axioms DGRHS.Decoupling.memLp_coupled_term
#print axioms DGRHS.Decoupling.memLp_decoupled_term

end DGRHS.Decoupling
