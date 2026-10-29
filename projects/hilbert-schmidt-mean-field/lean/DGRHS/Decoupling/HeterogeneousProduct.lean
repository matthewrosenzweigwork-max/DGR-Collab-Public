import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

noncomputable section
open MeasureTheory ProbabilityTheory

namespace DGRHS.Decoupling.Heterogeneous

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι]
variable (μ : ι → Measure S) [∀ i, IsProbabilityMeasure (μ i)]

/-- At each coordinate, retain an independent first and second sample with law μ i. -/
def heterogeneousPairSamples : Measure (ι → S × S) :=
  Measure.pi (fun i ↦ (μ i).prod (μ i))

instance heterogeneousPairSamples_isProbabilityMeasure :
    IsProbabilityMeasure (heterogeneousPairSamples μ) := by
  unfold heterogeneousPairSamples
  infer_instance

/-- The explicit rearrangement of two independent sample arrays as coordinate pairs. -/
def pairArrays (p : (ι → S) × (ι → S)) : ι → S × S :=
  fun i ↦ (p.1 i, p.2 i)

theorem pairArrays_measurePreserving :
    MeasurePreserving (pairArrays (ι := ι))
      ((Measure.pi μ).prod (Measure.pi μ)) (heterogeneousPairSamples μ) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow S S ι
  have he : MeasurePreserving e (Measure.pi (fun i ↦ (μ i).prod (μ i)))
      ((Measure.pi μ).prod (Measure.pi μ)) :=
    measurePreserving_arrowProdEquivProdArrow S S ι μ μ
  convert he.symm e using 1 <;> rfl

/-- Projection onto the first independent copy at each coordinate. -/
def firstCopySamples (z : ι → S × S) : ι → S :=
  fun i ↦ (z i).1

theorem firstCopySamples_measurePreserving :
    MeasurePreserving (firstCopySamples (ι := ι))
      (heterogeneousPairSamples μ) (Measure.pi μ) := by
  unfold firstCopySamples heterogeneousPairSamples
  exact measurePreserving_pi (fun i ↦ (μ i).prod (μ i)) μ
    (f := fun _ ↦ Prod.fst) (fun _ ↦ measurePreserving_fst)

/-- Projection onto the second independent copy at each coordinate. -/
def secondCopySamples (z : ι → S × S) : ι → S :=
  fun i ↦ (z i).2

theorem secondCopySamples_measurePreserving :
    MeasurePreserving (secondCopySamples (ι := ι))
      (heterogeneousPairSamples μ) (Measure.pi μ) := by
  unfold secondCopySamples heterogeneousPairSamples
  exact measurePreserving_pi (fun i ↦ (μ i).prod (μ i)) μ
    (f := fun _ ↦ Prod.snd) (fun _ ↦ measurePreserving_snd)

/-- Select one of the two copies independently at each coordinate. -/
def selectedCopySamples (s : ι → Bool) (z : ι → S × S) : ι → S :=
  fun i ↦ if s i then (z i).1 else (z i).2

theorem selectedCopySamples_measurePreserving (s : ι → Bool) :
    MeasurePreserving (selectedCopySamples (ι := ι) s)
      (heterogeneousPairSamples μ) (Measure.pi μ) := by
  unfold selectedCopySamples heterogeneousPairSamples
  exact measurePreserving_pi (fun i ↦ (μ i).prod (μ i)) μ
    (f := fun i z ↦ if s i then z.1 else z.2)
    (fun i ↦ by
      cases hs : s i
      · simpa [hs] using
          (measurePreserving_snd :
            MeasurePreserving (Prod.snd : S × S → S) ((μ i).prod (μ i)) (μ i))
      · simpa [hs] using
          (measurePreserving_fst :
            MeasurePreserving (Prod.fst : S × S → S) ((μ i).prod (μ i)) (μ i)))

/-- Keep the selected first-copy coordinates on A and selected second-copy coordinates off A,
while filling the other two coordinates from a fresh independent pair array. -/
def spliceCoordinate (b : Bool) (q : (S × S) × (S × S)) : S × S :=
  if b then (q.1.1, q.2.2) else (q.2.1, q.1.2)

theorem spliceCoordinate_true_measurePreserving (i : ι) :
    MeasurePreserving (spliceCoordinate true)
      (((μ i).prod (μ i)).prod ((μ i).prod (μ i))) ((μ i).prod (μ i)) := by
  change MeasurePreserving (fun q : (S × S) × (S × S) ↦ (q.1.1, q.2.2))
    (((μ i).prod (μ i)).prod ((μ i).prod (μ i))) ((μ i).prod (μ i))
  have hind := indepFun_prod (μ := (μ i).prod (μ i)) (ν := (μ i).prod (μ i))
    (X := Prod.fst) (Y := Prod.snd) measurable_fst measurable_snd
  have hfst : MeasurePreserving
      (fun q : (S × S) × (S × S) ↦ q.1.1)
      (((μ i).prod (μ i)).prod ((μ i).prod (μ i))) (μ i) :=
    measurePreserving_fst.comp measurePreserving_fst
  have hsnd : MeasurePreserving
      (fun q : (S × S) × (S × S) ↦ q.2.2)
      (((μ i).prod (μ i)).prod ((μ i).prod (μ i))) (μ i) :=
    measurePreserving_snd.comp measurePreserving_snd
  refine ⟨by fun_prop, ?_⟩
  have hmap := hind.map_prod_eq_prod_map_map hfst.aemeasurable hsnd.aemeasurable
  simpa only [Function.comp_def, hfst.map_eq, hsnd.map_eq] using hmap

theorem spliceCoordinate_measurePreserving (i : ι) (b : Bool) :
    MeasurePreserving (spliceCoordinate b)
      (((μ i).prod (μ i)).prod ((μ i).prod (μ i))) ((μ i).prod (μ i)) := by
  cases b
  · change MeasurePreserving
      (fun q : (S × S) × (S × S) ↦ (q.2.1, q.1.2))
      (((μ i).prod (μ i)).prod ((μ i).prod (μ i))) ((μ i).prod (μ i))
    have h := (spliceCoordinate_true_measurePreserving μ i).comp
      (Measure.measurePreserving_swap
        (μ := (μ i).prod (μ i)) (ν := (μ i).prod (μ i)))
    simpa only [spliceCoordinate, ↓reduceIte, Function.comp_def, Prod.swap] using h
  · exact spliceCoordinate_true_measurePreserving μ i

/-- Fill each index with the cross-selected pair of the retained and fresh arrays. -/
def splicePairArrays (s : ι → Bool) (z w : ι → S × S) : ι → S × S :=
  fun i ↦ spliceCoordinate (s i) (z i, w i)

theorem splicePairArrays_measurePreserving (s : ι → Bool) :
    MeasurePreserving (fun p : (ι → S × S) × (ι → S × S) ↦
      splicePairArrays (ι := ι) s p.1 p.2)
      ((heterogeneousPairSamples μ).prod (heterogeneousPairSamples μ))
      (heterogeneousPairSamples μ) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow (S × S) (S × S) ι
  have he : MeasurePreserving e
      (Measure.pi (fun i ↦ ((μ i).prod (μ i)).prod ((μ i).prod (μ i))))
      ((heterogeneousPairSamples μ).prod (heterogeneousPairSamples μ)) :=
    measurePreserving_arrowProdEquivProdArrow (S × S) (S × S) ι
      (fun i ↦ (μ i).prod (μ i)) (fun i ↦ (μ i).prod (μ i))
  have hp := measurePreserving_pi
    (fun i ↦ ((μ i).prod (μ i)).prod ((μ i).prod (μ i)))
    (fun i ↦ (μ i).prod (μ i))
    (f := fun i ↦ spliceCoordinate (s i))
    (fun i ↦ spliceCoordinate_measurePreserving μ i (s i))
  exact hp.comp (he.symm e)

end DGRHS.Decoupling.Heterogeneous

#print axioms DGRHS.Decoupling.Heterogeneous.pairArrays_measurePreserving
#print axioms DGRHS.Decoupling.Heterogeneous.firstCopySamples_measurePreserving
#print axioms DGRHS.Decoupling.Heterogeneous.secondCopySamples_measurePreserving
#print axioms DGRHS.Decoupling.Heterogeneous.selectedCopySamples_measurePreserving
#print axioms DGRHS.Decoupling.Heterogeneous.spliceCoordinate_true_measurePreserving
#print axioms DGRHS.Decoupling.Heterogeneous.spliceCoordinate_measurePreserving
#print axioms DGRHS.Decoupling.Heterogeneous.splicePairArrays_measurePreserving
