/- Pull actual changing-domain weak laws to a genuine common iid sample space.
Used only with proved measure-preserving coordinate-prefix maps. -/
import DGRHS.CLT.LawTransport
noncomputable section
open MeasureTheory Filter
namespace DGRHS.CLT
variable {ι E Ω Ω' : Type*} {S : ι → Type*}
  [MeasurableSpace Ω] [MeasurableSpace Ω'] [∀ n, MeasurableSpace (S n)]
  [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  {μ : ∀ n, Measure (S n)} [∀ n, IsProbabilityMeasure (μ n)] {l : Filter ι}

lemma tendstoInDistribution_pullback_source
    (X : ∀ n, S n → E) (Z : Ω' → E) (f : ∀ n, Ω → S n)
    (hf : ∀ n, MeasurePreserving (f n) P (μ n))
    (h : TendstoInDistribution X l Z μ Q) :
    TendstoInDistribution (fun n => X n ∘ f n) l Z (fun _ => P) Q := by
  have hmeas : ∀ n, AEMeasurable (X n ∘ f n) P := by
    intro n
    have hXm : AEMeasurable (X n) (P.map (f n)) := by
      rw [(hf n).map_eq]
      exact h.forall_aemeasurable n
    exact hXm.comp_aemeasurable (hf n).aemeasurable
  refine ⟨hmeas,h.aemeasurable_limit,?_⟩
  have hmap : ∀ n, P.map (X n ∘ f n) = (μ n).map (X n) := by
    intro n
    have hXm : AEMeasurable (X n) (P.map (f n)) := by
      rw [(hf n).map_eq]
      exact h.forall_aemeasurable n
    rw [← AEMeasurable.map_map_of_aemeasurable hXm (hf n).aemeasurable,(hf n).map_eq]
  have heq : (fun n => (⟨P.map (X n ∘ f n),
      (Measure.isProbabilityMeasure_map_iff (hmeas n)).mpr inferInstance⟩ : ProbabilityMeasure E)) =
      (fun n => (⟨(μ n).map (X n),
        (Measure.isProbabilityMeasure_map_iff (h.forall_aemeasurable n)).mpr inferInstance⟩ : ProbabilityMeasure E)) := by
    funext n
    exact Subtype.ext (hmap n)
  rw [heq]
  exact h.tendsto
end DGRHS.CLT
#print axioms DGRHS.CLT.tendstoInDistribution_pullback_source
