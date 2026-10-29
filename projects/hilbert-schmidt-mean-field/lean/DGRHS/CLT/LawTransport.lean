/- UNCHECKED outside frozen proof. Law transfer preserves actual finite-product
sample spaces and the actual common Gaussian target. Each convergence premise is
to be supplied by the constructed finite CLT, never assumed in the paper endpoint. -/
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace DGRHS.CLT
variable {ι E Ω Ω' Ω'' : Type*} {S : ι → Type*}
  [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']
  [∀ n, MeasurableSpace (S n)] [TopologicalSpace E] [MeasurableSpace E]
  [BorelSpace E] {P : Measure Ω} {Q : Measure Ω'} {R : Measure Ω''}
  [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
  {μ : ∀ n, Measure (S n)} [∀ n, IsProbabilityMeasure (μ n)]
  {l : Filter ι}

lemma tendstoInDistribution_transport_source
    (X : ∀ n, S n → E) (Z : Ω' → E) (f : ∀ n, Ω → S n)
    (hf : ∀ n, MeasurePreserving (f n) P (μ n))
    (hX : ∀ n, AEMeasurable (X n) (μ n))
    (h : TendstoInDistribution (fun n => X n ∘ f n) l Z (fun _ => P) Q) :
    TendstoInDistribution X l Z μ Q := by
  refine ⟨hX,h.aemeasurable_limit,?_⟩
  have hmap : ∀ n, P.map (X n ∘ f n) = (μ n).map (X n) := by
    intro n
    have hXm : AEMeasurable (X n) (P.map (f n)) := by
      rw [(hf n).map_eq]
      exact hX n
    rw [← AEMeasurable.map_map_of_aemeasurable hXm (hf n).aemeasurable,
      (hf n).map_eq]
  have hseq : (fun n => (⟨P.map (X n ∘ f n),
      (Measure.isProbabilityMeasure_map_iff (h.forall_aemeasurable n)).mpr inferInstance⟩ : ProbabilityMeasure E)) =
      (fun n => (⟨(μ n).map (X n),
        (Measure.isProbabilityMeasure_map_iff (hX n)).mpr inferInstance⟩ : ProbabilityMeasure E)) := by
    funext n
    exact Subtype.ext (hmap n)
  have ht := h.tendsto
  rw [hseq] at ht
  exact ht

lemma tendstoInDistribution_transport_target
    {X : ∀ n, S n → E} {Z : Ω' → E} {W : Ω'' → E}
    (h : TendstoInDistribution X l Z μ Q)
    (hi : ProbabilityTheory.IdentDistrib Z W Q R) :
    TendstoInDistribution X l W μ R := by
  refine ⟨h.forall_aemeasurable,hi.aemeasurable_snd,?_⟩
  convert h.tendsto using 1
  congr 1
  exact Subtype.ext hi.map_eq.symm

end DGRHS.CLT
#print axioms DGRHS.CLT.tendstoInDistribution_transport_source
#print axioms DGRHS.CLT.tendstoInDistribution_transport_target
