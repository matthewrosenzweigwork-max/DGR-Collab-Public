/- UNCHECKED outside frozen proof. Pinned Portmanteau instantiated on actual
pushforward probability laws; bounded test hypotheses are explicit. -/
import DGRHS.CLT.Approximation
import Mathlib.MeasureTheory.Measure.Portmanteau
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace DGRHS.CLT
variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
variable {Ω : ℕ → Type*} {Ω' : Type*}
  [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
  {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
  {ν : Measure Ω'} [IsProbabilityMeasure ν]

lemma tendstoInDistribution_of_bounded_lipschitz
    (X : ∀ n, Ω n → E) (Z : Ω' → E)
    (hX : ∀ n, AEMeasurable (X n) (μ n)) (hZ : AEMeasurable Z ν)
    (h : ∀ F : E → ℝ, (∃ C : ℝ, ∀ x y, dist (F x) (F y) ≤ C) →
      ∀ L : ℝ≥0, LipschitzWith L F →
        Tendsto (fun n => ∫ x, F (X n x) ∂μ n) atTop (𝓝 (∫ z, F (Z z) ∂ν))) :
    TendstoInDistribution X atTop Z μ ν := by
  refine ⟨hX, hZ, ?_⟩
  apply MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro F hb hl
  obtain ⟨L, hL⟩ := hl
  have ht := h F hb L hL
  have hm : ∀ n, (∫ y, F y ∂(μ n).map (X n)) = ∫ x, F (X n x) ∂μ n :=
    fun n => integral_map (hX n) (hL.continuous.measurable.aestronglyMeasurable)
  have hz : (∫ y, F y ∂ν.map Z) = ∫ z, F (Z z) ∂ν :=
    integral_map hZ hL.continuous.measurable.aestronglyMeasurable
  simpa only [ProbabilityMeasure.coe_mk, hm, hz] using ht

lemma bounded_lipschitz_integral_tendsto_of_tendstoInDistribution
    (X : ∀ n, Ω n → E) (Z : Ω' → E)
    (h : TendstoInDistribution X atTop Z μ ν)
    (F : E → ℝ) (hb : ∃ C : ℝ, ∀ x y, dist (F x) (F y) ≤ C)
    (L : ℝ≥0) (hL : LipschitzWith L F) :
    Tendsto (fun n => ∫ x, F (X n x) ∂μ n) atTop (𝓝 (∫ z, F (Z z) ∂ν)) := by
  let F' : BoundedContinuousFunction E ℝ := ⟨⟨F, hL.continuous⟩, hb⟩
  exact (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    h.forall_aemeasurable h.aemeasurable_limit).mp h F'

end DGRHS.CLT
#print axioms DGRHS.CLT.tendstoInDistribution_of_bounded_lipschitz
#print axioms DGRHS.CLT.bounded_lipschitz_integral_tendsto_of_tendstoInDistribution
