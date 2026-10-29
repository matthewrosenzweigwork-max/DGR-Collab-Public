/- Finite-dimensional projection criterion for changing particle domains. -/
import DGRHS.CLT.FiniteDimensionalCLT
open MeasureTheory ProbabilityTheory Filter
open scoped Topology InnerProductSpace
namespace DGRHS.CLT
variable {E Ω' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

theorem tendstoInDistribution_changing_inner_projections
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n, Ω n → E) (Y : Ω' → E)
    (hX : ∀ n, AEMeasurable (X n) (P n)) (hY : AEMeasurable Y P')
    (hproj : ∀ t : E, TendstoInDistribution
      (fun n ω ↦ inner ℝ (X n ω) t) atTop
      (fun ω ↦ inner ℝ (Y ω) t) P P') :
    TendstoInDistribution X atTop Y P P' where
  forall_aemeasurable := hX
  aemeasurable_limit := hY
  tendsto := by
    apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
    intro t
    have hp := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp (hproj t).tendsto (1 : ℝ)
    change Tendsto (fun n => charFun ((P n).map (X n)) t) atTop
      (𝓝 (charFun (P'.map Y) t))
    change Tendsto (fun n => charFun ((P n).map (fun ω => inner ℝ (X n ω) t)) (1 : ℝ))
      atTop (𝓝 (charFun (P'.map (fun ω => inner ℝ (Y ω) t)) (1 : ℝ))) at hp
    simpa only [charFun_map_eq_charFun_map_inner_one (hX _) t,
      charFun_map_eq_charFun_map_inner_one hY t] using hp
end DGRHS.CLT
#print axioms DGRHS.CLT.tendstoInDistribution_changing_inner_projections
#check @DGRHS.CLT.tendstoInDistribution_changing_inner_projections
