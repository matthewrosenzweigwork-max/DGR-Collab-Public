import DGPS.Frontier.LIP032.T12
import DGPS.Frontier.LIP032.T15
import DGPS.Frontier.LIP032.T47

/-!
# Topology of free-energy minimizer sets

The minimizer sets below carry the subspace topology of the weak topology on probability
measures. The first theorem retains the analytic and drift hypotheses of the positive-rate
contraction theorem; there is no standalone flow parameter in the public interface.
The second concerns the explicit circle interaction with
`γ(x) = cos(2πx)`, `V(x) = -4γ(x)^2`, and `W(x,y) = 4(γ(x)-γ(y))^2`.

## R5 notes

The conditional theorem reuses LIP032.12. The potential bounds are consequences of
`InteractionData`, and positivity of the extended scalar rate supplies a finite positive real
subrate, including when the scalar rate is infinite. The fixed minimizer supplies nonemptiness.
No analyticity, smoothness, or dimension hypothesis is added to the upstream assumptions.

For the explicit interaction and classical-gradient drift of LIP032.41 and LIP032.49,
nonemptiness and the obstruction to a contraction come from LIP032.47; the zero scalar rate
comes from LIP032.15. The obstruction is expressed as the actual negation of `ContractibleSpace`,
using its nullhomotopy characterization. No classification of connected components or of all
minimizers is asserted. These public corollaries do not amend or close the held specification.
-/

open MeasureTheory
open DGPS.Frontier.LIP032

namespace DGPS.Lipschitz

/-- Under the positive scalar-rate flow hypotheses, the weak minimizer space is contractible. -/
theorem minimizer_set_contractible_of_positive_scalarRate {d : ℕ} (A : InteractionData d)
    (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : MeanFieldData G B g β)
    (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ⊤ (fun x => A.W x y) (fun x => B x y))
    (hrate : 0 < scalarRate A drift)
    (μ : ProbabilityMeasure (Torus d)) (hμ : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A) :
    ContractibleSpace {ν : ProbabilityMeasure (Torus d) //
      DGPS.freeEnergy A ν = DGPS.freeEnergyMinimum A} := by
  obtain ⟨q, hq0, hqrate⟩ := exists_between hrate
  have hqtop : q ≠ ⊤ := ne_top_of_lt hqrate
  obtain ⟨M_V, hVb⟩ := A.V_bounded
  obtain ⟨M_W, hWb⟩ := A.W_bounded
  exact lip032_12_conditional_contractibility A drift hMF hV hWB
    (ENNReal.toReal_pos hq0.ne' hqtop)
    (by simpa only [ENNReal.ofReal_toReal hqtop] using hqrate)
    μ hμ M_V M_W hVb hWb

/-- The explicit circle minimizer set is nonempty and noncontractible, and its scalar rate for
its classical-gradient drift is zero. -/
theorem explicit_circle_minimizer_set_noncontractible :
    minimizerSetStar_LIP03244.Nonempty ∧
      ¬ ContractibleSpace ↥minimizerSetStar_LIP03244 ∧
      scalarRate interactionDataStar_LIP03241 driftStar_LIP03249 = 0 := by
  refine ⟨exists_minimizer_LIP03247, ?_, lip032_15_counterexample_scalar_rate_zero⟩
  intro hcontract
  obtain ⟨μ, ⟨H⟩⟩ := (contractible_iff_id_nullhomotopic ↥minimizerSetStar_LIP03244).1 hcontract
  apply lip032_47_no_contraction_real_intermediate_value_argument_no_homotopy μ
  exact ⟨fun p => H (p.2, p.1), H.continuous.comp (continuous_snd.prodMk continuous_fst),
    fun ν => H.map_zero_left ν, fun ν => H.map_one_left ν⟩

end DGPS.Lipschitz
