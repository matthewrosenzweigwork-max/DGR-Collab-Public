import DGPS.Lipschitz.T01ReferenceEigenbasis
import DGPS.Lipschitz.T01UnrestrictedLower
import DGPS.FiniteN.Tools.Rothaus
import DGPS.Variational.FrozenGibbs

/-!
# The ordinary one-body rate below the legacy reference rate

Every legacy reference Sobolev test is an actual weighted Sobolev test on the compatible
campaign reference. Their chosen gradients and entropies agree. This is the direction needed
to transfer a species upper bound on the current ordinary LSI rate to the legacy comparison
rate; it does not identify the Gaussian rate or assert a particle lower bound.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

open KernelApproximation

private theorem ordinaryLSRate_le_test {d : ℕ} (P : BoundedPositiveReference d)
    (f : Torus d → ℝ) (hu : f ∈ WeightedH1 P)
    (hpos : 0 < homogeneousEntropy P.measure (fun x => f x ^ 2)) :
    ordinaryLSRate P ≤ 2 * (∫⁻ x, ‖weightedGradient P f hu x‖ₑ ^ 2 ∂P.measure) /
      homogeneousEntropy P.measure (fun x => f x ^ 2) := by
  unfold ordinaryLSRate
  exact iInf_le_of_le ⟨f, hu, hpos⟩ le_rfl

/-- The current ordinary rate is bounded above by the legacy rate on the same reference. -/
theorem ordinaryLSRate_le_legacy_rLS_reference {d : ℕ} (P : BoundedPositiveReference d) :
    ordinaryLSRate P ≤ SharpLSI.FL.rLS P.measure := by
  unfold SharpLSI.FL.rLS
  refine le_iInf fun f => le_iInf fun hf => ?_
  have hu2 : MemLp f 2 (haar d) := P.memLp_measure_iff.1 hf.1.2.1
  have hg2 : MemLp (fun x => WithLp.toLp 2 (SharpLSI.weakGrad f x)) 2 (haar d) := by
    refine memLp_piLp_iff.mpr fun j => ?_
    exact P.memLp_measure_iff.1 (SharpLSI.memLp_grad_comp P.measure_ac_haar hf.1 j)
  have hw := isWeakGradient_of_legacy_pair
    (SharpLSI.isWeakGrad_weakGrad hf.1.1) hu2 hg2
  have hmem : f ∈ WeightedH1 P := (mem_weightedH1_iff P).2 ⟨_, hw⟩
  have hent : homogeneousEntropy P.measure (fun x => f x ^ 2) =
      SharpLSI.ent P.measure (fun x => f x ^ 2) :=
    FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hf.1.2.1.integrable_sq
  have hpos : 0 < homogeneousEntropy P.measure (fun x => f x ^ 2) := by
    rw [hent]
    exact hf.2
  have hE : (∫⁻ x, ‖weightedGradient P f hmem x‖ₑ ^ 2 ∂P.measure) =
      SharpLSI.dirichlet P.measure f := by
    unfold SharpLSI.dirichlet
    refine lintegral_congr_ae ?_
    filter_upwards [P.measure_ac_haar.ae_le (weightedGradient_ae_eq P hmem hw)] with x hx
    rw [hx, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    congr 1
    exact Analysis.norm_sq_eq_sqNorm _
  calc
    ordinaryLSRate P ≤
        2 * (∫⁻ x, ‖weightedGradient P f hmem x‖ₑ ^ 2 ∂P.measure) /
          homogeneousEntropy P.measure (fun x => f x ^ 2) :=
      ordinaryLSRate_le_test P f hmem hpos
    _ = _ := by rw [hE, hent]

/-- Compatibility wrapper for the spectral-reference interface. -/
theorem ordinaryLSRate_le_legacy_rLS {d : ℕ} (P : BoundedPositiveReference d)
    (_S : Spec d) (_hP : P.measure = _S.mu) :
    ordinaryLSRate P ≤ SharpLSI.FL.rLS P.measure :=
  ordinaryLSRate_le_legacy_rLS_reference P

end DGPS.Lipschitz
