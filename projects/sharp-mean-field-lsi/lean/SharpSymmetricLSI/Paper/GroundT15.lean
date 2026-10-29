import SharpSymmetricLSI.Paper.GroundT14

/-!
# R30 assembly: Section 7.2, compactness under the Gibbs law, conditional
-/

open MeasureTheory InformationTheory Set Filter Topology Real
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem aestronglyMeasurable_fluct_vec (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) (N J : ℕ) :
    AEStronglyMeasurable (fun X : Config N d => fun n : Fin J => fluct e N n X)
      (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := by
  have hm : Measurable fun X : Config N d => fun n : Fin J =>
      zSum (fun i => (he.memLp i).aestronglyMeasurable.mk (e i)) N n X := by
    unfold zSum
    refine measurable_pi_iff.mpr fun n => measurable_const.mul
      (Finset.measurable_sum _ fun l _ => ?_)
    exact (he.memLp _).aestronglyMeasurable.stronglyMeasurable_mk.measurable.comp
      (measurable_pi_apply l)
  exact hm.aestronglyMeasurable.congr (fluct_ae_eq hyp hμ he N J).symm

theorem aestronglyMeasurable_Uinf {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)}
    {T : ℕ → ℕ → ℝ} {Q : (ℕ → ℝ) → ℝ} (hQ : IsSecondChaos T Q) :
    AEStronglyMeasurable (Uinf W μ Q) gammaRef := by
  have h : AEStronglyMeasurable Q gammaRef := hQ.1.aestronglyMeasurable
  unfold Uinf
  exact ((continuous_id.div_const 2).add continuous_const).comp_aestronglyMeasurable h

end SharpLSI
