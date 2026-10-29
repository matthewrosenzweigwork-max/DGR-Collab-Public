import DGRHS.Commutator.SourceRieszLongMovingContinuity
import DGRHS.Commutator.SourceRieszMovingKernelApproximation
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! UNCOMPILED actual full singular-generator continuity. The actual long
transport integrals converge uniformly in time to the proper full integrals
using the previously established short-range row estimate. The density
representative is used only to establish uniform domination; joint density
measurability is not silently inferred from the continuous probability path. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma continuous_integral_sourceRieszTransportKernel_one_moving
    (s : ℝ) (hs : 0<s) (hd : s<(Fintype.card ι:ℝ))
    (v : ℝ→E→E) (hv : Continuous (Function.uncurry v))
    (K : ℝ≥0) (hK : ∀ r, LipschitzWith K (v r))
    (μ : ℝ→ProbabilityMeasure E) (hμ : Continuous μ)
    (ρ : ℝ→E→ℝ) (hρμ : ∀ r, (μ r : Measure E)=gaussianRieszDensityMeasure (ρ r))
    (M : ℝ) (hM : 0≤M) (hρ : ∀ r, ∀ᵐ x ∂volume, ρ r x≤M) :
    Continuous (fun r => ∫ p, sourceRieszTransportKernel 1 s (v r) p
      ∂(μ r : Measure E).prod (μ r : Measure E)) := by
  let J : ℝ→ℝ := fun r => ∫ p, sourceRieszTransportKernel 1 s (v r) p
    ∂(μ r : Measure E).prod (μ r : Measure E)
  let L : ℝ→ℝ→ℝ := fun η r => ∫ p, sourceRieszLongTransportKernel 1 s η (v r) p
    ∂(μ r : Measure E).prod (μ r : Measure E)
  let B : ℝ→ℝ := fun η =>
    localCompatible_sourceRieszShortTransportAllOrderPotentialBound (ι:=ι) 1 s η K M
  have hL (η : ℝ) (hη : 0<η) : Continuous (L η) := by
    have he (r : ℝ) : L η r =
        ∫ x, ∫ y, sourceRieszLongTransportKernel 1 s η (v r) (x,y)
          ∂(μ r : Measure E) ∂(μ r : Measure E) :=
      integral_prod _ (integrable_sourceRieszLocalLongKernel (μ r) s η 1 hs hη (hK r))
    simp_rw [show L η = (fun r => ∫ x, ∫ y,
        sourceRieszLongTransportKernel 1 s η (v r) (x,y)
          ∂(μ r : Measure E) ∂(μ r : Measure E)) from funext he]
    exact continuous_integral_sourceRieszLongTransportKernel_one_moving s η hs hη v hv K hK μ hμ
  have herr (η : ℝ) (hη : 0<η) (r : ℝ) : |J r-L η r|≤B η := by
    letI : IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)) := by
      rw [← hρμ r]
      infer_instance
    simpa only [J, L, B, hρμ r] using
      sourceRiesz_integral_full_sub_long_bound s η hs hη hd (hK r) (ρ r) M hM (hρ r)
  have hp : 0<(Fintype.card ι:ℝ)-s := sub_pos.mpr hd
  have hBc : Continuous B := by
    unfold B localCompatible_sourceRieszShortTransportAllOrderPotentialBound
    exact continuous_const.mul (Real.continuous_rpow_const hp.le)
  have hB0 : B 0=0 := by
    simp only [B, localCompatible_sourceRieszShortTransportAllOrderPotentialBound,
      Real.zero_rpow hp.ne', mul_zero]
  have ht : Tendsto B (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    simpa only [hB0] using (hBc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hu : TendstoUniformly L J (𝓝[>] (0:ℝ)) := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp ht).2 ε hε, self_mem_nhdsWithin] with η hηB hη
    intro r
    simpa only [Real.dist_eq] using (herr η hη r).trans_lt hηB
  have hc : ∀ᶠ η : ℝ in 𝓝[>] (0:ℝ), Continuous (L η) :=
    Filter.Eventually.mono
      (self_mem_nhdsWithin : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), 0 < η)
      (fun η hη => hL η hη)
  exact hu.continuous hc.frequently

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.continuous_integral_sourceRieszTransportKernel_one_moving
#print axioms DGRHS.Commutator.continuous_integral_sourceRieszTransportKernel_one_moving
