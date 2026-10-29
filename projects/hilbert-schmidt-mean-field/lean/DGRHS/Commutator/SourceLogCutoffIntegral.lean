import DGRHS.Commutator.SourceLogCutoffKernel
import DGRHS.Commutator.SourceLogDiagonalBand
import DGRHS.Commutator.SourceLogTransportMoments
import DGRHS.Commutator.SourceMovingLawIntegral
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Unchecked draft. Proper integrated approximation of the actual logarithmic
kernel, followed by continuity under a narrowly continuous probability law.
Uniform velocity Lipschitz and per-slice density bounds are explicit. This does
not derive the static PDE or any moving-test identity. Native API provenance is
preserved with the draft; no untruncated diagonal continuity is assumed. -/
noncomputable section
open MeasureTheory Set Metric Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceLogBallIndicator_eq_if (ε : ℝ) (z : E) :
    sourceLogBallIndicator ε z = if ‖z‖ < ε then 1 else 0 := by
  classical
  simp [sourceLogBallIndicator, Set.indicator, Metric.mem_ball, dist_zero_right]

lemma sourceLogCutoff_error_indicator (ε : ℝ) (hε : 0 < ε)
    {v : E → E} {K : ℝ≥0} (hv : LipschitzWith K v) (p : E × E) :
    |sourceLogTransportKernel 1 v p - sourceLogCutoffKernel ε v p| ≤
      (K : ℝ) * sourceLogBallIndicator ε (p.1 - p.2) := by
  rw [sourceLogBallIndicator_eq_if]
  simpa only [mul_ite, mul_one, mul_zero] using
    abs_sourceLogTransportKernel_sub_cutoff_le_band ε hε hv p

lemma integrable_sourceLogCutoffKernel (ε : ℝ) (hε : 0 < ε)
    {v : E → E} {K : ℝ≥0} (hv : LipschitzWith K v)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ] :
    Integrable (sourceLogCutoffKernel ε v) μ := by
  have hc : Continuous (fun p : Unit × (E × E) => sourceLogCutoffKernel ε v p.2) :=
    continuous_sourceLogCutoffKernel ε hε (fun _ : Unit => v)
      (hv.continuous.comp continuous_snd)
  have he : Continuous (fun p : E × E => ((), p)) :=
    continuous_const.prodMk continuous_id
  have hs : Continuous (sourceLogCutoffKernel ε v) := by
    apply (hc.comp he).congr
    intro p
    rfl
  exact integrable_of_abs_bound μ hs.measurable
    (abs_sourceLogCutoffKernel_le ε hε hv)

lemma integrable_sourceLogKernel_one {v : E → E} {K : ℝ≥0}
    (hv : LipschitzWith K v) (μ : Measure (E × E)) [IsProbabilityMeasure μ] :
    Integrable (sourceLogTransportKernel 1 v) μ :=
  integrable_of_abs_bound μ (measurable_sourceLogTransportKernel_one hv)
    (abs_sourceLogTransportKernel_one_le hv)

lemma abs_integral_sourceLogKernel_sub_cutoff_le (ε : ℝ) (hε : 0 < ε)
    {v : E → E} {K : ℝ≥0} (hv : LipschitzWith K v)
    (ρ : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ z ∂volume, ρ z ≤ M) :
    |(∫ p : E × E, sourceLogTransportKernel 1 v p
        ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) -
      (∫ p : E × E, sourceLogCutoffKernel ε v p
        ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))| ≤
      (K : ℝ) * M * volume.real (ball (0 : E) ε) := by
  let μ := (gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)
  have hi := integrable_sourceLogKernel_one hv μ
  have hc := integrable_sourceLogCutoffKernel ε hε hv μ
  have hb := (integrable_sourceLogDiagonalBand ε ρ M hM hρ).const_mul (K : ℝ)
  calc
    _ = ‖∫ p, sourceLogTransportKernel 1 v p - sourceLogCutoffKernel ε v p ∂μ‖ := by
      rw [integral_sub hi hc, Real.norm_eq_abs]
    _ ≤ ∫ p, (K : ℝ) * sourceLogBallIndicator ε (p.1 - p.2) ∂μ :=
      norm_integral_le_of_norm_le hb (Eventually.of_forall fun p => by
        simpa only [Real.norm_eq_abs] using sourceLogCutoff_error_indicator ε hε hv p)
    _ = (K : ℝ) * ∫ p, sourceLogBallIndicator ε (p.1 - p.2) ∂μ := integral_const_mul _ _
    _ ≤ (K : ℝ) * (M * volume.real (ball (0 : E) ε)) :=
      mul_le_mul_of_nonneg_left (integral_sourceLogDiagonalBand_le ε ρ M hM hρ)
        K.coe_nonneg
    _ = _ := by ring

lemma sourceLog_ball_real_volume_eq (ε : ℝ) :
    volume.real (ball (0 : E) ε) = (max ε 0) ^ Fintype.card ι *
      (ENNReal.ofReal (Real.sqrt Real.pi ^ Fintype.card ι /
        Real.Gamma ((Fintype.card ι : ℝ) / 2 + 1))).toReal := by
  change (volume (ball (0 : E) ε)).toReal = _
  rw [EuclideanSpace.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow]
  by_cases h : 0 ≤ ε
  · rw [ENNReal.toReal_ofReal h, max_eq_left h]
  · rw [ENNReal.ofReal_of_nonpos (le_of_not_ge h), ENNReal.toReal_zero,
      max_eq_right (le_of_not_ge h)]

lemma continuous_sourceLog_ball_real_volume :
    Continuous (fun ε : ℝ => volume.real (ball (0 : E) ε)) := by
  simp_rw [sourceLog_ball_real_volume_eq]
  exact ((continuous_id.max continuous_const).pow _).mul continuous_const

lemma exists_pos_sourceLog_ball_error_lt (K : ℝ≥0) (M : ℝ)
    (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ (K : ℝ) * M * volume.real (ball (0 : E) ε) < η := by
  have hc : Continuous (fun ε : ℝ => (K : ℝ) * M * volume.real (ball (0 : E) ε)) :=
    continuous_const.mul continuous_sourceLog_ball_real_volume
  have hlt : (K : ℝ) * M * volume.real (ball (0 : E) (0 : ℝ)) < η := by
    simpa using hη
  have he : ∀ᶠ ε in 𝓝 (0 : ℝ),
      (K : ℝ) * M * volume.real (ball (0 : E) ε) < η :=
    (hc.continuousAt (x := 0)).eventually (gt_mem_nhds hlt)
  obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ / 2, by linarith, hsmall ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < δ / 2)]
  linarith

section Moving
variable {P : Type*} [MetricSpace P] [SecondCountableTopology P]

lemma continuous_integral_sourceLogCutoff_probability (ε : ℝ) (hε : 0 < ε)
    (v : P → E → E) (hv : Continuous (fun p : P × E => v p.1 p.2))
    (K : ℝ≥0) (hK : ∀ a, LipschitzWith K (v a))
    (μ : P → ProbabilityMeasure E) (hμ : Continuous μ) :
    Continuous (fun a => ∫ p, sourceLogCutoffKernel ε (v a) p
      ∂(μ a : Measure E).prod (μ a : Measure E)) := by
  letI : MeasurableSpace P := borel P
  letI : BorelSpace P := ⟨rfl⟩
  have hp := ProbabilityMeasure.continuous_prod.comp (hμ.prodMk hμ)
  exact continuous_integral_moving_probability (fun a : P => a) continuous_id
    (fun a => (μ a).prod (μ a)) hp
    (fun p : P × (E × E) => sourceLogCutoffKernel ε (v p.1) p.2)
    (continuous_sourceLogCutoffKernel ε hε v hv) (K : ℝ)
    (fun p => abs_sourceLogCutoffKernel_le ε hε (hK p.1) p.2)

lemma continuous_integral_sourceLogKernel_one_probability
    (v : P → E → E) (hv : Continuous (fun p : P × E => v p.1 p.2))
    (K : ℝ≥0) (hK : ∀ a, LipschitzWith K (v a))
    (μ : P → ProbabilityMeasure E) (hμ : Continuous μ)
    (ρ : P → E → ℝ) (hρμ : ∀ a, (μ a : Measure E) = gaussianRieszDensityMeasure (ρ a))
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ a, ∀ᵐ z ∂volume, ρ a z ≤ M) :
    Continuous (fun a => ∫ p, sourceLogTransportKernel 1 (v a) p
      ∂(μ a : Measure E).prod (μ a : Measure E)) := by
  apply continuous_of_uniform_approx_of_continuous
  intro u hu
  obtain ⟨η, hη, hsmall⟩ := Metric.mem_uniformity_dist.mp hu
  obtain ⟨ε, hε, he⟩ := exists_pos_sourceLog_ball_error_lt (ι := ι) K M η hη
  refine ⟨fun a => ∫ p, sourceLogCutoffKernel ε (v a) p
      ∂(μ a : Measure E).prod (μ a : Measure E),
    continuous_integral_sourceLogCutoff_probability ε hε v hv K hK μ hμ, ?_⟩
  intro a
  apply hsmall
  rw [Real.dist_eq]
  haveI : IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ a)) :=
    hρμ a ▸ (inferInstance : IsProbabilityMeasure (μ a : Measure E))
  simpa only [hρμ a] using
    (abs_integral_sourceLogKernel_sub_cutoff_le ε hε (hK a) (ρ a) M hM (hρ a)).trans_lt he

lemma continuous_nested_integral_sourceLogKernel_one_probability
    (v : P → E → E) (hv : Continuous (fun p : P × E => v p.1 p.2))
    (K : ℝ≥0) (hK : ∀ a, LipschitzWith K (v a))
    (μ : P → ProbabilityMeasure E) (hμ : Continuous μ)
    (ρ : P → E → ℝ) (hρμ : ∀ a, (μ a : Measure E) = gaussianRieszDensityMeasure (ρ a))
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ a, ∀ᵐ z ∂volume, ρ a z ≤ M) :
    Continuous (fun a => ∫ x, ∫ y, sourceLogTransportKernel 1 (v a) (x,y)
      ∂(μ a : Measure E) ∂(μ a : Measure E)) := by
  have hc := continuous_integral_sourceLogKernel_one_probability v hv K hK μ hμ ρ hρμ M hM hρ
  apply hc.congr
  intro a
  exact integral_prod _ (integrable_sourceLogKernel_one (hK a) _)

end Moving
end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.sourceLogBallIndicator_eq_if
#print axioms DGRHS.Commutator.sourceLogBallIndicator_eq_if
#check @DGRHS.Commutator.sourceLogCutoff_error_indicator
#print axioms DGRHS.Commutator.sourceLogCutoff_error_indicator
#check @DGRHS.Commutator.integrable_sourceLogCutoffKernel
#print axioms DGRHS.Commutator.integrable_sourceLogCutoffKernel
#check @DGRHS.Commutator.integrable_sourceLogKernel_one
#print axioms DGRHS.Commutator.integrable_sourceLogKernel_one
#check @DGRHS.Commutator.abs_integral_sourceLogKernel_sub_cutoff_le
#print axioms DGRHS.Commutator.abs_integral_sourceLogKernel_sub_cutoff_le
#check @DGRHS.Commutator.sourceLog_ball_real_volume_eq
#print axioms DGRHS.Commutator.sourceLog_ball_real_volume_eq
#check @DGRHS.Commutator.continuous_sourceLog_ball_real_volume
#print axioms DGRHS.Commutator.continuous_sourceLog_ball_real_volume
#check @DGRHS.Commutator.exists_pos_sourceLog_ball_error_lt
#print axioms DGRHS.Commutator.exists_pos_sourceLog_ball_error_lt
#check @DGRHS.Commutator.continuous_integral_sourceLogCutoff_probability
#print axioms DGRHS.Commutator.continuous_integral_sourceLogCutoff_probability
#check @DGRHS.Commutator.continuous_integral_sourceLogKernel_one_probability
#print axioms DGRHS.Commutator.continuous_integral_sourceLogKernel_one_probability
#check @DGRHS.Commutator.continuous_nested_integral_sourceLogKernel_one_probability
#print axioms DGRHS.Commutator.continuous_nested_integral_sourceLogKernel_one_probability
