import DGRHS.Commutator.SourceMovingTimeAverage
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! UNCOMPILED analytic successor, not part of the first moving-law check.
The frozen-test derivative of a moving law and the actual pointwise temporal
derivative of a test give the derivative of their moving pairing. Only an
open neighbourhood of the differentiation point is required for the test
chain rule. The globally bounded continuous delta is available by endpoint
clamping from the source's closed-horizon derivative extension. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace DGRHS.Commutator
variable {E : Type*} [MetricSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

lemma hasDerivAt_integral_moving_probability
    (μ : ℝ → ProbabilityMeasure E) (hμ : Continuous μ)
    (q : ℝ → E → ℝ) (δ : ℝ × E → ℝ) (hδ : Continuous δ)
    (C : ℝ) (hC : ∀ p, |δ p| ≤ C) (r ε L : ℝ) (hε : 0<ε)
    (htime : ∀ u ∈ Ioo (r-ε) (r+ε), ∀ x,
      HasDerivAt (fun v => q v x) (δ (u,x)) u)
    (hproper : ∀ u ∈ Ioo (r-ε) (r+ε),
      Integrable (q u) (μ u : Measure E) ∧ Integrable (q r) (μ u : Measure E))
    (hstatic : HasDerivAt (fun u => ∫ x, q r x ∂(μ u : Measure E)) L r) :
    HasDerivAt (fun u => ∫ x, q u x ∂(μ u : Measure E))
      (L + ∫ x, δ (r,x) ∂(μ r : Measure E)) r := by
  have havg := tendsto_integral_sourceUnitTimeAverage μ hμ δ hδ C hC r
  have hlim := hstatic.tendsto_slope_zero.add (havg.mono_left nhdsWithin_le_nhds)
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply hlim.congr'
  have hsmall : ∀ᶠ h : ℝ in 𝓝[≠] 0, |h|<ε := by
    have hm : ∀ᶠ h : ℝ in 𝓝 0, |h|<ε := by
      filter_upwards [Metric.ball_mem_nhds (0:ℝ) hε] with h hh
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hh
    exact hm.filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ h : ℝ in 𝓝[≠] 0, h≠0 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    simpa using hh
  filter_upwards [hsmall,hne] with h hh hn
  have hrh : r+h ∈ Ioo (r-ε) (r+ε) := by
    rcases abs_lt.mp hh with ⟨hlo,hhi⟩
    constructor <;> linarith
  have hseg : uIcc r (r+h) ⊆ Ioo (r-ε) (r+ε) := by
    intro u hu
    change min r (r+h) ≤ u ∧ u ≤ max r (r+h) at hu
    have hr : r ∈ Ioo (r-ε) (r+ε) := by constructor <;> linarith
    exact ⟨lt_of_lt_of_le (lt_min hr.1 hrh.1) hu.1,
      lt_of_le_of_lt hu.2 (max_lt hr.2 hrh.2)⟩
  have hinc (x : E) : q (r+h) x-q r x = h*sourceUnitTimeAverage δ r h x := by
    have hi : IntervalIntegrable (fun u => δ (u,x)) volume r (r+h) :=
      (hδ.comp (continuous_id.prodMk continuous_const)).intervalIntegrable r (r+h)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => htime u (hseg hu) x) hi
    have hscale := intervalIntegral.smul_integral_comp_add_mul
      (fun u => δ (u,x)) (a := (0:ℝ)) (b := 1) h r
    have hav : h*sourceUnitTimeAverage δ r h x = ∫ u in r..r+h,δ (u,x) := by
      simpa only [sourceUnitTimeAverage, smul_eq_mul, mul_zero, zero_mul, add_zero, mul_one, one_mul,
        mul_comm h] using hscale
    exact hftc.symm.trans hav.symm
  have he : (∫ x,q (r+h) x ∂(μ (r+h) : Measure E))-
      (∫ x,q r x ∂(μ r : Measure E)) =
      ((∫ x,q r x ∂(μ (r+h) : Measure E))-(∫ x,q r x ∂(μ r : Measure E)))+
        h*(∫ x,sourceUnitTimeAverage δ r h x ∂(μ (r+h) : Measure E)) := by
    have hd : (∫ x,q (r+h) x ∂(μ (r+h) : Measure E))-
        (∫ x,q r x ∂(μ (r+h) : Measure E)) =
        h*(∫ x,sourceUnitTimeAverage δ r h x ∂(μ (r+h) : Measure E)) := by
      rw [← integral_sub (hproper (r+h) hrh).1 (hproper (r+h) hrh).2]
      simp_rw [hinc]
      exact integral_const_mul _ _
    linarith
  simp only [smul_eq_mul]
  rw [he]
  field_simp [hn] <;> ring

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.hasDerivAt_integral_moving_probability
#print axioms DGRHS.Commutator.hasDerivAt_integral_moving_probability
