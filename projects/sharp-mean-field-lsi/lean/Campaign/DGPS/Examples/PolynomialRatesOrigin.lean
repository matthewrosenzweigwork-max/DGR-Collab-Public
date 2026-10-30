import DGPS.Examples.PolynomialScalarSineUpper
import DGPS.Examples.PolynomialSpeciesPositiveRate
import DGPS.Variational.SpeciesInclusion

/-! Coarse actual scalar and species rate limits at the Haar field. The
residual lower bound and genuine sine upper bound suffice; no optimizer graph
or refined second-order asymptotic is used. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Circle.AngularNormalization DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

private theorem selected_root_tendsto : Tendsto root_EX054 (𝓝 (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, δ, _, hδ, hb⟩ := abs_root_le_sixth_EX054
  have hs : ∀ᶠ h : ℝ in 𝓝 0, |h| < δ := by
    have ht : Tendsto (fun h : ℝ => |h|) (𝓝 (0 : ℝ)) (𝓝 0) := by simpa using continuous_abs.tendsto (0 : ℝ)
    exact ht.eventually (gt_mem_nhds hδ)
  have ht : Tendsto (fun h : ℝ => C * h ^ 6) (𝓝 0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0)).pow 6).const_mul C
  refine squeeze_zero_norm' ?_ ht
  filter_upwards [hs] with h hh
  rw [Real.norm_eq_abs]
  exact hb h hh.le

/-- Both actual full-domain rates tend to the physical Haar baseline for any
actual drift family. This is a coarse origin limit, not a second-order rate
shift or a statement about minimizer attainment. -/
theorem polynomial_scalar_species_rates_at_origin
    (b : ∀ h : ℝ, AbsoluteDrift (canonical_elementary_polynomial_model h)) :
    Tendsto (fun h : ℝ => speciesRate (canonical_elementary_polynomial_model h) (b h)) (𝓝 0)
      (𝓝 (ENNReal.ofReal a0)) ∧
    Tendsto (fun h : ℝ => scalarRate (canonical_elementary_polynomial_model h) (b h)) (𝓝 0)
      (𝓝 (ENNReal.ofReal a0)) := by
  obtain ⟨C, δL, hC, hδL, hlower⟩ := polynomial_actual_residual_rate_bound
  obtain ⟨δU, hδU, hupper⟩ := polynomial_scalarRate_eventual_upper 1 (by norm_num)
  let A := fun h : ℝ => canonical_elementary_polynomial_model h
  let L := fun h : ℝ => polynomialReferenceLowerRate h - eta * C ^ 2 * h ^ 2 / (4 * a0)
  have habs : Tendsto (fun h : ℝ => |h|) (𝓝 0) (𝓝 0) := by simpa using continuous_abs.tendsto (0 : ℝ)
  have hOsc : Tendsto polynomialReferenceOscillation (𝓝 0) (𝓝 0) := by
    have hh : Tendsto (fun h : ℝ => 2 * |h| +
        2 * (|root_EX054 h| * (1 + |h| / 3))) (𝓝 0) (𝓝 0) := by
      simpa using (habs.const_mul 2).add
        ((selected_root_tendsto.abs.mul ((tendsto_const_nhds (x := (1 : ℝ))).add (habs.div_const 3))).const_mul 2)
    apply hh.congr'
    exact Eventually.of_forall fun h => by dsimp [polynomialReferenceOscillation]; ring
  have hneg : Tendsto (fun h : ℝ => -polynomialReferenceOscillation h) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using hOsc.neg
  have haRef : Tendsto polynomialReferenceLowerRate (𝓝 0) (𝓝 a0) := by
    change Tendsto (fun h : ℝ => a0 * Real.exp (-polynomialReferenceOscillation h)) (𝓝 0) (𝓝 a0)
    simpa only [Function.comp_def, Real.exp_zero, mul_one] using
      ((Real.continuous_exp.tendsto 0).comp hneg).const_mul a0
  have hL : Tendsto L (𝓝 0) (𝓝 a0) := by
    have ht : Tendsto (fun h : ℝ => eta * C ^ 2 * h ^ 2 / (4 * a0)) (𝓝 0) (𝓝 0) := by
      simpa using (((tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0)).pow 2).const_mul
        (eta * C ^ 2)).div_const (4 * a0)
    simpa only [L, sub_zero] using haRef.sub ht
  have hfin : ∀ᶠ h : ℝ in 𝓝 0,
      speciesRate (A h) (b h) ≠ ⊤ ∧ scalarRate (A h) (b h) ≠ ⊤ := by
    filter_upwards [habs.eventually (gt_mem_nhds hδU)] with h hh
    have hu := hupper h hh (b h)
    have hs := (speciesRate_le_scalarRate (A h) (b h)).trans hu
    exact ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs, ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu⟩
  have hb : ∀ ε : ℝ, 0 < ε → ∀ᶠ h : ℝ in 𝓝 0,
      |(speciesRate (A h) (b h)).toReal - a0| < ε ∧
        |(scalarRate (A h) (b h)).toReal - a0| < ε := by
    intro ε hε
    obtain ⟨δt, hδt, hut⟩ := polynomial_scalarRate_eventual_upper (ε / 2) (half_pos hε)
    filter_upwards [hfin, habs.eventually (ge_mem_nhds hδL), habs.eventually (gt_mem_nhds hδt),
      hL.eventually (lt_mem_nhds (by linarith : a0 - ε / 2 < a0))] with h hf hhL hhU hhlo
    have hl := hlower h hhL (b h)
    have hu := hut h hhU (b h)
    have hsL : L h ≤ (speciesRate (A h) (b h)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hf.1).1 hl
    have hSorder := ENNReal.toReal_mono hf.2 (speciesRate_le_scalarRate (A h) (b h))
    have hcU : (scalarRate (A h) (b h)).toReal ≤ a0 + ε / 2 :=
      ENNReal.toReal_le_of_le_ofReal (add_nonneg a0_pos.le (half_pos hε).le) hu
    constructor <;> rw [abs_lt] <;> constructor <;> linarith
  have hs : Tendsto (fun h : ℝ => (speciesRate (A h) (b h)).toReal) (𝓝 0) (𝓝 a0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    filter_upwards [hb ε hε] with h hh
    simpa only [Real.dist_eq] using hh.1
  have hc : Tendsto (fun h : ℝ => (scalarRate (A h) (b h)).toReal) (𝓝 0) (𝓝 a0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    filter_upwards [hb ε hε] with h hh
    simpa only [Real.dist_eq] using hh.2
  constructor
  · apply (ENNReal.tendsto_ofReal hs).congr'
    exact hfin.mono fun h hh => ENNReal.ofReal_toReal hh.1
  · apply (ENNReal.tendsto_ofReal hc).congr'
    exact hfin.mono fun h hh => ENNReal.ofReal_toReal hh.2

end DGPS.Examples.PolynomialSpecies
