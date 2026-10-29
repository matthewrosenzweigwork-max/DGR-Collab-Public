import DGRHS.Entropy.GibbsFiniteDomain
import DGRHS.Gaussian.LogPhysicalPotential
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! Genuine Lebesgue likelihood entropy from a bounded density and a finite
logarithmic moment. The measurable minorant of withDensity handles the source
interface without adding a measurability premise on its density representative.
Native pinned Mathlib JapaneseBracket and RN/likelihood proofs are reused;
primary source/license bytes are preserved in native-log-moment-entropy-reuse.
This supplies the missing LOG thermal-domain input, not the Riesz domain. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Entropy

lemma integrable_llr_of_upper_bound_and_reference {S : Type*} [MeasurableSpace S]
    (ν₀ μ : Measure S) [SigmaFinite ν₀] [NeZero ν₀] [IsProbabilityMeasure μ]
    (hμ : μ ≪ ν₀) (f : S → ℝ) (C : ℝ)
    (hexp : Integrable (fun x => Real.exp (f x)) ν₀)
    (hf : Integrable f μ) (hcap : ∀ᵐ x ∂μ, llr μ ν₀ x ≤ C) :
    Integrable (llr μ ν₀) μ := by
  let Q := ν₀.tilted f
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_tilted hexp
  have hμQ : μ ≪ Q := hμ.trans (absolutelyContinuous_tilted hexp)
  have hn := integrable_negativeLikelihoodPart Q μ hμQ
  have he := llr_tilted_right hμ hexp
  let z := Real.log (∫ x, Real.exp (f x) ∂ν₀)
  apply (((integrable_const |C|).add hf.norm).add (integrable_const |z|)).add hn |>.mono'
    (measurable_llr μ ν₀).aestronglyMeasurable
  filter_upwards [he, hcap] with x hx hc
  change ‖llr μ ν₀ x‖ ≤ |C| + ‖f x‖ + |z| + max (-llr μ Q x) 0
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  apply abs_le.mpr
  have hn0 := le_max_right (-llr μ Q x) 0
  have hn1 := le_max_left (-llr μ Q x) 0
  change llr μ Q x = -f x + z + llr μ ν₀ x at hx
  constructor
  · linarith [neg_le_abs (f x), le_abs_self z, abs_nonneg C]
  · linarith [le_abs_self C, abs_nonneg (f x), abs_nonneg z]

lemma llr_densityMeasure_le {ι : Type*} [Fintype ι]
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∀ᵐ x ∂DGRHS.Gaussian.gaussianRieszDensityMeasure ρ,
      llr (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ) volume x ≤ Real.log (1+M) := by
  let μ := DGRHS.Gaussian.gaussianRieszDensityMeasure ρ
  have hμ : μ ≪ volume := withDensity_absolutelyContinuous _ _
  obtain ⟨g,hgm,hg,hgeq⟩ := exists_measurable_le_withDensity_eq
    (volume : Measure (EuclideanSpace ℝ ι)) (fun x => ENNReal.ofReal (ρ x))
  have hRN : μ.rnDeriv volume =ᵐ[volume] g := by
    change (volume.withDensity (fun x => ENNReal.ofReal (ρ x))).rnDeriv volume =ᵐ[volume] g
    rw [← hgeq]
    exact Measure.rnDeriv_withDensity volume hgm
  filter_upwards [hμ.ae_le hRN, hμ.ae_le hρ, Measure.rnDeriv_pos hμ] with x hx hρx hp
  change Real.log (μ.rnDeriv volume x).toReal ≤ Real.log (1+M)
  apply Real.log_le_log (ENNReal.toReal_pos hp.ne' ?_) ?_
  · rw [hx]
    exact ne_of_lt ((hg x).trans_lt ENNReal.ofReal_lt_top)
  · have hh : (μ.rnDeriv volume x).toReal ≤ M := by
      rw [hx, ← ENNReal.toReal_ofReal hM]
      exact ENNReal.toReal_mono (by simp) ((hg x).trans (ENNReal.ofReal_le_ofReal hρx))
    linarith

theorem integrable_llr_densityMeasure_of_log_moment {ι : Type*} [Fintype ι]
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hlog : Integrable (fun x => Real.log (1+‖x‖))
      (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)) :
    Integrable (llr (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ) volume)
      (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ) := by
  let μ := DGRHS.Gaussian.gaussianRieszDensityMeasure ρ
  let r : ℝ := (Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ)+1
  let f := fun x : EuclideanSpace ℝ ι => -r * Real.log (1+‖x‖)
  have hexp : Integrable (fun x => Real.exp (f x)) volume := by
    have hi : Integrable (fun x : EuclideanSpace ℝ ι => (1+‖x‖)^(-r)) volume :=
      integrable_one_add_norm (by dsimp [r]; linarith)
    apply hi.congr
    filter_upwards [] with x
    rw [Real.rpow_def_of_pos (by positivity : 0 < 1+‖x‖)]
    congr 1
    dsimp [f]
    ring
  exact integrable_llr_of_upper_bound_and_reference volume μ
    (withDensity_absolutelyContinuous _ _) f (Real.log (1+M)) hexp
    (hlog.const_mul (-r)) (llr_densityMeasure_le ρ M hM hρ)

end DGRHS.Entropy
#check @DGRHS.Entropy.integrable_llr_of_upper_bound_and_reference
#print axioms DGRHS.Entropy.integrable_llr_of_upper_bound_and_reference
#check @DGRHS.Entropy.llr_densityMeasure_le
#print axioms DGRHS.Entropy.llr_densityMeasure_le
#check @DGRHS.Entropy.integrable_llr_densityMeasure_of_log_moment
#print axioms DGRHS.Entropy.integrable_llr_densityMeasure_of_log_moment
