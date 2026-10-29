/- A bounded-above Gibbs exponent makes finite entropy relative to Gibbs
exactly equivalent to finite base entropy and proper exponent expectation. -/
import DGRHS.Entropy.GibbsEntropyRewrite
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace DGRHS.Entropy

lemma integrable_negativeLikelihoodPart {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ν ≪ μ) : Integrable (fun x=>max (-llr ν μ x) 0) ν := by
  have hRN : Integrable (fun x=>(μ.rnDeriv ν x).toReal) ν :=
    Measure.integrable_toReal_rnDeriv
  have he : Integrable (fun x=>Real.exp (-llr ν μ x)) ν :=
    hRN.congr (exp_neg_llr hν).symm
  apply he.mono' ((measurable_llr ν μ).neg.max measurable_const).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
  apply max_le
  · change -llr ν μ x≤Real.exp (-llr ν μ x)
    linarith [Real.add_one_le_exp (-llr ν μ x)]
  · exact (Real.exp_pos _).le

 theorem gibbsKL_finite_domain {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (u : Ω→ℝ) (C : ℝ) (hcap : ∀ x,u x≤C)
    (hexp : Integrable (fun x=>Real.exp (u x)) μ) :
    klDiv ν (μ.tilted u)≠∞ ↔ ν ≪ μ ∧ Integrable u ν ∧ Integrable (llr ν μ) ν := by
  letI := isProbabilityMeasure_tilted hexp
  constructor
  · intro hfinite
    obtain ⟨hνQ,hllrQ⟩ := klDiv_ne_top_iff.mp hfinite
    have hν := hνQ.trans (tilted_absolutelyContinuous μ u)
    have hm : AEStronglyMeasurable u ν :=
      ((Real.aemeasurable_of_aemeasurable_exp hexp.aemeasurable).mono_ac hν).aestronglyMeasurable
    have hn := integrable_negativeLikelihoodPart μ ν hν
    let z := fun x=>llr ν (μ.tilted u) x-Real.log (∫ y,Real.exp (u y) ∂μ)+C
    have hz : Integrable z ν := (hllrQ.sub (integrable_const _)).add (integrable_const C)
    have he := llr_tilted_right hν hexp
    have ht : Integrable (fun x=>C-u x) ν := by
      apply (hz.norm.add hn).mono' ((aestronglyMeasurable_const).sub hm)
      filter_upwards [he] with x hx
      change ‖C-u x‖≤‖z x‖+max (-llr ν μ x) 0
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hcap x))]
      have h1 := le_abs_self (z x)
      have h2 := le_max_left (-llr ν μ x) 0
      change C-u x≤‖z x‖+max (-llr ν μ x) 0
      rw [Real.norm_eq_abs]
      dsimp [z] at h1
      rw [hx] at h1
      dsimp only [z]
      rw [hx]
      linarith
    have hu : Integrable u ν := by
      have hi := (integrable_const C).sub ht
      convert hi using 1
      funext x
      simp only [Pi.sub_apply]
      ring
    have hL : Integrable (llr ν μ) ν := by
      apply (hz.sub ht).congr
      filter_upwards [he] with x hx
      dsimp [z]
      rw [hx]
      ring
    exact ⟨hν,hu,hL⟩
  · rintro ⟨hν,hu,hL⟩
    exact klDiv_ne_top_iff.mpr ⟨hν.trans (absolutelyContinuous_tilted hexp),
      integrable_llr_tilted_right hν hu hL hexp⟩
end DGRHS.Entropy
#check @DGRHS.Entropy.gibbsKL_finite_domain
#print axioms DGRHS.Entropy.integrable_negativeLikelihoodPart
#print axioms DGRHS.Entropy.gibbsKL_finite_domain
