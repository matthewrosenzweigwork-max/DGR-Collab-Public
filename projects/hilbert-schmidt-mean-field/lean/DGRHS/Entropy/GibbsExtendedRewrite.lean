/- Genuine all-law extended rewriting for an exponent bounded above.
The energy expectation is the nonnegative shifted Lebesgue integral.
No improper real integral or conversion of infinite KL toReal is used. -/
import DGRHS.Entropy.GibbsFiniteDomain
import Mathlib.Data.EReal.Operations
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace DGRHS.Entropy

def gibbsExtendedFreeEnergy {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (u : Ω→ℝ) (C : ℝ) : EReal :=
  ((klDiv ν μ+(∫⁻ x,ENNReal.ofReal (C-u x) ∂ν) : ℝ≥0∞) : EReal)-(C:EReal)

 theorem gibbsExtendedFreeEnergy_rewrite {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (u : Ω→ℝ) (C : ℝ) (hcap : ∀ x,u x≤C)
    (hexp : Integrable (fun x=>Real.exp (u x)) μ) :
    gibbsExtendedFreeEnergy μ ν u C=
      (klDiv ν (μ.tilted u) : EReal)-(Real.log (∫ x,Real.exp (u x) ∂μ):EReal) := by
  letI := isProbabilityMeasure_tilted hexp
  have hpos : ∀ᵐ x ∂ν,0≤C-u x := Filter.Eventually.of_forall fun x=>sub_nonneg.mpr (hcap x)
  by_cases hQ : klDiv ν (μ.tilted u)=∞
  · by_cases hP : klDiv ν μ=∞
    · simp only [gibbsExtendedFreeEnergy,hP,hQ,top_add,EReal.coe_ennreal_top,EReal.top_sub_coe]
    · obtain ⟨hν,hL⟩ := klDiv_ne_top_iff.mp hP
      have hm : AEStronglyMeasurable (fun x=>C-u x) ν :=
        aestronglyMeasurable_const.sub
          (((Real.aemeasurable_of_aemeasurable_exp hexp.aemeasurable).mono_ac hν).aestronglyMeasurable)
      have hu : ¬Integrable u ν := by
        intro hu
        have hf := (gibbsKL_finite_domain μ ν u C hcap hexp).mpr ⟨hν,hu,hL⟩
        exact hf hQ
      have ht : ¬Integrable (fun x=>C-u x) ν := by
        intro ht
        apply hu
        have hi := (integrable_const C).sub ht
        convert hi using 1
        funext x
        simp only [Pi.sub_apply]
        ring
      have hinf : (∫⁻ x,ENNReal.ofReal (C-u x) ∂ν)=∞ := by
        by_contra hne
        exact ht ((lintegral_ofReal_ne_top_iff_integrable hm hpos).mp hne)
      simp only [gibbsExtendedFreeEnergy,hinf,hQ,add_top,EReal.coe_ennreal_top,EReal.top_sub_coe]
  · obtain ⟨hν,hu,hL⟩ := (gibbsKL_finite_domain μ ν u C hcap hexp).mp hQ
    have ht : Integrable (fun x=>C-u x) ν := (integrable_const C).sub hu
    have hP : klDiv ν μ≠∞ := klDiv_ne_top_iff.mpr ⟨hν,hL⟩
    have hi : (∫⁻ x,ENNReal.ofReal (C-u x) ∂ν)=ENNReal.ofReal (C-∫ x,u x ∂ν) := by
      rw [←ofReal_integral_eq_lintegral_ofReal ht hpos,integral_sub (integrable_const C) hu]
      simp
    have hv : 0≤C-∫ x,u x ∂ν := by
      have h := integral_nonneg_of_ae hpos
      rw [integral_sub (integrable_const C) hu] at h
      simpa using h
    have hr := (gibbsEntropy_rewrite μ ν u hν hu hexp hL).2
    unfold gibbsExtendedFreeEnergy
    rw [hi,EReal.coe_ennreal_add,←EReal.coe_ennreal_toReal hP,
      ←EReal.coe_ennreal_toReal hQ,EReal.coe_ennreal_ofReal,max_eq_left hv,
      ←EReal.coe_add,←EReal.coe_sub,←EReal.coe_sub]
    congr 1
    linarith
end DGRHS.Entropy
#check @DGRHS.Entropy.gibbsExtendedFreeEnergy_rewrite
#print axioms DGRHS.Entropy.gibbsExtendedFreeEnergy_rewrite
