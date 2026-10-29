/- Genuine attained extended infimum over all probability laws.
No absolute continuity, finite KL or proper energy restriction is imposed on
competitors. The bounded exponent makes the shifted energy nonnegative. -/
import DGRHS.Entropy.GibbsExtendedRewrite
noncomputable section
open MeasureTheory InformationTheory
namespace DGRHS.Entropy

def gibbsExtendedValues {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (u : Ω→ℝ) (C : ℝ) : Set EReal :=
  {r | ∃ ν : Measure Ω, IsProbabilityMeasure ν ∧
    r=gibbsExtendedFreeEnergy μ ν u C}

theorem gibbsExtended_isLeast {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : Ω→ℝ) (C : ℝ)
    (hcap : ∀ x,u x≤C)
    (hexp : Integrable (fun x=>Real.exp (u x)) μ) :
    IsLeast (gibbsExtendedValues μ u C)
      ((-Real.log (∫ x,Real.exp (u x) ∂μ) : ℝ):EReal) := by
  letI := isProbabilityMeasure_tilted hexp
  refine ⟨?_,?_⟩
  · refine ⟨μ.tilted u,inferInstance,?_⟩
    rw [gibbsExtendedFreeEnergy_rewrite μ (μ.tilted u) u C hcap hexp,
      klDiv_self]
    simp
  · intro r hr
    obtain ⟨ν,hν,hr⟩ := hr
    letI := hν
    rw [hr,gibbsExtendedFreeEnergy_rewrite μ ν u C hcap hexp]
    have h := EReal.sub_le_sub (EReal.coe_ennreal_nonneg (klDiv ν (μ.tilted u)))
      (le_rfl : (Real.log (∫ x,Real.exp (u x) ∂μ):EReal)≤_)
    simpa using h

theorem gibbsExtended_inf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : Ω→ℝ) (C : ℝ)
    (hcap : ∀ x,u x≤C)
    (hexp : Integrable (fun x=>Real.exp (u x)) μ) :
    sInf (gibbsExtendedValues μ u C)=
      ((-Real.log (∫ x,Real.exp (u x) ∂μ) : ℝ):EReal) :=
  (gibbsExtended_isLeast μ u C hcap hexp).csInf_eq

theorem gibbsExtended_cap_independent {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (u : Ω→ℝ) (C D : ℝ) (hC : ∀ x,u x≤C) (hD : ∀ x,u x≤D)
    (hexp : Integrable (fun x=>Real.exp (u x)) μ) :
    gibbsExtendedFreeEnergy μ ν u C=gibbsExtendedFreeEnergy μ ν u D := by
  rw [gibbsExtendedFreeEnergy_rewrite μ ν u C hC hexp,
    gibbsExtendedFreeEnergy_rewrite μ ν u D hD hexp]
end DGRHS.Entropy
#check @DGRHS.Entropy.gibbsExtended_isLeast
#print axioms DGRHS.Entropy.gibbsExtended_isLeast
#check @DGRHS.Entropy.gibbsExtended_inf
#print axioms DGRHS.Entropy.gibbsExtended_inf
#print axioms DGRHS.Entropy.gibbsExtended_cap_independent
