/- Null singular sets do not change genuine all-law free energies. Finite KL
forces absolute continuity; infinite KL remains infinite at positive scale. -/
import DGRHS.Entropy.GibbsBoundedEnergy
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace DGRHS.Entropy

def singularBoundedEnergyFreeEnergy {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (E : Ω→ℝ) (L b : ℝ) (Good : Ω→Prop) : EReal := by
  classical
  exact (klDiv ν μ:EReal)*(b⁻¹ : ℝ)+
    ((∫⁻ x,(if Good x then ENNReal.ofReal (E x-L) else ∞) ∂ν : ℝ≥0∞):EReal)+(L:EReal)

theorem singularBoundedEnergyFreeEnergy_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Ω→ℝ) (L b : ℝ) (hb : 0<b) (Good : Ω→Prop)
    (hGood : ∀ᵐ x ∂μ,Good x) :
    singularBoundedEnergyFreeEnergy μ ν E L b Good=boundedEnergyFreeEnergy μ ν E L b := by
  classical
  by_cases hK : klDiv ν μ=∞
  · simp only [singularBoundedEnergyFreeEnergy,boundedEnergyFreeEnergy,hK,
      EReal.coe_ennreal_top,EReal.top_mul_coe_of_pos (inv_pos.mpr hb),
      EReal.top_add_of_ne_bot (EReal.coe_ennreal_ne_bot _),EReal.top_add_coe]
  · have hac := (klDiv_ne_top_iff.mp hK).1
    have he : (fun x=>if Good x then ENNReal.ofReal (E x-L) else ∞)=ᵐ[ν]
        (fun x=>ENNReal.ofReal (E x-L)) := by
      filter_upwards [hac.ae_le hGood] with x hx
      simp only [if_pos hx]
    unfold singularBoundedEnergyFreeEnergy boundedEnergyFreeEnergy
    rw [lintegral_congr_ae he]
end DGRHS.Entropy
#check @DGRHS.Entropy.singularBoundedEnergyFreeEnergy_eq
#print axioms DGRHS.Entropy.singularBoundedEnergyFreeEnergy_eq
