/- Averaging a genuine pointwise estimate over every probability law.
The energy is bounded below and its nonnegative shifted Lebesgue integral
retains infinity. Bounded observables are proper even at infinite entropy. -/
import DGRHS.Entropy.GibbsBoundedEnergy
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace DGRHS.Entropy

theorem bounded_observable_pointwise_freeEnergy {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a E : S→ℝ) (ha : StronglyMeasurable a) (hE : StronglyMeasurable E)
    (A L b k d : ℝ) (hA : ∀ x,|a x|≤A) (hL : ∀ x,L≤E x)
    (hb : 0<b) (hk : 0≤k) (hpoint : ∀ x,|a x|≤k*E x+d) :
    Integrable a ν ∧ ((|∫ x,a x ∂ν| : ℝ):EReal)≤
      (k:EReal)*boundedEnergyFreeEnergy μ ν E L b+(d:EReal) := by
  have hai : Integrable a ν := (integrable_const A).mono' ha.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x=>by simpa only [Real.norm_eq_abs] using hA x)
  refine ⟨hai,?_⟩
  have habs : |∫ x,a x ∂ν|≤∫ x,|a x| ∂ν := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm a (μ:=ν)
  have hAbsProper : Integrable (fun x=>|a x|) ν := by
    simpa only [Real.norm_eq_abs] using hai.norm
  by_cases hk0 : k=0
  · have hbnd : (∫ x,|a x| ∂ν)≤d := by
      have h := integral_mono (f:=fun x=>|a x|) (g:=fun _=>d) hAbsProper (integrable_const d)
        (fun x=>by simpa only [hk0,zero_mul,zero_add] using hpoint x)
      simpa only [Real.norm_eq_abs,integral_const,probReal_univ,one_smul] using h
    simpa only [hk0,EReal.coe_zero,zero_mul,zero_add,EReal.coe_le_coe_iff] using habs.trans hbnd
  have hkp : 0<k := lt_of_le_of_ne hk (Ne.symm hk0)
  by_cases hKL : klDiv ν μ=∞
  · simp only [boundedEnergyFreeEnergy,hKL,EReal.coe_ennreal_top,
      EReal.top_mul_coe_of_pos (inv_pos.mpr hb),
      EReal.top_add_of_ne_bot (EReal.coe_ennreal_ne_bot _),EReal.top_add_coe,
      EReal.coe_mul_top_of_pos hkp]
    exact le_top
  by_cases hShift : (∫⁻ x,ENNReal.ofReal (E x-L) ∂ν)=∞
  · have hKn : (klDiv ν μ:EReal)*(b⁻¹:ℝ)≠⊥ := by
      rw [←EReal.coe_ennreal_toReal hKL,←EReal.coe_mul]
      exact EReal.coe_ne_bot _
    simp only [boundedEnergyFreeEnergy,hShift,EReal.coe_ennreal_top,
      EReal.add_top_of_ne_bot hKn,EReal.top_add_coe,EReal.coe_mul_top_of_pos hkp]
    exact le_top
  have hShiftProper : Integrable (fun x=>E x-L) ν :=
    (lintegral_ofReal_ne_top_iff_integrable (hE.aestronglyMeasurable.sub aestronglyMeasurable_const)
      (Filter.Eventually.of_forall fun x=>sub_nonneg.mpr (hL x))).mp hShift
  have hEnergy : Integrable E ν := by
    convert hShiftProper.add (integrable_const L) using 1
    funext x
    simp only [Pi.add_apply]
    ring
  have hBound : |∫ x,a x ∂ν|≤k*(∫ x,E x ∂ν)+d := by
    have h := integral_mono (f:=fun x=>|a x|) (g:=fun x=>k*E x+d)
      hAbsProper ((hEnergy.const_mul k).add (integrable_const d)) hpoint
    rw [integral_add (hEnergy.const_mul _) (integrable_const d),integral_const_mul] at h
    simpa only [Real.norm_eq_abs,integral_const,probReal_univ,one_smul] using habs.trans h
  rw [boundedEnergyFreeEnergy_eq_proper μ ν E L b hL hEnergy hKL,
    ←EReal.coe_mul,←EReal.coe_add,EReal.coe_le_coe_iff]
  have hn : 0≤(klDiv ν μ).toReal/b := div_nonneg ENNReal.toReal_nonneg hb.le
  nlinarith [mul_nonneg hk hn]

end DGRHS.Entropy
#check @DGRHS.Entropy.bounded_observable_pointwise_freeEnergy
#print axioms DGRHS.Entropy.bounded_observable_pointwise_freeEnergy
