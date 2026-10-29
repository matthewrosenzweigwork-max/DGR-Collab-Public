import DGRHS.Gaussian.PeriodicGreenGlobalLower
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-! The actual signed Green integral for an arbitrary probability law.
For absolutely continuous laws its negative part is proved finite below,
without any entropy hypothesis. No divergent real integral defines this form. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicGreenEnergyExtended (μ : Measure (PeriodicTorus ι)) : EReal :=
  (∫⁻ p : PeriodicTorus ι × PeriodicTorus ι,
    ENNReal.ofReal (max (periodicLogKernel (p.1-p.2)) 0) ∂μ.prod μ).toEReal-
  (∫⁻ p : PeriodicTorus ι × PeriodicTorus ι,
    ENNReal.ofReal (max (-periodicLogKernel (p.1-p.2)) 0) ∂μ.prod μ).toEReal

theorem periodicGreen_negativePart_integrable (μ : Measure (PeriodicTorus ι))
    [IsProbabilityMeasure μ] (hμ : μ ≪ periodicHaar ι) :
    Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      max (-periodicLogKernel (p.1-p.2)) 0) (μ.prod μ) := by
  have hprod : μ.prod μ ≪ (periodicHaar ι).prod (periodicHaar ι) := hμ.prod hμ
  have hb := hprod.ae_le ((periodicHaar_preserving_difference (ι := ι)).quasiMeasurePreserving.ae
    periodicLogKernel_lower_ae)
  apply (integrable_const (periodicGreenLowerConstant ι)).mono'
    ((((periodicLogKernel_measurable.comp (measurable_fst.sub measurable_snd)).neg).max
      measurable_const).aestronglyMeasurable)
  filter_upwards [hb] with p hp
  rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
  exact max_le (by change -periodicLogKernel (p.1-p.2)≤periodicGreenLowerConstant ι; linarith)
    periodicGreenLowerConstant_nonneg

theorem periodicGreen_negativePart_lintegral_ne_top (μ : Measure (PeriodicTorus ι))
    [IsProbabilityMeasure μ] (hμ : μ ≪ periodicHaar ι) :
    (∫⁻ p : PeriodicTorus ι × PeriodicTorus ι,
      ENNReal.ofReal (max (-periodicLogKernel (p.1-p.2)) 0) ∂μ.prod μ) ≠ ∞ := by
  rw [←ofReal_integral_eq_lintegral_ofReal (periodicGreen_negativePart_integrable μ hμ)
    (Eventually.of_forall fun p => le_max_right _ _)]
  exact ENNReal.ofReal_ne_top

lemma signedGreen_extended_eq_integral (μ : Measure (PeriodicTorus ι))
    (hi : Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      periodicLogKernel (p.1-p.2)) (μ.prod μ)) :
    periodicGreenEnergyExtended μ=
      (((∫ p : PeriodicTorus ι × PeriodicTorus ι,periodicLogKernel (p.1-p.2) ∂μ.prod μ):ℝ):EReal) := by
  have hp : Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      max (periodicLogKernel (p.1-p.2)) 0) (μ.prod μ) := by
    apply hi.norm.mono'
      (((periodicLogKernel_measurable.comp (measurable_fst.sub measurable_snd)).max
        measurable_const).aestronglyMeasurable)
    exact Eventually.of_forall fun p => by
      change ‖max (periodicLogKernel (p.1-p.2)) 0‖≤‖periodicLogKernel (p.1-p.2)‖
      rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _),Real.norm_eq_abs]
      exact max_le (le_abs_self _) (abs_nonneg _)
  have hn : Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      max (-periodicLogKernel (p.1-p.2)) 0) (μ.prod μ) := by
    apply hi.norm.mono'
      ((((periodicLogKernel_measurable.comp (measurable_fst.sub measurable_snd)).neg).max
        measurable_const).aestronglyMeasurable)
    exact Eventually.of_forall fun p => by
      change ‖max (-periodicLogKernel (p.1-p.2)) 0‖≤‖periodicLogKernel (p.1-p.2)‖
      rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _),Real.norm_eq_abs]
      exact max_le (neg_le_abs _) (abs_nonneg _)
  have hp0 : 0≤∫ p : PeriodicTorus ι × PeriodicTorus ι,
      max (periodicLogKernel (p.1-p.2)) 0 ∂μ.prod μ :=
    integral_nonneg fun _ => le_max_right _ _
  have hn0 : 0≤∫ p : PeriodicTorus ι × PeriodicTorus ι,
      max (-periodicLogKernel (p.1-p.2)) 0 ∂μ.prod μ :=
    integral_nonneg fun _ => le_max_right _ _
  unfold periodicGreenEnergyExtended
  rw [←ofReal_integral_eq_lintegral_ofReal hp (Eventually.of_forall fun _ => le_max_right _ _),
    ←ofReal_integral_eq_lintegral_ofReal hn (Eventually.of_forall fun _ => le_max_right _ _)]
  change (ENNReal.ofReal _ : EReal)-(ENNReal.ofReal _ : EReal)=_
  rw [EReal.coe_ennreal_ofReal,EReal.coe_ennreal_ofReal,max_eq_left hp0,max_eq_left hn0,
    ←EReal.coe_sub,←integral_sub hp hn]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    change max (periodicLogKernel (p.1-p.2)) 0-max (-periodicLogKernel (p.1-p.2)) 0=_
    by_cases h : 0≤periodicLogKernel (p.1-p.2)
    · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h),sub_zero]
    · rw [max_eq_right (le_of_not_ge h),max_eq_left (neg_nonneg.mpr (le_of_not_ge h))]
      ring

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicGreen_negativePart_integrable
#print axioms DGRHS.Periodic.periodicGreen_negativePart_lintegral_ne_top
#print axioms DGRHS.Periodic.signedGreen_extended_eq_integral
#check @DGRHS.Periodic.periodicGreen_negativePart_integrable
