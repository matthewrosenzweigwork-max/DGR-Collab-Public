import DGRHS.Gaussian.PeriodicLogFourier
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Unique
/-! Actual real, measurable, even representative of the original arbitrary-d
Fourier kernel. Adaptation of local historical GreenSymmetry, preserved bytes
and hash under records/attempts/periodic; no old verdict transfer. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
omit [Fintype ι] [Nonempty ι] in
lemma periodicFrequencyVector_neg (k : PeriodicFrequency ι) :
    periodicFrequencyVector (-k) = -periodicFrequencyVector k := by
  ext j
  simp
lemma periodicLogFourierCoeff_neg (k : PeriodicFrequency ι) :
    periodicLogFourierCoeff (-k) = periodicLogFourierCoeff k := by
  simp [periodicLogFourierCoeff,periodicFrequencyVector_neg]
lemma periodicLogConstant_pos : 0 < periodicLogConstant ι := by
  have hd : (0:ℝ) < Fintype.card ι := by exact_mod_cast (Fintype.card_pos (α := ι))
  exact div_pos (mul_pos (Real.Gamma_pos_of_pos (by positivity))
    (Real.rpow_pos_of_pos (by positivity) _)) (by norm_num)
lemma periodicStabilityThreshold_pos : 0 < periodicStabilityThreshold ι := by
  exact div_pos (pow_pos (by positivity) _) periodicLogConstant_pos
local instance periodicRealityCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

omit [Nonempty ι] in
/-- The coefficient integral uses the project's explicit normalized Haar measure. -/
theorem periodic_mFourierCoeff_eq_integral (f : (PeriodicTorus ι) → ℂ) (k : (PeriodicFrequency ι)) :
    UnitAddTorus.mFourierCoeff f k =
      ∫ x, UnitAddTorus.mFourier (-k) x * f x ∂(periodicHaar ι) := rfl

omit [Nonempty ι] in
theorem periodic_mFourierCoeff_congr {f g : (PeriodicTorus ι) → ℂ}
    (hfg : f =ᵐ[(periodicHaar ι)] g) (k : (PeriodicFrequency ι)) :
    UnitAddTorus.mFourierCoeff f k = UnitAddTorus.mFourierCoeff g k := by
  simp only [periodic_mFourierCoeff_eq_integral]
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

omit [Nonempty ι] in
theorem periodic_mFourierCoeff_conj (f : (PeriodicTorus ι) → ℂ) (k : (PeriodicFrequency ι)) :
    UnitAddTorus.mFourierCoeff (fun x ↦ conj (f x)) k =
      conj (UnitAddTorus.mFourierCoeff f (-k)) := by
  simp only [periodic_mFourierCoeff_eq_integral, neg_neg]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [UnitAddTorus.mFourier_neg, map_mul]

/-- Conjugating an L2 element conjugates its Fourier coefficient at the opposite frequency. -/
theorem periodic_mFourierCoeff_star (f : Lp ℂ 2 (periodicHaar ι)) (k : (PeriodicFrequency ι)) :
    UnitAddTorus.mFourierCoeff (star f : Lp ℂ 2 (periodicHaar ι)) k =
      conj (UnitAddTorus.mFourierCoeff f (-k)) := by
  have hstar : (star f : Lp ℂ 2 (periodicHaar ι)) =ᵐ[(periodicHaar ι)]
      (fun x ↦ conj (f x)) := Lp.coeFn_star f
  exact (periodic_mFourierCoeff_congr hstar k).trans (periodic_mFourierCoeff_conj f k)

omit [Nonempty ι] in
@[simp]
theorem conj_periodicLogFourierCoeff (k : (PeriodicFrequency ι)) :
    conj (periodicLogFourierCoeff k) = periodicLogFourierCoeff k := by
  unfold periodicLogFourierCoeff
  split_ifs <;> simp only [map_zero, Complex.conj_ofReal]

theorem periodicLogL2_star : star (periodicLogL2 (ι := ι)) = (periodicLogL2 (ι := ι)) := by
  apply periodicLogL2_unique
  intro k
  rw [periodic_mFourierCoeff_star, periodicLogL2_fourierCoeff, periodicLogFourierCoeff_neg,
    conj_periodicLogFourierCoeff]

theorem periodicLogL2_conj_ae :
    (fun x ↦ conj ((periodicLogL2 (ι := ι)) x)) =ᵐ[(periodicHaar ι)] (periodicLogL2 (ι := ι)) := by
  have h := Lp.coeFn_star (periodicLogL2 (ι := ι))
  rw [periodicLogL2_star] at h
  exact h.symm

theorem periodicLogL2_im_zero_ae :
    ∀ᵐ x ∂(periodicHaar ι), ((periodicLogL2 (ι := ι)) x).im = 0 := by
  filter_upwards [periodicLogL2_conj_ae] with x hx
  exact RCLike.conj_eq_iff_im.mp hx

/-- Invariance follows from the regular circle Haar measures and finite products. -/
instance periodicHaar_isNegInvariant : Measure.IsNegInvariant (periodicHaar ι) := by
  have : Measure.IsNegInvariant (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    unfold AddCircle.haarAddCircle
    infer_instance
  exact Measure.pi.isNegInvariant (fun _ : ι ↦ AddCircle.haarAddCircle)

omit [Nonempty ι] in
theorem periodicHaar_preserving_neg :
    MeasurePreserving (fun x : (PeriodicTorus ι) ↦ -x) (periodicHaar ι) (periodicHaar ι) :=
  Measure.measurePreserving_neg (periodicHaar ι)

omit [Nonempty ι] in
theorem periodic_mFourier_reflection (k : (PeriodicFrequency ι)) (x : (PeriodicTorus ι)) :
    UnitAddTorus.mFourier k (-x) = UnitAddTorus.mFourier (-k) x := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply,
    fourier_apply, smul_neg, neg_smul]

theorem periodic_mFourierCoeff_reflection (f : (PeriodicTorus ι) → ℂ) (k : (PeriodicFrequency ι)) :
    UnitAddTorus.mFourierCoeff (fun x ↦ f (-x)) k =
      UnitAddTorus.mFourierCoeff f (-k) := by
  simp only [periodic_mFourierCoeff_eq_integral, neg_neg]
  simpa only [periodic_mFourier_reflection] using
    (integral_neg_eq_self (fun x : (PeriodicTorus ι) ↦ UnitAddTorus.mFourier k x * f x)
      (periodicHaar ι))

/-- Reflection as an operation on the actual L2 quotient space. -/
def periodicReflectL2 (f : Lp ℂ 2 (periodicHaar ι)) : Lp ℂ 2 (periodicHaar ι) :=
  Lp.compMeasurePreserving (fun x : (PeriodicTorus ι) ↦ -x) periodicHaar_preserving_neg f

theorem periodicReflectL2_coeFn (f : Lp ℂ 2 (periodicHaar ι)) :
    periodicReflectL2 f =ᵐ[(periodicHaar ι)] (fun x ↦ f (-x)) :=
  Lp.coeFn_compMeasurePreserving f periodicHaar_preserving_neg

theorem periodic_mFourierCoeff_reflectL2 (f : Lp ℂ 2 (periodicHaar ι)) (k : (PeriodicFrequency ι)) :
    UnitAddTorus.mFourierCoeff (periodicReflectL2 f) k =
      UnitAddTorus.mFourierCoeff f (-k) :=
  (periodic_mFourierCoeff_congr (periodicReflectL2_coeFn f) k).trans
    (periodic_mFourierCoeff_reflection f k)

theorem periodicLogL2_reflect : periodicReflectL2 (periodicLogL2 (ι := ι)) = (periodicLogL2 (ι := ι)) := by
  apply periodicLogL2_unique
  intro k
  rw [periodic_mFourierCoeff_reflectL2, periodicLogL2_fourierCoeff, periodicLogFourierCoeff_neg]

theorem periodicLogL2_even_ae :
    (fun x ↦ (periodicLogL2 (ι := ι)) (-x)) =ᵐ[(periodicHaar ι)] (periodicLogL2 (ι := ι)) := by
  have h := periodicReflectL2_coeFn (periodicLogL2 (ι := ι))
  rw [periodicLogL2_reflect] at h
  exact h.symm

/-- A measurable, everywhere even, real representative of the Green L2 class. -/
def periodicLogKernel (x : (PeriodicTorus ι)) : ℝ :=
  (((periodicLogL2 (ι := ι)) x).re + ((periodicLogL2 (ι := ι)) (-x)).re) / 2

theorem periodicLogKernel_measurable : Measurable (periodicLogKernel (ι := ι)) := by
  have h : Measurable (fun x : (PeriodicTorus ι) ↦ ((periodicLogL2 (ι := ι)) x).re) :=
    Complex.continuous_re.measurable.comp (Lp.stronglyMeasurable (periodicLogL2 (ι := ι))).measurable
  exact (h.add (h.comp measurable_neg)).div_const 2

theorem periodicLogKernel_even (x : (PeriodicTorus ι)) :
    periodicLogKernel (-x) = periodicLogKernel x := by
  simp only [periodicLogKernel, neg_neg]
  ring

theorem periodicLogKernel_ae_re :
    periodicLogKernel =ᵐ[(periodicHaar ι)] (fun x ↦ ((periodicLogL2 (ι := ι)) x).re) := by
  filter_upwards [periodicLogL2_even_ae] with x hx
  simp only [periodicLogKernel, hx]
  ring

theorem periodicLogKernel_coe_ae :
    (fun x ↦ (periodicLogKernel x : ℂ)) =ᵐ[(periodicHaar ι)] (periodicLogL2 (ι := ι)) := by
  filter_upwards [periodicLogKernel_ae_re, periodicLogL2_conj_ae] with x hx hc
  rw [hx]
  exact RCLike.conj_eq_iff_re.mp hc

theorem periodicLogKernel_memLp : MemLp periodicLogKernel 2 (periodicHaar ι) :=
  (memLp_congr_ae periodicLogKernel_ae_re).2 (Lp.memLp (periodicLogL2 (ι := ι))).re

theorem periodicLogKernel_integrable :
    Integrable periodicLogKernel (periodicHaar ι) :=
  MemLp.integrable (by norm_num) periodicLogKernel_memLp

theorem periodicLogKernel_integral_zero :
    (∫ x, periodicLogKernel x ∂(periodicHaar ι)) = 0 := by
  calc
    (∫ x, periodicLogKernel x ∂(periodicHaar ι)) =
        ∫ x, ((periodicLogL2 (ι := ι)) x).re ∂(periodicHaar ι) :=
      integral_congr_ae periodicLogKernel_ae_re
    _ = (∫ x, (periodicLogL2 (ι := ι)) x ∂(periodicHaar ι)).re := integral_re periodicLogL2_integrable
    _ = 0 := by rw [periodicLogL2_integral_zero]; rfl

theorem periodicLogKernel_fourierCoeff (k : (PeriodicFrequency ι)) :
    UnitAddTorus.mFourierCoeff (fun x ↦ (periodicLogKernel x : ℂ)) k =
      periodicLogFourierCoeff k :=
  (periodic_mFourierCoeff_congr periodicLogKernel_coe_ae k).trans
    (periodicLogL2_fourierCoeff k)

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLogKernel_fourierCoeff
#print axioms DGRHS.Periodic.periodicLogKernel_integral_zero
#check @DGRHS.Periodic.periodicLogKernel_fourierCoeff
