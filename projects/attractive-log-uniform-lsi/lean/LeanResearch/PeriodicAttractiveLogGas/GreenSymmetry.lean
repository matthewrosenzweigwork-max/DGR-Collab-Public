import LeanResearch.PeriodicAttractiveLogGas.GreenFourier
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Reality and reflection symmetry of the constructed Green L2 class.

Conjugation and reflection are actual operations on `Lp` elements. Their
Fourier coefficients identify the transformed elements with `greenL2`.
A measurable real representative is then chosen by averaging the real parts
at opposite points; it is even everywhere and represents `greenL2` almost
everywhere. No pointwise Fourier sum or local regularity claim is used.

The L2 and measurable-representative statements have been elaborated.
The local logarithmic representative remains a separate obligation. -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate ENNReal

namespace PeriodicAttractiveLogGas

/- Match the local measure convention under which AddCircleMulti was defined.
Its finite product is definitionally `torusMeasure`, as already recorded by
`fourier_volume_eq_torusMeasure`. -/
local instance greenSymmetryCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The coefficient integral uses the project's explicit normalized Haar measure. -/
theorem torus_mFourierCoeff_eq_integral (f : Torus → ℂ) (k : Frequency) :
    UnitAddTorus.mFourierCoeff f k =
      ∫ x, UnitAddTorus.mFourier (-k) x * f x ∂torusMeasure := rfl

theorem torus_mFourierCoeff_congr {f g : Torus → ℂ}
    (hfg : f =ᵐ[torusMeasure] g) (k : Frequency) :
    UnitAddTorus.mFourierCoeff f k = UnitAddTorus.mFourierCoeff g k := by
  simp only [torus_mFourierCoeff_eq_integral]
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

theorem torus_mFourierCoeff_conj (f : Torus → ℂ) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (fun x ↦ conj (f x)) k =
      conj (UnitAddTorus.mFourierCoeff f (-k)) := by
  simp only [torus_mFourierCoeff_eq_integral, neg_neg]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [UnitAddTorus.mFourier_neg, map_mul]

/-- Conjugating an L2 element conjugates its Fourier coefficient at the opposite frequency. -/
theorem torus_mFourierCoeff_star (f : Lp ℂ 2 torusMeasure) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (star f : Lp ℂ 2 torusMeasure) k =
      conj (UnitAddTorus.mFourierCoeff f (-k)) := by
  have hstar : (star f : Lp ℂ 2 torusMeasure) =ᵐ[torusMeasure]
      (fun x ↦ conj (f x)) := Lp.coeFn_star f
  exact (torus_mFourierCoeff_congr hstar k).trans (torus_mFourierCoeff_conj f k)

@[simp]
theorem conj_greenFourierCoeff (k : Frequency) :
    conj (greenFourierCoeff k) = greenFourierCoeff k := by
  unfold greenFourierCoeff
  split_ifs <;> simp only [map_zero, Complex.conj_ofReal]

theorem greenL2_star : star greenL2 = greenL2 := by
  apply greenL2_unique
  intro k
  rw [torus_mFourierCoeff_star, greenL2_fourierCoeff, greenFourierCoeff_neg,
    conj_greenFourierCoeff]

theorem greenL2_conj_ae :
    (fun x ↦ conj (greenL2 x)) =ᵐ[torusMeasure] greenL2 := by
  have h := Lp.coeFn_star greenL2
  rw [greenL2_star] at h
  exact h.symm

theorem greenL2_im_zero_ae :
    ∀ᵐ x ∂torusMeasure, (greenL2 x).im = 0 := by
  filter_upwards [greenL2_conj_ae] with x hx
  exact RCLike.conj_eq_iff_im.mp hx

/-- Invariance follows from the regular circle Haar measures and finite products. -/
instance torusMeasure_isNegInvariant : Measure.IsNegInvariant torusMeasure := by
  have : Measure.IsNegInvariant (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    unfold AddCircle.haarAddCircle
    infer_instance
  exact Measure.pi.isNegInvariant (fun _ : Fin 2 ↦ AddCircle.haarAddCircle)

theorem torusMeasure_preserving_neg :
    MeasurePreserving (fun x : Torus ↦ -x) torusMeasure torusMeasure :=
  Measure.measurePreserving_neg torusMeasure

theorem torus_mFourier_reflection (k : Frequency) (x : Torus) :
    UnitAddTorus.mFourier k (-x) = UnitAddTorus.mFourier (-k) x := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply,
    fourier_apply, smul_neg, neg_smul]

theorem torus_mFourierCoeff_reflection (f : Torus → ℂ) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (fun x ↦ f (-x)) k =
      UnitAddTorus.mFourierCoeff f (-k) := by
  simp only [torus_mFourierCoeff_eq_integral, neg_neg]
  simpa only [torus_mFourier_reflection] using
    (integral_neg_eq_self (fun x : Torus ↦ UnitAddTorus.mFourier k x * f x)
      torusMeasure)

/-- Reflection as an operation on the actual L2 quotient space. -/
def reflectTorusL2 (f : Lp ℂ 2 torusMeasure) : Lp ℂ 2 torusMeasure :=
  Lp.compMeasurePreserving (fun x : Torus ↦ -x) torusMeasure_preserving_neg f

theorem reflectTorusL2_coeFn (f : Lp ℂ 2 torusMeasure) :
    reflectTorusL2 f =ᵐ[torusMeasure] (fun x ↦ f (-x)) :=
  Lp.coeFn_compMeasurePreserving f torusMeasure_preserving_neg

theorem torus_mFourierCoeff_reflectL2 (f : Lp ℂ 2 torusMeasure) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (reflectTorusL2 f) k =
      UnitAddTorus.mFourierCoeff f (-k) :=
  (torus_mFourierCoeff_congr (reflectTorusL2_coeFn f) k).trans
    (torus_mFourierCoeff_reflection f k)

theorem greenL2_reflect : reflectTorusL2 greenL2 = greenL2 := by
  apply greenL2_unique
  intro k
  rw [torus_mFourierCoeff_reflectL2, greenL2_fourierCoeff, greenFourierCoeff_neg]

theorem greenL2_even_ae :
    (fun x ↦ greenL2 (-x)) =ᵐ[torusMeasure] greenL2 := by
  have h := reflectTorusL2_coeFn greenL2
  rw [greenL2_reflect] at h
  exact h.symm

/-- A measurable, everywhere even, real representative of the Green L2 class. -/
def greenRealRepresentative (x : Torus) : ℝ :=
  ((greenL2 x).re + (greenL2 (-x)).re) / 2

theorem greenRealRepresentative_measurable : Measurable greenRealRepresentative := by
  have h : Measurable (fun x : Torus ↦ (greenL2 x).re) :=
    Complex.continuous_re.measurable.comp (Lp.stronglyMeasurable greenL2).measurable
  exact (h.add (h.comp measurable_neg)).div_const 2

theorem greenRealRepresentative_even (x : Torus) :
    greenRealRepresentative (-x) = greenRealRepresentative x := by
  simp only [greenRealRepresentative, neg_neg]
  ring

theorem greenRealRepresentative_ae_re :
    greenRealRepresentative =ᵐ[torusMeasure] (fun x ↦ (greenL2 x).re) := by
  filter_upwards [greenL2_even_ae] with x hx
  simp only [greenRealRepresentative, hx]
  ring

theorem greenRealRepresentative_coe_ae :
    (fun x ↦ (greenRealRepresentative x : ℂ)) =ᵐ[torusMeasure] greenL2 := by
  filter_upwards [greenRealRepresentative_ae_re, greenL2_conj_ae] with x hx hc
  rw [hx]
  exact RCLike.conj_eq_iff_re.mp hc

theorem greenRealRepresentative_memLp : MemLp greenRealRepresentative 2 torusMeasure :=
  (memLp_congr_ae greenRealRepresentative_ae_re).2 (Lp.memLp greenL2).re

theorem greenRealRepresentative_integrable :
    Integrable greenRealRepresentative torusMeasure :=
  MemLp.integrable (by norm_num) greenRealRepresentative_memLp

theorem greenRealRepresentative_integral_zero :
    (∫ x, greenRealRepresentative x ∂torusMeasure) = 0 := by
  calc
    (∫ x, greenRealRepresentative x ∂torusMeasure) =
        ∫ x, (greenL2 x).re ∂torusMeasure :=
      integral_congr_ae greenRealRepresentative_ae_re
    _ = (∫ x, greenL2 x ∂torusMeasure).re := integral_re greenL2_integrable
    _ = 0 := by rw [greenL2_integral_zero]; rfl

theorem greenRealRepresentative_fourierCoeff (k : Frequency) :
    UnitAddTorus.mFourierCoeff (fun x ↦ (greenRealRepresentative x : ℂ)) k =
      greenFourierCoeff k :=
  (torus_mFourierCoeff_congr greenRealRepresentative_coe_ae k).trans
    (greenL2_fourierCoeff k)

end PeriodicAttractiveLogGas
