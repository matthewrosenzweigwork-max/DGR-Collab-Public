import LeanResearch.PeriodicAttractiveLogGas.GreenSymmetry
import Mathlib.Tactic.FieldSimp

/-! Fourier-to-weak-equation passage for the constructed Green L2 class.
Source: lem:kernel. The analytic assertion that the ordinary negative
Laplacian of every smooth periodic test has the required Fourier multiplier
is a separate obligation. It is explicit in the hypothesis below. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace PeriodicAttractiveLogGas

local instance greenWeakFourierCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem mFourierCoeff_zero_eq_integral (f : Torus → ℂ) :
    UnitAddTorus.mFourierCoeff f 0 = ∫ x, f x ∂torusMeasure := by
  simp only [UnitAddTorus.mFourierCoeff, neg_zero, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_smul]
  rfl

theorem mFourier_apply_zero (k : Frequency) : UnitAddTorus.mFourier k (0 : Torus) = 1 := by
  simp [UnitAddTorus.mFourier]

theorem greenFourierCoeff_mul_laplacianSymbol {k : Frequency} (hk : k ≠ 0) :
    greenFourierCoeff k * ((4 * Real.pi ^ 2 * frequencySq k : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) := by
  rw [greenFourierCoeff_of_ne_zero hk, ← Complex.ofReal_mul]
  congr 1
  field_simp [Real.pi_ne_zero, ne_of_gt (frequencySq_pos hk)]
  ring

/-- Parseval plus Fourier inversion recovers the point evaluation, without
assuming summability of the test's coefficients. That summability is derived
from the actual L2 negative-Laplacian candidate and its multiplier identity. -/
theorem greenL2_pairing_eq_of_fourier_laplacian
    (f : C(Torus, ℂ)) (h : Lp ℂ 2 torusMeasure)
    (hf : ∀ k : Frequency, UnitAddTorus.mFourierCoeff h k =
      ((4 * Real.pi ^ 2 * frequencySq k : ℝ) : ℂ) * UnitAddTorus.mFourierCoeff f k) :
    (∫ x, conj (greenL2 x) * h x ∂torusMeasure) =
      ((2 * Real.pi : ℝ) : ℂ) * (f 0 - ∫ x, f x ∂torusMeasure) := by
  let c : ℂ := ((2 * Real.pi : ℝ) : ℂ)
  have hc : c ≠ 0 := by simp [c, Real.pi_ne_zero]
  let I : ℂ := ∫ x, conj (greenL2 x) * h x ∂torusMeasure
  have hparse : HasSum (fun k : Frequency ↦
      conj (greenFourierCoeff k) * UnitAddTorus.mFourierCoeff h k) I := by
    simp_rw [← greenL2_fourierCoeff]
    exact UnitAddTorus.hasSum_prod_mFourierCoeff greenL2 h
  have hterm (k : Frequency) :
      (conj (greenFourierCoeff k) * UnitAddTorus.mFourierCoeff h k) / c =
        UnitAddTorus.mFourierCoeff f k -
          (if k = 0 then UnitAddTorus.mFourierCoeff f 0 else 0) := by
    rw [conj_greenFourierCoeff, hf]
    by_cases hk : k = 0
    · subst k
      simp
    · simp only [hk, ite_false, sub_zero]
      rw [← mul_assoc, greenFourierCoeff_mul_laplacianSymbol hk]
      change c * UnitAddTorus.mFourierCoeff f k / c = _
      field_simp
  have hdiff : HasSum (fun k : Frequency ↦ UnitAddTorus.mFourierCoeff f k -
      (if k = 0 then UnitAddTorus.mFourierCoeff f 0 else 0)) (I / c) := by
    exact HasSum.congr_fun (hparse.div_const c) fun k ↦ (hterm k).symm
  have hall : HasSum (UnitAddTorus.mFourierCoeff f)
      (I / c + UnitAddTorus.mFourierCoeff f 0) := by
    simpa only [sub_add_cancel] using hdiff.add
      (hasSum_ite_eq (0 : Frequency) (UnitAddTorus.mFourierCoeff f 0))
  have heval : HasSum (UnitAddTorus.mFourierCoeff f) (f 0) := by
    simpa only [mFourier_apply_zero, smul_eq_mul, mul_one] using!
      UnitAddTorus.hasSum_mFourier_series_apply_of_summable hall.summable (0 : Torus)
  have heq := hall.unique heval
  rw [mFourierCoeff_zero_eq_integral] at heq
  change I = c * (f 0 - ∫ x, f x ∂torusMeasure)
  rw [mul_comm c]
  apply (div_eq_iff hc).mp
  rw [eq_sub_iff_add_eq]
  exact heq

theorem greenRealRepresentative_mul_integrable (h : C(Torus, ℝ)) :
    Integrable (fun x ↦ greenRealRepresentative x * h x) torusMeasure :=
  greenRealRepresentative_memLp.integrable_mul
    (ContinuousMap.memLp (μ := torusMeasure) (p := 2) ℝ h)

theorem greenRealRepresentative_pairing_eq_of_fourier_laplacian
    (f h : C(Torus, ℝ))
    (hf : ∀ k : Frequency,
      UnitAddTorus.mFourierCoeff (fun x ↦ (h x : ℂ)) k =
        ((4 * Real.pi ^ 2 * frequencySq k : ℝ) : ℂ) *
          UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k) :
    (∫ x, greenRealRepresentative x * h x ∂torusMeasure) =
      (2 * Real.pi) * (f 0 - ∫ x, f x ∂torusMeasure) := by
  let fc : C(Torus, ℂ) := ⟨fun x ↦ (f x : ℂ), by fun_prop⟩
  let hc : C(Torus, ℂ) := ⟨fun x ↦ (h x : ℂ), by fun_prop⟩
  let H : Lp ℂ 2 torusMeasure := ContinuousMap.toLp 2 torusMeasure ℂ hc
  have hcoe : (H : Torus → ℂ) =ᵐ[torusMeasure] hc :=
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) torusMeasure hc
  have hcoeff (k : Frequency) : UnitAddTorus.mFourierCoeff H k =
      ((4 * Real.pi ^ 2 * frequencySq k : ℝ) : ℂ) * UnitAddTorus.mFourierCoeff fc k := by
    rw [torus_mFourierCoeff_congr hcoe k]
    exact hf k
  have hpair := greenL2_pairing_eq_of_fourier_laplacian fc H hcoeff
  have hint : (∫ x, conj (greenL2 x) * H x ∂torusMeasure) =
      ((∫ x, greenRealRepresentative x * h x ∂torusMeasure : ℝ) : ℂ) := by
    calc
      _ = ∫ x, ((greenRealRepresentative x * h x : ℝ) : ℂ) ∂torusMeasure := by
        apply integral_congr_ae
        filter_upwards [greenRealRepresentative_coe_ae, hcoe] with x hx hh
        rw [← hx, hh]
        simp only [hc, ContinuousMap.coe_mk, Complex.conj_ofReal, Complex.ofReal_mul]
      _ = _ := integral_ofReal
  rw [hint] at hpair
  have hfint : (∫ x, fc x ∂torusMeasure) = ((∫ x, f x ∂torusMeasure : ℝ) : ℂ) :=
    integral_ofReal
  rw [hfint] at hpair
  apply Complex.ofReal_injective
  simpa only [fc, ContinuousMap.coe_mk, Complex.ofReal_mul, Complex.ofReal_sub] using hpair

end PeriodicAttractiveLogGas
