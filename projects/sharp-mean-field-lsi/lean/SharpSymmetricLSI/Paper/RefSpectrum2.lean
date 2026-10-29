import SharpSymmetricLSI.Paper.RefSpectrum1
import SharpSymmetricLSI.Paper.GroundState

/-!
# R23 (6.1), part 2: Fourier form of a weak equation `-Δe = g`

If `(e, G)` is a weak-gradient pair and `∫ G·∇Θ = ∫ g Θ` for every smooth periodic `Θ`, then
`ĝ(k) = 4π²|k|² ê(k)` (`cf_of_weak_eq`): test with `Θ = cos(2πk·x)` and `sin(2πk·x)`, and use
`Ĝⱼ = 2πi kⱼ ê`.
-/

open MeasureTheory Filter Topology Complex
open scoped ENNReal Real ContDiff
open UnitAddTorus

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `x ↦ ∑ᵢ kᵢ xᵢ` as a continuous linear map. -/
noncomputable def kLin (k : ι → ℤ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, (k i : ℝ) • ContinuousLinearMap.proj i

theorem kLin_apply (k : ι → ℤ) (x : ι → ℝ) : kLin k x = ∑ i, (k i : ℝ) * x i := by
  simp [kLin]

theorem kLin_single (k : ι → ℤ) (j : ι) : kLin k (Pi.single j 1) = k j := by
  rw [kLin_apply]
  simp [Pi.single_apply]

/-- `cos(2π k·x)`. -/
noncomputable def thC (k : ι → ℤ) (x : ι → ℝ) : ℝ := Real.cos (2 * π * kLin k x)

/-- `sin(2π k·x)`. -/
noncomputable def thS (k : ι → ℤ) (x : ι → ℝ) : ℝ := Real.sin (2 * π * kLin k x)

theorem kLin_add_intVec (k : ι → ℤ) (m : ι → ℤ) (x : ι → ℝ) :
    2 * π * kLin k (x + intVec m) = 2 * π * kLin k x + (∑ i, k i * m i : ℤ) * (2 * π) := by
  rw [map_add, kLin_apply k (intVec m)]
  simp only [intVec]
  push_cast
  ring

theorem isPer_thC (k : ι → ℤ) : IsPer (thC k) := fun m x => by
  simp only [thC, kLin_add_intVec, Real.cos_add_int_mul_two_pi]

theorem isPer_thS (k : ι → ℤ) : IsPer (thS k) := fun m x => by
  simp only [thS, kLin_add_intVec, Real.sin_add_int_mul_two_pi]

theorem contDiff_thC (k : ι → ℤ) : ContDiff ℝ ∞ (thC k) :=
  Real.contDiff_cos.comp (contDiff_const.mul (kLin k).contDiff)

theorem contDiff_thS (k : ι → ℤ) : ContDiff ℝ ∞ (thS k) :=
  Real.contDiff_sin.comp (contDiff_const.mul (kLin k).contDiff)

theorem Dk_thC (k : ι → ℤ) (j : ι) (x : ι → ℝ) :
    Dk (thC k) j x = -(2 * π * k j) * thS k x := by
  have h : HasFDerivAt (fun x => 2 * π * kLin k x) ((2 * π) • kLin k) x :=
    (kLin k).hasFDerivAt.const_mul (2 * π)
  have h2 := h.cos
  rw [Dk, show thC k = fun x => Real.cos (2 * π * kLin k x) from rfl, h2.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, kLin_single, thS]
  ring

theorem Dk_thS (k : ι → ℤ) (j : ι) (x : ι → ℝ) :
    Dk (thS k) j x = (2 * π * k j) * thC k x := by
  have h : HasFDerivAt (fun x => 2 * π * kLin k x) ((2 * π) • kLin k) x :=
    (kLin k).hasFDerivAt.const_mul (2 * π)
  have h2 := h.sin
  rw [Dk, show thS k = fun x => Real.sin (2 * π * kLin k x) from rfl, h2.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, kLin_single, thC]
  ring

theorem mFourier_neg_secT (k : ι → ℤ) (y : UnitAddTorus ι) :
    mFourier (-k) y = (thC k (secT y) : ℂ) - I * (thS k (secT y) : ℂ) := by
  conv_lhs => rw [← liftT_secT y]
  rw [mFourier_liftT, thC, thS, kLin_apply]
  set a : ℝ := 2 * π * ∑ i, (k i : ℝ) * secT y i
  have e : (2 * π * I * ∑ i, (((-k) i : ℤ) : ℂ) * (secT y i : ℂ)) = ((-a : ℝ) : ℂ) * I := by
    simp only [a, Pi.neg_apply, Int.cast_neg]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg]
  push_cast
  ring

theorem integrable_theta_mul {f : UnitAddTorus ι → ℝ} (hf : Integrable f) {Θ : (ι → ℝ) → ℝ}
    (hc : Continuous Θ) (hp : IsPer Θ) : Integrable (fun y => f y * Θ (secT y)) := by
  obtain ⟨C, hC⟩ := periodic_bounded hc hp
  exact hf.mul_bdd (c := C) (hc.measurable.comp measurable_secT).aestronglyMeasurable
    (Eventually.of_forall fun y => hC _)

theorem mFourierCoeff_eq_theta {f : UnitAddTorus ι → ℝ} (hf : Integrable f) (k : ι → ℤ) :
    mFourierCoeff (fun y => (f y : ℂ)) k =
      ((∫ y, f y * thC k (secT y) : ℝ) : ℂ) - I * ((∫ y, f y * thS k (secT y) : ℝ) : ℂ) := by
  rw [mFourierCoeff_eq_integral]
  have e : ∀ y, mFourier (-k) y • (f y : ℂ) =
      ((f y * thC k (secT y) : ℝ) : ℂ) - I * ((f y * thS k (secT y) : ℝ) : ℂ) := by
    intro y; rw [mFourier_neg_secT, smul_eq_mul]; push_cast; ring
  simp_rw [e]
  have h1 := integrable_theta_mul hf (contDiff_thC k).continuous (isPer_thC k)
  have h2 := integrable_theta_mul hf (contDiff_thS k).continuous (isPer_thS k)
  rw [integral_sub (f := fun t => ((f t * thC k (secT t) : ℝ) : ℂ))
    (g := fun t => I * ((f t * thS k (secT t) : ℝ) : ℂ)) (by exact h1.ofReal)
    (by exact h2.ofReal.const_mul I), integral_const_mul,
    integral_complex_ofReal, integral_complex_ofReal]

/-- **Fourier form of a weak equation `-Δe = g`.** -/
theorem cf_of_weak_eq {e : UnitAddTorus ι → ℝ} {G : UnitAddTorus ι → ι → ℝ}
    {g : UnitAddTorus ι → ℝ} (hw : IsWeakGrad e G) (he : Integrable e)
    (hG : ∀ j, Integrable fun y => G y j) (hg : Integrable g)
    (heq : ∀ Θ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ Θ → IsPer Θ →
      ∫ y, ∑ j, G y j * Dk Θ j (secT y) = ∫ y, g y * Θ (secT y)) (k : ι → ℤ) :
    mFourierCoeff (fun y => (g y : ℂ)) k =
      4 * π ^ 2 * (∑ j, ((k j : ℂ)) ^ 2) * mFourierCoeff (fun y => (e y : ℂ)) k := by
  set CG : ι → ℝ := fun j => ∫ y, G y j * thC k (secT y)
  set SG : ι → ℝ := fun j => ∫ y, G y j * thS k (secT y)
  have hGj : ∀ j, (CG j : ℂ) - I * (SG j : ℂ) =
      2 * π * I * k j * mFourierCoeff (fun y => (e y : ℂ)) k := by
    intro j
    rw [← mFourierCoeff_eq_theta (hG j), mFourierCoeff_grad hw he hG k j]
  have hint : ∀ (Θ : (ι → ℝ) → ℝ), Continuous Θ → IsPer Θ → ∀ j,
      Integrable fun y => G y j * Θ (secT y) := fun Θ hc hp j => integrable_theta_mul (hG j) hc hp
  have hC := heq _ (contDiff_thC k) (isPer_thC k)
  have hS := heq _ (contDiff_thS k) (isPer_thS k)
  simp_rw [Dk_thC, Dk_thS] at hC hS
  have eC : ∫ y, ∑ j, G y j * (-(2 * π * k j) * thS k (secT y)) =
      ∑ j, -(2 * π * k j) * SG j := by
    rw [integral_finsetSum _ fun j _ => ?_]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [← integral_const_mul]; congr 1; funext y; ring
    · exact ((hint _ (contDiff_thS k).continuous (isPer_thS k) j).const_mul
        (-(2 * π * k j))).congr (Eventually.of_forall fun y => by simp only; ring)
  have eS : ∫ y, ∑ j, G y j * ((2 * π * k j) * thC k (secT y)) =
      ∑ j, (2 * π * k j) * CG j := by
    rw [integral_finsetSum _ fun j _ => ?_]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [← integral_const_mul]; congr 1; funext y; ring
    · exact ((hint _ (contDiff_thC k).continuous (isPer_thC k) j).const_mul
        (2 * π * k j)).congr (Eventually.of_forall fun y => by simp only; ring)
  rw [eC] at hC
  rw [eS] at hS
  rw [mFourierCoeff_eq_theta hg, ← hC, ← hS]
  have : ∑ j, (-(2 * π * I * k j)) * ((CG j : ℂ) - I * (SG j : ℂ)) =
      4 * π ^ 2 * (∑ j, ((k j : ℂ)) ^ 2) * mFourierCoeff (fun y => (e y : ℂ)) k := by
    simp_rw [hGj]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : (I : ℂ) * I = -1 := I_mul_I
    linear_combination (-(4 * π ^ 2 * (k j : ℂ) ^ 2 * mFourierCoeff (fun y => (e y : ℂ)) k)) * this
  rw [← this]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hI : (I : ℂ) * I = -1 := I_mul_I
  linear_combination (-(2 * (π : ℂ) * (k j : ℂ) * (SG j : ℂ))) * hI

end SharpLSI
