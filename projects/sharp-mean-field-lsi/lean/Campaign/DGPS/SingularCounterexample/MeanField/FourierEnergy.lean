import DGPS.SingularCounterexample.Interfaces
import DGPS.SingularCounterexample.MeanField.Definitions

/-!
# Fourier identities for singular mean-field energies
-/

open MeasureTheory
open scoped ComplexConjugate

namespace DGPS.SingularCounterexample

open Examples.PositiveH1.Nonlinear
open Examples.PositiveH1.Fourier (fourierCoeff_eq_integral)

private theorem mFourier_add_argument (n : Fin 1 → ℤ) (x y : Circle) :
    UnitAddTorus.mFourier n (x + y) =
      UnitAddTorus.mFourier n x * UnitAddTorus.mFourier n y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply,
    fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul,
    Finset.prod_mul_distrib]

/-- Fourier transforms turn Haar convolution of integrable circle functions into products. -/
theorem fourierCoeff_conv_integrable {k f : Circle → ℝ}
    (hk : Integrable k (haar 1)) (hf : Integrable f (haar 1)) (n : Fin 1 → ℤ) :
    fourierCoeff (conv k f) n = fourierCoeff k n * fourierCoeff f n := by
  let χ : Circle → ℂ := UnitAddTorus.mFourier (-n)
  have hχ (x y : Circle) : χ x = χ y * χ (x - y) := by
    rw [← mFourier_add_argument]
    congr 1
    abel
  have htwist (x : Circle) :
      χ x * (conv k f x : ℂ) =
        convolution (fun y => χ y * (k y : ℂ))
          (fun y => χ y * (f y : ℂ)) (ContinuousLinearMap.mul ℂ ℂ) (haar 1) x := by
    change χ x * ((∫ y, k y * f (x - y) ∂haar 1 : ℝ) : ℂ) =
      ∫ y, (χ y * (k y : ℂ)) * (χ (x - y) * (f (x - y) : ℂ)) ∂haar 1
    rw [← integral_complex_ofReal, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [Complex.ofReal_mul, hχ x y]
    ring
  simp only [fourierCoeff_eq_integral]
  change (∫ x, χ x * (conv k f x : ℂ) ∂haar 1) =
    (∫ x, χ x * (k x : ℂ) ∂haar 1) * ∫ x, χ x * (f x : ℂ) ∂haar 1
  simp_rw [htwist]
  exact integral_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_mFourier_mul hk (-n)) (integrable_mFourier_mul hf (-n))

/-- SLC-M011: the coefficient identity for an `L¹` kernel and an `L²` function. -/
theorem coeff1_conv {k f : Circle → ℝ}
    (hk : Integrable k (haar 1)) (hf : MemLp f 2 (haar 1)) (n : ℤ) :
    coeff1 (conv k f) n = coeff1 k n * coeff1 f n :=
  fourierCoeff_conv_integrable hk (hf.integrable one_le_two) (freqZ n)

/-- SLC-M012: the weak density derivative identity at every integer frequency. -/
theorem coeff1_densityDeriv (ρ : AbsoluteDensity 1) (n : ℤ) :
    coeff1 (densityDeriv ρ) n =
      2 * Real.pi * Complex.I * (n : ℂ) * coeff1 ρ.density n := by
  have h := fourierCoeff_weakGradient (density_regular ρ).2.2 0 (freqZ n)
  have hf : (fun y => ((2 * ρ.sqrt y) • weakGradient ρ.sqrt ρ.sqrt_mem y) 0) =
      densityDeriv ρ := by
    funext y
    rfl
  rw [hf] at h
  exact h

/-- Parseval's product identity, reindexed by all integer circle frequencies. -/
theorem hasSum_coeff1_product {a b : Circle → ℝ}
    (ha : MemLp a 2 (haar 1)) (hb : MemLp b 2 (haar 1)) :
    HasSum (fun n : ℤ => (conj (coeff1 a n) * coeff1 b n).re)
      (∫ x, a x * b x ∂haar 1) := by
  have h := RCLike.hasSum_re ℂ (SharpLSI.hasSum_prod_cf_real ha hb)
  have h' := (Equiv.funUnique (Fin 1) ℤ).symm.hasSum_iff.mpr h
  exact h'

/-- The zero Fourier coefficient is the Haar integral. -/
theorem coeff1_zero (f : Circle → ℝ) : coeff1 f 0 = (∫ x, f x ∂haar 1 : ℝ) := by
  change fourierCoeff f (0 : Fin 1 → ℤ) = _
  rw [fourierCoeff_eq_integral]
  simp only [neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_mul]
  exact integral_complex_ofReal

/-- The real convolution pairing is the sum of the kernel coefficients times squared
Fourier norms. This also applies to nonsymmetric real kernels by taking real parts. -/
theorem hasSum_conv_energy {k f : Circle → ℝ}
    (hk : MemLp k 2 (haar 1)) (hf : MemLp f 2 (haar 1)) :
    HasSum (fun n : ℤ => (coeff1 k n).re * ‖coeff1 f n‖ ^ 2)
      (∫ x, f x * conv k f x ∂haar 1) := by
  have hc : MemLp (conv k f) 2 (haar 1) :=
    memLp_of_cont (conv_continuous_L2 hk hf) 2
  refine (hasSum_coeff1_product hf hc).congr_fun ?_
  intro n
  rw [coeff1_conv (hk.integrable one_le_two) hf]
  rw [show conj (coeff1 f n) * (coeff1 k n * coeff1 f n) =
      coeff1 k n * (coeff1 f n * conj (coeff1 f n)) by ring]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

private theorem haar_interaction_eq (k : Circle → ℝ) :
    (∫ x, (1 : ℝ) * conv k (fun _ => 1) x ∂haar 1) = (coeff1 k 0).re := by
  rw [coeff1_zero]
  simp [conv, Examples.PositiveH1.Nonlinear.conv]

/-- SLC-M013: subtracting the Haar energy removes exactly the zero Fourier mode. -/
theorem hasSum_interactionGap {k : Circle → ℝ}
    (hk : MemLp k 2 (haar 1)) (ρ : AbsoluteDensity 1) :
    HasSum (fun n : ℤ => if n = 0 then 0 else
        (coeff1 k n).re * ‖coeff1 ρ.density n‖ ^ 2) (interactionGap k ρ) := by
  have hρ0 : coeff1 ρ.density 0 = 1 := by
    rw [coeff1_zero, ρ.integral_density]
    norm_num
  have h := (hasSum_conv_energy hk (memLp_density_two ρ)).sub
    (hasSum_ite_eq (0 : ℤ) (coeff1 k 0).re)
  rw [interactionGap, haar_interaction_eq]
  refine h.congr_fun ?_
  intro n
  by_cases hn : n = 0
  · subst n
    simp [hρ0]
  · simp [hn]

theorem interactionGap_eq_tsum {k : Circle → ℝ}
    (hk : MemLp k 2 (haar 1)) (ρ : AbsoluteDensity 1) :
    interactionGap k ρ = ∑' n : ℤ, if n = 0 then 0 else
      (coeff1 k n).re * ‖coeff1 ρ.density n‖ ^ 2 :=
  (hasSum_interactionGap hk ρ).tsum_eq.symm

/-- SLC-M014: the density-derivative pairing has the Fourier multiplier `(2πn)²`.
The zero mode vanishes identically. -/
theorem hasSum_crossEnergy {k : Circle → ℝ}
    (hk : MemLp k 2 (haar 1)) (ρ : AbsoluteDensity 1) :
    HasSum (fun n : ℤ => (2 * Real.pi * (n : ℝ)) ^ 2 *
        (coeff1 k n).re * ‖coeff1 ρ.density n‖ ^ 2)
      (∫ x, densityDeriv ρ x * conv k (densityDeriv ρ) x ∂haar 1) := by
  refine (hasSum_conv_energy hk (memLp_densityDeriv ρ)).congr_fun ?_
  intro n
  have hn := SharpLSI.norm_grad_coeff_sq (freqZ n) 0 (coeff1 ρ.density n)
  change ‖2 * Real.pi * Complex.I * (n : ℂ) * coeff1 ρ.density n‖ ^ 2 =
    4 * Real.pi ^ 2 * (n : ℝ) ^ 2 * ‖coeff1 ρ.density n‖ ^ 2 at hn
  rw [coeff1_densityDeriv, hn]
  ring

theorem crossEnergy_eq_tsum {k : Circle → ℝ}
    (hk : MemLp k 2 (haar 1)) (ρ : AbsoluteDensity 1) :
    (∫ x, densityDeriv ρ x * conv k (densityDeriv ρ) x ∂haar 1) =
      ∑' n : ℤ, (2 * Real.pi * (n : ℝ)) ^ 2 *
        (coeff1 k n).re * ‖coeff1 ρ.density n‖ ^ 2 :=
  (hasSum_crossEnergy hk ρ).tsum_eq.symm

end DGPS.SingularCounterexample
