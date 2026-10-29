import DGRHS.Gaussian.PeriodicGaussianProductSeries

/-! Exact multidimensional Gaussian periodization by tensorizing the native
one-dimensional Poisson formula. All series are absolutely summable; no
formal interchange or asserted torus heat law is used. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι]

lemma periodicGaussian_norm_factor (b : ℂ) (x : EuclideanSpace ℝ ι) :
    Complex.exp (b*(‖x‖:ℂ)^2) = ∏ i,Complex.exp (b*(x i:ℂ)^2) := by
  rw [← Complex.ofReal_pow,EuclideanSpace.real_norm_sq_eq,Complex.ofReal_sum,Finset.mul_sum,
    Complex.exp_sum]
  simp only [Complex.ofReal_pow]

lemma periodicGaussian_shift_factor (a : ℝ) (x : EuclideanSpace ℝ ι) (k : PeriodicFrequency ι) :
    Complex.exp (-(Real.pi:ℂ)*a*(‖x+periodicFrequencyVector k‖:ℂ)^2) =
      ∏ i,Complex.exp (-(Real.pi:ℂ)*a*((x i:ℂ)+(k i:ℂ))^2) := by
  rw [periodicGaussian_norm_factor]
  simp only [PiLp.add_apply,periodicFrequencyVector_apply,Complex.ofReal_add,Complex.ofReal_intCast]

lemma periodicGaussian_frequency_factor (a : ℝ) (k : PeriodicFrequency ι) (x : PeriodicTorus ι) :
    Complex.exp (-(Real.pi:ℂ)/a*(‖periodicFrequencyVector k‖:ℂ)^2)*
      UnitAddTorus.mFourier k x =
      ∏ i,Complex.exp (-(Real.pi:ℂ)/a*(k i:ℂ)^2)*fourier (k i) (x i) := by
  rw [periodicGaussian_norm_factor]
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,periodicFrequencyVector_apply,
    Complex.ofReal_intCast,Finset.prod_mul_distrib]

lemma periodicGaussian_frequency_factor_summable (a : ℝ) (ha : 0<a) (x : UnitAddCircle) :
    Summable (fun n : ℤ => ‖Complex.exp (-(Real.pi:ℂ)/a*(n:ℂ)^2)*fourier n x‖) := by
  simpa only [Complex.ofReal_inv,div_eq_mul_inv] using
    periodicScalarFourierGaussian_summable_norm a⁻¹ (inv_pos.mpr ha) x

lemma periodicGaussian_spatial_series_summable (a : ℝ) (ha : 0<a) (x : EuclideanSpace ℝ ι) :
    Summable (fun k : PeriodicFrequency ι =>
      ‖Complex.exp (-(Real.pi:ℂ)*a*(‖x+periodicFrequencyVector k‖:ℂ)^2)‖) := by
  simp only [periodicGaussian_shift_factor]
  exact periodic_product_series_summable (fun i (n : ℤ) =>
    Complex.exp (-(Real.pi:ℂ)*a*((x i:ℂ)+(n:ℂ))^2))
    (fun i => periodicScalarGaussian_summable_norm a ha (x i))

lemma periodicGaussian_spectral_series_summable (a : ℝ) (ha : 0<a) (x : PeriodicTorus ι) :
    Summable (fun k : PeriodicFrequency ι =>
      ‖Complex.exp (-(Real.pi:ℂ)/a*(‖periodicFrequencyVector k‖:ℂ)^2)*
        UnitAddTorus.mFourier k x‖) := by
  simp only [periodicGaussian_frequency_factor]
  exact periodic_product_series_summable (fun i (n : ℤ) =>
    Complex.exp (-(Real.pi:ℂ)/a*(n:ℂ)^2)*fourier n (x i))
    (fun i => periodicGaussian_frequency_factor_summable a ha (x i))

/-- Actual Euclidean lattice periodization equals the torus Fourier Gaussian
at every point, in every finite dimension, with the exact Gaussian constant. -/
theorem periodicMultidimensionalGaussian_poisson (a : ℝ) (ha : 0<a)
    (x : EuclideanSpace ℝ ι) :
    (∑' k : PeriodicFrequency ι,Complex.exp (-(Real.pi:ℂ)*a*(‖x+periodicFrequencyVector k‖:ℂ)^2)) =
      (1/(a:ℂ)^(1/2:ℂ))^(Fintype.card ι) *
        ∑' k : PeriodicFrequency ι,Complex.exp (-(Real.pi:ℂ)/a*(‖periodicFrequencyVector k‖:ℂ)^2)*
          UnitAddTorus.mFourier k (fun i => (x i : UnitAddCircle)) := by
  simp only [periodicGaussian_shift_factor,periodicGaussian_frequency_factor]
  rw [periodic_product_series_eq _ (fun i => periodicScalarGaussian_summable_norm a ha (x i)),
    periodic_product_series_eq _ (fun i => periodicGaussian_frequency_factor_summable a ha (x i : UnitAddCircle))]
  simp only [periodicScalarGaussian_poisson a ha,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicGaussian_norm_factor
#print axioms DGRHS.Periodic.periodicGaussian_spatial_series_summable
#print axioms DGRHS.Periodic.periodicGaussian_spectral_series_summable
#print axioms DGRHS.Periodic.periodicMultidimensionalGaussian_poisson
#check @DGRHS.Periodic.periodicMultidimensionalGaussian_poisson
