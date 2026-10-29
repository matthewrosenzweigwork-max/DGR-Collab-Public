import DGRHS.Gaussian.PeriodicScalarPoisson
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Absolute product-series identities from native Fubini on the actual
counting product law, and the native Gaussian rapid-decay estimates. -/
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι]

lemma periodicCount_pi :
    Measure.pi (fun _ : ι => (Measure.count : Measure ℤ)) =
      (Measure.count : Measure (ι → ℤ)) := by
  apply Measure.ext_of_singleton
  intro k
  simp

lemma periodic_integral_count_eq_tsum {α : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (f : α → ℂ)
    (hf : Integrable f Measure.count) :
    (∫ x,f x ∂Measure.count) = ∑' x,f x := by
  simpa using integral_countable hf

lemma periodic_product_series_summable (f : ι → ℤ → ℂ)
    (hf : ∀ i,Summable (fun n => ‖f i n‖)) :
    Summable (fun k : ι → ℤ => ‖∏ i,f i (k i)‖) := by
  have hi : ∀ i,Integrable (f i) Measure.count := fun i => integrable_count_iff.mpr (hf i)
  have h := Integrable.fintype_prod hi
  rw [periodicCount_pi] at h
  exact integrable_count_iff.mp h

lemma periodic_product_series_eq (f : ι → ℤ → ℂ)
    (hf : ∀ i,Summable (fun n => ‖f i n‖)) :
    (∑' k : ι → ℤ,∏ i,f i (k i)) = ∏ i,∑' n : ℤ,f i n := by
  have hi : ∀ i,Integrable (f i) Measure.count := fun i => integrable_count_iff.mpr (hf i)
  have hp : Integrable (fun k : ι → ℤ => ∏ i,f i (k i)) Measure.count := by
    rw [← periodicCount_pi]
    exact Integrable.fintype_prod hi
  rw [← periodic_integral_count_eq_tsum _ hp,← periodicCount_pi,
    integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro i hi'
  exact periodic_integral_count_eq_tsum _ (hi i)

lemma periodicScalarGaussian_summable_norm (a : ℝ) (ha : 0<a) (x : ℝ) :
    Summable (fun n : ℤ => ‖Complex.exp (-(Real.pi:ℂ)*a*(x+n)^2)‖) := by
  have hc : (-(Real.pi:ℂ)*a).re < 0 := by simpa using neg_neg_of_pos (mul_pos Real.pi_pos ha)
  have h := (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact hc
    (-2*(Real.pi:ℂ)*a*x) (-2)).isBigO.const_mul_left
      (Complex.exp (-(Real.pi:ℂ)*a*x^2))
  have hs : Summable (fun n : ℤ =>
      Complex.exp (-(Real.pi:ℂ)*a*x^2)*
      Complex.exp (-(Real.pi:ℂ)*a*(n:ℂ)^2+(-2*(Real.pi:ℂ)*a*x)*(n:ℂ))) := by
    convert summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1:ℝ)<2))
      (h.comp_tendsto Int.tendsto_coe_cofinite) using 1
    simp [Function.comp_def]
  apply hs.norm.congr
  intro n
  congr 1
  rw [← Complex.exp_add]
  congr 1
  ring

lemma periodicScalarFourierGaussian_summable_norm (a : ℝ) (ha : 0<a) (x : UnitAddCircle) :
    Summable (fun n : ℤ => ‖Complex.exp (-(Real.pi:ℂ)*a*(n:ℂ)^2)*fourier n x‖) := by
  have h := periodicScalarGaussian_summable_norm a ha 0
  simpa only [Complex.ofReal_zero,zero_add,norm_mul,fourier_apply,Circle.norm_coe,mul_one] using h

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicCount_pi
#print axioms DGRHS.Periodic.periodic_product_series_summable
#print axioms DGRHS.Periodic.periodic_product_series_eq
#print axioms DGRHS.Periodic.periodicScalarGaussian_summable_norm
#print axioms DGRHS.Periodic.periodicScalarFourierGaussian_summable_norm
