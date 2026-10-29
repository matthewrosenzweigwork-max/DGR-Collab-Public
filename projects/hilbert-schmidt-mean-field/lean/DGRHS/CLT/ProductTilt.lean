/- Actual finite product of proper one-body exponential tilts. This derives
its density and normalization; no product-density identity is an input. -/
import DGRHS.CLT.ConstantTilt
import Mathlib.MeasureTheory.Integral.Pi
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace DGRHS.CLT
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [SigmaFinite μ]

lemma integrable_exp_sum_coordinates (f : S → ℝ)
    (hf : Integrable (fun x => Real.exp (f x)) μ) (N : ℕ) :
    Integrable (fun x : Fin N → S => Real.exp (∑ i, f (x i)))
      (Measure.pi (fun _ : Fin N => μ)) := by
  simpa only [Real.exp_sum] using Integrable.fintype_prod (fun _ : Fin N => hf)

lemma integral_exp_sum_coordinates (f : S → ℝ) (N : ℕ) :
    (∫ x : Fin N → S, Real.exp (∑ i, f (x i)) ∂Measure.pi (fun _ : Fin N => μ))=
      (∫ x, Real.exp (f x) ∂μ)^N := by
  simp only [Real.exp_sum]
  simpa only [Fintype.card_fin] using integral_fintype_prod_eq_pow (ι := Fin N) (μ := μ) (fun y => Real.exp (f y))

lemma measure_pi_tilted [NeZero μ] (f : S → ℝ)
    (hf : Integrable (fun x => Real.exp (f x)) μ) (N : ℕ) :
    Measure.pi (fun _ : Fin N => μ.tilted f)=
      (Measure.pi (fun _ : Fin N => μ)).tilted (fun x => ∑ i, f (x i)) := by
  classical
  letI := isProbabilityMeasure_tilted hf
  apply Measure.pi_eq
  intro s hs
  rw [tilted_apply_eq_ofReal_integral' _ (MeasurableSet.univ_pi hs)]
  rw [integral_exp_sum_coordinates (μ := μ) f N]
  simp only [Real.exp_sum]
  rw [Measure.restrict_pi_pi]
  rw [show (∫ x : Fin N → S, (∏ i, Real.exp (f (x i))) /
      (∫ x, Real.exp (f x) ∂μ)^N ∂Measure.pi (fun i => μ.restrict (s i)))=
      ∏ i : Fin N, ∫ x, Real.exp (f x)/(∫ x, Real.exp (f x) ∂μ) ∂μ.restrict (s i) by
    have he (x : Fin N → S) : (∏ i, Real.exp (f (x i)))/(∫ x, Real.exp (f x) ∂μ)^N =
        ∏ i : Fin N, Real.exp (f (x i))/(∫ x, Real.exp (f x) ∂μ) := by
      rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    simp_rw [he]
    exact integral_fintype_prod_eq_prod (μ := fun i : Fin N => μ.restrict (s i))
      (fun _ x => Real.exp (f x)/(∫ x, Real.exp (f x) ∂μ))]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x => div_nonneg
    (Real.exp_pos _).le (integral_nonneg (fun y => (Real.exp_pos _).le))))]
  apply Finset.prod_congr rfl
  intro i _
  exact (tilted_apply_eq_ofReal_integral' f (hs i)).symm
end DGRHS.CLT
#check @DGRHS.CLT.integrable_exp_sum_coordinates
#check @DGRHS.CLT.integral_exp_sum_coordinates
#check @DGRHS.CLT.measure_pi_tilted
#print axioms DGRHS.CLT.integrable_exp_sum_coordinates
#print axioms DGRHS.CLT.integral_exp_sum_coordinates
#print axioms DGRHS.CLT.measure_pi_tilted
