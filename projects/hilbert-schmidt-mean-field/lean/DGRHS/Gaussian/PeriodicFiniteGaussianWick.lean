import DGRHS.Gaussian.FiniteLaplace
import Mathlib.Probability.Moments.MGFAnalytic

/-! Actual finite independent Gaussian linearization primitives for the
periodic residual comparison. No favorable Gaussian field, MGF, partition
comparison or trace-class premise is supplied. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian

lemma periodic_stdGaussian_linear_exp (t : ℝ) :
    Integrable (fun z : ℝ => Real.exp (t*z)) (gaussianReal 0 1) ∧
    (∫ z : ℝ,Real.exp (t*z) ∂gaussianReal 0 1)=Real.exp (t^2/2) := by
  have hl : HasLaw (fun z : ℝ => z) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_id.aemeasurable,by simp⟩
  have he : mgf (fun z : ℝ => z) (gaussianReal 0 1) t=Real.exp (t^2/2) := by
    rw [mgf_gaussianReal hl]
    simp
  exact ⟨mgf_pos_iff.mp (he.symm ▸ Real.exp_pos _),he⟩

/-- Actual real Gaussian field on a finite Euclidean coordinate vector. -/
def periodicFiniteGaussianWick {α : Type*} [Fintype α] (t : ℝ) (q : α → ℝ)
    (z : α → ℝ) : ℝ :=
  Real.exp (t*(∑ i,q i*z i)-t^2/2*(∑ i,q i^2))

lemma periodic_finiteGaussian_linear_exp {α : Type*} [Fintype α] (q : α → ℝ) :
    Integrable (fun z : α → ℝ => Real.exp (∑ i,q i*z i)) (finiteStandardGaussian α) ∧
    (∫ z : α → ℝ,Real.exp (∑ i,q i*z i) ∂finiteStandardGaussian α) =
      Real.exp ((∑ i,q i^2)/2) := by
  have hf (i : α) := periodic_stdGaussian_linear_exp (q i)
  constructor
  · simp_rw [Real.exp_sum]
    exact Integrable.fintype_prod (fun i => (hf i).1)
  · simp_rw [Real.exp_sum]
    rw [finiteStandardGaussian,integral_fintype_prod_eq_prod
      (fun i (x : ℝ) => Real.exp (q i*x))]
    simp_rw [(hf _).2]
    rw [←Real.exp_sum]
    congr 1
    rw [Finset.sum_div]

/-- The genuine normal-ordered finite Gaussian exponential has mean one. -/
theorem periodicFiniteGaussianWick_mean_one {α : Type*} [Fintype α]
    (t : ℝ) (q : α → ℝ) :
    Integrable (periodicFiniteGaussianWick t q) (finiteStandardGaussian α) ∧
    (∫ z,periodicFiniteGaussianWick t q z ∂finiteStandardGaussian α)=1 := by
  have h := periodic_finiteGaussian_linear_exp (fun i => t*q i)
  have he (z : α → ℝ) : periodicFiniteGaussianWick t q z =
      Real.exp (-(t^2/2*(∑ i,q i^2)))*Real.exp (∑ i,(t*q i)*z i) := by
    unfold periodicFiniteGaussianWick
    rw [←Real.exp_add,Finset.mul_sum]
    congr 1
    simp only [mul_assoc]
    ring
  constructor
  · exact h.1.const_mul _ |>.congr (Filter.Eventually.of_forall fun z => (he z).symm)
  · simp_rw [he]
    rw [integral_const_mul,h.2,←Real.exp_add]
    rw [show ∑ i,(t*q i)^2=t^2*∑ i,q i^2 from by simp_rw [mul_pow];rw [Finset.mul_sum]]
    ring_nf
    exact Real.exp_zero

/-- Actual finite Gaussian product formula, including all empty index types. -/
theorem periodicFiniteGaussianWick_particle_integral {α γ : Type*} [Fintype α] [Fintype γ]
    (t : ℝ) (q : γ → α → ℝ) :
    Integrable (fun z : α → ℝ => ∏ j,periodicFiniteGaussianWick t (q j) z)
      (finiteStandardGaussian α) ∧
    (∫ z : α → ℝ,∏ j,periodicFiniteGaussianWick t (q j) z ∂finiteStandardGaussian α) =
      Real.exp (t^2/2*((∑ i,(∑ j,q j i)^2)-∑ j,∑ i,q j i^2)) := by
  have h := periodic_finiteGaussian_linear_exp (fun i => t*∑ j,q j i)
  have he (z : α → ℝ) : (∏ j,periodicFiniteGaussianWick t (q j) z) =
      Real.exp (-(t^2/2*(∑ j,∑ i,q j i^2)))*
        Real.exp (∑ i,(t*∑ j,q j i)*z i) := by
    unfold periodicFiniteGaussianWick
    rw [←Real.exp_sum,←Real.exp_add]
    congr 1
    simp_rw [Finset.sum_sub_distrib,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    ring
  constructor
  · exact h.1.const_mul _ |>.congr (Filter.Eventually.of_forall fun z => (he z).symm)
  · simp_rw [he]
    rw [integral_const_mul,h.2,←Real.exp_add]
    congr 1
    rw [show ∑ i,(t*∑ j,q j i)^2=t^2*∑ i,(∑ j,q j i)^2 from by simp_rw [mul_pow];rw [Finset.mul_sum]]
    ring

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_stdGaussian_linear_exp
#print axioms DGRHS.Periodic.periodic_finiteGaussian_linear_exp
#print axioms DGRHS.Periodic.periodicFiniteGaussianWick_mean_one
#print axioms DGRHS.Periodic.periodicFiniteGaussianWick_particle_integral
#check @DGRHS.Periodic.periodicFiniteGaussianWick_mean_one
#check @DGRHS.Periodic.periodicFiniteGaussianWick_particle_integral
