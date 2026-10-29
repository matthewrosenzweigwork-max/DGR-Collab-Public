/- Original covariance norm comparison, from the SAME positive symmetric
operator and actual inverse. The full eigenbasis is derived for kernel operators. -/
import DGRHS.Kernel.MeanZeroDeterminant
import DGRHS.Gaussian.HilbertTiltedResolvent
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace DGRHS.Kernel
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma positive_resolvent_quadratic_bounds (T : H →L[ℝ] H)
    (hT : T.toLinearMap.IsSymmetric) (b : HilbertBasis ι ℝ H) (a : ι → ℝ)
    (he : ∀ i, T (b i) = a i • b i)
    (hpos : ∀ v, 0 ≤ inner ℝ v (T v)) (β : ℝ) (hβ : 0 ≤ β)
    (R : H →L[ℝ] H) (hR : ∀ v, R v+β • T (R v)=v) (v : H) :
    ‖v‖^2/(1+β*‖T‖) ≤ inner ℝ v (R v) ∧ inner ℝ v (R v) ≤ ‖v‖^2 := by
  have ha (i : ι) : 0 ≤ a i := by
    have hh := hpos (b i)
    simpa only [he,real_inner_smul_right,real_inner_self_eq_norm_sq,
      b.orthonormal.1 i,one_pow,mul_one] using hh
  have haT (i : ι) : a i ≤ ‖T‖ := by
    have hh := T.le_opNorm (b i)
    have hn : ‖a i‖ ≤ ‖T‖ := by
      simpa only [he,norm_smul,b.orthonormal.1 i,mul_one] using hh
    exact (le_abs_self _).trans hn
  have hm (i : ι) : 1 ≤ 1+β*a i := by nlinarith [mul_nonneg hβ (ha i)]
  have hM : 0 < 1+β*‖T‖ := by nlinarith [mul_nonneg hβ (norm_nonneg T)]
  have hRc (w : H) (i : ι) : b.repr (R w) i = (1+β*a i)⁻¹*b.repr w i := by
    have hh := congrArg (fun z => b.repr z i) (hR w)
    simp only [map_add,map_smul,lp.coeFn_add,lp.coeFn_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hh
    rw [repr_symmetric_eigenoperator T hT b a he] at hh
    have hn : 1+β*a i ≠ 0 := ne_of_gt (by linarith [hm i])
    apply (eq_inv_mul_iff_mul_eq₀ hn).mpr
    nlinarith [hh]
  have hsq := DGRHS.Gaussian.summable_basis_coeff_sq b v
  have hParseval : (∑' i, (b.repr v i)^2)=‖v‖^2 := by
    simpa only [b.repr_apply_apply,pow_two,real_inner_comm,real_inner_self_eq_norm_sq] using
      b.tsum_inner_mul_inner v v
  have hup (i : ι) : (b.repr v i)^2/(1+β*a i) ≤ (b.repr v i)^2 := by
    exact div_le_self (sq_nonneg _) (hm i)
  have hs : Summable (fun i => (b.repr v i)^2/(1+β*a i)) :=
    Summable.of_nonneg_of_le (fun i => div_nonneg (sq_nonneg _) (by linarith [hm i])) hup hsq
  have hlo (i : ι) : (b.repr v i)^2/(1+β*‖T‖) ≤ (b.repr v i)^2/(1+β*a i) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by linarith [hm i])
      (by nlinarith [mul_le_mul_of_nonneg_left (haT i) hβ])
  rw [←DGRHS.Gaussian.tilted_basis_coeff_tsum_eq_inner b β a R hRc v,←hParseval]
  constructor
  · rw [←tsum_div_const]
    exact Summable.tsum_le_tsum hlo (hsq.div_const _) hs
  · exact Summable.tsum_le_tsum hup hs hsq

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

theorem meanZero_kernel_resolvent_quadratic_bounds [MeasurableSpace.CountablyGenerated S]
    (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap=h p) (hc : ∀ᵐ x ∂μ, (∫ y,h (x,y) ∂μ)=0)
    (hp : ∀ v : Lp ℝ 2 μ, 0 ≤ inner ℝ v (integralOperator h hh v))
    (β : ℝ) (hβ : 0 ≤ β) (R : meanZeroL2 μ →L[ℝ] meanZeroL2 μ)
    (hR : ∀ v, R v+β • integralOperatorOnMeanZero h hh hs hc (R v)=v)
    (v : meanZeroL2 μ) :
    ‖v‖^2/(1+β*‖integralOperatorOnMeanZero h hh hs hc‖) ≤ inner ℝ v (R v) ∧
      inner ℝ v (R v) ≤ ‖v‖^2 := by
  obtain ⟨κ,a,b,_,he⟩ := exists_integralOperatorOnMeanZero_eigenbasis h hh hs hc
  exact positive_resolvent_quadratic_bounds _ (integralOperatorOnMeanZero_isSymmetric h hh hs hc)
    b a he (fun w => hp w) β hβ R hR v

end DGRHS.Kernel
#check @DGRHS.Kernel.positive_resolvent_quadratic_bounds
#check @DGRHS.Kernel.meanZero_kernel_resolvent_quadratic_bounds
#print axioms DGRHS.Kernel.positive_resolvent_quadratic_bounds
#print axioms DGRHS.Kernel.meanZero_kernel_resolvent_quadratic_bounds
