/- Proper mixed exponential control for the source bounded-test MGF clause.
The product linear factor is derived from the native Hoeffding estimate;
the actual doubled particle-weight moment remains a physical obligation. -/
import DGRHS.CLT.CanonicalPartitionComparison
import DGRHS.CLT.BoundedProductLinearMGF
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace DGRHS.CLT

lemma exponential_sum_integral_cs {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] (X Y : Ω → ℝ)
    (hX : AEMeasurable X ν) (hY : AEMeasurable Y ν)
    (hx : Integrable (fun x => Real.exp (2*X x)) ν)
    (hy : Integrable (fun x => Real.exp (2*Y x)) ν) :
    Integrable (fun x => Real.exp (X x+Y x)) ν ∧
    (∫ x, Real.exp (X x+Y x) ∂ν) ≤
      Real.sqrt (∫ x, Real.exp (2*X x) ∂ν)*Real.sqrt (∫ x, Real.exp (2*Y x) ∂ν) := by
  have hXL := memLp_exp_of_integrable_double X hX hx
  have hYL := memLp_exp_of_integrable_double Y hY hy
  have hProd := hXL.integrable_mul hYL
  change Integrable (fun x => Real.exp (X x)*Real.exp (Y x)) ν at hProd
  refine ⟨?_,?_⟩
  · simpa only [Real.exp_add] using hProd
  · simp_rw [Real.exp_add]
    exact (integral_mul_le_toLp_norms hXL hYL).trans_eq (by
      rw [toLp_norm_eq_sqrt_second_moment hXL,toLp_norm_eq_sqrt_second_moment hYL]
      simp_rw [←Real.exp_nat_mul]
      norm_num)

theorem bounded_linear_weight_exponential_bound {S : Type*} [MeasurableSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ]
    (v : Lp ℝ 2 μ) (hv : (∫ x,v x ∂μ) = 0)
    (K : ℝ) (hK : ∀ᵐ x ∂μ, |v x| ≤ K)
    (Y : ∀ N : ℕ, (Fin N → S) → ℝ)
    (hY : ∀ N, AEMeasurable (Y N) (Measure.pi (fun _ : Fin N => μ)))
    (p C : ℝ)
    (hi : ∀ N, Integrable (fun x : Fin N → S => Real.exp ((2*p)*Y N x))
      (Measure.pi (fun _ : Fin N => μ)))
    (hb : ∀ N, (∫ x : Fin N → S, Real.exp ((2*p)*Y N x)
      ∂Measure.pi (fun _ : Fin N => μ)) ≤ C) :
    ∀ N, Integrable (fun x : Fin N → S => Real.exp
      (p*((Real.sqrt N)⁻¹*∑ i : Fin N,v (x i)+Y N x)))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → S, Real.exp
        (p*((Real.sqrt N)⁻¹*∑ i : Fin N,v (x i)+Y N x))
          ∂Measure.pi (fun _ : Fin N => μ)) ≤
        Real.sqrt (Real.exp ((((‖K-(-K)‖₊/2)^2 : ℝ≥0) : ℝ)*(2*p)^2/2))*Real.sqrt C := by
  intro N
  let A := fun x : Fin N → S => (Real.sqrt N)⁻¹*∑ i : Fin N,v (x i)
  have hA : Measurable A := by
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    exact (Lp.stronglyMeasurable v).measurable.comp (measurable_pi_apply i)
  obtain ⟨hLin,hLinBound⟩ := boundedProductLinearMGF v hv K hK (2*p) N
  have hDoubleLin : Integrable (fun x => Real.exp (2*(p*A x)))
      (Measure.pi (fun _ : Fin N => μ)) := by
    convert hLin using 1 <;> funext x <;> congr 1 <;> dsimp [A] <;> ring
  have hDoubleY : Integrable (fun x => Real.exp (2*(p*Y N x)))
      (Measure.pi (fun _ : Fin N => μ)) := by
    simpa only [mul_assoc] using hi N
  obtain ⟨hProper,hBound⟩ := exponential_sum_integral_cs
    (fun x => p*A x) (fun x => p*Y N x)
    (hA.aemeasurable.const_mul p) ((hY N).const_mul p) hDoubleLin hDoubleY
  have he : (fun x : Fin N → S => Real.exp (p*(A x+Y N x))) =
      fun x => Real.exp (p*A x+p*Y N x) := by funext x; congr 1; ring
  refine ⟨?_,?_⟩
  · change Integrable (fun x => Real.exp (p*(A x+Y N x))) _
    rw [he]
    exact hProper
  · change (∫ x,Real.exp (p*(A x+Y N x)) ∂Measure.pi (fun _ : Fin N => μ)) ≤ _
    rw [he]
    apply hBound.trans
    have hLinBound' : (∫ x,Real.exp (2*(p*A x)) ∂Measure.pi (fun _ : Fin N => μ)) ≤
        Real.exp ((((‖K-(-K)‖₊/2)^2 : ℝ≥0) : ℝ)*(2*p)^2/2) := by
      convert hLinBound using 1 <;> congr 1 <;> funext x <;> congr 1 <;> dsimp [A] <;> ring
    have hYBound : (∫ x,Real.exp (2*(p*Y N x)) ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
      simpa only [mul_assoc] using hb N
    exact mul_le_mul (Real.sqrt_le_sqrt hLinBound') (Real.sqrt_le_sqrt hYBound)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
end DGRHS.CLT
#print axioms DGRHS.CLT.exponential_sum_integral_cs
#print axioms DGRHS.CLT.bounded_linear_weight_exponential_bound
#check @DGRHS.CLT.bounded_linear_weight_exponential_bound
