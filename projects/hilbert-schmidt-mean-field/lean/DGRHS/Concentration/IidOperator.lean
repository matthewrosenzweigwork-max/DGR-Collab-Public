import DGRHS.Concentration.ExtendedRateTail
import DGRHS.Kernel.Operator

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
namespace DGRHS.Concentration

lemma finite_l2_tuple_sum_norm_le {n : ℕ} {E : Fin n → Type*}
    [∀ i, NormedAddCommGroup (E i)] (f : PiLp 2 E) :
    (∑ i, ‖f i‖) ≤ Real.sqrt (n : ℝ)*‖f‖ := by
  let R : PiLp 2 (fun _ : Fin n ↦ ℝ) := WithLp.toLp 2 (fun i ↦ ‖f i‖)
  let O : PiLp 2 (fun _ : Fin n ↦ ℝ) := WithLp.toLp 2 (fun _ ↦ 1)
  have hRsq : ‖R‖^2 = ‖f‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    change (∑ i, ‖(‖f i‖ : ℝ)‖^2) = ∑ i, ‖f i‖^2
    simp only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have hR : ‖R‖ = ‖f‖ := by nlinarith [norm_nonneg R,norm_nonneg f]
  have hOsq : ‖O‖^2 = (n : ℝ) := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [O]
  have hO : ‖O‖ = Real.sqrt (n : ℝ) := by
    nlinarith [norm_nonneg O,Real.sqrt_nonneg (n : ℝ),Real.sq_sqrt (show (0 : ℝ) ≤ n from Nat.cast_nonneg _)]
  have he : inner ℝ R O = ∑ i, ‖f i‖ := by simp [PiLp.inner_apply,R,O]
  have hc := abs_real_inner_le_norm R O
  rw [he,abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ norm_nonneg _),hR,hO] at hc
  simpa only [mul_comm] using hc

lemma iid_bilinear_operator_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (h : Ω × Ω → ℝ)
    (hh : MemLp h 2 (μ.prod μ))
    (f g : PiLp 2 (fun _ : Fin n ↦ Lp ℝ 2 μ)) (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1) :
    kernelL2Bilinear (fun _ : Fin n ↦ μ) (fun _ : Fin n ↦ μ)
      (iidOffDiagonalKernel n h) f g ≤ (n : ℝ)*‖DGRHS.Kernel.integralOperator h hh‖ := by
  let T := DGRHS.Kernel.integralOperator h hh
  have hPair : ∀ i j, (∫ p, iidOffDiagonalKernel n h i j p * f i p.1 * g j p.2 ∂μ.prod μ) ≤
      ‖T‖*‖f i‖*‖g j‖ := by
    intro i j
    by_cases hij : i ≠ j
    · simp only [iidOffDiagonalKernel,ite_eq_left hij]
      rw [← DGRHS.Kernel.inner_integralOperator h hh (g j) (f i)]
      exact (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans (by
        calc
          ‖T (g j)‖*‖f i‖ ≤ (‖T‖*‖g j‖)*‖f i‖ :=
            mul_le_mul_of_nonneg_right (T.le_opNorm (g j)) (norm_nonneg _)
          _ = ‖T‖*‖f i‖*‖g j‖ := by ring))
    · simp only [iidOffDiagonalKernel,ite_eq_right hij,zero_mul,integral_zero]
      positivity
  have hF : (∑ i, ‖f i‖) ≤ Real.sqrt (n : ℝ) :=
    (finite_l2_tuple_sum_norm_le f).trans (by simpa using mul_le_mul_of_nonneg_left hf (Real.sqrt_nonneg _))
  have hG : (∑ j, ‖g j‖) ≤ Real.sqrt (n : ℝ) :=
    (finite_l2_tuple_sum_norm_le g).trans (by simpa using mul_le_mul_of_nonneg_left hg (Real.sqrt_nonneg _))
  calc
    _ ≤ ∑ i, ∑ j, ‖T‖*‖f i‖*‖g j‖ :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hPair i j
    _ = ∑ i, (‖T‖*‖f i‖)*(∑ j, ‖g j‖) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = (∑ i, ‖T‖*‖f i‖)*(∑ j, ‖g j‖) := by rw [Finset.sum_mul]
    _ = ‖T‖*(∑ i, ‖f i‖)*(∑ j, ‖g j‖) := by rw [← Finset.mul_sum]
    _ ≤ ‖T‖*Real.sqrt (n : ℝ)*Real.sqrt (n : ℝ) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul hF hG (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
          (Real.sqrt_nonneg _)) (norm_nonneg T)
    _ = (n : ℝ)*‖T‖ := by
      calc
        _ = ‖T‖*(Real.sqrt (n : ℝ))^2 := by ring
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]; ring

/-- The genuine full finite bilinear supremum is controlled by the exact accepted
source integral operator, without assuming its D-test conclusion. -/
theorem iidSourceD_le_integralOperator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (h : Ω × Ω → ℝ)
    (hh : MemLp h 2 (μ.prod μ)) :
    iidSourceD μ n h ≤ (n : ℝ)*‖DGRHS.Kernel.integralOperator h hh‖ := by
  apply csSup_le ⟨0,kernelDTestValues_zero (fun _ : Fin n ↦ μ) (fun _ : Fin n ↦ μ) (iidOffDiagonalKernel n h)⟩
  rintro z ⟨f,g,hf,hg,rfl⟩
  exact iid_bilinear_operator_bound μ n h hh f g hf hg

#print axioms DGRHS.Concentration.finite_l2_tuple_sum_norm_le
#print axioms DGRHS.Concentration.iidSourceD_le_integralOperator
#check @DGRHS.Concentration.iidSourceD_le_integralOperator
end DGRHS.Concentration
