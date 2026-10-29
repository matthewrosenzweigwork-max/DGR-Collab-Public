/- Actual uniform product-law Gaussian-scale MGF for bounded centered readouts.
Reuse: pinned Mathlib Hoeffding lemma and independent sub-Gaussian sum, Apache2.
This does not assume any particle quadratic exponential/UI bound. -/
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace DGRHS.CLT
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

theorem boundedProductLinearMGF (v : Lp ℝ 2 μ) (hv : (∫ x, v x ∂μ) = 0)
    (K : ℝ) (hK : ∀ᵐ x ∂μ, |v x| ≤ K) (t : ℝ) (N : ℕ) :
    Integrable (fun x : Fin N → S => Real.exp (t * ((Real.sqrt N)⁻¹*∑ i : Fin N, v (x i))))
      (Measure.pi (fun _ : Fin N => μ)) ∧
    (∫ x : Fin N → S, Real.exp (t * ((Real.sqrt N)⁻¹*∑ i : Fin N, v (x i)))
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
      Real.exp ((((‖K-(-K)‖₊/2)^2 : ℝ≥0) : ℝ)*t^2/2) := by
  classical
  let P := Measure.pi (fun _ : Fin N => μ)
  let X := fun (i : Fin N) (x : Fin N → S) => v (x i)
  let c : ℝ≥0 := (‖K-(-K)‖₊/2)^2
  let r : ℝ := (Real.sqrt N)⁻¹
  have hi : iIndepFun X P := iIndepFun_pi (fun _ => (Lp.memLp v).aemeasurable)
  have hg : ∀ i : Fin N, HasSubgaussianMGF (X i) c P := by
    intro i
    apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    · exact ((Lp.stronglyMeasurable v).measurable.comp (measurable_pi_apply i)).aemeasurable
    · filter_upwards [(measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae hK]
        with x hx
      exact abs_le.mp hx
    · rw [integral_comp_eval (Lp.stronglyMeasurable v).aestronglyMeasurable,hv]
  have hs := HasSubgaussianMGF.sum_of_iIndepFun hi (s := Finset.univ) (fun i _ => hg i)
  have hs' : HasSubgaussianMGF (fun x : Fin N → S => ∑ i : Fin N, X i x)
      ((N : ℝ≥0)*c) P := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hs
  have hr := hs'.const_mul r
  have hc : ((⟨r^2,sq_nonneg r⟩ : ℝ≥0)*((N : ℝ≥0)*c) : ℝ) ≤ c := by
    change r^2*((N : ℝ)*(c : ℝ)) ≤ c
    by_cases hz : N = 0
    · subst N
      simp only [Nat.cast_zero,mul_zero,zero_mul]
      exact c.coe_nonneg
    · have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hz
      have hsq : r^2*(N : ℝ) = 1 := by
        dsimp [r]
        rw [inv_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
        exact inv_mul_cancel₀ hn
      rw [← mul_assoc,hsq,one_mul]
  refine ⟨hr.integrable_exp_mul t, ?_⟩
  have hm := hr.mgf_le t
  exact hm.trans (Real.exp_le_exp.mpr
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sq_nonneg t)) (by norm_num)))
end DGRHS.CLT
#print axioms DGRHS.CLT.boundedProductLinearMGF
#check @DGRHS.CLT.boundedProductLinearMGF
