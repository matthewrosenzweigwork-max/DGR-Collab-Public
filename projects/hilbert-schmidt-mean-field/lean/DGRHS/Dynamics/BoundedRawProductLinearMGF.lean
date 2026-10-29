/- Native Mathlib Hoeffding and independent-sum reuse for the actual raw
bounded measurable observable, before any L2 representative is selected.
The interval width is unchanged by constant shifts; source dynamic(iii). -/
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Pi
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace DGRHS.Dynamics
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

theorem boundedRawProductLinearMGF (q : S→ℝ) (hq : Measurable q)
    (a b : ℝ) (hb : ∀ x,q x∈Set.Icc a b) (t : ℝ) (N : ℕ) :
    Integrable (fun x : Fin N→S=>Real.exp (t*((Real.sqrt N)⁻¹*∑ i : Fin N,(q (x i)-∫ y,q y ∂μ))))
      (Measure.pi (fun _ : Fin N=>μ)) ∧
    (∫ x : Fin N→S,Real.exp (t*((Real.sqrt N)⁻¹*∑ i : Fin N,(q (x i)-∫ y,q y ∂μ)))
      ∂Measure.pi (fun _ : Fin N=>μ))≤Real.exp ((((‖b-a‖₊/2)^2:ℝ≥0):ℝ)*t^2/2) := by
  classical
  let P := Measure.pi (fun _ : Fin N=>μ)
  let X := fun (i : Fin N) (x : Fin N→S)=>q (x i)-∫ y,q y ∂μ
  let c : ℝ≥0 := (‖b-a‖₊/2)^2
  let r : ℝ := (Real.sqrt N)⁻¹
  have hi : iIndepFun X P := iIndepFun_pi (fun _=>(hq.sub_const _).aemeasurable)
  have hg : ∀ i : Fin N,HasSubgaussianMGF (X i) c P := by
    intro i
    have hh := hasSubgaussianMGF_of_mem_Icc (μ:=P) (X:=fun x : Fin N→S=>q (x i))
      (hq.comp (measurable_pi_apply i)).aemeasurable
      (Filter.Eventually.of_forall fun x : Fin N→S=>hb (x i))
    rw [integral_comp_eval hq.aestronglyMeasurable] at hh
    exact hh
  have hs := HasSubgaussianMGF.sum_of_iIndepFun hi (s:=Finset.univ) (fun i _=>hg i)
  have hs' : HasSubgaussianMGF (fun x : Fin N→S=>∑ i : Fin N,X i x) ((N:ℝ≥0)*c) P := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hs
  have hr := hs'.const_mul r
  have hc : ((⟨r^2,sq_nonneg r⟩:ℝ≥0)*((N:ℝ≥0)*c):ℝ)≤c := by
    change r^2*((N:ℝ)*(c:ℝ))≤c
    by_cases hz : N=0
    · subst N
      simp only [Nat.cast_zero,mul_zero,zero_mul]
      exact c.coe_nonneg
    · have hn : (N:ℝ)≠0 := by exact_mod_cast hz
      have hsq : r^2*(N:ℝ)=1 := by
        dsimp [r]
        rw [inv_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
        exact inv_mul_cancel₀ hn
      rw [←mul_assoc,hsq,one_mul]
  refine ⟨hr.integrable_exp_mul t,?_⟩
  exact (hr.mgf_le t).trans (Real.exp_le_exp.mpr
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sq_nonneg t)) (by norm_num)))
end DGRHS.Dynamics
#check @DGRHS.Dynamics.boundedRawProductLinearMGF
#print axioms DGRHS.Dynamics.boundedRawProductLinearMGF
