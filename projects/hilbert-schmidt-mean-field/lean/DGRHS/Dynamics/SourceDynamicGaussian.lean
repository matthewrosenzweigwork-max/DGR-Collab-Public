import DGRHS.Dynamics.SourceDynamicCovarianceTime
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-! Genuine finite Gaussian target for the original dynamic covariance.
The static second moments and actual stopped-gradient time covariance give
positivity. Native multivariateGaussian supplies the law, its proper moments
and its characteristic function; no favorable Gaussian law is an input. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal RealInnerProductSpace Topology
namespace DGRHS.Dynamics

theorem sourceDynamic_initial_secondMoment_posSemidef {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (k : ℕ) (Z : Ω→Fin k→ℝ) (hZ : ∀ a,MemLp (fun ω=>Z ω a) 2 ν) :
    Matrix.PosSemidef (fun a b=>∫ ω,Z ω a*Z ω b ∂ν) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change Matrix.conjTranspose (fun a b=>∫ ω,Z ω a*Z ω b ∂ν)=(fun a b=>∫ ω,Z ω a*Z ω b ∂ν)
    funext a b
    change (∫ ω,Z ω b*Z ω a ∂ν)=(∫ ω,Z ω a*Z ω b ∂ν)
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω=>mul_comm _ _)
  · intro θ
    have hi (a b : Fin k) : Integrable (fun ω=>Z ω a*Z ω b) ν := (hZ a).integrable_mul (hZ b)
    have hpoly (ω : Ω) : (∑ a,θ a*Z ω a)^2=∑ a,∑ b,(θ a*θ b)*(Z ω a*Z ω b) := by
      rw [pow_two,Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl;intro a _
      apply Finset.sum_congr rfl;intro b _
      ring
    have hn : 0≤∫ ω,(∑ a,θ a*Z ω a)^2 ∂ν := integral_nonneg fun ω=>sq_nonneg _
    simp_rw [hpoly] at hn
    rw [integral_finsetSum _ (fun a _=>integrable_finsetSum _ fun b _=>(hi a b).const_mul _)] at hn
    simp_rw [integral_finsetSum _ (fun b _=>(hi _ b).const_mul _),integral_const_mul] at hn
    simp only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,Finset.mul_sum]
    convert hn using 1
    apply Finset.sum_congr rfl;intro a _
    apply Finset.sum_congr rfl;intro b _
    ring

theorem sourceDynamic_total_covariance_posSemidef {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (ν : Measure Ω) (k : ℕ) (Z : Ω→Fin k→ℝ) (hZ : ∀ a,MemLp (fun ω=>Z ω a) 2 ν)
    (T β : ℝ) (hβ : 0≤β) (ρ : ℝ→EuclideanSpace ℝ ι→ℝ)
    (hρ : Measurable (Function.uncurry ρ))
    (hp : ∀ r∈Icc 0 T,IsProbabilityMeasure (DGRHS.Gaussian.gaussianRieszDensityMeasure (ρ r)))
    (t : Fin k→ℝ) (ht : ∀ a,t a≤T) (f : Fin k→ℝ→EuclideanSpace ℝ ι→ℝ) (G : ℝ≥0)
    (hf : ∀ a,ContinuousOn (fun p : ℝ×EuclideanSpace ℝ ι=>gradient (f a p.1) p.2) (Icc 0 (t a) ×ˢ univ))
    (hb : ∀ a,∀ r∈Icc 0 (t a),∀ z,‖gradient (f a r) z‖≤(G:ℝ)) :
    Matrix.PosSemidef (fun a b=>(∫ ω,Z ω a*Z ω b ∂ν)+sourceDynamicTimeCovariance β ρ k t f a b) :=
  (sourceDynamic_initial_secondMoment_posSemidef ν k Z hZ).add
    (sourceDynamic_time_covariance_posSemidef T β hβ ρ hρ hp k t ht f G hf hb)

theorem sourceDynamic_gaussian_target (k : ℕ) (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef) :
    let P := multivariateGaussian (0:EuclideanSpace ℝ (Fin k)) C
    IsProbabilityMeasure P ∧ HasGaussianLaw id P ∧
    (∀ a : Fin k,(∫ x,x a ∂P)=0) ∧
    (∀ a b : Fin k,Integrable (fun x=>x a*x b) P ∧ (∫ x,x a*x b ∂P)=C a b) ∧
    ∀ θ : EuclideanSpace ℝ (Fin k),charFun P θ=
      Complex.exp (-(∑ a,∑ b,θ a*θ b*C a b : ℝ)/2) := by
  dsimp only
  let P := multivariateGaussian (0:EuclideanSpace ℝ (Fin k)) C
  have hmean (a : Fin k) : (∫ x,x a ∂P)=0 := by
    rw [←EuclideanSpace.coe_proj,ContinuousLinearMap.integral_comp_id_comm]
    · simp [P]
    · exact IsGaussian.integrable_id
  have hG : HasGaussianLaw id P := IsGaussian.hasGaussianLaw_id
  have hcoord (a : Fin k) : MemLp (fun x=>x a) 2 P :=
    (hG.map_fun (EuclideanSpace.proj a)).memLp_two
  refine ⟨inferInstance,hG,hmean,?_,?_⟩
  · intro a b
    refine ⟨(hcoord a).integrable_mul (hcoord b),?_⟩
    have hc := covariance_eval_multivariateGaussian (μ:=(0:EuclideanSpace ℝ (Fin k))) hC a b
    rw [covariance_eq_sub (hcoord a) (hcoord b)] at hc
    simpa only [Pi.mul_apply,hmean,mul_zero,sub_zero] using hc
  · intro θ
    have hform : dotProduct θ (Matrix.mulVec C θ)=∑ a,∑ b,θ a*θ b*C a b := by
      simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
      apply Finset.sum_congr rfl;intro a _
      apply Finset.sum_congr rfl;intro b _
      ring
    rw [charFun_multivariateGaussian hC,hform]
    simp only [inner_zero_right,Complex.ofReal_zero,zero_mul,zero_sub,neg_div]

end DGRHS.Dynamics
set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_initial_secondMoment_posSemidef
#print axioms DGRHS.Dynamics.sourceDynamic_initial_secondMoment_posSemidef
set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_total_covariance_posSemidef
#print axioms DGRHS.Dynamics.sourceDynamic_total_covariance_posSemidef
set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_gaussian_target
#print axioms DGRHS.Dynamics.sourceDynamic_gaussian_target
