import DGRHS.Dynamics.SourceDynamicCovarianceInterval

/-! Native finite-dimensional Levy assembly for the constructed covariance law.
This is an analytic consumer of pointwise scalar CF convergence. The physical
CLT must prove that convergence from the source evolution, rather than assume it. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal RealInnerProductSpace Topology
namespace DGRHS.Dynamics

lemma sourceDynamic_finite_charFun {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (k : ℕ) (X : Ω→EuclideanSpace ℝ (Fin k))
    (hX : AEMeasurable X ν) (θ : EuclideanSpace ℝ (Fin k)) :
    charFun (ν.map X) θ=
      ∫ ω,Complex.exp ((∑ a,θ a*X ω a : ℝ)*Complex.I) ∂ν := by
  rw [charFun_apply,integral_map hX (by fun_prop)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω=>by
    simp [Function.comp_def,PiLp.inner_apply,RCLike.inner_apply',mul_comm]

theorem sourceDynamic_scalar_characteristic_clt {Ω : ℕ→Type*}
    [∀ N,MeasurableSpace (Ω N)] (ν : ∀ N,Measure (Ω N)) [∀ N,IsProbabilityMeasure (ν N)]
    (k : ℕ) (X : ∀ N,Ω N→EuclideanSpace ℝ (Fin k))
    (hX : ∀ N,AEMeasurable (X N) (ν N))
    (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (hcf : ∀ θ : EuclideanSpace ℝ (Fin k),
      Tendsto (fun N=>∫ ω,Complex.exp ((∑ a,θ a*X N ω a : ℝ)*Complex.I) ∂ν N) atTop
        (𝓝 (Complex.exp (-(∑ a,∑ b,θ a*θ b*C a b : ℝ)/2)))) :
    TendstoInDistribution X atTop id ν (multivariateGaussian (0:EuclideanSpace ℝ (Fin k)) C) := by
  apply TendstoInDistribution.of_tendsto_charFun hX measurable_id.aemeasurable
  intro θ
  simpa only [sourceDynamic_finite_charFun (ν _) k (X _) (hX _) θ,Measure.map_id,
    (sourceDynamic_gaussian_target k C hC).2.2.2.2 θ] using hcf θ

end DGRHS.Dynamics
set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_finite_charFun
#print axioms DGRHS.Dynamics.sourceDynamic_finite_charFun
set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_scalar_characteristic_clt
#print axioms DGRHS.Dynamics.sourceDynamic_scalar_characteristic_clt
