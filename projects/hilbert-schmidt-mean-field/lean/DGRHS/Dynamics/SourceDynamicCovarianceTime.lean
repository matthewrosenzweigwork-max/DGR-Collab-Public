import DGRHS.Commutator.SourceRieszStoppedSquareBounds
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The actual time part of the covariance in DGR (909--912).
Its smaller terminal horizons and positive semidefiniteness follow from the
same stopped native gradients. All spatial and time interchanges are proper.
This deterministic result is shared by the logarithmic and Riesz branches. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace
namespace DGRHS.Dynamics
open DGRHS.Commutator DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceDynamicTimeCovariance (β : ℝ) (ρ : ℝ→E→ℝ) (k : ℕ)
    (t : Fin k→ℝ) (f : Fin k→ℝ→E→ℝ) (a b : Fin k) : ℝ :=
  (2/β)*∫ r in Ioc 0 (min (t a) (t b)),
    ∫ z,⟪gradient (f a r) z,gradient (f b r) z⟫ ∂gaussianRieszDensityMeasure (ρ r)

lemma sourceDynamic_stopped_pair_proper (T : ℝ) (ρ : ℝ→E→ℝ)
    (hρ : Measurable (Function.uncurry ρ))
    (hp : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (k : ℕ) (t : Fin k→ℝ) (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0)
    (hf : ∀ a,ContinuousOn (fun p : ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a) ×ˢ univ))
    (hb : ∀ a,∀ r∈Icc 0 (t a),∀ z,‖gradient (f a r) z‖≤(G:ℝ))
    (a b : Fin k) :
    (∀ r∈Icc 0 T,Integrable (fun z=>
      ⟪sourceRieszStoppedGradient (t a) (f a) r z,
        sourceRieszStoppedGradient (t b) (f b) r z⟫) (gaussianRieszDensityMeasure (ρ r))) ∧
    Integrable (fun r=>∫ z,⟪sourceRieszStoppedGradient (t a) (f a) r z,
      sourceRieszStoppedGradient (t b) (f b) r z⟫ ∂gaussianRieszDensityMeasure (ρ r))
      (volume.restrict (Ioc 0 T)) := by
  let Q := fun p : ℝ×E=>⟪sourceRieszStoppedGradient (t a) (f a) p.1 p.2,
    sourceRieszStoppedGradient (t b) (f b) p.1 p.2⟫
  have hQ : Measurable Q :=
    (measurable_sourceRieszStoppedGradient (t a) (f a) (hf a)).inner
      (measurable_sourceRieszStoppedGradient (t b) (f b) (hf b))
  have hbound (r : ℝ) (z : E) : |Q (r,z)|≤(G:ℝ)^2 := by
    apply (abs_real_inner_le_norm _ _).trans
    simpa only [pow_two] using mul_le_mul
      (norm_sourceRieszStoppedGradient_le (t a) (f a) G (hb a) r z)
      (norm_sourceRieszStoppedGradient_le (t b) (f b) G (hb b) r z)
      (norm_nonneg _) G.coe_nonneg
  have hspace (r : ℝ) (hr : r∈Icc 0 T) :
      Integrable (fun z=>Q (r,z)) (gaussianRieszDensityMeasure (ρ r)) := by
    letI := hp r hr
    apply (integrable_const ((G:ℝ)^2)).mono'
      (hQ.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z=>by
      simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using hbound r z
  let κ := sourceDensityKernel volume ρ
  letI := sourceDensityKernel_sfinite volume ρ
  have hκ (r : ℝ) : κ r=gaussianRieszDensityMeasure (ρ r) := sourceDensityKernel_apply volume ρ hρ r
  have hm : Measurable (fun r=>∫ z,Q (r,z) ∂gaussianRieszDensityMeasure (ρ r)) := by
    simpa only [hκ] using (hQ.stronglyMeasurable.integral_kernel_prod_right' (κ:=κ)).measurable
  refine ⟨hspace,?_⟩
  apply (integrable_const ((G:ℝ)^2)).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  letI := hp r ⟨hr.1.le,hr.2⟩
  simpa only [measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using
    (norm_integral_le_of_norm_le_const (μ:=gaussianRieszDensityMeasure (ρ r))
      (Filter.Eventually.of_forall fun z=>by simpa only [Real.norm_eq_abs] using hbound r z))

lemma sourceDynamic_stopped_pair_identity (T ta tb : ℝ) (hta : ta≤T)
    (β : ℝ) (ρ : ℝ→E→ℝ) (f g : ℝ→E→ℝ) :
    (2/β)*(∫ r in Ioc 0 T,∫ z,
      ⟪sourceRieszStoppedGradient ta f r z,sourceRieszStoppedGradient tb g r z⟫
        ∂gaussianRieszDensityMeasure (ρ r))=
    (2/β)*(∫ r in Ioc 0 (min ta tb),∫ z,⟪gradient (f r) z,gradient (g r) z⟫
      ∂gaussianRieszDensityMeasure (ρ r)) := by
  let U := min ta tb
  let A := fun r=>∫ z,⟪gradient (f r) z,gradient (g r) z⟫ ∂gaussianRieszDensityMeasure (ρ r)
  have heq : (fun r=>∫ z,
      ⟪sourceRieszStoppedGradient ta f r z,sourceRieszStoppedGradient tb g r z⟫
        ∂gaussianRieszDensityMeasure (ρ r))=ᵐ[volume.restrict (Ioc 0 T)] (Ioc 0 U).indicator A := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    by_cases hu : r≤U
    · have ha : r∈Icc 0 ta := ⟨hr.1.le,hu.trans (min_le_left _ _)⟩
      have hb : r∈Icc 0 tb := ⟨hr.1.le,hu.trans (min_le_right _ _)⟩
      simp [sourceRieszStoppedGradient,ha,hb,Set.indicator,A,hr.1,hu,mem_Ioc]
    · have hcut : ∀ z,⟪sourceRieszStoppedGradient ta f r z,sourceRieszStoppedGradient tb g r z⟫=0 := by
        intro z
        rw [sourceRieszStoppedGradient_inner_eq_cut]
        simp [sourceRieszCrossGradientCut,Set.piecewise,U,mem_Icc,hu]
      simp only [hcut,integral_zero]
      simp [Set.indicator,mem_Ioc,hu]
  have hsub : Ioc 0 U⊆Ioc 0 T := fun r hr=>⟨hr.1,hr.2.trans ((min_le_left _ _).trans hta)⟩
  rw [integral_congr_ae heq,setIntegral_indicator measurableSet_Ioc,inter_eq_right.mpr hsub]

theorem sourceDynamic_time_covariance_quadratic (T β : ℝ) (ρ : ℝ→E→ℝ)
    (hρ : Measurable (Function.uncurry ρ))
    (hp : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (k : ℕ) (t θ : Fin k→ℝ) (ht : ∀ a,t a≤T) (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0)
    (hf : ∀ a,ContinuousOn (fun p : ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a) ×ˢ univ))
    (hb : ∀ a,∀ r∈Icc 0 (t a),∀ z,‖gradient (f a r) z‖≤(G:ℝ)) :
    (∑ a,∑ b,(θ a*θ b)*sourceDynamicTimeCovariance β ρ k t f a b)=
      (2/β)*∫ r in Ioc 0 T,∫ z,
        ‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
          ∂gaussianRieszDensityMeasure (ρ r) := by
  let Q := fun a b r=>∫ z,⟪sourceRieszStoppedGradient (t a) (f a) r z,
    sourceRieszStoppedGradient (t b) (f b) r z⟫ ∂gaussianRieszDensityMeasure (ρ r)
  have hi (a b : Fin k) := sourceDynamic_stopped_pair_proper T ρ hρ hp k t f G hf hb a b
  have hspace (r : ℝ) (hr : r∈Icc 0 T) :
      (∫ z,‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
        ∂gaussianRieszDensityMeasure (ρ r))=∑ a,∑ b,(θ a*θ b)*Q a b r := by
    simp_rw [sourceRieszStoppedGradientNormSq]
    rw [integral_finsetSum _ (fun a _=>integrable_finsetSum _ fun b _=>((hi a b).1 r hr).const_mul _)]
    simp_rw [integral_finsetSum _ (fun b _=>((hi _ b).1 r hr).const_mul _),integral_const_mul]
    rfl
  have heq : (fun r=>∫ z,‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
      ∂gaussianRieszDensityMeasure (ρ r))=ᵐ[volume.restrict (Ioc 0 T)]
      (fun r=>∑ a,∑ b,(θ a*θ b)*Q a b r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hspace r ⟨hr.1.le,hr.2⟩
  rw [integral_congr_ae heq,integral_finsetSum _
    (fun a _=>integrable_finsetSum _ fun b _=>(hi a b).2.const_mul _)]
  simp_rw [integral_finsetSum _ (fun b _=>(hi _ b).2.const_mul _),integral_const_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro b _
  have hp := sourceDynamic_stopped_pair_identity T (t a) (t b) (ht a) β ρ (f a) (f b)
  change (θ a*θ b)*sourceDynamicTimeCovariance β ρ k t f a b=
    (2/β)*((θ a*θ b)*(∫ r in Ioc 0 T,Q a b r))
  calc
    _ = (θ a*θ b)*((2/β)*(∫ r in Ioc 0 T,Q a b r)) := by rw [hp];rfl
    _ = _ := by ring

theorem sourceDynamic_time_covariance_posSemidef (T β : ℝ) (hβ : 0≤β)
    (ρ : ℝ→E→ℝ) (hρ : Measurable (Function.uncurry ρ))
    (hp : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (k : ℕ) (t : Fin k→ℝ) (ht : ∀ a,t a≤T) (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0)
    (hf : ∀ a,ContinuousOn (fun p : ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a) ×ˢ univ))
    (hb : ∀ a,∀ r∈Icc 0 (t a),∀ z,‖gradient (f a r) z‖≤(G:ℝ)) :
    Matrix.PosSemidef (sourceDynamicTimeCovariance β ρ k t f) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change Matrix.conjTranspose (sourceDynamicTimeCovariance β ρ k t f)=sourceDynamicTimeCovariance β ρ k t f
    funext a b
    change sourceDynamicTimeCovariance β ρ k t f b a=sourceDynamicTimeCovariance β ρ k t f a b
    unfold sourceDynamicTimeCovariance
    rw [min_comm (t b) (t a)]
    apply congrArg (fun v : ℝ=>(2/β)*v)
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun r=>integral_congr_ae
      (Filter.Eventually.of_forall fun z=>real_inner_comm _ _)
  · intro θ
    have hh := sourceDynamic_time_covariance_quadratic T β ρ hρ hp k t θ ht f G hf hb
    have hn : 0≤∑ a,∑ b,(θ a*θ b)*sourceDynamicTimeCovariance β ρ k t f a b := by
      rw [hh]
      exact mul_nonneg (div_nonneg (by norm_num) hβ)
        (integral_nonneg fun r=>integral_nonneg fun z=>sq_nonneg _)
    simp only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,Finset.mul_sum]
    convert hn using 1
    apply Finset.sum_congr rfl;intro a _
    apply Finset.sum_congr rfl;intro b _
    ring

end DGRHS.Dynamics
set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_time_covariance_quadratic
#print axioms DGRHS.Dynamics.sourceDynamic_time_covariance_quadratic
set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceDynamic_time_covariance_posSemidef
#print axioms DGRHS.Dynamics.sourceDynamic_stopped_pair_proper
#print axioms DGRHS.Dynamics.sourceDynamic_stopped_pair_identity
#print axioms DGRHS.Dynamics.sourceDynamic_time_covariance_posSemidef
