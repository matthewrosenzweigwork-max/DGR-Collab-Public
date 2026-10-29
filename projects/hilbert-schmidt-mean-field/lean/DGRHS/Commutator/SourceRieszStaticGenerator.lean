import DGRHS.Commutator.SourceRieszMovingGenerator

/-! UNCOMPILED positive-Riesz fixed-test specialization. Actual test,
Laplacian and canceled pair integrals are proper; the fixed generator is
continuous along the actual narrowly continuous probability path. The latter
continuity is proved, not included in the source mean-field class. The
Laplacian composition follows the typed-map pattern independently checked
for root SourceLogStaticGenerator; the Riesz properness and singular-limit
arguments are distinct and use only the positive-Riesz imports. -/
noncomputable section
open MeasureTheory Laplacian Set Filter
open scoped NNReal Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Dynamics
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma SourceBoundedC2Test.riesz_spatial_properness
    (φ : E→ℝ) (hφ : SourceBoundedC2Test φ)
    (s : ℝ) (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ))
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    Integrable φ (gaussianRieszDensityMeasure ρ) ∧
      Integrable (laplacian φ) (gaussianRieszDensityMeasure ρ) ∧
      Integrable (sourceRieszTransportKernel 1 s (gradient φ))
        ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  obtain ⟨hc,C,hC,hb⟩ := (sourceBoundedC2Test_iff_classical_bounds φ).mp hφ
  let K : ℝ≥0 := ⟨C,hC⟩
  have hH : Continuous (fun p : Unit×E => iteratedFDeriv ℝ 2 φ p.2) :=
    (hc.continuous_iteratedFDeriv le_rfl).comp continuous_snd
  have hL := continuous_laplacian_of_joint_hessian
    (EuclideanSpace.basisFun ι ℝ) (fun _ : Unit => φ) hH
  have he : Continuous (fun x : E => ((),x)) :=
    continuous_const.prodMk continuous_id
  have hΔ : Continuous (laplacian φ) := by
    simpa only [Function.comp_def] using hL.comp he
  refine ⟨?_,?_,(sourceRieszLocalTransport_pair s 1 hs hd
    (sourceAdjoint_gradient_lipschitz_of_hessian_bound φ hc K
      (fun x => (hb x).2.2)) ρ M hM hρ).1⟩
  · exact Integrable.mono' (integrable_const C) hc.continuous.measurable.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using (hb x).1)
  · exact Integrable.mono' (integrable_const ((Fintype.card ι:ℝ)*C))
      hΔ.measurable.aestronglyMeasurable (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using
          source_laplacian_bound_of_hessian (EuclideanSpace.basisFun ι ℝ) φ C
            (fun y => (hb y).2.2) x)

lemma SourceBoundedC2Test.continuous_riesz_static_generator_probability
    (φ : E→ℝ) (hφ : SourceBoundedC2Test φ)
    (s β : ℝ) (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ))
    (μ : ℝ→ProbabilityMeasure E) (hμ : Continuous μ)
    (ρ : ℝ→E→ℝ)
    (hρμ : ∀ r,(μ r:Measure E)=gaussianRieszDensityMeasure (ρ r))
    (M : ℝ) (hM : 0≤M) (hρ : ∀ r,∀ᵐ x ∂volume,ρ r x≤M) :
    Continuous (fun r => sourceRieszStaticMeanTestDrift s β (ρ r) φ) := by
  obtain ⟨hc,C,hC,hb⟩ := (sourceBoundedC2Test_iff_classical_bounds φ).mp hφ
  let K : ℝ≥0 := ⟨C,hC⟩
  have hv := sourceAdjoint_gradient_lipschitz_of_hessian_bound φ hc K
    (fun x => (hb x).2.2)
  exact continuous_sourceRieszStaticMeanTestDrift_moving s β hs hd
    (fun _ => φ) (fun _ => hc) (hv.continuous.comp continuous_snd)
    ((hc.continuous_iteratedFDeriv le_rfl).comp continuous_snd)
    K (fun _ x => (hb x).2.2) μ hμ ρ hρμ M hM hρ

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.SourceBoundedC2Test.riesz_spatial_properness
#print axioms DGRHS.Commutator.SourceBoundedC2Test.riesz_spatial_properness
#check @DGRHS.Commutator.SourceBoundedC2Test.continuous_riesz_static_generator_probability
#print axioms DGRHS.Commutator.SourceBoundedC2Test.continuous_riesz_static_generator_probability
