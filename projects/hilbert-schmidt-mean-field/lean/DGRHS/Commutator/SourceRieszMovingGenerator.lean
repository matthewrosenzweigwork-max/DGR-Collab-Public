import DGRHS.Commutator.SourceRieszFullMovingContinuity
import DGRHS.Commutator.SourceBoundedC2Spatial
import DGRHS.Commutator.SourceRieszStaticWeakForm
import DGRHS.Commutator.SourceRieszLocalEnergy
import DGRHS.Dynamics.SourceAdjointHessianLipschitz

/-! UNCOMPILED actual singular mean-field generator. The diffusion term is
the native Laplacian trace and the interaction is the checked canceled Riesz
pair kernel. Neither generator continuity nor its bound is assumed. A source
closed-horizon consumer will apply this to endpoint-clamped laws and tests. -/
noncomputable section
open MeasureTheory Laplacian Set
open scoped Topology NNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Dynamics
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma continuous_sourceRieszStaticMeanTestDrift_moving
    (s β : ℝ) (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ))
    (q : ℝ→E→ℝ) (hq : ∀ r,ContDiff ℝ 2 (q r))
    (hgrad : Continuous (fun p:ℝ×E=>gradient (q p.1) p.2))
    (hH : Continuous (fun p:ℝ×E=>iteratedFDeriv ℝ 2 (q p.1) p.2))
    (K : ℝ≥0) (hK : ∀ r x,‖iteratedFDeriv ℝ 2 (q r) x‖≤K)
    (μ : ℝ→ProbabilityMeasure E) (hμ : Continuous μ)
    (ρ : ℝ→E→ℝ) (hρμ : ∀ r,(μ r:Measure E)=gaussianRieszDensityMeasure (ρ r))
    (M : ℝ) (hM : 0≤M) (hρ : ∀ r,∀ᵐ x ∂volume,ρ r x≤M) :
    Continuous (fun r=>sourceRieszStaticMeanTestDrift s β (ρ r) (q r)) := by
  let b := stdOrthonormalBasis ℝ E
  let C : ℝ := (Module.finrank ℝ E:ℝ)*(K:ℝ)
  have hΔ : Continuous (fun p:ℝ×E=>laplacian (q p.1) p.2) :=
    continuous_laplacian_of_joint_hessian b q hH
  have hΔb (p:ℝ×E) : |laplacian (q p.1) p.2|≤C := by
    simpa only [C,Fintype.card_fin] using
      source_laplacian_bound_of_hessian b (q p.1) (K:ℝ) (hK p.1) p.2
  have hΔint := continuous_integral_moving_probability (fun r:ℝ=>r) continuous_id
    μ hμ (fun p:ℝ×E=>laplacian (q p.1) p.2) hΔ C hΔb
  have hp := continuous_integral_sourceRieszTransportKernel_one_moving s hs (by linarith)
    (fun r=>gradient (q r)) hgrad K
    (fun r=>sourceAdjoint_gradient_lipschitz_of_hessian_bound (q r) (hq r) K (hK r))
    μ hμ ρ hρμ M hM hρ
  simpa only [sourceRieszStaticMeanTestDrift,hρμ,Pi.sub_def] using
    (hΔint.const_mul β⁻¹).sub (hp.const_mul (1/2:ℝ))

lemma sourceRieszStaticMeanTestDrift_bound
    (s β : ℝ) (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ))
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (φ : E→ℝ) (hφ : ContDiff ℝ 2 φ) (K : ℝ≥0)
    (hK : ∀ x,‖iteratedFDeriv ℝ 2 φ x‖≤K) :
    |sourceRieszStaticMeanTestDrift s β ρ φ|≤
      |β⁻¹| * ((Module.finrank ℝ E:ℝ)*(K:ℝ)) +
        (1/2:ℝ)*(sourceRieszLocalProfileConstant (ι:=ι) s 1*(K:ℝ)^1*
          gaussianRieszPhysicalPotentialConstant s M ι) := by
  let C : ℝ := (Module.finrank ℝ E:ℝ)*(K:ℝ)
  have hΔ (x:E) : |laplacian φ x|≤C := by
    simpa only [C,Fintype.card_fin] using
      source_laplacian_bound_of_hessian (stdOrthonormalBasis ℝ E) φ (K:ℝ) hK x
  have hi : |∫ x,laplacian φ x ∂gaussianRieszDensityMeasure ρ|≤C := by
    have hh : ∀ᵐ x ∂gaussianRieszDensityMeasure ρ,‖laplacian φ x‖≤C :=
      Filter.Eventually.of_forall fun x=>by simpa only [Real.norm_eq_abs] using hΔ x
    simpa only [Real.norm_eq_abs,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one]
      using norm_integral_le_of_norm_le_const hh
  have hp := (sourceRieszLocalTransport_pair s 1 hs hd
    (sourceAdjoint_gradient_lipschitz_of_hessian_bound φ hφ K hK) ρ M hM hρ).2
  unfold sourceRieszStaticMeanTestDrift
  calc
    _ ≤ |β⁻¹*(∫ x,laplacian φ x ∂gaussianRieszDensityMeasure ρ)| +
        |(1/2:ℝ)*(∫ p,sourceRieszTransportKernel 1 s (gradient φ) p
          ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))| :=
      abs_sub _ _
    _ = |β⁻¹| * |∫ x,laplacian φ x ∂gaussianRieszDensityMeasure ρ| +
        (1/2:ℝ)*|∫ p,sourceRieszTransportKernel 1 s (gradient φ) p
          ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hi (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hp (by norm_num))

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.continuous_sourceRieszStaticMeanTestDrift_moving
#print axioms DGRHS.Commutator.continuous_sourceRieszStaticMeanTestDrift_moving
#check @DGRHS.Commutator.sourceRieszStaticMeanTestDrift_bound
#print axioms DGRHS.Commutator.sourceRieszStaticMeanTestDrift_bound
