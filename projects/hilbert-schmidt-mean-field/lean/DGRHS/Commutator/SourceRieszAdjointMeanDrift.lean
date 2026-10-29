import DGRHS.Commutator.SourceRieszAdjointPhysicalDrift
import DGRHS.Commutator.SourceRieszTimeMeasurable
import DGRHS.Commutator.SourceRieszStoppedCovariance

/-! Source3857--3929: the native backward PDE identifies the actual mean
test drift with one half of the proper difference-of-gradients pair integral.
The singular pair bound gives time properness. A stopped measurable gradient
extension is used only outside the original closed horizon. No uncancelled
force integrability or terminal identity is assumed.
Adaptation reference: root Dynamics/SourceLogAdjointTimeMeasurable. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set
open scoped NNReal RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Dynamics
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem sourceRiesz_adjoint_mean_drift_eq_half_pair
    (s β : ℝ) (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ))
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ z ∂volume,ρ z≤M)
    (q : ℝ→E→ℝ) (r : ℝ) (hq : ContDiff ℝ 2 (q r)) (K : ℝ≥0)
    (hK : ∀ z,‖iteratedFDeriv ℝ 2 (q r) z‖≤(K:ℝ))
    (hback : ∀ z,deriv (fun t=>q t z) r+β⁻¹*laplacian (q r) z=
      ∫ y,⟪sourceRieszForce s (z-y),gradient (q r) z-gradient (q r) y⟫
        ∂gaussianRieszDensityMeasure ρ) :
    sourceRieszMeanTestDrift s β ρ q r=
      (1/2:ℝ)*(∫ p,sourceRieszTransportKernel 1 s (gradient (q r)) p
        ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  have hv := sourceAdjoint_gradient_lipschitz_of_hessian_bound (q r) hq K hK
  have hi := (sourceRieszLocalTransport_pair s 1 hs hd hv ρ M hM hρ).1
  have he : (fun z=>deriv (fun t=>q t z) r+β⁻¹*laplacian (q r) z)=
      (fun z=>∫ y,sourceRieszTransportKernel 1 s (gradient (q r)) (z,y)
        ∂gaussianRieszDensityMeasure ρ) := by
    funext z
    simp_rw [sourceRieszTransportKernel_force s hs]
    exact hback z
  unfold sourceRieszMeanTestDrift
  rw [he,←integral_prod _ hi]
  ring

theorem sourceRiesz_adjoint_mean_drift_time_integrable
    (s β T M : ℝ) (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M)
    (ρ : ℝ→E→ℝ) (hρm : Measurable (Function.uncurry ρ))
    (hprob : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hρ : ∀ r∈Icc 0 T,∀ᵐ z ∂volume,ρ r z≤M)
    (q : ℝ→E→ℝ) (K : ℝ≥0)
    (hq : ∀ r∈Icc 0 T,ContDiff ℝ 2 (q r))
    (hK : ∀ r∈Icc 0 T,∀ z,‖iteratedFDeriv ℝ 2 (q r) z‖≤(K:ℝ))
    (hgrad : ContinuousOn (fun p : ℝ×E=>gradient (q p.1) p.2) (Icc 0 T ×ˢ univ))
    (hback : ∀ᵐ r ∂volume.restrict (Ioc 0 T),∀ z,
      deriv (fun t=>q t z) r+β⁻¹*laplacian (q r) z=
        ∫ y,⟪sourceRieszForce s (z-y),gradient (q r) z-gradient (q r) y⟫
          ∂gaussianRieszDensityMeasure (ρ r)) :
    Integrable (fun r=>sourceRieszMeanTestDrift s β (ρ r) q r)
      (volume.restrict (Ioc 0 T)) := by
  let v := sourceRieszStoppedGradient T q
  have hv : Measurable (Function.uncurry v) := measurable_sourceRieszStoppedGradient T q hgrad
  have hvr (r : ℝ) (hr : r∈Icc 0 T) : v r=gradient (q r) := by
    funext z
    simp [v,sourceRieszStoppedGradient,hr]
  let κ := sourceDensityKernel volume ρ
  letI := sourceDensityKernel_sfinite volume ρ
  have hκ (r : ℝ) : κ r=gaussianRieszDensityMeasure (ρ r) :=
    sourceDensityKernel_apply volume ρ hρm r
  have hk := measurable_sourceRieszTransportKernel_time s hs v hv
  have hI : Measurable (fun r=>∫ p,sourceRieszTransportKernel 1 s (v r) p
      ∂(κ r).prod (κ r)) := by
    have ht := hk.stronglyMeasurable.integral_kernel_prod_right' (κ:=κ.prod κ)
    simpa only [Kernel.prod_apply] using ht.measurable
  let C := sourceRieszLocalProfileConstant (ι:=ι) s 1*(K:ℝ)^1*
    gaussianRieszPhysicalPotentialConstant s M ι
  have hi : Integrable (fun r=>(1/2:ℝ)*(∫ p,sourceRieszTransportKernel 1 s (v r) p
      ∂(κ r).prod (κ r))) (volume.restrict (Ioc 0 T)) := by
    apply (integrable_const ((1/2:ℝ)*C)).mono' (hI.const_mul _).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr' : r∈Icc 0 T := ⟨hr.1.le,hr.2⟩
    letI := hprob r hr'
    have hL := sourceAdjoint_gradient_lipschitz_of_hessian_bound (q r) (hq r hr') K (hK r hr')
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2),hκ r,hvr r hr']
    exact mul_le_mul_of_nonneg_left
      (sourceRieszLocalTransport_pair s 1 hs hd hL (ρ r) M hM (hρ r hr')).2 (by norm_num)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc,hback] with r hr hb
  have hr' : r∈Icc 0 T := ⟨hr.1.le,hr.2⟩
  letI := hprob r hr'
  rw [hκ r,hvr r hr']
  exact (sourceRiesz_adjoint_mean_drift_eq_half_pair s β hs hd (ρ r) M hM
    (hρ r hr') q r (hq r hr') K (hK r hr') hb).symm

end DGRHS.Commutator
set_option pp.deepTerms true in
#check @DGRHS.Commutator.sourceRiesz_adjoint_mean_drift_eq_half_pair
#print axioms DGRHS.Commutator.sourceRiesz_adjoint_mean_drift_eq_half_pair
set_option pp.deepTerms true in
#check @DGRHS.Commutator.sourceRiesz_adjoint_mean_drift_time_integrable
#print axioms DGRHS.Commutator.sourceRiesz_adjoint_mean_drift_time_integrable
