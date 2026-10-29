import DGRHS.Commutator.SourceRieszDynamicQuadratic
import DGRHS.Commutator.SourceRieszDynamicForceEmpirical
import DGRHS.Dynamics.SourceAdjointHessianLipschitz

/-! Actual positive-Riesz backward-adjoint INSTANTANEOUS drift. The supplied
PDE is exactly dt+beta^-1 lap=the integral of actual force against the actual
spatial gradient difference. Proper sections/pairs are derived from original
bounded-density data. No time decomposition, martingale or bracket is assumed. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Original source adjoint operator with the combined difference kernel.
Separate un-cancelled force convolutions need not be proper in this regime. -/
def sourceRieszAdjointLinearizedOperator (β : ℝ) (ρ : E→ℝ) (s : ℝ)
    (q lap : E→ℝ) (x : E) : ℝ :=
  β⁻¹*lap x-∫ y,⟪sourceRieszForce s (x-y),gradient q x-gradient q y⟫ ∂gaussianRieszDensityMeasure ρ

theorem sourceRiesz_backward_adjoint_drift (s β : ℝ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι:ℝ)) (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (q : E→ℝ) (K : ℝ≥0) (hgrad : LipschitzWith K (gradient q)) (dt lap : E→ℝ)
    (hback : ∀ z,dt z+sourceRieszAdjointLinearizedOperator β ρ s q lap z=0)
    (N : ℕ) (hN : 0<N) (x : Fin N→E) :
    let μ := gaussianRieszDensityMeasure ρ
    let e := sourceRieszLocalEmpiricalLaw N x
    let h := sourceRieszTransportKernel 1 s (gradient q)
    (∀ z,Integrable (fun y=>⟪sourceRieszForce s (z-y),gradient q z-gradient q y⟫) μ) ∧
    Integrable (fun z=>dt z+β⁻¹*lap z) e ∧
    Integrable (fun z=>dt z+β⁻¹*lap z) μ ∧
    ((∫ z,dt z+β⁻¹*lap z ∂e)-(∫ z,dt z+β⁻¹*lap z ∂μ))-
      (1/2:ℝ)*((∫ p in {p : E×E|p.1≠p.2},h p ∂e.prod e)-(∫ p,h p ∂μ.prod μ))=
      -(1/2:ℝ)*sourceRieszLocalTransportEnergy ρ s 1 (gradient q) N x := by
  let μ := gaussianRieszDensityMeasure ρ
  let e := sourceRieszLocalEmpiricalLaw N x
  let h := sourceRieszTransportKernel 1 s (gradient q)
  have hsec (z : E) : Integrable (fun y=>h (z,y)) μ :=
    (sourceRieszLocalTransport_section s 1 hs (by linarith) hgrad ρ M hM hρ z).1
  have hforce : h=(fun p : E×E=>⟪sourceRieszForce s (p.1-p.2),gradient q p.1-gradient q p.2⟫) :=
    funext fun p=>sourceRieszTransportKernel_force s hs (gradient q) p.1 p.2
  have hp : (fun z=>dt z+β⁻¹*lap z)=(fun z=>∫ y,h (z,y) ∂μ) := by
    funext z
    have hb := hback z
    dsimp [sourceRieszAdjointLinearizedOperator] at hb
    rw [hforce]
    linarith
  obtain ⟨h1,h2,h3,h4,he⟩ := sourceRiesz_dynamic_quadratic_expansion s hs hd hgrad ρ M hM hρ N hN x
  refine ⟨?_,by rw [hp];exact h2.integral_prod_left,by rw [hp];exact h4.integral_prod_left,?_⟩
  · intro z
    simpa only [hforce] using hsec z
  · rw [hp,←integral_prod h h2,←integral_prod h h4]
    change ((∫ p,h p ∂e.prod μ)-(∫ p,h p ∂μ.prod μ))-
      (1/2:ℝ)*((∫ p in {p : E×E|p.1≠p.2},h p ∂e.prod e)-(∫ p,h p ∂μ.prod μ))=
      -(1/2:ℝ)*sourceRieszLocalTransportEnergy ρ s 1 (gradient q) N x
    rw [he]
    ring

/-- True source finite-N force drift with actual gradient and Hessian control.
The dt and lap functions are the physical time derivative and Laplacian data;
only their original backward PDE is assumed, not a favorable drift identity. -/
theorem sourceRiesz_backward_adjoint_particle_drift (s β : ℝ) (hs : 0<s) (hβ : 0<β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (q : E→ℝ) (hq : ContDiff ℝ 2 q) (K : ℝ≥0) (hK : ∀ z,‖iteratedFDeriv ℝ 2 q z‖≤(K:ℝ))
    (dt lap : E→ℝ) (hback : ∀ z,dt z+sourceRieszAdjointLinearizedOperator β ρ s q lap z=0)
    (N : ℕ) (hN : 0<N) (x : Fin N→E) :
    let μ := gaussianRieszDensityMeasure ρ
    let e := sourceRieszLocalEmpiricalLaw N x
    let h := sourceRieszTransportKernel 1 s (gradient q)
    Integrable h (e.prod e) ∧ Integrable h (μ.prod μ) ∧
    Integrable (fun z=>dt z+β⁻¹*lap z) e ∧ Integrable (fun z=>dt z+β⁻¹*lap z) μ ∧
    ((∫ z,dt z+β⁻¹*lap z ∂e)-(∫ z,dt z+β⁻¹*lap z ∂μ))-
      ((N:ℝ)^2)⁻¹*DGRHS.CanonicalVariance.offDiagonalSum
        (fun p : E×E=>⟪sourceRieszForce s (p.1-p.2),gradient q p.1⟫) x+
      (1/2:ℝ)*(∫ p,h p ∂μ.prod μ)=
      -(1/2:ℝ)*sourceRieszLocalTransportEnergy ρ s 1 (gradient q) N x := by
  have hg := DGRHS.Dynamics.sourceAdjoint_gradient_lipschitz_of_hessian_bound q hq K hK
  have hEmp := sourceRiesz_dynamic_drift_empirical s hs hg N x
  have hQuad := sourceRiesz_dynamic_quadratic_expansion s hs hd hg ρ M hM hρ N hN x
  obtain ⟨hsec,hiE,hiμ,he⟩ := sourceRiesz_backward_adjoint_drift s β hs hd ρ M hM hρ q K hg dt lap hback N hN x
  refine ⟨hEmp.1,hQuad.2.2.2.1,hiE,hiμ,?_⟩
  rw [hEmp.2]
  linarith [he]

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszAdjointLinearizedOperator
#print axioms DGRHS.Commutator.sourceRieszAdjointLinearizedOperator
#check @DGRHS.Commutator.sourceRiesz_backward_adjoint_drift
#print axioms DGRHS.Commutator.sourceRiesz_backward_adjoint_drift
#check @DGRHS.Commutator.sourceRiesz_backward_adjoint_particle_drift
#print axioms DGRHS.Commutator.sourceRiesz_backward_adjoint_particle_drift
