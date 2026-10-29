import DGRHS.Commutator.SourceRieszAdjointDrift
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-! Original finite-N positive-Riesz instantaneous physical drift, with the
actual time derivative, native Laplacian and native gradient of ONE test q.
The original pointwise backward-adjoint PDE and spatial Hessian bound remain
hypotheses. This is not an Ito identity or a stochastic time decomposition.
Adaptation reference: root SourceLogAdjointPhysicalDrift, checked ade1e009;
the singular Riesz properness and force identity are proved in own imports. -/
noncomputable section
open MeasureTheory Laplacian
open scoped NNReal RealInnerProductSpace
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Actual particle test drift, including collision-zero force. -/
def sourceRieszEmpiricalTestDrift (s β : ℝ) (q : ℝ→E→ℝ)
    (N : ℕ) (r : ℝ) (x : Fin N→E) : ℝ :=
  (∫ z,deriv (fun t=>q t z) r+β⁻¹*laplacian (q r) z ∂sourceRieszLocalEmpiricalLaw N x)-
    ((N:ℝ)^2)⁻¹*(∑ i : Fin N,∑ j : Fin N,
      ⟪sourceRieszForce s (x i-x j),gradient (q r) (x i)⟫)

/-- Actual mean-field test drift with the proper combined difference kernel. -/
def sourceRieszMeanTestDrift (s β : ℝ) (ρ : E→ℝ) (q : ℝ→E→ℝ) (r : ℝ) : ℝ :=
  (∫ z,deriv (fun t=>q t z) r+β⁻¹*laplacian (q r) z ∂gaussianRieszDensityMeasure ρ)-
    (1/2:ℝ)*(∫ p,sourceRieszTransportKernel 1 s (gradient (q r)) p
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))

/-- Native physical q/r wrapper. Proper pair and combined test integrals are
conclusions, not supplied favorable hypotheses. All positive N and every
configuration, including repeated locations, are covered. -/
theorem sourceRiesz_adjoint_physical_drift (s β : ℝ) (hs : 0<s) (hβ : 0<β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ z ∂volume,ρ z≤M)
    (q : ℝ→E→ℝ) (r : ℝ) (hq : ContDiff ℝ 2 (q r)) (K : ℝ≥0)
    (hK : ∀ z,‖iteratedFDeriv ℝ 2 (q r) z‖≤(K:ℝ))
    (hback : ∀ z,deriv (fun t=>q t z) r+β⁻¹*laplacian (q r) z=
      ∫ y,⟪sourceRieszForce s (z-y),gradient (q r) z-gradient (q r) y⟫
        ∂gaussianRieszDensityMeasure ρ)
    (N : ℕ) (hN : 0<N) (x : Fin N→E) :
    let μ := gaussianRieszDensityMeasure ρ
    let e := sourceRieszLocalEmpiricalLaw N x
    let h := sourceRieszTransportKernel 1 s (gradient (q r))
    Integrable h (e.prod e) ∧ Integrable h (μ.prod μ) ∧
    Integrable (fun z=>deriv (fun t=>q t z) r+β⁻¹*laplacian (q r) z) e ∧
    Integrable (fun z=>deriv (fun t=>q t z) r+β⁻¹*laplacian (q r) z) μ ∧
    sourceRieszEmpiricalTestDrift s β q N r x-sourceRieszMeanTestDrift s β ρ q r=
      -(1/2:ℝ)*sourceRieszLocalTransportEnergy ρ s 1 (gradient (q r)) N x := by
  have hb : ∀ z,deriv (fun t=>q t z) r+
      sourceRieszAdjointLinearizedOperator β ρ s (q r) (laplacian (q r)) z=0 := by
    intro z
    dsimp [sourceRieszAdjointLinearizedOperator]
    linarith [hback z]
  obtain ⟨h1,h2,h3,h4,he⟩ := sourceRiesz_backward_adjoint_particle_drift s β hs hβ hd
    ρ M hM hρ (q r) hq K hK (fun z=>deriv (fun t=>q t z) r) (laplacian (q r)) hb N hN x
  refine ⟨h1,h2,h3,h4,?_⟩
  rw [sourceRiesz_force_offDiagonalSum s N x (gradient (q r))] at he
  unfold sourceRieszEmpiricalTestDrift sourceRieszMeanTestDrift
  linarith [he]

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszEmpiricalTestDrift
#print axioms DGRHS.Commutator.sourceRieszEmpiricalTestDrift
#check @DGRHS.Commutator.sourceRieszMeanTestDrift
#print axioms DGRHS.Commutator.sourceRieszMeanTestDrift
#check @DGRHS.Commutator.sourceRiesz_adjoint_physical_drift
#print axioms DGRHS.Commutator.sourceRiesz_adjoint_physical_drift
