import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D15_Forces
import SharpSymmetricLSI.Defs.D16_GaussianLimit
import SharpSymmetricLSI.Paper.WeightedHS3

/-!
# R24: (6.3), weighted Hilbert–Schmidt identity

Manuscript (6.3): `∑_{i,j ≥ 1} λ_i |T_{ij}|² = ∬ |∇_x K(x,y)|² dμ(x) dμ(y) < ∞`
(Lean indices shifted: `λ_{i+1} Tmat i j²`). `∇_x K = b` (weak gradient in the first variable).
-/

open MeasureTheory

namespace SharpLSI

variable {d : ℕ}

/-- (6.3). -/
theorem weighted_hs {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    Integrable (fun p : Torus d × Torus d => sqNorm (bForce W μ p.1 p.2))
      ((μ : Measure (Torus d)).prod (μ : Measure (Torus d))) ∧
    HasSum (fun ij : ℕ × ℕ => lam (ij.1 + 1) * Tmat W μ e ij.1 ij.2 ^ 2)
      (∫ x, ∫ y, sqNorm (bForce W μ x y) ∂(μ : Measure (Torus d)) ∂(μ : Measure (Torus d))) := by
  exact weighted_hs_aux hyp hμ he

end SharpLSI
