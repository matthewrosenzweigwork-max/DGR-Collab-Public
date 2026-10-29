import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D16_GaussianLimit
import SharpSymmetricLSI.Paper.ULimit10

/-!
# R26: (6.6)–(6.9), the quadratic fluctuation and its limit

Manuscript (6.6), (6.7), (6.9) (and the existence of `Q_T` in (6.8)). Assume (1.2), `r_* > 0`,
`μ` the minimizer, `(e, λ)` a reference eigenbasis, `T = Tmat`.
* (6.6) `U_N = N^{-1} ∑_{i<j} K(Xᵢ,Xⱼ) + (2N)^{-1} ∑ᵢ K(Xᵢ,Xᵢ)`.
* (6.7) `E_{μ^{⊗N}} |N^{-1} ∑_{i<j} K(Xᵢ,Xⱼ)|² = ((N-1)/(2N)) ‖K‖²_{L²(μ⊗μ)}`.
* (6.8) the second chaos `Q_T` exists (unique in `L²(γ)`).
* (6.9) under `μ^{⊗N}`, `U_N ⇒ U_∞ = ½Q_T + ½d_K` jointly with every fixed collection
  `(Z_{N,1}, …, Z_{N,J})`, whose limit is `(z_1, …, z_J)` under `γ` (Lean coordinates `0..J-1`).
-/

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ}

/-- (6.6), (6.7), (6.8)-existence and (6.9). -/
theorem U_limit {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    (∀ N : ℕ, 1 ≤ N → ∀ X : Config N d, Ucentered W μ N X =
      (N : ℝ)⁻¹ * (∑ i, ∑ j, if i < j then centeredKernel W μ (X i) (X j) else 0) +
        (2 * (N : ℝ))⁻¹ * ∑ i, centeredKernel W μ (X i) (X i)) ∧
    (∀ N : ℕ, 1 ≤ N →
      ∫ X, ((N : ℝ)⁻¹ * ∑ i, ∑ j, if i < j then centeredKernel W μ (X i) (X j) else 0) ^ 2
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
        ((N : ℝ) - 1) / (2 * N) * ∫ x, ∫ y, centeredKernel W μ x y ^ 2
          ∂(μ : Measure (Torus d)) ∂(μ : Measure (Torus d))) ∧
    (∃ Q, IsSecondChaos (Tmat W μ e) Q) ∧
    ∀ Q, IsSecondChaos (Tmat W μ e) Q → ∀ (J : ℕ) (g : ℝ × (Fin J → ℝ) →ᵇ ℝ),
      Tendsto (fun N : ℕ => ∫ X, g (Ucentered W μ N X, fun n => fluct e N n X)
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d)))) atTop
        (𝓝 (∫ z, g (Uinf W μ Q z, fun n => z n) ∂gammaRef)) :=
  U_limit_aux hyp hμ he

end SharpLSI
