import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D17_Occupation
import SharpSymmetricLSI.Paper.R29Main

/-!
# R29: Lemma 7.1 (`lem:reference-compactness`), compactness under the product reference

Manuscript Lemma 7.1, (7.4), (7.5). Assume (1.2), `r_* > 0`, `μ` the minimizer, `(e, λ)` a
reference eigenbasis. Let `N_k → ∞` and `Ψ_k` symmetric in `H^1(μ^{⊗N_k})` with
`sup_k (‖Ψ_k‖² + ∫|∇Ψ_k|²) < ∞` (7.4). After extraction there is `Ψ ∈ L²(γ)` such that the
occupation coefficients `c_{α,k} = ⟨Ψ_k, B_{α,N_k}⟩` (padded by `0` for `|α| > N_k`, automatic
since `B_{α,N} = 0` there) converge in `ℓ²` to the Hermite coefficients `⟨Ψ, h_α⟩_γ`; the
squared norms converge; `Ψ_k`, `U_{N_k}` and every fixed collection of fluctuations converge
jointly in law to `Ψ`, `U_∞`, and the Gaussian coordinates; and `Ψ_k²` is uniformly integrable.
-/

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- Lemma 7.1. -/
theorem reference_compactness {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop) (Ψ : (k : ℕ) → Config (Ns k) d → ℝ)
    (hΨ : ∀ k, IsSymmetric (Ψ k) ∧
      MemH1C (Measure.pi fun _ : Fin (Ns k) => (μ : Measure (Torus d))) (Ψ k))
    (hB : ∃ B : NNReal, ∀ k, ∫⁻ X, ENNReal.ofReal (Ψ k X ^ 2 + gradSqC (Ψ k) X)
      ∂Measure.pi (fun _ : Fin (Ns k) => (μ : Measure (Torus d))) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ψinf : (ℕ → ℝ) → ℝ, MemLp Ψinf 2 gammaRef ∧
      Tendsto (fun k => ∑' α : ℕ →₀ ℕ, ENNReal.ofReal
          ((∫ X, Ψ (φ k) X * occBasis e α (Ns (φ k)) X
              ∂Measure.pi (fun _ : Fin (Ns (φ k)) => (μ : Measure (Torus d))) -
            ∫ z, Ψinf z * hermiteBasis α z ∂gammaRef) ^ 2)) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ X, Ψ (φ k) X ^ 2
          ∂Measure.pi (fun _ : Fin (Ns (φ k)) => (μ : Measure (Torus d)))) atTop
        (𝓝 (∫ z, Ψinf z ^ 2 ∂gammaRef)) ∧
      (∀ Q, IsSecondChaos (Tmat W μ e) Q → ∀ (J : ℕ) (g : ℝ × ℝ × (Fin J → ℝ) →ᵇ ℝ),
        Tendsto (fun k => ∫ X, g (Ψ (φ k) X, Ucentered W μ (Ns (φ k)) X,
            fun n => fluct e (Ns (φ k)) n X)
            ∂Measure.pi (fun _ : Fin (Ns (φ k)) => (μ : Measure (Torus d)))) atTop
          (𝓝 (∫ z, g (Ψinf z, Uinf W μ Q z, fun n => z n) ∂gammaRef))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ k,
        ∫⁻ X in {X | M < Ψ (φ k) X ^ 2}, ENNReal.ofReal (Ψ (φ k) X ^ 2)
          ∂Measure.pi (fun _ : Fin (Ns (φ k)) => (μ : Measure (Torus d))) ≤ ENNReal.ofReal ε :=
  reference_compactness_aux hyp hμ he Ns hNs Ψ hΨ hB

end SharpLSI
