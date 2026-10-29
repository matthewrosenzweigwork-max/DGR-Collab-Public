import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D17_Occupation
import SharpSymmetricLSI.Paper.Occ15

/-!
# R28: Section 7.1, the occupation basis and its Gaussian limit

Manuscript Section 7.1, (7.1)–(7.3). Assume (1.2), `r_* > 0`, `μ` the minimizer, `(e, λ)` a
reference eigenbasis.
* For `|α| ≤ N` the `B_{α,N}` are symmetric, in `H^1(μ^{⊗N})`, orthonormal in `L²(μ^{⊗N})`, with
  Dirichlet matrix `∫ ∇B_α·∇B_β dμ^{⊗N} = Λ_α δ_{αβ}`, and they span the symmetric subspace.
* The `h_α` form an orthonormal basis of `L²(γ)`.
* For every finite set `A` of occupations and every `J`, `(B_{α,N})_{α∈A}` and
  `(Z_{N,1..J})` converge jointly in law under `μ^{⊗N}` to `(h_α)_{α∈A}`, `(z_1..z_J)` under `γ`;
  every fixed moment of every fixed `B_{α,N}` is bounded uniformly in `N`.
-/

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ}

/-- Section 7.1. -/
theorem occupation_basis {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    (∀ N : ℕ, ∀ α β : ℕ →₀ ℕ, occSize α ≤ N → occSize β ≤ N →
      IsSymmetric (occBasis e α N) ∧
      MemH1C (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) (occBasis e α N) ∧
      ∫ X, occBasis e α N X * occBasis e β N X
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) = (if α = β then 1 else 0) ∧
      ∫ X, ∑ i, ∑ k, weakGradC (occBasis e α N) X i k * weakGradC (occBasis e β N) X i k
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
        (if α = β then occEnergy lam α else 0)) ∧
    (∀ N : ℕ, ∀ f : Config N d → ℝ,
      MemLp f 2 (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) → IsSymmetric f →
      (∀ α : ℕ →₀ ℕ, occSize α ≤ N → ∫ X, f X * occBasis e α N X
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) = 0) →
      f =ᵐ[Measure.pi fun _ : Fin N => (μ : Measure (Torus d))] 0) ∧
    (∀ α β : ℕ →₀ ℕ, ∫ z, hermiteBasis α z * hermiteBasis β z ∂gammaRef =
      if α = β then 1 else 0) ∧
    (∀ F : (ℕ → ℝ) → ℝ, MemLp F 2 gammaRef → (∀ α, ∫ z, F z * hermiteBasis α z ∂gammaRef = 0) →
      F =ᵐ[gammaRef] 0) ∧
    (∀ (A : Finset (ℕ →₀ ℕ)) (J : ℕ) (g : (A → ℝ) × (Fin J → ℝ) →ᵇ ℝ),
      Tendsto (fun N : ℕ => ∫ X, g (fun α => occBasis e α N X, fun n => fluct e N n X)
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d)))) atTop
        (𝓝 (∫ z, g (fun α => hermiteBasis α z, fun n => z n) ∂gammaRef))) ∧
    ∀ (α : ℕ →₀ ℕ) (p : ℕ), ∃ C : ℝ, ∀ N : ℕ, occSize α ≤ N →
      ∫ X, |occBasis e α N X| ^ p ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ C :=
  occupation_basis_aux hyp hμ he

end SharpLSI
