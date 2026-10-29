import SharpSymmetricLSI.Statements.R25_Lemma_A_2
import SharpSymmetricLSI.Defs.D08_Gibbs
import SharpSymmetricLSI.Paper.ForceApprox13
import SharpSymmetricLSI.Statements.R19_Lemma_5_2

/-!
# R31: (7.11)–(7.12), force approximation for the form limit

Manuscript Section 7.3, (7.11), (7.12). Assume (1.2), `r_* > 0`, `μ` the minimizer, `(e, λ)` a
reference eigenbasis, `K_R` as in (6.4) (`IsKernelApprox`). With
`U_N^{(R)} = N K_R(L_N,L_N)/2`, `b_R = ∇₁K_R`, `b_{Δ,R} = ½∇[K_R(x,x)]`:
* (7.11) `E_{μ^{⊗N}} |∇(U_N - U_N^{(R)})|² = ((N-1)/N) ‖b - b_R‖²_{L²(μ⊗μ)}
  + N^{-1} ‖b_Δ - b_{Δ,R}‖²_{L²(μ)}`;
* (7.12) `lim_{R→∞} limsup_{N→∞} E_{P_N} |∇(U_N - U_N^{(R)})|² = 0` (order of limits as stated).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- `U_N^{(R)} = N K_R(L_N, L_N)/2 = (2N)^{-1} ∑_{i,j} K_R(Xᵢ,Xⱼ)`. -/
noncomputable def Ukernel (K : Torus d → Torus d → ℝ) (N : ℕ) (X : Config N d) : ℝ :=
  1 / (2 * (N : ℝ)) * ∑ i, ∑ j, K (X i) (X j)

/-- (7.11) and (7.12). -/
theorem force_approximation {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {KR : ℕ → Torus d → Torus d → ℝ} (hKR : IsKernelApprox W μ e KR) :
    (∀ R N : ℕ, 1 ≤ N →
      ∫ X, gradSqC (fun Y => Ucentered W μ N Y - Ukernel (KR R) N Y) X
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
        ((N : ℝ) - 1) / N * ∫ x, ∫ y, sqNorm (fun k => bForce W μ x y k - grad1W (KR R) x y k)
            ∂(μ : Measure (Torus d)) ∂(μ : Measure (Torus d)) +
          (N : ℝ)⁻¹ * ∫ x, sqNorm (fun k => bDiag W μ x k -
            weakGrad (fun z => KR R z z / 2) x k) ∂(μ : Measure (Torus d))) ∧
    Tendsto (fun R => limsup (fun N => ∫⁻ X, ENNReal.ofReal
        (gradSqC (fun Y => Ucentered W μ N Y - Ukernel (KR R) N Y) X) ∂gibbs V W N) atTop)
      atTop (𝓝 0) := by
  have hU : ∀ (K : Torus d → Torus d → ℝ) (N : ℕ) (X : Config N d),
      Ukernel K N X = UkernelF K N X := fun _ _ _ => rfl
  simp only [hU]
  obtain ⟨Cp, p, hp, hCp⟩ := reference_entropy hd hyp hr hμ
  exact ⟨fun R N hN => force_identity hd hyp hr hμ he hKR R N hN,
    force_limit_of' hd hyp hr hμ he hKR ⟨Cp, p, hp, fun N hN => (hCp N hN).2.2⟩⟩

end SharpLSI
