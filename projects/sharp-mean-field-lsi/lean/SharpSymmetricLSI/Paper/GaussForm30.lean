import SharpSymmetricLSI.Paper.GaussForm29

/-!
# R32 (G5): diagonalizing variables with Hermite completeness, conditional on Prop. 2.1

`diagXi_of_prop21`: `genXi_of_prop21` together with the completeness clause of
`gaussian_diagonalization`: `F ∈ L²(γ)` orthogonal to all `h_α(ξ)` vanishes `γ`-a.e.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **Diagonalization with Hermite completeness, conditional on Prop. 2.1.** -/
theorem diagXi_of_prop21 (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) (h21 : Prop21Conclusion V W μ)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C) :
    ∃ (v : ℕ → ℕ → ℝ) (ν : ℕ → ℝ) (ξ : ℕ → (ℕ → ℝ) → ℝ),
      (∀ j, Summable (fun i => v j i ^ 2) ∧ Summable (fun i => (lamShift lam i * v j i) ^ 2)) ∧
      (∀ i j, ∑' a, v i a * ∑' b, C a b * v j b = if i = j then 1 else 0) ∧
      (∀ i j, ∑' a, lamShift lam a * v i a * v j a = if i = j then ν i else 0) ∧
      0 < ν 0 ∧ Monotone ν ∧ Tendsto ν atTop atTop ∧
      (∀ j, IsRowVariable v γ j (ξ j)) ∧
      (∀ J : ℕ, γ.map (fun z => fun j : Fin J => ξ j z) =
        Measure.pi (fun _ : Fin J => gaussianReal 0 1)) ∧
      ENNReal.ofReal (ν 0) = lamG (lamShift lam) C ∧
      (∀ F : (ℕ → ℝ) → ℝ, MemLp F 2 γ →
        (∀ α : ℕ →₀ ℕ, ∫ z, F z * hermiteBasis α (fun j => ξ j z) ∂γ = 0) → F =ᵐ[γ] 0) := by
  obtain ⟨v, ν, ξ, hv, hvC, hvΛ, hν0, hmono, htop, hξ, hlaw, hG, hP⟩ :=
    genXi_of_prop21 hyp hμ he h21 hC hγ
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  have hT := Tmat_symm hyp hμ he
  have hS := (hasSum_Tmat_sq hyp hμ he).summable
  have hCs := C_symm_of_secOp hT hS hσ0 hσ hC
  exact ⟨v, ν, ξ, hv, hvC, hvΛ, hν0, hmono, htop, hξ, hlaw, hG, fun F hF horth =>
    hermite_complete_xi hT hS hσ0 hσ hC hCs hγ (fun j => (hv j).1) hvC hξ hP hF horth⟩

end SharpLSI
