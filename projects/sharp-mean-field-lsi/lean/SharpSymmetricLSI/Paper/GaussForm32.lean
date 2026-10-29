import SharpSymmetricLSI.Paper.GaussForm30
import SharpSymmetricLSI.Paper.GaussFormClause6

/-!
# R32 (G6): the diagonalization of the Gaussian form, conditional on Prop. 2.1

`gaussian_diagonalization_of_prop21`: the conclusion of the frozen `gaussian_diagonalization`,
assembled from `genXi_of_prop21` (spectral data, `ξ_j`, their law, `C_{ii} = ∑_j (Cv_j)_i²`),
`hermite_complete_xi` (Hermite completeness) and `form_clause_xi` (the form of `F(ξ)`,
`Paper/GaussFormClause6.lean`, lane s42).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ContDiff

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **(8.4)–(8.7), (8.9), conditional on Prop. 2.1.** -/
theorem gaussian_diagonalization_of_prop21 (hyp : Hyp V W KV KW)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) {e : ℕ → Torus d → ℝ}
    {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (h21 : Prop21Conclusion V W μ) {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C) :
    ∃ (v : ℕ → ℕ → ℝ) (ν : ℕ → ℝ) (ξ : ℕ → (ℕ → ℝ) → ℝ),
      (∀ j, Summable (fun i => v j i ^ 2) ∧ Summable (fun i => (lamShift lam i * v j i) ^ 2)) ∧
      (∀ i j, ∑' a, v i a * ∑' b, C a b * v j b = if i = j then 1 else 0) ∧
      0 < ν 0 ∧ Monotone ν ∧ Tendsto ν atTop atTop ∧
      (∀ j, IsRowVariable v γ j (ξ j)) ∧
      (∀ J : ℕ, γ.map (fun z => fun j : Fin J => ξ j z) =
        Measure.pi (fun _ : Fin J => ProbabilityTheory.gaussianReal 0 1)) ∧
      (∀ (J : ℕ) (F : (Fin J → ℝ) → ℝ), ContDiff ℝ ∞ F → HasCompactSupport F →
        gaussForm (lamShift lam) γ (fun z => F (fun j => ξ j z)) =
          ∫⁻ z, ENNReal.ofReal (∑ j : Fin J, ν j *
            (fderiv ℝ F (fun i => ξ i z) (Pi.single j 1)) ^ 2) ∂γ) ∧
      ENNReal.ofReal (ν 0) = lamG (lamShift lam) C ∧
      (∀ F : (ℕ → ℝ) → ℝ, MemLp F 2 γ →
        (∀ α : ℕ →₀ ℕ, ∫ z, F z * hermiteBasis α (fun j => ξ j z) ∂γ = 0) → F =ᵐ[γ] 0) := by
  obtain ⟨v, ν, ξ, hv, hvC, hvΛ, hν0, hmono, htop, hξ, hlaw, hG, hP⟩ :=
    genXi_of_prop21 hyp hμ he h21 hC hγ
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  have hT := Tmat_symm hyp hμ he
  have hS := (hasSum_Tmat_sq hyp hμ he).summable
  have hCs := C_symm_of_secOp hT hS hσ0 hσ hC
  exact ⟨v, ν, ξ, hv, hvC, hν0, hmono, htop, hξ, hlaw,
    fun J F hF hFc => form_clause_xi hyp hμ he h21 hC hγ hv hvC hvΛ hξ hP J F hF hFc, hG,
    fun F hF horth =>
      hermite_complete_xi hT hS hσ0 hσ hC hCs hγ (fun j => (hv j).1) hvC hξ hP hF horth⟩

end SharpLSI
