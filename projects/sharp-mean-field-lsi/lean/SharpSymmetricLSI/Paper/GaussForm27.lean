import SharpSymmetricLSI.Paper.GaussForm26

/-!
# R32 (G2): the diagonalizing variables `ξ_j` for the paper's data, conditional on Prop. 2.1

`genXi_of_prop21`: in addition to `genEigen_of_prop21`, the row variables `ξ_j = ⟨v_j, z⟩`
(`L²(γ)` limits, `IsRowVariable v γ j (ξ j)`) exist and `(ξ_0, …, ξ_{J-1})` has law `N(0,1)^{⊗J}`
under `γ` for every `J`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **The diagonalizing Gaussian variables, conditional on Prop. 2.1.** -/
theorem genXi_of_prop21 (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
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
      ∀ i, HasSum (fun j => (∑' b, C i b * v j b) ^ 2) (C i i) := by
  obtain ⟨v, ν, hv, hvC, hvΛ, hν0, hmono, htop, hG, hP⟩ := genEigen_of_prop21 hyp hμ he h21 hC
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  have hT := Tmat_symm hyp hμ he
  have hS := (hasSum_Tmat_sq hyp hμ he).summable
  have hCs := C_symm_of_secOp hT hS hσ0 hσ hC
  have hY : ∀ j, ∃ Y, IsRowVariable v γ j Y := fun j =>
    exists_rowVariable hγ hσ0 (quadC_nonneg hT hS hσ0 hσ hC) (quadC_le hT hS hσ0 hσ hC) (hv j).1
  choose ξ hξ using hY
  exact ⟨v, ν, ξ, hv, hvC, hvΛ, hν0, hmono, htop, hξ,
    fun J => map_xi_eq_pi hT hS hσ0 hσ hC hCs hγ (fun j => (hv j).1) hvC hξ J, hG, hP⟩

end SharpLSI
