import SharpSymmetricLSI.Paper.GaussForm24
import SharpSymmetricLSI.Paper.RefSpec1

/-!
# R32 (F6): the diagonalization of `(Λ, C)` for the paper's data, conditional on Prop. 2.1

`genEigen_of_prop21`: for the minimizer `μ`, a reference eigenbasis `(e, λ)`, `λ' = lamShift λ`,
`T = Tmat W μ e` and `C = (I+T)⁻¹`, assuming `Prop21Conclusion` (R02, still open; used only
through `secOp_ge_of_prop21`): the vectors `v_j` with `v_j, Λv_j ∈ ℓ²`, `⟨v_i, C v_j⟩ = δ_{ij}`,
`⟨v_i, Λ v_j⟩ = ν_i δ_{ij}`, `0 < ν_0 ≤ ν_1 ≤ … → ∞` and `λ_G = ν_0`. `λ'_i > 0` and `λ'_i → ∞`
come from `exists_lam_lower` and `tendsto_lam_ref` (`Paper/RefSpec1.lean`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **Diagonalization of `(Λ, C)` and `λ_G = ν_0`, conditional on Prop. 2.1.** -/
theorem genEigen_of_prop21 (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) (h21 : Prop21Conclusion V W μ)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C) :
    ∃ (v : ℕ → ℕ → ℝ) (ν : ℕ → ℝ),
      (∀ j, Summable (fun i => v j i ^ 2) ∧ Summable (fun i => (lamShift lam i * v j i) ^ 2)) ∧
      (∀ i j, ∑' a, v i a * ∑' b, C a b * v j b = if i = j then 1 else 0) ∧
      (∀ i j, ∑' a, lamShift lam a * v i a * v j a = if i = j then ν i else 0) ∧
      0 < ν 0 ∧ Monotone ν ∧ Tendsto ν atTop atTop ∧
      ENNReal.ofReal (ν 0) = lamG (lamShift lam) C ∧
      ∀ i, HasSum (fun j => (∑' b, C i b * v j b) ^ 2) (C i i) := by
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  have hT := Tmat_symm hyp hμ he
  have hS := (hasSum_Tmat_sq hyp hμ he).summable
  have hCs := C_symm_of_secOp hT hS hσ0 hσ hC
  obtain ⟨c, hc0, hc⟩ := exists_lam_lower hyp hμ he
  have hpos : ∀ i, 0 < lamShift lam i := fun i => lt_of_lt_of_le hc0 (hc (i + 1) (by omega))
  have htop : Tendsto (lamShift lam) atTop atTop :=
    (tendsto_lam_ref hyp hμ he).comp (tendsto_add_atTop_nat 1)
  exact exists_genEigen_matrix hT hS hσ0 hσ hpos hC hCs htop

end SharpLSI
