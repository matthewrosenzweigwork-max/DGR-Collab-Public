import FullLabeledLSI.Defs.F02_Constants
import SharpSymmetricLSI.Statements.R25_Lemma_A_2

/-!
# F5: finite-rank quantities and the comparison expression (4.12)–(4.14), (6.1), (6.5), (6.13), (6.14)

Data of Sections 4.3 and 6: the minimizer `μ`, a reference eigenbasis `(e, lam)` (D16), and the
finite-rank kernels of Lemma A.2 of the symmetric manuscript, `K_R = ∑_{i,j} (T_R)_{ij} e_i ⊗ e_j`
(4.12). Lean indices are shifted as in D16: index `i` stands for the manuscript's mode `i + 1`.
* `FiniteRankApprox W μ e`: index sets `s R`, symmetric coefficients `a R i j = (T_R)_{i+1,j+1}`
  vanishing off `s R × s R` ("extend `T_R` by zero"), and the kernels satisfy `IsKernelApprox` (R25).
* `uR A R z = ½ zᵀ T_R z` (4.14); `URN A R N X = U_{N,R} = u_R(Z_N)` (4.14), `Z_N = fluct e N`.
* `kappaR A R = κ_R = ∫ e^{-u_R} dγ` (6.1) (the determinant formula is a lemma, not the definition).
* `vR A lam R z` (6.13): `¼ (T_R z)ᵀ Λ_R (T_R z) - ½ tr(T_R Λ_R) + ½ zᵀ Λ_R T_R z`.
* `refEnergy μ Ψ = ℰ⁰_N(Ψ) = ∫ |∇Ψ|² dQ_N`, `Q_N = μ^{⊗N}` (6.5).
* `Jexpr … = 𝒥_{N,R}(Ψ)` (6.14), real-valued, with `b_R = bRate μ lam C_R` for a given
  `C_R = (I + T_R)^{-1}` (6.1).
* `InSpectralRange e lam L F`: `F` lies in the range of `Π_{N,L}`, the span of the tensor
  eigenfunctions `∏ᵢ e_{jᵢ}(Xᵢ)` with `∑ᵢ λ_{jᵢ} ≤ L` (Section 6.3, (7.1)); here `lam` and `e` use the
  manuscript's indices (`e 0 = 1`, `lam 0 = 0`).
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- The finite-rank approximations of (4.12)–(4.13) (Lemma A.2 of the symmetric manuscript). -/
structure FiniteRankApprox (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (e : ℕ → Torus d → ℝ) where
  /-- The modes used at rank `R` (shifted indices). -/
  s : ℕ → Finset ℕ
  /-- `a R i j = (T_R)_{i+1, j+1}`. -/
  a : ℕ → ℕ → ℕ → ℝ
  symm : ∀ R i j, a R i j = a R j i
  supp : ∀ R i j, (i ∉ s R ∨ j ∉ s R) → a R i j = 0
  approx : IsKernelApprox W μ e
    (fun R x y => ∑ i ∈ s R, ∑ j ∈ s R, a R i j * e (i + 1) x * e (j + 1) y)

variable {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}

/-- `u_R(z) = ½ zᵀ T_R z` (4.14). -/
noncomputable def uR (A : FiniteRankApprox W μ e) (R : ℕ) (z : ℕ → ℝ) : ℝ :=
  (1 / 2) * ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * z i * z j

/-- `U_{N,R} = u_R(Z_N)` (4.14). -/
noncomputable def URN (A : FiniteRankApprox W μ e) (R N : ℕ) (X : Config N d) : ℝ :=
  uR A R (fun n => fluct e N n X)

/-- `κ_R = ∫ e^{-u_R} dγ` (6.1). -/
noncomputable def kappaR (A : FiniteRankApprox W μ e) (R : ℕ) : ℝ :=
  ∫ z, Real.exp (-uR A R z) ∂gammaRef

/-- `v_R(z) = ¼ (T_R z)ᵀ Λ_R (T_R z) - ½ tr(T_R Λ_R) + ½ zᵀ Λ_R T_R z` (6.13). -/
noncomputable def vR (A : FiniteRankApprox W μ e) (lam : ℕ → ℝ) (R : ℕ) (z : ℕ → ℝ) : ℝ :=
  (1 / 4) * ∑ m ∈ A.s R, lam (m + 1) * (∑ j ∈ A.s R, A.a R m j * z j) ^ 2
    - (1 / 2) * ∑ m ∈ A.s R, A.a R m m * lam (m + 1)
    + (1 / 2) * ∑ i ∈ A.s R, ∑ j ∈ A.s R, z i * lam (i + 1) * A.a R i j * z j

/-- `ℰ⁰_N(Ψ) = ∫ |∇Ψ|² dμ^{⊗N}` (6.5). -/
noncomputable def refEnergy (μ : Measure (Torus d)) {N : ℕ} (Ψ : Config N d → ℝ) : ℝ≥0∞ :=
  ∫⁻ X, ENNReal.ofReal (gradSqC Ψ X) ∂Measure.pi (fun _ : Fin N => μ)

/-- The comparison expression `𝒥_{N,R}(Ψ)` (6.14), with `b_R = min{r_LS(μ), λ_{G,R}}` computed
from a given `C_R = (I + T_R)^{-1}`. -/
noncomputable def Jexpr (A : FiniteRankApprox W μ e) (lam : ℕ → ℝ) (CR : ℕ → ℕ → ℝ) (R : ℕ)
    {N : ℕ} (Ψ : Config N d → ℝ) : ℝ :=
  let Q := Measure.pi (fun _ : Fin N => μ)
  (refEnergy μ Ψ).toReal + ∫ X, Ψ X ^ 2 * vR A lam R (fun n => fluct e N n X) ∂Q
    - (bRate μ lam CR).toReal / 2 *
      ((ent Q (fun X => Ψ X ^ 2)).toReal + ∫ X, Ψ X ^ 2 * URN A R N X ∂Q
        + Real.log (kappaR A R) * ∫ X, Ψ X ^ 2 ∂Q)

/-- `F` is in the range of the spectral projection `Π_{N,L}` (Section 6.3, (7.1)). -/
def InSpectralRange (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (L : ℝ) {N : ℕ}
    (F : Config N d → ℝ) : Prop :=
  ∃ (T : Finset (Fin N → ℕ)) (c : (Fin N → ℕ) → ℝ), (∀ j ∈ T, ∑ i, lam (j i) ≤ L) ∧
    ∀ X, F X = ∑ j ∈ T, c j * ∏ i, e (j i) (X i)

end SharpLSI.FL
