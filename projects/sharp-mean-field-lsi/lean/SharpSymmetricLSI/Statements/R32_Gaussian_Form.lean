import SharpSymmetricLSI.Defs.D18_Sanity
import SharpSymmetricLSI.Defs.D17_Occupation
import SharpSymmetricLSI.Infra.Entropy
import SharpSymmetricLSI.Paper.GaussLSI6
import SharpSymmetricLSI.Paper.GaussForm32
import SharpSymmetricLSI.Paper.FormDuality7

/-!
# R32: Sections 8.1–8.2, the Gaussian form, its diagonalization and the constant `λ_G`

Manuscript (8.1)–(8.13). Assume (1.2), `r_* > 0`, `μ` the minimizer, `(e, λ)` a reference
eigenbasis, `C = (I+T)^{-1}`, `γ_∞` centered Gaussian with covariance `C`, `ℰ_∞ = gaussForm`.
* closability of (8.1) (`gaussForm_eq_on_cyl`, D18) restated as `gaussian_form`;
* diagonalization (8.4)–(8.7): there are `v_j ∈ D(Λ)` with `⟨v_i, C v_j⟩ = δ_{ij}` and
  `0 < ν_1 ≤ ν_2 ≤ … → ∞` such that `ξ_j = ⟨v_j, z⟩` (`L²(γ_∞)` limits) are i.i.d. `N(0,1)` under
  `γ_∞`, the form of a cylinder function of finitely many `ξ`'s is `∫ ∑ ν_j |∂_{ξ_j} F|² dγ_∞`,
  `ν_1 = λ_G` (8.9), and the family is complete: the `ξ_j` generate the Gaussian σ-algebra, i.e.
  the Hermite products `h_α(ξ)` are complete in `L²(γ_∞)` (TeX lines 1613, 1622). Lean indices shifted (`ν 0 = ν_1`). The operator core (generator
  closure on cylinder functions) is a proof step; its stated consequence is (8.8).
* (8.8) duality: `ℰ_∞(f) = sup_φ (2∫ f(-L_∞φ) dγ_∞ - ℰ_∞(φ))` over compactly supported smooth
  cylinders, for `f ∈ L²(γ_∞)` (both sides may be `⊤`; stated in `EReal`), with the row
  variables `(Tz)_i` as `L²(γ_∞)` limits;
* (8.9) `λ_G > 0`; (8.10) Gaussian LSI and Poincaré with constant `λ_G`; (8.13) `r_* ≤ λ_G`.
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

namespace SharpLSI

variable {d : ℕ}

section
variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
include hd hyp hr hμ he hC hγ

/-- Section 8.1: (8.1) is closable; `ℰ_∞` extends it. -/
theorem gaussian_form (c : Cyl) : gaussForm (lamShift lam) γ c.eval = c.form (lamShift lam) γ := by
  exact gaussForm_eq_on_cyl hd hyp hr hμ he hC hγ c

/-- (8.4)–(8.7), (8.9): diagonalization of the Gaussian form. -/
theorem gaussian_diagonalization :
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
  exact gaussian_diagonalization_of_prop21 hyp hμ he
    (prop21Conclusion_of_equilibrium (prop_equilibrium hd hyp hr) hμ) hC hγ

/-- (8.8): form duality. -/
theorem form_duality {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable (Tmat W μ e) γ i (Y i))
    {f : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 γ) :
    (gaussForm (lamShift lam) γ f : EReal) =
      ⨆ c : Cyl, ((2 * ∫ z, f z * (-(c.gen (lamShift lam) Y z)) ∂γ : ℝ) : EReal) -
        (c.form (lamShift lam) γ : EReal) := by
  exact form_duality_of_prop21 hyp hμ he
    (prop21Conclusion_of_equilibrium (prop_equilibrium hd hyp hr) hμ) hC hγ hY hf

/-- (8.9) positivity, (8.10) Gaussian LSI and Poincaré, (8.13) `r_* ≤ λ_G`. -/
theorem gaussian_lsi :
    0 < lamG (lamShift lam) C ∧ lamG (lamShift lam) C < ⊤ ∧
    (∀ f : (ℕ → ℝ) → ℝ, MemLp f 2 γ →
      ent γ (fun z => f z ^ 2) ≤ 2 / lamG (lamShift lam) C * gaussForm (lamShift lam) γ f ∧
      var γ f ≤ gaussForm (lamShift lam) γ f / lamG (lamShift lam) C) ∧
    rStar V W ≤ lamG (lamShift lam) C := by
  exact gaussian_lsi_of_prop21 hd hyp hr hμ he hC hγ

end

end SharpLSI
