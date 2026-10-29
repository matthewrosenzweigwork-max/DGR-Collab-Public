import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D18_GaussianForm
import SharpSymmetricLSI.Paper.GaussForm16

/-!
# D18 sanity lemmas: `gaussForm` is the closure of (8.1)

In the setting of Proposition 2.3 (minimizer `μ`, reference eigenbasis, `C = (I+T)^{-1}`,
`γ_∞` with covariance `C`):
* `gaussForm_eq_on_cyl`: the relaxation agrees with (8.1) on every cylinder function. This is
  exactly closability of (8.1) (manuscript Section 8.1, R32): for a closable form the
  lower-semicontinuous relaxation is its closure and extends it.
* `gaussForm_quadratic`: `gaussForm` is a quadratic form on its finite domain (homogeneity and
  the parallelogram identity).
-/

open MeasureTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- Closability of (8.1): `ℰ_∞(φ) = ∫ ∑ λ_j |∂_jφ|² dγ_∞` for every cylinder `φ`. -/
theorem gaussForm_eq_on_cyl {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C) (c : Cyl) :
    gaussForm (lamShift lam) γ c.eval = c.form (lamShift lam) γ := by
  exact gaussForm_eq_on_cyl_of_prop21 hyp hμ he
    (prop21Conclusion_of_equilibrium (prop_equilibrium hd hyp hr) hμ) hC hγ c

/-- `ℰ_∞` is a quadratic form on its finite domain. -/
theorem gaussForm_quadratic {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C) :
    (∀ (a : ℝ) (f : (ℕ → ℝ) → ℝ),
      gaussForm (lamShift lam) γ (fun z => a * f z) =
        ENNReal.ofReal (a ^ 2) * gaussForm (lamShift lam) γ f) ∧
    ∀ f g : (ℕ → ℝ) → ℝ, gaussForm (lamShift lam) γ f < ⊤ → gaussForm (lamShift lam) γ g < ⊤ →
      gaussForm (lamShift lam) γ (fun z => f z + g z) < ⊤ ∧
      gaussForm (lamShift lam) γ (fun z => f z + g z) +
          gaussForm (lamShift lam) γ (fun z => f z - g z) =
        2 * gaussForm (lamShift lam) γ f + 2 * gaussForm (lamShift lam) γ g := by
  have := hγ.1
  have hlam : ∀ i, 0 ≤ lamShift lam i := fun i => he.lam_nonneg' (i + 1)
  exact ⟨fun a f => gaussForm_smul hlam a f, fun f g hf hg => gaussForm_parallelogram hlam hf hg⟩

end SharpLSI
