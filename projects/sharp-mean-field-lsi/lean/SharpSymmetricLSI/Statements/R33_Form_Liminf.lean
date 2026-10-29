import SharpSymmetricLSI.Statements.R04_Prop_2_3
import SharpSymmetricLSI.Paper.TestEnergy9
import SharpSymmetricLSI.Paper.Prop21Conclusion
import SharpSymmetricLSI.Statements.R19_Lemma_5_2
import SharpSymmetricLSI.Paper.FormLiminf12
import SharpSymmetricLSI.Paper.GaussPoincare3

/-!
# R33: Sections 8.3–8.5, cylinder tests, the form lower bound, symmetric Poincaré constants

Manuscript (8.14), (8.18), (8.20), Section 8.5. Assume (1.2), `r_* > 0`, `μ` the minimizer,
`(e, λ)` a reference eigenbasis, `C = (I+T)^{-1}`, `γ_∞` with covariance `C`.
* (8.14), (8.18): for a cylinder `φ`, the particle test `φ_N = φ(Z_{N,1}, …, Z_{N,J})` satisfies
  `ℰ_N(φ_N) → ℰ_∞(φ)`.
* (8.20) and (2.7): the form lower bound along the compact subsequences (this is
  `CompactnessProperty`, R4).
* Section 8.5: `liminf λ_N^sym ≥ λ_G`, `limsup λ_N^sym ≤ λ_G`, hence `λ_N^sym → λ_G` (2.8).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

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

/-- (8.14), (8.18): convergence of the test energies. -/
theorem test_energy_convergence (c : Cyl) :
    Tendsto (fun N => energy V W N (fun X => c.φ (fun i => fluct e N i X))) atTop
      (𝓝 (c.form (lamShift lam) γ)) := by
  obtain ⟨Cp, p, hp, hCp⟩ := reference_entropy hd hyp hr hμ
  exact test_energy_convergence_of hd hyp hr
    (prop21Conclusion_of_equilibrium (prop_equilibrium hd hyp hr) hμ) he hC hγ
    ⟨Cp, p, hp, fun N hN => ⟨(hCp N hN).2.1, (hCp N hN).2.2⟩⟩ c

/-- (8.20), (2.6)–(2.7): the form lower bound along compact subsequences. -/
theorem form_liminf : CompactnessProperty V W γ (gaussForm (lamShift lam) γ) :=
  form_liminf_of hd hyp hr hμ he hC hγ

/-- Section 8.5: convergence of the symmetric Poincaré constants. -/
theorem lamSym_tendsto :
    lamG (lamShift lam) C ≤ liminf (fun N => lamSym V W N) atTop ∧
    limsup (fun N => lamSym V W N) atTop ≤ lamG (lamShift lam) C ∧
    Tendsto (fun N => lamSym V W N) atTop (𝓝 (lamG (lamShift lam) C)) :=
  lamSym_tendsto_of'' hd hyp hr hμ he hC hγ (form_liminf_of hd hyp hr hμ he hC hγ)

end

end SharpLSI
