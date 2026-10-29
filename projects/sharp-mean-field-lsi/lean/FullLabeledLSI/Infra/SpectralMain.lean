import FullLabeledLSI.Infra.SpectralCutP5
import FullLabeledLSI.Infra.SpectralSetup

/-!
# The cut package from the equilibrium data

For `μ` the minimizer (`Hyp`, `0 < r_*`) and `(e, lam)` any reference eigenbasis of `-L_μ`, the cut
package (manuscript (6.18)-(6.21)) holds for every `N`, every `Ψ ∈ H¹(μ^{⊗N}) ∩ L^s` and the pair
`(S_t Ψ, Π_L S_t Ψ)`, with constants (`a`, `Cu`, `Cl`, the Weyl constant) independent of
`N, s, Bs, t, L, Ψ`.  The standing hypotheses are discharged internally:
* the density bounds `μ ≤ Cu · Haar`, `Haar ≤ Cl · μ` come from the Gibbs form of the minimizer
  (`refSetup`, `GoodDens.le_smul`, `GoodDens.haar_le_smul`);
* the `C¹` representatives, the rate `a`, `λ₀ = 0` and the Weyl growth come from `torus_standing`.

Main result: `cut_package_main`.
-/

open MeasureTheory SharpLSI
open scoped ENNReal

noncomputable section

namespace SharpLSI.FL.Spectral

variable {d : ℕ}

/-- **The cut package for the equilibrium.**  There are `C¹` representatives `eC` of the
eigenfunctions and constants `a, Cu, Cl, c` (independent of `N, s, Bs, t, L, Ψ`) with
`0 < a`, `a ≤ r_LS(μ)`, `μ ≤ Cu · Haar`, `Haar ≤ Cl · μ`, `λ₀ = 0`, Weyl growth `λ_j ≥ c j^{2/d}`,
such that for all `N`, `2 ≤ s`, `0 < t`, `L` and `Ψ ∈ H¹(μ^{⊗N})` with `‖Ψ‖_s ≤ Bs`, the structure
`CutPackage` holds for `(S_t Ψ, Π_L S_t Ψ)`. -/
theorem cut_package_main {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    ∃ (eC : ℕ → Torus d → ℝ) (a Cu Cl c : ℝ),
      0 < a ∧ ENNReal.ofReal a ≤ rLS (μ : Measure (Torus d)) ∧
      (μ : Measure (Torus d)) ≤ ENNReal.ofReal Cu • (volume : Measure (Torus d)) ∧
      (volume : Measure (Torus d)) ≤ ENNReal.ofReal Cl • (μ : Measure (Torus d)) ∧
      (∀ j, Gross.C1T (eC j)) ∧ (∀ j, eC j =ᵐ[(μ : Measure (Torus d))] e j) ∧
      lam 0 = 0 ∧ 0 < c ∧ (∀ j : ℕ, 1 ≤ j → c * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam j) ∧
      ∀ (N : ℕ) {s Bs t : ℝ} (L : ℝ) (Ψ : Config N d → ℝ), 2 ≤ s → 0 < t →
        MemH1C (Q (μ : Measure (Torus d)) N) Ψ →
        MemLp Ψ (ENNReal.ofReal s) (Q (μ : Measure (Torus d)) N) →
        eLpNorm Ψ (ENNReal.ofReal s) (Q (μ : Measure (Torus d)) N) ≤ ENNReal.ofReal Bs →
        CutPackage (μ : Measure (Torus d)) e lam a s Bs t L Ψ (Sfun he t Ψ)
          (Fcut (μ : Measure (Torus d)) e lam t L Ψ) := by
  obtain ⟨ρ, cρ, Cρ, Lσ, hμρ, hρ, -, -⟩ := refSetup hyp hμ
  obtain ⟨eC, a, hac, hca, hC1, hae, ha, hrls, hlam0, -, -, -, ⟨c, hc, hweyl⟩⟩ :=
    Gross.torus_standing hd hyp hr μ hμ e lam he
  have hup : (μ : Measure (Torus d)) ≤ ENNReal.ofReal Cρ • (volume : Measure (Torus d)) := by
    rw [hμρ]; exact hρ.le_smul
  have hlow : (volume : Measure (Torus d)) ≤ ENNReal.ofReal (1 / cρ) • (μ : Measure (Torus d)) := by
    rw [hμρ]; exact hρ.haar_le_smul
  refine ⟨eC, a, Cρ, 1 / cρ, c, ha, hrls, hup, hlow, hC1, hae, hlam0, hc, hweyl, ?_⟩
  intro N s Bs t L Ψ hs ht hH hΨs hBs
  exact cut_package_p5 hup hlow he hC1 hae ha hrls hlam0 hd ⟨c, hc, hweyl⟩ hs ht L hH hΨs hBs

end SharpLSI.FL.Spectral

end
