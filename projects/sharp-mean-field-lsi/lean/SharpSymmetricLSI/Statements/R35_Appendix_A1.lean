import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Infra.Heat
import SharpSymmetricLSI.Paper.AppASemiconvex
import SharpSymmetricLSI.Paper.AppAFisher3
import SharpSymmetricLSI.Paper.AppARStar4

/-!
# R35: Appendix A.1, semiconvex potentials and admissible mean-field tests

Manuscript Appendix A.1 and (A.1).
* A finite periodic function with distributional `D²u ≥ -K I` has a bounded Lipschitz
  representative (unique among continuous representatives). Stated on any torus `𝕋^ι`
  (applies to `V` on `𝕋^d` and `W` on `𝕋^{2d}`). The hypothesis is the a.e./distributional one:
  `u` locally integrable on the lift, tested as in (1.2).
* (A.1) heat-kernel Cauchy–Schwarz: `|∇e^{tΔ}ρ|²/e^{tΔ}ρ ≤ 4e^{tΔ}(|∇√ρ|²)` and
  `I(ρ_t|m) ≤ I(ρ|m)`.
* The infimum (1.7) is unchanged when restricted to smooth positive densities; for admissible
  `ρ`, the heat approximations `ρ_t = e^{tΔ}ρ` are smooth and positive, admissible for small `t`,
  and `D(ρ_t) → D(ρ)`, `G(ρ_t) → G(ρ)` as `t ↓ 0`.
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

namespace SharpLSI

/-- Appendix A.1: semiconvex functions have bounded Lipschitz representatives. -/
theorem semiconvex_lipschitz {ι : Type*} [Fintype ι] [DecidableEq ι] {u : UnitAddTorus ι → ℝ}
    {K : ℝ} (hloc : LocallyIntegrable (u ∘ liftT))
    (hsc : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
      ∀ ξ : ι → ℝ, -K * (∑ k, ξ k ^ 2) * ∫ x, φ x ≤ ∫ x, u (liftT x) * secondDirDeriv φ ξ x) :
    ∃ v : UnitAddTorus ι → ℝ, (∃ L, LipschitzWith L v) ∧ (∃ B, ∀ x, |v x| ≤ B) ∧
      v =ᵐ[volume] u ∧ ∀ w : UnitAddTorus ι → ℝ, Continuous w → w =ᵐ[volume] u → w = v := by
  exact semiconvex_lipschitz_aux hloc hsc

variable {d : ℕ}

/-- (A.1): heat-kernel Cauchy–Schwarz and monotonicity of the Fisher information. -/
theorem heat_fisher {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1)
    (hρ : MemH1 (haar d) (fun x => Real.sqrt (ρ x))) {t : ℝ} (ht : 0 < t) :
    (∀ᵐ x ∂haar d, sqNorm (weakGrad (heatT t ρ) x) / heatT t ρ x ≤
      4 * heatT t (fun y => sqNorm (weakGrad (fun z => Real.sqrt (ρ z)) y)) x) ∧
    fisherInfo (densMeasure (heatT t ρ)) (haar d) ≤ fisherInfo (densMeasure ρ) (haar d) := by
  exact heat_fisher_aux hρ0 hρ1 hρ ht

/-- Appendix A.1: restriction of (1.7) to smooth positive densities, and heat approximation. -/
theorem rStar_smooth_approx {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) :
    rStar V W = ⨅ ρ ∈ {ρ | Admissible V W ρ ∧ IsSmoothT ρ ∧ ∀ x, 0 < ρ x},
      dissipation V W ρ / (2 * (gap V W (densMeasure ρ)).toENNReal) ∧
    ∀ ρ, Admissible V W ρ →
      (∀ t : ℝ, 0 < t → IsSmoothT (heatT t ρ) ∧ ∀ x, 0 < heatT t ρ x) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), Admissible V W (heatT t ρ)) ∧
      Tendsto (fun t => dissipation V W (heatT t ρ)) (𝓝[>] 0) (𝓝 (dissipation V W ρ)) ∧
      Tendsto (fun t => gap V W (densMeasure (heatT t ρ))) (𝓝[>] 0)
        (𝓝 (gap V W (densMeasure ρ))) := by
  exact rStar_smooth_approx_aux hyp

end SharpLSI
