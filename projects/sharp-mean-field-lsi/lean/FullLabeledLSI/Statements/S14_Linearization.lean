import FullLabeledLSI.Defs.F02_Constants
import SharpSymmetricLSI.Statements.R02_Prop_2_1
import FullLabeledLSI.Paper.Sec8Min6

/-!
# S14: linearization at equilibrium (Section 8.3), (8.9)–(8.11)

Manuscript Section 8.3. Assume (1.2) and `r_* > 0`; `μ = p m` is the equilibrium. For bounded
mean-zero Lipschitz `hₐ`, put `ρₐ = μ(1 + t hₐ)`, `h̄ = ∑ θₐ hₐ`, `ηₐ = hₐ - h̄`. Then as `t → 0`
`G_θ(ρ) = (t²/2)[⟨h̄,(I+T)h̄⟩ + ∑ θₐ ‖ηₐ‖²] + o(t²)` (8.9) and
`D_θ(ρ) = t²[∫|∇((I+T)h̄)|² dμ + ∑ θₐ ∫|∇ηₐ|² dμ] + o(t²)` (8.10), and the infimum of the quadratic
quotients is `min{λ_G, λ_1}` (8.11).

Encodings: `⟨h,(I+T)h⟩ = secondVar W μ h`, `(I+T)h = h + Top W μ h` (D13); `∫|∇g|² dμ = dirichlet μ g`
(finite for the Lipschitz functions involved); the quotient in (8.11) ranges over all finite `q`,
`θₐ > 0` with `∑ θₐ = 1`, and bounded mean-zero Lipschitz `hₐ` with positive denominator, and the
infimum is taken in `ℝ≥0∞`; `λ_G = lamG (lamShift lam) C`, `λ_1 = lam 1` for a reference
eigenbasis `(e, lam)` (D16) and `C = (I+T)^{-1}`. Lipschitz is w.r.t. the product metric of `𝕋^d`.
The expansions are stated with `toReal`; the first conjunct of `linearization_expansions` says that
for small `t ≠ 0` the family is admissible with finite gap and dissipation, so `toReal` loses nothing
(the gap may vanish, e.g. for `h = 0`, so `MsAdmissible` is not claimed).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- An admissible perturbation family for Section 8.3: `q` groups, fractions `θ`, perturbations `h`. -/
def IsLinFamily (μ : Measure (Torus d)) (q : ℕ) (θ : Fin q → ℝ) (h : Fin q → Torus d → ℝ) :
    Prop :=
  (∀ a, 0 < θ a) ∧ ∑ a, θ a = 1 ∧
    ∀ a, (∃ L, LipschitzWith L (h a)) ∧ (∃ B, ∀ x, |h a x| ≤ B) ∧ ∫ x, h a x ∂μ = 0

/-- `h̄ = ∑ₐ θₐ hₐ`. -/
noncomputable def hBar {q : ℕ} (θ : Fin q → ℝ) (h : Fin q → Torus d → ℝ) (x : Torus d) : ℝ :=
  ∑ a, θ a * h a x

/-- The family `ρₐ = p(1 + t hₐ)`. -/
noncomputable def linFamily (p : Torus d → ℝ) {q : ℕ} (θ : Fin q → ℝ)
    (h : Fin q → Torus d → ℝ) (t : ℝ) : Family d :=
  ⟨q, θ, fun a x => p x * (1 + t * h a x)⟩

/-- The quadratic form of (8.9). -/
noncomputable def linGapForm (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) {q : ℕ}
    (θ : Fin q → ℝ) (h : Fin q → Torus d → ℝ) : ℝ :=
  secondVar W μ (hBar θ h) + ∑ a, θ a * ∫ x, (h a x - hBar θ h x) ^ 2 ∂μ

/-- The quadratic form of (8.10). -/
noncomputable def linDissForm (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) {q : ℕ}
    (θ : Fin q → ℝ) (h : Fin q → Torus d → ℝ) : ℝ :=
  (dirichlet μ (fun x => hBar θ h x + Top W μ (hBar θ h) x)).toReal +
    ∑ a, θ a * (dirichlet μ (fun x => h a x - hBar θ h x)).toReal

/-- Section 8.3, (8.9) and (8.10). -/
theorem linearization_expansions {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ) (p : Torus d → ℝ)
    (hp : HasPosLipDensity μ p) {q : ℕ} (θ : Fin q → ℝ) (h : Fin q → Torus d → ℝ)
    (hh : IsLinFamily (μ : Measure (Torus d)) q θ h) :
    (∀ᶠ t in 𝓝[≠] (0 : ℝ), (linFamily p θ h t).Admissible ∧
      msGap V W (linFamily p θ h t) < ⊤ ∧ msDiss V W (linFamily p θ h t) < ⊤) ∧
    Tendsto (fun t : ℝ => (msGap V W (linFamily p θ h t)).toReal / t ^ 2) (𝓝[≠] 0)
        (𝓝 (linGapForm W (μ : Measure (Torus d)) θ h / 2)) ∧
      Tendsto (fun t : ℝ => (msDiss V W (linFamily p θ h t)).toReal / t ^ 2) (𝓝[≠] 0)
        (𝓝 (linDissForm W (μ : Measure (Torus d)) θ h)) := by
  obtain ⟨hθ, hθ1, hrest⟩ := hh
  exact Sec8.lin_expansions hyp hμ θ h hθ hθ1 (fun a => (hrest a).1) (fun a => (hrest a).2.1)
    (fun a => (hrest a).2.2) hp

/-- Section 8.3, (8.11). -/
theorem linearized_minimum {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (C : ℕ → ℕ → ℝ) (hC : IsInverseOfIPlus (Tmat W μ e) C) :
    (⨅ (q : ℕ) (θ : Fin q → ℝ) (h : Fin q → Torus d → ℝ)
        (_ : IsLinFamily (μ : Measure (Torus d)) q θ h ∧
          0 < linGapForm W (μ : Measure (Torus d)) θ h),
        ENNReal.ofReal (linDissForm W (μ : Measure (Torus d)) θ h /
          linGapForm W (μ : Measure (Torus d)) θ h)) =
      min (lamG (lamShift lam) C) (ENNReal.ofReal (lam 1)) := by
  exact Sec8.lin_min hd hyp hr hμ he hC

end SharpLSI.FL
