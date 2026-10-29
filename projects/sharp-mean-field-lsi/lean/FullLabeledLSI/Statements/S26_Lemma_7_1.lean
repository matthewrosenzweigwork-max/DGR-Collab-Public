import FullLabeledLSI.Defs.F06_Hybrid
import SharpSymmetricLSI.Defs.D07_rStar
import FullLabeledLSI.Paper.Lindeberg8

/-!
# S26: Lemma 7.1 (`lem:Lindeberg`), the joint replacement estimate

Manuscript Lemma 7.1, (7.11), (7.12). Assume (1.2), `r_* > 0` (standing in Sections 6–7); `μ` the
minimizer, `(e, lam)` a reference eigenbasis, `J` the number of feature modes and `J_R ≤ J` the
number of modes in the fluctuation. Fix a spectral level `L` and a bound `B` for `‖F_N‖_{L²(Q_N)}`. For `F_N` given by (7.1) with coefficients `c`
(F6), `F̃_N`, `Z^low_N`, `G_N` as in Section 7:
* (7.12): for `Φ ∈ C_c^∞`, `|E_{Q_N} Φ(F_N, Z^low_N) - E_{Q̃} Φ(F̃_N, G_N)| ≤ C (√δ + n^{-1/2})`,
  with `C` independent of `N`, `δ` and the coefficients.
* (7.11): for continuous `Φ` of polynomial growth, `lim_{δ↓0} limsup_N |…| = 0`, uniformly over
  the coefficients.

Encodings:
* `‖F_N‖_2 ≤ B` is `∑_j c_j² ≤ B²` (the two agree by orthonormality, (7.2)).
* As in the manuscript, `J ≥ J_R` and `Φ : ℝ × ℝ^{J_R} → ℝ`; the fluctuation vectors are the
  first `J_R` components of `Zlow`, `Glow` (`Fin.castLE`), i.e. the modes `1, …, J_R`.
* (7.11) with uniformity: `∀ ε > 0, ∃ δ₀ > 0, ∀ δ ∈ (0, δ₀)`, eventually in `N`, the difference
  is `≤ ε` for every admissible coefficient array. This is the displayed (7.11) together with the
  sentence "the estimate is uniform over the coefficients with the stated norm bound"; the proof
  (moment bounds uniform in `N`, `δ` and the coefficients, then (7.12)) gives it in this form.
* Polynomial growth: `|Φ(p)| ≤ K (1 + ‖p‖)^k`.
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- (7.12): the rate for smooth compactly supported tests. -/
theorem joint_rate {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (J JR : ℕ) (hJ : JR ≤ J) (Φ : ℝ × (Fin JR → ℝ) → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ)
    (L B : ℝ) :
    ∃ C : ℝ, ∀ (N : ℕ) (c : (Fin N → Fin (J + 1)) → ℝ), SpectralCoeff lam L c →
      ∑ j, c j ^ 2 ≤ B ^ 2 → ∀ δ : ℝ, 0 < δ → 0 < lowCount c δ →
        |∫ X, Φ (polyEval e c X, fun m => Zlow e c δ X (Fin.castLE hJ m))
            ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) -
          ∫ w, Φ (hybEval e c δ w, fun m => Glow c δ w (Fin.castLE hJ m))
            ∂hybMeasure (μ : Measure (Torus d)) N J| ≤
        C * (Real.sqrt δ + (Real.sqrt (lowCount c δ))⁻¹) := by
  exact joint_rate_of_moment hd hyp hr μ hμ e lam he J JR hJ
    (hybridPolyMoment_of_min hd hyp hr μ hμ e lam he J) Φ hΦ hΦc L B

/-- (7.11): continuous tests of polynomial growth. -/
theorem joint_replace {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (J JR : ℕ) (hJ : JR ≤ J) (Φ : ℝ × (Fin JR → ℝ) → ℝ) (hΦ : Continuous Φ)
    (hgrowth : ∃ (K : ℝ) (k : ℕ), ∀ p, |Φ p| ≤ K * (1 + ‖p‖) ^ k)
    (L B : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ᶠ N in atTop, ∀ c : (Fin N → Fin (J + 1)) → ℝ, SpectralCoeff lam L c →
        ∑ j, c j ^ 2 ≤ B ^ 2 →
          |∫ X, Φ (polyEval e c X, fun m => Zlow e c δ X (Fin.castLE hJ m))
              ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) -
            ∫ w, Φ (hybEval e c δ w, fun m => Glow c δ w (Fin.castLE hJ m))
              ∂hybMeasure (μ : Measure (Torus d)) N J| ≤ ε := by
  exact joint_replace_of_moment hd hyp hr μ hμ e lam he J JR hJ
    (hybridPolyMoment_of_min hd hyp hr μ hμ e lam he J) Φ hΦ hgrowth L B

end SharpLSI.FL
