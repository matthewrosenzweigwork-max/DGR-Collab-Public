import FullLabeledLSI.Paper.Lindeberg7
import FullLabeledLSI.Infra.HypercontrHybrid

/-!
# Lemma 7.1, part 9: closing the interface

Lane 3's `Hyb.hybrid_poly_moment_min` is the interface `HybridPolyMoment` of `Paper/Lindeberg1.lean`
(`hybPoly` and `polyB` have the same body). With it the two frozen theorems of S26 follow from
`joint_rate_of_moment` and `joint_replace_of_moment`.
-/

open MeasureTheory

namespace SharpLSI.FL

variable {d : ℕ}

/-- The interface `HybridPolyMoment` holds for the minimizer and every reference eigenbasis. -/
theorem hybridPolyMoment_of_min {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (J : ℕ) : HybridPolyMoment (μ : Measure (Torus d)) e lam J := fun L q =>
  Hyb.hybrid_poly_moment_min hd hyp hr μ hμ e lam he J L q

end SharpLSI.FL
