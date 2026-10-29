import DGPS.Model.Data
import DGPS.Foundations.Torus

/-!
# LIP032.27: Uniform potential and interaction bounds

Task id: LIP032.27, "Uniform potential and interaction bounds" (node LIP032, contractibility of
the minimizer set; leaf formalization).

Provides:
* `DGPS.Frontier.LIP032.lip032_27_uniform_potential_interaction_bounds`: for every probability
  measure `ν` on the torus `𝕋^d` and bounds `M_V, M_W` for `|A.V|, |A.W|`, the integrands
  `A.V` (against `ν`) and `A.W` (against `ν ⊗ ν`) are integrable, `|∫ A.V dν| ≤ M_V` and
  `|(1/2) ∫ A.W d(ν ⊗ ν)| ≤ M_W / 2`.
* `DGPS.Frontier.LIP032.lip032_27_uniform_potential_interaction_bounds_exists`: such bounds
  `M_V, M_W ≥ 0` exist for every `A : InteractionData d` (the "choose bounds" step of the node).

R5 notes:
* The bounds `M_V, M_W ≥ 0` with `|A.V| ≤ M_V` and `|A.W| ≤ M_W` are chosen in the node text
  ("Choose bounds ..."); they are therefore hypotheses `hV`, `hW` of the main theorem (pointwise
  bounds, for all points), and their existence is proved separately in the `_exists` lemma.
  Nonnegativity of `M_V, M_W` is not needed as a hypothesis (it follows from the pointwise
  bounds on the nonempty torus), so it is not assumed.
* No positive-rate, flow, Lipschitz or gradient hypothesis is used: the statement is purely
  about continuous bounded integrands, and no statement issue arises for this task.
* `ν` is an arbitrary `Measure (Torus d)` with `[IsProbabilityMeasure ν]`; this is the
  underlying measure of a `ProbabilityMeasure (Torus d)`. The product is `ν.prod ν` and `A.W` is
  integrated as the uncurried function `fun p => A.W p.1 p.2`. The factor `1/2` is kept as
  `(1 / 2 : ℝ) * ∫ ...`, exactly as in the source energy; all terms are real.
* Integrability of the bounded continuous integrands is part of the conclusion, as in the
  specification ("the potential integrands are integrable").
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- Continuous real functions on the compact torus are bounded: helper for the `_exists` lemma. -/
theorem exists_abs_bound_LIP03227 {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : X → ℝ) (hf : Continuous f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_range hf.abs).bddAbove
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  exact le_trans (hM ⟨x, rfl⟩) (le_max_left _ _)

/-- Bounded continuous functions are integrable against a probability measure, with the
absolute value of the integral bounded by the sup bound. -/
theorem abs_integral_le_LIP03227 {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (hf : Continuous f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) :
    Integrable f μ ∧ |∫ x, f x ∂μ| ≤ M := by
  have hint : Integrable f μ :=
    Integrable.of_bound hf.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)
  refine ⟨hint, ?_⟩
  have h1 : |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ := by
    simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ) f
  have h2 : ∫ x, |f x| ∂μ ≤ ∫ _x, M ∂μ :=
    integral_mono hint.abs (integrable_const M) hM
  simpa using h1.trans h2

/-- Uniform bounds exist for the continuous potential data. -/
theorem lip032_27_uniform_potential_interaction_bounds_exists (A : InteractionData d) :
    ∃ M_V M_W : ℝ, 0 ≤ M_V ∧ 0 ≤ M_W ∧ (∀ x, |A.V x| ≤ M_V) ∧
      ∀ x y, |A.W x y| ≤ M_W := by
  obtain ⟨MV, hMV0, hMV⟩ := exists_abs_bound_LIP03227 A.V A.V_continuous
  obtain ⟨MW, hMW0, hMW⟩ :=
    exists_abs_bound_LIP03227 (fun p : Torus d × Torus d => A.W p.1 p.2) A.W_continuous
  exact ⟨MV, MW, hMV0, hMW0, hMV, fun x y => hMW (x, y)⟩

/-- LIP032.27: uniform potential and interaction bounds. For every probability `ν` on the
torus, the potential integrands are integrable and
`|∫ A.V dν| ≤ M_V`, `|(1/2) ∫ A.W d(ν ⊗ ν)| ≤ M_W / 2`. -/
theorem lip032_27_uniform_potential_interaction_bounds (A : InteractionData d)
    (M_V M_W : ℝ) (hV : ∀ x, |A.V x| ≤ M_V) (hW : ∀ x y, |A.W x y| ≤ M_W)
    (ν : Measure (Torus d)) [IsProbabilityMeasure ν] :
    Integrable A.V ν ∧
    Integrable (fun p : Torus d × Torus d => A.W p.1 p.2) (ν.prod ν) ∧
    |∫ x, A.V x ∂ν| ≤ M_V ∧
    |(1 / 2 : ℝ) * ∫ p, A.W p.1 p.2 ∂(ν.prod ν)| ≤ M_W / 2 := by
  obtain ⟨h1, h2⟩ := abs_integral_le_LIP03227 ν A.V A.V_continuous M_V hV
  obtain ⟨h3, h4⟩ := abs_integral_le_LIP03227 (ν.prod ν) (fun p : Torus d × Torus d => A.W p.1 p.2)
    A.W_continuous M_W (fun p => hW p.1 p.2)
  refine ⟨h1, h3, h2, ?_⟩
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

end DGPS.Frontier.LIP032
