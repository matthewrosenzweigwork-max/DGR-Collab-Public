import DGPS.Frontier.LIP032.T34
import DGPS.Foundations.Torus
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# LIP032.39: Lipschitz tests determine probabilities

Task id and title: LIP032.39, "Lipschitz tests determine probabilities" (node LIP032,
contractibility of the minimizer set; leaf formalization). No positive-rate or flow hypothesis is
used here, so the defect FD-001 of the isolated frozen LIP032 sentence is not touched by this unit.

## Provides
* `DGPS.Frontier.LIP032.lip032_39_lipschitz_tests_determine_probabilities` : two Borel
  probability measures `lam`, `eta` on the torus `Torus d` whose integrals agree for every
  real test that is `1`-Lipschitz for the Euclidean quotient distance (`DGPS.TorusLipschitzWith 1`)
  are equal.
* `DGPS.Frontier.LIP032.lip032_39_lipschitz_tests_determine_probabilities_metric` : the same
  statement on a general compact metric space with Borel sigma-algebra, with `LipschitzWith 1`
  tests for the ambient metric.
* `DGPS.Frontier.LIP032.lip032_39_lipschitz_tests_determine_probabilities_continuous` : under the
  same hypothesis on a compact metric space, the integrals of every continuous real test agree.

## R5 notes
* Ambient space. The specification says `X` is the torus with its Euclidean quotient metric. The
  main theorem is on `DGPS.Torus d` and its one-Lipschitz tests are `TorusLipschitzWith 1`, the
  campaign predicate for the Euclidean quotient distance `torusDist`. The ambient `dist` of
  `Torus d` is the sup metric, which is at most `torusDist`, so every `LipschitzWith 1` test is a
  `TorusLipschitzWith 1` test. The argument is therefore run once on a general compact metric
  space (`_metric`), and the torus theorem follows by this inclusion. The torus hypothesis (all
  `TorusLipschitzWith 1` tests) is the faithful reading; the `_metric` form with fewer tests is
  the stronger conclusion used internally.
* "Probabilities" are `Measure X` with `IsProbabilityMeasure`, with `BorelSpace`. Nonemptiness of
  `X` is derived from the existence of a probability measure and is not a hypothesis.
* "Equal integrals for every one-Lipschitz real test" is `∫ φ ∂lam = ∫ φ ∂eta` for every
  `φ : X → ℝ` that is `1`-Lipschitz. Such a `φ` is continuous on the compact space, hence
  integrable for both finite measures; integrability is not assumed.
* The spec splits Lipschitz constants into positive and zero cases. Here a `K`-Lipschitz function
  is rescaled by `(max K 1)⁻¹`, which handles both cases at once; equality of the masses of the
  two probabilities is used through `∫ c = c` for constants.
* LIP032.34 supplies the approximation (`_exists` form with `M = ‖φ‖∞`); the Lipschitz property
  of `a_L` comes from LIP032.33 via the `_sup` form.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

section Metric

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] [BorelSpace X] in
/-- A function that is `K`-Lipschitz has the same integral under `lam` and `eta` once all
`1`-Lipschitz tests do. -/
theorem integral_eq_of_lipschitzWith_LIP03239 {lam eta : Measure X}
    (h : ∀ φ : X → ℝ, LipschitzWith 1 φ → ∫ x, φ x ∂lam = ∫ x, φ x ∂eta)
    {K : NNReal} {φ : X → ℝ} (hφ : LipschitzWith K φ) :
    ∫ x, φ x ∂lam = ∫ x, φ x ∂eta := by
  have hK : (0 : ℝ) < (max K 1 : NNReal) := by
    have : (1 : NNReal) ≤ max K 1 := le_max_right _ _
    exact lt_of_lt_of_le one_pos (by exact_mod_cast this)
  set c : ℝ := ((max K 1 : NNReal) : ℝ)⁻¹ with hc
  have hc0 : c ≠ 0 := by positivity
  have hψ : LipschitzWith 1 (fun x => c * φ x) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h1 : dist (φ x) (φ y) ≤ K * dist x y := hφ.dist_le_mul x y
    have h2 : (K : ℝ) ≤ (max K 1 : NNReal) := by exact_mod_cast le_max_left K 1
    have h3 : dist (c * φ x) (c * φ y) = c * dist (φ x) (φ y) := by
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < c)]
    rw [h3]
    have h4 : c * ((max K 1 : NNReal) : ℝ) = 1 := by rw [hc]; field_simp
    calc c * dist (φ x) (φ y) ≤ c * (K * dist x y) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ c * ((max K 1 : NNReal) * dist x y) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 dist_nonneg) (by positivity)
      _ = ((1 : NNReal) : ℝ) * dist x y := by rw [← mul_assoc, h4]; simp
  have := h _ hψ
  rw [integral_const_mul, integral_const_mul] at this
  exact mul_left_cancel₀ hc0 this

/-- Probabilities that agree on all `1`-Lipschitz tests agree on all continuous real tests. -/
theorem lip032_39_lipschitz_tests_determine_probabilities_continuous
    {lam eta : Measure X} [IsProbabilityMeasure lam] [IsProbabilityMeasure eta]
    (h : ∀ φ : X → ℝ, LipschitzWith 1 φ → ∫ x, φ x ∂lam = ∫ x, φ x ∂eta)
    {ψ : X → ℝ} (hψ : Continuous ψ) :
    ∫ x, ψ x ∂lam = ∫ x, ψ x ∂eta := by
  have : Nonempty X := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := measure_univ (μ := lam)
    rw [Subsingleton.elim (Set.univ : Set X) ∅] at this
    simp at this
  have hint : ∀ f : X → ℝ, Continuous f → ∀ μ : Measure X, [IsFiniteMeasure μ] →
      Integrable f μ := fun f hf μ _ =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have key : ∀ ε : ℝ, 0 < ε → |(∫ x, ψ x ∂lam) - ∫ x, ψ x ∂eta| ≤ 2 * ε := by
    intro ε hε
    obtain ⟨δ, hδ, hcont, -, -, -⟩ := lip032_34_uniform_lipschitz_approximation_bound_exists hψ hε
    obtain ⟨ha, hlip, hnorm⟩ := lip032_34_uniform_lipschitz_approximation_bound_sup hψ hδ hcont
    set a := infConv_LIP03233 ψ ((2 * ‖(⟨ψ, hψ⟩ : C(X, ℝ))‖ + ε) / δ) with ha_def
    have hpt : ∀ x, |a x - ψ x| ≤ ε := fun x => by
      have := ContinuousMap.norm_coe_le_norm
        ((⟨a, ha⟩ : C(X, ℝ)) - ⟨ψ, hψ⟩) x
      exact (by simpa using this : |a x - ψ x| ≤ _).trans hnorm
    have hbound : ∀ μ : Measure X, IsProbabilityMeasure μ →
        |(∫ x, ψ x ∂μ) - ∫ x, a x ∂μ| ≤ ε := by
      intro μ _
      have hs : (∫ x, ψ x ∂μ) - ∫ x, a x ∂μ = ∫ x, (ψ x - a x) ∂μ :=
        (integral_sub (hint ψ hψ μ) (hint a ha μ)).symm
      rw [hs, ← Real.norm_eq_abs]
      have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => ψ x - a x) (C := ε)
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_sub_comm]; exact hpt x)
      simpa using this
    have hl := hbound lam inferInstance
    have he := hbound eta inferInstance
    have heq := integral_eq_of_lipschitzWith_LIP03239 h hlip
    have : (∫ x, ψ x ∂lam) - ∫ x, ψ x ∂eta
        = ((∫ x, ψ x ∂lam) - ∫ x, a x ∂lam) - ((∫ x, ψ x ∂eta) - ∫ x, a x ∂eta) := by
      rw [heq]; ring
    rw [this]
    calc _ ≤ |(∫ x, ψ x ∂lam) - ∫ x, a x ∂lam| + |(∫ x, ψ x ∂eta) - ∫ x, a x ∂eta| :=
          abs_sub _ _
      _ ≤ ε + ε := add_le_add hl he
      _ = 2 * ε := by ring
  by_contra hne
  have hpos : 0 < |(∫ x, ψ x ∂lam) - ∫ x, ψ x ∂eta| :=
    abs_pos.mpr (sub_ne_zero.mpr hne)
  have := key (|(∫ x, ψ x ∂lam) - ∫ x, ψ x ∂eta| / 4) (by positivity)
  linarith

/-- Lipschitz tests determine probabilities on a compact metric space. -/
theorem lip032_39_lipschitz_tests_determine_probabilities_metric
    {lam eta : Measure X} [IsProbabilityMeasure lam] [IsProbabilityMeasure eta]
    (h : ∀ φ : X → ℝ, LipschitzWith 1 φ → ∫ x, φ x ∂lam = ∫ x, φ x ∂eta) :
    lam = eta := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  exact lip032_39_lipschitz_tests_determine_probabilities_continuous h f.continuous

end Metric

variable {d : ℕ}

/-- Lipschitz tests determine probabilities: two probability measures on the torus whose integrals
agree on every real test that is `1`-Lipschitz for the Euclidean quotient distance are equal. -/
theorem lip032_39_lipschitz_tests_determine_probabilities
    (lam eta : Measure (Torus d)) [IsProbabilityMeasure lam] [IsProbabilityMeasure eta]
    (h : ∀ φ : Torus d → ℝ, TorusLipschitzWith 1 φ → ∫ x, φ x ∂lam = ∫ x, φ x ∂eta) :
    lam = eta := by
  refine lip032_39_lipschitz_tests_determine_probabilities_metric fun φ hφ => h φ fun x y => ?_
  have h1 : |φ x - φ y| ≤ dist x y := by
    simpa [Real.dist_eq] using hφ.dist_le_mul x y
  exact h1.trans (by simpa using (torusDist_comparison x y).1)

end DGPS.Frontier.LIP032
