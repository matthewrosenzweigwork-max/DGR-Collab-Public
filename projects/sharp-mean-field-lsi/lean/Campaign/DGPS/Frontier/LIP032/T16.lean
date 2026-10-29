import DGPS.Model.Data

/-!
# LIP032.16: Continuous kernel integrals and common bounds

Task id and title: LIP032.16, "Continuous kernel integrals and common bounds" (node LIP032,
contractibility of the minimizer set; leaf formalization, no positive-rate hypothesis is used).

## Provides
* `DGPS.Frontier.LIP032.kernelIntegral_LIP03216` : the kernel integral
  `K_ν(x) = ∫ A.W(x,y) dν(y)` as a function of `x`.
* `DGPS.Frontier.LIP032.lip032_16_continuous_kernel_integrals_common_bounds` : for a continuous
  interaction `A.W` bounded by `M_W`, and every probability `ν` on `𝕋^d`, `K_ν` is continuous and
  bounded by `M_W`; and for every `ε > 0` there is one `δ > 0`, independent of `ν`, such that
  `torusDist x x' < δ` implies `|K_ν x - K_ν x'| ≤ ε` for all probabilities `ν`.
* `DGPS.Frontier.LIP032.lip032_16_continuous_kernel_integrals_common_bounds_exists_bound` : the
  bound `M_W ≥ 0` with `|A.W x y| ≤ M_W` exists (compactness), so the hypothesis of the main
  statement is satisfiable for every `A : InteractionData d`.
* `DGPS.Frontier.LIP032.lip032_16_continuous_kernel_integrals_common_bounds_dist` : the same
  modulus statement for Mathlib's sup metric `dist` on `𝕋^d` (the form actually proved first).

## R5 notes
* Hypotheses: `A : InteractionData d` and a real `M_W` with `∀ x y, |A.W x y| ≤ M_W`. The
  specification says "choose `M_W ≥ 0` with `|A.W| ≤ M_W`"; nonnegativity of `M_W` follows from
  the bound at any point of the torus, so it is not assumed as a separate hypothesis. Existence
  of `M_W` is the separate lemma `..._exists_bound`.
* Probabilities `ν` are `Measure (Torus d)` with `[IsProbabilityMeasure ν]` for the Borel
  `σ`-algebra of the torus (no further measurability assumption is needed).
* Reading of `d(x,x')`: the specification's metric is the Euclidean quotient distance, here
  `torusDist`. Since `dist x x' ≤ torusDist x x'` (`torusDist_comparison`), a `δ` for `dist`
  is also a `δ` for `torusDist`; both versions are given.
* The quantifier order is as in the specification: `δ` depends only on `ε` (and `A`, `M_W`
  is not even used), and is uniform over all `ν`.
* `K_ν` is formalized as the Bochner integral `∫ y, A.W x y ∂ν`. Continuity of sections and
  the bound make every integrand integrable, so no junk value of the integral is used.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- The kernel integral `K_ν(x) = ∫ A.W(x,y) dν(y)`. -/
noncomputable def kernelIntegral_LIP03216 (A : InteractionData d) (ν : Measure (Torus d))
    (x : Torus d) : ℝ :=
  ∫ y, A.W x y ∂ν

/-- Each section `y ↦ A.W x y` is continuous. -/
theorem section_continuous_LIP03216 (A : InteractionData d) (x : Torus d) :
    Continuous (fun y => A.W x y) :=
  A.W_continuous.comp (continuous_const.prodMk continuous_id)

/-- Sections are integrable under a probability when bounded by `M`. -/
theorem section_integrable_LIP03216 (A : InteractionData d) (M : ℝ)
    (hM : ∀ x y, |A.W x y| ≤ M) (ν : Measure (Torus d)) [IsProbabilityMeasure ν]
    (x : Torus d) : Integrable (fun y => A.W x y) ν :=
  Integrable.of_bound (section_continuous_LIP03216 A x).aestronglyMeasurable M
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hM x y)

/-- Existence of a uniform bound for `A.W` by compactness. -/
theorem lip032_16_continuous_kernel_integrals_common_bounds_exists_bound
    (A : InteractionData d) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x y, |A.W x y| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d × Torus d)).exists_bound_of_continuousOn
    (f := fun p : Torus d × Torus d => A.W p.1 p.2) A.W_continuous.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x y => ?_⟩
  have := hM (x, y) (Set.mem_univ _)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- The uniform modulus of the kernel integral for the sup metric `dist`. -/
theorem lip032_16_continuous_kernel_integrals_common_bounds_dist
    (A : InteractionData d) (M : ℝ) (hM : ∀ x y, |A.W x y| ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (ν : Measure (Torus d)) [IsProbabilityMeasure ν]
      (x x' : Torus d), dist x x' < δ →
        |∫ y, A.W x y ∂ν - ∫ y, A.W x' y ∂ν| ≤ ε := by
  intro ε hε
  have huc : UniformContinuous (fun p : Torus d × Torus d => A.W p.1 p.2) :=
    CompactSpace.uniformContinuous_of_continuous A.W_continuous
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  refine ⟨δ, hδ, fun ν _ x x' hxx => ?_⟩
  have hpt : ∀ y, |A.W x y - A.W x' y| ≤ ε := fun y => by
    have h := hδε (a := (x, y)) (b := (x', y)) (by simpa [Prod.dist_eq] using hxx)
    rw [Real.dist_eq] at h
    exact h.le
  rw [← integral_sub (section_integrable_LIP03216 A M hM ν x)
    (section_integrable_LIP03216 A M hM ν x')]
  have := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun y => A.W x y - A.W x' y) (C := ε)
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hpt y)
  simpa [Real.norm_eq_abs] using this

/-- **LIP032.16.** For every probability `ν` on `𝕋^d`, the kernel integral
`K_ν(x) = ∫ A.W(x,y) dν(y)` is continuous with `|K_ν(x)| ≤ M_W`, and for every `ε > 0` there is
one `δ > 0`, independent of `ν`, with `torusDist x x' < δ → |K_ν x - K_ν x'| ≤ ε`. -/
theorem lip032_16_continuous_kernel_integrals_common_bounds
    (A : InteractionData d) (M_W : ℝ) (hW : ∀ x y, |A.W x y| ≤ M_W) :
    (∀ (ν : Measure (Torus d)) [IsProbabilityMeasure ν],
      Continuous (fun x => ∫ y, A.W x y ∂ν) ∧ ∀ x, |∫ y, A.W x y ∂ν| ≤ M_W) ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (ν : Measure (Torus d)) [IsProbabilityMeasure ν]
      (x x' : Torus d), torusDist x x' < δ →
        |∫ y, A.W x y ∂ν - ∫ y, A.W x' y ∂ν| ≤ ε := by
  refine ⟨fun ν _ => ⟨?_, fun x => ?_⟩, fun ε hε => ?_⟩
  · refine Metric.continuous_iff.mpr fun x ε hε => ?_
    obtain ⟨δ, hδ, h⟩ := lip032_16_continuous_kernel_integrals_common_bounds_dist A M_W hW
      (ε / 2) (half_pos hε)
    refine ⟨δ, hδ, fun x' hx' => ?_⟩
    rw [Real.dist_eq]
    have := h ν x' x hx'
    linarith [abs_sub_comm (∫ y, A.W x' y ∂ν) (∫ y, A.W x y ∂ν)]
  · have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun y => A.W x y) (C := M_W)
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hW x y)
    simpa [Real.norm_eq_abs] using this
  · obtain ⟨δ, hδ, h⟩ := lip032_16_continuous_kernel_integrals_common_bounds_dist A M_W hW ε hε
    exact ⟨δ, hδ, fun ν _ x x' hxx =>
      h ν x x' (lt_of_le_of_lt (torusDist_comparison x x').1 hxx)⟩

end DGPS.Frontier.LIP032
