import DGPS.Frontier.LIP032.T16

/-!
# LIP032.19: Finite-net weak-to-uniform continuity

Task id and title: LIP032.19, "Finite-net weak-to-uniform continuity" (node LIP032, contractibility
of the minimizer set; leaf formalization, no positive-rate or flow hypothesis is used).

## Provides
* `DGPS.Frontier.LIP032.kernelMap_LIP03219` : the kernel integral `K_ν`, `ν` a probability on
  `𝕋^d`, bundled as a continuous function `C(𝕋^d, ℝ)` (continuity from LIP032.16).
* `DGPS.Frontier.LIP032.lip032_19_finite_net_weak_uniform_continuity` : for every probability
  `ν₀` and `ε > 0` there is a neighborhood `𝒩` of `ν₀` in the weak topology of probability
  measures such that every `ν ∈ 𝒩` has `‖K_ν - K_{ν₀}‖_∞ < ε` (sup norm of `C(𝕋^d, ℝ)`).
* `DGPS.Frontier.LIP032.lip032_19_finite_net_weak_uniform_continuity_pointwise` : the same
  neighborhood gives `|K_ν x - K_{ν₀} x| < ε` for every `x`, with `K_ν x = ∫ A.W x y dν(y)`.

## R5 notes
* Hypotheses: only `A : InteractionData d`, a probability `ν₀`, and `ε > 0`. The bound `M_W` of
  LIP032.16 is obtained internally from its existence lemma, so it is not a hypothesis.
* "Weak neighborhood" is read as a neighborhood in Mathlib's topology on
  `ProbabilityMeasure (Torus d)`, which is the weak (narrow) topology: the coarsest topology
  making every bounded continuous test integral continuous.
* "Uniform norm" is the sup norm on `C(𝕋^d, ℝ)` (the torus is compact). The pointwise form is
  provided as a separate corollary.
* The finite net is taken for Mathlib's sup metric `dist` on `𝕋^d` using the `dist` form of
  LIP032.16 (`..._common_bounds_dist`), with tolerance `ε/4`; the specification's radius `δ`
  is stated for the Euclidean quotient distance, and for the covering argument the two metrics
  induce the same topology, so no information is lost. The resulting bound is `3ε/4 < ε`.
* The weak continuity of each center value `ν ↦ ∫ A.W x_j y dν(y)` uses the section `A.W x_j`
  as a bounded continuous function on the compact torus.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- The kernel integral of a probability measure, bundled as a continuous function. -/
noncomputable def kernelMap_LIP03219 (A : InteractionData d) (ν : ProbabilityMeasure (Torus d)) :
    C(Torus d, ℝ) :=
  ⟨fun x => ∫ y, A.W x y ∂(ν : Measure (Torus d)), by
    obtain ⟨M, -, hM⟩ := lip032_16_continuous_kernel_integrals_common_bounds_exists_bound A
    exact ((lip032_16_continuous_kernel_integrals_common_bounds A M hM).1
      (ν : Measure (Torus d))).1⟩

theorem kernelMap_apply_LIP03219 (A : InteractionData d) (ν : ProbabilityMeasure (Torus d))
    (x : Torus d) :
    kernelMap_LIP03219 A ν x = ∫ y, A.W x y ∂(ν : Measure (Torus d)) := rfl

/-- Weak continuity of the kernel integral at a fixed point. -/
theorem continuous_eval_LIP03219 (A : InteractionData d) (x : Torus d) :
    Continuous (fun ν : ProbabilityMeasure (Torus d) =>
      ∫ y, A.W x y ∂(ν : Measure (Torus d))) := by
  have h := ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (X := Torus d)
    (BoundedContinuousFunction.mkOfCompact
      ⟨fun y => A.W x y, section_continuous_LIP03216 A x⟩)
  simpa using h

/-- Pointwise form of the finite-net weak-to-uniform continuity, with strict margin `3ε/4`. -/
theorem pointwise_margin_LIP03219 (A : InteractionData d) (ν₀ : ProbabilityMeasure (Torus d))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N ∈ 𝓝 ν₀, ∀ ν ∈ N, ∀ x : Torus d,
      |∫ y, A.W x y ∂(ν : Measure (Torus d)) - ∫ y, A.W x y ∂(ν₀ : Measure (Torus d))|
        ≤ 3 * ε / 4 := by
  obtain ⟨M, -, hM⟩ := lip032_16_continuous_kernel_integrals_common_bounds_exists_bound A
  obtain ⟨δ, hδ, hmod⟩ := lip032_16_continuous_kernel_integrals_common_bounds_dist A M hM
    (ε / 4) (by linarith)
  obtain ⟨t, -, ht, hcov⟩ := finite_cover_balls_of_compact
    (isCompact_univ (X := Torus d)) hδ
  refine ⟨⋂ c ∈ t, {ν : ProbabilityMeasure (Torus d) |
      |∫ y, A.W c y ∂(ν : Measure (Torus d)) - ∫ y, A.W c y ∂(ν₀ : Measure (Torus d))|
        < ε / 4}, ?_, fun ν hν x => ?_⟩
  · refine (Filter.biInter_mem ht).2 fun c _ => ?_
    refine IsOpen.mem_nhds ?_ (by simpa using by linarith)
    exact isOpen_lt (continuous_abs.comp
      ((continuous_eval_LIP03219 A c).sub continuous_const)) continuous_const
  · obtain ⟨c, hct, hxc⟩ := Set.mem_iUnion₂.1 (hcov (Set.mem_univ x))
    have hc := Set.mem_iInter₂.1 hν c hct
    have hxc' : dist x c < δ := hxc
    have h1 := hmod (ν : Measure (Torus d)) x c hxc'
    have h2 := hmod (ν₀ : Measure (Torus d)) x c hxc'
    have hc' : |∫ y, A.W c y ∂(ν : Measure (Torus d)) - ∫ y, A.W c y ∂(ν₀ : Measure (Torus d))|
        < ε / 4 := hc
    rw [abs_lt] at hc'
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [hc'.1, hc'.2, h1.1, h1.2, h2.1, h2.2]

/-- **LIP032.19.** For every probability `ν₀` and `ε > 0` there is a weak neighborhood `𝒩` of
`ν₀` such that `ν ∈ 𝒩` implies `‖K_ν - K_{ν₀}‖_∞ < ε`. -/
theorem lip032_19_finite_net_weak_uniform_continuity (A : InteractionData d)
    (ν₀ : ProbabilityMeasure (Torus d)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N ∈ 𝓝 ν₀, ∀ ν ∈ N, ‖kernelMap_LIP03219 A ν - kernelMap_LIP03219 A ν₀‖ < ε := by
  obtain ⟨N, hN, h⟩ := pointwise_margin_LIP03219 A ν₀ ε hε
  refine ⟨N, hN, fun ν hν => lt_of_le_of_lt ?_ (show 3 * ε / 4 < ε by linarith)⟩
  refine (ContinuousMap.norm_le _ (by linarith)).2 fun x => ?_
  simpa [kernelMap_apply_LIP03219, Real.norm_eq_abs] using h ν hν x

/-- Pointwise corollary: the same neighborhood controls the difference at every point. -/
theorem lip032_19_finite_net_weak_uniform_continuity_pointwise (A : InteractionData d)
    (ν₀ : ProbabilityMeasure (Torus d)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N ∈ 𝓝 ν₀, ∀ ν ∈ N, ∀ x : Torus d,
      |∫ y, A.W x y ∂(ν : Measure (Torus d)) - ∫ y, A.W x y ∂(ν₀ : Measure (Torus d))| < ε := by
  obtain ⟨N, hN, h⟩ := pointwise_margin_LIP03219 A ν₀ ε hε
  exact ⟨N, hN, fun ν hν x => lt_of_le_of_lt (h ν hν x) (by linarith)⟩

end DGPS.Frontier.LIP032
