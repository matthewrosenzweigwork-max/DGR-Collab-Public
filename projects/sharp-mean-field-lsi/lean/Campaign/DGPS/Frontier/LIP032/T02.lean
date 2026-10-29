import DGPS.Frontier.LIP032.T19

/-!
# LIP032.02: Weak-to-uniform convolution

Task id and title: LIP032.02, "Weak-to-uniform convolution" (node LIP032, contractibility of the
minimizer set; leaf formalization, no positive-rate or flow hypothesis is used).

## Provides
* `DGPS.Frontier.LIP032.lip032_02_weak_uniform_convolution` : for an interaction `A`, the map
  `ν ↦ K_ν`, where `K_ν(x) = ∫ A.W(x,y) dν(y)`, from probability measures on `𝕋^d` with the weak
  topology to `C(𝕋^d, ℝ)` with its uniform norm, is continuous.
* `DGPS.Frontier.LIP032.lip032_02_weak_uniform_convolution_nhds` : the same fact in
  neighborhood form: for a probability `ν₀` and `ε > 0` there is a weak neighborhood `N` of `ν₀`
  with `‖K_ν - K_ν₀‖ < ε` for every `ν ∈ N`.

## R5 notes
* Hypotheses: only `A : InteractionData d`. No positive-rate, flow, or Lipschitz hypothesis is
  added, and none is needed for this continuity statement. The bound `M_W` of the kernel
  integral is obtained internally by compactness, not assumed.
* The map is `kernelMap_LIP03219 A`, the bundling of `K_ν` as an element of `C(𝕋^d, ℝ)`
  established in LIP032.19 (its underlying function is `x ↦ ∫ A.W x y ∂ν`). Continuity of
  each section and the uniform bound make the integrals genuine Bochner integrals, with no
  junk values.
* "Weak probabilities" is read as `ProbabilityMeasure (Torus d)` with Mathlib's weak (narrow)
  topology. "Uniform norm" is the sup norm of `C(𝕋^d, ℝ)`, which is the norm topology of the
  normed group instance; on the compact torus it agrees with the compact-open topology used
  for `Continuous`.
* The proof uses the neighborhood form of LIP032.19 at each base point: continuity at `ν₀` in
  the uniform norm is exactly the neighborhood statement with `dist = ‖· - ·‖`. No extra
  statement about the weak topology is used beyond LIP032.19.
* The Euclidean quotient distance of the specification does not appear in the statement; it
  enters only through LIP032.19 and LIP032.16, where it is handled by `torusDist_comparison`.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- **LIP032.02.** For every interaction `A` on `𝕋^d`, the weak-to-uniform convolution map
`ν ↦ K_ν`, from probability measures with the weak topology to `C(𝕋^d, ℝ)` with the uniform
norm, is continuous. -/
theorem lip032_02_weak_uniform_convolution (A : InteractionData d) :
    Continuous (fun ν : ProbabilityMeasure (Torus d) => kernelMap_LIP03219 A ν) := by
  refine continuous_iff_continuousAt.2 fun ν₀ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN, h⟩ := lip032_19_finite_net_weak_uniform_continuity A ν₀ ε hε
  filter_upwards [hN] with ν hν
  exact (dist_eq_norm _ _).trans_lt (h ν hν)

/-- **LIP032.02 (neighborhood form).** For every interaction `A`, every probability `ν₀` on
`𝕋^d`, and every `ε > 0`, there is a weak neighborhood `N` of `ν₀` such that every `ν ∈ N`
satisfies `‖K_ν - K_ν₀‖_∞ < ε`. -/
theorem lip032_02_weak_uniform_convolution_nhds (A : InteractionData d)
    (ν₀ : ProbabilityMeasure (Torus d)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N ∈ 𝓝 ν₀, ∀ ν ∈ N, ‖kernelMap_LIP03219 A ν - kernelMap_LIP03219 A ν₀‖ < ε :=
  lip032_19_finite_net_weak_uniform_continuity A ν₀ ε hε

end DGPS.Frontier.LIP032
