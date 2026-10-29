import DGPS.Frontier.LIP032.T02
import DGPS.Frontier.LIP032.T20
import DGPS.Frontier.LIP032.T21
import DGPS.Variational.EquilibriumGibbs

/-!
# LIP032.03: Continuity of normalized Gibbs densities

Task id and title: LIP032.03, "Continuity of normalized Gibbs densities" (node LIP032,
contractibility of the minimizer set; leaf formalization, no positive-rate or flow hypothesis
is used).

## Provides
* `DGPS.Frontier.LIP032.lip032_03_continuity_normalized_gibbs_densities` : for an interaction `A`
  on `𝕋^d`, the conjunction of (i) for all reals `M_V`, `M_W` with `|A.V| ≤ M_V` and
  `|A.W| ≤ M_W`, and all probabilities `ν`, `η` on `𝕋^d`,
  `‖p_ν - p_η‖_∞ ≤ 2 C ‖K_ν - K_η‖_∞` with `C = e^{2 (M_V + M_W)}`; and (ii) the map
  `ν ↦ p_ν`, from probabilities with the weak topology to `C(𝕋^d, ℝ)` with the uniform norm, is
  continuous.
* `DGPS.Frontier.LIP032.lip032_03_continuity_normalized_gibbs_densities_bound` : the inequality
  of (i) for one fixed pair of bounds and one pair of probabilities.
* `DGPS.Frontier.LIP032.lip032_03_continuity_normalized_gibbs_densities_continuous` : the
  continuity statement (ii), with no bound hypothesis.

## R5 notes
* Hypotheses: only `A : InteractionData d`. The reals `M_V`, `M_W` with the two bounds appear as
  explicit hypotheses of the inequality (they are the specification's context for `C`). The
  continuity statement (ii) has no such hypothesis: its bounds are obtained internally by
  compactness (`exists_bounds_LIP03203`). No positive-rate, flow, or LIP031 hypothesis is used
  anywhere, so nothing is strengthened or weakened relative to the frozen statement.
* `p_ν` is the packet's `DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d))`, that is
  `e^{-Φ}/Z` with `Φ = A.V + ∫ A.W(·,y) dν(y)` and `Z = ∫ e^{-Φ} dm`. The bundled version
  `gibbsDensityMap_LIP03203` is the continuous function of this definition; its continuity and
  the identification with `normExp_LIP03217 (potential_LIP03203 A ν)` are proved by unfolding
  (`gibbsDensity_eq_normExp_LIP03203` is `rfl`). The packet's Gibbs module is brought in only
  for this definition, as LIP032.18 does; no result of it is used.
* `K_ν` is `kernelMap_LIP03219 A ν`, the kernel integral `x ↦ ∫ A.W(x,y) dν(y)` bundled as an
  element of `C(𝕋^d, ℝ)` by LIP032.19.
* "Weak topology" is Mathlib's narrow topology on `ProbabilityMeasure (Torus d)`. "Uniform norm"
  is the norm of `C(𝕋^d, ℝ)`, which is the sup norm on the compact torus. The inequality is
  proved pointwise from LIP032.21 (`lip032_21_exact_2c_density_bound_of_le`) and transferred to
  the norm by `ContinuousMap.norm_le`; the real-supremum form of LIP032.21 is not needed.
* The common potential `A.V` cancels: the potential difference `U_ν - U_η` equals `K_ν - K_η`
  pointwise, and this is the only input of the LIP032.21 estimate.
* Continuity (ii) combines (i) with LIP032.02 (`lip032_02_weak_uniform_convolution_nhds`) at each
  base point: a weak neighborhood with `‖K_ν - K_ν₀‖ < ε / (2C)` gives `‖p_ν - p_ν₀‖ < ε`.
* The Euclidean quotient distance of the specification enters only through LIP032.02, LIP032.16
  and LIP032.19, and does not appear in this file.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- Bounds for an interaction: some reals `M_V`, `M_W` with `|A.V| ≤ M_V` and `|A.W| ≤ M_W`. -/
theorem exists_bounds_LIP03203 (A : InteractionData d) :
    ∃ M_V M_W : ℝ, (∀ x, |A.V x| ≤ M_V) ∧ (∀ x y, |A.W x y| ≤ M_W) := by
  obtain ⟨M_V, hM_V⟩ := exists_abs_bound_LIP03220 A.V_continuous
  obtain ⟨M_W, -, hM_W⟩ := lip032_16_continuous_kernel_integrals_common_bounds_exists_bound A
  exact ⟨M_V, M_W, hM_V, hM_W⟩

/-- The potential `U_ν(x) = A.V x + ∫ A.W(x,y) dν(y)` of a probability `ν`. -/
noncomputable def potential_LIP03203 (A : InteractionData d) (ν : ProbabilityMeasure (Torus d))
    (x : Torus d) : ℝ :=
  A.V x + ∫ y, A.W x y ∂(ν : Measure (Torus d))

/-- The potential is bounded by `M_V + M_W`. -/
theorem abs_potential_le_LIP03203 {A : InteractionData d} {M_V M_W : ℝ}
    (hV : ∀ x, |A.V x| ≤ M_V) (hW : ∀ x y, |A.W x y| ≤ M_W) (ν : ProbabilityMeasure (Torus d)) :
    ∀ x, |potential_LIP03203 A ν x| ≤ M_V + M_W := by
  intro x
  have hK := (lip032_16_continuous_kernel_integrals_common_bounds A M_W hW).1
    (ν : Measure (Torus d))
  unfold potential_LIP03203
  exact (abs_add_le _ _).trans (add_le_add (hV x) (hK.2 x))

/-- The potential is continuous. -/
theorem continuous_potential_LIP03203 (A : InteractionData d) {M_W : ℝ}
    (hW : ∀ x y, |A.W x y| ≤ M_W) (ν : ProbabilityMeasure (Torus d)) :
    Continuous (potential_LIP03203 A ν) := by
  have hK := (lip032_16_continuous_kernel_integrals_common_bounds A M_W hW).1
    (ν : Measure (Torus d))
  unfold potential_LIP03203
  exact A.V_continuous.add hK.1

/-- The packet's Gibbs density of a probability `ν` is continuous. -/
theorem continuous_gibbsDensity_LIP03203 (A : InteractionData d)
    (ν : ProbabilityMeasure (Torus d)) :
    Continuous (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d))) := by
  obtain ⟨M_V, M_W, hV, hW⟩ := exists_bounds_LIP03203 A
  exact (lip032_17_positive_normalized_exponential _ (continuous_potential_LIP03203 A hW ν)
    (M_V + M_W) (abs_potential_le_LIP03203 hV hW ν)).2.2.2.2.2

/-- The packet's Gibbs density is the normalized exponential of the potential `U_ν`. -/
theorem gibbsDensity_eq_normExp_LIP03203 (A : InteractionData d)
    (ν : ProbabilityMeasure (Torus d)) :
    DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)) =
      normExp_LIP03217 (potential_LIP03203 A ν) :=
  rfl

/-- The normalized Gibbs density `p_ν` of a probability `ν`, bundled as an element of
`C(𝕋^d, ℝ)`. -/
noncomputable def gibbsDensityMap_LIP03203 (A : InteractionData d)
    (ν : ProbabilityMeasure (Torus d)) : C(Torus d, ℝ) :=
  ⟨DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)), continuous_gibbsDensity_LIP03203 A ν⟩

/-- The pointwise `2C` bound for two normalized Gibbs densities, in the norm of `C(𝕋^d, ℝ)`. -/
theorem lip032_03_continuity_normalized_gibbs_densities_bound (A : InteractionData d)
    (M_V M_W : ℝ) (hV : ∀ x, |A.V x| ≤ M_V) (hW : ∀ x y, |A.W x y| ≤ M_W)
    (ν η : ProbabilityMeasure (Torus d)) :
    ‖gibbsDensityMap_LIP03203 A ν - gibbsDensityMap_LIP03203 A η‖ ≤
      2 * Real.exp (2 * (M_V + M_W)) * ‖kernelMap_LIP03219 A ν - kernelMap_LIP03219 A η‖ := by
  have hδ : ∀ x, |potential_LIP03203 A ν x - potential_LIP03203 A η x| ≤
      ‖kernelMap_LIP03219 A ν - kernelMap_LIP03219 A η‖ := by
    intro x
    have e : potential_LIP03203 A ν x - potential_LIP03203 A η x =
        (kernelMap_LIP03219 A ν - kernelMap_LIP03219 A η) x := by
      simp only [ContinuousMap.sub_apply, kernelMap_apply_LIP03219, potential_LIP03203]
      ring
    calc |potential_LIP03203 A ν x - potential_LIP03203 A η x|
        = ‖(kernelMap_LIP03219 A ν - kernelMap_LIP03219 A η) x‖ := by
          rw [e, Real.norm_eq_abs]
      _ ≤ ‖kernelMap_LIP03219 A ν - kernelMap_LIP03219 A η‖ :=
          ContinuousMap.norm_coe_le_norm _ x
  have hC : (0 : ℝ) ≤ 2 * Real.exp (2 * (M_V + M_W)) *
      ‖kernelMap_LIP03219 A ν - kernelMap_LIP03219 A η‖ := by
    positivity
  rw [ContinuousMap.norm_le _ hC]
  intro x
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs]
  exact lip032_21_exact_2c_density_bound_of_le (continuous_potential_LIP03203 A hW ν)
    (continuous_potential_LIP03203 A hW η) (abs_potential_le_LIP03203 hV hW ν)
    (abs_potential_le_LIP03203 hV hW η) hδ x

/-- Continuity of `ν ↦ p_ν` in the uniform norm, from the weak topology on probabilities. -/
theorem lip032_03_continuity_normalized_gibbs_densities_continuous (A : InteractionData d) :
    Continuous (fun ν : ProbabilityMeasure (Torus d) => gibbsDensityMap_LIP03203 A ν) := by
  obtain ⟨M_V, M_W, hV, hW⟩ := exists_bounds_LIP03203 A
  have hC : 0 < 2 * Real.exp (2 * (M_V + M_W)) := by positivity
  refine continuous_iff_continuousAt.2 fun ν₀ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN, h⟩ := lip032_02_weak_uniform_convolution_nhds A ν₀
    (ε / (2 * Real.exp (2 * (M_V + M_W)))) (div_pos hε hC)
  filter_upwards [hN] with ν hν
  rw [dist_eq_norm]
  calc ‖gibbsDensityMap_LIP03203 A ν - gibbsDensityMap_LIP03203 A ν₀‖
      ≤ 2 * Real.exp (2 * (M_V + M_W)) * ‖kernelMap_LIP03219 A ν - kernelMap_LIP03219 A ν₀‖ :=
        lip032_03_continuity_normalized_gibbs_densities_bound A M_V M_W hV hW ν ν₀
    _ < 2 * Real.exp (2 * (M_V + M_W)) * (ε / (2 * Real.exp (2 * (M_V + M_W)))) :=
        mul_lt_mul_of_pos_left (h ν hν) hC
    _ = ε := by field_simp

/-- **LIP032.03.** For every interaction `A` on `𝕋^d`: (i) for all bounds `M_V`, `M_W` on `A.V`
and `A.W`, and all probabilities `ν`, `η`, `‖p_ν - p_η‖_∞ ≤ 2 C ‖K_ν - K_η‖_∞` with
`C = e^{2 (M_V + M_W)}`; (ii) `ν ↦ p_ν` is continuous in the uniform norm. -/
theorem lip032_03_continuity_normalized_gibbs_densities (A : InteractionData d) :
    (∀ M_V M_W : ℝ, (∀ x, |A.V x| ≤ M_V) → (∀ x y, |A.W x y| ≤ M_W) →
      ∀ ν η : ProbabilityMeasure (Torus d),
        ‖gibbsDensityMap_LIP03203 A ν - gibbsDensityMap_LIP03203 A η‖ ≤
          2 * Real.exp (2 * (M_V + M_W)) *
            ‖kernelMap_LIP03219 A ν - kernelMap_LIP03219 A η‖) ∧
    Continuous (fun ν : ProbabilityMeasure (Torus d) => gibbsDensityMap_LIP03203 A ν) :=
  ⟨fun M_V M_W hV hW ν η =>
    lip032_03_continuity_normalized_gibbs_densities_bound A M_V M_W hV hW ν η,
    lip032_03_continuity_normalized_gibbs_densities_continuous A⟩

end DGPS.Frontier.LIP032
