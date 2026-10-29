import DGPS.Frontier.LIP032.T25
import DGPS.Frontier.LIP032.T34
import DGPS.Frontier.LIP032.T37

/-!
# LIP032.38: Continuous-test continuity and weak continuity

Task id and title: LIP032.38, "Continuous-test continuity and weak continuity" (node LIP032,
contractibility of the minimizer set; conditional on the Task 29 bindings and on the positive-rate
flow context of LIP031, inherited through LIP032.37).

## Provides
* `DGPS.Frontier.LIP032.lip032_38_continuous_test_continuity_weak_continuity` : MAIN. Under the exact
  positive-rate context of LIP032.37, there is a limit map `R` on the `L²(m)` classes such that
  (i) for every continuous real `φ` on the torus, the map `(ν, s) ↦ ∫ φ d(R [f_{ν,s}])` is continuous
  on `S × [0,1]`, and (ii) the map `(ν, s) ↦ R [f_{ν,s}]` into probability measures is continuous for
  the weak topology.
* `DGPS.Frontier.LIP032.continuousAt_of_bound_LIP03238` (helper) : the abstract epsilon argument.
  A time-dependent bound on Lipschitz tests with a distance `D` tending to zero at a base point gives
  continuity at that point of the test integrals of every continuous test.
* `DGPS.Frontier.LIP032.abs_integral_sub_le_LIP03238` (helper) : two continuous functions within
  `c` of each other everywhere have integrals against a probability within `c`.

## R5 notes
* Inherited hypotheses. The binders `A`, `drift`, `G`, `B`, `g`, `β`, `hMF`, `hV`, `hWB`, `r`, `hr`,
  `hrate`, `μ`, `hμ`, `M_V`, `M_W`, `hVb`, `hWb` are exactly those of LIP032.37. Nothing is added
  and nothing is removed. The unconditional reading of the frozen contractibility sentence is neither
  claimed nor strengthened here (FD-001).
* Choice function. As in LIP032.37 the conclusion is existential over the limit map `R` on the classes
  `l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)`; the same `R` serves every test and both
  conclusions. The specification speaks of "the" map `R(f)`; LIP032.37 provides it only as a choice.
* Parameter space. `S × [0,1]` is `minimizerSet_LIP03225 A × Set.Icc 0 1` with the product topology
  of the weak subspace topology and the subspace topology, as in LIP032.25.
* Tests. A "continuous real `φ`" is `Continuous φ` on the torus; the test integral is
  `∫ x, φ x ∂(R c : Measure (Torus d))`, as in LIP032.37.
* Weak continuity. The second conclusion is continuity into `ProbabilityMeasure (Torus d)` with its
  weak topology; it is deduced from the scalar continuities through the characterization of
  convergence by bounded continuous test functions. A bounded continuous function on the compact torus
  is a continuous function, so the first conclusion applies.
* Lipschitz approximation. LIP032.34 is used with the sup norm of `φ` and the radius from uniform
  continuity (existence form), for the accuracy `ε / 6`. The approximant is the infimal convolution
  of LIP032.33. Its Lipschitz property for `dist` gives `TorusLipschitzWith` since the quotient metric
  `dist` is dominated by the Euclidean quotient distance `torusDist`.
* Order of choices. The time `T` is chosen first from `2 L K e^{-rT} < ε/3`, with `T ≥ 0` obtained from
  the limit of the exponential, so no case split on `L K = 0` is needed. The neighborhood is chosen
  afterwards with the distance bound `ε / (3 (A_T + 1))`, which avoids a zero-denominator case for
  `A_T = ‖ψ‖∞ Σ(T)`.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- Helper: if two continuous functions are within `c` of each other everywhere, their integrals
against a probability measure are within `c`. -/
theorem abs_integral_sub_le_LIP03238 (P : ProbabilityMeasure (Torus d)) {f g : Torus d → ℝ}
    (hf : Continuous f) (hg : Continuous g) {c : ℝ} (h : ∀ x, |f x - g x| ≤ c) :
    |∫ x, f x ∂(P : Measure (Torus d)) - ∫ x, g x ∂(P : Measure (Torus d))| ≤ c := by
  have hfi : Integrable f (P : Measure (Torus d)) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hgi : Integrable g (P : Measure (Torus d)) :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  rw [← integral_sub hfi hgi]
  have := norm_integral_le_of_norm_le_const (μ := (P : Measure (Torus d)))
    (f := fun x => f x - g x) (C := c) (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using h x)
  simpa using this

/-- Helper: the abstract epsilon argument. If, for Lipschitz tests, the difference of the test
integrals at `z` and at the base point `z₀` is bounded, for every time `t ≥ 0`, by
`2 L K e^{-r t} + ‖ψ‖∞ (2 e^{γ t}) D z` with `D z → 0` as `z → z₀`, then the test integrals of
every continuous test converge at `z₀`. -/
theorem continuousAt_of_bound_LIP03238 {α : Type*} [TopologicalSpace α]
    (P : α → ProbabilityMeasure (Torus d)) (D : α → ℝ) (z₀ : α)
    (hD : Tendsto D (𝓝 z₀) (𝓝 0)) {K r γ : ℝ} (hr : 0 < r)
    (hb : ∀ L : ℝ, 0 ≤ L → ∀ ψ : Torus d → ℝ, TorusLipschitzWith L ψ → ∀ t : ℝ, 0 ≤ t → ∀ z : α,
      |∫ x, ψ x ∂(P z : Measure (Torus d)) - ∫ x, ψ x ∂(P z₀ : Measure (Torus d))| ≤
        2 * L * K * Real.exp (-(r * t)) + (⨆ x, |ψ x|) * (2 * Real.exp (γ * t)) * D z)
    (φ : Torus d → ℝ) (hφ : Continuous φ) :
    Tendsto (fun z => ∫ x, φ x ∂(P z : Measure (Torus d))) (𝓝 z₀)
      (𝓝 (∫ x, φ x ∂(P z₀ : Measure (Torus d)))) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hε6 : 0 < ε / 6 := by positivity
  obtain ⟨δ, hδ, hcont, -, hup, hab⟩ :=
    lip032_34_uniform_lipschitz_approximation_bound_exists hφ hε6
  set L : ℝ := (2 * ‖(⟨φ, hφ⟩ : C(Torus d, ℝ))‖ + ε / 6) / δ with hLdef
  set ψ : Torus d → ℝ := infConv_LIP03233 φ L with hψdef
  have hL0 : 0 ≤ L := by
    have hM : ∀ x, |φ x| ≤ ‖(⟨φ, hφ⟩ : C(Torus d, ℝ))‖ := fun x => by
      simpa using ContinuousMap.norm_coe_le_norm (⟨φ, hφ⟩ : C(Torus d, ℝ)) x
    obtain ⟨hε0, hM0⟩ := eps_M_nonneg_LIP03234 hδ hcont hM
    positivity
  have hlip : LipschitzWith L.toNNReal ψ :=
    (lip032_33_compact_minimum_produces_lipschitz_function hφ hL0).2.2
  have hψc : Continuous ψ := hlip.continuous
  have hψL : TorusLipschitzWith L ψ := by
    intro x y
    have h1 := lip032_33_compact_minimum_produces_lipschitz_function_dist hφ hL0 x y
    have h2 := (DGPS.torusDist_comparison x y).1
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hL0)
  have happrox : ∀ Q : ProbabilityMeasure (Torus d),
      |∫ x, φ x ∂(Q : Measure (Torus d)) - ∫ x, ψ x ∂(Q : Measure (Torus d))| ≤ ε / 6 :=
    fun Q => abs_integral_sub_le_LIP03238 Q hφ hψc fun x => by
      rw [abs_sub_comm]; exact hab x
  -- the time is fixed first
  have htend : Tendsto (fun t : ℝ => 2 * L * K * Real.exp (-(r * t))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => r * t) atTop atTop := tendsto_id.const_mul_atTop hr
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    simpa using h2.const_mul (2 * L * K)
  obtain ⟨T, hT, hT0⟩ := (((tendsto_order.1 htend).2 (ε / 3) (by positivity)).and
    (eventually_ge_atTop (0 : ℝ))).exists
  -- the finite coefficient `A_T`
  set AT : ℝ := (⨆ x, |ψ x|) * (2 * Real.exp (γ * T)) with hAT
  have hAT0 : 0 ≤ AT := mul_nonneg (Real.iSup_nonneg fun x => abs_nonneg _) (by positivity)
  have hη : 0 < ε / (3 * (AT + 1)) := by positivity
  filter_upwards [(tendsto_order.1 hD).2 _ hη] with z hz
  have hbz := hb L hL0 ψ hψL T hT0 z
  have hmid : AT * D z ≤ ε / 3 := by
    have h1 : AT * D z ≤ AT * (ε / (3 * (AT + 1))) :=
      mul_le_mul_of_nonneg_left hz.le hAT0
    have h2 : AT * (ε / (3 * (AT + 1))) ≤ (AT + 1) * (ε / (3 * (AT + 1))) :=
      mul_le_mul_of_nonneg_right (by linarith) hη.le
    have h3 : (AT + 1) * (ε / (3 * (AT + 1))) = ε / 3 := by
      field_simp
    linarith
  have hchain := abs_sub_chain_LIP03237
    (∫ x, φ x ∂(P z : Measure (Torus d))) (∫ x, ψ x ∂(P z : Measure (Torus d)))
    (∫ x, ψ x ∂(P z₀ : Measure (Torus d))) (∫ x, φ x ∂(P z₀ : Measure (Torus d)))
  have h₀ := happrox (P z₀)
  rw [abs_sub_comm] at h₀
  rw [Real.dist_eq]
  have hbz' : |∫ x, ψ x ∂(P z : Measure (Torus d)) - ∫ x, ψ x ∂(P z₀ : Measure (Torus d))| ≤
      2 * L * K * Real.exp (-(r * T)) + AT * D z := hbz
  linarith [happrox (P z)]

/-- **LIP032.38.** Continuous-test continuity and weak continuity. For a limit map `R` as in
LIP032.37, every continuous real test `φ` gives a continuous function
`(ν, s) ↦ ∫ φ d(R [f_{ν,s}])` on `S × [0,1]`, and the map `(ν, s) ↦ R [f_{ν,s}]` is weakly
continuous. -/
theorem lip032_38_continuous_test_continuity_weak_continuity (A : InteractionData d)
    (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β)
    (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ⊤ (fun x => A.W x y) (fun x => B x y))
    {r : ℝ} (hr : 0 < r) (hrate : ENNReal.ofReal r < scalarRate A drift)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (M_V M_W : ℝ) (hVb : ∀ x, |A.V x| ≤ M_V) (hWb : ∀ x y, |A.W x y| ≤ M_W) :
    ∃ (R : DGPS.Lipschitz.L2s d → ProbabilityMeasure (Torus d)),
      (∀ φ : Torus d → ℝ, Continuous φ →
        Continuous (fun z : minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1 =>
          ∫ x, φ x ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ z.1.1 z.2)) :
            Measure (Torus d)))) ∧
      Continuous (fun z : minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1 =>
        R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ z.1.1 z.2))) := by
  obtain ⟨R, hR⟩ :=
    lip032_37_difference_limiting_tests A drift hMF hV hWB hr hrate μ hμ M_V M_W hVb hWb
  have key : ∀ φ : Torus d → ℝ, Continuous φ →
      ∀ z₀ : minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1,
      Tendsto (fun z : minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1 =>
        ∫ x, φ x ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ z.1.1 z.2)) :
          Measure (Torus d))) (𝓝 z₀)
        (𝓝 (∫ x, φ x ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ z₀.1.1 z₀.2)) :
          Measure (Torus d)))) := by
    intro φ hφ z₀
    refine continuousAt_of_bound_LIP03238
      (fun z : minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1 =>
        R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ z.1.1 z.2)))
      (fun z : minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1 =>
        ∫ x, |interpolDensity_LIP03222 A μ z.1.1 z.2 x -
          interpolDensity_LIP03222 A μ z₀.1.1 z₀.2 x| ∂haar d)
      z₀ (lip032_25_exact_interpolation_l1_estimate_continuous A M_V M_W hVb hWb μ hμ z₀.1 z₀.2)
      (K := Real.sqrt (2 * (Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W) / r))
      (γ := 2 * Real.pi * (d : ℝ) * (g + 3 * β) ^ 2) hr ?_ φ hφ
    intro L hL ψ hψ t ht z
    exact hR z.1.1 z₀.1.1 z.1.2 z₀.1.2 z.2 z₀.2 z.2.2.1 z.2.2.2 z₀.2.2.1 z₀.2.2.2 L hL ψ hψ t ht
  refine ⟨R, fun φ hφ => continuous_iff_continuousAt.2 fun z₀ => key φ hφ z₀, ?_⟩
  refine continuous_iff_continuousAt.2 fun z₀ => ?_
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f => key f f.continuous z₀

end DGPS.Frontier.LIP032
