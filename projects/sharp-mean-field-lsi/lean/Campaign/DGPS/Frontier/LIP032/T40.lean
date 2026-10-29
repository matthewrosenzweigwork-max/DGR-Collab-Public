import DGPS.Frontier.LIP032.T29
import DGPS.Frontier.LIP032.T30
import DGPS.Frontier.LIP032.T39

/-!
# LIP032.40: Zero initial gap fixes the measure

Task id and title: LIP032.40, "Zero initial gap fixes the measure" (node LIP032, contractibility of
the minimizer set; leaf formalization, conditional on the positive-rate flow context of LIP031).

## Provides
* `DGPS.Frontier.LIP032.lip032_40_zero_initial_gap_fixes_measure` : MAIN. For a choice `u` of flows
  and a choice `R` of limiting probabilities with the LIP032.30 property `hch`, every free-energy
  minimizer `ν` satisfies `R [p_ν] = ν`, where `[p_ν]` is the `L²(m)` class of the Gibbs density
  `p_ν = gibbsDensity A ν`.
* `DGPS.Frontier.LIP032.lip032_40_zero_initial_gap_fixes_measure_exists` : non-vacuity: choices `u`,
  `R` with the property `hch` exist (LIP032.30), and for them `R [p_ν] = ν` for every minimizer.
* `DGPS.Frontier.LIP032.gibbs_test_integral_LIP03240` (helper) : for a minimizer `ν` and a
  continuous real test `φ`, the integral of `φ` against the class `[p_ν]` and Haar measure equals
  the integral of `φ` against `ν`.
* `DGPS.Frontier.LIP032.torusLip_continuous_LIP03240` (helper) : a one-Lipschitz function for the
  Euclidean quotient distance is continuous.
* `DGPS.Frontier.LIP032.interpol_zero_LIP03240` (helper) : the interpolation density at `s = 0` is
  the Gibbs density `p_ν`, as a function.

## R5 notes
* Hypotheses. The positive-rate context of LIP031 is inherited from the node (Section 2.1) and is
  taken as binders exactly as in LIP032.30: `A`, `drift : AbsoluteDrift A`, `G`, `B`, `g`, `β`,
  `hMF`, `hV : IsWeakGradient A.V G`, `hWB`, a real `r` with `hr : 0 < r` and
  `hrate : ENNReal.ofReal r < scalarRate A drift`. They are the inputs of the LIP031 tail inequality
  used in the proof. Beyond them the only hypotheses are the fixed minimizer `μ` with `hμ`, the
  choices `u`, `R`, and `hch`.
* Choices. The specification's limiting probability `R` is read as the output of LIP032.30: a
  choice of flows `u` and of limits `R`, both indexed by the initial class. The hypothesis `hch` is
  exactly the conclusion of LIP032.30, quantified over all minimizers and all `s ∈ [0,1]`. Only its
  `s = 0` instance is used. The theorem therefore applies to every choice with that property, not to
  one fixed choice. The `_exists` variant shows the property is satisfiable.
* Non-literal reading. The specification writes `p_ν` for the initial density. Here it is the
  class `l2Class_LIP03223 (gibbsDensity A ν)`, and the interpolation density `f_{ν,0}` is identified
  with `p_ν` as a function (`interpol_zero_LIP03240`), not only almost everywhere.
* Time zero. The initial value `u c 0 = [p_ν]` and the initial gap `flowGap A (u c) 0 = 0` come from
  the minimizer case of LIP032.29. The LIP031 tail bound at each `t ≥ 0` then has right-hand side
  zero, so `∫ (u c t) φ dm` is constant in `t ≥ 0` for every one-Lipschitz `φ`. Its value at `t = 0`
  is `∫ φ dν` by the Gibbs identity of LIP032.18, and its limit is `∫ φ dR(c)` by `hch`.
* Measure identification. The equality `R [p_ν] = ν` is derived from equality of integrals against
  all one-Lipschitz tests (LIP032.39, torus form) and `ProbabilityMeasure.toMeasure_injective`.
* Test class. The test class is `TorusLipschitzWith 1` for the Euclidean quotient distance, the
  one-Lipschitz class of LIP031. Its continuity is proved from `torusDist_comparison`, with
  `(Real.sqrt d).toNNReal` as Lipschitz constant.
* The bounds `M_V`, `M_W` are not binders here: the minimizer lemma of LIP032.29 obtains them
  internally.
* Membership `ν ∈ S` is the extended-real equation `freeEnergy A ν = freeEnergyMinimum A`, as in
  LIP032.22, .23, .28, .29 and .30.
* `d` is arbitrary; positivity of `d` is not used.
* Nothing here proves or strengthens the frozen contractibility sentence of the node (FD-001). The
  conclusion is conditional on the positive-rate hypotheses `hr`, `hrate` and on the choice property
  `hch`.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- At `s = 0` the interpolation density is the Gibbs density `p_ν`, as a function. -/
theorem interpol_zero_LIP03240 (A : InteractionData d) (μ ν : ProbabilityMeasure (Torus d)) :
    interpolDensity_LIP03222 A μ ν 0 = DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)) := by
  funext x
  unfold interpolDensity_LIP03222
  simp

/-- A one-Lipschitz function for the Euclidean quotient distance is continuous. -/
theorem torusLip_continuous_LIP03240 {f : Torus d → ℝ} (hf : TorusLipschitzWith 1 f) :
    Continuous f := by
  refine (LipschitzWith.of_dist_le_mul (K := (Real.sqrt (d : ℝ)).toNNReal) fun x y => ?_).continuous
  rw [Real.dist_eq, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  have h1 : |f x - f y| ≤ torusDist x y := by
    have := hf x y
    rwa [one_mul] at this
  exact h1.trans (torusDist_comparison x y).2

/-- For a minimizer `ν` and a continuous real test `φ`, the integral of `φ` against the class
`[p_ν]` and Haar measure equals the integral of `φ` against `ν`. -/
theorem gibbs_test_integral_LIP03240 (A : InteractionData d) (ν : ProbabilityMeasure (Torus d))
    (hν : freeEnergy A ν = freeEnergyMinimum A) {φ : Torus d → ℝ} (hφ : Continuous φ) :
    ∫ x, ⇑(l2Class_LIP03223 (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)))) x * φ x
        ∂haar d =
      ∫ x, φ x ∂(ν : Measure (Torus d)) := by
  obtain ⟨hc, h0, h1, heq⟩ := lip032_18_density_probability_test_integral_bridge_gibbs A ν hν
  obtain ⟨M, -, hM⟩ := exists_abs_bound_LIP03227 φ hφ
  have hb := lip032_18_density_probability_test_integral_bridge_integral hc h0 h1 hφ.measurable
    ⟨M, hM⟩
  have hae := l2Class_coe_ae_LIP03223 (memLp_two_of_continuous_LIP03223 hc)
  have key : ∫ x, φ x ∂(ν : Measure (Torus d)) =
      ∫ x, φ x ∂densityMeasure_LIP03218 (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d))) := by
    rw [heq]
  rw [key, hb.2]
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

/-- Zero initial gap fixes the measure: for a choice `u` of flows and `R` of limiting
probabilities with the LIP032.30 property, every free-energy minimizer `ν` satisfies
`R [p_ν] = ν`. -/
theorem lip032_40_zero_initial_gap_fixes_measure (A : InteractionData d)
    (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β)
    (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ⊤ (fun x => A.W x y) (fun x => B x y))
    {r : ℝ} (hr : 0 < r) (hrate : ENNReal.ofReal r < scalarRate A drift)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (u : DGPS.Lipschitz.L2s d → ℝ → DGPS.Lipschitz.L2s d)
    (R : DGPS.Lipschitz.L2s d → ProbabilityMeasure (Torus d))
    (hch : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A ν = freeEnergyMinimum A →
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        DGPS.Lipschitz.IsGlobalProbFlow hMF
            (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))
            (u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))) ∧
          freeEnergy A (R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))) =
            freeEnergyMinimum A ∧
          ∀ φ : Torus d → ℝ, Continuous φ →
            Tendsto (fun t : ℝ =>
                ∫ x, u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) t x * φ x ∂haar d)
              atTop
              (𝓝 (∫ x, φ x
                ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) :
                  Measure (Torus d))))) :
    ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A ν = freeEnergyMinimum A →
      R (l2Class_LIP03223 (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)))) = ν := by
  intro ν hν
  have hz := hch ν hν 0 le_rfl zero_le_one
  rw [interpol_zero_LIP03240 A μ ν] at hz
  obtain ⟨hflow, -, hten⟩ := hz
  obtain ⟨hu0, -, hgap0⟩ :=
    gate_lip032_29_initial_value_flowgap_definition_binding_minimizer A μ hμ ν hν hMF _ hflow
  obtain ⟨-, R', -, -, -, -, -, -, -, -, -, htail⟩ :=
    DGPS.Lipschitz.positive_rate_flow_tails_and_limiting_minimizer A drift hMF hV hWB hr hrate hflow
  have hbound : ∀ f : Torus d → ℝ, TorusLipschitzWith 1 f → ∀ t : ℝ, 0 ≤ t →
      ∫ x, u (l2Class_LIP03223 (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)))) t x * f x
          ∂haar d =
        ∫ x, f x ∂(R' : Measure (Torus d)) := by
    intro f hf t ht
    obtain ⟨h1, h2⟩ := htail f hf t ht
    rw [hgap0] at h2
    simp only [mul_zero, zero_div, Real.sqrt_zero] at h2
    exact sub_eq_zero.1 (abs_nonpos_iff.1 (h1.trans h2))
  have hfin : ∀ f : Torus d → ℝ, TorusLipschitzWith 1 f →
      ∫ x, f x ∂(R (l2Class_LIP03223 (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)))) :
        Measure (Torus d)) = ∫ x, f x ∂(ν : Measure (Torus d)) := by
    intro f hf
    have hfc := torusLip_continuous_LIP03240 hf
    have hlim : Tendsto (fun t : ℝ =>
        ∫ x, u (l2Class_LIP03223 (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)))) t x * f x
          ∂haar d)
        atTop (𝓝 (∫ x, f x ∂(R' : Measure (Torus d)))) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact (hbound f hf t ht).symm
    have hR := tendsto_nhds_unique (hten f hfc) hlim
    have h0 := hbound f hf 0 le_rfl
    rw [hu0, gibbs_test_integral_LIP03240 A ν hν hfc] at h0
    exact hR.trans h0.symm
  have hmeas : (R (l2Class_LIP03223 (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)))) :
      Measure (Torus d)) = (ν : Measure (Torus d)) :=
    lip032_39_lipschitz_tests_determine_probabilities _ _ hfin
  exact ProbabilityMeasure.toMeasure_injective hmeas

/-- Non-vacuity of the choice property: choices `u`, `R` with the LIP032.30 property exist, and
for every such choice `R [p_ν] = ν` for every minimizer `ν`. -/
theorem lip032_40_zero_initial_gap_fixes_measure_exists (A : InteractionData d)
    (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β)
    (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ⊤ (fun x => A.W x y) (fun x => B x y))
    {r : ℝ} (hr : 0 < r) (hrate : ENNReal.ofReal r < scalarRate A drift)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A) :
    ∃ (u : DGPS.Lipschitz.L2s d → ℝ → DGPS.Lipschitz.L2s d)
      (R : DGPS.Lipschitz.L2s d → ProbabilityMeasure (Torus d)),
      (∀ ν : ProbabilityMeasure (Torus d), freeEnergy A ν = freeEnergyMinimum A →
        ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
          DGPS.Lipschitz.IsGlobalProbFlow hMF
              (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))
              (u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))) ∧
            freeEnergy A (R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))) =
              freeEnergyMinimum A ∧
            ∀ φ : Torus d → ℝ, Continuous φ →
              Tendsto (fun t : ℝ =>
                  ∫ x, u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) t x * φ x ∂haar d)
                atTop
                (𝓝 (∫ x, φ x
                  ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) :
                    Measure (Torus d))))) ∧
      ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A ν = freeEnergyMinimum A →
        R (l2Class_LIP03223 (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)))) = ν := by
  obtain ⟨u, R, h⟩ :=
    lip032_30_choose_one_flow_one_limiting_probability A drift hMF hV hWB hr hrate μ hμ
  exact ⟨u, R, h, lip032_40_zero_initial_gap_fixes_measure A drift hMF hV hWB hr hrate μ hμ u R h⟩

end DGPS.Frontier.LIP032
