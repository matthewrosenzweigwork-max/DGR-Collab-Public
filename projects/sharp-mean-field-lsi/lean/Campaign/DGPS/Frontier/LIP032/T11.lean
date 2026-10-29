import DGPS.Frontier.LIP032.T10
import DGPS.Frontier.LIP032.T25
import DGPS.Frontier.LIP032.T32
import DGPS.Frontier.LIP032.T35
import DGPS.Frontier.LIP032.T36
import DGPS.Frontier.LIP032.T37
import DGPS.Frontier.LIP032.T38
import DGPS.Frontier.LIP032.T40

/-!
# LIP032.11: Homotopy into the minimizing set

Task id and title: LIP032.11, "Homotopy into the minimizing set" (node LIP032, contractibility of the
minimizer set; leaf formalization, conditional on Task 29 and on the positive-rate flow context of
LIP031, inherited through LIP032.09 and LIP032.10).

## Provides
* `DGPS.Frontier.LIP032.lip032_11_homotopy_minimizing_set` : MAIN. Under the exact positive-rate
  context of LIP032.09, a fixed minimizer `μ`, and bounds `|A.V| ≤ M_V`, `|A.W| ≤ M_W`, there are a
  limit map `R` on the `L²(m)` classes and a map `H : S × [0,1] → S` with `(H (ν, s)).1 = R [f_{ν,s}]`,
  such that `H` is continuous, `H (ν, 0) = ν` and `H (ν, 1) = μ` for every minimizer `ν`.

## R5 notes
* Inherited hypotheses. The binders `A`, `drift`, `G`, `B`, `g`, `β`, `hMF`, `hV`, `hWB`, `r`, `hr`,
  `hrate`, `μ`, `hμ`, `M_V`, `M_W`, `hVb`, `hWb` are exactly those of LIP032.09 (and of LIP032.32 and
  LIP032.38). Nothing is added and nothing is removed. The positive-rate data `hr` and `hrate` are
  inherited, so the unit is not stated in the unconditional reading, which is false (FD-001). The
  frozen unconditional contractibility sentence is neither claimed nor strengthened here.
* Choices. The specification speaks of "the" map `R` and of the map `H = R ∘ f`. Both are chosen in
  the conclusion: `R` is the limit map of LIP032.32 (the choice of LIP032.30), and `H` is determined by
  its values through `(H z).1 = R [f_{ν,s}]`. The same `R` serves the endpoint identities and the
  continuity, so the conclusion is about the map the specification defines.
* Codomain. `S` is `minimizerSet_LIP03225 A`, the subtype of the probability measures on the torus
  with the weak subspace topology, as in LIP032.25. Membership of each value in `S` is the
  free-energy conjunct of LIP032.32 for the chosen `R`. Continuity into `S` follows from continuity
  into the ambient probability space by the subtype criterion (LIB12).
* Parameter space. The domain is `minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1` with the product
  topology, as in LIP032.09. The endpoints `s = 0` and `s = 1` are the elements `⟨0, _⟩` and `⟨1, _⟩`
  of `Set.Icc (0 : ℝ) 1`. The endpoint value `μ` is the subtype element `⟨μ, hμ⟩`.
* Endpoint identities. The interpolation density at `s = 0` is `p_ν`, as a function (LIP032.40,
  lemma `interpol_zero_LIP03240`). At `s = 1` it is `p_μ`, as a function, since `(1 - 1) p_ν + 1 p_μ = p_μ`.
  The identities `R [p_ν] = ν` and `R [p_μ] = μ` are LIP032.10 applied to `ν` and to `μ`, with the
  choice property of LIP032.30 in the form of LIP032.32 (its flow, minimality and convergence conjuncts).
* Non-literal reading. The density `p_ν` is read as the class `l2Class_LIP03223 (gibbsDensity A ν)`,
  and `f_{ν,s}` as `interpolDensity_LIP03222 A μ ν s`, both as in LIP032.09.
* Proof route. The continuity argument is the LIP032.37 difference bound followed by the LIP032.38
  epsilon argument. Those files export the limit map only existentially, so the same `R` cannot be
  taken from them. The argument is therefore repeated here for the pair `(u, R)` of LIP032.32, using
  the same helpers. No new analytic step is introduced.
* Not stated. The identity `H (μ, s) = μ`, which the specification's proof mentions, is not part of
  the conclusion, since the statement does not list it.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- **LIP032.11.** Homotopy into the minimizing set. Under the positive-rate context of LIP032.09,
there are a limit map `R` on the `L²(m)` classes and a map `H : S × [0,1] → S` with
`H (ν, s) = R [f_{ν,s}]` such that `H` is continuous, `H (ν, 0) = ν` and `H (ν, 1) = μ` for every
minimizer `ν`. -/
theorem lip032_11_homotopy_minimizing_set (A : InteractionData d)
    (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β)
    (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ⊤ (fun x => A.W x y) (fun x => B x y))
    {r : ℝ} (hr : 0 < r) (hrate : ENNReal.ofReal r < scalarRate A drift)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (M_V M_W : ℝ) (hVb : ∀ x, |A.V x| ≤ M_V) (hWb : ∀ x y, |A.W x y| ≤ M_W) :
    ∃ (R : DGPS.Lipschitz.L2s d → ProbabilityMeasure (Torus d))
      (H : minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1 → minimizerSet_LIP03225 A),
      (∀ z : minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1,
        (H z).1 = R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ z.1.1 z.2))) ∧
      Continuous H ∧
      (∀ ν : minimizerSet_LIP03225 A, H (ν, ⟨0, by norm_num⟩) = ν) ∧
      (∀ ν : minimizerSet_LIP03225 A, H (ν, ⟨1, by norm_num⟩) = ⟨μ, hμ⟩) := by
  obtain ⟨u, R, h32⟩ :=
    lip032_32_uniform_tail_one_constant A drift hMF hV hWB hr hrate μ hμ M_V M_W hVb hWb
  -- the choice property of LIP032.30 for this pair `(u, R)`, as needed by LIP032.10
  have hzero := lip032_10_zero_gap_data_fixed A drift hMF hV hWB hr hrate μ hμ u R
    (fun ν hν s hs0 hs1 => ⟨(h32 ν hν s hs0 hs1).1, (h32 ν hν s hs0 hs1).2.1,
      (h32 ν hν s hs0 hs1).2.2.1⟩)
  -- every value lies in the minimizing set
  have hmem : ∀ z : minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1,
      freeEnergy A (R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ z.1.1 z.2))) =
        freeEnergyMinimum A :=
    fun z => (h32 z.1.1 z.1.2 z.2 z.2.2.1 z.2.2.2).2.1
  -- the difference bound of LIP032.37, for this pair `(u, R)`
  have hdiff : ∀ ν₁ ν₂ : ProbabilityMeasure (Torus d), freeEnergy A ν₁ = freeEnergyMinimum A →
      freeEnergy A ν₂ = freeEnergyMinimum A →
      ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ ≤ 1 → 0 ≤ s₂ → s₂ ≤ 1 →
      ∀ L : ℝ, 0 ≤ L → ∀ φ : Torus d → ℝ, TorusLipschitzWith L φ →
      ∀ t : ℝ, 0 ≤ t →
        |∫ x, φ x ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₁ s₁)) :
              Measure (Torus d)) -
            ∫ x, φ x ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₂ s₂)) :
              Measure (Torus d))| ≤
          2 * L * Real.sqrt (2 * (Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W) / r) *
              Real.exp (-(r * t)) +
            (⨆ x, |φ x|) * (2 * Real.exp (2 * Real.pi * (d : ℝ) * (g + 3 * β) ^ 2 * t)) *
              ∫ x, |interpolDensity_LIP03222 A μ ν₁ s₁ x - interpolDensity_LIP03222 A μ ν₂ s₂ x|
                ∂haar d := by
    intro ν₁ ν₂ hν₁ hν₂ s₁ s₂ hs₁0 hs₁1 hs₂0 hs₂1 L hL φ hφ t ht
    obtain ⟨hf₁, -, -, htail₁⟩ := h32 ν₁ hν₁ s₁ hs₁0 hs₁1
    obtain ⟨hf₂, -, -, htail₂⟩ := h32 ν₂ hν₂ s₂ hs₂0 hs₂1
    have hφc : Continuous φ := DGPS.Lipschitz.torusLipschitz_continuous hφ
    -- the two tail terms, each scaled to the Lipschitz test `φ` (LIP032.35)
    have T₁ : |∫ x, u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₁ s₁)) t x * φ x ∂haar d -
          ∫ x, φ x ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₁ s₁)) :
            Measure (Torus d))| ≤
        L * (Real.sqrt (2 * (Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W) / r) *
          Real.exp (-(r * t))) :=
      scaled_tail_bound_LIP03235
        (fun x => u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₁ s₁)) t x)
        (R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₁ s₁)) : Measure (Torus d))
        (by positivity) (fun ψ hψ => htail₁ ψ hψ t ht) hL φ hφ
    have T₂ : |∫ x, u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₂ s₂)) t x * φ x ∂haar d -
          ∫ x, φ x ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₂ s₂)) :
            Measure (Torus d))| ≤
        L * (Real.sqrt (2 * (Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W) / r) *
          Real.exp (-(r * t))) :=
      scaled_tail_bound_LIP03235
        (fun x => u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₂ s₂)) t x)
        (R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₂ s₂)) : Measure (Torus d))
        (by positivity) (fun ψ hψ => htail₂ ψ hψ t ht) hL φ hφ
    -- the middle term: the finite-time weighted-test bound of LIP032.36 for the flows
    have hmid := lip032_36_finite_time_weighted_test_bound_any_flows A hMF μ hμ ν₁ ν₂ hν₁ hν₂
      s₁ s₂ hs₁0 hs₁1 hs₂0 hs₂1 (u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₁ s₁)))
      (u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₂ s₂))) hf₁ hf₂ t ht φ hφc
    rw [integral_sub_mul_test_LIP03237
      (u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₁ s₁)) t)
      (u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₂ s₂)) t) φ hφc] at hmid
    -- the real triangle inequality through the two flow integrals
    have hchain := abs_sub_chain_LIP03237
      (∫ x, φ x ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₁ s₁)) :
        Measure (Torus d)))
      (∫ x, u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₁ s₁)) t x * φ x ∂haar d)
      (∫ x, u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₂ s₂)) t x * φ x ∂haar d)
      (∫ x, φ x ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₂ s₂)) :
        Measure (Torus d)))
    have hA : |∫ x, φ x ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₁ s₁)) :
          Measure (Torus d)) -
        ∫ x, u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₁ s₁)) t x * φ x ∂haar d| ≤
        L * (Real.sqrt (2 * (Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W) / r) *
          Real.exp (-(r * t))) := by
      rw [abs_sub_comm]
      exact T₁
    have hK : 2 * L * Real.sqrt (2 * (Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W) / r) *
        Real.exp (-(r * t)) =
        L * (Real.sqrt (2 * (Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W) / r) *
          Real.exp (-(r * t))) + L * (Real.sqrt (2 * (Real.log (Real.exp (2 * (M_V + M_W))) +
          2 * M_V + M_W) / r) * Real.exp (-(r * t))) := by
      ring
    rw [hK]
    linarith [hchain, hA, T₂, hmid]
  -- weak continuity of the limit map: the LIP032.38 argument for this pair `(u, R)`
  have hkey : ∀ φ : Torus d → ℝ, Continuous φ →
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
    exact hdiff z.1.1 z₀.1.1 z.1.2 z₀.1.2 z.2 z₀.2 z.2.2.1 z.2.2.2 z₀.2.2.1 z₀.2.2.2 L hL ψ hψ t ht
  have hweak : Continuous (fun z : minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1 =>
      R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ z.1.1 z.2))) := by
    refine continuous_iff_continuousAt.2 fun z₀ => ?_
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f => hkey f f.continuous z₀
  -- the map `H` into the subtype `S`, by the subtype criterion
  have hHc : Continuous (fun z : minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1 =>
      (⟨R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ z.1.1 z.2)), hmem z⟩ :
        minimizerSet_LIP03225 A)) :=
    Continuous.subtype_mk hweak hmem
  -- the interpolation density at `s = 1` is `p_μ`, as a function
  have hone : ∀ ν : ProbabilityMeasure (Torus d),
      interpolDensity_LIP03222 A μ ν 1 = DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d)) := by
    intro ν
    funext x
    unfold interpolDensity_LIP03222
    simp
  -- the endpoint `s = 0`: `R [p_ν] = ν` for every minimizer (LIP032.10)
  have hzero0 : ∀ ν : minimizerSet_LIP03225 A,
      R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν.1 0)) = ν.1 := by
    intro ν
    rw [interpol_zero_LIP03240]
    exact hzero ν.1 ν.2
  refine ⟨R, fun z => ⟨R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ z.1.1 z.2)), hmem z⟩,
    fun z => rfl, hHc, fun ν => Subtype.ext (hzero0 ν), ?_⟩
  -- the endpoint `s = 1`: `R [p_μ] = μ` (LIP032.10 applied to `μ`)
  intro ν
  apply Subtype.ext
  show R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν.1 1)) = μ
  rw [hone ν.1]
  exact hzero μ hμ

end DGPS.Frontier.LIP032
