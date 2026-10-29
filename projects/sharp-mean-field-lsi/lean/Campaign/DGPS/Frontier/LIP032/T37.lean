import DGPS.Frontier.LIP032.T35
import DGPS.Frontier.LIP032.T36

/-!
# LIP032.37: Difference of limiting tests

Task id and title: LIP032.37, "Difference of limiting tests" (node LIP032, contractibility of the
minimizer set; the difference estimate of LIP032.08, conditional on the Task 29 bindings and on the
positive-rate flow context of LIP031, inherited through Tasks 30, 32, 35 and 36).

## Provides
* `DGPS.Frontier.LIP032.lip032_37_difference_limiting_tests` : MAIN. Under the exact positive-rate
  context of LIP031, a fixed minimizer `μ`, and bounds `|A.V| ≤ M_V`, `|A.W| ≤ M_W`, there are
  a choice function `R` on the `L²(m)` classes such that, for all minimizers `ν₁, ν₂`, all
  `s₁, s₂ ∈ [0,1]`, every `L ≥ 0`, every `L`-Lipschitz `φ` and every `t ≥ 0`, with
  `c_i = [f_{ν_i,s_i}]`,
  `|∫ φ d(R c₁) - ∫ φ d(R c₂)| ≤ 2 L K e^{-rt} + ‖φ‖∞ Σ(t) ‖f₁ - f₂‖₁`, where
  `K = √(2 G_0 / r)`, `G_0 = log C + 2 M_V + M_W`, `C = exp (2 (M_V + M_W))`,
  `Σ(t) = 2 exp (2π d (g+3β)² t)`, `‖φ‖∞ = ⨆ x, |φ x|` and `‖f₁ - f₂‖₁ = ∫ |f₁ - f₂| dm`.
* `integrable_l2s_mul_test_LIP03237` (helper) : for `f ∈ L²(m)` and a continuous real `φ`, the
  product `f φ` is integrable with respect to Haar measure.
* `integral_sub_mul_test_LIP03237` (helper) : `∫ (f - f') φ dm = ∫ f φ dm - ∫ f' φ dm` for
  `f, f' ∈ L²(m)` and continuous `φ`.
* `abs_sub_chain_LIP03237` (helper) : the real chain inequality `|x - w| ≤ |x - y| + |y - z| + |z - w|`,
  which is the real triangle inequality with the three terms of the proof.

## R5 notes
* Inherited hypotheses. The binders `A`, `drift`, `G`, `B`, `g`, `β`, `hMF`, `hV`, `hWB`, `r`,
  `hr`, `hrate`, `μ`, `hμ`, `M_V`, `M_W`, `hVb`, `hWb` are exactly those of LIP032.35 (and of
  LIP032.32). Nothing is added and nothing is removed. The unconditional reading of the frozen
  contractibility sentence is neither claimed nor strengthened here (FD-001).
* Interpolation pairs. The Task 08 sentence "for interpolation densities `f, f̃`" is read as
  `f = f_{ν₁,s₁}` and `f̃ = f_{ν₂,s₂}` with `ν₁, ν₂` minimizers (the extended equation
  `freeEnergy A ν = freeEnergyMinimum A`) and `s₁, s₂ ∈ [0,1]`, as in LIP032.32, LIP032.35 and
  LIP032.36. The classes are `l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)`.
* Choice function. The conclusion is existential over `R` only. The statement of Task 08 mentions
  the limit map `R(f)` alone, so no flow `u` appears in it, and `∃ u R, P R` is equivalent to
  `∃ R, P R`. Inside the proof, one pair `(u, R)` from LIP032.32 serves both the tail terms and the
  middle term: the tail terms come from the tail conjunct of LIP032.32 through the helper of
  LIP032.35, and the middle term applies the `_any_flows` form of LIP032.36 to the flow conjunct of
  LIP032.32, which is the global-probability-flow property for the same `u`.
* The limit map. `R(f)(φ)` is `∫ x, φ x ∂(R c : Measure (Torus d))`, as in LIP032.32.
* Tests. "`L`-Lipschitz" is `TorusLipschitzWith L` for the Euclidean quotient distance, with only
  `0 ≤ L` assumed, as in LIP032.35. Continuity of `φ` is derived from `TorusLipschitzWith`
  (`torusLipschitz_continuous`), which is what the middle term needs.
* Sup norm. `‖φ‖∞` is read as `⨆ x, |φ x|`, as in LIP032.36. The bound is stated for the
  Lipschitz test `φ`; its supremum is finite because `φ` is continuous on the compact torus.
* Norm. `‖f₁ - f₂‖₁` is read as the real integral `∫ |f₁ x - f₂ x| dm` of the continuous
  interpolation densities, as in LIP032.36.
* Constant. `K` is written literally as `Real.sqrt (2 * G_0 / r)`, with
  `G_0 = Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W`, and the first term is written
  `2 * L * K * Real.exp (-(r * t))` with `L` on the left, exactly as in LIP032.35. The middle factor is
  `(⨆ x, |φ x|) * (2 * Real.exp (2 * Real.pi * d * (g + 3 * β) ^ 2 * t))`, exactly the LIP028 factor
  used in LIP032.36.
* Sign normalization. The difference `R₁ - R₂` is split as `(R₁ - U₁) + (U₁ - U₂) + (U₂ - R₂)`, where
  `U_i = ∫ u c_i t φ dm`. The two tail terms are brought to the form `|U_i - R_i|` of LIP032.35 by
  `abs_sub_comm` (for the first one only), and the middle term is `|U₁ - U₂|` after rewriting
  `∫ (u₁ - u₂) φ dm = ∫ u₁ φ dm - ∫ u₂ φ dm`.
* Integrability. The splitting of the middle integral needs integrability of `f φ` for `f ∈ L²(m)` and
  continuous `φ`. It is proved inside the file (helpers above, using that the continuous `φ` is bounded
  on the compact torus); no further hypothesis is added.
* Case `L = 0`. No separate case is needed: the helper of LIP032.35 covers every `L ≥ 0`.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- Helper: for an `L²(m)` class `f` and a continuous real test `φ`, the product `f φ` is integrable
with respect to Haar measure. The class is integrable on the probability space, and the continuous
`φ` is bounded on the compact torus by its supremum. -/
theorem integrable_l2s_mul_test_LIP03237 (f : DGPS.Lipschitz.L2s d) (φ : Torus d → ℝ)
    (hφ : Continuous φ) : Integrable (fun x => f x * φ x) (haar d) := by
  have hint : Integrable (fun x => f x) (haar d) := (Lp.memLp f).integrable (by norm_num)
  have hbdd : BddAbove (Set.range fun x => |φ x|) := (isCompact_range hφ.abs).bddAbove
  have hMφ : ∀ x, |φ x| ≤ ⨆ x, |φ x| := fun x => le_ciSup hbdd x
  refine Integrable.mono' (hint.abs.const_mul (⨆ x, |φ x|))
    (hint.aestronglyMeasurable.mul hφ.measurable.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  show ‖f x * φ x‖ ≤ (⨆ x, |φ x|) * |f x|
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul_of_nonneg_left (hMφ x) (abs_nonneg _)).trans_eq (mul_comm _ _)

/-- Helper: the integral of the product of a difference of two `L²(m)` classes with a continuous
test splits into the difference of the two integrals of the products. -/
theorem integral_sub_mul_test_LIP03237 (f f' : DGPS.Lipschitz.L2s d) (φ : Torus d → ℝ)
    (hφ : Continuous φ) :
    ∫ x, (f x - f' x) * φ x ∂haar d = ∫ x, f x * φ x ∂haar d - ∫ x, f' x * φ x ∂haar d := by
  simp only [sub_mul]
  exact integral_sub (integrable_l2s_mul_test_LIP03237 f φ hφ)
    (integrable_l2s_mul_test_LIP03237 f' φ hφ)

/-- Helper: the real chain inequality behind the decomposition `x - w = (x - y) + (y - z) + (z - w)`. -/
theorem abs_sub_chain_LIP03237 (x y z w : ℝ) :
    |x - w| ≤ |x - y| + |y - z| + |z - w| := by
  have e : x - w = (x - y) + (y - z) + (z - w) := by ring
  rw [e]
  linarith [abs_add_le ((x - y) + (y - z)) (z - w), abs_add_le (x - y) (y - z)]

/-- **LIP032.37.** Difference of limiting tests: for a choice of limit map `R` built from the flows of LIP032.32, every pair of
minimizers `ν₁, ν₂`, every `s₁, s₂ ∈ [0,1]`, every `L ≥ 0`, every `L`-Lipschitz `φ` and every `t ≥ 0`,
`|∫ φ d(R c₁) - ∫ φ d(R c₂)| ≤ 2 L K e^{-rt} + ‖φ‖∞ Σ(t) ‖f₁ - f₂‖₁`, with `c_i = [f_{ν_i,s_i}]`. -/
theorem lip032_37_difference_limiting_tests (A : InteractionData d)
    (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β)
    (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ⊤ (fun x => A.W x y) (fun x => B x y))
    {r : ℝ} (hr : 0 < r) (hrate : ENNReal.ofReal r < scalarRate A drift)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (M_V M_W : ℝ) (hVb : ∀ x, |A.V x| ≤ M_V) (hWb : ∀ x y, |A.W x y| ≤ M_W) :
    ∃ (R : DGPS.Lipschitz.L2s d → ProbabilityMeasure (Torus d)),
      ∀ (ν₁ ν₂ : ProbabilityMeasure (Torus d)), freeEnergy A ν₁ = freeEnergyMinimum A →
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
  obtain ⟨u, R, h32⟩ :=
    lip032_32_uniform_tail_one_constant A drift hMF hV hWB hr hrate μ hμ M_V M_W hVb hWb
  refine ⟨R, fun ν₁ ν₂ hν₁ hν₂ s₁ s₂ hs₁0 hs₁1 hs₂0 hs₂1 L hL φ hφ t ht => ?_⟩
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
  -- the middle term: the finite-time weighted-test bound of LIP032.36 for the selected flows
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

end DGPS.Frontier.LIP032
