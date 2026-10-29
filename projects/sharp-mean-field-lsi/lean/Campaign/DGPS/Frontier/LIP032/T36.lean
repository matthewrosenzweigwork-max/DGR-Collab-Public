import DGPS.Frontier.LIP032.T23
import DGPS.Frontier.LIP032.T24
import DGPS.Frontier.LIP032.T30

/-!
# LIP032.36: Finite-time weighted-test bound

Task id and title: LIP032.36, "Finite-time weighted-test bound" (node LIP032, contractibility of the
minimizer set; conditional on the Task 29 bindings and on the positive-rate flow context of LIP031,
inherited through the Task 30 selection).

## Provides
* `DGPS.Frontier.LIP032.lip032_36_finite_time_weighted_test_bound` : MAIN. Under the positive-rate
  context of Task 30 there is a choice `u` of one global probability flow `u c` for each class
  `c = [f_{ν,s}]` (`ν ∈ S`, `s ∈ [0,1]`), and for all `ν₁, ν₂ ∈ S`, `s₁, s₂ ∈ [0,1]`, `t ≥ 0` and
  continuous `φ`, the weighted test difference of the selected flows at time `t` is bounded by
  `‖φ‖∞ · Σ(t) · ∫ |f₁ - f₂| dm` with `Σ(t) = 2 exp (2π d (g+3β)² t)`.
* `DGPS.Frontier.LIP032.lip032_36_finite_time_weighted_test_bound_any_flows` : the same bound for
  arbitrary global probability flows `u`, `v` started at the two classes. The main theorem is an
  instance of it, since the Task 30 flows are such flows.
* Helper declarations (`integral_abs_class_sub_eq_LIP03236`, `l1_flow_bound_LIP03236`,
  `interp_memLp_LIP03236`) carry the suffix `_LIP03236`.

## R5 notes
* Inherited hypotheses. The binders `A`, `drift`, `G`, `B`, `g`, `β`, `hMF`, `hV`, `hWB`, `r`,
  `hr`, `hrate`, `μ`, `hμ` are those of the Task 30 theorem, taken verbatim as the node's Section 2.1
  context for the flow branch. Nothing is added and nothing is removed. The unconditional reading of
  the frozen contractibility sentence is not proved or assumed here (FD-001); the present unit is the
  conditional bound.
* The rate hypotheses `hV`, `hWB`, `hr`, `hrate` and `drift` enter only through the Task 30 selection
  of flows. The bound itself uses the stability clause of LIP028 (part (2)), which needs only the two
  flows and the flow structure `hMF`.
* Bounds. The constants `M_V`, `M_W` of the node are not binders. They are obtained inside the proof
  of the interpolation-class facts from LIP032.27, as in LIP032.23 and LIP032.29.
* Minimizer membership. `ν ∈ S` is the extended-real equation `freeEnergy A ν = freeEnergyMinimum A`,
  as in the upstream units. The family `𝓘` is indexed by pairs `(ν, s)`; its member is the class
  `l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)`.
* The flows. The statement of the node speaks of "the flows selected in Task 30". The main theorem
  packages this as an existential choice `u` whose first conjunct is exactly the Task 30 selection
  property (a global probability flow started at each class of the family). The bound is proved for
  every pair of global probability flows started at the two classes (the public `_any_flows` lemma),
  so it does not depend on which selection is taken.
* Densities and norms. `[f]` and `[f̃]` are classes of the continuous interpolation densities
  `f = f_{ν₁,s₁}`, `f̃ = f_{ν₂,s₂}`. The norm `‖f - f̃‖₁` is read as the real integral
  `∫ |f x - f̃ x| dm` of the continuous representatives. It equals the `L¹` norm of the difference of
  the classes; that equality is proved inside the file, using the almost-everywhere identity of the
  classes with the densities.
* Sup norm. `‖φ‖∞` is read as `⨆ x, |φ x|`. The hypothesis "bounded continuous" is read as
  `Continuous φ` only: on the compact torus a continuous function is bounded, which the proof uses
  to show that the supremum is finite and attained as an upper bound.
* Constant. The factor is `2 * Real.exp (2 * Real.pi * (d : ℝ) * (g + 3 * β) ^ 2 * t)`, exactly the
  constant `2 exp(2π d (g+3b)² t)` of LIP028 part (2) with `b := β`. No larger constant is used.
* Time. The inequality is stated and proved for `t ≥ 0` only, the range of LIP028.
* Extended norms. The upstream stability inequality is an inequality between finite-valued extended
  norms. It is converted to a real inequality by the Task 24 identity of the extended `L¹` norm with
  `ENNReal.ofReal` of the real integral, followed by `ENNReal.ofReal_le_ofReal_iff`; no real
  inequality is read off from an infinite value. The weighted-test estimate is the last component of
  the Task 24 bridge, which also gives the integrability of the product.
* The separate finiteness of the two weighted integrals mentioned in the node's proof is not stated as
  a separate conclusion; it is the integrability part of the Task 24 bridge used internally.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- Helper: an interpolation density is in `L²(m)`, so its class is a genuine `L²` class. -/
theorem interp_memLp_LIP03236 (A : InteractionData d) (μ ν : ProbabilityMeasure (Torus d))
    (hμ : freeEnergy A μ = freeEnergyMinimum A) (hν : freeEnergy A ν = freeEnergyMinimum A)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    MemLp (interpolDensity_LIP03222 A μ ν s) 2 (haar d) := by
  obtain ⟨M_V, M_W, -, -, hV, hW⟩ := lip032_27_uniform_potential_interaction_bounds_exists A
  exact (lip032_23_canonical_l2_class_representative_transport A M_V M_W hV hW μ hμ ν hν s hs0
    hs1).1

/-- Helper: for two functions in `L²(m)`, the real `L¹` norm of the difference of their classes is
the real integral of the absolute difference of the functions. -/
theorem integral_abs_class_sub_eq_LIP03236 {f f' : Torus d → ℝ} (hf : MemLp f 2 (haar d))
    (hf' : MemLp f' 2 (haar d)) :
    ∫ x, |l2Class_LIP03223 f x - l2Class_LIP03223 f' x| ∂haar d =
      ∫ x, |f x - f' x| ∂haar d := by
  refine integral_congr_ae ?_
  filter_upwards [l2Class_coe_ae_LIP03223 hf, l2Class_coe_ae_LIP03223 hf'] with x hx hx'
  simp only [hx, hx']

/-- Helper: the real `L¹` form of the stability clause of LIP028 (part (2)). The real `L¹` norm of
the difference of two global probability flows at time `t ≥ 0` is at most `Σ(t)` times the real
`L¹` norm of the difference of their initial data. -/
theorem l1_flow_bound_LIP03236 {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d}
    {g β : ℝ} (hMF : DGPS.Lipschitz.MeanFieldData G B g β)
    (c₁ c₂ : DGPS.Lipschitz.L2s d) (u v : ℝ → DGPS.Lipschitz.L2s d)
    (hu : DGPS.Lipschitz.IsGlobalProbFlow hMF c₁ u)
    (hv : DGPS.Lipschitz.IsGlobalProbFlow hMF c₂ v) (t : ℝ) (ht : 0 ≤ t) :
    ∫ x, |u t x - v t x| ∂haar d ≤
      2 * Real.exp (2 * Real.pi * (d : ℝ) * (g + 3 * β) ^ 2 * t) *
        ∫ x, |c₁ x - c₂ x| ∂haar d := by
  have hS := (DGPS.Lipschitz.global_bounded_flow_and_l1_stability hMF).2 c₁ c₂ u v hu hv t ht
  rw [eLpNorm_one_eq_ofReal_integral_abs_LIP03224 (integrable_sub_l2s_LIP03224 (u t) (v t)),
    eLpNorm_one_eq_ofReal_integral_abs_LIP03224 (integrable_sub_l2s_LIP03224 c₁ c₂)] at hS
  have hpos : (0 : ℝ) ≤ 2 * Real.exp (2 * Real.pi * (d : ℝ) * (g + 3 * β) ^ 2 * t) := by
    positivity
  have hI : 0 ≤ ∫ x, |c₁ x - c₂ x| ∂haar d := integral_nonneg fun x => abs_nonneg _
  rw [← ENNReal.ofReal_mul hpos] at hS
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hpos hI)).1 hS

/-- **LIP032.36 (any flows).** For two global probability flows `u`, `v` started at the classes of
the interpolation densities `f₁ = f_{ν₁,s₁}` and `f₂ = f_{ν₂,s₂}` (`ν₁, ν₂ ∈ S`, `s₁, s₂ ∈ [0,1]`),
every time `t ≥ 0` and every continuous test function `φ`,
`|∫ (u t - v t) φ dm| ≤ ‖φ‖∞ · Σ(t) · ∫ |f₁ - f₂| dm`, where `Σ(t) = 2 exp (2π d (g+3β)² t)`. -/
theorem lip032_36_finite_time_weighted_test_bound_any_flows (A : InteractionData d)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (ν₁ ν₂ : ProbabilityMeasure (Torus d))
    (hν₁ : freeEnergy A ν₁ = freeEnergyMinimum A) (hν₂ : freeEnergy A ν₂ = freeEnergyMinimum A)
    (s₁ s₂ : ℝ) (hs₁0 : 0 ≤ s₁) (hs₁1 : s₁ ≤ 1) (hs₂0 : 0 ≤ s₂) (hs₂1 : s₂ ≤ 1)
    (u v : ℝ → DGPS.Lipschitz.L2s d)
    (hu : DGPS.Lipschitz.IsGlobalProbFlow hMF
      (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₁ s₁)) u)
    (hv : DGPS.Lipschitz.IsGlobalProbFlow hMF
      (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₂ s₂)) v)
    (t : ℝ) (ht : 0 ≤ t) (φ : Torus d → ℝ) (hφ : Continuous φ) :
    |∫ x, (u t x - v t x) * φ x ∂haar d| ≤
      (⨆ x, |φ x|) * (2 * Real.exp (2 * Real.pi * (d : ℝ) * (g + 3 * β) ^ 2 * t)) *
        ∫ x, |interpolDensity_LIP03222 A μ ν₁ s₁ x - interpolDensity_LIP03222 A μ ν₂ s₂ x|
          ∂haar d := by
  have hm₁ := interp_memLp_LIP03236 A μ ν₁ hμ hν₁ s₁ hs₁0 hs₁1
  have hm₂ := interp_memLp_LIP03236 A μ ν₂ hμ hν₂ s₂ hs₂0 hs₂1
  have hflow := l1_flow_bound_LIP03236 hMF _ _ u v hu hv t ht
  rw [integral_abs_class_sub_eq_LIP03236 hm₁ hm₂] at hflow
  have hbdd : BddAbove (Set.range fun x => |φ x|) := (isCompact_range hφ.abs).bddAbove
  have hM0 : 0 ≤ ⨆ x, |φ x| := (abs_nonneg (φ 0)).trans (le_ciSup hbdd 0)
  have hMφ : ∀ x, |φ x| ≤ ⨆ x, |φ x| := fun x => le_ciSup hbdd x
  have htest := (lip032_24_real_l1_ennreal_norm_bridge (u t) (v t) φ hφ.measurable
    (⨆ x, |φ x|) hM0 hMφ).2.2.2.2.2
  refine htest.trans ?_
  refine (mul_le_mul_of_nonneg_left hflow hM0).trans (le_of_eq ?_)
  ring

/-- **LIP032.36.** Finite-time weighted-test bound for the Task 30 flows. Under the positive-rate
context of Task 30, there is a choice `u` of global probability flows started at the classes
`[f_{ν,s}]` (`ν ∈ S`, `s ∈ [0,1]`) such that, for `ν₁, ν₂ ∈ S`, `s₁, s₂ ∈ [0,1]`, `t ≥ 0` and every
continuous `φ`, `|∫ (u[f₁] t - u[f₂] t) φ dm| ≤ ‖φ‖∞ Σ(t) ‖f₁ - f₂‖₁`. -/
theorem lip032_36_finite_time_weighted_test_bound (A : InteractionData d)
    (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β)
    (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ⊤ (fun x => A.W x y) (fun x => B x y))
    {r : ℝ} (hr : 0 < r) (hrate : ENNReal.ofReal r < scalarRate A drift)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A) :
    ∃ u : DGPS.Lipschitz.L2s d → ℝ → DGPS.Lipschitz.L2s d,
      (∀ ν : ProbabilityMeasure (Torus d), freeEnergy A ν = freeEnergyMinimum A →
        ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
          DGPS.Lipschitz.IsGlobalProbFlow hMF
            (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))
            (u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)))) ∧
      ∀ (ν₁ ν₂ : ProbabilityMeasure (Torus d)), freeEnergy A ν₁ = freeEnergyMinimum A →
        freeEnergy A ν₂ = freeEnergyMinimum A →
        ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ ≤ 1 → 0 ≤ s₂ → s₂ ≤ 1 →
        ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus d → ℝ, Continuous φ →
          |∫ x, (u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₁ s₁)) t x -
              u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₂ s₂)) t x) * φ x ∂haar d| ≤
            (⨆ x, |φ x|) * (2 * Real.exp (2 * Real.pi * (d : ℝ) * (g + 3 * β) ^ 2 * t)) *
              ∫ x, |interpolDensity_LIP03222 A μ ν₁ s₁ x - interpolDensity_LIP03222 A μ ν₂ s₂ x|
                ∂haar d := by
  obtain ⟨u, _R, hspec⟩ :=
    lip032_30_choose_one_flow_one_limiting_probability A drift hMF hV hWB hr hrate μ hμ
  refine ⟨u, fun ν hν s hs0 hs1 => (hspec ν hν s hs0 hs1).1, ?_⟩
  intro ν₁ ν₂ hν₁ hν₂ s₁ s₂ hs₁0 hs₁1 hs₂0 hs₂1 t ht φ hφ
  exact lip032_36_finite_time_weighted_test_bound_any_flows A hMF μ hμ ν₁ ν₂ hν₁ hν₂ s₁ s₂
    hs₁0 hs₁1 hs₂0 hs₂1 _ _ (hspec ν₁ hν₁ s₁ hs₁0 hs₁1).1 (hspec ν₂ hν₂ s₂ hs₂0 hs₂1).1
    t ht φ hφ

end DGPS.Frontier.LIP032
