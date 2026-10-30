import DGPS.Lipschitz.FlatReducedEnergy
import DGPS.Lipschitz.T01EquilibriumBridge
import DGPS.Structural.FrozenGibbsIdentities

/-!
# Continuous Gibbs ratios for the direct-Lipschitz minimizer charts

All probability measures use their weak topology; continuous functions use the uniform norm.
-/

open MeasureTheory Filter Topology

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- The frozen density with its continuous representative. -/
noncomputable def t01FrozenDensityC (A : InteractionData d)
    (ν : ProbabilityMeasure (Torus d)) : C(Torus d, ℝ) :=
  ⟨(frozenGibbs A ν).density, frozenDensity_continuous A _⟩

/-- Weak convergence of the input is uniform convergence of its frozen density. -/
theorem t01_continuous_frozenDensityC (A : InteractionData d) :
    Continuous (t01FrozenDensityC A) := by
  rw [continuous_iff_continuousAt]
  intro ν
  change Tendsto (t01FrozenDensityC A) (𝓝 ν) (𝓝 (t01FrozenDensityC A ν))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hU := DGPS.Structural.frozenGibbs_weak_to_uniform A
    (fun ν' : ProbabilityMeasure (Torus d) => ν') ν tendsto_id
  filter_upwards [Metric.tendstoUniformly_iff.mp hU (ε / 2) (by positivity)] with ν' hν'
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ((ContinuousMap.norm_le _ (by positivity : 0 ≤ ε / 2)).mpr
    fun x => ?_) (by linarith)
  have hx := hν' x
  change ‖(frozenGibbs A ν').density x - (frozenGibbs A ν).density x‖ ≤ ε / 2
  simpa only [Real.norm_eq_abs, Real.dist_eq, abs_sub_comm] using hx.le

/-- The reciprocal of a fixed frozen density, using its everywhere-positive representative. -/
noncomputable def t01FrozenDensityInvC (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) : C(Torus d, ℝ) :=
  ⟨fun x => ((frozenGibbs A μ).density x)⁻¹,
    (frozenDensity_continuous A _).inv₀ fun x =>
      (lt_of_lt_of_le (Real.exp_pos _) (frozenDensity_bounds A _ x).1).ne'⟩

/-- The relative Gibbs perturbation `p_ν / p_μ - 1`. -/
noncomputable def t01GibbsRatio (A : InteractionData d)
    (μ ν : ProbabilityMeasure (Torus d)) : C(Torus d, ℝ) :=
  t01FrozenDensityC A ν * t01FrozenDensityInvC A μ - 1

theorem t01GibbsRatio_apply (A : InteractionData d)
    (μ ν : ProbabilityMeasure (Torus d)) (x : Torus d) :
    t01GibbsRatio A μ ν x =
      (frozenGibbs A ν).density x / (frozenGibbs A μ).density x - 1 := rfl

/-- The Gibbs-ratio map is weak-to-uniform continuous. -/
theorem t01_continuous_gibbsRatio (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) : Continuous (t01GibbsRatio A μ) :=
  ((t01_continuous_frozenDensityC A).mul continuous_const).sub continuous_const

theorem t01GibbsRatio_self (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) : t01GibbsRatio A μ μ = 0 := by
  ext x
  have hpos : 0 < (frozenGibbs A μ).density x :=
    lt_of_lt_of_le (Real.exp_pos _) (frozenDensity_bounds A _ x).1
  simp [t01GibbsRatio_apply, hpos.ne']

/-- Gibbs ratios are always in the open positive perturbation domain. -/
theorem t01GibbsRatio_pos (A : InteractionData d)
    (μ ν : ProbabilityMeasure (Torus d)) : t01GibbsRatio A μ ν ∈ posSet (Torus d) := by
  intro x
  have hμ : 0 < (frozenGibbs A μ).density x :=
    lt_of_lt_of_le (Real.exp_pos _) (frozenDensity_bounds A _ x).1
  have hν : 0 < (frozenGibbs A ν).density x :=
    lt_of_lt_of_le (Real.exp_pos _) (frozenDensity_bounds A _ x).1
  rw [t01GibbsRatio_apply]
  linarith [div_pos hν hμ]

/-- Multiplication by the base density recovers the frozen density exactly. -/
theorem t01_frozenDensity_eq_ratio (A : InteractionData d)
    (μ ν : ProbabilityMeasure (Torus d)) (x : Torus d) :
    (frozenGibbs A ν).density x =
      (frozenGibbs A μ).density x * (1 + t01GibbsRatio A μ ν x) := by
  have hμ : (frozenGibbs A μ).density x ≠ 0 :=
    (lt_of_lt_of_le (Real.exp_pos _) (frozenDensity_bounds A _ x).1).ne'
  rw [t01GibbsRatio_apply]
  field_simp
  <;> ring

/-- Relative Gibbs density reconstruction, valid for every frozen input. -/
theorem t01_frozenMeasure_eq_perturb (A : InteractionData d)
    (μ ν : ProbabilityMeasure (Torus d)) :
    (frozenGibbs A ν).measure =
      perturb (frozenGibbs A μ).measure (fun x => 1 + t01GibbsRatio A μ ν x) := by
  have hm : Measurable (fun x => ENNReal.ofReal ((frozenGibbs A μ).density x)) :=
    (frozenGibbs A μ).measurable_ofReal_density
  have hr : Measurable (fun x => ENNReal.ofReal (1 + t01GibbsRatio A μ ν x)) := by
    fun_prop
  unfold perturb BoundedPositiveReference.measure
  rw [← withDensity_mul _ hm hr]
  congr 1
  funext x
  change ENNReal.ofReal ((frozenGibbs A ν).density x) =
    ENNReal.ofReal ((frozenGibbs A μ).density x) *
      ENNReal.ofReal (1 + t01GibbsRatio A μ ν x)
  have hnonneg : 0 ≤ (frozenGibbs A μ).density x := by
    exact (lt_of_lt_of_le (Real.exp_pos _)
      (frozenDensity_bounds A (μ : Measure (Torus d)) x).1).le
  rw [← ENNReal.ofReal_mul hnonneg, ← t01_frozenDensity_eq_ratio]

/-- At a minimizing base measure, every relative frozen perturbation has mean zero. -/
theorem t01GibbsRatio_mean_zero (A : InteractionData d)
    {μ : ProbabilityMeasure (Torus d)}
    (hμ : freeEnergy A μ = freeEnergyMinimum A) (ν : ProbabilityMeasure (Torus d)) :
    ∫ x, t01GibbsRatio A μ ν x ∂(μ : Measure (Torus d)) = 0 := by
  have hfix := DGPS.Structural.minimizer_eq_frozenGibbs A hμ
  have heq := t01_frozenMeasure_eq_perturb A μ ν
  rw [← hfix] at heq
  have hint := integral_perturb (μ := (μ : Measure (Torus d)))
    (continuous_const.add (t01GibbsRatio A μ ν).continuous)
    (fun x => (t01GibbsRatio_pos A μ ν x).le) (fun _ => (1 : ℝ))
  change (∫ x, (1 : ℝ) ∂perturb (μ : Measure (Torus d))
    (fun x => 1 + t01GibbsRatio A μ ν x)) =
      ∫ x, (1 + t01GibbsRatio A μ ν x) * 1 ∂(μ : Measure (Torus d)) at hint
  rw [← heq] at hint
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
    mul_one] at hint
  rw [integral_add (integrable_const _) (integrable_cts _ _)] at hint
  have hmass : 1 + ∫ x, t01GibbsRatio A μ ν x ∂(μ : Measure (Torus d)) = 1 := by
    simpa using hint.symm
  linarith

/-- Minimizers are recovered from their continuous relative Gibbs perturbation. -/
theorem t01_minimizer_eq_perturb (A : InteractionData d)
    {μ ν : ProbabilityMeasure (Torus d)}
    (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (hν : freeEnergy A ν = freeEnergyMinimum A) :
    (ν : Measure (Torus d)) = perturb (μ : Measure (Torus d))
      (fun x => 1 + t01GibbsRatio A μ ν x) := by
  rw [DGPS.Structural.minimizer_eq_frozenGibbs A hν,
    t01_frozenMeasure_eq_perturb, ← DGPS.Structural.minimizer_eq_frozenGibbs A hμ]

/-- Change of measure for any test, with the exact same relative Gibbs ratio. -/
theorem t01_integral_minimizer (A : InteractionData d)
    {μ ν : ProbabilityMeasure (Torus d)}
    (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (hν : freeEnergy A ν = freeEnergyMinimum A) (F : Torus d → ℝ) :
    ∫ x, F x ∂(ν : Measure (Torus d)) =
      ∫ x, (1 + t01GibbsRatio A μ ν x) * F x ∂(μ : Measure (Torus d)) := by
  rw [t01_minimizer_eq_perturb A hμ hν]
  exact integral_perturb (continuous_const.add (t01GibbsRatio A μ ν).continuous)
    (fun x => (t01GibbsRatio_pos A μ ν x).le) F

/-- A positive continuous perturbation representing a minimizer is its Gibbs ratio. -/
theorem t01GibbsRatio_eq_of_perturb (A : InteractionData d)
    {μ ν : ProbabilityMeasure (Torus d)}
    (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (hν : freeEnergy A ν = freeEnergyMinimum A)
    (h : C(Torus d, ℝ)) (hpos : ∀ x, 0 < 1 + h x)
    (heq : (ν : Measure (Torus d)) = perturb (μ : Measure (Torus d))
      (fun x => 1 + h x)) : t01GibbsRatio A μ ν = h := by
  letI : (μ : Measure (Torus d)).IsOpenPosMeasure :=
    isOpenPosMeasure_of_minimizer (DGPS.Structural.minimizer_le A hμ)
  have hdens : perturb (μ : Measure (Torus d))
      (fun x => 1 + t01GibbsRatio A μ ν x) =
      perturb (μ : Measure (Torus d)) (fun x => 1 + h x) :=
    (t01_minimizer_eq_perturb A hμ hν).symm.trans heq
  unfold perturb at hdens
  have hae := (withDensity_eq_iff_of_sigmaFinite
    ((continuous_const.add (t01GibbsRatio A μ ν).continuous).measurable.ennreal_ofReal.aemeasurable)
    ((continuous_const.add h.continuous).measurable.ennreal_ofReal.aemeasurable)).mp hdens
  have hr : (fun x => t01GibbsRatio A μ ν x) =ᵐ[(μ : Measure (Torus d))] h := by
    filter_upwards [hae] with x hx
    have hx' := congrArg ENNReal.toReal hx
    change (ENNReal.ofReal (1 + t01GibbsRatio A μ ν x)).toReal =
      (ENNReal.ofReal (1 + h x)).toReal at hx'
    rw [ENNReal.toReal_ofReal (t01GibbsRatio_pos A μ ν x).le,
      ENNReal.toReal_ofReal (hpos x).le] at hx'
    linarith
  exact ContinuousMap.ext (congrFun ((Continuous.ae_eq_iff_eq
    (μ := (μ : Measure (Torus d))) (t01GibbsRatio A μ ν).continuous h.continuous).mp hr))

/-- Weakly continuous coordinates obtained by testing against continuous kernel vectors. -/
noncomputable def t01MinimizerCoords {k : ℕ} (φ : Fin k → C(Torus d, ℝ))
    (ν : ProbabilityMeasure (Torus d)) : Par k :=
  WithLp.toLp 2 (fun i => ∫ x, φ i x ∂(ν : Measure (Torus d)))

theorem t01MinimizerCoords_apply {k : ℕ} (φ : Fin k → C(Torus d, ℝ))
    (ν : ProbabilityMeasure (Torus d)) (i : Fin k) :
    t01MinimizerCoords φ ν i = ∫ x, φ i x ∂(ν : Measure (Torus d)) := rfl

theorem t01_continuous_minimizerCoords {k : ℕ} (φ : Fin k → C(Torus d, ℝ)) :
    Continuous (t01MinimizerCoords φ) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (BoundedContinuousFunction.mkOfCompact (φ i)))

theorem t01MinimizerCoords_self {A : InteractionData d}
    {μ : ProbabilityMeasure (Torus d)} {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ) : t01MinimizerCoords φ μ = 0 := by
  ext i
  exact hφ.integral_eq_zero i

/-- On minimizing measures, probability coordinates equal the coefficients of the ratio. -/
theorem t01MinimizerCoords_eq_pair {A : InteractionData d}
    {μ ν : ProbabilityMeasure (Torus d)} {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ)
    (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (hν : freeEnergy A ν = freeEnergyMinimum A) (i : Fin k) :
    t01MinimizerCoords φ ν i =
      pairCLM (μ : Measure (Torus d)) (φ i) (t01GibbsRatio A μ ν) := by
  rw [t01MinimizerCoords_apply, t01_integral_minimizer A hμ hν]
  have hprod : Integrable (fun x => t01GibbsRatio A μ ν x * φ i x)
      (μ : Measure (Torus d)) :=
    ((t01GibbsRatio A μ ν).continuous.mul (φ i).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [add_mul, one_mul]
  rw [integral_add (integrable_cts _ _) hprod, hφ.integral_eq_zero, zero_add,
    pairCLM_apply]
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-- The complementary coordinate lies in the same fixed complement and depends continuously
on the weak probability input. -/
noncomputable def t01MinimizerComplement {A : InteractionData d}
    {μ : ProbabilityMeasure (Torus d)} {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ) (ν : ProbabilityMeasure (Torus d)) : Ysub A μ :=
  projY hφ (t01GibbsRatio A μ ν)

theorem t01_continuous_minimizerComplement {A : InteractionData d}
    {μ : ProbabilityMeasure (Torus d)} {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ) : Continuous (t01MinimizerComplement hφ) :=
  (projY hφ).continuous.comp (t01_continuous_gibbsRatio A μ)

theorem t01MinimizerComplement_self {A : InteractionData d}
    {μ : ProbabilityMeasure (Torus d)} {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ) : t01MinimizerComplement hφ μ = 0 := by
  simp only [t01MinimizerComplement, t01GibbsRatio_self, map_zero]

/-- The kernel coordinates and the fixed complementary projection reconstruct a minimizing
measure's Gibbs ratio; the two coordinates refer to the same measure. -/
theorem t01GibbsRatio_decomposition {A : InteractionData d}
    {μ ν : ProbabilityMeasure (Torus d)} {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ)
    (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (hν : freeEnergy A ν = freeEnergyMinimum A) :
    t01GibbsRatio A μ ν = phiMap φ (t01MinimizerCoords φ ν) +
      (t01MinimizerComplement hφ ν : C(Torus d, ℝ)) := by
  ext x
  rw [ContinuousMap.add_apply, phiMap_apply]
  change _ = _ + projRaw (μ : Measure (Torus d)) φ (t01GibbsRatio A μ ν) x
  rw [projRaw_apply, t01GibbsRatio_mean_zero A hμ ν]
  simp_rw [t01MinimizerCoords_eq_pair hφ hμ hν, pairCLM_apply]
  ring

end DGPS.Lipschitz
