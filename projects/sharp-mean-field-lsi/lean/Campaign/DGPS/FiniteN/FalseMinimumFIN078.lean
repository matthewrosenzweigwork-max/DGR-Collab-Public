import DGPS.FiniteN.FalseMinimumFIN077
import DGPS.Analysis.OneDimensionalHardy

/-!
# FIN078: auxiliary exponential lower bound for the Poincare rate at the false minimum

For `ψ = scalarPsi κ h` with `κ > 2`, `0 < h < h_c(κ)` and the FIN076 geometry, the normalized
auxiliary densities `η_N ∝ e^{-Nψ}` satisfy, for all real `N ≥ 1`,
`λ_P(η_N) ≥ c e^{-NB}` with `B = ψ(t_b) - ψ(t₋)` and a model-dependent constant `c > 0`.

The ordinary Poincare rate is `λ_P(μ) = inf E_μ(g)/Var_μ(g)` over absolutely continuous
finite-energy test functions `g` with positive variance; the infimum is taken in `ℝ≥0∞`.
The proof applies the anchored half-line Hardy bound (FIN006) with anchor `t₊`, and bounds its
two resistance constants by the product barrier of FIN077.
-/

open Filter Topology MeasureTheory Set

namespace DGPS.FiniteN.FalseMinimumFIN078

open DGPS.Models DGPS.FiniteN.ScalarFoldFIN056 DGPS.FiniteN.FalseMinimumFIN076
  DGPS.FiniteN.FalseMinimumFIN077

/-- Admissible test pair for the ordinary Poincare rate on `I` with density `p`: `g` is absolutely
continuous on `I` with derivative `g'` in the fundamental-theorem form, `g'` is locally integrable,
the energy `∫ (g')² dμ` is finite, and `Var_μ g > 0`. -/
def PoincareTestFIN078 (I : Set ℝ) (p : ℝ → ℝ) (g g' : ℝ → ℝ) : Prop :=
  (∀ x ∈ I, ∀ y ∈ I, g y - g x = ∫ t in x..y, g' t) ∧ LocallyIntegrableOn g' I volume ∧
    Integrable (fun x => g' x ^ 2) (DGPS.FiniteN.densityMeasure I p) ∧
    0 < ProbabilityTheory.variance g (DGPS.FiniteN.densityMeasure I p)

/-- The ordinary Poincare rate `λ_P(μ) = inf E_μ(g)/Var_μ(g)` of `μ = densityMeasure I p`, the
infimum running over admissible pairs `(g, g')`; it is valued in `ℝ≥0∞`, so an empty
family would give `⊤`. -/
noncomputable def poincareRateFIN078 (I : Set ℝ) (p : ℝ → ℝ) : ENNReal :=
  ⨅ (g : ℝ → ℝ) (g' : ℝ → ℝ) (_ : PoincareTestFIN078 I p g g'),
    ENNReal.ofReal (∫ x, g' x ^ 2 ∂(DGPS.FiniteN.densityMeasure I p)) /
      ENNReal.ofReal (ProbabilityTheory.variance g (DGPS.FiniteN.densityMeasure I p))

section Bridge

theorem measure_toReal_FIN078 (ψ : ℝ → ℝ) (N : ℝ) (hcont : Continuous ψ)
    (hZ : 0 < ∫ y, Real.exp (-(N * ψ y))) {s : Set ℝ} (hs : MeasurableSet s) :
    (DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N) s).toReal =
      (∫ y in s, Real.exp (-(N * ψ y))) / ∫ y, Real.exp (-(N * ψ y)) := by
  rw [DGPS.FiniteN.densityMeasure_apply hs (Set.subset_univ _)]
  have hcont' : Continuous fun y => Real.exp (-(N * ψ y)) := by
    have := hcont; fun_prop
  have hnn : 0 ≤ᵐ[volume.restrict s] fun x => auxDensityFIN077 ψ N x :=
    Filter.Eventually.of_forall fun x => div_nonneg (Real.exp_pos _).le hZ.le
  have hm : AEStronglyMeasurable (auxDensityFIN077 ψ N) (volume.restrict s) := by
    unfold auxDensityFIN077
    exact (hcont'.div_const _).aestronglyMeasurable
  rw [← integral_eq_lintegral_of_nonneg_ae hnn hm]
  unfold auxDensityFIN077
  rw [integral_div]

theorem mass_one_FIN078 (ψ : ℝ → ℝ) (N : ℝ) (hint : Integrable fun y => Real.exp (-(N * ψ y)))
    (hZ : 0 < ∫ y, Real.exp (-(N * ψ y))) :
    DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N) Set.univ = 1 := by
  rw [DGPS.FiniteN.densityMeasure_apply MeasurableSet.univ (Set.subset_univ _),
    Measure.restrict_univ]
  have hpi : Integrable (auxDensityFIN077 ψ N) := by
    unfold auxDensityFIN077
    exact hint.div_const _
  have hnn : 0 ≤ᵐ[volume] auxDensityFIN077 ψ N :=
    Filter.Eventually.of_forall fun x => div_nonneg (Real.exp_pos _).le hZ.le
  rw [← ofReal_integral_eq_lintegral_ofReal hpi hnn]
  have hI : ∫ x, auxDensityFIN077 ψ N x = 1 := by
    unfold auxDensityFIN077
    rw [integral_div, div_self hZ.ne']
  rw [hI, ENNReal.ofReal_one]

theorem right_bridge_FIN078 (ψ : ℝ → ℝ) (N : ℝ) (hcont : Continuous ψ)
    (hZ : 0 < ∫ y, Real.exp (-(N * ψ y))) (a x : ℝ) :
    (DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N) (Set.Ici x)).toReal *
        ∫ t in a..x, (auxDensityFIN077 ψ N t)⁻¹ =
      (∫ y in Set.Ioi x, Real.exp (-(N * ψ y))) * ∫ t in a..x, Real.exp (N * ψ t) := by
  have hZne : (∫ y, Real.exp (-(N * ψ y))) ≠ 0 := hZ.ne'
  rw [measure_toReal_FIN078 ψ N hcont hZ measurableSet_Ici, inv_integral_FIN077 ψ N,
    ← setIntegral_congr_set (Ioi_ae_eq_Ici (μ := volume) (a := x))]
  field_simp

theorem left_bridge_FIN078 (ψ : ℝ → ℝ) (N : ℝ) (hcont : Continuous ψ)
    (hZ : 0 < ∫ y, Real.exp (-(N * ψ y))) (a x : ℝ) :
    (DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N) (Set.Iic x)).toReal *
        ∫ t in x..a, (auxDensityFIN077 ψ N t)⁻¹ =
      (∫ y in Set.Iic x, Real.exp (-(N * ψ y))) * ∫ t in x..a, Real.exp (N * ψ t) := by
  have hZne : (∫ y, Real.exp (-(N * ψ y))) ≠ 0 := hZ.ne'
  rw [measure_toReal_FIN078 ψ N hcont hZ measurableSet_Iic, inv_integral_FIN077 ψ N]
  field_simp

/-- Core rate bound: if the two one-sided products of `e^{-Nψ}` and `e^{Nψ}` anchored at `tp`
are bounded by `C e^{NB}`, then `λ_P(η_N) ≥ (1/(4C)) e^{-NB}`. -/
theorem rate_lower_FIN078 (ψ : ℝ → ℝ) (N : ℝ) (hcont : Continuous ψ) (tp C B : ℝ) (hC : 0 < C)
    (hint : Integrable fun y => Real.exp (-(N * ψ y)))
    (hR : ∀ x : ℝ, tp ≤ x →
      (∫ y in Set.Ioi x, Real.exp (-(N * ψ y))) * (∫ z in tp..x, Real.exp (N * ψ z)) ≤
        C * Real.exp (N * B))
    (hL : ∀ x : ℝ, x ≤ tp →
      (∫ y in Set.Iic x, Real.exp (-(N * ψ y))) * (∫ z in x..tp, Real.exp (N * ψ z)) ≤
        C * Real.exp (N * B)) :
    ENNReal.ofReal (1 / (4 * C) * Real.exp (-(N * B))) ≤
      poincareRateFIN078 Set.univ (auxDensityFIN077 ψ N) := by
  have hZ : 0 < ∫ y, Real.exp (-(N * ψ y)) :=
    integral_exp_pos (f := fun y => -(N * ψ y)) hint
  have : IsProbabilityMeasure (DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N)) :=
    ⟨mass_one_FIN078 ψ N hint hZ⟩
  have hpc : ContinuousOn (auxDensityFIN077 ψ N) Set.univ := by
    refine Continuous.continuousOn ?_
    unfold auxDensityFIN077
    have hc' : Continuous fun y => Real.exp (-(N * ψ y)) := by
      have := hcont; fun_prop
    exact hc'.div_const _
  have hp0 : ∀ x ∈ (Set.univ : Set ℝ), 0 < auxDensityFIN077 ψ N x := fun x _ =>
    div_pos (Real.exp_pos _) hZ
  have hBp : BddAbove ((fun x => (DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N)
      (Set.Ici x)).toReal * ∫ t in tp..x, (auxDensityFIN077 ψ N t)⁻¹) ''
        (Set.univ ∩ Set.Ioi tp)) := by
    refine ⟨C * Real.exp (N * B), ?_⟩
    rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    exact (le_of_eq (right_bridge_FIN078 ψ N hcont hZ tp x)).trans (hR x (le_of_lt hx))
  have hBm : BddAbove ((fun x => (DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N)
      (Set.Iic x)).toReal * ∫ t in x..tp, (auxDensityFIN077 ψ N t)⁻¹) ''
        (Set.univ ∩ Set.Iio tp)) := by
    refine ⟨C * Real.exp (N * B), ?_⟩
    rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    exact (le_of_eq (left_bridge_FIN078 ψ N hcont hZ tp x)).trans (hL x (le_of_lt hx))
  have hRc : DGPS.FiniteN.rightResistanceConstant Set.univ (auxDensityFIN077 ψ N) tp ≤
      C * Real.exp (N * B) := by
    refine csSup_le ⟨_, tp + 1, ⟨Set.mem_univ _, by simp⟩, rfl⟩ ?_
    rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    exact (le_of_eq (right_bridge_FIN078 ψ N hcont hZ tp x)).trans (hR x (le_of_lt hx))
  have hLc : DGPS.FiniteN.leftResistanceConstant Set.univ (auxDensityFIN077 ψ N) tp ≤
      C * Real.exp (N * B) := by
    refine csSup_le ⟨_, tp - 1, ⟨Set.mem_univ _, by simp⟩, rfl⟩ ?_
    rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    exact (le_of_eq (left_bridge_FIN078 ψ N hcont hZ tp x)).trans (hL x (le_of_lt hx))
  have hmax : max (DGPS.FiniteN.rightResistanceConstant Set.univ (auxDensityFIN077 ψ N) tp)
      (DGPS.FiniteN.leftResistanceConstant Set.univ (auxDensityFIN077 ψ N) tp) ≤
        C * Real.exp (N * B) := max_le hRc hLc
  have hc0 : 0 ≤ 1 / (4 * C) * Real.exp (-(N * B)) :=
    mul_nonneg (div_nonneg zero_le_one (by linarith)) (Real.exp_pos _).le
  have hexp : Real.exp (N * B) ≠ 0 := (Real.exp_pos _).ne'
  refine le_iInf fun g => le_iInf fun g' => le_iInf fun hadm => ?_
  obtain ⟨hf, hf', hE, hVpos⟩ := hadm
  have hvar := (anchored_half_line_resistance_poincare isOpen_univ ordConnected_univ
    (Set.mem_univ tp) hpc hp0 hBp hBm hf hf' hE).2.2.2
  have hE0 : 0 ≤ ∫ x, g' x ^ 2 ∂(DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N)) :=
    integral_nonneg fun x => sq_nonneg _
  have hVle : ProbabilityTheory.variance g
      (DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N)) ≤
        4 * (C * Real.exp (N * B)) *
          ∫ x, g' x ^ 2 ∂(DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N)) :=
    le_trans hvar (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax (by norm_num)) hE0)
  have hkey : 1 / (4 * C) * Real.exp (-(N * B)) *
      ProbabilityTheory.variance g (DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N)) ≤
        ∫ x, g' x ^ 2 ∂(DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N)) := by
    calc 1 / (4 * C) * Real.exp (-(N * B)) *
          ProbabilityTheory.variance g (DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N))
        ≤ 1 / (4 * C) * Real.exp (-(N * B)) *
          (4 * (C * Real.exp (N * B)) *
            ∫ x, g' x ^ 2 ∂(DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N))) :=
          mul_le_mul_of_nonneg_left hVle hc0
      _ = ∫ x, g' x ^ 2 ∂(DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N)) := by
          rw [Real.exp_neg]
          have hC0 : C ≠ 0 := hC.ne'
          field_simp
  have hVne0 : ENNReal.ofReal
      (ProbabilityTheory.variance g (DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N)))
        ≠ 0 :=
    (ENNReal.ofReal_pos.2 hVpos).ne'
  have hVneTop : ENNReal.ofReal
      (ProbabilityTheory.variance g (DGPS.FiniteN.densityMeasure Set.univ (auxDensityFIN077 ψ N)))
        ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  rw [ENNReal.le_div_iff_mul_le (Or.inl hVne0) (Or.inl hVneTop), ← ENNReal.ofReal_mul hc0]
  exact ENNReal.ofReal_le_ofReal hkey

end Bridge

theorem scalarPsi_continuous_FIN078 {κ h : ℝ} (hκ : 0 < κ) : Continuous (scalarPsi κ h) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_scalarPsi_FIN056 hκ h t).continuousAt

/-- **FIN078.** For `κ > 2`, `0 < h < h_c(κ)`, there are FIN076 geometric parameters
`0 < s₁ < s_c < s₂`, `t₊ = tp > 0` and a constant `c > 0` such that, with
`B = ψ(-s₁) - ψ(-s₂)` for `ψ = scalarPsi κ h`, the auxiliary Poincare rate of the normalized
density `η_N ∝ e^{-Nψ}` obeys `λ_P(η_N) ≥ c e^{-NB}` for every real `N ≥ 1`. -/
theorem false_minimum_auxiliary_exponential_lower (κ h : ℝ) (hκ : 2 < κ) (hh0 : 0 < h)
    (hhc : h < scalarFoldField κ) :
    ∃ s1 s2 tp : ℝ, 0 < s1 ∧ s1 < scalarFoldPoint κ ∧ scalarFoldPoint κ < s2 ∧ 0 < tp ∧
      FalseMinimumGeometryFIN076 κ h s1 s2 tp ∧
      ∃ c : ℝ, 0 < c ∧ ∀ N : ℝ, 1 ≤ N →
        ENNReal.ofReal (c * Real.exp (-(N * (scalarPsi κ h (-s1) - scalarPsi κ h (-s2))))) ≤
          poincareRateFIN078 Set.univ (auxDensityFIN077 (scalarPsi κ h) N) := by
  obtain ⟨s1, s2, tp, h1, h2, h3, h4, G, C, hC, hbd⟩ :=
    false_minimum_resistance_product_barrier_upper κ h hκ hh0 hhc
  refine ⟨s1, s2, tp, h1, h2, h3, h4, G, 1 / (4 * C), div_pos one_pos (by linarith),
    fun N hN => ?_⟩
  obtain ⟨hint, hL, hR⟩ := hbd N hN
  exact rate_lower_FIN078 (scalarPsi κ h) N (scalarPsi_continuous_FIN078 (by linarith)) tp C
    (scalarPsi κ h (-s1) - scalarPsi κ h (-s2)) hC hint hR hL

end DGPS.FiniteN.FalseMinimumFIN078
