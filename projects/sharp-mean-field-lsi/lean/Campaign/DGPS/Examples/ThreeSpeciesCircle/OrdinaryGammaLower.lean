import DGPS.Examples.ThreeSpeciesCircle.OrdinaryAllOptimizersGraph
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryTrialState
import DGPS.FiniteN.Tools.PositiveRate
import DGPS.Analysis.WeightedRateComparison
import DGPS.Structural.AmplitudePoincare

open MeasureTheory Filter Topology
open scoped ENNReal

/-!
# STR028-lower: the lower eigenvalue bound discharging `hγ`

For ordinary optimizers `ρ_j` at `h_j → 0`, `γ_j = str025_quot (h j) (ρ j) / (4π²) - 1 → 0`.

* Upper bound: the explicit trial state (`TrialState.trial_quotient`,
  `TrialState.optimizer_trial_bound`): `γ_j ≤ -16/15 h_j² + K₁ |h_j|³`.
* Lower bound: (A) the Haar Poincaré rate on `𝕋¹` is at least `4π²` (`torus_poincare`);
  (B) the Holley–Stroock-type comparison `ordinary_lsi_bounded_density_comparison` with
  oscillation `4|h|` of `log q_h` gives `λ_P(μ_h) ≥ e^{-4|h|}·4π²`;
  (C) global localization gives `‖√ρ_j - 1‖_∞ → 0`, hence `‖u_j - 1‖_∞ → 0` for the relative square
  root, and the quantitative `str025_core` gives `quotient ≥ c(η_j) λ_P(μ_{h_j})` with
  `c(η) → 1`.

The route does not use `ordinaryQuotient_gaussianEndpoint` (which is for fixed `h` and
vanishing entropy, with no uniformity in `h`).  The only side hypothesis is `h_j ≠ 0`
eventually, because the trial state `trial_quotient` is stated for `0 < |h|`.
-/

namespace DGPS.Examples.ThreeSpeciesCircle.OrdinaryGammaLower

open DGPS DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic
  DGPS.Examples.ThreeSpeciesCircle

theorem haar_poincareRate_ge_STR028_lower :
    ENNReal.ofReal (4 * Real.pi ^ 2) ≤
      poincareRate (⟨haar 1, inferInstance⟩ : ProbabilityMeasure (Torus 1)) := by
  refine (le_poincareRate_iff_forall _ _).2 ?_
  intro f hf
  have hw : IsWeakGradient f.fn f.grad :=
    ⟨f.isWeak.memLp, f.isWeak.memLp_grad, f.isWeak.ibp⟩
  have hP := DGPS.FiniteN.PositiveRate.torus_poincare hw
  have hvar : ProbabilityTheory.variance f.fn (haar 1) =
      weightedVariance (⟨haar 1, inferInstance⟩ : ProbabilityMeasure (Torus 1)) f.fn := by
    exact (ProbabilityTheory.variance_eq_integral
      f.isWeak.memLp.aestronglyMeasurable.aemeasurable).trans rfl
  have hgi : Integrable (fun x => ‖f.grad x‖ ^ 2) (haar 1) :=
    f.isWeak.memLp_grad.norm.integrable_sq
  have hE : dirichletEnergy (⟨haar 1, inferInstance⟩ : ProbabilityMeasure (Torus 1)) f =
      ENNReal.ofReal (∫ x, ‖f.grad x‖ ^ 2 ∂haar 1) := by
    unfold dirichletEnergy
    rw [ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    simp only [ProbabilityMeasure.coe_mk]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [hE, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by rw [← hvar]; exact hP)

theorem referenceRate_ge_STR028_lower (h : ℝ) :
    ENNReal.ofReal (Real.exp (-(4 * |h|))) * ENNReal.ofReal (4 * Real.pi ^ 2) ≤
      poincareRate (str025_prob h) := by
  have hosc : ∀ᵐ x ∂haar 1, ∀ᵐ y ∂haar 1,
      Real.log ((ordinaryReference h).density x / (DGPS.Structural.unitReference 1).density x) -
        Real.log ((ordinaryReference h).density y /
          (DGPS.Structural.unitReference 1).density y) ≤ 4 * |h| :=
    Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall fun y => by
      have h1 := abs_log_referenceDensity_le h x
      have h2 := abs_log_referenceDensity_le h y
      have h3 := (abs_le.1 h1).2
      have h4 := (abs_le.1 h2).1
      show Real.log (referenceDensity h x / 1) - Real.log (referenceDensity h y / 1) ≤ _
      rw [div_one, div_one]
      linarith
  have key := (ordinary_lsi_bounded_density_comparison (DGPS.Structural.unitReference 1)
    (ordinaryReference h) (4 * |h|) hosc).2.1.1
  have hU : (⟨(DGPS.Structural.unitReference 1).measure,
      (DGPS.Structural.unitReference 1).isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1)) =
      ⟨haar 1, inferInstance⟩ := Subtype.ext (DGPS.Structural.unitReference_measure 1)
  rw [hU] at key
  exact (mul_le_mul' le_rfl haar_poincareRate_ge_STR028_lower).trans key

/-- The sup-norm closeness of `√ρ_j` to `1`, from global localization. -/
theorem sqrt_uniform_STR028_lower (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (ρ : ℕ → AbsoluteDensity 1)
    (hpos : ∀ j, 0 < ordinaryEntropy (h j) (ρ j))
    (hmin : ∀ j, ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy (h j) ρ' →
      ordinaryFisher (h j) (ρ j) / (2 * ordinaryEntropy (h j) (ρ j)) ≤
        ordinaryFisher (h j) ρ' / (2 * ordinaryEntropy (h j) ρ')) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ j in atTop, ∀ᵐ y ∂haar 1, |(ρ j).sqrt y - 1| ≤ ε j := by
  have : HolderExponent (1 / 2 : ℝ) := ⟨by norm_num, by norm_num⟩
  obtain ⟨-, hloc⟩ := ordinaryOptimizer_globalLocalization h hh ρ hpos hmin
  obtain ⟨x, hx0, -, hxae⟩ := hloc (1 / 2)
  have hrho : Tendsto (fun j => rho (1 / 2 : ℝ) (x j)) atTop (𝓝 1) := by
    have := ((contDiff_rho (α := (1 / 2 : ℝ)) 0).continuous.tendsto 0).comp hx0
    rwa [rho_zero] at this
  refine ⟨fun j => ‖rho (1 / 2 : ℝ) (x j) - 1‖, ?_, ?_⟩
  · simpa using tendsto_iff_norm_sub_tendsto_zero.1 hrho
  · filter_upwards [hxae] with j hj
    filter_upwards [hj, (ρ j).sqrt_nonneg] with y hy hnn
    obtain ⟨t, rfl⟩ := bs_exists_pt y
    have h1 : (ρ j).density (pt t) = (rho (1 / 2 : ℝ) (x j)).val t := hy t rfl
    have h2 := sgv_abs_le_norm (rho (1 / 2 : ℝ) (x j) - 1) t
    have hnn' : 0 ≤ (ρ j).sqrt (pt t) := hnn
    have h3 := sgv_abs_sqrt_sub_one (g := (ρ j).density (pt t)) ((ρ j).density_nonneg _)
    have h4 : Real.sqrt ((ρ j).density (pt t)) = (ρ j).sqrt (pt t) :=
      Real.sqrt_sq hnn'
    rw [h4] at h3
    rw [h1] at h3
    refine h3.trans ?_
    simpa using h2

/-- Quantitative form of the lower bound at a single index. -/
theorem quot_lower_STR028_lower (h : ℝ) (ρ : AbsoluteDensity 1) {ε : ℝ}
    (hpos : 0 < ordinaryEntropy h ρ)
    (hε : ∀ᵐ y ∂haar 1, |ρ.sqrt y - 1| ≤ ε)
    (hη : (|ε| + (Real.exp |h| - Real.exp (-|h|))) * Real.exp |h| ≤ 1 / 2) :
    2 * (1 - ((|ε| + (Real.exp |h| - Real.exp (-|h|))) * Real.exp |h|) ^ 2 / 4) /
        (2 + 10 * ((|ε| + (Real.exp |h| - Real.exp (-|h|))) * Real.exp |h|)) *
      Real.exp (-(4 * |h|)) * (4 * Real.pi ^ 2) ≤ (str025_quot h ρ).toReal := by
  set δ : ℝ := Real.exp |h| - Real.exp (-|h|) with hδ
  have hE1 : 1 ≤ Real.exp |h| := Real.one_le_exp (abs_nonneg _)
  have hE2 : Real.exp (-|h|) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [abs_nonneg h])
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hclose : ∀ᵐ y ∂haar 1, |ρ.sqrt y - str025_w h y| ≤ |ε| + δ := by
    filter_upwards [hε] with y hy
    have hw1 := str025_w_ge h y
    have hw2 := str025_w_le h y
    have e1 : |ρ.sqrt y - 1| ≤ |ε| := hy.trans (le_abs_self _)
    have e2 : |1 - str025_w h y| ≤ δ := by
      rw [abs_le]; constructor <;> linarith
    calc |ρ.sqrt y - str025_w h y| = |(ρ.sqrt y - 1) + (1 - str025_w h y)| := by ring_nf
      _ ≤ |ρ.sqrt y - 1| + |1 - str025_w h y| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hu := str025_ae_u_close h ρ hclose
  rw [abs_of_nonneg (by positivity : 0 ≤ |ε| + δ)] at hu
  set η : ℝ := (|ε| + δ) * Real.exp |h| with hηdef
  have hη0 : 0 ≤ η := by positivity
  have hcore := str025_core h ρ hη0 hη hu hpos
  have hrate := referenceRate_ge_STR028_lower h
  have hc0 : 0 ≤ 2 * (1 - η ^ 2 / 4) / (2 + 10 * η) := by
    have : η ^ 2 ≤ 1 / 4 := by nlinarith
    apply div_nonneg
    · nlinarith
    · linarith
  have hne : str025_quot h ρ ≠ ⊤ := by
    unfold str025_quot
    exact ENNReal.div_ne_top (str025_fisher_ne_top h ρ) (mul_ne_zero two_ne_zero hpos.ne')
  have hmain : ENNReal.ofReal (2 * (1 - η ^ 2 / 4) / (2 + 10 * η) * Real.exp (-(4 * |h|)) *
      (4 * Real.pi ^ 2)) ≤ str025_quot h ρ := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hc0, mul_assoc]
    refine le_trans ?_ hcore
    exact mul_le_mul' le_rfl hrate
  have := ENNReal.toReal_mono hne hmain
  rwa [ENNReal.toReal_ofReal (by positivity)] at this

/-- **Lower eigenvalue bound for the ordinary optimizers (discharge of `hγ`).**
For `h_j → 0` (eventually nonzero) and ordinary optimizers `ρ_j` (positive entropy, minimal
quotient among positive-entropy densities), the multipliers
`γ_j = str025_quot (h j) (ρ j) / (4π²) - 1` tend to `0`.  Unconditional on `hγ` and on any trial
inequality: the upper bound is `TrialState.trial_quotient` and the lower bound is the sup-norm
localization combined with `str025_core` and the Haar Poincaré constant. -/
theorem ordinaryOptimizer_gamma_tendsto (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (hne : ∀ᶠ j in atTop, h j ≠ 0)
    (ρ : ℕ → AbsoluteDensity 1)
    (hpos : ∀ j, 0 < ordinaryEntropy (h j) (ρ j))
    (hmin : ∀ j, ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy (h j) ρ' →
      ordinaryFisher (h j) (ρ j) / (2 * ordinaryEntropy (h j) (ρ j)) ≤
        ordinaryFisher (h j) ρ' / (2 * ordinaryEntropy (h j) ρ')) :
    Tendsto (fun j => (str025_quot (h j) (ρ j)).toReal / (4 * Real.pi ^ 2) - 1)
      atTop (𝓝 0) := by
  obtain ⟨ε, hε0, hε⟩ := sqrt_uniform_STR028_lower h hh ρ hpos hmin
  have hab : Tendsto (fun j => |h j|) atTop (𝓝 0) := by simpa using hh.abs
  have hE1 : Tendsto (fun j => Real.exp |h j|) atTop (𝓝 1) := by
    simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hab
  have hE2 : Tendsto (fun j => Real.exp (-|h j|)) atTop (𝓝 1) := by
    have hn : Tendsto (fun j => -|h j|) atTop (𝓝 0) := by simpa using hab.neg
    simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hn
  have hη : Tendsto (fun j => (|ε j| + (Real.exp |h j| - Real.exp (-|h j|))) * Real.exp |h j|)
      atTop (𝓝 0) := by
    have := ((hε0.abs).add (hE1.sub hE2)).mul hE1
    simpa using this
  -- lower bound sequence
  have hlow : Tendsto (fun j =>
      2 * (1 - ((|ε j| + (Real.exp |h j| - Real.exp (-|h j|))) * Real.exp |h j|) ^ 2 / 4) /
        (2 + 10 * ((|ε j| + (Real.exp |h j| - Real.exp (-|h j|))) * Real.exp |h j|)) *
      Real.exp (-(4 * |h j|)) - 1) atTop (𝓝 0) := by
    have hc : Tendsto (fun j =>
        2 * (1 - ((|ε j| + (Real.exp |h j| - Real.exp (-|h j|))) * Real.exp |h j|) ^ 2 / 4) /
          (2 + 10 * ((|ε j| + (Real.exp |h j| - Real.exp (-|h j|))) * Real.exp |h j|)))
        atTop (𝓝 1) := by
      have h1 := (tendsto_const_nhds (x := (2 : ℝ))).mul
        (tendsto_const_nhds (x := (1 : ℝ)) |>.sub ((hη.pow 2).div_const 4))
      have h2 := (tendsto_const_nhds (x := (2 : ℝ))).add (hη.const_mul 10)
      convert h1.div h2 (by norm_num) using 2
      norm_num
    have he : Tendsto (fun j => Real.exp (-(4 * |h j|))) atTop (𝓝 1) := by
      have hn : Tendsto (fun j => -(4 * |h j|)) atTop (𝓝 0) := by
        simpa using (hab.const_mul 4).neg
      simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hn
    simpa using (hc.mul he).sub (tendsto_const_nhds (x := (1 : ℝ)))
  -- upper bound sequence
  obtain ⟨K1, h0, hK1, hh0, Ht⟩ := TrialState.trial_quotient
  have hup : Tendsto (fun j => -16 / 15 * h j ^ 2 + K1 * |h j| ^ 3) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => h j ^ 2) atTop (𝓝 0) := by simpa using hh.pow 2
    have h2 : Tendsto (fun j => |h j| ^ 3) atTop (𝓝 0) := by simpa using hab.pow 3
    simpa using (h1.const_mul (-16 / 15)).add (h2.const_mul K1)
  have hsmall : ∀ᶠ j in atTop, |h j| ≤ h0 :=
    (tendsto_order.1 hab).2 h0 hh0 |>.mono fun j hj => hj.le
  have hηle : ∀ᶠ j in atTop,
      (|ε j| + (Real.exp |h j| - Real.exp (-|h j|))) * Real.exp |h j| ≤ 1 / 2 :=
    (tendsto_order.1 hη).2 (1 / 2) (by norm_num) |>.mono fun j hj => hj.le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [hε, hηle] with j hj1 hj2
    have hq := quot_lower_STR028_lower (h j) (ρ j) (hpos j) hj1 hj2
    have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
    rw [sub_le_sub_iff_right, le_div_iff₀ hpi]
    exact hq
  · filter_upwards [hne, hsmall] with j hj1 hj2
    obtain ⟨ρ₁, h1, hq⟩ := Ht (h j) (abs_pos.2 hj1) hj2
    exact TrialState.optimizer_trial_bound (ρ j) (fun ρ' hρ' => hmin j ρ' hρ') ρ₁ h1 hq

/-- **`ordinaryOptimizer_on_rangeGraph` with `hγ` discharged.** -/
theorem ordinaryOptimizer_on_rangeGraph_unconditional (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (hne : ∀ᶠ j in atTop, h j ≠ 0)
    (ρ : ℕ → AbsoluteDensity 1)
    (hpos : ∀ j, 0 < ordinaryEntropy (h j) (ρ j))
    (hmin : ∀ j, ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy (h j) ρ' →
      ordinaryFisher (h j) (ρ j) / (2 * ordinaryEntropy (h j) (ρ j)) ≤
        ordinaryFisher (h j) ρ' / (2 * ordinaryEntropy (h j) ρ'))
    (α : ℝ) [HolderExponent α] (k : ℕ) (hk : 1 ≤ k) :
    ∃ (U : Set Par) (Wn : Set (Wsp α)) (ψ : Par → Wsp α) (x : ℕ → Par × Wsp α),
      IsOpen U ∧ (0 : Par) ∈ U ∧ IsOpen Wn ∧ (0 : Wsp α) ∈ Wn ∧ ψ 0 = 0 ∧ ContDiffOn ℝ k ψ U ∧
      (∀ p ∈ U, ψ p ∈ Wn ∧ rangeMap α (p, ψ p) = 0) ∧
      (∀ p ∈ U, ∀ w ∈ Wn, rangeMap α (p, w) = 0 → w = ψ p) ∧
      Tendsto x atTop (𝓝 0) ∧
      (∀ j, (x j).1 2 = h j ∧ 1 + (x j).1 3 = (str025_quot (h j) (ρ j)).toReal / (4 * Real.pi ^ 2)) ∧
      (∀ᶠ j in atTop, ∀ᵐ y ∂haar 1, ∀ s : ℝ, torusLift (fun _ => s) = y →
        (ρ j).density y = (rho α (x j)).val s) ∧
      ∀ᶠ j in atTop, (x j).1 ∈ U ∧ (x j).2 ∈ Wn ∧
        (∃ L : ℝ, eul α (x j) = ((1 + (x j).1 3) * L) • (1 : PH α 0)) ∧
        resid α (x j) = 0 ∧ rangeMap α (x j) = 0 ∧ (x j).2 = ψ (x j).1 :=
  ordinaryOptimizer_on_rangeGraph h hh ρ hpos hmin
    (ordinaryOptimizer_gamma_tendsto h hh hne ρ hpos hmin) α k hk

end DGPS.Examples.ThreeSpeciesCircle.OrdinaryGammaLower

