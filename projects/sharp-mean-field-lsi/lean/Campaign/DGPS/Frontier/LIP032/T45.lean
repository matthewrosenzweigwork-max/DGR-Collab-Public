import DGPS.Frontier.LIP032.T21
import DGPS.Frontier.LIP032.T44

/-!
# LIP032.45: Compactness through a closed parameter energy level

Task id and title: LIP032.45, "Compactness through a closed parameter energy level" (node LIP032,
contractibility of the minimizer set; leaf formalization on the explicit circle model `A_*` of
LIP032.41, no positive-rate or flow hypothesis is used).

## Provides
* `DGPS.Frontier.LIP032.probStar_LIP03245` (definition): the probability measure `μ_{P_a}` on `𝕋¹`
  with density `P_a = densityStar_LIP03244 a`, as an element of `ProbabilityMeasure (Torus 1)`.
* `DGPS.Frontier.LIP032.densityCM_LIP03245` (definition): `P_a` as an element of `C(Torus 1, ℝ)`
  (carrying the uniform norm).
* `DGPS.Frontier.LIP032.momentFamily_LIP03245` (definition): `m_*(a) = ∫ γ P_a dm`.
* `DGPS.Frontier.LIP032.energyStar_LIP03245` (definition): `e_*(a) = F_{A_*}(μ_{P_a})` as a real
  number (the real part of the extended free energy, shown finite).
* `DGPS.Frontier.LIP032.energyMinStar_LIP03245` (definition): `E_{*,min}`, the real value of the
  free-energy minimum of `A_*`.
* `DGPS.Frontier.LIP032.levelSetStar_LIP03245` (definition): `J_* = {a ∈ [-1,1] : e_*(a) = E_{*,min}}`.
* `DGPS.Frontier.LIP032.lip032_45_compactness_through_closed_parameter_energy_level`: MAIN. The
  conjunction of all the items below, for `a, b ∈ [-1, 1]`.
* `DGPS.Frontier.LIP032.lip032_45_compactness_through_closed_parameter_energy_level_density_lipschitz`:
  `‖P_a - P_b‖_∞ ≤ 16 e^16 |a - b|` in `C(Torus 1, ℝ)`, and `a ↦ P_a` is continuous in the uniform
  norm on `[-1, 1]`.
* `DGPS.Frontier.LIP032.lip032_45_compactness_through_closed_parameter_energy_level_weak_continuity`:
  the test-integral estimate `|μ_a(φ) - μ_b(φ)| ≤ C 16 e^16 |a - b|` for measurable `φ` with
  `|φ| ≤ C`, and weak continuity of `a ↦ μ_{P_a}` on `[-1, 1]`.
* `DGPS.Frontier.LIP032.lip032_45_compactness_through_closed_parameter_energy_level_log_partition`:
  `|log Z_*(a) - log Z_*(b)| ≤ 8 |a - b|`, and continuity of `a ↦ log Z_*(a)`.
* `DGPS.Frontier.LIP032.lip032_45_compactness_through_closed_parameter_energy_level_moment`:
  `M(μ_{P_a}) = m_*(a)`, `|m_*(a) - m_*(b)| ≤ 16 e^16 |a - b|`, and continuity of `m_*`.
* `DGPS.Frontier.LIP032.lip032_45_compactness_through_closed_parameter_energy_level_energy_formula`:
  `F_{A_*}(μ_{P_a}) = e_*(a) = 8 a m_*(a) - log Z_*(a) - 4 m_*(a)²` for every real `a`, and `e_*` is
  continuous on `[-1, 1]`.
* `DGPS.Frontier.LIP032.lip032_45_compactness_through_closed_parameter_energy_level_level_set`:
  `freeEnergyMinimum A_* = E_{*,min}`, and `J_*` is contained in `[-1, 1]`, nonempty and compact.
* `DGPS.Frontier.LIP032.lip032_45_compactness_through_closed_parameter_energy_level_minimizer_set`:
  `S_* = μ_P(J_*)` as sets of probability measures, and `S_*` is weakly compact.

## R5 notes
* FD-001 check. The statement concerns only the explicit model `A_*` of LIP032.41. None of the
  prerequisites (LIP032.17, .18, .20, .21, .41, .44 and LIP017's free-energy minimum) carries a
  positive-rate or flow hypothesis, so none is inherited and none is added: the argument is
  unconditional and this is a pure formalization task, not a statement issue.
* `m` is `haar 1`, `γ = gammaStar_LIP03241`, `Z_* = normalizerStar_LIP03244`,
  `P_a = densityStar_LIP03244 a`, `μ_a = densityMeasure_LIP03218 (P_a)`, `S_*` is
  `minimizerSetStar_LIP03244`. `P_a`, `Z_*` and `μ_a` are defined for every real `a`
  (`μ_a` is a probability measure for every real `a`, by LIP032.17 with `B = 8 |a|`); the
  specification's domain `[-1, 1]` enters as the hypotheses `a ∈ Set.Icc (-1) 1` in the Lipschitz
  bounds and as the set on which `ContinuousOn` is asserted. Several helper facts hold for every
  real `a, b` and are stated that way in the helper lemmas; the public statements keep `[-1, 1]`.
* Uniform norm. The uniform norm is the norm of `C(Torus 1, ℝ)` (the torus is compact): `P_a` is
  packaged as `densityCM_LIP03245 a : C(Torus 1, ℝ)` and the estimate is
  `‖densityCM a - densityCM b‖ ≤ 16 * exp 16 * |a - b|`. Continuity of `a ↦ P_a` in the uniform
  norm is `ContinuousOn densityCM_LIP03245 (Set.Icc (-1) 1)`; it follows from the Lipschitz bound
  (Lipschitz on a set implies continuous on it).
* The constant `16 e^16` is `2 C` with `C = e^{2 B_0}`, `B_0 = 8`, as in LIP032.21 applied to the
  potentials `-(8 a γ)` (LIP032.44), with `δ = 8 |a - b|` the pointwise bound on the potential
  difference (`|γ| ≤ 1`).
* Weak topology. `ProbabilityMeasure (Torus 1)` carries Mathlib's topology of weak convergence.
  Weak continuity of `a ↦ μ_{P_a}` on `[-1, 1]` is `ContinuousOn probStar_LIP03245 (Set.Icc (-1) 1)`,
  proved through Mathlib's characterization by continuity of the integrals of all `C(Torus 1, ℝ)`
  test functions, using the test-integral estimate with bound `C = ‖φ‖`.
* The test-integral estimate is stated for every measurable `φ` with a real bound `C` such that
  `|φ x| ≤ C` for all `x`. The specification's `‖φ‖_∞` is recovered by taking `C = ‖φ‖_∞` (for
  continuous `φ`, `C = ‖φ‖`); the more general form with an arbitrary bound `C` is what the bridge
  of LIP032.18 gives. Integrals are `∫ φ ∂(μ_a)` against the measure `densityMeasure_LIP03218 P_a`.
* `m_*(a)` is spelled `∫ x, γ x * P_a x ∂m`. Its identification with the first moment
  `momentStar_LIP03241` of `μ_{P_a}` is part of the statement (LIP032.18 bridge).
* `e_*(a)` is the real number `(freeEnergy A_* (μ_{P_a})).toReal`. The free energy takes values in
  `EReal`; the statement records the finiteness by the equation `freeEnergy A_* μ_{P_a} = ↑(e_*(a))`
  (the relative entropy of `μ_{P_a}` with respect to `m` is `∫ P_a log P_a dm`, finite and
  nonnegative, computed with the campaign's `DGPS.relativeEntropy_withDensity` and
  `DGPS.homogeneousEntropy_eq_formula`; LIP032.26 is not a listed prerequisite, so its short
  argument is repeated here). The closed form is
  `e_*(a) = 8 a m_*(a) - log Z_*(a) - 4 m_*(a)²`, valid for every real `a`: the entropy equals
  `8 a m_*(a) - log Z_*(a)` because `log P_a = 8 a γ - log Z_*(a)`, and the remaining term
  `-4 M²` is the exact energy identity of LIP032.41.
* `E_{*,min}` is `DGPS.freeEnergyMinimumReal A_*`, the real value of `freeEnergyMinimum A_*` (finite
  by `DGPS.freeEnergyMinimum_finite`); the statement records `freeEnergyMinimum A_* = ↑E_{*,min}`.
* `J_*` is the set of reals `a` with `a ∈ [-1, 1]` and `e_*(a) = E_{*,min}`; it is closed as the
  intersection of the closed interval with the preimage of a point under a function continuous on
  the interval, hence compact as a closed subset of a compact interval.
* Nonemptiness of `J_*` uses the existence of a free-energy minimizer, `DGPS.freeEnergy_minimum_exists`
  (the first conjunct of LIP017), then LIP032.44: a minimizer `ν` has `M(ν) ∈ [-1, 1]` and
  `ν = μ_{P_{M(ν)}}`, so `M(ν) ∈ J_*`.
* `S_* = μ_P(J_*)` is the equality of sets `minimizerSetStar_LIP03244 = probStar_LIP03245 '' J_*` in
  `ProbabilityMeasure (Torus 1)`. The inclusion `⊆` is LIP032.44 (membership of `M(ν)` in `J_*`
  because the free energy of `ν = μ_{P_{M(ν)}}` is `e_*(M(ν))` and equals the minimum); the
  inclusion `⊇` holds because `e_*(a) = E_{*,min}` says `F(μ_{P_a}) = F_*`.
* Compactness of `S_*` is only the continuous image of the compact set `J_*` under the map
  `a ↦ μ_{P_a}` (continuous on `J_* ⊆ [-1, 1]`). No lower semicontinuity of the entropy is needed
  for this step and none is used.
* `μ_{P_a}` is regarded as an element of `ProbabilityMeasure (Torus 1)` through
  `probStar_LIP03245`; its underlying measure is `densityMeasure_LIP03218 (densityStar_LIP03244 a)`
  by definition (`coe_probStar_LIP03245`).
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

/-! ### Elementary facts on the Gibbs family for all real parameters -/

/-- `|U_a| ≤ 8 |a|` for the potential family. -/
theorem abs_potentialFamily_le_abs_LIP03245 (a : ℝ) (x : Torus 1) :
    |potentialFamily_LIP03244 a x| ≤ 8 * |a| := by
  have h2 := abs_gammaStar_le_LIP03241 x
  have h3 := mul_nonneg (abs_nonneg a) (sub_nonneg.2 h2)
  unfold potentialFamily_LIP03244
  rw [abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  linarith

/-- The normalizer is positive, and `P_a` is continuous with mass one, for every real `a`. -/
theorem general_data_LIP03245 (a : ℝ) :
    0 < normalizerStar_LIP03244 a ∧ ∫ x, densityStar_LIP03244 a x ∂haar 1 = 1 ∧
      Continuous (densityStar_LIP03244 a) := by
  obtain ⟨-, -, hZpos, -, hint, hcont⟩ :=
    lip032_17_positive_normalized_exponential (potentialFamily_LIP03244 a)
      (continuous_potentialFamily_LIP03244 a) (8 * |a|) (abs_potentialFamily_le_abs_LIP03245 a)
  rw [normalizer_potentialFamily_LIP03244] at hZpos
  rw [normExp_potentialFamily_LIP03244] at hint hcont
  exact ⟨hZpos, hint, hcont⟩

/-- `P_a` is strictly positive for every real `a`. -/
theorem densityStar_pos_LIP03245 (a : ℝ) (x : Torus 1) : 0 < densityStar_LIP03244 a x :=
  div_pos (Real.exp_pos _) (general_data_LIP03245 a).1

/-- `μ_{P_a}` is a probability measure for every real `a`. -/
theorem isProbabilityMeasure_densityMeasure_LIP03245 (a : ℝ) :
    IsProbabilityMeasure (densityMeasure_LIP03218 (densityStar_LIP03244 a)) :=
  isProbabilityMeasure_density_LIP03218 (general_data_LIP03245 a).2.2
    (fun x => (densityStar_pos_LIP03245 a x).le) (general_data_LIP03245 a).2.1

/-- The probability measure `μ_{P_a}` as an element of `ProbabilityMeasure (Torus 1)`. -/
noncomputable def probStar_LIP03245 (a : ℝ) : ProbabilityMeasure (Torus 1) :=
  ⟨densityMeasure_LIP03218 (densityStar_LIP03244 a), isProbabilityMeasure_densityMeasure_LIP03245 a⟩

theorem coe_probStar_LIP03245 (a : ℝ) :
    ((probStar_LIP03245 a : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) =
      densityMeasure_LIP03218 (densityStar_LIP03244 a) := rfl

/-- `P_a` as a continuous function on the torus (carrying the uniform norm). -/
noncomputable def densityCM_LIP03245 (a : ℝ) : C(Torus 1, ℝ) :=
  ⟨densityStar_LIP03244 a, (general_data_LIP03245 a).2.2⟩

/-- The pointwise difference of two potentials of the family is at most `8 |a - b|`. -/
theorem abs_potentialFamily_sub_LIP03245 (a b : ℝ) (x : Torus 1) :
    |potentialFamily_LIP03244 a x - potentialFamily_LIP03244 b x| ≤ 8 * |a - b| := by
  have h2 := abs_gammaStar_le_LIP03241 x
  have h3 := mul_nonneg (abs_nonneg (a - b)) (sub_nonneg.2 h2)
  have e : potentialFamily_LIP03244 a x - potentialFamily_LIP03244 b x =
      -(8 * (a - b) * gammaStar_LIP03241 x) := by
    unfold potentialFamily_LIP03244
    ring
  rw [e, abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  linarith

/-- The pointwise Lipschitz estimate `|P_a x - P_b x| ≤ 16 e^16 |a - b|` on `[-1, 1]`. -/
theorem density_lipschitz_LIP03245 {a b : ℝ} (ha : a ∈ Set.Icc (-1 : ℝ) 1)
    (hb : b ∈ Set.Icc (-1 : ℝ) 1) (x : Torus 1) :
    |densityStar_LIP03244 a x - densityStar_LIP03244 b x| ≤ 16 * Real.exp 16 * |a - b| := by
  have h := lip032_21_exact_2c_density_bound_of_le (continuous_potentialFamily_LIP03244 a)
    (continuous_potentialFamily_LIP03244 b) (abs_potentialFamily_le_LIP03244 ha)
    (abs_potentialFamily_le_LIP03244 hb) (abs_potentialFamily_sub_LIP03245 a b) x
  rw [normExp_potentialFamily_LIP03244, normExp_potentialFamily_LIP03244] at h
  have e : (2 : ℝ) * 8 = 16 := by norm_num
  rw [e] at h
  calc _ ≤ _ := h
    _ = _ := by ring

/-- The logarithm of the normalizer is `8`-Lipschitz in `a`. -/
theorem abs_log_normalizer_sub_LIP03245 (a b : ℝ) :
    |Real.log (normalizerStar_LIP03244 a) - Real.log (normalizerStar_LIP03244 b)| ≤
      8 * |a - b| := by
  have h := lip032_20_log_partition_lipschitz_bound_of_le (continuous_potentialFamily_LIP03244 a)
    (continuous_potentialFamily_LIP03244 b) (abs_potentialFamily_sub_LIP03245 a b)
  rw [normalizer_potentialFamily_LIP03244, normalizer_potentialFamily_LIP03244] at h
  exact h

/-- Test-integral estimate for bounded measurable `φ`:
`|∫ φ dμ_a - ∫ φ dμ_b| ≤ C · 16 e^16 |a - b|`. -/
theorem abs_integral_sub_le_LIP03245 {a b : ℝ} (ha : a ∈ Set.Icc (-1 : ℝ) 1)
    (hb : b ∈ Set.Icc (-1 : ℝ) 1) {φ : Torus 1 → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hC : ∀ x, |φ x| ≤ C) :
    |∫ x, φ x ∂(probStar_LIP03245 a : Measure (Torus 1)) -
        ∫ x, φ x ∂(probStar_LIP03245 b : Measure (Torus 1))| ≤
      C * (16 * Real.exp 16 * |a - b|) := by
  have bridge : ∀ c : ℝ, ∫ x, φ x ∂(probStar_LIP03245 c : Measure (Torus 1)) =
      ∫ x, densityStar_LIP03244 c x * φ x ∂haar 1 := fun c =>
    (lip032_18_density_probability_test_integral_bridge_integral (general_data_LIP03245 c).2.2
      (fun x => (densityStar_pos_LIP03245 c x).le) (general_data_LIP03245 c).2.1 hφ ⟨C, hC⟩).2
  have hint : ∀ c : ℝ, Integrable (fun x => densityStar_LIP03244 c x * φ x) (haar 1) := by
    intro c
    obtain ⟨B, hB⟩ := exists_abs_bound_LIP03220 (general_data_LIP03245 c).2.2
    refine Integrable.of_bound
      (((general_data_LIP03245 c).2.2.measurable.mul hφ).aestronglyMeasurable) (B * C)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hB x) (hC x) (abs_nonneg _) ((abs_nonneg _).trans (hB x))
  rw [bridge a, bridge b, ← integral_sub (hint a) (hint b)]
  have h := norm_integral_le_of_norm_le_const (μ := haar 1)
    (f := fun x => densityStar_LIP03244 a x * φ x - densityStar_LIP03244 b x * φ x)
    (C := (16 * Real.exp 16 * |a - b|) * C)
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
      exact mul_le_mul (density_lipschitz_LIP03245 ha hb x) (hC x) (abs_nonneg _)
        (by positivity))
  rw [Real.norm_eq_abs] at h
  simpa [mul_comm] using h

/-- A function on a subset of the reals that is `K`-Lipschitz for the distance is continuous on it. -/
theorem continuousOn_of_lip_LIP03245 {β : Type*} [PseudoMetricSpace β] {s : Set ℝ} {g : ℝ → β}
    {K : ℝ} (hK : 0 ≤ K) (h : ∀ a ∈ s, ∀ b ∈ s, dist (g a) (g b) ≤ K * |a - b|) :
    ContinuousOn g s := by
  have hl : LipschitzOnWith ⟨K, hK⟩ g s :=
    LipschitzOnWith.of_dist_le_mul fun a ha b hb => by
      show dist (g a) (g b) ≤ K * dist a b
      rw [Real.dist_eq]
      exact h a ha b hb
  exact hl.continuousOn

/-- Weak continuity of `a ↦ μ_{P_a}` on `[-1, 1]`. -/
theorem continuousOn_probStar_LIP03245 :
    ContinuousOn probStar_LIP03245 (Set.Icc (-1 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.2
    fun f => ?_
  have hf : ContinuousOn
      (fun a : ℝ => ∫ x, f x ∂(probStar_LIP03245 a : Measure (Torus 1))) (Set.Icc (-1 : ℝ) 1) := by
    refine continuousOn_of_lip_LIP03245 (K := ‖f‖ * (16 * Real.exp 16)) (by positivity) ?_
    intro a ha b hb
    rw [Real.dist_eq]
    have h := abs_integral_sub_le_LIP03245 ha hb f.continuous.measurable
      (C := ‖f‖) (fun x => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x)
    simpa [mul_assoc] using h
  exact continuousOn_iff_continuous_domRestrict.1 hf

/-! ### The moment `m_*` -/

/-- `m_*(a) = ∫ γ P_a dm`. -/
noncomputable def momentFamily_LIP03245 (a : ℝ) : ℝ :=
  ∫ x, gammaStar_LIP03241 x * densityStar_LIP03244 a x ∂haar 1

/-- The first moment of `μ_{P_a}` is `m_*(a)`. -/
theorem momentStar_probStar_LIP03245 (a : ℝ) :
    momentStar_LIP03241 (probStar_LIP03245 a : Measure (Torus 1)) = momentFamily_LIP03245 a := by
  unfold momentStar_LIP03241 momentFamily_LIP03245
  rw [coe_probStar_LIP03245,
    (lip032_18_density_probability_test_integral_bridge_integral (general_data_LIP03245 a).2.2
    (fun x => (densityStar_pos_LIP03245 a x).le) (general_data_LIP03245 a).2.1
    continuous_gammaStar_LIP03241.measurable ⟨1, abs_gammaStar_le_LIP03241⟩).2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

/-- `m_*` is `16 e^16`-Lipschitz on `[-1, 1]`. -/
theorem abs_momentFamily_sub_LIP03245 {a b : ℝ} (ha : a ∈ Set.Icc (-1 : ℝ) 1)
    (hb : b ∈ Set.Icc (-1 : ℝ) 1) :
    |momentFamily_LIP03245 a - momentFamily_LIP03245 b| ≤ 16 * Real.exp 16 * |a - b| := by
  rw [← momentStar_probStar_LIP03245, ← momentStar_probStar_LIP03245]
  have h := abs_integral_sub_le_LIP03245 ha hb continuous_gammaStar_LIP03241.measurable
    (C := 1) abs_gammaStar_le_LIP03241
  unfold momentStar_LIP03241
  simpa using h

/-! ### The free energy along the family -/

/-- Entropy of a continuous positive mass-one density: `H(μ_f | m) = ∫ f log f dm ≥ 0`. -/
theorem entropy_of_density_LIP03245 {f : Torus 1 → ℝ} (hf : Continuous f)
    (h1 : ∫ x, f x ∂haar 1 = 1) (hpos : ∀ x, 0 < f x) :
    DGPS.relativeEntropy (densityMeasure_LIP03218 f) (haar 1)
        = ENNReal.ofReal (∫ x, f x * Real.log (f x) ∂haar 1) ∧
      0 ≤ ∫ x, f x * Real.log (f x) ∂haar 1 := by
  have hnn : ∀ x, 0 ≤ f x := fun x => (hpos x).le
  have hne : ∀ x, f x ≠ 0 := fun x => (hpos x).ne'
  have hcont : Continuous fun x => f x * Real.log (f x) := hf.mul (hf.log hne)
  have hint : Integrable f (haar 1) := integrable_continuous_LIP03218 hf
  have hlog : Integrable (fun x => f x * Real.log (f x)) (haar 1) :=
    integrable_continuous_LIP03218 hcont
  have hnn' : 0 ≤ᵐ[haar 1] f := Filter.Eventually.of_forall fun x => hnn x
  have hmeas : AEMeasurable f (haar 1) := hf.measurable.aemeasurable
  refine ⟨?_, ?_⟩
  · rw [densityMeasure_LIP03218, DGPS.relativeEntropy_withDensity hnn' hmeas,
      DGPS.homogeneousEntropy_eq_formula hnn' hint hlog, h1, Real.log_one, mul_zero, sub_zero]
  · have hsplit : ∫ x, (f x * Real.log (f x) - f x + 1) ∂haar 1
        = ∫ x, f x * Real.log (f x) ∂haar 1 := by
      have hA : Integrable (fun x => f x * Real.log (f x) - f x) (haar 1) := hlog.sub hint
      rw [integral_add hA (integrable_const 1), integral_sub hlog hint, h1, integral_const]
      simp
    rw [← hsplit]
    exact integral_nonneg fun x => DGPS.self_mul_log_sub_add_one_nonneg (hnn x)

/-- `∫ P_a log P_a dm = 8 a m_*(a) - log Z_*(a)`. -/
theorem integral_mul_log_densityStar_LIP03245 (a : ℝ) :
    ∫ x, densityStar_LIP03244 a x * Real.log (densityStar_LIP03244 a x) ∂haar 1 =
      8 * a * momentFamily_LIP03245 a - Real.log (normalizerStar_LIP03244 a) := by
  obtain ⟨hZ, h1, hf⟩ := general_data_LIP03245 a
  have hlog : ∀ x, Real.log (densityStar_LIP03244 a x) =
      8 * a * gammaStar_LIP03241 x - Real.log (normalizerStar_LIP03244 a) := by
    intro x
    unfold densityStar_LIP03244
    rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  have hγP : Integrable (fun x => gammaStar_LIP03241 x * densityStar_LIP03244 a x) (haar 1) :=
    integrable_continuous_LIP03218 (continuous_gammaStar_LIP03241.mul hf)
  have hP : Integrable (densityStar_LIP03244 a) (haar 1) := integrable_continuous_LIP03218 hf
  have e : (fun x => densityStar_LIP03244 a x * Real.log (densityStar_LIP03244 a x)) =
      fun x => 8 * a * (gammaStar_LIP03241 x * densityStar_LIP03244 a x) -
        Real.log (normalizerStar_LIP03244 a) * densityStar_LIP03244 a x := by
    funext x
    rw [hlog x]
    ring
  rw [e, integral_sub (hγP.const_mul _) (hP.const_mul _), integral_const_mul, integral_const_mul,
    h1]
  unfold momentFamily_LIP03245
  ring

/-- The closed form `8 a m_*(a) - log Z_*(a) - 4 m_*(a)²`. -/
noncomputable def energyFormula_LIP03245 (a : ℝ) : ℝ :=
  8 * a * momentFamily_LIP03245 a - Real.log (normalizerStar_LIP03244 a) -
    4 * momentFamily_LIP03245 a ^ 2

/-- The free energy of `μ_{P_a}` is the extended real `energyFormula a`. -/
theorem freeEnergy_probStar_LIP03245 (a : ℝ) :
    freeEnergy interactionDataStar_LIP03241 (probStar_LIP03245 a) =
      ((energyFormula_LIP03245 a : ℝ) : EReal) := by
  obtain ⟨hH, hnn⟩ := entropy_of_density_LIP03245 (general_data_LIP03245 a).2.2
    (general_data_LIP03245 a).2.1 (densityStar_pos_LIP03245 a)
  have hH' : DGPS.relativeEntropy ((probStar_LIP03245 a : ProbabilityMeasure (Torus 1)) :
      Measure (Torus 1)) (haar 1) = ENNReal.ofReal
        (∫ x, densityStar_LIP03244 a x * Real.log (densityStar_LIP03244 a x) ∂haar 1) := hH
  rw [energy_LIP03241, momentStar_probStar_LIP03245, hH', EReal.coe_ennreal_ofReal,
    max_eq_left hnn, integral_mul_log_densityStar_LIP03245,
    energyFormula_LIP03245, ← EReal.coe_sub]

/-- `e_*(a) = F_{A_*}(μ_{P_a})` as a real number. -/
noncomputable def energyStar_LIP03245 (a : ℝ) : ℝ :=
  (freeEnergy interactionDataStar_LIP03241 (probStar_LIP03245 a)).toReal

theorem energyStar_eq_formula_LIP03245 (a : ℝ) :
    energyStar_LIP03245 a = energyFormula_LIP03245 a := by
  unfold energyStar_LIP03245
  rw [freeEnergy_probStar_LIP03245, EReal.toReal_coe]

theorem coe_energyStar_LIP03245 (a : ℝ) :
    freeEnergy interactionDataStar_LIP03241 (probStar_LIP03245 a) =
      ((energyStar_LIP03245 a : ℝ) : EReal) := by
  rw [energyStar_eq_formula_LIP03245, freeEnergy_probStar_LIP03245]

theorem continuousOn_log_normalizer_LIP03245 :
    ContinuousOn (fun a : ℝ => Real.log (normalizerStar_LIP03244 a)) (Set.Icc (-1 : ℝ) 1) :=
  continuousOn_of_lip_LIP03245 (K := 8) (by norm_num) fun a _ b _ => by
    rw [Real.dist_eq]
    exact abs_log_normalizer_sub_LIP03245 a b

theorem continuousOn_momentFamily_LIP03245 :
    ContinuousOn momentFamily_LIP03245 (Set.Icc (-1 : ℝ) 1) :=
  continuousOn_of_lip_LIP03245 (K := 16 * Real.exp 16) (by positivity) fun a ha b hb => by
    rw [Real.dist_eq]
    exact abs_momentFamily_sub_LIP03245 ha hb

theorem continuousOn_energyStar_LIP03245 :
    ContinuousOn energyStar_LIP03245 (Set.Icc (-1 : ℝ) 1) := by
  have hm := continuousOn_momentFamily_LIP03245
  have hl := continuousOn_log_normalizer_LIP03245
  have h : ContinuousOn energyFormula_LIP03245 (Set.Icc (-1 : ℝ) 1) := by
    unfold energyFormula_LIP03245
    exact (((continuousOn_const.mul continuousOn_id).mul hm).sub hl).sub
      (continuousOn_const.mul (hm.pow 2))
  exact h.congr fun a _ => energyStar_eq_formula_LIP03245 a

/-! ### The energy level set `J_*` and the minimizer set -/

/-- The real value `E_{*,min}` of the free-energy minimum of `A_*`. -/
noncomputable def energyMinStar_LIP03245 : ℝ :=
  DGPS.freeEnergyMinimumReal interactionDataStar_LIP03241

/-- The energy level set `J_* = {a ∈ [-1, 1] : e_*(a) = E_{*,min}}`. -/
def levelSetStar_LIP03245 : Set ℝ :=
  {a | a ∈ Set.Icc (-1 : ℝ) 1 ∧ energyStar_LIP03245 a = energyMinStar_LIP03245}

theorem levelSetStar_subset_LIP03245 : levelSetStar_LIP03245 ⊆ Set.Icc (-1 : ℝ) 1 :=
  fun _ h => h.1

theorem isClosed_levelSetStar_LIP03245 : IsClosed levelSetStar_LIP03245 :=
  continuousOn_energyStar_LIP03245.preimage_isClosed_of_isClosed isClosed_Icc
    (isClosed_singleton (x := energyMinStar_LIP03245))

theorem isCompact_levelSetStar_LIP03245 : IsCompact levelSetStar_LIP03245 :=
  isCompact_Icc.of_isClosed_subset isClosed_levelSetStar_LIP03245 levelSetStar_subset_LIP03245

/-- `μ_{P_a}` is a minimizer iff `e_*(a) = E_{*,min}`. -/
theorem probStar_mem_minimizerSet_iff_LIP03245 (a : ℝ) :
    probStar_LIP03245 a ∈ minimizerSetStar_LIP03244 ↔
      energyStar_LIP03245 a = energyMinStar_LIP03245 := by
  show freeEnergy interactionDataStar_LIP03241 (probStar_LIP03245 a) =
      freeEnergyMinimum interactionDataStar_LIP03241 ↔ _
  rw [coe_energyStar_LIP03245, ← DGPS.coe_freeEnergyMinimumReal interactionDataStar_LIP03241,
    EReal.coe_eq_coe_iff]
  rfl

/-- Every minimizer is `μ_{P_a}` for some `a ∈ J_*`. -/
theorem minimizer_exists_param_LIP03245 (ν : ProbabilityMeasure (Torus 1))
    (hν : ν ∈ minimizerSetStar_LIP03244) :
    ∃ a ∈ levelSetStar_LIP03245, probStar_LIP03245 a = ν := by
  obtain ⟨hm, hEq⟩ := lip032_44_one_parameter_gibbs_family_contains_minimizer_minimizer ν hν
  have hν_eq : probStar_LIP03245 (momentStar_LIP03241 (ν : Measure (Torus 1))) = ν :=
    ProbabilityMeasure.toMeasure_injective hEq.symm
  refine ⟨momentStar_LIP03241 (ν : Measure (Torus 1)), ⟨hm, ?_⟩, hν_eq⟩
  apply (probStar_mem_minimizerSet_iff_LIP03245 _).1
  rw [hν_eq]
  exact hν

theorem levelSetStar_nonempty_LIP03245 : levelSetStar_LIP03245.Nonempty := by
  obtain ⟨ν, hν⟩ := DGPS.freeEnergy_minimum_exists interactionDataStar_LIP03241
  obtain ⟨a, ha, -⟩ := minimizer_exists_param_LIP03245 ν hν
  exact ⟨a, ha⟩

theorem minimizerSet_eq_image_LIP03245 :
    minimizerSetStar_LIP03244 = probStar_LIP03245 '' levelSetStar_LIP03245 := by
  ext ν
  constructor
  · intro hν
    obtain ⟨a, ha, hEq⟩ := minimizer_exists_param_LIP03245 ν hν
    exact ⟨a, ha, hEq⟩
  · rintro ⟨a, ha, rfl⟩
    exact (probStar_mem_minimizerSet_iff_LIP03245 a).2 ha.2

/-! ### Public statements -/

/-- Uniform-norm Lipschitz bound `‖P_a - P_b‖_∞ ≤ 16 e^16 |a - b|` on `[-1, 1]`, and continuity of
`a ↦ P_a` in the uniform norm. -/
theorem lip032_45_compactness_through_closed_parameter_energy_level_density_lipschitz :
    (∀ a ∈ Set.Icc (-1 : ℝ) 1, ∀ b ∈ Set.Icc (-1 : ℝ) 1,
      ‖densityCM_LIP03245 a - densityCM_LIP03245 b‖ ≤ 16 * Real.exp 16 * |a - b|) ∧
    ContinuousOn densityCM_LIP03245 (Set.Icc (-1 : ℝ) 1) := by
  have h : ∀ a ∈ Set.Icc (-1 : ℝ) 1, ∀ b ∈ Set.Icc (-1 : ℝ) 1,
      ‖densityCM_LIP03245 a - densityCM_LIP03245 b‖ ≤ 16 * Real.exp 16 * |a - b| := by
    intro a ha b hb
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
    rw [Real.norm_eq_abs]
    exact density_lipschitz_LIP03245 ha hb x
  refine ⟨h, continuousOn_of_lip_LIP03245 (K := 16 * Real.exp 16) (by positivity) ?_⟩
  intro a ha b hb
  rw [dist_eq_norm]
  exact h a ha b hb

/-- The test-integral estimate and weak continuity of `a ↦ μ_{P_a}` on `[-1, 1]`. -/
theorem lip032_45_compactness_through_closed_parameter_energy_level_weak_continuity :
    (∀ a ∈ Set.Icc (-1 : ℝ) 1, ∀ b ∈ Set.Icc (-1 : ℝ) 1, ∀ φ : Torus 1 → ℝ, Measurable φ →
      ∀ C : ℝ, (∀ x, |φ x| ≤ C) →
        |∫ x, φ x ∂(probStar_LIP03245 a : Measure (Torus 1)) -
            ∫ x, φ x ∂(probStar_LIP03245 b : Measure (Torus 1))| ≤
          C * (16 * Real.exp 16 * |a - b|)) ∧
    ContinuousOn probStar_LIP03245 (Set.Icc (-1 : ℝ) 1) :=
  ⟨fun _ ha _ hb _ hφ _ hC => abs_integral_sub_le_LIP03245 ha hb hφ hC,
    continuousOn_probStar_LIP03245⟩

/-- The log-partition estimate `|log Z_*(a) - log Z_*(b)| ≤ 8 |a - b|` and its continuity. -/
theorem lip032_45_compactness_through_closed_parameter_energy_level_log_partition :
    (∀ a ∈ Set.Icc (-1 : ℝ) 1, ∀ b ∈ Set.Icc (-1 : ℝ) 1,
      |Real.log (normalizerStar_LIP03244 a) - Real.log (normalizerStar_LIP03244 b)| ≤
        8 * |a - b|) ∧
    ContinuousOn (fun a : ℝ => Real.log (normalizerStar_LIP03244 a)) (Set.Icc (-1 : ℝ) 1) :=
  ⟨fun a _ b _ => abs_log_normalizer_sub_LIP03245 a b, continuousOn_log_normalizer_LIP03245⟩

/-- The moment `m_*(a) = ∫ γ P_a dm` is the first moment of `μ_{P_a}`, `16 e^16`-Lipschitz, and
continuous on `[-1, 1]`. -/
theorem lip032_45_compactness_through_closed_parameter_energy_level_moment :
    (∀ a : ℝ, momentStar_LIP03241 (probStar_LIP03245 a : Measure (Torus 1)) =
      ∫ x, gammaStar_LIP03241 x * densityStar_LIP03244 a x ∂haar 1) ∧
    (∀ a ∈ Set.Icc (-1 : ℝ) 1, ∀ b ∈ Set.Icc (-1 : ℝ) 1,
      |momentFamily_LIP03245 a - momentFamily_LIP03245 b| ≤ 16 * Real.exp 16 * |a - b|) ∧
    ContinuousOn momentFamily_LIP03245 (Set.Icc (-1 : ℝ) 1) :=
  ⟨fun a => momentStar_probStar_LIP03245 a, fun _ ha _ hb => abs_momentFamily_sub_LIP03245 ha hb,
    continuousOn_momentFamily_LIP03245⟩

/-- The free energy along the family: `F_{A_*}(μ_{P_a}) = e_*(a) = 8 a m_*(a) - log Z_*(a) -
4 m_*(a)²` (every real `a`), and `e_*` is continuous on `[-1, 1]`. -/
theorem lip032_45_compactness_through_closed_parameter_energy_level_energy_formula :
    (∀ a : ℝ, freeEnergy interactionDataStar_LIP03241 (probStar_LIP03245 a) =
      ((energyStar_LIP03245 a : ℝ) : EReal)) ∧
    (∀ a : ℝ, energyStar_LIP03245 a = 8 * a * momentFamily_LIP03245 a -
      Real.log (normalizerStar_LIP03244 a) - 4 * momentFamily_LIP03245 a ^ 2) ∧
    ContinuousOn energyStar_LIP03245 (Set.Icc (-1 : ℝ) 1) :=
  ⟨coe_energyStar_LIP03245, energyStar_eq_formula_LIP03245, continuousOn_energyStar_LIP03245⟩

/-- The level set `J_*` is contained in `[-1, 1]`, nonempty and compact; the free-energy minimum is
the real number `E_{*,min}`. -/
theorem lip032_45_compactness_through_closed_parameter_energy_level_level_set :
    freeEnergyMinimum interactionDataStar_LIP03241 = ((energyMinStar_LIP03245 : ℝ) : EReal) ∧
    levelSetStar_LIP03245 ⊆ Set.Icc (-1 : ℝ) 1 ∧ levelSetStar_LIP03245.Nonempty ∧
    IsCompact levelSetStar_LIP03245 :=
  ⟨(DGPS.coe_freeEnergyMinimumReal interactionDataStar_LIP03241).symm,
    levelSetStar_subset_LIP03245, levelSetStar_nonempty_LIP03245, isCompact_levelSetStar_LIP03245⟩

/-- `S_* = μ_P(J_*)`, and `S_*` is weakly compact. -/
theorem lip032_45_compactness_through_closed_parameter_energy_level_minimizer_set :
    minimizerSetStar_LIP03244 = probStar_LIP03245 '' levelSetStar_LIP03245 ∧
    IsCompact minimizerSetStar_LIP03244 := by
  refine ⟨minimizerSet_eq_image_LIP03245, ?_⟩
  rw [minimizerSet_eq_image_LIP03245]
  exact isCompact_levelSetStar_LIP03245.image_of_continuousOn
    (continuousOn_probStar_LIP03245.mono levelSetStar_subset_LIP03245)

/-- MAIN (LIP032.45). Compactness through a closed parameter energy level: the maps `a ↦ P_a`
(uniform norm), `a ↦ μ_{P_a}` (weak topology) and `a ↦ e_*(a)` are continuous on `[-1, 1]` with the
stated quantitative bounds; the level set `J_*` of `e_*` at `E_{*,min}` is nonempty and compact;
and the minimizer set is `S_* = μ_P(J_*)`, hence weakly compact. -/
theorem lip032_45_compactness_through_closed_parameter_energy_level :
    ((∀ a ∈ Set.Icc (-1 : ℝ) 1, ∀ b ∈ Set.Icc (-1 : ℝ) 1,
        ‖densityCM_LIP03245 a - densityCM_LIP03245 b‖ ≤ 16 * Real.exp 16 * |a - b|) ∧
      ContinuousOn densityCM_LIP03245 (Set.Icc (-1 : ℝ) 1)) ∧
    ((∀ a ∈ Set.Icc (-1 : ℝ) 1, ∀ b ∈ Set.Icc (-1 : ℝ) 1, ∀ φ : Torus 1 → ℝ, Measurable φ →
        ∀ C : ℝ, (∀ x, |φ x| ≤ C) →
          |∫ x, φ x ∂(probStar_LIP03245 a : Measure (Torus 1)) -
              ∫ x, φ x ∂(probStar_LIP03245 b : Measure (Torus 1))| ≤
            C * (16 * Real.exp 16 * |a - b|)) ∧
      ContinuousOn probStar_LIP03245 (Set.Icc (-1 : ℝ) 1)) ∧
    ((∀ a ∈ Set.Icc (-1 : ℝ) 1, ∀ b ∈ Set.Icc (-1 : ℝ) 1,
        |Real.log (normalizerStar_LIP03244 a) - Real.log (normalizerStar_LIP03244 b)| ≤
          8 * |a - b|) ∧
      ContinuousOn (fun a : ℝ => Real.log (normalizerStar_LIP03244 a)) (Set.Icc (-1 : ℝ) 1)) ∧
    ((∀ a : ℝ, momentStar_LIP03241 (probStar_LIP03245 a : Measure (Torus 1)) =
        ∫ x, gammaStar_LIP03241 x * densityStar_LIP03244 a x ∂haar 1) ∧
      (∀ a ∈ Set.Icc (-1 : ℝ) 1, ∀ b ∈ Set.Icc (-1 : ℝ) 1,
        |momentFamily_LIP03245 a - momentFamily_LIP03245 b| ≤ 16 * Real.exp 16 * |a - b|) ∧
      ContinuousOn momentFamily_LIP03245 (Set.Icc (-1 : ℝ) 1)) ∧
    ((∀ a : ℝ, freeEnergy interactionDataStar_LIP03241 (probStar_LIP03245 a) =
        ((energyStar_LIP03245 a : ℝ) : EReal)) ∧
      (∀ a : ℝ, energyStar_LIP03245 a = 8 * a * momentFamily_LIP03245 a -
        Real.log (normalizerStar_LIP03244 a) - 4 * momentFamily_LIP03245 a ^ 2) ∧
      ContinuousOn energyStar_LIP03245 (Set.Icc (-1 : ℝ) 1)) ∧
    (freeEnergyMinimum interactionDataStar_LIP03241 = ((energyMinStar_LIP03245 : ℝ) : EReal) ∧
      levelSetStar_LIP03245 ⊆ Set.Icc (-1 : ℝ) 1 ∧ levelSetStar_LIP03245.Nonempty ∧
      IsCompact levelSetStar_LIP03245) ∧
    (minimizerSetStar_LIP03244 = probStar_LIP03245 '' levelSetStar_LIP03245 ∧
      IsCompact minimizerSetStar_LIP03244) :=
  ⟨lip032_45_compactness_through_closed_parameter_energy_level_density_lipschitz,
    lip032_45_compactness_through_closed_parameter_energy_level_weak_continuity,
    lip032_45_compactness_through_closed_parameter_energy_level_log_partition,
    lip032_45_compactness_through_closed_parameter_energy_level_moment,
    lip032_45_compactness_through_closed_parameter_energy_level_energy_formula,
    lip032_45_compactness_through_closed_parameter_energy_level_level_set,
    lip032_45_compactness_through_closed_parameter_energy_level_minimizer_set⟩

end DGPS.Frontier.LIP032
