import DGPS.Frontier.LIP032.T18
import DGPS.Frontier.LIP032.T41

/-!
# LIP032.44: One-parameter Gibbs family contains every minimizer

Task id and title: LIP032.44, "One-parameter Gibbs family contains every minimizer" (node LIP032,
contractibility of the minimizer set; leaf formalization on the explicit circle model `A_*` of
LIP032.41, no positive-rate or flow hypothesis is used).

## Provides
* `DGPS.Frontier.LIP032.normalizerStar_LIP03244` (definition): `Z_*(a) = ∫ e^{8 a γ} dm` with
  `m = haar 1` and `γ = gammaStar_LIP03241`.
* `DGPS.Frontier.LIP032.densityStar_LIP03244` (definition): `P_a(x) = e^{8 a γ(x)} / Z_*(a)`.
* `DGPS.Frontier.LIP032.minimizerSetStar_LIP03244` (definition): the set `S_*` of free-energy
  minimizers of the explicit data `A_*` (`interactionDataStar_LIP03241`).
* `DGPS.Frontier.LIP032.lip032_44_one_parameter_gibbs_family_contains_minimizer`: MAIN. For
  `a ∈ [-1, 1]`: `e^{-8} ≤ Z_*(a) ≤ e^8`, `e^{-16} ≤ P_a ≤ e^{16}`, `P_a` is smooth periodic,
  positive, of mass one, and `μ_{P_a}` is a probability; and every `ν ∈ S_*` has
  `M(ν) ∈ [-1, 1]` and equals `μ_{P_{M(ν)}}`.
* `DGPS.Frontier.LIP032.lip032_44_one_parameter_gibbs_family_contains_minimizer_family`: the
  statement about the family `P_a`, `a ∈ [-1, 1]`.
* `DGPS.Frontier.LIP032.lip032_44_one_parameter_gibbs_family_contains_minimizer_moment_bound`:
  `|M(ν)| ≤ 1` for every probability `ν` on `𝕋¹`.
* `DGPS.Frontier.LIP032.lip032_44_one_parameter_gibbs_family_contains_minimizer_potential`:
  `V_*(x) + (W_* * ν)(x) = -8 M(ν) γ(x) + 4 ∫ γ² dν` for every probability `ν`.
* `DGPS.Frontier.LIP032.lip032_44_one_parameter_gibbs_family_contains_minimizer_gibbs_density`:
  the Gibbs density of `A_*` at any probability `ν` is `P_{M(ν)}`.
* `DGPS.Frontier.LIP032.lip032_44_one_parameter_gibbs_family_contains_minimizer_minimizer`: the
  last clause of MAIN (`M(ν) ∈ [-1, 1]` and `ν = μ_{P_{M(ν)}}` for `ν ∈ S_*`).

## R5 notes
* `m` is `haar 1`, `γ` is the LIP032.41 function `gammaStar_LIP03241` (the cosine mode), and
  `M(ν)` is `momentStar_LIP03241` of the underlying measure. The exponent `8 a γ` is spelled
  `8 * a * γ x`. `Z_*` and `P_a` are defined for every real `a`; the specification's restriction
  `a ∈ [-1, 1]` is a hypothesis (`a ∈ Set.Icc (-1) 1`) of the bounds and positivity claims, and
  the smoothness part holds for every real `a`.
* "Smooth" is the campaign predicate `IsSmoothPeriodic` (the lift to `Fin 1 → ℝ` is `C^∞`).
  "Positive probability density" is recorded as: pointwise `0 < P_a`, `∫ P_a dm = 1`, and
  `IsProbabilityMeasure (densityMeasure_LIP03218 P_a)` (the measure `μ_{P_a}` of LIP032.18). The
  last conjunct is read from the words "probability density" and follows from LIP032.18.
* `S_*` is the set of free-energy minimizers of `A_*`, formalized exactly as in LIP017 and
  LIP032.18: probabilities `ν : ProbabilityMeasure (Torus 1)` with
  `freeEnergy A_* ν = freeEnergyMinimum A_*`. Nonemptiness and compactness of `S_*` are not used.
* "Every `ν ∈ S_*` equals `μ_{P_a}` for `a = M(ν)`" is the equality of measures
  `(ν : Measure (Torus 1)) = densityMeasure_LIP03218 (densityStar_LIP03244 (M ν))`, with the
  extra conjunct `M(ν) ∈ [-1, 1]` as in the specification.
* The bound `|M(ν)| ≤ 1`, the kernel identity and the identification of the Gibbs density with
  `P_{M(ν)}` are proved for every probability `ν` (not only for minimizers), as in the proof
  sketch of the specification; only the final measure identity uses minimality, through
  LIP032.18 (which applies LIP017). No `LipschitzData`, rate, flow or gradient hypothesis occurs.
* The normalizer and density bounds come from LIP032.17 with `B = 8` applied to the potential
  `x ↦ -(8 a γ x)`; the constant `e^{-16}` is the rewriting of `e^{-(2·8)}`.
* The spatially constant term `4 ∫ γ² dν` is cancelled exactly: the partition function of the
  Gibbs density equals `Z_*(M ν)` times the positive factor `e^{-4 ∫ γ² dν}`, and the factor
  divides out. No Bessel-ratio equation and no classification of the possible parameters is used.
-/

open MeasureTheory
open scoped ContDiff

namespace DGPS.Frontier.LIP032

/-- The normalizer `Z_*(a) = ∫ e^{8 a γ} dm`. -/
noncomputable def normalizerStar_LIP03244 (a : ℝ) : ℝ :=
  ∫ x, Real.exp (8 * a * gammaStar_LIP03241 x) ∂haar 1

/-- The density `P_a(x) = e^{8 a γ(x)} / Z_*(a)`. -/
noncomputable def densityStar_LIP03244 (a : ℝ) (x : Torus 1) : ℝ :=
  Real.exp (8 * a * gammaStar_LIP03241 x) / normalizerStar_LIP03244 a

/-- The set `S_*` of free-energy minimizers of the explicit data `A_*`. -/
def minimizerSetStar_LIP03244 : Set (ProbabilityMeasure (Torus 1)) :=
  {ν | freeEnergy interactionDataStar_LIP03241 ν = freeEnergyMinimum interactionDataStar_LIP03241}

/-- The potential `x ↦ -(8 a γ x)` whose normalized exponential is `P_a`. -/
noncomputable def potentialFamily_LIP03244 (a : ℝ) (x : Torus 1) : ℝ :=
  -(8 * a * gammaStar_LIP03241 x)

theorem normalizer_potentialFamily_LIP03244 (a : ℝ) :
    normalizer_LIP03217 (potentialFamily_LIP03244 a) = normalizerStar_LIP03244 a := by
  unfold normalizer_LIP03217 normalizerStar_LIP03244 potentialFamily_LIP03244
  simp only [neg_neg]

theorem normExp_potentialFamily_LIP03244 (a : ℝ) :
    normExp_LIP03217 (potentialFamily_LIP03244 a) = densityStar_LIP03244 a := by
  funext x
  unfold normExp_LIP03217 densityStar_LIP03244
  rw [normalizer_potentialFamily_LIP03244]
  simp only [potentialFamily_LIP03244, neg_neg]

theorem continuous_potentialFamily_LIP03244 (a : ℝ) :
    Continuous (potentialFamily_LIP03244 a) :=
  (continuous_const.mul continuous_gammaStar_LIP03241).neg

theorem abs_potentialFamily_le_LIP03244 {a : ℝ} (ha : a ∈ Set.Icc (-1 : ℝ) 1) (x : Torus 1) :
    |potentialFamily_LIP03244 a x| ≤ 8 := by
  have h1 : |a| ≤ 1 := abs_le.mpr ha
  have h2 := abs_gammaStar_le_LIP03241 x
  have h3 : |a| * |gammaStar_LIP03241 x| ≤ 1 * 1 :=
    mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
  unfold potentialFamily_LIP03244
  rw [abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  linarith

/-- Smoothness of `P_a` (for every real `a`). -/
theorem isSmoothPeriodic_densityStar_LIP03244 (a : ℝ) :
    IsSmoothPeriodic (densityStar_LIP03244 a) := by
  have hg : ContDiff ℝ ∞ (gammaStar_LIP03241 ∘ torusLift) := isSmoothPeriodic_gammaStar_LIP03241
  show ContDiff ℝ ∞ (fun y : Fin 1 → ℝ =>
    Real.exp (8 * a * gammaStar_LIP03241 (torusLift y)) / normalizerStar_LIP03244 a)
  exact (Real.contDiff_exp.comp (contDiff_const.mul hg)).div_const _

/-- Normalizer bounds, density bounds, positivity and mass one for `a ∈ [-1, 1]`. -/
theorem family_data_LIP03244 {a : ℝ} (ha : a ∈ Set.Icc (-1 : ℝ) 1) :
    Real.exp (-8) ≤ normalizerStar_LIP03244 a ∧ normalizerStar_LIP03244 a ≤ Real.exp 8 ∧
      0 < normalizerStar_LIP03244 a ∧
      (∀ x, Real.exp (-16) ≤ densityStar_LIP03244 a x ∧
        densityStar_LIP03244 a x ≤ Real.exp 16) ∧
      ∫ x, densityStar_LIP03244 a x ∂haar 1 = 1 := by
  obtain ⟨hZl, hZu, hZpos, hbd, hint, -⟩ :=
    lip032_17_positive_normalized_exponential (potentialFamily_LIP03244 a)
      (continuous_potentialFamily_LIP03244 a) 8 (abs_potentialFamily_le_LIP03244 ha)
  rw [normalizer_potentialFamily_LIP03244] at hZl hZu hZpos
  rw [normExp_potentialFamily_LIP03244] at hbd hint
  have h16 : (2 : ℝ) * 8 = 16 := by norm_num
  rw [h16] at hbd
  exact ⟨hZl, hZu, hZpos, hbd, hint⟩

/-- The family statement: for `a ∈ [-1, 1]`, bounds on `Z_*(a)` and `P_a`, and `P_a` is a smooth
positive probability density. -/
theorem lip032_44_one_parameter_gibbs_family_contains_minimizer_family {a : ℝ}
    (ha : a ∈ Set.Icc (-1 : ℝ) 1) :
    Real.exp (-8) ≤ normalizerStar_LIP03244 a ∧ normalizerStar_LIP03244 a ≤ Real.exp 8 ∧
      (∀ x, Real.exp (-16) ≤ densityStar_LIP03244 a x ∧
        densityStar_LIP03244 a x ≤ Real.exp 16) ∧
      IsSmoothPeriodic (densityStar_LIP03244 a) ∧ (∀ x, 0 < densityStar_LIP03244 a x) ∧
      ∫ x, densityStar_LIP03244 a x ∂haar 1 = 1 ∧
      IsProbabilityMeasure (densityMeasure_LIP03218 (densityStar_LIP03244 a)) := by
  obtain ⟨hZl, hZu, hZpos, hbd, hint⟩ := family_data_LIP03244 ha
  have hpos : ∀ x, 0 < densityStar_LIP03244 a x := fun x =>
    lt_of_lt_of_le (Real.exp_pos _) (hbd x).1
  refine ⟨hZl, hZu, hbd, isSmoothPeriodic_densityStar_LIP03244 a, hpos, hint, ?_⟩
  have hcont : Continuous (densityStar_LIP03244 a) := by
    rw [← normExp_potentialFamily_LIP03244]
    exact (Real.continuous_exp.comp (continuous_potentialFamily_LIP03244 a).neg).div_const _
  exact isProbabilityMeasure_density_LIP03218 hcont (fun x => (hpos x).le) hint

/-- Every probability on `𝕋¹` has first moment in `[-1, 1]`. -/
theorem lip032_44_one_parameter_gibbs_family_contains_minimizer_moment_bound
    (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] :
    |momentStar_LIP03241 ν| ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := ν) (f := gammaStar_LIP03241) (C := 1)
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using abs_gammaStar_le_LIP03241 x)
  simpa [momentStar_LIP03241, Real.norm_eq_abs] using h

/-- The interaction kernel integral against `ν`. -/
theorem kernel_integral_LIP03244 (ν : Measure (Torus 1)) [IsProbabilityMeasure ν]
    (x : Torus 1) :
    ∫ y, WStar_LIP03241 x y ∂ν =
      4 * gammaStar_LIP03241 x ^ 2 - 8 * gammaStar_LIP03241 x * momentStar_LIP03241 ν +
        4 * ∫ y, gammaStar_LIP03241 y ^ 2 ∂ν := by
  have hγ := continuous_gammaStar_LIP03241
  have h1 : Integrable gammaStar_LIP03241 ν := integrable_of_continuous_LIP03241 ν hγ
  have h2 : Integrable (fun y => gammaStar_LIP03241 y ^ 2) ν :=
    integrable_of_continuous_LIP03241 ν (hγ.pow 2)
  have e : (fun y => WStar_LIP03241 x y) = fun y =>
      (4 * gammaStar_LIP03241 x ^ 2 - 8 * gammaStar_LIP03241 x * gammaStar_LIP03241 y) +
        4 * gammaStar_LIP03241 y ^ 2 := by
    funext y
    unfold WStar_LIP03241
    ring
  have h3 : Integrable (fun y => 8 * gammaStar_LIP03241 x * gammaStar_LIP03241 y) ν :=
    h1.const_mul _
  have h4 : Integrable (fun _ : Torus 1 => 4 * gammaStar_LIP03241 x ^ 2) ν := integrable_const _
  have h5 : Integrable (fun y => 4 * gammaStar_LIP03241 x ^ 2 -
      8 * gammaStar_LIP03241 x * gammaStar_LIP03241 y) ν := h4.sub h3
  have h6 : Integrable (fun y => 4 * gammaStar_LIP03241 y ^ 2) ν := h2.const_mul 4
  have h7 : ∫ y, 8 * gammaStar_LIP03241 x * gammaStar_LIP03241 y ∂ν =
      8 * gammaStar_LIP03241 x * momentStar_LIP03241 ν := by
    unfold momentStar_LIP03241
    exact integral_const_mul _ _
  have h8 : ∫ y, 4 * gammaStar_LIP03241 y ^ 2 ∂ν = 4 * ∫ y, gammaStar_LIP03241 y ^ 2 ∂ν :=
    integral_const_mul _ _
  rw [e, integral_add h5 h6, integral_sub h4 h3, h7, h8, integral_const]
  simp

/-- The equilibrium potential of `A_*` at `ν`:
`V_*(x) + (W_* * ν)(x) = -8 M(ν) γ(x) + 4 ∫ γ² dν`. -/
theorem lip032_44_one_parameter_gibbs_family_contains_minimizer_potential
    (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] (x : Torus 1) :
    DGPS.Lipschitz.equilibriumPotential interactionDataStar_LIP03241 ν x =
      -8 * momentStar_LIP03241 ν * gammaStar_LIP03241 x +
        4 * ∫ y, gammaStar_LIP03241 y ^ 2 ∂ν := by
  unfold DGPS.Lipschitz.equilibriumPotential DGPS.Lipschitz.interactionConvolution
  show VStar_LIP03241 x + ∫ y, WStar_LIP03241 x y ∂ν = _
  rw [kernel_integral_LIP03244]
  unfold VStar_LIP03241
  ring

/-- The Gibbs density of `A_*` at any probability `ν` is `P_{M(ν)}`: the spatially constant term
cancels from the normalized exponential. -/
theorem lip032_44_one_parameter_gibbs_family_contains_minimizer_gibbs_density
    (ν : Measure (Torus 1)) [IsProbabilityMeasure ν] :
    DGPS.Lipschitz.gibbsDensity interactionDataStar_LIP03241 ν =
      densityStar_LIP03244 (momentStar_LIP03241 ν) := by
  have hexp : ∀ x, Real.exp (-DGPS.Lipschitz.equilibriumPotential interactionDataStar_LIP03241 ν x) =
      Real.exp (8 * momentStar_LIP03241 ν * gammaStar_LIP03241 x) *
        Real.exp (-(4 * ∫ y, gammaStar_LIP03241 y ^ 2 ∂ν)) := by
    intro x
    rw [lip032_44_one_parameter_gibbs_family_contains_minimizer_potential, ← Real.exp_add]
    congr 1
    ring
  have hZ : DGPS.Lipschitz.gibbsPartition interactionDataStar_LIP03241 ν =
      normalizerStar_LIP03244 (momentStar_LIP03241 ν) *
        Real.exp (-(4 * ∫ y, gammaStar_LIP03241 y ^ 2 ∂ν)) := by
    unfold DGPS.Lipschitz.gibbsPartition normalizerStar_LIP03244
    rw [← integral_mul_const]
    exact integral_congr_ae (Filter.Eventually.of_forall hexp)
  funext x
  unfold DGPS.Lipschitz.gibbsDensity densityStar_LIP03244
  rw [hexp x, hZ, mul_div_mul_right _ _ (Real.exp_pos _).ne']

/-- Every minimizer `ν ∈ S_*` has `M(ν) ∈ [-1, 1]` and equals `μ_{P_{M(ν)}}`. -/
theorem lip032_44_one_parameter_gibbs_family_contains_minimizer_minimizer
    (ν : ProbabilityMeasure (Torus 1)) (hν : ν ∈ minimizerSetStar_LIP03244) :
    momentStar_LIP03241 (ν : Measure (Torus 1)) ∈ Set.Icc (-1 : ℝ) 1 ∧
      (ν : Measure (Torus 1)) =
        densityMeasure_LIP03218
          (densityStar_LIP03244 (momentStar_LIP03241 (ν : Measure (Torus 1)))) := by
  refine ⟨abs_le.mp
    (lip032_44_one_parameter_gibbs_family_contains_minimizer_moment_bound _), ?_⟩
  have h := (lip032_18_density_probability_test_integral_bridge_gibbs
    interactionDataStar_LIP03241 ν hν).2.2.2
  rw [lip032_44_one_parameter_gibbs_family_contains_minimizer_gibbs_density] at h
  exact h.symm

/-- MAIN (LIP032.44). The one-parameter Gibbs family `P_a`, `a ∈ [-1, 1]`, consists of smooth
positive probability densities with the stated bounds, and every minimizer `ν ∈ S_*` equals
`μ_{P_a}` for `a = M(ν) ∈ [-1, 1]`. -/
theorem lip032_44_one_parameter_gibbs_family_contains_minimizer :
    (∀ a : ℝ, a ∈ Set.Icc (-1 : ℝ) 1 →
      Real.exp (-8) ≤ normalizerStar_LIP03244 a ∧ normalizerStar_LIP03244 a ≤ Real.exp 8 ∧
        (∀ x, Real.exp (-16) ≤ densityStar_LIP03244 a x ∧
          densityStar_LIP03244 a x ≤ Real.exp 16) ∧
        IsSmoothPeriodic (densityStar_LIP03244 a) ∧ (∀ x, 0 < densityStar_LIP03244 a x) ∧
        ∫ x, densityStar_LIP03244 a x ∂haar 1 = 1 ∧
        IsProbabilityMeasure (densityMeasure_LIP03218 (densityStar_LIP03244 a))) ∧
    ∀ ν : ProbabilityMeasure (Torus 1), ν ∈ minimizerSetStar_LIP03244 →
      momentStar_LIP03241 (ν : Measure (Torus 1)) ∈ Set.Icc (-1 : ℝ) 1 ∧
        (ν : Measure (Torus 1)) =
          densityMeasure_LIP03218
            (densityStar_LIP03244 (momentStar_LIP03241 (ν : Measure (Torus 1)))) :=
  ⟨fun _ ha => lip032_44_one_parameter_gibbs_family_contains_minimizer_family ha,
    fun ν hν => lip032_44_one_parameter_gibbs_family_contains_minimizer_minimizer ν hν⟩

end DGPS.Frontier.LIP032
