import LeanResearch.PeriodicAttractiveLogGas.ResidualNearExponential
import LeanResearch.PeriodicAttractiveLogGas.ResidualFarExponential
import LeanResearch.PeriodicAttractiveLogGas.BoundaryCovarianceSplitting

/-! The supplied near/far Cauchy--Schwarz proof of Proposition
`prop:residual-exponential`, source lines 2578--2630. The references are actual
probability measures; no reference fixed-point conclusion is assumed here. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

namespace PeriodicAttractiveLogGas.ResidualExponential

open MeshCells MeshNearbyGeometry LabelOccupations ReferenceResidual
  ResidualNearExponential ResidualFarExponential GreenGradientOscillation

def residualSum {J N : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J N) (X : Fin N → Torus) : ℝ :=
  CanonicalPairs.canonicalSum
    (fun i j => ReferenceResidual.residual (μ (η i)) (μ (η j))) X / N

theorem residualSum_eq_upper_pairs {J N : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J N) (X : Fin N → Torus) :
    residualSum μ η X = (∑ ij ∈ upperPairs N,
      residual (μ (η ij.1)) (μ (η ij.2)) (X ij.1) (X ij.2)) / N := by
  rw [residualSum, canonicalSum_eq_sum_pairs]

theorem residualSum_split {J N : ℕ} (R : ℕ) (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J N) (X : Fin N → Torus) :
    residualSum μ η X = farResidualSum R μ η X + nearResidualSum R μ η X := by
  classical
  rw [residualSum_eq_upper_pairs, farResidualSum, canonicalSum_eq_sum_pairs,
    nearResidualSum, ← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  by_cases hd : periodicIndexDistance (η ij.1) (η ij.2) ≤ R
  · simp [farKernel, hd, not_lt.mpr hd]
  · simp [farKernel, hd, lt_of_not_ge hd]

theorem measurable_near_far {J N : ℕ} (R : ℕ)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) :
    Measurable (nearResidualSum R μ η) ∧ Measurable (farResidualSum R μ η) := by
  classical
  have hr (i j : Fin N) : Measurable (fun X : Fin N → Torus =>
      residual (μ (η i)) (μ (η j)) (X i) (X j)) := by
    have hk : Measurable (Function.uncurry (residual (μ (η i)) (μ (η j)))) :=
      ResidualDoubleCentering.measurable_doubleCenter (μ (η i)) (μ (η j))
        greenKernel measurable_greenKernel
    have hp : Measurable (fun X : Fin N → Torus => (X i, X j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    simpa only [Function.comp_def, Function.uncurry] using hk.comp hp
  constructor
  · apply Measurable.div_const
    apply Finset.measurable_sum
    intro ij hij
    by_cases hd : periodicIndexDistance (η ij.1) (η ij.2) ≤ R
    · simpa only [hd, ite_true] using hr ij.1 ij.2
    · simpa only [hd, ite_false] using (measurable_const : Measurable (fun _ : Fin N → Torus => (0 : ℝ)))
  · change Measurable (fun X => CanonicalPairs.canonicalSum (farKernel R μ η) X / (N : ℝ))
    simp_rw [canonicalSum_eq_sum_pairs]
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro ij hij
    by_cases hd : R < periodicIndexDistance (η ij.1) (η ij.2)
    · simpa only [farKernel, hd, ite_true] using hr ij.1 ij.2
    · simpa only [farKernel, hd, ite_false] using (measurable_const : Measurable (fun _ : Fin N → Torus => (0 : ℝ)))

/-- Cauchy--Schwarz with the square integrability derived from the two actual
doubled exponential moments. -/
theorem exponential_cauchy_schwarz {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) {F G : Ω → ℝ} (hF : Measurable F) (hG : Measurable G)
    {a b : ℝ} (ha : 0 ≤ a)
    (hFI : Integrable (fun X => Real.exp (2 * F X)) ρ)
    (hGI : Integrable (fun X => Real.exp (2 * G X)) ρ)
    (hFb : (∫ X, Real.exp (2 * F X) ∂ρ) ≤ a)
    (hGb : (∫ X, Real.exp (2 * G X) ∂ρ) ≤ Real.exp (2 * b)) :
    Integrable (fun X => Real.exp (F X + G X)) ρ ∧
    (∫ X, Real.exp (F X + G X) ∂ρ) ≤ Real.sqrt a * Real.exp b := by
  have he (u : ℝ) : Real.exp u ^ 2 = Real.exp (2 * u) := by
    rw [two_mul, Real.exp_add, pow_two]
  have hf : MemLp (fun X => Real.exp (F X)) 2 ρ :=
    (memLp_two_iff_integrable_sq hF.exp.aestronglyMeasurable).mpr (by simpa only [he] using hFI)
  have hg : MemLp (fun X => Real.exp (G X)) 2 ρ :=
    (memLp_two_iff_integrable_sq hG.exp.aestronglyMeasurable).mpr (by simpa only [he] using hGI)
  have hi : Integrable (fun X => Real.exp (F X + G X)) ρ := by
    simpa only [Real.exp_add, Pi.mul_apply] using! hf.integrable_mul hg
  refine ⟨hi, ?_⟩
  have hs := BoundaryCovarianceSplitting.integral_mul_squared_le hf hg
  simp only [← Real.exp_add, he] at hs
  have hb := mul_le_mul hFb hGb (integral_nonneg fun X => (Real.exp_pos _).le) ha
  have hsq : (Real.sqrt a * Real.exp b) ^ 2 = a * Real.exp (2 * b) := by
    rw [mul_pow, Real.sq_sqrt ha, he]
  have hpos : 0 ≤ Real.sqrt a * Real.exp b := by positivity
  nlinarith [hs.trans hb]

def sharpConstant (β₀ C₂ : ℝ) : ℝ :=
  Real.sqrt (5 / 3) * Real.exp (2 * β₀ *
    (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant * nearScale (chosenRadius β₀ C₂))

/-- The complete product-reference conclusion of the supplied residual
exponential proposition. All moments and independence inputs are discharged. -/
theorem residual_exponential_bound {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    {β₀ τ t C₂ : ℝ} (hβ : 0 ≤ β₀) (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (hmesh : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (hτ : 0 ≤ τ) (hτβ : τ ≤ 3 * β₀) (ht : 0 ≤ t)
    (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
      nearScale (chosenRadius β₀ C₂) * t ≤ 1)
    (η : LabelVector J N) (hη : OccupationCap t η) :
    Integrable (fun X => Real.exp (τ * residualSum μ η X)) (Measure.pi (fun i => μ (η i))) ∧
    (∫ X, Real.exp (τ * residualSum μ η X) ∂Measure.pi (fun i => μ (η i))) ≤
      sharpConstant β₀ C₂ := by
  have hf := chosen_far_exponential_bound hJ hN μ hμ hβ hτ hτβ hC hk η
  have hn := near_exponential_bound hJ hN hmesh μ hμ hβ hτ hτβ ht hcap η hη
  obtain ⟨hmn, hmf⟩ := measurable_near_far (chosenRadius β₀ C₂) μ η
  have hb : 2 * (2 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
      nearScale (chosenRadius β₀ C₂)) =
      4 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
        nearScale (chosenRadius β₀ C₂) := by ring
  have hc := exponential_cauchy_schwarz (Measure.pi (fun i => μ (η i)))
    (hmf.const_mul τ) (hmn.const_mul τ) (a := (5 : ℝ) / 3)
    (b := 2 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
      nearScale (chosenRadius β₀ C₂)) (by positivity)
    (by simpa only [mul_assoc] using hf.1)
    (by simpa only [mul_assoc] using hn.1)
    (by simpa only [mul_assoc] using hf.2)
    (by rw [hb]; simpa only [mul_assoc] using hn.2.1)
  simpa only [sharpConstant, residualSum_split (chosenRadius β₀ C₂), mul_add] using hc

/-- The source's original two-sided cell densities. The upper measure
comparison is derived here; the lower bound remains an explicit source input. -/
theorem residual_exponential_density_bound {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    {β₀ τ t C₂ : ℝ} (hβ : 0 ≤ β₀) (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (hmesh : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (w : MeshIndex J → Torus → ℝ≥0∞)
    (hμw : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (w a))
    (hw : ∀ a, ∀ᵐ x ∂meshCellMeasure J hJ a,
      ENNReal.ofReal (Real.exp (-1)) ≤ w a x ∧ w a x ≤ ENNReal.ofReal (Real.exp 1))
    (hτ : 0 ≤ τ) (hτβ : τ ≤ 3 * β₀) (ht : 0 ≤ t)
    (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
      nearScale (chosenRadius β₀ C₂) * t ≤ 1)
    (η : LabelVector J N) (hη : OccupationCap t η) :
    Integrable (fun X => Real.exp (τ * residualSum μ η X)) (Measure.pi (fun i => μ (η i))) ∧
    (∫ X, Real.exp (τ * residualSum μ η X) ∂Measure.pi (fun i => μ (η i))) ≤
      sharpConstant β₀ C₂ := by
  apply residual_exponential_bound hJ hN hβ hC hk hmesh μ _ hτ hτβ ht hcap η hη
  intro a
  rw [hμw a]
  exact NearLogMomentBounds.withDensity_le_exp_smul _ _ ((hw a).mono fun _ h => h.2)

theorem residual_exponential_zero {J N : ℕ}
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) :
    Integrable (fun X => Real.exp (0 * residualSum μ η X)) (Measure.pi (fun i => μ (η i))) ∧
    (∫ X, Real.exp (0 * residualSum μ η X) ∂Measure.pi (fun i => μ (η i))) = 1 := by
  simp only [zero_mul, Real.exp_zero]
  exact ⟨integrable_const 1, by simp⟩

/-- At zero coupling the cap is automatic and the exponential integral is
exactly one, without any occupancy or geometric restriction. -/
theorem residual_exponential_zero_coupling {J N : ℕ} (C₂ t : ℝ)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) {τ : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ 3 * (0 : ℝ)) :
    24 * (0 : ℝ) * (colorCount (chosenRadius 0 C₂) : ℝ) * universalConstant *
      nearScale (chosenRadius 0 C₂) * t ≤ 1 ∧
    Integrable (fun X => Real.exp (τ * residualSum μ η X)) (Measure.pi (fun i => μ (η i))) ∧
    (∫ X, Real.exp (τ * residualSum μ η X) ∂Measure.pi (fun i => μ (η i))) = 1 := by
  have hzero : τ = 0 := by linarith
  subst τ
  exact ⟨by norm_num, residual_exponential_zero μ η⟩

end PeriodicAttractiveLogGas.ResidualExponential
