import LeanResearch.PeriodicAttractiveLogGas.ReferenceDensityChange
import LeanResearch.PeriodicAttractiveLogGas.ReferencePotentialBounds

/-! Source eq:reference-exponential-comparison and its bounded-tilt remaining
term. Conditional entropy identities and tensorization are separate results. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PeriodicAttractiveLogGas.ReferenceExponentialComparison

open MeshCells LabelOccupations CellRestrictions ReferenceResidual ReferenceSelfTerms
  ResidualExponential ResidualNearExponential ResidualFarExponential GreenGradientOscillation
  ReferenceDensityChange ReferencePotentialBounds MovingPoleCalculus

/-- The finite change-of-reference calculation derives the target-law
integrability before converting its real integral. -/
theorem comparison_of_moments {Ω : Type*} [MeasurableSpace Ω]
    (ρ P : Measure Ω) [IsProbabilityMeasure ρ] [IsProbabilityMeasure P]
    {Y s : Ω → ℝ} (hY : Measurable Y) (hs : Measurable s)
    {β S C Z : ℝ} (hβ : 0 ≤ β) (hC : 0 < C) (hZ : 0 < Z)
    (hself : ∀ᵐ X ∂ρ, |s X| ≤ S)
    (hTI : Integrable (fun X => Real.exp (β * Y X - β * s X)) ρ)
    (hZI : Z = ∫ X, Real.exp (β * Y X - β * s X) ∂ρ)
    (hP : P = ρ.withDensity (fun X => ENNReal.ofReal (Real.exp (β * Y X - β * s X) / Z)))
    (hE₁ : Integrable (fun X => Real.exp (β * Y X)) ρ)
    (hE₁b : (∫ X, Real.exp (β * Y X) ∂ρ) ≤ C)
    (hE₃ : Integrable (fun X => Real.exp (3 * β * Y X)) ρ)
    (hE₃b : (∫ X, Real.exp (3 * β * Y X) ∂ρ) ≤ C) :
    Real.log Z ≤ β * S + Real.log C ∧
    Integrable (fun X => Real.exp (2 * β * Y X)) P ∧
    Real.log (∫ X, Real.exp (2 * β * Y X) ∂P) ≤ -Real.log Z + β * S + Real.log C := by
  have hdom (a : ℝ) : ∀ᵐ X ∂ρ,
      Real.exp (a * Y X - β * s X) ≤ Real.exp (β * S) * Real.exp (a * Y X) := by
    filter_upwards [hself] with X hX
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp hX).1 hβ
    linarith
  have hZb : Z ≤ Real.exp (β * S) * C := by
    rw [hZI]
    calc
      _ ≤ ∫ X, Real.exp (β * S) * Real.exp (β * Y X) ∂ρ :=
        integral_mono_ae hTI (hE₁.const_mul _) (hdom β)
      _ = Real.exp (β * S) * ∫ X, Real.exp (β * Y X) ∂ρ := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hE₁b (Real.exp_pos _).le
  have hlogZ : Real.log Z ≤ β * S + Real.log C := by
    have hh := Real.log_le_log hZ hZb
    simpa only [Real.log_mul (Real.exp_ne_zero _) hC.ne', Real.log_exp] using hh
  let q : Ω → ℝ := fun X => Real.exp (β * Y X - β * s X) / Z
  have hq : Measurable q := (((hY.const_mul β).sub (hs.const_mul β)).exp).div_const _
  have hq0 : ∀ᵐ X ∂ρ, 0 ≤ q X := Eventually.of_forall fun X => div_nonneg (Real.exp_pos _).le hZ.le
  have hid (X : Ω) : q X * Real.exp (2 * β * Y X) =
      Real.exp (3 * β * Y X - β * s X) / Z := by
    dsimp [q]
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    congr 2
    ring
  have hw : ∀ᵐ X ∂ρ, q X * Real.exp (2 * β * Y X) ≤
      (Real.exp (β * S) / Z) * Real.exp (3 * β * Y X) := by
    filter_upwards [hdom (3 * β)] with X hX
    rw [hid]
    simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right hX hZ.le
  have hwi : Integrable (fun X => q X * Real.exp (2 * β * Y X)) ρ :=
    (hE₃.const_mul (Real.exp (β * S) / Z)).mono' (hq.mul ((hY.const_mul (2 * β)).exp)).aestronglyMeasurable
      (hw.mono fun X hX => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg (Real.exp_pos _).le hZ.le) (Real.exp_pos _).le)]
        exact hX)
  have hpi : Integrable (fun X => Real.exp (2 * β * Y X)) P :=
    (RelativeEntropyVariational.integrable_density_iff hP hq hq0).mpr hwi
  have hPb : (∫ X, Real.exp (2 * β * Y X) ∂P) ≤ (Real.exp (β * S) / Z) * C := by
    rw [DensityMoments.integral_density hP hq hq0]
    calc
      _ ≤ ∫ X, (Real.exp (β * S) / Z) * Real.exp (3 * β * Y X) ∂ρ :=
        integral_mono_ae hwi (hE₃.const_mul _) hw
      _ = (Real.exp (β * S) / Z) * ∫ X, Real.exp (3 * β * Y X) ∂ρ := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hE₃b (div_nonneg (Real.exp_pos _).le hZ.le)
  refine ⟨hlogZ, hpi, ?_⟩
  have hh := Real.log_le_log (integral_exp_pos hpi) hPb
  rw [Real.log_mul (div_ne_zero (Real.exp_ne_zero _) hZ.ne') hC.ne',
    Real.log_div (Real.exp_ne_zero _) hZ.ne', Real.log_exp] at hh
  linarith

theorem source_reference_domination {J N : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) (η : LabelVector J N) (β : ℝ)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (hdensity : ∀ a, ∀ᵐ z ∂meshCellMeasure J hJ a,
      Real.exp (-1) ≤ Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ∧
      Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ≤ Real.exp 1) :
    ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a := by
  intro a
  rw [hformula a]
  exact NearLogMomentBounds.withDensity_le_exp_smul _ _
    ((hdensity a).mono fun z hz => ENNReal.ofReal_le_ofReal hz.2)

/-- Both inequalities in source eq:reference-exponential-comparison for the
actual labelled Gibbs law and the same self-consistent reference family. -/
theorem reference_exponential_comparison {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    {β β₀ t C₂ : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
    (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (hmesh : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) (ht : 0 ≤ t) (hη : OccupationCap t η)
    (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
      nearScale (chosenRadius β₀ C₂) * t ≤ 1)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (hdensity : ∀ a, ∀ᵐ z ∂meshCellMeasure J hJ a,
      Real.exp (-1) ≤ Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ∧
      Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ≤ Real.exp 1) :
    0 < referenceNormalizer μ η β ∧
    Real.log (referenceNormalizer μ η β) ≤ β * selfBound J + Real.log (sharpConstant β₀ C₂) ∧
    Integrable (fun X => Real.exp (2 * β * residualSum μ η X)) (labelGibbsMeasure hJ η β) ∧
    Real.log (∫ X, Real.exp (2 * β * residualSum μ η X) ∂labelGibbsMeasure hJ η β) ≤
      -Real.log (referenceNormalizer μ η β) + β * selfBound J + Real.log (sharpConstant β₀ C₂) := by
  have hβsub : β < 4 := hβle.trans_lt hsub
  let _ := isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ hβsub
  have hμ := source_reference_domination hJ μ η β hformula hdensity
  have h8 : 8 ≤ J := by omega
  have hc := change_of_reference_with_self_bounds hJ h8 hN μ η hβ hβsub hformula hdensity
  have hE₁ := residual_exponential_bound hJ hN (hβ.trans hβle) hC hk hmesh μ hμ
    hβ (by linarith) ht hcap η hη
  have hE₃ := residual_exponential_bound hJ hN (hβ.trans hβle) hC hk hmesh μ hμ
    (show 0 ≤ 3 * β by positivity) (show 3 * β ≤ 3 * β₀ by linarith) ht hcap η hη
  have hsharp : 0 < sharpConstant β₀ C₂ := by unfold sharpConstant; positivity
  have hh := comparison_of_moments (Measure.pi (fun i => μ (η i))) (labelGibbsMeasure hJ η β)
    (ReferenceDensityChange.measurable_residualSum μ η) (measurable_selfTerm μ η)
    hβ hsharp hc.2.1 hc.2.2.2.2.2 hc.1 rfl hc.2.2.1 hE₁.1 hE₁.2 hE₃.1 hE₃.2
  exact ⟨hc.2.1, hh⟩

/-- The bounded-tilt entropy estimate for the actual source remaining term.
This theorem does not assert a conditional entropy identity or tensorization. -/
theorem bounded_tilt_remaining_term {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    {β β₀ t C₂ : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
    (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (hmesh : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) (ht : 0 ≤ t) (hη : OccupationCap t η)
    (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
      nearScale (chosenRadius β₀ C₂) * t ≤ 1)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (hdensity : ∀ a, ∀ᵐ z ∂meshCellMeasure J hJ a,
      Real.exp (-1) ≤ Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ∧
      Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ≤ Real.exp 1)
    (Q : Measure (Configuration N)) [IsProbabilityMeasure Q]
    (q : Configuration N → ℝ) (hq : Measurable q) {K : ℝ}
    (hQ : Q = (labelGibbsMeasure hJ η β).withDensity (fun X => ENNReal.ofReal (q X)))
    (hb : ∀ᵐ X ∂labelGibbsMeasure hJ η β, 0 ≤ q X ∧ q X ≤ K) :
    Integrable (fun X => 2 * β * residualSum μ η X) Q ∧
    Integrable (fun X => Real.log (q X)) Q ∧
    (∫ X, 2 * β * residualSum μ η X ∂Q) ≤ (∫ X, Real.log (q X) ∂Q) -
      Real.log (referenceNormalizer μ η β) + β * selfBound J + Real.log (sharpConstant β₀ C₂) ∧
    (1 / 2 : ℝ) * (∫ X, Real.log (q X) ∂Q) -
        (2 * β₀ * selfBound J + Real.log (sharpConstant β₀ C₂)) ≤
      (∫ X, Real.log (q X) ∂Q) - (1 / 2 : ℝ) * (∫ X, 2 * β * residualSum μ η X ∂Q) -
        Real.log (referenceNormalizer μ η β) -
        (β / (N : ℝ)) * ∑ i, pairAverage (μ (η i)) (μ (η i)) := by
  have hβsub : β < 4 := hβle.trans_lt hsub
  let _ := isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ hβsub
  have hμ := source_reference_domination hJ μ η β hformula hdensity
  have hNp : 0 < N := by omega
  have hc := reference_exponential_comparison hJ hN hβ hβle hsub hC hk hmesh μ η ht hη hcap hformula hdensity
  have hlo : ∀ᵐ X ∂labelGibbsMeasure hJ η β,
      (2 * β) * (-(N : ℝ) * (greenLowerConstant + 3 * globalPotentialBound J)) ≤
        2 * β * residualSum μ η X :=
    Eventually.of_forall fun X => mul_le_mul_of_nonneg_left
      (residualSum_lower_bound hJ hNp μ hμ η X) (by positivity)
  have hv := RelativeEntropyVariational.bounded_tilt_relativeEntropy hQ hq hb
    ((ReferenceDensityChange.measurable_residualSum μ η).const_mul (2 * β)) hlo hc.2.2.1
  have hG : (∫ X, 2 * β * residualSum μ η X ∂Q) ≤ (∫ X, Real.log (q X) ∂Q) -
      Real.log (referenceNormalizer μ η β) + β * selfBound J + Real.log (sharpConstant β₀ C₂) := by
    linarith [hv.2.2, hc.2.2.2]
  refine ⟨hv.1, hv.2.1, hG, ?_⟩
  have h8 : 8 ≤ J := by omega
  have hpair : (∑ i, pairAverage (μ (η i)) (μ (η i))) ≤ (N : ℝ) * selfBound J := by
    calc
      _ ≤ ∑ _ : Fin N, selfBound J := Finset.sum_le_sum fun i _ =>
        (le_abs_self _).trans ((own_cell_pairAverage_abs hJ h8 (η i) (μ (η i)) (hμ (η i))).2)
      _ = _ := by simp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hcost : (β / (N : ℝ)) * ∑ i, pairAverage (μ (η i)) (μ (η i)) ≤ β * selfBound J := by
    calc
      _ ≤ (β / (N : ℝ)) * ((N : ℝ) * selfBound J) :=
        mul_le_mul_of_nonneg_left hpair (div_nonneg hβ hNr.le)
      _ = _ := by field_simp
  have hβs := mul_le_mul_of_nonneg_right hβle (selfBound_nonneg hJ)
  linarith [hc.2.1]

end PeriodicAttractiveLogGas.ReferenceExponentialComparison
