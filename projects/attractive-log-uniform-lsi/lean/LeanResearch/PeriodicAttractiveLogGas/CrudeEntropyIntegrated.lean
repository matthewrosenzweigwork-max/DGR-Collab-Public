import LeanResearch.PeriodicAttractiveLogGas.CrudeResidualIntegrated
import LeanResearch.PeriodicAttractiveLogGas.ConditionalLogSobolev
import LeanResearch.PeriodicAttractiveLogGas.LightRegionEntropy
import LeanResearch.PeriodicAttractiveLogGas.OccupationMassCutoff

/-! Source Proposition `crude-entropy-integrated`, lines3275--3351.
The actual reference correction and the original label law are retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped ENNReal NNReal BigOperators
namespace PeriodicAttractiveLogGas.CrudeEntropyIntegrated
open MeshCells LabelOccupations CellRestrictions ConditionalLawEstimates
  ReferenceResidual ReferenceSelfTerms ReferencePotentialBounds ReferenceDensityChange
  ReferenceConditionalNormalization CrudeResidualIntegrated ResidualExponential
  MovingPoleCalculus ConditionalEntropyDisintegration RelativeEntropyReferenceChange

def selfScale : ℝ := Real.exp 1 * (1 + kernelConstant + Real.pi / 2) + greenLowerConstant

def conditionalConstant (β₀ t C₂ : ℝ) : ℝ :=
  2 * β₀ * selfScale + integratedConstant (radius β₀) β₀ t C₂

def labelConstant (β₀ : ℝ) : ℝ :=
  Real.log 10 + β₀ * (kernelConstant + greenLowerConstant / 2) + 2 + β₀

theorem selfScale_nonneg : 0 ≤ selfScale := by
  have := kernelConstant_pos.le
  have := greenLowerConstant_pos.le
  unfold selfScale
  positivity

theorem selfBound_le_scale {J : ℕ} (hJ : 0 < J) :
    selfBound J ≤ selfScale * (1 + Real.log J) := by
  have hj : 0 ≤ Real.log (J : ℝ) := Real.log_nonneg (by exact_mod_cast hJ)
  have hc : 0 ≤ Real.exp 1 * (kernelConstant + Real.pi / 2) + greenLowerConstant := by
    have := kernelConstant_pos.le
    have := greenLowerConstant_pos.le
    positivity
  have := mul_nonneg hc hj
  unfold selfBound selfScale
  nlinarith [Real.exp_pos (1 : ℝ)]

/-- Actual product canonicality, with joint integrability proved before Fubini. -/
theorem residual_integrable_centered {J N : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J N) :
    Integrable (residualSum μ η) (Measure.pi (fun i => μ (η i))) ∧
      (∫ X, residualSum μ η X ∂Measure.pi (fun i => μ (η i))) = 0 := by
  let ν : Fin N → Measure Torus := fun i => μ (η i)
  let h : Fin N → Fin N → Torus → Torus → ℝ := fun i j => residual (μ (η i)) (μ (η j))
  let f := CanonicalPairs.upperKernel h
  have htri : ∀ i j, ¬ i < j → ∀ x y, f i j x y = 0 := by
    intro i j hij x y
    simp [f, CanonicalPairs.upperKernel, hij]
  have hi (i j : Fin N) : Integrable (Function.uncurry (f i j)) ((ν i).prod (ν j)) := by
    by_cases hij : i < j
    · have hh := ResidualDoubleCentering.integrable_doubleCenter (μ (η i)) (μ (η j)) greenKernel
        (integrable_green_product hJ (η j) _ _ (hμ (η j)))
      have he : f i j = h i j := CanonicalPairs.upperKernel_of_lt h hij
      rw [he]
      simpa only [h, ReferenceResidual.residual, ν] using hh
    · have he : f i j = fun _ _ => 0 := funext fun x => funext fun y => htri i j hij x y
      rw [he]
      exact integrable_const (0 : ℝ)
  have hz : ∀ i j, ∀ᵐ x ∂ν i, (∫ y, f i j x y ∂ν j) = 0 := by
    intro i j
    by_cases hij : i < j
    · have hh := ResidualDoubleCentering.ae_integral_doubleCenter_right_eq_zero
        (μ (η i)) (μ (η j)) greenKernel (integrable_green_product hJ (η j) _ _ (hμ (η j)))
      have he : f i j = h i j := CanonicalPairs.upperKernel_of_lt h hij
      rw [he]
      simpa only [h, ReferenceResidual.residual, ν] using hh
    · exact Eventually.of_forall fun x => by simp [htri i j hij]
  have hsum := CanonicalDecoupling.integrable_pairSum ν f htri hi
  have hzero := CanonicalDecoupling.integral_pairSum_eq_zero ν f htri hi hz
  refine ⟨hsum.div_const N, ?_⟩
  change (∫ X, CanonicalDecoupling.pairSum f X / N ∂Measure.pi ν) = 0
  rw [integral_div, hzero, zero_div]

/-- Holder's cubic interpolation, proved by its elementary Young inequality.
Both real integrals are genuinely integrable before the comparison. -/
theorem log_exp_third_le {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {F : Ω → ℝ}
    (h₁ : Integrable (fun x => Real.exp (F x)) ρ)
    (h₃ : Integrable (fun x => Real.exp (3 * F x)) ρ) :
    Real.log (∫ x, Real.exp (F x) ∂ρ) ≤
      (1 / 3 : ℝ) * Real.log (∫ x, Real.exp (3 * F x) ∂ρ) := by
  let M : ℝ := Real.log (∫ x, Real.exp (3 * F x) ∂ρ) / 3
  have hM : Real.exp (3 * M) = ∫ x, Real.exp (3 * F x) ∂ρ := by
    have he : 3 * M = Real.log (∫ x, Real.exp (3 * F x) ∂ρ) := by dsimp [M]; ring
    rw [he, Real.exp_log (integral_exp_pos h₃)]
  have hb (x : Ω) : Real.exp (F x) ≤
      (Real.exp (-2 * M) / 3) * Real.exp (3 * F x) + (2 / 3 : ℝ) * Real.exp M := by
    let a := Real.exp (F x - M)
    have ha : 0 < a := Real.exp_pos _
    have hy : a ≤ a^3 / 3 + 2 / 3 := by nlinarith [mul_nonneg (sq_nonneg (a - 1)) (by linarith : 0 ≤ a + 2)]
    have he : a ^ 3 = Real.exp (3 * (F x - M)) := by
      dsimp [a]; symm; exact Real.exp_nat_mul _ 3
    have hh := mul_le_mul_of_nonneg_left hy (Real.exp_pos M).le
    rw [he] at hh
    have hleft : Real.exp M * a = Real.exp (F x) := by
      dsimp [a]; rw [← Real.exp_add]; congr 1; ring
    rw [hleft] at hh
    convert hh using 1
    have he' : Real.exp M * Real.exp (3 * (F x - M)) =
        Real.exp (-2 * M) * Real.exp (3 * F x) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    nlinarith only [he']
  have hh := integral_mono h₁ ((h₃.const_mul _).add (integrable_const _)) hb
  simp only [Pi.add_apply] at hh
  rw [integral_add (h₃.const_mul _) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, one_smul, ← hM] at hh
  have he : Real.exp (-2 * M) / 3 * Real.exp (3 * M) + (2 / 3 : ℝ) * Real.exp M = Real.exp M := by
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    rw [show -2 * M + 3 * M = M by ring]
    ring
  rw [he] at hh
  have hl := Real.log_le_log (integral_exp_pos h₁) hh
  rw [Real.log_exp] at hl
  dsimp [M] at hl
  linarith

/-- Canonicality supplies the sign needed when weakening the two-thirds cost. -/
theorem log_residual_exp_nonneg {J N : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J N) (q : ℝ)
    (he : Integrable (fun X => Real.exp (q * residualSum μ η X))
      (Measure.pi (fun i => μ (η i)))) :
    0 ≤ Real.log (∫ X, Real.exp (q * residualSum μ η X) ∂Measure.pi (fun i => μ (η i))) := by
  obtain ⟨hi, hz⟩ := residual_integrable_centered hJ μ hμ η
  have hh := log_integral_exp_ge (Measure.pi (fun i => μ (η i))) (hi.const_mul q) he
  simpa only [integral_const_mul, hz, mul_zero] using hh

/-- The one-body correction is retained inside the actual integral. -/
theorem corrected_exp_bound {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {F s : Ω → ℝ}
    (hF : Measurable F) (hs : Measurable s) {β S : ℝ} (hβ : 0 ≤ β)
    (hself : ∀ᵐ x ∂ρ, |s x| ≤ S) (hi : Integrable (fun x => Real.exp (F x)) ρ) :
    Integrable (fun x => Real.exp (F x - β * s x)) ρ ∧
    Real.log (∫ x, Real.exp (F x - β * s x) ∂ρ) ≤
      β * S + Real.log (∫ x, Real.exp (F x) ∂ρ) := by
  have hd : ∀ᵐ x ∂ρ, Real.exp (F x - β * s x) ≤ Real.exp (β * S) * Real.exp (F x) := by
    filter_upwards [hself] with x hx
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp hx).1 hβ
    linarith
  have hI : Integrable (fun x => Real.exp (F x - β * s x)) ρ :=
    (hi.const_mul _).mono' ((hF.sub (hs.const_mul β)).exp.aestronglyMeasurable)
      (hd.mono fun x hx => by simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hx)
  refine ⟨hI, ?_⟩
  have hh := integral_mono_ae hI (hi.const_mul _) hd
  rw [integral_const_mul] at hh
  have hl := Real.log_le_log (integral_exp_pos hI) hh
  simpa only [Real.log_mul (Real.exp_ne_zero _) (integral_exp_pos hi).ne', Real.log_exp] using hl

/-- Exact density cancellation, after proving integrability under the tilted law. -/
theorem corrected_third_identity {Ω : Type*} [MeasurableSpace Ω]
    (ρ P : Measure Ω) [IsProbabilityMeasure ρ] [IsProbabilityMeasure P]
    {Y s : Ω → ℝ} (hY : Measurable Y) (hs : Measurable s) {β Z : ℝ} (hZ : 0 < Z)
    (hP : P = ρ.withDensity (fun X => ENNReal.ofReal (Real.exp (β * Y X - β * s X) / Z)))
    (hi : Integrable (fun X => Real.exp (3 * β * Y X - β * s X)) ρ) :
    Integrable (fun X => Real.exp (2 * β * Y X)) P ∧
    Real.log (∫ X, Real.exp (2 * β * Y X) ∂P) =
      Real.log (∫ X, Real.exp (3 * β * Y X - β * s X) ∂ρ) - Real.log Z := by
  let q : Ω → ℝ := fun X => Real.exp (β * Y X - β * s X) / Z
  have hq : Measurable q := ((hY.const_mul β).sub (hs.const_mul β)).exp.div_const _
  have hq0 : ∀ᵐ X ∂ρ, 0 ≤ q X := Eventually.of_forall fun _ =>
    div_nonneg (Real.exp_pos _).le hZ.le
  have hid (X : Ω) : q X * Real.exp (2 * β * Y X) =
      Real.exp (3 * β * Y X - β * s X) / Z := by
    dsimp [q]
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    congr 2
    ring
  have hwi : Integrable (fun X => q X * Real.exp (2 * β * Y X)) ρ := by
    simp_rw [hid]
    exact hi.div_const Z
  refine ⟨(RelativeEntropyVariational.integrable_density_iff hP hq hq0).mpr hwi, ?_⟩
  rw [DensityMoments.integral_density hP hq hq0]
  change Real.log (∫ X, q X * Real.exp (2 * β * Y X) ∂ρ) = _
  simp_rw [hid]
  rw [integral_div, Real.log_div (integral_exp_pos hi).ne' hZ.ne']

/-- Literal source one-body defect, before any estimate or weakening. -/
def correctionDefect {J N : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J N) (β : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (∫ X, Real.exp (3 * β * residualSum μ η X - β * selfTerm μ η X)
      ∂Measure.pi (fun i => μ (η i))) +
    (1 / 2 : ℝ) * Real.log (referenceNormalizer μ η β) +
      (β / (N : ℝ)) * ∑ i, pairAverage (μ (η i)) (μ (η i))

section Reference
variable {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
  {β β₀ t C₂ : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
  (ht : 0 < t) (htδ : t < occupationBound β₀)
  (hmesh : 8 * (radius β₀ + 4) ≤ J) (hC : 0 ≤ C₂)
  (hk : GreenGradientOscillation.KernelHessianBound C₂)
  (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
  (η : LabelVector J N) (hη : OccupationCap t η)
  (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
    ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
  (hdensity : ∀ a, ∀ᵐ z ∂meshCellMeasure J hJ a,
    Real.exp (-1) ≤ Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ∧
    Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ≤ Real.exp 1)

include hN hβ hβle hsub ht htδ hmesh hC hk hη hformula hdensity

theorem reference_crude_moments :
    Integrable (fun X => Real.exp (2 * β * residualSum μ η X)) (labelGibbsMeasure hJ η β) ∧
    Real.log (∫ X, Real.exp (2 * β * residualSum μ η X) ∂labelGibbsMeasure hJ η β) =
      Real.log (∫ X, Real.exp (3 * β * residualSum μ η X - β * selfTerm μ η X)
        ∂Measure.pi (fun i => μ (η i))) - Real.log (referenceNormalizer μ η β) ∧
    correctionDefect μ η β ≤ conditionalConstant β₀ t C₂ * N * (1 + Real.log J) := by
  let : IsProbabilityMeasure (labelGibbsMeasure hJ η β) :=
    isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ (hβle.trans_lt hsub)
  have hμ := ReferenceExponentialComparison.source_reference_domination hJ μ η β hformula hdensity
  have hc := change_of_reference_with_self_bounds hJ (by omega) hN μ η hβ
    (hβle.trans_lt hsub) hformula hdensity
  have hex (q : ℝ) (hq : 0 ≤ q) (hqβ : q ≤ 3 * β₀) :=
    crude_residual_of_domination hJ hN (radius_one_le β₀) (by omega)
      (hβ.trans hβle) ht.le hC hk hq hqβ
      (microscopic_power_bound (hβ.trans hβle) ht.le htδ) μ hμ η hη
  have h₁ := hex β hβ (by linarith)
  have h₃ := hex (3 * β) (by positivity) (by linarith)
  have hself := hc.2.2.2.2.2
  have hT₃ := corrected_exp_bound (Measure.pi (fun i => μ (η i)))
    ((measurable_residualSum μ η).const_mul (3 * β)) (measurable_selfTerm μ η) hβ hself h₃.1
  have hT₁ := corrected_exp_bound (Measure.pi (fun i => μ (η i)))
    ((measurable_residualSum μ η).const_mul β) (measurable_selfTerm μ η) hβ hself h₁.1
  have hid := corrected_third_identity (Measure.pi (fun i => μ (η i)))
    (labelGibbsMeasure hJ η β) (measurable_residualSum μ η) (measurable_selfTerm μ η)
    hc.2.1 hc.2.2.1 hT₃.1
  refine ⟨hid.1, hid.2, ?_⟩
  have hthird : Real.log (∫ X, Real.exp (β * residualSum μ η X) ∂Measure.pi (fun i => μ (η i))) ≤
      (1 / 3 : ℝ) * Real.log (∫ X, Real.exp (3 * β * residualSum μ η X) ∂Measure.pi (fun i => μ (η i))) := by
    simpa only [mul_assoc] using log_exp_third_le (Measure.pi (fun i => μ (η i))) h₁.1
      (by simpa only [mul_assoc] using h₃.1)
  have hL₃ := log_residual_exp_nonneg hJ μ hμ η (3 * β) h₃.1
  have hpair : (β / (N : ℝ)) * ∑ i, pairAverage (μ (η i)) (μ (η i)) ≤ β * selfBound J := by
    have hh : (∑ i, pairAverage (μ (η i)) (μ (η i))) ≤ N * selfBound J := by
      calc
        _ ≤ ∑ _ : Fin N, selfBound J := Finset.sum_le_sum fun i _ =>
          (le_abs_self _).trans (hc.2.2.2.1 (η i)).2
        _ = _ := by simp
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    calc
      _ ≤ (β / (N : ℝ)) * (N * selfBound J) := mul_le_mul_of_nonneg_left hh (div_nonneg hβ hNr.le)
      _ = _ := by field_simp
  have hβs := mul_le_mul_of_nonneg_right hβle (selfBound_nonneg hJ)
  have hD : correctionDefect μ η β ≤ 2 * β₀ * selfBound J +
      Real.log (∫ X, Real.exp (3 * β * residualSum μ η X) ∂Measure.pi (fun i => μ (η i))) := by
    dsimp only [correctionDefect]
    have hlogZ := hT₁.2
    change Real.log (referenceNormalizer μ η β) ≤ _ at hlogZ
    linarith only [hlogZ, hT₃.2, hthird, hpair, hβs, hL₃]
  have hscale := mul_le_mul_of_nonneg_left (selfBound_le_scale hJ)
    (show 0 ≤ 2 * β₀ by linarith)
  have hNN : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog : 0 ≤ 1 + Real.log (J : ℝ) := by
    have := Real.log_nonneg (show 1 ≤ (J : ℝ) by exact_mod_cast hJ)
    linarith
  have hsn := mul_le_mul_of_nonneg_left hNN
    (show 0 ≤ 2 * β₀ * selfScale * (1 + Real.log J) from
      mul_nonneg (mul_nonneg (by linarith) selfScale_nonneg) hlog)
  unfold conditionalConstant
  nlinarith only [hD, hscale, hsn, h₃.2]

end Reference

section EntropyReduction
variable {J n : ℕ} (hJ : 0 < J) (hN : 2 ≤ n + 1)
  {β β₀ t C₂ : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
  (ht : 0 < t) (htδ : t < occupationBound β₀)
  (hmesh : 8 * (radius β₀ + 4) ≤ J) (hC : 0 ≤ C₂)
  (hk : GreenGradientOscillation.KernelHessianBound C₂)
  (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
  (η : LabelVector J (n + 1)) (hη : OccupationCap t η)
  (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
    ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
  (hdensity : ∀ a, ∀ᵐ z ∂meshCellMeasure J hJ a,
    Real.exp (-1) ≤ Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ∧
    Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ≤ Real.exp 1)

include hN hβ hβle hsub ht htδ hmesh hC hk hη hformula hdensity

/-- Exact source reduction with the literal D2, including every integrability
needed for the change of reference and variational inequality. -/
theorem normalized_tilt_reduction {F : Configuration (n + 1) → ℝ}
    (hF : Measurable F) {K : ℝ} (hb : ∀ X, 0 ≤ F X ∧ F X ≤ K)
    (hS : 0 < ∫ X, F X ∂labelGibbsMeasure hJ η β) :
    (1 / 2 : ℝ) * (∫ X, Real.log (F X / ∫ X, F X ∂labelGibbsMeasure hJ η β)
        ∂normalizedTilt (labelGibbsMeasure hJ η β) F) - correctionDefect μ η β ≤
      ∑ i, ∫ X, conditionalLogEntropy
        (PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
          (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i)
        (F ∘ (configurationSplit i).symm) (OneCoordinateConditionals.removeSite i X)
          ∂normalizedTilt (labelGibbsMeasure hJ η β) F := by
  let P := labelGibbsMeasure hJ η β
  let S := ∫ X, F X ∂P
  let Q := normalizedTilt P F
  let q : Configuration (n + 1) → ℝ := fun X => F X / S
  let : IsProbabilityMeasure P := isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ (hβle.trans_lt hsub)
  let : IsProbabilityMeasure Q := normalizedTilt_probability
    (Eventually.of_forall fun X => (hb X).1)
    (RelativeEntropyVariational.bounded_density_integrable hF (Eventually.of_forall hb)).1 hS
  have hq : Measurable q := hF.div_const _
  have hqb : ∀ᵐ X ∂P, 0 ≤ q X ∧ q X ≤ K / S :=
    Eventually.of_forall fun X => ⟨div_nonneg (hb X).1 hS.le,
      div_le_div_of_nonneg_right (hb X).2 hS.le⟩
  have hQ : Q = P.withDensity (fun X => ENNReal.ofReal (q X)) := rfl
  have hμ := ReferenceExponentialComparison.source_reference_domination hJ μ η β hformula hdensity
  have he := reference_crude_moments hJ hN hβ hβle hsub ht htδ hmesh hC hk μ η hη hformula hdensity
  have hd := change_of_reference hJ hN μ η hβ (hβle.trans_lt hsub) hformula
  have hlo : ∀ᵐ X ∂P, (2 * β) * (-(n + 1 : ℕ) * (greenLowerConstant + 3 * globalPotentialBound J)) ≤
      2 * β * residualSum μ η X := Eventually.of_forall fun X =>
    mul_le_mul_of_nonneg_left (residualSum_lower_bound hJ (by omega) μ hμ η X) (by positivity)
  have hv := RelativeEntropyVariational.bounded_tilt_relativeEntropy hQ hq hqb
    ((measurable_residualSum μ η).const_mul (2 * β)) hlo he.1
  have hYi : Integrable (fun X => β * residualSum μ η X) Q := by
    have hh := hv.1.const_mul (1 / 2 : ℝ)
    convert hh using 1
    funext X
    ring
  have hsi := selfTerm_integrable hJ μ hμ η Q
  have hlogr : Integrable (fun X => Real.log (referenceTilt μ η β X / referenceNormalizer μ η β)) Q := by
    simpa only [Pi.sub_apply, log_reference_density μ η β hd.2.1] using!
      (hYi.sub (hsi.const_mul β)).sub (integrable_const (Real.log (referenceNormalizer μ η β)))
  have hlogrid : (∫ X, Real.log (referenceTilt μ η β X / referenceNormalizer μ η β) ∂Q) =
      (∫ X, β * residualSum μ η X ∂Q) - β * (∫ X, selfTerm μ η X ∂Q) -
        Real.log (referenceNormalizer μ η β) := by
    simp_rw [log_reference_density μ η β hd.2.1]
    have hsubi : Integrable (fun X => β * residualSum μ η X - β * selfTerm μ η X) Q :=
      hYi.sub (hsi.const_mul β)
    rw [integral_sub hsubi (integrable_const _), integral_sub hYi (hsi.const_mul β)]
    simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
  have hkl := bounded_tilt_real_change hd.2.2 hQ
    ((measurable_referenceTilt μ η β).div_const _) (fun X => div_pos (Real.exp_pos _) hd.2.1)
    hq hqb hlogr
  have hcomp := SourceConditionalEntropyComparison.comparison_of_integrable_residual
    hJ μ η hN hβ hβle hsub hformula hdensity hmesh htδ.le hη hF hb hS hkl.2.1 hYi
  have hkp : (klDiv Q P).toReal = ∫ X, Real.log (q X) ∂Q :=
    toReal_klDiv_eq_log_density hQ hq (hqb.mono fun _ h => h.1) hv.2.1
  rw [hkp, hlogrid] at hkl
  have htwo : (∫ X, 2 * β * residualSum μ η X ∂Q) = 2 * ∫ X, β * residualSum μ η X ∂Q := by
    rw [← integral_const_mul]
    congr 1
    funext X
    ring
  have hvb := hv.2.2
  rw [htwo, he.2.1] at hvb
  dsimp only [correctionDefect]
  linarith only [hcomp.2, hkl.2.2, hvb]

open SourceEntropyTests MovingPoleNumerators MovingPoleCharts GreenPointWeights
  ConditionalEntropyTightening

/-- The physical local test keeps its original Riesz-gradient energy;
only its square is represented by a bounded measurable extension. -/
theorem conditional_entropy_with_reference {f : Configuration (n + 1) → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell))) :
    entropy (labelGibbsMeasure hJ η β) (fun X => f X ^ 2) ≤
      (((2 * entropyBound β₀ / (J : ℝ) ^ 2) *
        (∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂labelGibbsMeasure hJ η β) +
        2 * conditionalConstant β₀ t C₂ * (n + 1 : ℕ) * (1 + Real.log J) *
          (∫ X, f X ^ 2 ∂labelGibbsMeasure hJ η β) : ℝ) : EReal) := by
  have hJ3 : 3 ≤ J := mesh_three_le hmesh
  have hsubβ := hβle.trans_lt hsub
  have hS0 : 0 ≤ ∫ X, f X ^ 2 ∂labelGibbsMeasure hJ η β := integral_nonneg fun _ => sq_nonneg _
  by_cases hS : ∫ X, f X ^ 2 ∂labelGibbsMeasure hJ η β = 0
  · rw [(source_zero_mass hJ hJ3 hN η hβ hsubβ hf hS).1, hS, mul_zero, add_zero]
    have hE : 0 ≤ ∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂labelGibbsMeasure hJ η β :=
      integral_nonneg (BoundaryEdgeSummation.totalEnergyDensity_nonneg f)
    have hL := entropyBound_nonneg (hβ.trans hβle)
    exact_mod_cast (show 0 ≤ (2 * entropyBound β₀ / (J : ℝ)^2) *
      (∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂labelGibbsMeasure hJ η β) by positivity)
  · have hSpos := lt_of_le_of_ne hS0 (Ne.symm hS)
    let P := labelGibbsMeasure hJ η β
    let F := squareExtension η (fun Z => f (sources Z))
    have hm : Measurable F := measurable_squareExtension hJ3 η hf.continuousOn
    obtain ⟨K, hb⟩ := squareExtension_bounds η hf.continuousOn
    have he := ConditionalLogSobolev.square_extension_entropy hJ hJ3 hN η hβ hsubβ hf
    have hr := normalized_tilt_reduction hJ hN hβ hβle hsub ht htδ hmesh hC hk μ η hη
      hformula hdensity hm hb (he.1.symm ▸ hSpos)
    have hd := (reference_crude_moments hJ hN hβ hβle hsub ht htδ hmesh hC hk μ η hη hformula hdensity).2.2
    have hE := ConditionalLogSobolev.square_extension_entropy_energy hJ μ η hβ hβle hformula
      hmesh htδ.le hη hN hsub hf hSpos
    rw [he.1] at hr
    have hweak : (1 / 2 : ℝ) * (∫ X, Real.log (F X / ∫ X, f X^2 ∂P) ∂normalizedTilt P F) -
        conditionalConstant β₀ t C₂ * (n + 1 : ℕ) * (1 + Real.log J) ≤
      ∑ i, ∫ X, conditionalLogEntropy
        (PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
          (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i)
        (F ∘ (configurationSplit i).symm) (OneCoordinateConditionals.removeSite i X) ∂normalizedTilt P F := by
      exact (sub_le_sub_left hd _).trans hr
    have hfinal := (mul_le_mul_of_nonneg_left hweak hS0).trans hE
    rw [he.2]
    apply EReal.coe_le_coe_iff.mpr
    dsimp only [P, F] at hfinal
    simp only [div_eq_mul_inv] at hfinal ⊢
    nlinarith only [hfinal]
end EntropyReduction

open SourceEntropyTests MovingPoleNumerators MovingPoleCharts GreenPointWeights

/-- Actual crude conditional entropy, with the reference constructed internally
and no sharp residual smallness condition. All temperature endpoints are included. -/
theorem crude_conditional_entropy {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    {β β₀ t C₂ : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htδ : t < occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J) (hC : 0 ≤ C₂)
    (hk : GreenGradientOscillation.KernelHessianBound C₂)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (hsmall : 4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1)
    (η : LabelVector J N) (hη : OccupationCap t η)
    {f : Configuration N → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell))) :
    entropy (labelGibbsMeasure hJ η β) (fun X => f X^2) ≤
      (((2 * entropyBound β₀ / (J : ℝ)^2) *
          (∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂labelGibbsMeasure hJ η β) +
        2 * conditionalConstant β₀ t C₂ * N * (1 + Real.log J) *
          (∫ X, f X^2 ∂labelGibbsMeasure hJ η β) : ℝ) : EReal) := by
  cases N with
  | zero => omega
  | succ n =>
    obtain ⟨μ, ρ, hμ, _, _, _, _, _, _, hformula, hdensity, _⟩ :=
      ReferenceFamilyExistence.exists_sourceReferenceFamily (hJ := hJ) hN ht hβ hβle hη hscale hsmall
    let : ∀ a, IsProbabilityMeasure (μ a) := hμ
    exact conditional_entropy_with_reference hJ hN hβ hβle hsub ht htδ hmesh hC hk
      μ η hη hformula hdensity hf

open MeshNearbyGeometry NearCellLifts SharpPoleMoments

/-- Uniform-cell original-kernel step. No reference-density factor occurs. -/
theorem original_section_exp_bound {J N R : ℕ} (hJ : 0 < J) (hN : 0 < N)
    (hR : 1 ≤ R) (hmesh : 8 * (R + 1) ≤ J)
    {β β₀ t : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (ht : 0 ≤ t)
    (hsmall : β₀ * (2 * (R : ℝ) + 1)^2 * t ≤ 1 / 16)
    (η : LabelVector J N) (hη : OccupationCap t η)
    (I : Finset (Fin N)) (b : MeshIndex J) (X : Configuration N)
    (hX : ∀ i ∈ I, X i ∈ closure (meshCell J hJ (η i))) :
    Integrable (fun y => Real.exp (β / N * ∑ i ∈ I, greenKernel (X i) y))
      (meshCellMeasure J hJ b) ∧
    (∫ y, Real.exp (β / N * ∑ i ∈ I, greenKernel (X i) y) ∂meshCellMeasure J hJ b) ≤
      Real.exp (Real.log 5 + β₀ * (Real.log J + kernelConstant)) := by
  classical
  let S := sourceIndices η I (nearbyCells R b)
  let a : ℝ := β / N
  let B : ℝ := a * I.card * (Real.log J + kernelConstant)
  let f : Torus → ℝ := fun y => β / N * ∑ i ∈ I, greenKernel (X i) y
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 ≤ a := div_nonneg hβ hNr.le
  have hcount := near_particle_count hmesh hη I b
  have hp : (Fintype.card S : ℝ) * a ≤ 3 / 16 := by
    rw [Fintype.card_coe]
    have hb := mul_le_mul_of_nonneg_right hcount ha
    have he : ((2 * (R : ℝ) + 1)^2 * (t * N)) * a = β * (2 * (R : ℝ) + 1)^2 * t := by
      dsimp [a]; field_simp
    rw [he] at hb
    have hbβ := mul_le_mul_of_nonneg_right hβle (show 0 ≤ (2 * (R : ℝ) + 1)^2 * t by positivity)
    nlinarith only [hb, hbβ, hsmall]
  have hY : ∀ i : S, ∃ Y : PlanarSpace, ∀ᵐ Z ∂squareLebesgue,
      greenKernel (X i) (meshChart J b Z) ≤ Real.log J - Real.log ‖Z - Y‖ + kernelConstant := by
    intro i
    have hi := (mem_sourceIndices η I (nearbyCells R b) i).mp i.property
    have hd : periodicIndexDistance (η i) b ≤ R := by
      rw [periodicIndexDistance_comm]; exact (mem_nearbyCells _ _).mp hi.2
    obtain ⟨Y, _, hY⟩ := near_chart_bounds hJ hmesh (η i) b hd (hX i hi.1)
    exact ⟨Y, hY.mono fun _ h => h.2⟩
  choose Y hY using hY
  have hm : Measurable f := (Finset.measurable_sum I fun i _ =>
    regularGreenRepresentative_measurable.comp (measurable_const.sub measurable_id)).const_mul _
  have hdom : ∀ᵐ Z ∂squareLebesgue, f (meshChart J b Z) ≤
      B + ∑ i : S, -a * Real.log ‖Z - Y i‖ := by
    have hall : ∀ᵐ Z ∂squareLebesgue, ∀ i : S,
        greenKernel (X i) (meshChart J b Z) ≤ Real.log J - Real.log ‖Z - Y i‖ + kernelConstant := by
      rw [ae_all_iff]; exact hY
    filter_upwards [hall, PoleLogMoments.ae_mem_closed_square] with Z hZ hZmem
    have hzy : meshChart J b Z ∈ closure (meshCell J hJ b) := by
      rw [MeshAdjacentCells.closure_meshCell]; exact ⟨Z, hZmem, rfl⟩
    have hfar (i : Fin N) (hi : i ∈ I) (hn : i ∉ S) :
        greenKernel (X i) (meshChart J b Z) ≤ Real.log J + kernelConstant := by
      have hnb : b ∉ nearbyCells R (η i) := by
        intro hh
        apply hn
        apply (mem_sourceIndices η I (nearbyCells R b) i).mpr
        refine ⟨hi, ?_⟩
        simpa only [mem_nearbyCells, periodicIndexDistance_comm] using hh
      have hg := (le_abs_self _).trans
        (FarReferenceResidual.green_abs_le_on_far_cells hJ hR (η i) b hnb (hX i hi) hzy)
      have hr : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR)
      rw [Real.log_div (by exact_mod_cast (show R ≠ 0 by omega))
        (by exact_mod_cast hJ.ne')] at hg
      linarith
    have hs : (∑ i ∈ I, greenKernel (X i) (meshChart J b Z)) ≤
        (I.card : ℝ) * (Real.log J + kernelConstant) +
          ∑ i : S, -Real.log ‖Z - Y i‖ := by
      have hh : (∑ i ∈ I, greenKernel (X i) (meshChart J b Z)) ≤
          ∑ i ∈ I, ((Real.log J + kernelConstant) +
            if hi : i ∈ S then -Real.log ‖Z - Y ⟨i, hi⟩‖ else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        split_ifs with hn
        · have hh := hZ ⟨i, hn⟩; dsimp only at hh; linarith
        · simpa only [add_zero] using hfar i hi hn
      refine hh.trans_eq ?_
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      congr 1
      calc
        _ = ∑ i ∈ S, (if hi : i ∈ S then -Real.log ‖Z - Y ⟨i, hi⟩‖ else 0) := by
          symm
          apply Finset.sum_subset
          · intro i hi; exact ((mem_sourceIndices η I (nearbyCells R b) i).mp hi).1
          · intro i _ hi; simp [hi]
        _ = ∑ i : S, (if hi : i.val ∈ S then -Real.log ‖Z - Y ⟨i.val, hi⟩‖ else 0) :=
          Finset.sum_subtype S (fun _ => Iff.rfl) _
        _ = _ := Finset.sum_congr rfl fun i _ => by simp [i.property]
    have hh := mul_le_mul_of_nonneg_left hs ha
    refine hh.trans_eq ?_
    dsimp [f, B, a]
    simp only [mul_add, Finset.mul_sum, mul_neg, neg_mul]
    ring
  obtain ⟨hi, hb⟩ := exponential_log_domination Y _ (hm.comp (measurable_meshChart J b)) ha hp hdom
  have hic : Integrable (fun y => Real.exp (f y)) (meshCellMeasure J hJ b) :=
    ((measurePreserving_meshChart J hJ b).integrable_comp hm.exp.aestronglyMeasurable).mp hi
  refine ⟨hic, ?_⟩
  rw [← integral_meshChart hJ b hic]
  refine hb.trans ?_
  have hcard : (I.card : ℝ) ≤ N := by
    have hh : I.card ≤ N := by simpa only [Fintype.card_fin] using Finset.card_le_univ I
    exact_mod_cast hh
  have hmulp := mul_le_mul_of_nonneg_left hcard ha
  have haN : a * N = β := by dsimp [a]; field_simp
  rw [haN] at hmulp
  have hlog : 0 ≤ Real.log (J : ℝ) + kernelConstant :=
    add_nonneg (Real.log_nonneg (by exact_mod_cast hJ)) kernelConstant_pos.le
  have hB : B ≤ β₀ * (Real.log J + kernelConstant) :=
    mul_le_mul_of_nonneg_right (hmulp.trans hβle) hlog
  rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hB) (by norm_num)

/-- Identification with the actual original Gibbs exponent. -/
theorem pairSumOn_original {N : ℕ} (β : ℝ) (X : Configuration N) :
    pairSumOn (fun _ _ x y => β / N * greenKernel x y) Finset.univ X =
      β / N * pairEnergy regularGreenRepresentative N X := by
  classical
  unfold pairSumOn pairEnergy
  have hI (i : Fin N) : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by ext j; simp
  simp_rw [hI]
  simp only [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j <;> simp [hij, greenKernel]

/-- Sequential integration for the actual original particle weight. -/
theorem original_partition_upper {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    {β β₀ t : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (_hsub : β₀ < 4)
    (ht : 0 < t) (htδ : t < occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J) (η : LabelVector J N) (hη : OccupationCap t η) :
    (labelPartitionFunction hJ η β).toReal ≤
      Real.exp ((N : ℝ) * (Real.log 5 + β₀ * (Real.log J + kernelConstant))) := by
  classical
  cases N with
  | zero => omega
  | succ n =>
    let ν : Fin (n + 1) → Measure Torus := fun i => meshCellMeasure J hJ (η i)
    let K : Fin (n + 1) → Fin (n + 1) → Torus → Torus → ℝ :=
      fun _ _ x y => β / (n + 1 : ℕ) * greenKernel x y
    let P : Fin (n + 1) → Torus → Prop := fun i x => x ∈ closure (meshCell J hJ (η i))
    have hP : ∀ i, ∀ᵐ x ∂ν i, P i x := fun i =>
      (ae_mem_meshCell J hJ (η i)).mono fun _ h => subset_closure h
    have hK : ∀ i j, Measurable (Function.uncurry (K i j)) := fun _ _ =>
      measurable_greenKernel.const_mul _
    have hsym : ∀ i j x y, K i j x y = K j i y x := by
      intro i j x y; dsimp [K]; rw [greenKernel_symm]
    have hrow (I : Finset (Fin (n + 1))) (j : Fin (n + 1)) (_hj : j ∉ I)
        (X : Configuration (n + 1)) (hX : ∀ i ∈ I, P i (X i)) :
        (∫⁻ z, ENNReal.ofReal (Real.exp (∑ i ∈ I, K i j (X i) z)) ∂ν j) ≤
          ENNReal.ofReal (Real.exp (Real.log 5 + β₀ * (Real.log J + kernelConstant))) := by
      have hh := original_section_exp_bound hJ (show 0 < n + 1 by omega)
        (radius_one_le β₀) (by omega) hβ hβle ht.le
        (microscopic_power_bound (hβ.trans hβle) ht.le htδ) η hη I (η j) X hX
      have he (z : Torus) : (∑ i ∈ I, K i j (X i) z) =
          β / (n + 1 : ℕ) * ∑ i ∈ I, greenKernel (X i) z := by
        dsimp [K]; rw [Finset.mul_sum]
      simp_rw [he]
      change (∫⁻ z, ENNReal.ofReal (Real.exp (β / (n + 1 : ℕ) *
        ∑ i ∈ I, greenKernel (X i) z)) ∂meshCellMeasure J hJ (η j)) ≤ _
      rw [← ofReal_integral_eq_lintegral_ofReal hh.1 (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
      exact ENNReal.ofReal_le_ofReal hh.2
    have hl := pair_lintegral_le ν P hP K hK hsym hrow Finset.univ
    have he (X : Configuration (n + 1)) : Real.exp (pairSumOn K Finset.univ X) =
        gibbsWeight regularGreenRepresentative (n + 1) β X := by
      rw [pairSumOn_original]; rfl
    simp only [Finset.card_univ, Fintype.card_fin] at hl
    simp_rw [he] at hl
    have hz : labelPartitionFunction hJ η β =
        ∫⁻ X, ENNReal.ofReal (gibbsWeight regularGreenRepresentative (n + 1) β X) ∂Measure.pi ν := by
      unfold labelPartitionFunction greenWeightDensity
      exact lintegral_congr_ae ((ae_regular_weight hJ η β).symm.mono fun _ h => congrArg ENNReal.ofReal h)
    rw [← hz] at hl
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hl).trans_eq
      (ENNReal.toReal_ofReal (Real.exp_pos _).le)

/-- Uniform lower integral, including all labels, not just the good set. -/
theorem original_partition_lower {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    {β β₀ : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
    (η : LabelVector J N) :
    Real.exp (-β₀ * ((N : ℝ) - 1) * greenLowerConstant / 2) ≤
      (labelPartitionFunction hJ η β).toReal := by
  have hi := (integrable_label_greenWeight hJ hN η hβ (hβle.trans_lt hsub)).congr
    (ae_regular_weight hJ η β).symm
  have hb := integral_mono (μ := labelReference hJ η) (integrable_const _) hi
    (green_uniform_lower_weight greenLowerConstant_pos.le green_lower_bound N hN hβ hβle)
  rw [integral_const, probReal_univ, one_smul] at hb
  rw [labelPartitionFunction_eq_ofReal_integral hJ hN η hβ (hβle.trans_lt hsub),
    ENNReal.toReal_ofReal (integral_nonneg fun X => (gibbsWeight_pos _ N β X).le)]
  exact hb.trans_eq (integral_congr_ae (ae_regular_weight hJ η β))

open DiscreteOccupationIdentities FibreEntropy

/-- The literal good-set mass and original partition ratios imply the bound
for every label. Only numerator labels need the good-set upper integral. -/
theorem label_log_probability_bound {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    {β β₀ t : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htδ : t < occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hmass : 1 / 2 ≤ labelCapMass (N := N) (t := t / 2) hJ β)
    (η : LabelVector J N) :
    -Real.log (labelProbability hJ η β).toReal ≤ labelConstant β₀ * N * (1 + Real.log J) := by
  let p := (labelProbability hJ η β).toReal
  let U : ℝ := N * (Real.log 5 + β₀ * (Real.log J + kernelConstant))
  let L : ℝ := -β₀ * ((N : ℝ) - 1) * greenLowerConstant / 2
  have hp : 0 < p := ENNReal.toReal_pos (labelProbability_ne_zero hJ hN η hβ (hβle.trans_lt hsub))
    (labelProbability_ne_top hJ hN η hβ (hβle.trans_lt hsub))
  have hlo : Real.exp L ≤ (labelPartitionFunction hJ η β).toReal :=
    original_partition_lower hJ hN hβ hβle hsub η
  have hr (ζ : LabelState J N (t / 2)) : labelWeight hJ β ζ ≤ Real.exp (U - L) * p := by
    have hζ : OccupationCap t ζ.val := ζ.property.mono (by linarith)
    have hu := original_partition_upper hJ hN hβ hβle hsub ht htδ hmesh ζ.val hζ
    apply (div_le_iff₀ hp).mp
    rw [show labelWeight hJ β ζ / p =
        (labelPartitionFunction hJ ζ.val β).toReal / (labelPartitionFunction hJ η β).toReal from
      LabelRatioTransport.labelProbability_ratio_eq_partition_ratio hJ hN η ζ.val hβ (hβle.trans_lt hsub)]
    calc
      _ ≤ Real.exp U / (labelPartitionFunction hJ η β).toReal :=
        div_le_div_of_nonneg_right hu ((Real.exp_pos L).le.trans hlo)
      _ ≤ Real.exp U / Real.exp L := div_le_div_of_nonneg_left (Real.exp_pos U).le (Real.exp_pos L) hlo
      _ = Real.exp (U - L) := (Real.exp_sub U L).symm
  have hcard : (Fintype.card (LabelState J N (t / 2)) : ℝ) ≤ ((J : ℝ)^2)^N := by
    have hh := Fintype.card_le_of_injective
      (fun ζ : LabelState J N (t / 2) => ζ.val) Subtype.val_injective
    have hh' : Fintype.card (LabelState J N (t / 2)) ≤ (J^2)^N := by
      simpa only [LabelVector, Fintype.card_fun, Fintype.card_fin, card_meshIndex] using hh
    exact_mod_cast hh'
  have hs : (1 / 2 : ℝ) ≤ ((J : ℝ)^2)^N * (Real.exp (U - L) * p) := by
    calc
      _ ≤ labelCapMass (N := N) (t := t / 2) hJ β := hmass
      _ ≤ ∑ _ : LabelState J N (t / 2), Real.exp (U - L) * p := Finset.sum_le_sum fun ζ _ => hr ζ
      _ = (Fintype.card (LabelState J N (t / 2)) : ℝ) * (Real.exp (U - L) * p) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (mul_nonneg (Real.exp_pos _).le hp.le)
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hproduct : 1 ≤ 2 * (((J : ℝ)^2)^N * Real.exp (U - L)) * p := by nlinarith only [hs]
  have hl := Real.log_le_log zero_lt_one hproduct
  rw [Real.log_one,
    Real.log_mul (mul_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hJr.ne')) (Real.exp_ne_zero _))) hp.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hJr.ne')) (Real.exp_ne_zero _)),
    Real.log_mul (pow_ne_zero _ (pow_ne_zero _ hJr.ne')) (Real.exp_ne_zero _),
    Real.log_exp, Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hβ₀ : 0 ≤ β₀ := hβ.trans hβle
  have hNr : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogJ : 0 ≤ Real.log (J : ℝ) := Real.log_nonneg (by exact_mod_cast hJ)
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have hfirst : -Real.log p ≤ N * (Real.log 10 + β₀ * (kernelConstant + greenLowerConstant / 2) +
      (2 + β₀) * Real.log J) := by
    have hm := mul_le_mul_of_nonneg_right hNr hlog2
    have hg := mul_nonneg hβ₀ greenLowerConstant_pos.le
    dsimp only [U, L] at hl
    rw [hlog10]
    nlinarith only [hl, hm, hg]
  refine hfirst.trans ?_
  have hA : 0 ≤ Real.log 10 + β₀ * (kernelConstant + greenLowerConstant / 2) := by
    have hc := kernelConstant_pos.le
    have hg := greenLowerConstant_pos.le
    have h10 : 0 ≤ Real.log (10 : ℝ) := Real.log_nonneg (by norm_num)
    positivity
  have hmul := mul_nonneg hA hlogJ
  have hscalar : Real.log 10 + β₀ * (kernelConstant + greenLowerConstant / 2) +
      (2 + β₀) * Real.log J ≤ labelConstant β₀ * (1 + Real.log J) := by
    unfold labelConstant
    nlinarith only [hmul, hβ₀]
  have hh := mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith only [hh]

/-- Finite entropy with original, possibly subprobability, positive weights.
No normalization and no support restriction are needed for this algebraic fact. -/
theorem finiteEntropy_le_log_weight {α : Type*} [Fintype α]
    (w F : α → ℝ) (hw : ∀ x, 0 < w x) (hF : ∀ x, 0 ≤ F x)
    {C : ℝ} (hC : ∀ x, -Real.log (w x) ≤ C) :
    finiteEntropy w F ≤ C * ∑ x, w x * F x := by
  classical
  have he (x : α) : w x * (F x * Real.log (F x)) =
      (w x * F x) * Real.log (w x * F x) + w x * F x * (-Real.log (w x)) := by
    by_cases hx : F x = 0
    · simp [hx]
    · rw [Real.log_mul (hw x).ne' hx]
      ring
  have hh := FiniteFibreEntropyBound.sum_mul_log_le (fun x => w x * F x)
    (fun x => mul_nonneg (hw x).le (hF x))
  have hb : (∑ x, w x * F x * (-Real.log (w x))) ≤ C * ∑ x, w x * F x := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => by
      have h := mul_le_mul_of_nonneg_left (hC x) (mul_nonneg (hw x).le (hF x))
      simpa only [mul_comm C] using h
  unfold finiteEntropy
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  linarith only [hh, hb]

/-- Source label entropy estimate, on the original unnormalized outer law.
The pointwise bound above in fact permits arbitrary nonnegative outer tests. -/
theorem crude_label_entropy {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    {β β₀ t : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htδ : t < occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hmass : 1 / 2 ≤ labelCapMass (N := N) (t := t / 2) hJ β)
    (Φ : LabelState J N t → ℝ) (hΦ : ∀ η, 0 ≤ Φ η) :
    finiteEntropy (labelWeight hJ β) Φ ≤
      labelConstant β₀ * N * (1 + Real.log J) * ∑ η, labelWeight hJ β η * Φ η := by
  exact finiteEntropy_le_log_weight (labelWeight hJ β) Φ
    (labelWeight_pos hJ hN hβ (hβle.trans_lt hsub)) hΦ
    (fun η => label_log_probability_bound hJ hN hβ hβle hsub ht htδ hmesh hmass η.val)

/-- The same bound for the full original finite label law, before any outer
restriction or zero extension. Its weights are the original Gibbs cell masses. -/
theorem crude_full_label_entropy {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    {β β₀ t : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htδ : t < occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hmass : 1 / 2 ≤ labelCapMass (N := N) (t := t / 2) hJ β)
    (Φ : LabelVector J N → ℝ) (hΦ : ∀ η, 0 ≤ Φ η) :
    entropy (finiteMeasure (fun η : LabelVector J N => (labelProbability hJ η β).toReal)) Φ ≤
      ((labelConstant β₀ * N * (1 + Real.log J) *
        ∑ η : LabelVector J N, (labelProbability hJ η β).toReal * Φ η : ℝ) : EReal) := by
  rw [entropy_finiteMeasure (fun η : LabelVector J N => (labelProbability hJ η β).toReal)
    Φ (fun _ => ENNReal.toReal_nonneg) hΦ]
  apply EReal.coe_le_coe_iff.mpr
  exact finiteEntropy_le_log_weight _ Φ (fun η => ENNReal.toReal_pos
    (labelProbability_ne_zero hJ hN η hβ (hβle.trans_lt hsub))
    (labelProbability_ne_top hJ hN η hβ (hβle.trans_lt hsub))) hΦ
    (label_log_probability_bound hJ hN hβ hβle hsub ht htδ hmesh hmass)

open LightRegionEntropy BoundaryEdgeSummation SmoothOccupations

/-- The conditional estimates are summed against the original label masses;
energy outside the chosen labels is retained through nonnegativity. -/
theorem crude_conditional_entropy_sum {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    {β β₀ t C₂ : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htδ : t < occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J) (hC : 0 ≤ C₂)
    (hk : GreenGradientOscillation.KernelHessianBound C₂)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (hsmall : 4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1)
    {C : ℝ≥0} {G : Configuration N → ℝ} (hG : ConfigurationEuclideanLipschitzWith C G)
    (hzero : ∀ X, t / 2 ≤ maximumOccupation N J hJ X → G X = 0) :
    (∑ η : LabelState J N t, labelWeight hJ β η * Rothaus.squareEntropy (labelGibbsMeasure hJ η.val β) G) ≤
      (2 * entropyBound β₀ / (J : ℝ)^2) *
        (∫ X, totalEnergyDensity G X ∂gibbsMeasure greenRealRepresentative N β) +
      2 * conditionalConstant β₀ t C₂ * N * (1 + Real.log J) *
        (∫ X, G X^2 ∂gibbsMeasure greenRealRepresentative N β) := by
  let : IsProbabilityMeasure (gibbsMeasure greenRealRepresentative N β) :=
    isProbabilityMeasure_greenGibbs N hN hβ (hβle.trans_lt hsub)
  let A : ℝ := 2 * entropyBound β₀ / (J : ℝ)^2
  let D : ℝ := 2 * conditionalConstant β₀ t C₂ * N * (1 + Real.log J)
  have hJ3 : 3 ≤ J := mesh_three_le hmesh
  have hm := conditionalSquare_mass (J := J) (N := N) (u := t / 2) (t := t)
    hJ3 hN hβ (hβle.trans_lt hsub) (by linarith) hG hzero
  have he (η : LabelState J N t) : Rothaus.squareEntropy (labelGibbsMeasure hJ η.val β) G ≤
      A * (∫ X, totalEnergyDensity G X ∂labelGibbsMeasure hJ η.val β) +
        D * conditionalSquare hJ β G η := by
    let : IsProbabilityMeasure (labelGibbsMeasure hJ η.val β) :=
      isProbabilityMeasure_labelGibbsMeasure hJ hN η.val hβ (hβle.trans_lt hsub)
    have hh := crude_conditional_entropy hJ hN hβ hβle hsub ht htδ hmesh hC hk hscale hsmall
      η.val η.property hG.lift.lipschitzOnWith
    rw [entropy_square_eq hG] at hh
    simpa only [A, D, conditionalSquare] using (EReal.coe_le_coe_iff.mp hh)
  have hEi : (∑ η : LabelState J N t, labelWeight hJ β η *
      ∫ X, totalEnergyDensity G X ∂labelGibbsMeasure hJ η.val β) ≤
        ∫ X, totalEnergyDensity G X ∂gibbsMeasure greenRealRepresentative N β := by
    simp_rw [labelWeight, weighted_label_integral hJ hN hβ (hβle.trans_lt hsub)]
    exact sum_label_fiber_integrals_le hJ (integrable_totalEnergyDensity hG) (totalEnergyDensity_nonneg G)
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (by norm_num)
    (ConditionalEntropyTightening.entropyBound_nonneg (hβ.trans hβle))) (sq_nonneg _)
  calc
    _ ≤ ∑ η : LabelState J N t, labelWeight hJ β η *
        (A * (∫ X, totalEnergyDensity G X ∂labelGibbsMeasure hJ η.val β) + D * conditionalSquare hJ β G η) :=
      Finset.sum_le_sum fun η _ => mul_le_mul_of_nonneg_left (he η) ENNReal.toReal_nonneg
    _ = A * (∑ η : LabelState J N t, labelWeight hJ β η *
          ∫ X, totalEnergyDensity G X ∂labelGibbsMeasure hJ η.val β) +
        D * (∑ η : LabelState J N t, labelWeight hJ β η * conditionalSquare hJ β G η) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro η _ <;> ring
    _ ≤ _ := by
      rw [hm]
      exact add_le_add (mul_le_mul_of_nonneg_left hEi hA) le_rfl

/-- Complete source crude light-region entropy at each admissible finer
resolution. Only the literal good-label mass is an additional hypothesis. -/
theorem crude_light_entropy {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    {β β₀ t C₂ : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htδ : t < occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J) (hC : 0 ≤ C₂)
    (hk : GreenGradientOscillation.KernelHessianBound C₂)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (hsmall : 4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1)
    (hmass : 1 / 2 ≤ labelCapMass (N := N) (t := t / 2) hJ β)
    {C : ℝ≥0} {G : Configuration N → ℝ} (hG : ConfigurationEuclideanLipschitzWith C G)
    (hzero : ∀ X, t / 2 ≤ maximumOccupation N J hJ X → G X = 0) :
    entropy (gibbsMeasure greenRealRepresentative N β) (fun X => G X^2) ≤
      (((2 * entropyBound β₀ / (J : ℝ)^2) *
          (∫ X, totalEnergyDensity G X ∂gibbsMeasure greenRealRepresentative N β) +
        (2 * conditionalConstant β₀ t C₂ + labelConstant β₀) * N * (1 + Real.log J) *
          (∫ X, G X^2 ∂gibbsMeasure greenRealRepresentative N β) : ℝ) : EReal) := by
  have hJ3 : 3 ≤ J := mesh_three_le hmesh
  have hm := conditionalSquare_mass (J := J) (N := N) (u := t / 2) (t := t)
    hJ3 hN hβ (hβle.trans_lt hsub) (by linarith) hG hzero
  have hl := crude_label_entropy hJ hN hβ hβle hsub ht htδ hmesh hmass
    (conditionalSquare hJ β G) (conditionalSquare_nonneg hJ β G)
  rw [hm] at hl
  have hc := crude_conditional_entropy_sum hJ hN hβ hβle hsub ht htδ hmesh hC hk hscale hsmall hG hzero
  rw [LightRegionEntropy.actual_entropy_chain (J := J) (N := N) (t := t) (u := t / 2)
    hJ3 hN hβ (hβle.trans_lt hsub) (by linarith) hG hzero]
  apply EReal.coe_le_coe_iff.mpr
  exact (add_le_add hc hl).trans_eq (by ring)

/-- The promised mass gate is independent of the finer resolution J.
These are literally the source cutoff levels t/4 and t/2. -/
theorem good_label_mass_uniform {J N : ℕ} {β β₀ t : ℝ}
    (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htδ : t < occupationBound β₀)
    (hresolution : HeavyScales.sourceResolution β₀ (t / 4) ≤ J)
    (hlarge : OccupationMassCutoff.halfMassThreshold β₀ (t / 4) (t / 2) ≤ N) :
    1 / 2 ≤ labelCapMass (N := N) (t := t / 2) (SeparatedRadius.source_mesh_pos hresolution) β := by
  have hδ := (chosen_parameters β₀ (hβ.trans hβle)).2.1
  exact OccupationMassCutoff.good_label_mass_ge_half (hβ.trans hβle) hsub
    (by linarith) (by linarith) (by linarith) hresolution hlarge hβ hβle

/-- All three source estimates' hypotheses are primitive at this endpoint;
the good-label mass is derived, not supplied. No far-imbalance input is used. -/
theorem crude_light_entropy_uniform {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    {β β₀ t C₂ : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htδ : t < occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J) (hC : 0 ≤ C₂)
    (hk : GreenGradientOscillation.KernelHessianBound C₂)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (hsmall : 4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1)
    (hresolution : HeavyScales.sourceResolution β₀ (t / 4) ≤ J)
    (hlarge : OccupationMassCutoff.halfMassThreshold β₀ (t / 4) (t / 2) ≤ N)
    {C : ℝ≥0} {G : Configuration N → ℝ} (hG : ConfigurationEuclideanLipschitzWith C G)
    (hzero : ∀ X, t / 2 ≤ maximumOccupation N J hJ X → G X = 0) :
    entropy (gibbsMeasure greenRealRepresentative N β) (fun X => G X^2) ≤
      (((2 * entropyBound β₀ / (J : ℝ)^2) *
          (∫ X, totalEnergyDensity G X ∂gibbsMeasure greenRealRepresentative N β) +
        (2 * conditionalConstant β₀ t C₂ + labelConstant β₀) * N * (1 + Real.log J) *
          (∫ X, G X^2 ∂gibbsMeasure greenRealRepresentative N β) : ℝ) : EReal) := by
  exact crude_light_entropy hJ hN hβ hβle hsub ht htδ hmesh hC hk hscale hsmall
    (good_label_mass_uniform hβ hβle hsub ht htδ hresolution hlarge) hG hzero

/-- At beta zero the literal interaction correction vanishes identically. -/
theorem correctionDefect_zero {J N : ℕ} (μ : MeshIndex J → Measure Torus)
    [∀ a, IsProbabilityMeasure (μ a)] (η : LabelVector J N) :
    correctionDefect μ η 0 = 0 := by
  simp [correctionDefect, referenceNormalizer, referenceTilt]

end PeriodicAttractiveLogGas.CrudeEntropyIntegrated
