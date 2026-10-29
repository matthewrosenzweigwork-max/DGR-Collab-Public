import LeanResearch.PeriodicAttractiveLogGas.SourceConditionalEntropyEnergy
import LeanResearch.PeriodicAttractiveLogGas.Rothaus
import LeanResearch.PeriodicAttractiveLogGas.ConditionalVarianceAssembly

/-! The centering and Rothaus tightening step of source lines 2702–2717.
The reusable estimate explicitly takes the defective inequality as an interface;
that interface alone is not asserted to complete the source conditional LSI. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.ConditionalEntropyTightening

open MeshCells LabelOccupations GreenPointWeights MovingPoleNumerators
open ConditionalSourceCharts MovingPoleCharts ConditionalLawEstimates CellRestrictions
open SourceConditionalEntropyEnergy ConditionalVarianceAssembly

/-- The source test has a bounded measurable class for the actual restricted
law, even when it has no regularity outside the closed physical rectangle. -/
theorem local_test_integrable_bounded {J N : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (hN : 2 ≤ N) (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {f : Configuration N → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell))) :
    Integrable f (labelGibbsMeasure hJ η β) ∧
      ∃ M : ℝ, ∀ᵐ X ∂labelGibbsMeasure hJ η β, |f X| ≤ M := by
  let : IsProbabilityMeasure (labelGibbsMeasure hJ η β) :=
    isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ hsub
  obtain ⟨g, _, hfg⟩ := (physicalLipschitz_of_chart hJ hJ3 η hf).exists_extension
    (closed_product_patches_nonempty hJ η (fun _ => TorusPatchDensity.Shape.cell))
  have he : f =ᵐ[labelGibbsMeasure hJ η β] g :=
    (SourceEntropyTests.ae_closedRectangle_labelGibbs hJ η β).mono fun X hX =>
      hfg (fun i _ => (SourceEntropyTests.mem_closedRectangle hJ η X).mp hX i)
  have hi : Integrable (fun X => g X) (labelGibbsMeasure hJ η β) :=
    Integrable.of_bound g.continuous.aestronglyMeasurable ‖g‖
      (Eventually.of_forall g.norm_coe_le_norm)
  refine ⟨hi.congr he.symm, ‖g‖, he.mono fun X hX => ?_⟩
  rw [hX, ← Real.norm_eq_abs]
  exact g.norm_coe_le_norm X

/-- The ordinary mean, the centered square entropy, and Rothaus all concern
the original local test, without a global boundedness hypothesis. -/
theorem local_rothaus {J N : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (hN : 2 ≤ N) (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {f : Configuration N → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell))) :
    entropy (labelGibbsMeasure hJ η β) (fun X => f X ^ 2) ≤
      entropy (labelGibbsMeasure hJ η β)
        (fun X => (f X - ∫ Y, f Y ∂labelGibbsMeasure hJ η β) ^ 2) +
      ((2 * ∫ X, (f X - ∫ Y, f Y ∂labelGibbsMeasure hJ η β) ^ 2
        ∂labelGibbsMeasure hJ η β : ℝ) : EReal) := by
  let : IsProbabilityMeasure (labelGibbsMeasure hJ η β) :=
    isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ hsub
  have hi := local_test_integrable_bounded hJ hJ3 hN η hβ hsub hf
  exact rothaus_centering_ae hi.1.aestronglyMeasurable.aemeasurable hi.2

/-- The actual fine Poincare theorem in the source's physical chart class. -/
theorem local_poincare {J n : ℕ} (hJ : 0 < J) (hN : 2 ≤ n + 1)
    (η : LabelVector J (n + 1)) {β β₀ t : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hsub : β₀ < 4) (ht : t ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J) (hη : OccupationCap t η)
    {f : Configuration (n + 1) → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell))) :
    (∫ X, (f X - ∫ Y, f Y ∂labelGibbsMeasure hJ η β) ^ 2
      ∂labelGibbsMeasure hJ η β) ≤ (finePoincareConstant β₀ / (J : ℝ) ^ 2) *
      ∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂labelGibbsMeasure hJ η β := by
  have hJ3 : 3 ≤ J := by omega
  have htpos : 0 < t := by
    have hh := one_le_cap_mass (show 0 < n + 1 by omega) hη
    have hn : (0 : ℝ) ≤ n + 1 := by positivity
    by_contra h
    have hh' := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hn
    norm_cast at hh
    nlinarith
  have hp := DeletedConditionalPoincare.labelGibbs_poincare hN hβ hβ₀ hsub htpos ht hmesh η hη
    (physicalLipschitz_of_chart hJ hJ3 η hf)
  have hi := (local_test_integrable_bounded hJ hJ3 hN η hβ (hβ₀.trans_lt hsub) hf).1
  rw [ProbabilityTheory.variance_eq_integral hi.aestronglyMeasurable.aemeasurable] at hp
  exact hp

/-- Subtracting any real constant preserves the literal physical local class. -/
theorem local_sub_const {J N : ℕ} (η : LabelVector J N)
    {f : Configuration N → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    (a : ℝ) :
    LipschitzOnWith C (fun Z => f (sources Z) - a) (closedChart J η (fun _ => Patch.cell)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro Z hZ W hW
  simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using hf.dist_le_mul Z hZ W hW

/-- Constant subtraction preserves even the totalized ordinary gradient. -/
theorem coordinateGradient_sub_const {N : ℕ} (f : Configuration N → ℝ) (a : ℝ)
    (i : Fin N) (X : Configuration N) :
    coordinateOrdinaryGradient (fun Y => f Y - a) i X = coordinateOrdinaryGradient f i X := by
  unfold coordinateOrdinaryGradient torusOrdinaryGradient rectangleOrdinaryGradient
  rw [fderiv_sub_const]

theorem energy_sub_const {N : ℕ} (f : Configuration N → ℝ) (a : ℝ) :
    BoundaryEdgeSummation.totalEnergyDensity (fun X => f X - a) =
      BoundaryEdgeSummation.totalEnergyDensity f := by
  funext X
  apply Finset.sum_congr rfl
  intro i _
  simp only [BoundaryEdgeSummation.coordinateEnergy, coordinateGradient_sub_const]

/-- Finite-real entropy representation for the original local test. -/
theorem local_entropy_eq {J N : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (hN : 2 ≤ N) (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {f : Configuration N → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell))) :
    entropy (labelGibbsMeasure hJ η β) (fun X => f X ^ 2) =
      (Rothaus.squareEntropy (labelGibbsMeasure hJ η β) f : EReal) := by
  let : IsProbabilityMeasure (labelGibbsMeasure hJ η β) :=
    isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ hsub
  exact entropy_eq_integral (Eventually.of_forall fun _ => sq_nonneg _)
    (SourceEntropyTests.source_square_integrable hJ hJ3 hN η hβ hsub hf).2

/-- Reusable source tightening step. The defective inequality remains an
explicit interface until the actual source reduction is instantiated. Fine
Poincare, centering, AE entropy representation and gradient invariance are
proved here from the original physical local test hypotheses. -/
theorem tighten_of_defective {J n : ℕ} (hJ : 0 < J) (hN : 2 ≤ n + 1)
    (η : LabelVector J (n + 1)) {β β₀ t D : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hsub : β₀ < 4) (ht : t ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J) (hη : OccupationCap t η) (hD : 0 ≤ D)
    (hdefective : ∀ (g : Configuration (n + 1) → ℝ) (K : ℝ≥0),
      LipschitzOnWith K (fun Z => g (sources Z)) (closedChart J η (fun _ => Patch.cell)) →
      entropy (labelGibbsMeasure hJ η β) (fun X => g X ^ 2) ≤
        (((2 * entropyBound β₀ / (J : ℝ) ^ 2) *
          (∫ X, BoundaryEdgeSummation.totalEnergyDensity g X ∂labelGibbsMeasure hJ η β) +
          2 * D * (∫ X, g X ^ 2 ∂labelGibbsMeasure hJ η β) : ℝ) : EReal))
    {f : Configuration (n + 1) → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell))) :
    entropy (labelGibbsMeasure hJ η β) (fun X => f X ^ 2) ≤
      ((((2 * entropyBound β₀ + (2 * D + 2) * finePoincareConstant β₀) / (J : ℝ) ^ 2) *
        ∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂labelGibbsMeasure hJ η β : ℝ) : EReal) := by
  have hJ3 : 3 ≤ J := by omega
  have hsubβ : β < 4 := hβ₀.trans_lt hsub
  let P := labelGibbsMeasure hJ η β
  let a := ∫ X, f X ∂P
  let g := fun X => f X - a
  have hg : LipschitzOnWith C (fun Z => g (sources Z)) (closedChart J η (fun _ => Patch.cell)) :=
    local_sub_const η hf a
  have he := energy_sub_const f a
  have hrep := local_entropy_eq hJ hJ3 hN η hβ hsubβ hf
  have hrep' := local_entropy_eq hJ hJ3 hN η hβ hsubβ hg
  have hr := local_rothaus hJ hJ3 hN η hβ hsubβ hf
  change entropy P (fun X => f X ^ 2) ≤ entropy P (fun X => g X ^ 2) +
    ((2 * ∫ X, g X ^ 2 ∂P : ℝ) : EReal) at hr
  rw [hrep, hrep', ← EReal.coe_add] at hr
  have hr' : Rothaus.squareEntropy P f ≤ Rothaus.squareEntropy P g + 2 * ∫ X, g X ^ 2 ∂P := by
    exact_mod_cast hr
  have hd := hdefective g C hg
  rw [hrep'] at hd
  change (Rothaus.squareEntropy P g : EReal) ≤
    (((2 * entropyBound β₀ / (J : ℝ) ^ 2) *
      (∫ X, BoundaryEdgeSummation.totalEnergyDensity g X ∂P) +
      2 * D * (∫ X, g X ^ 2 ∂P) : ℝ) : EReal) at hd
  have hd' : Rothaus.squareEntropy P g ≤ (2 * entropyBound β₀ / (J : ℝ) ^ 2) *
      (∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂P) + 2 * D * ∫ X, g X ^ 2 ∂P := by
    rw [he] at hd
    exact_mod_cast hd
  have hv := local_poincare hJ hN η hβ hβ₀ hsub ht hmesh hη hf
  change (∫ X, g X ^ 2 ∂P) ≤ (finePoincareConstant β₀ / (J : ℝ) ^ 2) *
    ∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂P at hv
  have hv' := mul_le_mul_of_nonneg_left hv (show 0 ≤ 2 * D + 2 by linarith)
  rw [hrep]
  apply EReal.coe_le_coe_iff.mpr
  calc
    Rothaus.squareEntropy P f ≤ (2 * entropyBound β₀ / (J : ℝ) ^ 2) *
        (∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂P) +
        (2 * D + 2) * ∫ X, g X ^ 2 ∂P := by linarith
    _ ≤ (2 * entropyBound β₀ / (J : ℝ) ^ 2) *
        (∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂P) +
        (2 * D + 2) * ((finePoincareConstant β₀ / (J : ℝ) ^ 2) *
          ∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂P) := add_le_add le_rfl hv'
    _ = _ := by ring

/-- A uniform explicit bound for the affine logarithmic coefficient. -/
theorem affine_log_div_sq_bound (a b : ℝ) {J : ℕ} (hJ : 0 < J) :
    |(a * Real.log (J : ℝ) + b) / (J : ℝ) ^ 2| ≤
      (|a| + |b|) * ((1 + Real.log (J : ℝ)) / (J : ℝ) ^ 2) := by
  have hj : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hl := Real.log_nonneg hj
  rw [abs_div, abs_of_nonneg (sq_nonneg (J : ℝ))]
  calc
    _ ≤ (|a| * Real.log (J : ℝ) + |b|) / (J : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      simpa only [abs_mul, abs_of_nonneg hl] using abs_add_le (a * Real.log (J : ℝ)) b
    _ ≤ ((|a| + |b|) * (1 + Real.log (J : ℝ))) / (J : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith [abs_nonneg a, abs_nonneg b]
    _ = _ := by ring

/-- The source coefficient is affine in log J before division by J squared.
Only the already-defined source constants occur; D_J is expanded literally. -/
theorem source_coefficient_affine (β₀ C₂ : ℝ) (J : ℕ) :
    (2 * entropyBound β₀ + (2 * (3 * β₀ * ReferenceSelfTerms.selfBound J +
      Real.log (ResidualExponential.sharpConstant β₀ C₂)) + 2) * finePoincareConstant β₀) /
        (J : ℝ) ^ 2 =
    ((6 * β₀ * Real.exp 1 * finePoincareConstant β₀) * Real.log (J : ℝ) +
      (2 * entropyBound β₀ + (6 * β₀ * (Real.exp 1 *
        (kernelConstant + Real.pi / 2) + MovingPoleCalculus.greenLowerConstant) +
        2 * Real.log (ResidualExponential.sharpConstant β₀ C₂) + 2) * finePoincareConstant β₀)) /
          (J : ℝ) ^ 2 := by
  unfold ReferenceSelfTerms.selfBound
  ring

/-- The explicit source constants give a bound uniform in every positive
resolution. It therefore also holds on any admissible subsequence. -/
theorem source_coefficient_growth (β₀ C₂ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ J : ℕ, 0 < J →
      |(2 * entropyBound β₀ + (2 * (3 * β₀ * ReferenceSelfTerms.selfBound J +
        Real.log (ResidualExponential.sharpConstant β₀ C₂)) + 2) * finePoincareConstant β₀) /
          (J : ℝ) ^ 2| ≤ B * ((1 + Real.log (J : ℝ)) / (J : ℝ) ^ 2) := by
  let a := 6 * β₀ * Real.exp 1 * finePoincareConstant β₀
  let b := 2 * entropyBound β₀ + (6 * β₀ * (Real.exp 1 *
    (kernelConstant + Real.pi / 2) + MovingPoleCalculus.greenLowerConstant) +
    2 * Real.log (ResidualExponential.sharpConstant β₀ C₂) + 2) * finePoincareConstant β₀
  refine ⟨|a| + |b|, add_nonneg (abs_nonneg _) (abs_nonneg _), ?_⟩
  intro J hJ
  rw [source_coefficient_affine]
  exact affine_log_div_sq_bound a b hJ

/-- The actual asymptotic statement for the exact source coefficient; the
implicit bound depends only on beta0 and the fixed Hessian constant. -/
theorem source_coefficient_isBigO (β₀ C₂ : ℝ) :
    (fun J : ℕ => (2 * entropyBound β₀ + (2 * (3 * β₀ * ReferenceSelfTerms.selfBound J +
      Real.log (ResidualExponential.sharpConstant β₀ C₂)) + 2) * finePoincareConstant β₀) /
        (J : ℝ) ^ 2) =O[atTop] (fun J : ℕ => (1 + Real.log (J : ℝ)) / (J : ℝ) ^ 2) := by
  obtain ⟨B, _, hB⟩ := source_coefficient_growth β₀ C₂
  apply Asymptotics.IsBigO.of_bound B
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with J hJ
  have hj : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hb : 0 ≤ (1 + Real.log (J : ℝ)) / (J : ℝ) ^ 2 :=
    div_nonneg (by linarith [Real.log_nonneg hj]) (sq_nonneg _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb] using hB J (by omega)

/-- The actual source lower-density and density-norm constants are on the
correct sides of one; the logarithmic coefficient therefore has its true sign. -/
theorem source_density_constants_bounds {D ω C₀ : ℝ}
    (hD : 1 ≤ D) (hω : 0 ≤ ω) (hC : 0 ≤ C₀) :
    PointWeightDensity.sourceLowerConstant D ω C₀ ≤ 1 ∧
      1 ≤ PointWeightDensity.sourceNormConstant D ω C₀ := by
  have he : Real.exp (-2 * ω - C₀ / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hr : D ^ (-(1 / 4 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hD (by norm_num)
  have hm : Real.exp (-2 * ω - C₀ / 2) * D ^ (-(1 / 4 : ℝ)) ≤ 1 := by
    simpa only [one_mul] using mul_le_mul he hr (Real.rpow_nonneg (by linarith) _) zero_le_one
  constructor
  · unfold PointWeightDensity.sourceLowerConstant
    apply (div_le_iff₀ (show 0 < 1 + 8 * Real.pi / 7 by positivity)).mpr
    have hπ := Real.pi_pos
    nlinarith
  · unfold PointWeightDensity.sourceNormConstant
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (Real.one_le_exp_iff.mpr (by linarith))
        (Real.one_le_rpow hD (by norm_num)))
      (Real.one_le_rpow (by linarith [Real.pi_pos]) (by norm_num))

theorem source_density_parameter_bounds {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    lowerBound β₀ ≤ 1 ∧ 1 ≤ densityNormBound β₀ := by
  apply source_density_constants_bounds
  · exact ConditionalParameters.distanceBound_one_le
      (ConditionalParameters.nearRadius_one_le β₀ kernelConstant)
  · exact ConditionalParameters.oscillationBound_nonneg hβ₀ kernelConstant_pos.le _
  · exact kernelConstant_pos.le

/-- Nonnegativity of the exact source entropy energy coefficient, including
its logarithmic density factor; no replacement by an absolute value. -/
theorem entropyBound_nonneg {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) : 0 ≤ entropyBound β₀ := by
  have hb := source_density_parameter_bounds hβ₀
  have hc := lowerBound_pos β₀
  have hK := densityNormBound_pos β₀
  have hlog : 0 ≤ 5 + 2 * Real.log (densityNormBound β₀ * lowerBound β₀ ^ (-(3 / 2 : ℝ))) := by
    convert (DensityMoments.logarithmic_coefficient_nonneg hc hb.1 hb.2).2.2 using 1; norm_num
  have hp : 0 ≤ DensityEntropy.poincareConstant squareSobolevConstant
      (lowerBound β₀) 4 (densityNormBound β₀) := by
    unfold DensityEntropy.poincareConstant
    positivity
  have hs : 0 ≤ DensityEntropy.logSobolevConstant squareSobolevConstant
      (lowerBound β₀) 4 (densityNormBound β₀) := by
    unfold DensityEntropy.logSobolevConstant
    exact add_nonneg (by positivity) (mul_nonneg hlog hp)
  exact hs.trans (le_max_left _ _)

/-- The actual sharp exponential constant is at least one, including beta0=0. -/
theorem sharpConstant_one_le {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (C₂ : ℝ) :
    1 ≤ ResidualExponential.sharpConstant β₀ C₂ := by
  have hs : (1 : ℝ) ≤ Real.sqrt (5 / 3) := by
    nlinarith [Real.sqrt_nonneg (5 / 3), Real.sq_sqrt (show (0 : ℝ) ≤ 5 / 3 by norm_num)]
  have hC := ResidualNearExponential.universalConstant_pos.le
  have hL := ReferenceResidual.nearScale_nonneg (ResidualFarExponential.chosenRadius β₀ C₂)
  unfold ResidualExponential.sharpConstant
  exact one_le_mul_of_one_le_of_one_le hs (Real.one_le_exp_iff.mpr (by positivity))

/-- Nonnegativity of the literal source D_J; its named definition belongs to
the root's reduction module, avoiding a circular import or duplicate constant. -/
theorem source_defect_nonneg {J : ℕ} (hJ : 0 < J) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (C₂ : ℝ) :
    0 ≤ 3 * β₀ * ReferenceSelfTerms.selfBound J +
      Real.log (ResidualExponential.sharpConstant β₀ C₂) :=
  add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hβ₀) (ReferenceSelfTerms.selfBound_nonneg hJ))
    (Real.log_nonneg (sharpConstant_one_le hβ₀ C₂))

theorem source_tightening_coefficient_nonneg {J : ℕ} (hJ : 0 < J)
    {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (C₂ : ℝ) :
    0 ≤ (2 * entropyBound β₀ + (2 * (3 * β₀ * ReferenceSelfTerms.selfBound J +
      Real.log (ResidualExponential.sharpConstant β₀ C₂)) + 2) * finePoincareConstant β₀) /
        (J : ℝ) ^ 2 := by
  have hL := entropyBound_nonneg hβ₀
  have hD := source_defect_nonneg hJ hβ₀ C₂
  have hA := finePoincareConstant_nonneg β₀
  positivity

end PeriodicAttractiveLogGas.ConditionalEntropyTightening
