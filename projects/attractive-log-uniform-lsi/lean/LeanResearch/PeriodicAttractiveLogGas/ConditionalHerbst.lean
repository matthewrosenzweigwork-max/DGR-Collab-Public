import LeanResearch.PeriodicAttractiveLogGas.ConditionalLogSobolev
import LeanResearch.PeriodicAttractiveLogGas.HerbstEntropy

/-! The actual conditional-LSI application in source lines 2889--2902.
The exponential test stays in the original prescribed closed physical chart.
Its full physical derivative and unscaled energy are derived below; neither
the entropy control nor an exponential energy rule is a final hypothesis.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.ConditionalHerbst

open MeshCells LabelOccupations CellRestrictions ConditionalLawEstimates
  MovingPoleNumerators MovingPoleCharts SourceConditionalEntropyEnergy
  ConditionalEntropyTightening GreenPointWeights

/-- Compact boundedness makes the literal exponential a Lipschitz test on
the same set, without imposing any regularity outside that set. -/
theorem local_exp_lipschitz {E : Type*} [PseudoMetricSpace E]
    {S : Set E} (hS : IsCompact S) {F : E → ℝ} {C : ℝ≥0}
    (hF : LipschitzOnWith C F S) (a : ℝ) :
    ∃ D : ℝ≥0, LipschitzOnWith D (fun x => Real.exp (a * F x)) S := by
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hF.continuousOn
  let D : ℝ≥0 := ⟨Real.exp (|a| * M) * |a| * C, by positivity⟩
  refine ⟨D, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have ha (z : E) (hz : z ∈ S) : a * F z ≤ |a| * M := by
    calc
      _ ≤ |a * F z| := le_abs_self _
      _ = |a| * ‖F z‖ := by rw [abs_mul, Real.norm_eq_abs]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hM z hz) (abs_nonneg a)
  change |Real.exp (a * F x) - Real.exp (a * F y)| ≤
    (Real.exp (|a| * M) * |a| * (C : ℝ)) * dist x y
  calc
    _ ≤ Real.exp (|a| * M) * |a * F x - a * F y| :=
      ReferenceMapCompactness.abs_exp_sub_le (ha x hx) (ha y hy)
    _ = Real.exp (|a| * M) * (|a| * |F x - F y|) := by rw [← mul_sub, abs_mul]
    _ ≤ Real.exp (|a| * M) * (|a| * ((C : ℝ) * dist x y)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left (hF.dist_le_mul x hx y hy) (abs_nonneg a)
    _ = _ := by ring

theorem source_exp_lipschitz {J N : ℕ} (η : LabelVector J N)
    {F : Configuration N → ℝ} {C : ℝ≥0}
    (hF : LipschitzOnWith C (fun Z => F (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    (a : ℝ) :
    ∃ D : ℝ≥0, LipschitzOnWith D (fun Z => Real.exp (a * F (sources Z)))
      (closedChart J η (fun _ => Patch.cell)) :=
  local_exp_lipschitz (isCompact_closedChart J η (fun _ => Patch.cell)) hF a

/-- The actual full Riesz chain rule, at an ordinary physical lift point. -/
theorem hasFDerivAt_exp_lift {N : ℕ} {F : Configuration N → ℝ}
    {y G : Gradient N}
    (hF : HasFDerivAt (fun w => F (configurationQuotient N w)) (innerSL ℝ G) y)
    (a : ℝ) :
    HasFDerivAt (fun w => Real.exp (a * F (configurationQuotient N w)))
      (innerSL ℝ ((a * Real.exp (a * F (configurationQuotient N y))) • G)) y := by
  convert! (hF.const_mul a).exp using 1
  ext v
  simp only [innerSL_apply_apply, inner_smul_left, conj_trivial, smul_apply, smul_eq_mul]
  ring

theorem exp_scalar_sq (a r : ℝ) :
    (a * Real.exp (a * r)) ^ 2 = a ^ 2 * Real.exp ((2 * a) * r) := by
  rw [mul_pow, pow_two (Real.exp (a * r)), ← Real.exp_add]
  congr 2
  ring

/-- The same extension supplies a measurable physical gradient field for F,
and the displayed scalar multiple is the actual exponential derivative.
The final equality uses exactly the unscaled sum of particle energies. -/
theorem source_exp_gradient_energy {J N : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (η : LabelVector J N) (β : ℝ) {F : Configuration N → ℝ} {C : ℝ≥0}
    (hF : LipschitzOnWith C (fun Z => F (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    (a : ℝ) :
    ∃ g : C(Configuration N, ℝ), ConfigurationEuclideanLipschitzWith C g ∧
      EqOn F g (Set.pi univ fun i => closure (meshCell J hJ (η i))) ∧
      ∀ᵐ X ∂labelGibbsMeasure hJ η β,
        (∀ y : Gradient N, configurationQuotient N y = X →
          HasFDerivAt (fun w => Real.exp (a * F (configurationQuotient N w)))
            (innerSL ℝ ((a * Real.exp (a * F X)) • descendedLiftGradient g X)) y) ∧
        BoundaryEdgeSummation.totalEnergyDensity (fun Y => Real.exp (a * F Y)) X =
          a ^ 2 * Real.exp ((2 * a) * F X) * BoundaryEdgeSummation.totalEnergyDensity F X := by
  obtain ⟨g, hg, hFg, hd⟩ := source_full_gradient_identification hJ hJ3 η β hF
  refine ⟨g, hg, hFg, hd.mono ?_⟩
  intro X hX
  have he (y : Gradient N) (hy : configurationQuotient N y = X) :
      HasFDerivAt (fun w => Real.exp (a * F (configurationQuotient N w)))
        (innerSL ℝ ((a * Real.exp (a * F X)) • descendedLiftGradient g X)) y := by
    simpa only [hy] using hasFDerivAt_exp_lift (hX.1 y hy) a
  refine ⟨he, ?_⟩
  have hn := energy_eq_norm_of_hasFDerivAt (f := fun Y => Real.exp (a * F Y))
    (he (configurationCenteredLift X) (configurationQuotient_centeredLift X))
  simp only [configurationQuotient_centeredLift] at hn
  rw [hn, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, exp_scalar_sq, hX.2]

theorem source_exp_energy_ae {J N : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (η : LabelVector J N) (β : ℝ) {F : Configuration N → ℝ} {C : ℝ≥0}
    (hF : LipschitzOnWith C (fun Z => F (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    (a : ℝ) :
    (fun X => BoundaryEdgeSummation.totalEnergyDensity (fun Y => Real.exp (a * F Y)) X) =ᵐ[
      labelGibbsMeasure hJ η β]
      (fun X => a ^ 2 * Real.exp ((2 * a) * F X) * BoundaryEdgeSummation.totalEnergyDensity F X) := by
  obtain ⟨_, _, _, hh⟩ := source_exp_gradient_energy hJ hJ3 η β hF a
  exact hh.mono fun _ hx => hx.2

/-- Every energy integral in the LSI application is a true finite integral.
This is proved from the admissible exponential test, before using its bound. -/
theorem source_exp_energy_integrable {J N : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (hN : 2 ≤ N) (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {F : Configuration N → ℝ} {C : ℝ≥0}
    (hF : LipschitzOnWith C (fun Z => F (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    (a : ℝ) :
    Integrable (BoundaryEdgeSummation.totalEnergyDensity (fun X => Real.exp (a * F X)))
      (labelGibbsMeasure hJ η β) := by
  obtain ⟨D, hD⟩ := source_exp_lipschitz η hF a
  exact source_full_energy_integrable hJ hJ3 hN η hβ hsub hD

/-- Moment finiteness follows from the original local test class, including
for centered moments. The original observable need not be globally regular. -/
theorem source_exp_integrable {J N : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (hN : 2 ≤ N) (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {F : Configuration N → ℝ} {C : ℝ≥0}
    (hF : LipschitzOnWith C (fun Z => F (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    (s : ℝ) :
    Integrable F (labelGibbsMeasure hJ η β) ∧
      Integrable (fun X => Real.exp (s * F X)) (labelGibbsMeasure hJ η β) ∧
      Integrable (fun X => Real.exp (s * (F X - ∫ Y, F Y ∂labelGibbsMeasure hJ η β)))
        (labelGibbsMeasure hJ η β) := by
  let : IsProbabilityMeasure (labelGibbsMeasure hJ η β) :=
    isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ hsub
  obtain ⟨hi, M, hb⟩ := local_test_integrable_bounded hJ hJ3 hN η hβ hsub hF
  exact ⟨hi, HerbstEntropy.integrable_exp_mul hi.aestronglyMeasurable.aemeasurable hb s,
    HerbstEntropy.integrable_centered_exp hi.aestronglyMeasurable.aemeasurable hb s⟩

/-- The exact AE exponential energy formula gives the integrated bound from
the literal physical gradient hypothesis, with no particle normalization. -/
theorem source_exp_energy_le {J N : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (hN : 2 ≤ N) (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {F : Configuration N → ℝ} {C : ℝ≥0}
    (hF : LipschitzOnWith C (fun Z => F (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    {L : ℝ} (hgrad : ∀ᵐ X ∂labelGibbsMeasure hJ η β,
      BoundaryEdgeSummation.totalEnergyDensity F X ≤ L ^ 2) (a : ℝ) :
    (∫ X, BoundaryEdgeSummation.totalEnergyDensity (fun Y => Real.exp (a * F Y)) X
      ∂labelGibbsMeasure hJ η β) ≤
      (a ^ 2 * L ^ 2) * HerbstEntropy.moment (labelGibbsMeasure hJ η β) F (2 * a) := by
  let P := labelGibbsMeasure hJ η β
  have hiE : Integrable
      (BoundaryEdgeSummation.totalEnergyDensity (fun Y => Real.exp (a * F Y))) P :=
    source_exp_energy_integrable hJ hJ3 hN η hβ hsub hF a
  have hiR : Integrable (fun X => (a ^ 2 * L ^ 2) * Real.exp ((2 * a) * F X)) P :=
    ((source_exp_integrable hJ hJ3 hN η hβ hsub hF (2 * a)).2.1).const_mul _
  calc
    _ ≤ ∫ X, (a ^ 2 * L ^ 2) * Real.exp ((2 * a) * F X) ∂P := by
      apply integral_mono_ae hiE hiR
      filter_upwards [source_exp_energy_ae hJ hJ3 η β hF a, hgrad] with X he hg
      rw [he]
      calc
        _ ≤ a ^ 2 * Real.exp ((2 * a) * F X) * L ^ 2 :=
          mul_le_mul_of_nonneg_left hg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

open GreenGradientOscillation ResidualFarExponential ResidualNearExponential ReferenceResidual

section Source

variable {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
  {β β₀ t C₂ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
  (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
  (hmesh : 8 * (radius β₀ + 4) ≤ J) (hmeshY : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
  (ht : 0 < t) (htC : t ≤ occupationBound β₀)
  (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
    nearScale (chosenRadius β₀ C₂) * t ≤ 1)
  (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
  (hsmall : 4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1)
  (η : LabelVector J N) (hη : OccupationCap t η)

include hN hβ hβ₀ hsub hC hk hmesh hmeshY ht htC hcap hscale hsmall hη

/-- The scalar Herbst entropy premise is discharged by the actual conditional
LSI and the proved physical chain rule, with its exact coefficient. -/
theorem source_entropy_control {F : Configuration N → ℝ} {C : ℝ≥0}
    (hF : LipschitzOnWith C (fun Z => F (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    {L : ℝ} (hgrad : ∀ᵐ X ∂labelGibbsMeasure hJ η β,
      BoundaryEdgeSummation.totalEnergyDensity F X ≤ L ^ 2) (s : ℝ) :
    entropy (labelGibbsMeasure hJ η β) (fun X => Real.exp (s * F X)) ≤
      (((ConditionalLogSobolev.coefficient J β₀ C₂ * L ^ 2 / 4) * s ^ 2 *
        HerbstEntropy.moment (labelGibbsMeasure hJ η β) F s : ℝ) : EReal) := by
  have hJ3 : 3 ≤ J := mesh_three_le hmesh
  obtain ⟨D, hD⟩ := source_exp_lipschitz η hF (s / 2)
  have hlsi := ConditionalLogSobolev.conditional_lsi hJ hN hβ hβ₀ hsub hC hk
    hmesh hmeshY ht htC hcap hscale hsmall η hη (f := fun X => Real.exp ((s / 2) * F X)) hD
  have heq : (fun X => Real.exp ((s / 2) * F X) ^ 2) =
      fun X => Real.exp (s * F X) := by
    funext X
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hlsi
  have hE := source_exp_energy_le hJ hJ3 hN η hβ (hβ₀.trans_lt hsub) hF hgrad (s / 2)
  rw [show 2 * (s / 2) = s by ring] at hE
  have hK := ConditionalLogSobolev.coefficient_nonneg hJ (hβ.trans hβ₀) C₂
  refine hlsi.trans (EReal.coe_le_coe_iff.mpr ?_)
  calc
    _ ≤ ConditionalLogSobolev.coefficient J β₀ C₂ *
        (((s / 2) ^ 2 * L ^ 2) * HerbstEntropy.moment (labelGibbsMeasure hJ η β) F s) :=
      mul_le_mul_of_nonneg_left hE hK
    _ = _ := by ring

/-- Source Herbst concentration under the original prescribed Gibbs law.
All moments are genuine finite integrals by `source_exp_integrable`.
The bound applies to every real parameter, including zero and negative ones. -/
theorem conditional_centered_exp_le {F : Configuration N → ℝ} {C : ℝ≥0}
    (hF : LipschitzOnWith C (fun Z => F (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    {L : ℝ} (hgrad : ∀ᵐ X ∂labelGibbsMeasure hJ η β,
      BoundaryEdgeSummation.totalEnergyDensity F X ≤ L ^ 2) (s : ℝ) :
    (∫ X, Real.exp (s * (F X - ∫ Y, F Y ∂labelGibbsMeasure hJ η β))
      ∂labelGibbsMeasure hJ η β) ≤
      Real.exp ((ConditionalLogSobolev.coefficient J β₀ C₂ * L ^ 2 / 4) * s ^ 2) := by
  have hJ3 : 3 ≤ J := mesh_three_le hmesh
  let : IsProbabilityMeasure (labelGibbsMeasure hJ η β) :=
    isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ (hβ₀.trans_lt hsub)
  obtain ⟨hi, M, hb⟩ := local_test_integrable_bounded hJ hJ3 hN η hβ (hβ₀.trans_lt hsub) hF
  exact HerbstEntropy.centered_exp_le_of_entropy_control hi.aestronglyMeasurable.aemeasurable hb
    (source_entropy_control hJ hN hβ hβ₀ hsub hC hk hmesh hmeshY ht htC hcap
      hscale hsmall η hη hF hgrad) s

/-- Equivalent squared-gradient form, convenient when the source gives the
energy bound directly rather than naming its square root. -/
theorem conditional_centered_exp_le_of_energy_le {F : Configuration N → ℝ} {C : ℝ≥0}
    (hF : LipschitzOnWith C (fun Z => F (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    {B : ℝ} (hB : 0 ≤ B) (hgrad : ∀ᵐ X ∂labelGibbsMeasure hJ η β,
      BoundaryEdgeSummation.totalEnergyDensity F X ≤ B) (s : ℝ) :
    (∫ X, Real.exp (s * (F X - ∫ Y, F Y ∂labelGibbsMeasure hJ η β))
      ∂labelGibbsMeasure hJ η β) ≤
      Real.exp ((ConditionalLogSobolev.coefficient J β₀ C₂ * B / 4) * s ^ 2) := by
  have hg : ∀ᵐ X ∂labelGibbsMeasure hJ η β,
      BoundaryEdgeSummation.totalEnergyDensity F X ≤ (Real.sqrt B) ^ 2 := by
    simpa only [Real.sq_sqrt hB] using hgrad
  simpa only [Real.sq_sqrt hB] using conditional_centered_exp_le hJ hN hβ hβ₀ hsub hC hk
    hmesh hmeshY ht htC hcap hscale hsmall η hη hF hg s

end Source

end PeriodicAttractiveLogGas.ConditionalHerbst
