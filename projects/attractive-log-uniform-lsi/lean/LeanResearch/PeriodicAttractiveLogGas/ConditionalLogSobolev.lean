import LeanResearch.PeriodicAttractiveLogGas.ConditionalEntropyReduction
import LeanResearch.PeriodicAttractiveLogGas.ConditionalEntropyTightening
import LeanResearch.PeriodicAttractiveLogGas.ConditionalEntropyParameters
import LeanResearch.PeriodicAttractiveLogGas.SourceConditionalEntropyComparison

/-! Assembly for the source prescribed-cell logarithmic Sobolev inequality.
The square representative is used only for entropy and measure changes;
the energy remains the gradient of the original physical local test. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators

namespace PeriodicAttractiveLogGas.ConditionalLogSobolev

open MeshCells LabelOccupations CellRestrictions ConditionalLawEstimates
  SourceEntropyTests ConditionalEntropyDisintegration ReferenceDensityChange
  ReferenceSelfTerms MovingPoleNumerators MovingPoleCharts GreenPointWeights
  OneCoordinateConditionals SourceConditionalEntropyEnergy

/-- The actual bounded square representative gives the original test's
entropy, with precisely the original second moment as the prefactor. -/
theorem square_extension_entropy {J N : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (hN : 2 ≤ N) (η : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {f : Configuration N → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell))) :
    let P := labelGibbsMeasure hJ η β
    let F := squareExtension η (fun Z => f (sources Z))
    (∫ X, F X ∂P) = ∫ X, f X ^ 2 ∂P ∧
    entropy P (fun X => f X ^ 2) =
      (((∫ X, f X ^ 2 ∂P) *
        ∫ X, Real.log (F X / ∫ Y, f Y ^ 2 ∂P) ∂normalizedTilt P F : ℝ) : EReal) := by
  let P := labelGibbsMeasure hJ η β
  let F := squareExtension η (fun Z => f (sources Z))
  let : IsProbabilityMeasure P := isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ hsub
  have he : F =ᵐ[P] fun X => f X ^ 2 := ae_squareExtension_labelGibbs hJ hJ3 η β f
  have hm := integral_congr_ae he
  obtain ⟨K, hb⟩ := squareExtension_bounds η hf.continuousOn
  have hh := (entropy_normalizedTilt (P := P)
    (measurable_squareExtension hJ3 η hf.continuousOn) (Eventually.of_forall hb)).2
  rw [entropy_congr_ae he, hm] at hh
  exact ⟨hm, hh⟩

section Reference
variable {J n : ℕ} (hJ : 0 < J)
  (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
  (η : LabelVector J (n + 1)) {β β₀ t : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
  (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
    ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
  (hmesh : 8 * (radius β₀ + 4) ≤ J) (ht : t ≤ occupationBound β₀)
  (hη : OccupationCap t η)

include hβ hβ₀ hformula hmesh ht hη

/-- The bounded square representative's actual conditional log entropies
are bounded by the energy of the original physical test, without differentiating
the zero extension used to obtain global measurability. -/
theorem square_extension_entropy_energy (hN : 2 ≤ n + 1) (hsub : β₀ < 4)
    {f : Configuration (n + 1) → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell)))
    (hS : 0 < ∫ X, f X ^ 2 ∂labelGibbsMeasure hJ η β) :
    let P := labelGibbsMeasure hJ η β
    let F := squareExtension η (fun Z => f (sources Z))
    let κ := fun i => PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
    (∫ X, f X ^ 2 ∂P) *
      (∑ i, ∫ X, conditionalLogEntropy (κ i) (F ∘ (configurationSplit i).symm)
        (removeSite i X) ∂normalizedTilt P F) ≤
      (entropyBound β₀ / (J : ℝ) ^ 2) *
        ∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂P := by
  have hJ3 : 3 ≤ J := mesh_three_le hmesh
  let P := labelGibbsMeasure hJ η β
  let F := squareExtension η (fun Z => f (sources Z))
  let κ := fun i => PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
    (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i
  have hm : Measurable F := measurable_squareExtension hJ3 η hf.continuousOn
  obtain ⟨K, hb⟩ := squareExtension_bounds η hf.continuousOn
  have he : F =ᵐ[P] fun X => f X ^ 2 := ae_squareExtension_labelGibbs hJ hJ3 η β f
  have hmass := integral_congr_ae he
  have hi := source_sum_entropy_disintegration hJ hN μ η hβ (hβ₀.trans_lt hsub) hformula
    hm hb (hmass.symm ▸ hS)
  have hval (i : Fin (n + 1)) :
      (fun X => conditionalEntropyValue (κ i) (fun p => F (insertSite i p.2 p.1))
        (removeSite i X)) =ᵐ[P]
      (fun X => conditionalEntropyValue (κ i) (fun p => f (insertSite i p.2 p.1) ^ 2)
        (removeSite i X)) := by
    have hs := ae_of_ae_map (measurable_removeSite i).aemeasurable
      (ae_squareExtension_conditional hJ hJ3 μ η hformula hN hβ (hβ₀.trans_lt hsub) f i)
    exact hs.mono fun X hX => conditionalEntropyValue_congr_ae (κ i) (removeSite i X) hX
  change (∫ X, F X ∂P) *
    (∑ i, ∫ X, conditionalLogEntropy (κ i) (F ∘ (configurationSplit i).symm)
      (removeSite i X) ∂normalizedTilt P F) = _ at hi
  rw [hmass] at hi
  calc
    _ = _ := hi
    _ = ∑ i, ∫ X, conditionalEntropyValue (κ i) (fun p => f (insertSite i p.2 p.1) ^ 2)
        (removeSite i X) ∂P := Finset.sum_congr rfl fun i _ => integral_congr_ae (hval i)
    _ ≤ _ := (source_entropy_sum_energy hJ μ η hβ hβ₀ hformula hmesh ht hη hN hsub hf).2.2

end Reference

open ConditionalEntropyReduction ConditionalEntropyTightening
  GreenGradientOscillation ResidualFarExponential ResidualNearExponential ReferenceResidual

/-- The literal coefficient of source eq:conditional-full-LSI. -/
def coefficient (J : ℕ) (β₀ C₂ : ℝ) : ℝ :=
  (2 * entropyBound β₀ + (2 * defectConstant J β₀ C₂ + 2) *
    ConditionalVarianceAssembly.finePoincareConstant β₀) / (J : ℝ) ^ 2

section Source
variable {J n : ℕ} (hJ : 0 < J) (hN : 2 ≤ n + 1)
  {β β₀ t C₂ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
  (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
  (hmesh : 8 * (radius β₀ + 4) ≤ J) (hmeshY : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
  (ht : 0 < t) (htC : t ≤ occupationBound β₀)
  (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
    nearScale (chosenRadius β₀ C₂) * t ≤ 1)
  (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
  (η : LabelVector J (n + 1)) (hη : OccupationCap t η)
  (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
    ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
  (hdensity : ∀ a, ∀ᵐ z ∂meshCellMeasure J hJ a,
    Real.exp (-1) ≤ Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ∧
    Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ≤ Real.exp 1)

include hN hβ hβ₀ hsub hC hk hmesh hmeshY ht htC hcap hη hformula hdensity

/-- The actual defective source inequality: the conditional entropy reduction
is proved and instantiated, not supplied as a theorem hypothesis. -/
theorem source_defective {f : Configuration (n + 1) → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell))) :
    entropy (labelGibbsMeasure hJ η β) (fun X => f X ^ 2) ≤
      (((2 * entropyBound β₀ / (J : ℝ) ^ 2) *
        (∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂labelGibbsMeasure hJ η β) +
        2 * defectConstant J β₀ C₂ * (∫ X, f X ^ 2 ∂labelGibbsMeasure hJ η β) : ℝ) : EReal) := by
  have hJ3 : 3 ≤ J := mesh_three_le hmesh
  have hsubβ := hβ₀.trans_lt hsub
  have hS0 : 0 ≤ ∫ X, f X ^ 2 ∂labelGibbsMeasure hJ η β :=
    integral_nonneg fun _ => sq_nonneg _
  by_cases hS : ∫ X, f X ^ 2 ∂labelGibbsMeasure hJ η β = 0
  · rw [(source_zero_mass hJ hJ3 hN η hβ hsubβ hf hS).1, hS, mul_zero, add_zero]
    have hE : 0 ≤ ∫ X, BoundaryEdgeSummation.totalEnergyDensity f X
        ∂labelGibbsMeasure hJ η β := integral_nonneg (BoundaryEdgeSummation.totalEnergyDensity_nonneg f)
    have hL := entropyBound_nonneg (hβ.trans hβ₀)
    exact_mod_cast (show 0 ≤ (2 * entropyBound β₀ / (J : ℝ) ^ 2) *
      (∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂labelGibbsMeasure hJ η β) by positivity)
  · have hSpos := lt_of_le_of_ne hS0 (Ne.symm hS)
    let P := labelGibbsMeasure hJ η β
    let F := squareExtension η (fun Z => f (sources Z))
    have hm : Measurable F := measurable_squareExtension hJ3 η hf.continuousOn
    obtain ⟨K, hb⟩ := squareExtension_bounds η hf.continuousOn
    have he := square_extension_entropy hJ hJ3 hN η hβ hsubβ hf
    have hr := SourceConditionalEntropyComparison.source_normalized_tilt_reduction
      hJ hN hβ hβ₀ hsub hC hk hmeshY μ η ht.le hη hcap hformula hdensity hmesh htC
      hm hb (he.1.symm ▸ hSpos)
    have hE := square_extension_entropy_energy hJ μ η hβ hβ₀ hformula hmesh htC hη hN hsub hf hSpos
    rw [he.1] at hr
    have hr' := mul_le_mul_of_nonneg_left hr hS0
    rw [he.2]
    apply EReal.coe_le_coe_iff.mpr
    have hfinal := hr'.trans hE
    dsimp only [P, F] at hfinal
    simp only [div_eq_mul_inv] at hfinal ⊢
    nlinarith only [hfinal]

end Source

/-- The supplied conditional LSI, with the reference family constructed by
the already-proved Schauder argument. No reference or defective estimate is
an assumption of this theorem. -/
theorem conditional_lsi_succ {J n : ℕ} (hJ : 0 < J) (hN : 2 ≤ n + 1)
    {β β₀ t C₂ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (hmesh : 8 * (radius β₀ + 4) ≤ J) (hmeshY : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
      nearScale (chosenRadius β₀ C₂) * t ≤ 1)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (hsmall : 4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1)
    (η : LabelVector J (n + 1)) (hη : OccupationCap t η)
    {f : Configuration (n + 1) → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell))) :
    entropy (labelGibbsMeasure hJ η β) (fun X => f X ^ 2) ≤
      ((coefficient J β₀ C₂ *
        ∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂labelGibbsMeasure hJ η β : ℝ) : EReal) := by
  obtain ⟨μ, ρ, hμ, _, _, _, _, _, _, hformula, hdensity, _⟩ :=
    ReferenceFamilyExistence.exists_sourceReferenceFamily (hJ := hJ) hN ht hβ hβ₀ hη hscale hsmall
  let : ∀ a, IsProbabilityMeasure (μ a) := hμ
  apply tighten_of_defective hJ hN η hβ hβ₀ hsub htC hmesh hη
    (source_defect_nonneg hJ (hβ.trans hβ₀) C₂) _ hf
  intro g K hg
  exact source_defective hJ hN hβ hβ₀ hsub hC hk hmesh hmeshY ht htC hcap
    μ η hη hformula hdensity hg

/-- Source thm:conditional-entropy for every original particle number N≥2,
including both inverse-temperature endpoints and every permitted label. -/
theorem conditional_lsi {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    {β β₀ t C₂ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (hmesh : 8 * (radius β₀ + 4) ≤ J) (hmeshY : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
      nearScale (chosenRadius β₀ C₂) * t ≤ 1)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (hsmall : 4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1)
    (η : LabelVector J N) (hη : OccupationCap t η)
    {f : Configuration N → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell))) :
    entropy (labelGibbsMeasure hJ η β) (fun X => f X ^ 2) ≤
      ((coefficient J β₀ C₂ *
        ∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂labelGibbsMeasure hJ η β : ℝ) : EReal) := by
  cases N with
  | zero => omega
  | succ n =>
    exact conditional_lsi_succ hJ hN hβ hβ₀ hsub hC hk hmesh hmeshY
      ht htC hcap hscale hsmall η hη hf

theorem coefficient_nonneg {J : ℕ} (hJ : 0 < J) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (C₂ : ℝ) :
    0 ≤ coefficient J β₀ C₂ := source_tightening_coefficient_nonneg hJ hβ₀ C₂

/-- The exact source coefficient, uniformly before restricting to admissible
resolutions. The bound has no dependence on N, labels, or beta in its range. -/
theorem coefficient_isBigO (β₀ C₂ : ℝ) :
    (fun J : ℕ => coefficient J β₀ C₂) =O[atTop]
      (fun J : ℕ => (1 + Real.log (J : ℝ)) / (J : ℝ) ^ 2) :=
  source_coefficient_isBigO β₀ C₂

/-- The numerical conditions can be fixed before the particle number and
inverse temperature. The Hessian constant is supplied by the proved original
Green-kernel bound, rather than a remaining analytic assumption. -/
theorem exists_uniform_conditional_lsi {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ KernelHessianBound C₂ ∧ ∃ t : ℝ, ∃ J₀ : ℕ,
      0 < t ∧ t < occupationBound β₀ ∧
      ∀ J : ℕ, J₀ ≤ J → ∀ hJ : 0 < J, ∀ N : ℕ, 2 ≤ N →
        ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → ∀ η : LabelVector J N, OccupationCap t η →
          ∀ (f : Configuration N → ℝ) (C : ℝ≥0),
            LipschitzOnWith C (fun Z => f (sources Z)) (closedChart J η (fun _ => Patch.cell)) →
            entropy (labelGibbsMeasure hJ η β) (fun X => f X ^ 2) ≤
              ((coefficient J β₀ C₂ *
                ∫ X, BoundaryEdgeSummation.totalEnergyDensity f X ∂labelGibbsMeasure hJ η β : ℝ) : EReal) := by
  obtain ⟨C₂, hC, hk⟩ := exists_kernelHessianBound
  obtain ⟨t, J₀, ht, htC, hsmall, hcap, hJ₀⟩ :=
    ConditionalEntropyParameters.exists_uniform_parameters hβ₀ C₂
  refine ⟨C₂, hC, hk, t, J₀, ht, htC, ?_⟩
  intro J hJ₀J hJ N hN β hβ hβle η hη f C hf
  obtain ⟨hm, hmY, hs⟩ := hJ₀ J hJ₀J
  exact conditional_lsi hJ hN hβ hβle hsub hC.le hk hm hmY ht htC.le
    hcap hs hsmall η hη hf

end PeriodicAttractiveLogGas.ConditionalLogSobolev
