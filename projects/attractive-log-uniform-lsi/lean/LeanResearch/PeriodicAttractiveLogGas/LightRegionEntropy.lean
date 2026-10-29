import LeanResearch.PeriodicAttractiveLogGas.FullLabelEntropy
import LeanResearch.PeriodicAttractiveLogGas.EntropyBoundaryComparison

/-! The source light-region entropy assembly (3106--3140), retaining the
original unnormalized label weights and the explicit far-imbalance input. -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

namespace PeriodicAttractiveLogGas.LightRegionEntropy

open MeshCells LabelOccupations CellRestrictions DiscreteOccupationIdentities
  SmoothOccupations BoundaryEdgeSummation EntropyBoundarySummation

variable {J N : ℕ} {β u t : ℝ}

/-- The half-open label fibres, rather than their closures, give the literal
support implication. Boundary points are assigned to their original label. -/
theorem zero_on_bad_label (hJ : 3 ≤ J) (hN : 0 < N)
    {G : Configuration N → ℝ}
    (hG : ∀ X, u ≤ maximumOccupation N J (by omega) X → G X = 0)
    (η : LabelVector J N) (hη : ¬ OccupationCap u η)
    {X : Configuration N} (hX : X ∈ labelFiber (by omega) η) : G X = 0 := by
  have he : configurationMeshLabel N J (by omega) X = η := by
    simpa only [labelFiber_eq_label_preimage, mem_preimage, mem_singleton_iff] using hX
  apply hG X
  exact (bad_labels_subset_maximum_gt N J hN hJ u (by
    change ¬ OccupationCap u (configurationMeshLabel N J (by omega) X)
    rwa [he])).le

theorem ae_labelFiber (hJ : 0 < J) (η : LabelVector J N) (β : ℝ) :
    ∀ᵐ X ∂labelGibbsMeasure hJ η β, X ∈ labelFiber hJ η := by
  apply Measure.ae_smul_measure
  apply (withDensity_absolutelyContinuous _ _).ae_le
  rw [labelReference_eq]
  apply Measure.ae_smul_measure
  exact ae_restrict_mem (measurableSet_labelFiber hJ η)

theorem square_mean_bad_label (hJ : 3 ≤ J) (hN : 0 < N)
    {G : Configuration N → ℝ}
    (hG : ∀ X, u ≤ maximumOccupation N J (by omega) X → G X = 0)
    (η : LabelVector J N) (hη : ¬ OccupationCap u η) :
    (∫ X, G X ^ 2 ∂labelGibbsMeasure (by omega) η β) = 0 := by
  have hz : (fun X => G X ^ 2) =ᵐ[labelGibbsMeasure (by omega) η β] fun _ => 0 := by
    filter_upwards [ae_labelFiber (by omega) η β] with X hX
    rw [zero_on_bad_label hJ hN hG η hη hX, zero_pow (by norm_num)]
  rw [integral_congr_ae hz, integral_zero]

theorem square_entropy_bad_label (hJ : 3 ≤ J) (hN : 0 < N)
    {G : Configuration N → ℝ}
    (hG : ∀ X, u ≤ maximumOccupation N J (by omega) X → G X = 0)
    (η : LabelVector J N) (hη : ¬ OccupationCap u η) :
    Rothaus.squareEntropy (labelGibbsMeasure (by omega) η β) G = 0 := by
  have hz : (fun X => G X ^ 2 * Real.log (G X ^ 2))
      =ᵐ[labelGibbsMeasure (by omega) η β] fun _ => 0 := by
    filter_upwards [ae_labelFiber (by omega) η β] with X hX
    rw [zero_on_bad_label hJ hN hG η hη hX]
    simp
  simp only [Rothaus.squareEntropy, integral_congr_ae hz, integral_zero,
    square_mean_bad_label hJ hN hG η hη, zero_mul, sub_self]

theorem weighted_label_integral (hJ : 0 < J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (η : LabelVector J N)
    (F : Configuration N → ℝ) :
    (labelProbability hJ η β).toReal * (∫ X, F X ∂labelGibbsMeasure hJ η β) =
      ∫ X in labelFiber hJ η, F X ∂gibbsMeasure greenRealRepresentative N β := by
  rw [labelGibbsMeasure_eq_cond hJ hN η hβ hsub, ProbabilityTheory.cond,
    integral_smul_measure]
  change (labelProbability hJ η β).toReal *
    (((labelProbability hJ η β)⁻¹).toReal * _) = _
  rw [ENNReal.toReal_inv, ← mul_assoc, mul_inv_cancel₀]
  · simp
  · exact (ENNReal.toReal_pos (labelProbability_ne_zero hJ hN η hβ hsub)
      (labelProbability_ne_top hJ hN η hβ hsub)).ne'

/-- Exact weighted disintegration over the outer labels for any integrable
observable which vanishes off those labels. The outer law is not normalized. -/
theorem sum_label_integrals (hJ : 0 < J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) {F : Configuration N → ℝ}
    (hF : Integrable F (gibbsMeasure greenRealRepresentative N β))
    (hzero : ∀ X, ¬ OccupationCap t (configurationMeshLabel N J hJ X) → F X = 0) :
    (∑ η : LabelState J N t, labelWeight hJ β η *
      ∫ X, F X ∂labelGibbsMeasure hJ η.val β) =
      ∫ X, F X ∂gibbsMeasure greenRealRepresentative N β := by
  classical
  simp_rw [labelWeight, weighted_label_integral hJ hN hβ hsub]
  rw [← integral_iUnion_fintype (fun η : LabelState J N t => measurableSet_labelFiber hJ η.val)
    (fun η ζ h => disjoint_labelFiber hJ (fun he => h (Subtype.ext he)))
    (fun _ => hF.integrableOn)]
  rw [← integral_indicator (MeasurableSet.iUnion fun η : LabelState J N t => measurableSet_labelFiber hJ η.val)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro X
  by_cases hx : X ∈ ⋃ η : LabelState J N t, labelFiber hJ η.val
  · simp only [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    symm
    apply hzero X
    intro hc
    apply hx
    refine mem_iUnion.mpr ⟨⟨configurationMeshLabel N J hJ X, hc⟩, ?_⟩
    simp only [labelFiber_eq_label_preimage, mem_preimage, mem_singleton_iff]

/-- The literal conditional square, indexed by the original outer labels. -/
def conditionalSquare (hJ : 0 < J) (β : ℝ) (G : Configuration N → ℝ)
    (η : LabelState J N t) : ℝ := ∫ X, G X ^ 2 ∂labelGibbsMeasure hJ η.val β

theorem conditionalSquare_nonneg (hJ : 0 < J) (β : ℝ) (G : Configuration N → ℝ)
    (η : LabelState J N t) : 0 ≤ conditionalSquare hJ β G η :=
  integral_nonneg fun X => sq_nonneg (G X)

theorem square_zero_outside_outer (hJ : 3 ≤ J) (hN : 0 < N) (hut : u ≤ t)
    {G : Configuration N → ℝ}
    (hzero : ∀ X, u ≤ maximumOccupation N J (by omega) X → G X = 0)
    (X : Configuration N) (hX : ¬ OccupationCap t (configurationMeshLabel N J (by omega) X)) :
    G X = 0 := by
  have hu : ¬ OccupationCap u (configurationMeshLabel N J (by omega) X) := by
    intro h
    apply hX
    exact fun a => (h a).trans (mul_le_mul_of_nonneg_right hut (Nat.cast_nonneg N))
  exact zero_on_bad_label hJ hN hzero _ hu (by
    simp only [labelFiber_eq_label_preimage, mem_preimage, mem_singleton_iff])

theorem integrable_square_log {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    {C : ℝ≥0} {G : Configuration N → ℝ} (hG : ConfigurationEuclideanLipschitzWith C G) :
    Integrable (fun X => G X ^ 2 * Real.log (G X ^ 2)) μ := by
  have hc : Continuous (fun X => G X ^ 2 * Real.log (G X ^ 2)) :=
    Real.continuous_mul_log.comp (hG.continuous.pow 2)
  exact (ContinuousMap.memLp (μ := μ) (p := 1) ℝ ⟨_, hc⟩).integrable le_rfl

theorem entropy_square_eq {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    {C : ℝ≥0} {G : Configuration N → ℝ} (hG : ConfigurationEuclideanLipschitzWith C G) :
    entropy μ (fun X => G X ^ 2) = (Rothaus.squareEntropy μ G : EReal) :=
  entropy_eq_integral (Eventually.of_forall fun X => sq_nonneg (G X))
    (integrable_square_log hG)

theorem conditionalSquare_mass (hJ : 3 ≤ J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (hut : u ≤ t)
    {C : ℝ≥0} {G : Configuration N → ℝ} (hG : ConfigurationEuclideanLipschitzWith C G)
    (hzero : ∀ X, u ≤ maximumOccupation N J (by omega) X → G X = 0) :
    (∑ η : LabelState J N t, labelWeight (by omega) β η * conditionalSquare (by omega) β G η) =
      ∫ X, G X ^ 2 ∂gibbsMeasure greenRealRepresentative N β := by
  apply sum_label_integrals (by omega) hN hβ hsub (integrable_square hG)
  intro X hX
  rw [square_zero_outside_outer hJ (by omega) hut hzero X hX]
  norm_num

/-- The exact entropy chain uses the original subprobability label weights;
all omitted conditional squares and logarithmic terms are zero. -/
theorem square_entropy_chain (hJ : 3 ≤ J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (hut : u ≤ t)
    {C : ℝ≥0} {G : Configuration N → ℝ} (hG : ConfigurationEuclideanLipschitzWith C G)
    (hzero : ∀ X, u ≤ maximumOccupation N J (by omega) X → G X = 0) :
    Rothaus.squareEntropy (gibbsMeasure greenRealRepresentative N β) G =
      (∑ η : LabelState J N t, labelWeight (by omega) β η *
        Rothaus.squareEntropy (labelGibbsMeasure (by omega) η.val β) G) +
      FibreEntropy.finiteEntropy (labelWeight (J := J) (N := N) (t := t) (by omega) β) (conditionalSquare (by omega) β G) := by
  have hm := conditionalSquare_mass hJ hN hβ hsub hut hG hzero
  have hl := sum_label_integrals (J := J) (N := N) (t := t) (by omega) hN hβ hsub (integrable_square_log hG)
    (fun X hX => by rw [square_zero_outside_outer hJ (by omega) hut hzero X hX]; simp)
  unfold Rothaus.squareEntropy FibreEntropy.finiteEntropy
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp only [conditionalSquare] at hm ⊢
  rw [hl, hm]
  ring

/-- Extended entropy version of the actual Gibbs finite partition chain. -/
theorem actual_entropy_chain (hJ : 3 ≤ J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (hut : u ≤ t)
    {C : ℝ≥0} {G : Configuration N → ℝ} (hG : ConfigurationEuclideanLipschitzWith C G)
    (hzero : ∀ X, u ≤ maximumOccupation N J (by omega) X → G X = 0) :
    entropy (gibbsMeasure greenRealRepresentative N β) (fun X => G X ^ 2) =
      ((∑ η : LabelState J N t, labelWeight (by omega) β η *
        Rothaus.squareEntropy (labelGibbsMeasure (by omega) η.val β) G) +
      FibreEntropy.finiteEntropy (labelWeight (J := J) (N := N) (t := t) (by omega) β) (conditionalSquare (by omega) β G) : ℝ) := by
  rw [entropy_square_eq hG, square_entropy_chain hJ hN hβ hsub hut hG hzero]

open ConditionalLawEstimates GreenGradientOscillation ResidualFarExponential
  ResidualNearExponential ReferenceResidual

section Conditional

variable {β₀ C₂ : ℝ}
  (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
  (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
  (hmesh : 8 * (radius β₀ + 4) ≤ J)
  (hmeshY : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
  (ht : 0 < t) (htC : t ≤ occupationBound β₀)
  (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
    nearScale (chosenRadius β₀ C₂) * t ≤ 1)
  (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
  (hsmall : 4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1)

include hβ hβ₀ hsub hC hk hmeshY ht htC hcap hscale hsmall

/-- Every outer conditional law satisfies the proved physical LSI. Summing
its genuine nonnegative energy restrictions loses no extra factor. -/
theorem conditional_entropy_sum (hN : 2 ≤ N)
    {C : ℝ≥0} {G : Configuration N → ℝ} (hG : ConfigurationEuclideanLipschitzWith C G) :
    (∑ η : LabelState J N t, labelWeight (mesh_pos hmesh) β η *
      Rothaus.squareEntropy (labelGibbsMeasure (mesh_pos hmesh) η.val β) G) ≤
      ConditionalLogSobolev.coefficient J β₀ C₂ *
        ∫ X, totalEnergyDensity G X ∂gibbsMeasure greenRealRepresentative N β := by
  have he (η : LabelState J N t) :
      Rothaus.squareEntropy (labelGibbsMeasure (mesh_pos hmesh) η.val β) G ≤
        ConditionalLogSobolev.coefficient J β₀ C₂ *
          ∫ X, totalEnergyDensity G X ∂labelGibbsMeasure (mesh_pos hmesh) η.val β := by
    let : IsProbabilityMeasure (labelGibbsMeasure (mesh_pos hmesh) η.val β) :=
      isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η.val hβ (hβ₀.trans_lt hsub)
    have hh := ConditionalLogSobolev.conditional_lsi (mesh_pos hmesh) hN
      hβ hβ₀ hsub hC hk hmesh hmeshY ht htC hcap hscale hsmall η.val η.property
      hG.lift.lipschitzOnWith
    rw [entropy_square_eq hG] at hh
    exact_mod_cast hh
  calc
    _ ≤ ∑ η : LabelState J N t, labelWeight (mesh_pos hmesh) β η *
        (ConditionalLogSobolev.coefficient J β₀ C₂ *
          ∫ X, totalEnergyDensity G X ∂labelGibbsMeasure (mesh_pos hmesh) η.val β) :=
      Finset.sum_le_sum fun η _ => mul_le_mul_of_nonneg_left (he η) ENNReal.toReal_nonneg
    _ = ConditionalLogSobolev.coefficient J β₀ C₂ *
        ∑ η : LabelState J N t, ∫ X in labelFiber (mesh_pos hmesh) η.val,
          totalEnergyDensity G X ∂gibbsMeasure greenRealRepresentative N β := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro η _
      rw [show labelWeight (mesh_pos hmesh) β η *
          (ConditionalLogSobolev.coefficient J β₀ C₂ *
            ∫ X, totalEnergyDensity G X ∂labelGibbsMeasure (mesh_pos hmesh) η.val β) =
          ConditionalLogSobolev.coefficient J β₀ C₂ *
            ((labelProbability (mesh_pos hmesh) η.val β).toReal *
              ∫ X, totalEnergyDensity G X ∂labelGibbsMeasure (mesh_pos hmesh) η.val β) by
        unfold labelWeight; ring]
      rw [weighted_label_integral (mesh_pos hmesh) hN hβ (hβ₀.trans_lt hsub)]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_label_fiber_integrals_le (mesh_pos hmesh) (integrable_totalEnergyDensity hG)
        (totalEnergyDensity_nonneg G))
      (ConditionalLogSobolev.coefficient_nonneg (mesh_pos hmesh) (hβ.trans hβ₀) C₂)

end Conditional

/-- Nonnegativity is derived for the actual full-label energy coefficient,
so the boundary comparison may be multiplied by that coefficient. -/
theorem full_label_coefficient_nonneg {β₀ cFar : ℝ} (hJ : 0 < J)
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (hcFar : 0 < cFar) (u : ℝ) :
    0 ≤ FullLabelEntropy.entropyConstant J β₀ u cFar := by
  have hocc := (OccupationCriterion.constants_nonneg (u := u) hJ hβ₀ hsub hcFar).1
  have hk := CellNormalizerBounds.kappaConstant_pos β₀ MovingPoleCalculus.greenLowerConstant
    kernelConstant hJ (lt_of_lt_of_le Nat.zero_lt_one (radius_one_le β₀))
  have hf : 0 ≤ FullLabelEntropy.fibreConstant J β₀ := by
    unfold FullLabelEntropy.fibreConstant
    exact div_nonneg (by positivity) hk.le
  have hl : 0 ≤ Real.log (J : ℝ) := Real.log_nonneg (by exact_mod_cast hJ)
  unfold FullLabelEntropy.entropyConstant
  exact add_nonneg (add_nonneg hocc (mul_nonneg (FullLabelEntropy.tau_nonneg hJ) hf))
    (div_nonneg (mul_nonneg (by norm_num) hl)
      (FullLabelEntropy.sparseCoefficient_pos hJ hsub hcFar).le)

/-- The literal extended conditional entropy also vanishes on every bad
inner label; no regularity assumption is needed for this support fact. -/
theorem actual_entropy_bad_label (hJ : 3 ≤ J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) {G : Configuration N → ℝ}
    (hzero : ∀ X, u ≤ maximumOccupation N J (by omega) X → G X = 0)
    (η : LabelVector J N) (hη : ¬ OccupationCap u η) :
    entropy (labelGibbsMeasure (by omega) η β) (fun X => G X ^ 2) = 0 := by
  let : IsProbabilityMeasure (labelGibbsMeasure (by omega) η β) :=
    isProbabilityMeasure_labelGibbsMeasure (by omega) hN η hβ hsub
  have hz : (fun X => G X ^ 2) =ᵐ[labelGibbsMeasure (by omega) η β] fun _ => 0 := by
    filter_upwards [ae_labelFiber (by omega) η β] with X hX
    rw [zero_on_bad_label hJ (by omega) hzero η hη hX]
    norm_num
  rw [entropy_congr_ae hz, entropy_zero]

/-- Source eq:particle-label-entropy with genuine extended entropies on
both sides, including the unnormalized finite outer measure. -/
theorem original_label_entropy_chain (hJ : 3 ≤ J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (hut : u ≤ t)
    {C : ℝ≥0} {G : Configuration N → ℝ} (hG : ConfigurationEuclideanLipschitzWith C G)
    (hzero : ∀ X, u ≤ maximumOccupation N J (by omega) X → G X = 0) :
    entropy (gibbsMeasure greenRealRepresentative N β) (fun X => G X ^ 2) =
      (∑ η : LabelState J N t, (labelWeight (by omega) β η : EReal) *
        entropy (labelGibbsMeasure (by omega) η.val β) (fun X => G X ^ 2)) +
      entropy (FibreEntropy.finiteMeasure (labelWeight (J := J) (N := N) (t := t) (by omega) β))
        (conditionalSquare (by omega) β G) := by
  classical
  have he (η : LabelState J N t) :
      entropy (labelGibbsMeasure (by omega) η.val β) (fun X => G X ^ 2) =
        (Rothaus.squareEntropy (labelGibbsMeasure (by omega) η.val β) G : EReal) := by
    let : IsProbabilityMeasure (labelGibbsMeasure (by omega) η.val β) :=
      isProbabilityMeasure_labelGibbsMeasure (by omega) hN η.val hβ hsub
    exact entropy_square_eq hG
  have hsum (s : Finset (LabelState J N t)) :
      (∑ η ∈ s, (labelWeight (by omega) β η : EReal) *
        (Rothaus.squareEntropy (labelGibbsMeasure (by omega) η.val β) G : EReal)) =
      ((∑ η ∈ s, labelWeight (by omega) β η *
        Rothaus.squareEntropy (labelGibbsMeasure (by omega) η.val β) G : ℝ) : EReal) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, ih, EReal.coe_add, EReal.coe_mul]
  simp_rw [he]
  rw [hsum]
  rw [FibreEntropy.entropy_finiteMeasure
    (labelWeight (J := J) (N := N) (t := t) (by omega) β) (conditionalSquare (by omega) β G)
    (fun _ => ENNReal.toReal_nonneg) (conditionalSquare_nonneg (by omega) β G), ← EReal.coe_add]
  exact actual_entropy_chain hJ hN hβ hsub hut hG hzero

/-- Exactly the two source light-region constants; neither depends on N,
actual beta, or the observable. The unresolved far constant is fixed. -/
def energyConstant (J : ℕ) (β₀ t u C₂ cFar : ℝ) : ℝ :=
  ConditionalLogSobolev.coefficient J β₀ C₂ +
    FullLabelEntropy.entropyConstant J β₀ u cFar *
      EntropyBoundarySummation.energyCoefficient J β₀ t C₂ / (J : ℝ)^2

def massConstant (J : ℕ) (β₀ t u C₂ cFar : ℝ) : ℝ :=
  FullLabelEntropy.entropyConstant J β₀ u cFar *
    EntropyBoundarySummation.massCoefficient J β₀ t C₂ +
      FullLabelEntropy.defectConstant J β₀ u cFar

theorem constants_nonneg {β₀ cFar : ℝ} (hJ : 0 < J) (hβ₀ : 0 ≤ β₀)
    (hsub : β₀ < 4) (hcFar : 0 < cFar) (t u C₂ : ℝ) :
    0 ≤ energyConstant J β₀ t u C₂ cFar ∧ 0 ≤ massConstant J β₀ t u C₂ cFar := by
  have hA := full_label_coefficient_nonneg hJ hβ₀ hsub hcFar u
  have hK := ConditionalLogSobolev.coefficient_nonneg hJ hβ₀ C₂
  have hE := EntropyBoundarySummation.source_coefficients_nonneg hJ hβ₀ t C₂
  have hB := (OccupationCriterion.constants_nonneg (u := u) hJ hβ₀ hsub hcFar).2
  have hS : 0 ≤ FullLabelEntropy.sparseLoss J β₀ :=
    add_nonneg (div_nonneg (FullLabelEntropy.quadraticLoss_nonneg hJ hsub) (by norm_num))
      (OccupationCoercivity.lowerLoss_nonneg J hβ₀)
  have hlog : 0 ≤ Real.log (J : ℝ) := Real.log_nonneg (by exact_mod_cast hJ)
  have hcoef := (FullLabelEntropy.sparseCoefficient_pos hJ hsub hcFar).le
  have hdef : 0 ≤ FullLabelEntropy.defectConstant J β₀ u cFar := by
    unfold FullLabelEntropy.defectConstant
    exact add_nonneg hB (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hS) hlog) hcoef)
  constructor
  · exact add_nonneg hK (div_nonneg (mul_nonneg hA hE.1) (sq_nonneg _))
  · exact add_nonneg (mul_nonneg hA hE.2) hdef

/-- Source cor:light-entropy for the actual physical Gibbs measure and
original outer label graph. Only the named far-imbalance analytic input
remains unresolved; no entropy, conditional LSI, mass or energy comparison
is an input to this theorem. -/
theorem light_entropy_of_far {β₀ C₂ cFar : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hmeshY : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
    (ht : 0 < t) (htC : t < occupationBound β₀)
    (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
      nearScale (chosenRadius β₀ C₂) * t ≤ 1)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (hsmall : 4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1)
    (hu : 0 < u) (hut : u < 3*t/4)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀ ≤ J)
    (hresolution : HeavyScales.sourceResolution β₀ (u/2) ≤ J)
    (hsmallJ : 1/(J^2:ℕ) < t/8) (hinner : 1/(J^2:ℕ) < u)
    (hcFar : 0 < cFar)
    (hlarge : FullLabelEntropy.particleThreshold J β₀ t u cFar ≤ N)
    (hfar : OccupationCoercivity.FarImbalance (N := N) (t := t) (mesh_pos hmesh) β β₀ cFar)
    {C : ℝ≥0} {G : Configuration N → ℝ} (hG : ConfigurationEuclideanLipschitzWith C G)
    (hzero : ∀ X, u ≤ maximumOccupation N J (mesh_pos hmesh) X → G X = 0) :
    entropy (gibbsMeasure greenRealRepresentative N β) (fun X => G X ^ 2) ≤
      ((energyConstant J β₀ t u C₂ cFar *
          (∫ X, totalEnergyDensity G X ∂gibbsMeasure greenRealRepresentative N β) +
        massConstant J β₀ t u C₂ cFar *
          ∫ X, G X ^ 2 ∂gibbsMeasure greenRealRepresentative N β : ℝ) : EReal) := by
  have hnear : OccupationNearImbalance.particleThreshold J β₀ t ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hN := (OccupationNearImbalance.particleThreshold_bounds (hβ.trans hβ₀) hsub ht hnear).2.2.2.1
  have hJ3 : 3 ≤ J := by have := radius_one_le β₀; omega
  have hut' : u ≤ t := by linarith only [hut, ht]
  have hu1 : u < 1 := by
    have hδ := (chosen_parameters β₀ (hβ.trans hβ₀)).2.1
    linarith only [hut', htC, hδ]
  have hm := conditionalSquare_mass hJ3 hN hβ (hβ₀.trans_lt hsub) hut' hG hzero
  have hs (η : LabelState J N t) (hη : ¬ OccupationCap u η.val) :
      conditionalSquare (mesh_pos hmesh) β G η = 0 :=
    square_mean_bad_label hJ3 (by omega) hzero η.val hη
  have hf := FullLabelEntropy.full_label_entropy_of_far hβ hβ₀ hsub ht htC hu hu1 hut
    hmesh hnearJ hresolution hsmallJ hinner hcFar hlarge hfar
    (conditionalSquare (mesh_pos hmesh) β G)
    (conditionalSquare_nonneg (mesh_pos hmesh) β G) hs
  rw [hm] at hf
  have hb := EntropyBoundaryComparison.entropy_boundary_comparison hβ hβ₀ hsub hC hk
    hmesh hmeshY ht htC.le hcap hscale hsmall hN hG
  have hA := full_label_coefficient_nonneg (mesh_pos hmesh) (hβ.trans hβ₀) hsub hcFar u
  have hb' := mul_le_mul_of_nonneg_left hb hA
  have hc := conditional_entropy_sum hβ hβ₀ hsub hC hk hmesh hmeshY ht htC.le
    hcap hscale hsmall hN hG
  have hall := add_le_add hc (hf.trans (add_le_add hb' le_rfl))
  have he := square_entropy_chain hJ3 hN hβ (hβ₀.trans_lt hsub) hut' hG hzero
  rw [← he] at hall
  rw [entropy_square_eq hG]
  apply EReal.coe_le_coe_iff.mpr
  exact hall.trans_eq (by unfold energyConstant massConstant; ring)

end PeriodicAttractiveLogGas.LightRegionEntropy
