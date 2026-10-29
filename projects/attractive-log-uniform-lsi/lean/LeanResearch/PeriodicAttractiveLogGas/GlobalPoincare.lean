import LeanResearch.PeriodicAttractiveLogGas.FullLabelVariance
import LeanResearch.PeriodicAttractiveLogGas.BoundaryComparison
import LeanResearch.PeriodicAttractiveLogGas.OccupationMassCutoff
import LeanResearch.PeriodicAttractiveLogGas.SourceConditionalEntropyEnergy

/-! Source prop:global-PI-large, 3151--3208. Variance-only physical Gibbs
assembly; the literal far-imbalance input remains explicit. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology
namespace PeriodicAttractiveLogGas.GlobalPoincare
open MeshCells LabelOccupations CellRestrictions DiscreteOccupationIdentities
open ConditionalLawEstimates ConditionalVarianceAssembly BoundaryEdgeSummation
open OccupationMassCutoff HeavyCoercivityConstants HeavyScales SeparatedRadius HeavyLocalization
variable {J N : ℕ} {β β₀ t : ℝ}

/-- The exact source first-reduction coefficient. -/
def firstCoefficient (J : ℕ) (β₀ t : ℝ) : ℝ :=
  (finePoincareConstant β₀ + FullLabelVariance.poincareConstant J β₀ *
    BoundaryComparison.boundaryComparisonConstant β₀ t) / (J : ℝ)^2

def cutoffCoefficient (J N : ℕ) (β₀ t : ℝ) : ℝ :=
  2*coercivityConstant β₀ (t/4) / ((J : ℝ)^2*N)

def absorptionCoefficient (N : ℕ) (β₀ t : ℝ) : ℝ :=
  2304*coercivityConstant β₀ (t/4) / (t^2*(N : ℝ)^2)

def poincareConstant (J : ℕ) (β₀ t : ℝ) : ℝ :=
  3*(firstCoefficient J β₀ t + 2*cutoffCoefficient J 1 β₀ t) + cutoffCoefficient J 1 β₀ t

/-- Exact finite conditional-law integral, with original label mass. -/
theorem weighted_label_integral (hJ : 0 < J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (η : LabelVector J N)
    (G : Configuration N → ℝ) :
    (labelProbability hJ η β).toReal * (∫ X, G X ∂labelGibbsMeasure hJ η β) =
      ∫ X in labelFiber hJ η, G X ∂gibbsMeasure greenRealRepresentative N β := by
  rw [labelGibbsMeasure_eq_cond hJ hN η hβ hsub, ProbabilityTheory.cond, integral_smul_measure]
  change (labelProbability hJ η β).toReal * (((labelProbability hJ η β)⁻¹).toReal * _) = _
  rw [ENNReal.toReal_inv, ← mul_assoc, mul_inv_cancel₀]
  · simp
  · exact (ENNReal.toReal_pos (labelProbability_ne_zero hJ hN η hβ hsub)
      (labelProbability_ne_top hJ hN η hβ hsub)).ne'

theorem good_event_eq_union (hJ : 0 < J) (t : ℝ) :
    goodLabelEvent N J hJ t = ⋃ η : LabelState J N t, labelFiber hJ η.val := by
  ext X
  simp only [goodLabelEvent, mem_ofPred_eq, mem_iUnion, labelFiber_eq_label_preimage,
    mem_preimage, mem_singleton_iff]
  constructor
  · intro hx
    exact ⟨⟨configurationMeshLabel N J hJ X, hx⟩, rfl⟩
  · rintro ⟨η, he⟩
    rw [he]
    exact η.property

theorem sum_label_integrals (hJ : 0 < J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) {G : Configuration N → ℝ}
    (hG : Integrable G (gibbsMeasure greenRealRepresentative N β)) :
    (∑ η : LabelState J N t, labelWeight hJ β η * ∫ X, G X ∂labelGibbsMeasure hJ η.val β) =
      ∫ X in goodLabelEvent N J hJ t, G X ∂gibbsMeasure greenRealRepresentative N β := by
  classical
  simp_rw [labelWeight, weighted_label_integral hJ hN hβ hsub]
  rw [← integral_iUnion_fintype (fun η : LabelState J N t => measurableSet_labelFiber hJ η.val)
    (fun η ζ h => disjoint_labelFiber hJ (fun he => h (Subtype.ext he)))
    (fun _ => hG.integrableOn), good_event_eq_union]

theorem good_event_mono (hJ : 0 < J) {u v : ℝ} (huv : u ≤ v) :
    goodLabelEvent N J hJ u ⊆ goodLabelEvent N J hJ v := by
  intro X hX
  exact OccupationCap.mono hX huv

/-- Actual t/2--t/4 cutoff, enlarged to the true outer t event. -/
theorem physical_cutoff (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ht : 0 < t) (ht1 : t/2 < 1)
    (hmesh : sourceResolution β₀ (t/4) ≤ J)
    (hN : HeavyCoercivityConstants.particleThreshold β₀ (t/4) ≤ N)
    (hβ : 0 ≤ β) (hβle : β ≤ β₀) (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y => F (configurationQuotient N y))) (c : ℝ) :
    (∫ X in badLabelEvent N J (source_mesh_pos hmesh) (t/2), (F X-c)^2
      ∂gibbsMeasure greenRealRepresentative N β) ≤
    cutoffCoefficient J N β₀ t * ambientEnergy (configurationLipschitzAmbient
      (gibbsMeasure greenRealRepresentative N β) (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF) +
    absorptionCoefficient N β₀ t * (∫ X in goodLabelEvent N J (source_mesh_pos hmesh) t,
      (F X-c)^2 ∂gibbsMeasure greenRealRepresentative N β) := by
  have hh := occupation_complement_control_good hβ₀ hsub (show 0 < t/4 by linarith)
    (show t/4 < t/2 by linarith) ht1 hmesh hN hβ hβle F hF c
  have he : 144*coercivityConstant β₀ (t/4) / ((N : ℝ)^2*(t/2-t/4)^2) =
      absorptionCoefficient N β₀ t := by
    unfold absorptionCoefficient
    have he : (t/2-t/4)^2 = t^2/16 := by ring
    rw [he]
    ring
  rw [he] at hh
  apply hh.trans
  apply add_le_add le_rfl
  have hC := coercivityConstant_pos hsub (show 0 < t/4 by linarith)
  apply mul_le_mul_of_nonneg_left _ (by unfold absorptionCoefficient; positivity)
  apply setIntegral_mono_set
  · exact (integrable_continuous_sq (gibbsMeasure greenRealRepresentative N β) (shiftValue F c)).integrableOn
  · exact Eventually.of_forall fun X => sq_nonneg (F X-c)
  · exact Eventually.of_forall fun X hX => good_event_mono _ (by linarith : t/2 ≤ t) hX

/-- The literal source ceiling gives eta_N at most one quarter. -/
theorem absorption_bound (ht : 0 < t) {C : ℝ} (hC : 0 ≤ C)
    (hN : 1 ≤ N) (hlarge : ⌈96*Real.sqrt C/t⌉₊ ≤ N) :
    2304*C/(t^2*(N : ℝ)^2) ≤ 1/4 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hh : 96*Real.sqrt C ≤ (N : ℝ)*t := (div_le_iff₀ ht).mp (Nat.ceil_le.mp hlarge)
  have hs := Real.sq_sqrt hC
  apply (div_le_iff₀ (by positivity : 0 < t^2*(N : ℝ)^2)).mpr
  nlinarith [sq_nonneg ((N : ℝ)*t-96*Real.sqrt C), Real.sqrt_nonneg C]

/-- Exact source absorption, retaining the exterior mass until the last step. -/
theorem absorb {A S E a B Bstar eta : ℝ} (hE : 0 ≤ E) (hA0 : 0 ≤ A)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hBB : B ≤ Bstar) (he : eta ≤ 1/4)
    (hA : A ≤ a*E+2*S) (hcut : S ≤ B*E+eta*A) :
    A+S ≤ (3*(a+2*Bstar)+Bstar)*E := by
  have heA := mul_le_mul_of_nonneg_right he hA0
  have hAE := mul_nonneg ha hE
  have hBE := mul_nonneg hB hE
  have hBstar := mul_le_mul_of_nonneg_right hBB hE
  have hAA : A ≤ 2*(a+2*B)*E := by nlinarith
  have hAS : A+S ≤ (5/2*(a+2*B)+B)*E := by nlinarith
  have hBs : 0 ≤ Bstar := hB.trans hBB
  nlinarith

/-- Ordinary coordinate derivatives and the ambient full gradient agree
on the genuine Gibbs full-measure differentiability set. -/
theorem physical_energy (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y => F (configurationQuotient N y))) (β : ℝ) :
    (∫ X, totalEnergyDensity F X ∂gibbsMeasure greenRealRepresentative N β) =
      ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
        (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF) := by
  rw [configurationLipschitzAmbient_energy_eq_integral]
  apply integral_congr_ae
  filter_upwards [ae_hasFDerivAt_configurationLift_gibbs greenRealRepresentative β F hF] with X hX
  have he := SourceConditionalEntropyEnergy.energy_eq_norm_of_hasFDerivAt
    (hX (configurationCenteredLift X) (configurationQuotient_centeredLift X))
  simpa only [configurationQuotient_centeredLift] using he

theorem continuous_memLp (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (F : C(Configuration N, ℝ)) : MemLp F 2 μ :=
  MemLp.of_bound F.continuous.measurable.aestronglyMeasurable ‖F‖
    (Eventually.of_forall F.norm_coe_le_norm)

/-- Exact conditional variance decomposition about an arbitrary center. -/
theorem integral_centered_square (μ : Measure (Configuration N)) [IsProbabilityMeasure μ]
    (F : C(Configuration N, ℝ)) (c : ℝ) :
    (∫ X, (F X-c)^2 ∂μ) = variance F μ + ((∫ X, F X ∂μ)-c)^2 := by
  have hf := continuous_memLp μ F
  have hs : MemLp (fun X => F X-c) 2 μ := hf.sub (memLp_const c)
  have hv := variance_eq_sub hs
  rw [variance_sub_const hf.aestronglyMeasurable c] at hv
  have hm : (∫ X, F X-c ∂μ) = (∫ X, F X ∂μ)-c := by
    rw [integral_sub (hf.integrable (by norm_num)) (integrable_const c)]
    simp
  change variance F μ = (∫ X, (F X-c)^2 ∂μ) - (∫ X, F X-c ∂μ)^2 at hv
  rw [hm] at hv
  linarith

/-- Fine conditional PI for every actual outer label, with the original
physical test and unscaled full coordinate energy. -/
theorem conditional_poincare (hN : 2 ≤ N) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hsub : β₀ < 4) (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hmesh : 8*(radius β₀+4) ≤ J) (η : LabelState J N t)
    (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y => F (configurationQuotient N y))) :
    variance F (labelGibbsMeasure (mesh_pos hmesh) η.val β) ≤
      (finePoincareConstant β₀/(J : ℝ)^2) *
        ∫ X, totalEnergyDensity F X ∂labelGibbsMeasure (mesh_pos hmesh) η.val β := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hp := configurationEuclideanLipschitzWith_iff_lift.mpr hF
  have hlocal : ConfigurationPhysicalLipschitzOn L F
      (DeletedConditionalPoincare.closedPatchProduct (mesh_pos hmesh) η.val (fun _ => .cell)) := by
    intro X _ Y _
    simpa only [Real.dist_eq] using hp X Y
  exact DeletedConditionalPoincare.labelGibbs_poincare hN hβ hβ₀ hsub ht htC hmesh η.val η.property hlocal

/-- The true ambient variance boundary estimate applied to the Lipschitz
physical representative; AE representatives are transported by actual
conditional-law absolute continuity. -/
theorem physical_boundary (hN : 2 ≤ N) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hsub : β₀ < 4) (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hmesh : 8*(radius β₀+4) ≤ J) (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y => F (configurationQuotient N y))) :
    labelEnergy (t := t) (mesh_pos hmesh) β (labelMean (mesh_pos hmesh) β F) ≤
      (BoundaryComparison.boundaryComparisonConstant β₀ t/(J : ℝ)^2) *
      ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
        (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF) := by
  have hh := BoundaryComparison.green_ambient_boundary_comparison hN hβ hβ₀ hsub ht htC hmesh
    (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
      (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF)
  simpa only [configurationLipschitzAmbient_value,
    BoundaryComparison.labelMean_toLp (mesh_pos hmesh) hN hβ (hβ₀.trans_lt hsub)] using hh

/-- The original restricted Gibbs squared norm splits over precisely the
outer labels into their conditional variances and conditional means. -/
theorem restricted_variance_decomposition (hJ : 0 < J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (F : C(Configuration N, ℝ)) (c : ℝ) :
    (∫ X in goodLabelEvent N J hJ t, (F X-c)^2 ∂gibbsMeasure greenRealRepresentative N β) =
      (∑ η : LabelState J N t, labelWeight hJ β η * variance F (labelGibbsMeasure hJ η.val β)) +
      ∑ η : LabelState J N t, labelWeight hJ β η * (labelMean hJ β F η-c)^2 := by
  have hsq : Integrable (fun X => (F X-c)^2) (gibbsMeasure greenRealRepresentative N β) :=
    integrable_continuous_sq _ (shiftValue F c)
  rw [← sum_label_integrals (t := t) hJ hN hβ hsub hsq]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro η _
  let : IsProbabilityMeasure (labelGibbsMeasure hJ η.val β) :=
    isProbabilityMeasure_labelGibbsMeasure hJ hN η.val hβ hsub
  rw [integral_centered_square]
  simp only [labelMean]
  ring

theorem ae_label_fibre (hJ : 0 < J) (η : LabelVector J N) (β : ℝ) :
    ∀ᵐ X ∂labelGibbsMeasure hJ η β, X ∈ labelFiber hJ η := by
  apply Measure.ae_smul_measure
  apply (withDensity_absolutelyContinuous _ _).ae_le
  rw [labelReference_eq]
  apply Measure.ae_smul_measure
  exact ae_restrict_mem (measurableSet_labelFiber hJ η)

local instance : DecidablePred (fun η : LabelState J N t =>
    OccupationCap (t/2) η.val) := fun _ => Classical.propDecidable _

/-- Conditional Jensen on the actual exterior label classes, followed by
unconditioned finite disintegration. -/
theorem exterior_means (hJ : 0 < J) (hN : 2 ≤ N) (hβ : 0 ≤ β) (hsub : β < 4)
    (F : C(Configuration N, ℝ)) (c : ℝ) :
    (∑ η : LabelState J N t, if OccupationCap (t/2) η.val then 0
      else labelWeight hJ β η*(labelMean hJ β F η-c)^2) ≤
      ∫ X in badLabelEvent N J hJ (t/2), (F X-c)^2 ∂gibbsMeasure greenRealRepresentative N β := by
  classical
  let H := (badLabelEvent N J hJ (t/2)).indicator (fun X => (F X-c)^2)
  have hH : Integrable H (gibbsMeasure greenRealRepresentative N β) :=
    (integrable_continuous_sq _ (shiftValue F c)).indicator (measurableSet_badLabelEvent N J hJ (t/2))
  have hH0 : ∀ X, 0 ≤ H X := fun X => by
    dsimp only [H]
    by_cases hx : X ∈ badLabelEvent N J hJ (t/2) <;> simp [hx, sq_nonneg]
  have hpoint (η : LabelState J N t) :
      (if OccupationCap (t/2) η.val then 0 else labelWeight hJ β η*(labelMean hJ β F η-c)^2) ≤
      labelWeight hJ β η * ∫ X, H X ∂labelGibbsMeasure hJ η.val β := by
    by_cases hc : OccupationCap (t/2) η.val
    · simp only [ite_eq_left hc]
      exact mul_nonneg ENNReal.toReal_nonneg (integral_nonneg hH0)
    · simp only [ite_eq_right hc]
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      have he : H =ᵐ[labelGibbsMeasure hJ η.val β] fun X => (F X-c)^2 := by
        filter_upwards [ae_label_fibre hJ η.val β] with X hX
        have hlabel : configurationMeshLabel N J hJ X = η.val := by
          simpa only [labelFiber_eq_label_preimage, mem_preimage, mem_singleton_iff] using hX
        have hx : X ∈ badLabelEvent N J hJ (t/2) := by
          change ¬ OccupationCap (t/2) (configurationMeshLabel N J hJ X)
          rwa [hlabel]
        exact Set.indicator_of_mem hx _
      rw [integral_congr_ae he]
      let : IsProbabilityMeasure (labelGibbsMeasure hJ η.val β) :=
        isProbabilityMeasure_labelGibbsMeasure hJ hN η.val hβ hsub
      have hv := integral_centered_square (labelGibbsMeasure hJ η.val β) F c
      have hn := ProbabilityTheory.variance_nonneg F (labelGibbsMeasure hJ η.val β)
      change ((∫ X, F X ∂labelGibbsMeasure hJ η.val β)-c)^2 ≤ _
      linarith
  calc
    _ ≤ ∑ η : LabelState J N t, labelWeight hJ β η * ∫ X, H X ∂labelGibbsMeasure hJ η.val β :=
      Finset.sum_le_sum fun η _ => hpoint η
    _ = ∫ X in goodLabelEvent N J hJ t, H X ∂gibbsMeasure greenRealRepresentative N β :=
      sum_label_integrals hJ hN hβ hsub hH
    _ ≤ ∫ X, H X ∂gibbsMeasure greenRealRepresentative N β :=
      setIntegral_le_integral hH (Eventually.of_forall hH0)
    _ = _ := integral_indicator (measurableSet_badLabelEvent N J hJ (t/2))

theorem conditional_variance_sum (hN : 2 ≤ N) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hsub : β₀ < 4) (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hmesh : 8*(radius β₀+4) ≤ J) (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y => F (configurationQuotient N y))) :
    (∑ η : LabelState J N t, labelWeight (mesh_pos hmesh) β η *
      variance F (labelGibbsMeasure (mesh_pos hmesh) η.val β)) ≤
    (finePoincareConstant β₀/(J : ℝ)^2) * ambientEnergy
      (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
        (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF) := by
  have hp := configurationEuclideanLipschitzWith_iff_lift.mpr hF
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun (η : LabelState J N t) _ =>
    mul_le_mul_of_nonneg_left (conditional_poincare hN hβ hβ₀ hsub ht htC hmesh η F hF)
      (show 0 ≤ labelWeight (mesh_pos hmesh) β η from ENNReal.toReal_nonneg))
  have hi := sum_label_fiber_integrals_le (t := t) (mesh_pos hmesh)
    (μ := gibbsMeasure greenRealRepresentative N β) (integrable_totalEnergyDensity hp)
    (totalEnergyDensity_nonneg F)
  simp_rw [mul_left_comm (labelWeight (mesh_pos hmesh) β _) (finePoincareConstant β₀/(J : ℝ)^2)] at hsum
  rw [← Finset.mul_sum] at hsum
  simp_rw [labelWeight, weighted_label_integral (mesh_pos hmesh) hN hβ (hβ₀.trans_lt hsub)] at hsum
  have hc : 0 ≤ finePoincareConstant β₀/(J : ℝ)^2 :=
    div_nonneg (finePoincareConstant_nonneg _) (sq_nonneg _)
  exact hsum.trans (by rw [← physical_energy F hF β]; exact mul_le_mul_of_nonneg_left hi hc)

theorem label_coefficient_nonneg (hβ₀ : 0 ≤ β₀) :
    0 ≤ FullLabelVariance.poincareConstant J β₀ :=
  (OccupationCoercivity.bufferConstant_nonneg J hβ₀).trans (le_max_right _ _)

theorem firstCoefficient_nonneg (hβ₀ : 0 ≤ β₀) (ht : 0 ≤ t) :
    0 ≤ firstCoefficient J β₀ t := by
  unfold firstCoefficient
  exact div_nonneg (add_nonneg (finePoincareConstant_nonneg _)
    (mul_nonneg (label_coefficient_nonneg hβ₀)
      (BoundaryComparison.boundaryComparisonConstant_nonneg β₀ ht))) (sq_nonneg _)

/-- Actual first reduction A ≤ a_J E + 2 S, with the source central
conditional mean, full outer graph and original Gibbs masses. -/
theorem first_reduction {cFar : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t < occupationBound β₀)
    (hmesh : 8*(radius β₀+4) ≤ J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀ ≤ J)
    (hsmall : 1/(J^2:ℕ) < t/8) (hcFar : 0 < cFar)
    (hlarge : OccupationCoercivity.particleThreshold J β₀ t cFar ≤ N)
    (hfar : OccupationCoercivity.FarImbalance (N := N) (t := t) (mesh_pos hmesh) β β₀ cFar)
    (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y => F (configurationQuotient N y))) :
    let c := OccupationPoincare.center (mesh_pos hmesh) β β₀
      (FibreProjection.fibreAverage (labelMean (t := t) (mesh_pos hmesh) β F))
    (∫ X in goodLabelEvent N J (mesh_pos hmesh) t, (F X-c)^2 ∂gibbsMeasure greenRealRepresentative N β) ≤
      firstCoefficient J β₀ t * ambientEnergy
        (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
          (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF) +
      2*(∫ X in badLabelEvent N J (mesh_pos hmesh) (t/2), (F X-c)^2
        ∂gibbsMeasure greenRealRepresentative N β) := by
  dsimp only
  let c := OccupationPoincare.center (mesh_pos hmesh) β β₀
    (FibreProjection.fibreAverage (labelMean (t := t) (mesh_pos hmesh) β F))
  have hN := (OccupationPoincare.threshold_gates (hβ.trans hβ₀) hsub ht hlarge).2.1
  have hv := conditional_variance_sum hN hβ hβ₀ hsub ht htC.le hmesh F hF
  have hl := FullLabelVariance.full_label_poincare_of_far hβ hβ₀ hsub ht htC hmesh
    hnearJ hsmall hcFar hlarge hfar (labelMean (mesh_pos hmesh) β F)
  have hb := mul_le_mul_of_nonneg_left
    (physical_boundary hN hβ hβ₀ hsub ht htC.le hmesh F hF)
    (label_coefficient_nonneg (J := J) (hβ.trans hβ₀))
  have hx := exterior_means (t := t) (mesh_pos hmesh) hN hβ (hβ₀.trans_lt hsub) F c
  have he := restricted_variance_decomposition (t := t) (mesh_pos hmesh) hN hβ (hβ₀.trans_lt hsub) F c
  dsimp only [c] at hx he
  dsimp only at hl
  rw [he]
  unfold firstCoefficient
  have ha : (finePoincareConstant β₀ + FullLabelVariance.poincareConstant J β₀ *
      BoundaryComparison.boundaryComparisonConstant β₀ t)/(J : ℝ)^2 =
      finePoincareConstant β₀/(J : ℝ)^2 + FullLabelVariance.poincareConstant J β₀ *
        (BoundaryComparison.boundaryComparisonConstant β₀ t/(J : ℝ)^2) := by ring
  rw [ha, add_mul]
  linarith only [hv, hl, hb, hx]

/-- Uniform source threshold: actual occupation and heavy thresholds plus
the literal ceiling 96 sqrt(C_DP)/t. -/
def particleThreshold (J : ℕ) (β₀ t cFar : ℝ) : ℕ :=
  max (OccupationCoercivity.particleThreshold J β₀ t cFar)
    (max (HeavyCoercivityConstants.particleThreshold β₀ (t/4))
      ⌈96*Real.sqrt (coercivityConstant β₀ (t/4))/t⌉₊)

theorem cutoffCoefficient_le (hJ : 0 < J) (hN : 1 ≤ N)
    (hsub : β₀ < 4) (ht : 0 < t) :
    cutoffCoefficient J N β₀ t ≤ cutoffCoefficient J 1 β₀ t := by
  have hC := coercivityConstant_pos hsub (show 0 < t/4 by linarith)
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold cutoffCoefficient
  norm_num only [Nat.cast_one, mul_one]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)

/-- An arbitrary-centered global norm is covered by the outer good event
and the complement of the half-cap; no support or mean-zero assumption. -/
theorem full_norm_le_good_bad (hJ : 0 < J) (ht : 0 ≤ t) (F : C(Configuration N, ℝ))
    (c β : ℝ) :
    (∫ X, (F X-c)^2 ∂gibbsMeasure greenRealRepresentative N β) ≤
      (∫ X in goodLabelEvent N J hJ t, (F X-c)^2 ∂gibbsMeasure greenRealRepresentative N β) +
      (∫ X in badLabelEvent N J hJ (t/2), (F X-c)^2 ∂gibbsMeasure greenRealRepresentative N β) := by
  have hi : Integrable (fun X => (F X-c)^2) (gibbsMeasure greenRealRepresentative N β) :=
    integrable_continuous_sq _ (shiftValue F c)
  rw [← integral_add_compl (measurableSet_goodLabelEvent N J hJ t) hi]
  apply add_le_add le_rfl
  apply setIntegral_mono_set hi.integrableOn (Eventually.of_forall fun X => sq_nonneg (F X-c))
  exact Eventually.of_forall fun X hx hc => hx (good_event_mono hJ (by linarith : t/2 ≤ t) hc)

/-- The actual physical Gibbs global PI for all sufficiently large N,
along the supplied variance-only proof. Only literal FarImbalance remains
as an unresolved analytic input; every conditional and cutoff estimate
is derived from the actual law. -/
theorem global_poincare_of_far {cFar : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t < occupationBound β₀)
    (hmesh : 8*(radius β₀+4) ≤ J)
    (hheavyJ : sourceResolution β₀ (t/4) ≤ J)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀ ≤ J)
    (hsmall : 1/(J^2:ℕ) < t/8) (hcFar : 0 < cFar)
    (hlarge : particleThreshold J β₀ t cFar ≤ N)
    (hfar : OccupationCoercivity.FarImbalance (N := N) (t := t) (mesh_pos hmesh) β β₀ cFar)
    (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y => F (configurationQuotient N y))) :
    variance F (gibbsMeasure greenRealRepresentative N β) ≤
      poincareConstant J β₀ t * ambientEnergy
        (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
          (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF) := by
  have hoc : OccupationCoercivity.particleThreshold J β₀ t cFar ≤ N := (le_max_left _ _).trans hlarge
  have hheavy : HeavyCoercivityConstants.particleThreshold β₀ (t/4) ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hceil : ⌈96*Real.sqrt (coercivityConstant β₀ (t/4))/t⌉₊ ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hN := (OccupationPoincare.threshold_gates (hβ.trans hβ₀) hsub ht hoc).2.1
  let : IsProbabilityMeasure (gibbsMeasure greenRealRepresentative N β) :=
    isProbabilityMeasure_greenGibbs N hN hβ (hβ₀.trans_lt hsub)
  let c := OccupationPoincare.center (mesh_pos hmesh) β β₀
    (FibreProjection.fibreAverage (labelMean (t := t) (mesh_pos hmesh) β F))
  let E := ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
    (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF)
  let A := ∫ X in goodLabelEvent N J (mesh_pos hmesh) t, (F X-c)^2
    ∂gibbsMeasure greenRealRepresentative N β
  let S := ∫ X in badLabelEvent N J (mesh_pos hmesh) (t/2), (F X-c)^2
    ∂gibbsMeasure greenRealRepresentative N β
  have hfirst : A ≤ firstCoefficient J β₀ t*E+2*S :=
    first_reduction hβ hβ₀ hsub ht htC hmesh hnearJ hsmall hcFar hoc hfar F hF
  have ht1 : t/2 < 1 := by
    have hh := (chosen_parameters β₀ (hβ.trans hβ₀)).2.1
    linarith
  have hcut : S ≤ cutoffCoefficient J N β₀ t*E+absorptionCoefficient N β₀ t*A :=
    physical_cutoff (hβ.trans hβ₀) hsub ht ht1 hheavyJ hheavy hβ hβ₀ F hF c
  have hC := coercivityConstant_pos hsub (show 0 < t/4 by linarith)
  have he : absorptionCoefficient N β₀ t ≤ 1/4 :=
    absorption_bound ht hC.le (by omega) hceil
  have hA : 0 ≤ A := integral_nonneg fun X => sq_nonneg (F X-c)
  have hE : 0 ≤ E := sq_nonneg _
  have hB : 0 ≤ cutoffCoefficient J N β₀ t := by unfold cutoffCoefficient; positivity
  have hab := absorb hE hA (firstCoefficient_nonneg (hβ.trans hβ₀) ht.le) hB
    (cutoffCoefficient_le (mesh_pos hmesh) (by omega) hsub ht) he hfirst hcut
  have hnorm := full_norm_le_good_bad (mesh_pos hmesh) ht.le F c β
  have hv := DensityMoments.variance_le_integral_sub_sq
    (ν := gibbsMeasure greenRealRepresentative N β) F.continuous.measurable c
  exact hv.trans (hnorm.trans hab)

end PeriodicAttractiveLogGas.GlobalPoincare
