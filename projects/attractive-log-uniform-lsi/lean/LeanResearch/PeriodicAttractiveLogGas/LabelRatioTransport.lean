import LeanResearch.PeriodicAttractiveLogGas.ConditionalLawEstimates
import LeanResearch.PeriodicAttractiveLogGas.CellNormalizerBounds
import LeanResearch.PeriodicAttractiveLogGas.OccupationProbability

/-! Source Lemma 3.9: common-factor transport of specified-label ratios
and the complete adjacent ratio and crossing range. The common-factor
transport lemma is general; the source wrappers use the actual cell
normalizer estimates and the actual one-site density lower bound.

Development proof: central verification and separate semantic review are
recorded in research/reviews. No protected acceptance is asserted.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace PeriodicAttractiveLogGas.LabelRatioTransport

open MeshCells MeshAdjacentCells CellRestrictions GreenPointWeights
  LabelOccupations OneCoordinateConditionals ConditionalLawEstimates

def cellNormalizer {n J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    (β : ℝ) (Y : Configuration n) : ℝ :=
  ∫ z, OneCoordinateConditionals.sourceWeight β Y z ∂meshCellMeasure J hJ a

def cellMass {n J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    (β : ℝ) (Y : Configuration n) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (OneCoordinateConditionals.sourceWeight β Y z) ∂meshCellMeasure J hJ a

theorem cellMass_eq_ofReal {n J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    (β : ℝ) (Y : Configuration n)
    (hi : Integrable (OneCoordinateConditionals.sourceWeight β Y) (meshCellMeasure J hJ a)) :
    cellMass hJ a β Y = ENNReal.ofReal (cellNormalizer hJ a β Y) :=
  (ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun z ↦ (sourceWeight_pos β Y z).le)).symm

theorem cellNormalizer_nonneg {n J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    (β : ℝ) (Y : Configuration n) : 0 ≤ cellNormalizer hJ a β Y :=
  integral_nonneg fun z ↦ (sourceWeight_pos β Y z).le

theorem cellNormalizer_eq_raw {n J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    (β : ℝ) (Y : Configuration n) :
    cellNormalizer hJ a β Y = ∫ z, rawSourceWeight β Y z ∂meshCellMeasure J hJ a :=
  integral_congr_ae ((meshCellMeasure_absolutelyContinuous J hJ a).ae_le
    (sourceWeight_ae_rawSourceWeight β Y))

theorem cellNormalizer_eq_haar {n J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    (β : ℝ) (Y : Configuration n) :
    cellNormalizer hJ a β Y = (J : ℝ) ^ 2 *
      ∫ z in meshCell J hJ a, OneCoordinateConditionals.sourceWeight β Y z ∂torusMeasure := by
  simp only [cellNormalizer, meshCellMeasure, integral_smul_measure, smul_eq_mul,
    ENNReal.toReal_pow, ENNReal.toReal_natCast]

theorem outsideWeight_pos {n : ℕ} (β : ℝ) (Y : Configuration n) :
    0 < OneCoordinateConditionals.outsideWeight β Y := Real.exp_pos _

theorem prescribedOutside_update_iff {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (Y : Configuration n) :
    PrescribedOutside hJ (Function.update η i a) i Y ↔ PrescribedOutside hJ η i Y := by
  simp only [PrescribedOutside, Function.update_of_ne (Fin.succAbove_ne i _)]

theorem ae_prescribedOutside {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) :
    ∀ᵐ Y ∂outsideReference (fun k ↦ meshCellMeasure J hJ (η k)) i,
      PrescribedOutside hJ η i Y := by
  apply ae_all_iff.mpr
  intro j
  have h := (measurePreserving_eval
    (fun k : Fin n ↦ meshCellMeasure J hJ (η (i.succAbove k))) j).quasiMeasurePreserving.ae
      (ae_mem_meshCell J hJ (η (i.succAbove j)))
  exact h.mono fun Y hY ↦ subset_closure hY

/-- The same positive outside-energy factor and the same outside measure
occur for every proposed value of the one prescribed label. -/
theorem labelPartition_eq_common_factor {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (β : ℝ) :
    labelPartitionFunction hJ (Function.update η i a) β =
      ∫⁻ Y, ENNReal.ofReal (OneCoordinateConditionals.outsideWeight β Y) * cellMass hJ a β Y
        ∂outsideReference (fun k ↦ meshCellMeasure J hJ (η k)) i := by
  let ζ := Function.update η i a
  have hac : labelReference hJ ζ ≪ referenceMeasure (n + 1) := by
    rw [labelReference_eq]
    exact Measure.absolutelyContinuous_restrict.smul_left _
  have hae := hac.ae_le (gibbsWeight_congr_ae_kernel regularGreenRepresentative_ae (n + 1) β)
  have hout : outsideReference (fun k ↦ meshCellMeasure J hJ (ζ k)) i =
      outsideReference (fun k ↦ meshCellMeasure J hJ (η k)) i := by
    unfold outsideReference
    congr 1
    funext j
    simp only [ζ, Function.update_of_ne (Fin.succAbove_ne i j)]
  calc
    _ = ∫⁻ X, jointDensity (n + 1) β X ∂labelReference hJ ζ :=
      lintegral_congr_ae (by
        filter_upwards [hae] with X hX
        exact congrArg ENNReal.ofReal hX.symm)
    _ = ∫⁻ Y, ∫⁻ z, jointDensity (n + 1) β (insertSite i z Y)
        ∂meshCellMeasure J hJ (ζ i)
        ∂outsideReference (fun k ↦ meshCellMeasure J hJ (ζ k)) i :=
      lintegral_pi_insert _ i (measurable_jointDensity _ β)
    _ = _ := by
      rw [hout]
      simp only [ζ, Function.update_self, jointDensity_insertSite]
      apply lintegral_congr
      intro Y
      exact lintegral_const_mul _ (measurable_sourceWeight β Y).ennreal_ofReal

/-- Extended-valued comparison is integrated before using finite positive
normalization. No integrability of a fictitious smaller Gibbs law is assumed. -/
theorem labelPartition_compare {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a b : MeshIndex J)
    (β C : ℝ)
    (hcomp : ∀ᵐ Y ∂outsideReference (fun k ↦ meshCellMeasure J hJ (η k)) i,
      ENNReal.ofReal C * cellMass hJ a β Y ≤ cellMass hJ b β Y) :
    ENNReal.ofReal C * labelPartitionFunction hJ (Function.update η i a) β ≤
      labelPartitionFunction hJ (Function.update η i b) β := by
  rw [labelPartition_eq_common_factor hJ η i a β, labelPartition_eq_common_factor hJ η i b β]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hcomp] with Y hY
  simpa only [mul_left_comm, mul_assoc] using
    mul_le_mul_right hY (ENNReal.ofReal (OneCoordinateConditionals.outsideWeight β Y))

theorem labelProbability_ratio_eq_partition_ratio {N J : ℕ}
    (hJ : 0 < J) (hN : 2 ≤ N) (η ζ : LabelVector J N)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    (labelProbability hJ ζ β).toReal / (labelProbability hJ η β).toReal =
      (labelPartitionFunction hJ ζ β).toReal / (labelPartitionFunction hJ η β).toReal := by
  have hs : 0 < (labelScale J N).toReal :=
    ENNReal.toReal_pos (labelScale_ne_zero hJ N) (labelScale_ne_top J N)
  have hp : 0 < (partitionFunction greenRealRepresentative N β).toReal :=
    ENNReal.toReal_pos (partitionFunction_ne_zero greenRealRepresentative_measurable N β)
      (green_partitionFunction_ne_top N hN hβ hsub)
  have ha : 0 < (labelPartitionFunction hJ η β).toReal :=
    ENNReal.toReal_pos (labelPartitionFunction_ne_zero hJ η β)
      (labelPartitionFunction_ne_top hJ hN η hβ hsub)
  rw [labelProbability_eq, labelProbability_eq]
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]
  field_simp [hs.ne', hp.ne', ha.ne']

/-- A proved comparison of actual one-site normalizers transports to the
ratio of actual specified-label probabilities. The label factor cancels. -/
theorem labelRatio_lower_of_normalizer_comparison {n J : ℕ} (hJ : 0 < J)
    (hn : 2 ≤ n + 1) (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a b : MeshIndex J)
    {β C : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) (hC : 0 ≤ C)
    (hcomp : ∀ Y : Configuration n, PrescribedOutside hJ η i Y →
      Integrable (OneCoordinateConditionals.sourceWeight β Y) (meshCellMeasure J hJ a) ∧
      Integrable (OneCoordinateConditionals.sourceWeight β Y) (meshCellMeasure J hJ b) ∧
      C * cellNormalizer hJ a β Y ≤ cellNormalizer hJ b β Y) :
    C ≤ (labelProbability hJ (Function.update η i b) β).toReal /
      (labelProbability hJ (Function.update η i a) β).toReal := by
  have hz := labelPartition_compare hJ η i a b β C (by
    filter_upwards [ae_prescribedOutside hJ η i] with Y hY
    obtain ⟨hia, hib, hc⟩ := hcomp Y hY
    rw [cellMass_eq_ofReal hJ a β Y hia, cellMass_eq_ofReal hJ b β Y hib,
      ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal hc)
  have hzreal := ENNReal.toReal_mono
    (labelPartitionFunction_ne_top hJ hn (Function.update η i b) hβ hsub) hz
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at hzreal
  rw [labelProbability_ratio_eq_partition_ratio hJ hn _ _ hβ hsub]
  exact (le_div_iff₀ (ENNReal.toReal_pos
    (labelPartitionFunction_ne_zero hJ (Function.update η i a) β)
    (labelPartitionFunction_ne_top hJ hn (Function.update η i a) hβ hsub))).mpr hzreal

/-- Generic arbitrary-cell interface for the analytic normalizer bounds.
The constants here are bounds on the normalized cell integrals. -/
theorem labelRatio_bounds_of_normalizer_bounds {n J : ℕ} (hJ : 0 < J)
    (hn : 2 ≤ n + 1) (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a b : MeshIndex J)
    {β L U : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) (hL : 0 < L) (hLU : L ≤ U)
    (hbounds : ∀ Y : Configuration n, PrescribedOutside hJ η i Y →
      Integrable (OneCoordinateConditionals.sourceWeight β Y) (meshCellMeasure J hJ a) ∧
      Integrable (OneCoordinateConditionals.sourceWeight β Y) (meshCellMeasure J hJ b) ∧
      L ≤ cellNormalizer hJ a β Y ∧ cellNormalizer hJ a β Y ≤ U ∧
      L ≤ cellNormalizer hJ b β Y ∧ cellNormalizer hJ b β Y ≤ U) :
    L / U ≤ (labelProbability hJ (Function.update η i b) β).toReal /
        (labelProbability hJ (Function.update η i a) β).toReal ∧
      (labelProbability hJ (Function.update η i b) β).toReal /
        (labelProbability hJ (Function.update η i a) β).toReal ≤ U / L := by
  have hU : 0 < U := hL.trans_le hLU
  have hlo := labelRatio_lower_of_normalizer_comparison hJ hn η i a b hβ hsub
    (div_nonneg hL.le hU.le) (by
      intro Y hY
      obtain ⟨hia, hib, _hla, hau, hlb, _hbu⟩ := hbounds Y hY
      refine ⟨hia, hib, ?_⟩
      calc
        _ ≤ L / U * U := mul_le_mul_of_nonneg_left hau (div_nonneg hL.le hU.le)
        _ = L := div_mul_cancel₀ L hU.ne'
        _ ≤ _ := hlb)
  have hrev := labelRatio_lower_of_normalizer_comparison hJ hn η i b a hβ hsub
    (div_nonneg hL.le hU.le) (by
      intro Y hY
      obtain ⟨hia, hib, hla, _hau, _hlb, hbu⟩ := hbounds Y hY
      refine ⟨hib, hia, ?_⟩
      calc
        _ ≤ L / U * U := mul_le_mul_of_nonneg_left hbu (div_nonneg hL.le hU.le)
        _ = L := div_mul_cancel₀ L hU.ne'
        _ ≤ _ := hla)
  have hpa : 0 < (labelProbability hJ (Function.update η i a) β).toReal :=
    ENNReal.toReal_pos (labelProbability_ne_zero hJ hn _ hβ hsub)
      (labelProbability_ne_top hJ hn _ hβ hsub)
  have hpb : 0 < (labelProbability hJ (Function.update η i b) β).toReal :=
    ENNReal.toReal_pos (labelProbability_ne_zero hJ hn _ hβ hsub)
      (labelProbability_ne_top hJ hn _ hβ hsub)
  refine ⟨hlo, (div_le_div_iff₀ hpa hL).mpr ?_⟩
  nlinarith [(div_le_div_iff₀ hU hpb).mp hrev]

/-- Actual arbitrary-cell comparison. The only kernel datum is an
explicit genuine global lower bound; all one-site moment bounds are proved
by CellNormalizerBounds from the source cap and mesh assumptions. -/
theorem arbitrary_label_ratio_normalized {n J : ℕ} (hn : 2 ≤ n + 1)
    {β β₀ δ Cg : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (_hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hCg : 0 ≤ Cg) (hg : ∀ z : Torus, -Cg ≤ regularGreenRepresentative z)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a b : MeshIndex J)
    (hadm : TwoEndpointAdmissible δ η i a b) :
    let hJ := mesh_pos hmesh
    let L := Real.exp (-β₀ * Cg)
    let U := CellNormalizerBounds.upperConstant β₀ kernelConstant J (radius β₀)
    let q := (labelProbability hJ (Function.update η i b) β).toReal /
      (labelProbability hJ (Function.update η i a) β).toReal
    0 < L / U ∧ L / U ≤ 1 ∧ L / U ≤ q ∧ q ≤ U / L := by
  let hJ := mesh_pos hmesh
  let L := Real.exp (-β₀ * Cg)
  let U := CellNormalizerBounds.upperConstant β₀ kernelConstant J (radius β₀)
  have hL : 0 < L := Real.exp_pos _
  have hbds (Y : Configuration n) (hY : PrescribedOutside hJ η i Y) :=
    CellNormalizerBounds.capped_source_normalizer_bounds hJ hβ hβ₀ hδ hCg hg hmesh
      (Function.update η i a) hadm.1 i Y
      ((prescribedOutside_update_iff hJ η i a Y).mpr hY)
  obtain ⟨Y₀, hY₀⟩ := (ae_prescribedOutside hJ η i).exists
  have hLU : L ≤ U := (hbds Y₀ hY₀ a).2.1.trans (hbds Y₀ hY₀ a).2.2
  have hU : 0 < U := hL.trans_le hLU
  have hratio := labelRatio_bounds_of_normalizer_bounds hJ hn η i a b hβ
    (hβ₀.trans_lt hsub) hL hLU (by
      intro Y hY
      have ha := hbds Y hY a
      have hb := hbds Y hY b
      exact ⟨ha.1, hb.1, ha.2.1, ha.2.2, hb.2.1, hb.2.2⟩)
  exact ⟨div_pos hL hU, (div_le_one hU).mpr hLU, hratio.1, hratio.2⟩

/-- Exact manuscript kappa, rather than an unspecified comparable
constant. The conclusion concerns the original specified-label masses. -/
theorem arbitrary_label_ratio {n J : ℕ} (hn : 2 ≤ n + 1)
    {β β₀ δ Cg : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hCg : 0 ≤ Cg) (hg : ∀ z : Torus, -Cg ≤ regularGreenRepresentative z)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a b : MeshIndex J)
    (hadm : TwoEndpointAdmissible δ η i a b) :
    let κ := CellNormalizerBounds.kappaConstant β₀ Cg kernelConstant J (radius β₀)
    let hJ := mesh_pos hmesh
    let q := (labelProbability hJ (Function.update η i b) β).toReal /
      (labelProbability hJ (Function.update η i a) β).toReal
    0 < κ ∧ κ ≤ 1 ∧ κ ≤ q ∧ q ≤ κ⁻¹ := by
  have h := arbitrary_label_ratio_normalized hn hβ hβ₀ hsub hδ₀ hδ hCg hg hmesh η i a b hadm
  have hk := CellNormalizerBounds.lower_div_upper_eq_kappa β₀ Cg kernelConstant
    (mesh_pos hmesh) (lt_of_lt_of_le (by omega : 0 < (1 : ℕ)) (radius_one_le β₀))
  dsimp only at h ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh := h.1
    rwa [hk] at hh
  · have hh := h.2.1
    rwa [hk] at hh
  · have hh := h.2.2.1
    rwa [hk] at hh
  · rw [← hk, inv_div]
    exact h.2.2.2

theorem cell_absoluteContinuous_edge_left {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (r : Fin 2) :
    meshCellMeasure J hJ a ≪ edgeCellMeasure J hJ a r :=
  (Measure.AbsolutelyContinuous.rfl.add_right (meshCellMeasure J hJ (nextCell J hJ a r))).smul_right
    (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ 0)

theorem cell_absoluteContinuous_edge_right {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (r : Fin 2) :
    meshCellMeasure J hJ (nextCell J hJ a r) ≪ edgeCellMeasure J hJ a r :=
  (Measure.AbsolutelyContinuous.rfl.add_right' (meshCellMeasure J hJ a)).smul_right
    (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ 0)

theorem edge_normalizer_eq_average {n J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (r : Fin 2)
    (β : ℝ) (Y : Configuration n)
    (ha : Integrable (OneCoordinateConditionals.sourceWeight β Y) (meshCellMeasure J hJ a))
    (hb : Integrable (OneCoordinateConditionals.sourceWeight β Y)
      (meshCellMeasure J hJ (nextCell J hJ a r))) :
    (∫ z, OneCoordinateConditionals.sourceWeight β Y z ∂edgeCellMeasure J hJ a r) =
      (cellNormalizer hJ a β Y + cellNormalizer hJ (nextCell J hJ a r) β Y) / 2 := by
  rw [edgeCellMeasure, integral_smul_measure, integral_add_measure ha hb]
  norm_num [cellNormalizer, smul_eq_mul]; ring

theorem edgeCellMeasure_restrict_first {J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (a : MeshIndex J) (r : Fin 2) :
    (edgeCellMeasure J hJ a r).restrict (meshCell J hJ a) =
      (2 : ℝ≥0∞)⁻¹ • meshCellMeasure J hJ a := by
  rw [edgeCellMeasure, Measure.restrict_smul, Measure.restrict_add]
  have ha : (meshCellMeasure J hJ a).restrict (meshCell J hJ a) = meshCellMeasure J hJ a :=
    Measure.restrict_eq_self_of_ae_mem (ae_mem_meshCell J hJ a)
  have hb : (meshCellMeasure J hJ (nextCell J hJ a r)).restrict (meshCell J hJ a) = 0 := by
    rw [meshCellMeasure, Measure.restrict_smul,
      Measure.restrict_restrict (measurableSet_meshCell J hJ a),
      Set.disjoint_iff_inter_eq_empty.mp (disjoint_edgeCells J hJ hJ2 a r)]
    simp only [Measure.restrict_empty, smul_zero]
  rw [ha, hb, add_zero]

/-- Exact crossing probability of the actual conditional kernel. The
finite positive denominator is part of LawBounds, not an assumed formula. -/
theorem conditional_crossing_eq {n J : ℕ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (β β₀ : ℝ) (i : Fin (n + 1)) (Y : Configuration n) (a : MeshIndex J) (r : Fin 2)
    (ha : LawBounds hJ β₀ β i Y a .cell)
    (hb : LawBounds hJ β₀ β i Y (nextCell J hJ a r) .cell)
    (he : LawBounds hJ β₀ β i Y a (.edge r)) :
    (conditionalKernel (edgeCellMeasure J hJ a r) i β Y (meshCell J hJ a)).toReal =
      cellNormalizer hJ a β Y /
        (cellNormalizer hJ a β Y + cellNormalizer hJ (nextCell J hJ a r) β Y) := by
  let Z : ℝ := ∫ z, OneCoordinateConditionals.sourceWeight β Y z ∂edgeCellMeasure J hJ a r
  have hZ : 0 < Z := he.regular_normalizer_pos
  have hm : pointLaw (edgeCellMeasure J hJ a r) Y (fun _ ↦ β / (n + 1 : ℕ))
      (meshCell J hJ a) = (2 : ℝ≥0∞)⁻¹ *
        (cellMass hJ a β Y * (ENNReal.ofReal Z)⁻¹) := by
    rw [pointLaw, withDensity_apply _ (measurableSet_meshCell J hJ a)]
    change (∫⁻ z, ENNReal.ofReal (OneCoordinateConditionals.sourceWeight β Y z / Z)
      ∂(edgeCellMeasure J hJ a r).restrict (meshCell J hJ a)) = _
    rw [edgeCellMeasure_restrict_first hJ hJ2 a r, lintegral_smul_measure, smul_eq_mul]
    simp_rw [ENNReal.ofReal_div_of_pos hZ, div_eq_mul_inv]
    congr 1
    exact lintegral_mul_const _ (measurable_sourceWeight β Y).ennreal_ofReal
  have hZe : Z = (cellNormalizer hJ a β Y +
      cellNormalizer hJ (nextCell J hJ a r) β Y) / 2 :=
    edge_normalizer_eq_average hJ a r β Y ha.regular_integrable hb.regular_integrable
  have hsum : 0 < cellNormalizer hJ a β Y +
      cellNormalizer hJ (nextCell J hJ a r) β Y :=
    add_pos ha.regular_normalizer_pos hb.regular_normalizer_pos
  have hreal := congrArg ENNReal.toReal hm
  rw [cellMass_eq_ofReal hJ a β Y ha.regular_integrable] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (cellNormalizer_nonneg hJ a β Y), ENNReal.toReal_ofReal hZ.le,
    ENNReal.toReal_ofNat] at hreal
  have hk : conditionalKernel (edgeCellMeasure J hJ a r) i β Y =
      pointLaw (edgeCellMeasure J hJ a r) Y (fun _ ↦ β / (n + 1 : ℕ)) :=
    he.kernel_eq_pointLaw
  rw [hk]
  calc
    _ = (2 : ℝ)⁻¹ * (cellNormalizer hJ a β Y * Z⁻¹) := hreal
    _ = _ := by rw [hZe]; field_simp [hsum.ne']

/-- Real algebra, with every denominator positive, converting the
probability of the first cell into the second-to-first normalizer ratio. -/
theorem ratio_bounds_of_crossing {A B c : ℝ} (hA : 0 < A) (hB : 0 < B) (hc : 0 < c)
    (hcross : c / 2 ≤ A / (A + B) ∧ A / (A + B) ≤ 1 - c / 2) :
    c ≤ 1 ∧ c / (2 - c) ≤ B / A ∧ B / A ≤ (2 - c) / c := by
  have hc1 : c ≤ 1 := by linarith [hcross.1.trans hcross.2]
  have hsum : 0 < A + B := add_pos hA hB
  have hlo := (le_div_iff₀ hsum).mp hcross.1
  have hhi := (div_le_iff₀ hsum).mp hcross.2
  have h2c : 0 < 2 - c := by linarith
  exact ⟨hc1, (div_le_div_iff₀ h2c hA).mpr (by nlinarith),
    (div_le_div_iff₀ hA hc).mpr (by nlinarith)⟩

/-- Literal source I_a/(I_a+I_b), with normalized-cell factors canceled.
Closed and coincident fixed source placements are allowed. -/
theorem adjacent_source_crossing {n J : ℕ} {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r)
    (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y) :
    let hJ := mesh_pos hmesh
    let b := nextCell J hJ a r
    Integrable (OneCoordinateConditionals.sourceWeight β Y) (meshCellMeasure J hJ a) ∧
      Integrable (OneCoordinateConditionals.sourceWeight β Y) (meshCellMeasure J hJ b) ∧
      0 < cellNormalizer hJ a β Y ∧ 0 < cellNormalizer hJ b β Y ∧
      lowerBound β₀ / 2 ≤ cellNormalizer hJ a β Y /
        (cellNormalizer hJ a β Y + cellNormalizer hJ b β Y) ∧
      cellNormalizer hJ a β Y / (cellNormalizer hJ a β Y + cellNormalizer hJ b β Y) ≤
        1 - lowerBound β₀ / 2 := by
  let hJ := mesh_pos hmesh
  let b := nextCell J hJ a r
  have hYa : PrescribedOutside hJ (Function.update η i a) i Y :=
    (prescribedOutside_update_iff hJ η i a Y).mpr hY
  have ha := capped_patch_law hJ hβ hβ₀ hδ hmesh (Function.update η i a) hadm.1 i Y hYa a .cell
  have hb := capped_patch_law hJ hβ hβ₀ hδ hmesh (Function.update η i a) hadm.1 i Y hYa b .cell
  have he := capped_patch_law hJ hβ hβ₀ hδ hmesh (Function.update η i a) hadm.1 i Y hYa a (.edge r)
  let Z : ℝ := ∫ z, OneCoordinateConditionals.sourceWeight β Y z ∂edgeCellMeasure J hJ a r
  have hZ : 0 < Z := he.regular_normalizer_pos
  have hlower : ∀ᵐ z ∂edgeCellMeasure J hJ a r,
      lowerBound β₀ ≤ OneCoordinateConditionals.sourceWeight β Y z / Z := by
    filter_upwards [he.density_lower,
      pointDensity_ae_rawDensity hJ (mesh_two_le hmesh) a (.edge r) β Y] with z hz hze
    change lowerBound β₀ ≤ pointDensity (edgeCellMeasure J hJ a r) Y
      (fun _ ↦ β / (n + 1 : ℕ)) z
    have hze' : pointDensity (edgeCellMeasure J hJ a r) Y
        (fun _ ↦ β / (n + 1 : ℕ)) z = rawDensity (edgeCellMeasure J hJ a r) β Y z := hze
    rw [hze']
    exact hz
  have hla : lowerBound β₀ ≤ cellNormalizer hJ a β Y / Z := by
    have h := integral_mono_ae (μ := meshCellMeasure J hJ a) (integrable_const (lowerBound β₀))
      (ha.regular_integrable.div_const Z) ((cell_absoluteContinuous_edge_left hJ a r).ae_le hlower)
    simpa only [cellNormalizer, integral_div, integral_const, probReal_univ, one_smul] using h
  have hlb : lowerBound β₀ ≤ cellNormalizer hJ b β Y / Z := by
    have h := integral_mono_ae (μ := meshCellMeasure J hJ b) (integrable_const (lowerBound β₀))
      (hb.regular_integrable.div_const Z) ((cell_absoluteContinuous_edge_right hJ a r).ae_le hlower)
    simpa only [cellNormalizer, integral_div, integral_const, probReal_univ, one_smul] using h
  have hZe : Z = (cellNormalizer hJ a β Y + cellNormalizer hJ b β Y) / 2 :=
    edge_normalizer_eq_average hJ a r β Y ha.regular_integrable hb.regular_integrable
  have hsum : 0 < cellNormalizer hJ a β Y + cellNormalizer hJ b β Y :=
    add_pos ha.regular_normalizer_pos hb.regular_normalizer_pos
  have hla' := (le_div_iff₀ hZ).mp hla
  have hlb' := (le_div_iff₀ hZ).mp hlb
  rw [hZe] at hla' hlb'
  exact ⟨ha.regular_integrable, hb.regular_integrable,
    ha.regular_normalizer_pos, hb.regular_normalizer_pos,
    (le_div_iff₀ hsum).mpr (by nlinarith), (div_le_iff₀ hsum).mpr (by nlinarith)⟩

theorem adjacent_source_ratio {n J : ℕ} {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r)
    (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y) :
    let hJ := mesh_pos hmesh
    let b := nextCell J hJ a r
    lowerBound β₀ ≤ 1 ∧
      lowerBound β₀ / (2 - lowerBound β₀) ≤ cellNormalizer hJ b β Y / cellNormalizer hJ a β Y ∧
      cellNormalizer hJ b β Y / cellNormalizer hJ a β Y ≤ (2 - lowerBound β₀) / lowerBound β₀ := by
  have h := adjacent_source_crossing hβ hβ₀ hδ hmesh η i a r hadm Y hY
  exact ratio_bounds_of_crossing h.2.2.1 h.2.2.2.1 (lowerBound_pos β₀) h.2.2.2.2

theorem adjacent_conditional_crossing {n J : ℕ} {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r)
    (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y) :
    let hJ := mesh_pos hmesh
    let p := (conditionalKernel (edgeCellMeasure J hJ a r) i β Y (meshCell J hJ a)).toReal
    lowerBound β₀ / 2 ≤ p ∧ p ≤ 1 - lowerBound β₀ / 2 := by
  let hJ := mesh_pos hmesh
  have hYa := (prescribedOutside_update_iff hJ η i a Y).mpr hY
  have ha := capped_patch_law hJ hβ hβ₀ hδ hmesh (Function.update η i a) hadm.1 i Y hYa a .cell
  have hb := capped_patch_law hJ hβ hβ₀ hδ hmesh (Function.update η i a) hadm.1 i Y hYa
    (nextCell J hJ a r) .cell
  have he := capped_patch_law hJ hβ hβ₀ hδ hmesh (Function.update η i a) hadm.1 i Y hYa a (.edge r)
  dsimp only
  rw [conditional_crossing_eq hJ (mesh_two_le hmesh) β β₀ i Y a r ha hb he]
  exact (adjacent_source_crossing hβ hβ₀ hδ hmesh η i a r hadm Y hY).2.2.2.2

/-- Source neighboring-label ratio for the actual specified-label masses.
Both endpoint caps and the full source parameter range remain explicit. -/
theorem adjacent_label_ratio {n J : ℕ} (hn : 2 ≤ n + 1) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (_hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r) :
    let hJ := mesh_pos hmesh
    let b := nextCell J hJ a r
    let p := (labelProbability hJ (Function.update η i a) β).toReal
    let q := (labelProbability hJ (Function.update η i b) β).toReal
    lowerBound β₀ ≤ 1 ∧
      lowerBound β₀ / (2 - lowerBound β₀) ≤ q / p ∧
      q / p ≤ (2 - lowerBound β₀) / lowerBound β₀ := by
  let hJ := mesh_pos hmesh
  let b := nextCell J hJ a r
  obtain ⟨Y₀, hY₀⟩ := (ae_prescribedOutside hJ η i).exists
  have hc1 := (adjacent_source_ratio hβ hβ₀ hδ hmesh η i a r hadm Y₀ hY₀).1
  have hc : 0 < lowerBound β₀ := lowerBound_pos β₀
  have h2c : 0 < 2 - lowerBound β₀ := by linarith
  have hlo := labelRatio_lower_of_normalizer_comparison hJ hn η i a b hβ (hβ₀.trans_lt hsub)
    (div_nonneg hc.le h2c.le) (by
      intro Y hY
      have h := adjacent_source_crossing hβ hβ₀ hδ hmesh η i a r hadm Y hY
      have hratio := (ratio_bounds_of_crossing h.2.2.1 h.2.2.2.1 hc h.2.2.2.2).2.1
      exact ⟨h.1, h.2.1, (le_div_iff₀ h.2.2.1).mp hratio⟩)
  have hrev := labelRatio_lower_of_normalizer_comparison hJ hn η i b a hβ (hβ₀.trans_lt hsub)
    (div_nonneg hc.le h2c.le) (by
      intro Y hY
      have h := adjacent_source_crossing hβ hβ₀ hδ hmesh η i a r hadm Y hY
      have hratio := (ratio_bounds_of_crossing h.2.2.1 h.2.2.2.1 hc h.2.2.2.2).2.2
      have hh := (div_le_div_iff₀ h.2.2.1 hc).mp hratio
      refine ⟨h.2.1, h.1, ?_⟩
      calc
        _ = lowerBound β₀ * cellNormalizer hJ b β Y / (2 - lowerBound β₀) := by ring
        _ ≤ _ := (div_le_iff₀ h2c).mpr (by nlinarith))
  have hp : 0 < (labelProbability hJ (Function.update η i a) β).toReal :=
    ENNReal.toReal_pos (labelProbability_ne_zero hJ hn _ hβ (hβ₀.trans_lt hsub))
      (labelProbability_ne_top hJ hn _ hβ (hβ₀.trans_lt hsub))
  have hq : 0 < (labelProbability hJ (Function.update η i b) β).toReal :=
    ENNReal.toReal_pos (labelProbability_ne_zero hJ hn _ hβ (hβ₀.trans_lt hsub))
      (labelProbability_ne_top hJ hn _ hβ (hβ₀.trans_lt hsub))
  refine ⟨hc1, hlo, (div_le_div_iff₀ hp hc).mpr ?_⟩
  nlinarith [(div_le_div_iff₀ h2c hq).mp hrev]

theorem crossing_of_ratio_bounds {p q c : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hlo : c / (2 - c) ≤ q / p) (hhi : q / p ≤ (2 - c) / c) :
    c / 2 ≤ p / (p + q) ∧ p / (p + q) ≤ 1 - c / 2 := by
  have h2c : 0 < 2 - c := by linarith
  have hlo' := (div_le_div_iff₀ h2c hp).mp hlo
  have hhi' := (div_le_div_iff₀ hp hc).mp hhi
  exact ⟨(le_div_iff₀ (add_pos hp hq)).mpr (by nlinarith),
    (div_le_iff₀ (add_pos hp hq)).mpr (by nlinarith)⟩

theorem ratio_bounds_symm {p q c : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hlo : c / (2 - c) ≤ p / q) (hhi : p / q ≤ (2 - c) / c) :
    c / (2 - c) ≤ q / p ∧ q / p ≤ (2 - c) / c := by
  have h2c : 0 < 2 - c := by linarith
  have hlo' := (div_le_div_iff₀ h2c hq).mp hlo
  have hhi' := (div_le_div_iff₀ hq hc).mp hhi
  exact ⟨(div_le_div_iff₀ h2c hp).mpr (by nlinarith),
    (div_le_div_iff₀ hp hc).mpr (by nlinarith)⟩

/-- Unoriented adjacency includes either coordinate direction and every
periodic wrap. Both prescribed endpoint completions are retained. -/
theorem edgeAdjacent_label_ratio {n J : ℕ} (hn : 2 ≤ n + 1) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a b : MeshIndex J)
    (he : EdgeAdjacent J (mesh_pos hmesh) a b)
    (hadm : TwoEndpointAdmissible δ η i a b) :
    let hJ := mesh_pos hmesh
    let p := (labelProbability hJ (Function.update η i a) β).toReal
    let q := (labelProbability hJ (Function.update η i b) β).toReal
    lowerBound β₀ ≤ 1 ∧
      lowerBound β₀ / (2 - lowerBound β₀) ≤ q / p ∧
      q / p ≤ (2 - lowerBound β₀) / lowerBound β₀ := by
  obtain ⟨r, hr | hr⟩ := he
  · subst b
    exact adjacent_label_ratio hn hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm
  · subst a
    have h := adjacent_label_ratio hn hβ hβ₀ hsub hδ₀ hδ hmesh η i b r hadm.symm
    have hp : 0 < (labelProbability (mesh_pos hmesh)
        (Function.update η i (nextCell J (mesh_pos hmesh) b r)) β).toReal :=
      ENNReal.toReal_pos (labelProbability_ne_zero (mesh_pos hmesh) hn _ hβ (hβ₀.trans_lt hsub))
        (labelProbability_ne_top (mesh_pos hmesh) hn _ hβ (hβ₀.trans_lt hsub))
    have hq : 0 < (labelProbability (mesh_pos hmesh) (Function.update η i b) β).toReal :=
      ENNReal.toReal_pos (labelProbability_ne_zero (mesh_pos hmesh) hn _ hβ (hβ₀.trans_lt hsub))
        (labelProbability_ne_top (mesh_pos hmesh) hn _ hβ (hβ₀.trans_lt hsub))
    exact ⟨h.1, ratio_bounds_symm hp hq (lowerBound_pos β₀) h.1 h.2.1 h.2.2⟩

theorem update_eq_of_agree_off_site {N J : ℕ} (η ζ : LabelVector J N) (i : Fin N)
    (h : ∀ k, k ≠ i → ζ k = η k) : Function.update η i (ζ i) = ζ := by
  classical
  funext k
  by_cases hk : k = i
  · subst k
    exact Function.update_self i (ζ i) η
  · rw [Function.update_of_ne hk]
    exact (h k hk).symm

/-- Literal arbitrary-cell statement for any N≥2 and two specified
label vectors agreeing off one coordinate. Distinctness is unnecessary. -/
theorem specified_label_ratio {N J : ℕ} (hN : 2 ≤ N)
    {β β₀ δ Cg : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hCg : 0 ≤ Cg) (hg : ∀ z : Torus, -Cg ≤ regularGreenRepresentative z)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η ζ : LabelVector J N) (hη : OccupationCap δ η) (hζ : OccupationCap δ ζ)
    (i : Fin N) (hi : ∀ k, k ≠ i → ζ k = η k) :
    let κ := CellNormalizerBounds.kappaConstant β₀ Cg kernelConstant J (radius β₀)
    let q := (labelProbability (mesh_pos hmesh) ζ β).toReal /
      (labelProbability (mesh_pos hmesh) η β).toReal
    0 < κ ∧ κ ≤ 1 ∧ κ ≤ q ∧ q ≤ κ⁻¹ := by
  cases N with
  | zero => omega
  | succ n =>
    have hu := update_eq_of_agree_off_site η ζ i hi
    have hadm : TwoEndpointAdmissible δ η i (η i) (ζ i) := by
      simpa only [TwoEndpointAdmissible, complete, Function.update_eq_self, hu] using And.intro hη hζ
    have h := arbitrary_label_ratio hN hβ hβ₀ hsub hδ₀ hδ hCg hg hmesh η i (η i) (ζ i) hadm
    simpa only [Function.update_eq_self, hu] using h

theorem specified_adjacent_label_ratio {N J : ℕ} (hN : 2 ≤ N) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η ζ : LabelVector J N) (hη : OccupationCap δ η) (hζ : OccupationCap δ ζ)
    (i : Fin N) (hi : ∀ k, k ≠ i → ζ k = η k)
    (he : EdgeAdjacent J (mesh_pos hmesh) (η i) (ζ i)) :
    let q := (labelProbability (mesh_pos hmesh) ζ β).toReal /
      (labelProbability (mesh_pos hmesh) η β).toReal
    lowerBound β₀ ≤ 1 ∧ lowerBound β₀ / (2 - lowerBound β₀) ≤ q ∧
      q ≤ (2 - lowerBound β₀) / lowerBound β₀ := by
  cases N with
  | zero => omega
  | succ n =>
    have hu := update_eq_of_agree_off_site η ζ i hi
    have hadm : TwoEndpointAdmissible δ η i (η i) (ζ i) := by
      simpa only [TwoEndpointAdmissible, complete, Function.update_eq_self, hu] using And.intro hη hζ
    have h := edgeAdjacent_label_ratio hN hβ hβ₀ hsub hδ₀ hδ hmesh η i (η i) (ζ i) he hadm
    simpa only [Function.update_eq_self, hu] using h

/-- The crossing range for the actual Gibbs mixture coefficient p. -/
theorem adjacent_mixing_range {n J : ℕ} (hn : 2 ≤ n + 1) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r) :
    let p := (twoCellMixingWeight (mesh_pos hmesh) η i a
      (nextCell J (mesh_pos hmesh) a r) β).toReal
    lowerBound β₀ / 2 ≤ p ∧ p ≤ 1 - lowerBound β₀ / 2 := by
  have h := adjacent_label_ratio hn hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm
  have hp0 := labelProbability_ne_zero (mesh_pos hmesh) hn (Function.update η i a)
    hβ (hβ₀.trans_lt hsub)
  have hpt := labelProbability_ne_top (mesh_pos hmesh) hn (Function.update η i a)
    hβ (hβ₀.trans_lt hsub)
  have hq0 := labelProbability_ne_zero (mesh_pos hmesh) hn
    (Function.update η i (nextCell J (mesh_pos hmesh) a r)) hβ (hβ₀.trans_lt hsub)
  have hqt := labelProbability_ne_top (mesh_pos hmesh) hn
    (Function.update η i (nextCell J (mesh_pos hmesh) a r)) hβ (hβ₀.trans_lt hsub)
  have hh := crossing_of_ratio_bounds (ENNReal.toReal_pos hp0 hpt) (ENNReal.toReal_pos hq0 hqt)
    (lowerBound_pos β₀) h.1 h.2.1 h.2.2
  simpa only [twoCellMixingWeight, ENNReal.toReal_div, ENNReal.toReal_add hpt hqt] using hh

theorem edgeAdjacent_mixing_range {n J : ℕ} (hn : 2 ≤ n + 1) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a b : MeshIndex J)
    (he : EdgeAdjacent J (mesh_pos hmesh) a b)
    (hadm : TwoEndpointAdmissible δ η i a b) :
    let p := (twoCellMixingWeight (mesh_pos hmesh) η i a b β).toReal
    lowerBound β₀ / 2 ≤ p ∧ p ≤ 1 - lowerBound β₀ / 2 := by
  have h := edgeAdjacent_label_ratio hn hβ hβ₀ hsub hδ₀ hδ hmesh η i a b he hadm
  have hp0 := labelProbability_ne_zero (mesh_pos hmesh) hn (Function.update η i a)
    hβ (hβ₀.trans_lt hsub)
  have hpt := labelProbability_ne_top (mesh_pos hmesh) hn (Function.update η i a)
    hβ (hβ₀.trans_lt hsub)
  have hq0 := labelProbability_ne_zero (mesh_pos hmesh) hn (Function.update η i b)
    hβ (hβ₀.trans_lt hsub)
  have hqt := labelProbability_ne_top (mesh_pos hmesh) hn (Function.update η i b)
    hβ (hβ₀.trans_lt hsub)
  have hh := crossing_of_ratio_bounds (ENNReal.toReal_pos hp0 hpt) (ENNReal.toReal_pos hq0 hqt)
    (lowerBound_pos β₀) h.1 h.2.1 h.2.2
  simpa only [twoCellMixingWeight, ENNReal.toReal_div, ENNReal.toReal_add hpt hqt] using hh

/-- The natural-valued profile n-e_a+e_b, with the subtraction performed
before the addition. Source uses require n_a≥1. -/
def moveOccupation {J : ℕ} (m : MeshIndex J → ℕ) (a b : MeshIndex J) : MeshIndex J → ℕ :=
  fun c ↦ m c - (if a = c then 1 else 0) + (if b = c then 1 else 0)

theorem occupation_eq_one_site_add {N J : ℕ} (η : LabelVector J N) (i : Fin N)
    (c : MeshIndex J) :
    occupation η c = (if η i = c then 1 else 0) +
      ∑ j ∈ Finset.univ.erase i, if η j = c then 1 else 0 := by
  classical
  rw [occupation, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact (Finset.add_sum_erase Finset.univ (fun j ↦ if η j = c then (1 : ℕ) else 0)
    (Finset.mem_univ i)).symm

theorem occupation_update {N J : ℕ} (η : LabelVector J N) (i : Fin N) (a b : MeshIndex J)
    (hia : η i = a) :
    occupation (Function.update η i b) = moveOccupation (occupation η) a b := by
  classical
  funext c
  have hη := occupation_eq_one_site_add η i c
  have hζ := occupation_eq_one_site_add (Function.update η i b) i c
  have hs : (∑ j ∈ Finset.univ.erase i, if Function.update η i b j = c then (1 : ℕ) else 0) =
      ∑ j ∈ Finset.univ.erase i, if η j = c then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [Function.update_self, hs] at hζ
  rw [hia] at hη
  change occupation (Function.update η i b) c =
    occupation η c - (if a = c then 1 else 0) + (if b = c then 1 else 0)
  by_cases hac : a = c <;> by_cases hbc : b = c <;> simp only [hac, hbc, ite_true, ite_false] at * <;>
    omega

/-- Every source occupation move is realized by changing one actual
particle label, using the already proved realization of every total profile. -/
theorem exists_label_move {N J : ℕ} (m : MeshIndex J → ℕ) (hm : ∑ a, m a = N)
    (a b : MeshIndex J) (ha : 1 ≤ m a) :
    ∃ (η : LabelVector J N) (i : Fin N), occupation η = m ∧ η i = a ∧
      occupation (Function.update η i b) = moveOccupation m a b := by
  classical
  let η := OccupationProbability.labelOfProfile m hm
  have hη : occupation η = m := OccupationProbability.occupation_labelOfProfile m hm
  have hcard : 1 ≤ (Finset.univ.filter fun i ↦ η i = a).card := by
    change 1 ≤ occupation η a
    rw [hη]
    exact ha
  obtain ⟨i, hi⟩ := Finset.one_le_card.mp hcard
  have hia : η i = a := (Finset.mem_filter.mp hi).2
  refine ⟨η, i, hη, hia, ?_⟩
  rw [occupation_update η i a b hia, hη]

theorem profile_ratio_eq_label_ratio {N J : ℕ} (hJ : 0 < J)
    {η : LabelVector J N} {m : MeshIndex J → ℕ} (hη : occupation η = m)
    (i : Fin N) (a b : MeshIndex J) (hia : η i = a) (β : ℝ) :
    (OccupationProbability.profileWeight (N := N) hJ (moveOccupation m a b) β).toReal /
        (OccupationProbability.profileWeight (N := N) hJ m β).toReal =
      (labelProbability hJ (Function.update η i b) β).toReal /
        (labelProbability hJ (Function.update η i a) β).toReal := by
  have hua : Function.update η i a = η := by
    rw [← hia, Function.update_eq_self]
  rw [hua, OccupationProbability.labelProbability_eq_profileWeight hJ η β,
    OccupationProbability.labelProbability_eq_profileWeight hJ (Function.update η i b) β,
    occupation_update η i a b hia, hη]

theorem arbitrary_profile_ratio {N J : ℕ} (hN : 2 ≤ N) {β β₀ δ Cg : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hCg : 0 ≤ Cg) (hg : ∀ z : Torus, -Cg ≤ regularGreenRepresentative z)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (m : MeshIndex J → ℕ) (a b : MeshIndex J) (ha : 1 ≤ m a)
    (hm : m ∈ cappedOccupations J N δ)
    (hm' : moveOccupation m a b ∈ cappedOccupations J N δ) :
    let κ := CellNormalizerBounds.kappaConstant β₀ Cg kernelConstant J (radius β₀)
    let q := (OccupationProbability.profileWeight (N := N) (mesh_pos hmesh)
      (moveOccupation m a b) β).toReal /
      (OccupationProbability.profileWeight (N := N) (mesh_pos hmesh) m β).toReal
    0 < κ ∧ κ ≤ 1 ∧ κ ≤ q ∧ q ≤ κ⁻¹ := by
  cases N with
  | zero => omega
  | succ n =>
    obtain ⟨η, i, hη, hia, hζ⟩ := exists_label_move m hm.1 a b ha
    have hηcap : OccupationCap δ η := by
      intro c
      simpa only [hη] using hm.2 c
    have hζcap : OccupationCap δ (Function.update η i b) := by
      intro c
      simpa only [hζ] using hm'.2 c
    have hua : Function.update η i a = η := by
      rw [← hia, Function.update_eq_self]
    have hadm : TwoEndpointAdmissible δ η i a b := by
      change OccupationCap δ (Function.update η i a) ∧ OccupationCap δ (Function.update η i b)
      exact ⟨hua.symm ▸ hηcap, hζcap⟩
    have h := arbitrary_label_ratio hN hβ hβ₀ hsub hδ₀ hδ hCg hg hmesh η i a b hadm
    simpa only [profile_ratio_eq_label_ratio (mesh_pos hmesh) hη i a b hia β] using h

/-- Q is the mass of one labeling. No factorial multiplicity is inserted
in this ratio, and the occupation-event probability is a different object. -/
theorem adjacent_profile_ratio {N J : ℕ} (hN : 2 ≤ N) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (m : MeshIndex J → ℕ) (a b : MeshIndex J) (ha : 1 ≤ m a)
    (hm : m ∈ cappedOccupations J N δ)
    (hm' : moveOccupation m a b ∈ cappedOccupations J N δ)
    (he : EdgeAdjacent J (mesh_pos hmesh) a b) :
    let q := (OccupationProbability.profileWeight (N := N) (mesh_pos hmesh)
      (moveOccupation m a b) β).toReal /
      (OccupationProbability.profileWeight (N := N) (mesh_pos hmesh) m β).toReal
    lowerBound β₀ ≤ 1 ∧ lowerBound β₀ / (2 - lowerBound β₀) ≤ q ∧
      q ≤ (2 - lowerBound β₀) / lowerBound β₀ := by
  cases N with
  | zero => omega
  | succ n =>
    obtain ⟨η, i, hη, hia, hζ⟩ := exists_label_move m hm.1 a b ha
    have hηcap : OccupationCap δ η := by
      intro c
      simpa only [hη] using hm.2 c
    have hζcap : OccupationCap δ (Function.update η i b) := by
      intro c
      simpa only [hζ] using hm'.2 c
    have hua : Function.update η i a = η := by
      rw [← hia, Function.update_eq_self]
    have hadm : TwoEndpointAdmissible δ η i a b := by
      change OccupationCap δ (Function.update η i a) ∧ OccupationCap δ (Function.update η i b)
      exact ⟨hua.symm ▸ hηcap, hζcap⟩
    have h := edgeAdjacent_label_ratio hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a b he hadm
    simpa only [profile_ratio_eq_label_ratio (mesh_pos hmesh) hη i a b hia β] using h

@[simp] theorem cellNormalizer_zero {n J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    (Y : Configuration n) : cellNormalizer hJ a 0 Y = 1 := by
  simp only [cellNormalizer, sourceWeight_zero, integral_const, probReal_univ, one_smul]

theorem label_ratio_zero {N J : ℕ} (hJ : 0 < J) (η ζ : LabelVector J N) :
    (labelProbability hJ ζ 0).toReal / (labelProbability hJ η 0).toReal = 1 := by
  rw [labelProbability_zero_coupling, labelProbability_zero_coupling]
  exact div_self (ENNReal.toReal_pos
    (ENNReal.inv_ne_zero.mpr (labelScale_ne_top J N))
    (ENNReal.inv_ne_top.mpr (labelScale_ne_zero hJ N))).ne'

theorem profile_ratio_zero {N J : ℕ} (hJ : 0 < J)
    (m m' : MeshIndex J → ℕ) (hm : ∑ a, m a = N) (hm' : ∑ a, m' a = N) :
    (OccupationProbability.profileWeight (N := N) hJ m' 0).toReal /
      (OccupationProbability.profileWeight (N := N) hJ m 0).toReal = 1 := by
  simpa only [OccupationProbability.profileWeight, dite_eq_left hm, dite_eq_left hm'] using
    label_ratio_zero hJ (OccupationProbability.labelOfProfile m hm)
      (OccupationProbability.labelOfProfile m' hm')

theorem mixing_weight_zero {N J : ℕ} (hJ : 0 < J) (η : LabelVector J N) (i : Fin N)
    (a b : MeshIndex J) : (twoCellMixingWeight hJ η i a b 0).toReal = 1 / 2 := by
  have h0 : (labelScale J N)⁻¹ ≠ (0 : ℝ≥0∞) :=
    ENNReal.inv_ne_zero.mpr (labelScale_ne_top J N)
  have ht : (labelScale J N)⁻¹ ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.inv_ne_top.mpr (labelScale_ne_zero hJ N)
  have hp : 0 < ((labelScale J N)⁻¹).toReal := ENNReal.toReal_pos h0 ht
  rw [twoCellMixingWeight, labelProbability_zero_coupling, labelProbability_zero_coupling,
    ENNReal.toReal_div, ENNReal.toReal_add ht ht]
  field_simp [hp.ne']; ring

end PeriodicAttractiveLogGas.LabelRatioTransport
