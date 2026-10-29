import LeanResearch.PeriodicAttractiveLogGas.OccupationFieldApproximation
import LeanResearch.PeriodicAttractiveLogGas.LabelRatioTransport

/-! The specified-label partition transport in the occupation-rates proof.
All outside expectations use the actual omitted-coordinate marginal of the
original prescribed-label Gibbs law. The occupation weight is the existing
`OccupationProbability.profileWeight`, with no multinomial factor.
Central source-bound checks and source correspondence are recorded in the
associated development note.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace PeriodicAttractiveLogGas.OccupationPartitionTransport

open MeshCells MeshAdjacentCells LabelOccupations CellRestrictions GreenPointWeights
  OneCoordinateConditionals ConditionalLawEstimates GreenConditionalInfluence
  LabelRatioTransport OccupationProbability OccupationFieldApproximation OccupationFieldL2

theorem measurable_sourceWeight_joint {n : ℕ} (β : ℝ) :
    Measurable (fun p : Configuration n × Torus ↦ sourceWeight β p.1 p.2) := by
  apply Real.continuous_exp.measurable.comp
  exact Finset.measurable_sum _ fun j _ ↦
    (regularGreenRepresentative_measurable.comp
      (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))).const_mul _

theorem measurable_cellNormalizer {n J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (β : ℝ) :
    Measurable (cellNormalizer (n := n) hJ a β) :=
  (measurable_sourceWeight_joint β).stronglyMeasurable.integral_prod_right.measurable

theorem measurable_cellMass {n J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (β : ℝ) :
    Measurable (cellMass (n := n) hJ a β) :=
  (measurable_sourceWeight_joint β).ennreal_ofReal.lintegral_prod_right

theorem measurable_outsideWeight {n : ℕ} (β : ℝ) :
    Measurable (outsideWeight (n := n) β) :=
  ((measurable_pairEnergy regularGreenRepresentative_measurable n).const_mul _).exp

theorem label_density_ae_jointDensity {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) :
    greenWeightDensity (n + 1) β =ᵐ[labelReference hJ η] jointDensity (n + 1) β := by
  have hac : labelReference hJ η ≪ referenceMeasure (n + 1) := by
    rw [labelReference_eq]
    exact Measure.absolutelyContinuous_restrict.smul_left _
  filter_upwards [hac.ae_le
    (gibbsWeight_congr_ae_kernel regularGreenRepresentative_ae (n + 1) β)] with X hX
  exact congrArg ENNReal.ofReal hX.symm

theorem labelPartition_eq_productNormalizer {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) :
    labelPartitionFunction hJ η β =
      productNormalizer (fun j ↦ meshCellMeasure J hJ (η j)) β :=
  lintegral_congr_ae (label_density_ae_jointDensity hJ η β)

theorem labelGibbs_eq_productGibbs {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (β : ℝ) :
    labelGibbsMeasure hJ η β =
      productGibbs (fun j ↦ meshCellMeasure J hJ (η j)) β := by
  unfold labelGibbsMeasure productGibbs
  rw [labelPartition_eq_productNormalizer]
  congr 1
  exact withDensity_congr_ae (label_density_ae_jointDensity hJ η β)

theorem sectionMass_eq_common_factor {n J : ℕ} (hJ : 0 < J)
    (i : Fin (n + 1)) (a : MeshIndex J) (β : ℝ) (Y : Configuration n) :
    sectionMass (meshCellMeasure J hJ a) i β Y =
      ENNReal.ofReal (outsideWeight β Y) * cellMass hJ a β Y := by
  simp only [sectionMass, jointDensity_insertSite]
  exact lintegral_const_mul _ (measurable_sourceWeight β Y).ennreal_ofReal

/-- Exact density of the actual outside marginal. The outside weight keeps
the denominator n+1 from the original joint law. -/
theorem label_outsideMarginal_eq {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (β : ℝ) :
    Measure.map (removeSite i) (labelGibbsMeasure hJ η β) =
      (outsideReference (fun j ↦ meshCellMeasure J hJ (η j)) i).withDensity
        (fun Y ↦ (labelPartitionFunction hJ η β)⁻¹ *
          (ENNReal.ofReal (outsideWeight β Y) * cellMass hJ (η i) β Y)) := by
  rw [labelGibbs_eq_productGibbs]
  change outsideMarginal (fun j ↦ meshCellMeasure J hJ (η j)) i β = _
  rw [outsideMarginal_eq, ← labelPartition_eq_productNormalizer]
  simp only [sectionMass_eq_common_factor]

section ActualParameters

variable {n J : ℕ} (hN : 2 ≤ n + 1) {β₀ β δ : ℝ}
  (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
  (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
  (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)

include hβ hβ₀ hδ hη

/-- The finite positive source normalizers justify cancellation under the
outside reference measure before converting extended integrals to real ones. -/
theorem lintegral_cellNormalizer_ratio (i : Fin (n + 1)) (b : MeshIndex J) :
    (∫⁻ Y, ENNReal.ofReal (cellNormalizer (mesh_pos hmesh) b β Y /
      cellNormalizer (mesh_pos hmesh) (η i) β Y)
      ∂Measure.map (removeSite i) (labelGibbsMeasure (mesh_pos hmesh) η β)) =
      labelPartitionFunction (mesh_pos hmesh) (Function.update η i b) β /
        labelPartitionFunction (mesh_pos hmesh) η β := by
  let hJ := mesh_pos hmesh
  have hm : Measurable (fun Y : Configuration n ↦ ENNReal.ofReal
      (cellNormalizer hJ b β Y / cellNormalizer hJ (η i) β Y)) :=
    ((measurable_cellNormalizer hJ b β).div (measurable_cellNormalizer hJ (η i) β)).ennreal_ofReal
  have hd : Measurable (fun Y : Configuration n ↦ (labelPartitionFunction hJ η β)⁻¹ *
      (ENNReal.ofReal (outsideWeight β Y) * cellMass hJ (η i) β Y)) :=
    measurable_const.mul ((measurable_outsideWeight β).ennreal_ofReal.mul
      (measurable_cellMass hJ (η i) β))
  rw [label_outsideMarginal_eq, lintegral_withDensity_eq_lintegral_mul _ hd hm]
  calc
    _ = ∫⁻ Y, (labelPartitionFunction hJ η β)⁻¹ *
        (ENNReal.ofReal (outsideWeight β Y) * cellMass hJ b β Y)
        ∂outsideReference (fun j ↦ meshCellMeasure J hJ (η j)) i := by
      apply lintegral_congr_ae
      filter_upwards [ae_prescribedOutside hJ η i] with Y hY
      have ha := capped_patch_law hJ hβ hβ₀ hδ hmesh η hη i Y hY (η i) .cell
      have hb := capped_patch_law hJ hβ hβ₀ hδ hmesh η hη i Y hY b .cell
      have hapos : 0 < cellNormalizer hJ (η i) β Y := ha.regular_normalizer_pos
      dsimp only [Pi.mul_apply]
      rw [cellMass_eq_ofReal hJ (η i) β Y ha.regular_integrable,
        cellMass_eq_ofReal hJ b β Y hb.regular_integrable,
        ENNReal.ofReal_div_of_pos hapos, div_eq_mul_inv]
      have hA : ENNReal.ofReal (cellNormalizer hJ (η i) β Y) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr hapos).ne'
      calc
        _ = (labelPartitionFunction hJ η β)⁻¹ *
            (ENNReal.ofReal (outsideWeight β Y) * ENNReal.ofReal (cellNormalizer hJ b β Y)) *
            (ENNReal.ofReal (cellNormalizer hJ (η i) β Y) *
              (ENNReal.ofReal (cellNormalizer hJ (η i) β Y))⁻¹) := by
                simp only [mul_assoc, mul_left_comm, mul_comm]
        _ = _ := by rw [ENNReal.mul_inv_cancel hA ENNReal.ofReal_ne_top, mul_one]
    _ = (labelPartitionFunction hJ η β)⁻¹ *
        labelPartitionFunction hJ (Function.update η i b) β := by
      have hf : Measurable (fun Y : Configuration n ↦
          ENNReal.ofReal (outsideWeight β Y) * cellMass hJ b β Y) :=
        (measurable_outsideWeight β).ennreal_ofReal.mul (measurable_cellMass hJ b β)
      rw [lintegral_const_mul _ hf, labelPartition_eq_common_factor]
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

include hN hsub

theorem cellNormalizer_ratio_integrable (i : Fin (n + 1)) (b : MeshIndex J) :
    Integrable (fun Y ↦ cellNormalizer (mesh_pos hmesh) b β Y /
      cellNormalizer (mesh_pos hmesh) (η i) β Y)
      (Measure.map (removeSite i) (labelGibbsMeasure (mesh_pos hmesh) η β)) := by
  have hm := (measurable_cellNormalizer (n := n) (mesh_pos hmesh) b β).div
    (measurable_cellNormalizer (mesh_pos hmesh) (η i) β)
  apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Eventually.of_forall fun Y ↦ div_nonneg (cellNormalizer_nonneg _ _ _ Y)
      (cellNormalizer_nonneg _ _ _ Y))).mp
  dsimp only [Pi.div_apply]
  rw [lintegral_cellNormalizer_ratio hβ hβ₀ hδ hmesh η hη i b, div_eq_mul_inv]
  exact ENNReal.mul_ne_top
    (labelPartitionFunction_ne_top (mesh_pos hmesh) hN _ hβ (hβ₀.trans_lt hsub))
    (ENNReal.inv_ne_top.mpr (labelPartitionFunction_ne_zero (mesh_pos hmesh) η β))

/-- The first equality in source occupation-exact-ratio. Positivity and
integrability are derived from the capped one-site law on every target cell. -/
theorem label_partition_ratio_eq_outside_integral (i : Fin (n + 1)) (b : MeshIndex J) :
    (labelProbability (mesh_pos hmesh) (Function.update η i b) β).toReal /
        (labelProbability (mesh_pos hmesh) η β).toReal =
      ∫ Y, cellNormalizer (mesh_pos hmesh) b β Y /
        cellNormalizer (mesh_pos hmesh) (η i) β Y
        ∂Measure.map (removeSite i) (labelGibbsMeasure (mesh_pos hmesh) η β) := by
  rw [labelProbability_ratio_eq_partition_ratio (mesh_pos hmesh) hN _ _ hβ (hβ₀.trans_lt hsub)]
  have hi := cellNormalizer_ratio_integrable hN hβ hβ₀ hsub hδ hmesh η hη i b
  have hn : ∀ Y : Configuration n, 0 ≤ cellNormalizer (mesh_pos hmesh) b β Y /
      cellNormalizer (mesh_pos hmesh) (η i) β Y := fun Y ↦
    div_nonneg (cellNormalizer_nonneg _ _ _ Y) (cellNormalizer_nonneg _ _ _ Y)
  have he := ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)
  rw [lintegral_cellNormalizer_ratio hβ hβ₀ hδ hmesh η hη i b] at he
  have hr := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hn), ENNReal.toReal_div] using hr.symm

/-- Pointwise algebra for arbitrary outside tuples, including coincident
ones. All deterministic cell normalizers are positive, even on empty cells. -/
theorem cellNormalizer_ratio_eq_fieldNormalizer_ratio (i : Fin (n + 1))
    (a b : MeshIndex J) (Y : Configuration n) :
    cellNormalizer (mesh_pos hmesh) b β Y / cellNormalizer (mesh_pos hmesh) a β Y =
      (potentialCellNormalizer (mesh_pos hmesh) η β b /
        potentialCellNormalizer (mesh_pos hmesh) η β a) *
      (fieldNormalizer (mesh_pos hmesh) η β i b (insertSite i 0 Y) /
        fieldNormalizer (mesh_pos hmesh) η β i a (insertSite i 0 Y)) := by
  have ha := potentialCellNormalizer_pos hN hβ hβ₀ hsub hδ hmesh η hη a
  have hb := potentialCellNormalizer_pos hN hβ hβ₀ hsub hδ hmesh η hη b
  simp only [fieldNormalizer_eq_raw_integral, removeSite_insertSite,
    ← cellNormalizer_eq_raw]
  by_cases hc : cellNormalizer (mesh_pos hmesh) a β Y = 0
  · simp only [hc, mul_zero, div_zero]
  · field_simp [ha.ne', hb.ne', hc]

theorem fieldNormalizer_ratio_integrable (hlarge : 8 * β₀ ≤ (n + 1 : ℕ))
    (i : Fin (n + 1)) (a b : MeshIndex J) :
    Integrable (fun X ↦ fieldNormalizer (mesh_pos hmesh) η β i b X /
      fieldNormalizer (mesh_pos hmesh) η β i a X) (labelGibbsMeasure (mesh_pos hmesh) η β) := by
  let μ := labelGibbsMeasure (mesh_pos hmesh) η β
  let q := fun X ↦ fieldNormalizer (mesh_pos hmesh) η β i b X /
    fieldNormalizer (mesh_pos hmesh) η β i a X
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  have hm : Measurable q := (measurable_fieldNormalizer (mesh_pos hmesh) η β i b).div
    (measurable_fieldNormalizer (mesh_pos hmesh) η β i a)
  have he : Integrable (fun X ↦ ‖q X - 1‖) μ := by
    simpa only [Real.norm_eq_abs] using!
      (fieldNormalizer_ratio_error hN hβ hβ₀ hsub hδ hmesh η hη hlarge i a b).1
  have hs : Integrable (fun X ↦ q X - 1) μ :=
    (integrable_norm_iff (hm.sub measurable_const).aestronglyMeasurable).mp he
  have hh : Integrable (fun X ↦ (q X - 1) + 1) μ := hs.add (integrable_const (1 : ℝ))
  simpa only [sub_add_cancel, q, μ] using! hh

/-- Both integrability and the error pass to the actual outside law through
coordinate deletion; no smaller Gibbs law is introduced. -/
theorem fieldNormalizer_ratio_outside (hlarge : 8 * β₀ ≤ (n + 1 : ℕ))
    (i : Fin (n + 1)) (a b : MeshIndex J) :
    Integrable (fun Y ↦ fieldNormalizer (mesh_pos hmesh) η β i b (insertSite i 0 Y) /
      fieldNormalizer (mesh_pos hmesh) η β i a (insertSite i 0 Y))
      (Measure.map (removeSite i) (labelGibbsMeasure (mesh_pos hmesh) η β)) ∧
    Integrable (fun Y ↦ |fieldNormalizer (mesh_pos hmesh) η β i b (insertSite i 0 Y) /
      fieldNormalizer (mesh_pos hmesh) η β i a (insertSite i 0 Y) - 1|)
      (Measure.map (removeSite i) (labelGibbsMeasure (mesh_pos hmesh) η β)) ∧
    (∫ Y, |fieldNormalizer (mesh_pos hmesh) η β i b (insertSite i 0 Y) /
      fieldNormalizer (mesh_pos hmesh) η β i a (insertSite i 0 Y) - 1|
      ∂Measure.map (removeSite i) (labelGibbsMeasure (mesh_pos hmesh) η β)) ≤
      (2 * exponentialErrorConstant J β₀ / fieldNormalizerLower J β₀) / Real.sqrt (n + 1 : ℝ) := by
  let μ := labelGibbsMeasure (mesh_pos hmesh) η β
  let q := fun X ↦ fieldNormalizer (mesh_pos hmesh) η β i b X /
    fieldNormalizer (mesh_pos hmesh) η β i a X
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  have hm : Measurable q := (measurable_fieldNormalizer (mesh_pos hmesh) η β i b).div
    (measurable_fieldNormalizer (mesh_pos hmesh) η β i a)
  have hinv : ∀ X, q (insertSite i 0 (removeSite i X)) = q X := by
    intro X
    simp only [q, fieldNormalizer_insertSite_removeSite]
  have hEm : Measurable (fun X ↦ |q X - 1|) :=
    continuous_abs.measurable.comp (hm.sub measurable_const)
  have hEinv : ∀ X, |q (insertSite i 0 (removeSite i X)) - 1| = |q X - 1| :=
    fun X ↦ congrArg (fun r : ℝ ↦ |r - 1|) (hinv X)
  have hE := fieldNormalizer_ratio_error hN hβ hβ₀ hsub hδ hmesh η hη hlarge i a b
  refine ⟨integrable_removeSite_insertSite μ i q hm hinv
    (fieldNormalizer_ratio_integrable hN hβ hβ₀ hsub hδ hmesh η hη hlarge i a b),
    integrable_removeSite_insertSite μ i (fun X ↦ |q X - 1|) hEm hEinv hE.1, ?_⟩
  change (∫ Y, |q (insertSite i 0 Y) - 1| ∂Measure.map (removeSite i) μ) ≤ _
  rw [integral_removeSite_insertSite μ i (fun X ↦ |q X - 1|) hEm hEinv]
  exact hE.2

theorem fieldNormalizer_ratio_mean_error (hlarge : 8 * β₀ ≤ (n + 1 : ℕ))
    (i : Fin (n + 1)) (a b : MeshIndex J) :
    |(∫ Y, fieldNormalizer (mesh_pos hmesh) η β i b (insertSite i 0 Y) /
      fieldNormalizer (mesh_pos hmesh) η β i a (insertSite i 0 Y)
      ∂Measure.map (removeSite i) (labelGibbsMeasure (mesh_pos hmesh) η β)) - 1| ≤
        (2 * exponentialErrorConstant J β₀ / fieldNormalizerLower J β₀) /
          Real.sqrt (n + 1 : ℝ) := by
  let μ := labelGibbsMeasure (mesh_pos hmesh) η β
  let ρ := Measure.map (removeSite i) μ
  let q := fun Y ↦ fieldNormalizer (mesh_pos hmesh) η β i b (insertSite i 0 Y) /
    fieldNormalizer (mesh_pos hmesh) η β i a (insertSite i 0 Y)
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_labelGibbsMeasure (mesh_pos hmesh) hN η hβ (hβ₀.trans_lt hsub)
  let : IsProbabilityMeasure ρ := by
    constructor
    change Measure.map (removeSite i) μ univ = 1
    rw [Measure.map_apply (measurable_removeSite i) MeasurableSet.univ]
    simp
  have hq := fieldNormalizer_ratio_outside hN hβ hβ₀ hsub hδ hmesh η hη hlarge i a b
  have hh := norm_integral_le_integral_norm (μ := ρ) (fun Y ↦ q Y - 1)
  rw [integral_sub hq.1 (integrable_const 1), integral_const, probReal_univ, one_smul] at hh
  simp only [Real.norm_eq_abs] at hh
  exact hh.trans hq.2.2

/-- The second equality in source occupation-exact-ratio, keeping the
random quotient inside the expectation. -/
theorem label_partition_ratio_eq_normalizer_ratio (i : Fin (n + 1)) (b : MeshIndex J) :
    (labelProbability (mesh_pos hmesh) (Function.update η i b) β).toReal /
        (labelProbability (mesh_pos hmesh) η β).toReal =
      (potentialCellNormalizer (mesh_pos hmesh) η β b /
        potentialCellNormalizer (mesh_pos hmesh) η β (η i)) *
      ∫ Y, fieldNormalizer (mesh_pos hmesh) η β i b (insertSite i 0 Y) /
        fieldNormalizer (mesh_pos hmesh) η β i (η i) (insertSite i 0 Y)
        ∂Measure.map (removeSite i) (labelGibbsMeasure (mesh_pos hmesh) η β) := by
  rw [label_partition_ratio_eq_outside_integral hN hβ hβ₀ hsub hδ hmesh η hη]
  simp_rw [cellNormalizer_ratio_eq_fieldNormalizer_ratio hN hβ hβ₀ hsub hδ hmesh η hη i]
  rw [integral_const_mul]

theorem potentialCellNormalizer_ratio_eq_haar (a b : MeshIndex J) :
    potentialCellNormalizer (mesh_pos hmesh) η β b /
      potentialCellNormalizer (mesh_pos hmesh) η β a =
    (∫ z in meshCell J (mesh_pos hmesh) b, Real.exp (β * meanPotential (mesh_pos hmesh) η β z)
      ∂torusMeasure) /
    (∫ z in meshCell J (mesh_pos hmesh) a, Real.exp (β * meanPotential (mesh_pos hmesh) η β z)
      ∂torusMeasure) := by
  have hJ0 : (J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (mesh_pos hmesh))
  have ha := (potential_haar_cell_normalizer hN hβ hβ₀ hsub hδ hmesh η hη a).2.1
  rw [potentialCellNormalizer_eq_haar, potentialCellNormalizer_eq_haar]
  field_simp [hJ0, ha.ne']

/-- The literal occupation profile probability is already well-defined
by permutation invariance. It is the mass of one specified labeling. -/
theorem profile_partition_ratio_eq_outside (i : Fin (n + 1)) (b : MeshIndex J) :
    (profileWeight (N := n + 1) (mesh_pos hmesh)
      (moveOccupation (occupation η) (η i) b) β).toReal /
      (profileWeight (N := n + 1) (mesh_pos hmesh) (occupation η) β).toReal =
    (∫ z in meshCell J (mesh_pos hmesh) b, Real.exp (β * meanPotential (mesh_pos hmesh) η β z)
      ∂torusMeasure) /
    (∫ z in meshCell J (mesh_pos hmesh) (η i), Real.exp (β * meanPotential (mesh_pos hmesh) η β z)
      ∂torusMeasure) *
      ∫ Y, fieldNormalizer (mesh_pos hmesh) η β i b (insertSite i 0 Y) /
        fieldNormalizer (mesh_pos hmesh) η β i (η i) (insertSite i 0 Y)
        ∂Measure.map (removeSite i) (labelGibbsMeasure (mesh_pos hmesh) η β) := by
  rw [profile_ratio_eq_label_ratio (mesh_pos hmesh) rfl i (η i) b rfl β,
    Function.update_eq_self,
    label_partition_ratio_eq_normalizer_ratio hN hβ hβ₀ hsub hδ hmesh η hη,
    potentialCellNormalizer_ratio_eq_haar hN hβ hβ₀ hsub hδ hmesh η hη]

theorem label_partition_ratio_eq_raw_outside (i : Fin (n + 1)) (b : MeshIndex J) :
    (labelProbability (mesh_pos hmesh) (Function.update η i b) β).toReal /
        (labelProbability (mesh_pos hmesh) η β).toReal =
      ∫ Y, (∫ z in meshCell J (mesh_pos hmesh) b,
        Real.exp (β * OccupationPositiveExponential.psi i z (insertSite i 0 Y)) ∂torusMeasure) /
        (∫ z in meshCell J (mesh_pos hmesh) (η i),
        Real.exp (β * OccupationPositiveExponential.psi i z (insertSite i 0 Y)) ∂torusMeasure)
        ∂Measure.map (removeSite i) (labelGibbsMeasure (mesh_pos hmesh) η β) := by
  rw [label_partition_ratio_eq_outside_integral hN hβ hβ₀ hsub hδ hmesh η hη]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro Y
  have hcell (a : MeshIndex J) : cellNormalizer (mesh_pos hmesh) a β Y =
      (J : ℝ) ^ 2 * ∫ z in meshCell J (mesh_pos hmesh) a,
        rawSourceWeight β Y z ∂torusMeasure := by
    rw [cellNormalizer_eq_raw]
    simp only [meshCellMeasure, integral_smul_measure, smul_eq_mul,
      ENNReal.toReal_pow, ENNReal.toReal_natCast]
  simp only [exp_psi_eq_rawSourceWeight, removeSite_insertSite]
  rw [hcell, hcell]
  have hJ0 : (J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (mesh_pos hmesh))
  by_cases ha : (∫ z in meshCell J (mesh_pos hmesh) (η i), rawSourceWeight β Y z ∂torusMeasure) = 0
  · simp only [ha, mul_zero, div_zero]
  · field_simp [hJ0, ha]

end ActualParameters

/-- Fixed-mesh constants are uniform in the particle number, prescribed
labels, chosen particles and cells, and beta in the full admitted interval. -/
def ratioErrorConstant (J : ℕ) (β₀ : ℝ) : ℝ :=
  2 * exponentialErrorConstant J β₀ / fieldNormalizerLower J β₀

def logarithmicRatioConstant (J : ℕ) (β₀ : ℝ) : ℝ := 2 * ratioErrorConstant J β₀

def ratioThreshold (J : ℕ) (β₀ : ℝ) : ℕ :=
  max (fieldThreshold β₀) ⌈(2 * ratioErrorConstant J β₀) ^ 2⌉₊

theorem ratioErrorConstant_nonneg (J : ℕ) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    0 ≤ ratioErrorConstant J β₀ :=
  div_nonneg (mul_nonneg (by norm_num) (exponentialErrorConstant_nonneg J hβ₀))
    (fieldNormalizerLower_pos J β₀).le

theorem logarithmicRatioConstant_nonneg (J : ℕ) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    0 ≤ logarithmicRatioConstant J β₀ :=
  mul_nonneg (by norm_num) (ratioErrorConstant_nonneg J hβ₀)

theorem ratioThreshold_bounds {N J : ℕ} {β₀ : ℝ} (hN : ratioThreshold J β₀ ≤ N) :
    2 ≤ N ∧ 8 * β₀ ≤ (N : ℝ) ∧ ratioErrorConstant J β₀ / Real.sqrt (N : ℝ) ≤ 1 / 2 := by
  have hf := fieldThreshold_bounds ((le_max_left _ _).trans hN)
  have hs : (2 * ratioErrorConstant J β₀) ^ 2 ≤ (N : ℝ) :=
    Nat.ceil_le.mp ((le_max_right _ _).trans hN)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hsq := Real.sq_sqrt hNr.le
  have hle : 2 * ratioErrorConstant J β₀ ≤ Real.sqrt (N : ℝ) := by nlinarith
  exact ⟨hf.1, hf.2, (div_le_iff₀ hsqrt).mpr (by linarith)⟩

/-- The elementary logarithmic estimate is proved on the actual interval
where the expected ratio lies; its positivity is a conclusion of that bound. -/
theorem abs_log_le_two_mul_abs_sub_one {q : ℝ} (hq : |q - 1| ≤ 1 / 2) :
    0 < q ∧ |Real.log q| ≤ 2 * |q - 1| := by
  have hhalf : (1 : ℝ) / 2 ≤ q := by linarith [(abs_le.mp hq).1]
  have hpos : 0 < q := by linarith
  have hup := Real.log_le_sub_one_of_pos hpos
  have hlo := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hlo
  have hdiv : 1 / q ≤ 2 * |q - 1| + 1 := (div_le_iff₀ hpos).mpr (by
    nlinarith [neg_le_abs (q - 1), abs_nonneg (q - 1)])
  rw [one_div] at hdiv
  refine ⟨hpos, abs_le.mpr ⟨?_, ?_⟩⟩
  · linarith
  · linarith [le_abs_self (q - 1), abs_nonneg (q - 1)]

/-- Source occupation-Q-ratio with the exact deterministic Haar-cell
integrals, and an explicit threshold making the relative error at most 1/2. -/
theorem occupation_Q_log_ratio {n J : ℕ} {β₀ β δ : ℝ}
    (hthreshold : ratioThreshold J β₀ ≤ n + 1)
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (i : Fin (n + 1)) (b : MeshIndex J) :
    |Real.log ((profileWeight (N := n + 1) (mesh_pos hmesh)
        (moveOccupation (occupation η) (η i) b) β).toReal /
      (profileWeight (N := n + 1) (mesh_pos hmesh) (occupation η) β).toReal) -
      Real.log ((∫ z in meshCell J (mesh_pos hmesh) b,
        Real.exp (β * meanPotential (mesh_pos hmesh) η β z) ∂torusMeasure) /
      (∫ z in meshCell J (mesh_pos hmesh) (η i),
        Real.exp (β * meanPotential (mesh_pos hmesh) η β z) ∂torusMeasure))| ≤
      logarithmicRatioConstant J β₀ / Real.sqrt (n + 1 : ℝ) := by
  obtain ⟨hN, hlarge, hhalf⟩ := ratioThreshold_bounds hthreshold
  let E := ∫ Y, fieldNormalizer (mesh_pos hmesh) η β i b (insertSite i 0 Y) /
    fieldNormalizer (mesh_pos hmesh) η β i (η i) (insertSite i 0 Y)
    ∂Measure.map (removeSite i) (labelGibbsMeasure (mesh_pos hmesh) η β)
  have he : |E - 1| ≤ ratioErrorConstant J β₀ / Real.sqrt (n + 1 : ℝ) :=
    fieldNormalizer_ratio_mean_error hN hβ hβ₀ hsub hδ hmesh η hη hlarge i (η i) b
  simp only [Nat.cast_add, Nat.cast_one] at hhalf
  have hE := abs_log_le_two_mul_abs_sub_one (he.trans hhalf)
  have ha := (potential_haar_cell_normalizer hN hβ hβ₀ hsub hδ hmesh η hη (η i)).2.1
  have hb := (potential_haar_cell_normalizer hN hβ hβ₀ hsub hδ hmesh η hη b).2.1
  rw [profile_partition_ratio_eq_outside hN hβ hβ₀ hsub hδ hmesh η hη i b,
    Real.log_mul (div_pos hb ha).ne' hE.1.ne']
  change |Real.log _ + Real.log E - Real.log _| ≤ _
  rw [add_sub_cancel_left]
  calc
    _ ≤ 2 * |E - 1| := hE.2
    _ ≤ 2 * (ratioErrorConstant J β₀ / Real.sqrt (n + 1 : ℝ)) :=
      mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by unfold logarithmicRatioConstant; ring

/-- The source cell is specified by a positive occupation count. There is
no positivity requirement on the destination occupation count. -/
theorem occupation_Q_log_ratio_cells {n J : ℕ} {β₀ β δ : ℝ}
    (hthreshold : ratioThreshold J β₀ ≤ n + 1)
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (a b : MeshIndex J) (ha : 1 ≤ occupation η a) :
    |Real.log ((profileWeight (N := n + 1) (mesh_pos hmesh)
        (moveOccupation (occupation η) a b) β).toReal /
      (profileWeight (N := n + 1) (mesh_pos hmesh) (occupation η) β).toReal) -
      Real.log ((∫ z in meshCell J (mesh_pos hmesh) b,
        Real.exp (β * meanPotential (mesh_pos hmesh) η β z) ∂torusMeasure) /
      (∫ z in meshCell J (mesh_pos hmesh) a,
        Real.exp (β * meanPotential (mesh_pos hmesh) η β z) ∂torusMeasure))| ≤
      logarithmicRatioConstant J β₀ / Real.sqrt (n + 1 : ℝ) := by
  classical
  obtain ⟨i, hi⟩ := Finset.one_le_card.mp ha
  have hia : η i = a := (Finset.mem_filter.mp hi).2
  simpa only [hia] using
    occupation_Q_log_ratio hthreshold hβ hβ₀ hsub hδ hmesh η hη i b

theorem occupation_update_le {N J : ℕ} (η : LabelVector J N) (i : Fin N)
    (b c : MeshIndex J) : occupation (Function.update η i b) c ≤ occupation η c + 1 := by
  classical
  rw [occupation_update η i (η i) b rfl]
  change occupation η c - (if η i = c then 1 else 0) + (if b = c then 1 else 0) ≤ _
  split_ifs <;> omega

/-- The literal two-particle source margin supplies both caps for every
one-label move, although the moved profile can leave the outer t-cap. -/
theorem source_move_caps {N J : ℕ} (hN : 0 < N) {t δ : ℝ}
    (hmargin : t + 2 / (N : ℝ) ≤ δ) (η : LabelVector J N) (hη : OccupationCap t η)
    (i : Fin N) (b : MeshIndex J) :
    OccupationCap δ η ∧ OccupationCap δ (Function.update η i b) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have htδ : t ≤ δ := by have := div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hNr.le; linarith
  have hmass : t * N + 2 ≤ δ * N := by
    have hm := mul_le_mul_of_nonneg_right hmargin hNr.le
    rwa [add_mul, div_mul_cancel₀ _ hNr.ne'] at hm
  refine ⟨hη.mono htδ, fun c ↦ ?_⟩
  have hc : (occupation (Function.update η i b) c : ℝ) ≤ (occupation η c : ℝ) + 1 := by
    exact_mod_cast occupation_update_le η i b c
  exact hc.trans ((add_le_add (hη c) le_rfl).trans (by linarith))

/-- Source form: the original outer occupation cap and the actual margin
discharge the source cap and the cap of the moved occupation profile. -/
theorem source_occupation_Q_log_ratio {n J : ℕ} {β₀ β δ t : ℝ}
    (hthreshold : ratioThreshold J β₀ ≤ n + 1)
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hmargin : t + 2 / (n + 1 : ℝ) ≤ δ)
    (η : LabelVector J (n + 1)) (hη : OccupationCap t η)
    (a b : MeshIndex J) (ha : 1 ≤ occupation η a) :
    moveOccupation (occupation η) a b ∈ cappedOccupations J (n + 1) δ ∧
    |Real.log ((profileWeight (N := n + 1) (mesh_pos hmesh)
        (moveOccupation (occupation η) a b) β).toReal /
      (profileWeight (N := n + 1) (mesh_pos hmesh) (occupation η) β).toReal) -
      Real.log ((∫ z in meshCell J (mesh_pos hmesh) b,
        Real.exp (β * meanPotential (mesh_pos hmesh) η β z) ∂torusMeasure) /
      (∫ z in meshCell J (mesh_pos hmesh) a,
        Real.exp (β * meanPotential (mesh_pos hmesh) η β z) ∂torusMeasure))| ≤
      logarithmicRatioConstant J β₀ / Real.sqrt (n + 1 : ℝ) := by
  classical
  obtain ⟨i, hi⟩ := Finset.one_le_card.mp ha
  have hia : η i = a := (Finset.mem_filter.mp hi).2
  have hm : t + 2 / (n + 1 : ℕ) ≤ δ := by simpa only [Nat.cast_add, Nat.cast_one] using hmargin
  have hcaps := source_move_caps (Nat.succ_pos n) hm η hη i b
  refine ⟨?_, occupation_Q_log_ratio_cells hthreshold hβ hβ₀ hsub hδ hmesh η hcaps.1 a b ha⟩
  rw [← occupation_update η i a b hia]
  exact (occupation_mem_cappedOccupations_iff _).mpr hcaps.2

end PeriodicAttractiveLogGas.OccupationPartitionTransport
