import LeanResearch.PeriodicAttractiveLogGas.OccupationPartitionTransport
import LeanResearch.PeriodicAttractiveLogGas.ConditionalSourceDerivatives
import LeanResearch.PeriodicAttractiveLogGas.DeletedConditionalPoincare
import LeanResearch.PeriodicAttractiveLogGas.OccupationPositiveExponential

/-! Source Proposition `occupation-second-differences`: the literal law
with one selected interaction removed, its cell-integral ratios, and the
restoration of that interaction. The particle denominator always remains
the original N. Development status is recorded in the companion note. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.OccupationSecondDifferences

open MeshCells MeshAdjacentCells LabelOccupations GreenPointWeights CellRestrictions
  OneCoordinateConditionals ConditionalLawEstimates CappedPointWeights
  ConditionalSourceCharts ConditionalSourceLipschitz ConditionalSourceDerivatives
  CellNormalizerBounds

section ScalarCovariance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Relative variance bounds give a relative product-moment error under
the same probability law. All second moments are genuine finite moments. -/
theorem relative_covariance_bound {A B : Ω → ℝ} (hA : MemLp A 2 μ)
    (hB : MemLp B 2 μ) (hAm : 0 < ∫ X, A X ∂μ) (hBm : 0 < ∫ X, B X ∂μ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hvA : variance A μ ≤ ε * (∫ X, A X ∂μ) ^ 2)
    (hvB : variance B μ ≤ ε * (∫ X, B X ∂μ) ^ 2) :
    |(∫ X, A X * B X ∂μ) / ((∫ X, A X ∂μ) * (∫ X, B X ∂μ)) - 1| ≤ ε := by
  let a := ∫ X, A X ∂μ
  let b := ∫ X, B X ∂μ
  have hab : 0 < a * b := mul_pos hAm hBm
  have hc := BoundaryCovarianceSplitting.covariance_squared_le hA hB
  have hv : variance A μ * variance B μ ≤ (ε * a ^ 2) * (ε * b ^ 2) :=
    mul_le_mul hvA hvB (variance_nonneg _ _) (mul_nonneg hε (sq_nonneg a))
  have hc' : |covariance A B μ| ≤ ε * (a * b) := by
    have hz : 0 ≤ ε * (a * b) := mul_nonneg hε hab.le
    have hs : |covariance A B μ| ^ 2 ≤ (ε * (a * b)) ^ 2 := by
      rw [sq_abs]
      nlinarith [hc.trans hv]
    nlinarith [abs_nonneg (covariance A B μ)]
  have he : (∫ X, A X * B X ∂μ) / (a * b) - 1 = covariance A B μ / (a * b) := by
    rw [covariance_eq_sub hA hB]
    simp only [Pi.mul_apply]
    dsimp only [a, b]
    field_simp [hAm.ne', hBm.ne']
  change |(∫ X, A X * B X ∂μ) / (a * b) - 1| ≤ ε
  rw [he, abs_div, abs_of_pos hab]
  exact (div_le_iff₀ hab).mpr hc'

theorem relative_covariance_log_bound {A B : Ω → ℝ} (hA : MemLp A 2 μ)
    (hB : MemLp B 2 μ) (hAm : 0 < ∫ X, A X ∂μ) (hBm : 0 < ∫ X, B X ∂μ)
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 2)
    (hvA : variance A μ ≤ ε * (∫ X, A X ∂μ) ^ 2)
    (hvB : variance B μ ≤ ε * (∫ X, B X ∂μ) ^ 2) :
    0 < (∫ X, A X * B X ∂μ) / ((∫ X, A X ∂μ) * (∫ X, B X ∂μ)) ∧
      |Real.log ((∫ X, A X * B X ∂μ) / ((∫ X, A X ∂μ) * (∫ X, B X ∂μ)))| ≤
        2 * ε := by
  have hc := relative_covariance_bound hA hB hAm hBm hε hvA hvB
  have hh := OccupationPartitionTransport.abs_log_le_two_mul_abs_sub_one (hc.trans hsmall)
  exact ⟨hh.1, hh.2.trans (mul_le_mul_of_nonneg_left hc (by norm_num))⟩

/-- The two elementary one-sided restoration bounds imply the needed
absolute logarithmic error, without a positive lower bound on beta. -/
theorem restoration_log_bound {R L U : ℝ} (hL : 0 ≤ L) (hU : 0 ≤ U)
    (hlo : Real.exp (-L) ≤ R) (hhi : R ≤ 1 + U) :
    0 < R ∧ |Real.log R| ≤ L + U := by
  have hR : 0 < R := (Real.exp_pos _).trans_le hlo
  have hl : -L ≤ Real.log R := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (-L)) hlo
  have hu := Real.log_le_sub_one_of_pos hR
  exact ⟨hR, abs_le.mpr ⟨by linarith, by linarith⟩⟩

end ScalarCovariance

section DeletedSources

variable {n J : ℕ}

/-- Normalized-cell integral of the actual optional-deletion source weight.
Its ratio equals the ratio of raw Haar cell integrals. -/
def cellIntegral (hJ : 0 < J) (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    (β : ℝ) (i : Fin (n + 1)) (a : MeshIndex J) (Y : Configuration n) : ℝ :=
  ∫ z, torusWeight Y (DeletedPairEnsemble.sourceCoefficient d β i) z
    ∂meshCellMeasure J hJ a

def cellRatio (hJ : 0 < J) (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    (β : ℝ) (i : Fin (n + 1)) (a b : MeshIndex J) (Y : Configuration n) : ℝ :=
  cellIntegral hJ d β i b Y / cellIntegral hJ d β i a Y

theorem measurable_sourceWeight (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    (β : ℝ) (i : Fin (n + 1)) :
    Measurable (fun p : Configuration n × Torus =>
      torusWeight p.1 (DeletedPairEnsemble.sourceCoefficient d β i) p.2) := by
  apply Real.continuous_exp.measurable.comp
  exact Finset.measurable_sum _ fun j _ =>
    (regularGreenRepresentative_measurable.comp
      (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))).const_mul _

theorem measurable_cellIntegral (hJ : 0 < J)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (i : Fin (n + 1)) (a : MeshIndex J) : Measurable (cellIntegral hJ d β i a) :=
  (measurable_sourceWeight d β i).stronglyMeasurable.integral_prod_right.measurable

theorem measurable_cellRatio (hJ : 0 < J)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (i : Fin (n + 1)) (a b : MeshIndex J) : Measurable (cellRatio hJ d β i a b) :=
  (measurable_cellIntegral hJ d β i b).div (measurable_cellIntegral hJ d β i a)

theorem cellIntegral_eq_raw (hJ : 0 < J)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (i : Fin (n + 1)) (a : MeshIndex J) (Y : Configuration n) :
    cellIntegral hJ d β i a Y = (J : ℝ) ^ 2 * deletedOutsideNormalizer hJ i d β a .cell Y := by
  rw [cellIntegral, meshCellMeasure, integral_smul_measure]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_natCast, smul_eq_mul,
    deletedOutsideNormalizer, OneCoordinateConditionals.patchDomain,
    TorusPatchDensity.domain, LocalPointEstimates.shape]

variable {β β₀ δ Cg : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
  (hδ : δ ≤ occupationBound β₀) (hCg : 0 ≤ Cg)
  (hg : ∀ z : Torus, -Cg ≤ regularGreenRepresentative z)
  (hmesh : 8 * (radius β₀ + 4) ≤ J)
  (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
  (d : Option (DeletedPairEnsemble.Pair (n + 1))) (i : Fin (n + 1))
  (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y)

include hβ hβ₀ hδ hCg hg hη hY in
/-- The source coefficient of the removed partner is genuinely allowed to
be zero. Both cell-integral bounds hold for every target cell. -/
theorem deleted_cell_integral_bounds (a : MeshIndex J) :
    Integrable (torusWeight Y (DeletedPairEnsemble.sourceCoefficient d β i))
      (meshCellMeasure J (mesh_pos hmesh) a) ∧
      Real.exp (-β₀ * Cg) ≤ cellIntegral (mesh_pos hmesh) d β i a Y ∧
      cellIntegral (mesh_pos hmesh) d β i a Y ≤
        upperConstant β₀ kernelConstant J (radius β₀) := by
  classical
  let I := otherParticles i
  let X := insertSite i 0 Y
  let w := DeletedPairEnsemble.coefficients d β i
  have hw : ∀ k, 0 ≤ w k := fun k => (DeletedPairEnsemble.coefficients_bounds d hβ i k).1
  have ht : ∑ k : I, w k ≤ β₀ := by
    rw [Finset.sum_coe_sort]
    exact total_source_weight_le (Nat.succ_pos n) hβ hβ₀ I
      (fun k _ => (DeletedPairEnsemble.coefficients_bounds d hβ i k).2)
  have hn : ∑ k : {k : I // η k ∈ nearby J (mesh_pos hmesh) (radius β₀) a .cell},
      w k.1 ≤ 1 / 16 := by
    rw [sum_near_eq_sourceWeight]
    exact sourceWeight_fixedDelta_le (Nat.succ_pos n) hβ hβ₀ kernelConstant_pos.le
      (hη.mono hδ) I _ (card_nearby_le J (mesh_pos hmesh) (radius β₀) a .cell)
      (fun k _ => (DeletedPairEnsemble.coefficients_bounds d hβ i k).2)
  have hu := cell_weight_upper (mesh_pos hmesh) (radius_one_le β₀) hmesh a
    (fun k : I => X k) (fun k : I => η k)
    (fun k => prescribedOutside_insertSite (mesh_pos hmesh) η i Y hY k k.2)
    (fun k : I => w k) (fun k => hw k) kernelConstant_pos.le kernel_log_bound ht hn
  have hl := cell_weight_lower (mesh_pos hmesh) a (fun k : I => X k) (fun k : I => w k)
    (fun k => hw k) hCg hg ht hu.1
  have he := DeletedPairEnsemble.sourceWeight_eq_subfamily d i β Y
  change torusWeight Y (DeletedPairEnsemble.sourceCoefficient d β i) =
    torusWeight (fun k : I => X k) (fun k : I => w k) at he
  rw [← he] at hu hl
  exact ⟨hu.1, hl, hu.2⟩

include hβ hβ₀ hδ hCg hg hη hY in
theorem deleted_cell_ratio_bounds (a b : MeshIndex J) :
    let κ := kappaConstant β₀ Cg kernelConstant J (radius β₀)
    κ ≤ cellRatio (mesh_pos hmesh) d β i a b Y ∧
      cellRatio (mesh_pos hmesh) d β i a b Y ≤ κ⁻¹ := by
  have ha := deleted_cell_integral_bounds hβ hβ₀ hδ hCg hg hmesh η hη d i Y hY a
  have hb := deleted_cell_integral_bounds hβ hβ₀ hδ hCg hg hmesh η hη d i Y hY b
  have hp : 0 < cellIntegral (mesh_pos hmesh) d β i a Y :=
    (Real.exp_pos _).trans_le ha.2.1
  have hU : 0 < upperConstant β₀ kernelConstant J (radius β₀) :=
    upperConstant_pos _ _ (mesh_pos hmesh) (by have h := radius_one_le β₀; omega)
  dsimp only [cellRatio]
  rw [← lower_div_upper_eq_kappa β₀ Cg kernelConstant (mesh_pos hmesh)
    (by have h := radius_one_le β₀; omega)]
  constructor
  · exact div_le_div₀ ((Real.exp_pos _).le.trans hb.2.1) hb.2.1 hp ha.2.2
  · rw [inv_div]
    exact div_le_div₀ hU.le hb.2.2 (Real.exp_pos _) ha.2.1

include hβ hβ₀ hδ hη hY in
/-- The gradient moment belongs to the changed conditional law itself. -/
theorem deleted_probe_gradient_moments (a : MeshIndex J) (z : Torus) :
    GreenGradientMoments.Estimates
      (pointLaw (meshCellMeasure J (mesh_pos hmesh) a) Y
        (DeletedPairEnsemble.sourceCoefficient d β i)) z kernelConstant (densityNormBound β₀) J := by
  have hb := DeletedPairEnsemble.capped_source_bounds d hβ hβ₀ hδ hmesh η hη i Y hY a .cell
  exact GreenGradientMoments.pointLaw_gradient_moments (mesh_pos hmesh) (radius_one_le β₀)
    hmesh kernelConstant_pos.le kernel_gradient_bound a .cell Y
    (DeletedPairEnsemble.sourceCoefficient d β i) hb.2.1 hb.2.2.2.1 hb.2.2.2.2.2 z

include hβ hβ₀ hδ hη hY in
/-- Uniform envelope control for the actual omitted-coefficient point law.
The pole is arbitrary, so this also permits the other selected particle. -/
theorem deleted_probe_envelope_bound (a : MeshIndex J) (z : Torus) :
    Integrable (fun y => OccupationPositiveExponential.positiveEnvelope (z - y))
      (pointLaw (meshCellMeasure J (mesh_pos hmesh) a) Y
        (DeletedPairEnsemble.sourceCoefficient d β i)) ∧
      (∫ y, OccupationPositiveExponential.positiveEnvelope (z - y)
        ∂pointLaw (meshCellMeasure J (mesh_pos hmesh) a) Y
          (DeletedPairEnsemble.sourceCoefficient d β i)) ≤
        densityNormBound β₀ * OccupationPositiveExponential.envelopeBound J := by
  have hb := DeletedPairEnsemble.capped_source_bounds d hβ hβ₀ hδ hmesh η hη i Y hY a .cell
  have hf := OccupationPositiveExponential.cell_positiveEnvelope_moment (mesh_pos hmesh) a z
  exact OccupationPositiveExponential.density_envelope_bound
    (measurable_pointDensity _ Y _) (fun y => div_nonneg (torusWeight_pos _ _ y).le hb.2.1.le)
    hb.2.2.2.1 hb.2.2.2.2.2
    (fun y => OccupationPositiveExponential.positiveEnvelope_nonneg (z - y)) hf.1 hf.2

end DeletedSources

section DeletedTransport

variable {n J : ℕ}

def jointRatio (hJ : 0 < J) (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    (β : ℝ) (i : Fin (n + 1)) (a b : MeshIndex J) (X : Configuration (n + 1)) : ℝ :=
  cellRatio hJ d β i a b (removeSite i X)

theorem measurable_jointRatio (hJ : 0 < J)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (i : Fin (n + 1)) (a b : MeshIndex J) :
    Measurable (jointRatio hJ d β i a b) :=
  (measurable_cellRatio hJ d β i a b).comp (measurable_removeSite i)

theorem cellIntegral_joint_eq_subfamily (hJ : 0 < J)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (i : Fin (n + 1)) (a : MeshIndex J) (X : Configuration (n + 1)) :
    cellIntegral hJ d β i a (removeSite i X) =
      ∫ z, torusWeight (fun k : otherParticles i => X k)
        (fun k => DeletedPairEnsemble.coefficients d β i k) z
        ∂meshCellMeasure J hJ a := by
  unfold cellIntegral
  rw [DeletedPairEnsemble.sourceWeight_eq_subfamily]
  have he : (fun k : otherParticles i => insertSite i 0 (removeSite i X) k) =
      (fun k : otherParticles i => X k) := by
    funext k
    rw [CoordinateConditionalKernels.insertSite_eq_update,
      Function.update_of_ne ((mem_otherParticles i k).mp k.property)]
  rw [he]

/-- A removed coefficient makes the probe integral independent of that
particle, as an equality on every configuration, not just almost everywhere. -/
theorem cellIntegral_joint_update (hJ : 0 < J)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (i j : Fin (n + 1)) (a : MeshIndex J) (X : Configuration (n + 1)) (z : Torus)
    (hj : j = i ∨ DeletedPairEnsemble.isDeleted d i j) :
    cellIntegral hJ d β i a (removeSite i (Function.update X j z)) =
      cellIntegral hJ d β i a (removeSite i X) := by
  classical
  rw [cellIntegral_joint_eq_subfamily, cellIntegral_joint_eq_subfamily]
  apply integral_congr_ae
  filter_upwards [] with y
  unfold torusWeight
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hkj : (k : Fin (n + 1)) = j
  · have hd : DeletedPairEnsemble.isDeleted d i j := hj.resolve_left (by
      intro hji
      exact ((mem_otherParticles i k).mp k.property) (hkj.trans hji))
    simp only [hkj, DeletedPairEnsemble.coefficients, hd, ite_true, zero_mul]
  · dsimp only
    rw [Function.update_of_ne hkj]

theorem jointRatio_update (hJ : 0 < J)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (i j : Fin (n + 1)) (a b : MeshIndex J) (X : Configuration (n + 1)) (z : Torus)
    (hj : j = i ∨ DeletedPairEnsemble.isDeleted d i j) :
    jointRatio hJ d β i a b (Function.update X j z) = jointRatio hJ d β i a b X := by
  unfold jointRatio cellRatio
  rw [cellIntegral_joint_update hJ d β i j b X z hj,
    cellIntegral_joint_update hJ d β i j a X z hj]

/-- The literal specified-cell partition integral with the optional pair
removed. There is no occupation multiplicity in this definition. -/
def deletedPartition (hJ : 0 < J) (η : LabelVector J (n + 1))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) : ℝ≥0∞ :=
  PositiveProductConditionals.normalizer (fun k => meshCellMeasure J hJ (η k))
    (DeletedPairEnsemble.weight regularGreenRepresentative d β)

def deletedCellMass (hJ : 0 < J) (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    (β : ℝ) (i : Fin (n + 1)) (a : MeshIndex J) (Y : Configuration n) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (torusWeight Y (DeletedPairEnsemble.sourceCoefficient d β i) z)
    ∂meshCellMeasure J hJ a

def deletedOutsideWeight (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    (β : ℝ) (i : Fin (n + 1)) (Y : Configuration n) : ℝ :=
  Real.exp ((β / (n + 1)) * (pairEnergy regularGreenRepresentative n Y -
    DeletedPairEnsemble.outsideRemoved regularGreenRepresentative d i Y))

theorem measurable_deletedOutsideWeight (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    (β : ℝ) (i : Fin (n + 1)) : Measurable (deletedOutsideWeight d β i) := by
  have hp := measurable_pairEnergy regularGreenRepresentative_measurable n
  have hr : Measurable (DeletedPairEnsemble.outsideRemoved regularGreenRepresentative d i) := by
    unfold DeletedPairEnsemble.outsideRemoved
    cases d with
    | none => exact measurable_const
    | some p =>
      dsimp only
      split_ifs
      · exact measurable_const
      · have hs : Measurable (fun Y : Configuration n => insertSite i (0 : Torus) Y) :=
          (measurable_insertSite i).comp (measurable_const.prodMk measurable_id)
        exact regularGreenRepresentative_measurable.comp
          (((measurable_pi_apply p.val.1).comp hs).sub ((measurable_pi_apply p.val.2).comp hs))
  exact Real.continuous_exp.measurable.comp ((hp.sub hr).const_mul _)

theorem measurable_deletedCellMass (hJ : 0 < J)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (i : Fin (n + 1)) (a : MeshIndex J) : Measurable (deletedCellMass hJ d β i a) :=
  (measurable_sourceWeight d β i).ennreal_ofReal.lintegral_prod_right

theorem deletedCellMass_eq_ofReal (hJ : 0 < J)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (i : Fin (n + 1)) (a : MeshIndex J) (Y : Configuration n)
    (hi : Integrable (torusWeight Y (DeletedPairEnsemble.sourceCoefficient d β i))
      (meshCellMeasure J hJ a)) :
    deletedCellMass hJ d β i a Y = ENNReal.ofReal (cellIntegral hJ d β i a Y) :=
  (ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun z => (torusWeight_pos _ _ z).le)).symm

theorem deleted_sectionMass (hJ : 0 < J)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (i : Fin (n + 1)) (a : MeshIndex J) (Y : Configuration n) :
    PositiveProductConditionals.sectionMass (meshCellMeasure J hJ a)
      (DeletedPairEnsemble.weight regularGreenRepresentative d β) i Y =
      ENNReal.ofReal (deletedOutsideWeight d β i Y) * deletedCellMass hJ d β i a Y := by
  simp only [PositiveProductConditionals.sectionMass, PositiveProductConditionals.density,
    DeletedPairEnsemble.weight_insertSite,
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact lintegral_const_mul _ (measurable_torusWeight Y _).ennreal_ofReal

theorem deletedPartition_update (hJ : 0 < J) (η : LabelVector J (n + 1))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (i : Fin (n + 1)) (a : MeshIndex J) :
    deletedPartition hJ (Function.update η i a) d β =
      ∫⁻ Y, ENNReal.ofReal (deletedOutsideWeight d β i Y) * deletedCellMass hJ d β i a Y
        ∂outsideReference (fun k => meshCellMeasure J hJ (η k)) i := by
  unfold deletedPartition
  rw [PositiveProductConditionals.normalizer_eq_sections _
    (DeletedPairEnsemble.measurable_weight regularGreenRepresentative_measurable d β) i]
  have ho : outsideReference (fun k => meshCellMeasure J hJ (Function.update η i a k)) i =
      outsideReference (fun k => meshCellMeasure J hJ (η k)) i := by
    unfold outsideReference
    congr 1
    funext k
    dsimp only
    rw [Function.update_of_ne (Fin.succAbove_ne i k)]
  rw [ho]
  simp only [Function.update_self, deleted_sectionMass]

theorem deleted_outsideMarginal (hJ : 0 < J) (η : LabelVector J (n + 1))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (i : Fin (n + 1)) :
    Measure.map (removeSite i) (DeletedPairConditionals.jointLaw hJ η (fun _ => .cell) d β) =
      (outsideReference (fun k => meshCellMeasure J hJ (η k)) i).withDensity
        (fun Y => (deletedPartition hJ η d β)⁻¹ *
          (ENNReal.ofReal (deletedOutsideWeight d β i Y) * deletedCellMass hJ d β i (η i) Y)) := by
  change PositiveProductConditionals.outsideMarginal
    (fun k => meshCellMeasure J hJ (η k))
    (DeletedPairEnsemble.weight regularGreenRepresentative d β) i = _
  rw [PositiveProductConditionals.outsideMarginal_eq _
    (DeletedPairEnsemble.measurable_weight regularGreenRepresentative_measurable d β) i]
  simp only [deleted_sectionMass, deletedPartition]

variable {β β₀ δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
  (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
  (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
  (d : Option (DeletedPairEnsemble.Pair (n + 1))) (i : Fin (n + 1))

include hβ hβ₀ hδ hη in
/-- Genuine weighted transport through the outside marginal of the
original deleted joint law. The outside factor keeps the original N. -/
theorem deleted_weighted_transport (b : MeshIndex J) {F : Configuration n → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ Y, ENNReal.ofReal (cellRatio (mesh_pos hmesh) d β i (η i) b Y) * F Y
      ∂Measure.map (removeSite i)
        (DeletedPairConditionals.jointLaw (mesh_pos hmesh) η (fun _ => .cell) d β)) =
      (deletedPartition (mesh_pos hmesh) η d β)⁻¹ *
        ∫⁻ Y, (ENNReal.ofReal (deletedOutsideWeight d β i Y) *
          deletedCellMass (mesh_pos hmesh) d β i b Y) * F Y
          ∂outsideReference (fun k => meshCellMeasure J (mesh_pos hmesh) (η k)) i := by
  let hJ := mesh_pos hmesh
  have hm : Measurable (fun Y => ENNReal.ofReal (cellRatio hJ d β i (η i) b Y) * F Y) :=
    (measurable_cellRatio hJ d β i (η i) b).ennreal_ofReal.mul hF
  have hd : Measurable (fun Y : Configuration n => (deletedPartition hJ η d β)⁻¹ *
      (ENNReal.ofReal (deletedOutsideWeight d β i Y) * deletedCellMass hJ d β i (η i) Y)) :=
    measurable_const.mul ((measurable_deletedOutsideWeight d β i).ennreal_ofReal.mul
      (measurable_deletedCellMass hJ d β i (η i)))
  rw [deleted_outsideMarginal, lintegral_withDensity_eq_lintegral_mul _ hd hm]
  have hf : Measurable (fun Y : Configuration n =>
      (ENNReal.ofReal (deletedOutsideWeight d β i Y) * deletedCellMass hJ d β i b Y) * F Y) :=
    ((measurable_deletedOutsideWeight d β i).ennreal_ofReal.mul
      (measurable_deletedCellMass hJ d β i b)).mul hF
  rw [← lintegral_const_mul _ hf]
  apply lintegral_congr_ae
  filter_upwards [LabelRatioTransport.ae_prescribedOutside hJ η i] with Y hY
  have ha := DeletedPairEnsemble.capped_source_bounds d hβ hβ₀ hδ hmesh η hη i Y hY (η i) .cell
  have hb := DeletedPairEnsemble.capped_source_bounds d hβ hβ₀ hδ hmesh η hη i Y hY b .cell
  dsimp only [Pi.mul_apply]
  rw [deletedCellMass_eq_ofReal hJ d β i (η i) Y ha.1,
    deletedCellMass_eq_ofReal hJ d β i b Y hb.1]
  change _ * (ENNReal.ofReal (cellIntegral hJ d β i b Y / cellIntegral hJ d β i (η i) Y) * F Y) = _
  have hapos : 0 < cellIntegral hJ d β i (η i) Y := ha.2.1
  rw [ENNReal.ofReal_div_of_pos hapos, div_eq_mul_inv]
  have hA := (ENNReal.ofReal_pos.mpr hapos).ne'
  calc
    _ = (deletedPartition hJ η d β)⁻¹ *
        ((ENNReal.ofReal (deletedOutsideWeight d β i Y) * ENNReal.ofReal (cellIntegral hJ d β i b Y)) * F Y) *
        (ENNReal.ofReal (cellIntegral hJ d β i (η i) Y) *
          (ENNReal.ofReal (cellIntegral hJ d β i (η i) Y))⁻¹) := by
            simp only [mul_assoc, mul_comm, mul_left_comm]
    _ = _ := by rw [ENNReal.mul_inv_cancel hA ENNReal.ofReal_ne_top, mul_one]

include hβ hβ₀ hδ hη in
theorem deleted_partition_ratio_lintegral (b : MeshIndex J) :
    (∫⁻ Y, ENNReal.ofReal (cellRatio (mesh_pos hmesh) d β i (η i) b Y)
      ∂Measure.map (removeSite i)
        (DeletedPairConditionals.jointLaw (mesh_pos hmesh) η (fun _ => .cell) d β)) =
      deletedPartition (mesh_pos hmesh) (Function.update η i b) d β /
        deletedPartition (mesh_pos hmesh) η d β := by
  have he := deleted_weighted_transport hβ hβ₀ hδ hmesh η hη d i b
    (F := fun _ => 1) measurable_const
  simp only [mul_one] at he
  rw [← deletedPartition_update] at he
  simpa only [div_eq_mul_inv, mul_comm] using he

end DeletedTransport

section RatioRegularity

open MovingPoleNumerators MovingPoleCharts MovingPoleCalculus MovingPoleNormalized
  MovingPoleDerivativeIdentification

variable {n J : ℕ}

theorem abs_exp_sub_le_sum (x y : ℝ) :
    |Real.exp x - Real.exp y| ≤ (Real.exp x + Real.exp y) * |x - y| := by
  have he : Real.exp y * Real.exp (x - y) = Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hh := mul_le_mul_of_nonneg_left (OccupationFieldEstimates.abs_exp_sub_one_bound (x - y))
    (Real.exp_pos y).le
  have hl : Real.exp y * |Real.exp (x - y) - 1| = |Real.exp x - Real.exp y| := by
    rw [← abs_of_pos (Real.exp_pos y), ← abs_mul, mul_sub, he, mul_one]
    rw [abs_of_pos (Real.exp_pos y)]
  rw [hl] at hh
  calc
    _ ≤ Real.exp y * (|x - y| * (1 + Real.exp (x - y))) := hh
    _ = (Real.exp y + Real.exp y * Real.exp (x - y)) * |x - y| := by ring
    _ = _ := by rw [he, add_comm]

theorem cellRatio_eq_exp_deletedLog (hJ : 0 < J)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (i : Fin (n + 1)) (a b : MeshIndex J) (Y : Configuration n)
    (ha : 0 < deletedOutsideNormalizer hJ i d β a .cell Y)
    (hb : 0 < deletedOutsideNormalizer hJ i d β b .cell Y) :
    cellRatio hJ d β i a b Y =
      Real.exp (deletedOutsideLog hJ i d β b .cell Y - deletedOutsideLog hJ i d β a .cell Y) := by
  have hj : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  rw [cellRatio, cellIntegral_eq_raw, cellIntegral_eq_raw, deletedOutsideLog,
    deletedOutsideLog, Real.exp_sub, Real.exp_log hb, Real.exp_log ha]
  field_simp [hj, ha.ne']

variable {β β₀ δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
  (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
  (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
  (d : Option (DeletedPairEnsemble.Pair (n + 1))) (i : Fin (n + 1))

include hβ hβ₀ hδ hη in
/-- The full weak-to-ordinary calculus is instantiated for the actual
deleted coefficients and every probe cell. -/
theorem deleted_probe_calculus (a : MeshIndex J) :
    SourceCalculus (fun k : otherParticles i => DeletedPairEnsemble.coefficients d β i k)
      J (mesh_pos hmesh) a .cell (cellChart (otherParticles i) η) (fun _ _ => 1) := by
  exact cellChart_sourceCalculus MovingPoleIntegrability.fixedKernelBounds (mesh_pos hmesh)
    (Nat.succ_pos n) hβ hβ₀ kernelConstant_pos.le kernelConstant_pos.le
    kernel_log_bound kernel_gradient_bound hmesh (otherParticles i) η (hη.mono hδ)
    (DeletedPairEnsemble.coefficients d β i)
    (fun k _ => (DeletedPairEnsemble.coefficients_bounds d hβ i k).1)
    (fun k _ => (DeletedPairEnsemble.coefficients_bounds d hβ i k).2)
    a .cell (smoothOnChart_of_contDiff contDiff_const)

include hβ hβ₀ hδ hη in
theorem jointRatio_lipschitz (a b : MeshIndex J) :
    ∃ L : ℝ≥0, ConfigurationPhysicalLipschitzOn L
      (jointRatio (mesh_pos hmesh) d β i a b)
      (DeletedConditionalPoincare.closedPatchProduct (mesh_pos hmesh) η (fun _ => .cell)) := by
  let hJ := mesh_pos hmesh
  let κ := kappaConstant β₀ greenLowerConstant kernelConstant J (radius β₀)
  have hκ : 0 < κ := kappaConstant_pos _ _ _ hJ (by have h := radius_one_le β₀; omega)
  have ha := deleted_probe_calculus hβ hβ₀ hδ hmesh η hη d i a
  have hb := deleted_probe_calculus hβ hβ₀ hδ hmesh η hη d i b
  obtain ⟨La, _, hLa, _⟩ := deleted_joint_lipschitz_of_sourceCalculus hJ (by omega)
    i η (fun _ => .cell) d β a .cell (fun _ => 1) ha
  obtain ⟨Lb, _, hLb, _⟩ := deleted_joint_lipschitz_of_sourceCalculus hJ (by omega)
    i η (fun _ => .cell) d β b .cell (fun _ => 1) hb
  let L : ℝ≥0 := ⟨2 * κ⁻¹, by positivity⟩ * (Lb + La)
  refine ⟨L, ?_⟩
  have he (X : Configuration (n + 1))
      (hX : X ∈ DeletedConditionalPoincare.closedPatchProduct hJ η (fun _ => .cell)) :
      jointRatio hJ d β i a b X = Real.exp
        (deletedOutsideLog hJ i d β b .cell (removeSite i X) -
          deletedOutsideLog hJ i d β a .cell (removeSite i X)) ∧
        jointRatio hJ d β i a b X ≤ κ⁻¹ := by
    have hY : PrescribedOutside hJ η i (removeSite i X) := by
      intro j
      exact hX (i.succAbove j) (mem_univ _)
    have hr := deleted_cell_ratio_bounds hβ hβ₀ hδ greenLowerConstant_pos.le
      green_lower_bound hmesh η hη d i _ hY a b
    obtain ⟨Z, hZ, hZY⟩ := outsideCoordinates_surjOn_closedChart hJ i η (fun _ => .cell)
      (removeSite_mem_closedOutsideProduct hJ i η (fun _ => .cell) hX)
    refine ⟨?_, hr.2⟩
    unfold jointRatio
    rw [← hZY]
    apply cellRatio_eq_exp_deletedLog
    · simpa only [deletedOutsideNormalizer, deletedWeight_outsideCoordinates,
        ← source_patchDomain, ← rawNormalizer_eq_integral] using ha.normalization.normalizer_pos Z hZ
    · simpa only [deletedOutsideNormalizer, deletedWeight_outsideCoordinates,
        ← source_patchDomain, ← rawNormalizer_eq_integral] using hb.normalization.normalizer_pos Z hZ
  intro X hX Y hY
  obtain ⟨heX, huX⟩ := he X hX
  obtain ⟨heY, huY⟩ := he Y hY
  rw [heX] at huX
  rw [heY] at huY
  rw [heX, heY]
  have hlog := physicalLipschitz_sub hLb hLa X hX Y hY
  calc
    _ ≤ _ := abs_exp_sub_le_sum _ _
    _ ≤ (2 * κ⁻¹) *
        |(deletedOutsideLog hJ i d β b .cell (removeSite i X) -
          deletedOutsideLog hJ i d β a .cell (removeSite i X)) -
          (deletedOutsideLog hJ i d β b .cell (removeSite i Y) -
          deletedOutsideLog hJ i d β a .cell (removeSite i Y))| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ ≤ (2 * κ⁻¹) * ((Lb + La : ℝ≥0) * configurationEuclideanDist X Y) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by
      change (2 * κ⁻¹) * ((Lb + La : ℝ≥0) * configurationEuclideanDist X Y) =
        ((2 * κ⁻¹) * (Lb + La : ℝ≥0)) * configurationEuclideanDist X Y
      ring

def probeField (hJ : 0 < J) (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    (β : ℝ) (i : Fin (n + 1)) (a : MeshIndex J) (Y : Configuration n) (j : Fin n) : PlanarSpace :=
  (-DeletedPairEnsemble.sourceCoefficient d β i j) •
    ∫ z, greenGradient (z - Y j)
      ∂pointLaw (meshCellMeasure J hJ a) Y (DeletedPairEnsemble.sourceCoefficient d β i)

def ratioField (hJ : 0 < J) (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    (β : ℝ) (i : Fin (n + 1)) (a b : MeshIndex J) (Y : Configuration n) (j : Fin n) : PlanarSpace :=
  cellRatio hJ d β i a b Y • (probeField hJ d β i b Y j - probeField hJ d β i a Y j)

theorem source_probeField (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ)
    (i : Fin (n + 1)) (a : MeshIndex J) (S : Set (SourceSpace (otherParticles i)))
    (hc : SourceCalculus (fun k : otherParticles i => DeletedPairEnsemble.coefficients d β i k)
      J hJ a .cell S (fun _ _ => 1)) (X : SourceSpace (otherParticles i)) (hX : X ∈ S)
    (j : Fin n) :
    sourceProjection (otherIndexEquiv i j)
      (rawLogGradient (fun k : otherParticles i => DeletedPairEnsemble.coefficients d β i k)
        J hJ a .cell X) = probeField hJ d β i a (outsideCoordinates i X) j := by
  have hp := (deletedPointLaw_outsideCoordinates (patchMeasure J hJ a .cell) i d β X).trans
    (pointLaw_patch_eq_raw hJ hJ2 a .cell _ _)
  rw [source_patchDomain] at hp
  rw [(hc.blocks X hX (otherIndexEquiv i j)).1, logBlock, source_patchDomain, ← hp]
  simp only [probeField, otherIndexEquiv_val, DeletedPairEnsemble.coefficients_succAbove]
  rfl

include hβ hβ₀ hδ hη in
/-- Genuine coordinate derivatives of the actual ratio under the actual
deleted joint law, derived from chart-interior value identities. -/
theorem jointRatio_derivatives (a b : MeshIndex J) :
    ∀ᵐ X ∂DeletedPairConditionals.jointLaw (mesh_pos hmesh) η (fun _ => .cell) d β,
      PrescribedOutside (mesh_pos hmesh) η i (removeSite i X) ∧
      ∀ j : Fin n, HasCoordinateDerivative (jointRatio (mesh_pos hmesh) d β i a b)
        (i.succAbove j) X (ratioField (mesh_pos hmesh) d β i a b (removeSite i X) j) := by
  let hJ := mesh_pos hmesh
  let S := cellChart (otherParticles i) η
  let w : otherParticles i → ℝ := fun k => DeletedPairEnsemble.coefficients d β i k
  have ha := deleted_probe_calculus hβ hβ₀ hδ hmesh η hη d i a
  have hb := deleted_probe_calculus hβ hβ₀ hδ hmesh η hη d i b
  have hd : ∀ᵐ Y ∂outsideReference (fun k => patchMeasure J hJ (η k) .cell) i,
      PrescribedOutside hJ η i Y ∧ ∀ j : Fin n,
        HasCoordinateDerivative (cellRatio hJ d β i a b) j Y (ratioField hJ d β i a b Y j) := by
    apply ae_outsideReference_of_chart hJ (by omega) i η (fun _ => .cell)
    have he (Z : SourceSpace (otherParticles i)) (hZ : Z ∈ S) :
        cellRatio hJ d β i a b (outsideCoordinates i Z) =
          Real.exp (rawLog w J hJ b .cell Z - rawLog w J hJ a .cell Z) := by
      rw [← deletedOutsideLog_comp, ← deletedOutsideLog_comp]
      apply cellRatio_eq_exp_deletedLog
      · simpa only [deletedOutsideNormalizer, deletedWeight_outsideCoordinates,
          ← source_patchDomain, ← rawNormalizer_eq_integral] using ha.normalization.normalizer_pos Z hZ
      · simpa only [deletedOutsideNormalizer, deletedWeight_outsideCoordinates,
          ← source_patchDomain, ← rawNormalizer_eq_integral] using hb.normalization.normalizer_pos Z hZ
    filter_upwards [ha.ordinary, hb.ordinary,
      ae_closedChart_mem_nhds J (fun k : otherParticles i => η k) (fun _ => Patch.cell),
      ae_restrict_mem (isCompact_closedChart J (fun k : otherParticles i => η k)
        (fun _ => Patch.cell)).measurableSet] with X hda hdb hn hX
    let G := rawLogGradient w J hJ b .cell X - rawLogGradient w J hJ a .cell X
    have hgerm : (fun Z => cellRatio hJ d β i a b (outsideCoordinates i Z)) =ᶠ[𝓝 X]
        (fun Z => Real.exp (rawLog w J hJ b .cell Z - rawLog w J hJ a .cell Z)) :=
      Filter.mem_of_superset hn fun Z hZ => he Z hZ
    have hder : HasFDerivAt (fun Z => cellRatio hJ d β i a b (outsideCoordinates i Z))
        (InnerProductSpace.toDual ℝ (SourceSpace (otherParticles i))
          (cellRatio hJ d β i a b (outsideCoordinates i X) • G)) X := by
      apply hgerm.hasFDerivAt_iff.mpr
      rw [he X hX]
      simpa only [G, w, map_smul, map_sub, Pi.sub_apply] using! (hdb.1.sub hda.1).exp
    refine ⟨?_, fun j => ?_⟩
    · intro j
      exact source_mem_closure_patch hJ _ _ hX (otherIndexEquiv i j)
    · have hg := hasCoordinateDerivative_of_source i _ X _ hder j
      have hpb : sourceProjection (otherIndexEquiv i j) (rawLogGradient w J hJ b .cell X) =
          probeField hJ d β i b (outsideCoordinates i X) j :=
        source_probeField hJ (by omega) d β i b S hb X hX j
      have hpa : sourceProjection (otherIndexEquiv i j) (rawLogGradient w J hJ a .cell X) =
          probeField hJ d β i a (outsideCoordinates i X) j :=
        source_probeField hJ (by omega) d β i a S ha X hX j
      simpa only [map_smul, G, map_sub, hpb, hpa, ratioField] using hg
  filter_upwards [ae_jointLaw_of_outsideReference hJ η (fun _ => .cell) d β i hd] with X hX
  exact ⟨hX.1, fun j => (hX.2 j).removeSite i X⟩

def gradientBlockBound (β₀ : ℝ) (J : ℕ) : ℝ :=
  β₀ * (densityNormBound β₀ * kernelConstant * J * (1 + 3 * Real.pi) ^ (3 / 4 : ℝ))

include hβ hβ₀ hδ hη in
theorem probeField_norm_le (a : MeshIndex J) (Y : Configuration n)
    (hY : PrescribedOutside (mesh_pos hmesh) η i Y) (j : Fin n) :
    ‖probeField (mesh_pos hmesh) d β i a Y j‖ ≤ gradientBlockBound β₀ J / (n + 1 : ℝ) := by
  have hm := deleted_probe_gradient_moments hβ hβ₀ hδ hmesh η hη d i Y hY a (Y j)
  have hc := DeletedPairEnsemble.sourceCoefficient_bounds d hβ i j
  have hc' : DeletedPairEnsemble.sourceCoefficient d β i j ≤ β₀ / (n + 1 : ℝ) :=
    hc.2.trans (div_le_div_of_nonneg_right hβ₀ (by positivity))
  rw [probeField, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hc.1]
  calc
    _ ≤ (β₀ / (n + 1 : ℝ)) *
        (densityNormBound β₀ * kernelConstant * J * (1 + 3 * Real.pi) ^ (3 / 4 : ℝ)) :=
      mul_le_mul hc' hm.norm_integral_le (norm_nonneg _)
        (div_nonneg (hβ.trans hβ₀) (by positivity))
    _ = _ := by unfold gradientBlockBound; ring

include hβ hβ₀ hδ hη in
theorem ratioField_norm_le (a b : MeshIndex J) (Y : Configuration n)
    (hY : PrescribedOutside (mesh_pos hmesh) η i Y) (j : Fin n) :
    ‖ratioField (mesh_pos hmesh) d β i a b Y j‖ ≤
      (2 * gradientBlockBound β₀ J /
        kappaConstant β₀ greenLowerConstant kernelConstant J (radius β₀)) / (n + 1 : ℝ) := by
  let κ := kappaConstant β₀ greenLowerConstant kernelConstant J (radius β₀)
  have hκ : 0 < κ := kappaConstant_pos _ _ _ (mesh_pos hmesh) (by have h := radius_one_le β₀; omega)
  have hr := deleted_cell_ratio_bounds hβ hβ₀ hδ greenLowerConstant_pos.le green_lower_bound
    hmesh η hη d i Y hY a b
  have hb := probeField_norm_le hβ hβ₀ hδ hmesh η hη d i b Y hY j
  have ha := probeField_norm_le hβ hβ₀ hδ hmesh η hη d i a Y hY j
  rw [ratioField, norm_smul, Real.norm_eq_abs, abs_of_pos (hκ.trans_le hr.1)]
  calc
    _ ≤ κ⁻¹ * (‖probeField (mesh_pos hmesh) d β i b Y j‖ +
        ‖probeField (mesh_pos hmesh) d β i a Y j‖) :=
      mul_le_mul hr.2 (norm_sub_le _ _) (norm_nonneg _) (inv_pos.mpr hκ).le
    _ ≤ κ⁻¹ * (gradientBlockBound β₀ J / (n + 1 : ℝ) + gradientBlockBound β₀ J / (n + 1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hb ha) (inv_pos.mpr hκ).le
    _ = _ := by dsimp only [κ]; ring

def ratioGradientBound (β₀ : ℝ) (J : ℕ) : ℝ :=
  2 * gradientBlockBound β₀ J /
    kappaConstant β₀ greenLowerConstant kernelConstant J (radius β₀)

include hβ hβ₀ hδ hη in
theorem jointRatio_energy_le (a b : MeshIndex J) :
    ∀ᵐ X ∂DeletedPairConditionals.jointLaw (mesh_pos hmesh) η (fun _ => .cell) d β,
      (∑ k, ‖coordinateOrdinaryGradient (jointRatio (mesh_pos hmesh) d β i a b) k X‖ ^ 2) ≤
        ratioGradientBound β₀ J ^ 2 / (n + 1 : ℝ) := by
  filter_upwards [jointRatio_derivatives hβ hβ₀ hδ hmesh η hη d i a b] with X hX
  have he := sum_coordinateGradient_removeSite i
    (cellRatio (mesh_pos hmesh) d β i a b) X
    (ratioField (mesh_pos hmesh) d β i a b (removeSite i X)) (fun j => (hX.2 j).gradient)
  change (∑ k, ‖coordinateOrdinaryGradient (fun Y =>
    cellRatio (mesh_pos hmesh) d β i a b (removeSite i Y)) k X‖ ^ 2) ≤ _
  rw [he]
  calc
    _ ≤ ∑ _j : Fin n, (ratioGradientBound β₀ J / (n + 1 : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _)
        (ratioField_norm_le hβ hβ₀ hδ hmesh η hη d i a b _ hX.1 j) 2
    _ = (n : ℝ) * (ratioGradientBound β₀ J / (n + 1 : ℝ)) ^ 2 := by simp
    _ ≤ (n + 1 : ℝ) * (ratioGradientBound β₀ J / (n + 1 : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = _ := by field_simp

theorem source_poincare_nonneg (β₀ : ℝ) : 0 ≤ poincareBound β₀ := by
  unfold poincareBound OneSiteConstants.poincare
  apply le_trans _ (le_max_left _ _)
  exact div_nonneg (mul_nonneg (densityNormBound_pos β₀).le (sq_nonneg _)) (lowerBound_pos β₀).le

/-- Fixed-parameter coefficient; it is independent of labels, particles,
probe cells and beta in the admitted interval. -/
def relativeVarianceConstant (J : ℕ) (β₀ : ℝ) : ℝ :=
  (2 * poincareBound β₀ / (J : ℝ) ^ 2) * ratioGradientBound β₀ J ^ 2 /
    kappaConstant β₀ greenLowerConstant kernelConstant J (radius β₀) ^ 2

theorem relativeVarianceConstant_nonneg (J : ℕ) (β₀ : ℝ) :
    0 ≤ relativeVarianceConstant J β₀ := by
  unfold relativeVarianceConstant
  exact div_nonneg (mul_nonneg (div_nonneg (mul_nonneg (by norm_num)
    (source_poincare_nonneg β₀)) (sq_nonneg _)) (sq_nonneg _)) (sq_nonneg _)

include hβ hβ₀ hδ hη in
/-- The actual source relative variance estimate. The physical gradient
bound and integrability are conclusions, and the original joint law is
the law to which the already proved deleted-pair Poincare inequality applies. -/
theorem jointRatio_relative_variance (hN : 2 ≤ n + 1) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (a b : MeshIndex J) :
    let ν := DeletedPairConditionals.jointLaw (mesh_pos hmesh) η (fun _ => .cell) d β
    MemLp (jointRatio (mesh_pos hmesh) d β i a b) 2 ν ∧
      0 < (∫ X, jointRatio (mesh_pos hmesh) d β i a b X ∂ν) ∧
      variance (jointRatio (mesh_pos hmesh) d β i a b) ν ≤
        (relativeVarianceConstant J β₀ / (n + 1 : ℝ)) *
          (∫ X, jointRatio (mesh_pos hmesh) d β i a b X ∂ν) ^ 2 := by
  let hJ := mesh_pos hmesh
  let ν := DeletedPairConditionals.jointLaw hJ η (fun _ => .cell) d β
  let κ := kappaConstant β₀ greenLowerConstant kernelConstant J (radius β₀)
  let m := ∫ X, jointRatio hJ d β i a b X ∂ν
  have hκ : 0 < κ := kappaConstant_pos _ _ _ hJ (by have h := radius_one_le β₀; omega)
  obtain ⟨L, hL⟩ := jointRatio_lipschitz hβ hβ₀ hδ hmesh η hη d i a b
  have hf := DeletedConditionalPoincare.joint_local_finite hN hJ (mesh_two_le hmesh)
    η (fun _ => .cell) d hβ (hβ₀.trans_lt hsub) hL
  let : IsProbabilityMeasure ν := hf.1
  have hm : κ ≤ m := by
    have hl : ∀ᵐ X ∂ν, κ ≤ jointRatio hJ d β i a b X := by
      filter_upwards [jointRatio_derivatives hβ hβ₀ hδ hmesh η hη d i a b] with X hX
      exact (deleted_cell_ratio_bounds hβ hβ₀ hδ greenLowerConstant_pos.le green_lower_bound
        hmesh η hη d i _ hX.1 a b).1
    have hi := integral_mono_ae (integrable_const κ) ((hf.2.1 2).integrable (by norm_num)) hl
    simpa only [integral_const, probReal_univ, one_smul] using hi
  have hE : (∫ X, ∑ k, ‖coordinateOrdinaryGradient (jointRatio hJ d β i a b) k X‖ ^ 2 ∂ν) ≤
      ratioGradientBound β₀ J ^ 2 / (n + 1 : ℝ) := by
    have hh := integral_mono_ae hf.2.2.2 (integrable_const _)
      (jointRatio_energy_le hβ hβ₀ hδ hmesh η hη d i a b)
    simpa only [integral_const, probReal_univ, one_smul] using hh
  have hP := DeletedConditionalPoincare.cells_joint_poincare hN d hβ hβ₀ hsub hδ₀ hδ hmesh η hη hL
  have hcoef : 0 ≤ 2 * poincareBound β₀ / (J : ℝ) ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) (source_poincare_nonneg β₀)) (sq_nonneg _)
  refine ⟨hf.2.1 2, hκ.trans_le hm, ?_⟩
  calc
    _ ≤ (2 * poincareBound β₀ / (J : ℝ) ^ 2) *
        (ratioGradientBound β₀ J ^ 2 / (n + 1 : ℝ)) :=
      hP.trans (mul_le_mul_of_nonneg_left hE hcoef)
    _ = (relativeVarianceConstant J β₀ / (n + 1 : ℝ)) * κ ^ 2 := by
      have hk0 : kappaConstant β₀ greenLowerConstant kernelConstant J (radius β₀) ≠ 0 := hκ.ne'
      unfold relativeVarianceConstant
      dsimp only [κ]
      field_simp [hk0]
    _ ≤ (relativeVarianceConstant J β₀ / (n + 1 : ℝ)) * m ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hκ.le hm 2)
        (div_nonneg (relativeVarianceConstant_nonneg J β₀) (by positivity))

end RatioRegularity

section PairRestoration

open OccupationPositiveExponential MovingPoleCalculus

variable {n J : ℕ} {β β₀ δ : ℝ}

def pairEnvelope (i j : Fin (n + 1)) (X : Configuration (n + 1)) : ℝ :=
  positiveEnvelope (X i - X j)

theorem measurable_pairEnvelope (i j : Fin (n + 1)) : Measurable (pairEnvelope i j) :=
  positiveEnvelope_measurable.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

/-- A single genuine conditional integration is enough because the
one-site envelope estimate is uniform in its fixed pole. This proves
joint integrability before the real expectation is used. -/
theorem deleted_pair_envelope (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hsub : β₀ < 4) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J) (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (i j : Fin (n + 1)) (hij : i ≠ j) :
    let ν := DeletedPairConditionals.jointLaw (mesh_pos hmesh) η (fun _ => .cell) d β
    Integrable (pairEnvelope i j) ν ∧
      (∫ X, pairEnvelope i j X ∂ν) ≤ densityNormBound β₀ * envelopeBound J := by
  let hJ := mesh_pos hmesh
  let ν := DeletedPairConditionals.jointLaw hJ η (fun _ => .cell) d β
  let κ := DeletedPairConditionals.ambientKernels hJ η (fun _ => .cell) d β
  let : IsProbabilityMeasure ν := DeletedPairConditionals.jointLaw_probability hJ
    (mesh_two_le hmesh) hN η (fun _ => .cell) d hβ (hβ₀.trans_lt hsub)
  have hpres : ∀ᵐ X ∂ν, PrescribedOutside hJ η j (removeSite j X) :=
    ae_jointLaw_of_outsideReference hJ η (fun _ => .cell) d β j
      (LabelRatioTransport.ae_prescribedOutside hJ η j)
  have hcond : ∀ᵐ X ∂ν, (∫⁻ y, ENNReal.ofReal (pairEnvelope i j (Function.update X j y)) ∂κ j X) ≤
      ENNReal.ofReal (densityNormBound β₀ * envelopeBound J) := by
    filter_upwards [hpres] with X hX
    have hb := DeletedPairEnsemble.capped_source_bounds d hβ hβ₀ hδ hmesh η hη j
      (removeSite j X) hX (η j) .cell
    have he := deleted_probe_envelope_bound hβ hβ₀ hδ hmesh η hη d j
      (removeSite j X) hX (η j) (X i)
    simp only [pairEnvelope, Function.update_of_ne hij, Function.update_self]
    change (∫⁻ y, ENNReal.ofReal (positiveEnvelope (X i - y))
      ∂DeletedPairConditionals.ambientKernels hJ η (fun _ => .cell) d β j X) ≤ _
    rw [DeletedPairConditionals.ambientKernel_eq_pointLaw hJ η (fun _ => .cell) d β j X hb.1 hb.2.1]
    change (∫⁻ y, ENNReal.ofReal (positiveEnvelope (X i - y))
      ∂pointLaw (meshCellMeasure J hJ (η j)) (removeSite j X)
        (DeletedPairEnsemble.sourceCoefficient d β j)) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal he.1
      (Eventually.of_forall fun y => positiveEnvelope_nonneg (X i - y))]
    exact ENNReal.ofReal_le_ofReal he.2
  have hlin : (∫⁻ X, ENNReal.ofReal (pairEnvelope i j X) ∂ν) ≤
      ENNReal.ofReal (densityNormBound β₀ * envelopeBound J) := by
    rw [← CoordinateConditionalKernels.lintegral_resample κ ν
      (DeletedPairConditionals.preservesLaw_ambientKernels hJ (mesh_two_le hmesh) hN
        η (fun _ => .cell) d hβ (hβ₀.trans_lt hsub)) j (measurable_pairEnvelope i j).ennreal_ofReal]
    exact (lintegral_mono_ae hcond).trans_eq (by simp)
  have hi : Integrable (pairEnvelope i j) ν :=
    (lintegral_ofReal_ne_top_iff_integrable (measurable_pairEnvelope i j).aestronglyMeasurable
      (Eventually.of_forall fun X => positiveEnvelope_nonneg (X i - X j))).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin)
  refine ⟨hi, ?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun X => positiveEnvelope_nonneg (X i - X j))
  rw [← he] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (densityNormBound_pos β₀).le
    (envelopeBound_nonneg J))).mp hlin

def restorationFactor (p : DeletedPairEnsemble.Pair (n + 1)) (β : ℝ)
    (X : Configuration (n + 1)) : ℝ :=
  Real.exp ((β / (n + 1 : ℝ)) * regularGreenRepresentative (X p.val.1 - X p.val.2))

theorem measurable_restorationFactor (p : DeletedPairEnsemble.Pair (n + 1)) (β : ℝ) :
    Measurable (restorationFactor p β) :=
  ((regularGreenRepresentative_measurable.comp
    ((measurable_pi_apply p.val.1).sub (measurable_pi_apply p.val.2))).const_mul _).exp

theorem deleted_pair_kernel_ae (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (η : LabelVector J (n + 1)) (p : DeletedPairEnsemble.Pair (n + 1)) (β : ℝ) :
    ∀ᵐ X ∂DeletedPairConditionals.jointLaw hJ η (fun _ => .cell) (some p) β,
      regularGreenRepresentative (X p.val.1 - X p.val.2) =
        greenRealRepresentative (X p.val.1 - X p.val.2) := by
  have hac : DeletedPairConditionals.jointLaw hJ η (fun _ => .cell) (some p) β ≪ referenceMeasure (n + 1) :=
    (PositiveProductConditionals.productLaw_absolutelyContinuous _ _).trans
      (DeletedPairEnsemble.domainReference_absolutelyContinuous hJ hJ2 η (fun _ => .cell))
  exact hac.ae_le ((quasiMeasurePreserving_pair_difference (n + 1) p.property.ne).ae_eq_comp
    regularGreenRepresentative_ae)

/-- Actual finite restoration expectation, with both one-sided source
bounds and no assumption about pair correlations under deletion. -/
theorem restoration_bounds (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hsub : β₀ < 4) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J) (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (p : DeletedPairEnsemble.Pair (n + 1)) (hlarge : 4 * β₀ ≤ (n + 1 : ℝ)) :
    let ν := DeletedPairConditionals.jointLaw (mesh_pos hmesh) η (fun _ => .cell) (some p) β
    Integrable (restorationFactor p β) ν ∧
      Real.exp (-(β₀ * greenLowerConstant / (n + 1 : ℝ))) ≤
        (∫ X, restorationFactor p β X ∂ν) ∧
      (∫ X, restorationFactor p β X ∂ν) ≤
        1 + (β₀ * (densityNormBound β₀ * envelopeBound J)) / (n + 1 : ℝ) := by
  let hJ := mesh_pos hmesh
  let ν := DeletedPairConditionals.jointLaw hJ η (fun _ => .cell) (some p) β
  let : IsProbabilityMeasure ν := DeletedPairConditionals.jointLaw_probability hJ
    (mesh_two_le hmesh) hN η (fun _ => .cell) (some p) hβ (hβ₀.trans_lt hsub)
  let u := β / (n + 1 : ℝ)
  have hu : 0 ≤ u := div_nonneg hβ (by positivity)
  have hu4 : u ≤ 1 / 4 := (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr (by linarith)
  have hE := deleted_pair_envelope hN hβ hβ₀ hsub hδ hmesh η hη (some p) p.val.1 p.val.2 p.property.ne
  have hp : ∀ᵐ X ∂ν, restorationFactor p β X ≤ 1 + u * pairEnvelope p.val.1 p.val.2 X := by
    filter_upwards [deleted_pair_kernel_ae hJ (mesh_two_le hmesh) η p β] with X hX
    unfold restorationFactor
    rw [hX]
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_max_left _ _) hu)).trans
      (exp_le_one_add_envelope hu hu4 (positiveGreen_nonneg _))
  have hmaj : Integrable (fun X => 1 + u * pairEnvelope p.val.1 p.val.2 X) ν :=
    (integrable_const 1).add (hE.1.const_mul u)
  have hi : Integrable (restorationFactor p β) ν := by
    apply hmaj.mono' (measurable_restorationFactor p β).aestronglyMeasurable
    filter_upwards [hp] with X hX
    simpa only [restorationFactor, Real.norm_of_nonneg (Real.exp_pos _).le] using hX
  refine ⟨hi, ?_, ?_⟩
  · have hlo (X : Configuration (n + 1)) :
        Real.exp (-(β₀ * greenLowerConstant / (n + 1 : ℝ))) ≤ restorationFactor p β X := by
      apply Real.exp_le_exp.mpr
      have hg := mul_le_mul_of_nonneg_left (green_lower_bound (X p.val.1 - X p.val.2)) hu
      have hb := mul_le_mul_of_nonneg_right hβ₀ greenLowerConstant_pos.le
      dsimp only [u] at hg
      have hdiv := div_le_div_of_nonneg_right hb (by positivity : (0 : ℝ) ≤ n + 1)
      simp only [div_eq_mul_inv, mul_neg, mul_assoc] at hg hdiv ⊢
      nlinarith [hg, hdiv]
    have hh := integral_mono_ae (integrable_const _) hi (Eventually.of_forall hlo)
    simpa only [integral_const, probReal_univ, one_smul] using hh
  · calc
      _ ≤ ∫ X, 1 + u * pairEnvelope p.val.1 p.val.2 X ∂ν := integral_mono_ae hi hmaj hp
      _ = 1 + u * ∫ X, pairEnvelope p.val.1 p.val.2 X ∂ν := by
        rw [integral_add (integrable_const _) (hE.1.const_mul u), integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul]
        rfl
      _ ≤ 1 + u * (densityNormBound β₀ * envelopeBound J) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hE.2 hu)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hβ₀ (by positivity : (0 : ℝ) ≤ n + 1))
          (mul_nonneg (densityNormBound_pos β₀).le (envelopeBound_nonneg J))
        dsimp only [u]
        apply add_le_add le_rfl
        simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh

end PairRestoration

section NormalizedTransport

variable {n J : ℕ}

theorem deletedPartition_ne_zero (hJ : 0 < J) (η : LabelVector J (n + 1))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) :
    deletedPartition hJ η d β ≠ 0 :=
  PositiveProductConditionals.normalizer_ne_zero _
    (DeletedPairEnsemble.measurable_weight regularGreenRepresentative_measurable d β)
    (DeletedPairEnsemble.weight_pos regularGreenRepresentative d β)

theorem deletedPartition_ne_top (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ n + 1)
    (η : LabelVector J (n + 1)) (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) : deletedPartition hJ η d β ≠ ⊤ :=
  (DeletedPairEnsemble.regular_domain_normalization hJ hJ2 hN η (fun _ => .cell) d hβ hsub).2.2.1

theorem deletedPartition_real_pos (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ n + 1)
    (η : LabelVector J (n + 1)) (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) : 0 < (deletedPartition hJ η d β).toReal :=
  ENNReal.toReal_pos (deletedPartition_ne_zero hJ η d β)
    (deletedPartition_ne_top hJ hJ2 hN η d hβ hsub)

theorem jointRatio_nonneg (hJ : 0 < J) (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    (β : ℝ) (i : Fin (n + 1)) (a b : MeshIndex J) (X : Configuration (n + 1)) :
    0 ≤ jointRatio hJ d β i a b X :=
  div_nonneg (integral_nonneg fun z => (torusWeight_pos _ _ z).le)
    (integral_nonneg fun z => (torusWeight_pos _ _ z).le)

theorem deleted_outside_lintegral (hJ : 0 < J) (η : LabelVector J (n + 1))
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (i : Fin (n + 1))
    {F : Configuration n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ Y, F Y ∂Measure.map (removeSite i)
      (DeletedPairConditionals.jointLaw hJ η (fun _ => .cell) d β)) =
      (deletedPartition hJ η d β)⁻¹ * ∫⁻ Y,
        (ENNReal.ofReal (deletedOutsideWeight d β i Y) * deletedCellMass hJ d β i (η i) Y) * F Y
        ∂outsideReference (fun k => meshCellMeasure J hJ (η k)) i := by
  have hd : Measurable (fun Y : Configuration n => (deletedPartition hJ η d β)⁻¹ *
      (ENNReal.ofReal (deletedOutsideWeight d β i Y) * deletedCellMass hJ d β i (η i) Y)) :=
    measurable_const.mul ((measurable_deletedOutsideWeight d β i).ennreal_ofReal.mul
      (measurable_deletedCellMass hJ d β i (η i)))
  have hm : Measurable (fun Y : Configuration n =>
      (ENNReal.ofReal (deletedOutsideWeight d β i Y) * deletedCellMass hJ d β i (η i) Y) * F Y) :=
    ((measurable_deletedOutsideWeight d β i).ennreal_ofReal.mul
      (measurable_deletedCellMass hJ d β i (η i))).mul hF
  rw [deleted_outsideMarginal, lintegral_withDensity_eq_lintegral_mul _ hd hF,
    ← lintegral_const_mul _ hm]
  apply lintegral_congr
  intro Y
  exact mul_assoc _ _ _

theorem outsideReference_update (hJ : 0 < J) (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (b : MeshIndex J) :
    outsideReference (fun k => meshCellMeasure J hJ (Function.update η i b k)) i =
      outsideReference (fun k => meshCellMeasure J hJ (η k)) i := by
  unfold outsideReference
  congr 1
  funext k
  dsimp only
  rw [Function.update_of_ne (Fin.succAbove_ne i k)]

variable {β β₀ δ : ℝ} (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
  (hsub : β₀ < 4) (hδ : δ ≤ occupationBound β₀)
  (hmesh : 8 * (radius β₀ + 4) ≤ J) (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
  (d : Option (DeletedPairEnsemble.Pair (n + 1))) (i : Fin (n + 1))

include hN hβ hβ₀ hsub hδ hη in
theorem deleted_normalized_transport (b : MeshIndex J) {F : Configuration n → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ Y, ENNReal.ofReal (cellRatio (mesh_pos hmesh) d β i (η i) b Y) * F Y
      ∂Measure.map (removeSite i)
        (DeletedPairConditionals.jointLaw (mesh_pos hmesh) η (fun _ => .cell) d β)) =
      (deletedPartition (mesh_pos hmesh) (Function.update η i b) d β /
        deletedPartition (mesh_pos hmesh) η d β) *
      ∫⁻ Y, F Y ∂Measure.map (removeSite i)
        (DeletedPairConditionals.jointLaw (mesh_pos hmesh) (Function.update η i b) (fun _ => .cell) d β) := by
  let hJ := mesh_pos hmesh
  rw [deleted_weighted_transport hβ hβ₀ hδ hmesh η hη d i b hF,
    deleted_outside_lintegral hJ (Function.update η i b) d β i hF,
    outsideReference_update]
  simp only [Function.update_self]
  have hZ0 := deletedPartition_ne_zero hJ (Function.update η i b) d β
  have hZt := deletedPartition_ne_top hJ (mesh_two_le hmesh) hN (Function.update η i b) d hβ
    (hβ₀.trans_lt hsub)
  rw [div_eq_mul_inv]
  symm
  calc
    _ = (deletedPartition hJ (Function.update η i b) d β *
        (deletedPartition hJ (Function.update η i b) d β)⁻¹) *
        ((deletedPartition hJ η d β)⁻¹ * ∫⁻ Y,
          (ENNReal.ofReal (deletedOutsideWeight d β i Y) * deletedCellMass hJ d β i b Y) * F Y
          ∂outsideReference (fun k => meshCellMeasure J hJ (η k)) i) := by
            simp only [mul_assoc, mul_comm, mul_left_comm]
    _ = _ := by rw [ENNReal.mul_inv_cancel hZ0 hZt, one_mul]

include hN hβ hβ₀ hsub hδ hη in
/-- Transport with an actual observable independent of the moved site.
The required independence will be discharged by the deleted coefficient. -/
theorem deleted_joint_transport (b : MeshIndex J) {F : Configuration (n + 1) → ℝ≥0∞}
    (hF : Measurable F) (hFi : ∀ X z, F (Function.update X i z) = F X) :
    (∫⁻ X, ENNReal.ofReal (jointRatio (mesh_pos hmesh) d β i (η i) b X) * F X
      ∂DeletedPairConditionals.jointLaw (mesh_pos hmesh) η (fun _ => .cell) d β) =
      (deletedPartition (mesh_pos hmesh) (Function.update η i b) d β /
        deletedPartition (mesh_pos hmesh) η d β) *
      ∫⁻ X, F X ∂DeletedPairConditionals.jointLaw (mesh_pos hmesh)
        (Function.update η i b) (fun _ => .cell) d β := by
  let hJ := mesh_pos hmesh
  let f := fun Y : Configuration n => F (insertSite i 0 Y)
  have hf : Measurable f := hF.comp ((measurable_insertSite i).comp (measurable_const.prodMk measurable_id))
  have he (X : Configuration (n + 1)) : f (removeSite i X) = F X := by
    dsimp only [f]
    rw [CoordinateConditionalKernels.insertSite_eq_update, hFi]
  have hm : Measurable (fun Y => ENNReal.ofReal (cellRatio hJ d β i (η i) b Y) * f Y) :=
    (measurable_cellRatio hJ d β i (η i) b).ennreal_ofReal.mul hf
  have hh := deleted_normalized_transport hN hβ hβ₀ hsub hδ hmesh η hη d i b hf
  rw [lintegral_map hm (measurable_removeSite i), lintegral_map hf (measurable_removeSite i)] at hh
  simpa only [he, jointRatio] using hh

include hβ hβ₀ hδ hη in
theorem deleted_single_ratio_joint (b : MeshIndex J) :
    (∫⁻ X, ENNReal.ofReal (jointRatio (mesh_pos hmesh) d β i (η i) b X)
      ∂DeletedPairConditionals.jointLaw (mesh_pos hmesh) η (fun _ => .cell) d β) =
      deletedPartition (mesh_pos hmesh) (Function.update η i b) d β /
        deletedPartition (mesh_pos hmesh) η d β := by
  have hh := deleted_partition_ratio_lintegral hβ hβ₀ hδ hmesh η hη d i b
  rw [lintegral_map (measurable_cellRatio _ d β i (η i) b).ennreal_ofReal (measurable_removeSite i)] at hh
  exact hh

include hN hβ hβ₀ hsub hδ hη in
/-- The fourth actual partition function is the product moment. The
second probe is independent of the first selected site because its exact
coefficient is zero, so no independence of the remaining law is assumed. -/
theorem deleted_double_ratio_joint (p : DeletedPairEnsemble.Pair (n + 1)) (b c : MeshIndex J)
    (hηb : OccupationCap δ (Function.update η p.val.1 b)) :
    (∫⁻ X, ENNReal.ofReal (jointRatio (mesh_pos hmesh) (some p) β p.val.1 (η p.val.1) b X) *
      ENNReal.ofReal (jointRatio (mesh_pos hmesh) (some p) β p.val.2 (η p.val.2) c X)
      ∂DeletedPairConditionals.jointLaw (mesh_pos hmesh) η (fun _ => .cell) (some p) β) =
      deletedPartition (mesh_pos hmesh) (Function.update (Function.update η p.val.1 b) p.val.2 c) (some p) β /
        deletedPartition (mesh_pos hmesh) η (some p) β := by
  let hJ := mesh_pos hmesh
  have hm := (measurable_jointRatio hJ (some p) β p.val.2 (η p.val.2) c).ennreal_ofReal
  have hs := deleted_joint_transport hN hβ hβ₀ hsub hδ hmesh η hη (some p) p.val.1 b hm (by
    intro X z
    congr 1
    exact jointRatio_update hJ (some p) β p.val.2 p.val.1 (η p.val.2) c X z
      (Or.inr (by simp [DeletedPairEnsemble.isDeleted])))
  have ht := deleted_single_ratio_joint hβ hβ₀ hδ hmesh (Function.update η p.val.1 b) hηb
    (some p) p.val.2 c
  simp only [Function.update_of_ne p.property.ne.symm] at ht
  rw [ht] at hs
  rw [hs]
  have hZ0 := deletedPartition_ne_zero hJ (Function.update η p.val.1 b) (some p) β
  have hZt := deletedPartition_ne_top hJ (mesh_two_le hmesh) hN (Function.update η p.val.1 b)
    (some p) hβ (hβ₀.trans_lt hsub)
  simp only [div_eq_mul_inv]
  calc
    _ = (deletedPartition hJ (Function.update (Function.update η p.val.1 b) p.val.2 c) (some p) β *
        (deletedPartition hJ η (some p) β)⁻¹) *
        (deletedPartition hJ (Function.update η p.val.1 b) (some p) β *
          (deletedPartition hJ (Function.update η p.val.1 b) (some p) β)⁻¹) := by
            simp only [mul_assoc, mul_comm, mul_left_comm]
    _ = _ := by rw [ENNReal.mul_inv_cancel hZ0 hZt, mul_one]

end NormalizedTransport

section RealPartitionIdentities

variable {n J : ℕ}

theorem weight_mul_restoration (p : DeletedPairEnsemble.Pair (n + 1)) (β : ℝ)
    (X : Configuration (n + 1)) :
    DeletedPairEnsemble.weight regularGreenRepresentative (some p) β X * restorationFactor p β X =
      DeletedPairEnsemble.weight regularGreenRepresentative none β X := by
  rw [DeletedPairEnsemble.weight_none, DeletedPairEnsemble.weight_eq_ratio]
  simp only [DeletedPairEnsemble.removedValue, restorationFactor, Nat.cast_add, Nat.cast_one]
  rw [mul_assoc, ← Real.exp_add]
  have he : -(β / (n + 1 : ℝ)) * regularGreenRepresentative (X p.val.1 - X p.val.2) +
      (β / (n + 1 : ℝ)) * regularGreenRepresentative (X p.val.1 - X p.val.2) = 0 := by ring
  rw [he, Real.exp_zero, mul_one]

theorem restoration_partition_lintegral (hJ : 0 < J) (η : LabelVector J (n + 1))
    (p : DeletedPairEnsemble.Pair (n + 1)) (β : ℝ) :
    (∫⁻ X, ENNReal.ofReal (restorationFactor p β X)
      ∂DeletedPairConditionals.jointLaw hJ η (fun _ => .cell) (some p) β) =
      deletedPartition hJ η none β / deletedPartition hJ η (some p) β := by
  change (∫⁻ X, ENNReal.ofReal (restorationFactor p β X)
    ∂PositiveProductConditionals.productLaw (fun k => meshCellMeasure J hJ (η k))
      (DeletedPairEnsemble.weight regularGreenRepresentative (some p) β)) = _
  rw [PositiveProductConditionals.productLaw, lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul _
      (PositiveProductConditionals.measurable_density
        (DeletedPairEnsemble.measurable_weight regularGreenRepresentative_measurable (some p) β))
      (measurable_restorationFactor p β).ennreal_ofReal]
  rw [div_eq_mul_inv, mul_comm (deletedPartition hJ η none β)]
  congr 1
  apply lintegral_congr
  intro X
  change ENNReal.ofReal (DeletedPairEnsemble.weight regularGreenRepresentative (some p) β X) *
    ENNReal.ofReal (restorationFactor p β X) =
      ENNReal.ofReal (DeletedPairEnsemble.weight regularGreenRepresentative none β X)
  rw [← ENNReal.ofReal_mul (DeletedPairEnsemble.weight_pos regularGreenRepresentative (some p) β X).le,
    weight_mul_restoration]

theorem deletedPartition_none (hJ : 0 < J) (η : LabelVector J (n + 1)) (β : ℝ) :
    deletedPartition hJ η none β = labelPartitionFunction hJ η β := by
  rw [OccupationPartitionTransport.labelPartition_eq_productNormalizer]
  unfold deletedPartition
  rw [DeletedPairEnsemble.weight_none]
  rfl

/-- The restoration error has a fixed-parameter coefficient and the
original particle denominator. -/
def restorationConstant (J : ℕ) (β₀ : ℝ) : ℝ :=
  β₀ * (MovingPoleCalculus.greenLowerConstant +
    densityNormBound β₀ * OccupationPositiveExponential.envelopeBound J)

theorem restorationConstant_nonneg (J : ℕ) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    0 ≤ restorationConstant J β₀ :=
  mul_nonneg hβ₀ (add_nonneg MovingPoleCalculus.greenLowerConstant_pos.le
    (mul_nonneg (densityNormBound_pos β₀).le (OccupationPositiveExponential.envelopeBound_nonneg J)))

variable {β β₀ δ : ℝ} (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
  (hsub : β₀ < 4) (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
  (hmesh : 8 * (radius β₀ + 4) ≤ J) (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
  (d : Option (DeletedPairEnsemble.Pair (n + 1))) (i : Fin (n + 1))

include hN hβ hβ₀ hsub hδ₀ hδ hη in
theorem deleted_single_ratio_real (b : MeshIndex J) :
    (∫ X, jointRatio (mesh_pos hmesh) d β i (η i) b X
      ∂DeletedPairConditionals.jointLaw (mesh_pos hmesh) η (fun _ => .cell) d β) =
      (deletedPartition (mesh_pos hmesh) (Function.update η i b) d β).toReal /
        (deletedPartition (mesh_pos hmesh) η d β).toReal := by
  let ν := DeletedPairConditionals.jointLaw (mesh_pos hmesh) η (fun _ => .cell) d β
  let : IsProbabilityMeasure ν := DeletedPairConditionals.jointLaw_probability (mesh_pos hmesh)
    (mesh_two_le hmesh) hN η (fun _ => .cell) d hβ (hβ₀.trans_lt hsub)
  have hi := (jointRatio_relative_variance hβ hβ₀ hδ hmesh η hη d i hN hsub hδ₀ (η i) b).1.integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have he := ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall
    (jointRatio_nonneg (mesh_pos hmesh) d β i (η i) b))
  rw [deleted_single_ratio_joint hβ hβ₀ hδ hmesh η hη d i b] at he
  have hr := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg
    (jointRatio_nonneg (mesh_pos hmesh) d β i (η i) b)), ENNReal.toReal_div] using hr

include hN hβ hβ₀ hsub hδ₀ hδ hη in
theorem deleted_double_ratio_real (p : DeletedPairEnsemble.Pair (n + 1)) (b c : MeshIndex J)
    (hηb : OccupationCap δ (Function.update η p.val.1 b)) :
    (∫ X, jointRatio (mesh_pos hmesh) (some p) β p.val.1 (η p.val.1) b X *
      jointRatio (mesh_pos hmesh) (some p) β p.val.2 (η p.val.2) c X
      ∂DeletedPairConditionals.jointLaw (mesh_pos hmesh) η (fun _ => .cell) (some p) β) =
      (deletedPartition (mesh_pos hmesh) (Function.update (Function.update η p.val.1 b) p.val.2 c)
        (some p) β).toReal / (deletedPartition (mesh_pos hmesh) η (some p) β).toReal := by
  let hJ := mesh_pos hmesh
  let ν := DeletedPairConditionals.jointLaw hJ η (fun _ => .cell) (some p) β
  let : IsProbabilityMeasure ν := DeletedPairConditionals.jointLaw_probability hJ
    (mesh_two_le hmesh) hN η (fun _ => .cell) (some p) hβ (hβ₀.trans_lt hsub)
  have hA := (jointRatio_relative_variance hβ hβ₀ hδ hmesh η hη (some p) p.val.1
    hN hsub hδ₀ (η p.val.1) b).1
  have hB := (jointRatio_relative_variance hβ hβ₀ hδ hmesh η hη (some p) p.val.2
    hN hsub hδ₀ (η p.val.2) c).1
  have hn X : 0 ≤ jointRatio hJ (some p) β p.val.1 (η p.val.1) b X *
      jointRatio hJ (some p) β p.val.2 (η p.val.2) c X :=
    mul_nonneg (jointRatio_nonneg _ _ _ _ _ _ _) (jointRatio_nonneg _ _ _ _ _ _ _)
  have he := ofReal_integral_eq_lintegral_ofReal (hA.integrable_mul hB) (Eventually.of_forall hn)
  simp only [Pi.mul_apply, ENNReal.ofReal_mul (jointRatio_nonneg hJ (some p) β p.val.1 (η p.val.1) b _)] at he
  rw [deleted_double_ratio_joint hN hβ hβ₀ hsub hδ hmesh η hη p b c hηb] at he
  have hr := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hn), ENNReal.toReal_div] using hr

include hN hβ hβ₀ hsub hδ hη in
theorem restoration_log_error (p : DeletedPairEnsemble.Pair (n + 1))
    (hlarge : 4 * β₀ ≤ (n + 1 : ℝ)) :
    |Real.log (labelPartitionFunction (mesh_pos hmesh) η β).toReal -
      Real.log (deletedPartition (mesh_pos hmesh) η (some p) β).toReal| ≤
      restorationConstant J β₀ / (n + 1 : ℝ) := by
  let hJ := mesh_pos hmesh
  have hb := restoration_bounds hN hβ hβ₀ hsub hδ hmesh η hη p hlarge
  have he := ofReal_integral_eq_lintegral_ofReal hb.1
    (Eventually.of_forall fun X => (Real.exp_pos _).le)
  rw [restoration_partition_lintegral hJ η p β] at he
  have hr := congrArg ENNReal.toReal he
  have hn : 0 ≤ ∫ X, restorationFactor p β X
      ∂DeletedPairConditionals.jointLaw hJ η (fun _ => .cell) (some p) β :=
    integral_nonneg fun X => (Real.exp_pos _).le
  simp only [ENNReal.toReal_ofReal hn, ENNReal.toReal_div, deletedPartition_none] at hr
  have hlog := restoration_log_bound
    (div_nonneg (mul_nonneg (hβ.trans hβ₀) MovingPoleCalculus.greenLowerConstant_pos.le) (by positivity))
    (div_nonneg (mul_nonneg (hβ.trans hβ₀) (mul_nonneg (densityNormBound_pos β₀).le
      (OccupationPositiveExponential.envelopeBound_nonneg J))) (by positivity)) hb.2.1 hb.2.2
  rw [hr, Real.log_div
    (by rw [← deletedPartition_none]; exact (deletedPartition_real_pos hJ (mesh_two_le hmesh) hN η none
      hβ (hβ₀.trans_lt hsub)).ne')
    (deletedPartition_real_pos hJ (mesh_two_le hmesh) hN η (some p) hβ (hβ₀.trans_lt hsub)).ne'] at hlog
  convert hlog.2 using 1
  unfold restorationConstant
  ring

end RealPartitionIdentities

section PairOutside

variable {n J : ℕ}

/-- The remaining positions form an actual pushforward of the original
N-particle deleted law; they are never identified with an (N-2)-particle Gibbs law. -/
abbrev PairOutsideSpace (p : DeletedPairEnsemble.Pair (n + 1)) :=
  {k : Fin (n + 1) // k ≠ p.val.1 ∧ k ≠ p.val.2} → Torus

def pairProject (p : DeletedPairEnsemble.Pair (n + 1))
    (X : Configuration (n + 1)) : PairOutsideSpace p := fun k => X k

def pairFill (p : DeletedPairEnsemble.Pair (n + 1)) (Y : PairOutsideSpace p) : Configuration (n + 1) :=
  fun k => if h : k ≠ p.val.1 ∧ k ≠ p.val.2 then Y ⟨k, h⟩ else 0

theorem measurable_pairProject (p : DeletedPairEnsemble.Pair (n + 1)) : Measurable (pairProject p) := by
  exact Measurable.of_eval fun k => measurable_pi_apply k.val

theorem measurable_pairFill (p : DeletedPairEnsemble.Pair (n + 1)) : Measurable (pairFill p) := by
  classical
  apply Measurable.of_eval
  intro k
  by_cases h : k ≠ p.val.1 ∧ k ≠ p.val.2
  · simpa only [pairFill, dite_eq_left h] using measurable_pi_apply (⟨k, h⟩ : {k // k ≠ p.val.1 ∧ k ≠ p.val.2})
  · simpa only [pairFill, dite_eq_right h] using (measurable_const : Measurable (fun _ : PairOutsideSpace p => (0 : Torus)))

theorem pairFill_project (p : DeletedPairEnsemble.Pair (n + 1)) (X : Configuration (n + 1)) :
    pairFill p (pairProject p X) = Function.update (Function.update X p.val.1 0) p.val.2 0 := by
  classical
  funext k
  by_cases hk1 : k = p.val.1
  · subst k; simp [pairFill, p.property.ne]
  · by_cases hk2 : k = p.val.2
    · subst k; simp [pairFill]
    · simp [pairFill, pairProject, hk1, hk2]

def pairOutsideLaw (hJ : 0 < J) (η : LabelVector J (n + 1))
    (p : DeletedPairEnsemble.Pair (n + 1)) (β : ℝ) : Measure (PairOutsideSpace p) :=
  Measure.map (pairProject p) (DeletedPairConditionals.jointLaw hJ η (fun _ => .cell) (some p) β)

def outsideRatio (hJ : 0 < J) (p : DeletedPairEnsemble.Pair (n + 1)) (β : ℝ)
    (i : Fin (n + 1)) (a b : MeshIndex J) (Y : PairOutsideSpace p) : ℝ :=
  jointRatio hJ (some p) β i a b (pairFill p Y)

theorem outsideRatio_project (hJ : 0 < J) (p : DeletedPairEnsemble.Pair (n + 1)) (β : ℝ)
    (i : Fin (n + 1)) (hi : i = p.val.1 ∨ i = p.val.2) (a b : MeshIndex J) (X : Configuration (n + 1)) :
    outsideRatio hJ p β i a b (pairProject p X) = jointRatio hJ (some p) β i a b X := by
  unfold outsideRatio
  rw [pairFill_project]
  rw [jointRatio_update hJ (some p) β i p.val.2 a b _ 0 (by
    rcases hi with rfl | rfl
    · exact Or.inr (by simp [DeletedPairEnsemble.isDeleted])
    · exact Or.inl rfl)]
  exact jointRatio_update hJ (some p) β i p.val.1 a b X 0 (by
    rcases hi with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by simp [DeletedPairEnsemble.isDeleted]))

theorem outsideRatio_moments (hJ : 0 < J) (η : LabelVector J (n + 1))
    (p : DeletedPairEnsemble.Pair (n + 1)) (β : ℝ) (i : Fin (n + 1))
    (hi : i = p.val.1 ∨ i = p.val.2) (a b : MeshIndex J) :
    (∫ Y, outsideRatio hJ p β i a b Y ∂pairOutsideLaw hJ η p β) =
      (∫ X, jointRatio hJ (some p) β i a b X ∂DeletedPairConditionals.jointLaw hJ η (fun _ => .cell) (some p) β) ∧
    variance (outsideRatio hJ p β i a b) (pairOutsideLaw hJ η p β) =
      variance (jointRatio hJ (some p) β i a b) (DeletedPairConditionals.jointLaw hJ η (fun _ => .cell) (some p) β) := by
  have hm : Measurable (outsideRatio hJ p β i a b) :=
    (measurable_jointRatio hJ (some p) β i a b).comp (measurable_pairFill p)
  constructor
  · rw [pairOutsideLaw, integral_map (measurable_pairProject p).aemeasurable hm.aestronglyMeasurable]
    simp only [outsideRatio_project hJ p β i hi a b]
  · rw [pairOutsideLaw, variance_map hm.aemeasurable (measurable_pairProject p).aemeasurable]
    congr 1
    funext X
    exact outsideRatio_project hJ p β i hi a b X

end PairOutside

section SourceLogarithms

variable {n J : ℕ}

theorem outsideRatio_product_moment (hJ : 0 < J) (η : LabelVector J (n + 1))
    (p : DeletedPairEnsemble.Pair (n + 1)) (β : ℝ) (a b c e : MeshIndex J) :
    (∫ Y, outsideRatio hJ p β p.val.1 a b Y * outsideRatio hJ p β p.val.2 c e Y
      ∂pairOutsideLaw hJ η p β) =
      (∫ X, jointRatio hJ (some p) β p.val.1 a b X * jointRatio hJ (some p) β p.val.2 c e X
        ∂DeletedPairConditionals.jointLaw hJ η (fun _ => .cell) (some p) β) := by
  have hA := (measurable_jointRatio hJ (some p) β p.val.1 a b).comp (measurable_pairFill p)
  have hB := (measurable_jointRatio hJ (some p) β p.val.2 c e).comp (measurable_pairFill p)
  have hm : Measurable (fun Y => outsideRatio hJ p β p.val.1 a b Y * outsideRatio hJ p β p.val.2 c e Y) := by
    have hh := hA.mul hB
    change Measurable (fun Y => outsideRatio hJ p β p.val.1 a b Y * outsideRatio hJ p β p.val.2 c e Y) at hh
    exact hh
  rw [pairOutsideLaw, integral_map (measurable_pairProject p).aemeasurable hm.aestronglyMeasurable]
  simp only [outsideRatio_project hJ p β p.val.1 (Or.inl rfl) a b,
    outsideRatio_project hJ p β p.val.2 (Or.inr rfl) c e]

theorem log_partition_cross_ratio {z₀ z₁ z₂ z₃ : ℝ}
    (h₀ : 0 < z₀) (h₁ : 0 < z₁) (h₂ : 0 < z₂) (h₃ : 0 < z₃) :
    Real.log ((z₃ / z₀) / ((z₁ / z₀) * (z₂ / z₀))) =
      Real.log z₃ - Real.log z₁ - Real.log z₂ + Real.log z₀ := by
  have he : (z₃ / z₀) / ((z₁ / z₀) * (z₂ / z₀)) = (z₃ * z₀) / (z₁ * z₂) := by
    field_simp
  rw [he, Real.log_div (mul_pos h₃ h₀).ne' (mul_pos h₁ h₂).ne',
    Real.log_mul h₃.ne' h₀.ne', Real.log_mul h₁.ne' h₂.ne']
  ring

/-- The threshold is chosen once for fixed J and beta0. It controls
both the covariance logarithm and the restored singular exponential. -/
def secondDifferenceThreshold (J : ℕ) (β₀ : ℝ) : ℕ :=
  max (OccupationFieldApproximation.fieldThreshold β₀) ⌈2 * relativeVarianceConstant J β₀⌉₊

def secondDifferenceConstant (J : ℕ) (β₀ : ℝ) : ℝ :=
  2 * relativeVarianceConstant J β₀ + 4 * restorationConstant J β₀

theorem secondDifferenceConstant_nonneg (J : ℕ) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    0 ≤ secondDifferenceConstant J β₀ :=
  add_nonneg (mul_nonneg (by norm_num) (relativeVarianceConstant_nonneg J β₀))
    (mul_nonneg (by norm_num) (restorationConstant_nonneg J hβ₀))

theorem secondDifferenceThreshold_bounds {N J : ℕ} {β₀ : ℝ}
    (hN : secondDifferenceThreshold J β₀ ≤ N) :
    2 ≤ N ∧ 4 * β₀ ≤ (N : ℝ) ∧ relativeVarianceConstant J β₀ / (N : ℝ) ≤ 1 / 2 := by
  have hf := OccupationFieldApproximation.fieldThreshold_bounds ((le_max_left _ _).trans hN)
  have hv : 2 * relativeVarianceConstant J β₀ ≤ (N : ℝ) :=
    Nat.ceil_le.mp ((le_max_right _ _).trans hN)
  refine ⟨hf.1, by linarith [hf.2], ?_⟩
  have hpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  exact (div_le_iff₀ hpos).mpr (by linarith)

variable {β β₀ δ : ℝ} (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
  (hsub : β₀ < 4) (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀)
  (hmesh : 8 * (radius β₀ + 4) ≤ J) (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)

include hN hβ hβ₀ hsub hδ₀ hδ hη in
theorem outsideRatio_relative_variance (p : DeletedPairEnsemble.Pair (n + 1))
    (i : Fin (n + 1)) (hi : i = p.val.1 ∨ i = p.val.2) (a b : MeshIndex J) :
    MemLp (outsideRatio (mesh_pos hmesh) p β i a b) 2 (pairOutsideLaw (mesh_pos hmesh) η p β) ∧
      0 < (∫ Y, outsideRatio (mesh_pos hmesh) p β i a b Y ∂pairOutsideLaw (mesh_pos hmesh) η p β) ∧
      variance (outsideRatio (mesh_pos hmesh) p β i a b) (pairOutsideLaw (mesh_pos hmesh) η p β) ≤
        (relativeVarianceConstant J β₀ / (n + 1 : ℝ)) *
          (∫ Y, outsideRatio (mesh_pos hmesh) p β i a b Y ∂pairOutsideLaw (mesh_pos hmesh) η p β) ^ 2 := by
  have hf := jointRatio_relative_variance hβ hβ₀ hδ hmesh η hη (some p) i hN hsub hδ₀ a b
  have hm := (measurable_jointRatio (mesh_pos hmesh) (some p) β i a b).comp (measurable_pairFill p)
  have ht := outsideRatio_moments (mesh_pos hmesh) η p β i hi a b
  refine ⟨?_, ht.1.symm ▸ hf.2.1, ?_⟩
  · apply (memLp_map_measure_iff hm.aestronglyMeasurable (measurable_pairProject p).aemeasurable).mpr
    have he : (jointRatio (mesh_pos hmesh) (some p) β i a b ∘ pairFill p) ∘ pairProject p =
        jointRatio (mesh_pos hmesh) (some p) β i a b := by
      funext X
      exact outsideRatio_project (mesh_pos hmesh) p β i hi a b X
    rw [he]
    exact hf.1
  · rw [ht.1, ht.2]
    exact hf.2.2

include hN hβ hβ₀ hsub hδ₀ hδ hη in
/-- Exact source covariance formula under the actual remaining-position
law, including genuine finite moments. -/
theorem deleted_covariance_identity (p : DeletedPairEnsemble.Pair (n + 1)) (b c : MeshIndex J)
    (hηb : OccupationCap δ (Function.update η p.val.1 b)) :
    let ν := pairOutsideLaw (mesh_pos hmesh) η p β
    let A := outsideRatio (mesh_pos hmesh) p β p.val.1 (η p.val.1) b
    let B := outsideRatio (mesh_pos hmesh) p β p.val.2 (η p.val.2) c
    Real.log ((∫ Y, A Y * B Y ∂ν) / ((∫ Y, A Y ∂ν) * (∫ Y, B Y ∂ν))) =
      Real.log (deletedPartition (mesh_pos hmesh) (Function.update (Function.update η p.val.1 b) p.val.2 c) (some p) β).toReal -
      Real.log (deletedPartition (mesh_pos hmesh) (Function.update η p.val.1 b) (some p) β).toReal -
      Real.log (deletedPartition (mesh_pos hmesh) (Function.update η p.val.2 c) (some p) β).toReal +
      Real.log (deletedPartition (mesh_pos hmesh) η (some p) β).toReal := by
  dsimp only
  rw [outsideRatio_product_moment,
    (outsideRatio_moments (mesh_pos hmesh) η p β p.val.1 (Or.inl rfl) (η p.val.1) b).1,
    (outsideRatio_moments (mesh_pos hmesh) η p β p.val.2 (Or.inr rfl) (η p.val.2) c).1,
    deleted_double_ratio_real hN hβ hβ₀ hsub hδ₀ hδ hmesh η hη p b c hηb,
    deleted_single_ratio_real hN hβ hβ₀ hsub hδ₀ hδ hmesh η hη (some p) p.val.1 b,
    deleted_single_ratio_real hN hβ hβ₀ hsub hδ₀ hδ hmesh η hη (some p) p.val.2 c]
  apply log_partition_cross_ratio <;>
    exact deletedPartition_real_pos (mesh_pos hmesh) (mesh_two_le hmesh) hN _ _ hβ (hβ₀.trans_lt hsub)

include hN hβ hβ₀ hsub hδ₀ hδ hη in
theorem deleted_second_difference (p : DeletedPairEnsemble.Pair (n + 1)) (b c : MeshIndex J)
    (hηb : OccupationCap δ (Function.update η p.val.1 b))
    (hsmall : relativeVarianceConstant J β₀ / (n + 1 : ℝ) ≤ 1 / 2) :
    |Real.log (deletedPartition (mesh_pos hmesh) (Function.update (Function.update η p.val.1 b) p.val.2 c) (some p) β).toReal -
      Real.log (deletedPartition (mesh_pos hmesh) (Function.update η p.val.1 b) (some p) β).toReal -
      Real.log (deletedPartition (mesh_pos hmesh) (Function.update η p.val.2 c) (some p) β).toReal +
      Real.log (deletedPartition (mesh_pos hmesh) η (some p) β).toReal| ≤
      2 * (relativeVarianceConstant J β₀ / (n + 1 : ℝ)) := by
  let ν := pairOutsideLaw (mesh_pos hmesh) η p β
  let : IsProbabilityMeasure (DeletedPairConditionals.jointLaw (mesh_pos hmesh) η
      (fun _ => .cell) (some p) β) := DeletedPairConditionals.jointLaw_probability (mesh_pos hmesh)
    (mesh_two_le hmesh) hN η (fun _ => .cell) (some p) hβ (hβ₀.trans_lt hsub)
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pairProject p).aemeasurable).mpr inferInstance
  have hA := outsideRatio_relative_variance hN hβ hβ₀ hsub hδ₀ hδ hmesh η hη p p.val.1
    (Or.inl rfl) (η p.val.1) b
  have hB := outsideRatio_relative_variance hN hβ hβ₀ hsub hδ₀ hδ hmesh η hη p p.val.2
    (Or.inr rfl) (η p.val.2) c
  have hh := relative_covariance_log_bound hA.1 hB.1 hA.2.1 hB.2.1
    (div_nonneg (relativeVarianceConstant_nonneg J β₀) (by positivity)) hsmall hA.2.2 hB.2.2
  rw [deleted_covariance_identity hN hβ hβ₀ hsub hδ₀ hδ hmesh η hη p b c hηb] at hh
  exact hh.2

include hN hβ hβ₀ hsub hδ₀ hδ hη in
/-- Restoring the same selected pair in all four labelings adds four
independently controlled logarithmic errors. -/
theorem partition_second_difference (p : DeletedPairEnsemble.Pair (n + 1)) (b c : MeshIndex J)
    (hηb : OccupationCap δ (Function.update η p.val.1 b))
    (hηc : OccupationCap δ (Function.update η p.val.2 c))
    (hηbc : OccupationCap δ (Function.update (Function.update η p.val.1 b) p.val.2 c))
    (hlarge : secondDifferenceThreshold J β₀ ≤ n + 1) :
    |Real.log (labelPartitionFunction (mesh_pos hmesh) (Function.update (Function.update η p.val.1 b) p.val.2 c) β).toReal -
      Real.log (labelPartitionFunction (mesh_pos hmesh) (Function.update η p.val.1 b) β).toReal -
      Real.log (labelPartitionFunction (mesh_pos hmesh) (Function.update η p.val.2 c) β).toReal +
      Real.log (labelPartitionFunction (mesh_pos hmesh) η β).toReal| ≤
      secondDifferenceConstant J β₀ / (n + 1 : ℝ) := by
  have ht := secondDifferenceThreshold_bounds hlarge
  simp only [Nat.cast_add, Nat.cast_one] at ht
  have hD := abs_le.mp (deleted_second_difference hN hβ hβ₀ hsub hδ₀ hδ hmesh η hη p b c hηb ht.2.2)
  have h₀ := abs_le.mp (restoration_log_error hN hβ hβ₀ hsub hδ hmesh η hη p ht.2.1)
  have h₁ := abs_le.mp (restoration_log_error hN hβ hβ₀ hsub hδ hmesh _ hηb p ht.2.1)
  have h₂ := abs_le.mp (restoration_log_error hN hβ hβ₀ hsub hδ hmesh _ hηc p ht.2.1)
  have h₃ := abs_le.mp (restoration_log_error hN hβ hβ₀ hsub hδ hmesh _ hηbc p ht.2.1)
  calc
    _ ≤ 2 * (relativeVarianceConstant J β₀ / (n + 1 : ℝ)) +
        4 * (restorationConstant J β₀ / (n + 1 : ℝ)) := by
      apply abs_le.mpr
      constructor <;> linarith [hD.1, hD.2, h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2, h₃.1, h₃.2]
    _ = _ := by unfold secondDifferenceConstant; ring

end SourceLogarithms

section SpecifiedLabelProbability

open LabelRatioTransport OccupationProbability

theorem label_partition_log_difference {N J : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (η η₁ η₂ η₃ : LabelVector J N) {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    Real.log (labelProbability hJ η₃ β).toReal - Real.log (labelProbability hJ η₁ β).toReal -
      Real.log (labelProbability hJ η₂ β).toReal + Real.log (labelProbability hJ η β).toReal =
    Real.log (labelPartitionFunction hJ η₃ β).toReal - Real.log (labelPartitionFunction hJ η₁ β).toReal -
      Real.log (labelPartitionFunction hJ η₂ β).toReal + Real.log (labelPartitionFunction hJ η β).toReal := by
  have hp (ζ : LabelVector J N) : 0 < (labelProbability hJ ζ β).toReal :=
    ENNReal.toReal_pos (labelProbability_ne_zero hJ hN ζ hβ hsub)
      (labelProbability_ne_top hJ hN ζ hβ hsub)
  have hZ (ζ : LabelVector J N) : 0 < (labelPartitionFunction hJ ζ β).toReal :=
    ENNReal.toReal_pos (labelPartitionFunction_ne_zero hJ ζ β)
      (labelPartitionFunction_ne_top hJ hN ζ hβ hsub)
  rw [← log_partition_cross_ratio (hp η) (hp η₁) (hp η₂) (hp η₃),
    labelProbability_ratio_eq_partition_ratio hJ hN η η₃ hβ hsub,
    labelProbability_ratio_eq_partition_ratio hJ hN η η₁ hβ hsub,
    labelProbability_ratio_eq_partition_ratio hJ hN η η₂ hβ hsub,
    log_partition_cross_ratio (hZ η) (hZ η₁) (hZ η₂) (hZ η₃)]

theorem label_second_difference {n J : ℕ} {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4) (hδ₀ : 0 < δ)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hlarge : secondDifferenceThreshold J β₀ ≤ n + 1)
    (η : LabelVector J (n + 1)) (p : DeletedPairEnsemble.Pair (n + 1)) (b c : MeshIndex J)
    (hη : OccupationCap δ η) (hηb : OccupationCap δ (Function.update η p.val.1 b))
    (hηc : OccupationCap δ (Function.update η p.val.2 c))
    (hηbc : OccupationCap δ (Function.update (Function.update η p.val.1 b) p.val.2 c)) :
    |Real.log (labelProbability (mesh_pos hmesh) (Function.update (Function.update η p.val.1 b) p.val.2 c) β).toReal -
      Real.log (labelProbability (mesh_pos hmesh) (Function.update η p.val.1 b) β).toReal -
      Real.log (labelProbability (mesh_pos hmesh) (Function.update η p.val.2 c) β).toReal +
      Real.log (labelProbability (mesh_pos hmesh) η β).toReal| ≤
      secondDifferenceConstant J β₀ / (n + 1 : ℝ) := by
  have hN := (secondDifferenceThreshold_bounds hlarge).1
  rw [label_partition_log_difference (mesh_pos hmesh) hN η _ _ _ hβ (hβ₀.trans_lt hsub)]
  exact partition_second_difference hN hβ hβ₀ hsub hδ₀ hδ hmesh η hη p b c hηb hηc hηbc hlarge

/-- Both orientations of two distinct selected labels are covered. No
condition that their source or target cells be different is imposed. -/
theorem two_label_second_difference {N J : ℕ} {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4) (hδ₀ : 0 < δ)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hlarge : secondDifferenceThreshold J β₀ ≤ N)
    (η : LabelVector J N) (i j : Fin N) (hij : i ≠ j) (b c : MeshIndex J)
    (hη : OccupationCap δ η) (hηb : OccupationCap δ (Function.update η i b))
    (hηc : OccupationCap δ (Function.update η j c))
    (hηbc : OccupationCap δ (Function.update (Function.update η i b) j c)) :
    |Real.log (labelProbability (mesh_pos hmesh) (Function.update (Function.update η i b) j c) β).toReal -
      Real.log (labelProbability (mesh_pos hmesh) (Function.update η i b) β).toReal -
      Real.log (labelProbability (mesh_pos hmesh) (Function.update η j c) β).toReal +
      Real.log (labelProbability (mesh_pos hmesh) η β).toReal| ≤
      secondDifferenceConstant J β₀ / (N : ℝ) := by
  classical
  cases N with
  | zero => exact Fin.elim0 i
  | succ n =>
    by_cases hlt : i < j
    · simpa only [Nat.cast_add, Nat.cast_one] using label_second_difference hβ hβ₀ hsub hδ₀ hδ hmesh hlarge
        η ⟨(i, j), hlt⟩ b c hη hηb hηc hηbc
    · have hji : j < i := by omega
      have he : Function.update (Function.update η i b) j c =
          Function.update (Function.update η j c) i b := by
        funext k
        by_cases hi : k = i
        · subst k; simp [hij]
        · by_cases hj : k = j
          · subst k; simp [hij.symm]
          · simp [Function.update_of_ne hi, Function.update_of_ne hj]
      have hh := label_second_difference hβ hβ₀ hsub hδ₀ hδ hmesh hlarge η
        ⟨(j, i), hji⟩ c b hη hηc hηb (he ▸ hηbc)
      dsimp only at hh
      rw [← he] at hh
      simp only [Nat.cast_add, Nat.cast_one]
      convert hh using 1
      congr 1
      ring

/-- Literal realization of the two source moves. In a shared source cell,
the requirement of two actual particles is retained explicitly. -/
theorem exists_two_label_moves {N J : ℕ} (m : MeshIndex J → ℕ) (hm : ∑ a, m a = N)
    (a b c e : MeshIndex J) (ha : 1 ≤ m a) (hc : 1 ≤ m c) (hsame : a = c → 2 ≤ m a) :
    ∃ (η : LabelVector J N) (i j : Fin N), i ≠ j ∧ occupation η = m ∧ η i = a ∧ η j = c ∧
      occupation (Function.update η i b) = moveOccupation m a b ∧
      occupation (Function.update η j e) = moveOccupation m c e ∧
      occupation (Function.update (Function.update η i b) j e) = moveOccupation (moveOccupation m a b) c e := by
  classical
  let η := labelOfProfile m hm
  have hη : occupation η = m := occupation_labelOfProfile m hm
  have hp : ∃ i j : Fin N, i ≠ j ∧ η i = a ∧ η j = c := by
    by_cases hac : a = c
    · have hcard : 1 < (Finset.univ.filter fun i => η i = a).card := by
        change 1 < occupation η a
        rw [hη]
        exact lt_of_lt_of_le (by norm_num : 1 < 2) (hsame hac)
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard
      exact ⟨i, j, hij, (Finset.mem_filter.mp hi).2, hac ▸ (Finset.mem_filter.mp hj).2⟩
    · have ha' : 1 ≤ (Finset.univ.filter fun i => η i = a).card := by simpa only [← hη, occupation] using ha
      have hc' : 1 ≤ (Finset.univ.filter fun i => η i = c).card := by simpa only [← hη, occupation] using hc
      obtain ⟨i, hi⟩ := Finset.one_le_card.mp ha'
      obtain ⟨j, hj⟩ := Finset.one_le_card.mp hc'
      have hia := (Finset.mem_filter.mp hi).2
      have hjc := (Finset.mem_filter.mp hj).2
      exact ⟨i, j, fun hij => hac (hia.symm.trans ((congrArg η hij).trans hjc)), hia, hjc⟩
  obtain ⟨i, j, hij, hia, hjc⟩ := hp
  have h₁ := (occupation_update η i a b hia).trans (congrArg (fun m => moveOccupation m a b) hη)
  have h₂ := (occupation_update η j c e hjc).trans (congrArg (fun m => moveOccupation m c e) hη)
  refine ⟨η, i, j, hij, hη, hia, hjc, h₁, h₂, ?_⟩
  rw [occupation_update (Function.update η i b) j c e (by simpa only [Function.update_of_ne hij.symm] using hjc), h₁]

/-- Source Proposition occupation-second-differences for the actual
specified-label probability Q. The stronger all-destination-cell estimate
immediately includes adjacent displacements. The common threshold and
constant depend only on the fixed J and beta0, not on N, beta, or the profile. -/
theorem occupation_second_difference {N J : ℕ} {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4) (hδ₀ : 0 < δ)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hlarge : secondDifferenceThreshold J β₀ ≤ N)
    (m : MeshIndex J → ℕ) (a b c e : MeshIndex J)
    (ha : 1 ≤ m a) (hc : 1 ≤ m c) (hsame : a = c → 2 ≤ m a)
    (hm : m ∈ cappedOccupations J N δ)
    (hm₁ : moveOccupation m a b ∈ cappedOccupations J N δ)
    (hm₂ : moveOccupation m c e ∈ cappedOccupations J N δ)
    (hm₃ : moveOccupation (moveOccupation m a b) c e ∈ cappedOccupations J N δ) :
    |Real.log (profileWeight (N := N) (mesh_pos hmesh) (moveOccupation (moveOccupation m a b) c e) β).toReal -
      Real.log (profileWeight (N := N) (mesh_pos hmesh) (moveOccupation m a b) β).toReal -
      Real.log (profileWeight (N := N) (mesh_pos hmesh) (moveOccupation m c e) β).toReal +
      Real.log (profileWeight (N := N) (mesh_pos hmesh) m β).toReal| ≤
      secondDifferenceConstant J β₀ / (N : ℝ) := by
  obtain ⟨η, i, j, hij, hη, _hia, _hjc, h₁, h₂, h₃⟩ := exists_two_label_moves m hm.1 a b c e ha hc hsame
  have hηcap : OccupationCap δ η := fun k => by simpa only [hη] using hm.2 k
  have h₁cap : OccupationCap δ (Function.update η i b) := fun k => by simpa only [h₁] using hm₁.2 k
  have h₂cap : OccupationCap δ (Function.update η j e) := fun k => by simpa only [h₂] using hm₂.2 k
  have h₃cap : OccupationCap δ (Function.update (Function.update η i b) j e) := fun k => by
    simpa only [h₃] using hm₃.2 k
  have hh := two_label_second_difference hβ hβ₀ hsub hδ₀ hδ hmesh hlarge η i j hij b e hηcap h₁cap h₂cap h₃cap
  simpa only [labelProbability_eq_profileWeight, hη, h₁, h₂, h₃] using hh

/-- Conservation of the literal natural-valued occupation total forces
the source of a move to contain a particle. This excludes a saturated
subtraction from silently creating a particle. -/
theorem move_source_pos_of_total {J : ℕ} (m : MeshIndex J → ℕ) (a b : MeshIndex J)
    (htotal : (∑ k, moveOccupation m a b k) = ∑ k, m k) : 1 ≤ m a := by
  classical
  by_contra h
  have hz : m a = 0 := by omega
  have he : moveOccupation m a b = fun k => m k + if b = k then 1 else 0 := by
    funext k
    by_cases hak : a = k
    · subst k
      simp only [moveOccupation, ite_true, hz, Nat.zero_sub, zero_add]
    · simp only [moveOccupation, ite_eq_right hak, Nat.sub_zero]
  rw [he, Finset.sum_add_distrib] at htotal
  have hone : (∑ k : MeshIndex J, if b = k then (1 : ℕ) else 0) = 1 := by simp
  rw [hone] at htotal
  omega

/-- The exact adjacent-cell source statement. All source availability,
including two particles in a shared source cell, is derived from the
four actual profiles and their common total N. -/
theorem occupation_second_differences {N J : ℕ} {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4) (hδ₀ : 0 < δ)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hlarge : secondDifferenceThreshold J β₀ ≤ N)
    (m : MeshIndex J → ℕ) (a b c e : MeshIndex J)
    (hab : EdgeAdjacent J (mesh_pos hmesh) a b) (_hce : EdgeAdjacent J (mesh_pos hmesh) c e)
    (hm : m ∈ cappedOccupations J N δ)
    (hm₁ : moveOccupation m a b ∈ cappedOccupations J N δ)
    (hm₂ : moveOccupation m c e ∈ cappedOccupations J N δ)
    (hm₃ : moveOccupation (moveOccupation m a b) c e ∈ cappedOccupations J N δ) :
    |Real.log (profileWeight (N := N) (mesh_pos hmesh) (moveOccupation (moveOccupation m a b) c e) β).toReal -
      Real.log (profileWeight (N := N) (mesh_pos hmesh) (moveOccupation m a b) β).toReal -
      Real.log (profileWeight (N := N) (mesh_pos hmesh) (moveOccupation m c e) β).toReal +
      Real.log (profileWeight (N := N) (mesh_pos hmesh) m β).toReal| ≤
      secondDifferenceConstant J β₀ / (N : ℝ) := by
  have ha := move_source_pos_of_total m a b (hm₁.1.trans hm.1.symm)
  have hc := move_source_pos_of_total m c e (hm₂.1.trans hm.1.symm)
  have hsame : a = c → 2 ≤ m a := by
    intro hac
    have hp := move_source_pos_of_total (moveOccupation m a b) c e (hm₃.1.trans hm₁.1.symm)
    rw [← hac] at hp
    have hba := (hab.ne (mesh_two_le hmesh)).symm
    simp only [moveOccupation, ite_true, ite_eq_right hba, add_zero] at hp
    omega
  exact occupation_second_difference hβ hβ₀ hsub hδ₀ hδ hmesh hlarge m a b c e ha hc hsame hm hm₁ hm₂ hm₃

end SpecifiedLabelProbability

end PeriodicAttractiveLogGas.OccupationSecondDifferences
