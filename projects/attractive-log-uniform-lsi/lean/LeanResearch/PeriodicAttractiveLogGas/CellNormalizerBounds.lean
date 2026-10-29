import LeanResearch.PeriodicAttractiveLogGas.SharpPoleMoments
import LeanResearch.PeriodicAttractiveLogGas.ConditionalLawEstimates

/-! The actual cell normalizer estimates in source Lemma 3.9. The
reference integral uses the sharp layer-cake disk moment; compatible lifts
retain the exact physical cell scaling. No label ratio is assumed. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.CellNormalizerBounds
open MeshCells MeshAdjacentCells GreenPointWeights GreenPointRescaling GreenFarOscillation
  ConditionalParameters SingularRectangleMoments PointWeightDensity

variable {ι : Type*} [Fintype ι]

def upperConstant (β₀ C₀ : ℝ) (J R : ℕ) : ℝ :=
  2 * Real.exp ((β₀ + 1) * C₀) * (R : ℝ) ^ (-β₀) * (J : ℝ) ^ (β₀ + 1 / 16)

def kappaConstant (β₀ Cg C₀ : ℝ) (J R : ℕ) : ℝ :=
  (R : ℝ) ^ β₀ * Real.exp (-β₀ * Cg - (β₀ + 1) * C₀) /
    (2 * (J : ℝ) ^ (β₀ + 1 / 16))

theorem upperConstant_pos (β₀ C₀ : ℝ) {J R : ℕ} (hJ : 0 < J) (hR : 0 < R) :
    0 < upperConstant β₀ C₀ J R := by
  unfold upperConstant
  positivity

theorem upperConstant_eq_exp (β₀ C₀ : ℝ) {J R : ℕ} (hJ : 0 < J) (hR : 0 < R) :
    upperConstant β₀ C₀ J R =
      2 * Real.exp (β₀ * Real.log ((J : ℝ) / R) + (1 / 16 : ℝ) * Real.log J + (β₀ + 1) * C₀) := by
  have hj : (0 : ℝ) < J := by exact_mod_cast hJ
  have hr : (0 : ℝ) < R := by exact_mod_cast hR
  simp only [upperConstant, Real.rpow_def_of_pos hj, Real.rpow_def_of_pos hr,
    mul_assoc, ← Real.exp_add]
  congr 2
  rw [Real.log_div hj.ne' hr.ne']
  ring

theorem lower_div_upper_eq_kappa (β₀ Cg C₀ : ℝ) {J R : ℕ}
    (hJ : 0 < J) (hR : 0 < R) :
    Real.exp (-β₀ * Cg) / upperConstant β₀ C₀ J R = kappaConstant β₀ Cg C₀ J R := by
  have hj : (0 : ℝ) < J := by exact_mod_cast hJ
  have hr : (0 : ℝ) < R := by exact_mod_cast hR
  rw [upperConstant, kappaConstant, Real.rpow_neg hr.le, Real.exp_sub]
  field_simp

theorem kappaConstant_pos (β₀ Cg C₀ : ℝ) {J R : ℕ} (hJ : 0 < J) (hR : 0 < R) :
    0 < kappaConstant β₀ Cg C₀ J R := by
  rw [← lower_div_upper_eq_kappa β₀ Cg C₀ hJ hR]
  exact div_pos (Real.exp_pos _) (upperConstant_pos β₀ C₀ hJ hR)

theorem kappaConstant_le_one {β₀ Cg C₀ : ℝ} (hβ₀ : 0 ≤ β₀)
    (hCg : 0 ≤ Cg) (hC₀ : 0 ≤ C₀) {J R : ℕ} (hR : 1 ≤ R) (hRJ : R ≤ J) :
    kappaConstant β₀ Cg C₀ J R ≤ 1 := by
  have hJ : 0 < J := lt_of_lt_of_le (by omega : 0 < R) hRJ
  have hj : (1 : ℝ) ≤ J := by exact_mod_cast (hR.trans hRJ)
  have hr : (0 : ℝ) < R := by exact_mod_cast hR
  have hrj : (R : ℝ) ≤ J := by exact_mod_cast hRJ
  have he : 0 ≤ β₀ * Real.log ((J : ℝ) / R) + (1 / 16 : ℝ) * Real.log J + (β₀ + 1) * C₀ := by
    have hl : 0 ≤ Real.log ((J : ℝ) / R) :=
      Real.log_nonneg ((le_div_iff₀ hr).mpr (by simpa using hrj))
    exact add_nonneg (add_nonneg (mul_nonneg hβ₀ hl)
      (mul_nonneg (by norm_num) (Real.log_nonneg hj)))
      (mul_nonneg (by linarith) hC₀)
  have hu : 1 ≤ upperConstant β₀ C₀ J R := by
    rw [upperConstant_eq_exp β₀ C₀ hJ (by omega)]
    linarith [Real.one_le_exp_iff.mpr he]
  have hl : Real.exp (-β₀ * Cg) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  rw [← lower_div_upper_eq_kappa β₀ Cg C₀ hJ (by omega)]
  exact (div_le_one (upperConstant_pos β₀ C₀ hJ (by omega))).mpr (hl.trans hu)

theorem torusWeight_lower (y : ι → Torus) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {β₀ Cg : ℝ} (hCg : 0 ≤ Cg)
    (hg : ∀ z : Torus, -Cg ≤ regularGreenRepresentative z)
    (ht : ∑ i, w i ≤ β₀) (z : Torus) :
    Real.exp (-β₀ * Cg) ≤ torusWeight y w z := by
  apply Real.exp_le_exp.mpr
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
    mul_le_mul_of_nonneg_left (hg (z - y i)) (hw i)
  have ht' := mul_le_mul_of_nonneg_right ht hCg
  rw [← Finset.sum_mul, mul_neg] at h
  linarith

theorem far_green_upper {J R C₀ : ℝ} (hJ : 0 < J) (hR : 0 < R)
    (hk : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    {z : Torus} (hsep : R / J ≤ torusEuclideanNorm z) :
    regularGreenRepresentative z ≤ Real.log (J / R) + C₀ := by
  have hz : z ≠ 0 := by
    intro he
    rw [he, torusEuclideanNorm_zero] at hsep
    exact (not_le_of_gt (div_pos hR hJ)) hsep
  have hb := (abs_le.mp (hk z hz)).2
  have hl := Real.log_le_log (div_pos hR hJ) hsep
  rw [Real.log_div hR.ne' hJ.ne'] at hl
  rw [Real.log_div hJ.ne' hR.ne']
  linarith

theorem greenWeight_le_sharp_majorant {J D C₀ B : ℝ}
    (hJ : 1 ≤ J) (hD : D < J / 2) (hC₀ : 0 ≤ C₀)
    (hk : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (a : PlanarSpace) (Y : ι → PlanarSpace) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hκ : ∑ i, w i ≤ 1 / 16)
    (F : PlanarSpace → ℝ) {Z : PlanarSpace} (hF : F Z ≤ B)
    (hne : ∀ i, Z ≠ Y i) (hd : ∀ i, ‖Z - Y i‖ ≤ D) :
    greenWeight a J Y w F Z ≤
      Real.exp (B + (1 / 16 : ℝ) * Real.log J + C₀) * poleProduct Y w Z := by
  have hj : 0 < J := zero_lt_one.trans_le hJ
  have hn := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
    mul_le_mul_of_nonneg_left
      (abs_le.mp (abs_logRemainder_le hj hD hk (hne i) (hd i))).2 (hw i)
  have hκ' : (∑ i, w i) * C₀ ≤ C₀ := by
    have h := mul_le_mul_of_nonneg_right hκ hC₀
    nlinarith
  have hlog := mul_le_mul_of_nonneg_right hκ (Real.log_nonneg hJ)
  have hsum : (∑ i, w i) * Real.log J + F Z +
      (∑ i, w i * logRemainder J (Y i) Z) ≤ B + (1 / 16 : ℝ) * Real.log J + C₀ := by
    rw [← Finset.sum_mul] at hn
    linarith
  have he : greenWeight a J Y w F Z =
      Real.exp ((∑ i, w i) * Real.log J + F Z +
        ∑ i, w i * logRemainder J (Y i) Z) * poleProduct Y w Z := by
    rw [greenWeight_factor a J Y w F 0 Z hne, perturbedWeight,
      ← mul_assoc, ← Real.exp_add]
    congr 2
    simp only [perturbation]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hsum) (poleProduct_nonneg Y w Z)

/-- Normalized cell measure. Both the singular reference moment and every
far-source bound are discharged from the actual placement and cap data. -/
theorem cell_weight_upper {J R : ℕ} (hJ : 0 < J) (hR : 1 ≤ R)
    (hmesh : 8 * (R + 4) ≤ J) (a : MeshIndex J)
    (y : ι → Torus) (labels : ι → MeshIndex J)
    (hy : ∀ i, y i ∈ closure (meshCell J hJ (labels i)))
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {β₀ C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hk : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (htotal : ∑ i, w i ≤ β₀)
    (hnear : ∑ i : {i // labels i ∈ nearby J hJ R a .cell}, w i ≤ 1 / 16) :
    Integrable (torusWeight y w) (meshCellMeasure J hJ a) ∧
      (∫ z, torusWeight y w z ∂meshCellMeasure J hJ a) ≤ upperConstant β₀ C₀ J R := by
  classical
  let P : ι → Prop := fun i ↦ labels i ∈ nearby J hJ R a .cell
  let Near := {i // P i}
  let Far := {i // ¬P i}
  have hlift (i : Near) : ∃ Y : PlanarSpace, meshChart J a Y = y i ∧
      ∀ Z ∈ patchClosed .cell, ‖Z - Y‖ ≤ distanceBound R :=
    nearby_lift hJ a (labels i) .cell i.property (hy i)
  choose Y hY hd using hlift
  let A := meshTranslation J a
  let F := referencePotential A J (fun i : Far ↦ y i) (fun i : Far ↦ w i)
  let B := β₀ * (Real.log ((J : ℝ) / R) + C₀)
  let E := B + (1 / 16 : ℝ) * Real.log J + C₀
  have hj : (0 : ℝ) < J := by exact_mod_cast hJ
  have hj1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hr : (0 : ℝ) < R := by exact_mod_cast hR
  have hrj : (R : ℝ) ≤ J := by exact_mod_cast (show R ≤ J by omega)
  have hB0 : 0 ≤ Real.log ((J : ℝ) / R) + C₀ :=
    add_nonneg (Real.log_nonneg ((le_div_iff₀ hr).mpr (by simpa using hrj))) hC₀
  have hwfar : ∑ i : Far, w i ≤ β₀ := by
    have he := Fintype.sum_subtype_add_sum_subtype P w
    have hn : 0 ≤ ∑ i : Near, w i := Finset.sum_nonneg fun i _ ↦ hw i
    change (∑ i : Near, w i) + (∑ i : Far, w i) = ∑ i, w i at he
    linarith
  have hF : ∀ Z ∈ patchClosed .cell, F Z ≤ B := by
    intro Z hZ
    have hs : ∀ i : Far, regularGreenRepresentative (meshChart J a Z - y i) ≤
        Real.log ((J : ℝ) / R) + C₀ := fun i ↦
      far_green_upper hj hr hk (far_gap hJ a (labels i) .cell i.property hZ (hy i))
    have hh := Finset.sum_le_sum (s := Finset.univ) fun (i : Far) _ ↦
      mul_le_mul_of_nonneg_left (hs i) (hw i)
    have ht := mul_le_mul_of_nonneg_right hwfar hB0
    rw [← Finset.sum_mul] at hh
    have hch : torusQuotient (RectangleDilation.affine A J Z) = meshChart J a Z :=
      (congrFun (meshChart_eq_chart J a) Z).symm
    dsimp [F, referencePotential, referenceSource, B]
    rw [hch]
    exact hh.trans ht
  have he : greenWeight A J Y (fun i : Near ↦ w i) F =
      (fun Z ↦ torusWeight y w (meshChart J a Z)) := by
    funext Z
    have hYi (i : Near) : chart A J (Y i) = y i := by
      simpa only [meshChart_eq_chart, A] using hY i
    have hch : torusQuotient (RectangleDilation.affine A J Z) = meshChart J a Z :=
      (congrFun (meshChart_eq_chart J a) Z).symm
    simp only [greenWeight, hYi]
    simp only [torusWeight, F, referencePotential, referenceSource, chart, hch]
    congr 1
    rw [add_comm]
    exact Fintype.sum_subtype_add_sum_subtype P
      (fun i ↦ w i * regularGreenRepresentative (meshChart J a Z - y i))
  let μ := patchReference .cell
  have hb : ∀ᵐ Z ∂μ, torusWeight y w (meshChart J a Z) ≤
      Real.exp E * poleProduct Y (fun i : Near ↦ w i) Z := by
    filter_upwards [ae_mem_patchClosed .cell,
      ae_avoid_poles (patchReference_le_volume .cell).absolutelyContinuous Y] with Z hZ hne
    rw [← congrFun he Z]
    exact greenWeight_le_sharp_majorant hj1 (distanceBound_lt_half hR hmesh) hC₀ hk
      A Y (fun i : Near ↦ w i) (fun i ↦ hw i) hnear F (hF Z hZ) hne (fun i ↦ hd i Z hZ)
  have hp := SharpPoleMoments.small_poleProduct_moment (patchReference_le_volume .cell)
    Y (fun i : Near ↦ w i) (fun i ↦ hw i) hnear
  have hi : Integrable (fun Z ↦ torusWeight y w (meshChart J a Z)) μ := by
    apply (hp.1.const_mul (Real.exp E)).mono'
      ((measurable_torusWeight y w).comp (continuous_meshChart J a).measurable).aestronglyMeasurable
    filter_upwards [hb] with Z hZ
    simpa only [Function.comp_def, Real.norm_of_nonneg (torusWeight_pos y w _).le] using hZ
  have hmp := measurePreserving_meshChart J hJ a
  have hm : AEStronglyMeasurable (torusWeight y w) (meshCellMeasure J hJ a) :=
    (measurable_torusWeight y w).aestronglyMeasurable
  have ht : Integrable (torusWeight y w) (meshCellMeasure J hJ a) :=
    (hmp.integrable_comp hm).mp hi
  refine ⟨ht, ?_⟩
  have hint : (∫ Z, torusWeight y w (meshChart J a Z) ∂μ) =
      ∫ z, torusWeight y w z ∂meshCellMeasure J hJ a := by
    rw [← hmp.map_eq]
    exact (integral_map hmp.aemeasurable
      (measurable_torusWeight y w).aestronglyMeasurable).symm
  have hc : 2 * Real.exp E = upperConstant β₀ C₀ J R := by
    simp only [upperConstant, Real.rpow_def_of_pos hj, Real.rpow_def_of_pos hr,
      mul_assoc, ← Real.exp_add]
    congr 2
    dsimp [E, B]
    rw [Real.log_div hj.ne' hr.ne']
    ring
  rw [← hint, ← hc]
  calc
    _ ≤ ∫ Z, Real.exp E * poleProduct Y (fun i : Near ↦ w i) Z ∂μ :=
      integral_mono_ae hi (hp.1.const_mul _) hb
    _ = Real.exp E * ∫ Z, poleProduct Y (fun i : Near ↦ w i) Z ∂μ := integral_const_mul _ _
    _ ≤ Real.exp E * 2 := mul_le_mul_of_nonneg_left hp.2 (Real.exp_pos _).le
    _ = _ := mul_comm _ _

theorem cell_weight_lower {J : ℕ} (hJ : 0 < J) (a : MeshIndex J)
    (y : ι → Torus) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {β₀ Cg : ℝ} (hCg : 0 ≤ Cg) (hg : ∀ z : Torus, -Cg ≤ regularGreenRepresentative z)
    (ht : ∑ i, w i ≤ β₀) (hi : Integrable (torusWeight y w) (meshCellMeasure J hJ a)) :
    Real.exp (-β₀ * Cg) ≤ ∫ z, torusWeight y w z ∂meshCellMeasure J hJ a := by
  let : IsProbabilityMeasure (meshCellMeasure J hJ a) := isProbabilityMeasure_meshCellMeasure J hJ a
  have h := integral_mono (integrable_const (Real.exp (-β₀ * Cg))) hi
    (torusWeight_lower y w hw hCg hg ht)
  simpa using h

open LabelOccupations CappedPointWeights OneCoordinateConditionals ConditionalLawEstimates

/-- The exact uniform constants for every fixed prescribed outside
placement, including coincident points. Cg is any actual nonnegative global
lower-bound constant; it is not a hypothesis about the desired normalizer. -/
theorem capped_source_normalizer_bounds {n J : ℕ} (hJ : 0 < J)
    {β β₀ δ Cg : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hδ : δ ≤ occupationBound β₀) (hCg : 0 ≤ Cg)
    (hg : ∀ z : Torus, -Cg ≤ regularGreenRepresentative z)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside hJ η i Y)
    (a : MeshIndex J) :
    Integrable (OneCoordinateConditionals.sourceWeight β Y) (meshCellMeasure J hJ a) ∧
      Real.exp (-β₀ * Cg) ≤
        (∫ z, OneCoordinateConditionals.sourceWeight β Y z ∂meshCellMeasure J hJ a) ∧
      (∫ z, OneCoordinateConditionals.sourceWeight β Y z ∂meshCellMeasure J hJ a) ≤
        upperConstant β₀ kernelConstant J (radius β₀) := by
  classical
  let I := otherParticles i
  let X := insertSite i 0 Y
  let w : Fin (n + 1) → ℝ := fun _ ↦ β / (n + 1 : ℕ)
  have hw : ∀ k, 0 ≤ w k := fun _ ↦ div_nonneg hβ (Nat.cast_nonneg _)
  have ht : ∑ k : I, w k ≤ β₀ := by
    rw [Finset.sum_coe_sort]
    exact total_source_weight_le (Nat.succ_pos n) hβ hβ₀ I (fun _ _ ↦ le_rfl)
  have hn : ∑ k : {k : I // η k ∈ nearby J hJ (radius β₀) a .cell}, w k.1 ≤ 1 / 16 := by
    rw [sum_near_eq_sourceWeight]
    exact sourceWeight_fixedDelta_le (Nat.succ_pos n) hβ hβ₀ kernelConstant_pos.le
      (hη.mono hδ) I _ (card_nearby_le J hJ (radius β₀) a .cell) (fun _ _ ↦ le_rfl)
  have hu := cell_weight_upper hJ (radius_one_le β₀) hmesh a
    (fun k : I ↦ X k) (fun k : I ↦ η k)
    (fun k ↦ prescribedOutside_insertSite hJ η i Y hY k k.2)
    (fun k : I ↦ w k) (fun k ↦ hw k) kernelConstant_pos.le kernel_log_bound ht hn
  have hl := cell_weight_lower hJ a (fun k : I ↦ X k) (fun k : I ↦ w k)
    (fun k ↦ hw k) hCg hg ht hu.1
  change Integrable (torusWeight (fun k : I ↦ X k) (fun k : I ↦ w k)) _ ∧ _ at hu
  have he := sourceWeight_eq_subfamily i β Y
  change OneCoordinateConditionals.sourceWeight β Y =
    torusWeight (fun k : I ↦ X k) (fun k : I ↦ w k) at he
  rw [← he] at hu hl
  exact ⟨hu.1, hl, hu.2⟩

theorem integral_cell_eq_normalized_div {J : ℕ} (hJ : 0 < J)
    (a : MeshIndex J) (f : Torus → ℝ) :
    (∫ z in meshCell J hJ a, f z ∂torusMeasure) =
      (∫ z, f z ∂meshCellMeasure J hJ a) / (J : ℝ) ^ 2 := by
  have hj : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  rw [meshCellMeasure, integral_smul_measure]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_natCast, smul_eq_mul]
  field_simp

/-- The displayed raw-Haar cell-integral bounds from the supplied proof,
with the source's original Green representative and its exact J exponents. -/
theorem capped_raw_cell_normalizer_bounds {n J : ℕ} (hJ : 0 < J)
    {β β₀ δ Cg : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hδ : δ ≤ occupationBound β₀) (hCg : 0 ≤ Cg)
    (hg : ∀ z : Torus, -Cg ≤ regularGreenRepresentative z)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside hJ η i Y)
    (a : MeshIndex J) :
    Integrable (rawSourceWeight β Y) (torusMeasure.restrict (meshCell J hJ a)) ∧
      Real.exp (-β₀ * Cg) / (J : ℝ) ^ 2 ≤
        (∫ z in meshCell J hJ a, rawSourceWeight β Y z ∂torusMeasure) ∧
      (∫ z in meshCell J hJ a, rawSourceWeight β Y z ∂torusMeasure) ≤
        2 * Real.exp ((β₀ + 1) * kernelConstant) * (radius β₀ : ℝ) ^ (-β₀) *
          (J : ℝ) ^ (β₀ + 1 / 16 - 2) := by
  have h := capped_source_normalizer_bounds hJ hβ hβ₀ hδ hCg hg hmesh η hη i Y hY a
  have hi := h.1
  rw [meshCellMeasure, integrable_smul_measure (by positivity) (by finiteness)] at hi
  have hae : OneCoordinateConditionals.sourceWeight β Y =ᵐ[torusMeasure.restrict (meshCell J hJ a)]
      rawSourceWeight β Y := ae_restrict_of_ae (sourceWeight_ae_rawSourceWeight β Y)
  have he := integral_congr_ae (μ := torusMeasure.restrict (meshCell J hJ a)) hae
  refine ⟨hi.congr hae, ?_, ?_⟩
  · rw [← he, integral_cell_eq_normalized_div]
    exact div_le_div_of_nonneg_right h.2.1 (sq_nonneg _)
  · rw [← he, integral_cell_eq_normalized_div]
    have hu := div_le_div_of_nonneg_right h.2.2 (sq_nonneg (J : ℝ))
    have hj : (0 : ℝ) < J := by exact_mod_cast hJ
    rw [upperConstant] at hu
    rw [Real.rpow_sub hj, Real.rpow_two]
    convert hu using 1
    ring

end PeriodicAttractiveLogGas.CellNormalizerBounds
