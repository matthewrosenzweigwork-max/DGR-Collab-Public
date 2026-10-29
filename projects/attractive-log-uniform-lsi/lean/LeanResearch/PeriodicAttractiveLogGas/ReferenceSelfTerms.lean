import LeanResearch.PeriodicAttractiveLogGas.ResidualExponential
import LeanResearch.PeriodicAttractiveLogGas.MovingPoleCalculus

/-! The own-cell logarithmic estimate and self terms in the supplied proof of
Lemma `reference-density`, source lines 2411--2442. No change-of-reference
identity or fixed-point existence is asserted in this unit. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.ReferenceSelfTerms

open MeshCells MeshNearbyGeometry NearCellLifts ReferenceResidual LabelOccupations
  PositiveLogPoleMoments ConditionalLawEstimates MovingPoleCalculus

def selfBound (J : ℕ) : ℝ :=
  Real.exp 1 * (Real.log (J : ℝ) + kernelConstant + Real.pi / 2) + greenLowerConstant

def selfTerm {J N : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J N) (X : Fin N → Torus) : ℝ :=
  (∑ i, ReferenceResidual.potential (μ (η i)) (X i)) / (N : ℝ)

theorem log_mesh_add_kernel_nonneg {J : ℕ} (hJ : 0 < J) :
    0 ≤ Real.log (J : ℝ) + kernelConstant := by
  have h1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  exact add_nonneg (Real.log_nonneg h1) kernelConstant_pos.le

/-- The compatible own-cell lift uses the sharp upper logarithm, without
adding log(sqrt 2). Its one planar pole is removed only on a null set. -/
theorem own_cell_chart_upper {J : ℕ} (hJ : 0 < J) (hmesh : 8 ≤ J)
    (a : MeshIndex J) {x : Torus} (hx : x ∈ closure (meshCell J hJ a)) :
    ∃ Y : PlanarSpace, ∀ᵐ Z ∂squareLebesgue,
      greenKernel x (meshChart J a Z) ≤
        Real.log (J : ℝ) + kernelConstant + positiveLogPole Y Z := by
  have hmesh' : 8 * (0 + 1) ≤ J := by simpa using hmesh
  have haa : periodicIndexDistance a a ≤ 0 := by
    simp [periodicIndexDistance, centeredIndexOffset]
  obtain ⟨Y, hY, hd⟩ := exists_reference_lift hJ hmesh' a a haa hx
  refine ⟨Y, ?_⟩
  have hne : ∀ᵐ Z ∂squareLebesgue, Z ≠ Y :=
    SingularRectangleMoments.squareLebesgue_le_volume.absolutelyContinuous.ae_le
      ((volume : Measure PlanarSpace).ae_ne Y)
  filter_upwards [PoleLogMoments.ae_mem_closed_square, hne] with Z hZ hZY
  have hh := GreenPointRescaling.abs_logRemainder_le
    (show (0 : ℝ) < J by exact_mod_cast hJ)
    (cellReferenceRadius_lt_half hmesh') kernel_log_bound hZY (hd Z hZ).2.1
  have hu := (abs_le.mp hh).2
  have hp : -Real.log ‖Z - Y‖ ≤ positiveLogPole Y Z := le_max_right _ _
  rw [greenKernel_symm, ← hY]
  unfold greenKernel
  rw [meshChart_sub]
  unfold GreenPointRescaling.logRemainder at hu
  linarith

/-- The exact positive-part integral on the actual normalized own-cell law. -/
theorem own_cell_positive_part {J : ℕ} (hJ : 0 < J) (hmesh : 8 ≤ J)
    (a : MeshIndex J) {x : Torus} (hx : x ∈ closure (meshCell J hJ a)) :
    Integrable (fun y => max 0 (greenKernel x y)) (meshCellMeasure J hJ a) ∧
    (∫ y, max 0 (greenKernel x y) ∂meshCellMeasure J hJ a) ≤
      Real.log (J : ℝ) + kernelConstant + Real.pi / 2 := by
  obtain ⟨Y, hY⟩ := own_cell_chart_upper hJ hmesh a hx
  have hl := positiveLogPole_moment_le_of_measure_le
    SingularRectangleMoments.squareLebesgue_le_volume Y (p := 1) (by omega)
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at hl
  have hm : Measurable (fun y => max 0 (greenKernel x y)) :=
    measurable_const.max (regularGreenRepresentative_measurable.comp (measurable_const.sub measurable_id))
  have hdom : ∀ᵐ Z ∂squareLebesgue, max 0 (greenKernel x (meshChart J a Z)) ≤
      Real.log (J : ℝ) + kernelConstant + positiveLogPole Y Z := by
    filter_upwards [hY] with Z hZ
    exact max_le (add_nonneg (log_mesh_add_kernel_nonneg hJ) (positiveLogPole_nonneg Y Z)) hZ
  have hiB : Integrable (fun Z => Real.log (J : ℝ) + kernelConstant + positiveLogPole Y Z)
      squareLebesgue := (integrable_const _).add hl.1
  have hi : Integrable (fun Z => max 0 (greenKernel x (meshChart J a Z))) squareLebesgue :=
    hiB.mono' (hm.comp (measurable_meshChart J a)).aestronglyMeasurable
      (hdom.mono fun Z hZ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ max 0 (greenKernel x (meshChart J a Z)) from le_max_left _ _)]
        exact hZ)
  have hic : Integrable (fun y => max 0 (greenKernel x y)) (meshCellMeasure J hJ a) :=
    ((measurePreserving_meshChart J hJ a).integrable_comp hm.aestronglyMeasurable).mp hi
  refine ⟨hic, ?_⟩
  rw [← integral_meshChart hJ a hic]
  calc
    _ ≤ ∫ Z, Real.log (J : ℝ) + kernelConstant + positiveLogPole Y Z ∂squareLebesgue :=
      integral_mono_ae hi hiB hdom
    _ = Real.log (J : ℝ) + kernelConstant + ∫ Z, positiveLogPole Y Z ∂squareLebesgue := by
      rw [integral_add (integrable_const _) hl.1]
      simp
    _ ≤ _ := by linarith [hl.2.1]

/-- Every pole in the closed own cell has a genuinely integrable Green kernel,
and the potential has the exact source upper and global lower bounds. -/
theorem own_cell_potential_bounds {J : ℕ} (hJ : 0 < J) (hmesh : 8 ≤ J)
    (a : MeshIndex J) (μ : Measure Torus) [IsProbabilityMeasure μ]
    (hμ : μ ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    {x : Torus} (hx : x ∈ closure (meshCell J hJ a)) :
    Integrable (greenKernel x) μ ∧
    -greenLowerConstant ≤ potential μ x ∧
    potential μ x ≤ Real.exp 1 * (Real.log (J : ℝ) + kernelConstant + Real.pi / 2) := by
  have hp := own_cell_positive_part hJ hmesh a hx
  have hps := hp.1.smul_measure (c := ENNReal.ofReal (Real.exp 1)) ENNReal.ofReal_ne_top
  have hpi := hps.mono_measure hμ
  have hm : Measurable (greenKernel x) :=
    regularGreenRepresentative_measurable.comp (measurable_const.sub measurable_id)
  have hgi : Integrable (greenKernel x) μ := (hpi.add (integrable_const greenLowerConstant)).mono'
    hm.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]
      change |greenKernel x y| ≤ max 0 (greenKernel x y) + greenLowerConstant
      have hlo := green_lower_bound (x - y)
      have hg := greenLowerConstant_pos.le
      have hp0 : 0 ≤ max 0 (greenKernel x y) := le_max_left _ _
      have hpg : greenKernel x y ≤ max 0 (greenKernel x y) := le_max_right _ _
      change -greenLowerConstant ≤ greenKernel x y at hlo
      rw [abs_le]
      constructor <;> linarith)
  refine ⟨hgi, ?_, ?_⟩
  · have hh := integral_mono (integrable_const (-greenLowerConstant)) hgi
      (fun y => green_lower_bound (x - y))
    simpa only [potential, integral_const, probReal_univ, one_smul] using hh
  · calc
      potential μ x ≤ ∫ y, max 0 (greenKernel x y) ∂μ :=
        integral_mono hgi hpi (fun y => le_max_right _ _)
      _ ≤ ∫ y, max 0 (greenKernel x y) ∂(ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a) :=
        integral_mono_measure hμ (Eventually.of_forall fun y => le_max_left _ _) hps
      _ = Real.exp 1 * ∫ y, max 0 (greenKernel x y) ∂meshCellMeasure J hJ a := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos 1).le, smul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hp.2 (Real.exp_pos 1).le

theorem selfBound_nonneg {J : ℕ} (hJ : 0 < J) : 0 ≤ selfBound J := by
  unfold selfBound
  have hb := log_mesh_add_kernel_nonneg hJ
  have hc := greenLowerConstant_pos.le
  positivity

theorem own_cell_potential_abs {J : ℕ} (hJ : 0 < J) (hmesh : 8 ≤ J)
    (a : MeshIndex J) (μ : Measure Torus) [IsProbabilityMeasure μ]
    (hμ : μ ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    {x : Torus} (hx : x ∈ closure (meshCell J hJ a)) :
    |potential μ x| ≤ selfBound J := by
  have hh := (own_cell_potential_bounds hJ hmesh a μ hμ hx).2
  have hb : 0 ≤ Real.exp 1 * (Real.log (J : ℝ) + kernelConstant + Real.pi / 2) :=
    mul_nonneg (Real.exp_pos _).le (add_nonneg (log_mesh_add_kernel_nonneg hJ) (by positivity))
  have hc := greenLowerConstant_pos.le
  rw [abs_le]
  unfold selfBound
  constructor <;> linarith

theorem measurable_potential (μ : Measure Torus) [IsProbabilityMeasure μ] :
    Measurable (potential μ) :=
  measurable_greenKernel.stronglyMeasurable.integral_prod_right.measurable

/-- Averaging the own-cell bound proves the source diagonal pair-constant
estimate, with integrability established before the integral is used. -/
theorem own_cell_pairAverage_abs {J : ℕ} (hJ : 0 < J) (hmesh : 8 ≤ J)
    (a : MeshIndex J) (μ : Measure Torus) [IsProbabilityMeasure μ]
    (hμ : μ ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a) :
    Integrable (potential μ) μ ∧ |pairAverage μ μ| ≤ selfBound J := by
  have hb : ∀ᵐ x ∂μ, |potential μ x| ≤ selfBound J :=
    (ae_mem_closed_cell_of_domination hJ a μ hμ).mono fun x hx =>
      own_cell_potential_abs hJ hmesh a μ hμ hx
  have hi : Integrable (potential μ) μ := (integrable_const (selfBound J)).mono'
    (measurable_potential μ).aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hb)
  refine ⟨hi, ?_⟩
  calc
    |pairAverage μ μ| ≤ ∫ x, |potential μ x| ∂μ := by
      simpa only [pairAverage, Real.norm_eq_abs] using norm_integral_le_integral_norm (potential μ)
    _ ≤ ∫ _, selfBound J ∂μ := integral_mono_ae hi.abs (integrable_const _) hb
    _ = _ := by simp

theorem selfTerm_abs {J N : ℕ} (hJ : 0 < J) (hmesh : 8 ≤ J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J N) (X : Fin N → Torus)
    (hX : ∀ i, X i ∈ closure (meshCell J hJ (η i))) :
    |selfTerm μ η X| ≤ selfBound J := by
  by_cases hN : N = 0
  · subst N
    simpa [selfTerm] using selfBound_nonneg hJ
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [selfTerm, abs_div, abs_of_pos hNr, div_le_iff₀ hNr]
  calc
    |∑ i, potential (μ (η i)) (X i)| ≤ ∑ i, |potential (μ (η i)) (X i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin N, selfBound J := Finset.sum_le_sum fun i _ =>
      own_cell_potential_abs hJ hmesh (η i) (μ (η i)) (hμ (η i)) (hX i)
    _ = _ := by simp [mul_comm]

theorem selfTerm_ae_abs {J N : ℕ} (hJ : 0 < J) (hmesh : 8 ≤ J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J N) :
    ∀ᵐ X ∂Measure.pi (fun i => μ (η i)), |selfTerm μ η X| ≤ selfBound J := by
  have hi (i : Fin N) : ∀ᵐ X ∂Measure.pi (fun i => μ (η i)),
      X i ∈ closure (meshCell J hJ (η i)) :=
    (measurePreserving_eval (fun j => μ (η j)) i).quasiMeasurePreserving.ae
      (ae_mem_closed_cell_of_domination hJ (η i) (μ (η i)) (hμ (η i)))
  filter_upwards [ae_all_iff.mpr hi] with X hX
  exact selfTerm_abs hJ hmesh μ hμ η X hX

theorem self_terms_density_bound {J N : ℕ} (hJ : 0 < J) (hmesh : 8 ≤ J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (w : MeshIndex J → Torus → ℝ≥0∞)
    (hμw : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (w a))
    (hw : ∀ a, ∀ᵐ x ∂meshCellMeasure J hJ a,
      ENNReal.ofReal (Real.exp (-1)) ≤ w a x ∧ w a x ≤ ENNReal.ofReal (Real.exp 1))
    (η : LabelVector J N) :
    (∀ a, Integrable (potential (μ a)) (μ a) ∧ |pairAverage (μ a) (μ a)| ≤ selfBound J) ∧
    (∀ X, (∀ i, X i ∈ closure (meshCell J hJ (η i))) → |selfTerm μ η X| ≤ selfBound J) ∧
    (∀ᵐ X ∂Measure.pi (fun i => μ (η i)), |selfTerm μ η X| ≤ selfBound J) := by
  have hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a := by
    intro a
    rw [hμw a]
    exact NearLogMomentBounds.withDensity_le_exp_smul _ _ ((hw a).mono fun _ h => h.2)
  exact ⟨fun a => own_cell_pairAverage_abs hJ hmesh a (μ a) (hμ a),
    fun X hX => selfTerm_abs hJ hmesh μ hμ η X hX, selfTerm_ae_abs hJ hmesh μ hμ η⟩

def averagePotential {J N : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J N) (x : Torus) : ℝ :=
  (∑ j, potential (μ (η j)) x) / (N : ℝ)

/-- Each off-diagonal ordered term occurs exactly once in the two terms of
an upper pair; no symmetry of the supplied function is assumed. -/
theorem upper_pair_cross_sum {N : ℕ} (f : Fin N → Fin N → ℝ) :
    (∑ ij ∈ ResidualNearExponential.upperPairs N, (f ij.1 ij.2 + f ij.2 ij.1)) =
      (∑ i, ∑ j, f i j) - ∑ i, f i i := by
  classical
  unfold ResidualNearExponential.upperPairs
  rw [Finset.sum_filter, Finset.sum_product]
  have hd (i j : Fin N) : (if i < j then f i j + f j i else 0) =
      (if i < j then f i j else 0) + (if i < j then f j i else 0) := by
    by_cases h : i < j <;> simp [h]
  simp_rw [hd, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin N => if i < j then f j i else 0)]
  have hs (i j : Fin N) :
      (if i < j then f i j else 0) + (if j < i then f i j else 0) +
        (if i = j then f i j else 0) = f i j := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j
      simp
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  have hh :
      (∑ i : Fin N, ∑ j : Fin N, if i < j then f i j else 0) +
      (∑ i : Fin N, ∑ j : Fin N, if j < i then f i j else 0) +
      (∑ i : Fin N, f i i) = ∑ i, ∑ j, f i j := by
    calc
      _ = ∑ i : Fin N, ∑ j : Fin N,
          ((if i < j then f i j else 0) + (if j < i then f i j else 0) +
            (if i = j then f i j else 0)) := by
        simp only [Finset.sum_add_distrib]
        simp
      _ = _ := by simp_rw [hs]
  linarith

/-- Exact source centering expansion for the actual regular Green
representative. The source-order residual identity already derives its
potential symmetry from greenKernel_symm. No pole identification is used. -/
theorem centering_expansion {J N : ℕ} (μ : MeshIndex J → Measure Torus)
    [∀ a, IsProbabilityMeasure (μ a)] (η : LabelVector J N) (X : Fin N → Torus) :
    ResidualExponential.residualSum μ η X =
      (∑ ij ∈ ResidualNearExponential.upperPairs N, greenKernel (X ij.1) (X ij.2)) / (N : ℝ) -
      (∑ i, averagePotential μ η (X i)) + selfTerm μ η X +
      (∑ ij ∈ ResidualNearExponential.upperPairs N, pairAverage (μ (η ij.1)) (μ (η ij.2))) / (N : ℝ) := by
  classical
  have hc := upper_pair_cross_sum (fun i j => potential (μ (η j)) (X i))
  simp only [Finset.sum_add_distrib] at hc
  have hr :
      (∑ ij ∈ ResidualNearExponential.upperPairs N,
        residual (μ (η ij.1)) (μ (η ij.2)) (X ij.1) (X ij.2)) =
      (∑ ij ∈ ResidualNearExponential.upperPairs N, greenKernel (X ij.1) (X ij.2)) -
        (∑ i, ∑ j, potential (μ (η j)) (X i)) + (∑ i, potential (μ (η i)) (X i)) +
      (∑ ij ∈ ResidualNearExponential.upperPairs N, pairAverage (μ (η ij.1)) (μ (η ij.2))) := by
    simp_rw [residual_eq_source_order, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    linarith
  rw [ResidualExponential.residualSum_eq_upper_pairs, hr]
  simp only [averagePotential, selfTerm, ← Finset.sum_div]
  ring

end PeriodicAttractiveLogGas.ReferenceSelfTerms
