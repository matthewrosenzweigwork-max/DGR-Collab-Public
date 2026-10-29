import LeanResearch.PeriodicAttractiveLogGas.HeavyCoercivity
import LeanResearch.PeriodicAttractiveLogGas.DiscreteOccupationIdentities

/-! The actual occupation transition cutoff and source Proposition
`prop:occupation-mass-cutoff`. Exact checking status is in the development note. -/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped BigOperators Topology NNReal

namespace PeriodicAttractiveLogGas.OccupationMassCutoff

open MeshCells LabelOccupations SmoothOccupations LocalizedVirialCutoffs
open SeparatedRadius HeavyScales HeavyCoercivityConstants HeavyLocalization

def transitionProfile (lo hi r : ℝ) : ℝ := H ((r - lo) / (hi - lo))

theorem hasDerivAt_transitionProfile (lo hi r : ℝ) :
    HasDerivAt (transitionProfile lo hi) (b ((r - lo) / (hi - lo)) / (hi - lo)) r := by
  change HasDerivAt (fun x : ℝ ↦ H ((x - lo) / (hi - lo))) _ r
  simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using
    (hasDerivAt_H _).comp r (((hasDerivAt_id r).sub_const lo).div_const (hi - lo))

theorem affine_lipschitz {lo hi : ℝ} (hgap : lo < hi) :
    LipschitzWith (Real.toNNReal (1 / (hi - lo))) (fun r : ℝ ↦ (r - lo) / (hi - lo)) := by
  have hg : 0 < hi - lo := sub_pos.mpr hgap
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq,
    show (x - lo) / (hi - lo) - (y - lo) / (hi - lo) = (x - y) / (hi - lo) by ring,
    abs_div, abs_of_pos hg, Real.toNNReal_of_nonneg (by positivity)]
  change |x - y| / (hi - lo) ≤ (1 / (hi - lo)) * |x - y|
  exact le_of_eq (by ring)

def cutoff (N J : ℕ) (hJ : 0 < J) (lo hi : ℝ) (X : Configuration N) : ℝ :=
  transitionProfile lo hi (maximumOccupation N J hJ X)

theorem continuous_cutoff (N J : ℕ) (hJ : 0 < J) (lo hi : ℝ) :
    Continuous (cutoff N J hJ lo hi) :=
  contDiff_H.continuous.comp
    (((maximumOccupation_continuous N J hJ).sub continuous_const).div_const (hi - lo))

def cutoffValue (N J : ℕ) (hJ : 0 < J) (lo hi : ℝ) : C(Configuration N, ℝ) :=
  ⟨cutoff N J hJ lo hi, continuous_cutoff N J hJ lo hi⟩

def cutoffLiftConstant (N J : ℕ) (lo hi : ℝ) : ℝ≥0 :=
  2 * (Real.toNNReal (1 / (hi - lo)) * occupationLipschitzConstant N J)

theorem cutoff_lift_lipschitz (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {lo hi : ℝ} (hgap : lo < hi) :
    LipschitzWith (cutoffLiftConstant N J lo hi)
      (fun y ↦ cutoffValue N J (by omega) lo hi (configurationQuotient N y)) :=
  H_lipschitz.comp ((affine_lipschitz hgap).comp (maximumOccupation_lift_lipschitz N J hN hJ))

theorem cutoff_mem_Icc (N J : ℕ) (hJ : 0 < J) (lo hi : ℝ) (X : Configuration N) :
    cutoffValue N J hJ lo hi X ∈ Icc (0 : ℝ) 1 := H_mem_Icc _

theorem cutoff_eq_zero {N J : ℕ} (hJ : 0 < J) {lo hi : ℝ} (hgap : lo < hi)
    {X : Configuration N} (hX : maximumOccupation N J hJ X ≤ lo) :
    cutoffValue N J hJ lo hi X = 0 :=
  H_eq_zero_of_le (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hX) (sub_pos.mpr hgap).le)

theorem cutoff_eq_one {N J : ℕ} (hJ : 0 < J) {lo hi : ℝ} (hgap : lo < hi)
    {X : Configuration N} (hX : hi ≤ maximumOccupation N J hJ X) :
    cutoffValue N J hJ lo hi X = 1 := by
  apply H_eq_one_of_one_le
  apply (le_div_iff₀ (sub_pos.mpr hgap)).2
  linarith

def transitionRegion (N J : ℕ) (hJ : 0 < J) (lo hi : ℝ) : Set (Configuration N) :=
  {X | lo < maximumOccupation N J hJ X ∧ maximumOccupation N J hJ X < hi}

def badLabelEvent (N J : ℕ) (hJ : 0 < J) (hi : ℝ) : Set (Configuration N) :=
  {X | configurationMeshLabel N J hJ X ∉ goodLabels J N hi}

def goodLabelEvent (N J : ℕ) (hJ : 0 < J) (hi : ℝ) : Set (Configuration N) :=
  {X | configurationMeshLabel N J hJ X ∈ goodLabels J N hi}

theorem measurableSet_transitionRegion (N J : ℕ) (hJ : 0 < J) (lo hi : ℝ) :
    MeasurableSet (transitionRegion N J hJ lo hi) :=
  ((isOpen_lt continuous_const (maximumOccupation_continuous N J hJ)).inter
    (isOpen_lt (maximumOccupation_continuous N J hJ) continuous_const)).measurableSet

theorem measurableSet_goodLabelEvent (N J : ℕ) (hJ : 0 < J) (hi : ℝ) :
    MeasurableSet (goodLabelEvent N J hJ hi) := by
  change MeasurableSet ((configurationMeshLabel N J hJ) ⁻¹' goodLabels J N hi)
  exact (Set.toFinite (goodLabels J N hi)).measurableSet.preimage
    (measurable_configurationMeshLabel N J hJ)

theorem measurableSet_badLabelEvent (N J : ℕ) (hJ : 0 < J) (hi : ℝ) :
    MeasurableSet (badLabelEvent N J hJ hi) :=
  (measurableSet_goodLabelEvent N J hJ hi).compl

theorem cutoff_eq_one_on_bad (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {lo hi : ℝ} (hgap : lo < hi) {X : Configuration N}
    (hX : X ∈ badLabelEvent N J (by omega) hi) :
    cutoffValue N J (by omega) lo hi X = 1 :=
  cutoff_eq_one (by omega) hgap (bad_labels_subset_maximum_gt N J hN hJ hi hX).le

theorem transitionRegion_subset_good (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J) (lo hi : ℝ) :
    transitionRegion N J (by omega) lo hi ⊆ goodLabelEvent N J (by omega) hi :=
  fun _ hX ↦ maximum_lt_subset_good_labels N J hN hJ hi hX.2

/-- The genuine chain rule on the common Gibbs-full differentiability set. -/
theorem ae_cutoff_gradient (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J) (lo hi β : ℝ) :
    ∀ᵐ X ∂gibbsMeasure greenRealRepresentative N β,
      descendedLiftGradient (cutoffValue N J (by omega) lo hi) X =
        (b ((maximumOccupation N J (by omega) X - lo) / (hi - lo)) / (hi - lo)) •
          descendedLiftGradient (maximumValue N J (by omega)) X := by
  filter_upwards [maximumOccupation_ae_hasFDerivAt_gibbs N J hN hJ greenRealRepresentative β]
    with X hX
  have hdu := hX (configurationCenteredLift X) (configurationQuotient_centeredLift X)
  have hd := (hasDerivAt_transitionProfile lo hi _).comp_hasFDerivAt
    (configurationCenteredLift X) hdu
  simp only [Function.comp_def, configurationQuotient_centeredLift] at hd
  apply ext_inner_right ℝ
  intro v
  rw [← innerSL_apply_apply, innerSL_descendedLiftGradient, descendedLiftDifferential]
  change fderiv ℝ (fun y ↦ transitionProfile lo hi
    (maximumOccupation N J (by omega) (configurationQuotient N y)))
    (configurationCenteredLift X) v = _
  rw [hd.fderiv]
  simp only [smul_apply, innerSL_apply_apply, inner_smul_left, conj_trivial, smul_eq_mul]

/-- The source strict transition-band bound, including both boundary levels. -/
theorem ae_cutoff_gradient_sq_bound (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {lo hi : ℝ} (hgap : lo < hi) (β : ℝ) :
    ∀ᵐ X ∂gibbsMeasure greenRealRepresentative N β,
      ‖descendedLiftGradient (cutoffValue N J (by omega) lo hi) X‖ ^ 2 ≤
        (transitionRegion N J (by omega) lo hi).indicator
          (fun _ ↦ 72 * (J : ℝ) ^ 2 / (N * (hi - lo) ^ 2)) X := by
  have hg : 0 < hi - lo := sub_pos.mpr hgap
  filter_upwards [ae_cutoff_gradient N J hN hJ lo hi β] with X hd
  rw [hd]
  by_cases hX : X ∈ transitionRegion N J (by omega) lo hi
  · rw [Set.indicator_of_mem hX, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hb0 : 0 ≤ b ((maximumOccupation N J (by omega) X - lo) / (hi - lo)) / (hi - lo) :=
      div_nonneg (b_nonneg _) hg.le
    have hb2 : b ((maximumOccupation N J (by omega) X - lo) / (hi - lo)) / (hi - lo) ≤
        2 / (hi - lo) := div_le_div_of_nonneg_right (b_le_two _) hg.le
    calc
      _ ≤ (2 / (hi - lo)) ^ 2 * (18 * (J : ℝ) ^ 2 / N) :=
        mul_le_mul (pow_le_pow_left₀ hb0 hb2 2)
          (maximumOccupation_gradient_sq_bound N J hN hJ X) (sq_nonneg _) (sq_nonneg _)
      _ = _ := by
        have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
        field_simp [hg.ne', hNr]
        ring
  · rw [Set.indicator_of_notMem hX]
    have hb : b ((maximumOccupation N J (by omega) X - lo) / (hi - lo)) = 0 := by
      by_cases hlo : maximumOccupation N J (by omega) X ≤ lo
      · exact b_eq_zero_of_le (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hlo) hg.le)
      · have hhi : hi ≤ maximumOccupation N J (by omega) X :=
          le_of_not_gt fun hh ↦ hX ⟨lt_of_not_ge hlo, hh⟩
        apply b_eq_zero_of_one_le
        apply (le_div_iff₀ hg).2
        linarith
    simp only [hb, zero_div, zero_smul, norm_zero, zero_pow (by decide : 2 ≠ 0), le_refl]

/-- The source particle threshold lies in the genuine subcritical probability
regime; this is derived rather than added to the proposition's hypotheses. -/
theorem threshold_two {N : ℕ} {β₀ lo : ℝ} (hlo : 0 < lo) (hlo1 : lo < 1)
    (hN : particleThreshold β₀ lo ≤ N) : 2 ≤ N := by
  apply SeparatedCoercivity.two_le_particle_number (δ := lo) hlo hlo1
  exact (div_le_div_of_nonneg_right (by norm_num : (4 : ℝ) ≤ 8) hlo.le).trans
    (threshold_eight hN)

theorem cutoff_energy_le (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {lo hi : ℝ} (hgap : lo < hi) (β : ℝ)
    [IsProbabilityMeasure (gibbsMeasure greenRealRepresentative N β)] :
    ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
      (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β)
      (cutoffValue N J (by omega) lo hi) (cutoff_lift_lipschitz N J hN hJ hgap)) ≤
        72 * (J : ℝ) ^ 2 / (N * (hi - lo) ^ 2) := by
  rw [configurationLipschitzAmbient_energy_eq_integral]
  calc
    _ ≤ ∫ _X, (72 * (J : ℝ) ^ 2 / (N * (hi - lo) ^ 2))
        ∂gibbsMeasure greenRealRepresentative N β := by
      apply integral_mono_ae
        (integrable_sq_norm_descendedLiftGradient _ _ (cutoff_lift_lipschitz N J hN hJ hgap))
        (integrable_const _)
      filter_upwards [ae_cutoff_gradient_sq_bound N J hN hJ hgap β] with X hX
      apply hX.trans
      by_cases hmem : X ∈ transitionRegion N J (by omega) lo hi
      · rw [Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hmem]
        positivity
    _ = _ := by simp

theorem bad_mass_le_cutoff_sq (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {lo hi : ℝ} (hgap : lo < hi) (β : ℝ) :
    (gibbsMeasure greenRealRepresentative N β (badLabelEvent N J (by omega) hi)).toReal ≤
      ∫ X, cutoffValue N J (by omega) lo hi X ^ 2 ∂gibbsMeasure greenRealRepresentative N β := by
  change (gibbsMeasure greenRealRepresentative N β).real (badLabelEvent N J (by omega) hi) ≤ _
  rw [← integral_indicator_one (measurableSet_badLabelEvent N J (by omega) hi)]
  apply integral_mono_ae
    ((integrable_const (1 : ℝ)).indicator (measurableSet_badLabelEvent N J (by omega) hi))
    (integrable_continuous_sq _ _)
  filter_upwards [] with X
  by_cases hmem : X ∈ badLabelEvent N J (by omega) hi
  · rw [Set.indicator_of_mem hmem, cutoff_eq_one_on_bad N J hN hJ hgap hmem]
    norm_num
  · rw [Set.indicator_of_notMem hmem]
    exact sq_nonneg _

/-- The original Gibbs mass of the actual bad-label event, with source constant
72 and the particle threshold independent of the mesh. -/
theorem bad_label_mass_bound {β₀ lo hi : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ4 : β₀ < 4) (hlo : 0 < lo) (hgap : lo < hi) (hhi : hi < 1)
    {N J : ℕ} (hJ : sourceResolution β₀ lo ≤ J) (hN : particleThreshold β₀ lo ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) :
    (gibbsMeasure greenRealRepresentative N β (badLabelEvent N J (source_mesh_pos hJ) hi)).toReal ≤
      72 * coercivityConstant β₀ lo / ((N : ℝ) ^ 2 * (hi - lo) ^ 2) := by
  have hNpos := threshold_positive hlo hN
  have hJthree := source_mesh_ge_three hJ
  have hNtwo := threshold_two hlo (hgap.trans hhi) hN
  let hprob := isProbabilityMeasure_greenGibbs N hNtwo hβ (hβle.trans_lt hβ4)
  have hcoer := HeavyCoercivity.heavy_coercivity hβ₀ hβ4 hlo (hgap.trans hhi) hJ hN hβ hβle
    (cutoffValue N J (source_mesh_pos hJ) lo hi)
    (cutoff_lift_lipschitz N J hNpos hJthree hgap)
    (fun X hX ↦ cutoff_eq_zero (source_mesh_pos hJ) hgap hX)
  have hcoef : 0 ≤ coercivityConstant β₀ lo / ((J : ℝ) ^ 2 * N) :=
    div_nonneg (coercivityConstant_pos hβ4 hlo).le (by positivity)
  calc
    _ ≤ ∫ X, cutoffValue N J (source_mesh_pos hJ) lo hi X ^ 2
        ∂gibbsMeasure greenRealRepresentative N β := bad_mass_le_cutoff_sq N J hNpos hJthree hgap β
    _ ≤ _ := hcoer.trans (mul_le_mul_of_nonneg_left
      (cutoff_energy_le N J hNpos hJthree hgap β) hcoef) |>.trans_eq (by
        have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hNpos
        have hJr : (J : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (source_mesh_pos hJ)
        field_simp [hNr, hJr, (sub_pos.mpr hgap).ne'])

/-- Exactly the source half-mass threshold, chosen independently of J. -/
def halfMassThreshold (β₀ lo hi : ℝ) : ℕ :=
  max (particleThreshold β₀ lo) ⌈12 * Real.sqrt (coercivityConstant β₀ lo) / (hi - lo)⌉₊

theorem mass_coefficient_le_half {β₀ lo hi : ℝ} (hβ4 : β₀ < 4)
    (hlo : 0 < lo) (hgap : lo < hi) {N : ℕ} (hN : halfMassThreshold β₀ lo hi ≤ N) :
    72 * coercivityConstant β₀ lo / ((N : ℝ) ^ 2 * (hi - lo) ^ 2) ≤ 1 / 2 := by
  have hC := coercivityConstant_pos hβ4 hlo
  have hg : 0 < hi - lo := sub_pos.mpr hgap
  have hDP : particleThreshold β₀ lo ≤ N := (le_max_left _ _).trans hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast threshold_positive hlo hDP
  have ht : 12 * Real.sqrt (coercivityConstant β₀ lo) / (hi - lo) ≤ (N : ℝ) :=
    Nat.ceil_le.mp ((le_max_right _ _).trans hN)
  have ht' := (div_le_iff₀ hg).mp ht
  have hs : (12 * Real.sqrt (coercivityConstant β₀ lo)) ^ 2 ≤ ((N : ℝ) * (hi - lo)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr ht'
  simp only [mul_pow, Real.sq_sqrt hC.le] at hs
  apply (div_le_iff₀ (by positivity : 0 < (N : ℝ) ^ 2 * (hi - lo) ^ 2)).2
  nlinarith

/-- The source pi mass is the existing actual unconditioned labelCapMass. -/
theorem good_label_mass_ge_half {β₀ lo hi : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ4 : β₀ < 4) (hlo : 0 < lo) (hgap : lo < hi) (hhi : hi < 1)
    {N J : ℕ} (hJ : sourceResolution β₀ lo ≤ J) (hN : halfMassThreshold β₀ lo hi ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) :
    1 / 2 ≤ DiscreteOccupationIdentities.labelCapMass (N := N) (t := hi) (source_mesh_pos hJ) β := by
  have hDP : particleThreshold β₀ lo ≤ N := (le_max_left _ _).trans hN
  have hNtwo := threshold_two hlo (hgap.trans hhi) hDP
  let hprob := isProbabilityMeasure_greenGibbs N hNtwo hβ (hβle.trans_lt hβ4)
  have hbad := (bad_label_mass_bound hβ₀ hβ4 hlo hgap hhi hJ hDP hβ hβle).trans
    (mass_coefficient_le_half hβ4 hlo hgap hN)
  rw [DiscreteOccupationIdentities.labelCapMass_eq_actual (source_mesh_pos hJ) hNtwo hβ
    (hβle.trans_lt hβ4)]
  have hsum := probReal_add_probReal_compl (μ := gibbsMeasure greenRealRepresentative N β)
    (measurableSet_goodLabelEvent N J (source_mesh_pos hJ) hi)
  change (gibbsMeasure greenRealRepresentative N β).real (goodLabelEvent N J (source_mesh_pos hJ) hi) +
    (gibbsMeasure greenRealRepresentative N β).real (badLabelEvent N J (source_mesh_pos hJ) hi) = 1 at hsum
  change 1 / 2 ≤ (gibbsMeasure greenRealRepresentative N β).real
    (goodLabelEvent N J (source_mesh_pos hJ) hi)
  change (gibbsMeasure greenRealRepresentative N β).real
    (badLabelEvent N J (source_mesh_pos hJ) hi) ≤ 1 / 2 at hbad
  linarith

def shiftValue {N : ℕ} (F : C(Configuration N, ℝ)) (c : ℝ) : C(Configuration N, ℝ) :=
  F - ContinuousMap.const (Configuration N) c

@[simp] theorem shiftValue_apply {N : ℕ} (F : C(Configuration N, ℝ)) (c : ℝ) (X : Configuration N) :
    shiftValue F c X = F X - c := rfl

theorem shift_lift_lipschitz {N : ℕ} (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y))) (c : ℝ) :
    LipschitzWith L (fun y ↦ shiftValue F c (configurationQuotient N y)) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro y z
  change ‖(F (configurationQuotient N y) - c) - (F (configurationQuotient N z) - c)‖ ≤ _
  rw [show (F (configurationQuotient N y) - c) - (F (configurationQuotient N z) - c) =
    F (configurationQuotient N y) - F (configurationQuotient N z) by ring]
  exact lipschitzWith_iff_norm_sub_le.mp hF y z

theorem ae_shift_gradient {N : ℕ} (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y))) (c β : ℝ) :
    ∀ᵐ X ∂gibbsMeasure greenRealRepresentative N β,
      descendedLiftGradient (shiftValue F c) X = descendedLiftGradient F X := by
  filter_upwards [ae_hasFDerivAt_configurationLift_gibbs greenRealRepresentative β F hF] with X hX
  have hd := (hX (configurationCenteredLift X) (configurationQuotient_centeredLift X)).sub_const c
  apply ext_inner_right ℝ
  intro v
  rw [← innerSL_apply_apply, innerSL_descendedLiftGradient, descendedLiftDifferential]
  change fderiv ℝ (fun y ↦ F (configurationQuotient N y) - c) (configurationCenteredLift X) v = _
  rw [hd.fderiv, innerSL_apply_apply]

def cutoffProduct (N J : ℕ) (hJ : 0 < J) (lo hi : ℝ) (F : C(Configuration N, ℝ)) (c : ℝ) :
    C(Configuration N, ℝ) := shiftValue F c * cutoffValue N J hJ lo hi

@[simp] theorem cutoffProduct_apply (N J : ℕ) (hJ : 0 < J) (lo hi : ℝ)
    (F : C(Configuration N, ℝ)) (c : ℝ) (X : Configuration N) :
    cutoffProduct N J hJ lo hi F c X = (F X - c) * cutoffValue N J hJ lo hi X := rfl

theorem cutoffProduct_lift_lipschitz (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {lo hi : ℝ} (hgap : lo < hi) (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y))) (c : ℝ) :
    LipschitzWith (‖shiftValue F c‖₊ * cutoffLiftConstant N J lo hi +
      L * ‖cutoffValue N J (by omega) lo hi‖₊)
      (fun y ↦ cutoffProduct N J (by omega) lo hi F c (configurationQuotient N y)) := by
  exact lipschitz_lift_mul (shiftValue F c) (cutoffValue N J (by omega) lo hi)
    (K := L) (L := cutoffLiftConstant N J lo hi)
    (shift_lift_lipschitz F hF c) (cutoff_lift_lipschitz N J hN hJ hgap)

theorem integrable_weighted_cutoff_gradient (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {lo hi : ℝ} (hgap : lo < hi) (F : C(Configuration N, ℝ)) (β : ℝ) :
    Integrable (fun X ↦ F X ^ 2 * ‖descendedLiftGradient (cutoffValue N J (by omega) lo hi) X‖ ^ 2)
      (gibbsMeasure greenRealRepresentative N β) := by
  apply (integrable_sq_norm_descendedLiftGradient (gibbsMeasure greenRealRepresentative N β)
    _ (cutoff_lift_lipschitz N J hN hJ hgap)).bdd_mul
      (F.continuous.measurable.pow_const 2).aestronglyMeasurable
  filter_upwards [] with X
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (F.norm_coe_le_norm X) 2

/-- Integrated cutoff cost on exactly the strict source transition band. -/
theorem weighted_cutoff_gradient_le (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {lo hi : ℝ} (hgap : lo < hi) (F : C(Configuration N, ℝ)) (β : ℝ) :
    (∫ X, F X ^ 2 * ‖descendedLiftGradient (cutoffValue N J (by omega) lo hi) X‖ ^ 2
      ∂gibbsMeasure greenRealRepresentative N β) ≤
      (72 * (J : ℝ) ^ 2 / (N * (hi - lo) ^ 2)) *
        ∫ X in transitionRegion N J (by omega) lo hi, F X ^ 2
          ∂gibbsMeasure greenRealRepresentative N β := by
  let A : ℝ := 72 * (J : ℝ) ^ 2 / (N * (hi - lo) ^ 2)
  let S := transitionRegion N J (by omega) lo hi
  have hS : MeasurableSet S := measurableSet_transitionRegion N J (by omega) lo hi
  calc
    _ ≤ ∫ X, A * S.indicator (fun X ↦ F X ^ 2) X ∂gibbsMeasure greenRealRepresentative N β := by
      apply integral_mono_ae (integrable_weighted_cutoff_gradient N J hN hJ hgap F β)
        (((integrable_continuous_sq (gibbsMeasure greenRealRepresentative N β) F).indicator hS).const_mul A)
      filter_upwards [ae_cutoff_gradient_sq_bound N J hN hJ hgap β] with X hX
      calc
        _ ≤ F X ^ 2 * S.indicator (fun _ ↦ A) X := mul_le_mul_of_nonneg_left hX (sq_nonneg _)
        _ = _ := by by_cases hmem : X ∈ S <;> simp [Set.indicator, hmem, mul_comm]
    _ = _ := by rw [integral_const_mul, integral_indicator hS]

theorem ae_cutoffProduct_gradient (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {lo hi : ℝ} (hgap : lo < hi) (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y))) (c β : ℝ) :
    ∀ᵐ X ∂gibbsMeasure greenRealRepresentative N β,
      descendedLiftGradient (cutoffProduct N J (by omega) lo hi F c) X =
        (F X - c) • descendedLiftGradient (cutoffValue N J (by omega) lo hi) X +
          cutoffValue N J (by omega) lo hi X • descendedLiftGradient F X := by
  filter_upwards [ae_descendedLiftGradient_mul (gibbsMeasure greenRealRepresentative N β)
      (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β)
      (shiftValue F c) (cutoffValue N J (by omega) lo hi)
      (shift_lift_lipschitz F hF c) (cutoff_lift_lipschitz N J hN hJ hgap),
    ae_shift_gradient F hF c β] with X hp hs
  simpa only [cutoffProduct, shiftValue_apply, hs] using hp

private theorem norm_add_sq_le_twice {E : Type*} [NormedAddCommGroup E] (v w : E) :
    ‖v + w‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (v + w)) (norm_add_le v w) 2
  nlinarith [sq_nonneg (‖v‖ - ‖w‖)]

theorem ae_cutoffProduct_gradient_sq_bound (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {lo hi : ℝ} (hgap : lo < hi) (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y))) (c β : ℝ) :
    ∀ᵐ X ∂gibbsMeasure greenRealRepresentative N β,
      ‖descendedLiftGradient (cutoffProduct N J (by omega) lo hi F c) X‖ ^ 2 ≤
        2 * ‖descendedLiftGradient F X‖ ^ 2 +
          2 * ((F X - c) ^ 2 * ‖descendedLiftGradient (cutoffValue N J (by omega) lo hi) X‖ ^ 2) := by
  filter_upwards [ae_cutoffProduct_gradient N J hN hJ hgap F hF c β] with X hd
  rw [hd]
  have hχ := cutoff_mem_Icc N J (by omega) lo hi X
  have hχsq : cutoffValue N J (by omega) lo hi X ^ 2 ≤ 1 := by
    nlinarith [hχ.1, hχ.2]
  have hχbound := mul_le_mul_of_nonneg_right hχsq (sq_nonneg ‖descendedLiftGradient F X‖)
  calc
    _ ≤ 2 * ‖(F X - c) • descendedLiftGradient (cutoffValue N J (by omega) lo hi) X‖ ^ 2 +
        2 * ‖cutoffValue N J (by omega) lo hi X • descendedLiftGradient F X‖ ^ 2 :=
      norm_add_sq_le_twice _ _
    _ ≤ _ := by
      simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      nlinarith

theorem cutoffProduct_gradient_integral_le (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {lo hi : ℝ} (hgap : lo < hi) (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y))) (c β : ℝ) :
    (∫ X, ‖descendedLiftGradient (cutoffProduct N J (by omega) lo hi F c) X‖ ^ 2
      ∂gibbsMeasure greenRealRepresentative N β) ≤
      2 * (∫ X, ‖descendedLiftGradient F X‖ ^ 2 ∂gibbsMeasure greenRealRepresentative N β) +
      2 * ∫ X, (F X - c) ^ 2 * ‖descendedLiftGradient (cutoffValue N J (by omega) lo hi) X‖ ^ 2
        ∂gibbsMeasure greenRealRepresentative N β := by
  let μ : Measure (Configuration N) := gibbsMeasure greenRealRepresentative N β
  change (∫ X, ‖descendedLiftGradient (cutoffProduct N J (by omega) lo hi F c) X‖ ^ 2 ∂μ) ≤
    2 * (∫ X, ‖descendedLiftGradient F X‖ ^ 2 ∂μ) +
      2 * ∫ X, (F X - c) ^ 2 * ‖descendedLiftGradient (cutoffValue N J (by omega) lo hi) X‖ ^ 2 ∂μ
  have hPi : Integrable
      (fun X ↦ ‖descendedLiftGradient (cutoffProduct N J (by omega) lo hi F c) X‖ ^ 2) μ :=
    integrable_sq_norm_descendedLiftGradient μ (cutoffProduct N J (by omega) lo hi F c)
      (cutoffProduct_lift_lipschitz N J hN hJ hgap F hF c)
  have hFi : Integrable (fun X ↦ ‖descendedLiftGradient F X‖ ^ 2) μ :=
    integrable_sq_norm_descendedLiftGradient μ F hF
  have hCi : Integrable
      (fun X ↦ (F X - c) ^ 2 * ‖descendedLiftGradient (cutoffValue N J (by omega) lo hi) X‖ ^ 2) μ := by
    simpa only [shiftValue_apply] using!
      integrable_weighted_cutoff_gradient N J hN hJ hgap (shiftValue F c) β
  have hRi : Integrable (fun X ↦ 2 * ‖descendedLiftGradient F X‖ ^ 2 +
      2 * ((F X - c) ^ 2 * ‖descendedLiftGradient (cutoffValue N J (by omega) lo hi) X‖ ^ 2)) μ := by
    simpa only [Pi.add_apply] using! ((hFi.const_mul 2).add (hCi.const_mul 2))
  calc
    _ ≤ ∫ X, 2 * ‖descendedLiftGradient F X‖ ^ 2 +
        2 * ((F X - c) ^ 2 * ‖descendedLiftGradient (cutoffValue N J (by omega) lo hi) X‖ ^ 2) ∂μ := by
      simpa only using! (integral_mono_ae hPi hRi
        (ae_cutoffProduct_gradient_sq_bound N J hN hJ hgap F hF c β))
    _ = _ := by
      rw [integral_add (hFi.const_mul 2) (hCi.const_mul 2), integral_const_mul, integral_const_mul]

/-- Product energy with the actual ambient normalization and arbitrary shift. -/
theorem cutoffProduct_energy_le (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {lo hi : ℝ} (hgap : lo < hi) (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y))) (c β : ℝ) :
    ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
      (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β)
      (cutoffProduct N J (by omega) lo hi F c) (cutoffProduct_lift_lipschitz N J hN hJ hgap F hF c)) ≤
      2 * ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
        (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF) +
      2 * ∫ X, (F X - c) ^ 2 * ‖descendedLiftGradient (cutoffValue N J (by omega) lo hi) X‖ ^ 2
        ∂gibbsMeasure greenRealRepresentative N β := by
  simp only [configurationLipschitzAmbient_energy_eq_integral]
  exact cutoffProduct_gradient_integral_le N J hN hJ hgap F hF c β

theorem bad_integral_le_cutoffProduct_sq (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {lo hi : ℝ} (hgap : lo < hi) (F : C(Configuration N, ℝ)) (c β : ℝ) :
    (∫ X in badLabelEvent N J (by omega) hi, (F X - c) ^ 2
      ∂gibbsMeasure greenRealRepresentative N β) ≤
      ∫ X, cutoffProduct N J (by omega) lo hi F c X ^ 2 ∂gibbsMeasure greenRealRepresentative N β := by
  have hbad := measurableSet_badLabelEvent N J (by omega) hi
  rw [← integral_indicator hbad]
  apply integral_mono_ae
    ((integrable_continuous_sq (gibbsMeasure greenRealRepresentative N β) (shiftValue F c)).indicator hbad)
    (integrable_continuous_sq _ (cutoffProduct N J (by omega) lo hi F c))
  filter_upwards [] with X
  by_cases hmem : X ∈ badLabelEvent N J (by omega) hi
  · rw [Set.indicator_of_mem hmem, cutoffProduct_apply,
      cutoff_eq_one_on_bad N J hN hJ hgap hmem, mul_one]
    simp only [shiftValue_apply, le_refl]
  · rw [Set.indicator_of_notMem hmem]
    exact sq_nonneg _

/-- Source `eq:occupation-complement-control`, on the original Gibbs law and
with the exact strict transition band. The shift is arbitrary. -/
theorem occupation_complement_control {β₀ lo hi : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ4 : β₀ < 4) (hlo : 0 < lo) (hgap : lo < hi) (hhi : hi < 1)
    {N J : ℕ} (hJ : sourceResolution β₀ lo ≤ J) (hN : particleThreshold β₀ lo ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀)
    (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y))) (c : ℝ) :
    (∫ X in badLabelEvent N J (source_mesh_pos hJ) hi, (F X - c) ^ 2
      ∂gibbsMeasure greenRealRepresentative N β) ≤
      (2 * coercivityConstant β₀ lo / ((J : ℝ) ^ 2 * N)) *
        ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
          (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF) +
      (144 * coercivityConstant β₀ lo / ((N : ℝ) ^ 2 * (hi - lo) ^ 2)) *
        ∫ X in transitionRegion N J (source_mesh_pos hJ) lo hi, (F X - c) ^ 2
          ∂gibbsMeasure greenRealRepresentative N β := by
  have hNpos : 0 < N := threshold_positive hlo hN
  have hJthree : 3 ≤ J := source_mesh_ge_three hJ
  let μ := gibbsMeasure greenRealRepresentative N β
  let E : ℝ := ambientEnergy (configurationLipschitzAmbient μ
    (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF)
  let p : ℝ := coercivityConstant β₀ lo / ((J : ℝ) ^ 2 * N)
  let A : ℝ := 72 * (J : ℝ) ^ 2 / (N * (hi - lo) ^ 2)
  let B : ℝ := ∫ X in transitionRegion N J (source_mesh_pos hJ) lo hi, (F X - c) ^ 2 ∂μ
  have hp : 0 ≤ p := div_nonneg (coercivityConstant_pos hβ4 hlo).le (by positivity)
  have hsupport : ∀ X, maximumOccupation N J (source_mesh_pos hJ) X ≤ lo →
      cutoffProduct N J (source_mesh_pos hJ) lo hi F c X = 0 := by
    intro X hX
    rw [cutoffProduct_apply, cutoff_eq_zero (source_mesh_pos hJ) hgap hX, mul_zero]
  have hcoer := HeavyCoercivity.heavy_coercivity hβ₀ hβ4 hlo (hgap.trans hhi) hJ hN hβ hβle
    (cutoffProduct N J (source_mesh_pos hJ) lo hi F c)
    (cutoffProduct_lift_lipschitz N J hNpos hJthree hgap F hF c) hsupport
  have hweighted := weighted_cutoff_gradient_le N J hNpos hJthree hgap (shiftValue F c) β
  have henergy := cutoffProduct_energy_le N J hNpos hJthree hgap F hF c β
  calc
    _ ≤ ∫ X, cutoffProduct N J (source_mesh_pos hJ) lo hi F c X ^ 2 ∂μ :=
      bad_integral_le_cutoffProduct_sq N J hNpos hJthree hgap F c β
    _ ≤ p * ambientEnergy (configurationLipschitzAmbient μ
        (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β)
        (cutoffProduct N J (source_mesh_pos hJ) lo hi F c)
        (cutoffProduct_lift_lipschitz N J hNpos hJthree hgap F hF c)) := hcoer
    _ ≤ p * (2 * E + 2 * (A * B)) := by
      apply mul_le_mul_of_nonneg_left (henergy.trans ?_) hp
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hweighted (by norm_num : (0 : ℝ) ≤ 2))
    _ = _ := by
      change p * (2 * E + 2 * (A * B)) =
        (2 * coercivityConstant β₀ lo / ((J : ℝ) ^ 2 * N)) * E +
          (144 * coercivityConstant β₀ lo / ((N : ℝ) ^ 2 * (hi - lo) ^ 2)) * B
      dsimp [p, A]
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hNpos
      have hJr : (J : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (source_mesh_pos hJ)
      field_simp [hNr, hJr, (sub_pos.mpr hgap).ne']
      ring

/-- The source's permitted enlargement of the cutoff-error domain to the
actual good-label event. -/
theorem occupation_complement_control_good {β₀ lo hi : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ4 : β₀ < 4) (hlo : 0 < lo) (hgap : lo < hi) (hhi : hi < 1)
    {N J : ℕ} (hJ : sourceResolution β₀ lo ≤ J) (hN : particleThreshold β₀ lo ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀)
    (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y))) (c : ℝ) :
    (∫ X in badLabelEvent N J (source_mesh_pos hJ) hi, (F X - c) ^ 2
      ∂gibbsMeasure greenRealRepresentative N β) ≤
      (2 * coercivityConstant β₀ lo / ((J : ℝ) ^ 2 * N)) *
        ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
          (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF) +
      (144 * coercivityConstant β₀ lo / ((N : ℝ) ^ 2 * (hi - lo) ^ 2)) *
        ∫ X in goodLabelEvent N J (source_mesh_pos hJ) hi, (F X - c) ^ 2
          ∂gibbsMeasure greenRealRepresentative N β := by
  have hband : (∫ X in transitionRegion N J (source_mesh_pos hJ) lo hi, (F X - c) ^ 2
      ∂gibbsMeasure greenRealRepresentative N β) ≤
      ∫ X in goodLabelEvent N J (source_mesh_pos hJ) hi, (F X - c) ^ 2
        ∂gibbsMeasure greenRealRepresentative N β := by
    apply setIntegral_mono_set
    · exact (integrable_continuous_sq (gibbsMeasure greenRealRepresentative N β) (shiftValue F c)).integrableOn
    · exact Eventually.of_forall fun X ↦ sq_nonneg (F X - c)
    · exact Eventually.of_forall fun X hX ↦
        transitionRegion_subset_good N J (threshold_positive hlo hN) (source_mesh_ge_three hJ) lo hi hX
  apply (occupation_complement_control hβ₀ hβ4 hlo hgap hhi hJ hN hβ hβle F hF c).trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hband
    (div_nonneg (mul_nonneg (by norm_num) (coercivityConstant_pos hβ4 hlo).le) (by positivity)))

/-- Source `eq:microscopic-good-mass`, with C_DP evaluated at δ/4. -/
theorem microscopic_bad_label_mass {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ4 : β₀ < 4) (hδ : 0 < δ) (hδ2 : δ < 2)
    {N J : ℕ} (hJ : sourceResolution β₀ (δ / 4) ≤ J)
    (hN : particleThreshold β₀ (δ / 4) ≤ N) {β : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) :
    (gibbsMeasure greenRealRepresentative N β
      (badLabelEvent N J (source_mesh_pos hJ) (δ / 2))).toReal ≤
      1152 * coercivityConstant β₀ (δ / 4) / (δ ^ 2 * (N : ℝ) ^ 2) := by
  have hlo : 0 < δ / 4 := by positivity
  calc
    _ ≤ 72 * coercivityConstant β₀ (δ / 4) / ((N : ℝ) ^ 2 * (δ / 2 - δ / 4) ^ 2) :=
      bad_label_mass_bound hβ₀ hβ4 hlo (by linarith) (by linarith) hJ hN hβ hβle
    _ = _ := by
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (threshold_positive hlo hN)
      field_simp [hNr, hδ.ne']
      ring

end PeriodicAttractiveLogGas.OccupationMassCutoff
