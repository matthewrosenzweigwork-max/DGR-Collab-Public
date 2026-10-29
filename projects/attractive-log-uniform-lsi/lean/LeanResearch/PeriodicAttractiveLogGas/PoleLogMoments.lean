import LeanResearch.PeriodicAttractiveLogGas.SingularRectangleMoments
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Uniform logarithmic pole moments on the reference rectangles

Source equation `eq:logarithmic-moment`, lines 527--534 of the immutable
manuscript. The norm inside the logarithm is the physical Euclidean norm.
The admissibility condition uses the coordinate supremum norm, exactly as
in the source. Both reference measures are the actual normalized Lebesgue
restrictions already constructed in `RectangleReflection`.

Near the pole, `|log r| ≤ r⁻¹`; the checked inverse-distance moment at
exponent `4/3 < 2` gives an integral bound `1 + 3*pi`. On the rest of the
rectangle, the logarithm is bounded by `log (2*(R+4))`. This explicit
bound proves integrability before any integral or real Lp norm is used as
an estimate. The two nonempty, bounded sets of moments have actual real
suprema, and `lambdaStar` is exactly their maximum.

This file is a SOURCE_ONLY candidate. Its author has not executed Lean,
inspected an axiom closure, or obtained a verifier verdict for these bytes.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PeriodicAttractiveLogGas
namespace PoleLogMoments

open SingularRectangleMoments

/-- The half-open square used in the source. The checked reference measure
was defined using its closure. The two normalizations are identified below. -/
def halfOpenSquare : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun _ : Fin 2 ↦ Ico (0 : ℝ) 1)

def halfOpenRectangle : Set PlanarSpace :=
  WithLp.ofLp ⁻¹' Set.pi Set.univ (fun j : Fin 2 ↦ Ico 0 (doubleRectangleWidth j))

theorem halfOpenSquare_subset_closed : halfOpenSquare ⊆ closedUnitSquare := by
  intro Z hZ j hj
  exact ⟨(hZ j hj).1, (hZ j hj).2.le⟩

theorem halfOpenRectangle_subset_closed : halfOpenRectangle ⊆ closedDoubleRectangle := by
  intro Z hZ j hj
  exact ⟨(hZ j hj).1, (hZ j hj).2.le⟩

theorem ae_mem_halfOpenSquare : ∀ᵐ Z ∂squareLebesgue, Z ∈ halfOpenSquare :=
  ae_mem_openUnitSquare.mono fun _ hZ j hj ↦ ⟨(hZ j hj).1.le, (hZ j hj).2⟩

theorem ae_mem_halfOpenRectangle : ∀ᵐ Z ∂rectangleLebesgue, Z ∈ halfOpenRectangle :=
  ae_mem_openDoubleRectangle.mono fun _ hZ j hj ↦ ⟨(hZ j hj).1.le, (hZ j hj).2⟩

theorem squareLebesgue_eq_halfOpen :
    squareLebesgue = volume.restrict halfOpenSquare := by
  calc
    squareLebesgue = squareLebesgue.restrict halfOpenSquare :=
      (Measure.restrict_eq_self_of_ae_mem ae_mem_halfOpenSquare).symm
    _ = volume.restrict halfOpenSquare :=
      Measure.restrict_restrict_of_subset halfOpenSquare_subset_closed

theorem rectangleLebesgue_eq_halfOpen :
    rectangleLebesgue = ENNReal.ofReal (1 / 2 : ℝ) • volume.restrict halfOpenRectangle := by
  calc
    rectangleLebesgue = rectangleLebesgue.restrict halfOpenRectangle :=
      (Measure.restrict_eq_self_of_ae_mem ae_mem_halfOpenRectangle).symm
    _ = ENNReal.ofReal (1 / 2 : ℝ) • volume.restrict halfOpenRectangle := by
      rw [rectangleLebesgue, Measure.restrict_smul,
        Measure.restrict_restrict_of_subset halfOpenRectangle_subset_closed]

/-- Coordinate supremum norm, separated explicitly from the Euclidean norm
on `PlanarSpace`. -/
def coordinateSupNorm (v : PlanarSpace) : ℝ := ‖WithLp.ofLp v‖

theorem coordinateSupNorm_nonneg (v : PlanarSpace) : 0 ≤ coordinateSupNorm v :=
  norm_nonneg _

theorem abs_coordinate_le_supNorm (v : PlanarSpace) (j : Fin 2) :
    |v j| ≤ coordinateSupNorm v := by
  simpa only [coordinateSupNorm, Real.norm_eq_abs] using
    (norm_le_pi_norm (WithLp.ofLp v) j)

/-- A deliberately nonsharp conversion of the source's supremum bound to
a genuine Euclidean distance bound. It introduces no change of norm into
the logarithmic moment itself. -/
theorem euclidean_norm_le_two_mul {v : PlanarSpace} {C : ℝ} (hC : 0 ≤ C)
    (hv : coordinateSupNorm v ≤ C) : ‖v‖ ≤ 2 * C := by
  have h0 : |v 0| ≤ C := (abs_coordinate_le_supNorm v 0).trans hv
  have h1 : |v 1| ≤ C := (abs_coordinate_le_supNorm v 1).trans hv
  have hs0 : (v 0) ^ 2 ≤ C ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (v 0)) h0 2
  have hs1 : (v 1) ^ 2 ≤ C ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (v 1)) h1 2
  have hs : ‖v‖ ^ 2 ≤ (2 * C) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    nlinarith [sq_nonneg C]
  nlinarith [norm_nonneg v]

/-- Exactly the source pole constraint, imposed on the closed rectangle. -/
def admissiblePoles (B : Set PlanarSpace) (R : ℝ) : Set PlanarSpace :=
  {Y | ∀ Z ∈ B, coordinateSupNorm (Z - Y) ≤ R + 4}

theorem zero_mem_admissiblePoles_square {R : ℝ} (hR : 1 ≤ R) :
    (0 : PlanarSpace) ∈ admissiblePoles closedUnitSquare R := by
  intro Z hZ
  change ‖WithLp.ofLp (Z - 0)‖ ≤ R + 4
  rw [sub_zero]
  apply (pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ R + 4)).mpr
  intro j
  have hj := hZ j (mem_univ j)
  change ‖Z j‖ ≤ R + 4
  rw [Real.norm_eq_abs, abs_of_nonneg hj.1]
  linarith [hj.2]

theorem zero_mem_admissiblePoles_rectangle {R : ℝ} (hR : 1 ≤ R) :
    (0 : PlanarSpace) ∈ admissiblePoles closedDoubleRectangle R := by
  intro Z hZ
  change ‖WithLp.ofLp (Z - 0)‖ ≤ R + 4
  rw [sub_zero]
  apply (pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ R + 4)).mpr
  intro j
  have hj := hZ j (mem_univ j)
  have hw : doubleRectangleWidth j ≤ 2 := by
    unfold doubleRectangleWidth
    split_ifs <;> norm_num
  change ‖Z j‖ ≤ R + 4
  rw [Real.norm_eq_abs, abs_of_nonneg hj.1]
  linarith [hj.2]

theorem admissiblePoles_square_nonempty {R : ℝ} (hR : 1 ≤ R) :
    (admissiblePoles closedUnitSquare R).Nonempty :=
  ⟨0, zero_mem_admissiblePoles_square hR⟩

theorem admissiblePoles_rectangle_nonempty {R : ℝ} (hR : 1 ≤ R) :
    (admissiblePoles closedDoubleRectangle R).Nonempty :=
  ⟨0, zero_mem_admissiblePoles_rectangle hR⟩

/-- The logarithm is totalized at the pole; that singleton is null for
both reference measures and every volume-dominated measure used below. -/
def poleLog (Y Z : PlanarSpace) : ℝ := Real.log ‖Z - Y‖

theorem measurable_poleLog (Y : PlanarSpace) : Measurable (poleLog Y) :=
  (measurable_id.sub measurable_const).norm.log

@[simp] theorem poleLog_at_pole (Y : PlanarSpace) : poleLog Y Y = 0 := by
  simp [poleLog]

theorem ae_ne_pole {μ : Measure PlanarSpace} (hμ : μ ≤ volume) (Y : PlanarSpace) :
    ∀ᵐ Z ∂μ, Z ≠ Y :=
  hμ.absolutelyContinuous.ae_le ((volume : Measure PlanarSpace).ae_ne Y)

theorem ae_norm_sub_pos {μ : Measure PlanarSpace} (hμ : μ ≤ volume) (Y : PlanarSpace) :
    ∀ᵐ Z ∂μ, 0 < ‖Z - Y‖ := by
  filter_upwards [ae_ne_pole hμ Y] with Z hZ
  exact norm_pos_iff.mpr (sub_ne_zero.mpr hZ)

/-- Arbitrary choices at the pole represent the same a.e. function. -/
theorem poleLog_ae_eq_of_eq_off_pole {μ : Measure PlanarSpace}
    (hμ : μ ≤ volume) (Y : PlanarSpace) {f : PlanarSpace → ℝ}
    (hf : ∀ Z, Z ≠ Y → f Z = poleLog Y Z) : f =ᵐ[μ] poleLog Y := by
  filter_upwards [ae_ne_pole hμ Y] with Z hZ
  exact hf Z hZ

theorem poleLog_change_at_pole_ae {μ : Measure PlanarSpace}
    (hμ : μ ≤ volume) (Y : PlanarSpace) (c : ℝ) :
    (fun Z ↦ if Z = Y then c else poleLog Y Z) =ᵐ[μ] poleLog Y := by
  classical
  apply poleLog_ae_eq_of_eq_off_pole hμ Y
  intro Z hZ
  simp only [hZ, ite_false]

/-- Elementary near/far bound. It holds even at `r = 0` for Mathlib's
totalized real logarithm and power, so no spurious positive-distance
hypothesis is needed for domination. -/
theorem abs_log_rpow_le {r D : ℝ} (hr : 0 ≤ r) (hD : 1 ≤ D) (hrD : r ≤ D) :
    |Real.log r| ^ (4 / 3 : ℝ) ≤
      r ^ (-(4 / 3 : ℝ)) + (Real.log D) ^ (4 / 3 : ℝ) := by
  by_cases hr1 : r ≤ 1
  · have hlog : |Real.log r| ≤ r⁻¹ := by
      rw [abs_of_nonpos (Real.log_nonpos hr hr1)]
      linarith [Real.neg_inv_le_log hr]
    calc
      _ ≤ (r⁻¹) ^ (4 / 3 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg _) hlog (by norm_num)
      _ = r ^ (-(4 / 3 : ℝ)) := (Real.rpow_neg_eq_inv_rpow r (4 / 3)).symm
      _ ≤ _ := le_add_of_nonneg_right
        (Real.rpow_nonneg (Real.log_nonneg hD) _)
  · have hr1' : 1 ≤ r := (lt_of_not_ge hr1).le
    have hlog : |Real.log r| ≤ Real.log D := by
      rw [abs_of_nonneg (Real.log_nonneg hr1')]
      exact Real.log_le_log (lt_of_lt_of_le zero_lt_one hr1') hrD
    calc
      _ ≤ (Real.log D) ^ (4 / 3 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg _) hlog (by norm_num)
      _ ≤ _ := le_add_of_nonneg_left (Real.rpow_nonneg hr _)

/-- The exact real expression used inside each source supremum. -/
def poleLogMoment (μ : Measure PlanarSpace) (Y : PlanarSpace) : ℝ :=
  (∫ Z, |poleLog Y Z| ^ (4 / 3 : ℝ) ∂μ) ^ (3 / 4 : ℝ)

theorem square_poleLogMoment_eq_halfOpen_integral (Y : PlanarSpace) :
    poleLogMoment squareLebesgue Y =
      (∫ Z in halfOpenSquare, |poleLog Y Z| ^ (4 / 3 : ℝ) ∂squareLebesgue) ^ (3 / 4 : ℝ) := by
  simp only [poleLogMoment, Measure.restrict_eq_self_of_ae_mem ae_mem_halfOpenSquare]

theorem rectangle_poleLogMoment_eq_halfOpen_integral (Y : PlanarSpace) :
    poleLogMoment rectangleLebesgue Y =
      (∫ Z in halfOpenRectangle, |poleLog Y Z| ^ (4 / 3 : ℝ) ∂rectangleLebesgue) ^ (3 / 4 : ℝ) := by
  simp only [poleLogMoment, Measure.restrict_eq_self_of_ae_mem ae_mem_halfOpenRectangle]

theorem poleLogMoment_nonneg (μ : Measure PlanarSpace) (Y : PlanarSpace) :
    0 ≤ poleLogMoment μ Y :=
  Real.rpow_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _) _

theorem lpNorm_poleLog_eq_moment (μ : Measure PlanarSpace) (Y : PlanarSpace) :
    lpNorm (poleLog Y) (ENNReal.ofReal (4 / 3 : ℝ)) μ = poleLogMoment μ Y := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by simp)
    (measurable_poleLog Y).aestronglyMeasurable]
  norm_num [poleLogMoment, Real.norm_eq_abs]

/-- Integrability is proved by domination before the finite integral bound.
The sole analytic input is the already proved singular power moment with
exponent `4/3`, whose radial integral contributes `3*pi`. -/
theorem poleLog_integrable_moment_and_bound {μ : Measure PlanarSpace}
    [IsProbabilityMeasure μ] (hμ : μ ≤ volume) (Y : PlanarSpace)
    {D : ℝ} (hD : 1 ≤ D) (hd : ∀ᵐ Z ∂μ, ‖Z - Y‖ ≤ D) :
    Integrable (fun Z ↦ |poleLog Y Z| ^ (4 / 3 : ℝ)) μ ∧
      (∫ Z, |poleLog Y Z| ^ (4 / 3 : ℝ) ∂μ) ≤
        1 + 3 * Real.pi + (Real.log D) ^ (4 / 3 : ℝ) := by
  obtain ⟨hi, hb⟩ := inverseDistancePower_integrable_and_integral_le hμ Y
    (u := 4 / 3) (by norm_num) (by norm_num)
  have hb' : (∫ Z, inverseDistancePower Y (4 / 3) Z ∂μ) ≤ 1 + 3 * Real.pi := by
    calc
      _ ≤ 1 + 2 * Real.pi / (2 - (4 / 3 : ℝ)) := hb
      _ = _ := by ring
  have hdom : ∀ᵐ Z ∂μ, |poleLog Y Z| ^ (4 / 3 : ℝ) ≤
      inverseDistancePower Y (4 / 3) Z + (Real.log D) ^ (4 / 3 : ℝ) := by
    filter_upwards [hd] with Z hZ
    exact abs_log_rpow_le (norm_nonneg _) hD hZ
  have hmajor : Integrable
      (fun Z ↦ inverseDistancePower Y (4 / 3) Z + (Real.log D) ^ (4 / 3 : ℝ)) μ :=
    hi.add (integrable_const _)
  have hint : Integrable (fun Z ↦ |poleLog Y Z| ^ (4 / 3 : ℝ)) μ := by
    apply hmajor.mono'
      (((continuous_abs.measurable.comp (measurable_poleLog Y)).pow_const (4 / 3 : ℝ)).aestronglyMeasurable)
    filter_upwards [hdom] with Z hZ
    simp only [Function.comp_def]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact hZ
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ Z, inverseDistancePower Y (4 / 3) Z + (Real.log D) ^ (4 / 3 : ℝ) ∂μ :=
      integral_mono_ae hint hmajor hdom
    _ = (∫ Z, inverseDistancePower Y (4 / 3) Z ∂μ) +
        (Real.log D) ^ (4 / 3 : ℝ) := by
      rw [integral_add hi (integrable_const _)]
      simp
    _ ≤ _ := add_le_add hb' le_rfl

theorem poleLog_memLp {μ : Measure PlanarSpace} [IsProbabilityMeasure μ]
    (hμ : μ ≤ volume) (Y : PlanarSpace) {D : ℝ} (hD : 1 ≤ D)
    (hd : ∀ᵐ Z ∂μ, ‖Z - Y‖ ≤ D) :
    MemLp (poleLog Y) (ENNReal.ofReal (4 / 3 : ℝ)) μ := by
  apply (integrable_norm_rpow_iff (measurable_poleLog Y).aestronglyMeasurable
    (by norm_num : ENNReal.ofReal (4 / 3 : ℝ) ≠ 0) (by simp)).mp
  simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4 / 3),
    Real.norm_eq_abs] using (poleLog_integrable_moment_and_bound hμ Y hD hd).1

/-- Finite-Lp membership is independent of the value assigned at the pole.
The function need not satisfy any pointwise condition there. -/
theorem poleLog_memLp_of_eq_off_pole {μ : Measure PlanarSpace} [IsProbabilityMeasure μ]
    (hμ : μ ≤ volume) (Y : PlanarSpace) {D : ℝ} (hD : 1 ≤ D)
    (hd : ∀ᵐ Z ∂μ, ‖Z - Y‖ ≤ D) {f : PlanarSpace → ℝ}
    (hf : ∀ Z, Z ≠ Y → f Z = poleLog Y Z) :
    MemLp f (ENNReal.ofReal (4 / 3 : ℝ)) μ :=
  (memLp_congr_ae (poleLog_ae_eq_of_eq_off_pole hμ Y hf)).mpr
    (poleLog_memLp hμ Y hD hd)

theorem poleLogMoment_le {μ : Measure PlanarSpace} [IsProbabilityMeasure μ]
    (hμ : μ ≤ volume) (Y : PlanarSpace) {D : ℝ} (hD : 1 ≤ D)
    (hd : ∀ᵐ Z ∂μ, ‖Z - Y‖ ≤ D) :
    poleLogMoment μ Y ≤
      (1 + 3 * Real.pi + (Real.log D) ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
  exact Real.rpow_le_rpow
    (integral_nonneg fun Z ↦ Real.rpow_nonneg (abs_nonneg (poleLog Y Z)) _)
    (poleLog_integrable_moment_and_bound hμ Y hD hd).2 (by norm_num)

/-- One explicit bound for both suprema. Only `R` occurs in it. -/
def uniformLogBound (R : ℝ) : ℝ :=
  (1 + 3 * Real.pi + (Real.log (2 * (R + 4))) ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ)

theorem uniformLogBound_nonneg {R : ℝ} (hR : 1 ≤ R) : 0 ≤ uniformLogBound R := by
  apply Real.rpow_nonneg
  have hD : 1 ≤ 2 * (R + 4) := by linarith
  have ht := Real.rpow_nonneg (Real.log_nonneg hD) (4 / 3 : ℝ)
  have hp := Real.pi_nonneg
  linarith

theorem ae_distance_le_of_admissible {μ : Measure PlanarSpace} {B : Set PlanarSpace}
    (hB : ∀ᵐ Z ∂μ, Z ∈ B) {R : ℝ} (hR : 1 ≤ R) {Y : PlanarSpace}
    (hY : Y ∈ admissiblePoles B R) : ∀ᵐ Z ∂μ, ‖Z - Y‖ ≤ 2 * (R + 4) := by
  filter_upwards [hB] with Z hZ
  exact euclidean_norm_le_two_mul (by linarith) (hY Z hZ)

theorem ae_mem_closed_square : ∀ᵐ Z ∂squareLebesgue, Z ∈ closedUnitSquare :=
  ae_restrict_mem measurableSet_closedUnitSquare

theorem ae_mem_closed_rectangle : ∀ᵐ Z ∂rectangleLebesgue, Z ∈ closedDoubleRectangle :=
  ae_mem_openDoubleRectangle.mono fun _ hZ j hj ↦ ⟨(hZ j hj).1.le, (hZ j hj).2.le⟩

theorem square_poleLog_memLp {R : ℝ} (hR : 1 ≤ R) {Y : PlanarSpace}
    (hY : Y ∈ admissiblePoles closedUnitSquare R) :
    MemLp (poleLog Y) (ENNReal.ofReal (4 / 3 : ℝ)) squareLebesgue :=
  poleLog_memLp squareLebesgue_le_volume Y (by linarith : 1 ≤ 2 * (R + 4))
    (ae_distance_le_of_admissible ae_mem_closed_square hR hY)

theorem rectangle_poleLog_memLp {R : ℝ} (hR : 1 ≤ R) {Y : PlanarSpace}
    (hY : Y ∈ admissiblePoles closedDoubleRectangle R) :
    MemLp (poleLog Y) (ENNReal.ofReal (4 / 3 : ℝ)) rectangleLebesgue :=
  poleLog_memLp rectangleLebesgue_le_volume Y (by linarith : 1 ≤ 2 * (R + 4))
    (ae_distance_le_of_admissible ae_mem_closed_rectangle hR hY)

theorem square_poleLogMoment_le {R : ℝ} (hR : 1 ≤ R) {Y : PlanarSpace}
    (hY : Y ∈ admissiblePoles closedUnitSquare R) :
    poleLogMoment squareLebesgue Y ≤ uniformLogBound R :=
  poleLogMoment_le squareLebesgue_le_volume Y (by linarith : 1 ≤ 2 * (R + 4))
    (ae_distance_le_of_admissible ae_mem_closed_square hR hY)

theorem rectangle_poleLogMoment_le {R : ℝ} (hR : 1 ≤ R) {Y : PlanarSpace}
    (hY : Y ∈ admissiblePoles closedDoubleRectangle R) :
    poleLogMoment rectangleLebesgue Y ≤ uniformLogBound R :=
  poleLogMoment_le rectangleLebesgue_le_volume Y (by linarith : 1 ≤ 2 * (R + 4))
    (ae_distance_le_of_admissible ae_mem_closed_rectangle hR hY)

/-- The set whose real supremum appears in the source. -/
def logarithmicMomentValues (B : Set PlanarSpace) (μ : Measure PlanarSpace) (R : ℝ) : Set ℝ :=
  poleLogMoment μ '' admissiblePoles B R

theorem square_logarithmicMomentValues_nonempty {R : ℝ} (hR : 1 ≤ R) :
    (logarithmicMomentValues closedUnitSquare squareLebesgue R).Nonempty :=
  ⟨poleLogMoment squareLebesgue 0, 0, zero_mem_admissiblePoles_square hR, rfl⟩

theorem rectangle_logarithmicMomentValues_nonempty {R : ℝ} (hR : 1 ≤ R) :
    (logarithmicMomentValues closedDoubleRectangle rectangleLebesgue R).Nonempty :=
  ⟨poleLogMoment rectangleLebesgue 0, 0, zero_mem_admissiblePoles_rectangle hR, rfl⟩

theorem square_logarithmicMomentValues_le {R : ℝ} (hR : 1 ≤ R) {v : ℝ}
    (hv : v ∈ logarithmicMomentValues closedUnitSquare squareLebesgue R) :
    v ≤ uniformLogBound R := by
  obtain ⟨Y, hY, rfl⟩ := hv
  exact square_poleLogMoment_le hR hY

theorem rectangle_logarithmicMomentValues_le {R : ℝ} (hR : 1 ≤ R) {v : ℝ}
    (hv : v ∈ logarithmicMomentValues closedDoubleRectangle rectangleLebesgue R) :
    v ≤ uniformLogBound R := by
  obtain ⟨Y, hY, rfl⟩ := hv
  exact rectangle_poleLogMoment_le hR hY

theorem square_logarithmicMomentValues_bddAbove {R : ℝ} (hR : 1 ≤ R) :
    BddAbove (logarithmicMomentValues closedUnitSquare squareLebesgue R) :=
  ⟨uniformLogBound R, fun _ hv ↦ square_logarithmicMomentValues_le hR hv⟩

theorem rectangle_logarithmicMomentValues_bddAbove {R : ℝ} (hR : 1 ≤ R) :
    BddAbove (logarithmicMomentValues closedDoubleRectangle rectangleLebesgue R) :=
  ⟨uniformLogBound R, fun _ hv ↦ rectangle_logarithmicMomentValues_le hR hv⟩

/-- The actual maximum of the source's two suprema, not an arbitrary
larger choice of constant. Nonemptiness and boundedness are proved above. -/
def lambdaStar (R : ℝ) : ℝ :=
  max (sSup (logarithmicMomentValues closedUnitSquare squareLebesgue R))
    (sSup (logarithmicMomentValues closedDoubleRectangle rectangleLebesgue R))

theorem lambdaStar_le_uniformLogBound {R : ℝ} (hR : 1 ≤ R) :
    lambdaStar R ≤ uniformLogBound R := by
  apply max_le
  · exact csSup_le (square_logarithmicMomentValues_nonempty hR)
      (fun _ hv ↦ square_logarithmicMomentValues_le hR hv)
  · exact csSup_le (rectangle_logarithmicMomentValues_nonempty hR)
      (fun _ hv ↦ rectangle_logarithmicMomentValues_le hR hv)

theorem square_poleLogMoment_le_lambdaStar {R : ℝ} (hR : 1 ≤ R) {Y : PlanarSpace}
    (hY : Y ∈ admissiblePoles closedUnitSquare R) :
    poleLogMoment squareLebesgue Y ≤ lambdaStar R := by
  exact (le_csSup (square_logarithmicMomentValues_bddAbove hR) ⟨Y, hY, rfl⟩).trans
    (le_max_left _ _)

theorem rectangle_poleLogMoment_le_lambdaStar {R : ℝ} (hR : 1 ≤ R) {Y : PlanarSpace}
    (hY : Y ∈ admissiblePoles closedDoubleRectangle R) :
    poleLogMoment rectangleLebesgue Y ≤ lambdaStar R := by
  exact (le_csSup (rectangle_logarithmicMomentValues_bddAbove hR) ⟨Y, hY, rfl⟩).trans
    (le_max_right _ _)

theorem lambdaStar_nonneg {R : ℝ} (hR : 1 ≤ R) : 0 ≤ lambdaStar R :=
  (poleLogMoment_nonneg squareLebesgue 0).trans
    (square_poleLogMoment_le_lambdaStar hR (zero_mem_admissiblePoles_square hR))

/-- Both the genuine finite-Lp gate and the bound by the exact supremum
are conclusions. No integrability or uniform logarithmic bound is assumed. -/
theorem square_poleLog_bound {R : ℝ} (hR : 1 ≤ R) {Y : PlanarSpace}
    (hY : Y ∈ admissiblePoles closedUnitSquare R) :
    MemLp (poleLog Y) (ENNReal.ofReal (4 / 3 : ℝ)) squareLebesgue ∧
      lpNorm (poleLog Y) (ENNReal.ofReal (4 / 3 : ℝ)) squareLebesgue ≤ lambdaStar R := by
  refine ⟨square_poleLog_memLp hR hY, ?_⟩
  rw [lpNorm_poleLog_eq_moment]
  exact square_poleLogMoment_le_lambdaStar hR hY

theorem rectangle_poleLog_bound {R : ℝ} (hR : 1 ≤ R) {Y : PlanarSpace}
    (hY : Y ∈ admissiblePoles closedDoubleRectangle R) :
    MemLp (poleLog Y) (ENNReal.ofReal (4 / 3 : ℝ)) rectangleLebesgue ∧
      lpNorm (poleLog Y) (ENNReal.ofReal (4 / 3 : ℝ)) rectangleLebesgue ≤ lambdaStar R := by
  refine ⟨rectangle_poleLog_memLp hR hY, ?_⟩
  rw [lpNorm_poleLog_eq_moment]
  exact rectangle_poleLogMoment_le_lambdaStar hR hY

theorem square_eLpNorm_poleLog_le {R : ℝ} (hR : 1 ≤ R) {Y : PlanarSpace}
    (hY : Y ∈ admissiblePoles closedUnitSquare R) :
    eLpNorm (poleLog Y) (ENNReal.ofReal (4 / 3 : ℝ)) squareLebesgue ≤
      ENNReal.ofReal (lambdaStar R) := by
  obtain ⟨hm, hb⟩ := square_poleLog_bound hR hY
  rw [← ofReal_lpNorm hm]
  exact ENNReal.ofReal_le_ofReal hb

theorem rectangle_eLpNorm_poleLog_le {R : ℝ} (hR : 1 ≤ R) {Y : PlanarSpace}
    (hY : Y ∈ admissiblePoles closedDoubleRectangle R) :
    eLpNorm (poleLog Y) (ENNReal.ofReal (4 / 3 : ℝ)) rectangleLebesgue ≤
      ENNReal.ofReal (lambdaStar R) := by
  obtain ⟨hm, hb⟩ := rectangle_poleLog_bound hR hY
  rw [← ofReal_lpNorm hm]
  exact ENNReal.ofReal_le_ofReal hb

end PoleLogMoments
end PeriodicAttractiveLogGas
