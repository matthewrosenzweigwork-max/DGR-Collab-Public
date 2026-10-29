import LeanResearch.PeriodicAttractiveLogGas.SmoothClipping
import LeanResearch.PeriodicAttractiveLogGas.LabelOccupations
import LeanResearch.PeriodicAttractiveLogGas.ConfigurationMetric
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-! SOURCE_ONLY development of the actual smooth mesh occupations in source
Lemma `lem:smooth-occupations`. The one-dimensional profile below is a
probability smoothing of an explicit 3-Lipschitz trapezoid. This differs from
the source's interval-indicator smoothing only in the choice of profile; the
plateau, support, range and numerical derivative bounds are the same.

No cutoff, overlap, count, or gradient conclusion is an assumed structure
field. This source has not been elaborated by its author. The development
note records the precise scope and any remaining construction obligations.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped BigOperators Topology ContDiff NNReal Convolution

namespace PeriodicAttractiveLogGas.SmoothOccupations

open MeshCells MeshAdjacentCells MeshNearbyGeometry LabelOccupations

def trapezoid (x : ℝ) : ℝ :=
  min (normalClip (3 * x + 5 / 4)) (normalClip (17 / 4 - 3 * x))

theorem trapezoid_nonneg (x : ℝ) : 0 ≤ trapezoid x :=
  le_min (normalClip_nonneg _) (normalClip_nonneg _)

theorem trapezoid_le_one (x : ℝ) : trapezoid x ≤ 1 :=
  (min_le_left _ _).trans (normalClip_le_one _)

theorem trapezoid_eq_one {x : ℝ} (hx : x ∈ Icc (-(1 / 12 : ℝ)) (13 / 12)) :
    trapezoid x = 1 := by
  have hl : 1 ≤ 3 * x + 5 / 4 := by linarith [hx.1]
  have hr : 1 ≤ 17 / 4 - 3 * x := by linarith [hx.2]
  simp only [trapezoid, normalClip, max_eq_right (zero_le_one.trans hl),
    max_eq_right (zero_le_one.trans hr), min_eq_left hl, min_eq_left hr, min_self]

theorem trapezoid_eq_zero_left {x : ℝ} (hx : x ≤ -(5 / 12 : ℝ)) :
    trapezoid x = 0 := by
  have h : 3 * x + 5 / 4 ≤ 0 := by linarith
  simp only [trapezoid, normalClip, max_eq_left h, min_eq_right zero_le_one]
  exact min_eq_left (normalClip_nonneg _)

theorem trapezoid_eq_zero_right {x : ℝ} (hx : 17 / 12 ≤ x) :
    trapezoid x = 0 := by
  have h : 17 / 4 - 3 * x ≤ 0 := by linarith
  change min (normalClip _) (normalClip _) = 0
  rw [show normalClip (17 / 4 - 3 * x) = 0 by
    simp only [normalClip, max_eq_left h, min_eq_right zero_le_one]]
  exact min_eq_right (normalClip_nonneg _)

theorem trapezoid_lipschitz : LipschitzWith 3 trapezoid := by
  have hl : LipschitzWith 3 (fun x : ℝ ↦ 3 * x + 5 / 4) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_ofNat]
    rw [show 3 * x + 5 / 4 - (3 * y + 5 / 4) = 3 * (x - y) by ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hr : LipschitzWith 3 (fun x : ℝ ↦ 17 / 4 - 3 * x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_ofNat]
    rw [show 17 / 4 - 3 * x - (17 / 4 - 3 * y) = -(3 * (x - y)) by ring,
      abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  simpa only [trapezoid, one_mul, max_self, Function.comp_def] using!
    (normalClip_lipschitz.comp hl).min (normalClip_lipschitz.comp hr)

/-- A concrete, already normalized, smooth probability kernel. -/
def profileKernel : ℝ → ℝ := mollifierDilate clippingKernel (1 / 12)

theorem profileKernel_nonneg (x : ℝ) : 0 ≤ profileKernel x :=
  mollifierDilate_nonneg clippingKernel_nonneg (by norm_num) x

theorem profileKernel_smooth : ContDiff ℝ ∞ profileKernel :=
  contDiff_mollifierDilate contDiff_clippingKernel _

theorem profileKernel_compact : HasCompactSupport profileKernel :=
  hasCompactSupport_mollifierDilate hasCompactSupport_clippingKernel (by norm_num)

theorem profileKernel_integrable : Integrable profileKernel volume :=
  profileKernel_smooth.continuous.integrable_of_hasCompactSupport profileKernel_compact

theorem integral_profileKernel : (∫ x : ℝ, profileKernel x) = 1 := by
  rw [profileKernel, integral_mollifierDilate volume (by norm_num : (0 : ℝ) < 1 / 12),
    integral_clippingKernel]

theorem profileKernel_support {x : ℝ} (hx : profileKernel x ≠ 0) : |x| ≤ 1 / 12 := by
  have h := tsupport_mollifierDilate_subset
    (by norm_num : (0 : ℝ) < 1 / 12) tsupport_clippingKernel_subset
    (subset_tsupport profileKernel hx)
  simpa only [mul_one, mem_closedBall_zero_iff, Real.norm_eq_abs] using h

def profile : ℝ → ℝ :=
  profileKernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] trapezoid

theorem profile_smooth : ContDiff ℝ ∞ profile :=
  contDiff_mollifierDilate_convolution volume hasCompactSupport_clippingKernel
    contDiff_clippingKernel trapezoid_lipschitz.continuous (by norm_num)

theorem profile_integrand_integrable (x : ℝ) :
    Integrable (fun t ↦ profileKernel t * trapezoid (x - t)) volume :=
  profileKernel_compact.convolutionExists_left_of_continuous_right
    (ContinuousLinearMap.lsmul ℝ ℝ) profileKernel_integrable.locallyIntegrable
    trapezoid_lipschitz.continuous x

theorem profile_nonneg (x : ℝ) : 0 ≤ profile x := by
  change 0 ≤ ∫ t, profileKernel t * trapezoid (x - t)
  exact integral_nonneg fun t ↦ mul_nonneg (profileKernel_nonneg t) (trapezoid_nonneg _)

theorem profile_le_one (x : ℝ) : profile x ≤ 1 := by
  rw [← integral_profileKernel]
  apply integral_mono (profile_integrand_integrable x) profileKernel_integrable
  intro t
  exact mul_le_of_le_one_right (profileKernel_nonneg t) (trapezoid_le_one _)

theorem profile_eq_one {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : profile x = 1 := by
  change (∫ t, profileKernel t * trapezoid (x - t)) = 1
  rw [← integral_profileKernel]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : profileKernel t = 0
  · simp only [ht, zero_mul]
  · have htb := abs_le.mp (profileKernel_support ht)
    rw [trapezoid_eq_one (show x - t ∈ Icc (-(1 / 12 : ℝ)) (13 / 12) by
      constructor <;> linarith [hx.1, hx.2, htb.1, htb.2]), mul_one]

theorem profile_eq_zero_left {x : ℝ} (hx : x ≤ -(1 / 2 : ℝ)) : profile x = 0 := by
  change (∫ t, profileKernel t * trapezoid (x - t)) = 0
  apply integral_eq_zero_of_ae
  filter_upwards with t
  change profileKernel t * trapezoid (x - t) = 0
  by_cases ht : profileKernel t = 0
  · simp only [ht, zero_mul]
  · have htb := (abs_le.mp (profileKernel_support ht)).1
    rw [trapezoid_eq_zero_left (by linarith : x - t ≤ -(5 / 12 : ℝ)), mul_zero]

theorem profile_eq_zero_right {x : ℝ} (hx : 3 / 2 ≤ x) : profile x = 0 := by
  change (∫ t, profileKernel t * trapezoid (x - t)) = 0
  apply integral_eq_zero_of_ae
  filter_upwards with t
  change profileKernel t * trapezoid (x - t) = 0
  by_cases ht : profileKernel t = 0
  · simp only [ht, zero_mul]
  · have htb := (abs_le.mp (profileKernel_support ht)).2
    rw [trapezoid_eq_zero_right (by linarith : 17 / 12 ≤ x - t), mul_zero]

theorem profile_support {x : ℝ} (hx : profile x ≠ 0) :
    x ∈ Ioo (-(1 / 2 : ℝ)) (3 / 2) := by
  constructor
  · exact lt_of_not_ge fun h ↦ hx (profile_eq_zero_left h)
  · exact lt_of_not_ge fun h ↦ hx (profile_eq_zero_right h)

theorem profile_lipschitz : LipschitzWith 3 profile :=
  lipschitzWith_probability_convolution profileKernel_compact profileKernel_integrable
    profileKernel_nonneg integral_profileKernel trapezoid_lipschitz

theorem profile_deriv_bound (x : ℝ) : |deriv profile x| ≤ 3 := by
  simpa only [Real.norm_eq_abs, NNReal.coe_ofNat] using
    norm_deriv_le_of_lipschitz profile_lipschitz (x₀ := x)

/-- The unperiodized tensor product for the actual index `a`. -/
def planarCutoff (J : ℕ) (a : MeshIndex J) (x : PlanarSpace) : ℝ :=
  profile ((J : ℝ) * x 0 - a 0) * profile ((J : ℝ) * x 1 - a 1)

theorem planarCutoff_nonneg (J : ℕ) (a : MeshIndex J) (x : PlanarSpace) :
    0 ≤ planarCutoff J a x := mul_nonneg (profile_nonneg _) (profile_nonneg _)

theorem planarCutoff_le_one (J : ℕ) (a : MeshIndex J) (x : PlanarSpace) :
    planarCutoff J a x ≤ 1 := by
  exact (mul_le_mul (profile_le_one _) (profile_le_one _)
    (profile_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem planarCutoff_smooth (J : ℕ) (a : MeshIndex J) :
    ContDiff ℝ ∞ (planarCutoff J a) := by
  apply ContDiff.mul
  · exact profile_smooth.comp
      ((contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff).sub contDiff_const)
  · exact profile_smooth.comp
      ((contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff).sub contDiff_const)

theorem planarCutoff_support {J : ℕ} {a : MeshIndex J} {x : PlanarSpace}
    (hx : planarCutoff J a x ≠ 0) (j : Fin 2) :
    -(1 / 2 : ℝ) < (J : ℝ) * x j - a j ∧ (J : ℝ) * x j - a j < 3 / 2 := by
  have h0 : profile ((J : ℝ) * x 0 - a 0) ≠ 0 :=
    left_ne_zero_of_mul hx
  have h1 : profile ((J : ℝ) * x 1 - a 1) ≠ 0 :=
    right_ne_zero_of_mul hx
  fin_cases j
  · exact profile_support h0
  · exact profile_support h1

/-- The actual physical center of the prescribed cell. -/
def centerLift (J : ℕ) (a : MeshIndex J) : PlanarSpace :=
  WithLp.toLp 2 (fun j ↦ ((a j : ℝ) + 1 / 2) / J)

def cellCenter (J : ℕ) (a : MeshIndex J) : Torus := torusQuotient (centerLift J a)

theorem planarCutoff_tsupport_coordinates {J : ℕ} {a : MeshIndex J}
    {x : PlanarSpace} (hx : x ∈ tsupport (planarCutoff J a)) (j : Fin 2) :
    |(J : ℝ) * x j - a j - 1 / 2| ≤ 1 := by
  have hs : tsupport (planarCutoff J a) ⊆
      {y | |(J : ℝ) * y j - a j - 1 / 2| ≤ 1} := by
    apply closure_minimal
    · intro y hy
      obtain ⟨hl, hu⟩ := planarCutoff_support hy j
      change |(J : ℝ) * y j - a j - 1 / 2| ≤ 1
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · exact isClosed_le
        (((continuous_const.mul (EuclideanSpace.proj (𝕜 := ℝ) j).continuous).sub
          continuous_const).sub continuous_const).abs continuous_const
  exact hs hx

theorem planarCutoff_compact (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    HasCompactSupport (planarCutoff J a) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  apply (isCompact_closedBall (centerLift J a) (2 / J)).of_isClosed_subset
    (isClosed_tsupport _)
  intro x hx
  rw [mem_closedBall, dist_eq_norm]
  have hc (j : Fin 2) : |(x - centerLift J a) j| ≤ 1 / J := by
    have hj := planarCutoff_tsupport_coordinates hx j
    have he : (x - centerLift J a) j =
        ((J : ℝ) * x j - a j - 1 / 2) / J := by
      change x j - ((a j : ℝ) + 1 / 2) / J = _
      field_simp [hJr.ne']
      ring
    rw [he, abs_div, abs_of_pos hJr]
    exact div_le_div_of_nonneg_right hj hJr.le
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2 / J)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have h0 := pow_le_pow_left₀ (abs_nonneg _) (hc 0) 2
  have h1 := pow_le_pow_left₀ (abs_nonneg _) (hc 1) 2
  simp only [sq_abs] at h0 h1
  rw [show ((2 : ℝ) / J) ^ 2 = 4 * ((1 : ℝ) / J) ^ 2 by ring]
  nlinarith [sq_nonneg ((1 : ℝ) / J)]

theorem planarCutoff_tsupport_box (J : ℕ) (hJ : 3 ≤ J) (a : MeshIndex J) :
    tsupport (planarCutoff J a) ⊆
      euclideanFundamentalBox (centeredBoxAnchor (centerLift J a)) := by
  have hJr : (3 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJp : (0 : ℝ) < J := by linarith
  intro x hx j _
  obtain ⟨hl, hu⟩ := abs_le.mp (planarCutoff_tsupport_coordinates hx j)
  change ((a j : ℝ) + 1 / 2) / J - 1 / 2 < x j ∧
    x j ≤ ((a j : ℝ) + 1 / 2) / J - 1 / 2 + 1
  constructor
  · apply (mul_lt_mul_iff_of_pos_right hJp).mp
    rw [sub_mul, div_mul_cancel₀ _ hJp.ne']
    nlinarith
  · apply (mul_le_mul_iff_of_pos_right hJp).mp
    rw [add_mul, sub_mul, div_mul_cancel₀ _ hJp.ne', one_mul]
    nlinarith

def cellCutoff (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) : C(Torus, ℝ) :=
  periodizedTest (planarCutoff J a) (planarCutoff_smooth J a)
    (planarCutoff_compact J hJ a)

@[simp] theorem cellCutoff_lift (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (x : PlanarSpace) :
    cellCutoff J hJ a (torusQuotient x) = periodicSum (planarCutoff J a) x :=
  periodizedTest_lift _ _ _ _

theorem cellCutoff_smooth (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    ContDiff ℝ ∞ (fun x ↦ cellCutoff J hJ a (torusQuotient x)) :=
  contDiff_lift_periodizedTest _ _ _

theorem cellCutoff_nonneg (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (z : Torus) :
    0 ≤ cellCutoff J hJ a z := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective z
  rw [cellCutoff_lift]
  exact finsum_nonneg fun k ↦ planarCutoff_nonneg J a _

/-- A global formula uses a translated centered representative, with exactly
the source cell center and physical mesh scale. -/
theorem cellCutoff_centered_formula (J : ℕ) (hJ : 3 ≤ J) (a : MeshIndex J) (z : Torus) :
    cellCutoff J (by omega) a z =
      planarCutoff J a (centerLift J a + centeredLift (z - cellCenter J a)) := by
  let x := centerLift J a + centeredLift (z - cellCenter J a)
  have hxq : torusQuotient x = z := by
    ext j
    change ((centerLift J a j + centeredLift (z - cellCenter J a) j : ℝ) : UnitAddCircle) = _
    rw [AddCircle.coe_add]
    change cellCenter J a j + torusQuotient (centeredLift (z - cellCenter J a)) j = z j
    rw [torusQuotient_centeredLift]
    change cellCenter J a j + (z j - cellCenter J a j) = z j
    abel
  have hxb : x ∈ euclideanFundamentalBox (centeredBoxAnchor (centerLift J a)) := by
    intro j _
    obtain ⟨hl, hu⟩ := centeredLift_coordinate_mem (z - cellCenter J a) j
    change centerLift J a j - 1 / 2 < centerLift J a j + centeredLift (z - cellCenter J a) j ∧
      centerLift J a j + centeredLift (z - cellCenter J a) j ≤ centerLift J a j - 1 / 2 + 1
    constructor <;> linarith
  calc
    cellCutoff J (by omega) a z = cellCutoff J (by omega) a (torusQuotient x) := by rw [hxq]
    _ = periodicSum (planarCutoff J a) x := cellCutoff_lift J (by omega) a x
    _ = planarCutoff J a x := periodicSum_eq_on_box (planarCutoff_tsupport_box J hJ a) hxb

theorem cellCutoff_le_one (J : ℕ) (hJ : 3 ≤ J) (a : MeshIndex J) (z : Torus) :
    cellCutoff J (by omega) a z ≤ 1 := by
  rw [cellCutoff_centered_formula J hJ]
  exact planarCutoff_le_one J a _

theorem cellCutoff_eq_one_on_closure (J : ℕ) (hJ : 3 ≤ J) (a : MeshIndex J)
    {z : Torus} (hz : z ∈ closure (meshCell J (by omega) a)) :
    cellCutoff J (by omega) a z = 1 := by
  rw [closure_meshCell] at hz
  obtain ⟨Z, hZ, rfl⟩ := hz
  rw [meshChart, cellCutoff_lift,
    periodicSum_eq_on_box (planarCutoff_tsupport_box J hJ a)]
  · have hJr : (J : ℝ) ≠ 0 := by exact_mod_cast (show J ≠ 0 by omega)
    have he (j : Fin 2) : (J : ℝ) * meshAffine J a Z j - a j = Z j := by
      rw [meshAffine_apply]
      field_simp [hJr]
      ring
    simp only [planarCutoff, he, profile_eq_one (hZ 0 (mem_univ _)),
      profile_eq_one (hZ 1 (mem_univ _)), mul_one]
  · intro j _
    have hJr : (3 : ℝ) ≤ J := by exact_mod_cast hJ
    have hJp : (0 : ℝ) < J := by linarith
    have hZj := hZ j (mem_univ j)
    change ((a j : ℝ) + 1 / 2) / J - 1 / 2 <
      (J : ℝ)⁻¹ * ((a j : ℝ) + Z j) ∧
      (J : ℝ)⁻¹ * ((a j : ℝ) + Z j) ≤ ((a j : ℝ) + 1 / 2) / J - 1 / 2 + 1
    rw [show (J : ℝ)⁻¹ * ((a j : ℝ) + Z j) = ((a j : ℝ) + Z j) / J by
      rw [div_eq_mul_inv, mul_comm]]
    constructor
    · apply (mul_lt_mul_iff_of_pos_right hJp).mp
      rw [sub_mul, div_mul_cancel₀ _ hJp.ne', div_mul_cancel₀ _ hJp.ne']
      nlinarith [hZj.1]
    · apply (mul_le_mul_iff_of_pos_right hJp).mp
      rw [add_mul, sub_mul, div_mul_cancel₀ _ hJp.ne', div_mul_cancel₀ _ hJp.ne', one_mul]
      nlinarith [hZj.2]

/-- Nonzero cutoffs supply actual integer translates of the half-open
representative; the witness is not an extra localization hypothesis. -/
theorem cellCutoff_support_witness (J : ℕ) (hJ : 3 ≤ J) (a : MeshIndex J)
    {z : Torus} (hz : cellCutoff J (by omega) a z ≠ 0) :
    ∃ k : Frequency, ∀ j : Fin 2,
      -(1 / 2 : ℝ) < J * unitRepresentative (z j) - a j + J * (k j : ℝ) ∧
      J * unitRepresentative (z j) - a j + J * (k j : ℝ) < 3 / 2 := by
  let x := centerLift J a + centeredLift (z - cellCenter J a)
  have hxq : torusQuotient x = z := by
    ext j
    change ((centerLift J a j + centeredLift (z - cellCenter J a) j : ℝ) : UnitAddCircle) = _
    rw [AddCircle.coe_add]
    change cellCenter J a j + torusQuotient (centeredLift (z - cellCenter J a)) j = z j
    rw [torusQuotient_centeredLift]
    change cellCenter J a j + (z j - cellCenter J a j) = z j
    abel
  have hx : planarCutoff J a x ≠ 0 := by
    simpa only [cellCutoff_centered_formula J hJ a z] using hz
  obtain ⟨k, hk⟩ := exists_frequencyVector_of_torusQuotient_eq
    ((torusQuotient_halfOpenLift z).trans hxq.symm)
  refine ⟨k, fun j ↦ ?_⟩
  have h := planarCutoff_support hx j
  rw [hk] at h
  simp only [PiLp.add_apply, halfOpenLift_apply, frequencyVector_apply] at h
  constructor <;> nlinarith [h.1, h.2]

/-- The exact source support box, expressed through an ordinary lift about
the prescribed center. This is a periodic square, including its boundary. -/
def cellSupportSquare (J : ℕ) (a : MeshIndex J) : Set Torus :=
  torusQuotient '' {x : PlanarSpace | ∀ j : Fin 2,
    |x j - centerLift J a j| ≤ 1 / J}

theorem cellSupportSquare_isClosed (J : ℕ) (a : MeshIndex J) :
    IsClosed (cellSupportSquare J a) := by
  have he : {x : PlanarSpace | ∀ j : Fin 2, |x j - centerLift J a j| ≤ 1 / J} =
      (PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)) ⁻¹'
        Set.pi Set.univ (fun j ↦ Icc (centerLift J a j - 1 / J) (centerLift J a j + 1 / J)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Icc, abs_le]
    apply forall_congr'
    intro j
    change (-(1 / (J : ℝ)) ≤ x j - centerLift J a j ∧
      x j - centerLift J a j ≤ 1 / J) ↔
      (centerLift J a j - 1 / J ≤ x j ∧ x j ≤ centerLift J a j + 1 / J)
    constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith
  have hc : IsCompact {x : PlanarSpace | ∀ j : Fin 2, |x j - centerLift J a j| ≤ 1 / J} := by
    rw [he]
    exact (PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)).isCompact_preimage.mpr
      (isCompact_univ_pi fun _ ↦ isCompact_Icc)
  exact (hc.image isOpenQuotientMap_torusQuotient.continuous).isClosed

theorem cellCutoff_support_square (J : ℕ) (hJ : 3 ≤ J) (a : MeshIndex J) :
    Function.support (cellCutoff J (by omega) a) ⊆ cellSupportSquare J a := by
  intro z hz
  obtain ⟨k, hk⟩ := cellCutoff_support_witness J hJ a hz
  refine ⟨halfOpenLift z + frequencyVector k, ?_, ?_⟩
  · intro j
    have hJr : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
    have he : (halfOpenLift z + frequencyVector k) j - centerLift J a j =
        (J * unitRepresentative (z j) - a j + J * (k j : ℝ) - 1 / 2) / J := by
      simp only [PiLp.add_apply, halfOpenLift_apply, frequencyVector_apply, centerLift]
      change unitRepresentative (z j) + (k j : ℝ) - ((a j : ℝ) + 1 / 2) / J = _
      field_simp
      ring
    rw [he, abs_div, abs_of_pos hJr]
    apply div_le_div_of_nonneg_right _ hJr.le
    exact abs_le.mpr ⟨by linarith [(hk j).1], by linarith [(hk j).2]⟩
  · rw [torusQuotient_add_frequencyVector, torusQuotient_halfOpenLift]

theorem cellCutoff_tsupport_square (J : ℕ) (hJ : 3 ≤ J) (a : MeshIndex J) :
    tsupport (cellCutoff J (by omega) a) ⊆ cellSupportSquare J a :=
  closure_minimal (cellCutoff_support_square J hJ a) (cellSupportSquare_isClosed J a)

theorem cellCutoff_tsupport_ball (J : ℕ) (hJ : 3 ≤ J) (a : MeshIndex J) :
    tsupport (cellCutoff J (by omega) a) ⊆
      {z : Torus | torusEuclideanDist z (cellCenter J a) ≤ Real.sqrt 2 / J} := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := cellCutoff_tsupport_square J hJ a hz
  apply (torusEuclideanDist_quotient_le x (centerLift J a)).trans
  rw [dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : (0 : ℝ) ≤ Real.sqrt 2 / J)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, div_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have h0 := pow_le_pow_left₀ (abs_nonneg _) (hx 0) 2
  have h1 := pow_le_pow_left₀ (abs_nonneg _) (hx 1) 2
  simp only [PiLp.sub_apply, sq_abs, div_pow, one_pow] at *
  convert add_le_add h0 h1 using 1
  ring

/-- The label selected at a seam is the actual half-open label. -/
theorem cellCutoff_support_nearby (J : ℕ) (hJ : 3 ≤ J) (a : MeshIndex J)
    {z : Torus} (hz : cellCutoff J (by omega) a z ≠ 0) :
    meshLabel J (by omega) z ∈ nearbyCells 1 a := by
  obtain ⟨k, hk⟩ := cellCutoff_support_witness J hJ a hz
  let b := meshLabel J (by omega) z
  have hb (j : Fin 2) : (b j : ℝ) ≤ J * unitRepresentative (z j) ∧
      J * unitRepresentative (z j) < (b j : ℝ) + 1 := by
    have h := (coordinateLabel_eq_iff J (by omega) (z j) (b j)).mp rfl
    have hJr : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
    constructor
    · simpa only [mul_comm] using (div_le_iff₀ hJr).mp h.1
    · simpa only [mul_comm] using (lt_div_iff₀ hJr).mp h.2
  apply (mem_nearbyCells a b).mpr
  apply (periodicIndexDistance_le_iff a b).mpr
  intro j
  have hi : ((b j : ℤ) - (a j : ℤ) + (J : ℤ) * k j).natAbs ≤ 1 := by
    have hl : (-2 : ℝ) < (b j : ℝ) - a j + J * (k j : ℝ) := by
      linarith [(hk j).1, (hb j).2]
    have hu : (b j : ℝ) - a j + J * (k j : ℝ) < 2 := by
      linarith [(hk j).2, (hb j).1]
    have hli : (-2 : ℤ) < (b j : ℤ) - a j + (J : ℤ) * k j := by exact_mod_cast hl
    have hui : (b j : ℤ) - a j + (J : ℤ) * k j < 2 := by exact_mod_cast hu
    omega
  have hmin := centeredIndexOffset_natAbs_le (show 0 < J by omega) b a k j
  have he : (centeredIndexOffset a b j).natAbs = (centeredIndexOffset b a j).natAbs := by
    unfold centeredIndexOffset
    rw [show indexClass a j - indexClass b j = -(indexClass b j - indexClass a j) by abel,
      ZMod.natAbs_valMinAbs_neg]
  rw [he]
  exact hmin.trans hi

/-- The source's nine-cell count uses the sharper symmetric window, rather
than the larger common window used for two-cell conditional estimates. -/
theorem card_nearby_one_le_nine (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    (nearbyCells 1 a).card ≤ 9 := by
  let S : Finset ℤ := Finset.Icc (-1) 1
  have hs : nearbyCells 1 a ⊆
      (S ×ˢ S).image (fun p ↦ shiftIndex J hJ a (pairFrequency p)) := by
    intro b hb
    obtain ⟨d, hd, hc⟩ := nearby_displacement hb
    refine Finset.mem_image.mpr ⟨(d 0, d 1), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hd 0),
        Finset.mem_Icc.mpr (hd 1)⟩
    · rw [pairFrequency_coordinates]
      exact shiftIndex_eq J hJ a b d hc
  calc
    _ ≤ ((S ×ˢ S).image (fun p ↦ shiftIndex J hJ a (pairFrequency p))).card :=
      Finset.card_le_card hs
    _ ≤ (S ×ˢ S).card := Finset.card_image_le
    _ = 9 := by norm_num [S, Finset.card_product, Int.card_Icc]

def overlapBase (J : ℕ) (hJ : 0 < J) (z : Torus) : MeshIndex J :=
  fun j ↦ residueIndex J hJ ⌊J * unitRepresentative (z j) + 1 / 2⌋

def activeCells (J : ℕ) (hJ : 0 < J) (z : Torus) : Finset (MeshIndex J) :=
  Finset.univ.filter fun a ↦ cellCutoff J hJ a z ≠ 0

theorem activeCells_card_le_four (J : ℕ) (hJ : 3 ≤ J) (z : Torus) :
    (activeCells J (by omega) z).card ≤ 4 := by
  let S : Finset ℤ := Finset.Icc (-1) 0
  let b := overlapBase J (by omega) z
  have hs : activeCells J (by omega) z ⊆
      (S ×ˢ S).image (fun p ↦ shiftIndex J (by omega) b (pairFrequency p)) := by
    intro a ha
    obtain ⟨k, hk⟩ := cellCutoff_support_witness J hJ a (Finset.mem_filter.mp ha).2
    let m : Frequency := fun j ↦ ⌊J * unitRepresentative (z j) + 1 / 2⌋
    let d : Frequency := fun j ↦ (a j : ℤ) - (J : ℤ) * k j - m j
    have hd (j : Fin 2) : -1 ≤ d j ∧ d j ≤ 0 := by
      have hfl := Int.floor_le (J * unitRepresentative (z j) + 1 / 2)
      have hfu := Int.lt_floor_add_one (J * unitRepresentative (z j) + 1 / 2)
      have he : (d j : ℝ) = (a j : ℝ) - J * (k j : ℝ) - m j := by
        simp only [d, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      have hl : (-2 : ℝ) < (d j : ℝ) := by
        rw [he]
        dsimp only [m]
        linarith [(hk j).2]
      have hu : (d j : ℝ) < 1 := by
        rw [he]
        dsimp only [m]
        linarith [(hk j).1]
      have hli : (-2 : ℤ) < d j := by exact_mod_cast hl
      have hui : d j < 1 := by exact_mod_cast hu
      omega
    have hc (j : Fin 2) : (d j : ZMod J) = indexClass a j - indexClass b j := by
      have hb : indexClass b j = (m j : ZMod J) :=
        residueIndex_cast J (by omega) (m j)
      rw [hb]
      simp only [d, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
        ZMod.natCast_self, zero_mul, sub_zero, indexClass]
    refine Finset.mem_image.mpr ⟨(d 0, d 1), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hd 0), Finset.mem_Icc.mpr (hd 1)⟩
    · rw [pairFrequency_coordinates]
      exact shiftIndex_eq J (by omega) b a d hc
  calc
    _ ≤ ((S ×ˢ S).image (fun p ↦ shiftIndex J (by omega) b (pairFrequency p))).card :=
      Finset.card_le_card hs
    _ ≤ (S ×ˢ S).card := Finset.card_image_le
    _ = 4 := by norm_num [S, Finset.card_product, Int.card_Icc]

theorem sum_cellCutoff_le_four (J : ℕ) (hJ : 3 ≤ J) (z : Torus) :
    ∑ a : MeshIndex J, cellCutoff J (by omega) a z ≤ 4 := by
  have he : ∑ a : MeshIndex J, cellCutoff J (by omega) a z =
      ∑ a ∈ activeCells J (by omega) z, cellCutoff J (by omega) a z := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ ha
    by_contra h
    exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  rw [he]
  calc
    _ ≤ ∑ _a ∈ activeCells J (by omega) z, (1 : ℝ) :=
      Finset.sum_le_sum fun a _ ↦ cellCutoff_le_one J hJ a z
    _ = ((activeCells J (by omega) z).card : ℝ) := by simp
    _ ≤ 4 := by exact_mod_cast activeCells_card_le_four J hJ z

/-- The actual smooth occupation fraction; particles remain labelled. -/
def occupationFraction (N J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (X : Configuration N) : ℝ := (∑ i : Fin N, cellCutoff J hJ a (X i)) / N

theorem occupationFraction_nonneg (N J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (X : Configuration N) : 0 ≤ occupationFraction N J hJ a X :=
  div_nonneg (Finset.sum_nonneg fun i _ ↦ cellCutoff_nonneg J hJ a (X i)) (Nat.cast_nonneg N)

theorem occupationFraction_continuous (N J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    Continuous (occupationFraction N J hJ a) :=
  (continuous_finsetSum Finset.univ fun i _ ↦
    (cellCutoff J hJ a).continuous.comp (continuous_apply i)).div_const _

theorem hard_occupation_le_fraction (N J : ℕ) (hJ : 3 ≤ J) (a : MeshIndex J)
    (X : Configuration N) :
    (occupation (configurationMeshLabel N J (by omega) X) a : ℝ) / N ≤
      occupationFraction N J (by omega) a X := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have he : (occupation (configurationMeshLabel N J (by omega) X) a : ℝ) =
      ∑ i : Fin N, if meshLabel J (by omega) (X i) = a then (1 : ℝ) else 0 := by
    simpa only [occupation, configurationMeshLabel] using!
      (Finset.natCast_card_filter (R := ℝ)
        (fun i : Fin N ↦ meshLabel J (by omega) (X i) = a) Finset.univ)
  rw [he]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · rw [cellCutoff_eq_one_on_closure J hJ a (subset_closure hi)]
  · exact cellCutoff_nonneg J (by omega) a (X i)

theorem fraction_le_nearby_occupations (N J : ℕ) (hJ : 3 ≤ J) (a : MeshIndex J)
    (X : Configuration N) :
    occupationFraction N J (by omega) a X ≤
      (∑ b ∈ nearbyCells 1 a,
        (occupation (configurationMeshLabel N J (by omega) X) b : ℝ)) / N := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have he : (∑ b ∈ nearbyCells 1 a,
      (occupation (configurationMeshLabel N J (by omega) X) b : ℝ)) =
      ∑ i : Fin N, if meshLabel J (by omega) (X i) ∈ nearbyCells 1 a then (1 : ℝ) else 0 := by
    have hc := sourceIndices_card_eq_sum_fibers (configurationMeshLabel N J (by omega) X)
      Finset.univ (nearbyCells 1 a)
    calc
      _ = ((sourceIndices (configurationMeshLabel N J (by omega) X)
          Finset.univ (nearbyCells 1 a)).card : ℝ) := by
        rw [hc, Nat.cast_sum]
        rfl
      _ = _ := by
        simpa only [sourceIndices, configurationMeshLabel] using!
          (Finset.natCast_card_filter (R := ℝ)
            (fun i : Fin N ↦ meshLabel J (by omega) (X i) ∈ nearbyCells 1 a) Finset.univ)
  rw [he]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · exact cellCutoff_le_one J hJ a (X i)
  · have hz : cellCutoff J (by omega) a (X i) = 0 := by
      by_contra hz
      exact hi (cellCutoff_support_nearby J hJ a hz)
    rw [hz]

theorem sum_occupationFraction_le_four (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    (X : Configuration N) : ∑ a : MeshIndex J, occupationFraction N J (by omega) a X ≤ 4 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [occupationFraction, ← Finset.sum_div]
  rw [Finset.sum_comm]
  apply (div_le_iff₀ hNr).mpr
  calc
    _ ≤ ∑ _i : Fin N, (4 : ℝ) := Finset.sum_le_sum fun i _ ↦ sum_cellCutoff_le_four J hJ (X i)
    _ = 4 * N := by simp; ring

theorem occupationFraction_le_one (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    (a : MeshIndex J) (X : Configuration N) : occupationFraction N J (by omega) a X ≤ 1 := by
  apply (div_le_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mpr
  calc
    _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ cellCutoff_le_one J hJ a (X i)
    _ = 1 * N := by simp

def heavyCenters (N J : ℕ) (hJ : 0 < J) (t : ℝ) (X : Configuration N) : Finset (MeshIndex J) :=
  Finset.univ.filter fun a ↦ t < occupationFraction N J hJ a X

/-- This finite count is independent of the number of mesh centers. -/
theorem heavyCenters_card_le (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {t : ℝ} (ht : 0 < t) (X : Configuration N) :
    ((heavyCenters N J (by omega) t X).card : ℝ) ≤ 4 / t := by
  apply (le_div_iff₀ ht).mpr
  calc
    _ = ∑ _a ∈ heavyCenters N J (by omega) t X, t := by simp
    _ ≤ ∑ a ∈ heavyCenters N J (by omega) t X, occupationFraction N J (by omega) a X :=
      Finset.sum_le_sum fun a ha ↦ (Finset.mem_filter.mp ha).2.le
    _ ≤ ∑ a : MeshIndex J, occupationFraction N J (by omega) a X :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun a _ _ ↦ occupationFraction_nonneg N J (by omega) a X)
    _ ≤ 4 := sum_occupationFraction_le_four N J hN hJ X

def maximumOccupation (N J : ℕ) (hJ : 0 < J) (X : Configuration N) : ℝ :=
  Finset.univ.sup' ⟨(fun _ ↦ ⟨0, hJ⟩), Finset.mem_univ _⟩
    (fun a ↦ occupationFraction N J hJ a X)

theorem occupationFraction_le_maximum (N J : ℕ) (hJ : 0 < J) (a : MeshIndex J)
    (X : Configuration N) : occupationFraction N J hJ a X ≤ maximumOccupation N J hJ X := by
  simpa only [maximumOccupation] using!
    (Finset.le_sup' (fun b ↦ occupationFraction N J hJ b X) (Finset.mem_univ a))

theorem maximumOccupation_le_iff (N J : ℕ) (hJ : 0 < J) (X : Configuration N) (t : ℝ) :
    maximumOccupation N J hJ X ≤ t ↔ ∀ a, occupationFraction N J hJ a X ≤ t := by
  simpa only [maximumOccupation, Finset.mem_univ, true_implies] using!
    (Finset.sup'_le_iff (s := (Finset.univ : Finset (MeshIndex J)))
      ⟨(fun _ ↦ ⟨0, hJ⟩), Finset.mem_univ _⟩ (fun a ↦ occupationFraction N J hJ a X))

theorem maximumOccupation_attained (N J : ℕ) (hJ : 0 < J) (X : Configuration N) :
    ∃ a, maximumOccupation N J hJ X = occupationFraction N J hJ a X := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.univ) (H := ⟨(fun _ ↦ ⟨0, hJ⟩), Finset.mem_univ _⟩)
    (fun a ↦ occupationFraction N J hJ a X)
  exact ⟨a, ha⟩

theorem maximumOccupation_continuous (N J : ℕ) (hJ : 0 < J) :
    Continuous (maximumOccupation N J hJ) :=
  Continuous.finset_sup'_apply _ fun a _ ↦ occupationFraction_continuous N J hJ a

theorem maximumOccupation_nonneg (N J : ℕ) (hJ : 0 < J) (X : Configuration N) :
    0 ≤ maximumOccupation N J hJ X := by
  obtain ⟨a, ha⟩ := maximumOccupation_attained N J hJ X
  rw [ha]
  exact occupationFraction_nonneg N J hJ a X

theorem maximumOccupation_le_one (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J) (X : Configuration N) :
    maximumOccupation N J (by omega) X ≤ 1 :=
  (maximumOccupation_le_iff N J (by omega) X 1).mpr
    (fun a ↦ occupationFraction_le_one N J hN hJ a X)

theorem bad_labels_subset_maximum_gt (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J) (t : ℝ) :
    {X : Configuration N | configurationMeshLabel N J (by omega) X ∉ goodLabels J N t} ⊆
      {X | t < maximumOccupation N J (by omega) X} := by
  intro X hX
  by_contra h
  apply hX
  intro a
  have ha := (hard_occupation_le_fraction N J hJ a X).trans
    ((occupationFraction_le_maximum N J (by omega) a X).trans (le_of_not_gt h))
  exact (div_le_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mp ha

theorem maximum_lt_subset_good_labels (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J) (t : ℝ) :
    {X : Configuration N | maximumOccupation N J (by omega) X < t} ⊆
      {X | configurationMeshLabel N J (by omega) X ∈ goodLabels J N t} := by
  intro X hX a
  have ha := (hard_occupation_le_fraction N J hJ a X).trans
    ((occupationFraction_le_maximum N J (by omega) a X).trans hX.le)
  exact (div_le_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mp ha

theorem maximum_gt_subset_bad_labels_ninth (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {t : ℝ} (ht : 0 ≤ t) :
    {X : Configuration N | t < maximumOccupation N J (by omega) X} ⊆
      {X | configurationMeshLabel N J (by omega) X ∉ goodLabels J N (t / 9)} := by
  intro X hX hgood
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmax : maximumOccupation N J (by omega) X ≤ t := by
    apply (maximumOccupation_le_iff N J (by omega) X t).mpr
    intro a
    apply (fraction_le_nearby_occupations N J hJ a X).trans
    apply (div_le_iff₀ hNr).mpr
    calc
      _ ≤ ∑ _b ∈ nearbyCells 1 a, t / 9 * N := Finset.sum_le_sum fun b _ ↦ hgood b
      _ = ((nearbyCells 1 a).card : ℝ) * (t / 9 * N) := by simp
      _ ≤ 9 * (t / 9 * N) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_nearby_one_le_nine J (by omega) a)
        (by positivity)
      _ = t * N := by ring
  exact (not_lt_of_ge hmax) hX

private theorem abs_product_sub_product_le {a b c d : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    |a * b - c * d| ≤ |a - c| + |b - d| := by
  calc
    _ = |(a - c) * b + c * (b - d)| := by congr 1; ring
    _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ = |a - c| * b + c * |b - d| := by rw [abs_mul, abs_mul, abs_of_nonneg hb, abs_of_nonneg hc]
    _ ≤ |a - c| * 1 + 1 * |b - d| := add_le_add
      (mul_le_mul_of_nonneg_left hb1 (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hc1 (abs_nonneg _))
    _ = _ := by ring

private theorem planar_norm_sq (v : PlanarSpace) :
    ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

private theorem planar_coordinate_sum_le (v : PlanarSpace) :
    |v 0| + |v 1| ≤ Real.sqrt 2 * ‖v‖ := by
  have hv := planar_norm_sq v
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn := norm_nonneg v
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have hc : (|v 0| + |v 1|) ^ 2 ≤ (Real.sqrt 2 * ‖v‖) ^ 2 := by
    rw [mul_pow, hs, hv]
    nlinarith [sq_nonneg (|v 0| - |v 1|), sq_abs (v 0), sq_abs (v 1)]
  nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), mul_nonneg hp hn]

def cellLipschitzConstant (J : ℕ) : ℝ≥0 := ⟨3 * Real.sqrt 2 * J, by positivity⟩

theorem cellLipschitzConstant_sq (J : ℕ) :
    (cellLipschitzConstant J : ℝ) ^ 2 = 18 * (J : ℝ) ^ 2 := by
  change (3 * Real.sqrt 2 * (J : ℝ)) ^ 2 = _
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem planarCutoff_lipschitz (J : ℕ) (a : MeshIndex J) :
    LipschitzWith (cellLipschitzConstant J) (planarCutoff J a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hc (j : Fin 2) :
      |profile ((J : ℝ) * x j - a j) - profile ((J : ℝ) * y j - a j)| ≤
        3 * J * |x j - y j| := by
    have h := profile_lipschitz.dist_le_mul ((J : ℝ) * x j - a j)
      ((J : ℝ) * y j - a j)
    simp only [Real.dist_eq, NNReal.coe_ofNat] at h
    rw [show (J : ℝ) * x j - a j - ((J : ℝ) * y j - a j) = J * (x j - y j) by ring] at h
    simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg J : (0 : ℝ) ≤ J)] at h
    simpa only [mul_assoc] using h
  rw [Real.dist_eq, dist_eq_norm]
  calc
    _ ≤ |profile ((J : ℝ) * x 0 - a 0) - profile ((J : ℝ) * y 0 - a 0)| +
        |profile ((J : ℝ) * x 1 - a 1) - profile ((J : ℝ) * y 1 - a 1)| :=
      abs_product_sub_product_le (profile_nonneg _) (profile_le_one _)
        (profile_nonneg _) (profile_le_one _)
    _ ≤ 3 * J * (|x 0 - y 0| + |x 1 - y 1|) := by nlinarith [hc 0, hc 1]
    _ ≤ 3 * J * (Real.sqrt 2 * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (planar_coordinate_sum_le (x - y)) (by positivity)
    _ = (cellLipschitzConstant J : ℝ) * ‖x - y‖ := by
      change _ = (3 * Real.sqrt 2 * J) * ‖x - y‖
      ring

private theorem planarCutoff_tsupport_openBox (J : ℕ) (hJ : 3 ≤ J) (a : MeshIndex J)
    {x : PlanarSpace} (hx : x ∈ tsupport (planarCutoff J a)) :
    x ∈ euclideanOpenBox (centeredBoxAnchor (centerLift J a)) := by
  have hJr : (3 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJp : (0 : ℝ) < J := by linarith
  intro j _
  obtain ⟨hl, hu⟩ := abs_le.mp (planarCutoff_tsupport_coordinates hx j)
  change ((a j : ℝ) + 1 / 2) / J - 1 / 2 < x j ∧
    x j < ((a j : ℝ) + 1 / 2) / J - 1 / 2 + 1
  constructor
  · apply (mul_lt_mul_iff_of_pos_right hJp).mp
    rw [sub_mul, div_mul_cancel₀ _ hJp.ne']
    nlinarith
  · apply (mul_lt_mul_iff_of_pos_right hJp).mp
    rw [add_mul, sub_mul, div_mul_cancel₀ _ hJp.ne', one_mul]
    nlinarith

/-- Disjoint periodic copies preserve the derivative constant. At a zero of
the nonnegative periodization the derivative vanishes; at a nonzero point
the local formula is one translate of the constructed planar cutoff. -/
theorem cellCutoff_lift_fderiv_bound (J : ℕ) (hJ : 3 ≤ J) (a : MeshIndex J)
    (x : PlanarSpace) :
    ‖fderiv ℝ (fun y ↦ cellCutoff J (by omega) a (torusQuotient y)) x‖ ≤
      cellLipschitzConstant J := by
  let F := periodicSum (planarCutoff J a)
  have he : (fun y ↦ cellCutoff J (by omega) a (torusQuotient y)) = F :=
    funext (cellCutoff_lift J (by omega) a)
  rw [he]
  by_cases hx : F x = 0
  · have hm : IsLocalMin F x := by
      exact Eventually.of_forall fun y ↦ by
        rw [hx]
        exact finsum_nonneg fun k ↦ planarCutoff_nonneg J a _
    rw [hm.fderiv_eq_zero, norm_zero]
    exact (cellLipschitzConstant J).coe_nonneg
  · let z := torusQuotient x
    let y := centerLift J a + centeredLift (z - cellCenter J a)
    have hyq : torusQuotient y = z := by
      ext j
      change ((centerLift J a j + centeredLift (z - cellCenter J a) j : ℝ) : UnitAddCircle) = _
      rw [AddCircle.coe_add]
      change cellCenter J a j + torusQuotient (centeredLift (z - cellCenter J a)) j = z j
      rw [torusQuotient_centeredLift]
      change cellCenter J a j + (z j - cellCenter J a j) = z j
      abel
    have hyp : planarCutoff J a y ≠ 0 := by
      have hc : cellCutoff J (by omega) a z ≠ 0 := by simpa only [z, cellCutoff_lift] using hx
      simpa only [cellCutoff_centered_formula J hJ a z] using hc
    obtain ⟨k, hk⟩ := exists_frequencyVector_of_torusQuotient_eq hyq.symm
    have hp : (fun w ↦ F (w + frequencyVector k)) = F :=
      funext fun w ↦ periodicSum_add_frequencyVector _ w k
    have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := F) (x := x) (frequencyVector k)
    rw [hp, ← hk] at hd
    have hyo := planarCutoff_tsupport_openBox J hJ a (subset_tsupport _ hyp)
    have hloc : F =ᶠ[𝓝 y] planarCutoff J a :=
      periodicSum_eventuallyEq (planarCutoff_tsupport_box J hJ a)
        (fun j ↦ (hyo j (mem_univ j)).1) (fun j ↦ (hyo j (mem_univ j)).2)
    rw [hd, hloc.fderiv_eq]
    exact norm_fderiv_le_of_lipschitz ℝ (planarCutoff_lipschitz J a)

theorem cellCutoff_lift_lipschitz (J : ℕ) (hJ : 3 ≤ J) (a : MeshIndex J) :
    LipschitzWith (cellLipschitzConstant J)
      (fun x ↦ cellCutoff J (by omega) a (torusQuotient x)) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((cellCutoff_smooth J (by omega) a).differentiable (by simp))
  intro x
  exact cellCutoff_lift_fderiv_bound J hJ a x

def particleProjection (N : ℕ) (i : Fin N) : Gradient N →L[ℝ] PlanarSpace :=
  (ContinuousLinearMap.proj i).comp (configurationRegroupEquiv N).symm.toContinuousLinearMap

@[simp] theorem particleProjection_apply (N : ℕ) (i : Fin N) (y : Gradient N) (j : Fin 2) :
    particleProjection N i y j = y (i, j) := rfl

@[simp] theorem quotient_particleProjection (N : ℕ) (i : Fin N) (y : Gradient N) :
    torusQuotient (particleProjection N i y) = configurationQuotient N y i := rfl

theorem sum_particleProjection_norm_sq (N : ℕ) (y : Gradient N) :
    ∑ i : Fin N, ‖particleProjection N i y‖ ^ 2 = ‖y‖ ^ 2 := by
  rw [gradient_norm_sq]
  apply Finset.sum_congr rfl
  intro i _
  rw [planar_norm_sq, Fin.sum_univ_two]
  rfl

theorem occupationFraction_smooth (N J : ℕ) (hJ : 0 < J) (a : MeshIndex J) :
    ContDiff ℝ ∞ (fun y : Gradient N ↦
      occupationFraction N J hJ a (configurationQuotient N y)) := by
  have h : ContDiff ℝ ∞ (fun y : Gradient N ↦
      (∑ i : Fin N, cellCutoff J hJ a (torusQuotient (particleProjection N i y))) / N) :=
    (ContDiff.sum fun i _ ↦ (cellCutoff_smooth J hJ a).comp
      (particleProjection N i).contDiff).div_const _
  simpa only [quotient_particleProjection, occupationFraction] using h

def occupationLipschitzConstant (N J : ℕ) : ℝ≥0 :=
  ⟨Real.sqrt (18 * (J : ℝ) ^ 2 / N), Real.sqrt_nonneg _⟩

theorem occupationLipschitzConstant_sq (N J : ℕ) :
    (occupationLipschitzConstant N J : ℝ) ^ 2 = 18 * (J : ℝ) ^ 2 / N :=
  Real.sq_sqrt (by positivity)

/-- Cauchy--Schwarz is applied to the particle blocks in the actual Euclidean
cover. It supplies precisely one inverse power of `N` in the squared bound. -/
theorem occupationFraction_lift_lipschitz (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    (a : MeshIndex J) :
    LipschitzWith (occupationLipschitzConstant N J)
      (fun y ↦ occupationFraction N J (by omega) a (configurationQuotient N y)) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  let d : Fin N → ℝ := fun i ↦
    cellCutoff J (by omega) a (configurationQuotient N y i) -
      cellCutoff J (by omega) a (configurationQuotient N z i)
  have hd (i : Fin N) : (d i) ^ 2 ≤
      (cellLipschitzConstant J : ℝ) ^ 2 * ‖particleProjection N i (y - z)‖ ^ 2 := by
    have h := (cellCutoff_lift_lipschitz J hJ a).dist_le_mul
      (particleProjection N i y) (particleProjection N i z)
    simp only [quotient_particleProjection, dist_eq_norm, ← map_sub] at h
    have hp := pow_le_pow_left₀ (abs_nonneg (d i)) h 2
    simpa only [d, sq_abs, mul_pow] using hp
  have hsum : (∑ i : Fin N, (d i) ^ 2) ≤
      (cellLipschitzConstant J : ℝ) ^ 2 * ‖y - z‖ ^ 2 := by
    calc
      _ ≤ ∑ i : Fin N, (cellLipschitzConstant J : ℝ) ^ 2 *
          ‖particleProjection N i (y - z)‖ ^ 2 := Finset.sum_le_sum fun i _ ↦ hd i
      _ = _ := by rw [← Finset.mul_sum, sum_particleProjection_norm_sq]
  have hcs : (∑ i : Fin N, d i) ^ 2 ≤
      (N : ℝ) * (cellLipschitzConstant J : ℝ) ^ 2 * ‖y - z‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
      (fun _ ↦ (1 : ℝ)) d
    have h' : (∑ i : Fin N, d i) ^ 2 ≤ (N : ℝ) * ∑ i : Fin N, (d i) ^ 2 := by
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one] using h
    exact h'.trans (by nlinarith [mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg N)])
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have he : occupationFraction N J (by omega) a (configurationQuotient N y) -
      occupationFraction N J (by omega) a (configurationQuotient N z) =
      (∑ i : Fin N, d i) / N := by
    simp only [occupationFraction, ← sub_div, ← Finset.sum_sub_distrib, d]
  rw [Real.dist_eq, he, dist_eq_norm]
  have hb : |(∑ i : Fin N, d i) / N| ^ 2 ≤
      ((occupationLipschitzConstant N J : ℝ) * ‖y - z‖) ^ 2 := by
    rw [sq_abs, div_pow, mul_pow, occupationLipschitzConstant_sq]
    apply (div_le_iff₀ (sq_pos_of_pos hNr)).mpr
    rw [cellLipschitzConstant_sq] at hcs
    convert hcs using 1
    field_simp [hNr.ne']
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp hb

def occupationValue (N J : ℕ) (hJ : 0 < J) (a : MeshIndex J) : C(Configuration N, ℝ) :=
  ⟨occupationFraction N J hJ a, occupationFraction_continuous N J hJ a⟩

/-- A genuine smooth pair, constructed by the proved quotient-gradient
representation; no derivative field is supplied as a premise. -/
def occupationSmoothPair (N J : ℕ) (hJ : 0 < J) (a : MeshIndex J) : SmoothPair N :=
  SmoothPair.ofContDiffLift (occupationValue N J hJ a) (occupationFraction_smooth N J hJ a)

def maximumValue (N J : ℕ) (hJ : 0 < J) : C(Configuration N, ℝ) :=
  ⟨maximumOccupation N J hJ, maximumOccupation_continuous N J hJ⟩

theorem maximumOccupation_lift_lipschitz (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J) :
    LipschitzWith (occupationLipschitzConstant N J)
      (fun y ↦ maximumOccupation N J (by omega) (configurationQuotient N y)) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  have hu (v w : Gradient N) :
      maximumOccupation N J (by omega) (configurationQuotient N v) -
        maximumOccupation N J (by omega) (configurationQuotient N w) ≤
      (occupationLipschitzConstant N J : ℝ) * dist v w := by
    obtain ⟨a, ha⟩ := maximumOccupation_attained N J (by omega) (configurationQuotient N v)
    have h := (occupationFraction_lift_lipschitz N J hN hJ a).dist_le_mul v w
    rw [Real.dist_eq] at h
    have haw := occupationFraction_le_maximum N J (by omega) a (configurationQuotient N w)
    rw [ha]
    linarith [le_abs_self (occupationFraction N J (by omega) a (configurationQuotient N v) -
      occupationFraction N J (by omega) a (configurationQuotient N w))]
  rw [Real.dist_eq]
  apply abs_le.mpr
  constructor
  · have h := hu z y
    rw [dist_comm] at h
    linarith
  · exact hu y z

theorem occupationFraction_gradient_sq_bound (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    (a : MeshIndex J) (X : Configuration N) :
    ‖descendedLiftGradient (occupationValue N J (by omega) a) X‖ ^ 2 ≤
      18 * (J : ℝ) ^ 2 / N := by
  have h := norm_descendedLiftGradient_le (occupationValue N J (by omega) a)
    (occupationFraction_lift_lipschitz N J hN hJ a) X
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [occupationLipschitzConstant_sq] using hs

/-- This bound also holds for the totalized gradient at exceptional points.
The following theorem identifies it with the actual derivative almost everywhere. -/
theorem maximumOccupation_gradient_sq_bound (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    (X : Configuration N) :
    ‖descendedLiftGradient (maximumValue N J (by omega)) X‖ ^ 2 ≤
      18 * (J : ℝ) ^ 2 / N := by
  have h := norm_descendedLiftGradient_le (maximumValue N J (by omega))
    (maximumOccupation_lift_lipschitz N J hN hJ) X
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [occupationLipschitzConstant_sq] using hs

theorem maximumOccupation_ae_hasFDerivAt (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J) :
    ∀ᵐ X ∂referenceMeasure N, ∀ y : Gradient N, configurationQuotient N y = X →
      HasFDerivAt (fun w ↦ maximumOccupation N J (by omega) (configurationQuotient N w))
        (innerSL ℝ (descendedLiftGradient (maximumValue N J (by omega)) X)) y :=
  ae_hasFDerivAt_configurationLift_descendedGradient (maximumValue N J (by omega))
    (maximumOccupation_lift_lipschitz N J hN hJ)

theorem maximumOccupation_ae_hasFDerivAt_gibbs (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    (g : Torus → ℝ) (β : ℝ) :
    ∀ᵐ X ∂gibbsMeasure g N β, ∀ y : Gradient N, configurationQuotient N y = X →
      HasFDerivAt (fun w ↦ maximumOccupation N J (by omega) (configurationQuotient N w))
        (innerSL ℝ (descendedLiftGradient (maximumValue N J (by omega)) X)) y :=
  ae_hasFDerivAt_configurationLift_gibbs g β (maximumValue N J (by omega))
    (maximumOccupation_lift_lipschitz N J hN hJ)

/-- At every differentiability point all active occupations have the same
physical differential. Nonsymmetric configurations and tied maxima are allowed. -/
theorem active_occupation_fderiv_eq (N J : ℕ) (hJ : 0 < J) (y : Gradient N)
    (hy : DifferentiableAt ℝ
      (fun w ↦ maximumOccupation N J hJ (configurationQuotient N w)) y)
    (a : MeshIndex J)
    (ha : maximumOccupation N J hJ (configurationQuotient N y) =
      occupationFraction N J hJ a (configurationQuotient N y)) :
    fderiv ℝ (fun w ↦ maximumOccupation N J hJ (configurationQuotient N w)) y =
      fderiv ℝ (fun w ↦ occupationFraction N J hJ a (configurationQuotient N w)) y := by
  have hm : IsLocalMin
      (fun w ↦ maximumOccupation N J hJ (configurationQuotient N w) -
        occupationFraction N J hJ a (configurationQuotient N w)) y := by
    exact Eventually.of_forall fun w ↦ by
      change maximumOccupation N J hJ (configurationQuotient N y) -
        occupationFraction N J hJ a (configurationQuotient N y) ≤
        maximumOccupation N J hJ (configurationQuotient N w) -
        occupationFraction N J hJ a (configurationQuotient N w)
      rw [ha, sub_self]
      exact sub_nonneg.mpr (occupationFraction_le_maximum N J hJ a _)
  have hz := hm.hasFDerivAt_eq_zero
    (hy.hasFDerivAt.sub ((occupationFraction_smooth N J hJ a).differentiable
      (by simp) y).hasFDerivAt)
  exact sub_eq_zero.mp hz

theorem maximumOccupation_ae_active_fderiv_eq (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J) :
    ∀ᵐ X ∂referenceMeasure N, ∀ y : Gradient N, configurationQuotient N y = X →
      ∀ a : MeshIndex J, maximumOccupation N J (by omega) X =
        occupationFraction N J (by omega) a X →
      fderiv ℝ (fun w ↦ maximumOccupation N J (by omega) (configurationQuotient N w)) y =
        fderiv ℝ (fun w ↦ occupationFraction N J (by omega) a (configurationQuotient N w)) y := by
  filter_upwards [ae_differentiableAt_configurationLift_all_representatives
    (maximumValue N J (by omega)) (maximumOccupation_lift_lipschitz N J hN hJ)] with X hX
  intro y hy a ha
  apply active_occupation_fderiv_eq N J (by omega) y (hX y hy) a
  simpa only [hy] using ha

end PeriodicAttractiveLogGas.SmoothOccupations
