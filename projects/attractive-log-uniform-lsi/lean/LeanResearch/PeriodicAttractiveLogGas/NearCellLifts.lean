import LeanResearch.PeriodicAttractiveLogGas.MeshNearbyGeometry
import LeanResearch.PeriodicAttractiveLogGas.GreenPointRescaling
import LeanResearch.PeriodicAttractiveLogGas.PositiveLogPoleMoments
import LeanResearch.PeriodicAttractiveLogGas.ConditionalLawEstimates

/-! Exact cell-only geometry for source Lemma residual-kernels.
The radius is sqrt(2)*(R+1) and the mesh gate is J >= 8*(R+1).
Earlier edge-patch bounds are not substituted for these constants. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PeriodicAttractiveLogGas.NearCellLifts

open MeshCells MeshAdjacentCells MeshNearbyGeometry PositiveLogPoleMoments

def cellReferenceRadius (R : ℕ) : ℝ := Real.sqrt 2 * ((R : ℝ) + 1)

theorem one_le_cellReferenceRadius (R : ℕ) : 1 ≤ cellReferenceRadius R := by
  have hs : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  unfold cellReferenceRadius
  nlinarith [mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (Nat.cast_nonneg R)]

theorem cellReferenceRadius_lt_half {J R : ℕ} (hmesh : 8 * (R + 1) ≤ J) :
    cellReferenceRadius R < (J : ℝ) / 2 := by
  have hJr : 8 * ((R : ℝ) + 1) ≤ J := by exact_mod_cast hmesh
  have hs : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hm := mul_lt_mul_of_pos_right hs (show (0 : ℝ) < (R : ℝ) + 1 by positivity)
  unfold cellReferenceRadius
  linarith [show (0 : ℝ) ≤ R from Nat.cast_nonneg R]

/-- A literal compatible lift with the sharper cell-only coordinate bound. -/
theorem exists_compatible_lift {J R : ℕ} (hJ : 0 < J) (a b : MeshIndex J)
    (hab : periodicIndexDistance a b ≤ R) {y : Torus}
    (hy : y ∈ closure (meshCell J hJ b)) :
    ∃ Y : PlanarSpace, meshChart J a Y = y ∧
      ∀ Z ∈ closedUnitSquare, ∀ k : Fin 2, |Z k - Y k| ≤ (R : ℝ) + 1 := by
  rw [closure_meshCell J hJ b] at hy
  obtain ⟨V, hV, rfl⟩ := hy
  obtain ⟨d, hd, hc⟩ := nearby_displacement ((mem_nearbyCells a b).mpr hab)
  refine ⟨frequencyVector d + V, meshChart_integerDisplacement hJ a b d hc V, ?_⟩
  intro Z hZ k
  have hdl : -(R : ℝ) ≤ (d k : ℝ) := by exact_mod_cast (hd k).1
  have hdu : (d k : ℝ) ≤ (R : ℝ) := by exact_mod_cast (hd k).2
  have hv := hV k (mem_univ k)
  have hz := hZ k (mem_univ k)
  change 0 ≤ V k ∧ V k ≤ 1 at hv
  change 0 ≤ Z k ∧ Z k ≤ 1 at hz
  rw [PiLp.add_apply, frequencyVector_apply, abs_le]
  constructor <;> linarith

theorem norm_sub_le_cellReferenceRadius {R : ℕ} {Z Y : PlanarSpace}
    (h : ∀ k : Fin 2, |Z k - Y k| ≤ (R : ℝ) + 1) :
    ‖Z - Y‖ ≤ cellReferenceRadius R := by
  apply euclidean_norm_le_sqrt_two_mul (by positivity)
  simpa only [PiLp.sub_apply] using h

/-- Exact Euclidean radius, half-period condition and physical distance law. -/
theorem exists_reference_lift {J R : ℕ} (hJ : 0 < J)
    (hmesh : 8 * (R + 1) ≤ J) (a b : MeshIndex J)
    (hab : periodicIndexDistance a b ≤ R) {y : Torus}
    (hy : y ∈ closure (meshCell J hJ b)) :
    ∃ Y : PlanarSpace, meshChart J a Y = y ∧
      ∀ Z ∈ closedUnitSquare,
        (∀ k : Fin 2, |Z k - Y k| ≤ (R : ℝ) + 1) ∧
        ‖Z - Y‖ ≤ cellReferenceRadius R ∧
        ‖Z - Y‖ < (J : ℝ) / 2 ∧
        torusEuclideanDist (meshChart J a Z) y = (J : ℝ)⁻¹ * ‖Z - Y‖ := by
  obtain ⟨Y, hY, hbound⟩ := exists_compatible_lift hJ a b hab hy
  refine ⟨Y, hY, ?_⟩
  intro Z hZ
  have hn := norm_sub_le_cellReferenceRadius (hbound Z hZ)
  have hh := hn.trans_lt (cellReferenceRadius_lt_half hmesh)
  exact ⟨hbound Z hZ, hn, hh, by
    rw [← hY]
    exact torusDistance_meshChart_eq_scaled_norm hJ a hh⟩

theorem meshChart_sub (J : ℕ) (a : MeshIndex J) (Z Y : PlanarSpace) :
    meshChart J a Z - meshChart J a Y = torusQuotient ((J : ℝ)⁻¹ • (Z - Y)) := by
  change torusQuotient (meshAffine J a Z) - torusQuotient (meshAffine J a Y) = _
  rw [← torusQuotient_sub, meshAffine_sub]

theorem abs_neg_log_le_positive_part {r D : ℝ} (hr : 0 < r) (hD : 1 ≤ D) (hrD : r ≤ D) :
    |-Real.log r| ≤ max 0 (-Real.log r) + Real.log D := by
  have hl := Real.log_le_log hr hrD
  have hDlog := Real.log_nonneg hD
  have hzero : (0 : ℝ) ≤ max 0 (-Real.log r) := le_max_left _ _
  have hneg : -Real.log r ≤ max 0 (-Real.log r) := le_max_right _ _
  rw [abs_le]
  constructor <;> linarith

/-- Pointwise domination of the actual shifted Green kernel off its pole. -/
theorem shifted_green_bound {J R : ℕ} (hJ : 0 < J)
    (hmesh : 8 * (R + 1) ≤ J) (a : MeshIndex J)
    {C₀ : ℝ} (hb : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    {Y Z : PlanarSpace} (hne : Z ≠ Y) (hd : ‖Z - Y‖ ≤ cellReferenceRadius R) :
    |regularGreenRepresentative (meshChart J a Z - meshChart J a Y) - Real.log (J : ℝ)| ≤
      positiveLogPole Y Z + (Real.log (cellReferenceRadius R) + C₀) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have he := GreenPointRescaling.abs_logRemainder_le hJr
    (cellReferenceRadius_lt_half hmesh) hb hne hd
  have hl := abs_neg_log_le_positive_part
    (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) (one_le_cellReferenceRadius R) hd
  have hid :
      regularGreenRepresentative (meshChart J a Z - meshChart J a Y) - Real.log (J : ℝ) =
      -Real.log ‖Z - Y‖ + GreenPointRescaling.logRemainder J Y Z := by
    rw [meshChart_sub]
    unfold GreenPointRescaling.logRemainder
    ring
  rw [hid]
  calc
    _ ≤ |-Real.log ‖Z - Y‖| + |GreenPointRescaling.logRemainder J Y Z| := abs_add_le _ _
    _ ≤ (max 0 (-Real.log ‖Z - Y‖) + Real.log (cellReferenceRadius R)) + C₀ :=
      add_le_add hl he
    _ = _ := by unfold positiveLogPole; ring

/-- The actual normalized-square chart bound at every prescribed point of the
other closed cell; only its single planar pole is discarded. -/
theorem exists_ae_shifted_green_domination {J R : ℕ} (hJ : 0 < J)
    (hmesh : 8 * (R + 1) ≤ J) (a b : MeshIndex J)
    (hab : periodicIndexDistance a b ≤ R) {y : Torus}
    (hy : y ∈ closure (meshCell J hJ b)) :
    ∃ Y : PlanarSpace, meshChart J a Y = y ∧
      ∀ᵐ Z ∂squareLebesgue,
        |regularGreenRepresentative (meshChart J a Z - y) - Real.log (J : ℝ)| ≤
          positiveLogPole Y Z +
            (Real.log (cellReferenceRadius R) + ConditionalLawEstimates.kernelConstant) := by
  obtain ⟨Y, hY, hbound⟩ := exists_reference_lift hJ hmesh a b hab hy
  refine ⟨Y, hY, ?_⟩
  have hne : ∀ᵐ Z ∂squareLebesgue, Z ≠ Y :=
    SingularRectangleMoments.squareLebesgue_le_volume.absolutelyContinuous.ae_le
      ((volume : Measure PlanarSpace).ae_ne Y)
  filter_upwards [PoleLogMoments.ae_mem_closed_square, hne] with Z hZ hZY
  rw [← hY]
  exact shifted_green_bound hJ hmesh a ConditionalLawEstimates.kernel_log_bound hZY (hbound Z hZ).2.1

theorem near_shift_bound_nonneg (R : ℕ) :
    0 ≤ Real.log (cellReferenceRadius R) + ConditionalLawEstimates.kernelConstant :=
  add_nonneg (Real.log_nonneg (one_le_cellReferenceRadius R))
    ConditionalLawEstimates.kernelConstant_pos.le

end PeriodicAttractiveLogGas.NearCellLifts
