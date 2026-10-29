import LeanResearch.PeriodicAttractiveLogGas.RadialScaling
import LeanResearch.PeriodicAttractiveLogGas.Periodization
import LeanResearch.PeriodicAttractiveLogGas.TorusDistance

/-! The prescribed radial mollifier on the square torus.

This is the actual integer-lattice periodization of the fixed planar dilation.
Its Euclidean lift is smooth and periodic. For the source range
`0 < ε ≤ 1 / 16`, the planar topological support lies in the centered
fundamental box, so the existing normalized Haar transport proves mass one.
The centered-lift formula also gives support in the open Euclidean quotient
ball of radius `ε`, with the stronger closed support bound `ε / 2`.
There is no additional scale-dependent normalization.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ContDiff Topology

namespace PeriodicAttractiveLogGas

private theorem periodicSum_neg_of_even {f : PlanarSpace → ℝ}
    (hf : ∀ x, f (-x) = f x) (x : PlanarSpace) : periodicSum f (-x) = periodicSum f x := by
  have h := finsum_comp_equiv (Equiv.neg Frequency)
    (f := fun k ↦ f (-x + frequencyVector k))
  change (∑ᶠ k : Frequency, f (-x + frequencyVector (-k))) = periodicSum f (-x) at h
  calc
    periodicSum f (-x) = ∑ᶠ k : Frequency, f (-x + frequencyVector (-k)) := h.symm
    _ = periodicSum f x := by
      apply finsum_congr
      intro k
      have hk : frequencyVector (-k) = -frequencyVector k := by
        ext j
        simp
      have heq : -x + frequencyVector (-k) = -(x + frequencyVector k) := by
        rw [hk]
        abel
      rw [heq, hf]

/-- The continuous torus kernel whose lift is the smooth lattice periodization. -/
def periodicMollifier (ε : ℝ) (hε : 0 < ε) : C(Torus, ℝ) :=
  periodizedTest (scaledRadialMollifier ε) (contDiff_scaledRadialMollifier ε)
    (hasCompactSupport_scaledRadialMollifier ε hε)

@[simp] theorem periodicMollifier_lift (ε : ℝ) (hε : 0 < ε) (x : PlanarSpace) :
    periodicMollifier ε hε (torusQuotient x) = periodicSum (scaledRadialMollifier ε) x :=
  periodizedTest_lift (scaledRadialMollifier ε) (contDiff_scaledRadialMollifier ε)
    (hasCompactSupport_scaledRadialMollifier ε hε) x

theorem contDiff_periodicMollifier_lift (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ∞ (fun x : PlanarSpace ↦ periodicMollifier ε hε (torusQuotient x)) :=
  contDiff_lift_periodizedTest (scaledRadialMollifier ε) (contDiff_scaledRadialMollifier ε)
    (hasCompactSupport_scaledRadialMollifier ε hε)

theorem periodicMollifier_lift_add_frequencyVector (ε : ℝ) (hε : 0 < ε)
    (x : PlanarSpace) (k : Frequency) :
    periodicMollifier ε hε (torusQuotient (x + frequencyVector k)) =
      periodicMollifier ε hε (torusQuotient x) := by
  rw [torusQuotient_add_frequencyVector]

theorem continuous_periodicMollifier (ε : ℝ) (hε : 0 < ε) :
    Continuous (periodicMollifier ε hε) :=
  (periodicMollifier ε hε).continuous

theorem measurable_periodicMollifier (ε : ℝ) (hε : 0 < ε) :
    Measurable (periodicMollifier ε hε) :=
  (continuous_periodicMollifier ε hε).measurable

theorem integrable_periodicMollifier (ε : ℝ) (hε : 0 < ε) :
    Integrable (periodicMollifier ε hε) torusMeasure :=
  memLp_one_iff_integrable.mp
    (ContinuousMap.memLp (μ := torusMeasure) (p := 1) ℝ (periodicMollifier ε hε))

theorem periodicMollifier_nonneg (ε : ℝ) (hε : 0 < ε) (z : Torus) :
    0 ≤ periodicMollifier ε hε z := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective z
  rw [periodicMollifier_lift]
  exact finsum_nonneg (fun k ↦ scaledRadialMollifier_nonneg ε (x + frequencyVector k))

theorem periodicMollifier_neg (ε : ℝ) (hε : 0 < ε) (z : Torus) :
    periodicMollifier ε hε (-z) = periodicMollifier ε hε z := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective z
  have hq : torusQuotient (-x) = -torusQuotient x := by
    ext j
    rfl
  rw [← hq, periodicMollifier_lift, periodicMollifier_lift]
  exact periodicSum_neg_of_even (scaledRadialMollifier_neg ε) x

theorem tsupport_scaledRadialMollifier_subset_centeredBox (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) :
    tsupport (scaledRadialMollifier ε) ⊆
      euclideanFundamentalBox (centeredBoxAnchor 0) := by
  intro x hx
  apply euclideanOpenBox_subset_fundamentalBox
  apply mem_centeredOpenBox_of_norm_lt_half
  have hx' := mem_closedBall_zero_iff.mp
    (tsupport_scaledRadialMollifier_subset_closedBall ε hε hx)
  linarith

/-- The normalized Haar integral is the planar integral on the source scale range. -/
theorem integral_periodicMollifier (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) :
    ∫ z, periodicMollifier ε hε z ∂torusMeasure = 1 := by
  change (∫ z, periodizedTest (scaledRadialMollifier ε) (contDiff_scaledRadialMollifier ε)
    (hasCompactSupport_scaledRadialMollifier ε hε) z ∂torusMeasure) = 1
  rw [integral_periodizedTest (contDiff_scaledRadialMollifier ε)
    (hasCompactSupport_scaledRadialMollifier ε hε)
    (tsupport_scaledRadialMollifier_subset_centeredBox ε hε hεsmall)]
  exact integral_scaledRadialMollifier ε hε

/-- On the centered fundamental box, no nonzero lattice translate contributes. -/
theorem periodicMollifier_lift_eq_scaled_on_box (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) {x : PlanarSpace}
    (hx : x ∈ euclideanFundamentalBox (centeredBoxAnchor 0)) :
    periodicMollifier ε hε (torusQuotient x) = scaledRadialMollifier ε x := by
  rw [periodicMollifier_lift]
  exact periodicSum_eq_on_box
    (tsupport_scaledRadialMollifier_subset_centeredBox ε hε hεsmall) hx

/-- A global representative formula for the actual descended torus kernel. -/
theorem periodicMollifier_eq_scaled_centeredLift (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) (z : Torus) :
    periodicMollifier ε hε z = scaledRadialMollifier ε (centeredLift z) := by
  calc
    periodicMollifier ε hε z = periodicMollifier ε hε (torusQuotient (centeredLift z)) := by
      rw [torusQuotient_centeredLift]
    _ = scaledRadialMollifier ε (centeredLift z) :=
      periodicMollifier_lift_eq_scaled_on_box ε hε hεsmall
        (centeredLift_mem_fundamentalBox z)

theorem periodicMollifier_lift_eq_scaled_of_norm_lt_half (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) {x : PlanarSpace} (hx : ‖x‖ < (1 / 2 : ℝ)) :
    periodicMollifier ε hε (torusQuotient x) = scaledRadialMollifier ε x := by
  rw [periodicMollifier_eq_scaled_centeredLift ε hε hεsmall,
    centeredLift_torusQuotient_of_norm_lt_half hx]

/-- Radiality is with respect to the proved Euclidean quotient norm. -/
theorem periodicMollifier_eq_of_norm_eq (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) {z w : Torus}
    (hzw : torusEuclideanNorm z = torusEuclideanNorm w) :
    periodicMollifier ε hε z = periodicMollifier ε hε w := by
  rw [periodicMollifier_eq_scaled_centeredLift ε hε hεsmall,
    periodicMollifier_eq_scaled_centeredLift ε hε hεsmall]
  exact scaledRadialMollifier_eq_of_norm_eq ε (by simpa only [norm_centeredLift] using hzw)

theorem periodicMollifier_eq_zero_of_half_le_norm (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) {z : Torus} (hz : ε / 2 ≤ torusEuclideanNorm z) :
    periodicMollifier ε hε z = 0 := by
  rw [periodicMollifier_eq_scaled_centeredLift ε hε hεsmall]
  exact scaledRadialMollifier_eq_zero_of_half_le_norm ε hε
    (by simpa only [norm_centeredLift] using hz)

theorem support_periodicMollifier_subset (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) :
    Function.support (periodicMollifier ε hε) ⊆ {z : Torus | torusEuclideanNorm z < ε / 2} := by
  intro z hz
  change torusEuclideanNorm z < ε / 2
  by_contra h
  exact hz (periodicMollifier_eq_zero_of_half_le_norm ε hε hεsmall (le_of_not_gt h))

theorem tsupport_periodicMollifier_subset_closed (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) :
    tsupport (periodicMollifier ε hε) ⊆ {z : Torus | torusEuclideanNorm z ≤ ε / 2} := by
  apply closure_minimal ?_ (isClosed_le continuous_torusEuclideanNorm continuous_const)
  intro z hz
  exact (show torusEuclideanNorm z < ε / 2 from
    support_periodicMollifier_subset ε hε hεsmall hz).le

/-- The topological support is contained in the open quotient ball of radius `ε`. -/
theorem tsupport_periodicMollifier_subset (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) :
    tsupport (periodicMollifier ε hε) ⊆ {z : Torus | torusEuclideanNorm z < ε} := by
  intro z hz
  have hz' := tsupport_periodicMollifier_subset_closed ε hε hεsmall hz
  change torusEuclideanNorm z ≤ ε / 2 at hz'
  change torusEuclideanNorm z < ε
  linarith

theorem norm_periodicMollifier_le (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε ≤ (1 / 16 : ℝ)) (z : Torus) :
    ‖periodicMollifier ε hε z‖ ≤ fixedRadialMollifier 0 * ε ^ (-2 : ℝ) := by
  rw [periodicMollifier_eq_scaled_centeredLift ε hε hεsmall]
  exact norm_scaledRadialMollifier_le ε hε (centeredLift z)

end PeriodicAttractiveLogGas
