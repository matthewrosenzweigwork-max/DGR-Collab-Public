import LeanResearch.PeriodicAttractiveLogGas.Periodization
import LeanResearch.PeriodicAttractiveLogGas.LogFundamentalSolution

/-! The actual torus Green weak equation transported to compact local Euclidean
tests. Periodization, its ordinary Laplacian, Haar/volume normalization and
pairing integrability are proved before using the weak equation. -/

noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology ContDiff Laplacian

namespace PeriodicAttractiveLogGas

def greenLift (x : PlanarSpace) : ℝ := greenRealRepresentative (torusQuotient x)

theorem locallyIntegrable_greenLift : LocallyIntegrable greenLift volume :=
  locallyIntegrable_greenRealRepresentative_lift

theorem integrable_greenLift_mul_neg_laplacian {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (fun x ↦ greenLift x * -Δ f x) volume := by
  have h := integrable_planarLaplacian_pairing
    (locallyIntegrable_greenLift.locallyIntegrableOn Set.univ) hf hc (subset_univ _)
  simpa only [mul_neg] using! h.neg

/-- The local identity before choosing which lattice point lies in the box. -/
theorem greenLift_weak_equation_box {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {a : PlanarSpace}
    (hs : tsupport f ⊆ euclideanFundamentalBox a) :
    (∫ x, greenLift x * -Δ f x) =
      (2 * Real.pi) * (periodicSum f 0 - ∫ x, f x) := by
  let F := periodizedTest f hf hc
  have hF := contDiff_lift_periodizedTest f hf hc
  have hpair := greenRealRepresentative_test_integrable F hF
  have hzero (x : PlanarSpace) (hx : x ∉ euclideanFundamentalBox a) :
      greenLift x * -Δ f x = 0 := by
    have hz : Δ f x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hx (hs (tsupport_laplacian_subset f h)))
    rw [hz, neg_zero, mul_zero]
  calc
    (∫ x, greenLift x * -Δ f x) =
        ∫ x in euclideanFundamentalBox a, greenLift x * -Δ f x :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ x in euclideanFundamentalBox a,
        greenRealRepresentative (torusQuotient x) *
          torusNegativeLaplacian F hF (torusQuotient x) := by
      apply integral_congr_ae
      filter_upwards [periodizedTest_negativeLaplacian_ae hf hc hs] with x hx
      exact congrArg (fun t : ℝ ↦ greenLift x * t) hx.symm
    _ = ∫ z, greenRealRepresentative z * torusNegativeLaplacian F hF z ∂torusMeasure :=
      integral_torus_lift_on_box hpair a
    _ = (2 * Real.pi) * (F 0 - ∫ z, F z ∂torusMeasure) :=
      greenRealRepresentative_weak_equation F hF
    _ = (2 * Real.pi) * (periodicSum f 0 - ∫ x, f x) := by
      have hz : F 0 = periodicSum f 0 := by
        have hq0 : torusQuotient (0 : PlanarSpace) = (0 : Torus) := by ext j; rfl
        simpa only [hq0] using periodizedTest_lift f hf hc (0 : PlanarSpace)
      rw [hz, integral_periodizedTest hf hc hs]

/-- In a box containing the zero lift, the delta mass is at the ordinary origin. -/
theorem greenLift_weak_equation_box_zero {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {a : PlanarSpace}
    (hs : tsupport f ⊆ euclideanFundamentalBox a)
    (hzero : (0 : PlanarSpace) ∈ euclideanFundamentalBox a) :
    (∫ x, greenLift x * -Δ f x) = (2 * Real.pi) * (f 0 - ∫ x, f x) := by
  rw [greenLift_weak_equation_box hf hc hs, periodicSum_eq_on_box hs hzero]

def offIntegerLattice : Set PlanarSpace := {x | torusQuotient x ≠ 0}

theorem isOpen_offIntegerLattice : IsOpen offIntegerLattice :=
  isClosed_singleton.isOpen_compl.preimage isOpenQuotientMap_torusQuotient.continuous

theorem periodicSum_zero_of_support_offIntegerLattice {f : PlanarSpace → ℝ}
    (hf : tsupport f ⊆ offIntegerLattice) : periodicSum f 0 = 0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro k
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  have hq := hf hx
  apply hq
  simpa only [zero_add, torusQuotient_zero] using
    torusQuotient_add_frequencyVector (0 : PlanarSpace) k

theorem greenLift_weak_equation_box_away {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {a : PlanarSpace}
    (hs : tsupport f ⊆ euclideanFundamentalBox a)
    (ha : tsupport f ⊆ offIntegerLattice) :
    (∫ x, greenLift x * -Δ f x) = -(2 * Real.pi) * ∫ x, f x := by
  rw [greenLift_weak_equation_box hf hc hs,
    periodicSum_zero_of_support_offIntegerLattice ha]
  ring

end PeriodicAttractiveLogGas
