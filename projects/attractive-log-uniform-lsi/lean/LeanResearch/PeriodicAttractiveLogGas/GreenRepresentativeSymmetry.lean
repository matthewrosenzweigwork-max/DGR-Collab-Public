import LeanResearch.PeriodicAttractiveLogGas.GreenLocalWeak
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! Pointwise symmetries of continuous representatives of the Green lift.

The hypotheses are continuity on the complement of the integer lattice and
almost-everywhere equality there with the constructed measurable Green lift.
Restricted measure preservation transports the equality under lattice
translations and reflection. Uniqueness of continuous representatives on an
open set then proves the pointwise symmetries. This module does not construct
the continuous representative or assert any bound on it.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace PeriodicAttractiveLogGas

@[simp] theorem torusQuotient_neg (x : PlanarSpace) :
    torusQuotient (-x) = -torusQuotient x := by
  ext j
  change ((-x j : ℝ) : UnitAddCircle) = -(x j : UnitAddCircle)
  rfl

@[simp] theorem greenLift_add_frequencyVector (x : PlanarSpace) (k : Frequency) :
    greenLift (x + frequencyVector k) = greenLift x := by
  simp only [greenLift, torusQuotient_add_frequencyVector]

@[simp] theorem greenLift_neg (x : PlanarSpace) : greenLift (-x) = greenLift x := by
  simp only [greenLift, torusQuotient_neg, greenRealRepresentative_even]

@[simp] theorem mem_offIntegerLattice_add_frequencyVector_iff
    (x : PlanarSpace) (k : Frequency) :
    x + frequencyVector k ∈ offIntegerLattice ↔ x ∈ offIntegerLattice := by
  simp only [offIntegerLattice, mem_ofPred_eq, torusQuotient_add_frequencyVector]

@[simp] theorem mem_offIntegerLattice_neg_iff (x : PlanarSpace) :
    -x ∈ offIntegerLattice ↔ x ∈ offIntegerLattice := by
  simp only [offIntegerLattice, mem_ofPred_eq, torusQuotient_neg, neg_ne_zero]

theorem preimage_offIntegerLattice_add_frequencyVector (k : Frequency) :
    (fun x : PlanarSpace ↦ x + frequencyVector k) ⁻¹' offIntegerLattice =
      offIntegerLattice := by
  ext x
  exact mem_offIntegerLattice_add_frequencyVector_iff x k

theorem preimage_offIntegerLattice_neg :
    (fun x : PlanarSpace ↦ -x) ⁻¹' offIntegerLattice = offIntegerLattice := by
  ext x
  exact mem_offIntegerLattice_neg_iff x

/-- Lattice translations preserve Euclidean volume restricted to the open
complement of the integer lattice. -/
theorem measurePreserving_add_frequencyVector_offIntegerLattice (k : Frequency) :
    MeasurePreserving (fun x : PlanarSpace ↦ x + frequencyVector k)
      (volume.restrict offIntegerLattice) (volume.restrict offIntegerLattice) := by
  have h := (measurePreserving_add_right (volume : Measure PlanarSpace)
    (frequencyVector k)).restrict_preimage isOpen_offIntegerLattice.measurableSet
  simpa only [preimage_offIntegerLattice_add_frequencyVector] using h

/-- Reflection preserves the same restricted Euclidean volume. -/
theorem measurePreserving_neg_offIntegerLattice :
    MeasurePreserving (fun x : PlanarSpace ↦ -x)
      (volume.restrict offIntegerLattice) (volume.restrict offIntegerLattice) := by
  have h := (Measure.measurePreserving_neg (volume : Measure PlanarSpace)).restrict_preimage
    isOpen_offIntegerLattice.measurableSet
  simpa only [preimage_offIntegerLattice_neg] using h

/-- Any continuous representative of the Green lift is pointwise lattice
periodic away from the integer lattice. No symmetry of the representative is assumed. -/
theorem greenRepresentative_add_frequencyVector {G : PlanarSpace → ℝ}
    (hG : ContinuousOn G offIntegerLattice)
    (hGae : G =ᵐ[volume.restrict offIntegerLattice] greenLift)
    (k : Frequency) {x : PlanarSpace} (hx : x ∈ offIntegerLattice) :
    G (x + frequencyVector k) = G x := by
  have hcomp :=
    (measurePreserving_add_frequencyVector_offIntegerLattice k).quasiMeasurePreserving.ae_eq_comp hGae
  have hae : (fun y ↦ G (y + frequencyVector k)) =ᵐ[volume.restrict offIntegerLattice] G := by
    filter_upwards [hcomp, hGae] with y hy hy'
    exact hy.trans ((greenLift_add_frequencyVector y k).trans hy'.symm)
  have hc : ContinuousOn (fun y ↦ G (y + frequencyVector k)) offIntegerLattice :=
    hG.comp' (continuous_id.add continuous_const).continuousOn
      (fun y hy ↦ (mem_offIntegerLattice_add_frequencyVector_iff y k).2 hy)
  exact (Measure.eqOn_open_of_ae_eq hae isOpen_offIntegerLattice hc hG) hx

/-- Any continuous representative of the Green lift is pointwise even away
from the integer lattice. -/
theorem greenRepresentative_neg {G : PlanarSpace → ℝ}
    (hG : ContinuousOn G offIntegerLattice)
    (hGae : G =ᵐ[volume.restrict offIntegerLattice] greenLift)
    {x : PlanarSpace} (hx : x ∈ offIntegerLattice) : G (-x) = G x := by
  have hcomp := measurePreserving_neg_offIntegerLattice.quasiMeasurePreserving.ae_eq_comp hGae
  have hae : (fun y ↦ G (-y)) =ᵐ[volume.restrict offIntegerLattice] G := by
    filter_upwards [hcomp, hGae] with y hy hy'
    exact hy.trans ((greenLift_neg y).trans hy'.symm)
  have hc : ContinuousOn (fun y ↦ G (-y)) offIntegerLattice :=
    hG.comp' continuous_neg.continuousOn (fun y hy ↦ (mem_offIntegerLattice_neg_iff y).2 hy)
  exact (Measure.eqOn_open_of_ae_eq hae isOpen_offIntegerLattice hc hG) hx

/-- Give a representative the value zero at every lattice point. This choice
permits global algebraic symmetry and does not assert smoothness at the poles. -/
def greenRepresentativeZeroExtension (G : PlanarSpace → ℝ) (x : PlanarSpace) : ℝ := by
  classical
  exact if x ∈ offIntegerLattice then G x else 0

theorem greenRepresentativeZeroExtension_of_mem (G : PlanarSpace → ℝ)
    {x : PlanarSpace} (hx : x ∈ offIntegerLattice) :
    greenRepresentativeZeroExtension G x = G x := by
  simp [greenRepresentativeZeroExtension, hx]

theorem greenRepresentativeZeroExtension_of_notMem (G : PlanarSpace → ℝ)
    {x : PlanarSpace} (hx : x ∉ offIntegerLattice) :
    greenRepresentativeZeroExtension G x = 0 := by
  simp [greenRepresentativeZeroExtension, hx]

theorem greenRepresentativeZeroExtension_eqOn (G : PlanarSpace → ℝ) :
    EqOn (greenRepresentativeZeroExtension G) G offIntegerLattice :=
  fun _ hx ↦ greenRepresentativeZeroExtension_of_mem G hx

theorem continuousOn_greenRepresentativeZeroExtension {G : PlanarSpace → ℝ}
    (hG : ContinuousOn G offIntegerLattice) :
    ContinuousOn (greenRepresentativeZeroExtension G) offIntegerLattice :=
  hG.congr (greenRepresentativeZeroExtension_eqOn G)

theorem contDiffOn_greenRepresentativeZeroExtension {G : PlanarSpace → ℝ}
    (hG : ContDiffOn ℝ ∞ G offIntegerLattice) :
    ContDiffOn ℝ ∞ (greenRepresentativeZeroExtension G) offIntegerLattice :=
  hG.congr (fun _ hx ↦ greenRepresentativeZeroExtension_of_mem G hx)

theorem greenRepresentativeZeroExtension_ae {G : PlanarSpace → ℝ}
    (hGae : G =ᵐ[volume.restrict offIntegerLattice] greenLift) :
    greenRepresentativeZeroExtension G =ᵐ[volume.restrict offIntegerLattice] greenLift :=
  ((greenRepresentativeZeroExtension_eqOn G).aeEq_restrict
    isOpen_offIntegerLattice.measurableSet).trans hGae

/-- The zero-at-lattice extension has genuine lattice periodicity at every point. -/
theorem greenRepresentativeZeroExtension_add_frequencyVector {G : PlanarSpace → ℝ}
    (hG : ContinuousOn G offIntegerLattice)
    (hGae : G =ᵐ[volume.restrict offIntegerLattice] greenLift)
    (x : PlanarSpace) (k : Frequency) :
    greenRepresentativeZeroExtension G (x + frequencyVector k) =
      greenRepresentativeZeroExtension G x := by
  classical
  by_cases hx : x ∈ offIntegerLattice
  · rw [greenRepresentativeZeroExtension_of_mem G
      ((mem_offIntegerLattice_add_frequencyVector_iff x k).2 hx),
      greenRepresentativeZeroExtension_of_mem G hx]
    exact greenRepresentative_add_frequencyVector hG hGae k hx
  · have htrans : x + frequencyVector k ∉ offIntegerLattice :=
      fun h ↦ hx ((mem_offIntegerLattice_add_frequencyVector_iff x k).1 h)
    rw [greenRepresentativeZeroExtension_of_notMem G htrans,
      greenRepresentativeZeroExtension_of_notMem G hx]

/-- The zero-at-lattice extension is genuinely even at every point. -/
theorem greenRepresentativeZeroExtension_neg {G : PlanarSpace → ℝ}
    (hG : ContinuousOn G offIntegerLattice)
    (hGae : G =ᵐ[volume.restrict offIntegerLattice] greenLift) (x : PlanarSpace) :
    greenRepresentativeZeroExtension G (-x) = greenRepresentativeZeroExtension G x := by
  classical
  by_cases hx : x ∈ offIntegerLattice
  · rw [greenRepresentativeZeroExtension_of_mem G ((mem_offIntegerLattice_neg_iff x).2 hx),
      greenRepresentativeZeroExtension_of_mem G hx]
    exact greenRepresentative_neg hG hGae hx
  · have hneg : -x ∉ offIntegerLattice := fun h ↦ hx ((mem_offIntegerLattice_neg_iff x).1 h)
    rw [greenRepresentativeZeroExtension_of_notMem G hneg,
      greenRepresentativeZeroExtension_of_notMem G hx]

end PeriodicAttractiveLogGas
