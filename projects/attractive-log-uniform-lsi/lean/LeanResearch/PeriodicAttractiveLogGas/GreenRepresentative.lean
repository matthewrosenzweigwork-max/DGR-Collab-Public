import LeanResearch.PeriodicAttractiveLogGas.GreenRegularity
import LeanResearch.PeriodicAttractiveLogGas.GreenRepresentativeSymmetry
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! An actual regular Green representative on the square torus.

The smooth Euclidean representative constructed by Weyl regularity is set to
zero on the integer lattice. Its proved pointwise periodicity permits descent
through the quotient. The open quotient map supplies continuity away from the
origin and hence measurability on the whole torus. The normalized fundamental
box map transfers the Euclidean almost-everywhere identity to the specified
torus probability measure. No regularity or representative identity is assumed.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace PeriodicAttractiveLogGas

/-- The actual smooth Green lift, with value zero at every lattice point. -/
def regularGreenLift : PlanarSpace → ℝ :=
  greenRepresentativeZeroExtension smoothGreenLift

theorem regularGreenLift_of_mem {x : PlanarSpace} (hx : x ∈ offIntegerLattice) :
    regularGreenLift x = smoothGreenLift x :=
  greenRepresentativeZeroExtension_of_mem smoothGreenLift hx

theorem regularGreenLift_of_notMem {x : PlanarSpace} (hx : x ∉ offIntegerLattice) :
    regularGreenLift x = 0 :=
  greenRepresentativeZeroExtension_of_notMem smoothGreenLift hx

@[simp] theorem regularGreenLift_zero : regularGreenLift 0 = 0 := by
  apply regularGreenLift_of_notMem
  simp [offIntegerLattice]

theorem contDiffOn_regularGreenLift : ContDiffOn ℝ ∞ regularGreenLift offIntegerLattice :=
  contDiffOn_greenRepresentativeZeroExtension contDiffOn_smoothGreenLift

@[simp] theorem regularGreenLift_add_frequencyVector (x : PlanarSpace) (k : Frequency) :
    regularGreenLift (x + frequencyVector k) = regularGreenLift x :=
  greenRepresentativeZeroExtension_add_frequencyVector
    contDiffOn_smoothGreenLift.continuousOn greenLift_ae_smoothGreenLift.symm x k

@[simp] theorem regularGreenLift_neg (x : PlanarSpace) :
    regularGreenLift (-x) = regularGreenLift x :=
  greenRepresentativeZeroExtension_neg contDiffOn_smoothGreenLift.continuousOn
    greenLift_ae_smoothGreenLift.symm x

theorem regularGreenLift_eq_of_torusQuotient_eq {x y : PlanarSpace}
    (hxy : torusQuotient x = torusQuotient y) : regularGreenLift x = regularGreenLift y := by
  obtain ⟨m, rfl⟩ := exists_frequencyVector_of_torusQuotient_eq hxy
  exact (regularGreenLift_add_frequencyVector x m).symm

/-- Descent of the actual periodic lift; the chosen preimage does not affect the value. -/
def regularGreenRepresentative (z : Torus) : ℝ :=
  regularGreenLift (Classical.choose (torusQuotient_surjective z))

@[simp] theorem regularGreenRepresentative_lift (x : PlanarSpace) :
    regularGreenRepresentative (torusQuotient x) = regularGreenLift x := by
  apply regularGreenLift_eq_of_torusQuotient_eq
  exact Classical.choose_spec (torusQuotient_surjective (torusQuotient x))

theorem regularGreenRepresentative_lift_of_mem {x : PlanarSpace}
    (hx : x ∈ offIntegerLattice) :
    regularGreenRepresentative (torusQuotient x) = smoothGreenLift x :=
  (regularGreenRepresentative_lift x).trans (regularGreenLift_of_mem hx)

@[simp] theorem regularGreenRepresentative_zero : regularGreenRepresentative 0 = 0 := by
  rw [← torusQuotient_zero, regularGreenRepresentative_lift, regularGreenLift_zero]

theorem regularGreenRepresentative_even (z : Torus) :
    regularGreenRepresentative (-z) = regularGreenRepresentative z := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective z
  calc
    regularGreenRepresentative (-torusQuotient x) =
        regularGreenRepresentative (torusQuotient (-x)) :=
      congrArg regularGreenRepresentative (torusQuotient_neg x).symm
    _ = regularGreenLift (-x) := regularGreenRepresentative_lift (-x)
    _ = regularGreenLift x := regularGreenLift_neg x
    _ = regularGreenRepresentative (torusQuotient x) :=
      (regularGreenRepresentative_lift x).symm

/-- Ordinary Euclidean smoothness of the descended lift off every pole. -/
theorem contDiffOn_regularGreenRepresentative_lift :
    ContDiffOn ℝ ∞ (fun x : PlanarSpace ↦
      regularGreenRepresentative (torusQuotient x)) offIntegerLattice := by
  simpa only [regularGreenRepresentative_lift] using contDiffOn_regularGreenLift

theorem continuousAt_regularGreenRepresentative {z : Torus} (hz : z ≠ 0) :
    ContinuousAt regularGreenRepresentative z := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective z
  apply isOpenQuotientMap_torusQuotient.continuousAt_comp_iff.mp
  have hx : x ∈ offIntegerLattice := hz
  have hc : ContinuousAt regularGreenLift x :=
    contDiffOn_regularGreenLift.continuousOn.continuousAt
      (isOpen_offIntegerLattice.mem_nhds hx)
  simpa only [Function.comp_def, regularGreenRepresentative_lift] using hc

theorem continuousOn_regularGreenRepresentative :
    ContinuousOn regularGreenRepresentative ({0}ᶜ : Set Torus) := by
  intro z hz
  exact (continuousAt_regularGreenRepresentative (by simpa using hz)).continuousWithinAt

theorem regularGreenRepresentative_measurable : Measurable regularGreenRepresentative :=
  measurable_of_continuousOn_compl_singleton 0 continuousOn_regularGreenRepresentative

/-- The only points removed from the Euclidean regularity domain are the
integer lattice, parametrized by the actual frequency vectors. -/
theorem offIntegerLattice_compl_eq_range_frequencyVector :
    offIntegerLatticeᶜ = Set.range frequencyVector := by
  ext x
  constructor
  · intro hx
    have hx0 : torusQuotient x = 0 := by
      simpa only [offIntegerLattice, mem_compl_iff, mem_ofPred_eq, not_not] using hx
    obtain ⟨k, hk⟩ := exists_frequencyVector_of_torusQuotient_eq
      (torusQuotient_zero.trans hx0.symm)
    exact ⟨k, by simpa only [zero_add] using hk.symm⟩
  · rintro ⟨k, rfl⟩
    have hk0 : torusQuotient (frequencyVector k) = 0 := by
      simpa only [zero_add, torusQuotient_zero] using
        torusQuotient_add_frequencyVector (0 : PlanarSpace) k
    exact fun hne ↦ hne hk0

theorem countable_compl_offIntegerLattice : offIntegerLatticeᶜ.Countable := by
  rw [offIntegerLattice_compl_eq_range_frequencyVector]
  exact Set.countable_range frequencyVector

theorem ae_mem_offIntegerLattice : ∀ᵐ x : PlanarSpace ∂volume, x ∈ offIntegerLattice := by
  rw [ae_iff]
  exact countable_compl_offIntegerLattice.measure_zero volume

theorem regularGreenLift_measurable : Measurable regularGreenLift :=
  contDiffOn_regularGreenLift.continuousOn.measurable_of_countable_compl
    countable_compl_offIntegerLattice

/-- The zero values on the lattice do not change the Euclidean AE class. -/
theorem regularGreenLift_ae_greenLift : regularGreenLift =ᵐ[volume] greenLift := by
  have hrestricted : regularGreenLift =ᵐ[volume.restrict offIntegerLattice] greenLift :=
    greenRepresentativeZeroExtension_ae greenLift_ae_smoothGreenLift.symm
  filter_upwards [ae_imp_of_ae_restrict hrestricted, ae_mem_offIntegerLattice] with x hx hxmem
  exact hx hxmem

/-- The descended regular function represents the original real Fourier Green
function for the exact probability Haar measure, not just on Euclidean charts. -/
theorem regularGreenRepresentative_ae :
    regularGreenRepresentative =ᵐ[torusMeasure] greenRealRepresentative := by
  have hmp := measurePreserving_torusQuotient_box (centeredBoxAnchor 0)
  rw [← hmp.map_eq]
  apply (ae_map_iff hmp.aemeasurable
    (measurableSet_eq_fun regularGreenRepresentative_measurable
      greenRealRepresentative_measurable)).2
  have hae : regularGreenLift =ᵐ[volume.restrict
      (euclideanFundamentalBox (centeredBoxAnchor 0))] greenLift :=
    regularGreenLift_ae_greenLift.restrict
  filter_upwards [hae] with x hx
  simpa only [regularGreenRepresentative_lift, greenLift] using hx

theorem regularGreenRepresentative_coe_ae :
    (fun x ↦ (regularGreenRepresentative x : ℂ)) =ᵐ[torusMeasure] greenL2 := by
  filter_upwards [regularGreenRepresentative_ae, greenRealRepresentative_coe_ae] with x hx hc
  rw [hx]
  exact hc

theorem regularGreenRepresentative_memLp :
    MemLp regularGreenRepresentative 2 torusMeasure :=
  (memLp_congr_ae regularGreenRepresentative_ae).2 greenRealRepresentative_memLp

theorem regularGreenRepresentative_integrable :
    Integrable regularGreenRepresentative torusMeasure :=
  MemLp.integrable (by norm_num) regularGreenRepresentative_memLp

theorem regularGreenRepresentative_integral_zero :
    (∫ x, regularGreenRepresentative x ∂torusMeasure) = 0 :=
  (integral_congr_ae regularGreenRepresentative_ae).trans greenRealRepresentative_integral_zero

theorem regularGreenRepresentative_fourierCoeff (k : Frequency) :
    UnitAddTorus.mFourierCoeff (fun x ↦ (regularGreenRepresentative x : ℂ)) k =
      greenFourierCoeff k :=
  (torus_mFourierCoeff_congr regularGreenRepresentative_coe_ae k).trans
    (greenL2_fourierCoeff k)

/-- Pointwise local logarithmic expansion for the descended representative,
with the previously constructed smooth harmonic remainder. -/
theorem regularGreenRepresentative_local_expansion {x : PlanarSpace}
    (hx : x ∈ euclideanOpenBox (centeredBoxAnchor 0)) (hne : x ≠ 0) :
    regularGreenRepresentative (torusQuotient x) =
      planarLogKernel x + planarGreenQuadratic x + smoothGreenLogRemainder x :=
  (regularGreenRepresentative_lift_of_mem
    (mem_offIntegerLattice_of_mem_centeredOpenBox hx hne)).trans
      (smoothGreenLift_local_expansion hx hne)

end PeriodicAttractiveLogGas
