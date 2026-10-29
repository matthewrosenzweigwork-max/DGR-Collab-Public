import LeanResearch.PeriodicAttractiveLogGas.Geometry
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! An L2 Fourier construction with the exact square-torus coefficients.

Source: eq:fourier and the Fourier construction in lem:kernel. This file
constructs only the L2 class. The distributional equation, a real even
representative, local logarithmic expansion, and off-pole estimates remain
separate obligations. No pointwise Fourier sum is used.

The exact construction and mean-zero identities have been elaborated and
checked; later distributional and pointwise properties are not asserted here. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal lp

namespace PeriodicAttractiveLogGas

abbrev Frequency := Fin 2 → ℤ

/-- The real Euclidean vector associated with an integer frequency. -/
def frequencyVector (k : Frequency) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun j ↦ (k j : ℝ)

@[simp]
theorem frequencyVector_apply (k : Frequency) (j : Fin 2) :
    frequencyVector k j = (k j : ℝ) := rfl

@[simp]
theorem frequencyVector_zero : frequencyVector 0 = 0 := by
  ext j
  simp

theorem frequencyVector_injective : Function.Injective frequencyVector := by
  intro k l h
  funext j
  have hj : (k j : ℝ) = (l j : ℝ) :=
    congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v j) h
  exact Int.cast_injective hj

/-- This is the sum of coordinate squares, not the squared Pi supremum norm. -/
def frequencySq (k : Frequency) : ℝ := ∑ j, (k j : ℝ) ^ 2

theorem frequencySq_eq_norm_sq (k : Frequency) :
    frequencySq k = ‖frequencyVector k‖ ^ 2 := by
  simpa only [frequencySq, frequencyVector_apply] using
    (EuclideanSpace.real_norm_sq_eq (frequencyVector k)).symm

@[simp]
theorem frequencySq_zero : frequencySq 0 = 0 := by
  simp [frequencySq]

@[simp]
theorem frequencySq_neg (k : Frequency) : frequencySq (-k) = frequencySq k := by
  simp [frequencySq]

theorem frequencySq_pos {k : Frequency} (hk : k ≠ 0) : 0 < frequencySq k := by
  have hv : frequencyVector k ≠ 0 := by
    intro h
    apply hk
    apply frequencyVector_injective
    simpa using h
  rw [frequencySq_eq_norm_sq, pow_two]
  exact mul_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hv)

abbrev frequencyBasis :
    Module.Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis

abbrev frequencyLattice : Submodule ℤ (EuclideanSpace ℝ (Fin 2)) :=
  Submodule.span ℤ (Set.range frequencyBasis)

def frequencyLatticePoint (k : Frequency) : frequencyLattice :=
  ⟨frequencyVector k, by
    apply (frequencyBasis.mem_span_iff_repr_mem ℤ (frequencyVector k)).2
    intro j
    refine ⟨k j, ?_⟩
    simp [frequencyBasis]⟩

theorem frequencyLatticePoint_injective :
    Function.Injective frequencyLatticePoint := by
  intro k l h
  exact frequencyVector_injective (congrArg Subtype.val h)

/-- Pull inverse-fourth-power summability back from the standard integer lattice. -/
theorem summable_frequencyVector_inv_pow_four :
    Summable (fun k : Frequency ↦ ‖frequencyVector k‖⁻¹ ^ 4) := by
  have hdim : Module.finrank ℤ frequencyLattice = 2 := by
    rw [ZLattice.rank ℝ frequencyLattice]
    exact finrank_euclideanSpace_fin
  have hs := ZLattice.summable_norm_pow_inv frequencyLattice 4 (by
    rw [hdim]
    norm_num)
  have hp := hs.comp_injective frequencyLatticePoint_injective
  change Summable (fun k : Frequency ↦ ‖frequencyVector k‖⁻¹ ^ 4) at hp
  exact hp

/-- Zero mean and the manuscript's nonzero Fourier coefficient. -/
def greenFourierCoeff (k : Frequency) : ℂ :=
  if k = 0 then 0 else ((1 / (2 * Real.pi * frequencySq k) : ℝ) : ℂ)

@[simp]
theorem greenFourierCoeff_zero : greenFourierCoeff 0 = 0 := by
  simp [greenFourierCoeff]

theorem greenFourierCoeff_of_ne_zero {k : Frequency} (hk : k ≠ 0) :
    greenFourierCoeff k = ((1 / (2 * Real.pi * frequencySq k) : ℝ) : ℂ) := by
  simp [greenFourierCoeff, hk]

@[simp]
theorem greenFourierCoeff_neg (k : Frequency) :
    greenFourierCoeff (-k) = greenFourierCoeff k := by
  simp [greenFourierCoeff]

theorem norm_greenFourierCoeff_sq (k : Frequency) :
    ‖greenFourierCoeff k‖ ^ 2 =
      (2 * Real.pi)⁻¹ ^ 2 * ‖frequencyVector k‖⁻¹ ^ 4 := by
  by_cases hk : k = 0
  · subst k
    simp
  · simp only [greenFourierCoeff_of_ne_zero hk, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, one_div]
    rw [frequencySq_eq_norm_sq, mul_inv_rev, ← inv_pow, mul_pow]
    ring

theorem summable_greenFourierCoeff_sq :
    Summable (fun k : Frequency ↦ ‖greenFourierCoeff k‖ ^ 2) := by
  exact (summable_frequencyVector_inv_pow_four.mul_left ((2 * Real.pi)⁻¹ ^ 2)).congr
    fun k ↦ (norm_greenFourierCoeff_sq k).symm

theorem greenFourierCoeff_memℓp : Memℓp greenFourierCoeff 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2
  simpa using summable_greenFourierCoeff_sq

def greenCoeffVector : ℓ²(Frequency, ℂ) :=
  ⟨greenFourierCoeff, greenFourierCoeff_memℓp⟩

/- The exact local measure convention used inside AddCircleMulti. Its product
is definitionally the project's explicit probability Haar measure. -/
local instance greenFourierCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem fourier_volume_eq_torusMeasure :
    (volume : Measure Torus) = torusMeasure := rfl

def torusFourierBasis : HilbertBasis Frequency ℂ (Lp ℂ 2 torusMeasure) :=
  UnitAddTorus.mFourierBasis (d := Fin 2)

theorem torusFourierBasis_repr (f : Lp ℂ 2 torusMeasure) (k : Frequency) :
    torusFourierBasis.repr f k = UnitAddTorus.mFourierCoeff f k :=
  UnitAddTorus.mFourierBasis_repr f k

/-- An actual L2 element obtained by the inverse Fourier isometry. -/
def greenL2 : Lp ℂ 2 torusMeasure :=
  torusFourierBasis.repr.symm greenCoeffVector

theorem greenL2_fourierCoeff (k : Frequency) :
    UnitAddTorus.mFourierCoeff greenL2 k = greenFourierCoeff k := by
  rw [← torusFourierBasis_repr]
  simp [greenL2, greenCoeffVector]

theorem greenL2_unique (f : Lp ℂ 2 torusMeasure)
    (hf : ∀ k : Frequency, UnitAddTorus.mFourierCoeff f k = greenFourierCoeff k) :
    f = greenL2 := by
  apply torusFourierBasis.repr.injective
  apply lp.ext
  funext k
  simpa only [torusFourierBasis_repr, greenL2_fourierCoeff] using hf k

theorem existsUnique_greenL2 :
    ∃! f : Lp ℂ 2 torusMeasure,
      ∀ k : Frequency, UnitAddTorus.mFourierCoeff f k = greenFourierCoeff k := by
  refine ⟨greenL2, greenL2_fourierCoeff, ?_⟩
  intro f hf
  exact greenL2_unique f hf

theorem greenL2_hasSum :
    HasSum (fun k : Frequency ↦ greenFourierCoeff k •
      UnitAddTorus.mFourierLp (d := Fin 2) 2 k) greenL2 := by
  simp_rw [← greenL2_fourierCoeff]
  exact UnitAddTorus.hasSum_mFourier_series_L2 greenL2

theorem greenL2_integrable : Integrable (greenL2 : Torus → ℂ) torusMeasure :=
  MemLp.integrable (by norm_num) (Lp.memLp greenL2)

theorem greenL2_integral_zero : (∫ x, greenL2 x ∂torusMeasure) = 0 := by
  simpa only [UnitAddTorus.mFourierCoeff, neg_zero, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_smul, greenFourierCoeff_zero] using!
    greenL2_fourierCoeff (0 : Frequency)

end PeriodicAttractiveLogGas
