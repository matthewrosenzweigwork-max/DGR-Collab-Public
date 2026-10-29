import DGRHS.Gaussian.PeriodicLogFourier
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Packet P9h, unit 2 (part 1): lifts of torus points to `ℝ^d` and the minimal-image property for
Lipschitz transport fields on the flat torus.

A point of the torus `𝕋^d = ι → UnitAddCircle` has a representative in the centered cube
`[-1/2,1/2]^d`; `periodicCenteredLift` picks one.  For `z = x - y` with this representative `ẑ`, the
flat torus distance (sup of the circle norms of the coordinates) is `max_i |ẑ_i|`, which is at most
`‖ẑ + m‖₂` for every lattice vector `m`.  Hence a field `v : 𝕋^d → ℝ^d` that is `K`-Lipschitz for the
sup-metric of the torus satisfies `‖v x - v y‖ ≤ K ‖ẑ + m‖₂` for all `m` (used termwise in the lattice
sums of the periodized kernels).
-/

noncomputable section
open MeasureTheory
open scoped NNReal
namespace DGRHS.Periodic
universe u
set_option linter.unusedSectionVars false
variable {ι : Type u} [Fintype ι]

/-- The representative in `[-1/2, 1/2)` of a point of the unit circle. -/
def circleCentered (t : UnitAddCircle) : ℝ :=
  ((AddCircle.equivIco (1 : ℝ) (-1 / 2) t : Set.Ico (-1 / 2 : ℝ) (-1 / 2 + 1)) : ℝ)

lemma circleCentered_abs_le (t : UnitAddCircle) : |circleCentered t| ≤ 1 / 2 := by
  have h := (AddCircle.equivIco (1 : ℝ) (-1 / 2) t).2
  unfold circleCentered
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

lemma circleCentered_coe (t : UnitAddCircle) : ((circleCentered t : ℝ) : UnitAddCircle) = t := by
  unfold circleCentered
  exact AddCircle.coe_equivIco

lemma measurable_circleCentered : Measurable circleCentered := by
  have h := (AddCircle.measurableEquivIco (1 : ℝ) (-1 / 2)).measurable
  exact measurable_subtype_coe.comp h

lemma norm_circleCentered (t : UnitAddCircle) : ‖t‖ = |circleCentered t| := by
  conv_lhs => rw [← circleCentered_coe t]
  exact (AddCircle.norm_coe_eq_abs_iff (p := 1) one_ne_zero).2 (by simpa using circleCentered_abs_le t)

lemma abs_le_abs_add_int {r : ℝ} (hr : |r| ≤ 1 / 2) (m : ℤ) : |r| ≤ |r + (m : ℝ)| := by
  by_cases hm : m = 0
  · simp [hm]
  · have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have := Int.one_le_abs hm
      exact_mod_cast this
    have h2 : |(m : ℝ)| ≤ |r + (m : ℝ)| + |r| := by
      calc |(m : ℝ)| = |(r + (m : ℝ)) + (-r)| := by ring_nf
        _ ≤ |r + (m : ℝ)| + |-r| := abs_add_le _ _
        _ = _ := by rw [abs_neg]
    linarith

/-- The lift of a point of `ℝ^d` to the torus. -/
def periodicLift (x : EuclideanSpace ℝ ι) : PeriodicTorus ι := fun i => (x i : UnitAddCircle)

/-- A representative in `[-1/2,1/2]^d` of a torus point. -/
def periodicCenteredLift (z : PeriodicTorus ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i => circleCentered (z i)

lemma periodicCenteredLift_apply (z : PeriodicTorus ι) (i : ι) :
    periodicCenteredLift z i = circleCentered (z i) := rfl

lemma periodicCenteredLift_abs_le (z : PeriodicTorus ι) (i : ι) :
    |periodicCenteredLift z i| ≤ 1 / 2 := circleCentered_abs_le (z i)

lemma periodicLift_centeredLift (z : PeriodicTorus ι) : periodicLift (periodicCenteredLift z) = z := by
  funext i
  exact circleCentered_coe (z i)

lemma periodicLift_add (x y : EuclideanSpace ℝ ι) :
    periodicLift (x + y) = periodicLift x + periodicLift y := by
  funext i
  simp [periodicLift]

lemma periodicLift_sub (x y : EuclideanSpace ℝ ι) :
    periodicLift (x - y) = periodicLift x - periodicLift y := by
  funext i
  simp [periodicLift]

lemma periodicLift_lattice [Nonempty ι] (m : PeriodicFrequency ι) :
    periodicLift (periodicFrequencyVector m) = 0 := by
  funext i
  simp only [periodicLift, periodicFrequencyVector_apply, Pi.zero_apply]
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨m i, by simp⟩

lemma periodicLift_add_lattice [Nonempty ι] (x : EuclideanSpace ℝ ι) (m : PeriodicFrequency ι) :
    periodicLift (x + periodicFrequencyVector m) = periodicLift x := by
  rw [periodicLift_add, periodicLift_lattice, add_zero]

/-- Minimal image: the flat torus distance of `x`, `y` is at most the Euclidean norm of every lift of
`x - y`. -/
lemma dist_le_norm_centeredLift_add [Nonempty ι] (x y : PeriodicTorus ι) (m : PeriodicFrequency ι) :
    dist x y ≤ ‖periodicCenteredLift (x - y) + periodicFrequencyVector m‖ := by
  rw [dist_pi_le_iff (norm_nonneg _)]
  intro i
  rw [dist_eq_norm, ← Pi.sub_apply, norm_circleCentered]
  have hi : |circleCentered ((x - y) i)| ≤ |circleCentered ((x - y) i) + (m i : ℝ)| :=
    abs_le_abs_add_int (circleCentered_abs_le _) (m i)
  refine hi.trans ?_
  have := PiLp.norm_apply_le (periodicCenteredLift (x - y) + periodicFrequencyVector m) i
  simpa [periodicCenteredLift_apply] using this

lemma norm_sub_le_of_lipschitz [Nonempty ι] {K : ℝ≥0} {v : PeriodicTorus ι → EuclideanSpace ℝ ι}
    (hv : LipschitzWith K v) (x y : PeriodicTorus ι) (m : PeriodicFrequency ι) :
    ‖v x - v y‖ ≤ (K : ℝ) * ‖periodicCenteredLift (x - y) + periodicFrequencyVector m‖ := by
  have h := hv.dist_le_mul x y
  rw [dist_eq_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_left (dist_le_norm_centeredLift_add x y m) K.coe_nonneg)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.measurable_circleCentered
#print axioms DGRHS.Periodic.norm_circleCentered
#print axioms DGRHS.Periodic.periodicLift_add_lattice
#print axioms DGRHS.Periodic.dist_le_norm_centeredLift_add
#print axioms DGRHS.Periodic.norm_sub_le_of_lipschitz
