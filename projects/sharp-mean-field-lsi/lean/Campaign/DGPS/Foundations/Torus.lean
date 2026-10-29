import SharpSymmetricLSI.Infra.TorusLift

/-!
# The unit torus, Haar probability and weak gradients (DEF001)

INTERFACES/definitions.md §1. `Torus d = ℝ^d/ℤ^d`, realised (as permitted) by the legacy carrier
`SharpLSI.Torus d = UnitAddTorus (Fin d) = Fin d → AddCircle 1`, imported in place.
`haar d` is its Haar probability measure, the pushforward of Lebesgue measure on the unit box
(`haar_eq_map_unitBox`).

Euclidean conventions:
* Mathlib's metric on `Fin d → AddCircle 1` is the sup metric; it is **not** used for Lipschitz
  constants. `torusDist` is the Euclidean quotient distance `√(∑ⱼ ‖xⱼ - yⱼ‖²)`; it is bounded by
  the Euclidean distance of any lifts (`torusDist_liftT_le`) and equals it for lifts within
  half a period in each coordinate (`torusDist_liftT_eq`).
* Tangent vectors live in `EuclideanSpace ℝ (Fin d)`, so `‖v‖² = ∑ⱼ vⱼ²`
  (`tangent_norm_sq`); on `N` particles the squared norm is the sum over labels and coordinates
  (`particleTangentNormSq_eq`).

Weak gradients (tested on smooth periodic functions, Haar integrals): `IsWeakGradient u g` says
`u ∈ L²(m)`, `g ∈ L²(m; ℝ^d)` and `∫ u ∂ⱼφ dm = -∫ gⱼ φ dm` for every smooth periodic real `φ`
and every `j`. `weakGradient u hu` takes the proof `hu : MemH1 u` as an argument and is never
defaulted to zero. Its a.e. uniqueness is FOU001 (`DGPS/Foundations/WeakSobolev.lean`).
-/

open MeasureTheory
open scoped ContDiff ENNReal

namespace DGPS

/-- The unit flat torus `𝕋^d = ℝ^d/ℤ^d` (DEF001), carrier `Fin d → AddCircle 1`. -/
abbrev Torus (d : ℕ) := SharpLSI.Torus d

/-- Normalized Haar probability measure `m` on `𝕋^d` (DEF001). -/
noncomputable abbrev haar (d : ℕ) : Measure (Torus d) := SharpLSI.haar d

instance haar_isProbabilityMeasure (d : ℕ) : IsProbabilityMeasure (haar d) :=
  SharpLSI.haar_isProbabilityMeasure d

/-- The periodic lift `ℝ^d → 𝕋^d`. -/
abbrev torusLift {d : ℕ} (x : Fin d → ℝ) : Torus d := SharpLSI.liftT x

/-- Haar measure is the image of Lebesgue measure on the unit box `(0,1]^d` under the lift. -/
theorem haar_eq_map_unitBox (d : ℕ) :
    haar d = ((volume : Measure (Fin d → ℝ)).restrict (SharpLSI.unitBox (Fin d))).map
      torusLift :=
  (SharpLSI.measurePreserving_liftT (ι := Fin d)).map_eq.symm

/-! ### Euclidean quotient metric -/

/-- The Euclidean quotient distance on `𝕋^d`. -/
noncomputable def torusDist {d : ℕ} (x y : Torus d) : ℝ := SharpLSI.flatDist x y

/-- Lipschitz with constant `L` for the Euclidean quotient distance. -/
def TorusLipschitzWith {d : ℕ} (L : ℝ) (f : Torus d → ℝ) : Prop :=
  ∀ x y, |f x - f y| ≤ L * torusDist x y

theorem torusDist_comparison {d : ℕ} (x y : Torus d) :
    dist x y ≤ torusDist x y ∧ torusDist x y ≤ Real.sqrt d * dist x y := by
  simpa [torusDist] using SharpLSI.flatDist_comparison x y

theorem torusDist_metric {d : ℕ} :
    (∀ x : Torus d, torusDist x x = 0) ∧
    (∀ x y : Torus d, torusDist x y = torusDist y x) ∧
    (∀ x y z : Torus d, torusDist x z ≤ torusDist x y + torusDist y z) ∧
    (∀ x y : Torus d, torusDist x y = 0 → x = y) ∧
    ∀ x : Torus d, (nhds x).HasBasis (fun ε : ℝ => 0 < ε) (fun ε => {y | torusDist x y < ε}) :=
  SharpLSI.flatDist_metric

private theorem norm_coe_unitAddCircle_le (a : ℝ) : ‖(a : UnitAddCircle)‖ ≤ |a| := by
  rw [UnitAddCircle.norm_eq]
  simpa using round_le a 0

/-- The quotient distance is at most the Euclidean distance of any two lifts. -/
theorem torusDist_liftT_le {d : ℕ} (x y : Fin d → ℝ) :
    torusDist (torusLift x) (torusLift y) ≤ Real.sqrt (∑ j, (x j - y j) ^ 2) := by
  unfold torusDist SharpLSI.flatDist
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun j _ => ?_
  have h : ‖(torusLift x) j - (torusLift y) j‖ ≤ |x j - y j| := by
    simpa [torusLift, SharpLSI.liftT] using norm_coe_unitAddCircle_le (x j - y j)
  calc ‖(torusLift x) j - (torusLift y) j‖ ^ 2 ≤ |x j - y j| ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = (x j - y j) ^ 2 := sq_abs _

/-- Local isometry: for lifts within half a period in each coordinate, the quotient distance
is the Euclidean distance. -/
theorem torusDist_liftT_eq {d : ℕ} {x y : Fin d → ℝ} (h : ∀ j, |x j - y j| ≤ 1 / 2) :
    torusDist (torusLift x) (torusLift y) = Real.sqrt (∑ j, (x j - y j) ^ 2) := by
  unfold torusDist SharpLSI.flatDist
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : ‖((x j - y j : ℝ) : UnitAddCircle)‖ = |x j - y j| :=
    (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).mpr (by simpa using h j)
  have : ‖(torusLift x) j - (torusLift y) j‖ = |x j - y j| := by
    simpa [torusLift, SharpLSI.liftT] using hj
  rw [this, sq_abs]

/-! ### Euclidean tangent norms -/

/-- Tangent vectors at a point of `𝕋^d`, with the Euclidean norm. -/
abbrev Tangent (d : ℕ) := EuclideanSpace ℝ (Fin d)

theorem tangent_norm_sq {d : ℕ} (v : Tangent d) : ‖v‖ ^ 2 = ∑ j, v j ^ 2 :=
  EuclideanSpace.real_norm_sq_eq v

/-- Squared norm of a tangent vector of `(𝕋^d)^N`: the sum over labels of Euclidean squares. -/
noncomputable def particleTangentNormSq {N d : ℕ} (v : Fin N → Tangent d) : ℝ := ∑ i, ‖v i‖ ^ 2

theorem particleTangentNormSq_eq {N d : ℕ} (v : Fin N → Tangent d) :
    particleTangentNormSq v = ∑ i, ∑ j, v i j ^ 2 := by
  simp [particleTangentNormSq, tangent_norm_sq]

/-! ### Smooth periodic tests and weak gradients -/

/-- `φ : 𝕋^d → ℝ` is a smooth periodic function: its periodic lift is `C^∞` on `ℝ^d`. -/
def IsSmoothPeriodic {d : ℕ} (φ : Torus d → ℝ) : Prop := ContDiff ℝ ∞ (φ ∘ torusLift)

/-- The coordinate partial derivative `∂ⱼφ` of a function on `𝕋^d`, computed on the lift at
the representative in `(0,1]^d` (independent of the representative for periodic smooth `φ`). -/
noncomputable def coordPartial {d : ℕ} (j : Fin d) (φ : Torus d → ℝ) (x : Torus d) : ℝ :=
  fderiv ℝ (φ ∘ torusLift) (SharpLSI.secT x) (Pi.single j 1)

/-- `g` is the weak gradient of `u` in `H¹(m)` (DEF001/FOU001): `u ∈ L²(m)`, `g ∈ L²(m; ℝ^d)`,
and `∫ u ∂ⱼφ dm = -∫ gⱼ φ dm` for every smooth periodic real `φ` and every coordinate `j`. -/
structure IsWeakGradient {d : ℕ} (u : Torus d → ℝ) (g : Torus d → Tangent d) : Prop where
  memLp : MemLp u 2 (haar d)
  memLp_grad : MemLp g 2 (haar d)
  ibp : ∀ φ : Torus d → ℝ, IsSmoothPeriodic φ → ∀ j : Fin d,
    ∫ x, u x * coordPartial j φ x ∂haar d = -∫ x, g x j * φ x ∂haar d

/-- `u ∈ H¹(m)`: `u` has an `L²` weak gradient. -/
def MemH1 {d : ℕ} (u : Torus d → ℝ) : Prop := ∃ g, IsWeakGradient u g

/-- The weak gradient of `u ∈ H¹(m)` (DEF001). It requires the membership proof; it is never
defaulted to zero. -/
noncomputable def weakGradient {d : ℕ} (u : Torus d → ℝ) (hu : MemH1 u) : Torus d → Tangent d :=
  hu.choose

theorem isWeakGradient_weakGradient {d : ℕ} {u : Torus d → ℝ} (hu : MemH1 u) :
    IsWeakGradient u (weakGradient u hu) :=
  hu.choose_spec

end DGPS
