import DGPS.Frontier.STR029.T20
import DGPS.Frontier.STR029.T21
import DGPS.Frontier.STR029.T22

/-!
# STR029.23: Three locally unique solution branches

Task STR029.23 of the frontier packet (node STR029, wave 16, verification level V2).

The unit states that, near the three points `((2, 0), s0)` and `((-1, ±√3), s0)` with
`s0 = -16/15`, the slice system `K(h, z)` of the reduced smooth function `E` (STR029.20) has
exactly one zero curve per neighbourhood for small `h`, that the three curves are rotations of
one another, and that they share their third coordinate. The proof applies the implicit-function
box `ift_box_STR02923` (Lemma A, built on the pinned Mathlib smooth implicit-function API) at the
even branch point, takes sup-norm balls around it, and transports the branch to the other two by
the rotation symmetry from STR029.21. The invertible Jacobian at the base point comes from
STR029.22.

## Provides

All names are in the namespace `DGPS.Frontier.STR029`. The main declaration is the unit's
specification. The other declarations are helpers, each carrying the suffix `_STR02923`.

Main declaration:
- `DGPS.Frontier.STR029.str029_23_three_locally_unique_solution_branches`: there is a reduced data
  package from STR029.20 (`U V ψ O E`), a radius `η > 0`, open neighbourhoods `N 0, N 1, N 2`
  of the three points, and curves `Z j` smooth on `(-η, η)` with `Z j h ∈ N j`, such that
  `Kfun E (h, z) = 0 ↔ z = Z j h` for `z ∈ N j`; the curves and sets are rotations of one
  another, and the third coordinate of all three curves is the same.

Constants and planar rotation algebra:
- `DGPS.Frontier.STR029.cos_theta_STR02923`: `cos (2π/3) = -1/2`.
- `DGPS.Frontier.STR029.sin_theta_STR02923`: `sin (2π/3) = √3/2`.
- `DGPS.Frontier.STR029.sqrt3_mul_self_STR02923`: `√3 * √3 = 3`.
- `DGPS.Frontier.STR029.cos_sq_add_sin_sq_STR02923`: `cos² + sin² = 1` at `2π/3`.
- `DGPS.Frontier.STR029.rot_STR02923`: rotation by `2π/3` in the `(z 0, z 1)` plane, `z 2` fixed.
- `DGPS.Frontier.STR029.rotI_STR02923`: inverse rotation, by `-2π/3`.
- `DGPS.Frontier.STR029.rotI_rot_STR02923`: `rotI ∘ rot = id`.
- `DGPS.Frontier.STR029.rot_rotI_STR02923`: `rot ∘ rotI = id`.
- `DGPS.Frontier.STR029.rot_add_STR02923`: `rot` is additive.
- `DGPS.Frontier.STR029.rot_smul_STR02923`: `rot` is homogeneous.
- `DGPS.Frontier.STR029.rotLM_STR02923`: `rot` as a linear map.
- `DGPS.Frontier.STR029.rotCLM_STR02923`: `rot` as a continuous linear map.
- `DGPS.Frontier.STR029.rotCLM_apply_STR02923`: `rotCLM` applied equals `rot`.
- `DGPS.Frontier.STR029.rot_zero_STR02923`: `rot 0 = 0`.
- `DGPS.Frontier.STR029.rot_injective_STR02923`: `rot` is injective.
- `DGPS.Frontier.STR029.rot_single0_STR02923`: value of `rot` on the first basis vector.
- `DGPS.Frontier.STR029.rot_single1_STR02923`: value of `rot` on the second basis vector.
- `DGPS.Frontier.STR029.sumsq_rot_STR02923`: `rot` preserves `A² + B²`.
- `DGPS.Frontier.STR029.Jred_rot_STR02923`: `Jred` is invariant under the planar rotation.
- `DGPS.Frontier.STR029.closed_rot_STR02923`: the closed-form zero-field function is invariant.
- `DGPS.Frontier.STR029.rot_cube_STR02923`: `rot³ = id`.
- `DGPS.Frontier.STR029.rot0_STR02923`: first coordinate of `rot`, explicit.
- `DGPS.Frontier.STR029.rot1_STR02923`: second coordinate of `rot`, explicit.
- `DGPS.Frontier.STR029.rot2_STR02923`: third coordinate of `rot` is unchanged.
- `DGPS.Frontier.STR029.rot_continuous_STR02923`: `rot` is continuous.
- `DGPS.Frontier.STR029.dist_rot_le_STR02923`: `rot` is 2-Lipschitz (sup metric).
- `DGPS.Frontier.STR029.dist_rotrot_le_STR02923`: `rot ∘ rot` is 4-Lipschitz.
- `DGPS.Frontier.STR029.image_rot_eq_STR02923`: `rot '' A = (rot ∘ rot) ⁻¹' A`.
- `DGPS.Frontier.STR029.isOpen_image_rot_STR02923`: the image of an open set under `rot` is open.
- `DGPS.Frontier.STR029.disjoint_image_rot_STR02923`: `rot` preserves disjointness of images.
- `DGPS.Frontier.STR029.rotP0_STR02923`: `rot P0 = (-1, √3, s0)`.
- `DGPS.Frontier.STR029.rotrotP0_STR02923`: `rot (rot P0) = (-1, -√3, s0)`.
- `DGPS.Frontier.STR029.three_le_dist_P0_rot_STR02923`: `dist P0 (rot P0) ≥ 3`.
- `DGPS.Frontier.STR029.three_le_dist_P0_rotrot_STR02923`: `dist P0 (rot (rot P0)) ≥ 3`.
- `DGPS.Frontier.STR029.disjoint_ball_rot_STR02923`: `ball P0 ρ` and its `rot`-image are disjoint
  for `ρ ≤ 1/2`.
- `DGPS.Frontier.STR029.disjoint_ball_rotrot_STR02923`: the same for the `rot ∘ rot`-image.
- `DGPS.Frontier.STR029.refl_mem_ball_STR02923`: `ball P0 ρ` is invariant under `(A, B, s) ↦ (A, -B, s)`.

Parameter map and carriers:
- `DGPS.Frontier.STR029.ptPar_STR02923`: `(h, z) ↦ (h z0, h z1, h, h² z2)` into `Par_STR02916`.
- `DGPS.Frontier.STR029.ptPar_rot_STR02923`: `ptPar` intertwines `rot` with the parameter rotation.
- `DGPS.Frontier.STR029.ptPar_zero_STR02923`: `ptPar 0 z = 0`.
- `DGPS.Frontier.STR029.continuous_ptPar_STR02923`: `(h, z) ↦ ptPar h z` is continuous.
- `DGPS.Frontier.STR029.rot_hasFDerivAt_STR02923`: the derivative of `rot` is `rotCLM`.
- `DGPS.Frontier.STR029.rot_contDiff_STR02923`: `rot` is `C^∞`.
- `DGPS.Frontier.STR029.Wset_STR02923`: `U1 ∩ ψ1⁻¹' V2 ∩ U2`, the parameter set where both graphs
  are defined and agree.
- `DGPS.Frontier.STR029.Qset_STR02923`: `O ∩ ptPar⁻¹' W`.
- `DGPS.Frontier.STR029.Gset_STR02923`: the points of `Qset` whose `rot` and `rot²` images also lie
  in `Qset`.
- `DGPS.Frontier.STR029.isOpen_Qset_STR02923`: `Qset` is open when `O` and `W` are.
- `DGPS.Frontier.STR029.isOpen_Gset_STR02923`: `Gset` is open when `O` and `W` are.
- `DGPS.Frontier.STR029.psi_agree_STR02923`: two characterised graph functions agree on the overlap.
- `DGPS.Frontier.STR029.Fgraph_agree_STR02923`: the graph functions of STR029.20 and STR029.21
  agree on the overlap.
- `DGPS.Frontier.STR029.rot_core_STR02923`: inversion of a planar rotation.
- `DGPS.Frontier.STR029.fderiv_rot_STR02923`: equivariance of the derivative of a `rot`-invariant
  function.
- `DGPS.Frontier.STR029.Kfun_rot_STR02923`: `Kfun` is equivariant under `rot` on an open invariant
  set where `E` is invariant.
- `DGPS.Frontier.STR029.E_rot_STR02923`: local `rot`-invariance of `E` on `Gset`, from the graph
  equivariance of STR029.21.
- `DGPS.Frontier.STR029.fderiv_slice_STR02923`: the `z`-derivative of the slice `E (h, ·)` is the
  derivative of `E` in the `(0, v)` direction.
- `DGPS.Frontier.STR029.diffAt_STR02923`: a `C^∞` function on an open set is differentiable there.
- `DGPS.Frontier.STR029.contDiffOn_Kfun_STR02923`: `Kfun E` is `C^∞` on an open set where `E` is.
- `DGPS.Frontier.STR029.Mz_STR02923`: the `z`-derivative of `Kfun E` at `p`, as a continuous linear
  map.
- `DGPS.Frontier.STR029.continuousAt_det_STR02923`: the determinant of the `z`-derivative is
  continuous.
- `DGPS.Frontier.STR029.isInvertible_of_det_STR02923`: nonzero determinant implies invertibility.
- `DGPS.Frontier.STR029.Mz_slice_STR02923`: on `z`-slices, the derivative of `Kmap` (STR029.22)
  equals `Mz` at `(0, z)`.
- `DGPS.Frontier.STR029.det_Mz_STR02923`: the determinant of `Mz E (0, P0)` equals `-1/2`, computed
  from the closed form of `E (0, ·)` and the STR029.22 Jacobian.

Implicit-function and branch machinery:
- `DGPS.Frontier.STR029.ift_box_STR02923`: Lemma A. Near a zero `u` of a `C^∞` map `K` with
  invertible `z`-derivative, there are a graph function `g`, a radius `r > 0`, and the zero set of
  `K` in the ball of radius `r` equals the graph of `g`; `g` is `C^∞` where its graph stays in
  the ball.
- `DGPS.Frontier.STR029.mem_Gset_iff_STR02923`: membership in `Gset` unfolded into six conditions.
- `DGPS.Frontier.STR029.mem_O_of_Gset_STR02923`: `Gset` is contained in `O`.
- `DGPS.Frontier.STR029.zero_mem_Gset_STR02923`: `(0, z) ∈ Gset` for all `z`, given `W ∋ 0` and
  `O ⊇ {0} × ℝ³`.
- `DGPS.Frontier.STR029.Gset_rot_STR02923`: `Gset` is invariant under `rot` in the `z` variable.
- `DGPS.Frontier.STR029.rot_eq_iff_STR02923`: `rot x = rot y ↔ x = y`.
- `DGPS.Frontier.STR029.rot_eq_zero_iff_STR02923`: `rot x = 0 ↔ x = 0`.
- `DGPS.Frontier.STR029.branches_STR02923`: the three-branch statement for a general `E` and `W`,
  from `ift_box_STR02923`, rotation invariance on `Gset`, and the base-point Jacobian.

## R5 notes

Hypotheses and domains.
- The frozen statement has no hypotheses. Its existential quantifies over the reduced data
  package `U V ψ O E`, which the proof takes from STR029.20, STR029.21 and STR029.22 through the
  pinned names listed in the imports. Nothing is added.
- The statement says only that the zero set of `K` has the stated form. It does not say that the
  curves are the LSI minimisers; that identification belongs to other units.
- `h` ranges over the open interval `(-η, η)`, which contains `h = 0`. The formula for `E` at
  `h ≠ 0` enters only through `E_rot_STR02923`, where it transfers the rotation equivariance of
  STR029.21 to `E`. The closed form of `E (0, ·)` and the smoothness of `E` on the open set `O`
  are used directly.

Readings of the specification.
- `K(h, z)` is read as `Kfun E (h, z)`: the two angular partial derivatives of `E (h, ·)` at `z`,
  together with the value `E (h, z)`. The third component is the value, so the zero set requires
  `E (h, z) = 0` as well. The specification does not define `K` in the text we were given; this
  is the same slice system as `Kmap` in STR029.22.
- The neighbourhoods `N j` are open subsets of the `z`-space `Fin 3 → ℝ` that do not depend on
  `h`. The base points are `(2, 0, s0)`, `(-1, √3, s0)`, `(-1, -√3, s0)` with `s0 = -16/15`,
  read in the coordinates `(A, B, s)` of the scaled variables. `N 0` is a sup-norm ball
  around `(2, 0, s0)`.
- "Reflection invariant" for `N 0` is read as invariance under `(A, B, s) ↦ (A, -B, s)`, the
  symmetry `t ↦ -t` of the even branch. The specification does not name the reflection.
- The rotations `x ↦ x + j/3` on densities are read as rotation by `2πj/3` in the angular
  variable `t = 2πx`, that is, by `2π/3` in `(A, B)` with `s` fixed.
- The parameter map `ptPar h z = (h z0, h z1, h, h² z2)` encodes `a = h z0`, `b = h z1`,
  `γ = h² z2`, and `z2 = s = γ/h²`. This is the scaled-variable identification of STR029.20 and
  STR029.21, taken from their statements and not re-verified against STR029.01.
- "Smooth curves" means `ContDiffOn ℝ ∞` on the open interval `(-η, η)`. Nothing is claimed at
  the endpoints.
- The three curves are `g`, `rot ∘ g` and `rot ∘ rot ∘ g`, where `g` is the graph function of
  `ift_box_STR02923` at the base point. The curves share the third coordinate by `rot2_STR02923`.
- The specification asks for disjoint neighbourhoods. Disjointness comes from the balls of radius
  `ρ ≤ 1/2` and the distance bound `≥ 3` from `P0` to its rotated images.

Design choices and limits of the rotation argument.
- Rotation invariance of `E` is used only on `Gset_STR02923 O W`, where `(h, z)`, `(h, rot z)` and
  `(h, rot² z)` all lie in the common graph domain `W = Wset_STR02923 U U2 V2 ψ`. The
  equivariance of STR029.21 is therefore used in local form, not globally. This is the
  hypothesis `hinv` of `branches_STR02923`.
- The determinant `det (Mz E (0, P0)) ≠ 0` is computed once, from the closed form of `E (0, ·)`,
  and then carried to the neighbourhoods by the implicit-function box. The other two branches are
  obtained by rotation, not by a separate computation.
- A single `η` serves all three branches. It is chosen so that `g` maps `(-η, η)` into the ball of
  radius `ρ`, and so that the points `(h, g h)` stay in the implicit-function box; the three
  parameter intervals therefore coincide.
- Lemma A (`ift_box_STR02923`) packages the pinned smooth implicit-function declarations
  `ContDiffAt.implicitFunction` and `ContDiffAt.contDiffAt_implicitFunction`. These are used as
  library API, with no new hypothesis and no extra assumption.
-/

open scoped ContDiff
open Topology

namespace DGPS.Frontier.STR029

theorem cos_theta_STR02923 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

theorem sin_theta_STR02923 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.sin_pi_sub, Real.sin_pi_div_three]

theorem sqrt3_mul_self_STR02923 : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

theorem cos_sq_add_sin_sq_STR02923 :
    Real.cos (2 * Real.pi / 3) ^ 2 + Real.sin (2 * Real.pi / 3) ^ 2 = 1 :=
  Real.cos_sq_add_sin_sq _

/-- The rotation `(A, B, s) ↦ (A cos θ - B sin θ, A sin θ + B cos θ, s)` with `θ = 2π/3`. -/
noncomputable def rot_STR02923 (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![z 0 * Real.cos (2 * Real.pi / 3) - z 1 * Real.sin (2 * Real.pi / 3),
    z 0 * Real.sin (2 * Real.pi / 3) + z 1 * Real.cos (2 * Real.pi / 3), z 2]

/-- The inverse rotation, by `-2π/3`. -/
noncomputable def rotI_STR02923 (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![z 0 * Real.cos (2 * Real.pi / 3) + z 1 * Real.sin (2 * Real.pi / 3),
    -(z 0 * Real.sin (2 * Real.pi / 3)) + z 1 * Real.cos (2 * Real.pi / 3), z 2]

theorem rotI_rot_STR02923 (z : Fin 3 → ℝ) : rotI_STR02923 (rot_STR02923 z) = z := by
  have h := cos_sq_add_sin_sq_STR02923
  funext i
  fin_cases i
  · simp [rot_STR02923, rotI_STR02923]
    linear_combination (z 0) * h
  · simp [rot_STR02923, rotI_STR02923]
    linear_combination (z 1) * h
  · simp [rot_STR02923, rotI_STR02923]

theorem rot_rotI_STR02923 (z : Fin 3 → ℝ) : rot_STR02923 (rotI_STR02923 z) = z := by
  have h := cos_sq_add_sin_sq_STR02923
  funext i
  fin_cases i
  · simp [rot_STR02923, rotI_STR02923]
    linear_combination (z 0) * h
  · simp [rot_STR02923, rotI_STR02923]
    linear_combination (z 1) * h
  · simp [rot_STR02923, rotI_STR02923]

theorem rot_add_STR02923 (x y : Fin 3 → ℝ) :
    rot_STR02923 (x + y) = rot_STR02923 x + rot_STR02923 y := by
  funext i
  fin_cases i <;> simp [rot_STR02923] <;> ring

theorem rot_smul_STR02923 (a : ℝ) (x : Fin 3 → ℝ) :
    rot_STR02923 (a • x) = a • rot_STR02923 x := by
  funext i
  fin_cases i <;> simp [rot_STR02923] <;> ring

/-- The rotation as a linear map. -/
noncomputable def rotLM_STR02923 : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun := rot_STR02923
  map_add' := rot_add_STR02923
  map_smul' := rot_smul_STR02923

/-- The rotation as a continuous linear map. -/
noncomputable def rotCLM_STR02923 : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap rotLM_STR02923

theorem rotCLM_apply_STR02923 (z : Fin 3 → ℝ) : rotCLM_STR02923 z = rot_STR02923 z := rfl

theorem rot_zero_STR02923 : rot_STR02923 0 = 0 := by
  funext i
  fin_cases i <;> simp [rot_STR02923]

theorem rot_injective_STR02923 {x y : Fin 3 → ℝ} (h : rot_STR02923 x = rot_STR02923 y) :
    x = y := by
  have := congrArg rotI_STR02923 h
  rwa [rotI_rot_STR02923, rotI_rot_STR02923] at this

theorem rot_single0_STR02923 :
    rot_STR02923 (Pi.single 0 1) =
      Real.cos (2 * Real.pi / 3) • (Pi.single 0 1 : Fin 3 → ℝ) +
        Real.sin (2 * Real.pi / 3) • (Pi.single 1 1 : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;> simp [rot_STR02923]

theorem rot_single1_STR02923 :
    rot_STR02923 (Pi.single 1 1) =
      (-Real.sin (2 * Real.pi / 3)) • (Pi.single 0 1 : Fin 3 → ℝ) +
        Real.cos (2 * Real.pi / 3) • (Pi.single 1 1 : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;> simp [rot_STR02923]

/-- The sum of squares is invariant under the rotation. -/
theorem sumsq_rot_STR02923 (A B : ℝ) :
    (A * Real.cos (2 * Real.pi / 3) - B * Real.sin (2 * Real.pi / 3)) ^ 2 +
      (A * Real.sin (2 * Real.pi / 3) + B * Real.cos (2 * Real.pi / 3)) ^ 2 = A ^ 2 + B ^ 2 := by
  linear_combination (A ^ 2 + B ^ 2) * cos_sq_add_sin_sq_STR02923

/-- The reduced constant `J_4^red` is invariant under the rotation. -/
theorem Jred_rot_STR02923 (A B : ℝ) :
    Jred_STR02918 (A * Real.cos (2 * Real.pi / 3) - B * Real.sin (2 * Real.pi / 3))
        (A * Real.sin (2 * Real.pi / 3) + B * Real.cos (2 * Real.pi / 3)) =
      Jred_STR02918 A B := by
  rw [cos_theta_STR02923, sin_theta_STR02923, Jred_eq_STR02918, Jred_eq_STR02918]
  have hq : (A * (-1 / 2) - B * (Real.sqrt 3 / 2)) ^ 2 +
      (A * (Real.sqrt 3 / 2) + B * (-1 / 2)) ^ 2 = A ^ 2 + B ^ 2 := by
    linear_combination ((A ^ 2 + B ^ 2) / 4) * sqrt3_mul_self_STR02923
  have hp : (A * (-1 / 2) - B * (Real.sqrt 3 / 2)) ^ 3 -
      3 * (A * (-1 / 2) - B * (Real.sqrt 3 / 2)) * (A * (Real.sqrt 3 / 2) + B * (-1 / 2)) ^ 2 =
      A ^ 3 - 3 * A * B ^ 2 := by
    linear_combination (3 * (A ^ 3 - 3 * A * B ^ 2) / 8 +
      Real.sqrt 3 * (3 * A ^ 2 * B - B ^ 3) / 8) * sqrt3_mul_self_STR02923
  rw [hq, hp]

/-- The closed form `z ↦ J_4^red(z_0, z_1) - z_2 (z_0² + z_1²)/2` is invariant under the rotation. -/
theorem closed_rot_STR02923 (z : Fin 3 → ℝ) :
    Jred_STR02918 (rot_STR02923 z 0) (rot_STR02923 z 1) -
        rot_STR02923 z 2 * ((rot_STR02923 z 0 ^ 2 + rot_STR02923 z 1 ^ 2) / 2) =
      Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2) := by
  have h0 : rot_STR02923 z 0 = z 0 * Real.cos (2 * Real.pi / 3) - z 1 * Real.sin (2 * Real.pi / 3) :=
    rfl
  have h1 : rot_STR02923 z 1 = z 0 * Real.sin (2 * Real.pi / 3) + z 1 * Real.cos (2 * Real.pi / 3) :=
    rfl
  have h2 : rot_STR02923 z 2 = z 2 := rfl
  rw [h0, h1, h2, Jred_rot_STR02923, sumsq_rot_STR02923 (z 0) (z 1)]

/-- Three applications of the rotation are the identity. -/
theorem rot_cube_STR02923 (z : Fin 3 → ℝ) :
    rot_STR02923 (rot_STR02923 (rot_STR02923 z)) = z := by
  have ht := sqrt3_mul_self_STR02923
  funext i
  fin_cases i
  · simp only [rot_STR02923, cos_theta_STR02923, sin_theta_STR02923]
    simp
    linear_combination ((3 * z 0 + Real.sqrt 3 * z 1) / 8) * ht
  · simp only [rot_STR02923, cos_theta_STR02923, sin_theta_STR02923]
    simp
    linear_combination ((3 * z 1 - Real.sqrt 3 * z 0) / 8) * ht
  · simp [rot_STR02923]

/-- The slice system `K(h, z)`: the two partial derivatives of `E(h, ·)` at `z` in the
directions `e₀`, `e₁`, and the value `E(h, z)`. -/
noncomputable def Kfun_STR02923 (E : ℝ × (Fin 3 → ℝ) → ℝ) (p : ℝ × (Fin 3 → ℝ)) : Fin 3 → ℝ :=
  ![fderiv ℝ (fun w : Fin 3 → ℝ => E (p.1, w)) p.2 (Pi.single 0 1),
    fderiv ℝ (fun w : Fin 3 → ℝ => E (p.1, w)) p.2 (Pi.single 1 1), E p]

theorem rot0_STR02923 (z : Fin 3 → ℝ) :
    rot_STR02923 z 0 = z 0 * (-1 / 2) - z 1 * (Real.sqrt 3 / 2) := by
  simp [rot_STR02923, cos_theta_STR02923, sin_theta_STR02923]

theorem rot1_STR02923 (z : Fin 3 → ℝ) :
    rot_STR02923 z 1 = z 0 * (Real.sqrt 3 / 2) + z 1 * (-1 / 2) := by
  simp [rot_STR02923, cos_theta_STR02923, sin_theta_STR02923]

theorem rot2_STR02923 (z : Fin 3 → ℝ) : rot_STR02923 z 2 = z 2 := rfl

theorem rot_continuous_STR02923 : Continuous rot_STR02923 := by
  have h : rot_STR02923 = rotCLM_STR02923 := funext fun z => rfl
  rw [h]
  exact rotCLM_STR02923.continuous

/-- The rotation is `2`-Lipschitz in the sup norm. -/
theorem dist_rot_le_STR02923 (x y : Fin 3 → ℝ) :
    dist (rot_STR02923 x) (rot_STR02923 y) ≤ 2 * dist x y := by
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs2 : Real.sqrt 3 ≤ 2 := by nlinarith [sqrt3_mul_self_STR02923]
  have hdn : 0 ≤ dist x y := dist_nonneg
  have hq0 : |x 0 - y 0| ≤ dist x y := by
    rw [← Real.dist_eq]; exact dist_le_pi_dist x y 0
  have hq1 : |x 1 - y 1| ≤ dist x y := by
    rw [← Real.dist_eq]; exact dist_le_pi_dist x y 1
  have hq0' := abs_le.1 hq0
  have hq1' := abs_le.1 hq1
  have hA0 := mul_nonneg (show 0 ≤ x 0 - y 0 + dist x y by linarith) hs0
  have hB0 := mul_nonneg (show 0 ≤ dist x y - (x 0 - y 0) by linarith) hs0
  have hA1 := mul_nonneg (show 0 ≤ x 1 - y 1 + dist x y by linarith) hs0
  have hB1 := mul_nonneg (show 0 ≤ dist x y - (x 1 - y 1) by linarith) hs0
  have hC := mul_nonneg (show 0 ≤ 2 - Real.sqrt 3 by linarith) hdn
  rw [dist_pi_le_iff (by positivity)]
  intro i
  fin_cases i
  · show dist (rot_STR02923 x 0) (rot_STR02923 y 0) ≤ 2 * dist x y
    rw [rot0_STR02923, rot0_STR02923, Real.dist_eq, abs_le]
    constructor <;> nlinarith
  · show dist (rot_STR02923 x 1) (rot_STR02923 y 1) ≤ 2 * dist x y
    rw [rot1_STR02923, rot1_STR02923, Real.dist_eq, abs_le]
    constructor <;> nlinarith
  · show dist (rot_STR02923 x 2) (rot_STR02923 y 2) ≤ 2 * dist x y
    rw [rot2_STR02923, rot2_STR02923]
    exact (dist_le_pi_dist x y 2).trans (by linarith)

theorem dist_rotrot_le_STR02923 (x y : Fin 3 → ℝ) :
    dist (rot_STR02923 (rot_STR02923 x)) (rot_STR02923 (rot_STR02923 y)) ≤ 4 * dist x y := by
  have h1 := dist_rot_le_STR02923 (rot_STR02923 x) (rot_STR02923 y)
  have h2 := dist_rot_le_STR02923 x y
  linarith

theorem image_rot_eq_STR02923 (A : Set (Fin 3 → ℝ)) :
    rot_STR02923 '' A = (fun z => rot_STR02923 (rot_STR02923 z)) ⁻¹' A := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    show rot_STR02923 (rot_STR02923 (rot_STR02923 w)) ∈ A
    rw [rot_cube_STR02923]
    exact hw
  · intro hz
    exact ⟨rot_STR02923 (rot_STR02923 z), hz, rot_cube_STR02923 z⟩

theorem isOpen_image_rot_STR02923 {A : Set (Fin 3 → ℝ)} (hA : IsOpen A) :
    IsOpen (rot_STR02923 '' A) := by
  rw [image_rot_eq_STR02923]
  exact hA.preimage (rot_continuous_STR02923.comp rot_continuous_STR02923)

theorem disjoint_image_rot_STR02923 {A B : Set (Fin 3 → ℝ)} (h : Disjoint A B) :
    Disjoint (rot_STR02923 '' A) (rot_STR02923 '' B) :=
  (Set.disjoint_image_iff (fun _ _ hxy => rot_injective_STR02923 hxy)).2 h

theorem rotP0_STR02923 :
    rot_STR02923 (![2, 0, -16 / 15] : Fin 3 → ℝ) = ![-1, Real.sqrt 3, -16 / 15] := by
  funext i
  fin_cases i
  · norm_num [rot0_STR02923]
  · norm_num [rot1_STR02923]
    ring
  · norm_num [rot2_STR02923]

theorem rotrotP0_STR02923 :
    rot_STR02923 (rot_STR02923 (![2, 0, -16 / 15] : Fin 3 → ℝ)) =
      ![-1, -Real.sqrt 3, -16 / 15] := by
  have ht := sqrt3_mul_self_STR02923
  have e0 : rot_STR02923 (![-1, Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) 0 = -1 := by
    rw [rot0_STR02923]; simp; linear_combination (-1 / 2 : ℝ) * ht
  have e1 : rot_STR02923 (![-1, Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) 1 = -Real.sqrt 3 := by
    rw [rot1_STR02923]; simp; ring
  have e2 : rot_STR02923 (![-1, Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) 2 = -16 / 15 := by
    rw [rot2_STR02923]; simp
  rw [rotP0_STR02923]
  funext i
  fin_cases i <;> simp [e0, e1, e2]

theorem three_le_dist_P0_rot_STR02923 :
    (3 : ℝ) ≤ dist (![2, 0, -16 / 15] : Fin 3 → ℝ) (rot_STR02923 (![2, 0, -16 / 15])) := by
  have h := dist_le_pi_dist (![2, 0, -16 / 15] : Fin 3 → ℝ)
    (rot_STR02923 (![2, 0, -16 / 15])) 0
  rw [rotP0_STR02923] at h ⊢
  have h2 : dist ((![2, 0, -16 / 15] : Fin 3 → ℝ) 0)
      ((![-1, Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) 0) = 3 := by
    norm_num [Real.dist_eq]
  linarith

theorem three_le_dist_P0_rotrot_STR02923 :
    (3 : ℝ) ≤ dist (![2, 0, -16 / 15] : Fin 3 → ℝ)
      (rot_STR02923 (rot_STR02923 (![2, 0, -16 / 15]))) := by
  have h := dist_le_pi_dist (![2, 0, -16 / 15] : Fin 3 → ℝ)
    (rot_STR02923 (rot_STR02923 (![2, 0, -16 / 15]))) 0
  rw [rotrotP0_STR02923] at h ⊢
  have h2 : dist ((![2, 0, -16 / 15] : Fin 3 → ℝ) 0)
      ((![-1, -Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) 0) = 3 := by
    norm_num [Real.dist_eq]
  linarith

theorem disjoint_ball_rot_STR02923 {ρ : ℝ} (hρ : ρ ≤ 1 / 2) :
    Disjoint (Metric.ball (![2, 0, -16 / 15] : Fin 3 → ℝ) ρ)
      (rot_STR02923 '' Metric.ball (![2, 0, -16 / 15] : Fin 3 → ℝ) ρ) := by
  refine Set.disjoint_left.2 fun z hz hz' => ?_
  obtain ⟨w, hw, rfl⟩ := hz'
  have h1 := Metric.mem_ball.1 hz
  have h2 := Metric.mem_ball.1 hw
  have h3 := dist_rot_le_STR02923 w (![2, 0, -16 / 15] : Fin 3 → ℝ)
  have h4 := dist_triangle (![2, 0, -16 / 15] : Fin 3 → ℝ) (rot_STR02923 w)
    (rot_STR02923 (![2, 0, -16 / 15]))
  have h5 := dist_comm (![2, 0, -16 / 15] : Fin 3 → ℝ) (rot_STR02923 w)
  linarith [three_le_dist_P0_rot_STR02923]

theorem disjoint_ball_rotrot_STR02923 {ρ : ℝ} (hρ : ρ ≤ 1 / 2) :
    Disjoint (Metric.ball (![2, 0, -16 / 15] : Fin 3 → ℝ) ρ)
      (rot_STR02923 '' (rot_STR02923 '' Metric.ball (![2, 0, -16 / 15] : Fin 3 → ℝ) ρ)) := by
  refine Set.disjoint_left.2 fun z hz hz' => ?_
  obtain ⟨v, ⟨w, hw, rfl⟩, rfl⟩ := hz'
  have h1 := Metric.mem_ball.1 hz
  have h2 := Metric.mem_ball.1 hw
  have h3 := dist_rotrot_le_STR02923 w (![2, 0, -16 / 15] : Fin 3 → ℝ)
  have h4 := dist_triangle (![2, 0, -16 / 15] : Fin 3 → ℝ)
    (rot_STR02923 (rot_STR02923 w)) (rot_STR02923 (rot_STR02923 (![2, 0, -16 / 15])))
  have h5 := dist_comm (![2, 0, -16 / 15] : Fin 3 → ℝ) (rot_STR02923 (rot_STR02923 w))
  linarith [three_le_dist_P0_rotrot_STR02923]

theorem refl_mem_ball_STR02923 {ρ : ℝ} (hρ : 0 < ρ) (z : Fin 3 → ℝ) :
    (![z 0, -z 1, z 2] : Fin 3 → ℝ) ∈ Metric.ball (![2, 0, -16 / 15] : Fin 3 → ℝ) ρ ↔
      z ∈ Metric.ball (![2, 0, -16 / 15] : Fin 3 → ℝ) ρ := by
  have key : ∀ i : Fin 3, dist ((![z 0, -z 1, z 2] : Fin 3 → ℝ) i)
      ((![2, 0, -16 / 15] : Fin 3 → ℝ) i) =
        dist (z i) ((![2, 0, -16 / 15] : Fin 3 → ℝ) i) := by
    intro i
    fin_cases i <;> simp [Real.dist_eq]
  simp only [Metric.mem_ball, dist_pi_lt_iff hρ, key]

/-! ### Parameter points, the regions, and the rotation equivariance -/

/-- The parameter point `(h z₀, h z₁, h, h² z₂)` attached to `(h, z)`. -/
noncomputable def ptPar_STR02923 (h : ℝ) (z : Fin 3 → ℝ) : Par_STR02916 :=
  (h * z 0, h * z 1, h, h ^ 2 * z 2)

theorem ptPar_rot_STR02923 (h : ℝ) (z : Fin 3 → ℝ) :
    ptPar_STR02923 h (rot_STR02923 z) =
      rotPar_STR02916 (2 * Real.pi / 3) (ptPar_STR02923 h z) := by
  have e0 : rot_STR02923 z 0 =
      z 0 * Real.cos (2 * Real.pi / 3) - z 1 * Real.sin (2 * Real.pi / 3) := rfl
  have e1 : rot_STR02923 z 1 =
      z 0 * Real.sin (2 * Real.pi / 3) + z 1 * Real.cos (2 * Real.pi / 3) := rfl
  have e2 : rot_STR02923 z 2 = z 2 := rfl
  unfold ptPar_STR02923 rotPar_STR02916
  rw [e0, e1, e2]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext rfl rfl))
  · dsimp only; ring
  · dsimp only; ring

theorem ptPar_zero_STR02923 (z : Fin 3 → ℝ) : ptPar_STR02923 0 z = 0 := by
  simp [ptPar_STR02923]

theorem continuous_ptPar_STR02923 :
    Continuous (fun p : ℝ × (Fin 3 → ℝ) => ptPar_STR02923 p.1 p.2) := by
  unfold ptPar_STR02923
  fun_prop

theorem rot_hasFDerivAt_STR02923 (z : Fin 3 → ℝ) :
    HasFDerivAt rot_STR02923 rotCLM_STR02923 z := by
  have h : rot_STR02923 = ⇑rotCLM_STR02923 := funext fun _ => rfl
  rw [h]
  exact rotCLM_STR02923.hasFDerivAt

theorem rot_contDiff_STR02923 : ContDiff ℝ ∞ rot_STR02923 := by
  have h : rot_STR02923 = ⇑rotCLM_STR02923 := funext fun _ => rfl
  rw [h]
  exact rotCLM_STR02923.contDiff

/-- The parameter points where the graph functions of STR029.20 and STR029.21 are both defined
and agree with the characterising zero set. -/
def Wset_STR02923 (U1 U2 : Set Par_STR02916) (V2 : Set E_STR02969)
    (ψ1 : Par_STR02916 → E_STR02969) : Set Par_STR02916 :=
  U1 ∩ ψ1 ⁻¹' V2 ∩ U2

/-- The set of `(h, z)` in `O` whose parameter point `(h z₀, h z₁, h, h² z₂)` lies in `W`. -/
def Qset_STR02923 (O : Set (ℝ × (Fin 3 → ℝ))) (W : Set Par_STR02916) :
    Set (ℝ × (Fin 3 → ℝ)) :=
  O ∩ (fun p : ℝ × (Fin 3 → ℝ) => ptPar_STR02923 p.1 p.2) ⁻¹' W

/-- The set of `(h, z)` such that `(h, z)`, `(h, rot z)` and `(h, rot² z)` all lie in `Qset`. -/
def Gset_STR02923 (O : Set (ℝ × (Fin 3 → ℝ))) (W : Set Par_STR02916) :
    Set (ℝ × (Fin 3 → ℝ)) :=
  Qset_STR02923 O W ∩
      (fun p : ℝ × (Fin 3 → ℝ) => (p.1, rot_STR02923 p.2)) ⁻¹' Qset_STR02923 O W ∩
    (fun p : ℝ × (Fin 3 → ℝ) => (p.1, rot_STR02923 (rot_STR02923 p.2))) ⁻¹' Qset_STR02923 O W

theorem isOpen_Qset_STR02923 {O : Set (ℝ × (Fin 3 → ℝ))} {W : Set Par_STR02916}
    (hO : IsOpen O) (hW : IsOpen W) : IsOpen (Qset_STR02923 O W) :=
  hO.inter (hW.preimage continuous_ptPar_STR02923)

theorem isOpen_Gset_STR02923 {O : Set (ℝ × (Fin 3 → ℝ))} {W : Set Par_STR02916}
    (hO : IsOpen O) (hW : IsOpen W) : IsOpen (Gset_STR02923 O W) := by
  have hQ := isOpen_Qset_STR02923 hO hW
  have c1 : Continuous (fun p : ℝ × (Fin 3 → ℝ) => (p.1, rot_STR02923 p.2)) :=
    continuous_fst.prodMk (rot_continuous_STR02923.comp continuous_snd)
  have c2 : Continuous (fun p : ℝ × (Fin 3 → ℝ) => (p.1, rot_STR02923 (rot_STR02923 p.2))) :=
    continuous_fst.prodMk
      ((rot_continuous_STR02923.comp rot_continuous_STR02923).comp continuous_snd)
  exact (hQ.inter (hQ.preimage c1)).inter (hQ.preimage c2)

/-- On the set where the two graph functions have the same zero-set characterisation, they agree. -/
theorem psi_agree_STR02923 {U1 U2 : Set Par_STR02916} {V1 V2 : Set E_STR02969}
    {ψ1 ψ2 : Par_STR02916 → E_STR02969}
    (hψ1V : ∀ p ∈ U1, ψ1 p ∈ V1)
    (hiff1 : ∀ p ∈ U1, ∀ w ∈ V1, Rpar_STR02916 p w = 0 ↔ w = ψ1 p)
    (hiff2 : ∀ p ∈ U2, ∀ w ∈ V2, Rpar_STR02916 p w = 0 ↔ w = ψ2 p)
    {p : Par_STR02916} (hp1 : p ∈ U1) (hp1' : ψ1 p ∈ V2) (hp2 : p ∈ U2) :
    ψ1 p = ψ2 p :=
  (hiff2 p hp2 (ψ1 p) hp1').1 ((hiff1 p hp1 (ψ1 p) (hψ1V p hp1)).2 rfl)

theorem Fgraph_agree_STR02923 {U1 U2 : Set Par_STR02916} {V1 V2 : Set E_STR02969}
    {ψ1 ψ2 : Par_STR02916 → E_STR02969}
    (hψ1V : ∀ p ∈ U1, ψ1 p ∈ V1)
    (hiff1 : ∀ p ∈ U1, ∀ w ∈ V1, Rpar_STR02916 p w = 0 ↔ w = ψ1 p)
    (hiff2 : ∀ p ∈ U2, ∀ w ∈ V2, Rpar_STR02916 p w = 0 ↔ w = ψ2 p)
    {p : Par_STR02916} (hp1 : p ∈ U1) (hp1' : ψ1 p ∈ V2) (hp2 : p ∈ U2) :
    Fgraph_STR02921 ψ1 p = Fgraph_STR02921 ψ2 p := by
  unfold Fgraph_STR02921
  rw [psi_agree_STR02923 hψ1V hiff1 hiff2 hp1 hp1' hp2]

theorem rot_core_STR02923 (c s a b a' b' : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (ha : a = c * a' + s * b') (hb : b = -s * a' + c * b') :
    a' = a * c - b * s ∧ b' = a * s + b * c := by
  constructor
  · linear_combination (-c) * ha + s * hb + (-a') * hcs
  · linear_combination (-s) * ha + (-c) * hb + (-b') * hcs

theorem fderiv_rot_STR02923 (g : (Fin 3 → ℝ) → ℝ) (z : Fin 3 → ℝ)
    (hgd : DifferentiableAt ℝ g (rot_STR02923 z))
    (hev : (fun w => g (rot_STR02923 w)) =ᶠ[𝓝 z] g) (v : Fin 3 → ℝ) :
    fderiv ℝ g z v = fderiv ℝ g (rot_STR02923 z) (rot_STR02923 v) := by
  have h1 : HasFDerivAt (fun w => g (rot_STR02923 w))
      ((fderiv ℝ g (rot_STR02923 z)).comp rotCLM_STR02923) z :=
    hgd.hasFDerivAt.comp z (rot_hasFDerivAt_STR02923 z)
  have h2 : HasFDerivAt g ((fderiv ℝ g (rot_STR02923 z)).comp rotCLM_STR02923) z :=
    h1.congr_of_eventuallyEq hev.symm
  rw [h2.fderiv]
  rfl

/-- The equivariance of the slice map: `E(h, rot z) = E(h, z)` on `G` gives
`K(h, rot z) = rot (K(h, z))`. -/
theorem Kfun_rot_STR02923 {E : ℝ × (Fin 3 → ℝ) → ℝ} {G : Set (ℝ × (Fin 3 → ℝ))}
    (hGo : IsOpen G) (hGr : ∀ p ∈ G, (p.1, rot_STR02923 p.2) ∈ G)
    (hdiff : ∀ p ∈ G, DifferentiableAt ℝ E p)
    (hinv : ∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ G → E (h, rot_STR02923 z) = E (h, z))
    {h : ℝ} {z : Fin 3 → ℝ} (hz : (h, z) ∈ G) :
    Kfun_STR02923 E (h, rot_STR02923 z) = rot_STR02923 (Kfun_STR02923 E (h, z)) := by
  have hrz : (h, rot_STR02923 z) ∈ G := hGr _ hz
  have hopen : IsOpen {w : Fin 3 → ℝ | (h, w) ∈ G} :=
    hGo.preimage (continuous_const.prodMk continuous_id)
  have hev : (fun w : Fin 3 → ℝ => E (h, rot_STR02923 w)) =ᶠ[𝓝 z]
      (fun w : Fin 3 → ℝ => E (h, w)) := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact hinv h w hw
  have hgd : DifferentiableAt ℝ (fun w : Fin 3 → ℝ => E (h, w)) (rot_STR02923 z) :=
    ((hdiff _ hrz).hasFDerivAt.comp (rot_STR02923 z)
      (hasFDerivAt_prodMk_right h (rot_STR02923 z))).differentiableAt
  have hM0 := fderiv_rot_STR02923 (fun w : Fin 3 → ℝ => E (h, w)) z hgd hev (Pi.single 0 1)
  have hM1 := fderiv_rot_STR02923 (fun w : Fin 3 → ℝ => E (h, w)) z hgd hev (Pi.single 1 1)
  rw [rot_single0_STR02923, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hM0
  rw [rot_single1_STR02923, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hM1
  obtain ⟨ka, kb⟩ := rot_core_STR02923 _ _ _ _ _ _ cos_sq_add_sin_sq_STR02923 hM0 hM1
  funext i
  fin_cases i
  · exact ka
  · exact kb
  · exact hinv h z hz

/-- The rotation invariance of `E` on `G`, from the closed form at `h = 0` and from the
equivariance of the graph function `Fgraph` for `h ≠ 0`. -/
theorem E_rot_STR02923 {E : ℝ × (Fin 3 → ℝ) → ℝ} {O : Set (ℝ × (Fin 3 → ℝ))}
    {W : Set Par_STR02916} (ψ1 : Par_STR02916 → E_STR02969)
    (hval : ∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
      E (h, z) = Fgraph_STR02921 ψ1 (ptPar_STR02923 h z) / h ^ 4)
    (hzero : ∀ z : Fin 3 → ℝ,
      E ((0 : ℝ), z) = Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2))
    (hW : ∀ p ∈ W, rotPar_STR02916 (2 * Real.pi / 3) p ∈ W →
      Fgraph_STR02921 ψ1 (rotPar_STR02916 (2 * Real.pi / 3) p) = Fgraph_STR02921 ψ1 p)
    {h : ℝ} {z : Fin 3 → ℝ} (hz : (h, z) ∈ O) (hrz : (h, rot_STR02923 z) ∈ O)
    (hWz : ptPar_STR02923 h z ∈ W) (hWrz : ptPar_STR02923 h (rot_STR02923 z) ∈ W) :
    E (h, rot_STR02923 z) = E (h, z) := by
  by_cases hh : h = 0
  · subst hh
    rw [hzero, hzero, closed_rot_STR02923]
  · rw [hval h _ hrz hh, hval h z hz hh, ptPar_rot_STR02923,
      hW (ptPar_STR02923 h z) hWz (by rw [← ptPar_rot_STR02923]; exact hWrz)]

/-! ### The slice map `K` and its `z`-derivative on an open set -/

theorem fderiv_slice_STR02923 (E : ℝ × (Fin 3 → ℝ) → ℝ) {p : ℝ × (Fin 3 → ℝ)}
    (hE : DifferentiableAt ℝ E p) (v : Fin 3 → ℝ) :
    fderiv ℝ (fun w : Fin 3 → ℝ => E (p.1, w)) p.2 v = fderiv ℝ E p ((0 : ℝ), v) := by
  have h2 : fderiv ℝ (fun w : Fin 3 → ℝ => E (p.1, w)) p.2 =
      (fderiv ℝ E p).comp (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ)) :=
    (hE.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)).fderiv
  rw [h2]
  rfl

theorem diffAt_STR02923 {E : ℝ × (Fin 3 → ℝ) → ℝ} {S : Set (ℝ × (Fin 3 → ℝ))} (hS : IsOpen S)
    (hE : ContDiffOn ℝ ∞ E S) {p : ℝ × (Fin 3 → ℝ)} (hp : p ∈ S) :
    DifferentiableAt ℝ E p :=
  (hE.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)

theorem contDiffOn_Kfun_STR02923 {E : ℝ × (Fin 3 → ℝ) → ℝ} {S : Set (ℝ × (Fin 3 → ℝ))}
    (hS : IsOpen S) (hE : ContDiffOn ℝ ∞ E S) :
    ContDiffOn ℝ ∞ (Kfun_STR02923 E) S := by
  have hD : ContDiffOn ℝ ∞ (fun p => fderiv ℝ E p) S :=
    hE.fderiv_of_isOpen hS (by simp)
  have h0 : ContDiffOn ℝ ∞
      (fun p => fderiv ℝ E p ((0 : ℝ), (Pi.single 0 1 : Fin 3 → ℝ))) S :=
    hD.clm_apply contDiffOn_const
  have h1 : ContDiffOn ℝ ∞
      (fun p => fderiv ℝ E p ((0 : ℝ), (Pi.single 1 1 : Fin 3 → ℝ))) S :=
    hD.clm_apply contDiffOn_const
  have hF : ContDiffOn ℝ ∞ (fun p => (![fderiv ℝ E p ((0 : ℝ), (Pi.single 0 1 : Fin 3 → ℝ)),
      fderiv ℝ E p ((0 : ℝ), (Pi.single 1 1 : Fin 3 → ℝ)), E p] : Fin 3 → ℝ)) S := by
    refine contDiffOn_pi.2 fun i => ?_
    fin_cases i
    · exact h0
    · exact h1
    · exact hE
  refine hF.congr fun p hp => ?_
  funext i
  fin_cases i
  · exact fderiv_slice_STR02923 E (diffAt_STR02923 hS hE hp) _
  · exact fderiv_slice_STR02923 E (diffAt_STR02923 hS hE hp) _
  · rfl

/-- The `z`-derivative of `K(h, ·)` at `p`, as a continuous linear map of `z`. -/
noncomputable def Mz_STR02923 (E : ℝ × (Fin 3 → ℝ) → ℝ) (p : ℝ × (Fin 3 → ℝ)) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (fderiv ℝ (Kfun_STR02923 E) p).comp (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ))

theorem continuousAt_det_STR02923 {f : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    {S : Set (ℝ × (Fin 3 → ℝ))} (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S)
    {u : ℝ × (Fin 3 → ℝ)} (hu : u ∈ S) :
    ContinuousAt (fun v => ((fderiv ℝ f v).comp
      (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ))).det) u := by
  have hc : ContinuousAt (fun v => fderiv ℝ f v) u :=
    (hf.continuousOn_fderiv_of_isOpen hS (by simp)).continuousAt (hS.mem_nhds hu)
  have hcomp : ContinuousAt (fun v => (fderiv ℝ f v).comp
      (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ))) u :=
    hc.clm_comp continuousAt_const
  exact ContinuousLinearMap.continuous_det.continuousAt.comp hcomp

theorem isInvertible_of_det_STR02923 {L : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)} (h : L.det ≠ 0) :
    L.IsInvertible :=
  ⟨L.toContinuousLinearEquivOfDetNeZero h, L.coe_toContinuousLinearEquivOfDetNeZero h⟩

theorem Mz_slice_STR02923 (E : ℝ × (Fin 3 → ℝ) → ℝ) {S : Set (ℝ × (Fin 3 → ℝ))}
    (hS : IsOpen S) (hE : ContDiffOn ℝ ∞ E S) {z : Fin 3 → ℝ} (hz : ((0 : ℝ), z) ∈ S) :
    fderiv ℝ (Kmap_STR02922 E) z = Mz_STR02923 E ((0 : ℝ), z) := by
  have hK : DifferentiableAt ℝ (Kfun_STR02923 E) ((0 : ℝ), z) :=
    ((contDiffOn_Kfun_STR02923 hS hE).contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp)
  have hfun : (fun w : Fin 3 → ℝ => Kfun_STR02923 E ((0 : ℝ), w)) = Kmap_STR02922 E := rfl
  have h2 : fderiv ℝ (fun w : Fin 3 → ℝ => Kfun_STR02923 E ((0 : ℝ), w)) z =
      (fderiv ℝ (Kfun_STR02923 E) ((0 : ℝ), z)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ)) :=
    (hK.hasFDerivAt.comp z (hasFDerivAt_prodMk_right (0 : ℝ) z)).fderiv
  rw [← hfun, h2]
  rfl

theorem det_Mz_STR02923 {E : ℝ × (Fin 3 → ℝ) → ℝ} {S : Set (ℝ × (Fin 3 → ℝ))} (hS : IsOpen S)
    (hE : ContDiffOn ℝ ∞ E S) (hz : ((0 : ℝ), (![2, 0, -16 / 15] : Fin 3 → ℝ)) ∈ S)
    (hzero : ∀ z : Fin 3 → ℝ,
      E ((0 : ℝ), z) = Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2)) :
    (Mz_STR02923 E ((0 : ℝ), (![2, 0, -16 / 15] : Fin 3 → ℝ))).det = -1 / 2 := by
  have hJ := (str029_22_invertible_finite_dimensional_jacobian_of_slice E hzero).2.1
  have hMat : LinearMap.toMatrix' (Mz_STR02923 E ((0 : ℝ), (![2, 0, -16 / 15] : Fin 3 → ℝ)) :
      (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) = jacobian_STR02922 E ![2, 0, -16 / 15] := by
    rw [← Mz_slice_STR02923 E hS hE hz]
    ext i j
    simp [LinearMap.toMatrix'_apply, jacobian_STR02922]
  have hdet := LinearMap.det_toMatrix' (Mz_STR02923 E ((0 : ℝ), (![2, 0, -16 / 15] : Fin 3 → ℝ)) :
    (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
  rw [hMat, hJ] at hdet
  show LinearMap.det _ = _
  rw [← hdet]
  norm_num [Matrix.det_fin_three]

/-- A local implicit-function box for a `C^∞` map `K` at a zero `u` with invertible
`z`-derivative: there are a graph function `g` of the first variable and a radius `r` such that
on the ball of radius `r` around `u` the zero set of `K` is exactly the graph of `g`, and `g` is
`C^∞` wherever its graph stays in the ball. -/
theorem ift_box_STR02923 {K : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ)} {S T : Set (ℝ × (Fin 3 → ℝ))}
    (hS : IsOpen S) (hK : ContDiffOn ℝ ∞ K S) (hT : IsOpen T)
    {u : ℝ × (Fin 3 → ℝ)} (huS : u ∈ S) (huT : u ∈ T) (hKu : K u = 0)
    (hdu : ((fderiv ℝ K u).comp (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ))).det ≠ 0) :
    ∃ (g : ℝ → (Fin 3 → ℝ)) (r : ℝ), 0 < r ∧ g u.1 = u.2 ∧
      (∀ v ∈ Metric.ball u r, v ∈ S ∧ v ∈ T ∧
        ((fderiv ℝ K v).comp (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ))).det ≠ 0 ∧
        (K v = 0 ↔ v.2 = g v.1)) ∧
      (∀ h1 : ℝ, (h1, g h1) ∈ Metric.ball u r → ContDiffAt ℝ ∞ g h1) := by
  have hpn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hcdf : ContDiffAt ℝ ∞ K u := hK.contDiffAt (hS.mem_nhds huS)
  have hinv : ((fderiv ℝ K u).comp (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ))).IsInvertible :=
    isInvertible_of_det_STR02923 hdu
  have hgu : (hcdf.implicitFunction hpn hinv) u.1 = u.2 :=
    hcdf.implicitFunction_apply_self hpn hinv
  have hev := hcdf.eventually_apply_eq_iff_implicitFunction hpn hinv
  have hdet_ev : ∀ᶠ v in 𝓝 u,
      ((fderiv ℝ K v).comp (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ))).det ≠ 0 :=
    (continuousAt_det_STR02923 hS hK huS).eventually_ne hdu
  have hall : ∀ᶠ v in 𝓝 u, v ∈ S ∧ v ∈ T ∧
      ((fderiv ℝ K v).comp (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ))).det ≠ 0 ∧
      (K v = 0 ↔ v.2 = (hcdf.implicitFunction hpn hinv) v.1) := by
    filter_upwards [hS.mem_nhds huS, hT.mem_nhds huT, hdet_ev, hev] with v hvS hvT hvd hv
    rw [hKu] at hv
    exact ⟨hvS, hvT, hvd, hv.trans eq_comm⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hall
  refine ⟨hcdf.implicitFunction hpn hinv, r, hr, hgu, fun v hv => hball (Metric.mem_ball.1 hv), ?_⟩
  intro h1 hmem
  have hmem' := hball (Metric.mem_ball.1 hmem)
  obtain ⟨hu1S, -, hu1d, hu1iff⟩ := hmem'
  have hK1 : ContDiffAt ℝ ∞ K (h1, (hcdf.implicitFunction hpn hinv) h1) :=
    hK.contDiffAt (hS.mem_nhds hu1S)
  have hKu1 : K (h1, (hcdf.implicitFunction hpn hinv) h1) = 0 := hu1iff.2 rfl
  have hinv1 : ((fderiv ℝ K (h1, (hcdf.implicitFunction hpn hinv) h1)).comp
      (ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ))).IsInvertible :=
    isInvertible_of_det_STR02923 hu1d
  have hg1 : (hK1.implicitFunction hpn hinv1) h1 = (hcdf.implicitFunction hpn hinv) h1 :=
    hK1.implicitFunction_apply_self hpn hinv1
  have hcg1 : ContinuousAt (hK1.implicitFunction hpn hinv1) h1 :=
    (hK1.contDiffAt_implicitFunction hpn hinv1).continuousAt
  have hcont : ∀ᶠ x in 𝓝 h1, (x, (hK1.implicitFunction hpn hinv1) x) ∈ Metric.ball u r := by
    have hφ : ContinuousAt (fun x : ℝ => (x, (hK1.implicitFunction hpn hinv1) x)) h1 :=
      continuousAt_id.prodMk hcg1
    have hmem1 : ((h1, (hK1.implicitFunction hpn hinv1) h1) : ℝ × (Fin 3 → ℝ)) ∈
        Metric.ball u r := by
      rw [hg1]
      exact hmem
    exact hφ.eventually_mem (Metric.isOpen_ball.mem_nhds hmem1)
  have hK1eq : ∀ᶠ x in 𝓝 h1, K (x, (hK1.implicitFunction hpn hinv1) x) = 0 := by
    filter_upwards [hK1.eventually_apply_implicitFunction hpn hinv1] with x hx
    rw [hx, hKu1]
  have hgeq : (hcdf.implicitFunction hpn hinv) =ᶠ[𝓝 h1] (hK1.implicitFunction hpn hinv1) := by
    filter_upwards [hcont, hK1eq] with x hx1 hx2
    exact ((hball (Metric.mem_ball.1 hx1)).2.2.2.1 hx2).symm
  exact (hK1.contDiffAt_implicitFunction hpn hinv1).congr_of_eventuallyEq hgeq

theorem mem_Gset_iff_STR02923 {O : Set (ℝ × (Fin 3 → ℝ))} {W : Set Par_STR02916}
    {h : ℝ} {z : Fin 3 → ℝ} :
    (h, z) ∈ Gset_STR02923 O W ↔
      (h, z) ∈ O ∧ ptPar_STR02923 h z ∈ W ∧
      (h, rot_STR02923 z) ∈ O ∧ ptPar_STR02923 h (rot_STR02923 z) ∈ W ∧
      (h, rot_STR02923 (rot_STR02923 z)) ∈ O ∧
        ptPar_STR02923 h (rot_STR02923 (rot_STR02923 z)) ∈ W := by
  simp only [Gset_STR02923, Qset_STR02923, Set.mem_inter_iff, Set.mem_preimage, and_assoc]

theorem mem_O_of_Gset_STR02923 {O : Set (ℝ × (Fin 3 → ℝ))} {W : Set Par_STR02916}
    {p : ℝ × (Fin 3 → ℝ)} (hp : p ∈ Gset_STR02923 O W) : p ∈ O := by
  obtain ⟨h, z⟩ := p
  exact (mem_Gset_iff_STR02923.1 hp).1

theorem zero_mem_Gset_STR02923 {O : Set (ℝ × (Fin 3 → ℝ))} {W : Set Par_STR02916}
    (h0O : ∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O) (h0W : (0 : Par_STR02916) ∈ W)
    (z : Fin 3 → ℝ) : ((0 : ℝ), z) ∈ Gset_STR02923 O W := by
  have hW0 : ∀ w : Fin 3 → ℝ, ptPar_STR02923 0 w ∈ W := fun w => by
    rw [ptPar_zero_STR02923]
    exact h0W
  exact mem_Gset_iff_STR02923.2 ⟨h0O z, hW0 z, h0O _, hW0 _, h0O _, hW0 _⟩

theorem Gset_rot_STR02923 {O : Set (ℝ × (Fin 3 → ℝ))} {W : Set Par_STR02916}
    {h : ℝ} {z : Fin 3 → ℝ} (hz : (h, z) ∈ Gset_STR02923 O W) :
    (h, rot_STR02923 z) ∈ Gset_STR02923 O W := by
  obtain ⟨hO0, hW0, hO1, hW1, hO2, hW2⟩ := mem_Gset_iff_STR02923.1 hz
  rw [mem_Gset_iff_STR02923, rot_cube_STR02923]
  exact ⟨hO1, hW1, hO2, hW2, hO0, hW0⟩

theorem rot_eq_iff_STR02923 {x y : Fin 3 → ℝ} : rot_STR02923 x = rot_STR02923 y ↔ x = y :=
  ⟨rot_injective_STR02923, fun h => congrArg rot_STR02923 h⟩

theorem rot_eq_zero_iff_STR02923 {x : Fin 3 → ℝ} : rot_STR02923 x = 0 ↔ x = 0 := by
  constructor
  · intro h
    exact rot_injective_STR02923 (h.trans rot_zero_STR02923.symm)
  · intro h
    rw [h, rot_zero_STR02923]

theorem branches_STR02923 {O : Set (ℝ × (Fin 3 → ℝ))} {E : ℝ × (Fin 3 → ℝ) → ℝ}
    {W : Set Par_STR02916}
    (hO : IsOpen O) (hWo : IsOpen W) (h0W : (0 : Par_STR02916) ∈ W)
    (h0O : ∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O) (hEC : ContDiffOn ℝ ∞ E O)
    (hinv : ∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ Gset_STR02923 O W →
      E (h, rot_STR02923 z) = E (h, z))
    (hKzero : Kfun_STR02923 E ((0 : ℝ), (![2, 0, -16 / 15] : Fin 3 → ℝ)) = 0)
    (hdet : (Mz_STR02923 E ((0 : ℝ), (![2, 0, -16 / 15] : Fin 3 → ℝ))).det ≠ 0) :
    ∃ η : ℝ, 0 < η ∧
      ∃ (N : Fin 3 → Set (Fin 3 → ℝ)) (Z : Fin 3 → ℝ → (Fin 3 → ℝ)),
        IsOpen (N 0) ∧ IsOpen (N 1) ∧ IsOpen (N 2) ∧
        N 0 ∈ 𝓝 (![2, 0, -16 / 15] : Fin 3 → ℝ) ∧
        N 1 ∈ 𝓝 (![-1, Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) ∧
        N 2 ∈ 𝓝 (![-1, -Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) ∧
        (∀ i j : Fin 3, i ≠ j → Disjoint (N i) (N j)) ∧
        (∀ z : Fin 3 → ℝ, z ∈ N 0 ↔ (![z 0, -z 1, z 2] : Fin 3 → ℝ) ∈ N 0) ∧
        N 1 = rot_STR02923 '' N 0 ∧ N 2 = rot_STR02923 '' N 1 ∧
        (∀ j : Fin 3, ContDiffOn ℝ ∞ (Z j) (Set.Ioo (-η) η)) ∧
        (∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, Z j h ∈ N j) ∧
        (∀ h ∈ Set.Ioo (-η) η, Z 1 h = rot_STR02923 (Z 0 h) ∧ Z 2 h = rot_STR02923 (Z 1 h)) ∧
        (∀ h ∈ Set.Ioo (-η) η, ∀ j : Fin 3, Z j h 2 = Z 0 h 2) ∧
        (∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, ∀ z ∈ N j,
          Kfun_STR02923 E (h, z) = 0 ↔ z = Z j h) := by
  obtain ⟨g, r, hr, hgu, hball, hgsm⟩ :=
    ift_box_STR02923 hO (contDiffOn_Kfun_STR02923 hO hEC) (isOpen_Gset_STR02923 hO hWo)
      (h0O (![2, 0, -16 / 15] : Fin 3 → ℝ))
      (zero_mem_Gset_STR02923 h0O h0W (![2, 0, -16 / 15] : Fin 3 → ℝ)) hKzero hdet
  have hg0 : g 0 = (![2, 0, -16 / 15] : Fin 3 → ℝ) := hgu
  have hm0 : ((0 : ℝ), g 0) ∈ Metric.ball ((0 : ℝ), (![2, 0, -16 / 15] : Fin 3 → ℝ)) r := by
    rw [hg0]
    exact Metric.mem_ball_self hr
  have hcont : ContinuousAt g 0 := (hgsm 0 hm0).continuousAt
  obtain ⟨ρ, hρ0, hρ1, hρr⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ρ ≤ r / 2 :=
    ⟨min (r / 2) (1 / 2), lt_min (half_pos hr) (by norm_num), min_le_right _ _,
      min_le_left _ _⟩
  have hgP : ∀ᶠ h in 𝓝 (0 : ℝ), g h ∈ Metric.ball (![2, 0, -16 / 15] : Fin 3 → ℝ) ρ := by
    apply hcont.eventually_mem
    rw [hg0]
    exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ0)
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 hgP
  obtain ⟨η, hη0, hηδ, hηr⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ η ≤ r / 2 :=
    ⟨min δ (r / 2), lt_min hδ (half_pos hr), min_le_left _ _, min_le_right _ _⟩
  have hsmall : ∀ h ∈ Set.Ioo (-η) η, |h| < η := fun h hh => abs_lt.2 ⟨hh.1, hh.2⟩
  have hnear : ∀ h ∈ Set.Ioo (-η) η, g h ∈ Metric.ball (![2, 0, -16 / 15] : Fin 3 → ℝ) ρ := by
    intro h hh
    apply hδP
    rw [Real.dist_eq, sub_zero]
    exact lt_of_lt_of_le (hsmall h hh) hηδ
  have hin : ∀ h ∈ Set.Ioo (-η) η, ∀ z ∈ Metric.ball (![2, 0, -16 / 15] : Fin 3 → ℝ) ρ,
      ((h, z) : ℝ × (Fin 3 → ℝ)) ∈
        Metric.ball ((0 : ℝ), (![2, 0, -16 / 15] : Fin 3 → ℝ)) r := by
    intro h hh z hz
    have hz' := Metric.mem_ball.1 hz
    have hh' := hsmall h hh
    rw [Metric.mem_ball, Prod.dist_eq]
    refine max_lt ?_ ?_
    · show dist h 0 < r
      rw [Real.dist_eq, sub_zero]
      linarith
    · show dist z (![2, 0, -16 / 15] : Fin 3 → ℝ) < r
      linarith
  have hGo : IsOpen (Gset_STR02923 O W) := isOpen_Gset_STR02923 hO hWo
  have hGr : ∀ p ∈ Gset_STR02923 O W, (p.1, rot_STR02923 p.2) ∈ Gset_STR02923 O W := by
    rintro ⟨p1, p2⟩ hp
    exact Gset_rot_STR02923 hp
  have hdiff : ∀ p ∈ Gset_STR02923 O W, DifferentiableAt ℝ E p := fun p hp =>
    diffAt_STR02923 hO hEC (mem_O_of_Gset_STR02923 hp)
  refine ⟨η, hη0,
    ![Metric.ball (![2, 0, -16 / 15] : Fin 3 → ℝ) ρ,
      rot_STR02923 '' Metric.ball (![2, 0, -16 / 15] : Fin 3 → ℝ) ρ,
      rot_STR02923 '' (rot_STR02923 '' Metric.ball (![2, 0, -16 / 15] : Fin 3 → ℝ) ρ)],
    ![g, fun h => rot_STR02923 (g h), fun h => rot_STR02923 (rot_STR02923 (g h))],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact Metric.isOpen_ball
  · exact isOpen_image_rot_STR02923 Metric.isOpen_ball
  · exact isOpen_image_rot_STR02923 (isOpen_image_rot_STR02923 Metric.isOpen_ball)
  · exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ0)
  · rw [← rotP0_STR02923]
    exact (isOpen_image_rot_STR02923 Metric.isOpen_ball).mem_nhds
      (Set.mem_image_of_mem _ (Metric.mem_ball_self hρ0))
  · rw [← rotrotP0_STR02923]
    exact (isOpen_image_rot_STR02923 (isOpen_image_rot_STR02923 Metric.isOpen_ball)).mem_nhds
      (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ (Metric.mem_ball_self hρ0)))
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact disjoint_ball_rot_STR02923 hρ1
    · exact disjoint_ball_rotrot_STR02923 hρ1
    · exact (disjoint_ball_rot_STR02923 hρ1).symm
    · exact (hij rfl).elim
    · exact disjoint_image_rot_STR02923 (disjoint_ball_rot_STR02923 hρ1)
    · exact (disjoint_ball_rotrot_STR02923 hρ1).symm
    · exact (disjoint_image_rot_STR02923 (disjoint_ball_rot_STR02923 hρ1)).symm
    · exact (hij rfl).elim
  · exact fun z => (refl_mem_ball_STR02923 hρ0 z).symm
  · intro j
    fin_cases j
    · intro h hh
      exact (hgsm h (hin h hh (g h) (hnear h hh))).contDiffWithinAt
    · intro h hh
      exact (ContDiffAt.comp h rot_contDiff_STR02923.contDiffAt
        (hgsm h (hin h hh (g h) (hnear h hh)))).contDiffWithinAt
    · intro h hh
      exact (ContDiffAt.comp h rot_contDiff_STR02923.contDiffAt
        (ContDiffAt.comp h rot_contDiff_STR02923.contDiffAt
          (hgsm h (hin h hh (g h) (hnear h hh))))).contDiffWithinAt
  · intro j h hh
    fin_cases j
    · exact hnear h hh
    · exact ⟨g h, hnear h hh, rfl⟩
    · exact ⟨rot_STR02923 (g h), ⟨g h, hnear h hh, rfl⟩, rfl⟩
  · intro h _
    exact ⟨rfl, rfl⟩
  · intro h _ j
    fin_cases j <;> rfl
  · intro j h hh z hz
    fin_cases j
    · exact (hball (h, z) (hin h hh z hz)).2.2.2
    · obtain ⟨w, hw, rfl⟩ := hz
      have hwG : (h, w) ∈ Gset_STR02923 O W := (hball (h, w) (hin h hh w hw)).2.1
      have hK0 := Kfun_rot_STR02923 (E := E) hGo hGr hdiff hinv hwG
      show Kfun_STR02923 E (h, rot_STR02923 w) = 0 ↔ rot_STR02923 w = rot_STR02923 (g h)
      rw [hK0, rot_eq_zero_iff_STR02923, rot_eq_iff_STR02923]
      exact (hball (h, w) (hin h hh w hw)).2.2.2
    · obtain ⟨u, ⟨w, hw, rfl⟩, rfl⟩ := hz
      have hwG : (h, w) ∈ Gset_STR02923 O W := (hball (h, w) (hin h hh w hw)).2.1
      have hwG1 : (h, rot_STR02923 w) ∈ Gset_STR02923 O W := Gset_rot_STR02923 hwG
      have hK0 := Kfun_rot_STR02923 (E := E) hGo hGr hdiff hinv hwG
      have hK1 := Kfun_rot_STR02923 (E := E) hGo hGr hdiff hinv hwG1
      show Kfun_STR02923 E (h, rot_STR02923 (rot_STR02923 w)) = 0 ↔
        rot_STR02923 (rot_STR02923 w) = rot_STR02923 (rot_STR02923 (g h))
      rw [hK1, hK0, rot_eq_zero_iff_STR02923, rot_eq_zero_iff_STR02923,
        rot_eq_iff_STR02923, rot_eq_iff_STR02923]
      exact (hball (h, w) (hin h hh w hw)).2.2.2

theorem str029_23_three_locally_unique_solution_branches :
    ∃ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
      IsOpen U ∧ (0 : Par_STR02916) ∈ U ∧ IsOpen V ∧ (0 : E_STR02969) ∈ V ∧
      ContDiffOn ℝ ∞ ψ U ∧ ψ 0 = 0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
      (∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) ∧
      ∃ (O : Set (ℝ × (Fin 3 → ℝ))) (E : ℝ × (Fin 3 → ℝ) → ℝ),
        IsOpen O ∧ (∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O) ∧ ContDiffOn ℝ ∞ E O ∧
        (∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
          E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4) ∧
        (∀ z : Fin 3 → ℝ, E ((0 : ℝ), z) =
          Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2)) ∧
        ∃ η : ℝ, 0 < η ∧
          ∃ (N : Fin 3 → Set (Fin 3 → ℝ)) (Z : Fin 3 → ℝ → (Fin 3 → ℝ)),
            IsOpen (N 0) ∧ IsOpen (N 1) ∧ IsOpen (N 2) ∧
            N 0 ∈ 𝓝 (![2, 0, -16 / 15] : Fin 3 → ℝ) ∧
            N 1 ∈ 𝓝 (![-1, Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) ∧
            N 2 ∈ 𝓝 (![-1, -Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) ∧
            (∀ i j : Fin 3, i ≠ j → Disjoint (N i) (N j)) ∧
            (∀ z : Fin 3 → ℝ, z ∈ N 0 ↔ (![z 0, -z 1, z 2] : Fin 3 → ℝ) ∈ N 0) ∧
            N 1 = rot_STR02923 '' N 0 ∧ N 2 = rot_STR02923 '' N 1 ∧
            (∀ j : Fin 3, ContDiffOn ℝ ∞ (Z j) (Set.Ioo (-η) η)) ∧
            (∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, Z j h ∈ N j) ∧
            (∀ h ∈ Set.Ioo (-η) η, Z 1 h = rot_STR02923 (Z 0 h) ∧ Z 2 h = rot_STR02923 (Z 1 h)) ∧
            (∀ h ∈ Set.Ioo (-η) η, ∀ j : Fin 3, Z j h 2 = Z 0 h 2) ∧
            (∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, ∀ z ∈ N j,
              Kfun_STR02923 E (h, z) = 0 ↔ z = Z j h) := by
  obtain ⟨U, V, ψ, hU, h0U, hV, h0V, hψC, hψ0, hψV, hRpar, O, hO, h0O, E, hEC, hval, hzero, -⟩ :=
    str029_20_smooth_reduced_function_through_zero_field
  obtain ⟨U2, V2, ψ2, hU2, h0U2, hV2, h0V2, -, hψ02, -, hiff2, -, -, -, -, -, -, -, -, hFrot,
    -, -, -, -, -⟩ :=
    str029_21_equivariance_unique_range_graph
  have h0W : (0 : Par_STR02916) ∈ Wset_STR02923 U U2 V2 ψ :=
    ⟨⟨h0U, by show ψ 0 ∈ V2; rw [hψ0]; exact h0V2⟩, h0U2⟩
  have hWo : IsOpen (Wset_STR02923 U U2 V2 ψ) :=
    (hψC.continuousOn.isOpen_inter_preimage hU hV2).inter hU2
  have hW : ∀ p ∈ Wset_STR02923 U U2 V2 ψ,
      rotPar_STR02916 (2 * Real.pi / 3) p ∈ Wset_STR02923 U U2 V2 ψ →
      Fgraph_STR02921 ψ (rotPar_STR02916 (2 * Real.pi / 3) p) = Fgraph_STR02921 ψ p := by
    intro p hp hrp
    have hkey := hFrot 1 p hp.2
    have hθ : 2 * Real.pi * ((1 : ℤ) : ℝ) / 3 = 2 * Real.pi / 3 := by norm_num
    rw [hθ] at hkey
    have e1 := Fgraph_agree_STR02923 hψV hRpar hiff2 hrp.1.1 hrp.1.2 hrp.2
    have e2 := Fgraph_agree_STR02923 hψV hRpar hiff2 hp.1.1 hp.1.2 hp.2
    rw [e1, e2, hkey]
  have hinv : ∀ (h : ℝ) (z : Fin 3 → ℝ),
      (h, z) ∈ Gset_STR02923 O (Wset_STR02923 U U2 V2 ψ) →
      E (h, rot_STR02923 z) = E (h, z) := by
    intro h z hG
    obtain ⟨hO0, hW0, hO1, hW1, -, -⟩ := mem_Gset_iff_STR02923.1 hG
    exact E_rot_STR02923 ψ hval hzero hW hO0 hO1 hW0 hW1
  have hKzero : Kfun_STR02923 E ((0 : ℝ), (![2, 0, -16 / 15] : Fin 3 → ℝ)) = 0 :=
    (str029_22_invertible_finite_dimensional_jacobian_of_slice E hzero).1
  have hdet : (Mz_STR02923 E ((0 : ℝ), (![2, 0, -16 / 15] : Fin 3 → ℝ))).det ≠ 0 := by
    rw [det_Mz_STR02923 hO hEC (h0O (![2, 0, -16 / 15] : Fin 3 → ℝ)) hzero]
    norm_num
  exact ⟨U, V, ψ, hU, h0U, hV, h0V, hψC, hψ0, hψV, hRpar, O, E, hO, h0O, hEC, hval, hzero,
    branches_STR02923 (W := Wset_STR02923 U U2 V2 ψ) hO hWo h0W h0O hEC hinv hKzero hdet⟩

end DGPS.Frontier.STR029
