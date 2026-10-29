import DGPS.Frontier.STR029.T18
import DGPS.Frontier.STR029.T20

/-!
# STR029.22: Invertible finite-dimensional Jacobian

Task id: STR029.22. Title: Invertible finite-dimensional Jacobian. Node STR029.
Prerequisites: STR029.18 (`Jred_STR02918`, with the polynomial form `Jred_eq_STR02918`) and
STR029.20 (`str029_20_smooth_reduced_function_through_zero_field`, whose `h = 0` clause is the
closed form of the extension `V`).

Provides:
* `DGPS.Frontier.STR029.str029_22_invertible_finite_dimensional_jacobian`: there is a function `E`
  on `ℝ × (Fin 3 → ℝ)` whose `h = 0` slice is the closed form `J_4^red(A, B) - s (A² + B²)/2` of
  STR029.20, and for `K = (∂_A V, ∂_B V, V)` in the coordinates `z = (A, B, s)` at `h = 0`:
  `K` vanishes at `(2, 0, -16/15)`, its Jacobian there is `!![1/6, 0, -2; 0, 3/2, 0; 0, 0, -2]`,
  its inverse is `!![6, 0, -6; 0, 2/3, 0; 0, 0, -1/2]`, and the Jacobians at `(-1, ±√3, -16/15)`
  are invertible.
* `DGPS.Frontier.STR029.str029_22_invertible_finite_dimensional_jacobian_of_slice`: the same
  conclusions for every `E` whose `h = 0` slice is the closed form.
* `DGPS.Frontier.STR029.Kmap_STR02922`, `DGPS.Frontier.STR029.jacobian_STR02922`: the map `K` and
  its Jacobian in `(A, B, s)`, built from `E`. Entry `(i, j)` of the Jacobian is `∂_j K_i`.

R5 notes:
1. Extension. `V` is the function of STR029.20. The main statement existentially quantifies `E`,
   and its only constraint is the `h = 0` clause of STR029.20. That clause is taken from the
   theorem `str029_20_smooth_reduced_function_through_zero_field`, which supplies such an `E`, so
   the existential is not vacuous. The other clauses of STR029.20 (smoothness, the formula for
   `h ≠ 0`, the uniform limits) are not used and not restated.
2. Partial derivatives. `∂_A V`, `∂_B V`, `∂_s V` at `h = 0` are the Fréchet partial derivatives in
   the coordinate directions `Pi.single j 1` of the slice `z ↦ E (0, z)`. The derivative of `K` is
   the Fréchet derivative of the map `z ↦ K(z)`. The slice equals the closed form for every `z`, so
   the derivatives depend only on the closed form and not on the values of `E` for `h ≠ 0`.
3. Closed form. `J_4^red` is `Jred_STR02918` of STR029.18, with radius the nonnegative root. The
   polynomial form `Jred_eq_STR02918` is used to write the closed form in `A` and `B` only.
4. Invertibility. "Invertible" is read as `IsUnit` in the matrix ring over `ℝ`, that is two-sided
   invertibility. At `(2, 0, -16/15)` the inverse is stated explicitly, as the specification gives
   it. At `(-1, ±√3, -16/15)` only `IsUnit` is stated; its witness is computed in the proof.
5. Rotated points. `(-1, ±√3)` are the images of `(2, 0)` under rotation by `±2π/3` in the shape
   plane. The statement concerns those explicit points. It does not formalize rotation as a
   symmetry argument. The Jacobians are computed directly from the closed form. The vanishing of
   `K` at those points is true but is not part of the statement.
6. Scope. The points are at `h = 0` only. No smallness of `h`, no compact set, no neighbourhood,
   and no rate normalisation enter. The parameter `s` is the scaled parameter `s = γ/h²`, and the
   value `s₀ = -16/15` is the one of the specification.
-/

namespace DGPS.Frontier.STR029

/-! ### The closed form of the `h = 0` slice, in the coordinates `z = (A, B, s)` -/

/-- The closed form `J_4^red(A, B) - s (A² + B²)/2` of STR029.20 as a polynomial in `z`. -/
noncomputable def Vp_STR02922 (z : Fin 3 → ℝ) : ℝ :=
  (z 0 * z 0 + z 1 * z 1) * (z 0 * z 0 + z 1 * z 1) / 48
    - (z 0 * z 0 * z 0 - 3 * z 0 * (z 1 * z 1)) / 12
    - 9 * (z 0 * z 0 + z 1 * z 1) / 20 - z 2 * ((z 0 * z 0 + z 1 * z 1) / 2)

/-- The closed form agrees with `Jred_STR02918` of STR029.18. -/
theorem Vp_eq_STR02922 (z : Fin 3 → ℝ) :
    Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2) = Vp_STR02922 z := by
  rw [Jred_eq_STR02918]
  unfold Vp_STR02922
  ring

/-- `∂_A` of the closed form. -/
noncomputable def dA_STR02922 (z : Fin 3 → ℝ) : ℝ :=
  (z 0 * z 0 + z 1 * z 1) * z 0 / 12 - (z 0 * z 0 - z 1 * z 1) / 4 - 9 * z 0 / 10 - z 2 * z 0

/-- `∂_B` of the closed form. -/
noncomputable def dB_STR02922 (z : Fin 3 → ℝ) : ℝ :=
  (z 0 * z 0 + z 1 * z 1) * z 1 / 12 + z 0 * z 1 / 2 - 9 * z 1 / 10 - z 2 * z 1

/-- `∂_A ∂_A` of the closed form. -/
noncomputable def HAA_STR02922 (z : Fin 3 → ℝ) : ℝ :=
  (2 * (z 0 * z 0) + (z 0 * z 0 + z 1 * z 1)) / 12 - z 0 / 2 - 9 / 10 - z 2

/-- `∂_B ∂_A` of the closed form. -/
noncomputable def HAB_STR02922 (z : Fin 3 → ℝ) : ℝ := z 0 * z 1 / 6 + z 1 / 2

/-- `∂_B ∂_B` of the closed form. -/
noncomputable def HBB_STR02922 (z : Fin 3 → ℝ) : ℝ :=
  (2 * (z 1 * z 1) + (z 0 * z 0 + z 1 * z 1)) / 12 + z 0 / 2 - 9 / 10 - z 2

/-- The vector `K = (∂_A V, ∂_B V, V)` on the slice `h = 0`. -/
noncomputable def Kclosed_STR02922 (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![dA_STR02922 z, dB_STR02922 z, Vp_STR02922 z]

/-! ### Differentiability and directional derivatives -/

theorem differentiableAt_dA_STR02922 (z : Fin 3 → ℝ) :
    DifferentiableAt ℝ (fun w : Fin 3 → ℝ => dA_STR02922 w) z := by
  unfold dA_STR02922
  fun_prop

theorem differentiableAt_dB_STR02922 (z : Fin 3 → ℝ) :
    DifferentiableAt ℝ (fun w : Fin 3 → ℝ => dB_STR02922 w) z := by
  unfold dB_STR02922
  fun_prop

theorem differentiableAt_Vp_STR02922 (z : Fin 3 → ℝ) :
    DifferentiableAt ℝ (fun w : Fin 3 → ℝ => Vp_STR02922 w) z := by
  unfold Vp_STR02922
  fun_prop

theorem differentiableAt_Kclosed_STR02922 (z : Fin 3 → ℝ) :
    DifferentiableAt ℝ Kclosed_STR02922 z := by
  rw [differentiableAt_pi]
  intro i
  fin_cases i
  · exact differentiableAt_dA_STR02922 z
  · exact differentiableAt_dB_STR02922 z
  · exact differentiableAt_Vp_STR02922 z

/-- If `F` is differentiable at `z` and its restriction to the line `s ↦ z + s • v` has derivative
`c` at `0`, then the Fréchet derivative of `F` at `z` in direction `v` is `c`. -/
theorem fderiv_line_STR02922 {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (F : G → H) (z v : G) (c : H)
    (hF : DifferentiableAt ℝ F z) (hc : HasDerivAt (fun s : ℝ => F (z + s • v)) c 0) :
    fderiv ℝ F z v = c := by
  have hline : HasDerivAt (fun s : ℝ => z + s • v) v 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add z
  have hcomp : HasDerivAt (F ∘ fun s : ℝ => z + s • v) (fderiv ℝ F z v) 0 :=
    hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  exact (hc.unique hcomp).symm

theorem hasDerivAt_coord_STR02922 (z v : Fin 3 → ℝ) (k : Fin 3) :
    HasDerivAt (fun s : ℝ => z k + s * v k) (v k) 0 := by
  simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const (v k)).const_add (z k)

theorem hasDerivAt_dA_line_STR02922 (z v : Fin 3 → ℝ) :
    HasDerivAt (fun s : ℝ => dA_STR02922 (z + s • v))
      (HAA_STR02922 z * v 0 + HAB_STR02922 z * v 1 - z 0 * v 2) 0 := by
  have h0 := hasDerivAt_coord_STR02922 z v 0
  have h1 := hasDerivAt_coord_STR02922 z v 1
  have h2 := hasDerivAt_coord_STR02922 z v 2
  have hP := (h0.fun_mul h0).fun_add (h1.fun_mul h1)
  have hd := ((hP.fun_mul h0).div_const 12).fun_sub
    (((h0.fun_mul h0).fun_sub (h1.fun_mul h1)).div_const 4)
  have hd2 := (hd.fun_sub ((h0.const_mul 9).div_const 10)).fun_sub (h2.fun_mul h0)
  convert hd2 using 1
  · funext s
    simp only [dA_STR02922, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · simp only [HAA_STR02922, HAB_STR02922]
    ring

theorem hasDerivAt_dB_line_STR02922 (z v : Fin 3 → ℝ) :
    HasDerivAt (fun s : ℝ => dB_STR02922 (z + s • v))
      (HAB_STR02922 z * v 0 + HBB_STR02922 z * v 1 - z 1 * v 2) 0 := by
  have h0 := hasDerivAt_coord_STR02922 z v 0
  have h1 := hasDerivAt_coord_STR02922 z v 1
  have h2 := hasDerivAt_coord_STR02922 z v 2
  have hP := (h0.fun_mul h0).fun_add (h1.fun_mul h1)
  have hd := ((hP.fun_mul h1).div_const 12).fun_add ((h0.fun_mul h1).div_const 2)
  have hd2 := (hd.fun_sub ((h1.const_mul 9).div_const 10)).fun_sub (h2.fun_mul h1)
  convert hd2 using 1
  · funext s
    simp only [dB_STR02922, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · simp only [HAB_STR02922, HBB_STR02922]
    ring

theorem hasDerivAt_Vp_line_STR02922 (z v : Fin 3 → ℝ) :
    HasDerivAt (fun s : ℝ => Vp_STR02922 (z + s • v))
      (dA_STR02922 z * v 0 + dB_STR02922 z * v 1 - (z 0 * z 0 + z 1 * z 1) / 2 * v 2) 0 := by
  have h0 := hasDerivAt_coord_STR02922 z v 0
  have h1 := hasDerivAt_coord_STR02922 z v 1
  have h2 := hasDerivAt_coord_STR02922 z v 2
  have hP := (h0.fun_mul h0).fun_add (h1.fun_mul h1)
  have hPP := hP.fun_mul hP
  have hcub := ((h0.fun_mul h0).fun_mul h0).fun_sub ((h0.const_mul 3).fun_mul (h1.fun_mul h1))
  have hd := (((hPP.div_const 48).fun_sub (hcub.div_const 12)).fun_sub
    ((hP.const_mul 9).div_const 20)).fun_sub (h2.fun_mul (hP.div_const 2))
  convert hd using 1
  · funext s
    simp only [Vp_STR02922, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · simp only [dA_STR02922, dB_STR02922]
    ring

theorem hasDerivAt_Kclosed_line_STR02922 (z v : Fin 3 → ℝ) :
    HasDerivAt (fun s : ℝ => Kclosed_STR02922 (z + s • v))
      ![HAA_STR02922 z * v 0 + HAB_STR02922 z * v 1 - z 0 * v 2,
        HAB_STR02922 z * v 0 + HBB_STR02922 z * v 1 - z 1 * v 2,
        dA_STR02922 z * v 0 + dB_STR02922 z * v 1 - (z 0 * z 0 + z 1 * z 1) / 2 * v 2] 0 := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · exact hasDerivAt_dA_line_STR02922 z v
  · exact hasDerivAt_dB_line_STR02922 z v
  · exact hasDerivAt_Vp_line_STR02922 z v

theorem fderiv_Vp_STR02922 (z v : Fin 3 → ℝ) :
    fderiv ℝ Vp_STR02922 z v =
      dA_STR02922 z * v 0 + dB_STR02922 z * v 1 - (z 0 * z 0 + z 1 * z 1) / 2 * v 2 :=
  fderiv_line_STR02922 Vp_STR02922 z v _ (differentiableAt_Vp_STR02922 z)
    (hasDerivAt_Vp_line_STR02922 z v)

theorem fderiv_Kclosed_STR02922 (z v : Fin 3 → ℝ) :
    fderiv ℝ Kclosed_STR02922 z v =
      ![HAA_STR02922 z * v 0 + HAB_STR02922 z * v 1 - z 0 * v 2,
        HAB_STR02922 z * v 0 + HBB_STR02922 z * v 1 - z 1 * v 2,
        dA_STR02922 z * v 0 + dB_STR02922 z * v 1 - (z 0 * z 0 + z 1 * z 1) / 2 * v 2] :=
  fderiv_line_STR02922 Kclosed_STR02922 z v _ (differentiableAt_Kclosed_STR02922 z)
    (hasDerivAt_Kclosed_line_STR02922 z v)

/-! ### The map `K` and its Jacobian, built from an extension `E` -/

/-- The map `K = (∂_A V, ∂_B V, V)` on the slice `h = 0`, with `V` read from `E`. -/
noncomputable def Kmap_STR02922 (E : ℝ × (Fin 3 → ℝ) → ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![fderiv ℝ (fun w : Fin 3 → ℝ => E ((0 : ℝ), w)) z (Pi.single 0 1),
    fderiv ℝ (fun w : Fin 3 → ℝ => E ((0 : ℝ), w)) z (Pi.single 1 1),
    E ((0 : ℝ), z)]

/-- The Jacobian of `K` in `(A, B, s)` at `z`; entry `(i, j)` is `∂_j K_i`. -/
noncomputable def jacobian_STR02922 (E : ℝ × (Fin 3 → ℝ) → ℝ) (z : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => fderiv ℝ (Kmap_STR02922 E) z (Pi.single j 1) i

/-- If the `h = 0` slice of `E` is the closed form, then `K` is the closed-form vector. -/
theorem Kmap_eq_STR02922 (E : ℝ × (Fin 3 → ℝ) → ℝ)
    (hE : ∀ z : Fin 3 → ℝ,
      E ((0 : ℝ), z) = Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2)) :
    Kmap_STR02922 E = Kclosed_STR02922 := by
  have hslice : (fun w : Fin 3 → ℝ => E ((0 : ℝ), w)) = Vp_STR02922 :=
    funext fun w => (hE w).trans (Vp_eq_STR02922 w)
  funext z
  have hV : E ((0 : ℝ), z) = Vp_STR02922 z := (hE z).trans (Vp_eq_STR02922 z)
  unfold Kmap_STR02922 Kclosed_STR02922
  rw [hslice, hV, fderiv_Vp_STR02922, fderiv_Vp_STR02922]
  ext i
  fin_cases i <;> simp

/-- The Jacobian of `K` in `(A, B, s)` at `z`, written out. -/
theorem jacobian_eq_STR02922 (E : ℝ × (Fin 3 → ℝ) → ℝ)
    (hE : ∀ z : Fin 3 → ℝ,
      E ((0 : ℝ), z) = Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2))
    (z : Fin 3 → ℝ) :
    jacobian_STR02922 E z =
      !![HAA_STR02922 z, HAB_STR02922 z, -z 0;
        HAB_STR02922 z, HBB_STR02922 z, -z 1;
        dA_STR02922 z, dB_STR02922 z, -((z 0 * z 0 + z 1 * z 1) / 2)] := by
  unfold jacobian_STR02922
  rw [Kmap_eq_STR02922 E hE]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fderiv_Kclosed_STR02922, Pi.single_apply]

/-! ### The main statements -/

/-- STR029.22, for every extension `E` whose `h = 0` slice is the closed form of STR029.20. -/
theorem str029_22_invertible_finite_dimensional_jacobian_of_slice (E : ℝ × (Fin 3 → ℝ) → ℝ)
    (hE : ∀ z : Fin 3 → ℝ,
      E ((0 : ℝ), z) = Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2)) :
    Kmap_STR02922 E ![2, 0, -16 / 15] = 0 ∧
      jacobian_STR02922 E ![2, 0, -16 / 15] = !![1 / 6, 0, -2; 0, 3 / 2, 0; 0, 0, -2] ∧
      (jacobian_STR02922 E ![2, 0, -16 / 15])⁻¹ = !![6, 0, -6; 0, 2 / 3, 0; 0, 0, -1 / 2] ∧
      IsUnit (jacobian_STR02922 E ![-1, Real.sqrt 3, -16 / 15]) ∧
      IsUnit (jacobian_STR02922 E ![-1, -Real.sqrt 3, -16 / 15]) := by
  have ht : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hK0 : Kmap_STR02922 E ![2, 0, -16 / 15] = 0 := by
    rw [Kmap_eq_STR02922 E hE]
    funext i
    fin_cases i <;> simp [Kclosed_STR02922, dA_STR02922, dB_STR02922, Vp_STR02922] <;> norm_num
  have hM0 : jacobian_STR02922 E ![2, 0, -16 / 15] =
      !![1 / 6, 0, -2; 0, 3 / 2, 0; 0, 0, -2] := by
    rw [jacobian_eq_STR02922 E hE]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HAA_STR02922, HAB_STR02922, HBB_STR02922, dA_STR02922, dB_STR02922] <;> norm_num
  have hMinv : (jacobian_STR02922 E ![2, 0, -16 / 15])⁻¹ =
      !![6, 0, -6; 0, 2 / 3, 0; 0, 0, -1 / 2] := by
    apply Matrix.inv_eq_right_inv
    rw [hM0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
  have hMp : jacobian_STR02922 E ![-1, Real.sqrt 3, -16 / 15] =
      !![7 / 6, Real.sqrt 3 / 3, 1; Real.sqrt 3 / 3, 1 / 2, -Real.sqrt 3; 0, 0, -2] := by
    rw [jacobian_eq_STR02922 E hE]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HAA_STR02922, HAB_STR02922, HBB_STR02922, dA_STR02922, dB_STR02922] <;>
      linarith [ht]
  have hMm : jacobian_STR02922 E ![-1, -Real.sqrt 3, -16 / 15] =
      !![7 / 6, -(Real.sqrt 3 / 3), 1; -(Real.sqrt 3 / 3), 1 / 2, Real.sqrt 3; 0, 0, -2] := by
    rw [jacobian_eq_STR02922 E hE]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HAA_STR02922, HAB_STR02922, HBB_STR02922, dA_STR02922, dB_STR02922] <;>
      linarith [ht]
  refine ⟨hK0, hM0, hMinv, ?_, ?_⟩
  · rw [hMp]
    refine isUnit_iff_exists.2 ⟨!![2, -(4 * Real.sqrt 3 / 3), 3;
      -(4 * Real.sqrt 3 / 3), 14 / 3, -(3 * Real.sqrt 3); 0, 0, -1 / 2], ?_, ?_⟩ <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> linarith [ht]
  · rw [hMm]
    refine isUnit_iff_exists.2 ⟨!![2, 4 * Real.sqrt 3 / 3, 3;
      4 * Real.sqrt 3 / 3, 14 / 3, 3 * Real.sqrt 3; 0, 0, -1 / 2], ?_, ?_⟩ <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> linarith [ht]

/-- STR029.22. There is a function `E` on `ℝ × (Fin 3 → ℝ)` whose `h = 0` slice is the closed form
of STR029.20, and for it the statements of `str029_22_invertible_finite_dimensional_jacobian_of_slice`
hold. The function `E` is supplied by STR029.20. -/
theorem str029_22_invertible_finite_dimensional_jacobian :
    ∃ E : ℝ × (Fin 3 → ℝ) → ℝ,
      (∀ z : Fin 3 → ℝ,
        E ((0 : ℝ), z) = Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2)) ∧
      Kmap_STR02922 E ![2, 0, -16 / 15] = 0 ∧
      jacobian_STR02922 E ![2, 0, -16 / 15] = !![1 / 6, 0, -2; 0, 3 / 2, 0; 0, 0, -2] ∧
      (jacobian_STR02922 E ![2, 0, -16 / 15])⁻¹ = !![6, 0, -6; 0, 2 / 3, 0; 0, 0, -1 / 2] ∧
      IsUnit (jacobian_STR02922 E ![-1, Real.sqrt 3, -16 / 15]) ∧
      IsUnit (jacobian_STR02922 E ![-1, -Real.sqrt 3, -16 / 15]) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, E, -, -, hzero, -⟩ :=
    str029_20_smooth_reduced_function_through_zero_field
  exact ⟨E, hzero, str029_22_invertible_finite_dimensional_jacobian_of_slice E hzero⟩

end DGPS.Frontier.STR029
