import Mathlib

/-!
Task id and title: FIN068.17, Radical first and second jet (module
`DGPS.Frontier.FIN068.T17`).

Provides:
* `DGPS.Frontier.FIN068.radicalR_FIN06817`: the function `R(w) = √((-4 + w 0)^2 + w 1)` on
  `EuclideanSpace ℝ (Fin 2)` (a helper definition, not a claim).
* `DGPS.Frontier.FIN068.fin068_17_radical_first_second_jet`: at the origin, `R = 4`; the scalar
  first partials `R_u = -1` and `R_z = 1/8`; the scalar second partials `R_uu = 0`,
  `R_uz = R_zu = 1/32`, `R_zz = -1/256`; the Fréchet first-derivative entries `fderiv R 0 e₀ = -1`
  and `fderiv R 0 e₁ = 1/8`; and the Fréchet second-derivative entries
  `fderiv (fderiv R) 0 eᵢ eⱼ` with the same values (`e₀`, `e₁` the standard basis vectors).
* Helper lemmas, all named with the suffix `_FIN06817` and not part of the interface: the radicand
  and radical Fréchet derivatives on the positive patch, the derivative along coordinate lines, the
  slice formulas for the scalar partials, and the line identity
  `fderiv_fderiv_apply_line_FIN06817` used for the second-order Fréchet entries.

Proof: on the positive-radicand patch `R` is a composition of the polynomial radicand with
`Real.sqrt`, so `HasFDerivAt.sqrt` gives the first-order Fréchet derivative
`(1 / (2R)) (2(-4+u) du + dz)`. At the origin this gives `R = 4`, `R_u = -1`, `R_z = 1/8`. The
second-order Fréchet entries come from differentiating `fderiv R` along the coordinate lines, using
that `fderiv R` agrees with an explicit closed form near the origin on each line. The scalar second
partials are the derivatives of the one-variable slice derivatives, evaluated by the same closed
forms.

R5 notes:
* Domain and codomain: the function is read on `EuclideanSpace ℝ (Fin 2)`, with `w 0 = u` and
  `w 1 = z`. This is the coordinate convention of FIN068.38 and FIN068.37 (`quarticPsi_FIN066`
  takes `EuclideanSpace ℝ (Fin 2)`). The origin `(0, 0)` of the specification is the zero vector.
* No hypothesis is added. The specification's statement is unconditional, and the radicand is
  positive at the origin (value `16`), so the positive-radical patch is used only through the
  `HasFDerivAt.sqrt` side condition at the origin and at points near it.
* Scalar partials are read as one-variable derivatives of coordinate slices:
  `R_u` is `deriv (fun t => R !₂[t, 0]) 0` and `R_z` is `deriv (fun t => R !₂[0, t]) 0`.
* Scalar second partials are read as the iterated slice derivatives:
  `R_uu = deriv (fun t => deriv (fun s => R !₂[s, 0]) t) 0`,
  `R_uz = deriv (fun t => deriv (fun s => R !₂[s, t]) 0) 0` (first differentiate in `u`, then
  in `z`), `R_zu = deriv (fun t => deriv (fun s => R !₂[t, s]) 0) 0` (first differentiate in `z`,
  then in `u`), and `R_zz = deriv (fun t => deriv (fun s => R !₂[0, s]) t) 0`. Both mixed
  orders are stated and proved separately, although they agree here.
* The Fréchet entries use the basis `EuclideanSpace.single i 1` for `e_i`. The second derivative
  is the bilinear `fderiv ℝ (fderiv ℝ R) 0 v w`, read as the Hessian entry. The scalar and
  Fréchet forms are both part of the statement, so the separation the specification asks for is
  explicit.
* The specification's "derivative bounds in the directional norm" and the "positive-radical
  patch" formulas are not stated separately; only the values at the origin are claimed, as the
  specification's statement lists.
* `Real.sqrt` is the square root on `ℝ`. Its nonnegativity is used only through the identity
  `Real.sqrt (4 ^ 2) = 4` at the origin.
* The specification's `(0,0)` value `R = 4` is `radicalR_FIN06817 0 = 4`; no normalization is
  applied to the function.
-/

open Real Filter Topology

namespace DGPS.Frontier.FIN068

noncomputable def radicalR_FIN06817 (w : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Real.sqrt ((-4 + w 0) ^ 2 + w 1)

lemma hasFDerivAt_radicand_FIN06817 (q : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (fun w : EuclideanSpace ℝ (Fin 2) => (-4 + w 0) ^ 2 + w 1)
      ((2 * (-4 + q 0)) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) + EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) q := by
  have h0 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin 2) => w 0)
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) q :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt
  have h1 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin 2) => w 1)
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) q :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt
  have h2 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin 2) => -4 + w 0)
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) q := h0.const_add (-4 : ℝ)
  have h3 := h2.pow 2
  have h4 := h3.add h1
  refine h4.congr_fderiv ?_
  ext v
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma hasFDerivAt_radicalR_FIN06817 (q : EuclideanSpace ℝ (Fin 2))
    (hq : 0 < (-4 + q 0) ^ 2 + q 1) :
    HasFDerivAt radicalR_FIN06817
      ((1 / (2 * Real.sqrt ((-4 + q 0) ^ 2 + q 1))) •
        ((2 * (-4 + q 0)) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) + EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2))) q :=
  (hasFDerivAt_radicand_FIN06817 q).sqrt hq.ne'

lemma fderiv_radicalR_apply_FIN06817 (q v : EuclideanSpace ℝ (Fin 2))
    (hq : 0 < (-4 + q 0) ^ 2 + q 1) :
    fderiv ℝ radicalR_FIN06817 q v =
      (1 / (2 * Real.sqrt ((-4 + q 0) ^ 2 + q 1))) * (2 * (-4 + q 0) * v 0 + v 1) := by
  rw [(hasFDerivAt_radicalR_FIN06817 q hq).fderiv]
  simp
  ring

lemma contDiffAt_radicalR_FIN06817 :
    ContDiffAt ℝ 2 radicalR_FIN06817 0 := by
  unfold radicalR_FIN06817
  have hpoly : ContDiff ℝ 2 (fun w : EuclideanSpace ℝ (Fin 2) => (-4 + w 0) ^ 2 + w 1) := by
    fun_prop
  have hne : (fun w : EuclideanSpace ℝ (Fin 2) => (-4 + w 0) ^ 2 + w 1) 0 ≠ 0 := by
    simp
  exact (hpoly.contDiffAt).sqrt hne

lemma differentiableAt_fderiv_radicalR_FIN06817 :
    DifferentiableAt ℝ (fderiv ℝ radicalR_FIN06817) 0 :=
  ((contDiffAt_radicalR_FIN06817.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num))

lemma fderiv_fderiv_apply_line_FIN06817 (w v : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fderiv ℝ radicalR_FIN06817) 0 w v =
      deriv (fun t : ℝ => fderiv ℝ radicalR_FIN06817 (t • w) v) 0 := by
  have hline : HasDerivAt (fun t : ℝ => t • w) w 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
  have hF := differentiableAt_fderiv_radicalR_FIN06817.hasFDerivAt
  have hc : HasDerivAt (fun t : ℝ => fderiv ℝ radicalR_FIN06817 (t • w))
      (fderiv ℝ (fderiv ℝ radicalR_FIN06817) 0 w) 0 := by
    have hF' : HasFDerivAt (fderiv ℝ radicalR_FIN06817) (fderiv ℝ (fderiv ℝ radicalR_FIN06817) 0)
        ((fun t : ℝ => t • w) 0) := by
      simpa using hF
    exact hF'.comp_hasDerivAt (x := (0:ℝ)) hline
  have hv := hc.clm_apply (hasDerivAt_const (0:ℝ) v)
  rw [hv.deriv]
  simp


lemma radicalR_zero_FIN06817 : radicalR_FIN06817 0 = 4 := by
  unfold radicalR_FIN06817
  have h : (-4 + (0 : EuclideanSpace ℝ (Fin 2)) 0) ^ 2 + (0 : EuclideanSpace ℝ (Fin 2)) 1 = 4 ^ 2 := by
    norm_num
  rw [h, Real.sqrt_sq (by norm_num)]

lemma fderiv_radicalR_zero_FIN06817 (v : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ radicalR_FIN06817 0 v = (1 / 8) * (-8 * v 0 + v 1) := by
  have h := fderiv_radicalR_apply_FIN06817 0 v (by norm_num)
  rw [h]
  norm_num

lemma line_u_FIN06817 :
    (fun s : ℝ => (!₂[s, (0 : ℝ)] : EuclideanSpace ℝ (Fin 2))) =
      fun s => s • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) := by
  funext s
  ext i
  fin_cases i <;> simp

lemma line_z_FIN06817 :
    (fun s : ℝ => (!₂[(0 : ℝ), s] : EuclideanSpace ℝ (Fin 2))) =
      fun s => s • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
  funext s
  ext i
  fin_cases i <;> simp

lemma fderiv_radicalR_line_u_FIN06817 (t : ℝ) (ht : t < 4) (v : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ radicalR_FIN06817 (t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) v =
      (1 / (2 * (4 - t))) * (2 * (-4 + t) * v 0 + v 1) := by
  have hq : (-4 + (t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) 0) ^ 2 +
      (t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) 1 = (4 - t) ^ 2 := by
    simp
    ring
  have hpos : 0 < (4 - t) ^ 2 := by
    have : (4 - t) ≠ 0 := by intro h; linarith
    positivity
  rw [fderiv_radicalR_apply_FIN06817 _ _ (by rw [hq]; exact hpos), hq, Real.sqrt_sq (by linarith)]
  simp

lemma fderiv_radicalR_line_z_FIN06817 (t : ℝ) (ht : -16 < t) (v : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ radicalR_FIN06817 (t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) v =
      (1 / (2 * Real.sqrt (16 + t))) * (-8 * v 0 + v 1) := by
  have hq : (-4 + (t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) 0) ^ 2 +
      (t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) 1 = 16 + t := by
    simp
    norm_num
  have h0 : (t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) 0 = 0 := by
    simp
  have h1 : (t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) 1 = t := by
    simp
  rw [fderiv_radicalR_apply_FIN06817 _ _ (by rw [h0, h1]; linarith), h0, h1]
  norm_num


lemma sqrt16_FIN06817 : Real.sqrt 16 = 4 := by
  rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

lemma hasDerivAt_inv_sqrt_FIN06817 :
    HasDerivAt (fun t : ℝ => 1 / (2 * Real.sqrt (16 + t))) (-1 / 256) 0 := by
  have hs : HasDerivAt (fun t : ℝ => 16 + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add 16
  have hsq := hs.sqrt (by norm_num)
  have h2 := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).div (hsq.const_mul 2) (by norm_num [sqrt16_FIN06817])
  convert h2 using 1
  norm_num [sqrt16_FIN06817]

lemma hasDerivAt_inv_lin_FIN06817 :
    HasDerivAt (fun t : ℝ => 1 / (2 * (4 - t))) (1 / 32) 0 := by
  have hs : HasDerivAt (fun t : ℝ => 4 - t) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub 4
  have h2 := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).div (hs.const_mul 2) (by norm_num)
  convert h2 using 1
  norm_num

lemma deriv_line_FIN06817 (w : EuclideanSpace ℝ (Fin 2)) :
    deriv (fun t : ℝ => radicalR_FIN06817 (t • w)) 0 = fderiv ℝ radicalR_FIN06817 0 w := by
  have hR : HasFDerivAt radicalR_FIN06817 (fderiv ℝ radicalR_FIN06817 0) ((fun t : ℝ => t • w) 0) := by
    rw [show ((fun t : ℝ => t • w) 0) = (0 : EuclideanSpace ℝ (Fin 2)) by simp]
    exact (contDiffAt_radicalR_FIN06817.differentiableAt (by norm_num)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => t • w) w 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
  exact (hR.comp_hasDerivAt (x := (0 : ℝ)) hline).deriv

lemma deriv_u_FIN06817 :
    deriv (fun t : ℝ => radicalR_FIN06817 !₂[t, (0 : ℝ)]) 0 = -1 := by
  have h : (fun t : ℝ => radicalR_FIN06817 !₂[t, (0 : ℝ)]) =
      fun t : ℝ => radicalR_FIN06817 (t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) := by
    funext t
    congr 1
    ext i
    fin_cases i <;> simp
  rw [h, deriv_line_FIN06817, fderiv_radicalR_zero_FIN06817]
  simp

lemma deriv_z_FIN06817 :
    deriv (fun t : ℝ => radicalR_FIN06817 !₂[(0 : ℝ), t]) 0 = 1 / 8 := by
  have h : (fun t : ℝ => radicalR_FIN06817 !₂[(0 : ℝ), t]) =
      fun t : ℝ => radicalR_FIN06817 (t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) := by
    funext t
    congr 1
    ext i
    fin_cases i <;> simp
  rw [h, deriv_line_FIN06817, fderiv_radicalR_zero_FIN06817]
  simp

lemma fderiv_e0_FIN06817 :
    fderiv ℝ radicalR_FIN06817 0 (EuclideanSpace.single 0 1) = -1 := by
  rw [fderiv_radicalR_zero_FIN06817]
  simp

lemma fderiv_e1_FIN06817 :
    fderiv ℝ radicalR_FIN06817 0 (EuclideanSpace.single 1 1) = 1 / 8 := by
  rw [fderiv_radicalR_zero_FIN06817]
  simp

lemma fderivfderiv_uu_FIN06817 :
    fderiv ℝ (fderiv ℝ radicalR_FIN06817) 0 (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) = 0 := by
  rw [fderiv_fderiv_apply_line_FIN06817]
  have hev : (fun t : ℝ => fderiv ℝ radicalR_FIN06817 (t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) =ᶠ[𝓝 0] fun _ => (-1 : ℝ) := by
    filter_upwards [eventually_lt_nhds (show (0 : ℝ) < 4 by norm_num)] with t ht
    rw [fderiv_radicalR_line_u_FIN06817 t ht]
    have hne : (4 - t) ≠ 0 := by intro h; linarith
    simp
    field_simp
    ring
  rw [hev.deriv_eq]
  simp

lemma fderivfderiv_uz_FIN06817 :
    fderiv ℝ (fderiv ℝ radicalR_FIN06817) 0 (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) = 1 / 32 := by
  rw [fderiv_fderiv_apply_line_FIN06817]
  have hev : (fun t : ℝ => fderiv ℝ radicalR_FIN06817 (t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) =ᶠ[𝓝 0] fun t => 1 / (2 * (4 - t)) := by
    filter_upwards [eventually_lt_nhds (show (0 : ℝ) < 4 by norm_num)] with t ht
    rw [fderiv_radicalR_line_u_FIN06817 t ht]
    simp
  rw [hev.deriv_eq, hasDerivAt_inv_lin_FIN06817.deriv]

lemma fderivfderiv_zu_FIN06817 :
    fderiv ℝ (fderiv ℝ radicalR_FIN06817) 0 (EuclideanSpace.single 1 1) (EuclideanSpace.single 0 1) = 1 / 32 := by
  rw [fderiv_fderiv_apply_line_FIN06817]
  have hev : (fun t : ℝ => fderiv ℝ radicalR_FIN06817 (t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) =ᶠ[𝓝 0]
      fun t => 1 / (2 * Real.sqrt (16 + t)) * (-8) := by
    filter_upwards [eventually_gt_nhds (show (-16 : ℝ) < 0 by norm_num)] with t ht
    rw [fderiv_radicalR_line_z_FIN06817 t ht]
    simp
  rw [hev.deriv_eq, (hasDerivAt_inv_sqrt_FIN06817.mul_const (-8)).deriv]
  norm_num

lemma fderivfderiv_zz_FIN06817 :
    fderiv ℝ (fderiv ℝ radicalR_FIN06817) 0 (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1) = -1 / 256 := by
  rw [fderiv_fderiv_apply_line_FIN06817]
  have hev : (fun t : ℝ => fderiv ℝ radicalR_FIN06817 (t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) =ᶠ[𝓝 0]
      fun t => 1 / (2 * Real.sqrt (16 + t)) := by
    filter_upwards [eventually_gt_nhds (show (-16 : ℝ) < 0 by norm_num)] with t ht
    rw [fderiv_radicalR_line_z_FIN06817 t ht]
    simp
  rw [hev.deriv_eq, hasDerivAt_inv_sqrt_FIN06817.deriv]

lemma slice_u_FIN06817 (z : ℝ) :
    (fun s : ℝ => radicalR_FIN06817 !₂[s, z]) = fun s => Real.sqrt ((-4 + s) ^ 2 + z) := by
  funext s
  simp [radicalR_FIN06817]

lemma slice_z_FIN06817 (a : ℝ) :
    (fun s : ℝ => radicalR_FIN06817 !₂[a, s]) = fun s => Real.sqrt ((-4 + a) ^ 2 + s) := by
  funext s
  simp [radicalR_FIN06817]

lemma deriv_slice_u_FIN06817 (z t : ℝ) (h : 0 < (-4 + t) ^ 2 + z) :
    deriv (fun s : ℝ => Real.sqrt ((-4 + s) ^ 2 + z)) t =
      (2 * (-4 + t)) / (2 * Real.sqrt ((-4 + t) ^ 2 + z)) := by
  have h1 : HasDerivAt (fun s : ℝ => -4 + s) 1 t := by
    simpa using (hasDerivAt_id t).const_add (-4 : ℝ)
  have h2 : HasDerivAt (fun s : ℝ => (-4 + s) ^ 2 + z) (2 * (-4 + t)) t := by
    have h3 := (h1.pow 2).add_const z
    convert h3 using 1
    norm_num
  exact (h2.sqrt h.ne').deriv

lemma deriv_slice_z_FIN06817 (a b : ℝ) (h : 0 < (-4 + a) ^ 2 + b) :
    deriv (fun s : ℝ => Real.sqrt ((-4 + a) ^ 2 + s)) b =
      1 / (2 * Real.sqrt ((-4 + a) ^ 2 + b)) := by
  have h1 : HasDerivAt (fun s : ℝ => (-4 + a) ^ 2 + s) 1 b := by
    simpa using (hasDerivAt_id b).const_add ((-4 + a) ^ 2)
  exact (h1.sqrt h.ne').deriv

lemma radicand_pos_FIN06817 (t : ℝ) (ht : t < 4) : 0 < (-4 + t) ^ 2 + 0 := by
  rw [add_zero, show (-4 + t) ^ 2 = (4 - t) ^ 2 by ring]
  exact pow_pos (by linarith) 2

lemma sqrt_radicand_FIN06817 (t : ℝ) (ht : t < 4) :
    Real.sqrt ((-4 + t) ^ 2 + 0) = 4 - t := by
  rw [add_zero, show (-4 + t) ^ 2 = (4 - t) ^ 2 by ring]
  exact Real.sqrt_sq (by linarith)

lemma scalar_uu_FIN06817 :
    deriv (fun t : ℝ => deriv (fun s : ℝ => radicalR_FIN06817 !₂[s, (0 : ℝ)]) t) 0 = 0 := by
  have hev : (fun t : ℝ => deriv (fun s : ℝ => radicalR_FIN06817 !₂[s, (0 : ℝ)]) t)
      =ᶠ[𝓝 0] fun _ => (-1 : ℝ) := by
    filter_upwards [eventually_lt_nhds (show (0 : ℝ) < 4 by norm_num)] with t ht
    have hne : (4 - t) ≠ 0 := by intro h; linarith
    rw [slice_u_FIN06817 0, deriv_slice_u_FIN06817 0 t (radicand_pos_FIN06817 t ht),
      sqrt_radicand_FIN06817 t ht]
    rw [div_eq_iff (mul_ne_zero two_ne_zero hne)]
    ring
  rw [hev.deriv_eq]
  simp

lemma scalar_uz_FIN06817 :
    deriv (fun t : ℝ => deriv (fun s : ℝ => radicalR_FIN06817 !₂[s, t]) 0) 0 = 1 / 32 := by
  have hev : (fun t : ℝ => deriv (fun s : ℝ => radicalR_FIN06817 !₂[s, t]) 0)
      =ᶠ[𝓝 0] fun t => (-8 : ℝ) * (1 / (2 * Real.sqrt (16 + t))) := by
    filter_upwards [eventually_gt_nhds (show (-16 : ℝ) < 0 by norm_num)] with t ht
    have hpos : 0 < (-4 + (0 : ℝ)) ^ 2 + t := by
      norm_num
      linarith
    rw [slice_u_FIN06817 t, deriv_slice_u_FIN06817 t 0 hpos,
      show ((-4 : ℝ) + 0) ^ 2 = 16 by norm_num]
    ring
  rw [hev.deriv_eq, (hasDerivAt_inv_sqrt_FIN06817.const_mul (-8)).deriv]
  norm_num

lemma scalar_zu_FIN06817 :
    deriv (fun t : ℝ => deriv (fun s : ℝ => radicalR_FIN06817 !₂[t, s]) 0) 0 = 1 / 32 := by
  have hev : (fun t : ℝ => deriv (fun s : ℝ => radicalR_FIN06817 !₂[t, s]) 0)
      =ᶠ[𝓝 0] fun t => 1 / (2 * (4 - t)) := by
    filter_upwards [eventually_lt_nhds (show (0 : ℝ) < 4 by norm_num)] with t ht
    rw [slice_z_FIN06817 t, deriv_slice_z_FIN06817 t 0 (radicand_pos_FIN06817 t ht),
      sqrt_radicand_FIN06817 t ht]
  rw [hev.deriv_eq, hasDerivAt_inv_lin_FIN06817.deriv]

lemma scalar_zz_FIN06817 :
    deriv (fun t : ℝ => deriv (fun s : ℝ => radicalR_FIN06817 !₂[(0 : ℝ), s]) t) 0 = -1 / 256 := by
  have hev : (fun t : ℝ => deriv (fun s : ℝ => radicalR_FIN06817 !₂[(0 : ℝ), s]) t)
      =ᶠ[𝓝 0] fun t => 1 / (2 * Real.sqrt (16 + t)) := by
    filter_upwards [eventually_gt_nhds (show (-16 : ℝ) < 0 by norm_num)] with t ht
    have hpos : 0 < (-4 + (0 : ℝ)) ^ 2 + t := by
      norm_num
      linarith
    rw [slice_z_FIN06817 0, deriv_slice_z_FIN06817 0 t hpos,
      show ((-4 : ℝ) + 0) ^ 2 = 16 by norm_num]
  rw [hev.deriv_eq, hasDerivAt_inv_sqrt_FIN06817.deriv]

/-- Main declaration: value, first-order scalar partials, second-order scalar partials,
the first-order Frechet entries, and the second-order Frechet entries at `0`. -/
theorem fin068_17_radical_first_second_jet :
    radicalR_FIN06817 0 = 4 ∧
    deriv (fun t : ℝ => radicalR_FIN06817 !₂[t, (0 : ℝ)]) 0 = -1 ∧
    deriv (fun t : ℝ => radicalR_FIN06817 !₂[(0 : ℝ), t]) 0 = 1 / 8 ∧
    deriv (fun t : ℝ => deriv (fun s : ℝ => radicalR_FIN06817 !₂[s, (0 : ℝ)]) t) 0 = 0 ∧
    deriv (fun t : ℝ => deriv (fun s : ℝ => radicalR_FIN06817 !₂[s, t]) 0) 0 = 1 / 32 ∧
    deriv (fun t : ℝ => deriv (fun s : ℝ => radicalR_FIN06817 !₂[t, s]) 0) 0 = 1 / 32 ∧
    deriv (fun t : ℝ => deriv (fun s : ℝ => radicalR_FIN06817 !₂[(0 : ℝ), s]) t) 0 = -1 / 256 ∧
    fderiv ℝ radicalR_FIN06817 0 (EuclideanSpace.single 0 1) = -1 ∧
    fderiv ℝ radicalR_FIN06817 0 (EuclideanSpace.single 1 1) = 1 / 8 ∧
    fderiv ℝ (fderiv ℝ radicalR_FIN06817) 0 (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) = 0 ∧
    fderiv ℝ (fderiv ℝ radicalR_FIN06817) 0 (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) = 1 / 32 ∧
    fderiv ℝ (fderiv ℝ radicalR_FIN06817) 0 (EuclideanSpace.single 1 1) (EuclideanSpace.single 0 1) = 1 / 32 ∧
    fderiv ℝ (fderiv ℝ radicalR_FIN06817) 0 (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1) = -1 / 256 :=
  ⟨radicalR_zero_FIN06817, deriv_u_FIN06817, deriv_z_FIN06817, scalar_uu_FIN06817,
    scalar_uz_FIN06817, scalar_zu_FIN06817, scalar_zz_FIN06817, fderiv_e0_FIN06817,
    fderiv_e1_FIN06817, fderivfderiv_uu_FIN06817, fderivfderiv_uz_FIN06817,
    fderivfderiv_zu_FIN06817, fderivfderiv_zz_FIN06817⟩

end DGPS.Frontier.FIN068
