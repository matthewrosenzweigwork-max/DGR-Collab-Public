import DGPS.Frontier.FIN068.T18
import DGPS.Frontier.FIN068.T19
import DGPS.Frontier.FIN068.T20

/-!
Task id and title: FIN068.21, Gradient remainder (module `DGPS.Frontier.FIN068.T21`).

Provides:
* `DGPS.Frontier.FIN068.fin068_21_gradient_remainder`: let `δ < 1`, `B = {|u| ≤ δ, |z| ≤ δ}`
  (`fixedRect_FIN06819 δ`), `J = fun q => liftPotential_FIN06804 q.1 q.2` and `P = quadP_FIN06820`.
  If `M₃` bounds the third derivative of `J` on `B` in the `ℓ¹` form of FIN068.19, then for every
  `h ∈ B` and every direction `v`,
  `|D(J - P)(h)[v]| ≤ (M₃ / 2) ‖h‖₁² ‖v‖₁`, with `‖(a,b)‖₁ = |a| + |b|`.
  Here `D f(x)[v] = fderiv ℝ f x v` (the Fréchet derivative on `ℝ × ℝ`).
* `DGPS.Frontier.FIN068.fin068_21_gradient_remainder_exists`: there are `δ ∈ (0,1)` and `M₃ ≥ 0`
  for which the bound above holds for all `h ∈ B` and all `v` (combination with FIN068.19 and
  FIN068.20, which supply `δ` and `M₃`).
* Helper declarations, all with suffix `_FIN06821` and not part of the interface: `liftJ_FIN06821`,
  `remF_FIN06821` (the function `J - P`), `mem_patch_FIN06821`, `contDiffAt_liftJ_FIN06821`,
  `contDiff_quadP_FIN06821`, the line derivative lemmas on `ℝ × ℝ`, the identity
  `D²(J - P)(x)[h,v] = D²J(x)[h,v] - D²P(x)[h,v]`, `fderiv_liftJ_zero_FIN06821`
  (`DJ(0) = 0`), `fderiv_remF_zero_FIN06821` (`D(J - P)(0) = 0`), and the boundary inequality used
  in the proof.

Proof: `D(J - P)(0) = 0`: `DJ(0) = 0` by the FIN068.18 first-order partials (`-5/κ + b = 0` and
`1/(2κη) - b/8 = 0`), and `DP(0) = 0` since `P` has no linear part. For fixed `h ∈ B` and `v`, the
function `g(s) = D(J - P)(s h)[v]` satisfies `g(0) = 0` and `g'(s) = D²(J - P)(s h)[h, v]`. The
second derivative of `P` is constant, so `D²(J - P)(s h)[h,v] = D²J(s h)[h,v] - D²P(s h)[h,v]`, and
FIN068.20 at the point `s h ∈ B` (with `‖s h‖₁ = s ‖h‖₁` for `s ∈ [0,1]`) gives
`|g'(s)| ≤ M₃ s ‖h‖₁² ‖v‖₁`. Integrating over `[0,1]` gives the bound `(M₃/2) ‖h‖₁² ‖v‖₁`. The
integral is realized through Mathlib's boundary inequality
`image_norm_le_of_norm_deriv_right_le_deriv_boundary` with the comparison function `s ↦ K s²/2`,
`K = M₃ ‖h‖₁² ‖v‖₁`, whose derivative `K s` dominates `|g'(s)|`.

R5 notes:
* Hypotheses: `δ < 1` (the patch condition of FIN068.19 and FIN068.20) and `hM`, which says that
  `M₃` bounds the third derivative of `J` on `B`. These are the hypotheses of FIN068.20 and are not
  new. The lower bound `0 < δ` and the sign `0 ≤ M₃` are not used, and `M₃` is not assumed to be
  nonnegative in the main declaration. The existence declaration removes `hM` and `δ < 1` by
  FIN068.19 and FIN068.20.
* Norm: `‖D(J - P)(h)‖` is read as the `ℓ¹` operator norm of the linear form (the supremum of
  `|D(J-P)(h)[v]|` over `‖v‖₁ ≤ 1`). The bound is stated in the equivalent directional form
  `|D(J-P)(h)[v]| ≤ (M₃/2)‖h‖₁²‖v‖₁` for all `v`. This is the same convention as FIN068.19 and
  FIN068.20. Mathlib's operator norm on `ℝ × ℝ` is the sup norm, which differs from the `ℓ¹` one by
  up to a factor 2, so the constant `M₃/2` is not read through it.
* `D(J - P)(0) = 0` is proved, not assumed. It uses the campaign relations `κ = 5/b` and `η = 4/5`,
  taken from the definitions `quarticKappa = 5 / quarticB` and `quarticEta = 4 / 5`. The relation
  `1/κ = b/5` is `inv_quarticKappa_FIN06820` from FIN068.20. FIN068.03 and FIN068.05 are not
  imported. The derivative `deriv besselRatio 4` is treated as an opaque real number.
* The second derivative `D²(J - P)(x)[h,v]` is `fderiv ℝ (fderiv ℝ (J - P)) x h v`, that is the
  first direction `h` is the outer one. This matches `iteratedFDeriv_two_apply` and FIN068.20.
* The integral over `[0,1]` is replaced by the boundary inequality with `B(s) = K s²/2`. It
  gives the same constant without integrability side conditions. The FTC identifier named in the
  specification (`integral_id` style) is not used.
* The derivative `D(J-P)` is Mathlib's Fréchet `fderiv` on `ℝ × ℝ` for the lifted potential
  `liftPotential_FIN06804 q.1 q.2` (FIN068.04). The Euclidean reading of FIN068.18 is not used.
* `P` is `quadP_FIN06820` of FIN068.20 (`J(0,0) + A u²/2 - d u z/32 + d z²/512`). Its
  constants are `A = quarticB/5 - deriv besselRatio 4` and `d = quarticB - 4 deriv besselRatio 4`.
-/

open Filter Topology DGPS.Models DGPS.Circle.BesselMoments
open scoped ContDiff

namespace DGPS.Frontier.FIN068

/-- The lifted potential `J` on `ℝ × ℝ`, `J q = liftPotential q.1 q.2` (FIN068.04). -/
noncomputable def liftJ_FIN06821 (q : ℝ × ℝ) : ℝ := liftPotential_FIN06804 q.1 q.2

/-- The difference `J - P` on `ℝ × ℝ`. -/
noncomputable def remF_FIN06821 (q : ℝ × ℝ) : ℝ := liftPotential_FIN06804 q.1 q.2 - quadP_FIN06820 q

lemma mem_patch_FIN06821 {δ : ℝ} (hδ1 : δ < 1) {p : ℝ × ℝ} (hp : p ∈ fixedRect_FIN06819 δ) :
    p ∈ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1 := by
  obtain ⟨hp1, hp2⟩ := hp
  exact ⟨abs_lt.mp (lt_of_le_of_lt hp1 hδ1), abs_lt.mp (lt_of_le_of_lt hp2 hδ1)⟩

lemma contDiffAt_liftJ_FIN06821 (y : ℝ × ℝ)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ 2 liftJ_FIN06821 y :=
  ((fin068_04_lift_two_ordinary_variables).1.contDiffAt
    ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hy)).of_le (by simp)

lemma contDiff_quadP_FIN06821 : ContDiff ℝ 2 quadP_FIN06820 := by
  unfold quadP_FIN06820
  fun_prop

lemma contDiffAt_remF_FIN06821 (y : ℝ × ℝ)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ 2 remF_FIN06821 y :=
  (contDiffAt_liftJ_FIN06821 y hy).sub contDiff_quadP_FIN06821.contDiffAt

lemma deriv_line_zero_FIN06821 (f : ℝ × ℝ → ℝ) (hf : ContDiffAt ℝ 2 f 0) (a : ℝ × ℝ) :
    deriv (fun t : ℝ => f (t • a)) 0 = fderiv ℝ f 0 a := by
  have hR : HasFDerivAt f (fderiv ℝ f 0) ((fun t : ℝ => t • a) 0) := by
    rw [show ((fun t : ℝ => t • a) 0) = (0 : ℝ × ℝ) by simp]
    exact (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => t • a) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const a
  exact (hR.comp_hasDerivAt (x := (0 : ℝ)) hline).deriv

lemma fderiv_liftJ_zero_FIN06821 (v : ℝ × ℝ) : fderiv ℝ liftJ_FIN06821 0 v = 0 := by
  have hJ : ContDiffAt ℝ 2 liftJ_FIN06821 0 :=
    contDiffAt_liftJ_FIN06821 0 (by simp)
  obtain ⟨hu, hz, -⟩ := fin068_18_assemble_jet_j
  have hk : (5 : ℝ) / quarticKappa = quarticB := by
    rw [div_eq_mul_one_div, inv_quarticKappa_FIN06820]
    ring
  have h1 : fderiv ℝ liftJ_FIN06821 0 ((1 : ℝ), (0 : ℝ)) = 0 := by
    rw [← deriv_line_zero_FIN06821 liftJ_FIN06821 hJ ((1 : ℝ), (0 : ℝ))]
    have hfun : (fun t : ℝ => liftJ_FIN06821 (t • ((1 : ℝ), (0 : ℝ)))) =
        fun t : ℝ => liftPotential_FIN06804 t 0 := by
      funext t
      simp [liftJ_FIN06821]
    rw [hfun, hu]
    have hk' : -(5 : ℝ) / quarticKappa = -quarticB := by
      rw [neg_div, hk]
    rw [hk']
    ring
  have h2 : fderiv ℝ liftJ_FIN06821 0 ((0 : ℝ), (1 : ℝ)) = 0 := by
    rw [← deriv_line_zero_FIN06821 liftJ_FIN06821 hJ ((0 : ℝ), (1 : ℝ))]
    have hfun : (fun t : ℝ => liftJ_FIN06821 (t • ((0 : ℝ), (1 : ℝ)))) =
        fun t : ℝ => liftPotential_FIN06804 0 t := by
      funext t
      simp [liftJ_FIN06821]
    rw [hfun, hz]
    have he : (1 : ℝ) / (2 * quarticKappa * quarticEta) = (1 / quarticKappa) * (5 / 8) := by
      unfold quarticEta
      ring
    rw [he, inv_quarticKappa_FIN06820]
    ring
  have hdec : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  calc fderiv ℝ liftJ_FIN06821 0 v
      = fderiv ℝ liftJ_FIN06821 0 (v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ))) := by
        rw [← hdec]
    _ = 0 := by
        rw [map_add, map_smul, map_smul, h1, h2]
        simp

lemma fderiv_quadP_zero_FIN06821 (v : ℝ × ℝ) : fderiv ℝ quadP_FIN06820 0 v = 0 := by
  rw [fderiv_quadP_FIN06820]
  simp

lemma fderiv_remF_zero_FIN06821 (v : ℝ × ℝ) : fderiv ℝ remF_FIN06821 0 v = 0 := by
  have hJ : DifferentiableAt ℝ liftJ_FIN06821 0 :=
    (contDiffAt_liftJ_FIN06821 0 (by simp)).differentiableAt (by norm_num)
  have hP : DifferentiableAt ℝ quadP_FIN06820 0 :=
    (contDiff_quadP_FIN06821.contDiffAt).differentiableAt (by norm_num)
  have hfun : remF_FIN06821 = fun q => liftJ_FIN06821 q - quadP_FIN06820 q := rfl
  have key : fderiv ℝ (fun q => liftJ_FIN06821 q - quadP_FIN06820 q) 0 =
      fderiv ℝ liftJ_FIN06821 0 - fderiv ℝ quadP_FIN06820 0 := fderiv_sub hJ hP
  rw [hfun, key, sub_apply, fderiv_liftJ_zero_FIN06821, fderiv_quadP_zero_FIN06821, sub_zero]

/-- Derivative of `s ↦ D(J - P)(s h)[v]` at a point `t`, with value `D²(J - P)(t h)[h, v]`. -/
lemma hasDerivAt_remF_line_FIN06821 (h v : ℝ × ℝ) (t : ℝ)
    (hF : ContDiffAt ℝ 2 remF_FIN06821 (t • h)) :
    HasDerivAt (fun s : ℝ => fderiv ℝ remF_FIN06821 (s • h) v)
      (fderiv ℝ (fderiv ℝ remF_FIN06821) (t • h) h v) t := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ remF_FIN06821) (t • h) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hline : HasDerivAt (fun s : ℝ => s • h) h t := by
    simpa using (hasDerivAt_id t).smul_const h
  have hc : HasDerivAt (fun s : ℝ => fderiv ℝ remF_FIN06821 (s • h))
      (fderiv ℝ (fderiv ℝ remF_FIN06821) (t • h) h) t :=
    hdiff.hasFDerivAt.comp_hasDerivAt t hline
  simpa using hc.clm_apply (hasDerivAt_const t v)

/-- The second derivative of `J - P` splits as `D²J - D²P` at a point of the patch. -/
lemma fderiv_fderiv_remF_FIN06821 (y h v : ℝ × ℝ)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1) :
    fderiv ℝ (fderiv ℝ remF_FIN06821) y h v =
      iteratedFDeriv ℝ 2 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2) y ![h, v] -
        iteratedFDeriv ℝ 2 quadP_FIN06820 y ![h, v] := by
  have hJ' : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2) y :=
    contDiffAt_liftJ_FIN06821 y hy
  have hP : ContDiffAt ℝ 2 quadP_FIN06820 y := contDiff_quadP_FIN06821.contDiffAt
  have hs : iteratedFDeriv ℝ 2 remF_FIN06821 y =
      iteratedFDeriv ℝ 2 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2) y -
        iteratedFDeriv ℝ 2 quadP_FIN06820 y :=
    iteratedFDeriv_sub_apply hJ' hP
  have hs' := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℝ × ℝ) ℝ =>
    T ![h, v]) hs
  simp only [sub_apply, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hs' ⊢
  exact hs'

/-- Main declaration. See the module docstring. -/
theorem fin068_21_gradient_remainder (δ M₃ : ℝ) (hδ1 : δ < 1)
    (hM : ∀ x ∈ fixedRect_FIN06819 δ, ∀ h v w : ℝ × ℝ,
      |iteratedFDeriv ℝ 3 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2) x ![h, v, w]| ≤
        M₃ * (|h.1| + |h.2|) * (|v.1| + |v.2|) * (|w.1| + |w.2|)) :
    ∀ h ∈ fixedRect_FIN06819 δ, ∀ v : ℝ × ℝ,
      |fderiv ℝ (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2 - quadP_FIN06820 q) h v| ≤
        M₃ / 2 * (|h.1| + |h.2|) ^ 2 * (|v.1| + |v.2|) := by
  intro h hh v
  show |fderiv ℝ remF_FIN06821 h v| ≤ M₃ / 2 * (|h.1| + |h.2|) ^ 2 * (|v.1| + |v.2|)
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • h ∈ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1 :=
    fun t ht => mem_patch_FIN06821 hδ1 (smul_mem_fixedRect_FIN06820 hh ht)
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => fderiv ℝ remF_FIN06821 (s • h) v)
      (fderiv ℝ (fderiv ℝ remF_FIN06821) (t • h) h v) t := fun t ht =>
    hasDerivAt_remF_line_FIN06821 h v t (contDiffAt_remF_FIN06821 _ (hmem t ht))
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      |fderiv ℝ (fderiv ℝ remF_FIN06821) (t • h) h v| ≤
        M₃ * (|h.1| + |h.2|) ^ 2 * (|v.1| + |v.2|) * t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    rw [fderiv_fderiv_remF_FIN06821 _ h v (hmem t ht')]
    have hT := fin068_20_hessian_remainder δ M₃ hδ1 hM (t • h)
      (smul_mem_fixedRect_FIN06820 hh ht') h v
    have hnorm : |(t • h).1| + |(t • h).2| = t * (|h.1| + |h.2|) := by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul, abs_of_nonneg ht.1]
      ring
    rw [hnorm] at hT
    calc _ ≤ M₃ * (t * (|h.1| + |h.2|)) * (|h.1| + |h.2|) * (|v.1| + |v.2|) := hT
      _ = M₃ * (|h.1| + |h.2|) ^ 2 * (|v.1| + |v.2|) * t := by ring
  have hcont : ContinuousOn (fun s : ℝ => fderiv ℝ remF_FIN06821 (s • h) v) (Set.Icc 0 1) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hf' : ∀ x ∈ Set.Ico (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => fderiv ℝ remF_FIN06821 (s • h) v)
      (fderiv ℝ (fderiv ℝ remF_FIN06821) (x • h) h v) (Set.Ici x) x := fun x hx =>
    (hderiv x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt
  have hB : ∀ x : ℝ, HasDerivAt (fun x : ℝ => M₃ * (|h.1| + |h.2|) ^ 2 * (|v.1| + |v.2|) * x ^ 2 / 2)
      (M₃ * (|h.1| + |h.2|) ^ 2 * (|v.1| + |v.2|) * x) x := by
    intro x
    have := ((hasDerivAt_pow 2 x).const_mul (M₃ * (|h.1| + |h.2|) ^ 2 * (|v.1| + |v.2|))).div_const 2
    convert this using 1
    norm_num
    ring
  have hbnd : ∀ x ∈ Set.Ico (0 : ℝ) 1, ‖fderiv ℝ (fderiv ℝ remF_FIN06821) (x • h) h v‖ ≤
      M₃ * (|h.1| + |h.2|) ^ 2 * (|v.1| + |v.2|) * x := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact hbound x hx
  have ha : ‖(fun s : ℝ => fderiv ℝ remF_FIN06821 (s • h) v) 0‖ ≤
      (fun x : ℝ => M₃ * (|h.1| + |h.2|) ^ 2 * (|v.1| + |v.2|) * x ^ 2 / 2) 0 := by
    simp [fderiv_remF_zero_FIN06821]
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont hf' ha hB hbnd
    (Set.right_mem_Icc.2 zero_le_one)
  simp only [one_smul, Real.norm_eq_abs] at key
  linarith

/-- Combination with FIN068.19 and FIN068.20: there are `δ ∈ (0,1)` and `M₃ ≥ 0` such that the
gradient remainder bound holds at every point of the closed rectangle and in every direction. -/
theorem fin068_21_gradient_remainder_exists :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ M₃ : ℝ, 0 ≤ M₃ ∧
      ∀ h ∈ fixedRect_FIN06819 δ, ∀ v : ℝ × ℝ,
        |fderiv ℝ (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2 - quadP_FIN06820 q) h v| ≤
          M₃ / 2 * (|h.1| + |h.2|) ^ 2 * (|v.1| + |v.2|) := by
  obtain ⟨δ, hδ0, hδ1, -, -, M₃, hM₃, hM, -⟩ := fin068_20_hessian_remainder_exists
  exact ⟨δ, hδ0, hδ1, M₃, hM₃, fin068_21_gradient_remainder δ M₃ hδ1 hM⟩

end DGPS.Frontier.FIN068
