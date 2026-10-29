import DGPS.Frontier.FIN068.T18
import DGPS.Frontier.FIN068.T19

/-!
Task id and title: FIN068.20, Hessian remainder (module `DGPS.Frontier.FIN068.T20`).

Provides:
* `DGPS.Frontier.FIN068.fin068_20_hessian_remainder`: let `0 < δ < 1` (only `δ < 1` is used),
  `B = {|u| ≤ δ, |z| ≤ δ}` (`fixedRect_FIN06819 δ`), `J = fun q => liftPotential_FIN06804 q.1 q.2`
  on `ℝ × ℝ` and `P(u,z) = J(0,0) + A u²/2 - d u z/32 + d z²/512` (`quadP_FIN06820`) with
  `A = quarticB/5 - deriv besselRatio 4` and `d = quarticB - 4 * deriv besselRatio 4`. If `M₃`
  satisfies `|D³J(x)[h,v,w]| ≤ M₃ ‖h‖₁ ‖v‖₁ ‖w‖₁` for all `x ∈ B` (the form of FIN068.19), then for
  every `h ∈ B` and all `v, w`,
  `|D²J(h)[v,w] - D²P(h)[v,w]| ≤ M₃ ‖h‖₁ ‖v‖₁ ‖w‖₁`, with `‖(a,b)‖₁ = |a| + |b|`. Here
  `D²f(x)[v,w] = iteratedFDeriv ℝ 2 f x ![v, w]`.
* `DGPS.Frontier.FIN068.fin068_20_hessian_remainder_hessian_P_eq_hessian_J_zero`: for every
  point `x` and all `v, w`, `D²P(x)[v,w] = D²J(0)[v,w]` (the identity `D²P = D²J(0)` of the proof).
* `DGPS.Frontier.FIN068.fin068_20_hessian_remainder_exists`: combination with FIN068.19: there are
  `δ ∈ (0,1)` and `M₃ ≥ 0` such that `B ⊆ (-1,1)²`, segments from zero stay in `B`, the third
  derivative bound holds on `B`, and the Hessian remainder bound holds for all `h ∈ B` and `v, w`.
* Helper declarations, all with suffix `_FIN06820` and not part of the interface: `constA_FIN06820`,
  `constD_FIN06820`, `quadP_FIN06820`, `hessCLM_FIN06820` (the constant Hessian of `P` as a
  continuous bilinear map), the iterated-slice lemmas on `ℝ × ℝ`, and the formula for `D²J(0)`.

Proof: `D²P` is the constant bilinear form `Hcl` (`P` is a quadratic polynomial, its derivative is
the linear map `x ↦ Hcl x`). `D²J(0)` has the same four entries: the iterated slice derivatives of
FIN068.18 are the entries of `fderiv (fderiv J) 0` by the generic slice lemmas, and the identities
`1/κ = b/5`, `A = 1/κ - v₀`, `-d/32 = v₀/8 - b/32`, `d/256 = b/256 - v₀/64` close the arithmetic.
For fixed `v, w` and `h ∈ B`, the function `φ(t) = D²J(t h)[v,w]` has derivative
`D³J(t h)[h,v,w]` on `[0,1]` (`iteratedFDeriv_succ_apply_left`, `J` smooth on the open patch, and
`t h ∈ B` by the segment property); the derivative is bounded by `M₃ ‖h‖₁ ‖v‖₁ ‖w‖₁`, so Mathlib's
mean value inequality `norm_image_sub_le_of_norm_deriv_le_segment'` gives
`|φ 1 - φ 0| ≤ M₃ ‖h‖₁ ‖v‖₁ ‖w‖₁`. Then `φ 1 = D²J(h)[v,w]` and `φ 0 = D²J(0)[v,w] = D²P(h)[v,w]`.

R5 notes:
* Hypotheses: the main declaration takes `δ < 1` (from "`δ ∈ (0,1)`" of FIN068.19; the lower bound
  `0 < δ` is not used and is not assumed) and the hypothesis `hM` that `M₃` bounds the third
  derivative on `B`. This is the hypothesis of the specification ("`M₃` bounds the third derivative",
  FIN068.19), not an added one; `0 ≤ M₃` is not needed. The existence of such `δ`, `M₃` is
  `fin068_20_hessian_remainder_exists` (via FIN068.19).
* "The stipulated operator norm" is read as the `ℓ¹` operator norm of a bilinear form, expressed
  as the directional estimate `|D²J(h)[v,w] - D²P(h)[v,w]| ≤ M₃ ‖h‖₁ ‖v‖₁ ‖w‖₁` for all `v, w`
  (equivalent to the operator norm bound by taking the supremum over `‖v‖₁, ‖w‖₁ ≤ 1`), as in
  FIN068.19 and as the specification's formalization note suggests. No Mathlib operator norm on
  `ℝ × ℝ` (which is the sup norm) and no custom `ℓ¹` Banach instance is used. The supremum over unit
  directions is not formalized separately.
* `P` is the explicit polynomial of FIN068.06, `J(0,0) + A u²/2 - d u z/32 + d z²/512`, with `A`
  and `d` written out as in FIN068.05 (`quarticB/5 - deriv besselRatio 4` and
  `quarticB - 4 * deriv besselRatio 4`), where `deriv besselRatio 4` is the derivative value
  `g'(4)`. The specification only says `D²P = D²J(0)`; this is proved
  (`..._hessian_P_eq_hessian_J_zero`) from the FIN068.18 jet and the campaign relations
  `κ = 5/b`, `η = 4/5` (reproved here as small helpers instead of importing FIN068.05).
* The second and third derivatives are Mathlib's `iteratedFDeriv ℝ 2` and `iteratedFDeriv ℝ 3` on
  `ℝ × ℝ`, with the derivative direction as the first argument; the same convention as
  FIN068.19. `J` is read on `ℝ × ℝ` as in FIN068.04 and FIN068.19 (`p.1 = u`, `p.2 = z`); the
  Euclidean reading of FIN068.18 is not used, only its scalar slice values.
* The integral form of the proof ("integrate from zero to one") is replaced by Mathlib's mean
  value inequality on `[0,1]`, which gives the same bound without integrability side conditions.
* No definition body of FIN068.37 or FIN068.38 is used.
-/

open Filter Topology DGPS.Models DGPS.Circle.BesselMoments
open scoped ContDiff

namespace DGPS.Frontier.FIN068

/-- The constant `A = b/5 - g'(4)`. -/
noncomputable def constA_FIN06820 : ℝ := quarticB / 5 - deriv besselRatio 4

/-- The constant `d = b - 4 g'(4)`. -/
noncomputable def constD_FIN06820 : ℝ := quarticB - 4 * deriv besselRatio 4

/-- The quadratic polynomial `P(u,z) = J(0,0) + A u²/2 - d u z/32 + d z²/512`. -/
noncomputable def quadP_FIN06820 (q : ℝ × ℝ) : ℝ :=
  liftPotential_FIN06804 0 0 + constA_FIN06820 * q.1 ^ 2 / 2 -
    constD_FIN06820 * q.1 * q.2 / 32 + constD_FIN06820 * q.2 ^ 2 / 512

/-- The constant Hessian of `P` as a continuous bilinear map. -/
noncomputable def hessCLM_FIN06820 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
      (constA_FIN06820 • ContinuousLinearMap.fst ℝ ℝ ℝ -
        (constD_FIN06820 / 32) • ContinuousLinearMap.snd ℝ ℝ ℝ) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      (-(constD_FIN06820 / 32) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (constD_FIN06820 / 256) • ContinuousLinearMap.snd ℝ ℝ ℝ)

lemma hessCLM_apply_FIN06820 (v w : ℝ × ℝ) :
    hessCLM_FIN06820 v w = (constA_FIN06820 * v.1 - constD_FIN06820 / 32 * v.2) * w.1 +
      (-(constD_FIN06820 / 32) * v.1 + constD_FIN06820 / 256 * v.2) * w.2 := by
  simp [hessCLM_FIN06820]
  ring

lemma hasFDerivAt_quadP_FIN06820 (x : ℝ × ℝ) :
    HasFDerivAt quadP_FIN06820 (hessCLM_FIN06820 x) x := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) x :=
    hasFDerivAt_fst
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    hasFDerivAt_snd
  have h11 := h1.mul h1
  have h12 := h1.mul h2
  have h22 := h2.mul h2
  have hP := (((hasFDerivAt_const (liftPotential_FIN06804 0 0) x).add
      (h11.const_mul (constA_FIN06820 / 2))).sub
      (h12.const_mul (constD_FIN06820 / 32))).add
      (h22.const_mul (constD_FIN06820 / 512))
  convert hP using 1
  · funext q
    simp only [quadP_FIN06820, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  · ext
    · simp [hessCLM_FIN06820]
      ring
    · simp [hessCLM_FIN06820]
      ring

lemma fderiv_quadP_FIN06820 : fderiv ℝ quadP_FIN06820 = ⇑hessCLM_FIN06820 := by
  funext x
  exact (hasFDerivAt_quadP_FIN06820 x).fderiv

lemma hessian_quadP_FIN06820 (x v w : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 quadP_FIN06820 x ![v, w] = hessCLM_FIN06820 v w := by
  rw [iteratedFDeriv_two_apply, fderiv_quadP_FIN06820]
  simp [ContinuousLinearMap.fderiv]

/-! Iterated slice lemmas on `ℝ × ℝ` (as in FIN068.18 for the Euclidean plane). -/

lemma hasDerivAt_fderiv_line_FIN06820 (f : ℝ × ℝ → ℝ) (hf : ContDiffAt ℝ 2 f 0)
    (w v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => fderiv ℝ f (t • w) v) (fderiv ℝ (fderiv ℝ f) 0 w v) 0 := by
  have hline : HasDerivAt (fun t : ℝ => t • w) w 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) 0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF := hdiff.hasFDerivAt
  have hc : HasDerivAt (fun t : ℝ => fderiv ℝ f (t • w))
      (fderiv ℝ (fderiv ℝ f) 0 w) 0 := by
    have hF' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0)
        ((fun t : ℝ => t • w) 0) := by
      simpa using hF
    exact hF'.comp_hasDerivAt (x := (0 : ℝ)) hline
  simpa using hc.clm_apply (hasDerivAt_const (0 : ℝ) v)

lemma tendsto_smul_zero_FIN06820 (a : ℝ × ℝ) :
    Tendsto (fun t : ℝ => t • a) (𝓝 0) (𝓝 0) := by
  have hc : Continuous fun t : ℝ => t • a := by fun_prop
  simpa using hc.tendsto 0

lemma deriv_deriv_slice_FIN06820 (f : ℝ × ℝ → ℝ) (hf : ContDiffAt ℝ 2 f 0) (a b : ℝ × ℝ) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => f (t • b + s • a)) 0) 0 =
      fderiv ℝ (fderiv ℝ f) 0 b a := by
  have hev : (fun t : ℝ => deriv (fun s : ℝ => f (t • b + s • a)) 0) =ᶠ[𝓝 0]
      fun t : ℝ => fderiv ℝ f (t • b) a := by
    filter_upwards [(tendsto_smul_zero_FIN06820 b).eventually (hf.eventually (by simp))] with
      t ht
    have hF : HasFDerivAt f (fderiv ℝ f (t • b)) (t • b) :=
      (ht.differentiableAt (by norm_num)).hasFDerivAt
    have hline : HasDerivAt (fun s : ℝ => t • b + s • a) a 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add (t • b)
    exact (hF.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hline (by simp)).deriv
  rw [hev.deriv_eq]
  exact (hasDerivAt_fderiv_line_FIN06820 f hf b a).deriv

lemma deriv_deriv_diag_FIN06820 (f : ℝ × ℝ → ℝ) (hf : ContDiffAt ℝ 2 f 0) (a : ℝ × ℝ) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => f (s • a)) t) 0 =
      fderiv ℝ (fderiv ℝ f) 0 a a := by
  have hev : (fun t : ℝ => deriv (fun s : ℝ => f (s • a)) t) =ᶠ[𝓝 0]
      fun t : ℝ => fderiv ℝ f (t • a) a := by
    filter_upwards [(tendsto_smul_zero_FIN06820 a).eventually (hf.eventually (by simp))] with
      t ht
    have hF : HasFDerivAt f (fderiv ℝ f (t • a)) ((fun s : ℝ => s • a) t) :=
      (ht.differentiableAt (by norm_num)).hasFDerivAt
    have hline : HasDerivAt (fun s : ℝ => s • a) a t := by
      simpa using (hasDerivAt_id t).smul_const a
    exact (hF.comp_hasDerivAt (x := t) hline).deriv
  rw [hev.deriv_eq]
  exact (hasDerivAt_fderiv_line_FIN06820 f hf a a).deriv

lemma inv_quarticKappa_FIN06820 : 1 / quarticKappa = quarticB / 5 := by
  unfold quarticKappa
  exact one_div_div 5 quarticB

/-- The second derivative of `J` at zero, entrywise from FIN068.18 and the relation `1/κ = b/5`. -/
lemma hessian_J_zero_FIN06820 (v w : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2) 0 ![v, w] =
      (constA_FIN06820 * v.1 - constD_FIN06820 / 32 * v.2) * w.1 +
        (-(constD_FIN06820 / 32) * v.1 + constD_FIN06820 / 256 * v.2) * w.2 := by
  set Jf : ℝ × ℝ → ℝ := fun q => liftPotential_FIN06804 q.1 q.2 with hJf
  have hJ : ContDiffAt ℝ 2 Jf 0 := by
    have h := (fin068_04_lift_two_ordinary_variables).1
    have hmem : ((0 : ℝ × ℝ)) ∈ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1 := by
      simp
    exact ((h.contDiffAt ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hmem)).of_le (by simp))
  obtain ⟨-, -, h3, h4, h5, h6, -⟩ := fin068_18_assemble_jet_j
  have hi := inv_quarticKappa_FIN06820
  have e11 : fderiv ℝ (fderiv ℝ Jf) 0 (1, 0) (1, 0) = constA_FIN06820 := by
    have h := deriv_deriv_diag_FIN06820 Jf hJ (1, 0)
    have hl : ∀ s : ℝ, Jf (s • ((1 : ℝ), (0 : ℝ))) = liftPotential_FIN06804 s 0 := by
      intro s
      simp [hJf]
    simp only [hl] at h
    rw [← h, h3, hi]
    unfold constA_FIN06820
    ring
  have e22 : fderiv ℝ (fderiv ℝ Jf) 0 (0, 1) (0, 1) = constD_FIN06820 / 256 := by
    have h := deriv_deriv_diag_FIN06820 Jf hJ (0, 1)
    have hl : ∀ s : ℝ, Jf (s • ((0 : ℝ), (1 : ℝ))) = liftPotential_FIN06804 0 s := by
      intro s
      simp [hJf]
    simp only [hl] at h
    rw [← h, h6]
    unfold constD_FIN06820
    ring
  have e12 : fderiv ℝ (fderiv ℝ Jf) 0 (1, 0) (0, 1) = -(constD_FIN06820 / 32) := by
    have h := deriv_deriv_slice_FIN06820 Jf hJ (0, 1) (1, 0)
    have hl : ∀ s t : ℝ, Jf (t • ((1 : ℝ), (0 : ℝ)) + s • ((0 : ℝ), (1 : ℝ))) =
        liftPotential_FIN06804 t s := by
      intro s t
      simp [hJf]
    simp only [hl] at h
    rw [← h, h5]
    unfold constD_FIN06820
    ring
  have e21 : fderiv ℝ (fderiv ℝ Jf) 0 (0, 1) (1, 0) = -(constD_FIN06820 / 32) := by
    have h := deriv_deriv_slice_FIN06820 Jf hJ (1, 0) (0, 1)
    have hl : ∀ s t : ℝ, Jf (t • ((0 : ℝ), (1 : ℝ)) + s • ((1 : ℝ), (0 : ℝ))) =
        liftPotential_FIN06804 s t := by
      intro s t
      simp [hJf]
    simp only [hl] at h
    rw [← h, h4]
    unfold constD_FIN06820
    ring
  rw [iteratedFDeriv_two_apply]
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have hw : w = w.1 • ((1 : ℝ), (0 : ℝ)) + w.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have hexp : fderiv ℝ (fderiv ℝ Jf) 0 v w =
      fderiv ℝ (fderiv ℝ Jf) 0 (v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)))
        (w.1 • ((1 : ℝ), (0 : ℝ)) + w.2 • ((0 : ℝ), (1 : ℝ))) := by
    rw [← hv, ← hw]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hexp]
  simp only [map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul, e11, e22, e12, e21]
  ring

lemma fin068_20_hessian_remainder_hessian_P_eq_hessian_J_zero (x v w : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 quadP_FIN06820 x ![v, w] =
      iteratedFDeriv ℝ 2 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2) 0 ![v, w] := by
  rw [hessian_quadP_FIN06820, hessian_J_zero_FIN06820, hessCLM_apply_FIN06820]

/-- Derivative of `t ↦ D²J(t h)[v,w]` on the smooth patch. -/
lemma hasDerivAt_hessian_line_FIN06820 (h v w : ℝ × ℝ) (t : ℝ)
    (ht : t • h ∈ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt
      (fun s : ℝ => iteratedFDeriv ℝ 2 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2)
        (s • h) ![v, w])
      (iteratedFDeriv ℝ 3 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2) (t • h) ![h, v, w])
      t := by
  set Jf : ℝ × ℝ → ℝ := fun q => liftPotential_FIN06804 q.1 q.2 with hJf
  have hcd : ContDiffAt ℝ ∞ Jf (t • h) :=
    (fin068_04_lift_two_ordinary_variables).1.contDiffAt
      ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds ht)
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 Jf) (t • h) := by
    have h1 : ContDiffAt ℝ 1 (iteratedFDeriv ℝ 2 Jf) (t • h) :=
      hcd.iteratedFDeriv_right (m := 1) (i := 2) (by simp)
    exact h1.differentiableAt (by norm_num)
  have hline : HasDerivAt (fun s : ℝ => s • h) h t := by
    simpa using (hasDerivAt_id t).smul_const h
  have hF := hdiff.hasFDerivAt
  have hc : HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ 2 Jf (s • h))
      (fderiv ℝ (iteratedFDeriv ℝ 2 Jf) (t • h) h) t :=
    hF.comp_hasDerivAt t hline
  have hL := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ × ℝ) ℝ
    (![v, w] : Fin 2 → ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt t hc
  exact hL

/-- Points `t • h` with `t ∈ [0,1]` and `h ∈ B` lie in `B`. -/
lemma smul_mem_fixedRect_FIN06820 {δ : ℝ} {h : ℝ × ℝ} (hh : h ∈ fixedRect_FIN06819 δ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : t • h ∈ fixedRect_FIN06819 δ := by
  apply segment_fixedRect_FIN06819 δ h hh
  exact ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, by simp⟩

/-- Main declaration. See the module docstring. -/
theorem fin068_20_hessian_remainder (δ M₃ : ℝ) (hδ1 : δ < 1)
    (hM : ∀ x ∈ fixedRect_FIN06819 δ, ∀ h v w : ℝ × ℝ,
      |iteratedFDeriv ℝ 3 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2) x ![h, v, w]| ≤
        M₃ * (|h.1| + |h.2|) * (|v.1| + |v.2|) * (|w.1| + |w.2|)) :
    ∀ h ∈ fixedRect_FIN06819 δ, ∀ v w : ℝ × ℝ,
      |iteratedFDeriv ℝ 2 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2) h ![v, w] -
          iteratedFDeriv ℝ 2 quadP_FIN06820 h ![v, w]| ≤
        M₃ * (|h.1| + |h.2|) * (|v.1| + |v.2|) * (|w.1| + |w.2|) := by
  intro h hh v w
  set Jf : ℝ × ℝ → ℝ := fun q => liftPotential_FIN06804 q.1 q.2 with hJf
  have hsub : fixedRect_FIN06819 δ ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1 := by
    rintro p ⟨hp1, hp2⟩
    exact ⟨abs_lt.mp (lt_of_le_of_lt hp1 hδ1), abs_lt.mp (lt_of_le_of_lt hp2 hδ1)⟩
  set C : ℝ := M₃ * (|h.1| + |h.2|) * (|v.1| + |v.2|) * (|w.1| + |w.2|) with hC
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s : ℝ => iteratedFDeriv ℝ 2 Jf (s • h) ![v, w])
        (iteratedFDeriv ℝ 3 Jf (t • h) ![h, v, w]) (Set.Icc (0 : ℝ) 1) t := fun t ht =>
    (hasDerivAt_hessian_line_FIN06820 h v w t
      (hsub (smul_mem_fixedRect_FIN06820 hh ht))).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ 3 Jf (t • h) ![h, v, w]‖ ≤ C := fun t ht => by
    rw [Real.norm_eq_abs]
    exact hM _ (smul_mem_fixedRect_FIN06820 hh ⟨ht.1, ht.2.le⟩) h v w
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1
    (Set.right_mem_Icc.2 zero_le_one)
  simp only [one_smul, zero_smul, sub_zero, mul_one, Real.norm_eq_abs] at key
  rw [fin068_20_hessian_remainder_hessian_P_eq_hessian_J_zero h v w]
  exact key

/-- Combination with FIN068.19: there are `δ ∈ (0,1)` and `M₃ ≥ 0` such that the closed rectangle
lies in the smooth patch, segments from zero stay in it, the third derivative is bounded there, and
the Hessian remainder bound holds at every point of the rectangle. -/
theorem fin068_20_hessian_remainder_exists :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      fixedRect_FIN06819 δ ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1 ∧
      (∀ p ∈ fixedRect_FIN06819 δ, segment ℝ (0 : ℝ × ℝ) p ⊆ fixedRect_FIN06819 δ) ∧
      ∃ M₃ : ℝ, 0 ≤ M₃ ∧
        (∀ x ∈ fixedRect_FIN06819 δ, ∀ h v w : ℝ × ℝ,
          |iteratedFDeriv ℝ 3 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2) x ![h, v, w]| ≤
            M₃ * (|h.1| + |h.2|) * (|v.1| + |v.2|) * (|w.1| + |w.2|)) ∧
        ∀ h ∈ fixedRect_FIN06819 δ, ∀ v w : ℝ × ℝ,
          |iteratedFDeriv ℝ 2 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2) h ![v, w] -
              iteratedFDeriv ℝ 2 quadP_FIN06820 h ![v, w]| ≤
            M₃ * (|h.1| + |h.2|) * (|v.1| + |v.2|) * (|w.1| + |w.2|) := by
  obtain ⟨hsub, hseg, M₃, hM₃, hM⟩ :=
    fin068_19_fixed_compact_convex_domain_derivative_bound_each_delta (1 / 2) (by norm_num)
      (by norm_num)
  exact ⟨1 / 2, by norm_num, by norm_num, hsub, hseg, M₃, hM₃, hM,
    fin068_20_hessian_remainder (1 / 2) M₃ (by norm_num) hM⟩

end DGPS.Frontier.FIN068
