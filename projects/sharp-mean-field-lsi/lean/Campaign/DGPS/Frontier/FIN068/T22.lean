import DGPS.Frontier.FIN068.T21

/-!
Task id and title: FIN068.22, Value remainder (module `DGPS.Frontier.FIN068.T22`).

Provides:
* `DGPS.Frontier.FIN068.fin068_22_value_remainder`: let `δ < 1`, `B = {|u| ≤ δ, |z| ≤ δ}`
  (`fixedRect_FIN06819 δ`), `J = liftPotential_FIN06804` on `ℝ × ℝ` (read as `J h = liftPotential_FIN06804 h.1 h.2`)
  and `P = quadP_FIN06820`. If `M₃` bounds the third derivative of `J` on `B` in the `ℓ¹` form of
  FIN068.19 (hypothesis `hM`, the same as in FIN068.20 and FIN068.21), then for every `h ∈ B`,
  `|J(h) - P(h)| ≤ (M₃ / 6) ‖h‖₁³`, with `‖(a,b)‖₁ = |a| + |b|`.
* `DGPS.Frontier.FIN068.fin068_22_value_remainder_exists`: there are `δ ∈ (0,1)` and `M₃ ≥ 0`
  for which the value remainder bound holds at every point of `B` (combination with FIN068.20 and
  FIN068.21, which supply `δ` and `M₃`).
* Helper declarations, all with suffix `_FIN06822` and not part of the interface:
  `hasDerivAt_remF_seg_FIN06822` (the derivative of `s ↦ F(s h)` for a function `F` that is `C²` at
  `t h`), and `remF_zero_FIN06822` (`J(0) - P(0) = 0`).

Proof: `J(0) = P(0)`, since `quadP_FIN06820 0` equals `liftPotential_FIN06804 0 0`. Put
`g(s) = (J - P)(s h)` for `h ∈ B` and `s ∈ [0,1]`. Then `g(0) = 0` and `g'(s) = D(J - P)(s h)[h]`.
FIN068.21 at the point `s h ∈ B` (with `‖s h‖₁ = s ‖h‖₁`) gives `|g'(s)| ≤ (M₃/2) ‖h‖₁³ s²`.
Integrating over `[0,1]` gives `|g(1)| ≤ (M₃/2) ‖h‖₁³ / 3 = (M₃/6) ‖h‖₁³`. The integral is realized
through Mathlib's boundary inequality `image_norm_le_of_norm_deriv_right_le_deriv_boundary` with the
comparison function `s ↦ K s³/3`, `K = (M₃/2) ‖h‖₁³`, whose derivative `K s²` dominates `|g'(s)|`.

R5 notes:
* Hypotheses: `δ < 1` (the patch condition of FIN068.19 and FIN068.20) and `hM`, which says that
  `M₃` bounds the third derivative of `J` on `B`. These are the hypotheses of FIN068.21 and are not
  new. The lower bound `0 < δ` and the sign `0 ≤ M₃` are not used in the main declaration. The
  existence declaration removes `hM` and `δ < 1` by FIN068.20.
* The specification's `M₃` is the constant of the third-derivative bound; it is therefore carried as
  the explicit parameter `M₃` together with `hM`, the same way FIN068.21 carries it. It is not
  computed.
* Norm: `‖(a,b)‖₁ = |a| + |b|` is written explicitly, not as a Mathlib norm, as in FIN068.19 to
  FIN068.21. The bound is stated in the form `|J(h) - P(h)| ≤ (M₃/6)(|h.1| + |h.2|)³`.
* The integral over `[0,1]` is replaced by the boundary inequality with `B(s) = K s³/3`. It gives
  the same constant without integrability side conditions. The FTC identifier named in the
  specification (`integral_id` style) is not used.
* The value `J(h)` is `liftPotential_FIN06804 h.1 h.2` (FIN068.04) and `P(h)` is `quadP_FIN06820 h`
  (FIN068.20), with `P(u,z) = J(0,0) + A u²/2 - d u z/32 + d z²/512`. The identity `J(0) = P(0)`
  is proved from the definition of `quadP_FIN06820` and is not assumed.
* The derivative of `s ↦ (J - P)(s h)` is Mathlib's Fréchet `fderiv` on `ℝ × ℝ` (as in FIN068.21).
  The Euclidean reading of FIN068.18 is not used.
-/

namespace DGPS.Frontier.FIN068

/-- The derivative of `s ↦ F (s • h)` at `t`, for `F` of class `C²` at `t • h`. -/
lemma hasDerivAt_remF_seg_FIN06822 (h : ℝ × ℝ) (t : ℝ)
    (hF : ContDiffAt ℝ 2 remF_FIN06821 (t • h)) :
    HasDerivAt (fun s : ℝ => remF_FIN06821 (s • h)) (fderiv ℝ remF_FIN06821 (t • h) h) t := by
  have hline : HasDerivAt (fun s : ℝ => s • h) h t := by
    simpa using (hasDerivAt_id t).smul_const h
  exact (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hline

/-- `J(0) - P(0) = 0`, since `P(0) = J(0,0)` by the definition of `quadP_FIN06820`. -/
lemma remF_zero_FIN06822 : remF_FIN06821 0 = 0 := by
  simp [remF_FIN06821, quadP_FIN06820]

/-- Main declaration. See the module docstring. -/
theorem fin068_22_value_remainder (δ M₃ : ℝ) (hδ1 : δ < 1)
    (hM : ∀ x ∈ fixedRect_FIN06819 δ, ∀ h v w : ℝ × ℝ,
      |iteratedFDeriv ℝ 3 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2) x ![h, v, w]| ≤
        M₃ * (|h.1| + |h.2|) * (|v.1| + |v.2|) * (|w.1| + |w.2|)) :
    ∀ h ∈ fixedRect_FIN06819 δ,
      |liftPotential_FIN06804 h.1 h.2 - quadP_FIN06820 h| ≤ M₃ / 6 * (|h.1| + |h.2|) ^ 3 := by
  intro h hh
  show |remF_FIN06821 h| ≤ M₃ / 6 * (|h.1| + |h.2|) ^ 3
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • h ∈ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1 :=
    fun t ht => mem_patch_FIN06821 hδ1 (smul_mem_fixedRect_FIN06820 hh ht)
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => remF_FIN06821 (s • h))
      (fderiv ℝ remF_FIN06821 (t • h) h) t := fun t ht =>
    hasDerivAt_remF_seg_FIN06822 h t (contDiffAt_remF_FIN06821 _ (hmem t ht))
  have hcont : ContinuousOn (fun s : ℝ => remF_FIN06821 (s • h)) (Set.Icc 0 1) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hf' : ∀ x ∈ Set.Ico (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => remF_FIN06821 (s • h))
      (fderiv ℝ remF_FIN06821 (x • h) h) (Set.Ici x) x := fun x hx =>
    (hderiv x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt
  have hB : ∀ x : ℝ, HasDerivAt (fun x : ℝ => M₃ / 2 * (|h.1| + |h.2|) ^ 3 * x ^ 3 / 3)
      (M₃ / 2 * (|h.1| + |h.2|) ^ 3 * x ^ 2) x := by
    intro x
    have := ((hasDerivAt_pow 3 x).const_mul (M₃ / 2 * (|h.1| + |h.2|) ^ 3)).div_const 3
    convert this using 1
    norm_num
    ring
  have hbnd : ∀ x ∈ Set.Ico (0 : ℝ) 1, ‖fderiv ℝ remF_FIN06821 (x • h) h‖ ≤
      M₃ / 2 * (|h.1| + |h.2|) ^ 3 * x ^ 2 := by
    intro x hx
    rw [Real.norm_eq_abs]
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
    have hT := fin068_21_gradient_remainder δ M₃ hδ1 hM (x • h) (smul_mem_fixedRect_FIN06820 hh hx') h
    have hnorm : |(x • h).1| + |(x • h).2| = x * (|h.1| + |h.2|) := by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul, abs_of_nonneg hx.1]
      ring
    rw [hnorm] at hT
    have hT' : |fderiv ℝ remF_FIN06821 (x • h) h| ≤
        M₃ / 2 * (x * (|h.1| + |h.2|)) ^ 2 * (|h.1| + |h.2|) := hT
    calc |fderiv ℝ remF_FIN06821 (x • h) h|
        ≤ M₃ / 2 * (x * (|h.1| + |h.2|)) ^ 2 * (|h.1| + |h.2|) := hT'
      _ = M₃ / 2 * (|h.1| + |h.2|) ^ 3 * x ^ 2 := by ring
  have ha : ‖(fun s : ℝ => remF_FIN06821 (s • h)) 0‖ ≤
      (fun x : ℝ => M₃ / 2 * (|h.1| + |h.2|) ^ 3 * x ^ 3 / 3) 0 := by
    simp [remF_zero_FIN06822]
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont hf' ha hB hbnd
    (Set.right_mem_Icc.2 zero_le_one)
  simp only [one_smul, Real.norm_eq_abs] at key
  linarith

/-- Combination with FIN068.20 and FIN068.21: there are `δ ∈ (0,1)` and `M₃ ≥ 0` such that the
value remainder bound holds at every point of the closed rectangle. -/
theorem fin068_22_value_remainder_exists :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ M₃ : ℝ, 0 ≤ M₃ ∧
      ∀ h ∈ fixedRect_FIN06819 δ,
        |liftPotential_FIN06804 h.1 h.2 - quadP_FIN06820 h| ≤ M₃ / 6 * (|h.1| + |h.2|) ^ 3 := by
  obtain ⟨δ, hδ0, hδ1, -, -, M₃, hM₃, hM, -⟩ := fin068_20_hessian_remainder_exists
  exact ⟨δ, hδ0, hδ1, M₃, hM₃, fin068_22_value_remainder δ M₃ hδ1 hM⟩

end DGPS.Frontier.FIN068
