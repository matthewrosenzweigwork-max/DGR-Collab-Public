import DGPS.Frontier.EX012.T28

/-!
# EX012.26: Projections at both regularities

Task id: EX012.26 (node EX012, one-site complementary range equation).
Title: Projections at both regularities.

Provides:
* `DGPS.Frontier.EX012.ex012_26_projections_both_regularities`: the main statement. For
  `k = 0, 2` (i) `Q_k` kills `1`, `c₁ = cos (2π x)` and `s₁ = sin (2π x)`; (ii) `Q_k` fixes every
  member of `PH.orthSub α k`; (iii) `Q_k f` has the pointwise formula
  `f - ∫ f - 2 (∫ f c₁) c₁ - 2 (∫ f s₁) s₁`; (iv) for `f : PH α 2` the two projections agree after
  the inclusion `PH α 2 → PH α 0` of EX012.25, `Q₀ (ι f) = ι' (Q₂ f)` pointwise (and as elements
  of `PH α 0`, since `Q₂ f` is a member of `PH.orthSub α 2`).
* `DGPS.Frontier.EX012.proj_EX01226`: the projection `Q_k : PH α k →L[ℝ] PH.orthSub α k`
  (defined for every `k`), `f ↦ f - modeProj k {0,1} f` with its codomain restricted.
* `DGPS.Frontier.EX012.ex012_26_projections_both_regularities_val`: the pointwise formula for
  every `k`.
* `DGPS.Frontier.EX012.ex012_26_projections_both_regularities_fixes`: `Q_k w = w` for `w` in
  `PH.orthSub α k`, every `k`.
* `DGPS.Frontier.EX012.ex012_26_projections_both_regularities_kills`: `Q_k` kills `1`, `c₁`,
  `s₁`, every `k`.
* `DGPS.Frontier.EX012.ex012_26_projections_both_regularities_incl`: compatibility with the
  inclusion of EX012.25 at the level of functions and of elements of `PH α 0`.
* Helper lemmas (all suffixed `_EX01226`): `mem_projFun_EX01226` (membership of
  `f - modeProj k {0,1} f` in `PH.orthSub α k`, proved before bundling), `proj_coe_EX01226`
  (the underlying element of `Q_k f`), `coeffs_one_EX01226`, `coeffs_cosMode_EX01226`,
  `coeffs_sinMode_EX01226` (the three integral coefficients of `1`, `c₁`, `s₁`).

R5 notes:
* The only hypothesis is `[HolderExponent α]` (the campaign form of `0 < α < 1`). The main
  statement carries `k = 0 ∨ k = 2` as listed in the specification; the helper declarations and
  the construction hold for every `k : ℕ`.
* "The finite-mode projection in FOU017 with modes `{0,1}`" is `PH.modeProj k {0, 1}`; `Q_k` is
  `id - modeProj k {0,1}`, so that `Q_k f = f - ∫ f - 2 (∫ f c₁) c₁ - 2 (∫ f s₁) s₁` (via
  `PH.modeProj01_val`). "Subtracting the mean and first cosine/sine modes" is read this way.
* The map `Q_k` is built by `ContinuousLinearMap.codRestrict` after proving the three integral
  constraints (`mem_projFun_EX01226`); `Subtype.ext` is used only at the final equalities.
  The proof of membership is the same argument as in FOU017's `PH.orthSub_closedComplemented`,
  which does not export its projection, so it is re-proved here (no existing file is edited).
* "Fixes every member of the orthogonal subspace" is read as `Q_k ⟨w, hw⟩ = ⟨w, hw⟩` for
  `w : PH.orthSub α k` (i.e. `Q_k (w : PH α k) = w` as elements of the subtype).
* "Kills `1, c₁, s₁`" is read as `Q_k 1 = 0`, `Q_k c₁ = 0`, `Q_k s₁ = 0` in `PH.orthSub α k`,
  with `1 : PH α k` the ring identity (the constant function `1`) and
  `c₁ = cosMode_EX01228 α k 1`, `s₁ = sinMode_EX01228 α k 1` of EX012.28.
* "Agrees with the same pointwise formula after inclusion `PH α 2 → PH α 0`" is read as:
  for `f : PH α 2`, `(Q₀ (ι f)).val = (Q₂ f).val` as functions on `ℝ`, where `ι` is
  `ex012_25_inclusion_second_derivative_elliptic_compatibility_incl`; equivalently both equal the
  same closed-form pointwise expression of `f`. The element-level form is
  `Q₀ (ι f) = ⟨ι (Q₂ f), _⟩` in `PH.orthSub α 0`, where `ι` maps `PH.orthSub α 2` into
  `PH.orthSub α 0`: we state it as an equality of the underlying elements
  `((Q₀ (ι f) : PH.orthSub α 0) : PH α 0) = ι ((Q₂ f : PH.orthSub α 2) : PH α 2)`.
-/

open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.EX012

section Construction

variable {α : ℝ} [HolderExponent α]

theorem mem_projFun_EX01226 (k : ℕ) (f : PH α k) :
    f - PH.modeProj k {0, 1} f ∈ PH.orthSub α k := by
  obtain ⟨a, b, c⟩ := PH.modeProj01_orth f
  refine ⟨?_, ?_, ?_⟩
  · rw [map_sub, a, sub_self]
  · rw [map_sub, b, sub_self]
  · rw [map_sub, c, sub_self]

variable (α)

/-- The projection `Q_k : PH α k →L[ℝ] PH.orthSub α k` subtracting the mean and the first
cosine/sine modes. -/
noncomputable def proj_EX01226 (k : ℕ) : PH α k →L[ℝ] PH.orthSub α k :=
  (ContinuousLinearMap.id ℝ (PH α k) - PH.modeProj k {0, 1}).codRestrict (PH.orthSub α k)
    (mem_projFun_EX01226 k)

variable {α}

theorem proj_coe_EX01226 (k : ℕ) (f : PH α k) :
    ((proj_EX01226 α k f : PH.orthSub α k) : PH α k) = f - PH.modeProj k {0, 1} f := rfl

/-- Pointwise formula for `Q_k`. -/
theorem ex012_26_projections_both_regularities_val (k : ℕ) (f : PH α k) (x : ℝ) :
    ((proj_EX01226 α k f : PH.orthSub α k) : PH α k).val x =
      f.val x - PH.integral k f - 2 * PH.cosCoeff k 1 f * Real.cos (2 * Real.pi * x) -
        2 * PH.sinCoeff k 1 f * Real.sin (2 * Real.pi * x) := by
  rw [proj_coe_EX01226, PH.val_sub, Pi.sub_apply, PH.modeProj01_val]
  ring

/-- `Q_k` fixes every member of the orthogonal subspace. -/
theorem ex012_26_projections_both_regularities_fixes (k : ℕ) (w : PH.orthSub α k) :
    proj_EX01226 α k (w : PH α k) = w := by
  apply Subtype.ext
  rw [proj_coe_EX01226, PH.modeProj01_eq_zero w.2, sub_zero]

end Construction

section Coefficients

variable {α : ℝ} [HolderExponent α]

theorem coeffs_one_EX01226 (k : ℕ) :
    PH.integral k (1 : PH α k) = 1 ∧ PH.cosCoeff k 1 (1 : PH α k) = 0 ∧
      PH.sinCoeff k 1 (1 : PH α k) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [PH.integral_apply]; simp
  · rw [PH.cosCoeff_apply]; simp
  · rw [PH.sinCoeff_apply]; simp

theorem coeffs_cosMode_EX01226 (k : ℕ) :
    PH.integral k (cosMode_EX01228 α k 1) = 0 ∧ PH.cosCoeff k 1 (cosMode_EX01228 α k 1) = 1 / 2 ∧
      PH.sinCoeff k 1 (cosMode_EX01228 α k 1) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [PH.integral_apply]; exact int_cosMode_EX01228 k one_ne_zero
  · rw [PH.cosCoeff_apply]
    have := int_cosMode_mul_cosMode_EX01228 (α := α) k 1 one_ne_zero
    simp only [cosMode_val_EX01228] at this ⊢
    simpa using this
  · rw [PH.sinCoeff_apply]
    have := int_sinMode_mul_cosMode_EX01228 (α := α) k 1 one_ne_zero
    simp only [cosMode_val_EX01228, sinMode_val_EX01228] at this ⊢
    rw [show (fun x : ℝ => Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) * x) *
        Real.sin (2 * Real.pi * ((1 : ℕ) : ℝ) * x)) =
        fun x => Real.sin (2 * Real.pi * ((1 : ℕ) : ℝ) * x) *
          Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) * x) from funext fun x => mul_comm _ _]
    exact this

theorem coeffs_sinMode_EX01226 (k : ℕ) :
    PH.integral k (sinMode_EX01228 α k 1) = 0 ∧ PH.cosCoeff k 1 (sinMode_EX01228 α k 1) = 0 ∧
      PH.sinCoeff k 1 (sinMode_EX01228 α k 1) = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [PH.integral_apply]; exact int_sinMode_EX01228 k one_ne_zero
  · rw [PH.cosCoeff_apply]
    have := int_sinMode_mul_cosMode_EX01228 (α := α) k 1 one_ne_zero
    simp only [cosMode_val_EX01228, sinMode_val_EX01228] at this ⊢
    exact this
  · rw [PH.sinCoeff_apply]
    have := int_sinMode_mul_sinMode_EX01228 (α := α) k 1 one_ne_zero
    simp only [sinMode_val_EX01228] at this ⊢
    simpa using this

end Coefficients

section Kills

variable {α : ℝ} [HolderExponent α]

/-- `Q_k` kills `1`, `c₁` and `s₁`. -/
theorem ex012_26_projections_both_regularities_kills (k : ℕ) :
    proj_EX01226 α k (1 : PH α k) = 0 ∧ proj_EX01226 α k (cosMode_EX01228 α k 1) = 0 ∧
      proj_EX01226 α k (sinMode_EX01228 α k 1) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · apply Subtype.ext
    refine PH.ext (funext fun x => ?_)
    obtain ⟨h1, h2, h3⟩ := coeffs_one_EX01226 (α := α) k
    rw [ex012_26_projections_both_regularities_val, h1, h2, h3]
    simp
  · apply Subtype.ext
    refine PH.ext (funext fun x => ?_)
    obtain ⟨h1, h2, h3⟩ := coeffs_cosMode_EX01226 (α := α) k
    rw [ex012_26_projections_both_regularities_val, h1, h2, h3, cosMode_val_EX01228]
    simp
  · apply Subtype.ext
    refine PH.ext (funext fun x => ?_)
    obtain ⟨h1, h2, h3⟩ := coeffs_sinMode_EX01226 (α := α) k
    rw [ex012_26_projections_both_regularities_val, h1, h2, h3, sinMode_val_EX01228]
    simp

/-- Compatibility with the inclusion `ι : PH α 2 → PH α 0` of EX012.25. -/
theorem ex012_26_projections_both_regularities_incl (f : PH α 2) :
    (∀ x : ℝ, ((proj_EX01226 α 0
        (ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f) :
          PH.orthSub α 0) : PH α 0).val x =
      ((proj_EX01226 α 2 f : PH.orthSub α 2) : PH α 2).val x) ∧
    ((proj_EX01226 α 0
        (ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f) :
          PH.orthSub α 0) : PH α 0) =
      ex012_25_inclusion_second_derivative_elliptic_compatibility_incl
        ((proj_EX01226 α 2 f : PH.orthSub α 2) : PH α 2) := by
  have hval : ∀ x : ℝ, ((proj_EX01226 α 0
        (ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f) :
          PH.orthSub α 0) : PH α 0).val x =
      ((proj_EX01226 α 2 f : PH.orthSub α 2) : PH α 2).val x := by
    intro x
    rw [ex012_26_projections_both_regularities_val, ex012_26_projections_both_regularities_val]
    have e1 : PH.integral 0
        (ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f) =
        PH.integral 2 f := by
      rw [PH.integral_apply, PH.integral_apply]; rfl
    have e2 : PH.cosCoeff 0 1
        (ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f) =
        PH.cosCoeff 2 1 f := by
      rw [PH.cosCoeff_apply, PH.cosCoeff_apply]; rfl
    have e3 : PH.sinCoeff 0 1
        (ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f) =
        PH.sinCoeff 2 1 f := by
      rw [PH.sinCoeff_apply, PH.sinCoeff_apply]; rfl
    rw [e1, e2, e3,
      ex012_25_inclusion_second_derivative_elliptic_compatibility_incl_val]
  exact ⟨hval, PH.ext (funext fun x => hval x)⟩

end Kills

section Main

variable {α : ℝ} [HolderExponent α]

/-- **EX012.26.**  For `k = 0, 2` the map `Q_k : PH α k →L[ℝ] PH.orthSub α k` (`id` minus the
finite-mode projection `modeProj k {0,1}`, codomain restricted) kills `1`, `c₁`, `s₁`, fixes every
member of `PH.orthSub α k`, has the pointwise formula `f - ∫ f - 2 (∫ f c₁) c₁ - 2 (∫ f s₁) s₁`,
and the two projections agree after the inclusion `PH α 2 → PH α 0`. -/
theorem ex012_26_projections_both_regularities :
    ∀ k : ℕ, (k = 0 ∨ k = 2) →
      (proj_EX01226 α k (1 : PH α k) = 0 ∧
        proj_EX01226 α k (cosMode_EX01228 α k 1) = 0 ∧
        proj_EX01226 α k (sinMode_EX01228 α k 1) = 0) ∧
      (∀ w : PH.orthSub α k, proj_EX01226 α k (w : PH α k) = w) ∧
      (∀ (f : PH α k) (x : ℝ),
        ((proj_EX01226 α k f : PH.orthSub α k) : PH α k).val x =
          f.val x - PH.integral k f - 2 * PH.cosCoeff k 1 f * Real.cos (2 * Real.pi * x) -
            2 * PH.sinCoeff k 1 f * Real.sin (2 * Real.pi * x)) ∧
      (k = 2 → ∀ f : PH α 2,
        (∀ x : ℝ, ((proj_EX01226 α 0
            (ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f) :
              PH.orthSub α 0) : PH α 0).val x =
          ((proj_EX01226 α 2 f : PH.orthSub α 2) : PH α 2).val x)) := by
  intro k _
  exact ⟨ex012_26_projections_both_regularities_kills k,
    ex012_26_projections_both_regularities_fixes k, ex012_26_projections_both_regularities_val k,
    fun hk f => by
      subst hk
      exact (ex012_26_projections_both_regularities_incl f).1⟩

end Main

end DGPS.Frontier.EX012
