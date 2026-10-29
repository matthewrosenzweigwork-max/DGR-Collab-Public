import DGPS.Frontier.EX012.T26
import DGPS.Frontier.EX012.T27

/-!
# EX012.04: Bounded derivative and Fourier projections

Task id: EX012.04 (node EX012, one-site complementary range equation).
Title: Bounded derivative and Fourier projections.

Provides:
* `DGPS.Frontier.EX012.ex012_04_bounded_derivative_fourier_projections`: the main statement, a
  conjunction of (i) `‖D f‖ ≤ 3/(2π) ‖f‖` for the angular derivative `D : PH α 2 →L[ℝ] PH α 0`
  of EX012.24; (ii) `‖ι‖ ≤ 3` and `‖D²‖ ≤ ((2π)^2)⁻¹` for the inclusion and the second derivative
  of EX012.25; (iii) for `k = 0, 2` the constant and first-harmonic projections
  `modeCLM k 0`, `modeCLM k 1` and the projection `Q_k = proj_EX01226 α k` onto the complement
  are continuous linear maps, with `‖Q_k‖ ≤ 1 + ‖modeCLM k 0‖ + ‖modeCLM k 1‖`; (iv) the
  projections commute with the inclusion `ι : PH α 2 → PH α 0`; (v) the multiplication of
  `PH α 0` is a continuous bilinear map with the FOU017 bound; (vi) the first-harmonic injection
  `(a, b) ↦ a c₁ + b s₁` is a bounded linear map `ℝ × ℝ →L[ℝ] PH α k`.
* `DGPS.Frontier.EX012.ex012_04_bounded_derivative_fourier_projections_deriv`: item (i) in its
  operator-norm form `‖D‖ ≤ 3/(2π)`, together with the pointwise bound.
* `DGPS.Frontier.EX012.ex012_04_bounded_derivative_fourier_projections_incl_secondDeriv`: item
  (ii) in pointwise and operator-norm form.
* `DGPS.Frontier.EX012.ex012_04_bounded_derivative_fourier_projections_modeProj`: for every
  `k`, `PH.modeProj k {0, 1} = modeCLM k 0 + modeCLM k 1`, the sum of the constant and the
  first-harmonic projection.
* `DGPS.Frontier.EX012.ex012_04_bounded_derivative_fourier_projections_proj_norm`: for every `k`,
  `‖Q_k f‖ ≤ (1 + ‖modeCLM k 0‖ + ‖modeCLM k 1‖) ‖f‖` and the operator-norm form.
* `DGPS.Frontier.EX012.ex012_04_bounded_derivative_fourier_projections_commute`: for
  `n ∈ {0, 1}` and `f : PH α 2`, `modeCLM 0 n (ι f) = ι (modeCLM 2 n f)`, the same for
  `PH.modeProj _ {0, 1}`, and `Q₀ (ι f) = ι (Q₂ f)` as elements of `PH α 0`.
* `DGPS.Frontier.EX012.ex012_04_bounded_derivative_fourier_projections_mul`: the product bound
  `‖f * g‖ ≤ C * (‖f‖ * ‖g‖)` with the FOU017 constant `C ≥ 0`, via the bilinear map of EX012.27.
* `DGPS.Frontier.EX012.ex012_04_bounded_derivative_fourier_projections_harmInj`: the
  first-harmonic injection is bounded, with operator-norm bound `‖c₁‖ + ‖s₁‖`.

R5 notes:
* The only hypothesis is `[HolderExponent α]`, the campaign form of `0 < α < 1`; `k = 0 ∨ k = 2`
  is the regularity restriction listed in the specification and nothing else is added.
* This is an assembly unit: every bound is the corresponding bound of EX012.24 to EX012.28, so
  the constants are exactly those of the specification (`3/(2π)`, `3`, `(2π)^(-2)`).
* "Bounded linear map" is read as a continuous linear map (`→L[ℝ]`); for the maps already
  bundled (`angDeriv_EX01224`, the T25 inclusion and second derivative, `modeCLM`,
  `proj_EX01226`, the T27 multiplication, `harmInj_EX01228`) boundedness is part of the type,
  and the stated numerical bounds are given in addition.
* "The constant and first-harmonic projections" is read as `PH.modeCLM k 0` and `PH.modeCLM k 1`
  of FOU017 (the single-mode projections onto frequencies `0` and `1`); their sum is
  `PH.modeProj k {0, 1}`, which is how `Q_k f = f - modeProj k {0,1} f` is formed in EX012.26.
* "The projections commute with the inclusion" is stated for `modeCLM _ 0`, `modeCLM _ 1`,
  `modeProj _ {0,1}` and for `Q` through the coerced elements, because the codomains of `Q₀` and
  `Q₂` are different subtypes; the `Q` form is `((Q₀ (ι f) : Y) : PH α 0) = ι ((Q₂ f : W) : PH α 2)`.
* The bound for `Q_k` is `1 + ‖P₀‖ + ‖P₁‖` with the operator norms of the FOU017 projections
  (the specification gives no numerical value for them), proved with the triangle inequality.
* The multiplication bound is stated with the chosen FOU017 constant `mulConst_EX01227 α` of
  EX012.27 and with the existential form `∃ C ≥ 0`.
* The first-harmonic injection is stated for every regularity `k`, which includes `k = 0`.
-/

open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.EX012

section Projections

variable {α : ℝ} [HolderExponent α]

theorem modeProj_eq_add_EX01204 (k : ℕ) :
    (PH.modeProj k {0, 1} : PH α k →L[ℝ] PH α k) = PH.modeCLM k 0 + PH.modeCLM k 1 := by
  unfold PH.modeProj
  rw [Finset.sum_pair (by norm_num)]

theorem modeCLM_incl_EX01204 (n : ℕ) (f : PH α 2) :
    PH.modeCLM 0 n (ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f) =
      ex012_25_inclusion_second_derivative_elliptic_compatibility_incl (PH.modeCLM 2 n f) := by
  refine PH.ext (funext fun x => ?_)
  have e1 : PH.cosCoeff 0 n
      (ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f) =
      PH.cosCoeff 2 n f := by
    rw [PH.cosCoeff_apply, PH.cosCoeff_apply]; rfl
  have e2 : PH.sinCoeff 0 n
      (ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f) =
      PH.sinCoeff 2 n f := by
    rw [PH.sinCoeff_apply, PH.sinCoeff_apply]; rfl
  rw [PH.modeCLM_val, e1, e2,
    ex012_25_inclusion_second_derivative_elliptic_compatibility_incl_val, PH.modeCLM_val]

theorem proj_norm_le_EX01204 (k : ℕ) (f : PH α k) :
    ‖proj_EX01226 α k f‖ ≤ (1 + ‖(PH.modeCLM k 0 : PH α k →L[ℝ] PH α k)‖ +
      ‖(PH.modeCLM k 1 : PH α k →L[ℝ] PH α k)‖) * ‖f‖ := by
  show ‖((proj_EX01226 α k f : PH.orthSub α k) : PH α k)‖ ≤ _
  rw [proj_coe_EX01226, modeProj_eq_add_EX01204, add_apply, sub_add_eq_sub_sub]
  have h0 := (PH.modeCLM k 0 : PH α k →L[ℝ] PH α k).le_opNorm f
  have h1 := (PH.modeCLM k 1 : PH α k →L[ℝ] PH α k).le_opNorm f
  have t1 := norm_sub_le (f - PH.modeCLM k 0 f) (PH.modeCLM k 1 f)
  have t2 := norm_sub_le f (PH.modeCLM k 0 f)
  nlinarith

/-- The sum of the constant and first-harmonic projections is `PH.modeProj k {0, 1}`. -/
theorem ex012_04_bounded_derivative_fourier_projections_modeProj (k : ℕ) :
    (PH.modeProj k {0, 1} : PH α k →L[ℝ] PH α k) = PH.modeCLM k 0 + PH.modeCLM k 1 :=
  modeProj_eq_add_EX01204 k

/-- `Q_k` is bounded with norm at most `1 + ‖P₀‖ + ‖P₁‖`. -/
theorem ex012_04_bounded_derivative_fourier_projections_proj_norm (k : ℕ) :
    (∀ f : PH α k, ‖proj_EX01226 α k f‖ ≤ (1 + ‖(PH.modeCLM k 0 : PH α k →L[ℝ] PH α k)‖ +
      ‖(PH.modeCLM k 1 : PH α k →L[ℝ] PH α k)‖) * ‖f‖) ∧
    ‖(proj_EX01226 α k : PH α k →L[ℝ] PH.orthSub α k)‖ ≤
      1 + ‖(PH.modeCLM k 0 : PH α k →L[ℝ] PH α k)‖ +
        ‖(PH.modeCLM k 1 : PH α k →L[ℝ] PH α k)‖ :=
  ⟨proj_norm_le_EX01204 k, ContinuousLinearMap.opNorm_le_bound _
    (by positivity) (proj_norm_le_EX01204 k)⟩

/-- The projections commute with the inclusion `PH α 2 → PH α 0`. -/
theorem ex012_04_bounded_derivative_fourier_projections_commute (f : PH α 2) :
    (∀ n : ℕ, PH.modeCLM 0 n
        (ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f) =
      ex012_25_inclusion_second_derivative_elliptic_compatibility_incl (PH.modeCLM 2 n f)) ∧
    PH.modeProj 0 {0, 1}
        (ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f) =
      ex012_25_inclusion_second_derivative_elliptic_compatibility_incl
        (PH.modeProj 2 {0, 1} f) ∧
    ((proj_EX01226 α 0
        (ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f) :
          PH.orthSub α 0) : PH α 0) =
      ex012_25_inclusion_second_derivative_elliptic_compatibility_incl
        ((proj_EX01226 α 2 f : PH.orthSub α 2) : PH α 2) := by
  refine ⟨fun n => modeCLM_incl_EX01204 n f, ?_,
    (ex012_26_projections_both_regularities_incl f).2⟩
  rw [modeProj_eq_add_EX01204, modeProj_eq_add_EX01204, add_apply, add_apply, map_add, modeCLM_incl_EX01204, modeCLM_incl_EX01204]

end Projections

section Derivatives

variable {α : ℝ} [HolderExponent α]

/-- The bound for `D`, pointwise and as an operator norm. -/
theorem ex012_04_bounded_derivative_fourier_projections_deriv :
    (∀ f : PH α 2, ‖angDeriv_EX01224 f‖ ≤ 3 / (2 * Real.pi) * ‖f‖) ∧
      ‖(angDeriv_EX01224 : PH α 2 →L[ℝ] PH α 0)‖ ≤ 3 / (2 * Real.pi) :=
  ⟨ex012_24_bounded_angular_first_derivative_norm,
    ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      ex012_24_bounded_angular_first_derivative_norm⟩

/-- The bounds for the inclusion and the second derivative. -/
theorem ex012_04_bounded_derivative_fourier_projections_incl_secondDeriv :
    (∀ f : PH α 2,
      ‖ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f‖ ≤ 3 * ‖f‖) ∧
    (∀ f : PH α 2,
      ‖ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv f‖ ≤
        ((2 * Real.pi) ^ 2)⁻¹ * ‖f‖) ∧
    ‖(ex012_25_inclusion_second_derivative_elliptic_compatibility_incl : PH α 2 →L[ℝ] PH α 0)‖
      ≤ 3 ∧
    ‖(ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv :
        PH α 2 →L[ℝ] PH α 0)‖ ≤ ((2 * Real.pi) ^ 2)⁻¹ :=
  ⟨ex012_25_inclusion_second_derivative_elliptic_compatibility_incl_norm_le,
    ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv_norm_le,
    ex012_25_inclusion_second_derivative_elliptic_compatibility_incl_opNorm_le,
    ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv_opNorm_le⟩

end Derivatives

section Multiplication

variable (α : ℝ) [HolderExponent α]

/-- The multiplication of `PH α 0` is a continuous bilinear map with a nonnegative constant. -/
theorem ex012_04_bounded_derivative_fourier_projections_mul :
    ∃ m : PH α 0 →L[ℝ] PH α 0 →L[ℝ] PH α 0, ∃ C : ℝ, 0 ≤ C ∧
      (∀ f g : PH α 0, m f g = f * g) ∧
      ∀ f g : PH α 0, ‖m f g‖ ≤ C * (‖f‖ * ‖g‖) :=
  ⟨ex012_27_bounded_multiplication α, mulConst_EX01227 α, mulConst_nonneg_EX01227 α,
    ex012_27_bounded_multiplication_apply α, (ex012_27_bounded_multiplication_bound α).2⟩

end Multiplication

section Harmonic

variable (α : ℝ) [HolderExponent α]

/-- The first-harmonic injection is bounded. -/
theorem ex012_04_bounded_derivative_fourier_projections_harmInj (k : ℕ) :
    (∀ a b : ℝ, ‖harmInj_EX01228 α k (a, b)‖ ≤
      |a| * ‖cosMode_EX01228 α k 1‖ + |b| * ‖sinMode_EX01228 α k 1‖) ∧
    ‖harmInj_EX01228 α k‖ ≤ ‖cosMode_EX01228 α k 1‖ + ‖sinMode_EX01228 α k 1‖ :=
  ⟨harmInj_norm_le_EX01228 k, harmInj_opNorm_le_EX01228 k⟩

end Harmonic

section Main

variable {α : ℝ} [HolderExponent α]

/-- **EX012.04.**  The angular derivative `D`, the inclusion, `D²`, the constant and
first-harmonic projections `modeCLM k 0`, `modeCLM k 1`, the projection `Q_k` onto the complement
(`k = 0, 2`), the multiplication on `PH α 0` and the first-harmonic injection are bounded, with
the bounds of EX012.24 to EX012.28, and the projections commute with the inclusion. -/
theorem ex012_04_bounded_derivative_fourier_projections :
    (∀ f : PH α 2, ‖angDeriv_EX01224 f‖ ≤ 3 / (2 * Real.pi) * ‖f‖) ∧
    (‖(ex012_25_inclusion_second_derivative_elliptic_compatibility_incl : PH α 2 →L[ℝ] PH α 0)‖
      ≤ 3 ∧
      ‖(ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv :
        PH α 2 →L[ℝ] PH α 0)‖ ≤ ((2 * Real.pi) ^ 2)⁻¹) ∧
    (∀ k : ℕ, (k = 0 ∨ k = 2) →
      (∃ P₀ P₁ : PH α k →L[ℝ] PH α k, P₀ = PH.modeCLM k 0 ∧ P₁ = PH.modeCLM k 1 ∧
        PH.modeProj k {0, 1} = P₀ + P₁ ∧
        ∃ Q : PH α k →L[ℝ] PH.orthSub α k, Q = proj_EX01226 α k ∧
          ‖Q‖ ≤ 1 + ‖P₀‖ + ‖P₁‖)) ∧
    (∀ f : PH α 2,
      (∀ n : ℕ, PH.modeCLM 0 n
          (ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f) =
        ex012_25_inclusion_second_derivative_elliptic_compatibility_incl (PH.modeCLM 2 n f)) ∧
      ((proj_EX01226 α 0
          (ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f) :
            PH.orthSub α 0) : PH α 0) =
        ex012_25_inclusion_second_derivative_elliptic_compatibility_incl
          ((proj_EX01226 α 2 f : PH.orthSub α 2) : PH α 2)) ∧
    (∃ m : PH α 0 →L[ℝ] PH α 0 →L[ℝ] PH α 0, ∃ C : ℝ, 0 ≤ C ∧
      (∀ f g : PH α 0, m f g = f * g) ∧
      ∀ f g : PH α 0, ‖m f g‖ ≤ C * (‖f‖ * ‖g‖)) ∧
    (∀ k : ℕ, ∃ H : (ℝ × ℝ) →L[ℝ] PH α k,
      (∀ a b : ℝ, H (a, b) = a • cosMode_EX01228 α k 1 + b • sinMode_EX01228 α k 1) ∧
      ‖H‖ ≤ ‖cosMode_EX01228 α k 1‖ + ‖sinMode_EX01228 α k 1‖) := by
  refine ⟨ex012_24_bounded_angular_first_derivative_norm,
    ⟨ex012_25_inclusion_second_derivative_elliptic_compatibility_incl_opNorm_le,
      ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv_opNorm_le⟩,
    fun k _ => ⟨PH.modeCLM k 0, PH.modeCLM k 1, rfl, rfl,
      ex012_04_bounded_derivative_fourier_projections_modeProj k, proj_EX01226 α k, rfl,
      (ex012_04_bounded_derivative_fourier_projections_proj_norm k).2⟩,
    fun f => ⟨fun n => modeCLM_incl_EX01204 n f,
      (ex012_04_bounded_derivative_fourier_projections_commute f).2.2⟩,
    ex012_04_bounded_derivative_fourier_projections_mul α,
    fun k => ⟨harmInj_EX01228 α k, harmInj_apply_EX01228 k,
      (ex012_04_bounded_derivative_fourier_projections_harmInj α k).2⟩⟩

end Main

end DGPS.Frontier.EX012
