import DGPS.Frontier.EX012.T24
import DGPS.Frontier.EX012.T25

/-!
# EX012.28: Harmonic vectors and derivatives

Task id: EX012.28 (node EX012, one-site complementary range equation).
Title: Harmonic vectors and derivatives.

Provides:
* `DGPS.Frontier.EX012.ex012_28_harmonic_vectors_derivatives`: the main statement, a conjunction
  of (i) for `n = 1, 2`, `D c_n = -n s_n`, `D s_n = n c_n`, `D² c_n = -n² c_n`, `D² s_n = -n² s_n`
  (with `D` of T24, `D²` of T25, `c_n, s_n` in `PH α 2` on the left and in `PH α 0` on the right);
  (ii) `∫ c_n = ∫ s_n = 0`; (iii) `∫ c_n c_m = ∫ s_n s_m = δ_{nm}/2` and `∫ s_n c_m = 0`, all over
  `[0,1]`, for `n, m ∈ {1,2}`; (iv) the pointwise formula, the norm bounds and the injectivity of
  the bounded first-harmonic map `(a, b) ↦ a c₁ + b s₁`.
* `DGPS.Frontier.EX012.cosMode_EX01228` and `DGPS.Frontier.EX012.sinMode_EX01228`: the bundled
  vectors `c_n = cos (2π n x)` and `s_n = sin (2π n x)` in `PH α k` (any `k`).
* `DGPS.Frontier.EX012.harmInj_EX01228`: the first-harmonic injection
  `ℝ × ℝ →L[ℝ] PH α k`, `(a, b) ↦ a c₁ + b s₁`.
* Helper lemmas (all suffixed `_EX01228`): `cosMode_val_EX01228`, `sinMode_val_EX01228` (pointwise
  values); `angDeriv_cosMode_EX01228`, `angDeriv_sinMode_EX01228`, `secondDeriv_cosMode_EX01228`,
  `secondDeriv_sinMode_EX01228` (the derivative identities, for every `n : ℕ`);
  `int_cos_int_EX01228`, `int_sin_int_EX01228` (`∫₀¹ cos / sin (2π j x) = 0` for integers
  `j ≠ 0`); `int_cos_cos_EX01228`, `int_sin_sin_EX01228`, `int_sin_cos_EX01228` (product
  integrals); `int_cosMode_EX01228`, `int_sinMode_EX01228`, `int_cosMode_mul_cosMode_EX01228`,
  `int_sinMode_mul_sinMode_EX01228`, `int_sinMode_mul_cosMode_EX01228` (the same for the bundled
  vectors); `harmInj_apply_EX01228`, `harmInj_val_EX01228`, `harmInj_norm_le_EX01228`,
  `harmInj_opNorm_le_EX01228`, `harmInj_injective_EX01228` (the injection).

R5 notes:
* The only hypothesis is `[HolderExponent α]` (the campaign form of `0 < α < 1`) and, as listed
  in the specification, `n, m ∈ {1,2}`, written `n = 1 ∨ n = 2`. The helper lemmas are stronger:
  the derivative identities hold for every `n : ℕ`, and the integral lemmas need only `m ≠ 0`.
* "Bundle `c₁, s₁, c₂, s₂` in the needed `PH` spaces" is read as the families `cosMode α k n =
  PH.trig k n 1 0` and `sinMode α k n = PH.trig k n 0 1` for arbitrary `k`, so that all of
  `PH α 0` and `PH α 2` (and `PH α 1`) are covered. The `PH` library already bundles
  trigonometric functions (`isPH_trigFun`, `PH.trig` of FOU017), so the four membership proofs
  of the specification (the Lipschitz/Hölder splitting at `|x - y| ≤ 1`) are reused, not redone.
* `D` is T24's `angDeriv_EX01224 : PH α 2 →L[ℝ] PH α 0` and `D²` is T25's `secondDeriv`
  `: PH α 2 →L[ℝ] PH α 0`. Since `D` lowers `PH α 2` to `PH α 0`, the iterate `D ∘ D` is not
  available as a composition of bundled maps; `D²` is read as the T25 map, which T25 proves equal
  to the angular `D (D ·)` pointwise (`..._secondDeriv_angular`). So `D c_n` and `D² c_n` are
  stated with `c_n ∈ PH α 2` and the right side `∓ n s_n`, `-n² c_n` in `PH α 0`; the scalar
  multiples are written as `•` with the real scalar `(n : ℝ)`.
* Angular normalization: `D = (2π)⁻¹ ∂ₓ` in the unit-period variable `x`, so `D c_n = -n s_n`
  with no `2π` left over, matching the specification.
* The integrals are `intervalIntegral`s over `[0,1]` of the underlying functions `.val` (the
  value does not depend on `k`, so the statements are made for every `k`). `δ_{nm}/2` is written
  `if n = m then 1 / 2 else 0`. The case `n = m` of `∫ s_n c_m` and the constant-frequency
  contributions are handled with `sin 0 = 0`, `cos 0 = 1` after the product-to-sum identities.
* "The bounded first-harmonic injection" is read as `ℝ × ℝ →L[ℝ] PH α k` (sup norm on `ℝ × ℝ`)
  with `(a, b) ↦ a c₁ + b s₁`, for every `k`; "bounded" is the norm bound
  `‖a c₁ + b s₁‖ ≤ |a| ‖c₁‖ + |b| ‖s₁‖` and the operator norm bound `‖c₁‖ + ‖s₁‖`; "injection"
  is `Function.Injective`, proved by evaluating at `x = 0` and `x = 1/4`. Coefficient
  extraction (the left inverse) is not part of this unit (it is isolated in EX012.35).
-/

open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.EX012

section Trig

theorem int_cos_int_EX01228 (j : ℤ) (hj : j ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * Real.pi * (j : ℝ) * x) = 0 := by
  have hj' : (j : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hj
  have hc : (2 * Real.pi * (j : ℝ)) ≠ 0 := by positivity
  have := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun u => Real.cos u) hc
  rw [this]
  simp [integral_cos]
  have h2 : 2 * Real.pi * (j : ℝ) = ((2 * j : ℤ) : ℝ) * Real.pi := by push_cast; ring
  rw [h2, Real.sin_int_mul_pi]
  simp

theorem int_sin_int_EX01228 (j : ℤ) (hj : j ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * (j : ℝ) * x) = 0 := by
  have hj' : (j : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hj
  have hc : (2 * Real.pi * (j : ℝ)) ≠ 0 := by positivity
  have := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun u => Real.sin u) hc
  rw [this]
  simp [integral_sin]
  have h2 : 2 * Real.pi * (j : ℝ) = (j : ℝ) * (2 * Real.pi) := by ring
  rw [h2, Real.cos_int_mul_two_pi]
  simp

theorem int_cos_cos_EX01228 (n : ℕ) {m : ℕ} (hm : m ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * Real.pi * n * x) * Real.cos (2 * Real.pi * m * x) =
      if n = m then 1 / 2 else 0 := by
  have hpt : ∀ x : ℝ, Real.cos (2 * Real.pi * n * x) * Real.cos (2 * Real.pi * m * x) =
      (1 / 2) * Real.cos (2 * Real.pi * (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * x) +
        (1 / 2) * Real.cos (2 * Real.pi * (((n : ℤ) + (m : ℤ) : ℤ) : ℝ) * x) := by
    intro x
    have h1 := Real.cos_sub (2 * Real.pi * n * x) (2 * Real.pi * m * x)
    have h2 := Real.cos_add (2 * Real.pi * n * x) (2 * Real.pi * m * x)
    have e1 : 2 * Real.pi * (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * x =
        2 * Real.pi * n * x - 2 * Real.pi * m * x := by push_cast; ring
    have e2 : 2 * Real.pi * (((n : ℤ) + (m : ℤ) : ℤ) : ℝ) * x =
        2 * Real.pi * n * x + 2 * Real.pi * m * x := by push_cast; ring
    rw [e1, e2, h1, h2]; ring
  rw [intervalIntegral.integral_congr (fun x _ => hpt x),
    intervalIntegral.integral_add ((by fun_prop : Continuous fun x : ℝ => (1 / 2 : ℝ) *
      Real.cos (2 * Real.pi * (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * x)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x : ℝ => (1 / 2 : ℝ) *
      Real.cos (2 * Real.pi * (((n : ℤ) + (m : ℤ) : ℤ) : ℝ) * x)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hsum : ((n : ℤ) + (m : ℤ)) ≠ 0 := by omega
  rw [int_cos_int_EX01228 _ hsum]
  by_cases h : n = m
  · subst h
    simp
  · have hd : ((n : ℤ) - (m : ℤ)) ≠ 0 := by omega
    rw [int_cos_int_EX01228 _ hd]
    simp [h]

theorem int_sin_sin_EX01228 (n : ℕ) {m : ℕ} (hm : m ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * n * x) * Real.sin (2 * Real.pi * m * x) =
      if n = m then 1 / 2 else 0 := by
  have hpt : ∀ x : ℝ, Real.sin (2 * Real.pi * n * x) * Real.sin (2 * Real.pi * m * x) =
      (1 / 2) * Real.cos (2 * Real.pi * (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * x) +
        (-1 / 2) * Real.cos (2 * Real.pi * (((n : ℤ) + (m : ℤ) : ℤ) : ℝ) * x) := by
    intro x
    have h1 := Real.cos_sub (2 * Real.pi * n * x) (2 * Real.pi * m * x)
    have h2 := Real.cos_add (2 * Real.pi * n * x) (2 * Real.pi * m * x)
    have e1 : 2 * Real.pi * (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * x =
        2 * Real.pi * n * x - 2 * Real.pi * m * x := by push_cast; ring
    have e2 : 2 * Real.pi * (((n : ℤ) + (m : ℤ) : ℤ) : ℝ) * x =
        2 * Real.pi * n * x + 2 * Real.pi * m * x := by push_cast; ring
    rw [e1, e2, h1, h2]; ring
  rw [intervalIntegral.integral_congr (fun x _ => hpt x),
    intervalIntegral.integral_add ((by fun_prop : Continuous fun x : ℝ => (1 / 2 : ℝ) *
      Real.cos (2 * Real.pi * (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * x)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x : ℝ => (-1 / 2 : ℝ) *
      Real.cos (2 * Real.pi * (((n : ℤ) + (m : ℤ) : ℤ) : ℝ) * x)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hsum : ((n : ℤ) + (m : ℤ)) ≠ 0 := by omega
  rw [int_cos_int_EX01228 _ hsum]
  by_cases h : n = m
  · subst h
    simp
  · have hd : ((n : ℤ) - (m : ℤ)) ≠ 0 := by omega
    rw [int_cos_int_EX01228 _ hd]
    simp [h]

theorem int_sin_cos_EX01228 (n : ℕ) {m : ℕ} (hm : m ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * n * x) * Real.cos (2 * Real.pi * m * x) = 0 := by
  have hpt : ∀ x : ℝ, Real.sin (2 * Real.pi * n * x) * Real.cos (2 * Real.pi * m * x) =
      (1 / 2) * Real.sin (2 * Real.pi * (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * x) +
        (1 / 2) * Real.sin (2 * Real.pi * (((n : ℤ) + (m : ℤ) : ℤ) : ℝ) * x) := by
    intro x
    have h1 := Real.sin_sub (2 * Real.pi * n * x) (2 * Real.pi * m * x)
    have h2 := Real.sin_add (2 * Real.pi * n * x) (2 * Real.pi * m * x)
    have e1 : 2 * Real.pi * (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * x =
        2 * Real.pi * n * x - 2 * Real.pi * m * x := by push_cast; ring
    have e2 : 2 * Real.pi * (((n : ℤ) + (m : ℤ) : ℤ) : ℝ) * x =
        2 * Real.pi * n * x + 2 * Real.pi * m * x := by push_cast; ring
    rw [e1, e2, h1, h2]; ring
  rw [intervalIntegral.integral_congr (fun x _ => hpt x),
    intervalIntegral.integral_add ((by fun_prop : Continuous fun x : ℝ => (1 / 2 : ℝ) *
      Real.sin (2 * Real.pi * (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * x)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x : ℝ => (1 / 2 : ℝ) *
      Real.sin (2 * Real.pi * (((n : ℤ) + (m : ℤ) : ℤ) : ℝ) * x)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hsum : ((n : ℤ) + (m : ℤ)) ≠ 0 := by omega
  rw [int_sin_int_EX01228 _ hsum]
  by_cases h : n = m
  · subst h
    simp
  · have hd : ((n : ℤ) - (m : ℤ)) ≠ 0 := by omega
    rw [int_sin_int_EX01228 _ hd]
    simp

end Trig

section Modes

variable (α : ℝ) [HolderExponent α]

/-- The cosine mode `c_n(x) = cos (2π n x)` as an element of `PH α k`. -/
noncomputable def cosMode_EX01228 (k n : ℕ) : PH α k := PH.trig k n 1 0

/-- The sine mode `s_n(x) = sin (2π n x)` as an element of `PH α k`. -/
noncomputable def sinMode_EX01228 (k n : ℕ) : PH α k := PH.trig k n 0 1

variable {α}

theorem cosMode_val_EX01228 (k n : ℕ) (x : ℝ) :
    (cosMode_EX01228 α k n).val x = Real.cos (2 * Real.pi * n * x) := by
  simp [cosMode_EX01228, trigFun]

theorem sinMode_val_EX01228 (k n : ℕ) (x : ℝ) :
    (sinMode_EX01228 α k n).val x = Real.sin (2 * Real.pi * n * x) := by
  simp [sinMode_EX01228, trigFun]

theorem angDeriv_cosMode_EX01228 (n : ℕ) :
    angDeriv_EX01224 (cosMode_EX01228 α 2 n) = (-(n : ℝ)) • sinMode_EX01228 α 0 n := by
  refine PH.ext (funext fun x => ?_)
  rw [ex012_24_bounded_angular_first_derivative_val]
  simp only [cosMode_EX01228, sinMode_EX01228, PH.val_trig, trigFun_deriv, PH.val_smul,
    Pi.smul_apply, smul_eq_mul, trigFun]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem angDeriv_sinMode_EX01228 (n : ℕ) :
    angDeriv_EX01224 (sinMode_EX01228 α 2 n) = (n : ℝ) • cosMode_EX01228 α 0 n := by
  refine PH.ext (funext fun x => ?_)
  rw [ex012_24_bounded_angular_first_derivative_val]
  simp only [cosMode_EX01228, sinMode_EX01228, PH.val_trig, trigFun_deriv, PH.val_smul,
    Pi.smul_apply, smul_eq_mul, trigFun]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem secondDeriv_cosMode_EX01228 (n : ℕ) :
    ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv
        (cosMode_EX01228 α 2 n) = (-((n : ℝ) ^ 2)) • cosMode_EX01228 α 0 n := by
  refine PH.ext (funext fun x => ?_)
  rw [ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv_val]
  simp only [cosMode_EX01228, PH.val_trig, trigFun_deriv, PH.val_smul,
    Pi.smul_apply, smul_eq_mul, trigFun]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem secondDeriv_sinMode_EX01228 (n : ℕ) :
    ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv
        (sinMode_EX01228 α 2 n) = (-((n : ℝ) ^ 2)) • sinMode_EX01228 α 0 n := by
  refine PH.ext (funext fun x => ?_)
  rw [ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv_val]
  simp only [sinMode_EX01228, PH.val_trig, trigFun_deriv, PH.val_smul,
    Pi.smul_apply, smul_eq_mul, trigFun]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem int_cosMode_EX01228 (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..1, (cosMode_EX01228 α k n).val x = 0 := by
  simp only [cosMode_val_EX01228]
  have := int_cos_int_EX01228 (n : ℤ) (by exact_mod_cast hn)
  simpa using this

theorem int_sinMode_EX01228 (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..1, (sinMode_EX01228 α k n).val x = 0 := by
  simp only [sinMode_val_EX01228]
  have := int_sin_int_EX01228 (n : ℤ) (by exact_mod_cast hn)
  simpa using this

theorem int_cosMode_mul_cosMode_EX01228 (k n : ℕ) {m : ℕ} (hm : m ≠ 0) :
    ∫ x in (0 : ℝ)..1, (cosMode_EX01228 α k n).val x * (cosMode_EX01228 α k m).val x =
      if n = m then 1 / 2 else 0 := by
  simp only [cosMode_val_EX01228]
  exact int_cos_cos_EX01228 n hm

theorem int_sinMode_mul_sinMode_EX01228 (k n : ℕ) {m : ℕ} (hm : m ≠ 0) :
    ∫ x in (0 : ℝ)..1, (sinMode_EX01228 α k n).val x * (sinMode_EX01228 α k m).val x =
      if n = m then 1 / 2 else 0 := by
  simp only [sinMode_val_EX01228]
  exact int_sin_sin_EX01228 n hm

theorem int_sinMode_mul_cosMode_EX01228 (k n : ℕ) {m : ℕ} (hm : m ≠ 0) :
    ∫ x in (0 : ℝ)..1, (sinMode_EX01228 α k n).val x * (cosMode_EX01228 α k m).val x = 0 := by
  simp only [sinMode_val_EX01228, cosMode_val_EX01228]
  exact int_sin_cos_EX01228 n hm

end Modes

section Injection

variable (α : ℝ) [HolderExponent α]

/-- The bounded first-harmonic injection `(a, b) ↦ a c₁ + b s₁ : ℝ × ℝ →L[ℝ] PH α k`. -/
noncomputable def harmInj_EX01228 (k : ℕ) : (ℝ × ℝ) →L[ℝ] PH α k :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (cosMode_EX01228 α k 1) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (sinMode_EX01228 α k 1)

variable {α}

theorem harmInj_apply_EX01228 (k : ℕ) (a b : ℝ) :
    harmInj_EX01228 α k (a, b) = a • cosMode_EX01228 α k 1 + b • sinMode_EX01228 α k 1 := rfl

theorem harmInj_val_EX01228 (k : ℕ) (a b x : ℝ) :
    (harmInj_EX01228 α k (a, b)).val x =
      a * Real.cos (2 * Real.pi * x) + b * Real.sin (2 * Real.pi * x) := by
  rw [harmInj_apply_EX01228, PH.val_add, Pi.add_apply, PH.val_smul, PH.val_smul, Pi.smul_apply,
    Pi.smul_apply, cosMode_val_EX01228, sinMode_val_EX01228]
  simp

theorem harmInj_norm_le_EX01228 (k : ℕ) (a b : ℝ) :
    ‖harmInj_EX01228 α k (a, b)‖ ≤
      |a| * ‖cosMode_EX01228 α k 1‖ + |b| * ‖sinMode_EX01228 α k 1‖ := by
  rw [harmInj_apply_EX01228]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]

theorem harmInj_opNorm_le_EX01228 (k : ℕ) :
    ‖harmInj_EX01228 α k‖ ≤ ‖cosMode_EX01228 α k 1‖ + ‖sinMode_EX01228 α k 1‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) fun p => ?_
  obtain ⟨a, b⟩ := p
  have ha : |a| ≤ ‖(a, b)‖ := by simp
  have hb : |b| ≤ ‖(a, b)‖ := by simp
  have := harmInj_norm_le_EX01228 (α := α) k a b
  have h1 := norm_nonneg (cosMode_EX01228 α k 1)
  have h2 := norm_nonneg (sinMode_EX01228 α k 1)
  nlinarith [mul_le_mul_of_nonneg_right ha h1, mul_le_mul_of_nonneg_right hb h2]

theorem harmInj_injective_EX01228 (k : ℕ) : Function.Injective (harmInj_EX01228 α k) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨a, b⟩ h
  have h0 := congrArg (fun f : PH α k => f.val 0) h
  have h1 := congrArg (fun f : PH α k => f.val (1 / 4)) h
  simp only [harmInj_val_EX01228, PH.val_zero, Pi.zero_apply] at h0 h1
  have e : 2 * Real.pi * (1 / 4 : ℝ) = Real.pi / 2 := by ring
  rw [e] at h1
  simp at h0 h1
  simp [h0, h1]

end Injection

section Main

variable {α : ℝ} [HolderExponent α]

/-- **EX012.28.**  For `n = 1, 2`: `D c_n = -n s_n`, `D s_n = n c_n`, `D² c_n = -n² c_n`,
`D² s_n = -n² s_n` (with `c_n, s_n` taken in `PH α 2` on the left and in `PH α 0` on the right);
the integrals `∫ c_n = ∫ s_n = 0`, `∫ c_n c_m = ∫ s_n s_m = δ_{nm}/2`, `∫ s_n c_m = 0` over
`[0,1]`; and the first-harmonic map `(a, b) ↦ a c₁ + b s₁` is a bounded injective linear map
`ℝ × ℝ →L[ℝ] PH α k`, with the pointwise formula and the norm bound `|a| ‖c₁‖ + |b| ‖s₁‖`. -/
theorem ex012_28_harmonic_vectors_derivatives :
    (∀ n : ℕ, (n = 1 ∨ n = 2) →
      angDeriv_EX01224 (cosMode_EX01228 α 2 n) = (-(n : ℝ)) • sinMode_EX01228 α 0 n ∧
      angDeriv_EX01224 (sinMode_EX01228 α 2 n) = (n : ℝ) • cosMode_EX01228 α 0 n ∧
      ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv
          (cosMode_EX01228 α 2 n) = (-((n : ℝ) ^ 2)) • cosMode_EX01228 α 0 n ∧
      ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv
          (sinMode_EX01228 α 2 n) = (-((n : ℝ) ^ 2)) • sinMode_EX01228 α 0 n) ∧
    (∀ (k n : ℕ), (n = 1 ∨ n = 2) →
      (∫ x in (0 : ℝ)..1, (cosMode_EX01228 α k n).val x) = 0 ∧
      (∫ x in (0 : ℝ)..1, (sinMode_EX01228 α k n).val x) = 0) ∧
    (∀ (k n m : ℕ), (n = 1 ∨ n = 2) → (m = 1 ∨ m = 2) →
      (∫ x in (0 : ℝ)..1, (cosMode_EX01228 α k n).val x * (cosMode_EX01228 α k m).val x) =
          (if n = m then 1 / 2 else 0) ∧
      (∫ x in (0 : ℝ)..1, (sinMode_EX01228 α k n).val x * (sinMode_EX01228 α k m).val x) =
          (if n = m then 1 / 2 else 0) ∧
      (∫ x in (0 : ℝ)..1, (sinMode_EX01228 α k n).val x * (cosMode_EX01228 α k m).val x) = 0) ∧
    (∀ k : ℕ,
      (∀ a b x : ℝ, (harmInj_EX01228 α k (a, b)).val x =
        a * Real.cos (2 * Real.pi * x) + b * Real.sin (2 * Real.pi * x)) ∧
      (∀ a b : ℝ, ‖harmInj_EX01228 α k (a, b)‖ ≤
        |a| * ‖cosMode_EX01228 α k 1‖ + |b| * ‖sinMode_EX01228 α k 1‖) ∧
      ‖harmInj_EX01228 α k‖ ≤ ‖cosMode_EX01228 α k 1‖ + ‖sinMode_EX01228 α k 1‖ ∧
      Function.Injective (harmInj_EX01228 α k)) := by
  refine ⟨fun n _ => ⟨angDeriv_cosMode_EX01228 n, angDeriv_sinMode_EX01228 n,
      secondDeriv_cosMode_EX01228 n, secondDeriv_sinMode_EX01228 n⟩, ?_, ?_, fun k => ?_⟩
  · intro k n hn
    have hn' : n ≠ 0 := by omega
    exact ⟨int_cosMode_EX01228 k hn', int_sinMode_EX01228 k hn'⟩
  · intro k n m _ hm
    have hm' : m ≠ 0 := by omega
    exact ⟨int_cosMode_mul_cosMode_EX01228 k n hm', int_sinMode_mul_sinMode_EX01228 k n hm',
      int_sinMode_mul_cosMode_EX01228 k n hm'⟩
  · exact ⟨harmInj_val_EX01228 k, harmInj_norm_le_EX01228 k, harmInj_opNorm_le_EX01228 k,
      harmInj_injective_EX01228 k⟩

end Main

end DGPS.Frontier.EX012
