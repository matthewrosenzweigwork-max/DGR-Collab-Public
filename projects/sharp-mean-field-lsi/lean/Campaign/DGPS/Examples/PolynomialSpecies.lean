import DGPS.Circle.AngularNormalization
import DGPS.Model.Data

/-!
# The canonical elementary polynomial model (EX052)

Fix `η = (√97 - 7)/8`, the degree-two feature `P_h(θ) = cos 2θ - (h/3) cos θ` and the polynomial
centering `m₀(h) = -h²/24`, with `θ = 2π x` on the unit-period torus `Torus 1`. The model is

* `V_h = -h cos θ + η (P_h - m₀)²`,
* `W_h(θ, φ) = -η (P_h(θ) - P_h(φ))²`.

`DGPS.Examples.canonical_elementary_polynomial_model h : InteractionData 1` is this model, defined
for every real `h` (the parameter is fixed before any optimizer or split parameter is chosen).
The exact formulas are used: there is no Bessel centering. Declarations:

* `eta_relation`, `eta_pos`: `7 η + 4 η² = 3` and `0 < η`;
* `polyV_lift`, `polyW_lift`, `angV_model`, `angW_model`: the explicit formulas on lifts and in the
  angular variable `θ = 2π x` of `DGPS.Circle.AngularNormalization` (EX001);
* `polyV_trig_degree_four`: `V_h` is a combination of `1, cos θ, …, cos 4θ`;
* `lipschitzData_canonical_model`: direct Lipschitz regularity (`LipschitzData`);
* `canonical_elementary_polynomial_model_spec`: the bundled statement.
-/

open scoped ContDiff

namespace DGPS.Examples.PolynomialSpecies

open DGPS Real

/-- The fixed radical `η = (√97 - 7)/8`. -/
noncomputable def eta : ℝ := (Real.sqrt 97 - 7) / 8

theorem eta_relation : 7 * eta + 4 * eta ^ 2 = 3 := by
  have h : Real.sqrt 97 ^ 2 = 97 := Real.sq_sqrt (by norm_num)
  unfold eta
  nlinarith [h]

theorem eta_pos : 0 < eta := by
  have : (7 : ℝ) < Real.sqrt 97 := by
    rw [show (7 : ℝ) = Real.sqrt 49 by
      rw [show (49 : ℝ) = 7 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  unfold eta
  linarith

/-- The `k`-th cosine mode `x ↦ cos (2π k x)` on `Torus 1`. -/
noncomputable def cosT (k : ℕ) (x : Torus 1) : ℝ := (fourier (k : ℤ) (x 0)).re

theorem continuous_cosT (k : ℕ) : Continuous (cosT k) :=
  Complex.continuous_re.comp ((fourier (k : ℤ)).continuous.comp (continuous_apply 0))

theorem cosT_coe (k : ℕ) (a : ℝ) :
    (fourier (k : ℤ) (a : AddCircle (1 : ℝ))).re = Real.cos (2 * π * k * a) := by
  have h2 : (2 * Real.pi * Complex.I * ((k : ℤ) : ℂ) * (a : ℂ) / ((1 : ℝ) : ℂ) : ℂ) =
      ((2 * Real.pi * k * a : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [fourier_coe_apply, h2, Complex.exp_ofReal_mul_I_re]

theorem cosT_lift (k : ℕ) (a : Fin 1 → ℝ) :
    cosT k (torusLift a) = Real.cos (2 * π * k * a 0) := by
  simpa [cosT, torusLift, SharpLSI.liftT] using cosT_coe k (a 0)

theorem exists_lift (x : Torus 1) : ∃ t : ℝ, torusLift (fun _ => t) = x := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (x 0)
  refine ⟨t, funext fun i => ?_⟩
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  simpa [torusLift, SharpLSI.liftT] using ht

theorem abs_cosT_le (k : ℕ) (x : Torus 1) : |cosT k x| ≤ 1 := by
  obtain ⟨t, rfl⟩ := exists_lift x
  rw [cosT_lift]
  exact Real.abs_cos_le_one _

private theorem torusDist_one' (x y : Torus 1) : torusDist x y = ‖x 0 - y 0‖ := by
  unfold torusDist SharpLSI.flatDist
  simp

theorem abs_cosT_sub_le (k : ℕ) (x y : Torus 1) :
    |cosT k x - cosT k y| ≤ 2 * π * k * torusDist x y := by
  rw [torusDist_one']
  unfold cosT
  generalize x 0 = t
  generalize y 0 = t'
  induction t using QuotientAddGroup.induction_on with | _ a => ?_
  induction t' using QuotientAddGroup.induction_on with | _ b => ?_
  rw [← QuotientAddGroup.mk_sub, AddCircle.norm_eq]
  have ea : (QuotientAddGroup.mk a : AddCircle (1 : ℝ)) = (a : AddCircle (1 : ℝ)) := rfl
  have eb : (QuotientAddGroup.mk b : AddCircle (1 : ℝ)) = (b : AddCircle (1 : ℝ)) := rfl
  rw [ea, eb, cosT_coe, cosT_coe]
  set n : ℤ := round ((1 : ℝ)⁻¹ * (a - b)) with hn
  have hcos : Real.cos (2 * π * k * a) =
      Real.cos (2 * π * k * (b + (a - b - n * 1))) := by
    have : 2 * π * k * a =
        2 * π * k * (b + (a - b - n * 1)) + ((k * n : ℤ) : ℝ) * (2 * π) := by
      push_cast; ring
    rw [this, Real.cos_add_int_mul_two_pi]
  rw [hcos]
  refine (Real.abs_cos_sub_cos_le _ _).trans ?_
  have : 2 * π * k * (b + (a - b - n * 1)) - 2 * π * k * b = 2 * π * k * (a - b - n * 1) := by
    ring
  rw [this, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * π * k)]

/-- The degree-two feature `P_h = cos 2θ - (h/3) cos θ` on `Torus 1` (`θ = 2π x`). -/
noncomputable def polyFeature (h : ℝ) (x : Torus 1) : ℝ := cosT 2 x - h / 3 * cosT 1 x

/-- The polynomial centering `m₀(h) = -h²/24` (no Bessel centering). -/
noncomputable def polyCentering (h : ℝ) : ℝ := -h ^ 2 / 24

/-- `V_h = -h cos θ + η (P_h - m₀)²`. -/
noncomputable def polyV (h : ℝ) (x : Torus 1) : ℝ :=
  -h * cosT 1 x + eta * (polyFeature h x - polyCentering h) ^ 2

/-- `W_h(x, y) = -η (P_h(x) - P_h(y))²`. -/
noncomputable def polyW (h : ℝ) (x y : Torus 1) : ℝ :=
  -eta * (polyFeature h x - polyFeature h y) ^ 2

theorem continuous_polyFeature (h : ℝ) : Continuous (polyFeature h) :=
  (continuous_cosT 2).sub (continuous_const.mul (continuous_cosT 1))

theorem continuous_polyV (h : ℝ) : Continuous (polyV h) := by
  unfold polyV
  have := continuous_polyFeature h
  have := continuous_cosT 1
  fun_prop

theorem continuous_polyW (h : ℝ) : Continuous (fun p : Torus 1 × Torus 1 => polyW h p.1 p.2) := by
  unfold polyW
  have h1 : Continuous fun p : Torus 1 × Torus 1 => polyFeature h p.1 :=
    (continuous_polyFeature h).comp continuous_fst
  have h2 : Continuous fun p : Torus 1 × Torus 1 => polyFeature h p.2 :=
    (continuous_polyFeature h).comp continuous_snd
  fun_prop

theorem polyW_symm (h : ℝ) (x y : Torus 1) : polyW h x y = polyW h y x := by
  unfold polyW; ring

theorem polyW_diag (h : ℝ) (x : Torus 1) : polyW h x x = 0 := by
  unfold polyW; ring

end DGPS.Examples.PolynomialSpecies

namespace DGPS.Examples

open DGPS.Examples.PolynomialSpecies

/-- **EX052.** The canonical elementary polynomial model with fixed `η = (√97 - 7)/8`,
`P_h(θ) = cos 2θ - (h/3) cos θ`, `m₀(h) = -h²/24`, `V_h = -h cos θ + η (P_h - m₀)²` and
`W_h(θ, φ) = -η (P_h(θ) - P_h(φ))²`, with `θ = 2π x` on `Torus 1`. -/
noncomputable def canonical_elementary_polynomial_model (h : ℝ) : InteractionData 1 where
  V := polyV h
  W := polyW h
  V_continuous := continuous_polyV h
  W_continuous := continuous_polyW h
  W_symm := polyW_symm h
  W_diag := polyW_diag h

end DGPS.Examples

namespace DGPS.Examples.PolynomialSpecies

open DGPS Real

@[simp] theorem model_V (h : ℝ) :
    (canonical_elementary_polynomial_model h).V = polyV h := rfl

@[simp] theorem model_W (h : ℝ) :
    (canonical_elementary_polynomial_model h).W = polyW h := rfl

/-- Explicit formula for `V_h` on lifts, `θ = 2π a`. -/
theorem polyV_lift (h : ℝ) (a : Fin 1 → ℝ) :
    (canonical_elementary_polynomial_model h).V (torusLift a) =
      -h * Real.cos (2 * π * a 0) +
        eta * (Real.cos (2 * (2 * π * a 0)) - h / 3 * Real.cos (2 * π * a 0) + h ^ 2 / 24) ^ 2 := by
  have h2 : 2 * π * ((2 : ℕ) : ℝ) * a 0 = 2 * (2 * π * a 0) := by push_cast; ring
  have h1 : 2 * π * ((1 : ℕ) : ℝ) * a 0 = 2 * π * a 0 := by push_cast; ring
  simp only [model_V, polyV, polyFeature, polyCentering, cosT_lift, h1, h2]
  ring_nf

/-- Explicit formula for `W_h` on lifts. -/
theorem polyW_lift (h : ℝ) (a b : Fin 1 → ℝ) :
    (canonical_elementary_polynomial_model h).W (torusLift a) (torusLift b) =
      -eta * ((Real.cos (2 * (2 * π * a 0)) - h / 3 * Real.cos (2 * π * a 0)) -
        (Real.cos (2 * (2 * π * b 0)) - h / 3 * Real.cos (2 * π * b 0))) ^ 2 := by
  have h2 : ∀ c : Fin 1 → ℝ, 2 * π * ((2 : ℕ) : ℝ) * c 0 = 2 * (2 * π * c 0) := by
    intro c; push_cast; ring
  have h1 : ∀ c : Fin 1 → ℝ, 2 * π * ((1 : ℕ) : ℝ) * c 0 = 2 * π * c 0 := by
    intro c; push_cast; ring
  simp only [model_W, polyW, polyFeature, cosT_lift, h1, h2]

/-- In the angular variable `θ = 2π x` (EX001, `angEquiv`): `V_h(θ) = -h cos θ + η (P_h(θ) - m₀)²`. -/
theorem angV_model (h θ : ℝ) :
    Circle.AngularNormalization.angV (canonical_elementary_polynomial_model h) (θ : Circle.AngularNormalization.AngCircle) =
      -h * Real.cos θ + eta * (Real.cos (2 * θ) - h / 3 * Real.cos θ - (-h ^ 2 / 24)) ^ 2 := by
  have e : Circle.AngularNormalization.angEquiv.symm (θ : Circle.AngularNormalization.AngCircle) =
      torusLift (fun _ => θ / (2 * π)) := by
    rw [MeasurableEquiv.symm_apply_eq, Circle.AngularNormalization.angEquiv_apply]
    have : ((torusLift fun _ : Fin 1 => θ / (2 * π)) 0 : UnitAddCircle) =
        ((θ / (2 * π) : ℝ) : UnitAddCircle) := rfl
    rw [this, Circle.AngularNormalization.angRescale_mk]
    congr 1
    field_simp
  unfold Circle.AngularNormalization.angV
  rw [e, polyV_lift]
  have : 2 * π * (θ / (2 * π)) = θ := by field_simp
  simp only [this]
  ring

/-- In the angular variable: `W_h(θ, φ) = -η (P_h(θ) - P_h(φ))²`. -/
theorem angW_model (h θ φ : ℝ) :
    Circle.AngularNormalization.angW (canonical_elementary_polynomial_model h)
        (θ : Circle.AngularNormalization.AngCircle) (φ : Circle.AngularNormalization.AngCircle) =
      -eta * ((Real.cos (2 * θ) - h / 3 * Real.cos θ) -
        (Real.cos (2 * φ) - h / 3 * Real.cos φ)) ^ 2 := by
  have e : ∀ θ : ℝ, Circle.AngularNormalization.angEquiv.symm
      (θ : Circle.AngularNormalization.AngCircle) = torusLift (fun _ => θ / (2 * π)) := by
    intro θ
    rw [MeasurableEquiv.symm_apply_eq, Circle.AngularNormalization.angEquiv_apply]
    have : ((torusLift fun _ : Fin 1 => θ / (2 * π)) 0 : UnitAddCircle) =
        ((θ / (2 * π) : ℝ) : UnitAddCircle) := rfl
    rw [this, Circle.AngularNormalization.angRescale_mk]
    congr 1
    field_simp
  unfold Circle.AngularNormalization.angW
  rw [e, e, polyW_lift]
  have : ∀ θ : ℝ, 2 * π * (θ / (2 * π)) = θ := fun θ => by field_simp
  simp only [this]

/-- `V_h` has trigonometric degree at most four: it is a combination of `cos (kθ)`, `k ≤ 4`. -/
theorem polyV_trig_degree_four (h : ℝ) :
    ∃ c : Fin 5 → ℝ, ∀ x : Torus 1,
      (canonical_elementary_polynomial_model h).V x = ∑ k : Fin 5, c k * cosT k x := by
  refine ⟨![eta * (1 / 2 + h ^ 2 / 18 + (h ^ 2 / 24) ^ 2),
    -h - eta * (h / 3 + 2 * h * (h ^ 2 / 24) / 3), eta * (h ^ 2 / 18 + 2 * (h ^ 2 / 24)),
    -eta * h / 3, eta / 2], fun x => ?_⟩
  obtain ⟨t, rfl⟩ := exists_lift x
  rw [polyV_lift, Fin.sum_univ_five]
  simp only [cosT_lift]
  set θ := 2 * π * t with hθ
  norm_num
  have e1 : 2 * π * t = θ := hθ.symm
  have e2 : 2 * π * 2 * t = 2 * θ := by rw [hθ]; ring
  have e3 : 2 * π * 3 * t = 3 * θ := by rw [hθ]; ring
  have e4 : 2 * π * 4 * t = 4 * θ := by rw [hθ]; ring
  rw [e1, e2, e3, e4]
  have c2 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  have c3 : Real.cos (3 * θ) = 4 * Real.cos θ ^ 3 - 3 * Real.cos θ := Real.cos_three_mul θ
  have c4 : Real.cos (4 * θ) = 2 * (2 * Real.cos θ ^ 2 - 1) ^ 2 - 1 := by
    rw [show 4 * θ = 2 * (2 * θ) by ring, Real.cos_two_mul, c2]
  rw [c2, c3, c4]
  ring

/-! ### Direct Lipschitz regularity -/

theorem abs_polyFeature_le (h : ℝ) (x : Torus 1) : |polyFeature h x| ≤ 1 + |h| / 3 := by
  unfold polyFeature
  calc |cosT 2 x - h / 3 * cosT 1 x| ≤ |cosT 2 x| + |h / 3 * cosT 1 x| := abs_sub _ _
    _ ≤ 1 + |h| / 3 := by
      rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      have h1 := abs_cosT_le 2 x
      have h2 := abs_cosT_le 1 x
      have h3 : |h| / 3 * |cosT 1 x| ≤ |h| / 3 * 1 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith

theorem abs_polyFeature_sub_le (h : ℝ) (x y : Torus 1) :
    |polyFeature h x - polyFeature h y| ≤ (4 * π + |h| / 3 * (2 * π)) * torusDist x y := by
  have h2 := abs_cosT_sub_le 2 x y
  have h1 := abs_cosT_sub_le 1 x y
  have e : polyFeature h x - polyFeature h y =
      (cosT 2 x - cosT 2 y) - h / 3 * (cosT 1 x - cosT 1 y) := by
    unfold polyFeature; ring
  rw [e]
  have h3 : |h / 3 * (cosT 1 x - cosT 1 y)| ≤ |h| / 3 * (2 * π * (1 : ℕ) * torusDist x y) := by
    rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  calc _ ≤ |cosT 2 x - cosT 2 y| + |h / 3 * (cosT 1 x - cosT 1 y)| := abs_sub _ _
    _ ≤ 2 * π * (2 : ℕ) * torusDist x y + |h| / 3 * (2 * π * (1 : ℕ) * torusDist x y) :=
        add_le_add h2 h3
    _ = _ := by push_cast; ring

theorem lipschitzData_canonical_model (h : ℝ) :
    LipschitzData (canonical_elementary_polynomial_model h) := by
  have hdist : ∀ x y : Torus 1, 0 ≤ torusDist x y := fun x y => Real.sqrt_nonneg _
  set L : ℝ := 4 * π + |h| / 3 * (2 * π) with hL
  set B : ℝ := 1 + |h| / 3 with hB
  have hL0 : 0 ≤ L := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hη := eta_pos
  refine ⟨⟨|h| * (2 * π) + eta * L * (2 * B + 2 * |polyCentering h|), fun x y => ?_⟩, ?_⟩
  · show |polyV h x - polyV h y| ≤ _
    have e : polyV h x - polyV h y = -h * (cosT 1 x - cosT 1 y) +
        eta * ((polyFeature h x - polyFeature h y) *
          (polyFeature h x + polyFeature h y - 2 * polyCentering h)) := by
      unfold polyV; ring
    rw [e]
    have h1 : |-h * (cosT 1 x - cosT 1 y)| ≤ |h| * (2 * π) * torusDist x y := by
      have := abs_cosT_sub_le 1 x y
      rw [abs_mul, abs_neg]
      calc |h| * |cosT 1 x - cosT 1 y| ≤ |h| * (2 * π * (1 : ℕ) * torusDist x y) :=
            mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = _ := by push_cast; ring
    have hP := abs_polyFeature_sub_le h x y
    have hPx := abs_polyFeature_le h x
    have hPy := abs_polyFeature_le h y
    have h2 : |polyFeature h x + polyFeature h y - 2 * polyCentering h| ≤
        2 * B + 2 * |polyCentering h| := by
      calc _ ≤ |polyFeature h x + polyFeature h y| + |2 * polyCentering h| := abs_sub _ _
        _ ≤ |polyFeature h x| + |polyFeature h y| + 2 * |polyCentering h| := by
            rw [abs_mul, abs_two]
            exact add_le_add_left (abs_add_le _ _) _
        _ ≤ _ := by linarith
    have h3 : |eta * ((polyFeature h x - polyFeature h y) *
        (polyFeature h x + polyFeature h y - 2 * polyCentering h))| ≤
        eta * L * (2 * B + 2 * |polyCentering h|) * torusDist x y := by
      rw [abs_mul, abs_of_pos hη, abs_mul]
      have h4 : |polyFeature h x - polyFeature h y| *
          |polyFeature h x + polyFeature h y - 2 * polyCentering h| ≤
          (L * torusDist x y) * (2 * B + 2 * |polyCentering h|) :=
        mul_le_mul hP h2 (abs_nonneg _) (mul_nonneg hL0 (hdist x y))
      calc eta * (|polyFeature h x - polyFeature h y| *
            |polyFeature h x + polyFeature h y - 2 * polyCentering h|)
          ≤ eta * ((L * torusDist x y) * (2 * B + 2 * |polyCentering h|)) :=
            mul_le_mul_of_nonneg_left h4 hη.le
        _ = _ := by ring
    calc _ ≤ |-h * (cosT 1 x - cosT 1 y)| +
          |eta * ((polyFeature h x - polyFeature h y) *
            (polyFeature h x + polyFeature h y - 2 * polyCentering h))| := abs_add_le _ _
      _ ≤ _ := by nlinarith [h1, h3]
  · rw [LipschitzData.W_lipschitz_sum_iff]
    refine ⟨eta * L * (4 * B), fun x y x' y' => ?_⟩
    show |polyW h x y - polyW h x' y'| ≤ _
    have e : polyW h x y - polyW h x' y' =
        -eta * (((polyFeature h x - polyFeature h y) - (polyFeature h x' - polyFeature h y')) *
          ((polyFeature h x - polyFeature h y) + (polyFeature h x' - polyFeature h y'))) := by
      unfold polyW; ring
    rw [e, abs_mul, abs_mul, abs_neg, abs_of_pos hη]
    have hx := abs_polyFeature_sub_le h x x'
    have hy := abs_polyFeature_sub_le h y y'
    have hD : |(polyFeature h x - polyFeature h y) - (polyFeature h x' - polyFeature h y')| ≤
        L * (torusDist x x' + torusDist y y') := by
      have e2 : (polyFeature h x - polyFeature h y) - (polyFeature h x' - polyFeature h y') =
          (polyFeature h x - polyFeature h x') - (polyFeature h y - polyFeature h y') := by ring
      rw [e2]
      calc _ ≤ |polyFeature h x - polyFeature h x'| + |polyFeature h y - polyFeature h y'| :=
            abs_sub _ _
        _ ≤ L * torusDist x x' + L * torusDist y y' := add_le_add hx hy
        _ = _ := by ring
    have hS : |(polyFeature h x - polyFeature h y) + (polyFeature h x' - polyFeature h y')| ≤
        4 * B := by
      have a1 := abs_polyFeature_le h x
      have a2 := abs_polyFeature_le h y
      have a3 := abs_polyFeature_le h x'
      have a4 := abs_polyFeature_le h y'
      calc _ ≤ |polyFeature h x - polyFeature h y| + |polyFeature h x' - polyFeature h y'| :=
            abs_add_le _ _
        _ ≤ (|polyFeature h x| + |polyFeature h y|) + (|polyFeature h x'| + |polyFeature h y'|) :=
            add_le_add (abs_sub _ _) (abs_sub _ _)
        _ ≤ 4 * B := by linarith
    calc eta * (|(polyFeature h x - polyFeature h y) - (polyFeature h x' - polyFeature h y')| *
          |(polyFeature h x - polyFeature h y) + (polyFeature h x' - polyFeature h y')|)
        ≤ eta * ((L * (torusDist x x' + torusDist y y')) * (4 * B)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hD hS (abs_nonneg _)
            (mul_nonneg hL0 (add_nonneg (hdist _ _) (hdist _ _)))) hη.le
      _ = _ := by ring

end DGPS.Examples.PolynomialSpecies

namespace DGPS.Examples

open DGPS.Examples.PolynomialSpecies

/-- **EX052 (bundled specification).** `η = (√97 - 7)/8` satisfies `7 η + 4 η² = 3`, `0 < η`; for
every real `h` the model `canonical_elementary_polynomial_model h` has `V = polyV h` and
`W = polyW h` (`V_h = -h cos θ + η (P_h - m₀)²`, `W_h = -η (P_h(θ) - P_h(φ))²`, `m₀ = -h²/24`),
`V` has trigonometric degree at most four, the interaction is a single squared difference of the
degree-two feature `P_h` (symmetric, zero diagonal), and the data are directly Lipschitz. -/
theorem canonical_elementary_polynomial_model_spec :
    7 * eta + 4 * eta ^ 2 = 3 ∧ 0 < eta ∧
    ∀ h : ℝ,
      (canonical_elementary_polynomial_model h).V = polyV h ∧
      (canonical_elementary_polynomial_model h).W = polyW h ∧
      (∀ x : Torus 1, polyV h x =
        -h * cosT 1 x + eta * (polyFeature h x - (-h ^ 2 / 24)) ^ 2) ∧
      (∀ x y : Torus 1, polyW h x y = -eta * (polyFeature h x - polyFeature h y) ^ 2) ∧
      (∀ x : Torus 1, polyFeature h x = cosT 2 x - h / 3 * cosT 1 x) ∧
      (∃ c : Fin 5 → ℝ, ∀ x : Torus 1,
        (canonical_elementary_polynomial_model h).V x = ∑ k : Fin 5, c k * cosT k x) ∧
      (∀ x y, (canonical_elementary_polynomial_model h).W x y =
        (canonical_elementary_polynomial_model h).W y x) ∧
      (∀ x, (canonical_elementary_polynomial_model h).W x x = 0) ∧
      LipschitzData (canonical_elementary_polynomial_model h) :=
  ⟨eta_relation, eta_pos, fun h =>
    ⟨rfl, rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, polyV_trig_degree_four h,
      (canonical_elementary_polynomial_model h).W_symm,
      (canonical_elementary_polynomial_model h).W_diag, lipschitzData_canonical_model h⟩⟩

end DGPS.Examples
