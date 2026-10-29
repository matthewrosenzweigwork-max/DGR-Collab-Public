import DGPS.FiniteN.ScalarCosine

/-!
# FIN065: the explicit anisotropic quartic model and its rational Bessel certificate

Write `g = I₁/I₀` (`besselRatio`), `b = g(4)`, `κ = 5/b`, `η = 4/5`, `c(x) = cos 2πx`,
`s(x) = sin 2πx`.  The model `DGPS.Models.anisotropicQuarticSaddle` has external field one and
`V = -c - (κ/2)(c² + η s²)`, `W(x,y) = (κ/2)[(c x - c y)² + η (s x - s y)²]`.

The certificate `b > 889110/1029889 > 55/64 > 6/7` follows from exact rational arithmetic on the
series of EX002: the positive series of `I₁(4)` truncated after `n = 5` (the `n = 6` term is also
kept, which makes the inequality strict) is a lower bound, and the tail of the series of `I₀(4)`
from `n = 6` is bounded by the geometric series with ratio `4/49`.  With the Riccati identity
`g' = 1 - g/r - g²` at `r = 4`, `v = g'(4) = 1 - b/4 - b²`, and the positivity of
`A = b/5 - v`, `d = b - 4 v` and the bound `1 - κ v = 9/4 + 5b - 5/b > 1/2` reduce to `b > 6/7`.

The main theorem is `DGPS.FiniteN.quartic_explicit_model_rational_certificate`.
-/

open MeasureTheory Filter Topology
open DGPS.Circle.BesselMoments DGPS.Circle.BesselConcavity

namespace DGPS.Models

/-- `s(x) = sin 2πx` on the circle `𝕋^1`, as the imaginary part of the first character. -/
noncomputable def scalarSin (x : DGPS.Torus 1) : ℝ := (fourier 1 (x 0)).im

theorem continuous_scalarSin : Continuous scalarSin :=
  Complex.continuous_im.comp ((map_continuous (fourier (T := 1) 1)).comp (continuous_apply 0))

theorem scalarSin_lift (a : Fin 1 → ℝ) :
    scalarSin (DGPS.torusLift a) = Real.sin (2 * Real.pi * a 0) := by
  have h : (DGPS.torusLift a) 0 = ((a 0 : ℝ) : UnitAddCircle) := rfl
  rw [scalarSin, h, fourier_coe_apply]
  have : (2 * Real.pi * Complex.I * ((1:ℤ) : ℂ) * (a 0 : ℂ) / ((1 : ℝ) : ℂ)) =
      ((2 * Real.pi * a 0 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_im]

/-- `b = g(4) = I₁(4)/I₀(4)`. -/
noncomputable def quarticB : ℝ := besselRatio 4

/-- `κ = 5 / b`. -/
noncomputable def quarticKappa : ℝ := 5 / quarticB

/-- `η = 4/5`. -/
noncomputable def quarticEta : ℝ := 4 / 5

/-- The anisotropic quartic saddle model: external field one,
`V = -c - (κ/2)(c² + η s²)` and `W(x,y) = (κ/2)[(c x - c y)² + η (s x - s y)²]`. -/
noncomputable def anisotropicQuarticSaddle : DGPS.InteractionData 1 where
  V := fun x => -scalarCos x - quarticKappa / 2 * (scalarCos x ^ 2 + quarticEta * scalarSin x ^ 2)
  W := fun x y => quarticKappa / 2 *
    ((scalarCos x - scalarCos y) ^ 2 + quarticEta * (scalarSin x - scalarSin y) ^ 2)
  V_continuous := by
    have := continuous_scalarCos; have := continuous_scalarSin; fun_prop
  W_continuous := by
    have := continuous_scalarCos; have := continuous_scalarSin; fun_prop
  W_symm := fun x y => by ring
  W_diag := fun x => by simp

end DGPS.Models

namespace DGPS.FiniteN.QuarticSaddle

/-- terms of the series `I₀(4) = ∑ 4^j / (j!)²` -/
noncomputable def i0Term (j : ℕ) : ℝ := (4 : ℝ) ^ j / (j.factorial : ℝ) ^ 2

theorem i0Term_pos (j : ℕ) : 0 < i0Term j := by unfold i0Term; positivity

theorem i0Term_succ (j : ℕ) : i0Term (j + 1) = i0Term j * (4 / ((j : ℝ) + 1) ^ 2) := by
  unfold i0Term
  rw [Nat.factorial_succ]
  push_cast
  have : (j.factorial : ℝ) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp

theorem i0Term_tail (j : ℕ) : i0Term (j + 6) ≤ i0Term 6 * (4 / 49) ^ j := by
  induction j with
  | zero => simp
  | succ n ih =>
    have h1 : i0Term (n + 1 + 6) = i0Term (n + 6) * (4 / (((n + 6 : ℕ) : ℝ) + 1) ^ 2) := by
      rw [show n + 1 + 6 = (n + 6) + 1 by ring, i0Term_succ]
    rw [h1, pow_succ]
    have h2 : 4 / (((n + 6 : ℕ) : ℝ) + 1) ^ 2 ≤ 4 / 49 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      push_cast
      nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have h3 : 0 ≤ 4 / (((n + 6 : ℕ) : ℝ) + 1) ^ 2 := by positivity
    calc i0Term (n + 6) * (4 / (((n + 6 : ℕ) : ℝ) + 1) ^ 2)
        ≤ (i0Term 6 * (4 / 49) ^ n) * (4 / 49) :=
          mul_le_mul ih h2 h3 (by have := i0Term_pos 6; positivity)
      _ = i0Term 6 * ((4 / 49) ^ n * (4 / 49)) := by ring

/-- upper bound for `I₀(4)`: partial sum through `n = 5` plus the geometric tail bound -/
theorem i0_four_le :
    besselI 0 4 ≤ (∑ j ∈ Finset.range 6, i0Term j) + i0Term 6 * (49 / 45) := by
  have h : HasSum i0Term (besselI 0 4) := by
    have := hasSum_besselI_zero 4
    convert this using 2 with j
    unfold i0Term
    norm_num
  have h6 := (hasSum_nat_add_iff' 6).mpr h
  have hg : HasSum (fun j : ℕ => i0Term 6 * (4 / 49 : ℝ) ^ j) (i0Term 6 * (1 - 4 / 49)⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have := hasSum_le i0Term_tail h6 hg
  have e : (1 - (4 : ℝ) / 49)⁻¹ = 49 / 45 := by norm_num
  rw [e] at this
  linarith

theorem i0_four_le_rat : besselI 0 4 ≤ 1029889 / 91125 := by
  refine i0_four_le.trans (le_of_eq ?_)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, i0Term, Nat.factorial]
  norm_num

/-- lower bound for `I₁(4)`: the positive series through `n = 6` -/
theorem i1_four_ge : (6586 / 675 : ℝ) < besselI 1 4 := by
  have h := hasSum_besselI1Over 4
  have hnn : ∀ j ∉ Finset.range 7, 0 ≤ (1 / 2 : ℝ) * ((4 : ℝ) ^ 2 / 4) ^ j /
      ((j.factorial : ℝ) * ((j + 1).factorial : ℝ)) := fun j _ => by positivity
  have hle := sum_le_hasSum (Finset.range 7) hnn h
  have e : besselI1Over 4 = besselI 1 4 / 4 := besselI1Over_of_ne 4 (by norm_num)
  rw [e] at hle
  have hs : (∑ j ∈ Finset.range 7, (1 / 2 : ℝ) * ((4 : ℝ) ^ 2 / 4) ^ j /
      ((j.factorial : ℝ) * ((j + 1).factorial : ℝ))) = 6586 / 2700 + 4 ^ 6 / 2 / (720 * 5040) := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
    norm_num
  rw [hs] at hle
  norm_num at hle ⊢
  linarith

/-- the rational certificate `b > 889110/1029889` -/
theorem quarticB_gt : (889110 / 1029889 : ℝ) < DGPS.Models.quarticB := by
  unfold DGPS.Models.quarticB besselRatio
  rw [lt_div_iff₀ (besselI_zero_pos 4)]
  have h0 := i0_four_le_rat
  have h1 := i1_four_ge
  nlinarith

/-- Riccati identity `g' = 1 - g/r - g²` at `r = 4` -/
theorem deriv_besselRatio_four :
    deriv besselRatio 4 = 1 - DGPS.Models.quarticB / 4 - DGPS.Models.quarticB ^ 2 := by
  rw [deriv_ratio]
  unfold ratioDeriv DGPS.Models.quarticB
  have e : besselI1Over 4 = besselI 1 4 / 4 := besselI1Over_of_ne 4 (by norm_num)
  rw [e]
  unfold besselRatio
  have := (besselI_zero_pos 4).ne'
  field_simp

end DGPS.FiniteN.QuarticSaddle

namespace DGPS.FiniteN

open DGPS.Models

/-- **FIN065.** Quartic explicit model rational certificate.

With `b = g(4)`, `κ = 5/b`, `η = 4/5` (`g = I₁/I₀`), the model `anisotropicQuarticSaddle` has
`V = -c - (κ/2)(c² + η s²)` and `W = (κ/2)[(c x - c y)² + η (s x - s y)²]` with `c = cos 2π·`,
`s = sin 2π·` (also on lifts of real coordinates).  The rational certificate
`b > 889110/1029889 > 55/64 > 6/7` holds, and, with `v = g'(4)`, the Riccati identity gives
`v = 1 - b/4 - b²`; `A = 1/κ - v = b/5 - v > 0`, `d = b - 4v > 0` and
`1 - κ v = 9/4 + 5b - 5/b > 1/2`. -/
theorem quartic_explicit_model_rational_certificate :
    (quarticB = besselRatio 4 ∧ quarticKappa = 5 / quarticB ∧ quarticEta = 4 / 5) ∧
    (∀ x, anisotropicQuarticSaddle.V x =
      -scalarCos x - quarticKappa / 2 * (scalarCos x ^ 2 + quarticEta * scalarSin x ^ 2)) ∧
    (∀ x y, anisotropicQuarticSaddle.W x y = quarticKappa / 2 *
      ((scalarCos x - scalarCos y) ^ 2 + quarticEta * (scalarSin x - scalarSin y) ^ 2)) ∧
    (∀ a : Fin 1 → ℝ, scalarCos (DGPS.torusLift a) = Real.cos (2 * Real.pi * a 0) ∧
      scalarSin (DGPS.torusLift a) = Real.sin (2 * Real.pi * a 0)) ∧
    ((889110 / 1029889 : ℝ) < quarticB ∧ (55 / 64 : ℝ) < 889110 / 1029889 ∧
      (6 / 7 : ℝ) < 55 / 64) ∧
    0 < quarticKappa ∧
    deriv besselRatio 4 = 1 - quarticB / 4 - quarticB ^ 2 ∧
    (0 < 1 / quarticKappa - deriv besselRatio 4 ∧
      1 / quarticKappa - deriv besselRatio 4 = quarticB / 5 - deriv besselRatio 4 ∧
      0 < quarticB / 5 - deriv besselRatio 4) ∧
    0 < quarticB - 4 * deriv besselRatio 4 ∧
    (1 - quarticKappa * deriv besselRatio 4 = 9 / 4 + 5 * quarticB - 5 / quarticB ∧
      1 / 2 < 1 - quarticKappa * deriv besselRatio 4) := by
  have hb := QuarticSaddle.quarticB_gt
  have hb67 : (6 / 7 : ℝ) < quarticB := by
    refine lt_trans ?_ hb
    norm_num
  have hbpos : 0 < quarticB := by linarith
  have hv := QuarticSaddle.deriv_besselRatio_four
  have hκ : quarticKappa = 5 / quarticB := rfl
  have hA : quarticB / 5 - deriv besselRatio 4 = quarticB ^ 2 + quarticB * (9 / 20) - 1 := by
    rw [hv]; ring
  have hk : 1 - quarticKappa * deriv besselRatio 4 = 9 / 4 + 5 * quarticB - 5 / quarticB := by
    rw [hκ, hv]; field_simp; ring
  have h1κ : 1 / quarticKappa = quarticB / 5 := by
    rw [hκ]; field_simp
  refine ⟨⟨rfl, rfl, rfl⟩, fun _ => rfl, fun _ _ => rfl,
    fun a => ⟨scalarCos_lift a, scalarSin_lift a⟩,
    ⟨hb, by norm_num, by norm_num⟩, by rw [hκ]; positivity, hv,
    ⟨?_, by rw [h1κ], ?_⟩, ?_, hk, ?_⟩
  · rw [h1κ, hA]; nlinarith
  · rw [hA]; nlinarith
  · rw [hv]; nlinarith
  · rw [hk]
    have : 5 / quarticB < 35 / 6 := by
      rw [div_lt_iff₀ hbpos]; nlinarith
    nlinarith

end DGPS.FiniteN
