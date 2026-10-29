import Mathlib

/-!
# Lemma 9.6, part B: a uniform positive lower bound for periodic solutions of the Euler ODE

Lane C of the Section 9 formalization.  Pure real analysis (no torus, no Sobolev theory).

If `F > 0` is `C²`, 1-periodic, `∫₀¹ F² = 1`, and `F'' = F (B - r log F)` with `B ≤ R/2`, `0 ≤ r ≤ 1`, then
`F ≥ exp(-(1+R))` (`min_lower_bound`).  Mechanism: at a minimum point `x₁` of `F`, `m = F(x₁)`,
`F'(x₁) = 0` and `F'' ≤ a² F` with `a² = R/2 + r log(1/m)`, hence (Grönwall) `F(x) ≤ m e^{a|x-x₁|}`
and `1 = ∫F² ≤ m² e^a`, which forces `log(1/m) ≤ a/2` and then `log(1/m) ≤ 1 + R`.
-/

open Set Filter Topology MeasureTheory

namespace SharpLSI.FL.Ex.SR

/-- One-sided Grönwall: if `F ≥ 0`, `F'' ≤ a² F` and `F'(x₀) = 0` then `F(x₀+s) ≤ F(x₀) e^{as}`
for `s ≥ 0`. -/
theorem grow_bound {F F1 F2 : ℝ → ℝ} {a x0 : ℝ} (ha : 0 ≤ a)
    (hd1 : ∀ x, HasDerivAt F (F1 x) x) (hd2 : ∀ x, HasDerivAt F1 (F2 x) x)
    (hnn : ∀ x, 0 ≤ F x) (hF2 : ∀ x, F2 x ≤ a ^ 2 * F x) (hF1 : F1 x0 = 0) :
    ∀ s, 0 ≤ s → F (x0 + s) ≤ F x0 * Real.exp (a * s) := by
  -- `y = F' + a F` satisfies `y' ≤ a y`, so `y e^{-as}` is antitone
  have hY : ∀ s, HasDerivAt (fun s => (F1 (x0 + s) + a * F (x0 + s)) * Real.exp (-a * s))
      (Real.exp (-a * s) * ((F2 (x0 + s) + a * F1 (x0 + s)) -
        a * (F1 (x0 + s) + a * F (x0 + s)))) s := by
    intro s
    have h1 : HasDerivAt (fun s => F1 (x0 + s) + a * F (x0 + s))
        (F2 (x0 + s) + a * F1 (x0 + s)) s :=
      (((hd2 (x0 + s))).add (((hd1 (x0 + s))).const_mul a)).comp_const_add x0 s
    have h2 : HasDerivAt (fun s => Real.exp (-a * s)) (Real.exp (-a * s) * (-a * 1)) s :=
      ((hasDerivAt_id' s).const_mul (-a)).exp
    refine (h1.mul h2).congr_deriv ?_
    ring
  have hYanti : Antitone (fun s => (F1 (x0 + s) + a * F (x0 + s)) * Real.exp (-a * s)) := by
    refine antitone_of_deriv_nonpos (fun s => (hY s).differentiableAt) fun s => ?_
    rw [(hY s).deriv]
    refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
    have := hF2 (x0 + s)
    nlinarith [this]
  have hyle : ∀ s, 0 ≤ s → F1 (x0 + s) + a * F (x0 + s) ≤ a * F x0 * Real.exp (a * s) := by
    intro s hs
    have h := hYanti hs
    beta_reduce at h
    have h0 : (F1 (x0 + 0) + a * F (x0 + 0)) * Real.exp (-a * 0) = a * F x0 := by
      simp [hF1]
    rw [h0] at h
    have e : Real.exp (-a * s) * Real.exp (a * s) = 1 := by
      rw [← Real.exp_add]; simp
    have := mul_le_mul_of_nonneg_right h (Real.exp_pos (a * s)).le
    calc F1 (x0 + s) + a * F (x0 + s)
        = (F1 (x0 + s) + a * F (x0 + s)) * Real.exp (-a * s) * Real.exp (a * s) := by
          rw [mul_assoc, e, mul_one]
      _ ≤ a * F x0 * Real.exp (a * s) := this
  have hF1le : ∀ s, 0 ≤ s → F1 (x0 + s) ≤ a * F x0 * Real.exp (a * s) := by
    intro s hs
    have := hyle s hs
    have := mul_nonneg ha (hnn (x0 + s))
    linarith [hyle s hs]
  -- `N(s) = F(x₀+s) - F(x₀) e^{as}` is antitone on `s ≥ 0`
  have hN : ∀ s, HasDerivAt (fun s => F (x0 + s) - F x0 * Real.exp (a * s))
      (F1 (x0 + s) - F x0 * (Real.exp (a * s) * (a * 1))) s := by
    intro s
    have h1 : HasDerivAt (fun s => F (x0 + s)) (F1 (x0 + s)) s := (hd1 (x0 + s)).comp_const_add x0 s
    have h2 : HasDerivAt (fun s => Real.exp (a * s)) (Real.exp (a * s) * (a * 1)) s :=
      ((hasDerivAt_id' s).const_mul a).exp
    exact h1.sub (h2.const_mul _)
  have hNanti : AntitoneOn (fun s => F (x0 + s) - F x0 * Real.exp (a * s)) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) (fun s _ => (hN s).continuousAt.continuousWithinAt)
      (fun s _ => (hN s).differentiableAt.differentiableWithinAt) fun s hs => ?_
    rw [interior_Ici] at hs
    rw [(hN s).deriv]
    have := hF1le s (le_of_lt hs)
    nlinarith [this]
  intro s hs
  have := hNanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs) hs
  simp only [add_zero, mul_zero, Real.exp_zero, mul_one, sub_self] at this
  linarith

/-- Two-sided Grönwall bound around a critical point (reflection). -/
theorem grow_bound_two {F F1 F2 : ℝ → ℝ} {a x0 : ℝ} (ha : 0 ≤ a)
    (hd1 : ∀ x, HasDerivAt F (F1 x) x) (hd2 : ∀ x, HasDerivAt F1 (F2 x) x)
    (hnn : ∀ x, 0 ≤ F x) (hF2 : ∀ x, F2 x ≤ a ^ 2 * F x) (hF1 : F1 x0 = 0) :
    ∀ x, F x ≤ F x0 * Real.exp (a * |x - x0|) := by
  intro x
  rcases le_total x0 x with h | h
  · have := grow_bound ha hd1 hd2 hnn hF2 hF1 (x - x0) (by linarith)
    rw [abs_of_nonneg (by linarith)]
    simpa using this
  · -- reflect: `G y = F (x0 - y)`
    have hG1 : ∀ y, HasDerivAt (fun y => F (x0 - y)) (-F1 (x0 - y)) y := by
      intro y
      exact (hd1 (x0 - y)).comp_const_sub x0 y
    have hG2 : ∀ y, HasDerivAt (fun y => -F1 (x0 - y)) (F2 (x0 - y)) y := by
      intro y
      exact (((hd2 (x0 - y)).comp_const_sub x0 y).neg).congr_deriv (by ring)
    have := grow_bound (F := fun y => F (x0 - y)) (F1 := fun y => -F1 (x0 - y))
      (F2 := fun y => F2 (x0 - y)) (a := a) (x0 := 0) ha hG1 hG2 (fun y => hnn _)
      (fun y => hF2 _) (by simp [hF1]) (x0 - x) (by linarith)
    rw [abs_of_nonpos (by linarith)]
    simp only [zero_add, sub_sub_cancel, sub_zero] at this
    have e : -(x - x0) = x0 - x := by ring
    rw [e]
    exact this

/-- **Uniform lower bound.** -/
theorem min_lower_bound {R r : ℝ} (hR : 0 ≤ R) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {F F1 F2 B : ℝ → ℝ} (hd1 : ∀ x, HasDerivAt F (F1 x) x) (hd2 : ∀ x, HasDerivAt F1 (F2 x) x)
    (hpos : ∀ x, 0 < F x) (hper : Function.Periodic F 1)
    (hode : ∀ x, F2 x = F x * (B x - r * Real.log (F x))) (hB : ∀ x, B x ≤ R / 2)
    (hmass : ∫ x in (0 : ℝ)..1, F x ^ 2 = 1) :
    ∀ x, Real.exp (-(1 + R)) ≤ F x := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => (hd1 x).continuousAt
  -- global minimum
  obtain ⟨x1, -, hx1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn
    (nonempty_Icc.2 zero_le_one) hFc.continuousOn
  have hmin : ∀ x, F x1 ≤ F x := by
    intro x
    obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico₀ one_pos x
    rw [hxy]
    exact hx1 ⟨hy.1, hy.2.le⟩
  have hF1x1 : F1 x1 = 0 := by
    have hlm : IsLocalMin F x1 := Filter.Eventually.of_forall hmin
    exact hlm.hasDerivAt_eq_zero (hd1 x1)
  set m := F x1 with hm
  have hm0 : 0 < m := hpos x1
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := hcon
  have hmlt : m < Real.exp (-(1 + R)) := lt_of_le_of_lt (hmin x) hx
  set ℓ : ℝ := -Real.log m with hℓ
  have hmexp : m = Real.exp (-ℓ) := by
    rw [hℓ, neg_neg, Real.exp_log hm0]
  have hℓgt : 1 + R < ℓ := by
    have := Real.log_lt_log hm0 hmlt
    rw [Real.log_exp] at this
    linarith
  have hℓ0 : 0 < ℓ := by linarith
  set a : ℝ := Real.sqrt (R / 2 + r * ℓ) with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = R / 2 + r * ℓ := Real.sq_sqrt (by positivity)
  have hF2 : ∀ y, F2 y ≤ a ^ 2 * F y := by
    intro y
    rw [hode y, ha2]
    have hlog : -ℓ ≤ Real.log (F y) := by
      have e : -ℓ = Real.log m := by rw [hℓ]; ring
      rw [e]
      exact Real.log_le_log hm0 (hmin y)
    have : B y - r * Real.log (F y) ≤ R / 2 + r * ℓ := by
      nlinarith [hB y, mul_le_mul_of_nonneg_left hlog hr0]
    nlinarith [hpos y, mul_le_mul_of_nonneg_left this (hpos y).le]
  have hbound := grow_bound_two ha0 hd1 hd2 (fun y => (hpos y).le) hF2 hF1x1
  -- mass estimate
  have hper2 : Function.Periodic (fun x => F x ^ 2) 1 := fun y => by simp [hper y]
  have hint : ∫ y in (0 : ℝ)..1, F y ^ 2 ≤ m ^ 2 * Real.exp a := by
    have hshift := hper2.intervalIntegral_add_eq (x1 - 1 / 2) 0
    have hshift' : ∫ y in (0 : ℝ)..1, F y ^ 2 = ∫ y in (x1 - 1 / 2)..(x1 - 1 / 2 + 1), F y ^ 2 := by
      simpa using hshift.symm
    rw [hshift']
    have hFi : IntervalIntegrable (fun y => F y ^ 2) volume (x1 - 1 / 2) (x1 - 1 / 2 + 1) :=
      (hFc.pow 2).intervalIntegrable _ _
    calc ∫ y in (x1 - 1 / 2)..(x1 - 1 / 2 + 1), F y ^ 2
        ≤ ∫ y in (x1 - 1 / 2)..(x1 - 1 / 2 + 1), m ^ 2 * Real.exp a := by
          refine intervalIntegral.integral_mono_on (by linarith) hFi
            intervalIntegrable_const fun y hy => ?_
          have hy1 : |y - x1| ≤ 1 / 2 := by
            rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
          have h1 := hbound y
          have h2 : Real.exp (a * |y - x1|) ≤ Real.exp (a * (1 / 2)) :=
            Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hy1 ha0)
          have h3 : F y ≤ m * Real.exp (a * (1 / 2)) :=
            h1.trans (mul_le_mul_of_nonneg_left h2 hm0.le)
          have h4 : F y ^ 2 ≤ (m * Real.exp (a * (1 / 2))) ^ 2 :=
            pow_le_pow_left₀ (hpos y).le h3 2
          refine h4.trans (le_of_eq ?_)
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 2
          push_cast; ring
      _ = m ^ 2 * Real.exp a := by simp
  rw [hmass] at hint
  -- `1 ≤ m² e^a = e^{a - 2ℓ}` forces `a ≥ 2ℓ`
  have hexp : 1 ≤ Real.exp (a - 2 * ℓ) := by
    have : m ^ 2 * Real.exp a = Real.exp (a - 2 * ℓ) := by
      rw [hmexp, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1; push_cast; ring
    rwa [this] at hint
  have h2ℓ : 2 * ℓ ≤ a := by
    have := Real.exp_le_exp.1 (by simpa using hexp : Real.exp 0 ≤ Real.exp (a - 2 * ℓ))
    linarith
  have : (2 * ℓ) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by linarith) h2ℓ 2
  rw [ha2] at this
  nlinarith [mul_le_mul_of_nonneg_right hr1 hℓ0.le]

end SharpLSI.FL.Ex.SR
