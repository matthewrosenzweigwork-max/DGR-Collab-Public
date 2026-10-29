import DGPS.Frontier.STR029.T15

/-!
# STR029.70: Explicit order-two forcing of the weighted variational gradient

Task id: STR029.70 (node STR029), "Explicit order-two forcing of the weighted variational
gradient".

Statement formalized.  For `p = A cos t + B sin t`, `q ∈ E`, and bounded `(A, B, s, q)`, the
coefficient of `h²` in `P G(h, h² s, h p + h² q)` is
`-2 (q'' + q) + (-3A + (A² - B²)/2) cos 2t + (3B + A B) sin 2t + 3A cos 4t + 3B sin 4t`,
and the remainder is `O_{C^{0,α}}(|h|³)` uniformly on bounded parameter sets lying in a fixed
sufficiently small scaled neighbourhood.

Provides (every declaration is in the namespace `DGPS.Frontier.STR029`):

* `DGPS.Frontier.STR029.str029_70_explicit_order_two_forcing_weighted_variational`: main
  statement.  There is a map `F : ℝ → ℝ → E → Y` with the explicit pointwise formula above such
  that, for a fixed radius `r > 0` and every bound `M`, there is a constant `C ≥ 0` with
  `‖Rvar (hA, hB, h, h² s, h² q) - h² • F A B q‖ ≤ C |h|³` whenever `|A|, |B|, |s|, ‖q‖ ≤ M`
  and the scaled chart point has norm at most `r`.
* `DGPS.Frontier.STR029.str029_70_explicit_order_two_forcing_weighted_variational_chart`: the
  quantitative estimate with the concrete forcing element `forcingY_STR02970 A B q`, with a
  radius `r` independent of `M`.
* `DGPS.Frontier.STR029.str029_70_explicit_order_two_forcing_weighted_variational_forcing_val`:
  the pointwise formula for the forcing, as a value of the Hölder function.
* `DGPS.Frontier.STR029.str029_70_explicit_order_two_forcing_weighted_variational_chart_eq`:
  the variational range map at the scaled chart point is, by definition,
  `P G (h, h² s, h p + h² q)`.
* `DGPS.Frontier.STR029.str029_70_explicit_order_two_forcing_weighted_variational_small`: the
  same estimate with a radius depending on `M` and with the plain condition `|h| ≤ r`.

R5 notes:

* Carriers.  `G` is `Gfun_STR02955`, `P` is `PCLM_STR02955`, and `P G` at the chart point is the
  variational range map `Rvar_STR02915` (the Euler range map is not used or assumed).  The
  identification is definitional and is recorded as the `_chart_eq` lemma.  The Hölder exponent
  is the fixed `α = 1/2` of the concrete carriers `PeriodicHolder_STR02968`,
  `PeriodicC2_STR02969`, `E_STR02969`, `Y_STR02969`.
* Parameters.  The point `(h, h² s, h p + h² q)` is the chart point
  `paramMap_STR02915 (h A, h B, h, h² s, h² q)`, where `p = A cos + B sin` is carried by the
  coordinates `(h A, h B)` and `q` by `h² • q ∈ E`.  The statement is on exactly these scaled
  chart variables; the only hypotheses are the bounds on `(A, B, s, q)` and the neighbourhood
  condition described next.
* Neighbourhood.  "Fixed sufficiently small scaled neighbourhood" is read as the closed ball
  `‖(hA, hB, h, h² s, h² q)‖ ≤ r` in the sup norm of `ℝ × ℝ × ℝ × ℝ × E`, with `r > 0`
  independent of the bound `M`.  The `_small` corollary gives the same estimate with an
  `M`-dependent radius and the plain condition `|h| ≤ r`.
* Bounded parameter sets.  Boundedness is `|A|, |B|, |s|, ‖q‖ ≤ M` with `M` an arbitrary real;
  the constant `C` depends on `M` only.  For `M < 0` the hypotheses are vacuous.
* Remainder.  "`O_{C^{0,α}}(|h|³)`" is read as the explicit norm bound
  `‖remainder‖_{C^{0,1/2}} ≤ C |h|³`, and "the coefficient of `h²`" as
  `‖P G(...) - h² • F‖ ≤ C |h|³`.  In the main statement `F` is existentially quantified, but it
  is pinned down by the pointwise formula, and it equals `forcingY_STR02970`.
* Method.  The proof does not use Fréchet second derivatives.  It uses the exact algebraic
  decomposition of the chart point in the commutative Hölder algebra: the gradient equals
  `ρ • (h² • B2 + h³ • R3 - κ • 1)` with explicit brackets `B2, R3` and a scalar `κ`, and
  `P B2 = forcing`.  The factor `ρ` is controlled through a Lipschitz estimate of the smooth
  density weight near `0`, and `κ = O(h²)` is read off from the mean-zero structure.
* Conventions.  None of the inherited entropy, Fisher, deficit, or rate-normalization
  conventions is touched; the unit only reuses `Gfun_STR02955`, `PCLM_STR02955`, `rho_STR02954`
  and `Rvar_STR02915` as they stand.
* Helpers.  Every helper carries the suffix `_STR02970`; they are all in the single namespace
  `DGPS.Frontier.STR029`.
-/

open scoped ContDiff
open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.STR029

theorem meanT_cos_nat_STR02970 (n : ℕ) (hn : 1 ≤ n) :
    meanT_STR02901 (fun t => Real.cos (n * t)) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  refine ftc_mean_STR02955 (F := fun t => Real.sin (n * t) / n) (fun x => ?_) (by fun_prop) ?_
  · have h1 : HasDerivAt (fun y : ℝ => (n : ℝ) * y) n x := by
      simpa using (hasDerivAt_id x).const_mul (n : ℝ)
    refine (h1.sin.div_const (n : ℝ)).congr_deriv ?_
    field_simp
  · simp only [mul_zero, Real.sin_zero, zero_div]
    have : (n : ℝ) * (2 * Real.pi) = ((2 * n : ℕ) : ℝ) * Real.pi := by push_cast; ring
    rw [this, Real.sin_nat_mul_pi, zero_div]

theorem meanT_sin_nat_STR02970 (n : ℕ) (hn : 1 ≤ n) :
    meanT_STR02901 (fun t => Real.sin (n * t)) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  refine ftc_mean_STR02955 (F := fun t => -Real.cos (n * t) / n) (fun x => ?_) (by fun_prop) ?_
  · have h1 : HasDerivAt (fun y : ℝ => (n : ℝ) * y) n x := by
      simpa using (hasDerivAt_id x).const_mul (n : ℝ)
    refine (h1.cos.neg.div_const (n : ℝ)).congr_deriv ?_
    field_simp
  · simp only [mul_zero, Real.cos_zero]
    rw [Real.cos_nat_mul_two_pi]

theorem meanT_add'_STR02970 {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    meanT_STR02901 (fun t => f t + g t) = meanT_STR02901 f + meanT_STR02901 g :=
  meanT_add_STR02953 hf hg

theorem meanT_mul'_STR02970 (c : ℝ) (f : ℝ → ℝ) :
    meanT_STR02901 (fun t => c * f t) = c * meanT_STR02901 f :=
  meanT_smul_STR02953 c f

theorem meanT_comb4_STR02970 {n1 n2 n3 n4 : ℕ} (h1 : 1 ≤ n1) (h2 : 1 ≤ n2) (h3 : 1 ≤ n3)
    (h4 : 1 ≤ n4) (c1 c2 c3 c4 : ℝ) :
    meanT_STR02901 (fun t => c1 * Real.cos (n1 * t) + c2 * Real.sin (n2 * t) +
      c3 * Real.cos (n3 * t) + c4 * Real.sin (n4 * t)) = 0 := by
  rw [meanT_add'_STR02970 (by fun_prop) (by fun_prop), meanT_add'_STR02970 (by fun_prop) (by fun_prop),
    meanT_add'_STR02970 (by fun_prop) (by fun_prop), meanT_mul'_STR02970, meanT_mul'_STR02970,
    meanT_mul'_STR02970, meanT_mul'_STR02970, meanT_cos_nat_STR02970 n1 h1,
    meanT_sin_nat_STR02970 n2 h2, meanT_cos_nat_STR02970 n3 h3, meanT_sin_nat_STR02970 n4 h4]
  ring

theorem inE_add_STR02970 {f g : ℝ → ℝ} (hf : InE_STR02901 f) (hg : InE_STR02901 g)
    (cf : Continuous f) (cg : Continuous g) : InE_STR02901 (fun t => f t + g t) := by
  have hc := Real.continuous_cos
  have hs := Real.continuous_sin
  refine ⟨?_, ?_, ?_⟩
  · rw [meanT_add'_STR02970 cf cg, hf.1, hg.1, add_zero]
  · have : (fun t => (f t + g t) * Real.cos t) = fun t => f t * Real.cos t + g t * Real.cos t := by
      funext t; ring
    rw [this, meanT_add'_STR02970 (f := fun t => f t * Real.cos t) (g := fun t => g t * Real.cos t)
      (cf.mul hc) (cg.mul hc), hf.2.1, hg.2.1, add_zero]
  · have : (fun t => (f t + g t) * Real.sin t) = fun t => f t * Real.sin t + g t * Real.sin t := by
      funext t; ring
    rw [this, meanT_add'_STR02970 (f := fun t => f t * Real.sin t) (g := fun t => g t * Real.sin t)
      (cf.mul hs) (cg.mul hs), hf.2.2, hg.2.2, add_zero]

/-- The harmonic of order `j + 1`. -/
noncomputable def harm_STR02970 (j : ℕ) (a b : ℝ) (t : ℝ) : ℝ :=
  a * Real.cos (((j + 1 : ℕ) : ℝ) * t) + b * Real.sin (((j + 1 : ℕ) : ℝ) * t)

theorem harm_cont_STR02970 (j : ℕ) (a b : ℝ) : Continuous (harm_STR02970 j a b) := by
  unfold harm_STR02970
  fun_prop

theorem harm_inE_STR02970 (j : ℕ) (hj : 1 ≤ j) (a b : ℝ) : InE_STR02901 (harm_STR02970 j a b) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold harm_STR02970
    rw [meanT_add'_STR02970 (f := fun t => a * Real.cos (((j + 1 : ℕ) : ℝ) * t))
      (g := fun t => b * Real.sin (((j + 1 : ℕ) : ℝ) * t)) (by fun_prop) (by fun_prop),
      meanT_mul'_STR02970, meanT_mul'_STR02970, meanT_cos_nat_STR02970 (j + 1) (by omega),
      meanT_sin_nat_STR02970 (j + 1) (by omega)]
    ring
  · have e : (fun t => harm_STR02970 j a b t * Real.cos t) = fun t =>
        a / 2 * Real.cos (((j + 2 : ℕ) : ℝ) * t) + b / 2 * Real.sin (((j + 2 : ℕ) : ℝ) * t) +
        a / 2 * Real.cos ((j : ℕ) * t) + b / 2 * Real.sin ((j : ℕ) * t) := by
      funext t
      have e1 : ((j + 2 : ℕ) : ℝ) * t = ((j + 1 : ℕ) : ℝ) * t + t := by push_cast; ring
      have e2 : ((j : ℕ) : ℝ) * t = ((j + 1 : ℕ) : ℝ) * t - t := by push_cast; ring
      rw [e1, e2, Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]
      unfold harm_STR02970
      ring
    rw [e]
    exact meanT_comb4_STR02970 (by omega) (by omega) hj hj _ _ _ _
  · have e : (fun t => harm_STR02970 j a b t * Real.sin t) = fun t =>
        (-(b / 2)) * Real.cos (((j + 2 : ℕ) : ℝ) * t) + a / 2 * Real.sin (((j + 2 : ℕ) : ℝ) * t) +
        b / 2 * Real.cos ((j : ℕ) * t) + (-(a / 2)) * Real.sin ((j : ℕ) * t) := by
      funext t
      have e1 : ((j + 2 : ℕ) : ℝ) * t = ((j + 1 : ℕ) : ℝ) * t + t := by push_cast; ring
      have e2 : ((j : ℕ) : ℝ) * t = ((j + 1 : ℕ) : ℝ) * t - t := by push_cast; ring
      rw [e1, e2, Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]
      unfold harm_STR02970
      ring
    rw [e]
    exact meanT_comb4_STR02970 (by omega) (by omega) hj hj _ _ _ _

theorem trig_forcing_STR02970 (A B t : ℝ) :
    6 * Real.sin (3 * t) * (-A * Real.sin t + B * Real.cos t) -
        (-A * Real.sin t + B * Real.cos t) ^ 2 + (A ^ 2 + B ^ 2) / 2 =
      harm_STR02970 1 (-3 * A + (A ^ 2 - B ^ 2) / 2) (3 * B + A * B) t +
        harm_STR02970 3 (3 * A) (3 * B) t := by
  have h3 : Real.sin (3 * t) =
      2 * (Real.sin t * Real.cos t) * Real.cos t + (2 * Real.cos t ^ 2 - 1) * Real.sin t := by
    rw [show 3 * t = 2 * t + t by ring, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul]
    ring
  have h2c : Real.cos (2 * t) = 2 * Real.cos t ^ 2 - 1 := Real.cos_two_mul t
  have h2s : Real.sin (2 * t) = 2 * Real.sin t * Real.cos t := Real.sin_two_mul t
  have h4c : Real.cos (4 * t) = 2 * (2 * Real.cos t ^ 2 - 1) ^ 2 - 1 := by
    rw [show 4 * t = 2 * (2 * t) by ring, Real.cos_two_mul, h2c]
  have h4s : Real.sin (4 * t) =
      2 * (2 * Real.sin t * Real.cos t) * (2 * Real.cos t ^ 2 - 1) := by
    rw [show 4 * t = 2 * (2 * t) by ring, Real.sin_two_mul, h2c, h2s]
  have k2 : ((1 + 1 : ℕ) : ℝ) = 2 := by norm_num
  have k4 : ((3 + 1 : ℕ) : ℝ) = 4 := by norm_num
  unfold harm_STR02970
  rw [k2, k4, h3, h2c, h2s, h4c, h4s]
  linear_combination (-24 * Real.cos t ^ 2 * A + 6 * A - A ^ 2) * Real.sin_sq_add_cos_sq t


theorem harm_isPerHolder_STR02970 (j : ℕ) (a b : ℝ) :
    IsPerHolder_STR02968 (1 / 2) (harm_STR02970 j a b) := by
  have key : ∀ n : ℕ, IsPerHolder_STR02968 (1 / 2)
      (fun t => a * Real.cos ((n : ℝ) * t) + b * Real.sin ((n : ℝ) * t)) := by
    intro n
    have hper : Function.Periodic (fun t => a * Real.cos ((n : ℝ) * t) + b * Real.sin ((n : ℝ) * t))
        (2 * Real.pi) := fun t => by
      have e1 : (n : ℝ) * (t + 2 * Real.pi) = n * t + n * (2 * Real.pi) := by ring
      simp only [e1, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]
    have hd : Differentiable ℝ (fun t => a * Real.cos ((n : ℝ) * t) + b * Real.sin ((n : ℝ) * t)) := by
      fun_prop
    have hder : ∀ x, deriv (fun t => a * Real.cos ((n : ℝ) * t) + b * Real.sin ((n : ℝ) * t)) x =
        -(a * n) * Real.sin (n * x) + (b * n) * Real.cos (n * x) := by
      intro x
      have h1 : HasDerivAt (fun y : ℝ => (n : ℝ) * y) n x := by
        simpa using (hasDerivAt_id x).const_mul (n : ℝ)
      have h2 : HasDerivAt (fun t => a * Real.cos ((n : ℝ) * t) + b * Real.sin ((n : ℝ) * t))
          (a * (-Real.sin (↑n * x) * ↑n) + b * (Real.cos (↑n * x) * ↑n)) x :=
        (h1.cos.const_mul a).add (h1.sin.const_mul b)
      rw [h2.deriv]
      ring
    have hb : Bdd (deriv (fun t => a * Real.cos ((n : ℝ) * t) + b * Real.sin ((n : ℝ) * t))) :=
      ⟨|a| * n + |b| * n, fun x => by
        rw [hder x]
        have hs := Real.abs_sin_le_one ((n : ℝ) * x)
        have hc := Real.abs_cos_le_one ((n : ℝ) * x)
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        calc |-(a * n) * Real.sin (n * x) + (b * n) * Real.cos (n * x)|
            ≤ |-(a * n) * Real.sin (n * x)| + |(b * n) * Real.cos (n * x)| := abs_add_le _ _
          _ = |a| * n * |Real.sin (n * x)| + |b| * n * |Real.cos (n * x)| := by
              simp only [abs_mul, abs_neg, abs_of_nonneg hn0]
          _ ≤ |a| * n * 1 + |b| * n * 1 := by gcongr
          _ = |a| * n + |b| * n := by ring⟩
    exact mkHolder_STR02955
      (c0_of_deriv_STR02953 (α := 1 / 2) half_pos_STR02968 (by norm_num) hper hd hb).1
  exact key (j + 1)

/-- The harmonic `a cos (n t) + b sin (n t)`, `n = j + 1`, as an element of `C^{0,1/2}`. -/
noncomputable def harmH_STR02970 (j : ℕ) (a b : ℝ) : PeriodicHolder_STR02968 :=
  PeriodicHolder_STR02968.mk (harm_STR02970 j a b) (harm_isPerHolder_STR02970 j a b)

theorem harmH_val_STR02970 (j : ℕ) (a b : ℝ) :
    (harmH_STR02970 j a b).val = harm_STR02970 j a b := rfl

/-- The Hölder-algebra element `cos`. -/
noncomputable def cH_STR02970 : PeriodicHolder_STR02968 := e0_STR02955 cosC2_STR02915

/-- The Hölder-algebra element `sin`. -/
noncomputable def sH_STR02970 : PeriodicHolder_STR02968 := e0_STR02955 sinC2_STR02915

theorem cH_val_STR02970 : cH_STR02970.val = Real.cos := rfl
theorem sH_val_STR02970 : sH_STR02970.val = Real.sin := rfl

theorem e1_cos_STR02970 : e1_STR02955 cosC2_STR02915 = (-1 : ℝ) • sH_STR02970 := by
  apply ext_STR02954
  funext t
  rw [e1_val_STR02955, PeriodicHolder_STR02968.val_smul]
  simp only [cosC2_val_STR02915, sH_val_STR02970, Pi.smul_apply, smul_eq_mul]
  rw [Real.deriv_cos']
  ring

theorem e1_sin_STR02970 : e1_STR02955 sinC2_STR02915 = cH_STR02970 := by
  apply ext_STR02954
  rw [e1_val_STR02955]
  simp only [sinC2_val_STR02915, cH_val_STR02970]
  exact Real.deriv_sin

theorem e2_cos_STR02970 : e2_STR02955 cosC2_STR02915 = (-1 : ℝ) • cH_STR02970 := by
  apply ext_STR02954
  funext t
  rw [e2_val_STR02955, PeriodicHolder_STR02968.val_smul]
  simp only [cosC2_val_STR02915, cH_val_STR02970, Pi.smul_apply, smul_eq_mul]
  rw [Real.deriv_cos']
  have h2 : HasDerivAt (fun x => -Real.sin x) (-Real.cos t) t := (Real.hasDerivAt_sin t).neg
  rw [h2.deriv]
  ring

theorem e2_sin_STR02970 : e2_STR02955 sinC2_STR02915 = (-1 : ℝ) • sH_STR02970 := by
  apply ext_STR02954
  funext t
  rw [e2_val_STR02955, PeriodicHolder_STR02968.val_smul]
  simp only [sinC2_val_STR02915, sH_val_STR02970, Pi.smul_apply, smul_eq_mul]
  rw [Real.deriv_sin]
  simp [Real.deriv_cos']


/-! ### The chart point and the algebraic expansion -/

/-- The harmonic part `A cos + B sin` of the chart point, as a Hölder-algebra element. -/
noncomputable def p0_STR02970 (A B : ℝ) : PeriodicHolder_STR02968 :=
  A • cH_STR02970 + B • sH_STR02970

/-- The derivative `-A sin + B cos` of `p0`, as a Hölder-algebra element. -/
noncomputable def p1_STR02970 (A B : ℝ) : PeriodicHolder_STR02968 :=
  B • cH_STR02970 - A • sH_STR02970

/-- The chart point `h A cos + h B sin + h² q` in `C^{2,1/2}`. -/
noncomputable def uch_STR02970 (h A B : ℝ) (q : E_STR02969) : PeriodicC2_STR02969 :=
  (h * A) • cosC2_STR02915 + (h * B) • sinC2_STR02915 +
    ((h ^ 2 • q : E_STR02969) : PeriodicC2_STR02969)

theorem e0_uch_STR02970 (h A B : ℝ) (q : E_STR02969) :
    e0_STR02955 (uch_STR02970 h A B q) =
      h • p0_STR02970 A B + h ^ 2 • e0_STR02955 (q : PeriodicC2_STR02969) := by
  unfold uch_STR02970
  rw [map_add, map_add, map_smul, map_smul, Submodule.coe_smul, map_smul]
  apply ext_STR02954
  funext t
  simp only [p0_STR02970, PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, cH_val_STR02970, sH_val_STR02970]
  have c : (e0_STR02955 cosC2_STR02915).val t = Real.cos t := rfl
  have d : (e0_STR02955 sinC2_STR02915).val t = Real.sin t := rfl
  rw [c, d]
  ring

theorem e1_uch_STR02970 (h A B : ℝ) (q : E_STR02969) :
    e1_STR02955 (uch_STR02970 h A B q) =
      h • p1_STR02970 A B + h ^ 2 • e1_STR02955 (q : PeriodicC2_STR02969) := by
  unfold uch_STR02970
  rw [map_add, map_add, map_smul, map_smul, Submodule.coe_smul, map_smul, e1_cos_STR02970,
    e1_sin_STR02970]
  apply ext_STR02954
  funext t
  simp only [p1_STR02970, PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_sub,
    PeriodicHolder_STR02968.val_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    cH_val_STR02970, sH_val_STR02970]
  ring

theorem e2_uch_STR02970 (h A B : ℝ) (q : E_STR02969) :
    e2_STR02955 (uch_STR02970 h A B q) =
      (-h) • p0_STR02970 A B + h ^ 2 • e2_STR02955 (q : PeriodicC2_STR02969) := by
  unfold uch_STR02970
  rw [map_add, map_add, map_smul, map_smul, Submodule.coe_smul, map_smul, e2_cos_STR02970,
    e2_sin_STR02970]
  apply ext_STR02954
  funext t
  simp only [p0_STR02970, PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, cH_val_STR02970, sH_val_STR02970]
  ring

/-- The order-two bracket `-2 (q'' + q) + 6 sin 3t p' - p'^2`. -/
noncomputable def B2_STR02970 (A B : ℝ) (q : E_STR02969) : PeriodicHolder_STR02968 :=
  (-2 : ℝ) • (e2_STR02955 (q : PeriodicC2_STR02969) + e0_STR02955 (q : PeriodicC2_STR02969)) +
    (6 : ℝ) • (s3_STR02955 * p1_STR02970 A B) - p1_STR02970 A B * p1_STR02970 A B

/-- The order-three bracket. -/
noncomputable def R3_STR02970 (h s A B : ℝ) (q : E_STR02969) : PeriodicHolder_STR02968 :=
  (6 : ℝ) • (s3_STR02955 * e1_STR02955 (q : PeriodicC2_STR02969)) -
    (2 : ℝ) • (p1_STR02970 A B * e1_STR02955 (q : PeriodicC2_STR02969)) -
    (2 * s) • p0_STR02970 A B +
    h • ((-2 * s) • e0_STR02955 (q : PeriodicC2_STR02969) -
      e1_STR02955 (q : PeriodicC2_STR02969) * e1_STR02955 (q : PeriodicC2_STR02969))

theorem bracket_chart_STR02970 (h s A B I E : ℝ) (q : E_STR02969) :
    (-2 : ℝ) • e2_STR02955 (uch_STR02970 h A B q) +
        (6 * h) • (s3_STR02955 * e1_STR02955 (uch_STR02970 h A B q)) -
        e1_STR02955 (uch_STR02970 h A B q) * e1_STR02955 (uch_STR02970 h A B q) -
        (2 * (1 + h ^ 2 * s)) • e0_STR02955 (uch_STR02970 h A B q) -
        I • (1 : PeriodicHolder_STR02968) +
        (2 * (1 + h ^ 2 * s) * E) • (1 : PeriodicHolder_STR02968) =
      h ^ 2 • B2_STR02970 A B q + h ^ 3 • R3_STR02970 h s A B q -
        (I - 2 * (1 + h ^ 2 * s) * E) • (1 : PeriodicHolder_STR02968) := by
  rw [e0_uch_STR02970, e1_uch_STR02970, e2_uch_STR02970]
  apply ext_STR02954
  funext t
  simp only [B2_STR02970, R3_STR02970, PeriodicHolder_STR02968.val_add,
    PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_smul, val_mul_STR02954,
    val_one_STR02954, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- The density weight at the chart point. -/
noncomputable def rhoCh_STR02970 (h A B : ℝ) (q : E_STR02969) : PeriodicHolder_STR02968 :=
  rho_STR02954 (h, e0_STR02955 (uch_STR02970 h A B q))

/-- The scalar `κ = I - 2 (1 + γ) E` at the chart point. -/
noncomputable def kappa_STR02970 (h s A B : ℝ) (q : E_STR02969) : ℝ :=
  meanCLM_STR02954 (e1_STR02955 (uch_STR02970 h A B q) * e1_STR02955 (uch_STR02970 h A B q) *
      rhoCh_STR02970 h A B q) -
    2 * (1 + h ^ 2 * s) *
      meanCLM_STR02954 (e0_STR02955 (uch_STR02970 h A B q) * rhoCh_STR02970 h A B q)

theorem Gmap_chart_STR02970 (h s A B : ℝ) (q : E_STR02969) :
    Gmap_STR02955 (paramMap_STR02915 (h * A, h * B, h, h ^ 2 * s, h ^ 2 • q)) =
      rhoCh_STR02970 h A B q *
        (h ^ 2 • B2_STR02970 A B q + h ^ 3 • R3_STR02970 h s A B q -
          kappa_STR02970 h s A B q • (1 : PeriodicHolder_STR02968)) := by
  show Gfun_STR02955 h (h ^ 2 * s) (uch_STR02970 h A B q) = _
  unfold Gfun_STR02955
  rw [bracket_chart_STR02970]
  rfl


/-! ### The projection and the explicit forcing -/

theorem PCLM_one_STR02970 : PCLM_STR02955 (1 : PeriodicHolder_STR02968) = 0 := by
  apply ext_STR02954
  rw [PCLM_val_STR02955, val_one_STR02954]
  funext t
  simp only [projP_STR02953, pair_STR02953, meanT_const_STR02955, one_mul, meanT_cos_STR02955,
    meanT_sin_STR02955]
  show 1 - 1 - 2 * 0 * Real.cos t - 2 * 0 * Real.sin t = 0
  ring

theorem PCLM_eq_self_STR02970 {f : PeriodicHolder_STR02968} (hf : InE_STR02901 f.val) :
    PCLM_STR02955 f = f :=
  ext_STR02954 (by rw [PCLM_val_STR02955]; exact projP_of_inE_STR02955 hf)

theorem inE_add_H_STR02970 {x y : PeriodicHolder_STR02968} (hx : InE_STR02901 x.val)
    (hy : InE_STR02901 y.val) : InE_STR02901 (x + y).val :=
  inE_add_STR02970 hx hy x.isPerHolder.2.1 y.isPerHolder.2.1

theorem q_inE_STR02970 (q : E_STR02969) : InE_STR02901 (q : PeriodicC2_STR02969).val :=
  (str029_69_completeness_closed_complements_range_spaces_E.1 _).1 q.2

/-- The explicit order-two forcing
`-2 (q'' + q) + (-3A + (A²-B²)/2) cos 2t + (3B + AB) sin 2t + 3A cos 4t + 3B sin 4t`. -/
noncomputable def forcing_STR02970 (A B : ℝ) (q : E_STR02969) : PeriodicHolder_STR02968 :=
  (-2 : ℝ) • (e2_STR02955 (q : PeriodicC2_STR02969) + e0_STR02955 (q : PeriodicC2_STR02969)) +
    harmH_STR02970 1 (-3 * A + (A ^ 2 - B ^ 2) / 2) (3 * B + A * B) +
    harmH_STR02970 3 (3 * A) (3 * B)

theorem harm1_STR02970 (a b t : ℝ) :
    harm_STR02970 1 a b t = a * Real.cos (2 * t) + b * Real.sin (2 * t) := by
  have : ((1 + 1 : ℕ) : ℝ) = 2 := by norm_num
  simp only [harm_STR02970, this]

theorem harm3_STR02970 (a b t : ℝ) :
    harm_STR02970 3 a b t = a * Real.cos (4 * t) + b * Real.sin (4 * t) := by
  have : ((3 + 1 : ℕ) : ℝ) = 4 := by norm_num
  simp only [harm_STR02970, this]

theorem forcing_val_STR02970 (A B : ℝ) (q : E_STR02969) (t : ℝ) :
    (forcing_STR02970 A B q).val t =
      -2 * (deriv (deriv (q : PeriodicC2_STR02969).val) t + (q : PeriodicC2_STR02969).val t) +
        (-3 * A + (A ^ 2 - B ^ 2) / 2) * Real.cos (2 * t) + (3 * B + A * B) * Real.sin (2 * t) +
        3 * A * Real.cos (4 * t) + 3 * B * Real.sin (4 * t) := by
  simp only [forcing_STR02970, PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, harmH_val_STR02970, harm1_STR02970, harm3_STR02970,
    e2_val_STR02955, e0_val_STR02955]
  ring

theorem forcing_inE_STR02970 (A B : ℝ) (q : E_STR02969) :
    InE_STR02901 (forcing_STR02970 A B q).val := by
  have h1 : InE_STR02901 ((-2 : ℝ) • (e2_STR02955 (q : PeriodicC2_STR02969) +
      e0_STR02955 (q : PeriodicC2_STR02969))).val :=
    inE_smul_STR02955 (-2) (c2_inE_STR02955 (q : PeriodicC2_STR02969).isC2 (q_inE_STR02970 q).1)
  exact inE_add_H_STR02970 (inE_add_H_STR02970 h1 (harm_inE_STR02970 1 le_rfl _ _))
    (harm_inE_STR02970 3 (by norm_num) _ _)

theorem B2_eq_STR02970 (A B : ℝ) (q : E_STR02969) :
    B2_STR02970 A B q = forcing_STR02970 A B q - ((A ^ 2 + B ^ 2) / 2) • (1 : PeriodicHolder_STR02968) := by
  apply ext_STR02954
  funext t
  have := trig_forcing_STR02970 A B t
  simp only [B2_STR02970, p1_STR02970, forcing_STR02970, PeriodicHolder_STR02968.val_add,
    PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_smul, val_mul_STR02954,
    val_one_STR02954, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
    harmH_val_STR02970, e2_val_STR02955, e0_val_STR02955, cH_val_STR02970, sH_val_STR02970]
  have s3v : s3_STR02955.val t = Real.sin (3 * t) := rfl
  rw [s3v]
  linear_combination this

theorem PCLM_B2_STR02970 (A B : ℝ) (q : E_STR02969) :
    PCLM_STR02955 (B2_STR02970 A B q) = forcing_STR02970 A B q := by
  rw [B2_eq_STR02970, map_sub, map_smul, PCLM_one_STR02970, smul_zero, sub_zero]
  exact PCLM_eq_self_STR02970 (forcing_inE_STR02970 A B q)


/-! ### Abstract estimate and the Lipschitz bound for the density weight -/

theorem proj_remainder_STR02970 (ρ B R : PeriodicHolder_STR02968) (h κ : ℝ) :
    ‖PCLM_STR02955 (ρ * (h ^ 2 • B + h ^ 3 • R - κ • (1 : PeriodicHolder_STR02968))) -
        h ^ 2 • PCLM_STR02955 B‖ ≤
      ‖PCLM_STR02955‖ * (h ^ 2 * (‖ρ - 1‖ * ‖B‖) + |h| ^ 3 * (‖ρ‖ * ‖R‖) + |κ| * ‖ρ - 1‖) := by
  have key : PCLM_STR02955 (ρ * (h ^ 2 • B + h ^ 3 • R - κ • (1 : PeriodicHolder_STR02968))) -
        h ^ 2 • PCLM_STR02955 B =
      PCLM_STR02955 (h ^ 2 • ((ρ - 1) * B) + h ^ 3 • (ρ * R) - κ • (ρ - 1)) := by
    have e : ρ * (h ^ 2 • B + h ^ 3 • R - κ • (1 : PeriodicHolder_STR02968)) - h ^ 2 • B =
        (h ^ 2 • ((ρ - 1) * B) + h ^ 3 • (ρ * R) - κ • (ρ - 1)) - κ • (1 : PeriodicHolder_STR02968) := by
      apply ext_STR02954
      funext t
      simp only [PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_sub,
        PeriodicHolder_STR02968.val_smul, val_mul_STR02954, val_one_STR02954, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
      ring
    have e2 := congrArg PCLM_STR02955 e
    rw [map_sub, map_sub, map_smul, map_smul, PCLM_one_STR02970, smul_zero, sub_zero] at e2
    rw [← e2]
  rw [key]
  refine (PCLM_STR02955.le_opNorm _).trans ?_
  gcongr
  calc ‖h ^ 2 • ((ρ - 1) * B) + h ^ 3 • (ρ * R) - κ • (ρ - 1)‖
      ≤ ‖h ^ 2 • ((ρ - 1) * B) + h ^ 3 • (ρ * R)‖ + ‖κ • (ρ - 1)‖ := norm_sub_le _ _
    _ ≤ ‖h ^ 2 • ((ρ - 1) * B)‖ + ‖h ^ 3 • (ρ * R)‖ + ‖κ • (ρ - 1)‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ h ^ 2 * (‖ρ - 1‖ * ‖B‖) + |h| ^ 3 * (‖ρ‖ * ‖R‖) + |κ| * ‖ρ - 1‖ := by
        rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_pow, abs_pow, sq_abs]
        gcongr <;> exact norm_mul_le _ _

theorem rho_lip_STR02970 :
    ∃ ε : ℝ, 0 < ε ∧ ∃ L : ℝ, 0 ≤ L ∧ ∀ (h : ℝ) (v : PeriodicHolder_STR02968),
      |h| < ε → ‖v‖ < ε → ‖rho_STR02954 (h, v) - 1‖ ≤ L * max |h| ‖v‖ := by
  have hc : ContDiffAt ℝ 1 rho_STR02954 ((0 : ℝ), (0 : PeriodicHolder_STR02968)) :=
    rho_smooth_STR02954.contDiffAt.of_le (by exact_mod_cast le_top)
  obtain ⟨K, t, ht, hL⟩ := hc.exists_lipschitzOnWith
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 ht
  refine ⟨ε, hε, K, K.coe_nonneg, fun h v hh hv => ?_⟩
  have hmem : (h, v) ∈ Metric.ball ((0 : ℝ), (0 : PeriodicHolder_STR02968)) ε := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [dist_zero_right, Real.norm_eq_abs, max_lt_iff]
    exact ⟨hh, hv⟩
  have h0 : ((0 : ℝ), (0 : PeriodicHolder_STR02968)) ∈ t := mem_of_mem_nhds ht
  have := hL.dist_le_mul (h, v) (hball hmem) _ h0
  rw [rho_zero_STR02955, dist_eq_norm, Prod.dist_eq] at this
  simpa only [dist_zero_right, Real.norm_eq_abs] using this


/-! ### Norm bounds at the chart point -/

/-- The constant `‖cos‖ + ‖sin‖` in the Hölder norm. -/
noncomputable def cp_STR02970 : ℝ := ‖cH_STR02970‖ + ‖sH_STR02970‖

theorem cp_nonneg_STR02970 : 0 ≤ cp_STR02970 := add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem norm_p0_le_STR02970 {A B M : ℝ} (hA : |A| ≤ M) (hB : |B| ≤ M) :
    ‖p0_STR02970 A B‖ ≤ M * cp_STR02970 := by
  unfold p0_STR02970 cp_STR02970
  calc ‖A • cH_STR02970 + B • sH_STR02970‖ ≤ ‖A • cH_STR02970‖ + ‖B • sH_STR02970‖ :=
        norm_add_le _ _
    _ = |A| * ‖cH_STR02970‖ + |B| * ‖sH_STR02970‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ M * ‖cH_STR02970‖ + M * ‖sH_STR02970‖ := by gcongr
    _ = M * (‖cH_STR02970‖ + ‖sH_STR02970‖) := by ring

theorem norm_p1_le_STR02970 {A B M : ℝ} (hA : |A| ≤ M) (hB : |B| ≤ M) :
    ‖p1_STR02970 A B‖ ≤ M * cp_STR02970 := by
  unfold p1_STR02970 cp_STR02970
  calc ‖B • cH_STR02970 - A • sH_STR02970‖ ≤ ‖B • cH_STR02970‖ + ‖A • sH_STR02970‖ :=
        norm_sub_le _ _
    _ = |B| * ‖cH_STR02970‖ + |A| * ‖sH_STR02970‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ M * ‖cH_STR02970‖ + M * ‖sH_STR02970‖ := by gcongr
    _ = M * (‖cH_STR02970‖ + ‖sH_STR02970‖) := by ring

theorem norm_emb_q_le_STR02970 (T : PeriodicC2_STR02969 →L[ℝ] PeriodicHolder_STR02968)
    {q : E_STR02969} {M : ℝ} (hq : ‖q‖ ≤ M) : ‖T (q : PeriodicC2_STR02969)‖ ≤ ‖T‖ * M :=
  (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left hq (norm_nonneg _))

theorem norm_B2_le_STR02970 {A B M : ℝ} {q : E_STR02969} (hA : |A| ≤ M) (hB : |B| ≤ M)
    (hq : ‖q‖ ≤ M) :
    ‖B2_STR02970 A B q‖ ≤ 2 * ((‖e2_STR02955‖ + ‖e0_STR02955‖) * M) +
      6 * (‖s3_STR02955‖ * (M * cp_STR02970)) + (M * cp_STR02970) * (M * cp_STR02970) := by
  have h1 := norm_p1_le_STR02970 hA hB
  have h2 := norm_emb_q_le_STR02970 e2_STR02955 hq
  have h0 := norm_emb_q_le_STR02970 e0_STR02955 hq
  unfold B2_STR02970
  calc ‖(-2 : ℝ) • (e2_STR02955 (q : PeriodicC2_STR02969) + e0_STR02955 (q : PeriodicC2_STR02969)) +
          (6 : ℝ) • (s3_STR02955 * p1_STR02970 A B) - p1_STR02970 A B * p1_STR02970 A B‖
      ≤ ‖(-2 : ℝ) • (e2_STR02955 (q : PeriodicC2_STR02969) + e0_STR02955 (q : PeriodicC2_STR02969))‖ +
          ‖(6 : ℝ) • (s3_STR02955 * p1_STR02970 A B)‖ + ‖p1_STR02970 A B * p1_STR02970 A B‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 2 * (‖e2_STR02955 (q : PeriodicC2_STR02969)‖ + ‖e0_STR02955 (q : PeriodicC2_STR02969)‖) +
          6 * (‖s3_STR02955‖ * ‖p1_STR02970 A B‖) + ‖p1_STR02970 A B‖ * ‖p1_STR02970 A B‖ := by
        rw [norm_smul, norm_smul]
        norm_num
        gcongr
        · exact norm_add_le _ _
        · exact norm_mul_le _ _
        · exact norm_mul_le _ _
    _ ≤ _ := by
        have hM : 0 ≤ M := (abs_nonneg A).trans hA
        have hcp : 0 ≤ M * cp_STR02970 := mul_nonneg hM cp_nonneg_STR02970
        gcongr
        linarith


/-- Norm of a scalar multiple of a product. -/
theorem norm_smul_mul_le_STR02970 (c : ℝ) (x y : PeriodicHolder_STR02968) :
    ‖c • (x * y)‖ ≤ |c| * (‖x‖ * ‖y‖) := by
  rw [norm_smul, Real.norm_eq_abs]
  gcongr
  exact norm_mul_le _ _

/-- Bound for the order-two bracket. -/
noncomputable def CB_STR02970 (M : ℝ) : ℝ :=
  2 * ((‖e2_STR02955‖ + ‖e0_STR02955‖) * M) + 6 * (‖s3_STR02955‖ * (M * cp_STR02970)) +
    (M * cp_STR02970) * (M * cp_STR02970)

/-- Bound for the order-three bracket. -/
noncomputable def CR_STR02970 (M : ℝ) : ℝ :=
  6 * (‖s3_STR02955‖ * (‖e1_STR02955‖ * M)) + 2 * ((M * cp_STR02970) * (‖e1_STR02955‖ * M)) +
    2 * M * (M * cp_STR02970) +
    (2 * M * (‖e0_STR02955‖ * M) + (‖e1_STR02955‖ * M) * (‖e1_STR02955‖ * M))

/-- Bound for `e0` of the chart point, divided by `|h|`. -/
noncomputable def K0_STR02970 (M : ℝ) : ℝ := M * cp_STR02970 + ‖e0_STR02955‖ * M

/-- Bound for `e1` of the chart point, divided by `|h|`. -/
noncomputable def K1_STR02970 (M : ℝ) : ℝ := M * cp_STR02970 + ‖e1_STR02955‖ * M

theorem sq_le_abs_STR02970 {h : ℝ} (hh : |h| ≤ 1) : h ^ 2 ≤ |h| := by
  calc h ^ 2 = |h| * |h| := by rw [← sq_abs]; ring
    _ ≤ |h| * 1 := by gcongr
    _ = |h| := mul_one _

theorem norm_R3_le_STR02970 {h s A B M : ℝ} {q : E_STR02969} (hh : |h| ≤ 1) (hs : |s| ≤ M)
    (hA : |A| ≤ M) (hB : |B| ≤ M) (hq : ‖q‖ ≤ M) :
    ‖R3_STR02970 h s A B q‖ ≤ CR_STR02970 M := by
  have hM : 0 ≤ M := (abs_nonneg A).trans hA
  have hp0 := norm_p0_le_STR02970 hA hB
  have hp1 := norm_p1_le_STR02970 hA hB
  have h1 := norm_emb_q_le_STR02970 e1_STR02955 hq
  have h0 := norm_emb_q_le_STR02970 e0_STR02955 hq
  have hcp : 0 ≤ M * cp_STR02970 := mul_nonneg hM cp_nonneg_STR02970
  unfold R3_STR02970 CR_STR02970
  set x1 := (6 : ℝ) • (s3_STR02955 * e1_STR02955 (q : PeriodicC2_STR02969)) with hx1
  set x2 := (2 : ℝ) • (p1_STR02970 A B * e1_STR02955 (q : PeriodicC2_STR02969)) with hx2
  set x3 := (2 * s) • p0_STR02970 A B with hx3
  set x4 := h • ((-2 * s) • e0_STR02955 (q : PeriodicC2_STR02969) -
      e1_STR02955 (q : PeriodicC2_STR02969) * e1_STR02955 (q : PeriodicC2_STR02969)) with hx4
  have t1 : ‖x1‖ ≤ 6 * (‖s3_STR02955‖ * (‖e1_STR02955‖ * M)) := by
    refine (norm_smul_mul_le_STR02970 _ _ _).trans ?_
    norm_num
    gcongr
  have t2 : ‖x2‖ ≤ 2 * ((M * cp_STR02970) * (‖e1_STR02955‖ * M)) := by
    refine (norm_smul_mul_le_STR02970 _ _ _).trans ?_
    norm_num
    gcongr
  have t3 : ‖x3‖ ≤ 2 * M * (M * cp_STR02970) := by
    rw [hx3, norm_smul, Real.norm_eq_abs, abs_mul, abs_two]
    gcongr
  have t4 : ‖x4‖ ≤ 2 * M * (‖e0_STR02955‖ * M) + (‖e1_STR02955‖ * M) * (‖e1_STR02955‖ * M) := by
    rw [hx4, norm_smul, Real.norm_eq_abs]
    have a1 : ‖(-2 * s) • e0_STR02955 (q : PeriodicC2_STR02969) -
        e1_STR02955 (q : PeriodicC2_STR02969) * e1_STR02955 (q : PeriodicC2_STR02969)‖ ≤
        2 * M * (‖e0_STR02955‖ * M) + (‖e1_STR02955‖ * M) * (‖e1_STR02955‖ * M) := by
      refine (norm_sub_le _ _).trans ?_
      have b1 : ‖(-2 * s) • e0_STR02955 (q : PeriodicC2_STR02969)‖ ≤ 2 * M * (‖e0_STR02955‖ * M) := by
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_two]
        gcongr
      have b2 : ‖e1_STR02955 (q : PeriodicC2_STR02969) * e1_STR02955 (q : PeriodicC2_STR02969)‖ ≤
          (‖e1_STR02955‖ * M) * (‖e1_STR02955‖ * M) :=
        (norm_mul_le _ _).trans (by gcongr)
      linarith
    calc |h| * _ ≤ 1 * _ := by gcongr
      _ ≤ _ := by linarith
  calc ‖x1 - x2 - x3 + x4‖ ≤ ‖x1 - x2 - x3‖ + ‖x4‖ := norm_add_le _ _
    _ ≤ ‖x1 - x2‖ + ‖x3‖ + ‖x4‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ‖x1‖ + ‖x2‖ + ‖x3‖ + ‖x4‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ _ := by linarith


theorem norm_e0_uch_le_STR02970 {h A B M : ℝ} {q : E_STR02969} (hh : |h| ≤ 1) (hA : |A| ≤ M)
    (hB : |B| ≤ M) (hq : ‖q‖ ≤ M) :
    ‖e0_STR02955 (uch_STR02970 h A B q)‖ ≤ |h| * K0_STR02970 M := by
  rw [e0_uch_STR02970]
  have hp := norm_p0_le_STR02970 hA hB
  have hq' := norm_emb_q_le_STR02970 e0_STR02955 hq
  have hh2 := sq_le_abs_STR02970 hh
  calc ‖h • p0_STR02970 A B + h ^ 2 • e0_STR02955 (q : PeriodicC2_STR02969)‖
      ≤ ‖h • p0_STR02970 A B‖ + ‖h ^ 2 • e0_STR02955 (q : PeriodicC2_STR02969)‖ := norm_add_le _ _
    _ = |h| * ‖p0_STR02970 A B‖ + h ^ 2 * ‖e0_STR02955 (q : PeriodicC2_STR02969)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
    _ ≤ |h| * (M * cp_STR02970) + |h| * (‖e0_STR02955‖ * M) := by gcongr
    _ = |h| * K0_STR02970 M := by unfold K0_STR02970; ring

theorem norm_e1_uch_le_STR02970 {h A B M : ℝ} {q : E_STR02969} (hh : |h| ≤ 1) (hA : |A| ≤ M)
    (hB : |B| ≤ M) (hq : ‖q‖ ≤ M) :
    ‖e1_STR02955 (uch_STR02970 h A B q)‖ ≤ |h| * K1_STR02970 M := by
  rw [e1_uch_STR02970]
  have hp := norm_p1_le_STR02970 hA hB
  have hq' := norm_emb_q_le_STR02970 e1_STR02955 hq
  have hh2 := sq_le_abs_STR02970 hh
  calc ‖h • p1_STR02970 A B + h ^ 2 • e1_STR02955 (q : PeriodicC2_STR02969)‖
      ≤ ‖h • p1_STR02970 A B‖ + ‖h ^ 2 • e1_STR02955 (q : PeriodicC2_STR02969)‖ := norm_add_le _ _
    _ = |h| * ‖p1_STR02970 A B‖ + h ^ 2 * ‖e1_STR02955 (q : PeriodicC2_STR02969)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
    _ ≤ |h| * (M * cp_STR02970) + |h| * (‖e1_STR02955‖ * M) := by gcongr
    _ = |h| * K1_STR02970 M := by unfold K1_STR02970; ring

/-- The `e0` of the chart point has mean zero. -/
theorem mean_e0_uch_STR02970 (h A B : ℝ) (q : E_STR02969) :
    meanCLM_STR02954 (e0_STR02955 (uch_STR02970 h A B q)) = 0 := by
  have hc : meanCLM_STR02954 cH_STR02970 = 0 := by
    rw [meanCLM_apply_STR02954, cH_val_STR02970]; exact meanT_cos_STR02955
  have hs : meanCLM_STR02954 sH_STR02970 = 0 := by
    rw [meanCLM_apply_STR02954, sH_val_STR02970]; exact meanT_sin_STR02955
  have hq : meanCLM_STR02954 (e0_STR02955 (q : PeriodicC2_STR02969)) = 0 := by
    rw [meanCLM_apply_STR02954]; exact (q_inE_STR02970 q).1
  rw [e0_uch_STR02970]
  simp only [p0_STR02970, map_add, map_smul, hc, hs, hq, smul_zero, add_zero]

theorem coe_norm_STR02970 (q : E_STR02969) : ‖(q : PeriodicC2_STR02969)‖ = ‖q‖ := rfl


theorem abs_mean_le_STR02970 (x : PeriodicHolder_STR02968) :
    |meanCLM_STR02954 x| ≤ ‖meanCLM_STR02954‖ * ‖x‖ := by
  have := meanCLM_STR02954.le_opNorm x
  rwa [Real.norm_eq_abs] at this

/-- Abstract bound for the scalar `κ = I - 2 (1 + γ) E`. -/
theorem kappa_abstract_STR02970 {a0 a1 ρ : PeriodicHolder_STR02968} {h s M K0 K1 Lr : ℝ}
    (hh : |h| ≤ 1) (hs : |s| ≤ M) (hM : 0 ≤ M) (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1)
    (e0b : ‖a0‖ ≤ |h| * K0) (e1b : ‖a1‖ ≤ |h| * K1)
    (hm : meanCLM_STR02954 a0 = 0) (hρ1 : ‖ρ - 1‖ ≤ Lr * |h|) (hρ : ‖ρ‖ ≤ 1 + Lr) :
    |meanCLM_STR02954 (a1 * a1 * ρ) - 2 * (1 + h ^ 2 * s) * meanCLM_STR02954 (a0 * ρ)| ≤
      (‖meanCLM_STR02954‖ * (K1 ^ 2 * (1 + Lr)) +
        2 * (1 + M) * (‖meanCLM_STR02954‖ * (K0 * Lr))) * h ^ 2 := by
  have hNm := norm_nonneg meanCLM_STR02954
  have hI : |meanCLM_STR02954 (a1 * a1 * ρ)| ≤
      ‖meanCLM_STR02954‖ * ((|h| * K1) * (|h| * K1) * (1 + Lr)) := by
    refine (abs_mean_le_STR02970 _).trans ?_
    gcongr
    calc ‖a1 * a1 * ρ‖ ≤ ‖a1 * a1‖ * ‖ρ‖ := norm_mul_le _ _
      _ ≤ (‖a1‖ * ‖a1‖) * ‖ρ‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ((|h| * K1) * (|h| * K1)) * (1 + Lr) := by gcongr
  have hE0 : a0 * ρ = a0 * (ρ - 1) + a0 := by rw [mul_sub, mul_one, sub_add_cancel]
  have hE : |meanCLM_STR02954 (a0 * ρ)| ≤ ‖meanCLM_STR02954‖ * ((|h| * K0) * (Lr * |h|)) := by
    rw [hE0, map_add, hm, add_zero]
    refine (abs_mean_le_STR02970 _).trans ?_
    gcongr
    calc ‖a0 * (ρ - 1)‖ ≤ ‖a0‖ * ‖ρ - 1‖ := norm_mul_le _ _
      _ ≤ (|h| * K0) * (Lr * |h|) := by gcongr
  have hc : |2 * (1 + h ^ 2 * s)| ≤ 2 * (1 + M) := by
    have h2 : h ^ 2 ≤ 1 := by
      have := sq_le_abs_STR02970 hh
      linarith
    have h3 : |h ^ 2 * s| ≤ M := by
      rw [abs_mul, abs_pow, sq_abs]
      calc h ^ 2 * |s| ≤ 1 * M := by gcongr
        _ = M := one_mul M
    calc |2 * (1 + h ^ 2 * s)| = 2 * |1 + h ^ 2 * s| := by rw [abs_mul, abs_two]
      _ ≤ 2 * (1 + |h ^ 2 * s|) := by
          gcongr
          calc |1 + h ^ 2 * s| ≤ |(1 : ℝ)| + |h ^ 2 * s| := abs_add_le _ _
            _ = 1 + |h ^ 2 * s| := by rw [abs_one]
      _ ≤ 2 * (1 + M) := by gcongr
  calc |meanCLM_STR02954 (a1 * a1 * ρ) - 2 * (1 + h ^ 2 * s) * meanCLM_STR02954 (a0 * ρ)|
      ≤ |meanCLM_STR02954 (a1 * a1 * ρ)| + |2 * (1 + h ^ 2 * s) * meanCLM_STR02954 (a0 * ρ)| :=
        abs_sub _ _
    _ ≤ ‖meanCLM_STR02954‖ * ((|h| * K1) * (|h| * K1) * (1 + Lr)) +
          2 * (1 + M) * (‖meanCLM_STR02954‖ * ((|h| * K0) * (Lr * |h|))) := by
        rw [abs_mul (2 * (1 + h ^ 2 * s))]
        gcongr
    _ = _ := by rw [← sq_abs h]; ring

/-- The two bounds on the density weight at the chart point. -/
theorem rhoCh_bounds_STR02970 {ε L M h A B : ℝ} {q : E_STR02969} (hL0 : 0 ≤ L)
    (hLip : ∀ (h : ℝ) (v : PeriodicHolder_STR02968), |h| < ε → ‖v‖ < ε →
      ‖rho_STR02954 (h, v) - 1‖ ≤ L * max |h| ‖v‖)
    (hh : |h| ≤ 1) (hhε : |h| < ε) (hA : |A| ≤ M) (hB : |B| ≤ M) (hq : ‖q‖ ≤ M)
    (hv : ‖e0_STR02955 (uch_STR02970 h A B q)‖ < ε) :
    ‖rhoCh_STR02970 h A B q - 1‖ ≤ L * (1 + K0_STR02970 M) * |h| ∧
      ‖rhoCh_STR02970 h A B q‖ ≤ 1 + L * (1 + K0_STR02970 M) := by
  have hM : 0 ≤ M := (abs_nonneg A).trans hA
  have hK0 : 0 ≤ K0_STR02970 M :=
    add_nonneg (mul_nonneg hM cp_nonneg_STR02970) (mul_nonneg (norm_nonneg _) hM)
  have h1 := hLip h _ hhε hv
  have e0b := norm_e0_uch_le_STR02970 hh hA hB hq
  have hmax : max |h| ‖e0_STR02955 (uch_STR02970 h A B q)‖ ≤ |h| * (1 + K0_STR02970 M) := by
    refine max_le ?_ (e0b.trans ?_)
    · exact le_mul_of_one_le_right (abs_nonneg h) (by linarith)
    · gcongr; linarith
  have h2 : ‖rhoCh_STR02970 h A B q - 1‖ ≤ L * (1 + K0_STR02970 M) * |h| := by
    calc ‖rhoCh_STR02970 h A B q - 1‖ ≤ L * max |h| ‖e0_STR02955 (uch_STR02970 h A B q)‖ := h1
      _ ≤ L * (|h| * (1 + K0_STR02970 M)) := by gcongr
      _ = L * (1 + K0_STR02970 M) * |h| := by ring
  refine ⟨h2, ?_⟩
  calc ‖rhoCh_STR02970 h A B q‖ = ‖(rhoCh_STR02970 h A B q - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ ‖rhoCh_STR02970 h A B q - 1‖ + ‖(1 : PeriodicHolder_STR02968)‖ := norm_add_le _ _
    _ = ‖rhoCh_STR02970 h A B q - 1‖ + 1 := by rw [norm_one_STR02954]
    _ ≤ L * (1 + K0_STR02970 M) * 1 + 1 := by
        gcongr
        exact h2.trans (by gcongr)
    _ = 1 + L * (1 + K0_STR02970 M) := by ring


/-- The Lipschitz constant of the density weight, scaled by the bound on `e0` of the chart point. -/
noncomputable def Lrho_STR02970 (L M : ℝ) : ℝ := L * (1 + K0_STR02970 M)

/-- The bound on `κ / h²`. -/
noncomputable def Ckap_STR02970 (L M : ℝ) : ℝ :=
  ‖meanCLM_STR02954‖ * (K1_STR02970 M ^ 2 * (1 + Lrho_STR02970 L M)) +
    2 * (1 + M) * (‖meanCLM_STR02954‖ * (K0_STR02970 M * Lrho_STR02970 L M))

/-- The constant in the third-order remainder bound. -/
noncomputable def Ccore_STR02970 (L M : ℝ) : ℝ :=
  ‖PCLM_STR02955‖ * (Lrho_STR02970 L M * CB_STR02970 M +
    (1 + Lrho_STR02970 L M) * CR_STR02970 M + Ckap_STR02970 L M * Lrho_STR02970 L M)

theorem remainder_core_STR02970 {ε L M h s A B : ℝ} {q : E_STR02969} (hL0 : 0 ≤ L)
    (hLip : ∀ (h : ℝ) (v : PeriodicHolder_STR02968), |h| < ε → ‖v‖ < ε →
      ‖rho_STR02954 (h, v) - 1‖ ≤ L * max |h| ‖v‖)
    (hh : |h| ≤ 1) (hhε : |h| < ε) (hs : |s| ≤ M) (hA : |A| ≤ M) (hB : |B| ≤ M)
    (hq : ‖q‖ ≤ M) (hv : ‖e0_STR02955 (uch_STR02970 h A B q)‖ < ε) :
    ‖PCLM_STR02955 (Gmap_STR02955 (paramMap_STR02915 (h * A, h * B, h, h ^ 2 * s, h ^ 2 • q))) -
        h ^ 2 • forcing_STR02970 A B q‖ ≤ Ccore_STR02970 L M * |h| ^ 3 := by
  have hM : 0 ≤ M := (abs_nonneg A).trans hA
  have hK0 : 0 ≤ K0_STR02970 M :=
    add_nonneg (mul_nonneg hM cp_nonneg_STR02970) (mul_nonneg (norm_nonneg _) hM)
  have hK1 : 0 ≤ K1_STR02970 M :=
    add_nonneg (mul_nonneg hM cp_nonneg_STR02970) (mul_nonneg (norm_nonneg _) hM)
  obtain ⟨hρ1, hρ⟩ := rhoCh_bounds_STR02970 hL0 hLip hh hhε hA hB hq hv
  have hLρ0 : 0 ≤ Lrho_STR02970 L M := mul_nonneg hL0 (by linarith)
  have h1Lρ : 0 ≤ 1 + Lrho_STR02970 L M := by linarith
  have hκ : |kappa_STR02970 h s A B q| ≤ Ckap_STR02970 L M * h ^ 2 :=
    kappa_abstract_STR02970 hh hs hM hK0 hK1 (norm_e0_uch_le_STR02970 hh hA hB hq)
      (norm_e1_uch_le_STR02970 hh hA hB hq) (mean_e0_uch_STR02970 h A B q) hρ1 hρ
  have hκ0 : 0 ≤ Ckap_STR02970 L M * h ^ 2 := (abs_nonneg _).trans hκ
  have hB2 : ‖B2_STR02970 A B q‖ ≤ CB_STR02970 M := norm_B2_le_STR02970 hA hB hq
  have hR3 := norm_R3_le_STR02970 hh hs hA hB hq
  have hρ1' : ‖rhoCh_STR02970 h A B q - 1‖ ≤ Lrho_STR02970 L M * |h| := hρ1
  have hρ' : ‖rhoCh_STR02970 h A B q‖ ≤ 1 + Lrho_STR02970 L M := hρ
  rw [Gmap_chart_STR02970, ← PCLM_B2_STR02970 A B q]
  refine (proj_remainder_STR02970 _ _ _ _ _).trans ?_
  calc ‖PCLM_STR02955‖ * (h ^ 2 * (‖rhoCh_STR02970 h A B q - 1‖ * ‖B2_STR02970 A B q‖) +
        |h| ^ 3 * (‖rhoCh_STR02970 h A B q‖ * ‖R3_STR02970 h s A B q‖) +
        |kappa_STR02970 h s A B q| * ‖rhoCh_STR02970 h A B q - 1‖)
      ≤ ‖PCLM_STR02955‖ * (h ^ 2 * ((Lrho_STR02970 L M * |h|) * CB_STR02970 M) +
        |h| ^ 3 * ((1 + Lrho_STR02970 L M) * CR_STR02970 M) +
        (Ckap_STR02970 L M * h ^ 2) * (Lrho_STR02970 L M * |h|)) := by gcongr
    _ = Ccore_STR02970 L M * |h| ^ 3 := by unfold Ccore_STR02970; rw [← sq_abs h]; ring


/-- The explicit forcing as an element of the range space `Y`. -/
noncomputable def forcingY_STR02970 (A B : ℝ) (q : E_STR02969) : Y_STR02969 :=
  ⟨forcing_STR02970 A B q,
    (str029_69_completeness_closed_complements_range_spaces_Y.1 _).2 (forcing_inE_STR02970 A B q)⟩

theorem norm_uch_le_STR02970 (h A B : ℝ) (q : E_STR02969) :
    ‖uch_STR02970 h A B q‖ ≤
      |h * A| * ‖cosC2_STR02915‖ + |h * B| * ‖sinC2_STR02915‖ + ‖h ^ 2 • q‖ := by
  unfold uch_STR02970
  calc ‖(h * A) • cosC2_STR02915 + (h * B) • sinC2_STR02915 +
        ((h ^ 2 • q : E_STR02969) : PeriodicC2_STR02969)‖
      ≤ ‖(h * A) • cosC2_STR02915‖ + ‖(h * B) • sinC2_STR02915‖ +
        ‖((h ^ 2 • q : E_STR02969) : PeriodicC2_STR02969)‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ = |h * A| * ‖cosC2_STR02915‖ + |h * B| * ‖sinC2_STR02915‖ + ‖h ^ 2 • q‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, coe_norm_STR02970]

theorem str029_70_explicit_order_two_forcing_weighted_variational_chart :
    ∃ r : ℝ, 0 < r ∧ ∀ M : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A B s h : ℝ) (q : E_STR02969), |A| ≤ M → |B| ≤ M → |s| ≤ M → ‖q‖ ≤ M →
        ‖(h * A, h * B, h, h ^ 2 * s, h ^ 2 • q)‖ ≤ r →
        ‖Rvar_STR02915 (h * A, h * B, h, h ^ 2 * s, h ^ 2 • q) - h ^ 2 • forcingY_STR02970 A B q‖ ≤
          C * |h| ^ 3 := by
  obtain ⟨ε, hε, L, hL0, hLip⟩ := rho_lip_STR02970
  set D : ℝ := ‖e0_STR02955‖ * (‖cosC2_STR02915‖ + ‖sinC2_STR02915‖ + 1) with hD
  have hD0 : 0 ≤ D := by positivity
  have hr0 : 0 < ε / (2 * (D + 1)) := by positivity
  set r : ℝ := min 1 (ε / (2 * (D + 1))) with hr
  have hrpos : 0 < r := lt_min one_pos hr0
  have hr1 : r ≤ 1 := min_le_left _ _
  have hr2 : r * (2 * (D + 1)) ≤ ε := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  refine ⟨r, hrpos, fun M => ⟨max (Ccore_STR02970 L M) 0, le_max_right _ _, ?_⟩⟩
  intro A B s h q hA hB hs hq hrh
  simp only [Prod.norm_def, max_le_iff, Real.norm_eq_abs] at hrh
  obtain ⟨hhA, hhB, hh, -, hhq⟩ := hrh
  have hh1 : |h| ≤ 1 := hh.trans hr1
  have hrD : 0 ≤ r * D := mul_nonneg hrpos.le hD0
  have hhε : |h| < ε := by nlinarith
  have hv : ‖e0_STR02955 (uch_STR02970 h A B q)‖ < ε := by
    have h1 := e0_STR02955.le_opNorm (uch_STR02970 h A B q)
    have h2 := norm_uch_le_STR02970 h A B q
    have h3 : ‖uch_STR02970 h A B q‖ ≤ r * (‖cosC2_STR02915‖ + ‖sinC2_STR02915‖ + 1) := by
      refine h2.trans ?_
      have := norm_nonneg cosC2_STR02915
      have := norm_nonneg sinC2_STR02915
      nlinarith
    have h4 : ‖e0_STR02955 (uch_STR02970 h A B q)‖ ≤ r * D := by
      refine h1.trans ?_
      rw [hD]
      calc ‖e0_STR02955‖ * ‖uch_STR02970 h A B q‖
          ≤ ‖e0_STR02955‖ * (r * (‖cosC2_STR02915‖ + ‖sinC2_STR02915‖ + 1)) := by gcongr
        _ = r * (‖e0_STR02955‖ * (‖cosC2_STR02915‖ + ‖sinC2_STR02915‖ + 1)) := by ring
    nlinarith
  have key := remainder_core_STR02970 hL0 hLip hh1 hhε hs hA hB hq hv
  have e : ‖Rvar_STR02915 (h * A, h * B, h, h ^ 2 * s, h ^ 2 • q) -
      h ^ 2 • forcingY_STR02970 A B q‖ =
      ‖PCLM_STR02955 (Gmap_STR02955 (paramMap_STR02915 (h * A, h * B, h, h ^ 2 * s, h ^ 2 • q))) -
        h ^ 2 • forcing_STR02970 A B q‖ := rfl
  rw [e]
  exact key.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))


/-- The pointwise formula for the forcing, as an element of `Y`. -/
theorem str029_70_explicit_order_two_forcing_weighted_variational_forcing_val
    (A B : ℝ) (q : E_STR02969) (t : ℝ) :
    ((forcingY_STR02970 A B q : Y_STR02969) : PeriodicHolder_STR02968).val t =
      -2 * (deriv (deriv (q : PeriodicC2_STR02969).val) t + (q : PeriodicC2_STR02969).val t) +
        (-3 * A + (A ^ 2 - B ^ 2) / 2) * Real.cos (2 * t) + (3 * B + A * B) * Real.sin (2 * t) +
        3 * A * Real.cos (4 * t) + 3 * B * Real.sin (4 * t) :=
  forcing_val_STR02970 A B q t

/-- The chart point of the range map is `P G (h, h² s, h p + h² q)`. -/
theorem str029_70_explicit_order_two_forcing_weighted_variational_chart_eq
    (A B s h : ℝ) (q : E_STR02969) :
    ((Rvar_STR02915 (h * A, h * B, h, h ^ 2 * s, h ^ 2 • q) : Y_STR02969) :
        PeriodicHolder_STR02968) =
      PCLM_STR02955 (Gfun_STR02955 h (h ^ 2 * s)
        ((h * A) • cosC2_STR02915 + (h * B) • sinC2_STR02915 +
          ((h ^ 2 • q : E_STR02969) : PeriodicC2_STR02969))) := rfl

/-- The same estimate with a radius depending on the bound `M`. -/
theorem str029_70_explicit_order_two_forcing_weighted_variational_small (M : ℝ) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A B s h : ℝ) (q : E_STR02969), |A| ≤ M → |B| ≤ M → |s| ≤ M → ‖q‖ ≤ M → |h| ≤ r →
        ‖Rvar_STR02915 (h * A, h * B, h, h ^ 2 * s, h ^ 2 • q) - h ^ 2 • forcingY_STR02970 A B q‖ ≤
          C * |h| ^ 3 := by
  obtain ⟨r0, hr0, hC⟩ := str029_70_explicit_order_two_forcing_weighted_variational_chart
  obtain ⟨C, hC0, hCb⟩ := hC M
  have hpos : 0 < r0 / (|M| + 1) := by positivity
  refine ⟨min 1 (r0 / (|M| + 1)), lt_min one_pos hpos, C, hC0, ?_⟩
  intro A B s h q hA hB hs hq hh
  have hh1 : |h| ≤ 1 := hh.trans (min_le_left _ _)
  have hk : |h| * (|M| + 1) ≤ r0 := (le_div_iff₀ (by positivity)).1 (hh.trans (min_le_right _ _))
  have hM : 0 ≤ M := (abs_nonneg A).trans hA
  rw [abs_of_nonneg hM] at hk
  have hh0 := abs_nonneg h
  have hhM : |h| * M ≤ r0 := by nlinarith
  have hh2 : |h| ^ 2 ≤ |h| := by nlinarith
  refine hCb A B s h q hA hB hs hq ?_
  simp only [Prod.norm_def, max_le_iff, Real.norm_eq_abs]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_mul]
    calc |h| * |A| ≤ |h| * M := by gcongr
      _ ≤ r0 := hhM
  · rw [abs_mul]
    calc |h| * |B| ≤ |h| * M := by gcongr
      _ ≤ r0 := hhM
  · nlinarith
  · rw [abs_mul, abs_pow]
    calc |h| ^ 2 * |s| ≤ |h| * M := by gcongr
      _ ≤ r0 := hhM
  · rw [norm_smul, Real.norm_eq_abs, abs_pow]
    calc |h| ^ 2 * ‖q‖ ≤ |h| * M := by gcongr
      _ ≤ r0 := hhM

/-- STR029.70: the coefficient of `h²` in `P G (h, h² s, h p + h² q)` is the explicit forcing
`-2 (q'' + q) + (-3A + (A²-B²)/2) cos 2t + (3B + AB) sin 2t + 3A cos 4t + 3B sin 4t`, with
remainder `O_{C^{0,1/2}}(|h|³)` uniformly for bounded `(A, B, s, q)` in a fixed small scaled
neighbourhood. -/
theorem str029_70_explicit_order_two_forcing_weighted_variational :
    ∃ F : ℝ → ℝ → E_STR02969 → Y_STR02969,
      (∀ (A B : ℝ) (q : E_STR02969) (t : ℝ),
        ((F A B q : Y_STR02969) : PeriodicHolder_STR02968).val t =
          -2 * (deriv (deriv (q : PeriodicC2_STR02969).val) t + (q : PeriodicC2_STR02969).val t) +
            (-3 * A + (A ^ 2 - B ^ 2) / 2) * Real.cos (2 * t) +
            (3 * B + A * B) * Real.sin (2 * t) +
            3 * A * Real.cos (4 * t) + 3 * B * Real.sin (4 * t)) ∧
      ∃ r : ℝ, 0 < r ∧ ∀ M : ℝ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ (A B s h : ℝ) (q : E_STR02969), |A| ≤ M → |B| ≤ M → |s| ≤ M → ‖q‖ ≤ M →
          ‖(h * A, h * B, h, h ^ 2 * s, h ^ 2 • q)‖ ≤ r →
          ‖Rvar_STR02915 (h * A, h * B, h, h ^ 2 * s, h ^ 2 • q) - h ^ 2 • F A B q‖ ≤
            C * |h| ^ 3 :=
  ⟨forcingY_STR02970, str029_70_explicit_order_two_forcing_weighted_variational_forcing_val,
    str029_70_explicit_order_two_forcing_weighted_variational_chart⟩

end DGPS.Frontier.STR029
