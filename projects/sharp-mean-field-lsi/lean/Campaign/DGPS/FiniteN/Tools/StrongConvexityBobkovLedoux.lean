import DGPS.FiniteN.Tools.StrongConvexityLSI
import Mathlib

/-!
# Strongly convex LSI from Prekopa-Leindler (INF002, Bobkov-Ledoux route)

For `U : ℝ^k → ℝ` of class `C²` with `D²U ≥ λ I`, `λ > 0`, the Gibbs law `e^{-U}/Z` satisfies
`HasLSIRate (gibbs U) λ`, given the Prekopa-Leindler inequality (`PrekopaLeindlerStatement k`).

Route (Bobkov-Ledoux 2000): PL with `f = e^{ψ/(1-t) - U}`, `g = e^{-U}`,
`h = e^{ψ + t |∇ψ|²/(2λθ) - U}` (the Hopf-Lax term is bounded explicitly through the
second-order Taylor bound on `ψ`), differentiation at `t = 0` gives
`Ent(e^ψ) ≤ (1/2λ) ∫ |∇ψ|² e^ψ`, and `ψ = log (f² + ε)`, `ε → 0` gives the LSI.
-/

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace DGPS.FiniteN.Tools.StrongConvexityBobkovLedoux

variable {k : ℕ}

abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

theorem hasDerivAt_fderiv_line {W : E k → ℝ} (hW : ContDiff ℝ 2 W) (x v : E k) (s : ℝ) :
    HasDerivAt (fun s : ℝ => fderiv ℝ W (x + s • v) v)
      (fderiv ℝ (fderiv ℝ W) (x + s • v) v v) s := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ W) := hW.fderiv_right (by norm_num)
  have h2 : HasFDerivAt (fderiv ℝ W) (fderiv ℝ (fderiv ℝ W) (x + s • v)) (x + s • v) :=
    ((h1.differentiable (by norm_num)) _).hasFDerivAt
  have h3 : HasDerivAt (fun s : ℝ => x + s • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  have h4 := (h2.comp_hasDerivAt s h3)
  have h5 := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt s h4
  exact h5

theorem hasDerivAt_comp_line {W : E k → ℝ} (hW : ContDiff ℝ 2 W) (x v : E k) (s : ℝ) :
    HasDerivAt (fun s : ℝ => W (x + s • v)) (fderiv ℝ W (x + s • v) v) s := by
  have h2 : HasFDerivAt W (fderiv ℝ W (x + s • v)) (x + s • v) :=
    ((hW.differentiable (by norm_num)) _).hasFDerivAt
  have h3 : HasDerivAt (fun s : ℝ => x + s • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  exact h2.comp_hasDerivAt s h3

theorem tangent_ineq {W : E k → ℝ} (hW : ContDiff ℝ 2 W) {κ : ℝ}
    (h : ∀ x v, κ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ W) x v v) (x y : E k) :
    W x + fderiv ℝ W x (y - x) + κ / 2 * ‖y - x‖ ^ 2 ≤ W y := by
  obtain ⟨v, hv⟩ : ∃ v, v = y - x := ⟨_, rfl⟩
  have hy : y = x + (1 : ℝ) • v := by rw [hv]; simp
  rw [← hv, hy]
  simp only [one_smul, hv]
  rw [← hv]
  have hφd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => W (x + s • v) - κ * ‖v‖ ^ 2 / 2 * s ^ 2)
      (fderiv ℝ W (x + s • v) v - κ * ‖v‖ ^ 2 * s) s := by
    intro s
    have := (hasDerivAt_comp_line hW x v s).sub
      (((hasDerivAt_id s).pow 2).const_mul (κ * ‖v‖ ^ 2 / 2))
    refine HasDerivAt.congr_deriv this ?_
    simp; ring
  have hgd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ W (x + s • v) v - κ * ‖v‖ ^ 2 * s)
      (fderiv ℝ (fderiv ℝ W) (x + s • v) v v - κ * ‖v‖ ^ 2) s := by
    intro s
    have := (hasDerivAt_fderiv_line hW x v s).sub ((hasDerivAt_id s).const_mul (κ * ‖v‖ ^ 2))
    exact HasDerivAt.congr_deriv this (by simp)
  have hmono : Monotone (fun s : ℝ => fderiv ℝ W (x + s • v) v - κ * ‖v‖ ^ 2 * s) := by
    refine monotone_of_deriv_nonneg (fun s => (hgd s).differentiableAt) ?_
    intro s
    rw [(hgd s).deriv]
    linarith [h (x + s • v) v]
  have hcont : ContinuousOn (fun s : ℝ => W (x + s • v) - κ * ‖v‖ ^ 2 / 2 * s ^ 2) (Set.Icc 0 1) :=
    fun s _ => (hφd s).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope
    (fun s : ℝ => W (x + s • v) - κ * ‖v‖ ^ 2 / 2 * s ^ 2)
    (fun s : ℝ => fderiv ℝ W (x + s • v) v - κ * ‖v‖ ^ 2 * s) zero_lt_one hcont
    (fun s _ => hφd s)
  have h0 := hmono hξ.1.le
  simp only [zero_smul, add_zero, one_smul, mul_zero, sub_zero] at hξe h0
  nlinarith [hξe, h0]

theorem convex_ineq {U : E k → ℝ} (hU : ContDiff ℝ 2 U) {lam : ℝ}
    (h : ∀ x v, lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x v v) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (x y : E k) :
    U ((1 - t) • x + t • y) + lam * (t * (1 - t)) / 2 * ‖x - y‖ ^ 2 ≤ (1 - t) * U x + t * U y := by
  set z := (1 - t) • x + t • y with hz
  have hx : x - z = t • (x - y) := by rw [hz]; module
  have hy : y - z = (1 - t) • (y - x) := by rw [hz]; module
  have h1 := tangent_ineq hU h z x
  have h2 := tangent_ineq hU h z y
  rw [hx, norm_smul, mul_pow] at h1
  rw [hy, norm_smul, mul_pow, norm_sub_rev y x] at h2
  have e1 : ‖t‖ ^ 2 = t ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have e2 : ‖1 - t‖ ^ 2 = (1 - t) ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have e3 : fderiv ℝ U z (y - x) = - fderiv ℝ U z (x - y) := by rw [← neg_sub, map_neg]
  rw [e1, map_smul, smul_eq_mul] at h1
  rw [e2, map_smul, smul_eq_mul, e3] at h2
  have := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 ht1)
  have := mul_le_mul_of_nonneg_left h2 ht0
  nlinarith

theorem integrable_exp_neg_of_convex {U : E k → ℝ} (hU : ContDiff ℝ 2 U) {lam : ℝ} (hlam : 0 < lam)
    (h : ∀ x v, lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x v v) :
    Integrable (fun x => Real.exp (-U x)) := by
  set C := ‖fderiv ℝ U 0‖ with hC
  have hgauss : Integrable (fun y : E k => Real.exp (-(lam / 4) * ‖y‖ ^ 2)) := by
    have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E k)
      (b := ((lam / 4 : ℝ) : ℂ)) (by simpa using hlam) 0 0
    have h2 := this.norm
    refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [zero_mul, add_zero]
    rw [show (-((lam / 4 : ℝ) : ℂ) * (‖y‖ : ℂ) ^ 2) = ((-(lam / 4) * ‖y‖ ^ 2 : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_exp, Complex.ofReal_re]
  refine (hgauss.const_mul (Real.exp (-U 0 + C ^ 2 / lam))).mono'
    (Real.measurable_exp.comp hU.continuous.measurable.neg).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 := tangent_ineq hU h 0 y
  simp only [sub_zero] at h1
  have h2 : - fderiv ℝ U 0 y ≤ C * ‖y‖ := by
    have h5 := (fderiv ℝ U 0).le_opNorm y
    rw [Real.norm_eq_abs] at h5
    have h6 := neg_abs_le (fderiv ℝ U 0 y)
    linarith
  have h3 : C * ‖y‖ ≤ lam / 4 * ‖y‖ ^ 2 + C ^ 2 / lam := by
    have : 0 ≤ (lam / 2 * ‖y‖ - C) ^ 2 / lam := by positivity
    have e : (lam / 2 * ‖y‖ - C) ^ 2 / lam = lam / 4 * ‖y‖ ^ 2 - C * ‖y‖ + C ^ 2 / lam := by
      field_simp; ring
    linarith
  nlinarith

/-- The Prekopa-Leindler inequality (Lebesgue measure on `ℝ^k`), in the form used by the
Bobkov-Ledoux argument: nonnegative measurable integrable `f g h` with
`h((1-t)x+ty) ≥ f(x)^(1-t) g(y)^t` satisfy `(∫f)^(1-t) (∫g)^t ≤ ∫h`. -/
def PrekopaLeindlerStatement (k : ℕ) : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 → ∀ f g h : E k → ℝ, Measurable f → Measurable g → Measurable h →
    (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) → (∀ x, 0 ≤ h x) →
    (∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) →
    Integrable f → Integrable g → Integrable h →
    (∫ x, f x) ^ (1 - t) * (∫ x, g x) ^ t ≤ ∫ x, h x

theorem integrable_of_le_const_mul {U : E k → ℝ} (hint : Integrable (fun x => Real.exp (-U x)))
    {F : E k → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x) {C : ℝ}
    (hC : ∀ x, F x ≤ C * Real.exp (-U x)) : Integrable F :=
  (hint.const_mul C).mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact hC x)

theorem real_aux {lam M θ t p r : ℝ} (hlam : 0 < lam) (hθ : 0 < θ) (ht : 0 ≤ t)
    (ha : lam * θ ≤ lam * (1 - t) - M * t) :
    t * p * r + M * t ^ 2 / 2 * r ^ 2 - lam * (t * (1 - t)) / 2 * r ^ 2 ≤ t * (p ^ 2 / (2 * lam * θ)) := by
  set a := lam * (1 - t) - M * t with hadef
  have hapos : 0 < a := lt_of_lt_of_le (by positivity) ha
  have h1 : p * r - a / 2 * r ^ 2 ≤ p ^ 2 / (2 * a) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (a * r - p)]
  have h2 : p ^ 2 / (2 * a) ≤ p ^ 2 / (2 * lam * θ) := by
    apply div_le_div_of_nonneg_left (sq_nonneg p) (by positivity)
    nlinarith
  have h3 : t * p * r + M * t ^ 2 / 2 * r ^ 2 - lam * (t * (1 - t)) / 2 * r ^ 2
      = t * (p * r - a / 2 * r ^ 2) := by rw [hadef]; ring
  rw [h3]
  exact mul_le_mul_of_nonneg_left (h1.trans h2) ht

theorem pl_core (hPL : PrekopaLeindlerStatement k) {U : E k → ℝ} (hU : ContDiff ℝ 2 U) {lam : ℝ}
    (hlam : 0 < lam) (hconv : ∀ x v, lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x v v)
    {ψ : E k → ℝ} (hψ : ContDiff ℝ 2 ψ) {K L M θ t : ℝ} (hK : ∀ x, |ψ x| ≤ K)
    (hL : ∀ x, ‖fderiv ℝ ψ x‖ ≤ L) (hM : ∀ x v, fderiv ℝ (fderiv ℝ ψ) x v v ≤ M * ‖v‖ ^ 2)
    (hθ : 0 < θ) (ht0 : 0 < t) (ht1 : t < 1) (ha : lam * θ ≤ lam * (1 - t) - M * t) :
    (∫ x, Real.exp (ψ x / (1 - t) - U x)) ^ (1 - t) * (∫ x, Real.exp (-U x)) ^ t ≤
      ∫ x, Real.exp (ψ x + t * (‖fderiv ℝ ψ x‖ ^ 2 / (2 * lam * θ)) - U x) := by
  have hint := integrable_exp_neg_of_convex hU hlam hconv
  have hUm : Measurable U := hU.continuous.measurable
  have hψm : Measurable ψ := hψ.continuous.measurable
  have hDm : Measurable fun x => ‖fderiv ℝ ψ x‖ :=
    (hψ.continuous_fderiv (by norm_num)).norm.measurable
  have h1t : 0 < 1 - t := sub_pos.2 ht1
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  refine hPL t ht0 ht1 _ _ _ ?_ ?_ ?_ (fun x => (Real.exp_pos _).le) (fun x => (Real.exp_pos _).le)
    (fun x => (Real.exp_pos _).le) ?_ ?_ hint ?_
  · exact Real.measurable_exp.comp ((hψm.div_const _).sub hUm)
  · exact Real.measurable_exp.comp hUm.neg
  · exact Real.measurable_exp.comp ((hψm.add (measurable_const.mul ((hDm.pow_const 2).div_const _))).sub hUm)
  · intro x y
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    set z := (1 - t) • x + t • y with hz
    have hc := convex_ineq hU hconv ht0.le ht1.le x y
    have hx : x - z = t • (x - y) := by rw [hz]; module
    have hT := tangent_ineq (W := fun w => -ψ w) hψ.neg (κ := -M) (fun x v => by
      have := hM x v
      have e : fderiv ℝ (fderiv ℝ fun w => -ψ w) x v v = - fderiv ℝ (fderiv ℝ ψ) x v v := by
        have e1 : fderiv ℝ (fun w => -ψ w) = fun w => - fderiv ℝ ψ w := by
          funext w; exact fderiv_fun_neg (f := ψ) (x := w)
        rw [e1, fderiv_fun_neg]; rfl
      rw [e]; linarith) z x
    have hfd : fderiv ℝ (fun w => -ψ w) z (x - z) = - fderiv ℝ ψ z (x - z) := by
      rw [fderiv_fun_neg]; rfl
    rw [hfd, hx, map_smul, smul_eq_mul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hT
    have hbd : fderiv ℝ ψ z (x - y) ≤ ‖fderiv ℝ ψ z‖ * ‖x - y‖ := by
      refine (le_abs_self _).trans ?_
      have := (fderiv ℝ ψ z).le_opNorm (x - y)
      rwa [Real.norm_eq_abs] at this
    have haux := real_aux (M := M) (θ := θ) (t := t) (p := ‖fderiv ℝ ψ z‖) (r := ‖x - y‖) hlam hθ
      ht0.le ha
    have e2 : (ψ x / (1 - t) - U x) * (1 - t) + -U y * t = ψ x - ((1 - t) * U x + t * U y) := by
      field_simp; ring
    rw [e2]
    have hmul : t * (fderiv ℝ ψ z (x - y)) ≤ t * (‖fderiv ℝ ψ z‖ * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left hbd ht0.le
    nlinarith [hT, hc, haux, hmul]
  · refine integrable_of_le_const_mul hint (U := U) (Real.measurable_exp.comp ((hψm.div_const _).sub hUm))
      (fun x => (Real.exp_pos _).le) (C := Real.exp (K / (1 - t))) fun x => ?_
    rw [sub_eq_add_neg, Real.exp_add]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    exact div_le_div_of_nonneg_right (le_of_abs_le (hK x)) h1t.le
  · refine integrable_of_le_const_mul hint (U := U)
      (Real.measurable_exp.comp ((hψm.add (measurable_const.mul ((hDm.pow_const 2).div_const _))).sub hUm))
      (fun x => (Real.exp_pos _).le) (C := Real.exp (K + t * (L ^ 2 / (2 * lam * θ)))) fun x => ?_
    rw [sub_eq_add_neg, Real.exp_add]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    have : ‖fderiv ℝ ψ x‖ ^ 2 / (2 * lam * θ) ≤ L ^ 2 / (2 * lam * θ) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hL x) 2) (by positivity)
    nlinarith [le_of_abs_le (hK x), mul_le_mul_of_nonneg_left this ht0.le]

theorem integral_gibbs {U : E k → ℝ} (hUm : Measurable U) (F : E k → ℝ) :
    ∫ x, F x ∂(DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U) =
      (∫ x, Real.exp (-U x) * F x) / ∫ x, Real.exp (-U x) := by
  unfold DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs
  have hm : Measurable fun x => ENNReal.ofReal (Real.exp (-U x) / ∫ y, Real.exp (-U y)) :=
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp hUm.neg).div_const _)
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  rw [← integral_div]
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  ring

theorem pl_core_gibbs (hPL : PrekopaLeindlerStatement k) {U : E k → ℝ} (hU : ContDiff ℝ 2 U)
    {lam : ℝ} (hlam : 0 < lam) (hconv : ∀ x v, lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x v v)
    {ψ : E k → ℝ} (hψ : ContDiff ℝ 2 ψ) {K L M θ t : ℝ} (hK : ∀ x, |ψ x| ≤ K)
    (hL : ∀ x, ‖fderiv ℝ ψ x‖ ≤ L) (hM : ∀ x v, fderiv ℝ (fderiv ℝ ψ) x v v ≤ M * ‖v‖ ^ 2)
    (hθ : 0 < θ) (ht0 : 0 < t) (ht1 : t < 1) (ha : lam * θ ≤ lam * (1 - t) - M * t) :
    (∫ x, Real.exp (ψ x / (1 - t)) ∂(DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U)) ^ (1 - t) ≤
      ∫ x, Real.exp (ψ x + t * (‖fderiv ℝ ψ x‖ ^ 2 / (2 * lam * θ)))
        ∂(DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U) := by
  have hmain := pl_core hPL hU hlam hconv hψ hK hL hM hθ ht0 ht1 ha
  have hint := integrable_exp_neg_of_convex hU hlam hconv
  have hZ := DGPS.FiniteN.Tools.StrongConvexityLSI.integral_exp_neg_pos hint
  have hUm : Measurable U := hU.continuous.measurable
  set Z := ∫ x, Real.exp (-U x) with hZdef
  simp only [integral_gibbs hUm]
  have e1 : ∀ c : ℝ, ∀ x, Real.exp (c - U x) = Real.exp (-U x) * Real.exp c := fun c x => by
    rw [← Real.exp_add]; congr 1; ring
  simp_rw [e1] at hmain
  set A := ∫ x, Real.exp (-U x) * Real.exp (ψ x / (1 - t)) with hA
  set B := ∫ x, Real.exp (-U x) * Real.exp (ψ x + t * (‖fderiv ℝ ψ x‖ ^ 2 / (2 * lam * θ)))
    with hB
  have hA0 : 0 ≤ A := integral_nonneg fun x => by positivity
  rw [Real.div_rpow hA0 hZ.le]
  have hZZ : Z ^ (1 - t) * Z ^ t = Z := by
    rw [← Real.rpow_add hZ]; simp
  have hZp : 0 < Z ^ (1 - t) := Real.rpow_pos_of_pos hZ _
  have hZt : 0 < Z ^ t := Real.rpow_pos_of_pos hZ _
  rw [div_le_div_iff₀ hZp hZ]
  have : A ^ (1 - t) * Z ^ t ≤ B := hmain
  calc A ^ (1 - t) * Z = A ^ (1 - t) * (Z ^ (1 - t) * Z ^ t) := by rw [hZZ]
    _ = (A ^ (1 - t) * Z ^ t) * Z ^ (1 - t) := by ring
    _ ≤ B * Z ^ (1 - t) := mul_le_mul_of_nonneg_right this hZp.le

theorem deriv_le_of_le {A B : ℝ → ℝ} {A' B' : ℝ} (hA : HasDerivAt A A' 0) (hB : HasDerivAt B B' 0)
    (h0 : A 0 = B 0) {t0 : ℝ} (ht0 : 0 < t0) (h : ∀ t, 0 < t → t < t0 → A t ≤ B t) : A' ≤ B' := by
  have h1 := hA.tendsto_slope_zero_right
  have h2 := hB.tendsto_slope_zero_right
  have h3 := h2.sub h1
  refine sub_nonneg.1 (ge_of_tendsto h3 ?_)
  have : Set.Ioo (0 : ℝ) t0 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT ht0
  filter_upwards [this] with t ht
  simp only [zero_add, smul_eq_mul]
  rw [← mul_sub, ← sub_sub_sub_cancel_right]
  have := h t ht.1 ht.2
  rw [← h0]
  exact mul_nonneg (inv_nonneg.2 ht.1.le) (by linarith)

theorem hasDerivAt_exp_div {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {ψ : α → ℝ} (hψ : Measurable ψ) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ x, |ψ x| ≤ K) :
    HasDerivAt (fun t : ℝ => ∫ x, Real.exp (ψ x / (1 - t)) ∂μ)
      (∫ x, ψ x * Real.exp (ψ x) ∂μ) 0 := by
  have hs : Set.Ioo (-(1 / 2) : ℝ) (1 / 2) ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hmeas : ∀ t : ℝ, Measurable fun x => Real.exp (ψ x / (1 - t)) := fun t =>
    Real.measurable_exp.comp (hψ.div_const _)
  have hbd : ∀ t ∈ Set.Ioo (-(1 / 2) : ℝ) (1 / 2), ∀ x,
      ‖ψ x / (1 - t) ^ 2 * Real.exp (ψ x / (1 - t))‖ ≤ 4 * K * Real.exp (2 * K) := by
    intro t ht x
    obtain ⟨h1, h2⟩ := ht
    have hpos : 0 < 1 - t := by linarith
    have hge : 1 / 2 ≤ 1 - t := by linarith
    have hψK := hK x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_div,
      abs_of_pos (by positivity : 0 < (1 - t) ^ 2)]
    have e1 : |ψ x| / (1 - t) ^ 2 ≤ 4 * K := by
      rw [div_le_iff₀ (by positivity)]
      have hsq : 1 / 4 ≤ (1 - t) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq hK0]
    have e2 : Real.exp (ψ x / (1 - t)) ≤ Real.exp (2 * K) := by
      refine Real.exp_le_exp.2 ?_
      have : ψ x / (1 - t) ≤ |ψ x| / (1 - t) := div_le_div_of_nonneg_right (le_abs_self _) hpos.le
      have : |ψ x| / (1 - t) ≤ 2 * K := by
        rw [div_le_iff₀ hpos]; nlinarith [abs_nonneg (ψ x)]
      linarith
    exact mul_le_mul e1 e2 (Real.exp_pos _).le (by positivity)
  have hint0 : Integrable (fun x => Real.exp (ψ x / (1 - 0))) μ := by
    refine Integrable.of_bound (hmeas 0).aestronglyMeasurable (Real.exp K)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by simpa using le_of_abs_le (hK x))
  have hF'meas : AEStronglyMeasurable (fun x => ψ x / (1 - (0 : ℝ)) ^ 2 * Real.exp (ψ x / (1 - 0))) μ :=
    ((hψ.div_const _).mul (hmeas 0)).aestronglyMeasurable
  have hdiff : ∀ x, ∀ t ∈ Set.Ioo (-(1 / 2) : ℝ) (1 / 2),
      HasDerivAt (fun t : ℝ => Real.exp (ψ x / (1 - t)))
        (ψ x / (1 - t) ^ 2 * Real.exp (ψ x / (1 - t))) t := by
    intro x t ht
    have hpos : 1 - t ≠ 0 := by
      have := ht.2; intro h; linarith
    have h1 : HasDerivAt (fun t : ℝ => ψ x / (1 - t)) (ψ x / (1 - t) ^ 2) t := by
      have := (hasDerivAt_const t (ψ x)).div ((hasDerivAt_id t).const_sub 1) hpos
      exact this.congr_deriv (by simp)
    exact (h1.exp).congr_deriv (by ring)
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun t x => Real.exp (ψ x / (1 - t)))
    (F' := fun t x => ψ x / (1 - t) ^ 2 * Real.exp (ψ x / (1 - t)))
    (bound := fun _ => 4 * K * Real.exp (2 * K)) hs
    (Filter.Eventually.of_forall fun t => (hmeas t).aestronglyMeasurable) hint0 hF'meas
    (Filter.Eventually.of_forall fun x t ht => hbd t ht x) (integrable_const _)
    (Filter.Eventually.of_forall hdiff)).2
  simpa using key

theorem hasDerivAt_exp_add {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {ψ H : α → ℝ} (hψ : Measurable ψ) (hH : Measurable H) {K Hb : ℝ} (hK : ∀ x, |ψ x| ≤ K)
    (hH0 : ∀ x, 0 ≤ H x) (hHb : ∀ x, H x ≤ Hb) (hHb0 : 0 ≤ Hb) :
    HasDerivAt (fun t : ℝ => ∫ x, Real.exp (ψ x + t * H x) ∂μ)
      (∫ x, H x * Real.exp (ψ x) ∂μ) 0 := by
  have hs : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hmeas : ∀ t : ℝ, Measurable fun x => Real.exp (ψ x + t * H x) := fun t =>
    Real.measurable_exp.comp (hψ.add (measurable_const.mul hH))
  have hbd : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ∀ x,
      ‖H x * Real.exp (ψ x + t * H x)‖ ≤ Hb * Real.exp (K + Hb) := by
    intro t ht x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (hH0 x)]
    refine mul_le_mul (hHb x) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hHb0
    have h1 := le_of_abs_le (hK x)
    have h2 : t * H x ≤ Hb := by
      calc t * H x ≤ 1 * H x := mul_le_mul_of_nonneg_right ht.2.le (hH0 x)
        _ ≤ Hb := by linarith [hHb x]
    linarith
  have hint0 : Integrable (fun x => Real.exp (ψ x + 0 * H x)) μ := by
    refine Integrable.of_bound (hmeas 0).aestronglyMeasurable (Real.exp K)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by simpa using le_of_abs_le (hK x))
  have hF'meas : AEStronglyMeasurable (fun x => H x * Real.exp (ψ x + 0 * H x)) μ :=
    (hH.mul (hmeas 0)).aestronglyMeasurable
  have hdiff : ∀ x, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun t : ℝ => Real.exp (ψ x + t * H x))
        (H x * Real.exp (ψ x + t * H x)) t := by
    intro x t _
    have h1 : HasDerivAt (fun t : ℝ => ψ x + t * H x) (H x) t := by
      simpa using ((hasDerivAt_id t).mul_const (H x)).const_add (ψ x)
    exact (h1.exp).congr_deriv (by ring)
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun t x => Real.exp (ψ x + t * H x))
    (F' := fun t x => H x * Real.exp (ψ x + t * H x))
    (bound := fun _ => Hb * Real.exp (K + Hb)) hs
    (Filter.Eventually.of_forall fun t => (hmeas t).aestronglyMeasurable) hint0 hF'meas
    (Filter.Eventually.of_forall fun x t ht => hbd t ht x) (integrable_const _)
    (Filter.Eventually.of_forall hdiff)).2
  simpa using key

theorem ent_le_of_pl_family {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {ψ H : α → ℝ} (hψ : Measurable ψ) (hH : Measurable H) {K Hb : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, |ψ x| ≤ K) (hH0 : ∀ x, 0 ≤ H x) (hHb : ∀ x, H x ≤ Hb) (hHb0 : 0 ≤ Hb)
    {t0 : ℝ} (ht0 : 0 < t0)
    (hfam : ∀ t : ℝ, 0 < t → t < t0 →
      (∫ x, Real.exp (ψ x / (1 - t)) ∂μ) ^ (1 - t) ≤ ∫ x, Real.exp (ψ x + t * H x) ∂μ) :
    ∫ x, ψ x * Real.exp (ψ x) ∂μ - (∫ x, Real.exp (ψ x) ∂μ) * Real.log (∫ x, Real.exp (ψ x) ∂μ)
      ≤ ∫ x, H x * Real.exp (ψ x) ∂μ := by
  have hA := hasDerivAt_exp_div (μ := μ) hψ hK0 hK
  have hB := hasDerivAt_exp_add (μ := μ) hψ hH hK hH0 hHb hHb0
  set m := ∫ x, Real.exp (ψ x) ∂μ with hm
  have hmpos : 0 < m := by
    rw [hm, integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le)]
    · have : Function.support (fun x => Real.exp (ψ x)) = Set.univ :=
        Set.eq_univ_of_forall fun x => (Real.exp_pos _).ne'
      rw [this]; simp
    · refine Integrable.of_bound (Real.measurable_exp.comp hψ).aestronglyMeasurable (Real.exp K)
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (le_of_abs_le (hK x))
  have ha0 : (∫ x, Real.exp (ψ x / (1 - 0)) ∂μ) = m := by simp [hm]
  have hA' := hA.rpow ((hasDerivAt_id (0:ℝ)).const_sub 1) (by rw [ha0]; exact hmpos)
  have hb0 : (∫ x, Real.exp (ψ x + 0 * H x) ∂μ) = m := by simp [hm]
  have := deriv_le_of_le hA' hB (by simp only [ha0, hb0]; simp) ht0 (fun t h1 h2 => hfam t h1 h2)
  simp only [ha0] at this
  simpa [sub_eq_add_neg, add_comm, mul_comm] using this

theorem ent_core (hPL : PrekopaLeindlerStatement k) {U : E k → ℝ} (hU : ContDiff ℝ 2 U)
    {lam : ℝ} (hlam : 0 < lam) (hconv : ∀ x v, lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x v v)
    {ψ : E k → ℝ} (hψ : ContDiff ℝ 2 ψ) {K L M : ℝ} (hK : ∀ x, |ψ x| ≤ K)
    (hL : ∀ x, ‖fderiv ℝ ψ x‖ ≤ L) (hM0 : 0 ≤ M)
    (hM : ∀ x v, fderiv ℝ (fderiv ℝ ψ) x v v ≤ M * ‖v‖ ^ 2) :
    ∫ x, ψ x * Real.exp (ψ x) ∂(DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U) -
        (∫ x, Real.exp (ψ x) ∂(DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U)) *
          Real.log (∫ x, Real.exp (ψ x) ∂(DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U))
      ≤ ∫ x, (‖fderiv ℝ ψ x‖ ^ 2 / (2 * lam)) * Real.exp (ψ x)
          ∂(DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U) := by
  have := DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs_isProbabilityMeasure
      (integrable_exp_neg_of_convex hU hlam hconv)
  set μ := DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U with hμ
  have hψm : Measurable ψ := hψ.continuous.measurable
  have hDm : Measurable fun x => ‖fderiv ℝ ψ x‖ :=
    (hψ.continuous_fderiv (by norm_num)).norm.measurable
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  set c : ℝ := ∫ x, (‖fderiv ℝ ψ x‖ ^ 2 / (2 * lam)) * Real.exp (ψ x) ∂μ with hc
  set LHS := ∫ x, ψ x * Real.exp (ψ x) ∂μ - (∫ x, Real.exp (ψ x) ∂μ) *
    Real.log (∫ x, Real.exp (ψ x) ∂μ) with hLHS
  have hθ : ∀ θ : ℝ, 0 < θ → θ < 1 → LHS ≤ c / θ := by
    intro θ hθ0 hθ1
    have ht0 : 0 < lam * (1 - θ) / (lam + M) := by
      have : 0 < 1 - θ := by linarith
      positivity
    have := ent_le_of_pl_family (μ := μ) (ψ := ψ)
      (H := fun x => ‖fderiv ℝ ψ x‖ ^ 2 / (2 * lam * θ)) hψm
      ((hDm.pow_const 2).div_const _) hK0 hK (fun x => by positivity)
      (fun x => div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hL x) 2)
        (by positivity)) (Hb := L ^ 2 / (2 * lam * θ)) (by positivity) ht0 ?_
    · refine this.trans (le_of_eq ?_)
      rw [hc, ← integral_div]
      congr 1
      funext x
      field_simp
    · intro t h1 h2
      have h3 : t * (lam + M) < lam * (1 - θ) := by
        rw [lt_div_iff₀ (by positivity)] at h2; exact h2
      have ht1 : t < 1 := by nlinarith
      exact pl_core_gibbs hPL hU hlam hconv hψ hK hL hM hθ0 h1 ht1 (by nlinarith)
  have hlim : Tendsto (fun θ : ℝ => c / θ) (𝓝[<] 1) (𝓝 c) := by
    have : Tendsto (fun θ : ℝ => c / θ) (𝓝 1) (𝓝 (c / 1)) :=
      tendsto_const_nhds.div tendsto_id one_ne_zero
    rw [div_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with θ hθ'
  exact hθ θ hθ'.1 hθ'.2

theorem logsq_contDiff {f : E k → ℝ} (hf : ContDiff ℝ ∞ f) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (fun x => Real.log (f x ^ 2 + ε)) :=
  ((hf.pow 2).add contDiff_const).log (fun x => by positivity)

theorem logsq_bounds {f : E k → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {ε : ℝ}
    (hε : 0 < ε) :
    (∃ K, ∀ x, |Real.log (f x ^ 2 + ε)| ≤ K) ∧
    (∃ L, ∀ x, ‖fderiv ℝ (fun x => Real.log (f x ^ 2 + ε)) x‖ ≤ L) ∧
    (∃ M, 0 ≤ M ∧ ∀ x v, fderiv ℝ (fderiv ℝ (fun x => Real.log (f x ^ 2 + ε))) x v v ≤ M * ‖v‖ ^ 2) := by
  set ψ : E k → ℝ := fun x => Real.log (f x ^ 2 + ε) with hψ
  have hψd : ContDiff ℝ ∞ ψ := logsq_contDiff hf hε
  set χ : E k → ℝ := fun x => ψ x - Real.log ε with hχ
  have hχd : ContDiff ℝ ∞ χ := hψd.sub contDiff_const
  have hχc : HasCompactSupport χ := by
    have := hc.comp_left (g := fun s : ℝ => Real.log (s ^ 2 + ε) - Real.log ε) (by simp)
    exact this
  have hdχ : fderiv ℝ χ = fderiv ℝ ψ := by
    funext x; exact fderiv_sub_const (f := ψ) (x := x) (Real.log ε)
  have hddχ : fderiv ℝ (fderiv ℝ χ) = fderiv ℝ (fderiv ℝ ψ) := by rw [hdχ]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hχd.continuous.bounded_above_of_compact_support hχc
    refine ⟨C + |Real.log ε|, fun x => ?_⟩
    have h1 := hC x
    rw [Real.norm_eq_abs] at h1
    have : ψ x = χ x + Real.log ε := by simp [hχ]
    show |ψ x| ≤ _
    rw [this]
    calc |χ x + Real.log ε| ≤ |χ x| + |Real.log ε| := abs_add_le _ _
      _ ≤ _ := by linarith
  · have h1 : Continuous (fderiv ℝ χ) := hχd.continuous_fderiv (by simp)
    obtain ⟨C, hC⟩ := (hχc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous h1
    exact ⟨C, fun x => by rw [← hdχ]; exact hC x⟩
  · have hc1 : HasCompactSupport (fderiv ℝ χ) := hχc.fderiv (𝕜 := ℝ)
    have h1c : ContDiff ℝ 1 (fderiv ℝ χ) := hχd.fderiv_right (by simp)
    obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc1 h1c (by simp)
    refine ⟨(C : ℝ), C.2, fun x v => ?_⟩
    rw [← hddχ]
    have h2 : ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ C := norm_fderiv_le_of_lipschitz ℝ hC
    have h3 : ‖fderiv ℝ (fderiv ℝ χ) x v v‖ ≤ ‖fderiv ℝ (fderiv ℝ χ) x‖ * ‖v‖ * ‖v‖ :=
      ((fderiv ℝ (fderiv ℝ χ) x v).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ χ) x).le_opNorm v) (norm_nonneg _))
    calc fderiv ℝ (fderiv ℝ χ) x v v ≤ ‖fderiv ℝ (fderiv ℝ χ) x v v‖ := Real.le_norm_self _
      _ ≤ ‖fderiv ℝ (fderiv ℝ χ) x‖ * ‖v‖ * ‖v‖ := h3
      _ ≤ (C : ℝ) * ‖v‖ * ‖v‖ := by gcongr
      _ = (C : ℝ) * ‖v‖ ^ 2 := by ring

theorem fderiv_logsq_bound {f : E k → ℝ} (hf : ContDiff ℝ ∞ f) {ε : ℝ} (hε : 0 < ε) (x : E k) :
    ‖fderiv ℝ (fun x => Real.log (f x ^ 2 + ε)) x‖ ^ 2 * (f x ^ 2 + ε) ≤
      4 * ‖fderiv ℝ f x‖ ^ 2 := by
  have hd : DifferentiableAt ℝ f x := (hf.differentiable (by simp)) x
  have h1 : HasFDerivAt (fun x => f x ^ 2 + ε) ((2 * f x) • fderiv ℝ f x) x := by
    have h := (hd.hasFDerivAt.mul hd.hasFDerivAt).add_const ε
    convert h using 1
    · funext y; simp [pow_two, add_comm]
    · ext v; simp; ring
  have hpos : 0 < f x ^ 2 + ε := by positivity
  have h2 := h1.log hpos.ne'
  rw [h2.fderiv, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have e1 : |(f x ^ 2 + ε)⁻¹| = (f x ^ 2 + ε)⁻¹ := abs_of_pos (inv_pos.2 hpos)
  have e2 : |2 * f x| ^ 2 = 4 * f x ^ 2 := by rw [sq_abs]; ring
  rw [e1]
  have : ((f x ^ 2 + ε)⁻¹ * (|2 * f x| * ‖fderiv ℝ f x‖)) ^ 2 * (f x ^ 2 + ε)
      = (4 * f x ^ 2) * ‖fderiv ℝ f x‖ ^ 2 / (f x ^ 2 + ε) := by
    rw [mul_pow, mul_pow, e2]
    field_simp
  rw [this, div_le_iff₀ hpos]
  have := sq_nonneg (‖fderiv ℝ f x‖)
  nlinarith [mul_nonneg this hε.le]

theorem integrable_gradsq {f : E k → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (μ : Measure (E k)) [IsFiniteMeasure μ] :
    Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) μ := by
  have h1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hc1 : HasCompactSupport (fderiv ℝ f) := hc.fderiv (𝕜 := ℝ)
  have hc2 : HasCompactSupport (fun x => ‖fderiv ℝ f x‖ ^ 2) := by
    have := hc1.norm.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
    exact this
  exact (h1.norm.pow 2).integrable_of_hasCompactSupport hc2

theorem integrable_sq_of_compact {f : E k → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (μ : Measure (E k)) [IsFiniteMeasure μ] : Integrable (fun x => f x ^ 2) μ := by
  have hc2 : HasCompactSupport (fun x => f x ^ 2) := by
    have := hc.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
    exact this
  exact (hf.continuous.pow 2).integrable_of_hasCompactSupport hc2

theorem ent_eps (hPL : PrekopaLeindlerStatement k) {U : E k → ℝ} (hU : ContDiff ℝ 2 U)
    {lam : ℝ} (hlam : 0 < lam) (hconv : ∀ x v, lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x v v)
    {f : E k → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∫ x, (f x ^ 2 + ε) * Real.log (f x ^ 2 + ε) ∂(DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U) -
      (∫ x, f x ^ 2 ∂(DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U) + ε) *
        Real.log (∫ x, f x ^ 2 ∂(DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U) + ε)
      ≤ (2 / lam) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U) := by
  have hP := DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs_isProbabilityMeasure
      (integrable_exp_neg_of_convex hU hlam hconv)
  set μ := DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U with hμ
  obtain ⟨⟨K, hK⟩, ⟨L, hL⟩, ⟨M, hM0, hM⟩⟩ := logsq_bounds hf hc hε
  have hψ : ContDiff ℝ 2 (fun x => Real.log (f x ^ 2 + ε)) :=
    (logsq_contDiff hf hε).of_le (by simp)
  have key := ent_core hPL hU hlam hconv hψ hK hL hM0 hM
  have hexp : ∀ x, Real.exp (Real.log (f x ^ 2 + ε)) = f x ^ 2 + ε :=
    fun x => Real.exp_log (by positivity)
  simp_rw [hexp] at key
  have hsq := integrable_sq_of_compact hf hc μ
  have hI : ∫ x, (f x ^ 2 + ε) ∂μ = ∫ x, f x ^ 2 ∂μ + ε := by
    rw [integral_add hsq (integrable_const ε)]; simp
  rw [hI] at key
  have e : ∫ x, (f x ^ 2 + ε) * Real.log (f x ^ 2 + ε) ∂μ
      = ∫ x, Real.log (f x ^ 2 + ε) * (f x ^ 2 + ε) ∂μ := by simp_rw [mul_comm]
  rw [e]
  refine key.trans ?_
  have hg := (integrable_gradsq hf hc μ).const_mul (2 / lam)
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hg
    (Filter.Eventually.of_forall fun x => ?_)
  have h := fderiv_logsq_bound hf hε x
  have hpos : 0 < 2 * lam := by positivity
  show ‖fderiv ℝ (fun x => Real.log (f x ^ 2 + ε)) x‖ ^ 2 / (2 * lam) * (f x ^ 2 + ε) ≤ _
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  have : 2 / lam * ‖fderiv ℝ f x‖ ^ 2 * (2 * lam) = 4 * ‖fderiv ℝ f x‖ ^ 2 := by
    field_simp; ring
  rw [this]; exact h

theorem lsi_real (hPL : PrekopaLeindlerStatement k) {U : E k → ℝ} (hU : ContDiff ℝ 2 U)
    {lam : ℝ} (hlam : 0 < lam) (hconv : ∀ x v, lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x v v)
    {f : E k → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂(DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U) -
      (∫ x, f x ^ 2 ∂(DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U)) *
        Real.log (∫ x, f x ^ 2 ∂(DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U))
      ≤ (2 / lam) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U) := by
  have hP := DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs_isProbabilityMeasure
      (integrable_exp_neg_of_convex hU hlam hconv)
  set μ := DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U with hμ
  set A := ∫ x, f x ^ 2 ∂μ with hA
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hf.continuous
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := B ^ 2 + 1)).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  have hlim1 : Tendsto (fun ε : ℝ => ∫ x, (f x ^ 2 + ε) * Real.log (f x ^ 2 + ε) ∂μ)
      (𝓝[>] 0) (𝓝 (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_
      (integrable_const C) ?_
    · exact Filter.Eventually.of_forall fun ε =>
        (Real.continuous_mul_log.comp ((hf.continuous.pow 2).add_const ε)).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
      refine Filter.Eventually.of_forall fun x => ?_
      have h0 : 0 ≤ f x ^ 2 + ε := by nlinarith [sq_nonneg (f x), hε.1]
      have h1 : f x ^ 2 + ε ≤ B ^ 2 + 1 := by
        have := hB x
        rw [Real.norm_eq_abs] at this
        have : f x ^ 2 ≤ B ^ 2 := by
          have := sq_le_sq' (by linarith [abs_nonneg (f x), neg_abs_le (f x)]) (le_trans (le_abs_self _) this)
          exact this
        linarith [hε.2]
      exact hC _ ⟨h0, h1⟩
    · refine Filter.Eventually.of_forall fun x => ?_
      have : Tendsto (fun ε : ℝ => f x ^ 2 + ε) (𝓝[>] 0) (𝓝 (f x ^ 2)) := by
        have : Tendsto (fun ε : ℝ => f x ^ 2 + ε) (𝓝 0) (𝓝 (f x ^ 2 + 0)) :=
          tendsto_const_nhds.add tendsto_id
        rw [add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      exact (Real.continuous_mul_log.tendsto _).comp this
  have hlim2 : Tendsto (fun ε : ℝ => (A + ε) * Real.log (A + ε)) (𝓝[>] 0)
      (𝓝 (A * Real.log A)) := by
    have : Tendsto (fun ε : ℝ => A + ε) (𝓝[>] 0) (𝓝 A) := by
      have : Tendsto (fun ε : ℝ => A + ε) (𝓝 0) (𝓝 (A + 0)) :=
        tendsto_const_nhds.add tendsto_id
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact (Real.continuous_mul_log.tendsto _).comp this
  refine le_of_tendsto (hlim1.sub hlim2) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact ent_eps hPL hU hlam hconv hf hc hε

end DGPS.FiniteN.Tools.StrongConvexityBobkovLedoux

namespace DGPS.FiniteN.Tools

/-- INF002: the Gibbs law of a `C²`, `λ`-strongly convex potential satisfies the log-Sobolev
inequality with rate `λ`, assuming the Prekopa-Leindler inequality (Bobkov-Ledoux). -/
theorem hasLSIRate_of_stronglyConvex_of_PL {k : ℕ}
    (hPL : StrongConvexityBobkovLedoux.PrekopaLeindlerStatement k)
    {U : EuclideanSpace ℝ (Fin k) → ℝ} (hU : ContDiff ℝ 2 U) {lam : ℝ} (hlam : 0 < lam)
    (hconv : ∀ x v, lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x v v) :
    DGPS.FiniteN.Tools.StrongConvexityLSI.HasLSIRate
      (DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U) lam := by
  have hP := DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs_isProbabilityMeasure
      (StrongConvexityBobkovLedoux.integrable_exp_neg_of_convex hU hlam hconv)
  set μ := DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs U with hμ
  intro f hfT
  obtain ⟨hf, hc⟩ := hfT
  have hsq := StrongConvexityBobkovLedoux.integrable_sq_of_compact hf hc μ
  have hlog : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ := by
    have hc2 : HasCompactSupport (fun x => f x ^ 2 * Real.log (f x ^ 2)) := by
      have := hc.comp_left (g := fun r : ℝ => r ^ 2 * Real.log (r ^ 2)) (by simp)
      exact this
    exact (Real.continuous_mul_log.comp (hf.continuous.pow 2)).integrable_of_hasCompactSupport hc2
  rw [DGPS.homogeneousEntropy_eq_formula (Filter.Eventually.of_forall fun x => sq_nonneg (f x))
    hsq hlog]
  have hg : ∫⁻ x, DGPS.FiniteN.Tools.StrongConvexityLSI.gradSq f x ∂μ
      = ENNReal.ofReal (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal (StrongConvexityBobkovLedoux.integrable_gradsq hf hc μ)
      (Filter.Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    unfold DGPS.FiniteN.Tools.StrongConvexityLSI.gradSq
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [hg, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal
    (StrongConvexityBobkovLedoux.lsi_real hPL hU hlam hconv hf hc)

end DGPS.FiniteN.Tools
