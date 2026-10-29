import DGPS.Circle.StationaryFlux
import DGPS.Examples.SixthOrderCentering
import DGPS.Examples.PolynomialEquilibrium
import DGPS.Examples.PolynomialExactGap

/-!
# Polynomial centered residual (EX057)

For the polynomial equilibrium density `qhat = density_EX054 h (root_EX054 h)` and the feature
`phi = sqrt 2 * (P_h - qhat(P_h))`, the residual `(Ahat - 4) phi` with `Ahat = -L_qhat` is
qhat-centered and has `C^k` norm `O(h)` for each fixed `k`.  The exact closed form is
`sqrt 2 * (h cos 3t - (h^2/6) cos 2t + h^2/6 + 4 mu_h(P_h)) + sqrt 2 * s * (P_h')^2`
with `s = root_EX054 h = O(h^6)`.
-/

open MeasureTheory Real Filter Topology Set
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments DGPS.Circle.StationaryFlux
open DGPS.Examples.PolynomialSpecies DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialCenteredResidual

/-! ### Real-line trigonometric jets -/

/-- Five-term cosine polynomial on the real line. -/
noncomputable def trig5_EX057 (a0 a1 a2 a3 a4 t : ℝ) : ℝ :=
  a0 + a1 * Real.cos t + a2 * Real.cos (2 * t) + a3 * Real.cos (3 * t) + a4 * Real.cos (4 * t)

/-- The `j`-th derivative of `t ↦ a cos (n t)` is `a n^j cos (n t + j π/2)`. -/
noncomputable def termD_EX057 (a n : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  a * n ^ j * Real.cos (n * t + (j : ℝ) * π / 2)

noncomputable def jet_EX057 (a0 a1 a2 a3 a4 : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  termD_EX057 a0 0 j t + termD_EX057 a1 1 j t + termD_EX057 a2 2 j t +
    termD_EX057 a3 3 j t + termD_EX057 a4 4 j t

theorem hasDerivAt_termD_EX057 (a n : ℝ) (j : ℕ) (t : ℝ) :
    HasDerivAt (termD_EX057 a n j) (termD_EX057 a n (j + 1) t) t := by
  have h1 : HasDerivAt (fun x : ℝ => n * x + (j : ℝ) * π / 2) n t := by
    simpa using ((hasDerivAt_id' t).const_mul n).add_const ((j : ℝ) * π / 2)
  have h2 := (h1.cos).const_mul (a * n ^ j)
  have hc : Real.cos (n * t + ((j + 1 : ℕ) : ℝ) * π / 2)
      = -Real.sin (n * t + (j : ℝ) * π / 2) := by
    rw [← Real.cos_add_pi_div_two]
    congr 1
    push_cast
    ring
  have key : termD_EX057 a n (j + 1) t = a * n ^ j * (-Real.sin (n * t + (j : ℝ) * π / 2) * n) := by
    unfold termD_EX057
    rw [hc]
    ring
  rw [key]
  exact h2

theorem iteratedDeriv_trig5_EX057 (a0 a1 a2 a3 a4 : ℝ) (j : ℕ) :
    iteratedDeriv j (trig5_EX057 a0 a1 a2 a3 a4) = jet_EX057 a0 a1 a2 a3 a4 j := by
  induction j with
  | zero =>
    funext t
    simp [trig5_EX057, jet_EX057, termD_EX057]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    apply HasDerivAt.deriv
    exact ((((hasDerivAt_termD_EX057 a0 0 j t).add (hasDerivAt_termD_EX057 a1 1 j t)).add
      (hasDerivAt_termD_EX057 a2 2 j t)).add (hasDerivAt_termD_EX057 a3 3 j t)).add
      (hasDerivAt_termD_EX057 a4 4 j t)

theorem abs_termD_le_EX057 (a n : ℝ) (j : ℕ) (hn0 : 0 ≤ n) (hn4 : n ≤ 4) (t : ℝ) :
    |termD_EX057 a n j t| ≤ |a| * 4 ^ j := by
  unfold termD_EX057
  rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hn0]
  have hp : n ^ j ≤ 4 ^ j := pow_le_pow_left₀ hn0 hn4 j
  have hc : |Real.cos (n * t + (j : ℝ) * π / 2)| ≤ 1 := Real.abs_cos_le_one _
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hp (abs_nonneg a)) hc (abs_nonneg _)
    (by positivity)).trans_eq (mul_one _)

theorem abs_jet_le_EX057 (a0 a1 a2 a3 a4 : ℝ) (j : ℕ) (t : ℝ) :
    |jet_EX057 a0 a1 a2 a3 a4 j t| ≤
      |a0| * 4 ^ j + |a1| * 4 ^ j + |a2| * 4 ^ j + |a3| * 4 ^ j + |a4| * 4 ^ j := by
  unfold jet_EX057
  have h0 := abs_termD_le_EX057 a0 0 j le_rfl (by norm_num) t
  have h1 := abs_termD_le_EX057 a1 1 j (by norm_num) (by norm_num) t
  have h2 := abs_termD_le_EX057 a2 2 j (by norm_num) (by norm_num) t
  have h3 := abs_termD_le_EX057 a3 3 j (by norm_num) (by norm_num) t
  have h4 := abs_termD_le_EX057 a4 4 j (by norm_num) (by norm_num) t
  have e1 := abs_add_le (termD_EX057 a0 0 j t + termD_EX057 a1 1 j t + termD_EX057 a2 2 j t +
    termD_EX057 a3 3 j t) (termD_EX057 a4 4 j t)
  have e2 := abs_add_le (termD_EX057 a0 0 j t + termD_EX057 a1 1 j t + termD_EX057 a2 2 j t)
    (termD_EX057 a3 3 j t)
  have e3 := abs_add_le (termD_EX057 a0 0 j t + termD_EX057 a1 1 j t) (termD_EX057 a2 2 j t)
  have e4 := abs_add_le (termD_EX057 a0 0 j t) (termD_EX057 a1 1 j t)
  linarith

/-! ### Trigonometric identities for the closed form -/

noncomputable def Pd_EX057 (h x : ℝ) : ℝ := -2 * Real.sin (2 * x) + h / 3 * Real.sin x

noncomputable def Pdd_EX057 (h x : ℝ) : ℝ := -4 * Real.cos (2 * x) + h / 3 * Real.cos x

theorem trig_A_EX057 (h t : ℝ) :
    h * Real.sin t * Pd_EX057 h t + h * Real.cos t
      = h * Real.cos (3 * t) - h ^ 2 / 6 * Real.cos (2 * t) + h ^ 2 / 6 := by
  unfold Pd_EX057
  rw [Real.sin_two_mul, Real.cos_two_mul, Real.cos_three_mul]
  linear_combination (-4 * h * Real.cos t + h ^ 2 / 3) * Real.sin_sq_add_cos_sq t

theorem trig_B_EX057 (h t : ℝ) :
    Pd_EX057 h t ^ 2
      = 2 - 2 * Real.cos (4 * t) - 2 * h / 3 * Real.cos t + 2 * h / 3 * Real.cos (3 * t)
        + h ^ 2 / 18 - h ^ 2 / 18 * Real.cos (2 * t) := by
  have c4 : Real.cos (4 * t) = 2 * (2 * Real.cos t ^ 2 - 1) ^ 2 - 1 := by
    rw [show 4 * t = 2 * (2 * t) by ring, Real.cos_two_mul, Real.cos_two_mul]
  unfold Pd_EX057
  rw [c4, Real.sin_two_mul, Real.cos_two_mul, Real.cos_three_mul]
  linear_combination (16 * Real.cos t ^ 2 - 8 * h / 3 * Real.cos t + h ^ 2 / 9) *
    Real.sin_sq_add_cos_sq t

/-! ### Real-line generator data for the root density -/

noncomputable def logW_EX057 (h s x : ℝ) : ℝ :=
  h * Real.cos x - s * (Real.cos (2 * x) - h / 3 * Real.cos x)

noncomputable def Q_EX057 (h s x : ℝ) : ℝ :=
  Real.exp (logW_EX057 h s x) / partition_EX054 h s

noncomputable def Phi_EX057 (h m x : ℝ) : ℝ :=
  Real.sqrt 2 * (Real.cos (2 * x) - h / 3 * Real.cos x - m)

noncomputable def D_EX057 (h s x : ℝ) : ℝ :=
  Q_EX057 h s x * (Real.sqrt 2 * Pd_EX057 h x)

noncomputable def Dd_EX057 (h s x : ℝ) : ℝ :=
  Q_EX057 h s x * (-h * Real.sin x - s * Pd_EX057 h x) * (Real.sqrt 2 * Pd_EX057 h x)
    + Q_EX057 h s x * (Real.sqrt 2 * Pdd_EX057 h x)

theorem hasDerivAt_cos2_EX057 (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos (2 * y)) (-Real.sin (2 * x) * 2) x := by
  have := ((hasDerivAt_id' x).const_mul (2 : ℝ)).cos
  exact this.congr_deriv (by ring)

theorem hasDerivAt_sin2_EX057 (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (2 * y)) (Real.cos (2 * x) * 2) x := by
  have := ((hasDerivAt_id' x).const_mul (2 : ℝ)).sin
  exact this.congr_deriv (by ring)

theorem hasDerivAt_logW_EX057 (h s x : ℝ) :
    HasDerivAt (fun y => logW_EX057 h s y) (-h * Real.sin x - s * Pd_EX057 h x) x := by
  have h1 : HasDerivAt (fun y : ℝ => Real.cos y) (-Real.sin x) x := Real.hasDerivAt_cos x
  have := (h1.const_mul h).sub (((hasDerivAt_cos2_EX057 x).sub (h1.const_mul (h / 3))).const_mul s)
  unfold logW_EX057 Pd_EX057
  exact this.congr_deriv (by ring)

theorem hasDerivAt_Q_EX057 (h s x : ℝ) :
    HasDerivAt (fun y => Q_EX057 h s y) (Q_EX057 h s x * (-h * Real.sin x - s * Pd_EX057 h x)) x := by
  have := ((hasDerivAt_logW_EX057 h s x).exp).div_const (partition_EX054 h s)
  unfold Q_EX057
  exact this.congr_deriv (by ring)

theorem hasDerivAt_Phi_EX057 (h m x : ℝ) :
    HasDerivAt (fun y => Phi_EX057 h m y) (Real.sqrt 2 * Pd_EX057 h x) x := by
  have h1 : HasDerivAt (fun y : ℝ => Real.cos y) (-Real.sin x) x := Real.hasDerivAt_cos x
  have := (((hasDerivAt_cos2_EX057 x).sub (h1.const_mul (h / 3))).sub_const m).const_mul
    (Real.sqrt 2)
  unfold Phi_EX057 Pd_EX057
  exact this.congr_deriv (by ring)

theorem hasDerivAt_sqrtPd_EX057 (h x : ℝ) :
    HasDerivAt (fun y => Real.sqrt 2 * Pd_EX057 h y) (Real.sqrt 2 * Pdd_EX057 h x) x := by
  have h1 : HasDerivAt (fun y : ℝ => Real.sin y) (Real.cos x) x := Real.hasDerivAt_sin x
  have := (((hasDerivAt_sin2_EX057 x).const_mul (-2)).add (h1.const_mul (h / 3))).const_mul
    (Real.sqrt 2)
  unfold Pd_EX057 Pdd_EX057
  exact this.congr_deriv (by ring)

theorem hasDerivAt_D_EX057 (h s x : ℝ) :
    HasDerivAt (fun y => D_EX057 h s y) (Dd_EX057 h s x) x := by
  have := (hasDerivAt_Q_EX057 h s x).mul (hasDerivAt_sqrtPd_EX057 h x)
  unfold D_EX057 Dd_EX057
  exact this

/-! ### Circle objects -/

/-- `qhat_h`: the normalized equilibrium density at the root. -/
noncomputable def qhat_EX057 (h : ℝ) : AngCircle → ℝ := density_EX054 h (root_EX054 h)

/-- `phi_h = sqrt 2 * (P_h - qhat_h(P_h))`. -/
noncomputable def phi_EX057 (h : ℝ) : AngCircle → ℝ :=
  fun θ => Real.sqrt 2 * (feature_EX054 h θ - moment_EX054 h (root_EX054 h))

/-- `Ahat f = -(1/q) (q f')'`, written with the circle derivative. -/
noncomputable def gen_EX057 (q f : AngCircle → ℝ) (θ : AngCircle) : ℝ :=
  -(angDeriv (fun x => q x * angDeriv f x) θ) / q θ

/-- The residual `(Ahat - 4) phi_h`. -/
noncomputable def resid_EX057 (h : ℝ) (θ : AngCircle) : ℝ :=
  gen_EX057 (qhat_EX057 h) (phi_EX057 h) θ - 4 * phi_EX057 h θ

theorem angCos_coe_EX057 (t : ℝ) : angCos (t : AngCircle) = Real.cos t := by
  show angMode 1 (t : AngCircle) = Real.cos t
  rw [angMode_coe]
  simp

theorem feature_coe_EX057 (h t : ℝ) :
    feature_EX054 h (t : AngCircle) = Real.cos (2 * t) - h / 3 * Real.cos t := by
  unfold feature_EX054
  rw [angCos_coe_EX057]
  congr 1

theorem qhat_coe_EX057 (h t : ℝ) :
    qhat_EX057 h (t : AngCircle) = Q_EX057 h (root_EX054 h) t := by
  unfold qhat_EX057 density_EX054 weight_EX054 Q_EX057 logW_EX057
  rw [feature_coe_EX057, angCos_coe_EX057]

theorem phi_coe_EX057 (h t : ℝ) :
    phi_EX057 h (t : AngCircle) = Phi_EX057 h (moment_EX054 h (root_EX054 h)) t := by
  unfold phi_EX057 Phi_EX057
  rw [feature_coe_EX057]

theorem angDeriv_phi_coe_EX057 (h t : ℝ) :
    angDeriv (phi_EX057 h) (t : AngCircle) = Real.sqrt 2 * Pd_EX057 h t := by
  rw [angDeriv_coe]
  have hl : lift (phi_EX057 h) = Phi_EX057 h (moment_EX054 h (root_EX054 h)) := by
    funext x
    exact phi_coe_EX057 h x
  rw [hl]
  exact (hasDerivAt_Phi_EX057 h _ t).deriv

theorem lift_F_EX057 (h : ℝ) :
    lift (fun θ => qhat_EX057 h θ * angDeriv (phi_EX057 h) θ) = D_EX057 h (root_EX054 h) := by
  funext x
  show qhat_EX057 h (x : AngCircle) * angDeriv (phi_EX057 h) (x : AngCircle) = _
  unfold D_EX057
  rw [qhat_coe_EX057, angDeriv_phi_coe_EX057]

theorem resid_coe_div_EX057 (h t : ℝ) :
    resid_EX057 h (t : AngCircle) = -(Dd_EX057 h (root_EX054 h) t) / Q_EX057 h (root_EX054 h) t
      - 4 * Phi_EX057 h (moment_EX054 h (root_EX054 h)) t := by
  have hder : angDeriv (fun θ => qhat_EX057 h θ * angDeriv (phi_EX057 h) θ) (t : AngCircle)
      = Dd_EX057 h (root_EX054 h) t := by
    rw [angDeriv_coe, lift_F_EX057]
    exact (hasDerivAt_D_EX057 h _ t).deriv
  unfold resid_EX057 gen_EX057
  rw [hder, qhat_coe_EX057, phi_coe_EX057]

theorem Q_ne_zero_EX057 (h s x : ℝ) : Q_EX057 h s x ≠ 0 := by
  unfold Q_EX057
  exact div_ne_zero (Real.exp_pos _).ne' (partition_pos_EX054 h s).ne'

theorem resid_formula_EX057 (h t : ℝ) :
    resid_EX057 h (t : AngCircle) = Real.sqrt 2 * (h * Real.sin t * Pd_EX057 h t
      + root_EX054 h * Pd_EX057 h t ^ 2 + h * Real.cos t + 4 * moment_EX054 h (root_EX054 h)) := by
  have hDQ : -(Dd_EX057 h (root_EX054 h) t) / Q_EX057 h (root_EX054 h) t
      = -(Real.sqrt 2 * ((-h * Real.sin t - root_EX054 h * Pd_EX057 h t) * Pd_EX057 h t)
          + Real.sqrt 2 * Pdd_EX057 h t) := by
    rw [div_eq_iff (Q_ne_zero_EX057 h _ t)]
    unfold Dd_EX057
    ring
  rw [resid_coe_div_EX057, hDQ]
  unfold Pdd_EX057 Phi_EX057
  ring

/-! ### Trigonometric coefficients and their bounds -/

noncomputable def cc0_EX057 (h s m : ℝ) : ℝ :=
  Real.sqrt 2 * (h ^ 2 / 6 + 4 * m + 2 * s + s * h ^ 2 / 18)

noncomputable def cc1_EX057 (h s : ℝ) : ℝ := Real.sqrt 2 * (-(2 * h / 3) * s)

noncomputable def cc2_EX057 (h s : ℝ) : ℝ := Real.sqrt 2 * (-(h ^ 2 / 6) - s * h ^ 2 / 18)

noncomputable def cc3_EX057 (h s : ℝ) : ℝ := Real.sqrt 2 * (h + 2 * h / 3 * s)

noncomputable def cc4_EX057 (s : ℝ) : ℝ := Real.sqrt 2 * (-2 * s)

theorem resid_trig_EX057 (h t : ℝ) :
    resid_EX057 h (t : AngCircle) = trig5_EX057
      (cc0_EX057 h (root_EX054 h) (moment_EX054 h (root_EX054 h)))
      (cc1_EX057 h (root_EX054 h)) (cc2_EX057 h (root_EX054 h))
      (cc3_EX057 h (root_EX054 h)) (cc4_EX057 (root_EX054 h)) t := by
  rw [resid_formula_EX057]
  unfold trig5_EX057 cc0_EX057 cc1_EX057 cc2_EX057 cc3_EX057 cc4_EX057
  linear_combination (Real.sqrt 2) * trig_A_EX057 h t
    + (Real.sqrt 2 * root_EX054 h) * trig_B_EX057 h t

noncomputable def Bc_EX057 (C0 : ℝ) : ℝ := 1 / 24 + C0 / (2 * eta)

theorem coeff_bound_EX057 (h s m C0 : ℝ) (hC0 : 0 ≤ C0) (hB : 0 ≤ Bc_EX057 C0)
    (hh1 : |h| ≤ 1) (hs : |s| ≤ C0 * |h|) (hm : |m| ≤ Bc_EX057 C0 * |h|) :
    |cc0_EX057 h s m| ≤ 2 * ((1 + 4 * Bc_EX057 C0 + 3 * C0) * |h|) ∧
    |cc1_EX057 h s| ≤ 2 * ((1 + 4 * Bc_EX057 C0 + 3 * C0) * |h|) ∧
    |cc2_EX057 h s| ≤ 2 * ((1 + 4 * Bc_EX057 C0 + 3 * C0) * |h|) ∧
    |cc3_EX057 h s| ≤ 2 * ((1 + 4 * Bc_EX057 C0 + 3 * C0) * |h|) ∧
    |cc4_EX057 s| ≤ 2 * ((1 + 4 * Bc_EX057 C0 + 3 * C0) * |h|) := by
  have hu0 : 0 ≤ |h| := abs_nonneg h
  have hsq : h ^ 2 = |h| ^ 2 := (sq_abs h).symm
  have hh2' : 0 ≤ h ^ 2 := sq_nonneg h
  have hh2 : h ^ 2 ≤ |h| := by nlinarith [mul_nonneg hu0 (sub_nonneg.2 hh1)]
  have hh2one : h ^ 2 ≤ 1 := by nlinarith
  have hsh : |s * h ^ 2| ≤ C0 * |h| := by
    rw [abs_mul, abs_of_nonneg hh2']
    have := mul_le_mul hs hh2one hh2' (mul_nonneg hC0 hu0)
    linarith
  have hhs : |h * s| ≤ C0 * |h| := by
    rw [abs_mul]
    have := mul_le_mul_of_nonneg_left hs hu0
    nlinarith [mul_nonneg (mul_nonneg hC0 hu0) (sub_nonneg.2 hh1)]
  have key : ∀ r X : ℝ, 0 ≤ r → r ≤ 2 → |X| ≤ (1 + 4 * Bc_EX057 C0 + 3 * C0) * |h| →
      |r * X| ≤ 2 * ((1 + 4 * Bc_EX057 C0 + 3 * C0) * |h|) := by
    intro r X hr hr2 hX
    rw [abs_mul, abs_of_nonneg hr]
    nlinarith [abs_nonneg X, mul_nonneg (sub_nonneg.2 hr2) (abs_nonneg X)]
  have hr0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hr2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  obtain ⟨hs1, hs2⟩ := abs_le.1 hs
  obtain ⟨hm1, hm2⟩ := abs_le.1 hm
  obtain ⟨hsh1, hsh2⟩ := abs_le.1 hsh
  obtain ⟨hhs1, hhs2⟩ := abs_le.1 hhs
  have hb1 := neg_abs_le h
  have hb2 := le_abs_self h
  have hBu := mul_nonneg hB hu0
  have hCu := mul_nonneg hC0 hu0
  unfold cc0_EX057 cc1_EX057 cc2_EX057 cc3_EX057 cc4_EX057
  refine ⟨key _ _ hr0 hr2 ?_, key _ _ hr0 hr2 ?_, key _ _ hr0 hr2 ?_, key _ _ hr0 hr2 ?_,
    key _ _ hr0 hr2 ?_⟩
  · rw [abs_le]
    constructor <;> nlinarith
  · rw [abs_le]
    constructor <;> nlinarith
  · rw [abs_le]
    constructor <;> nlinarith
  · rw [abs_le]
    constructor <;> nlinarith
  · rw [abs_le]
    constructor <;> nlinarith

theorem moment_bound_EX057 (h C0 : ℝ) (hh1 : |h| ≤ 1)
    (hroot : |root_EX054 h| ≤ C0 * |h|) :
    |moment_EX054 h (root_EX054 h)| ≤ Bc_EX057 C0 * |h| := by
  have hη : 0 < eta := eta_pos
  have heq := root_equation_EX054 h
  have hdiff : moment_EX054 h (root_EX054 h) - polyCentering h = root_EX054 h / (2 * eta) := by
    rw [eq_div_iff (mul_pos two_pos hη).ne']
    linear_combination (-1 : ℝ) * heq
  have h1 : |moment_EX054 h (root_EX054 h)| ≤ |moment_EX054 h (root_EX054 h) - polyCentering h|
      + |polyCentering h| := by
    have := abs_add_le (moment_EX054 h (root_EX054 h) - polyCentering h) (polyCentering h)
    rwa [sub_add_cancel] at this
  have h2 : |moment_EX054 h (root_EX054 h) - polyCentering h| ≤ C0 * |h| / (2 * eta) := by
    rw [hdiff, abs_div, abs_of_pos (mul_pos two_pos hη)]
    exact div_le_div_of_nonneg_right hroot (by linarith)
  have h3 : |polyCentering h| ≤ |h| / 24 := by
    unfold polyCentering
    have hsq : h ^ 2 = |h| ^ 2 := (sq_abs h).symm
    rw [abs_le]
    constructor <;> nlinarith [abs_nonneg h, mul_nonneg (abs_nonneg h) (sub_nonneg.2 hh1)]
  have h4 : C0 * |h| / (2 * eta) = C0 / (2 * eta) * |h| := by ring
  unfold Bc_EX057
  nlinarith [h1, h2, h3, h4]

/-! ### Centering -/

theorem phi_qhat_integral_EX057 (h : ℝ) :
    ∫ θ, phi_EX057 h θ * qhat_EX057 h θ ∂angHaar = 0 := by
  have hZ : partition_EX054 h (root_EX054 h) ≠ 0 := (partition_pos_EX054 h _).ne'
  have hpt : (fun θ => phi_EX057 h θ * qhat_EX057 h θ)
      = fun θ => (Real.sqrt 2 / partition_EX054 h (root_EX054 h)) *
          (feature_EX054 h θ * weight_EX054 h (root_EX054 h) θ)
        - (Real.sqrt 2 * moment_EX054 h (root_EX054 h) / partition_EX054 h (root_EX054 h)) *
          weight_EX054 h (root_EX054 h) θ := by
    funext θ
    unfold phi_EX057 qhat_EX057 density_EX054
    ring
  have hmom : ∫ θ, feature_EX054 h θ * weight_EX054 h (root_EX054 h) θ ∂angHaar
      = moment_EX054 h (root_EX054 h) * partition_EX054 h (root_EX054 h) := by
    unfold moment_EX054
    field_simp
  have hw : ∫ θ, weight_EX054 h (root_EX054 h) θ ∂angHaar = partition_EX054 h (root_EX054 h) :=
    rfl
  rw [hpt, integral_sub ((integrable_feature_weight_EX054 h _).const_mul _)
    ((integrable_weight_EX054 h _).const_mul _), integral_const_mul, integral_const_mul, hmom, hw]
  field_simp
  ring

theorem integral_resid_centered_EX057 (h : ℝ) :
    ∫ θ, resid_EX057 h θ * qhat_EX057 h θ ∂angHaar = 0 := by
  have hG : DGPS.Circle.StationaryFlux.lift (fun θ => resid_EX057 h θ * qhat_EX057 h θ)
      = fun x => -(Dd_EX057 h (root_EX054 h) x)
          - 4 * (Phi_EX057 h (moment_EX054 h (root_EX054 h)) x * Q_EX057 h (root_EX054 h) x) := by
    funext x
    show resid_EX057 h (x : AngCircle) * qhat_EX057 h (x : AngCircle) = _
    rw [resid_coe_div_EX057, qhat_coe_EX057, sub_mul, div_mul_cancel₀ _ (Q_ne_zero_EX057 h _ x)]
    ring
  have hPQ : DGPS.Circle.StationaryFlux.lift (fun θ => phi_EX057 h θ * qhat_EX057 h θ)
      = fun x => Phi_EX057 h (moment_EX054 h (root_EX054 h)) x * Q_EX057 h (root_EX054 h) x := by
    funext x
    show phi_EX057 h (x : AngCircle) * qhat_EX057 h (x : AngCircle) = _
    rw [phi_coe_EX057, qhat_coe_EX057]
  have hcontDd : Continuous (fun x => Dd_EX057 h (root_EX054 h) x) := by
    unfold Dd_EX057 Q_EX057 logW_EX057 Pd_EX057 Pdd_EX057
    fun_prop
  have hcontPQ : Continuous (fun x => Phi_EX057 h (moment_EX054 h (root_EX054 h)) x
      * Q_EX057 h (root_EX054 h) x) := by
    unfold Phi_EX057 Q_EX057 logW_EX057
    fun_prop
  have hDint : ∫ x in (0 : ℝ)..2 * π, Dd_EX057 h (root_EX054 h) x = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_D_EX057 h (root_EX054 h) x) (hcontDd.intervalIntegrable _ _)]
    have hp := lift_periodic (fun θ => qhat_EX057 h θ * angDeriv (phi_EX057 h) θ) 0
    rw [lift_F_EX057, zero_add] at hp
    rw [hp, sub_self]
  have hz : ∫ θ, phi_EX057 h θ * qhat_EX057 h θ ∂angHaar = 0 := phi_qhat_integral_EX057 h
  have h2' : ∫ x in (0 : ℝ)..2 * π, Phi_EX057 h (moment_EX054 h (root_EX054 h)) x
      * Q_EX057 h (root_EX054 h) x = 0 := by
    have h2 : ∫ x in (0 : ℝ)..2 * π,
        DGPS.Circle.StationaryFlux.lift (fun θ => phi_EX057 h θ * qhat_EX057 h θ) x
          = 2 * π * ∫ θ, phi_EX057 h θ * qhat_EX057 h θ ∂angHaar :=
      integral_lift_period _
    rw [hPQ, hz, mul_zero] at h2
    exact h2
  have h1 : ∫ x in (0 : ℝ)..2 * π, (-(Dd_EX057 h (root_EX054 h) x)
      - 4 * (Phi_EX057 h (moment_EX054 h (root_EX054 h)) x * Q_EX057 h (root_EX054 h) x))
      = 2 * π * ∫ θ, resid_EX057 h θ * qhat_EX057 h θ ∂angHaar := by
    have := integral_lift_period (fun θ => resid_EX057 h θ * qhat_EX057 h θ)
    rw [hG] at this
    exact this
  have hsplit : ∫ x in (0 : ℝ)..2 * π, (-(Dd_EX057 h (root_EX054 h) x)
      - 4 * (Phi_EX057 h (moment_EX054 h (root_EX054 h)) x * Q_EX057 h (root_EX054 h) x))
      = -(∫ x in (0 : ℝ)..2 * π, Dd_EX057 h (root_EX054 h) x)
        - 4 * ∫ x in (0 : ℝ)..2 * π, Phi_EX057 h (moment_EX054 h (root_EX054 h)) x
          * Q_EX057 h (root_EX054 h) x := by
    have hA : IntervalIntegrable (fun x : ℝ => -(Dd_EX057 h (root_EX054 h) x))
        MeasureTheory.volume (0 : ℝ) (2 * π) := hcontDd.neg.intervalIntegrable _ _
    have hB : IntervalIntegrable
        (fun x : ℝ => 4 * (Phi_EX057 h (moment_EX054 h (root_EX054 h)) x
          * Q_EX057 h (root_EX054 h) x))
        MeasureTheory.volume (0 : ℝ) (2 * π) := (hcontPQ.const_mul 4).intervalIntegrable _ _
    refine (intervalIntegral.integral_sub hA hB).trans ?_
    simp only [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  rw [hsplit, hDint, h2'] at h1
  have hI : 2 * π * ∫ θ, resid_EX057 h θ * qhat_EX057 h θ ∂angHaar = 0 := by
    rw [← h1]
    ring
  rcases mul_eq_zero.1 hI with h0 | h0
  · exact absurd h0 (by positivity)
  · exact h0

end DGPS.Examples.PolynomialCenteredResidual

namespace DGPS.Examples

open DGPS.Examples.PolynomialCenteredResidual

/-- EX057: the polynomial centered residual `(Ahat - 4) phi_h`, with `Ahat = -L_qhat`
and `phi_h = sqrt 2 * (P_h - qhat_h(P_h))`, is qhat-centered and has `C^k` norm `O(h)`
for each fixed `k`. -/
theorem polynomial_centered_residual :
    ∀ k : ℕ, ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ h : ℝ, |h| ≤ δ →
      (∫ θ, resid_EX057 h θ * qhat_EX057 h θ ∂angHaar = 0) ∧
      ∀ j : ℕ, j ≤ k → ∀ θ : ℝ,
        |iteratedDeriv j (lift (resid_EX057 h)) θ| ≤ C * |h| := by
  intro k
  obtain ⟨C0, δ0, hC0, hδ0, hroot⟩ := abs_root_le_sixth_EX054
  have hB0 : 0 ≤ Bc_EX057 C0 :=
    add_nonneg (by norm_num) (div_nonneg hC0.le (by linarith [eta_pos]))
  refine ⟨5 * (2 * (1 + 4 * Bc_EX057 C0 + 3 * C0)) * 4 ^ k, min δ0 1, ?_, lt_min hδ0 one_pos,
    fun h hh => ⟨integral_resid_centered_EX057 h, fun j hj θ => ?_⟩⟩
  · have : 0 < 1 + 4 * Bc_EX057 C0 + 3 * C0 := by linarith
    positivity
  · have hh1 : |h| ≤ 1 := le_trans hh (min_le_right _ _)
    have hhδ0 : |h| ≤ δ0 := le_trans hh (min_le_left _ _)
    have hu0 : 0 ≤ |h| := abs_nonneg h
    have h6 : h ^ 6 ≤ |h| := by
      have e : h ^ 6 = |h| ^ 6 := (Even.pow_abs (by decide) h).symm
      rw [e]
      exact pow_le_of_le_one hu0 hh1 (by norm_num)
    have hs : |root_EX054 h| ≤ C0 * |h| :=
      le_trans (hroot h hhδ0) (mul_le_mul_of_nonneg_left h6 hC0.le)
    have hm := moment_bound_EX057 h C0 hh1 hs
    have hlift : lift (resid_EX057 h) = trig5_EX057
        (cc0_EX057 h (root_EX054 h) (moment_EX054 h (root_EX054 h)))
        (cc1_EX057 h (root_EX054 h)) (cc2_EX057 h (root_EX054 h))
        (cc3_EX057 h (root_EX054 h)) (cc4_EX057 (root_EX054 h)) := by
      funext t
      exact resid_trig_EX057 h t
    obtain ⟨b0, b1, b2, b3, b4⟩ := coeff_bound_EX057 h (root_EX054 h)
      (moment_EX054 h (root_EX054 h)) C0 hC0.le hB0 hh1 hs hm
    rw [hlift, iteratedDeriv_trig5_EX057]
    set M := 2 * ((1 + 4 * Bc_EX057 C0 + 3 * C0) * |h|) with hMdef
    have hM : 0 ≤ M := by
      have : 0 ≤ 1 + 4 * Bc_EX057 C0 + 3 * C0 := by linarith
      positivity
    have hj4 : (4 : ℝ) ^ j ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hj
    have e : ∀ x : ℝ, |x| ≤ M → |x| * 4 ^ j ≤ M * 4 ^ k := fun x hx =>
      mul_le_mul hx hj4 (by positivity) hM
    have hjb := abs_jet_le_EX057 (cc0_EX057 h (root_EX054 h) (moment_EX054 h (root_EX054 h)))
      (cc1_EX057 h (root_EX054 h)) (cc2_EX057 h (root_EX054 h))
      (cc3_EX057 h (root_EX054 h)) (cc4_EX057 (root_EX054 h)) j θ
    have hsum := add_le_add (add_le_add (add_le_add (add_le_add
      (e _ b0) (e _ b1)) (e _ b2)) (e _ b3)) (e _ b4)
    calc _ ≤ _ := hjb
      _ ≤ 5 * M * 4 ^ k := by linarith
      _ = 5 * (2 * (1 + 4 * Bc_EX057 C0 + 3 * C0)) * 4 ^ k * |h| := by rw [hMdef]; ring

end DGPS.Examples
