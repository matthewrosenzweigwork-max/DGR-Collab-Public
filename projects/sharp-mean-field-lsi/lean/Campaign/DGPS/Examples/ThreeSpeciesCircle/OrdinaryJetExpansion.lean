import DGPS.Examples.ThreeSpeciesCircle.OrdinaryReducedFactor

/-!
# Cumulant (jet) expansion of the reduced value at `Xp p` (packet STR028-b2)

For `p = (a, b, h, γ)` small, with `R0 = √(a² + b²)`,
`Phi (Xp p) = -γ R0²/2 - (9/20) h² R0² - h (a³ - 3ab²)/12 + R0⁴/48 + R0² · E p`
with `|E p| ≤ K ((|h| + R0)³ + |γ| (|h| + R0) + γ²)`
(`phi_jet_expansion_STR028b2`). `E` is an explicit plain function (zero where `R0 = 0`).

Proof route: `Phi (Xp p)` is a quotient of weighted circle averages (`Phi_eq_av_STR028b2`);
the averages are expanded around the weight `e^{h cos 3θ}` using the `3`-periodic Fourier
moments `m1`, `m2` of the weight, pointwise exponential bounds on the jet `uF`, and the
quotient/logarithm bookkeeping `assemble1/2`.
-/

open Function Filter Topology Asymptotics MeasureTheory
open DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic

namespace DGPS.Examples.ThreeSpeciesCircle
variable {α : ℝ} [HolderExponent α]

noncomputable def uF_STR028b2 (a b c2 s2 c4 s4 θ : ℝ) : ℝ :=
  a * Real.cos θ + b * Real.sin θ + (c2 * Real.cos (2 * θ) + s2 * Real.sin (2 * θ)) +
    (c4 * Real.cos (4 * θ) + s4 * Real.sin (4 * θ))

noncomputable def dF_STR028b2 (a b c2 s2 c4 s4 θ : ℝ) : ℝ :=
  (-a * Real.sin θ + b * Real.cos θ) + 2 * (-c2 * Real.sin (2 * θ) + s2 * Real.cos (2 * θ)) +
    4 * (-c4 * Real.sin (4 * θ) + s4 * Real.cos (4 * θ))

theorem uval_STR028b2 (p : Par) (x : ℝ) :
    (uCLM (Xp p : Par × Wsp α)).val x =
      uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p) (2 * Real.pi * x) := by
  rw [uCLM_Xp, jw, jetW_coe]
  simp only [uF_STR028b2, PH.val_add, PH.val_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, PH.val_trig, trigFun]
  push_cast
  ring_nf

theorem dval_STR028b2 (p : Par) (x : ℝ) :
    (DuCLM (Xp p : Par × Wsp α)).val x =
      dF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p) (2 * Real.pi * x) := by
  rw [sgv_Du]
  have hfun : (uCLM (Xp p : Par × Wsp α)).val =
      fun x => uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p) (2 * Real.pi * x) :=
    funext (uval_STR028b2 p)
  rw [hfun]
  have h1 : HasDerivAt (fun x : ℝ => 2 * Real.pi * x) (2 * Real.pi) x := by
    simpa using (hasDerivAt_id x).const_mul (2 * Real.pi)
  have h2 := h1.const_mul 2
  have h4 := h1.const_mul 4
  have hd := ((((h1.cos.const_mul (p 0)).add (h1.sin.const_mul (p 1))).add
    (((h2.cos.const_mul (jc2 p)).add (h2.sin.const_mul (js2 p))))).add
    (((h4.cos.const_mul (jc4 p)).add (h4.sin.const_mul (js4 p)))))
  have hd2 : HasDerivAt (fun x : ℝ => uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p)
      (2 * Real.pi * x)) ((2 * Real.pi) * dF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p)
      (2 * Real.pi * x)) x := by
    unfold uF_STR028b2 dF_STR028b2
    refine hd.congr_deriv ?_
    ring
  rw [hd2.deriv]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- Weighted average with weight `e^{h cos 6πx}` (normalised). -/
noncomputable def av_STR028b2 (h : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..1, f x * Real.exp (h * Real.cos (6 * Real.pi * x))) /
    ∫ x in (0 : ℝ)..1, Real.exp (h * Real.cos (6 * Real.pi * x))

theorem Z0_eq_STR028b2 (h : ℝ) : Z0_STR028b1 (α := α) h =
    ∫ x in (0 : ℝ)..1, Real.exp (h * Real.cos (6 * Real.pi * x)) := by
  unfold Z0_STR028b1 ZV_STR028b1 eV_STR028b1
  rw [PH.integral_apply]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [PH.expMap_val, sgv_phi]
  have hu : uCLM (((Pi.single 2 h : Par), (0 : Wsp α)) : Par × Wsp α) = 0 :=
    uCLM_ab_zero_STR028b1 _ (by simp) (by simp)
  rw [hu]
  simp

theorem ZV_eq_STR028b2 (p : Par) : ZV_STR028b1 (Xp p : Par × Wsp α) =
    ∫ x in (0 : ℝ)..1, Real.exp (p 2 * Real.cos (6 * Real.pi * x) +
      uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p) (2 * Real.pi * x)) := by
  unfold ZV_STR028b1 eV_STR028b1
  rw [PH.integral_apply]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [PH.expMap_val, sgv_phi, uval_STR028b2]
  rfl


theorem Z0r_pos_STR028b2 (h : ℝ) : 0 < ∫ x in (0 : ℝ)..1, Real.exp (h * Real.cos (6 * Real.pi * x)) := by
  refine intervalIntegral.intervalIntegral_pos_of_pos ?_ (fun x => Real.exp_pos _) one_pos
  exact (by fun_prop : Continuous fun x : ℝ => Real.exp (h * Real.cos (6 * Real.pi * x))).intervalIntegrable _ _

theorem av_one_STR028b2 (h : ℝ) : av_STR028b2 h (fun _ => 1) = 1 := by
  unfold av_STR028b2
  simp only [one_mul]
  exact div_self (Z0r_pos_STR028b2 h).ne'

theorem ZV_av_STR028b2 (p : Par) : ZV_STR028b1 (Xp p : Par × Wsp α) =
    av_STR028b2 (p 2) (fun x => Real.exp (uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p)
      (2 * Real.pi * x))) * ∫ x in (0 : ℝ)..1, Real.exp (p 2 * Real.cos (6 * Real.pi * x)) := by
  rw [ZV_eq_STR028b2]
  unfold av_STR028b2
  rw [div_mul_cancel₀ _ (Z0r_pos_STR028b2 _).ne']
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only
  rw [Real.exp_add]; ring

theorem int_rho_STR028b2 (p : Par) (f : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, (rho α (Xp p : Par × Wsp α)).val x * f x =
      av_STR028b2 (p 2) (fun x => f x * Real.exp (uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p)
        (js4 p) (2 * Real.pi * x))) /
      av_STR028b2 (p 2) (fun x => Real.exp (uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p)
        (2 * Real.pi * x))) := by
  have hZ := ZV_av_STR028b2 (α := α) p
  have hZpos := ZV_pos_STR028b1 (Xp p : Par × Wsp α)
  have hZ0 := Z0r_pos_STR028b2 (p 2)
  have hN : av_STR028b2 (p 2) (fun x => Real.exp (uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p)
      (js4 p) (2 * Real.pi * x))) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hZ; exact hZpos.ne' hZ
  have e1 : ∀ x, (rho α (Xp p : Par × Wsp α)).val x * f x =
      (ZV_STR028b1 (Xp p : Par × Wsp α))⁻¹ * ((f x * Real.exp (uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p)
        (jc4 p) (js4 p) (2 * Real.pi * x))) * Real.exp (p 2 * Real.cos (6 * Real.pi * x))) := by
    intro x
    rw [rho_eq_STR028b1]
    simp only [PH.val_smul, Pi.smul_apply, smul_eq_mul]
    unfold eV_STR028b1
    rw [PH.expMap_val, sgv_phi, uval_STR028b2, Real.exp_add]
    simp only [Xp]
    ring
  simp_rw [e1]
  rw [intervalIntegral.integral_const_mul, hZ]
  unfold av_STR028b2 at hN ⊢
  simp only [] at hN ⊢
  generalize (∫ x in (0 : ℝ)..1, Real.exp (p 2 * Real.cos (6 * Real.pi * x))) = Z0 at hZ0 hN ⊢
  generalize (∫ x in (0 : ℝ)..1, Real.exp (uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p)
    (2 * Real.pi * x)) * Real.exp (p 2 * Real.cos (6 * Real.pi * x))) = I2 at hN ⊢
  generalize (∫ x in (0 : ℝ)..1, f x * Real.exp (uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p)
    (2 * Real.pi * x)) * Real.exp (p 2 * Real.cos (6 * Real.pi * x))) = I1
  have hI2 : I2 ≠ 0 := fun h0 => hN (by rw [h0, zero_div])
  field_simp


theorem Phi_eq_av_STR028b2 (p : Par) : Phi_STR028b1 (Xp p : Par × Wsp α) =
    av_STR028b2 (p 2) (fun x => dF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p) (2 * Real.pi * x) *
        dF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p) (2 * Real.pi * x) *
        Real.exp (uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p) (2 * Real.pi * x))) /
      av_STR028b2 (p 2) (fun x => Real.exp (uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p)
        (2 * Real.pi * x))) -
    2 * (1 + p 3) * (av_STR028b2 (p 2) (fun x => uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p)
        (2 * Real.pi * x) * Real.exp (uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p)
        (2 * Real.pi * x))) /
      av_STR028b2 (p 2) (fun x => Real.exp (uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p)
        (2 * Real.pi * x))) -
      Real.log (av_STR028b2 (p 2) (fun x => Real.exp (uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p)
        (js4 p) (2 * Real.pi * x))))) := by
  have hZ := ZV_av_STR028b2 (α := α) p
  have hZ0 := Z0r_pos_STR028b2 (p 2)
  have hZpos := ZV_pos_STR028b1 (Xp p : Par × Wsp α)
  have hN : 0 < av_STR028b2 (p 2) (fun x => Real.exp (uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p)
      (js4 p) (2 * Real.pi * x))) := by
    rw [hZ] at hZpos
    exact pos_of_mul_pos_left hZpos hZ0.le |>.trans_le le_rfl
  have k1 : PH.integral 0 (rho α (Xp p : Par × Wsp α) * (DuCLM (Xp p) * DuCLM (Xp p))) =
      av_STR028b2 (p 2) (fun x => dF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p) (2 * Real.pi * x) *
        dF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p) (2 * Real.pi * x) *
        Real.exp (uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p) (2 * Real.pi * x))) /
      av_STR028b2 (p 2) (fun x => Real.exp (uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p)
        (2 * Real.pi * x))) := by
    rw [PH.integral_apply]
    simp only [PH.val_mul, Pi.mul_apply, dval_STR028b2]
    exact int_rho_STR028b2 p _
  have k2 : PH.integral 0 (rho α (Xp p : Par × Wsp α) * u0CLM (Xp p)) =
      av_STR028b2 (p 2) (fun x => uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p)
        (2 * Real.pi * x) * Real.exp (uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p)
        (2 * Real.pi * x))) /
      av_STR028b2 (p 2) (fun x => Real.exp (uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p)
        (2 * Real.pi * x))) := by
    rw [PH.integral_apply]
    simp only [PH.val_mul, Pi.mul_apply, sgv_u0, uval_STR028b2]
    exact int_rho_STR028b2 p _
  have hlog : Real.log (ZV_STR028b1 (Xp p : Par × Wsp α)) - Real.log (Z0_STR028b1 (α := α) ((Xp p : Par × Wsp α).1 2)) =
      Real.log (av_STR028b2 (p 2) (fun x => Real.exp (uF_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p)
        (js4 p) (2 * Real.pi * x)))) := by
    have : (Xp p : Par × Wsp α).1 2 = p 2 := rfl
    rw [this, Z0_eq_STR028b2, hZ, Real.log_mul hN.ne' hZ0.ne']
    ring
  unfold Phi_STR028b1 kap
  rw [hlog, k1, k2]
  have : (Xp p : Par × Wsp α).1 3 = p 3 := rfl
  rw [this]
  ring

/-- Weighted average of a function of `θ = 2πx`. -/
noncomputable def avt_STR028b2 (h : ℝ) (F : ℝ → ℝ) : ℝ :=
  av_STR028b2 h (fun x => F (2 * Real.pi * x))

theorem wt_cont_STR028b2 (h : ℝ) :
    Continuous fun x : ℝ => Real.exp (h * Real.cos (6 * Real.pi * x)) := by fun_prop

theorem Fc_STR028b2 {F : ℝ → ℝ} (hF : Continuous F) :
    Continuous fun x : ℝ => F (2 * Real.pi * x) := hF.comp (by fun_prop)

theorem intF_STR028b2 (h : ℝ) {F : ℝ → ℝ} (hF : Continuous F) :
    IntervalIntegrable (fun x : ℝ => F (2 * Real.pi * x) *
      Real.exp (h * Real.cos (6 * Real.pi * x))) MeasureTheory.volume 0 1 :=
  ((Fc_STR028b2 hF).mul (wt_cont_STR028b2 h)).intervalIntegrable _ _

theorem avt_add_STR028b2 (h : ℝ) {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G) :
    avt_STR028b2 h (fun θ => F θ + G θ) = avt_STR028b2 h F + avt_STR028b2 h G := by
  unfold avt_STR028b2 av_STR028b2
  rw [← add_div]
  congr 1
  rw [← intervalIntegral.integral_add (intF_STR028b2 h hF) (intF_STR028b2 h hG)]
  simp only [add_mul]

theorem avt_sub_STR028b2 (h : ℝ) {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G) :
    avt_STR028b2 h (fun θ => F θ - G θ) = avt_STR028b2 h F - avt_STR028b2 h G := by
  unfold avt_STR028b2 av_STR028b2
  rw [← sub_div]
  congr 1
  rw [← intervalIntegral.integral_sub (intF_STR028b2 h hF) (intF_STR028b2 h hG)]
  simp only [sub_mul]

theorem avt_const_mul_STR028b2 (h c : ℝ) (F : ℝ → ℝ) :
    avt_STR028b2 h (fun θ => c * F θ) = c * avt_STR028b2 h F := by
  unfold avt_STR028b2 av_STR028b2
  rw [← mul_div_assoc, ← intervalIntegral.integral_const_mul]
  simp only [mul_assoc]

theorem avt_const_STR028b2 (h c : ℝ) : avt_STR028b2 h (fun _ => c) = c := by
  have := avt_const_mul_STR028b2 h c (fun _ => 1)
  simp only [mul_one] at this
  rw [this]
  unfold avt_STR028b2 av_STR028b2
  simp only [one_mul]
  rw [div_self (Z0r_pos_STR028b2 h).ne', mul_one]

theorem avt_abs_le_STR028b2 (h : ℝ) {F : ℝ → ℝ} (hF : Continuous F) {M : ℝ}
    (hM : ∀ θ, |F θ| ≤ M) : |avt_STR028b2 h F| ≤ M := by
  unfold avt_STR028b2 av_STR028b2
  have hZ := Z0r_pos_STR028b2 h
  rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  have hw := wt_cont_STR028b2 h
  have h1 : ∫ x in (0 : ℝ)..1, F (2 * Real.pi * x) * Real.exp (h * Real.cos (6 * Real.pi * x)) ≤
      ∫ x in (0 : ℝ)..1, M * Real.exp (h * Real.cos (6 * Real.pi * x)) :=
    intervalIntegral.integral_mono_on zero_le_one (intF_STR028b2 h hF)
      ((continuous_const.mul hw).intervalIntegrable _ _)
      (fun x _ => mul_le_mul_of_nonneg_right (le_trans (le_abs_self _) (hM _)) (Real.exp_pos _).le)
  have h2 : ∫ x in (0 : ℝ)..1, (-M) * Real.exp (h * Real.cos (6 * Real.pi * x)) ≤
      ∫ x in (0 : ℝ)..1, F (2 * Real.pi * x) * Real.exp (h * Real.cos (6 * Real.pi * x)) :=
    intervalIntegral.integral_mono_on zero_le_one
      ((continuous_const.mul hw).intervalIntegrable _ _) (intF_STR028b2 h hF)
      (fun x _ => mul_le_mul_of_nonneg_right (by have := hM (2 * Real.pi * x); linarith [neg_abs_le (F (2 * Real.pi * x))]) (Real.exp_pos _).le)
  rw [intervalIntegral.integral_const_mul] at h1 h2
  rw [abs_le]
  constructor <;> nlinarith

theorem avt_zero_STR028b2 (F : ℝ → ℝ) :
    avt_STR028b2 0 F = ∫ x in (0 : ℝ)..1, F (2 * Real.pi * x) := by
  unfold avt_STR028b2 av_STR028b2
  simp

theorem int_sin_w_STR028b2 (h : ℝ) (k : ℕ) :
    ∫ x in (0:ℝ)..1, Real.sin (k * (2 * Real.pi * x)) *
      Real.exp (h * Real.cos (6 * Real.pi * x)) = 0 := by
  set g : ℝ → ℝ := fun x => Real.sin (k * (2 * Real.pi * x)) *
      Real.exp (h * Real.cos (6 * Real.pi * x)) with hg
  have h1 : ∫ x in (0:ℝ)..1, g (1 - x) = ∫ x in (0:ℝ)..1, g x := by
    rw [intervalIntegral.integral_comp_sub_left]; simp
  have h2 : ∀ x, g (1 - x) = - g x := by
    intro x
    simp only [hg]
    have e1 : (k:ℝ) * (2 * Real.pi * (1 - x)) = k * (2 * Real.pi) - k * (2 * Real.pi * x) := by ring
    have e2 : 6 * Real.pi * (1 - x) = ((3:ℕ):ℝ) * (2 * Real.pi) - 6 * Real.pi * x := by push_cast; ring
    rw [e1, e2, Real.sin_nat_mul_two_pi_sub, Real.cos_nat_mul_two_pi_sub]
    ring
  simp_rw [h2] at h1
  rw [intervalIntegral.integral_neg] at h1
  linarith

theorem cos_third_STR028b2 (k : ℕ) (hk : k % 3 ≠ 0) :
    Real.cos (k * (2 * Real.pi / 3)) = -1/2 := by
  have hk' : k % 3 = 1 ∨ k % 3 = 2 := by omega
  obtain ⟨m, hm⟩ : ∃ m, k = 3 * m + k % 3 := ⟨k / 3, by omega⟩
  rcases hk' with h | h
  · rw [h] at hm
    have : (k:ℝ) * (2 * Real.pi / 3) = 2 * Real.pi / 3 + m * (2 * Real.pi) := by
      rw [hm]; push_cast; ring
    rw [this, Real.cos_add_nat_mul_two_pi]
    have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  · rw [h] at hm
    have : (k:ℝ) * (2 * Real.pi / 3) = (Real.pi / 3 + Real.pi) + m * (2 * Real.pi) := by
      rw [hm]; push_cast; ring
    rw [this, Real.cos_add_nat_mul_two_pi, Real.cos_add_pi, Real.cos_pi_div_three]; norm_num

theorem int_cos_w_STR028b2 (h : ℝ) (k : ℕ) (hk : k % 3 ≠ 0) :
    ∫ x in (0:ℝ)..1, Real.cos (k * (2 * Real.pi * x)) *
      Real.exp (h * Real.cos (6 * Real.pi * x)) = 0 := by
  set g : ℝ → ℝ := fun x => Real.cos (k * (2 * Real.pi * x)) *
      Real.exp (h * Real.cos (6 * Real.pi * x)) with hg
  have hper : Function.Periodic g 1 := by
    intro x
    simp only [hg]
    have e1 : (k:ℝ) * (2 * Real.pi * (x + 1)) = k * (2 * Real.pi * x) + k * (2 * Real.pi) := by ring
    have e2 : 6 * Real.pi * (x + 1) = 6 * Real.pi * x + ((3:ℕ):ℝ) * (2 * Real.pi) := by push_cast; ring
    rw [e1, e2, Real.cos_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi]
  have h1 : ∫ x in (0:ℝ)..1, g (x + 1/3) = ∫ x in (0:ℝ)..1, g x := by
    rw [intervalIntegral.integral_comp_add_right]
    have := hper.intervalIntegral_add_eq (1/3) 0
    simp only [zero_add] at this ⊢
    rw [add_comm (1:ℝ) (1/3)]; exact this
  have hB := cos_third_STR028b2 k hk
  have h2 : ∀ x, g (x + 1/3) = Real.cos (k * (2 * Real.pi / 3)) * g x -
      Real.sin (k * (2 * Real.pi / 3)) * (Real.sin (k * (2 * Real.pi * x)) *
        Real.exp (h * Real.cos (6 * Real.pi * x))) := by
    intro x
    simp only [hg]
    have e1 : (k:ℝ) * (2 * Real.pi * (x + 1/3)) = k * (2 * Real.pi * x) + k * (2 * Real.pi / 3) := by ring
    have e2 : 6 * Real.pi * (x + 1/3) = 6 * Real.pi * x + 2 * Real.pi := by ring
    rw [e1, e2, Real.cos_add_two_pi, Real.cos_add]
    ring
  simp_rw [h2] at h1
  have c1 : Continuous g := by simp only [hg]; fun_prop
  have c2 : Continuous fun x : ℝ => Real.sin (k * (2 * Real.pi * x)) *
        Real.exp (h * Real.cos (6 * Real.pi * x)) := by fun_prop
  rw [intervalIntegral.integral_sub
    (f := fun x => Real.cos (k * (2 * Real.pi / 3)) * g x)
    (g := fun x => Real.sin (k * (2 * Real.pi / 3)) * (Real.sin (k * (2 * Real.pi * x)) *
        Real.exp (h * Real.cos (6 * Real.pi * x))))
    ((continuous_const.mul c1).intervalIntegrable _ _)
    ((continuous_const.mul c2).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, int_sin_w_STR028b2, hB] at h1
  linarith

/-- Plain integrals of the trigonometric modes. -/
theorem int_cos_nat_STR028b2 (k : ℕ) (hk : 1 ≤ k) :
    ∫ x in (0:ℝ)..1, Real.cos (k * (2 * Real.pi * x)) = 0 := by
  have hc : (k:ℝ) * (2 * Real.pi) ≠ 0 := by positivity
  have : ∀ x : ℝ, Real.cos (k * (2 * Real.pi * x)) = Real.cos ((k * (2 * Real.pi)) * x) := fun x => by ring_nf
  simp_rw [this]
  rw [intervalIntegral.integral_comp_mul_left (fun y => Real.cos y) hc, integral_cos]
  have h1 : Real.sin ((k:ℝ) * (2 * Real.pi)) = 0 := by
    have := Real.sin_nat_mul_pi (2 * k)
    push_cast at this
    rw [← this]; ring_nf
  simp [h1]

theorem int_sin_nat_STR028b2 (k : ℕ) (hk : 1 ≤ k) :
    ∫ x in (0:ℝ)..1, Real.sin (k * (2 * Real.pi * x)) = 0 := by
  have hc : (k:ℝ) * (2 * Real.pi) ≠ 0 := by positivity
  have : ∀ x : ℝ, Real.sin (k * (2 * Real.pi * x)) = Real.sin ((k * (2 * Real.pi)) * x) := fun x => by ring_nf
  simp_rw [this]
  rw [intervalIntegral.integral_comp_mul_left (fun y => Real.sin y) hc, integral_sin]
  simp

theorem wt_sub_one_STR028b2 {h : ℝ} (hh : |h| ≤ 1) (x : ℝ) :
    |Real.exp (h * Real.cos (6 * Real.pi * x)) - 1| ≤ 2 * |h| := by
  have hc : |Real.cos (6 * Real.pi * x)| ≤ 1 := Real.abs_cos_le_one _
  have hy : |h * Real.cos (6 * Real.pi * x)| ≤ 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg h, abs_nonneg (Real.cos (6 * Real.pi * x))]
  have := Real.abs_exp_sub_one_le hy
  rw [abs_mul] at this
  nlinarith [mul_le_mul_of_nonneg_left hc (abs_nonneg h)]

theorem Z0_sub_one_STR028b2 {h : ℝ} (hh : |h| ≤ 1) :
    |(∫ x in (0:ℝ)..1, Real.exp (h * Real.cos (6 * Real.pi * x))) - 1| ≤ 2 * |h| := by
  have e : (∫ x in (0:ℝ)..1, Real.exp (h * Real.cos (6 * Real.pi * x))) - 1 =
      ∫ x in (0:ℝ)..1, (Real.exp (h * Real.cos (6 * Real.pi * x)) - 1) := by
    rw [intervalIntegral.integral_sub ((wt_cont_STR028b2 h).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)]
    simp
  rw [e]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun x => Real.exp (h * Real.cos (6 * Real.pi * x)) - 1) (C := 2 * |h|)
    (fun x _ => by rw [Real.norm_eq_abs]; exact wt_sub_one_STR028b2 hh x)
  simpa using this

/-- Rough comparison of the weighted average with the plain integral. -/
theorem avt_rough_STR028b2 {h : ℝ} (hh : |h| ≤ 1 / 4) {F : ℝ → ℝ} (hF : Continuous F) {M : ℝ}
    (hM : ∀ θ, |F θ| ≤ M) :
    |avt_STR028b2 h F - ∫ x in (0:ℝ)..1, F (2 * Real.pi * x)| ≤ 8 * |h| * M := by
  have hh1 : |h| ≤ 1 := by linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hZ1 := Z0_sub_one_STR028b2 hh1
  set Z := ∫ x in (0:ℝ)..1, Real.exp (h * Real.cos (6 * Real.pi * x)) with hZ
  set I := ∫ x in (0:ℝ)..1, F (2 * Real.pi * x) with hI
  have hZl : 1 / 2 ≤ Z := by
    have := (abs_le.mp hZ1).1; linarith [abs_nonneg h]
  have hIb : |I| ≤ M := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun x => F (2 * Real.pi * x)) (C := M)
      (fun x _ => by rw [Real.norm_eq_abs]; exact hM _)
    simp only [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at this
    exact this
  have hW : |(∫ x in (0:ℝ)..1, F (2 * Real.pi * x) * Real.exp (h * Real.cos (6 * Real.pi * x))) - I|
      ≤ 2 * |h| * M := by
    have e : (∫ x in (0:ℝ)..1, F (2 * Real.pi * x) * Real.exp (h * Real.cos (6 * Real.pi * x))) - I =
        ∫ x in (0:ℝ)..1, F (2 * Real.pi * x) * (Real.exp (h * Real.cos (6 * Real.pi * x)) - 1) := by
      rw [hI, ← intervalIntegral.integral_sub (intF_STR028b2 h hF)
        ((Fc_STR028b2 hF).intervalIntegrable _ _)]
      congr 1; ext x; ring
    rw [e]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun x => F (2 * Real.pi * x) * (Real.exp (h * Real.cos (6 * Real.pi * x)) - 1))
      (C := M * (2 * |h|))
      (fun x _ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hM _) (wt_sub_one_STR028b2 hh1 x) (abs_nonneg _) hM0)
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  unfold avt_STR028b2 av_STR028b2
  beta_reduce
  rw [← hZ]
  have hZne : Z ≠ 0 := by linarith
  have e2 : ∀ W : ℝ, W / Z - I = ((W - I) - I * (Z - 1)) / Z := by
    intro W; field_simp; ring
  rw [e2, abs_div, abs_of_pos (by linarith : 0 < Z), div_le_iff₀ (by linarith)]
  have h3 : |((∫ x in (0:ℝ)..1, F (2 * Real.pi * x) * Real.exp (h * Real.cos (6 * Real.pi * x))) - I) -
        I * (Z - 1)| ≤ 2 * |h| * M + M * (2 * |h|) := by
    refine (abs_sub _ _).trans (add_le_add hW ?_)
    rw [abs_mul]
    exact mul_le_mul hIb hZ1 (abs_nonneg _) hM0
  nlinarith [mul_nonneg (mul_nonneg (abs_nonneg h) hM0) (by linarith : 0 ≤ Z - 1 / 2)]

theorem avt_sin_mode_STR028b2 (h : ℝ) (k : ℕ) :
    avt_STR028b2 h (fun θ => Real.sin (k * θ)) = 0 := by
  unfold avt_STR028b2 av_STR028b2
  beta_reduce
  rw [int_sin_w_STR028b2, zero_div]

theorem avt_cos_mode_STR028b2 (h : ℝ) (k : ℕ) (hk : k % 3 ≠ 0) :
    avt_STR028b2 h (fun θ => Real.cos (k * θ)) = 0 := by
  unfold avt_STR028b2 av_STR028b2
  beta_reduce
  rw [int_cos_w_STR028b2 h k hk, zero_div]

noncomputable def m1_STR028b2 (h : ℝ) : ℝ := avt_STR028b2 h (fun θ => Real.cos (3 * θ))
noncomputable def m2_STR028b2 (h : ℝ) : ℝ := avt_STR028b2 h (fun θ => Real.cos (6 * θ))

theorem m_zero_STR028b2 : m1_STR028b2 0 = 0 ∧ m2_STR028b2 0 = 0 := by
  constructor
  · unfold m1_STR028b2; rw [avt_zero_STR028b2]
    have := int_cos_nat_STR028b2 3 (by norm_num)
    simpa using this
  · unfold m2_STR028b2; rw [avt_zero_STR028b2]
    have := int_cos_nat_STR028b2 6 (by norm_num)
    simpa using this

theorem cint_sub_STR028b2 {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ∫ x in (0:ℝ)..1, (f x - g x) = (∫ x in (0:ℝ)..1, f x) - ∫ x in (0:ℝ)..1, g x :=
  intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)

theorem cint_add_STR028b2 {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ∫ x in (0:ℝ)..1, (f x + g x) = (∫ x in (0:ℝ)..1, f x) + ∫ x in (0:ℝ)..1, g x :=
  intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)

theorem int_c_STR028b2 : ∫ x in (0:ℝ)..1, Real.cos (6 * Real.pi * x) = 0 := by
  have := int_cos_nat_STR028b2 3 (by norm_num)
  have e : ∀ x : ℝ, Real.cos (((3:ℕ):ℝ) * (2 * Real.pi * x)) = Real.cos (6 * Real.pi * x) :=
    fun x => by push_cast; ring_nf
  simp only [e] at this
  exact this

theorem int_c2_STR028b2 : ∫ x in (0:ℝ)..1, Real.cos (6 * Real.pi * x) ^ 2 = 1 / 2 := by
  have h6 := int_cos_nat_STR028b2 6 (by norm_num)
  have e : ∀ x : ℝ, Real.cos (6 * Real.pi * x) ^ 2 =
      1 / 2 + (1 / 2) * Real.cos (((6:ℕ):ℝ) * (2 * Real.pi * x)) := fun x => by
    rw [Real.cos_sq]; push_cast; ring_nf
  simp_rw [e]
  rw [cint_add_STR028b2 (f := fun _ => 1 / 2)
    (g := fun x => (1 / 2) * Real.cos (((6:ℕ):ℝ) * (2 * Real.pi * x))) (by fun_prop) (by fun_prop),
    intervalIntegral.integral_const_mul, h6]
  simp

theorem m1_bound_STR028b2 {h : ℝ} (hh : |h| ≤ 1 / 2) : |m1_STR028b2 h - h / 2| ≤ 2 * h ^ 2 := by
  have hh1 : |h| ≤ 1 := by linarith
  have h2 : h ^ 2 ≤ 1 / 4 := by
    have := sq_abs h; nlinarith [abs_nonneg h]
  have hc : ∀ x : ℝ, |Real.cos (6 * Real.pi * x)| ≤ 1 := fun x => Real.abs_cos_le_one _
  have hr : ∀ x : ℝ, |Real.exp (h * Real.cos (6 * Real.pi * x)) - 1 - h * Real.cos (6 * Real.pi * x)|
      ≤ h ^ 2 * Real.cos (6 * Real.pi * x) ^ 2 := by
    intro x
    have hy : |h * Real.cos (6 * Real.pi * x)| ≤ 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg h, abs_nonneg (Real.cos (6 * Real.pi * x)), hc x]
    have := Real.abs_exp_sub_one_sub_id_le hy
    calc _ ≤ (h * Real.cos (6 * Real.pi * x)) ^ 2 := this
      _ = _ := by ring
  have hcc : Continuous fun x : ℝ => Real.cos (6 * Real.pi * x) := by fun_prop
  have hZ : |(∫ x in (0:ℝ)..1, Real.exp (h * Real.cos (6 * Real.pi * x))) - 1| ≤ h ^ 2 / 2 := by
    have e : (∫ x in (0:ℝ)..1, Real.exp (h * Real.cos (6 * Real.pi * x))) - 1 =
        ∫ x in (0:ℝ)..1, (Real.exp (h * Real.cos (6 * Real.pi * x)) - 1 - h * Real.cos (6 * Real.pi * x)) := by
      rw [cint_sub_STR028b2 (f := fun x => Real.exp (h * Real.cos (6 * Real.pi * x)) - 1)
        (g := fun x => h * Real.cos (6 * Real.pi * x)) (by fun_prop) (by fun_prop),
        cint_sub_STR028b2 (f := fun x => Real.exp (h * Real.cos (6 * Real.pi * x)))
        (g := fun _ => 1) (by fun_prop) (by fun_prop), intervalIntegral.integral_const_mul,
        int_c_STR028b2]
      simp
    rw [e]
    have := intervalIntegral.norm_integral_le_of_norm_le (a := 0) (b := 1) (μ := MeasureTheory.volume) zero_le_one
      (f := fun x => Real.exp (h * Real.cos (6 * Real.pi * x)) - 1 - h * Real.cos (6 * Real.pi * x))
      (g := fun x => h ^ 2 * Real.cos (6 * Real.pi * x) ^ 2)
      (Filter.Eventually.of_forall (fun x _ => by rw [Real.norm_eq_abs]; exact hr x))
      ((by fun_prop : Continuous fun x : ℝ => h ^ 2 * Real.cos (6 * Real.pi * x) ^ 2).intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul, int_c2_STR028b2, Real.norm_eq_abs] at this
    linarith
  have hN : |(∫ x in (0:ℝ)..1, Real.cos (6 * Real.pi * x) * Real.exp (h * Real.cos (6 * Real.pi * x))) - h / 2|
      ≤ h ^ 2 / 2 := by
    have e : (∫ x in (0:ℝ)..1, Real.cos (6 * Real.pi * x) * Real.exp (h * Real.cos (6 * Real.pi * x))) - h / 2 =
        ∫ x in (0:ℝ)..1, Real.cos (6 * Real.pi * x) *
          (Real.exp (h * Real.cos (6 * Real.pi * x)) - 1 - h * Real.cos (6 * Real.pi * x)) := by
      have e1 : ∀ x : ℝ, Real.cos (6 * Real.pi * x) *
          (Real.exp (h * Real.cos (6 * Real.pi * x)) - 1 - h * Real.cos (6 * Real.pi * x)) =
          (Real.cos (6 * Real.pi * x) * Real.exp (h * Real.cos (6 * Real.pi * x)) -
            Real.cos (6 * Real.pi * x)) - h * Real.cos (6 * Real.pi * x) ^ 2 := fun x => by ring
      simp_rw [e1]
      rw [cint_sub_STR028b2 (f := fun x => Real.cos (6 * Real.pi * x) * Real.exp (h * Real.cos (6 * Real.pi * x)) -
            Real.cos (6 * Real.pi * x)) (g := fun x => h * Real.cos (6 * Real.pi * x) ^ 2)
        (by fun_prop) (by fun_prop),
        cint_sub_STR028b2 (f := fun x => Real.cos (6 * Real.pi * x) * Real.exp (h * Real.cos (6 * Real.pi * x)))
        (g := fun x => Real.cos (6 * Real.pi * x)) (by fun_prop) (by fun_prop),
        intervalIntegral.integral_const_mul, int_c_STR028b2, int_c2_STR028b2]
      ring
    rw [e]
    have := intervalIntegral.norm_integral_le_of_norm_le (a := 0) (b := 1) (μ := MeasureTheory.volume) zero_le_one
      (f := fun x => Real.cos (6 * Real.pi * x) *
          (Real.exp (h * Real.cos (6 * Real.pi * x)) - 1 - h * Real.cos (6 * Real.pi * x)))
      (g := fun x => h ^ 2 * Real.cos (6 * Real.pi * x) ^ 2)
      (Filter.Eventually.of_forall (fun x _ => by
        rw [Real.norm_eq_abs, abs_mul]
        calc _ ≤ 1 * (h ^ 2 * Real.cos (6 * Real.pi * x) ^ 2) :=
              mul_le_mul (hc x) (hr x) (abs_nonneg _) zero_le_one
          _ = _ := one_mul _))
      ((by fun_prop : Continuous fun x : ℝ => h ^ 2 * Real.cos (6 * Real.pi * x) ^ 2).intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul, int_c2_STR028b2, Real.norm_eq_abs] at this
    linarith
  have hm : m1_STR028b2 h = (∫ x in (0:ℝ)..1, Real.cos (6 * Real.pi * x) * Real.exp (h * Real.cos (6 * Real.pi * x))) /
      ∫ x in (0:ℝ)..1, Real.exp (h * Real.cos (6 * Real.pi * x)) := by
    unfold m1_STR028b2 avt_STR028b2 av_STR028b2
    beta_reduce
    congr 1
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    congr 2; ring_nf
  rw [hm]
  generalize (∫ x in (0:ℝ)..1, Real.cos (6 * Real.pi * x) * Real.exp (h * Real.cos (6 * Real.pi * x))) = B at hN ⊢
  generalize (∫ x in (0:ℝ)..1, Real.exp (h * Real.cos (6 * Real.pi * x))) = Z at hZ ⊢
  have hZl : 7 / 8 ≤ Z := by
    have := (abs_le.mp hZ).1; nlinarith
  have hZne : Z ≠ 0 := by linarith
  have e3 : B / Z - h / 2 = ((B - h / 2) - (h / 2) * (Z - 1)) / Z := by
    field_simp; ring
  rw [e3, abs_div, abs_of_pos (by linarith : 0 < Z), div_le_iff₀ (by linarith)]
  have h3 : |(B - h / 2) - (h / 2) * (Z - 1)| ≤ h ^ 2 / 2 + (|h| / 2) * (h ^ 2 / 2) := by
    refine (abs_sub _ _).trans (add_le_add hN ?_)
    rw [abs_mul, abs_div, abs_two]
    exact mul_le_mul_of_nonneg_left hZ (by positivity)
  nlinarith [abs_nonneg h, sq_nonneg h, mul_nonneg (sq_nonneg h) (by linarith : 0 ≤ Z - 7 / 8)]

noncomputable def four8_STR028b2 (c0 c1 s1 c2 s2 c3 s3 c4 s4 c5 s5 c6 s6 c7 s7 c8 s8 θ : ℝ) : ℝ :=
  c0 + (c1 * Real.cos θ + s1 * Real.sin θ) + (c2 * Real.cos (2 * θ) + s2 * Real.sin (2 * θ)) +
    (c3 * Real.cos (3 * θ) + s3 * Real.sin (3 * θ)) + (c4 * Real.cos (4 * θ) + s4 * Real.sin (4 * θ)) +
    (c5 * Real.cos (5 * θ) + s5 * Real.sin (5 * θ)) + (c6 * Real.cos (6 * θ) + s6 * Real.sin (6 * θ)) +
    (c7 * Real.cos (7 * θ) + s7 * Real.sin (7 * θ)) + (c8 * Real.cos (8 * θ) + s8 * Real.sin (8 * θ))

theorem four8_cont_STR028b2 (c0 c1 s1 c2 s2 c3 s3 c4 s4 c5 s5 c6 s6 c7 s7 c8 s8 : ℝ) :
    Continuous (four8_STR028b2 c0 c1 s1 c2 s2 c3 s3 c4 s4 c5 s5 c6 s6 c7 s7 c8 s8) := by
  unfold four8_STR028b2; fun_prop

theorem avt_cos1_STR028b2 (h : ℝ) : avt_STR028b2 h (fun θ => Real.cos θ) = 0 := by
  simpa using avt_cos_mode_STR028b2 h 1 (by norm_num)
theorem avt_cos2_STR028b2 (h : ℝ) : avt_STR028b2 h (fun θ => Real.cos (2 * θ)) = 0 := by
  simpa using avt_cos_mode_STR028b2 h 2 (by norm_num)
theorem avt_cos4_STR028b2 (h : ℝ) : avt_STR028b2 h (fun θ => Real.cos (4 * θ)) = 0 := by
  simpa using avt_cos_mode_STR028b2 h 4 (by norm_num)
theorem avt_cos5_STR028b2 (h : ℝ) : avt_STR028b2 h (fun θ => Real.cos (5 * θ)) = 0 := by
  simpa using avt_cos_mode_STR028b2 h 5 (by norm_num)
theorem avt_cos7_STR028b2 (h : ℝ) : avt_STR028b2 h (fun θ => Real.cos (7 * θ)) = 0 := by
  simpa using avt_cos_mode_STR028b2 h 7 (by norm_num)
theorem avt_cos8_STR028b2 (h : ℝ) : avt_STR028b2 h (fun θ => Real.cos (8 * θ)) = 0 := by
  simpa using avt_cos_mode_STR028b2 h 8 (by norm_num)
theorem avt_sin1_STR028b2 (h : ℝ) : avt_STR028b2 h (fun θ => Real.sin θ) = 0 := by
  simpa using avt_sin_mode_STR028b2 h 1
theorem avt_sin2_STR028b2 (h : ℝ) : avt_STR028b2 h (fun θ => Real.sin (2 * θ)) = 0 := by
  simpa using avt_sin_mode_STR028b2 h 2
theorem avt_sin3_STR028b2 (h : ℝ) : avt_STR028b2 h (fun θ => Real.sin (3 * θ)) = 0 := by
  simpa using avt_sin_mode_STR028b2 h 3
theorem avt_sin4_STR028b2 (h : ℝ) : avt_STR028b2 h (fun θ => Real.sin (4 * θ)) = 0 := by
  simpa using avt_sin_mode_STR028b2 h 4
theorem avt_sin5_STR028b2 (h : ℝ) : avt_STR028b2 h (fun θ => Real.sin (5 * θ)) = 0 := by
  simpa using avt_sin_mode_STR028b2 h 5
theorem avt_sin6_STR028b2 (h : ℝ) : avt_STR028b2 h (fun θ => Real.sin (6 * θ)) = 0 := by
  simpa using avt_sin_mode_STR028b2 h 6
theorem avt_sin7_STR028b2 (h : ℝ) : avt_STR028b2 h (fun θ => Real.sin (7 * θ)) = 0 := by
  simpa using avt_sin_mode_STR028b2 h 7
theorem avt_sin8_STR028b2 (h : ℝ) : avt_STR028b2 h (fun θ => Real.sin (8 * θ)) = 0 := by
  simpa using avt_sin_mode_STR028b2 h 8

theorem avt_four8_STR028b2 (h c0 c1 s1 c2 s2 c3 s3 c4 s4 c5 s5 c6 s6 c7 s7 c8 s8 : ℝ) :
    avt_STR028b2 h (four8_STR028b2 c0 c1 s1 c2 s2 c3 s3 c4 s4 c5 s5 c6 s6 c7 s7 c8 s8) =
      c0 + c3 * m1_STR028b2 h + c6 * m2_STR028b2 h := by
  unfold four8_STR028b2
  simp (disch := fun_prop) only [avt_add_STR028b2, avt_const_mul_STR028b2, avt_const_STR028b2]
  simp only [avt_cos1_STR028b2, avt_cos2_STR028b2, avt_cos4_STR028b2, avt_cos5_STR028b2,
    avt_cos7_STR028b2, avt_cos8_STR028b2, avt_sin1_STR028b2, avt_sin2_STR028b2, avt_sin3_STR028b2,
    avt_sin4_STR028b2, avt_sin5_STR028b2, avt_sin6_STR028b2, avt_sin7_STR028b2, avt_sin8_STR028b2]
  unfold m1_STR028b2 m2_STR028b2
  ring

theorem cos2_STR028b2 (θ : ℝ) : Real.cos (2 * θ) = (Real.cos θ)^2 - (Real.sin θ)^2 := by
  rw [show (2:ℝ)*θ = θ+θ by ring, Real.cos_add]; ring

theorem sin2_STR028b2 (θ : ℝ) : Real.sin (2 * θ) = 2*(Real.cos θ)*(Real.sin θ) := by
  rw [show (2:ℝ)*θ = θ+θ by ring, Real.sin_add]; ring

theorem cos3_STR028b2 (θ : ℝ) : Real.cos (3 * θ) = (Real.cos θ)^3 - 3*(Real.cos θ)*(Real.sin θ)^2 := by
  rw [show (3:ℝ)*θ = 2*θ+θ by ring, Real.cos_add, cos2_STR028b2, sin2_STR028b2]; ring

theorem sin3_STR028b2 (θ : ℝ) : Real.sin (3 * θ) = 3*(Real.cos θ)^2*(Real.sin θ) - (Real.sin θ)^3 := by
  rw [show (3:ℝ)*θ = 2*θ+θ by ring, Real.sin_add, cos2_STR028b2, sin2_STR028b2]; ring

theorem cos4_STR028b2 (θ : ℝ) : Real.cos (4 * θ) = (Real.cos θ)^4 - 6*(Real.cos θ)^2*(Real.sin θ)^2 + (Real.sin θ)^4 := by
  rw [show (4:ℝ)*θ = 3*θ+θ by ring, Real.cos_add, cos3_STR028b2, sin3_STR028b2]; ring

theorem sin4_STR028b2 (θ : ℝ) : Real.sin (4 * θ) = 4*(Real.cos θ)^3*(Real.sin θ) - 4*(Real.cos θ)*(Real.sin θ)^3 := by
  rw [show (4:ℝ)*θ = 3*θ+θ by ring, Real.sin_add, cos3_STR028b2, sin3_STR028b2]; ring

theorem cos5_STR028b2 (θ : ℝ) : Real.cos (5 * θ) = (Real.cos θ)^5 - 10*(Real.cos θ)^3*(Real.sin θ)^2 + 5*(Real.cos θ)*(Real.sin θ)^4 := by
  rw [show (5:ℝ)*θ = 4*θ+θ by ring, Real.cos_add, cos4_STR028b2, sin4_STR028b2]; ring

theorem sin5_STR028b2 (θ : ℝ) : Real.sin (5 * θ) = 5*(Real.cos θ)^4*(Real.sin θ) - 10*(Real.cos θ)^2*(Real.sin θ)^3 + (Real.sin θ)^5 := by
  rw [show (5:ℝ)*θ = 4*θ+θ by ring, Real.sin_add, cos4_STR028b2, sin4_STR028b2]; ring

theorem cos6_STR028b2 (θ : ℝ) : Real.cos (6 * θ) = (Real.cos θ)^6 - 15*(Real.cos θ)^4*(Real.sin θ)^2 + 15*(Real.cos θ)^2*(Real.sin θ)^4 - (Real.sin θ)^6 := by
  rw [show (6:ℝ)*θ = 5*θ+θ by ring, Real.cos_add, cos5_STR028b2, sin5_STR028b2]; ring

theorem sin6_STR028b2 (θ : ℝ) : Real.sin (6 * θ) = 6*(Real.cos θ)^5*(Real.sin θ) - 20*(Real.cos θ)^3*(Real.sin θ)^3 + 6*(Real.cos θ)*(Real.sin θ)^5 := by
  rw [show (6:ℝ)*θ = 5*θ+θ by ring, Real.sin_add, cos5_STR028b2, sin5_STR028b2]; ring

theorem cos7_STR028b2 (θ : ℝ) : Real.cos (7 * θ) = (Real.cos θ)^7 - 21*(Real.cos θ)^5*(Real.sin θ)^2 + 35*(Real.cos θ)^3*(Real.sin θ)^4 - 7*(Real.cos θ)*(Real.sin θ)^6 := by
  rw [show (7:ℝ)*θ = 6*θ+θ by ring, Real.cos_add, cos6_STR028b2, sin6_STR028b2]; ring

theorem sin7_STR028b2 (θ : ℝ) : Real.sin (7 * θ) = 7*(Real.cos θ)^6*(Real.sin θ) - 35*(Real.cos θ)^4*(Real.sin θ)^3 + 21*(Real.cos θ)^2*(Real.sin θ)^5 - (Real.sin θ)^7 := by
  rw [show (7:ℝ)*θ = 6*θ+θ by ring, Real.sin_add, cos6_STR028b2, sin6_STR028b2]; ring

theorem cos8_STR028b2 (θ : ℝ) : Real.cos (8 * θ) = (Real.cos θ)^8 - 28*(Real.cos θ)^6*(Real.sin θ)^2 + 70*(Real.cos θ)^4*(Real.sin θ)^4 - 28*(Real.cos θ)^2*(Real.sin θ)^6 + (Real.sin θ)^8 := by
  rw [show (8:ℝ)*θ = 7*θ+θ by ring, Real.cos_add, cos7_STR028b2, sin7_STR028b2]; ring

theorem sin8_STR028b2 (θ : ℝ) : Real.sin (8 * θ) = 8*(Real.cos θ)^7*(Real.sin θ) - 56*(Real.cos θ)^5*(Real.sin θ)^3 + 56*(Real.cos θ)^3*(Real.sin θ)^5 - 8*(Real.cos θ)*(Real.sin θ)^7 := by
  rw [show (8:ℝ)*θ = 7*θ+θ by ring, Real.sin_add, cos7_STR028b2, sin7_STR028b2]; ring

noncomputable def u1F_STR028b2 (a b θ : ℝ) : ℝ := a * Real.cos θ + b * Real.sin θ
noncomputable def v1F_STR028b2 (a b θ : ℝ) : ℝ := -a * Real.sin θ + b * Real.cos θ
noncomputable def wF_STR028b2 (c2 s2 c4 s4 θ : ℝ) : ℝ :=
  c2 * Real.cos (2 * θ) + s2 * Real.sin (2 * θ) + c4 * Real.cos (4 * θ) + s4 * Real.sin (4 * θ)
noncomputable def zF_STR028b2 (c2 s2 c4 s4 θ : ℝ) : ℝ :=
  2 * (-c2 * Real.sin (2 * θ) + s2 * Real.cos (2 * θ)) + 4 * (-c4 * Real.sin (4 * θ) + s4 * Real.cos (4 * θ))

theorem uF_split_STR028b2 (a b c2 s2 c4 s4 θ : ℝ) :
    uF_STR028b2 a b c2 s2 c4 s4 θ = u1F_STR028b2 a b θ + wF_STR028b2 c2 s2 c4 s4 θ := by
  unfold uF_STR028b2 u1F_STR028b2 wF_STR028b2; ring

theorem dF_split_STR028b2 (a b c2 s2 c4 s4 θ : ℝ) :
    dF_STR028b2 a b c2 s2 c4 s4 θ = v1F_STR028b2 a b θ + zF_STR028b2 c2 s2 c4 s4 θ := by
  unfold dF_STR028b2 v1F_STR028b2 zF_STR028b2; ring

noncomputable def ga_STR028b2 (a b θ : ℝ) : ℝ :=
  -(u1F_STR028b2 a b θ)^2 + (v1F_STR028b2 a b θ)^2

theorem eq_ga_STR028b2 (a b : ℝ) :
    ga_STR028b2 a b = four8_STR028b2 (0) (0) (0) (-a^2 + b^2) (-2*a*b) (0) (0) (0) (0) (0) (0) (0) (0) (0) (0) (0) (0) := by
  funext θ
  unfold ga_STR028b2 four8_STR028b2 u1F_STR028b2 v1F_STR028b2
  simp only [cos2_STR028b2, sin2_STR028b2, cos3_STR028b2, sin3_STR028b2, cos4_STR028b2, sin4_STR028b2, cos5_STR028b2, sin5_STR028b2, cos6_STR028b2, sin6_STR028b2, cos7_STR028b2, sin7_STR028b2, cos8_STR028b2, sin8_STR028b2]
  linear_combination (0) * Real.cos_sq_add_sin_sq θ

theorem cont_ga_STR028b2 (a b : ℝ) : Continuous (ga_STR028b2 a b ) := by
  rw [eq_ga_STR028b2]; exact four8_cont_STR028b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem avt_ga_STR028b2 (h : ℝ) (a b : ℝ) :
    avt_STR028b2 h (ga_STR028b2 a b ) = (0) + (0) * m1_STR028b2 h + (0) * m2_STR028b2 h := by
  rw [eq_ga_STR028b2]; exact avt_four8_STR028b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

noncomputable def gb_STR028b2 (a b c2 s2 c4 s4 θ : ℝ) : ℝ :=
  -2*(u1F_STR028b2 a b θ)*(wF_STR028b2 c2 s2 c4 s4 θ) + 2*(v1F_STR028b2 a b θ)*(zF_STR028b2 c2 s2 c4 s4 θ)

theorem eq_gb_STR028b2 (a b c2 s2 c4 s4 : ℝ) :
    gb_STR028b2 a b c2 s2 c4 s4 = four8_STR028b2 (0) (a*c2 + b*s2) (a*s2 - b*c2) (0) (0) (-3*a*c2 + 3*a*c4 + 3*b*s2 + 3*b*s4) (-3*a*s2 + 3*a*s4 - 3*b*c2 - 3*b*c4) (0) (0) (-5*a*c4 + 5*b*s4) (-5*a*s4 - 5*b*c4) (0) (0) (0) (0) (0) (0) := by
  funext θ
  unfold gb_STR028b2 four8_STR028b2 u1F_STR028b2 v1F_STR028b2 wF_STR028b2 zF_STR028b2
  simp only [cos2_STR028b2, sin2_STR028b2, cos3_STR028b2, sin3_STR028b2, cos4_STR028b2, sin4_STR028b2, cos5_STR028b2, sin5_STR028b2, cos6_STR028b2, sin6_STR028b2, cos7_STR028b2, sin7_STR028b2, cos8_STR028b2, sin8_STR028b2]
  linear_combination ((Real.cos θ)^3*(3*a*c4 + 3*b*s4) + (Real.cos θ)^2*(Real.sin θ)*(9*a*s4 - 9*b*c4) + (Real.cos θ)*(Real.sin θ)^2*(-9*a*c4 - 9*b*s4) + (Real.cos θ)*(a*c2 + b*s2) + (Real.sin θ)^3*(-3*a*s4 + 3*b*c4) + (Real.sin θ)*(a*s2 - b*c2)) * Real.cos_sq_add_sin_sq θ

theorem cont_gb_STR028b2 (a b c2 s2 c4 s4 : ℝ) : Continuous (gb_STR028b2 a b c2 s2 c4 s4 ) := by
  rw [eq_gb_STR028b2]; exact four8_cont_STR028b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem avt_gb_STR028b2 (h : ℝ) (a b c2 s2 c4 s4 : ℝ) :
    avt_STR028b2 h (gb_STR028b2 a b c2 s2 c4 s4 ) = (0) + (-3*a*c2 + 3*a*c4 + 3*b*s2 + 3*b*s4) * m1_STR028b2 h + (0) * m2_STR028b2 h := by
  rw [eq_gb_STR028b2]; exact avt_four8_STR028b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

noncomputable def gc_STR028b2 (c2 s2 c4 s4 θ : ℝ) : ℝ :=
  -(wF_STR028b2 c2 s2 c4 s4 θ)^2 + (zF_STR028b2 c2 s2 c4 s4 θ)^2

theorem eq_gc_STR028b2 (c2 s2 c4 s4 : ℝ) :
    gc_STR028b2 c2 s2 c4 s4 = four8_STR028b2 (3*c2^2/2 + 15*c4^2/2 + 3*s2^2/2 + 15*s4^2/2) (0) (0) (7*c2*c4 + 7*s2*s4) (7*c2*s4 - 7*c4*s2) (0) (0) (-5*c2^2/2 + 5*s2^2/2) (-5*c2*s2) (0) (0) (-9*c2*c4 + 9*s2*s4) (-9*c2*s4 - 9*c4*s2) (0) (0) (-17*c4^2/2 + 17*s4^2/2) (-17*c4*s4) := by
  funext θ
  unfold gc_STR028b2 four8_STR028b2 wF_STR028b2 zF_STR028b2
  simp only [cos2_STR028b2, sin2_STR028b2, cos3_STR028b2, sin3_STR028b2, cos4_STR028b2, sin4_STR028b2, cos5_STR028b2, sin5_STR028b2, cos6_STR028b2, sin6_STR028b2, cos7_STR028b2, sin7_STR028b2, cos8_STR028b2, sin8_STR028b2]
  linear_combination ((Real.cos θ)^6*(15*c4^2/2 + 15*s4^2/2) + (Real.cos θ)^4*(Real.sin θ)^2*(45*c4^2/2 + 45*s4^2/2) + (Real.cos θ)^4*(7*c2*c4 + 15*c4^2/2 + 7*s2*s4 + 15*s4^2/2) + (Real.cos θ)^3*(Real.sin θ)*(14*c2*s4 - 14*c4*s2) + (Real.cos θ)^2*(Real.sin θ)^4*(45*c4^2/2 + 45*s4^2/2) + (Real.cos θ)^2*(Real.sin θ)^2*(15*c4^2 + 15*s4^2) + (Real.cos θ)^2*(3*c2^2/2 + 7*c2*c4 + 15*c4^2/2 + 3*s2^2/2 + 7*s2*s4 + 15*s4^2/2) + (Real.cos θ)*(Real.sin θ)^3*(14*c2*s4 - 14*c4*s2) + (Real.cos θ)*(Real.sin θ)*(14*c2*s4 - 14*c4*s2) + (Real.sin θ)^6*(15*c4^2/2 + 15*s4^2/2) + (Real.sin θ)^4*(-7*c2*c4 + 15*c4^2/2 - 7*s2*s4 + 15*s4^2/2) + (Real.sin θ)^2*(3*c2^2/2 - 7*c2*c4 + 15*c4^2/2 + 3*s2^2/2 - 7*s2*s4 + 15*s4^2/2) + 3*c2^2/2 + 15*c4^2/2 + 3*s2^2/2 + 15*s4^2/2) * Real.cos_sq_add_sin_sq θ

theorem cont_gc_STR028b2 (c2 s2 c4 s4 : ℝ) : Continuous (gc_STR028b2 c2 s2 c4 s4 ) := by
  rw [eq_gc_STR028b2]; exact four8_cont_STR028b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem avt_gc_STR028b2 (h : ℝ) (c2 s2 c4 s4 : ℝ) :
    avt_STR028b2 h (gc_STR028b2 c2 s2 c4 s4 ) = (3*c2^2/2 + 15*c4^2/2 + 3*s2^2/2 + 15*s4^2/2) + (0) * m1_STR028b2 h + (-9*c2*c4 + 9*s2*s4) * m2_STR028b2 h := by
  rw [eq_gc_STR028b2]; exact avt_four8_STR028b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

noncomputable def gd_STR028b2 (a b θ : ℝ) : ℝ :=
  -2*(u1F_STR028b2 a b θ)^3/3 + (u1F_STR028b2 a b θ)*(v1F_STR028b2 a b θ)^2

theorem eq_gd_STR028b2 (a b : ℝ) :
    gd_STR028b2 a b = four8_STR028b2 (0) (a*(-a^2 - b^2)/4) (b*(-a^2 - b^2)/4) (0) (0) (5*a*(-a^2 + 3*b^2)/12) (5*b*(-3*a^2 + b^2)/12) (0) (0) (0) (0) (0) (0) (0) (0) (0) (0) := by
  funext θ
  unfold gd_STR028b2 four8_STR028b2 u1F_STR028b2 v1F_STR028b2
  simp only [cos2_STR028b2, sin2_STR028b2, cos3_STR028b2, sin3_STR028b2, cos4_STR028b2, sin4_STR028b2, cos5_STR028b2, sin5_STR028b2, cos6_STR028b2, sin6_STR028b2, cos7_STR028b2, sin7_STR028b2, cos8_STR028b2, sin8_STR028b2]
  linear_combination ((Real.cos θ)*(-a^3/4 - a*b^2/4) + (Real.sin θ)*(-a^2*b/4 - b^3/4)) * Real.cos_sq_add_sin_sq θ

theorem cont_gd_STR028b2 (a b : ℝ) : Continuous (gd_STR028b2 a b ) := by
  rw [eq_gd_STR028b2]; exact four8_cont_STR028b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem avt_gd_STR028b2 (h : ℝ) (a b : ℝ) :
    avt_STR028b2 h (gd_STR028b2 a b ) = (0) + (5*a*(-a^2 + 3*b^2)/12) * m1_STR028b2 h + (0) * m2_STR028b2 h := by
  rw [eq_gd_STR028b2]; exact avt_four8_STR028b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

noncomputable def ge_STR028b2 (a b c2 s2 c4 s4 θ : ℝ) : ℝ :=
  -2*(u1F_STR028b2 a b θ)^2*(wF_STR028b2 c2 s2 c4 s4 θ) + 2*(u1F_STR028b2 a b θ)*(v1F_STR028b2 a b θ)*(zF_STR028b2 c2 s2 c4 s4 θ) + (v1F_STR028b2 a b θ)^2*(wF_STR028b2 c2 s2 c4 s4 θ)

theorem eq_ge_STR028b2 (a b c2 s2 c4 s4 : ℝ) :
    ge_STR028b2 a b c2 s2 c4 s4 = four8_STR028b2 (a^2*c2/4 + a*b*s2/2 - b^2*c2/4) (0) (0) (-a^2*c2/2 + 5*a^2*c4/4 + 5*a*b*s4/2 - b^2*c2/2 - 5*b^2*c4/4) (-a^2*s2/2 + 5*a^2*s4/4 - 5*a*b*c4/2 - b^2*s2/2 - 5*b^2*s4/4) (0) (0) (-7*a^2*c2/4 - a^2*c4/2 + 7*a*b*s2/2 + 7*b^2*c2/4 - b^2*c4/2) (-7*a^2*s2/4 - a^2*s4/2 - 7*a*b*c2/2 + 7*b^2*s2/4 - b^2*s4/2) (0) (0) (-11*a^2*c4/4 + 11*a*b*s4/2 + 11*b^2*c4/4) (-11*a^2*s4/4 - 11*a*b*c4/2 + 11*b^2*s4/4) (0) (0) (0) (0) := by
  funext θ
  unfold ge_STR028b2 four8_STR028b2 u1F_STR028b2 v1F_STR028b2 wF_STR028b2 zF_STR028b2
  simp only [cos2_STR028b2, sin2_STR028b2, cos3_STR028b2, sin3_STR028b2, cos4_STR028b2, sin4_STR028b2, cos5_STR028b2, sin5_STR028b2, cos6_STR028b2, sin6_STR028b2, cos7_STR028b2, sin7_STR028b2, cos8_STR028b2, sin8_STR028b2]
  linear_combination ((Real.cos θ)^4*(3*a^2*c4/4 + 5*a*b*s4/2 - 7*b^2*c4/4) + (Real.cos θ)^3*(Real.sin θ)*(a^2*s4/2 - 5*a*b*c4 - 9*b^2*s4/2) + (Real.cos θ)^2*(Real.sin θ)^2*(3*a^2*c4 + 3*b^2*c4) + (Real.cos θ)^2*(-a^2*c2/4 + 5*a^2*c4/4 + a*b*s2/2 + 5*a*b*s4/2 - 3*b^2*c2/4 - 5*b^2*c4/4) + (Real.cos θ)*(Real.sin θ)^3*(9*a^2*s4/2 - 5*a*b*c4 - b^2*s4/2) + (Real.cos θ)*(Real.sin θ)*(-a^2*s2 + 5*a^2*s4/2 - 5*a*b*c4 - b^2*s2 - 5*b^2*s4/2) + (Real.sin θ)^4*(-7*a^2*c4/4 - 5*a*b*s4/2 + 3*b^2*c4/4) + (Real.sin θ)^2*(3*a^2*c2/4 - 5*a^2*c4/4 + a*b*s2/2 - 5*a*b*s4/2 + b^2*c2/4 + 5*b^2*c4/4) + a^2*c2/4 + a*b*s2/2 - b^2*c2/4) * Real.cos_sq_add_sin_sq θ

theorem cont_ge_STR028b2 (a b c2 s2 c4 s4 : ℝ) : Continuous (ge_STR028b2 a b c2 s2 c4 s4 ) := by
  rw [eq_ge_STR028b2]; exact four8_cont_STR028b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem avt_ge_STR028b2 (h : ℝ) (a b c2 s2 c4 s4 : ℝ) :
    avt_STR028b2 h (ge_STR028b2 a b c2 s2 c4 s4 ) = (a^2*c2/4 + a*b*s2/2 - b^2*c2/4) + (0) * m1_STR028b2 h + (-11*a^2*c4/4 + 11*a*b*s4/2 + 11*b^2*c4/4) * m2_STR028b2 h := by
  rw [eq_ge_STR028b2]; exact avt_four8_STR028b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

noncomputable def gf_STR028b2 (a b θ : ℝ) : ℝ :=
  -(u1F_STR028b2 a b θ)^4/4 + (u1F_STR028b2 a b θ)^2*(v1F_STR028b2 a b θ)^2/2

theorem eq_gf_STR028b2 (a b : ℝ) :
    gf_STR028b2 a b = four8_STR028b2 (-a^4/32 - a^2*b^2/16 - b^4/32) (0) (0) (-a^4/8 + b^4/8) (a*b*(-a^2 - b^2)/4) (0) (0) (-3*a^4/32 + 9*a^2*b^2/16 - 3*b^4/32) (3*a*b*(-a^2 + b^2)/8) (0) (0) (0) (0) (0) (0) (0) (0) := by
  funext θ
  unfold gf_STR028b2 four8_STR028b2 u1F_STR028b2 v1F_STR028b2
  simp only [cos2_STR028b2, sin2_STR028b2, cos3_STR028b2, sin3_STR028b2, cos4_STR028b2, sin4_STR028b2, cos5_STR028b2, sin5_STR028b2, cos6_STR028b2, sin6_STR028b2, cos7_STR028b2, sin7_STR028b2, cos8_STR028b2, sin8_STR028b2]
  linear_combination ((Real.cos θ)^2*(-5*a^4/32 - a^2*b^2/16 + 3*b^4/32) + (Real.cos θ)*(Real.sin θ)*(-a^3*b/2 - a*b^3/2) + (Real.sin θ)^2*(3*a^4/32 - a^2*b^2/16 - 5*b^4/32) - a^4/32 - a^2*b^2/16 - b^4/32) * Real.cos_sq_add_sin_sq θ

theorem cont_gf_STR028b2 (a b : ℝ) : Continuous (gf_STR028b2 a b ) := by
  rw [eq_gf_STR028b2]; exact four8_cont_STR028b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem avt_gf_STR028b2 (h : ℝ) (a b : ℝ) :
    avt_STR028b2 h (gf_STR028b2 a b ) = (-a^4/32 - a^2*b^2/16 - b^4/32) + (0) * m1_STR028b2 h + (0) * m2_STR028b2 h := by
  rw [eq_gf_STR028b2]; exact avt_four8_STR028b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

noncomputable def gu1_STR028b2 (a b θ : ℝ) : ℝ :=
  (u1F_STR028b2 a b θ)^2

theorem eq_gu1_STR028b2 (a b : ℝ) :
    gu1_STR028b2 a b = four8_STR028b2 (a^2/2 + b^2/2) (0) (0) (a^2/2 - b^2/2) (a*b) (0) (0) (0) (0) (0) (0) (0) (0) (0) (0) (0) (0) := by
  funext θ
  unfold gu1_STR028b2 four8_STR028b2 u1F_STR028b2
  simp only [cos2_STR028b2, sin2_STR028b2, cos3_STR028b2, sin3_STR028b2, cos4_STR028b2, sin4_STR028b2, cos5_STR028b2, sin5_STR028b2, cos6_STR028b2, sin6_STR028b2, cos7_STR028b2, sin7_STR028b2, cos8_STR028b2, sin8_STR028b2]
  linear_combination (a^2/2 + b^2/2) * Real.cos_sq_add_sin_sq θ

theorem cont_gu1_STR028b2 (a b : ℝ) : Continuous (gu1_STR028b2 a b ) := by
  rw [eq_gu1_STR028b2]; exact four8_cont_STR028b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem avt_gu1_STR028b2 (h : ℝ) (a b : ℝ) :
    avt_STR028b2 h (gu1_STR028b2 a b ) = (a^2/2 + b^2/2) + (0) * m1_STR028b2 h + (0) * m2_STR028b2 h := by
  rw [eq_gu1_STR028b2]; exact avt_four8_STR028b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

noncomputable def gv1_STR028b2 (a b θ : ℝ) : ℝ :=
  (v1F_STR028b2 a b θ)^2

theorem eq_gv1_STR028b2 (a b : ℝ) :
    gv1_STR028b2 a b = four8_STR028b2 (a^2/2 + b^2/2) (0) (0) (-a^2/2 + b^2/2) (-a*b) (0) (0) (0) (0) (0) (0) (0) (0) (0) (0) (0) (0) := by
  funext θ
  unfold gv1_STR028b2 four8_STR028b2 v1F_STR028b2
  simp only [cos2_STR028b2, sin2_STR028b2, cos3_STR028b2, sin3_STR028b2, cos4_STR028b2, sin4_STR028b2, cos5_STR028b2, sin5_STR028b2, cos6_STR028b2, sin6_STR028b2, cos7_STR028b2, sin7_STR028b2, cos8_STR028b2, sin8_STR028b2]
  linear_combination (a^2/2 + b^2/2) * Real.cos_sq_add_sin_sq θ

theorem cont_gv1_STR028b2 (a b : ℝ) : Continuous (gv1_STR028b2 a b ) := by
  rw [eq_gv1_STR028b2]; exact four8_cont_STR028b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem avt_gv1_STR028b2 (h : ℝ) (a b : ℝ) :
    avt_STR028b2 h (gv1_STR028b2 a b ) = (a^2/2 + b^2/2) + (0) * m1_STR028b2 h + (0) * m2_STR028b2 h := by
  rw [eq_gv1_STR028b2]; exact avt_four8_STR028b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

noncomputable def gU_STR028b2 (a b c2 s2 c4 s4 θ : ℝ) : ℝ :=
  (u1F_STR028b2 a b θ) + (wF_STR028b2 c2 s2 c4 s4 θ)

theorem eq_gU_STR028b2 (a b c2 s2 c4 s4 : ℝ) :
    gU_STR028b2 a b c2 s2 c4 s4 = four8_STR028b2 (0) (a) (b) (c2) (s2) (0) (0) (c4) (s4) (0) (0) (0) (0) (0) (0) (0) (0) := by
  funext θ
  unfold gU_STR028b2 four8_STR028b2 u1F_STR028b2 wF_STR028b2
  simp only [cos2_STR028b2, sin2_STR028b2, cos3_STR028b2, sin3_STR028b2, cos4_STR028b2, sin4_STR028b2, cos5_STR028b2, sin5_STR028b2, cos6_STR028b2, sin6_STR028b2, cos7_STR028b2, sin7_STR028b2, cos8_STR028b2, sin8_STR028b2]
  linear_combination (0) * Real.cos_sq_add_sin_sq θ

theorem cont_gU_STR028b2 (a b c2 s2 c4 s4 : ℝ) : Continuous (gU_STR028b2 a b c2 s2 c4 s4 ) := by
  rw [eq_gU_STR028b2]; exact four8_cont_STR028b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem avt_gU_STR028b2 (h : ℝ) (a b c2 s2 c4 s4 : ℝ) :
    avt_STR028b2 h (gU_STR028b2 a b c2 s2 c4 s4 ) = (0) + (0) * m1_STR028b2 h + (0) * m2_STR028b2 h := by
  rw [eq_gU_STR028b2]; exact avt_four8_STR028b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem RT_pow_STR028b2 {R T : ℝ} (hR : 0 ≤ R) (hRT : R ≤ T) (hT1 : T ≤ 1) (p q : ℕ)
    (hp : 2 ≤ p) (hpq : 5 ≤ p + q) : R ^ p * T ^ q ≤ R ^ 2 * T ^ 3 := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
  have hT0 : 0 ≤ T := hR.trans hRT
  calc R ^ (p' + 2) * T ^ q = R ^ 2 * (R ^ p' * T ^ q) := by ring
    _ ≤ R ^ 2 * (T ^ p' * T ^ q) := by gcongr
    _ = R ^ 2 * T ^ (p' + q) := by rw [pow_add]
    _ ≤ R ^ 2 * T ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hT0 hT1 (by omega)) (by positivity)

theorem term_STR028b2 {R T u v w z : ℝ} (hR : 0 ≤ R) (hRT : R ≤ T) (hT1 : T ≤ 1)
    (hu : |u| ≤ R) (hv : |v| ≤ R) (hw : |w| ≤ 4 * (R * T)) (hz : |z| ≤ 12 * (R * T))
    (i j k l : ℕ) (hp : 2 ≤ i + j + k + l) (hq : 5 ≤ 2 * (k + l) + i + j) :
    |u ^ i * v ^ j * w ^ k * z ^ l| ≤ 4 ^ k * 12 ^ l * (R ^ 2 * T ^ 3) := by
  have hT0 : 0 ≤ T := hR.trans hRT
  have h1 : |u ^ i * v ^ j * w ^ k * z ^ l| ≤
      R ^ i * R ^ j * (4 * (R * T)) ^ k * (12 * (R * T)) ^ l := by
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_pow, abs_pow]
    gcongr
  have h2 : R ^ i * R ^ j * (4 * (R * T)) ^ k * (12 * (R * T)) ^ l =
      4 ^ k * 12 ^ l * (R ^ (i + j + k + l) * T ^ (k + l)) := by ring
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := mul_le_mul_of_nonneg_left (RT_pow_STR028b2 hR hRT hT1 _ _ hp (by omega)) (by positivity)

theorem Rm_bound_STR028b2 {R T u v w z : ℝ} (hR : 0 ≤ R) (hRT : R ≤ T) (hT1 : T ≤ 1)
    (hu : |u| ≤ R) (hv : |v| ≤ R) (hw : |w| ≤ 4 * (R * T)) (hz : |z| ≤ 12 * (R * T)) :
    |(-1)*(u^3*v^0*w^1*z^0) + (1)*(u^2*v^1*w^0*z^1) + (-3/2)*(u^2*v^0*w^2*z^0) + (1/2)*(u^2*v^0*w^0*z^2) + (1)*(u^1*v^2*w^1*z^0) + (2)*(u^1*v^1*w^1*z^1) + (-1)*(u^1*v^0*w^3*z^0) + (-2)*(u^1*v^0*w^2*z^0) + (1)*(u^1*v^0*w^1*z^2) + (1)*(u^1*v^0*w^0*z^2) + (1/2)*(u^0*v^2*w^2*z^0) + (1)*(u^0*v^1*w^2*z^1) + (2)*(u^0*v^1*w^1*z^1) + (-1/4)*(u^0*v^0*w^4*z^0) + (-2/3)*(u^0*v^0*w^3*z^0) + (1/2)*(u^0*v^0*w^2*z^2) + (1)*(u^0*v^0*w^1*z^2)| ≤ 3159 * (R ^ 2 * T ^ 3) := by
  have t0 := abs_le.mp (term_STR028b2 hR hRT hT1 hu hv hw hz 3 0 1 0 (by norm_num) (by norm_num))
  have t1 := abs_le.mp (term_STR028b2 hR hRT hT1 hu hv hw hz 2 1 0 1 (by norm_num) (by norm_num))
  have t2 := abs_le.mp (term_STR028b2 hR hRT hT1 hu hv hw hz 2 0 2 0 (by norm_num) (by norm_num))
  have t3 := abs_le.mp (term_STR028b2 hR hRT hT1 hu hv hw hz 2 0 0 2 (by norm_num) (by norm_num))
  have t4 := abs_le.mp (term_STR028b2 hR hRT hT1 hu hv hw hz 1 2 1 0 (by norm_num) (by norm_num))
  have t5 := abs_le.mp (term_STR028b2 hR hRT hT1 hu hv hw hz 1 1 1 1 (by norm_num) (by norm_num))
  have t6 := abs_le.mp (term_STR028b2 hR hRT hT1 hu hv hw hz 1 0 3 0 (by norm_num) (by norm_num))
  have t7 := abs_le.mp (term_STR028b2 hR hRT hT1 hu hv hw hz 1 0 2 0 (by norm_num) (by norm_num))
  have t8 := abs_le.mp (term_STR028b2 hR hRT hT1 hu hv hw hz 1 0 1 2 (by norm_num) (by norm_num))
  have t9 := abs_le.mp (term_STR028b2 hR hRT hT1 hu hv hw hz 1 0 0 2 (by norm_num) (by norm_num))
  have t10 := abs_le.mp (term_STR028b2 hR hRT hT1 hu hv hw hz 0 2 2 0 (by norm_num) (by norm_num))
  have t11 := abs_le.mp (term_STR028b2 hR hRT hT1 hu hv hw hz 0 1 2 1 (by norm_num) (by norm_num))
  have t12 := abs_le.mp (term_STR028b2 hR hRT hT1 hu hv hw hz 0 1 1 1 (by norm_num) (by norm_num))
  have t13 := abs_le.mp (term_STR028b2 hR hRT hT1 hu hv hw hz 0 0 4 0 (by norm_num) (by norm_num))
  have t14 := abs_le.mp (term_STR028b2 hR hRT hT1 hu hv hw hz 0 0 3 0 (by norm_num) (by norm_num))
  have t15 := abs_le.mp (term_STR028b2 hR hRT hT1 hu hv hw hz 0 0 2 2 (by norm_num) (by norm_num))
  have t16 := abs_le.mp (term_STR028b2 hR hRT hT1 hu hv hw hz 0 0 1 2 (by norm_num) (by norm_num))
  rw [abs_le]
  constructor <;> linarith

theorem exp5_STR028b2 {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24)| ≤ |x| ^ 5 / 100 := by
  have h := Real.exp_bound hx (n := 5) (by norm_num)
  have e : ∑ m ∈ Finset.range 5, x ^ m / (m.factorial : ℝ) =
      1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  norm_num [Nat.factorial]
  ring

theorem exp3_STR028b2 {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ |x| ^ 3 * (2 / 9) := by
  have h := Real.exp_bound hx (n := 3) (by norm_num)
  have e : ∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ) = 1 + x + x ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  norm_num [Nat.factorial]

theorem exp2_STR028b2 {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x)| ≤ |x| ^ 2 * (3 / 4) := by
  have h := Real.exp_bound hx (n := 2) (by norm_num)
  have e : ∑ m ∈ Finset.range 2, x ^ m / (m.factorial : ℝ) = 1 + x := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  norm_num [Nat.factorial]

theorem exp1_STR028b2 {x : ℝ} (hx : |x| ≤ 1) : |Real.exp x - 1| ≤ |x| * 2 := by
  have h := Real.exp_bound hx (n := 1) (by norm_num)
  have e : ∑ m ∈ Finset.range 1, x ^ m / (m.factorial : ℝ) = 1 := by
    simp
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  norm_num [Nat.factorial]

theorem pt_bound_STR028b2 {R T u v w z : ℝ} (hR : 0 ≤ R) (hRT : R ≤ T) (hT1 : T ≤ 1 / 100)
    (hu : |u| ≤ R) (hv : |v| ≤ R) (hw : |w| ≤ 4 * (R * T)) (hz : |z| ≤ 12 * (R * T)) :
    |((v + z) ^ 2 - 2 * (u + w) + 2) * Real.exp (u + w) - 2 -
      ((v ^ 2 - u ^ 2) + (2 * v * z - 2 * u * w) + (z ^ 2 - w ^ 2) + (v ^ 2 * u - 2 / 3 * u ^ 3) +
        (v ^ 2 * w + 2 * u * v * z - 2 * u ^ 2 * w) + (v ^ 2 * u ^ 2 / 2 - u ^ 4 / 4))| ≤
      3300 * (R ^ 2 * T ^ 3) := by
  have hT0 : 0 ≤ T := hR.trans hRT
  have hT1' : T ≤ 1 := by linarith
  have hR1 : R ≤ 1 / 100 := hRT.trans hT1
  have hRT' : R * T ≤ R / 100 := by
    have := mul_le_mul_of_nonneg_left hT1 hR
    linarith
  have hx : |u + w| ≤ 2 * R := by
    have := abs_add_le u w
    linarith
  have hd : |v + z| ≤ 2 * R := by
    have := abs_add_le v z
    linarith
  have hx1 : |u + w| ≤ 1 := by linarith
  have hRm := Rm_bound_STR028b2 hR hRT hT1' hu hv hw hz
  have hE := exp5_STR028b2 hx1
  have hR5 : R ^ 5 ≤ R ^ 2 * T ^ 3 := by
    simpa using RT_pow_STR028b2 hR hRT hT1' 5 0 (by norm_num) (by norm_num)
  have hR5' : 0 ≤ R ^ 5 := pow_nonneg hR 5
  have hR6 : R ^ 6 ≤ R ^ 5 / 100 := by
    have : R ^ 6 = R * R ^ 5 := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right (hR1) hR5'
    linarith
  -- bound on exp remainder
  have hE' : |Real.exp (u + w) - (1 + (u + w) + (u + w) ^ 2 / 2 + (u + w) ^ 3 / 6 + (u + w) ^ 4 / 24)| ≤
      32 / 100 * R ^ 5 := by
    refine hE.trans ?_
    have h5 : |u + w| ^ 5 ≤ (2 * R) ^ 5 := pow_le_pow_left₀ (abs_nonneg _) hx 5
    have h6 : (2 * R) ^ 5 = 32 * R ^ 5 := by ring
    linarith
  have hA : |(v + z) ^ 2 - 2 * (u + w) + 2| ≤ 3 := by
    have h1 : |v + z| ^ 2 ≤ (2 * R) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hd 2
    rw [sq_abs] at h1
    have h2 := abs_le.mp hx
    rw [abs_le]
    have h3 : 0 ≤ (v + z) ^ 2 := sq_nonneg _
    have h4 : (2 * R) ^ 2 = 4 * R ^ 2 := by ring
    have h5 : R ^ 2 ≤ R / 100 := by nlinarith
    constructor <;> linarith
  have hB1 : |(v + z) ^ 2 * (u + w) ^ 3| ≤ 32 * R ^ 5 := by
    rw [abs_mul, abs_pow, abs_pow]
    calc _ ≤ (2 * R) ^ 2 * (2 * R) ^ 3 := by gcongr
      _ = 32 * R ^ 5 := by ring
  have hB2 : |(v + z) ^ 2 * (u + w) ^ 4| ≤ 64 * R ^ 6 := by
    rw [abs_mul, abs_pow, abs_pow]
    calc _ ≤ (2 * R) ^ 2 * (2 * R) ^ 4 := by gcongr
      _ = 64 * R ^ 6 := by ring
  have hB3 : |(u + w) ^ 5| ≤ 32 * R ^ 5 := by
    rw [abs_pow]
    calc _ ≤ (2 * R) ^ 5 := by gcongr
      _ = 32 * R ^ 5 := by ring
  have hB : |(v + z) ^ 2 * (u + w) ^ 3 / 6 + (v + z) ^ 2 * (u + w) ^ 4 / 24 - (u + w) ^ 5 / 12| ≤
      9 * R ^ 5 := by
    have a1 := abs_le.mp hB1
    have a2 := abs_le.mp hB2
    have a3 := abs_le.mp hB3
    rw [abs_le]
    constructor <;> linarith
  have hAE : |((v + z) ^ 2 - 2 * (u + w) + 2) *
      (Real.exp (u + w) - (1 + (u + w) + (u + w) ^ 2 / 2 + (u + w) ^ 3 / 6 + (u + w) ^ 4 / 24))| ≤
      3 * (32 / 100 * R ^ 5) := by
    rw [abs_mul]
    exact mul_le_mul hA hE' (abs_nonneg _) (by norm_num)
  have key : ((v + z) ^ 2 - 2 * (u + w) + 2) * Real.exp (u + w) - 2 -
      ((v ^ 2 - u ^ 2) + (2 * v * z - 2 * u * w) + (z ^ 2 - w ^ 2) + (v ^ 2 * u - 2 / 3 * u ^ 3) +
        (v ^ 2 * w + 2 * u * v * z - 2 * u ^ 2 * w) + (v ^ 2 * u ^ 2 / 2 - u ^ 4 / 4)) =
      ((v + z) ^ 2 - 2 * (u + w) + 2) *
        (Real.exp (u + w) - (1 + (u + w) + (u + w) ^ 2 / 2 + (u + w) ^ 3 / 6 + (u + w) ^ 4 / 24)) +
      ((v + z) ^ 2 * (u + w) ^ 3 / 6 + (v + z) ^ 2 * (u + w) ^ 4 / 24 - (u + w) ^ 5 / 12) +
      ((-1)*(u^3*v^0*w^1*z^0) + (1)*(u^2*v^1*w^0*z^1) + (-3/2)*(u^2*v^0*w^2*z^0) + (1/2)*(u^2*v^0*w^0*z^2) + (1)*(u^1*v^2*w^1*z^0) + (2)*(u^1*v^1*w^1*z^1) + (-1)*(u^1*v^0*w^3*z^0) + (-2)*(u^1*v^0*w^2*z^0) + (1)*(u^1*v^0*w^1*z^2) + (1)*(u^1*v^0*w^0*z^2) + (1/2)*(u^0*v^2*w^2*z^0) + (1)*(u^0*v^1*w^2*z^1) + (2)*(u^0*v^1*w^1*z^1) + (-1/4)*(u^0*v^0*w^4*z^0) + (-2/3)*(u^0*v^0*w^3*z^0) + (1/2)*(u^0*v^0*w^2*z^2) + (1)*(u^0*v^0*w^1*z^2)) := by ring
  rw [key]
  have b1 := abs_le.mp hAE
  have b2 := abs_le.mp hB
  have b3 := abs_le.mp hRm
  rw [abs_le]
  constructor <;> linarith

theorem N_pt_STR028b2 {R T u w : ℝ} (hR : 0 ≤ R) (hRT : R ≤ T) (hT1 : T ≤ 1 / 100)
    (hu : |u| ≤ R) (hw : |w| ≤ 4 * (R * T)) :
    |Real.exp (u + w) - (1 + (u + w) + u ^ 2 / 2)| ≤ 10 * (R ^ 2 * T) := by
  have hT0 : 0 ≤ T := hR.trans hRT
  have hRT' : R * T ≤ R / 100 := by
    have := mul_le_mul_of_nonneg_left hT1 hR
    linarith
  have hx : |u + w| ≤ 2 * R := by
    have := abs_add_le u w
    linarith
  have hx1 : |u + w| ≤ 1 := by linarith
  have e3 := exp3_STR028b2 hx1
  have h3 : |u + w| ^ 3 ≤ (2 * R) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hx 3
  have h3' : (2 * R) ^ 3 = 8 * (R ^ 2 * R) := by ring
  have hRR : R ^ 2 * R ≤ R ^ 2 * T := mul_le_mul_of_nonneg_left hRT (sq_nonneg R)
  have huw : |2 * u * w| ≤ 8 * (R ^ 2 * T) := by
    rw [abs_mul, abs_mul, abs_two]
    calc 2 * |u| * |w| ≤ 2 * R * (4 * (R * T)) := by gcongr
      _ = 8 * (R ^ 2 * T) := by ring
  have hww : |w ^ 2| ≤ 16 * (R ^ 2 * T) / 100 := by
    rw [abs_pow]
    calc |w| ^ 2 ≤ (4 * (R * T)) ^ 2 := by gcongr
      _ = 16 * (R ^ 2 * T) * T := by ring
      _ ≤ 16 * (R ^ 2 * T) * (1 / 100) := by gcongr
      _ = _ := by ring
  have a1 := abs_le.mp huw
  have a2 := abs_le.mp hww
  have a3 := abs_le.mp e3
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg (sq_nonneg R) hT0]

theorem M_pt_STR028b2 {R T u w : ℝ} (hR : 0 ≤ R) (hRT : R ≤ T) (hT1 : T ≤ 1 / 100)
    (hu : |u| ≤ R) (hw : |w| ≤ 4 * (R * T)) :
    |(u + w) * Real.exp (u + w) - ((u + w) + u ^ 2)| ≤ 20 * (R ^ 2 * T) := by
  have hT0 : 0 ≤ T := hR.trans hRT
  have hRT' : R * T ≤ R / 100 := by
    have := mul_le_mul_of_nonneg_left hT1 hR
    linarith
  have hx : |u + w| ≤ 2 * R := by
    have := abs_add_le u w
    linarith
  have hx1 : |u + w| ≤ 1 := by linarith
  have e2 := exp2_STR028b2 hx1
  have hRR : R ^ 2 * R ≤ R ^ 2 * T := mul_le_mul_of_nonneg_left hRT (sq_nonneg R)
  have hxe : |(u + w) * (Real.exp (u + w) - (1 + (u + w)))| ≤ 6 * (R ^ 2 * R) := by
    rw [abs_mul]
    have h2 : |u + w| ^ 2 ≤ (2 * R) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
    calc |u + w| * |Real.exp (u + w) - (1 + (u + w))| ≤ (2 * R) * (|u + w| ^ 2 * (3 / 4)) := by
          gcongr
      _ ≤ (2 * R) * ((2 * R) ^ 2 * (3 / 4)) := by gcongr
      _ = 6 * (R ^ 2 * R) := by ring
  have huw : |2 * u * w| ≤ 8 * (R ^ 2 * T) := by
    rw [abs_mul, abs_mul, abs_two]
    calc 2 * |u| * |w| ≤ 2 * R * (4 * (R * T)) := by gcongr
      _ = 8 * (R ^ 2 * T) := by ring
  have hww : |w ^ 2| ≤ 16 * (R ^ 2 * T) / 100 := by
    rw [abs_pow]
    calc |w| ^ 2 ≤ (4 * (R * T)) ^ 2 := by gcongr
      _ = 16 * (R ^ 2 * T) * T := by ring
      _ ≤ 16 * (R ^ 2 * T) * (1 / 100) := by gcongr
      _ = _ := by ring
  have a1 := abs_le.mp huw
  have a2 := abs_le.mp hww
  have a3 := abs_le.mp hxe
  have key : (u + w) * Real.exp (u + w) - ((u + w) + u ^ 2) =
      (u + w) * (Real.exp (u + w) - (1 + (u + w))) + (2 * u * w + w ^ 2) := by ring
  rw [key, abs_le]
  constructor <;> linarith

theorem P_pt_STR028b2 {R T u v w z : ℝ} (hR : 0 ≤ R) (hRT : R ≤ T) (hT1 : T ≤ 1 / 100)
    (hu : |u| ≤ R) (hv : |v| ≤ R) (hw : |w| ≤ 4 * (R * T)) (hz : |z| ≤ 12 * (R * T)) :
    |(v + z) * (v + z) * Real.exp (u + w) - v ^ 2| ≤ 50 * (R ^ 2 * T) := by
  have hT0 : 0 ≤ T := hR.trans hRT
  have hRT' : R * T ≤ R / 100 := by
    have := mul_le_mul_of_nonneg_left hT1 hR
    linarith
  have hx : |u + w| ≤ 2 * R := by
    have := abs_add_le u w
    linarith
  have hd : |v + z| ≤ 2 * R := by
    have := abs_add_le v z
    linarith
  have hx1 : |u + w| ≤ 1 := by linarith
  have e1 := exp1_STR028b2 hx1
  have hRR : R ^ 2 * R ≤ R ^ 2 * T := mul_le_mul_of_nonneg_left hRT (sq_nonneg R)
  have hde : |(v + z) * (v + z) * (Real.exp (u + w) - 1)| ≤ 16 * (R ^ 2 * R) := by
    rw [abs_mul, abs_mul]
    calc |v + z| * |v + z| * |Real.exp (u + w) - 1| ≤ (2 * R) * (2 * R) * (|u + w| * 2) := by
          gcongr
      _ ≤ (2 * R) * (2 * R) * ((2 * R) * 2) := by gcongr
      _ = 16 * (R ^ 2 * R) := by ring
  have hvz : |2 * v * z| ≤ 24 * (R ^ 2 * T) := by
    rw [abs_mul, abs_mul, abs_two]
    calc 2 * |v| * |z| ≤ 2 * R * (12 * (R * T)) := by gcongr
      _ = 24 * (R ^ 2 * T) := by ring
  have hzz : |z ^ 2| ≤ 144 * (R ^ 2 * T) / 100 := by
    rw [abs_pow]
    calc |z| ^ 2 ≤ (12 * (R * T)) ^ 2 := by gcongr
      _ = 144 * (R ^ 2 * T) * T := by ring
      _ ≤ 144 * (R ^ 2 * T) * (1 / 100) := by gcongr
      _ = _ := by ring
  have a1 := abs_le.mp hde
  have a2 := abs_le.mp hvz
  have a3 := abs_le.mp hzz
  have key : (v + z) * (v + z) * Real.exp (u + w) - v ^ 2 =
      (v + z) * (v + z) * (Real.exp (u + w) - 1) + (2 * v * z + z ^ 2) := by ring
  rw [key, abs_le]
  constructor <;> linarith

structure JH_STR028b2 (a b c2 s2 c4 s4 R T : ℝ) : Prop where
  hR : 0 ≤ R
  hab : a ^ 2 + b ^ 2 = R ^ 2
  hRT : R ≤ T
  hT : T ≤ 1 / 100
  hc2 : |c2| ≤ R * T
  hs2 : |s2| ≤ R * T
  hc4 : |c4| ≤ R * T
  hs4 : |s4| ≤ R * T

theorem pw_u1_STR028b2 {a b c2 s2 c4 s4 R T : ℝ} (H : JH_STR028b2 a b c2 s2 c4 s4 R T) (θ : ℝ) :
    |u1F_STR028b2 a b θ| ≤ R := by
  unfold u1F_STR028b2
  apply abs_le_of_sq_le_sq _ H.hR
  have h1 : (a * Real.cos θ + b * Real.sin θ) ^ 2 + (a * Real.sin θ - b * Real.cos θ) ^ 2 =
      (a ^ 2 + b ^ 2) * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
  rw [Real.cos_sq_add_sin_sq, mul_one, H.hab] at h1
  nlinarith [sq_nonneg (a * Real.sin θ - b * Real.cos θ)]

theorem pw_v1_STR028b2 {a b c2 s2 c4 s4 R T : ℝ} (H : JH_STR028b2 a b c2 s2 c4 s4 R T) (θ : ℝ) :
    |v1F_STR028b2 a b θ| ≤ R := by
  unfold v1F_STR028b2
  apply abs_le_of_sq_le_sq _ H.hR
  have h1 : (a * Real.cos θ + b * Real.sin θ) ^ 2 + (-a * Real.sin θ + b * Real.cos θ) ^ 2 =
      (a ^ 2 + b ^ 2) * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
  rw [Real.cos_sq_add_sin_sq, mul_one, H.hab] at h1
  nlinarith [sq_nonneg (a * Real.cos θ + b * Real.sin θ)]

theorem tm_STR028b2 {c B : ℝ} (t : ℝ) (hc : |c| ≤ B) (ht : |t| ≤ 1) : |c * t| ≤ B := by
  rw [abs_mul]
  calc |c| * |t| ≤ B * 1 := by gcongr; exact (abs_nonneg _).trans hc
    _ = B := mul_one B

theorem pw_w_STR028b2 {a b c2 s2 c4 s4 R T : ℝ} (H : JH_STR028b2 a b c2 s2 c4 s4 R T) (θ : ℝ) :
    |wF_STR028b2 c2 s2 c4 s4 θ| ≤ 4 * (R * T) := by
  unfold wF_STR028b2
  have t1 := abs_le.mp (tm_STR028b2 (Real.cos (2 * θ)) H.hc2 (Real.abs_cos_le_one _))
  have t2 := abs_le.mp (tm_STR028b2 (Real.sin (2 * θ)) H.hs2 (Real.abs_sin_le_one _))
  have t3 := abs_le.mp (tm_STR028b2 (Real.cos (4 * θ)) H.hc4 (Real.abs_cos_le_one _))
  have t4 := abs_le.mp (tm_STR028b2 (Real.sin (4 * θ)) H.hs4 (Real.abs_sin_le_one _))
  rw [abs_le]
  constructor <;> linarith

theorem pw_z_STR028b2 {a b c2 s2 c4 s4 R T : ℝ} (H : JH_STR028b2 a b c2 s2 c4 s4 R T) (θ : ℝ) :
    |zF_STR028b2 c2 s2 c4 s4 θ| ≤ 12 * (R * T) := by
  unfold zF_STR028b2
  have t1 := abs_le.mp (tm_STR028b2 (Real.sin (2 * θ)) H.hc2 (Real.abs_sin_le_one _))
  have t2 := abs_le.mp (tm_STR028b2 (Real.cos (2 * θ)) H.hs2 (Real.abs_cos_le_one _))
  have t3 := abs_le.mp (tm_STR028b2 (Real.sin (4 * θ)) H.hc4 (Real.abs_sin_le_one _))
  have t4 := abs_le.mp (tm_STR028b2 (Real.cos (4 * θ)) H.hs4 (Real.abs_cos_le_one _))
  rw [abs_le]
  constructor <;> linarith

theorem cont_uF_STR028b2 (a b c2 s2 c4 s4 : ℝ) : Continuous (uF_STR028b2 a b c2 s2 c4 s4) := by
  unfold uF_STR028b2; fun_prop

theorem cont_dF_STR028b2 (a b c2 s2 c4 s4 : ℝ) : Continuous (dF_STR028b2 a b c2 s2 c4 s4) := by
  unfold dF_STR028b2; fun_prop

theorem avt_close_STR028b2 (h : ℝ) {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G)
    {B A : ℝ} (hB : ∀ θ, |F θ - G θ| ≤ B) (hA : avt_STR028b2 h G = A) :
    |avt_STR028b2 h F - A| ≤ B := by
  have := avt_abs_le_STR028b2 h (F := fun θ => F θ - G θ) (hF.sub hG) hB
  rw [avt_sub_STR028b2 h hF hG, hA] at this
  exact this

theorem avt_lin3_STR028b2 (h c1 c2 c3 : ℝ) {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G) :
    avt_STR028b2 h (fun θ => c1 + c2 * F θ + c3 * G θ) =
      c1 + c2 * avt_STR028b2 h F + c3 * avt_STR028b2 h G := by
  have e1 := avt_add_STR028b2 h (F := fun θ => c1 + c2 * F θ) (G := fun θ => c3 * G θ)
    (by fun_prop) (by fun_prop)
  have e2 := avt_add_STR028b2 h (F := fun _ => c1) (G := fun θ => c2 * F θ) (by fun_prop) (by fun_prop)
  rw [e1, e2, avt_const_STR028b2, avt_const_mul_STR028b2, avt_const_mul_STR028b2]

theorem uF_eq_STR028b2 (a b c2 s2 c4 s4 : ℝ) :
    uF_STR028b2 a b c2 s2 c4 s4 = gU_STR028b2 a b c2 s2 c4 s4 := by
  funext θ
  rw [uF_split_STR028b2]; rfl

theorem crudeN_STR028b2 (h : ℝ) {a b c2 s2 c4 s4 R T : ℝ} (H : JH_STR028b2 a b c2 s2 c4 s4 R T) :
    |avt_STR028b2 h (fun θ => Real.exp (uF_STR028b2 a b c2 s2 c4 s4 θ)) - (1 + R ^ 2 / 4)| ≤
      10 * (R ^ 2 * T) := by
  have hc := cont_gU_STR028b2 a b c2 s2 c4 s4
  have hc1 := cont_gu1_STR028b2 a b
  refine avt_close_STR028b2 h (G := fun θ => 1 + 1 * gU_STR028b2 a b c2 s2 c4 s4 θ +
    (1 / 2) * gu1_STR028b2 a b θ) (by have := cont_uF_STR028b2 a b c2 s2 c4 s4; fun_prop)
    (by fun_prop) (fun θ => ?_) ?_
  · have := N_pt_STR028b2 H.hR H.hRT H.hT (pw_u1_STR028b2 H θ) (pw_w_STR028b2 H θ)
    have e : uF_STR028b2 a b c2 s2 c4 s4 θ = u1F_STR028b2 a b θ + wF_STR028b2 c2 s2 c4 s4 θ :=
      uF_split_STR028b2 _ _ _ _ _ _ _
    have e2 : gU_STR028b2 a b c2 s2 c4 s4 θ = u1F_STR028b2 a b θ + wF_STR028b2 c2 s2 c4 s4 θ := rfl
    have e3 : gu1_STR028b2 a b θ = (u1F_STR028b2 a b θ) ^ 2 := rfl
    rw [e, e2, e3]
    convert this using 2
    ring
  · rw [avt_lin3_STR028b2 h _ _ _ hc hc1, avt_gU_STR028b2, avt_gu1_STR028b2]
    have := H.hab
    nlinarith

theorem crudeM_STR028b2 (h : ℝ) {a b c2 s2 c4 s4 R T : ℝ} (H : JH_STR028b2 a b c2 s2 c4 s4 R T) :
    |avt_STR028b2 h (fun θ => uF_STR028b2 a b c2 s2 c4 s4 θ *
      Real.exp (uF_STR028b2 a b c2 s2 c4 s4 θ)) - R ^ 2 / 2| ≤ 20 * (R ^ 2 * T) := by
  have hc := cont_gU_STR028b2 a b c2 s2 c4 s4
  have hc1 := cont_gu1_STR028b2 a b
  have hu := cont_uF_STR028b2 a b c2 s2 c4 s4
  refine avt_close_STR028b2 h (G := fun θ => 0 + 1 * gU_STR028b2 a b c2 s2 c4 s4 θ +
    1 * gu1_STR028b2 a b θ) (by fun_prop) (by fun_prop) (fun θ => ?_) ?_
  · have := M_pt_STR028b2 H.hR H.hRT H.hT (pw_u1_STR028b2 H θ) (pw_w_STR028b2 H θ)
    have e : uF_STR028b2 a b c2 s2 c4 s4 θ = u1F_STR028b2 a b θ + wF_STR028b2 c2 s2 c4 s4 θ :=
      uF_split_STR028b2 _ _ _ _ _ _ _
    have e2 : gU_STR028b2 a b c2 s2 c4 s4 θ = u1F_STR028b2 a b θ + wF_STR028b2 c2 s2 c4 s4 θ := rfl
    have e3 : gu1_STR028b2 a b θ = (u1F_STR028b2 a b θ) ^ 2 := rfl
    rw [e, e2, e3]
    convert this using 2
    ring
  · rw [avt_lin3_STR028b2 h _ _ _ hc hc1, avt_gU_STR028b2, avt_gu1_STR028b2]
    have := H.hab
    nlinarith

theorem crudeP_STR028b2 (h : ℝ) {a b c2 s2 c4 s4 R T : ℝ} (H : JH_STR028b2 a b c2 s2 c4 s4 R T) :
    |avt_STR028b2 h (fun θ => dF_STR028b2 a b c2 s2 c4 s4 θ * dF_STR028b2 a b c2 s2 c4 s4 θ *
      Real.exp (uF_STR028b2 a b c2 s2 c4 s4 θ)) - R ^ 2 / 2| ≤ 50 * (R ^ 2 * T) := by
  have hc := cont_gU_STR028b2 a b c2 s2 c4 s4
  have hc1 := cont_gv1_STR028b2 a b
  have hu := cont_uF_STR028b2 a b c2 s2 c4 s4
  have hd := cont_dF_STR028b2 a b c2 s2 c4 s4
  refine avt_close_STR028b2 h (G := fun θ => 0 + 0 * gU_STR028b2 a b c2 s2 c4 s4 θ +
    1 * gv1_STR028b2 a b θ) (by fun_prop) (by fun_prop) (fun θ => ?_) ?_
  · have := P_pt_STR028b2 H.hR H.hRT H.hT (pw_u1_STR028b2 H θ) (pw_v1_STR028b2 H θ)
      (pw_w_STR028b2 H θ) (pw_z_STR028b2 H θ)
    have e : uF_STR028b2 a b c2 s2 c4 s4 θ = u1F_STR028b2 a b θ + wF_STR028b2 c2 s2 c4 s4 θ :=
      uF_split_STR028b2 _ _ _ _ _ _ _
    have e' : dF_STR028b2 a b c2 s2 c4 s4 θ = v1F_STR028b2 a b θ + zF_STR028b2 c2 s2 c4 s4 θ :=
      dF_split_STR028b2 _ _ _ _ _ _ _
    have e3 : gv1_STR028b2 a b θ = (v1F_STR028b2 a b θ) ^ 2 := rfl
    rw [e, e', e3]
    convert this using 2
    ring
  · rw [avt_lin3_STR028b2 h _ _ _ hc hc1, avt_gv1_STR028b2]
    have := H.hab
    nlinarith

theorem log1_STR028b2 {s : ℝ} (hs : |s| ≤ 1 / 2) : |Real.log (1 + s) - s| ≤ 2 * s ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -s) (by rw [abs_neg]; linarith) 1
  have e : ∑ i ∈ Finset.range 1, (-s) ^ (i + 1) / ((i : ℝ) + 1) = -s := by simp
  have e2 : (1 - -s) = 1 + s := by ring
  rw [e, e2, abs_neg] at h
  have hp : 0 ≤ |s| := abs_nonneg s
  have h3 : |s| ^ (1 + 1) / (1 - |s|) ≤ 2 * s ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    have : |s| ^ (1 + 1) = s ^ 2 := by rw [pow_two, pow_two, abs_mul_abs_self]
    rw [this]
    nlinarith [sq_nonneg s]
  have : -s + Real.log (1 + s) = Real.log (1 + s) - s := by ring
  rw [this] at h
  exact h.trans h3

theorem log2_STR028b2 {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |Real.log (1 + s) - s + s ^ 2 / 2| ≤ 2 * |s| ^ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -s) (by rw [abs_neg]; linarith) 2
  have e : ∑ i ∈ Finset.range 2, (-s) ^ (i + 1) / ((i : ℝ) + 1) = -s + s ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ]
  have e2 : (1 - -s) = 1 + s := by ring
  rw [e, e2, abs_neg] at h
  have hp : 0 ≤ |s| := abs_nonneg s
  have h3 : |s| ^ (2 + 1) / (1 - |s|) ≤ 2 * |s| ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    have : |s| ^ (2 + 1) = |s| ^ 3 := rfl
    rw [this]
    nlinarith [pow_nonneg hp 3, pow_nonneg hp 4]
  have : -s + s ^ 2 / 2 + Real.log (1 + s) = Real.log (1 + s) - s + s ^ 2 / 2 := by ring
  rw [this] at h
  exact h.trans h3

theorem eq1_STR028b2 {q s M P L : ℝ} (hN0 : (1 + s) ≠ 0) :
    P / (1 + s) - 2 * (M / (1 + s) - L) - (P - 2 * M + 2 * s + q ^ 2 / 16) =
        ((q / 4) * (2 * (M - q / 2) - (P - q / 2) - (s - q / 4)) +
          (s - q / 4) * (q / 4 + 2 * (M - q / 2) - (P - q / 2) - (s - q / 4))) +
        (P - 2 * M) * s ^ 2 / (1 + s) + 2 * (L - s + s ^ 2 / 2) := by
  field_simp
  ring

theorem eq2_STR028b2 {q s M L : ℝ} (hN0 : (1 + s) ≠ 0) :
    M / (1 + s) - L - q / 4 =
        (M - q / 2) - (s - q / 4) - M * s / (1 + s) - (L - s) := by
  field_simp
  ring

theorem qbounds_STR028b2 {q T : ℝ} (hq : 0 ≤ q) (hqT : q ≤ T ^ 2) (hT0 : 0 ≤ T)
    (hT1 : T ≤ 1 / 100) :
    q ≤ 1 / 10000 ∧ q * q ≤ q * T / 100 ∧ q * T ≤ q / 100 ∧ q ^ 2 * T ≤ q * T ^ 3 ∧
      q ^ 2 * T ^ 2 ≤ q ^ 2 * T / 100 ∧ q ^ 3 ≤ q * T ^ 3 := by
  have hT2 : T ^ 2 ≤ T * (1 / 100) := by
    have := mul_le_mul_of_nonneg_left hT1 hT0
    linarith
  have hqT' : q * T ≤ q / 100 := by
    have := mul_le_mul_of_nonneg_left hT1 hq
    linarith
  have hq1 : q ≤ 1 / 10000 := by
    have : T ^ 2 ≤ 1 / 100 * (1 / 100) := by
      have := mul_le_mul_of_nonneg_left hT1 hT0
      have h2 : T * (1 / 100) ≤ 1 / 100 * (1 / 100) := mul_le_mul_of_nonneg_right hT1 (by norm_num)
      linarith
    linarith
  have hq2 : q * q ≤ q * T / 100 := by
    calc q * q ≤ q * T ^ 2 := mul_le_mul_of_nonneg_left hqT hq
      _ ≤ q * (T * (1 / 100)) := mul_le_mul_of_nonneg_left hT2 hq
      _ = q * T / 100 := by ring
  have r1 : q ^ 2 * T ≤ q * T ^ 3 := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqT hq) hT0
    have c1 : q * T ^ 2 * T = q * T ^ 3 := by ring
    have c2 : q * q * T = q ^ 2 * T := by ring
    linarith
  have r2 : q ^ 2 * T ^ 2 ≤ q ^ 2 * T / 100 := by
    have := mul_le_mul_of_nonneg_left hT2 (sq_nonneg q)
    linarith
  have r3 : q ^ 3 ≤ q * T ^ 3 := by
    have h4 : q ^ 2 ≤ T ^ 3 := by
      have a := pow_le_pow_left₀ hq hqT 2
      have b : T ^ 4 ≤ T ^ 3 := pow_le_pow_of_le_one hT0 (by linarith) (by norm_num)
      have c : (T ^ 2) ^ 2 = T ^ 4 := by ring
      linarith
    have := mul_le_mul_of_nonneg_left h4 hq
    have c : q * q ^ 2 = q ^ 3 := by ring
    linarith
  exact ⟨hq1, hq2, hqT', r1, r2, r3⟩

theorem assemble1_STR028b2 {q T s M P : ℝ} (hq : 0 ≤ q) (hqT : q ≤ T ^ 2) (hT0 : 0 ≤ T)
    (hT1 : T ≤ 1 / 100) (hs : |s - q / 4| ≤ 50 * (q * T)) (hM : |M - q / 2| ≤ 50 * (q * T))
    (hP : |P - q / 2| ≤ 50 * (q * T)) :
    |P / (1 + s) - 2 * (M / (1 + s) - Real.log (1 + s)) - (P - 2 * M + 2 * s + q ^ 2 / 16)| ≤
        200 * (q * T ^ 3) := by
  obtain ⟨hq1, hq2, hqT', r1, r2, r3⟩ := qbounds_STR028b2 hq hqT hT0 hT1
  have he : 0 ≤ q * T := mul_nonneg hq hT0
  obtain ⟨s1l, s1r⟩ := abs_le.mp hs
  obtain ⟨m1l, m1r⟩ := abs_le.mp hM
  obtain ⟨p1l, p1r⟩ := abs_le.mp hP
  have hsq : |s| ≤ q := by
    rw [abs_le]; constructor <;> linarith
  have hs12 : |s| ≤ 1 / 2 := by linarith
  have hNpos : 0 < 1 + s := by
    have := (abs_le.mp hsq).1
    linarith
  have hdiv : ∀ x : ℝ, |x / (1 + s)| ≤ 2 * |x| := by
    intro x
    rw [abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    have := abs_nonneg x
    have h1 : 1 / 2 ≤ 1 + s := by
      have := (abs_le.mp hs12).1
      linarith
    have := mul_le_mul_of_nonneg_left h1 this
    linarith
  have ρ2 := log2_STR028b2 hs12
  rw [eq1_STR028b2 hNpos.ne']
  have hY : |2 * (M - q / 2) - (P - q / 2) - (s - q / 4)| ≤ 200 * (q * T) := by
    rw [abs_le]; constructor <;> linarith
  have hY2 : |q / 4 + 2 * (M - q / 2) - (P - q / 2) - (s - q / 4)| ≤ q / 4 + 200 * (q * T) := by
    rw [abs_le]; constructor <;> linarith
  have A1 : |(q / 4) * (2 * (M - q / 2) - (P - q / 2) - (s - q / 4))| ≤ q / 4 * (200 * (q * T)) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hY (by positivity)
  have A2 : |(s - q / 4) * (q / 4 + 2 * (M - q / 2) - (P - q / 2) - (s - q / 4))| ≤
      50 * (q * T) * (q / 4 + 200 * (q * T)) := by
    rw [abs_mul]
    exact mul_le_mul hs hY2 (abs_nonneg _) (by positivity)
  have hPM : |P - 2 * M| ≤ 3 * q := by
    rw [abs_le]; constructor <;> linarith
  have A3 : |(P - 2 * M) * s ^ 2 / (1 + s)| ≤ 6 * q ^ 3 := by
    refine (hdiv _).trans ?_
    rw [abs_mul, abs_pow]
    have h2 : |s| ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (abs_nonneg s) hsq 2
    have h3 := mul_le_mul hPM h2 (by positivity) (by positivity)
    have c : 3 * q * q ^ 2 = 3 * q ^ 3 := by ring
    linarith
  have hs3 : |s| ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ (abs_nonneg s) hsq 3
  obtain ⟨a1l, a1r⟩ := abs_le.mp A1
  obtain ⟨a2l, a2r⟩ := abs_le.mp A2
  obtain ⟨a3l, a3r⟩ := abs_le.mp A3
  obtain ⟨a4l, a4r⟩ := abs_le.mp ρ2
  have e1 : q / 4 * (200 * (q * T)) = 50 * (q ^ 2 * T) := by ring
  have e2 : 50 * (q * T) * (q / 4 + 200 * (q * T)) =
      25 / 2 * (q ^ 2 * T) + 10000 * (q ^ 2 * T ^ 2) := by ring
  have hpos : 0 ≤ q * T ^ 3 := by positivity
  rw [abs_le]
  constructor
  · linarith only [a1l, a2l, a3l, a4l, e1, e2, r1, r2, r3, hs3, hpos]
  · linarith only [a1r, a2r, a3r, a4r, e1, e2, r1, r2, r3, hs3, hpos]

theorem assemble2_STR028b2 {q T s M : ℝ} (hq : 0 ≤ q) (hqT : q ≤ T ^ 2) (hT0 : 0 ≤ T)
    (hT1 : T ≤ 1 / 100) (hs : |s - q / 4| ≤ 50 * (q * T)) (hM : |M - q / 2| ≤ 50 * (q * T)) :
    |M / (1 + s) - Real.log (1 + s) - q / 4| ≤ 200 * (q * T) := by
  obtain ⟨hq1, hq2, hqT', r1, r2, r3⟩ := qbounds_STR028b2 hq hqT hT0 hT1
  have he : 0 ≤ q * T := mul_nonneg hq hT0
  obtain ⟨s1l, s1r⟩ := abs_le.mp hs
  obtain ⟨m1l, m1r⟩ := abs_le.mp hM
  have hsq : |s| ≤ q := by
    rw [abs_le]; constructor <;> linarith
  have hs12 : |s| ≤ 1 / 2 := by linarith
  have hNpos : 0 < 1 + s := by
    have := (abs_le.mp hsq).1
    linarith
  have hdiv : ∀ x : ℝ, |x / (1 + s)| ≤ 2 * |x| := by
    intro x
    rw [abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    have := abs_nonneg x
    have h1 : 1 / 2 ≤ 1 + s := by
      have := (abs_le.mp hs12).1
      linarith
    have := mul_le_mul_of_nonneg_left h1 this
    linarith
  have ρ1 := log1_STR028b2 hs12
  rw [eq2_STR028b2 hNpos.ne']
  have hMq : |M| ≤ q := by rw [abs_le]; constructor <;> linarith
  have B1 : |M * s / (1 + s)| ≤ 2 * (q * q) := by
    refine (hdiv _).trans ?_
    rw [abs_mul]
    have := mul_le_mul hMq hsq (abs_nonneg _) hq
    linarith
  obtain ⟨b1l, b1r⟩ := abs_le.mp B1
  obtain ⟨b2l, b2r⟩ := abs_le.mp ρ1
  have hss : s ^ 2 ≤ q ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg s) hsq 2
    rwa [sq_abs] at this
  have c : q ^ 2 = q * q := by ring
  rw [abs_le]
  constructor
  · linarith only [b1l, b1r, b2l, b2r, s1l, s1r, m1l, m1r, hq2, hqT', hss, c]
  · linarith only [b1l, b1r, b2l, b2r, s1l, s1r, m1l, m1r, hq2, hqT', hss, c]

noncomputable def Gf_STR028b2 (a b c2 s2 c4 s4 θ : ℝ) : ℝ :=
  (dF_STR028b2 a b c2 s2 c4 s4 θ * dF_STR028b2 a b c2 s2 c4 s4 θ -
    2 * uF_STR028b2 a b c2 s2 c4 s4 θ + 2) * Real.exp (uF_STR028b2 a b c2 s2 c4 s4 θ) - 2

noncomputable def Xf_STR028b2 (a b c2 s2 c4 s4 θ : ℝ) : ℝ :=
  ga_STR028b2 a b θ + gb_STR028b2 a b c2 s2 c4 s4 θ + gc_STR028b2 c2 s2 c4 s4 θ +
    gd_STR028b2 a b θ + ge_STR028b2 a b c2 s2 c4 s4 θ + gf_STR028b2 a b θ

noncomputable def tot0_STR028b2 (a b c2 s2 c4 s4 : ℝ) : ℝ :=
  (3 * c2 ^ 2 / 2 + 15 * c4 ^ 2 / 2 + 3 * s2 ^ 2 / 2 + 15 * s4 ^ 2 / 2) +
    (a ^ 2 * c2 / 4 + a * b * s2 / 2 - b ^ 2 * c2 / 4) +
    (-a ^ 4 / 32 - a ^ 2 * b ^ 2 / 16 - b ^ 4 / 32)

noncomputable def tot3_STR028b2 (a b c2 s2 c4 s4 : ℝ) : ℝ :=
  (-5 * a ^ 3 + 15 * a * b ^ 2 - 36 * a * c2 + 36 * a * c4 + 36 * b * s2 + 36 * b * s4) / 12

noncomputable def tot6_STR028b2 (a b c2 s2 c4 s4 : ℝ) : ℝ :=
  (-11 * a ^ 2 * c4 + 22 * a * b * s4 + 11 * b ^ 2 * c4 - 36 * c2 * c4 + 36 * s2 * s4) / 4

theorem cont_Gf_STR028b2 (a b c2 s2 c4 s4 : ℝ) : Continuous (Gf_STR028b2 a b c2 s2 c4 s4) := by
  have hu := cont_uF_STR028b2 a b c2 s2 c4 s4
  have hd := cont_dF_STR028b2 a b c2 s2 c4 s4
  unfold Gf_STR028b2
  fun_prop

theorem cont_Xf_STR028b2 (a b c2 s2 c4 s4 : ℝ) : Continuous (Xf_STR028b2 a b c2 s2 c4 s4) := by
  have h1 := cont_ga_STR028b2 a b
  have h2 := cont_gb_STR028b2 a b c2 s2 c4 s4
  have h3 := cont_gc_STR028b2 c2 s2 c4 s4
  have h4 := cont_gd_STR028b2 a b
  have h5 := cont_ge_STR028b2 a b c2 s2 c4 s4
  have h6 := cont_gf_STR028b2 a b
  unfold Xf_STR028b2
  fun_prop

theorem avt_comb4_STR028b2 (h : ℝ) {A B C : ℝ → ℝ} (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) :
    avt_STR028b2 h (fun θ => A θ - 2 * B θ + 2 * C θ - 2) =
      avt_STR028b2 h A - 2 * avt_STR028b2 h B + 2 * avt_STR028b2 h C - 2 := by
  rw [avt_sub_STR028b2 h (F := fun θ => A θ - 2 * B θ + 2 * C θ) (G := fun _ => (2 : ℝ))
    (by fun_prop) (by fun_prop)]
  rw [avt_add_STR028b2 h (F := fun θ => A θ - 2 * B θ) (G := fun θ => 2 * C θ)
    (by fun_prop) (by fun_prop)]
  rw [avt_sub_STR028b2 h (F := A) (G := fun θ => 2 * B θ) hA (by fun_prop)]
  rw [avt_const_mul_STR028b2, avt_const_mul_STR028b2, avt_const_STR028b2]

theorem avt_Gf_STR028b2 (h a b c2 s2 c4 s4 : ℝ) :
    avt_STR028b2 h (Gf_STR028b2 a b c2 s2 c4 s4) =
      avt_STR028b2 h (fun θ => dF_STR028b2 a b c2 s2 c4 s4 θ * dF_STR028b2 a b c2 s2 c4 s4 θ *
        Real.exp (uF_STR028b2 a b c2 s2 c4 s4 θ)) -
      2 * avt_STR028b2 h (fun θ => uF_STR028b2 a b c2 s2 c4 s4 θ *
        Real.exp (uF_STR028b2 a b c2 s2 c4 s4 θ)) +
      2 * avt_STR028b2 h (fun θ => Real.exp (uF_STR028b2 a b c2 s2 c4 s4 θ)) - 2 := by
  have hu := cont_uF_STR028b2 a b c2 s2 c4 s4
  have hd := cont_dF_STR028b2 a b c2 s2 c4 s4
  have e : Gf_STR028b2 a b c2 s2 c4 s4 = fun θ =>
      (dF_STR028b2 a b c2 s2 c4 s4 θ * dF_STR028b2 a b c2 s2 c4 s4 θ *
        Real.exp (uF_STR028b2 a b c2 s2 c4 s4 θ)) -
      2 * (uF_STR028b2 a b c2 s2 c4 s4 θ * Real.exp (uF_STR028b2 a b c2 s2 c4 s4 θ)) +
      2 * Real.exp (uF_STR028b2 a b c2 s2 c4 s4 θ) - 2 := by
    funext θ
    unfold Gf_STR028b2
    ring
  rw [e]
  exact avt_comb4_STR028b2 h (by fun_prop) (by fun_prop) (by fun_prop)

theorem avt_Xf_STR028b2 (h a b c2 s2 c4 s4 : ℝ) :
    avt_STR028b2 h (Xf_STR028b2 a b c2 s2 c4 s4) =
      tot0_STR028b2 a b c2 s2 c4 s4 + tot3_STR028b2 a b c2 s2 c4 s4 * m1_STR028b2 h +
        tot6_STR028b2 a b c2 s2 c4 s4 * m2_STR028b2 h := by
  have h1 := cont_ga_STR028b2 a b
  have h2 := cont_gb_STR028b2 a b c2 s2 c4 s4
  have h3 := cont_gc_STR028b2 c2 s2 c4 s4
  have h4 := cont_gd_STR028b2 a b
  have h5 := cont_ge_STR028b2 a b c2 s2 c4 s4
  have h6 := cont_gf_STR028b2 a b
  unfold Xf_STR028b2
  rw [avt_add_STR028b2 h (F := fun θ => ga_STR028b2 a b θ + gb_STR028b2 a b c2 s2 c4 s4 θ +
      gc_STR028b2 c2 s2 c4 s4 θ + gd_STR028b2 a b θ + ge_STR028b2 a b c2 s2 c4 s4 θ)
      (G := gf_STR028b2 a b) (by fun_prop) h6]
  rw [avt_add_STR028b2 h (F := fun θ => ga_STR028b2 a b θ + gb_STR028b2 a b c2 s2 c4 s4 θ +
      gc_STR028b2 c2 s2 c4 s4 θ + gd_STR028b2 a b θ)
      (G := ge_STR028b2 a b c2 s2 c4 s4) (by fun_prop) h5]
  rw [avt_add_STR028b2 h (F := fun θ => ga_STR028b2 a b θ + gb_STR028b2 a b c2 s2 c4 s4 θ +
      gc_STR028b2 c2 s2 c4 s4 θ) (G := gd_STR028b2 a b) (by fun_prop) h4]
  rw [avt_add_STR028b2 h (F := fun θ => ga_STR028b2 a b θ + gb_STR028b2 a b c2 s2 c4 s4 θ)
      (G := gc_STR028b2 c2 s2 c4 s4) (by fun_prop) h3]
  rw [avt_add_STR028b2 h (F := ga_STR028b2 a b) (G := gb_STR028b2 a b c2 s2 c4 s4) h1 h2]
  rw [avt_ga_STR028b2, avt_gb_STR028b2, avt_gc_STR028b2, avt_gd_STR028b2, avt_ge_STR028b2,
    avt_gf_STR028b2]
  unfold tot0_STR028b2 tot3_STR028b2 tot6_STR028b2
  ring

theorem fine_STR028b2 (h : ℝ) {a b c2 s2 c4 s4 R T : ℝ} (H : JH_STR028b2 a b c2 s2 c4 s4 R T) :
    |avt_STR028b2 h (Gf_STR028b2 a b c2 s2 c4 s4) - (tot0_STR028b2 a b c2 s2 c4 s4 +
      tot3_STR028b2 a b c2 s2 c4 s4 * m1_STR028b2 h +
      tot6_STR028b2 a b c2 s2 c4 s4 * m2_STR028b2 h)| ≤ 3300 * (R ^ 2 * T ^ 3) := by
  refine avt_close_STR028b2 h (G := Xf_STR028b2 a b c2 s2 c4 s4) (cont_Gf_STR028b2 _ _ _ _ _ _)
    (cont_Xf_STR028b2 _ _ _ _ _ _) (fun θ => ?_) (avt_Xf_STR028b2 h a b c2 s2 c4 s4)
  have := pt_bound_STR028b2 H.hR H.hRT H.hT (pw_u1_STR028b2 H θ) (pw_v1_STR028b2 H θ)
    (pw_w_STR028b2 H θ) (pw_z_STR028b2 H θ)
  have e : Gf_STR028b2 a b c2 s2 c4 s4 θ - Xf_STR028b2 a b c2 s2 c4 s4 θ =
      ((v1F_STR028b2 a b θ + zF_STR028b2 c2 s2 c4 s4 θ) ^ 2 -
        2 * (u1F_STR028b2 a b θ + wF_STR028b2 c2 s2 c4 s4 θ) + 2) *
        Real.exp (u1F_STR028b2 a b θ + wF_STR028b2 c2 s2 c4 s4 θ) - 2 -
      ((v1F_STR028b2 a b θ ^ 2 - u1F_STR028b2 a b θ ^ 2) +
        (2 * v1F_STR028b2 a b θ * zF_STR028b2 c2 s2 c4 s4 θ -
          2 * u1F_STR028b2 a b θ * wF_STR028b2 c2 s2 c4 s4 θ) +
        (zF_STR028b2 c2 s2 c4 s4 θ ^ 2 - wF_STR028b2 c2 s2 c4 s4 θ ^ 2) +
        (v1F_STR028b2 a b θ ^ 2 * u1F_STR028b2 a b θ - 2 / 3 * u1F_STR028b2 a b θ ^ 3) +
        (v1F_STR028b2 a b θ ^ 2 * wF_STR028b2 c2 s2 c4 s4 θ +
          2 * u1F_STR028b2 a b θ * v1F_STR028b2 a b θ * zF_STR028b2 c2 s2 c4 s4 θ -
          2 * u1F_STR028b2 a b θ ^ 2 * wF_STR028b2 c2 s2 c4 s4 θ) +
        (v1F_STR028b2 a b θ ^ 2 * u1F_STR028b2 a b θ ^ 2 / 2 - u1F_STR028b2 a b θ ^ 4 / 4)) := by
    unfold Gf_STR028b2 Xf_STR028b2 ga_STR028b2 gb_STR028b2 gc_STR028b2 gd_STR028b2 ge_STR028b2
      gf_STR028b2
    simp only [uF_split_STR028b2, dF_split_STR028b2]
    ring
  rw [e]
  exact this

theorem mm_STR028b2 {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) (hX : 0 ≤ X) : |x * y| ≤ X * Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) hX

theorem abs_ab_STR028b2 {a b R : ℝ} (hab : a ^ 2 + b ^ 2 = R ^ 2) (hR : 0 ≤ R) :
    |a| ≤ R ∧ |b| ≤ R ∧ |-a ^ 2 + b ^ 2| ≤ R ^ 2 ∧ |a * b| ≤ R ^ 2 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact abs_le_of_sq_le_sq (by nlinarith [sq_nonneg b]) hR
  · exact abs_le_of_sq_le_sq (by nlinarith [sq_nonneg a]) hR
  · rw [abs_le]; constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
  · rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

theorem tot3_bound_STR028b2 {a b c2 s2 c4 s4 R T : ℝ} (H : JH_STR028b2 a b c2 s2 c4 s4 R T) :
    |tot3_STR028b2 a b c2 s2 c4 s4| ≤ 14 * (R ^ 2 * T) := by
  obtain ⟨ha, hb, -, -⟩ := abs_ab_STR028b2 H.hab H.hR
  have hT0 : 0 ≤ T := H.hR.trans H.hRT
  have hq : |-5 * a ^ 2 + 15 * b ^ 2| ≤ 15 * R ^ 2 := by
    have h1 : a ^ 2 ≤ R ^ 2 := by nlinarith [sq_nonneg b, H.hab]
    have h2 : b ^ 2 ≤ R ^ 2 := by nlinarith [sq_nonneg a, H.hab]
    have h3 := sq_nonneg a
    have h4 := sq_nonneg b
    rw [abs_le]; constructor <;> linarith
  have t0 := abs_le.mp (mm_STR028b2 ha hq H.hR)
  have t1 := abs_le.mp (mm_STR028b2 ha H.hc2 H.hR)
  have t2 := abs_le.mp (mm_STR028b2 ha H.hc4 H.hR)
  have t3 := abs_le.mp (mm_STR028b2 hb H.hs2 H.hR)
  have t4 := abs_le.mp (mm_STR028b2 hb H.hs4 H.hR)
  have r3 : R * (15 * R ^ 2) ≤ 15 * (R ^ 2 * T) := by
    have := mul_le_mul_of_nonneg_left H.hRT (sq_nonneg R)
    linarith
  have hpos : 0 ≤ R ^ 2 * T := by positivity
  unfold tot3_STR028b2
  rw [abs_le]
  obtain ⟨t0l, t0r⟩ := t0
  obtain ⟨t1l, t1r⟩ := t1
  obtain ⟨t2l, t2r⟩ := t2
  obtain ⟨t3l, t3r⟩ := t3
  obtain ⟨t4l, t4r⟩ := t4
  constructor
  · linarith only [t0l, t0r, t1l, t1r, t2l, t2r, t3l, t3r, t4l, t4r, r3, hpos]
  · linarith only [t0l, t0r, t1l, t1r, t2l, t2r, t3l, t3r, t4l, t4r, r3, hpos]

theorem tot6_bound_STR028b2 {a b c2 s2 c4 s4 R T : ℝ} (H : JH_STR028b2 a b c2 s2 c4 s4 R T) :
    |tot6_STR028b2 a b c2 s2 c4 s4| ≤ 30 * (R ^ 2 * T ^ 2) := by
  obtain ⟨-, -, hu, hab4⟩ := abs_ab_STR028b2 H.hab H.hR
  have hT0 : 0 ≤ T := H.hR.trans H.hRT
  have hRT0 : 0 ≤ R * T := mul_nonneg H.hR hT0
  have t1 := abs_le.mp (mm_STR028b2 hu H.hc4 (sq_nonneg R))
  have t2 := abs_le.mp (mm_STR028b2 hab4 H.hs4 (by positivity))
  have t3 := abs_le.mp (mm_STR028b2 H.hc2 H.hc4 hRT0)
  have t4 := abs_le.mp (mm_STR028b2 H.hs2 H.hs4 hRT0)
  have r : R ^ 2 * (R * T) ≤ R ^ 2 * T ^ 2 := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right H.hRT hT0) (sq_nonneg R)
    linarith
  have hpos : 0 ≤ R ^ 2 * T ^ 2 := by positivity
  unfold tot6_STR028b2
  rw [abs_le]
  obtain ⟨t1l, t1r⟩ := t1
  obtain ⟨t2l, t2r⟩ := t2
  obtain ⟨t3l, t3r⟩ := t3
  obtain ⟨t4l, t4r⟩ := t4
  constructor
  · linarith only [t1l, t1r, t2l, t2r, t3l, t3r, t4l, t4r, r, hpos]
  · linarith only [t1l, t1r, t2l, t2r, t3l, t3r, t4l, t4r, r, hpos]

theorem m2_bound_STR028b2 {h : ℝ} (hh : |h| ≤ 1 / 4) : |m2_STR028b2 h| ≤ 8 * |h| := by
  have h1 := avt_rough_STR028b2 hh (F := fun θ => Real.cos (6 * θ)) (by fun_prop) (M := 1)
    (fun θ => Real.abs_cos_le_one _)
  have h2 := int_cos_nat_STR028b2 6 (by norm_num)
  simp only [Nat.cast_ofNat] at h2
  unfold m2_STR028b2
  rw [h2, sub_zero, mul_one] at h1
  exact h1

theorem core_real_STR028b2 {q T γ h N M P G t0 t3 t6 m1 m2 : ℝ} (hq : 0 ≤ q) (hqT : q ≤ T ^ 2)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1 / 100) (hs : |N - 1 - q / 4| ≤ 50 * (q * T))
    (hM : |M - q / 2| ≤ 50 * (q * T)) (hP : |P - q / 2| ≤ 50 * (q * T))
    (hG : G = P - 2 * M + 2 * N - 2)
    (hfine : |G - (t0 + t3 * m1 + t6 * m2)| ≤ 3300 * (q * T ^ 3))
    (ht3 : |t3| ≤ 14 * (q * T)) (ht6 : |t6| ≤ 30 * (q * T ^ 2))
    (hm1 : |m1 - h / 2| ≤ 2 * h ^ 2) (hm2 : |m2| ≤ 8 * |h|) (hh : |h| ≤ T) :
    |P / N - 2 * (1 + γ) * (M / N - Real.log N) - (-γ * q / 2 + (t0 + t3 * (h / 2) + q ^ 2 / 16))| ≤
      3800 * (q * T ^ 3) + 400 * |γ| * (q * T) := by
  have e1 : 1 + (N - 1) = N := by ring
  have A := assemble1_STR028b2 hq hqT hT0 hT1 hs hM hP
  have B := assemble2_STR028b2 hq hqT hT0 hT1 hs hM
  rw [e1] at A B
  have hqT0 : 0 ≤ q * T := mul_nonneg hq hT0
  have hpos : 0 ≤ q * T ^ 3 := by positivity
  have hh2 : h ^ 2 ≤ T ^ 2 := by
    obtain ⟨l, r⟩ := abs_le.mp hh
    nlinarith
  have b3 : |t3 * (m1 - h / 2)| ≤ 28 * (q * T ^ 3) := by
    rw [abs_mul]
    have := mul_le_mul ht3 (hm1.trans (by linarith : 2 * h ^ 2 ≤ 2 * T ^ 2)) (abs_nonneg _)
      (by positivity)
    linarith
  have b4 : |t6 * m2| ≤ 240 * (q * T ^ 3) := by
    rw [abs_mul]
    have := mul_le_mul ht6 (hm2.trans (by linarith : 8 * |h| ≤ 8 * T)) (abs_nonneg _)
      (by positivity)
    linarith
  have b5 : |2 * γ * (M / N - Real.log N - q / 4)| ≤ 400 * |γ| * (q * T) := by
    rw [abs_mul, abs_mul, abs_two]
    have := mul_le_mul_of_nonneg_left B (abs_nonneg γ)
    linarith
  have key : P / N - 2 * (1 + γ) * (M / N - Real.log N) -
      (-γ * q / 2 + (t0 + t3 * (h / 2) + q ^ 2 / 16)) =
      (P / N - 2 * (M / N - Real.log N) - (P - 2 * M + 2 * (N - 1) + q ^ 2 / 16)) +
      (G - (t0 + t3 * m1 + t6 * m2)) + t3 * (m1 - h / 2) + t6 * m2 -
      2 * γ * (M / N - Real.log N - q / 4) := by
    rw [hG]; ring
  rw [key]
  obtain ⟨a1l, a1r⟩ := abs_le.mp A
  obtain ⟨a2l, a2r⟩ := abs_le.mp hfine
  obtain ⟨a3l, a3r⟩ := abs_le.mp b3
  obtain ⟨a4l, a4r⟩ := abs_le.mp b4
  obtain ⟨a5l, a5r⟩ := abs_le.mp b5
  rw [abs_le]
  constructor
  · linarith only [a1l, a2l, a3l, a4l, a5r, hpos]
  · linarith only [a1r, a2r, a3r, a4r, a5l, hpos]

theorem core_STR028b2 (h γ : ℝ) {a b c2 s2 c4 s4 R T : ℝ}
    (H : JH_STR028b2 a b c2 s2 c4 s4 R T) (hh : |h| ≤ T) :
    |avt_STR028b2 h (fun θ => dF_STR028b2 a b c2 s2 c4 s4 θ * dF_STR028b2 a b c2 s2 c4 s4 θ *
        Real.exp (uF_STR028b2 a b c2 s2 c4 s4 θ)) /
      avt_STR028b2 h (fun θ => Real.exp (uF_STR028b2 a b c2 s2 c4 s4 θ)) -
    2 * (1 + γ) * (avt_STR028b2 h (fun θ => uF_STR028b2 a b c2 s2 c4 s4 θ *
        Real.exp (uF_STR028b2 a b c2 s2 c4 s4 θ)) /
      avt_STR028b2 h (fun θ => Real.exp (uF_STR028b2 a b c2 s2 c4 s4 θ)) -
      Real.log (avt_STR028b2 h (fun θ => Real.exp (uF_STR028b2 a b c2 s2 c4 s4 θ)))) -
    (-γ * R ^ 2 / 2 + (tot0_STR028b2 a b c2 s2 c4 s4 + tot3_STR028b2 a b c2 s2 c4 s4 * (h / 2) +
      (R ^ 2) ^ 2 / 16))| ≤ 3800 * (R ^ 2 * T ^ 3) + 400 * |γ| * (R ^ 2 * T) := by
  have hT0 : 0 ≤ T := H.hR.trans H.hRT
  have hpos : 0 ≤ R ^ 2 * T := by positivity
  have hN := crudeN_STR028b2 h H
  have hM := crudeM_STR028b2 h H
  have hP := crudeP_STR028b2 h H
  have hh4 : |h| ≤ 1 / 4 := by have := H.hT; linarith
  have hh2 : |h| ≤ 1 / 2 := by linarith
  refine core_real_STR028b2 (q := R ^ 2) (h := h)
    (G := avt_STR028b2 h (Gf_STR028b2 a b c2 s2 c4 s4))
    (pow_nonneg H.hR 2) (pow_le_pow_left₀ H.hR H.hRT 2) hT0 H.hT ?_ ?_ ?_
    (avt_Gf_STR028b2 h a b c2 s2 c4 s4 |>.trans (by ring)) (fine_STR028b2 h H)
    (tot3_bound_STR028b2 H) ?_ (m1_bound_STR028b2 hh2) (m2_bound_STR028b2 hh4) hh
  · rw [show _ - 1 - R ^ 2 / 4 = _ - (1 + R ^ 2 / 4) by ring]
    exact hN.trans (by linarith)
  · exact hM.trans (by linarith)
  · exact hP.trans (by linarith)
  · exact tot6_bound_STR028b2 H

theorem JH_of_STR028b2 {a b h R : ℝ} (hR : 0 ≤ R) (hab : a ^ 2 + b ^ 2 = R ^ 2)
    (hT : |h| + R ≤ 1 / 100) :
    JH_STR028b2 a b (h * a / 2 + (b ^ 2 - a ^ 2) / 12) (-(h * b) / 2 - a * b / 6)
      (-(h * a) / 10) (-(h * b) / 10) R (|h| + R) := by
  obtain ⟨ha, hb, hu, hab4⟩ := abs_ab_STR028b2 hab hR
  have h0 := abs_nonneg h
  have hha : |h * a| ≤ |h| * R := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left ha h0
  have hhb : |h * b| ≤ |h| * R := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hb h0
  obtain ⟨u1, u2⟩ := abs_le.mp hu
  obtain ⟨v1, v2⟩ := abs_le.mp hab4
  obtain ⟨p1, p2⟩ := abs_le.mp hha
  obtain ⟨q1, q2⟩ := abs_le.mp hhb
  have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
  have hhR : 0 ≤ |h| * R := mul_nonneg h0 hR
  refine ⟨hR, hab, by linarith, by linarith, ?_, ?_, ?_, ?_⟩
  · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_le]; constructor <;> nlinarith

theorem main_id_STR028b2 (a b h : ℝ) :
    tot0_STR028b2 a b (h * a / 2 + (b ^ 2 - a ^ 2) / 12) (-(h * b) / 2 - a * b / 6)
      (-(h * a) / 10) (-(h * b) / 10) +
    tot3_STR028b2 a b (h * a / 2 + (b ^ 2 - a ^ 2) / 12) (-(h * b) / 2 - a * b / 6)
      (-(h * a) / 10) (-(h * b) / 10) * (h / 2) + ((a ^ 2 + b ^ 2) ^ 2) / 16 =
    -(9 / 20) * h ^ 2 * (a ^ 2 + b ^ 2) - h * (a ^ 3 - 3 * a * b ^ 2) / 12 +
      (a ^ 2 + b ^ 2) ^ 2 / 48 := by
  unfold tot0_STR028b2 tot3_STR028b2
  ring

theorem phi_jet_expansion_STR028b2 :
    ∃ r : ℝ, 0 < r ∧ ∃ K : ℝ, ∃ E : Par → ℝ, ∀ p : Par, ‖p‖ < r →
      Phi_STR028b1 (Xp (α := α) p) =
        -p 3 * R0_STR028b1 p ^ 2 / 2 - 9 / 20 * p 2 ^ 2 * R0_STR028b1 p ^ 2 -
          p 2 * (p 0 ^ 3 - 3 * p 0 * p 1 ^ 2) / 12 + R0_STR028b1 p ^ 4 / 48 +
          R0_STR028b1 p ^ 2 * E p ∧
      |E p| ≤ K * ((|p 2| + R0_STR028b1 p) ^ 3 + |p 3| * (|p 2| + R0_STR028b1 p) + p 3 ^ 2) := by
  refine ⟨1 / 300, by norm_num, 4000, fun p => if R0_STR028b1 p = 0 then 0 else
    (Phi_STR028b1 (Xp (α := α) p) - (-p 3 * R0_STR028b1 p ^ 2 / 2 - 9 / 20 * p 2 ^ 2 * R0_STR028b1 p ^ 2 -
          p 2 * (p 0 ^ 3 - 3 * p 0 * p 1 ^ 2) / 12 + R0_STR028b1 p ^ 4 / 48)) /
      R0_STR028b1 p ^ 2, fun p hp => ?_⟩
  have hR := R0_nonneg_STR028b1 p
  have hR2 := R0_sq_STR028b1 p
  have hn0 : |p 0| ≤ ‖p‖ := by simpa using norm_le_pi_norm p 0
  have hn1 : |p 1| ≤ ‖p‖ := by simpa using norm_le_pi_norm p 1
  have hn2 : |p 2| ≤ ‖p‖ := by simpa using norm_le_pi_norm p 2
  have hRle : R0_STR028b1 p ≤ |p 0| + |p 1| := by
    unfold R0_STR028b1
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_abs (p 0), sq_abs (p 1), abs_nonneg (p 0), abs_nonneg (p 1)]
  have hT : |p 2| + R0_STR028b1 p ≤ 1 / 100 := by linarith
  have H : JH_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p) (R0_STR028b1 p)
      (|p 2| + R0_STR028b1 p) := JH_of_STR028b2 hR hR2.symm hT
  have hc := core_STR028b2 (p 2) (p 3) H (le_add_of_nonneg_right hR)
  have hPhi := Phi_eq_av_STR028b2 (α := α) p
  have hc' : |Phi_STR028b1 (Xp (α := α) p) - (-p 3 * R0_STR028b1 p ^ 2 / 2 +
      (tot0_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p) +
        tot3_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p) * (p 2 / 2) +
        (R0_STR028b1 p ^ 2) ^ 2 / 16))| ≤ 3800 * (R0_STR028b1 p ^ 2 * (|p 2| + R0_STR028b1 p) ^ 3) +
        400 * |p 3| * (R0_STR028b1 p ^ 2 * (|p 2| + R0_STR028b1 p)) := by
    rw [hPhi]; exact hc
  have hid : -p 3 * R0_STR028b1 p ^ 2 / 2 +
      (tot0_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p) +
        tot3_STR028b2 (p 0) (p 1) (jc2 p) (js2 p) (jc4 p) (js4 p) * (p 2 / 2) +
        (R0_STR028b1 p ^ 2) ^ 2 / 16) =
      -p 3 * R0_STR028b1 p ^ 2 / 2 - 9 / 20 * p 2 ^ 2 * R0_STR028b1 p ^ 2 -
          p 2 * (p 0 ^ 3 - 3 * p 0 * p 1 ^ 2) / 12 + R0_STR028b1 p ^ 4 / 48 := by
    have h4 : R0_STR028b1 p ^ 4 = (p 0 ^ 2 + p 1 ^ 2) ^ 2 := by rw [← hR2]; ring
    have := main_id_STR028b2 (p 0) (p 1) (p 2)
    unfold jc2 js2 jc4 js4
    rw [h4, hR2]
    linarith [this]
  rw [hid] at hc'
  dsimp only
  split_ifs with hz
  · have hz2 : R0_STR028b1 p ^ 2 = 0 := by rw [hz]; norm_num
    have h0 : |Phi_STR028b1 (Xp (α := α) p) - (-p 3 * R0_STR028b1 p ^ 2 / 2 -
        9 / 20 * p 2 ^ 2 * R0_STR028b1 p ^ 2 -
          p 2 * (p 0 ^ 3 - 3 * p 0 * p 1 ^ 2) / 12 + R0_STR028b1 p ^ 4 / 48)| ≤ 0 :=
      hc'.trans (by rw [hz2]; simp)
    have h1 := abs_nonpos_iff.mp h0
    refine ⟨by linarith, ?_⟩
    rw [abs_zero]
    positivity
  · have hpos : 0 < R0_STR028b1 p ^ 2 := by positivity
    set D := Phi_STR028b1 (Xp (α := α) p) - (-p 3 * R0_STR028b1 p ^ 2 / 2 -
        9 / 20 * p 2 ^ 2 * R0_STR028b1 p ^ 2 -
          p 2 * (p 0 ^ 3 - 3 * p 0 * p 1 ^ 2) / 12 + R0_STR028b1 p ^ 4 / 48) with hD
    have e : R0_STR028b1 p ^ 2 * (D / R0_STR028b1 p ^ 2) = D := by field_simp
    refine ⟨by linarith, ?_⟩
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have q1 : 0 ≤ R0_STR028b1 p ^ 2 * (|p 2| + R0_STR028b1 p) ^ 3 := by positivity
    have q2 : 0 ≤ |p 3| * (R0_STR028b1 p ^ 2 * (|p 2| + R0_STR028b1 p)) := by positivity
    have q3 : 0 ≤ p 3 ^ 2 * R0_STR028b1 p ^ 2 := by positivity
    linarith only [hc', q1, q2, q3]
end DGPS.Examples.ThreeSpeciesCircle
