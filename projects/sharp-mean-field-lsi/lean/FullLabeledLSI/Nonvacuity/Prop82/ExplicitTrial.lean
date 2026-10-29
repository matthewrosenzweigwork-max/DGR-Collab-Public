import FullLabeledLSI.Nonvacuity.Prop82.Trial
import FullLabeledLSI.Nonvacuity.Prop82.Score

/-!
# An explicit rational trial below the equilibrium threshold

Instead of assuming a fourth-order integral limit, use t = 1/100000000.
The entropy Taylor error follows from the source's scalar logarithm estimate.
Two exact positive-coefficient polynomial identities bound the remaining
entropy and Fisher remainders on the ENTIRE interval -1 <= cos(theta) <= 1.
No quadrature or floating-point bound enters a Lean proof below.

This file is UNCOMPILED proof source. The certificates were independently
checked by exact rational polynomial arithmetic, not by the Lean kernel.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82

noncomputable def trialParameter : Real := 1 / 100000000

noncomputable def rhoPoly (t c : Real) : Real :=
  1 + t * c + (t ^ 2 / 5) * (2 * c ^ 2 - 1)

noncomputable def entropyPoly (u : Real) : Real :=
  u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 12

noncomputable def entropyApprox (t c : Real) : Real :=
  t ^ 2 * c ^ 2 / 2 +
    t ^ 3 * (c * ((2 * c ^ 2 - 1) / 5) - c ^ 3 / 6) +
    t ^ 4 * (((2 * c ^ 2 - 1) / 5) ^ 2 / 2 -
      c ^ 2 * ((2 * c ^ 2 - 1) / 5) / 2 + c ^ 4 / 12)

noncomputable def fisherApprox (t c : Real) : Real :=
  t ^ 2 * (1 - c ^ 2) + (3 / 5) * t ^ 3 * (1 - c ^ 2) * c +
    t ^ 4 * (1 - c ^ 2) * (c ^ 2 / 25 - (2 * c ^ 2 - 1) / 5)

noncomputable def fisherNumerator (t c : Real) : Real :=
  t ^ 2 * (1 - c ^ 2) * (1 + 4 * t * c / 5) ^ 2

theorem trialParameter_pos : 0 < trialParameter := by norm_num [trialParameter]

theorem trialParameter_small : |trialParameter| ≤ 1 / 2 := by norm_num [trialParameter]

theorem trial_eq_rhoPoly (t : Real) (x : Torus 1) :
    trial t x = rhoPoly t (gCos x) := by
  unfold trial rhoPoly
  rw [c2_apply]

theorem abs_rhoPoly_sub_one {c : Real} (hc : |c| ≤ 1) :
    |rhoPoly trialParameter c - 1| ≤ 2 * trialParameter := by
  have hc0 := (abs_le.mp hc).1
  have hc1 := (abs_le.mp hc).2
  have hc2 : c ^ 2 ≤ 1 := by nlinarith [sq_abs c, abs_nonneg c]
  rw [abs_le]
  unfold rhoPoly trialParameter
  constructor <;> nlinarith [sq_nonneg c]

theorem rhoPoly_pos {c : Real} (hc : |c| ≤ 1) :
    0 < rhoPoly trialParameter c := by
  have h := (abs_le.mp (abs_rhoPoly_sub_one hc)).1
  have h2 : 2 * trialParameter < 1 := by norm_num [trialParameter]
  linarith

/-- Fifth-order absolute remainder, derived from the actual logarithm. -/
theorem abs_entropyPoly_remainder {u : Real} (hu : |u| ≤ 1 / 2) :
    |klFun (1 + u) - entropyPoly u| ≤ 4 * |u| ^ 5 := by
  have hu' : |(-u)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hu' 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at h
  set E := Real.log (1 + u) - u + u ^ 2 / 2 - u ^ 3 / 3 + u ^ 4 / 4 with hE
  have hE' : |E| ≤ 2 * |u| ^ 5 := by
    have e : (0 : Real) + (-u) ^ (0 + 1) / ((0 : Nat) + 1 : Real) +
        (-u) ^ (1 + 1) / ((1 : Nat) + 1 : Real) +
        (-u) ^ (2 + 1) / ((2 : Nat) + 1 : Real) +
        (-u) ^ (3 + 1) / ((3 : Nat) + 1 : Real) + Real.log (1 + u) = E := by
      rw [hE]
      push_cast
      ring
    rw [e] at h
    have h1 : 0 < 1 - |u| := by linarith
    refine h.trans ?_
    rw [div_le_iff₀ h1, show (4 : Nat) + 1 = 5 from rfl]
    have hh := pow_nonneg (abs_nonneg u) 5
    nlinarith [mul_le_mul_of_nonneg_left
      (show (1 : Real) ≤ 2 * (1 - |u|) by linarith) hh]
  have hk : klFun (1 + u) - entropyPoly u = -(u ^ 5) / 4 + (1 + u) * E := by
    rw [klFun_apply, hE]
    unfold entropyPoly
    ring
  have h1u : |1 + u| ≤ 3 / 2 := by
    rw [abs_le]
    constructor <;> linarith [(abs_le.mp hu).1, (abs_le.mp hu).2]
  rw [hk]
  calc
    |-(u ^ 5) / 4 + (1 + u) * E| ≤ |-(u ^ 5) / 4| + |(1 + u) * E| :=
      abs_add_le _ _
    _ = |u| ^ 5 / 4 + |1 + u| * |E| := by
      rw [abs_div, abs_neg, abs_pow, abs_mul]
      norm_num
    _ ≤ |u| ^ 5 / 4 + 3 / 2 * (2 * |u| ^ 5) := by gcongr
    _ ≤ 4 * |u| ^ 5 := by nlinarith [pow_nonneg (abs_nonneg u) 5]

/-- Exact rational Bernstein certificate for the polynomial entropy error. -/
theorem entropy_polynomial_lower {c : Real} (hc : |c| ≤ 1) :
    entropyApprox trialParameter c - trialParameter ^ 4 / 20000 ≤
      entropyPoly (rhoPoly trialParameter c - 1) := by
  have hp : 0 ≤ c + 1 := by linarith [(abs_le.mp hc).1]
  have hm : 0 ≤ 1 - c := by linarith [(abs_le.mp hc).2]
  have hcert : 19200000000000000000000000000000000000000000000000000000000000000000000 *
      (entropyPoly (rhoPoly trialParameter c - 1) - entropyApprox trialParameter c +
        trialParameter ^ 4 / 20000) =
      37499650000001399999998000000001 * (1 - c) ^ 8 +
      300001499999983600000035999999976 * (c + 1) * (1 - c) ^ 7 +
      1050003100000046399999780000000220 * (c + 1) ^ 2 * (1 - c) ^ 6 +
      2100000300000022800000467999999064 * (c + 1) ^ 3 * (1 - c) ^ 5 +
      2624999999999917200000000000001734 * (c + 1) ^ 4 * (1 - c) ^ 4 +
      2099999700000022799999531999999064 * (c + 1) ^ 5 * (1 - c) ^ 3 +
      1049996900000046400000220000000220 * (c + 1) ^ 6 * (1 - c) ^ 2 +
      299998499999983599999963999999976 * (c + 1) ^ 7 * (1 - c) +
      37500350000001400000002000000001 * (c + 1) ^ 8 := by
    norm_num [trialParameter, entropyPoly, rhoPoly, entropyApprox] <;> ring
  have hn : 0 ≤ 19200000000000000000000000000000000000000000000000000000000000000000000 *
      (entropyPoly (rhoPoly trialParameter c - 1) - entropyApprox trialParameter c +
        trialParameter ^ 4 / 20000) := by
    rw [hcert]
    positivity
  have hh := (mul_nonneg_iff_of_pos_left
    (by norm_num : (0 : Real) < 19200000000000000000000000000000000000000000000000000000000000000000000)).mp hn
  linarith

/-- Exact rational Bernstein certificate for the Fisher integrand. -/
theorem fisher_polynomial_upper {c : Real} (hc : |c| ≤ 1) :
    fisherNumerator trialParameter c / rhoPoly trialParameter c ≤
      fisherApprox trialParameter c + trialParameter ^ 4 / 10000 := by
  have hp : 0 ≤ c + 1 := by linarith [(abs_le.mp hc).1]
  have hm : 0 ≤ 1 - c := by linarith [(abs_le.mp hc).2]
  apply (div_le_iff₀ (rhoPoly_pos hc)).mpr
  have hcert : 3200000000000000000000000000000000000000000000000000000 *
      ((fisherApprox trialParameter c + trialParameter ^ 4 / 10000) *
        rhoPoly trialParameter c - fisherNumerator trialParameter c) =
      49999999500000001 * (1 - c) ^ 6 +
      300000797999993598 * (c + 1) * (1 - c) ^ 5 +
      749991997500083183 * (c + 1) ^ 2 * (1 - c) ^ 4 +
      999999999999718372 * (c + 1) ^ 3 * (1 - c) ^ 3 +
      750008002500083183 * (c + 1) ^ 4 * (1 - c) ^ 2 +
      299999201999993598 * (c + 1) ^ 5 * (1 - c) +
      50000000500000001 * (c + 1) ^ 6 := by
    norm_num [trialParameter, fisherApprox, rhoPoly, fisherNumerator] <;> ring
  have hn : 0 ≤ 3200000000000000000000000000000000000000000000000000000 *
      ((fisherApprox trialParameter c + trialParameter ^ 4 / 10000) *
        rhoPoly trialParameter c - fisherNumerator trialParameter c) := by
    rw [hcert]
    positivity
  have hh := (mul_nonneg_iff_of_pos_left
    (by norm_num : (0 : Real) < 3200000000000000000000000000000000000000000000000000000)).mp hn
  linarith

/-- The actual KL integrand, not a polynomial stand-in. -/
theorem explicit_entropy_pointwise {c : Real} (hc : |c| ≤ 1) :
    entropyApprox trialParameter c - trialParameter ^ 4 / 10000 ≤
      klFun (rhoPoly trialParameter c) := by
  have hu := abs_rhoPoly_sub_one hc
  have hsmall : |rhoPoly trialParameter c - 1| ≤ 1 / 2 := by
    have hh : 2 * trialParameter ≤ (1 / 2 : Real) := by norm_num [trialParameter]
    exact hu.trans hh
  have he := abs_entropyPoly_remainder hsmall
  have hpow := pow_le_pow_left₀ (abs_nonneg (rhoPoly trialParameter c - 1)) hu 5
  have hconst : 4 * (2 * trialParameter) ^ 5 ≤ trialParameter ^ 4 / 20000 := by
    norm_num [trialParameter]
  have hl := (abs_le.mp he).1
  have hp := entropy_polynomial_lower hc
  have harg : 1 + (rhoPoly trialParameter c - 1) = rhoPoly trialParameter c := by ring
  rw [harg] at hl
  linarith


/-! ## The actual integrals of the trial -/

theorem integral_cos_poly4 (b0 b1 b2 b3 b4 : Real) :
    (∫ x, b0 + b1 * gCos x + b2 * gCos x ^ 2 +
      b3 * gCos x ^ 3 + b4 * gCos x ^ 4 ∂haar 1) =
      b0 + b2 / 2 + 3 * b4 / 8 := by
  have hc := continuous_gCos
  rw [integral_add (by apply SharpLSI.integrable_bdd; fun_prop) (by apply SharpLSI.integrable_bdd; fun_prop),
    integral_add (by apply SharpLSI.integrable_bdd; fun_prop) (by apply SharpLSI.integrable_bdd; fun_prop),
    integral_add (by apply SharpLSI.integrable_bdd; fun_prop) (by apply SharpLSI.integrable_bdd; fun_prop),
    integral_add (integrable_const _) (by apply SharpLSI.integrable_bdd; fun_prop)]
  simp only [integral_const_mul, integral_gCos, integral_gCos_sq,
    integral_gCos_pow3, integral_gCos_pow4, integral_const, probReal_univ,
    smul_eq_mul, one_mul]
  ring

theorem continuous_entropyApprox (t : Real) : Continuous (fun x => entropyApprox t (gCos x)) := by
  have hc := continuous_gCos
  unfold entropyApprox
  fun_prop

theorem continuous_fisherApprox (t : Real) : Continuous (fun x => fisherApprox t (gCos x)) := by
  have hc := continuous_gCos
  unfold fisherApprox
  fun_prop

theorem integral_entropyApprox (t : Real) :
    (∫ x, entropyApprox t (gCos x) ∂haar 1) = t ^ 2 / 4 + 13 * t ^ 4 / 800 := by
  have he : ∀ c : Real, entropyApprox t c =
      t ^ 4 / 50 + (-t ^ 3 / 5) * c + (t ^ 2 / 2 + t ^ 4 / 50) * c ^ 2 +
        (7 * t ^ 3 / 30) * c ^ 3 + (-11 * t ^ 4 / 300) * c ^ 4 := by
    intro c
    unfold entropyApprox
    ring
  simp_rw [he]
  rw [integral_cos_poly4]
  ring

theorem integral_fisherApprox (t : Real) :
    (∫ x, fisherApprox t (gCos x) ∂haar 1) = t ^ 2 / 2 + 11 * t ^ 4 / 200 := by
  have he : ∀ c : Real, fisherApprox t c =
      (t ^ 2 + t ^ 4 / 5) + (3 * t ^ 3 / 5) * c +
        (-t ^ 2 - 14 * t ^ 4 / 25) * c ^ 2 +
        (-3 * t ^ 3 / 5) * c ^ 3 + (9 * t ^ 4 / 25) * c ^ 4 := by
    intro c
    unfold fisherApprox
    ring
  simp_rw [he]
  rw [integral_cos_poly4]
  ring

theorem integral_trial_sCos_sq (t : Real) :
    (∫ x, trial t x * sCos x ^ 2 ∂haar 1) = 1 / 2 - t ^ 2 / 20 := by
  have he : ∀ x, trial t x * sCos x ^ 2 =
      (1 - t ^ 2 / 5) + t * gCos x + (-1 + 3 * t ^ 2 / 5) * gCos x ^ 2 +
        (-t) * gCos x ^ 3 + (-2 * t ^ 2 / 5) * gCos x ^ 4 := by
    intro x
    have hs : sCos x ^ 2 = 1 - gCos x ^ 2 := by
      linarith [gCos_sq_add_sCos_sq x]
    rw [hs, trial_eq_rhoPoly]
    unfold rhoPoly
    ring
  simp_rw [he]
  rw [integral_cos_poly4]
  ring

theorem forceEnergy_trial (t : Real) :
    forceEnergy (trial t) = aCos * (t ^ 2 / 8 - t ^ 4 / 80) := by
  have hGc : ContDiff Real 1 (gConv (trial t) ∘ liftT) :=
    (contDiff_gConv_lift (trial_mass t)).of_le le_top
  have hgrad : ∀ᵐ x ∂haar 1,
      weakGrad (gConv (trial t)) x 0 = -(Real.pi * t) * sCos x := by
    filter_upwards [weakGrad_ae_eq_of_contDiff hGc] with x hx
    rw [hx]
    simp only
    rw [gConv_lift (trial_mass t), fderiv_trig_lift,
      integral_gCos_trial, integral_sCos_trial, ← sCos_secT]
    ring
  unfold forceEnergy
  calc
    (∫ x, trial t x * weakGrad (gConv (trial t)) x 0 ^ 2 ∂haar 1) =
        aCos * t ^ 2 / 4 * (∫ x, trial t x * sCos x ^ 2 ∂haar 1) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hgrad] with x hx
      rw [hx]
      unfold aCos
      ring
    _ = _ := by rw [integral_trial_sCos_sq]; ring

theorem trial_lift (t : Real) : trial t ∘ liftT = fun z : Fin 1 → Real =>
    1 + t * Real.cos (2 * Real.pi * z 0) +
      t ^ 2 / 5 * (2 * Real.cos (2 * Real.pi * z 0) ^ 2 - 1) := by
  funext z
  change trial t (liftT z) = _
  rw [trial_eq_rhoPoly, gCos_coe (liftT z) (z 0) rfl] <;> rfl

theorem dpart_trial (t : Real) (x : Torus 1) :
    dpart (trial t) 0 x = -(2 * Real.pi) * t * sCos x * (1 + 4 * t * gCos x / 5) := by
  unfold dpart
  apply fderiv_apply_of_line ((trial_smooth t).differentiable (by simp) _)
  rw [trial_lift]
  have hg := (((hasDerivAt_id (0 : Real)).const_add (secT x 0)).const_mul
    (2 * Real.pi)).cos
  have hh := ((hasDerivAt_const (0 : Real) (1 : Real)).add (hg.const_mul t)).add
    ((((hg.pow 2).const_mul 2).sub_const 1).const_mul (t ^ 2 / 5))
  convert hh using 1
  · funext z
    simp
  · simp only [id, Pi.pow_apply]
    norm_num
    rw [gCos_secT, sCos_secT]
    ring

theorem fisher_eq_dpart_integral {rho : Torus 1 → Real} (h : SmoothProbability rho) :
    fisher rho = ∫ x, dpart rho 0 x ^ 2 / rho x ∂haar 1 := by
  rw [fisher_eq_score_variance h]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [← rho_mul_scoreTest h x]
    field_simp [(h.positive x).ne'] <;> ring

theorem fisher_trial_integral {t : Real} (ht : |t| ≤ 1 / 2) :
    fisher (trial t) = aCos *
      (∫ x, fisherNumerator t (gCos x) / rhoPoly t (gCos x) ∂haar 1) := by
  rw [fisher_eq_dpart_integral (trial_probability ht), ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    have hs : sCos x ^ 2 = 1 - gCos x ^ 2 := by
      linarith [gCos_sq_add_sCos_sq x]
    rw [dpart_trial, trial_eq_rhoPoly]
    unfold fisherNumerator aCos
    simp only [mul_pow, neg_sq]
    rw [hs]
    ring

theorem entropy_trial_integral {t : Real} (ht : |t| ≤ 1 / 2) :
    entropy (trial t) = ∫ x, klFun (trial t x) ∂haar 1 := by
  have hp := trial_probability ht
  have hi : Integrable (fun x => klFun (trial t x)) (haar 1) :=
    SharpLSI.integrable_bdd (continuous_klFun.comp (trial_continuous t))
  have hn := fun x => klFun_nonneg (hp.nonneg x)
  unfold entropy
  rw [klDiv_densMeasure hp.nonneg hp.mass,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn),
    ENNReal.toReal_ofReal (integral_nonneg hn)]

theorem explicit_trial_entropy_lower :
    trialParameter ^ 2 / 4 + 13 * trialParameter ^ 4 / 800 - trialParameter ^ 4 / 10000 ≤
      entropy (trial trialParameter) := by
  rw [← integral_entropyApprox trialParameter, entropy_trial_integral trialParameter_small]
  calc
    (∫ x, entropyApprox trialParameter (gCos x) ∂haar 1) - trialParameter ^ 4 / 10000 =
        ∫ x, entropyApprox trialParameter (gCos x) - trialParameter ^ 4 / 10000 ∂haar 1 := by
      rw [integral_sub (SharpLSI.integrable_bdd (continuous_entropyApprox _)) (integrable_const _)]
      simp
    _ ≤ _ := by
      apply integral_mono
        ((SharpLSI.integrable_bdd (continuous_entropyApprox _)).sub (integrable_const _))
        (SharpLSI.integrable_bdd (continuous_klFun.comp (trial_continuous _)))
      intro x
      show entropyApprox trialParameter (gCos x) - trialParameter ^ 4 / 10000 ≤
        klFun (trial trialParameter x)
      rw [trial_eq_rhoPoly]
      exact explicit_entropy_pointwise (abs_gCos_le x)

theorem explicit_trial_fisher_upper :
    fisher (trial trialParameter) ≤ aCos *
      (trialParameter ^ 2 / 2 + 11 * trialParameter ^ 4 / 200 + trialParameter ^ 4 / 10000) := by
  have hc := continuous_gCos
  have hnum : Continuous (fun x => fisherNumerator trialParameter (gCos x)) := by
    unfold fisherNumerator
    fun_prop
  have hden : Continuous (fun x => rhoPoly trialParameter (gCos x)) := by
    unfold rhoPoly
    fun_prop
  have hint : Integrable (fun x => fisherNumerator trialParameter (gCos x) /
        rhoPoly trialParameter (gCos x)) (haar 1) :=
    SharpLSI.integrable_bdd (hnum.div hden fun x => (rhoPoly_pos (abs_gCos_le x)).ne')
  rw [fisher_trial_integral trialParameter_small]
  calc
    aCos * (∫ x, fisherNumerator trialParameter (gCos x) /
        rhoPoly trialParameter (gCos x) ∂haar 1) ≤
        aCos * (∫ x, fisherApprox trialParameter (gCos x) + trialParameter ^ 4 / 10000 ∂haar 1) := by
      apply mul_le_mul_of_nonneg_left _ a_pos.le
      apply integral_mono hint
        ((SharpLSI.integrable_bdd (continuous_fisherApprox _)).add (integrable_const _))
      intro x
      exact fisher_polynomial_upper (abs_gCos_le x)
    _ = _ := by
      rw [integral_add (SharpLSI.integrable_bdd (continuous_fisherApprox _)) (integrable_const _),
        integral_fisherApprox]
      simp

/-- Strict inequality for an actual positive normalized trial density. -/
theorem explicit_trial_defect_negative :
    realDiss (trial trialParameter) - 3 * aCos * realGap (trial trialParameter) < 0 := by
  have hI := explicit_trial_fisher_upper
  have hH := mul_le_mul_of_nonneg_left explicit_trial_entropy_lower
    (show 0 ≤ 3 * aCos by have := a_pos; positivity)
  have hp : 0 < aCos * trialParameter ^ 4 :=
    mul_pos a_pos (pow_pos trialParameter_pos 4)
  unfold realDiss realGap
  rw [firstMode_trial, forceEnergy_trial]
  nlinarith

/-- The strict upper bound is now obtained WITHOUT `TrialFourthOrder`. -/
theorem realRate_lt_threshold : realRate < aCos * (3 / 2) := by
  have ha := trial_admissible trialParameter_small trialParameter_pos.ne'
  have hG := realGap_pos ha
  have hdef := explicit_trial_defect_negative
  apply (realRate_le_realQuotient ha).trans_lt
  apply (div_lt_iff₀ (by positivity : 0 < 2 * realGap (trial trialParameter))).mpr
  nlinarith

end SharpLSI.FL.Prop82
