import FullLabeledLSI.Nonvacuity.Prop82.Poincare

/-!
# The two-harmonic trial family

The family, regularity, strict positivity, normalization, Fourier moment,
and admissibility have proof scripts below. An OPTIONAL fourth-order route is
also stated: `TrialFourthOrder` is unproved, and its conditional theorem takes
it as an explicit input. This route is NOT used by the main assembly.
`ExplicitTrial.lean` instead supplies a direct strict-upper-bound proof script
using an explicit rational trial, without any fourth-order-limit assumption.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82

noncomputable def trial (t : Real) (x : Torus 1) : Real :=
  1 + t * gCos x + (t ^ 2 / 5) * c2 x

theorem trial_smooth (t : Real) : IsSmoothT (trial t) :=
  (contDiff_const.add (contDiff_const.mul contDiff_gCos_lift)).add
    (contDiff_const.mul contDiff_c2_lift)

theorem trial_continuous (t : Real) : Continuous (trial t) :=
  Sec8.continuous_of_smooth (trial_smooth t)

theorem trial_mass (t : Real) : ∫ x, trial t x ∂haar 1 = 1 := by
  unfold trial
  have i1 : Integrable (fun x : Torus 1 => 1 + t * gCos x) (haar 1) :=
    SharpLSI.integrable_bdd (continuous_const.add (continuous_const.mul continuous_gCos))
  have i2 : Integrable (fun x : Torus 1 => t ^ 2 / 5 * c2 x) (haar 1) :=
    (SharpLSI.integrable_bdd continuous_c2).const_mul (t ^ 2 / 5)
  rw [integral_add i1 i2,
    integral_mode continuous_gCos integral_gCos t, integral_const_mul, integral_c2]
  ring

/-- A uniform positive lower bound, not merely almost-everywhere positivity. -/
theorem trial_lower_bound {t : Real} (ht : |t| ≤ 1 / 2) (x : Torus 1) :
    9 / 20 ≤ trial t x := by
  have hg := abs_gCos_le x
  have hc := (abs_le.mp (abs_c2_le x)).1
  have htc : |t * gCos x| ≤ 1 / 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg t, abs_nonneg (gCos x)]
  have htlo := (abs_le.mp htc).1
  have ht2 : t ^ 2 ≤ 1 / 4 := by
    nlinarith [sq_abs t, abs_nonneg t]
  have hprod := mul_nonneg (sq_nonneg t) (show 0 ≤ c2 x + 1 by linarith)
  unfold trial
  nlinarith

theorem trial_probability {t : Real} (ht : |t| ≤ 1 / 2) :
    SmoothProbability (trial t) := by
  refine ⟨trial_smooth t, ?_, trial_mass t⟩
  intro x
  have := trial_lower_bound ht x
  linarith

theorem integral_gCos_c2 : ∫ x, gCos x * c2 x ∂haar 1 = 0 := by
  have he : ∀ x, gCos x * c2 x = 2 * gCos x ^ 3 - gCos x := fun x => by
    rw [c2_apply]; ring
  simp_rw [he]
  have i1 : Integrable (fun x : Torus 1 => 2 * gCos x ^ 3) (haar 1) :=
    (SharpLSI.integrable_bdd (continuous_gCos.pow 3)).const_mul 2
  have i2 : Integrable (fun x : Torus 1 => gCos x) (haar 1) :=
    SharpLSI.integrable_bdd continuous_gCos
  rw [integral_sub i1 i2, integral_const_mul, integral_gCos_pow3, integral_gCos]
  ring

theorem integral_sCos_c2 : ∫ x, sCos x * c2 x ∂haar 1 = 0 := by
  have he : ∀ x, sCos x * c2 x = 2 * (sCos x * gCos x ^ 2) - sCos x :=
    fun x => by rw [c2_apply]; ring
  simp_rw [he]
  have i1 : Integrable (fun x : Torus 1 => 2 * (sCos x * gCos x ^ 2)) (haar 1) :=
    (SharpLSI.integrable_bdd (continuous_sCos.mul (continuous_gCos.pow 2))).const_mul 2
  have i2 : Integrable (fun x : Torus 1 => sCos x) (haar 1) :=
    SharpLSI.integrable_bdd continuous_sCos
  rw [integral_sub i1 i2, integral_const_mul, integral_sCos_gCos_sq, integral_sCos]
  ring

theorem integral_gCos_trial (t : Real) :
    ∫ x, gCos x * trial t x ∂haar 1 = t / 2 := by
  have he : ∀ x, gCos x * trial t x =
      gCos x * (1 + t * gCos x) + (t ^ 2 / 5) * (gCos x * c2 x) :=
    fun x => by unfold trial; ring
  simp_rw [he]
  have i1 : Integrable (fun x : Torus 1 => gCos x * (1 + t * gCos x)) (haar 1) :=
    SharpLSI.integrable_bdd (continuous_gCos.mul
      (continuous_const.add (continuous_const.mul continuous_gCos)))
  have i2 : Integrable (fun x : Torus 1 => t ^ 2 / 5 * (gCos x * c2 x)) (haar 1) :=
    (SharpLSI.integrable_bdd (continuous_gCos.mul continuous_c2)).const_mul (t ^ 2 / 5)
  rw [integral_add i1 i2,
    integral_gCos_rho, integral_const_mul, integral_gCos_c2]
  ring

theorem integral_sCos_trial (t : Real) :
    ∫ x, sCos x * trial t x ∂haar 1 = 0 := by
  have he : ∀ x, sCos x * trial t x =
      sCos x * (1 + t * gCos x) + (t ^ 2 / 5) * (sCos x * c2 x) :=
    fun x => by unfold trial; ring
  simp_rw [he]
  have i1 : Integrable (fun x : Torus 1 => sCos x * (1 + t * gCos x)) (haar 1) :=
    SharpLSI.integrable_bdd (continuous_sCos.mul
      (continuous_const.add (continuous_const.mul continuous_gCos)))
  have i2 : Integrable (fun x : Torus 1 => t ^ 2 / 5 * (sCos x * c2 x)) (haar 1) :=
    (SharpLSI.integrable_bdd (continuous_sCos.mul continuous_c2)).const_mul (t ^ 2 / 5)
  rw [integral_add i1 i2,
    integral_sCos_rho, integral_const_mul, integral_sCos_c2]
  ring

theorem firstMode_trial (t : Real) : firstMode (trial t) = t ^ 2 / 4 := by
  rw [firstMode_eq (Sec8.integrable_of_smooth (trial_smooth t)),
    integral_gCos_trial, integral_sCos_trial]
  ring

theorem trial_gap_pos {t : Real} (ht : |t| ≤ 1 / 2) (ht0 : t ≠ 0) :
    0 < gap cosV (cosW 1) (densMeasure (trial t)) := by
  have hp := trial_probability ht
  have hfin := (circle_quantitative_lsi_aux hp.nonneg hp.mass hp.sqrt_memH1).1
  have hkl : klDiv (densMeasure (trial t)) (haar 1) =
      ENNReal.ofReal (entropy (trial t)) := (ENNReal.ofReal_toReal hfin).symm
  rw [(cosine_free_energy_aux (by norm_num : (0 : Real) < 1)).2.2.2.1
    (trial t) hp.nonneg hp.mass,
    hkl, EReal.coe_ennreal_ofReal, max_eq_left (entropy_nonneg (trial t)),
    firstMode_trial, ← EReal.coe_add]
  have hs : 0 < t ^ 2 := sq_pos_of_ne_zero ht0
  have hh := entropy_nonneg (trial t)
  have hpos : 0 < entropy (trial t) + 1 / 2 * (t ^ 2 / 4) := by nlinarith
  exact_mod_cast hpos

theorem trial_admissible {t : Real} (ht : |t| ≤ 1 / 2) (ht0 : t ≠ 0) :
    Admissible cosV (cosW 1) (trial t) :=
  (trial_probability ht).admissible (trial_gap_pos ht ht0)

/-- OPEN ANALYTIC OBLIGATION. A proof of this proposition is not supplied.
The coefficient is the physical one: `-aCos/160`, not `-1/160`.
The definitions in this limit are the actual KL/Fisher/force integrals. -/
def TrialFourthOrder : Prop :=
  Tendsto (fun t : Real =>
    (realDiss (trial t) - 3 * aCos * realGap (trial t)) / t ^ 4)
    (𝓝[≠] 0) (𝓝 (-aCos / 160))

/-- Conditional only on the explicitly named fourth-order analytic limit.
A polynomial coefficient calculation alone does not discharge `hfourth`. -/
theorem realRate_lt_threshold_of_trial_fourth_order (hfourth : TrialFourthOrder) :
    realRate < aCos * (3 / 2) := by
  have hneg := eventually_negative_of_quartic_limit a_pos hfourth
  have hsmall : ∀ᶠ t in 𝓝[≠] (0 : Real), |t| < 1 / 2 :=
    eventually_nhdsWithin_of_eventually_nhds small_eventually
  have hne : ∀ᶠ t in 𝓝[≠] (0 : Real), t ≠ 0 := self_mem_nhdsWithin
  obtain ⟨t, ht, hts, ht0⟩ := (hneg.and (hsmall.and hne)).exists
  have ha := trial_admissible hts.le ht0
  have hG := realGap_pos ha
  apply (realRate_le_realQuotient ha).trans_lt
  apply (div_lt_iff₀ (by positivity : 0 < 2 * realGap (trial t))).mpr
  nlinarith

end SharpLSI.FL.Prop82
