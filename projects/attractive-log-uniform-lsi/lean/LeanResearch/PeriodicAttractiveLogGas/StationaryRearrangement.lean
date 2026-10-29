import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PeriodicAttractiveLogGas.StationaryRearrangement

/-- The exact scalar profile in the manuscript's square-torus isoperimetric lemma.
The geometric perimeter bound is a separate obligation. -/
def profile (s : ℝ) : ℝ := min (4 * Real.pi * s) (min 4 (4 * Real.pi * (1 - s)))

lemma profile_strict {s : ℝ} (hs : s ∈ Ioo 0 1) :
    4 * Real.pi * s * (1 - s) < profile s := by
  have hπ := Real.pi_pos
  have hp := Real.pi_lt_four
  have hquad : 4 * s * (1 - s) ≤ 1 := by nlinarith [sq_nonneg (2*s-1)]
  unfold profile
  apply lt_min
  · nlinarith [mul_pos hπ (sq_pos_of_pos hs.1)]
  · apply lt_min
    · nlinarith [mul_le_mul_of_nonneg_left hquad hπ.le]
    · nlinarith [mul_pos hπ (sq_pos_of_pos (sub_pos.mpr hs.2))]

lemma profile_continuous : Continuous profile := by
  unfold profile
  fun_prop

/-- The source's area between the rearranged cumulative distribution and the diagonal. -/
def excessArea (M : ℝ → ℝ) : ℝ := ∫ s in (0 : ℝ)..1, M s - s

private lemma id_ac : AbsolutelyContinuousOnInterval (fun s : ℝ => s) 0 1 :=
  contDiff_id.contDiffOn.absolutelyContinuousOnInterval

private lemma linear_ac :
    AbsolutelyContinuousOnInterval (fun s : ℝ => 1 - 2*s) 0 1 := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  fun_prop

private lemma quadratic_ac :
    AbsolutelyContinuousOnInterval (fun s : ℝ => s*(1-s)) 0 1 := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  fun_prop

private lemma deriv_linear (s : ℝ) : deriv (fun x : ℝ => 1-2*x) s = -2 := by
  simpa only [id_eq, mul_one, neg_mul, one_mul] using
    (((hasDerivAt_id s).const_mul 2).const_sub 1).deriv

private lemma deriv_quadratic (s : ℝ) :
    deriv (fun x : ℝ => x*(1-x)) s = 1-2*s := by
  have h : HasDerivAt (fun x : ℝ => x*(1-x)) (1*(1-s)+s*(-1)) s :=
    (hasDerivAt_id s).mul ((hasDerivAt_id s).const_sub 1)
  convert h.deriv using 1
  ring

lemma excessArea_eq {M : ℝ → ℝ} (hM : AbsolutelyContinuousOnInterval M 0 1) :
    excessArea M = (∫ s in (0 : ℝ)..1, M s) - 1/2 := by
  have hi : IntervalIntegrable (fun s : ℝ => s) volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  rw [excessArea, intervalIntegral.integral_sub hM.continuousOn.intervalIntegrable hi,
    integral_id]
  norm_num

/-- First integration by parts identity, with precisely the source's endpoint and W21 data. -/
lemma curvature_moment {M : ℝ → ℝ}
    (hM : AbsolutelyContinuousOnInterval M 0 1)
    (hp : AbsolutelyContinuousOnInterval (deriv M) 0 1)
    (h0 : M 0 = 0) (h1 : M 1 = 1) :
    (∫ s in (0 : ℝ)..1, s*(1-s)*(-deriv (deriv M) s)) = 2 * excessArea M := by
  have hq := quadratic_ac.integral_mul_deriv_eq_deriv_mul hp
  have hl := linear_ac.integral_mul_deriv_eq_deriv_mul hM
  simp only [deriv_quadratic, mul_zero, zero_mul, sub_self] at hq
  simp only [deriv_linear, h0, h1] at hl
  rw [intervalIntegral.integral_const_mul] at hl
  have hn : (∫ s in (0 : ℝ)..1, s*(1-s)*(-deriv (deriv M) s)) =
      -(∫ s in (0 : ℝ)..1, s*(1-s)*deriv (deriv M) s) := by
    simp only [mul_neg, intervalIntegral.integral_neg]
  rw [hn, hq, excessArea_eq hM]
  norm_num at hl ⊢
  linarith

/-- Second integration identity. No integrated identity is an input. -/
lemma slope_excess {M : ℝ → ℝ} (hM : AbsolutelyContinuousOnInterval M 0 1)
    (h0 : M 0 = 0) (h1 : M 1 = 1) :
    (∫ s in (0 : ℝ)..1, deriv M s * (M s - s)) = excessArea M := by
  have hm := hM.integral_deriv_mul_eq_sub hM
  have hs := id_ac.integral_mul_deriv_eq_deriv_mul hM
  have him := hM.intervalIntegrable_deriv.mul_continuousOn hM.continuousOn
  have his := hM.intervalIntegrable_deriv.mul_continuousOn continuous_id.continuousOn
  change IntervalIntegrable (fun s : ℝ => deriv M s * s) volume 0 1 at his
  have htwo : (∫ s in (0 : ℝ)..1, deriv M s * M s + M s * deriv M s) =
      2 * (∫ s in (0 : ℝ)..1, deriv M s * M s) := by
    simp_rw [show ∀ s, deriv M s * M s + M s * deriv M s =
      2 * (deriv M s * M s) by intro s; ring]
    rw [intervalIntegral.integral_const_mul]
  rw [htwo, h0, h1] at hm
  simp only [deriv_id'', h0, h1, mul_one, mul_zero, one_mul] at hs
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub him his, excessArea_eq hM]
  have hcomm : (∫ s in (0 : ℝ)..1, deriv M s * s) =
      ∫ s in (0 : ℝ)..1, s * deriv M s := by
    congr 1
    funext s
    ring
  rw [hcomm]
  linarith

lemma profile_ge {s : ℝ} (hs : s ∈ Icc 0 1) :
    4 * Real.pi * s * (1-s) ≤ profile s := by
  by_cases h0 : s = 0
  · subst s
    simp [profile, Real.pi_nonneg]
  by_cases h1 : s = 1
  · subst s
    simp [profile, Real.pi_nonneg]
  exact (profile_strict ⟨lt_of_le_of_ne hs.1 (Ne.symm h0),
    lt_of_le_of_ne hs.2 h1⟩).le

/-- Strict isoperimetric scalar comparison integrated against the actual second
derivative. Positivity on a set of positive measure is derived from the area
identity, not introduced as an additional premise. -/
lemma curvature_profile_strict {M : ℝ → ℝ}
    (hM : AbsolutelyContinuousOnInterval M 0 1)
    (hp : AbsolutelyContinuousOnInterval (deriv M) 0 1)
    (h0 : M 0 = 0) (h1 : M 1 = 1) (hA : 0 < excessArea M)
    (hn : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), 0 ≤ -deriv (deriv M) s) :
    8 * Real.pi * excessArea M <
      ∫ s in (0 : ℝ)..1, profile s * (-deriv (deriv M) s) := by
  let d := fun s => -deriv (deriv M) s
  let f := fun s => 4 * Real.pi * s * (1-s) * d s
  let g := fun s => profile s * d s
  have hd : IntervalIntegrable d volume 0 1 := hp.intervalIntegrable_deriv.neg
  have hf : IntervalIntegrable f volume 0 1 := hd.continuousOn_mul (by fun_prop)
  have hg : IntervalIntegrable g volume 0 1 :=
    hd.continuousOn_mul profile_continuous.continuousOn
  have hle : f ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] g := by
    filter_upwards [hn, ae_restrict_mem measurableSet_Ioc] with s hs hmem
    exact mul_le_mul_of_nonneg_right (profile_ge ⟨hmem.1.le,hmem.2⟩) hs
  have hid : (∫ s in (0 : ℝ)..1, f s) = 8 * Real.pi * excessArea M := by
    have he : f = fun s => 4 * Real.pi * (s*(1-s)*(-deriv (deriv M) s)) := by
      funext s
      dsimp [f,d]
      ring
    rw [he, intervalIntegral.integral_const_mul, curvature_moment hM hp h0 h1]
    ring
  rw [← hid]
  change (∫ s in (0 : ℝ)..1, f s) < ∫ s in (0 : ℝ)..1, g s
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  have hweak := MeasureTheory.integral_mono_ae hf.1 hg.1 hle
  apply lt_of_le_of_ne hweak
  intro heq
  have he := (MeasureTheory.integral_eq_iff_of_ae_le hf.1 hg.1 hle).mp heq
  have hz : f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] 0 := by
    filter_upwards [he,hn,ae_restrict_mem measurableSet_Ioc] with s he hs hmem
    by_cases h1s : s = 1
    · simp [f,h1s]
    have hstrict := profile_strict ⟨hmem.1,lt_of_le_of_ne hmem.2 h1s⟩
    have hdz : d s = 0 := by
      apply le_antisymm _ hs
      by_contra! hpos
      exact (mul_lt_mul_of_pos_right hstrict hpos).ne he
    simp [f,hdz]
  have hi : (∫ s in (0 : ℝ)..1, f s) = 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      MeasureTheory.integral_congr_ae hz]
    simp only [Pi.zero_apply, integral_zero]
  have hpositive : 0 < 8 * Real.pi * excessArea M := by positivity
  linarith only [hid,hi,hpositive]

/-- The complete integration contradiction, including the endpoint rho=8pi.
Constructing M from smooth torus level sets and proving the rearranged
differential inequality remain separate geometric/analytic obligations. -/
theorem rearranged_contradiction {M : ℝ → ℝ} {ρ : ℝ}
    (hM : AbsolutelyContinuousOnInterval M 0 1)
    (hp : AbsolutelyContinuousOnInterval (deriv M) 0 1)
    (h0 : M 0 = 0) (h1 : M 1 = 1) (hA : 0 < excessArea M)
    (hn : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), 0 ≤ -deriv (deriv M) s)
    (hineq : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      profile s * (-deriv (deriv M) s) ≤ ρ * deriv M s * (M s-s))
    (hρ : ρ ≤ 8*Real.pi) : False := by
  have hleft := hp.intervalIntegrable_deriv.neg.continuousOn_mul
    profile_continuous.continuousOn
  have hright : IntervalIntegrable (fun s => ρ * deriv M s * (M s-s)) volume 0 1 :=
    (hp.continuousOn.const_mul ρ |>.mul (hM.continuousOn.sub continuous_id.continuousOn)).intervalIntegrable
  have hle : (∫ s in (0 : ℝ)..1, profile s * (-deriv (deriv M) s)) ≤
      ∫ s in (0 : ℝ)..1, ρ * deriv M s * (M s-s) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
    exact MeasureTheory.integral_mono_ae hleft.1 hright.1 hineq
  have hid : (∫ s in (0 : ℝ)..1, ρ * deriv M s * (M s-s)) = ρ * excessArea M := by
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul, slope_excess hM h0 h1]
  have hstrict := curvature_profile_strict hM hp h0 h1 hA hn
  rw [hid] at hle
  have hlast := mul_le_mul_of_nonneg_right hρ hA.le
  linarith only [hle,hstrict,hlast]

end PeriodicAttractiveLogGas.StationaryRearrangement
