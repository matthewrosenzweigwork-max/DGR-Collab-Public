import LeanResearch.PeriodicAttractiveLogGas.StationaryRearrangement
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Order.ProjIcc

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PeriodicAttractiveLogGas.StationaryCumulative
open StationaryRearrangement

/-- Constant extension of the interval profile. -/
def extendProfile (q : ℝ → ℝ) : ℝ → ℝ :=
  Set.IccExtend (a := (0:ℝ)) (b := 1) (by norm_num) (fun x => q x)

lemma extendProfile_eq {q : ℝ → ℝ} {s : ℝ} (hs : s ∈ Icc 0 1) :
    extendProfile q s = q s := by
  exact Set.IccExtend_val (by norm_num : (0:ℝ)≤1) (fun x => q x) ⟨s,hs⟩

lemma continuous_extendProfile {q : ℝ → ℝ} (hq : ContinuousOn q (Icc 0 1)) :
    Continuous (extendProfile q) := by
  exact (continuousOn_iff_continuous_domRestrict.mp hq).Icc_extend'

lemma antitone_extendProfile {q : ℝ → ℝ} (hq : AntitoneOn q (Icc 0 1)) :
    Antitone (extendProfile q) := by
  intro a b hab
  exact hq (Set.projIcc 0 1 (by norm_num) a).property
    (Set.projIcc 0 1 (by norm_num) b).property
    (Set.monotone_projIcc (by norm_num : (0:ℝ)≤1) hab)

lemma ac_extendProfile {q : ℝ → ℝ} (hq : AbsolutelyContinuousOnInterval q 0 1) :
    AbsolutelyContinuousOnInterval (extendProfile q) 0 1 := by
  apply hq.congr
  intro s hs
  exact (extendProfile_eq (by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hs)).symm

/-- The literal source cumulative integral. A continuous constant extension of
the decreasing rearrangement outside [0,1] will supply the global input below. -/
def cumulative (q : ℝ → ℝ) (s : ℝ) : ℝ := ∫ r in (0 : ℝ)..s, Real.exp (q r)

lemma cumulative_extendProfile {q : ℝ → ℝ} {s : ℝ} (hs : s ∈ Icc 0 1) :
    cumulative (extendProfile q) s = cumulative q s := by
  apply intervalIntegral.integral_congr
  intro r hr
  have hri : r ∈ Icc 0 s := by simpa only [uIcc_of_le hs.1] using hr
  exact congrArg Real.exp (extendProfile_eq ⟨hri.1,hri.2.trans hs.2⟩)

lemma exp_ac {q : ℝ → ℝ} (hq : AbsolutelyContinuousOnInterval q 0 1) :
    AbsolutelyContinuousOnInterval (fun s => Real.exp (q s)) 0 1 := by
  obtain ⟨C,hC⟩ := hq.exists_bound
  have he : ContDiff ℝ 1 Real.exp := Real.contDiff_exp
  obtain ⟨K,hK⟩ := he.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_Icc (-C) C) isCompact_Icc
  apply hK.comp_absolutelyContinuousOnInterval _ hq
  intro s hs
  exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hC s hs)

lemma cumulative_ac {q : ℝ → ℝ} (hq : Continuous q) :
    AbsolutelyContinuousOnInterval (cumulative q) 0 1 := by
  exact ((Real.continuous_exp.comp hq).intervalIntegrable 0 1).absolutelyContinuousOnInterval_intervalIntegral
    (by simp)

lemma cumulative_hasDerivAt {q : ℝ → ℝ} (hq : Continuous q) (s : ℝ) :
    HasDerivAt (cumulative q) (Real.exp (q s)) s := by
  exact intervalIntegral.integral_hasDerivAt_right ((Real.continuous_exp.comp hq).intervalIntegrable 0 s)
    (Real.continuous_exp.comp hq).aestronglyMeasurable.stronglyMeasurableAtFilter (Real.continuous_exp.comp hq).continuousAt

lemma deriv_cumulative {q : ℝ → ℝ} (hq : Continuous q) :
    deriv (cumulative q) = fun s => Real.exp (q s) := by
  funext s
  exact (cumulative_hasDerivAt hq s).deriv

lemma deriv_cumulative_ac {q : ℝ → ℝ} (hc : Continuous q)
    (hq : AbsolutelyContinuousOnInterval q 0 1) :
    AbsolutelyContinuousOnInterval (deriv (cumulative q)) 0 1 := by
  rw [deriv_cumulative hc]
  exact exp_ac hq

lemma second_deriv_ae {q : ℝ → ℝ} (hc : Continuous q)
    (hq : AbsolutelyContinuousOnInterval q 0 1) :
    ∀ᵐ s ∂volume.restrict (Ioc (0:ℝ) 1),
      deriv (deriv (cumulative q)) s = Real.exp (q s) * deriv q s := by
  have ha : ∀ᵐ s ∂volume.restrict (Ioc (0:ℝ) 1),
      s ∈ uIcc (0:ℝ) 1 → DifferentiableAt ℝ q s := ae_restrict_of_ae hq.ae_differentiableAt
  filter_upwards [ha,ae_restrict_mem measurableSet_Ioc] with s hd hs
  have hi : s ∈ uIcc (0:ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ⟨hs.1.le,hs.2⟩
  rw [deriv_cumulative hc]
  exact ((Real.hasDerivAt_exp (q s)).comp s (hd hi).hasDerivAt).deriv

lemma curvature_nonneg {q : ℝ → ℝ} (hc : Continuous q) (hq : Antitone q) (s : ℝ) :
    0 ≤ -deriv (deriv (cumulative q)) s := by
  rw [deriv_cumulative hc]
  have ha : Antitone (fun r => Real.exp (q r)) := fun a b hab =>
    Real.exp_le_exp.mpr (hq hab)
  exact neg_nonneg.mpr ha.deriv_nonpos

lemma cumulative_concave {q : ℝ → ℝ} (hc : Continuous q) (hq : Antitone q) :
    ConcaveOn ℝ univ (cumulative q) := by
  apply Antitone.concaveOn_univ_of_deriv (fun s => (cumulative_hasDerivAt hc s).differentiableAt)
  rw [deriv_cumulative hc]
  exact fun a b hab => Real.exp_le_exp.mpr (hq hab)

@[simp] lemma cumulative_zero (q : ℝ → ℝ) : cumulative q 0 = 0 := by
  simp [cumulative]

lemma cumulative_ge {q : ℝ → ℝ} (hc : Continuous q) (hq : Antitone q)
    (hmass : (∫ s in (0 : ℝ)..1, Real.exp (q s)) = 1) {s : ℝ} (hs : s ∈ Icc 0 1) :
    s ≤ cumulative q s := by
  have h := (cumulative_concave hc hq).2 (mem_univ (0:ℝ)) (mem_univ (1:ℝ))
    (sub_nonneg.mpr hs.2) hs.1 (show (1-s)+s=1 by ring)
  have h1 : cumulative q 1 = 1 := hmass
  simpa only [smul_eq_mul, cumulative_zero, h1, mul_zero, mul_one, zero_add] using h

/-- Nonconstancy of the monotone endpoint values gives positive excess area.
The negative second derivative is the actual derivative, not supplied data. -/
lemma excessArea_pos {q : ℝ → ℝ} (hc : Continuous q) (hq : Antitone q)
    (hac : AbsolutelyContinuousOnInterval q 0 1)
    (hmass : (∫ s in (0 : ℝ)..1, Real.exp (q s)) = 1) (hne : q 1 < q 0) :
    0 < excessArea (cumulative q) := by
  let M := cumulative q
  let d := fun s => -deriv (deriv M) s
  let w := fun s => s*(1-s)*d s
  have hM := cumulative_ac hc
  have hp := deriv_cumulative_ac hc hac
  have h0 : M 0 = 0 := cumulative_zero q
  have h1 : M 1 = 1 := hmass
  have hd : IntervalIntegrable d volume 0 1 := hp.intervalIntegrable_deriv.neg
  have hw : IntervalIntegrable w volume 0 1 := hd.continuousOn_mul (by fun_prop)
  have hn : 0 ≤ᵐ[volume.restrict (Ioc (0:ℝ) 1)] w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact mul_nonneg (mul_nonneg hs.1.le (sub_nonneg.mpr hs.2)) (curvature_nonneg hc hq s)
  have hid := curvature_moment hM hp h0 h1
  change (∫ s in (0:ℝ)..1, w s) = 2*excessArea M at hid
  have hi0 : 0 ≤ ∫ s in (0:ℝ)..1, w s := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
    exact integral_nonneg_of_ae hn
  have hA0 : 0 ≤ excessArea M := by linarith only [hid,hi0]
  apply lt_of_le_of_ne hA0
  intro hzero
  have hi : (∫ s in (0:ℝ)..1, w s)=0 := by rw [hid,← hzero]; ring
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] at hi
  have hw0 := (integral_eq_zero_iff_of_nonneg_ae hn hw.1).mp hi
  have hne1 : ∀ᵐ s : ℝ ∂volume.restrict (Ioc (0:ℝ) 1), s ≠ 1 :=
    ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
  have hd0 : d =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] 0 := by
    filter_upwards [hw0,hne1,ae_restrict_mem measurableSet_Ioc] with s hs hs1 hmem
    have hpw : 0 < s*(1-s) := mul_pos hmem.1 (sub_pos.mpr (lt_of_le_of_ne hmem.2 hs1))
    exact (mul_eq_zero.mp hs).resolve_left hpw.ne'
  have hid0 : (∫ s in (0:ℝ)..1, d s) = 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1), integral_congr_ae hd0]
    simp only [Pi.zero_apply, integral_zero]
  have hdiff := hp.integral_deriv_eq_sub
  have hder := deriv_cumulative hc
  change (∫ s in (0:ℝ)..1, -deriv (deriv (cumulative q)) s)=0 at hid0
  rw [intervalIntegral.integral_neg, hdiff, hder] at hid0
  have hstrict : Real.exp (q 1) < Real.exp (q 0) := Real.exp_lt_exp.mpr hne
  dsimp only at hid0
  linarith only [hid0,hstrict]

lemma deriv_extendProfile_eq {q : ℝ → ℝ} {s : ℝ} (hs : s ∈ Ioo 0 1) :
    deriv (extendProfile q) s = deriv q s := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
  exact extendProfile_eq ⟨hr.1.le,hr.2.le⟩

lemma second_deriv_extendProfile_ae {q : ℝ → ℝ}
    (hq : AbsolutelyContinuousOnInterval q 0 1) :
    ∀ᵐ s ∂volume.restrict (Ioc (0:ℝ) 1),
      deriv (deriv (cumulative (extendProfile q))) s = Real.exp (q s) * deriv q s := by
  have hc : ContinuousOn q (Icc 0 1) := by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hq.continuousOn
  have ha := second_deriv_ae (continuous_extendProfile hc) (ac_extendProfile hq)
  have hn : ∀ᵐ s : ℝ ∂volume.restrict (Ioc (0:ℝ) 1), s ≠ 1 :=
    ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
  filter_upwards [ha,hn,ae_restrict_mem measurableSet_Ioc] with s hs hn hm
  have hi : s ∈ Ioo (0:ℝ) 1 := ⟨hm.1,lt_of_le_of_ne hm.2 hn⟩
  simpa only [extendProfile_eq ⟨hm.1.le,hm.2⟩,deriv_extendProfile_eq hi] using hs

/-- The cumulative integral's complete analytic data from an interval profile.
The actual torus rearrangement, its normalization and its absolute continuity
are still to be constructed; no stationary or geometric result is assumed here. -/
theorem interval_cumulative_data {q : ℝ → ℝ}
    (hq : AbsolutelyContinuousOnInterval q 0 1) (ha : AntitoneOn q (Icc 0 1))
    (hmass : (∫ s in (0:ℝ)..1, Real.exp (q s)) = 1) (hne : q 1 < q 0) :
    let M := cumulative (extendProfile q)
    AbsolutelyContinuousOnInterval M 0 1 ∧
    AbsolutelyContinuousOnInterval (deriv M) 0 1 ∧
    M 0 = 0 ∧ M 1 = 1 ∧
    (∀ s ∈ Icc (0:ℝ) 1, M s = cumulative q s ∧ deriv M s = Real.exp (q s)) ∧
    ConcaveOn ℝ univ M ∧
    (∀ s ∈ Icc (0:ℝ) 1, s ≤ M s) ∧
    0 < excessArea M ∧
    (∀ᵐ s ∂volume.restrict (Ioc (0:ℝ) 1),
      deriv (deriv M) s = Real.exp (q s) * deriv q s ∧ 0 ≤ -deriv (deriv M) s) := by
  have hc : ContinuousOn q (Icc 0 1) := by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hq.continuousOn
  have hec := continuous_extendProfile hc
  have hea := antitone_extendProfile ha
  have heac := ac_extendProfile hq
  have hm : cumulative (extendProfile q) 1 = 1 := by
    rw [cumulative_extendProfile (by norm_num : (1:ℝ)∈Icc 0 1)]
    exact hmass
  have he : extendProfile q 1 < extendProfile q 0 := by
    simpa only [extendProfile_eq (by norm_num : (1:ℝ)∈Icc 0 1),
      extendProfile_eq (by norm_num : (0:ℝ)∈Icc 0 1)] using hne
  refine ⟨cumulative_ac hec,deriv_cumulative_ac hec heac,cumulative_zero _,hm,?_,
    cumulative_concave hec hea,?_,excessArea_pos hec hea heac hm he,?_⟩
  · intro s hs
    refine ⟨cumulative_extendProfile hs,?_⟩
    rw [deriv_cumulative hec]
    exact congrArg Real.exp (extendProfile_eq hs)
  · intro s hs
    exact cumulative_ge hec hea hm hs
  · filter_upwards [second_deriv_extendProfile_ae hq] with s hs
    exact ⟨hs,curvature_nonneg hec hea s⟩

end PeriodicAttractiveLogGas.StationaryCumulative
