import DGPS.Examples.EngineeredCentralInterval
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# The interval weak-to-AC adapter for EX040

Compact primitives identify zero weak derivatives as constants. This yields an AC
representative up to both endpoints for every weak W1,1 pair, with a.e. derivative and value
preserved. No endpoint trace is prescribed. All helpers retain the packet suffix.
-/

open MeasureTheory Real Set Filter Topology
open scoped ContDiff

namespace DGPS.Examples

/-- A smooth compactly supported test of integral zero has a smooth primitive compactly
supported in the same open interval. -/
theorem compact_smooth_primitive_EX040 {a b : ℝ} {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcompact : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ Ioo a b) (hzero : ∫ x, φ x = 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ioo a b ∧ ∀ x : ℝ, HasDerivAt ψ (φ x) x := by
  classical
  by_cases hz : φ = 0
  · refine ⟨fun _ => 0, contDiff_const, ?_, by simp, ?_⟩
    · exact HasCompactSupport.intro isCompact_empty (fun _ _ => rfl)
    · intro x
      simpa only [hz, Pi.zero_apply] using hasDerivAt_const x (0 : ℝ)
  have hne : (tsupport φ).Nonempty := by
    by_contra hn
    apply hz
    funext x
    exact image_eq_zero_of_notMem_tsupport (fun hx => hn ⟨x, hx⟩)
  obtain ⟨c, hc, hmin⟩ :=
    hcompact.isCompact.exists_isMinOn hne (continuous_id.continuousOn)
  obtain ⟨d, hd, hmax⟩ :=
    hcompact.isCompact.exists_isMaxOn hne (continuous_id.continuousOn)
  have hmin' : ∀ x ∈ tsupport φ, c ≤ x := fun x hx => hmin hx
  have hmax' : ∀ x ∈ tsupport φ, x ≤ d := fun x hx => hmax hx
  have hac : a < c := (hsupp hc).1
  have hdb : d < b := (hsupp hd).2
  let l : ℝ := (a + c) / 2
  let r : ℝ := (d + b) / 2
  have hal : a < l := by dsimp [l]; linarith
  have hlc : l < c := by dsimp [l]; linarith
  have hdr : d < r := by dsimp [r]; linarith
  have hrb : r < b := by dsimp [r]; linarith
  have hsub : Function.support φ ⊆ Ioc l r := by
    intro x hx
    have ht := subset_tsupport φ hx
    exact ⟨hlc.trans_le (hmin' x ht), (hmax' x ht).trans hdr.le⟩
  let F : ℝ → ℝ := fun x => ∫ t in l..x, φ t
  have hFd : ∀ x : ℝ, HasDerivAt F (φ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hφ.continuous.intervalIntegrable l x)
      hφ.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hφ.continuous.continuousAt
  have hder : deriv F = φ := funext fun x => (hFd x).deriv
  have hFs : ContDiff ℝ ∞ F := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun x => (hFd x).differentiableAt, ?_⟩
    rw [hder]
    exact hφ
  have hleft : ∀ x : ℝ, x ≤ l → F x = 0 := by
    intro x hx
    change (∫ t in l..x, φ t) = 0
    calc
      _ = ∫ _ in l..x, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_ge hx] at ht
        apply image_eq_zero_of_notMem_tsupport
        intro hts
        have hct := hmin' t hts
        linarith [ht.2]
      _ = 0 := by simp
  have hright : ∀ x : ℝ, r ≤ x → F x = 0 := by
    intro x hx
    change (∫ t in l..x, φ t) = 0
    have hsubx : Function.support φ ⊆ Ioc l x := by
      intro t ht
      exact ⟨(hsub ht).1, (hsub ht).2.trans hx⟩
    exact (intervalIntegral.integral_eq_integral_of_support_subset hsubx).trans hzero
  have hsupport : Function.support F ⊆ Icc l r := by
    intro x hx
    by_contra hnot
    rcases lt_or_ge x l with hxl | hlx
    · exact hx (hleft x hxl.le)
    · have hrx : r < x := lt_of_not_ge fun hxr => hnot ⟨hlx, hxr⟩
      exact hx (hright x hrx.le)
  have hts : tsupport F ⊆ Icc l r := closure_minimal hsupport isClosed_Icc
  refine ⟨F, hFs, HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupport, ?_, hFd⟩
  intro x hx
  have hxr := hts hx
  exact ⟨hal.trans_le hxr.1, hxr.2.trans_lt hrb⟩

/-- A normalized smooth test supported strictly inside a nondegenerate interval. -/
theorem exists_normalized_interval_test_EX040 {a b : ℝ} (hab : a < b) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      tsupport ρ ⊆ Ioo a b ∧ (∫ x, ρ x) = 1 := by
  let z : ℝ := (a + b) / 2
  let B : ContDiffBump z :=
    { rIn := (b - a) / 8
      rOut := (b - a) / 4
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  refine ⟨B.normed volume, B.contDiff_normed, B.hasCompactSupport_normed, ?_,
    B.integral_normed⟩
  rw [B.tsupport_normed_eq]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  change -(B.rOut) ≤ x - z ∧ x - z ≤ B.rOut at hx
  change a < x ∧ x < b
  dsimp [B, z] at hx
  constructor <;> linarith [hx.1, hx.2]

/-- A locally integrable function with zero weak derivative on an interval is a.e. constant.
The proof uses compact primitives of zero-mean tests, rather than assuming an AC representative. -/
theorem weak_deriv_zero_constant_EX040 {a b : ℝ} (hab : a < b) {u : ℝ → ℝ}
    (hu : LocallyIntegrable u volume)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ x, deriv ψ x * u x) = 0) :
    ∃ c : ℝ, ∀ᵐ x, x ∈ Ioo a b → u x = c := by
  obtain ⟨ρ, hρ, hρc, hρs, hρ1⟩ := exists_normalized_interval_test_EX040 hab
  let c : ℝ := ∫ x, ρ x * u x
  have hρu : Integrable (fun x => ρ x * u x) volume := by
    simpa only [smul_eq_mul] using
      hu.integrable_smul_left_of_hasCompactSupport hρ.continuous hρc
  have hzero : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ x, φ x * (u x - c)) = 0 := by
    intro φ hφ hφc hφs
    let A : ℝ := ∫ x, φ x
    let χ : ℝ → ℝ := fun x => φ x - A * ρ x
    have hχ : ContDiff ℝ ∞ χ := hφ.sub (contDiff_const.mul hρ)
    have hsupport : Function.support χ ⊆ tsupport φ ∪ tsupport ρ := by
      intro x hx
      by_contra hn
      have hp : x ∉ tsupport φ := fun ht => hn (Or.inl ht)
      have hr : x ∉ tsupport ρ := fun ht => hn (Or.inr ht)
      have hp0 := image_eq_zero_of_notMem_tsupport hp
      have hr0 := image_eq_zero_of_notMem_tsupport hr
      exact hx (by simp only [χ, hp0, hr0, mul_zero, sub_zero])
    have hχc : HasCompactSupport χ :=
      HasCompactSupport.of_support_subset_isCompact
        (hφc.isCompact.union hρc.isCompact) hsupport
    have hχs : tsupport χ ⊆ Ioo a b := by
      have ht : tsupport χ ⊆ tsupport φ ∪ tsupport ρ :=
        closure_minimal hsupport ((isClosed_tsupport φ).union (isClosed_tsupport ρ))
      exact ht.trans (union_subset hφs hρs)
    have hχ0 : (∫ x, χ x) = 0 := by
      change (∫ x, φ x - A * ρ x) = 0
      rw [integral_sub (hφ.continuous.integrable_of_hasCompactSupport hφc)
        ((hρ.continuous.integrable_of_hasCompactSupport hρc).const_mul A),
        integral_const_mul, hρ1]
      dsimp [A]
      ring
    obtain ⟨ψ, hψ, hψc, hψs, hψd⟩ :=
      compact_smooth_primitive_EX040 hχ hχc hχs hχ0
    have hder : deriv ψ = χ := funext fun x => (hψd x).deriv
    have hpair := hweak ψ hψ hψc hψs
    rw [hder] at hpair
    have hφu : Integrable (fun x => φ x * u x) volume := by
      simpa only [smul_eq_mul] using
        hu.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have heq : (fun x => χ x * u x) =
        fun x => φ x * u x - A * (ρ x * u x) := by
      funext x
      dsimp [χ]
      ring
    rw [heq, integral_sub hφu (hρu.const_mul A), integral_const_mul] at hpair
    have heq2 : (fun x => φ x * (u x - c)) =
        fun x => φ x * u x - c * φ x := by funext x; ring
    rw [heq2, integral_sub hφu
      ((hφ.continuous.integrable_of_hasCompactSupport hφc).const_mul c),
      integral_const_mul]
    dsimp [c, A] at hpair ⊢
    linarith
  have hul : LocallyIntegrable (fun x => u x - c) volume :=
    hu.sub continuous_const.locallyIntegrable
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hul.locallyIntegrableOn (Ioo a b)) (fun φ hφ hφc hφs => by
      simpa only [smul_eq_mul] using hzero φ hφ hφc hφs)
  refine ⟨c, hae.mono ?_⟩
  intro x hx hmem
  exact sub_eq_zero.mp (hx hmem)

/-- One-dimensional weak W1,1 functions admit an AC representative up to the endpoints.
No value or trace is prescribed at either endpoint. -/
theorem interval_weak_ac_rep_EX040 {a b : ℝ} (hab : a < b) {u g : ℝ → ℝ}
    (hu : IntervalIntegrable u volume a b) (hg : IntervalIntegrable g volume a b)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
      (∫ x in a..b, u x * deriv ψ x) = -(∫ x in a..b, g x * ψ x)) :
    ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v a b ∧
      (∀ᵐ x, x ∈ Ioo a b → u x = v x) ∧
      (∀ᵐ x, x ∈ uIcc a b → HasDerivAt v (g x) x) := by
  let F : ℝ → ℝ := fun x => ∫ t in a..x, g t
  have hFac : AbsolutelyContinuousOnInterval F a b :=
    hg.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hFd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt F (g x) x := by
    filter_upwards [hg.ae_hasDerivAt_integral] with x hx hmem
    exact hx hmem a (by simp)
  let H : ℝ → ℝ := (Ioo a b).indicator (fun x => u x - F x)
  have hFi : IntervalIntegrable F volume a b := hFac.continuousOn.intervalIntegrable
  have hHi : Integrable H volume := by
    rw [integrable_indicator_iff measurableSet_Ioo]
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mp (hu.sub hFi)
  have hHw : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ x, deriv ψ x * H x) = 0 := by
    intro ψ hψ hψc hψs
    have hdψ : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
    have hψac : AbsolutelyContinuousOnInterval ψ a b := by
      have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
      exact hψ1.contDiffOn.absolutelyContinuousOnInterval
    have hψa : ψ a = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => (lt_irrefl a) (hψs ht).1)
    have hψb : ψ b = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => (lt_irrefl b) (hψs ht).2)
    have hprod : Function.support (fun x => deriv ψ x * H x) ⊆ Ioc a b := by
      intro x hx
      by_contra hn
      have hnot : x ∉ Ioo a b := fun ht => hn ⟨ht.1, ht.2.le⟩
      have hHzero : H x = 0 := by simp only [H, indicator_of_notMem hnot]
      exact hx (by change deriv ψ x * H x = 0; rw [hHzero, mul_zero])
    rw [← intervalIntegral.integral_eq_integral_of_support_subset hprod]
    have heq : (∫ x in a..b, deriv ψ x * H x) =
        ∫ x in a..b, u x * deriv ψ x - F x * deriv ψ x := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab.le
      intro x hx
      simp only [H, indicator_of_mem hx]
      ring
    have hui := hu.mul_continuousOn hdψ.continuousOn
    have hFui := hFi.mul_continuousOn hdψ.continuousOn
    rw [heq, intervalIntegral.integral_sub hui hFui]
    have hibp := hFac.integral_mul_deriv_eq_deriv_mul hψac
    rw [hψa, hψb] at hibp
    simp only [mul_zero, sub_self, zero_sub] at hibp
    have hderiv : (∫ x in a..b, deriv F x * ψ x) =
        ∫ x in a..b, g x * ψ x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hFd] with x hx hmem
      rw [(hx (uIoc_subset_uIcc hmem)).deriv]
    rw [hderiv] at hibp
    linarith [hweak ψ hψ hψc hψs]
  obtain ⟨c, hc⟩ := weak_deriv_zero_constant_EX040 hab hHi.locallyIntegrable hHw
  let v : ℝ → ℝ := fun x => F x + c
  have hcac : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
    (show ContDiff ℝ 1 (fun _ : ℝ => c) from contDiff_const).contDiffOn.absolutelyContinuousOnInterval
  refine ⟨v, hFac.fun_add hcac, ?_, ?_⟩
  · filter_upwards [hc] with x hx hmem
    have hvalue := hx hmem
    simp only [H, indicator_of_mem hmem] at hvalue
    change u x = F x + c
    linarith
  · filter_upwards [hFd] with x hx hmem
    exact (hx hmem).add_const c

end DGPS.Examples
