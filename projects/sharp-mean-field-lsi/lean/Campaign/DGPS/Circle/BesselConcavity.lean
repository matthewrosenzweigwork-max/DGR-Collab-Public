import DGPS.Circle.BesselMonotonicity
/-!
# Strict Bessel concavity and the fold parameter (EX004)

With `g = I₁/I₀` (`besselRatio`), integration by parts gives `g' = 1 - g/t - g²` (valid at `t = 0`
too when `g/t` is read as the continuous extension `I₁Over/I₀`). Differentiating, `g'' = -g'/t +
g/t² - 2 g g'`; at a zero of `g''` its derivative is negative, and `g' < 1/2 = g'(0)` excludes an
initial stretch of positivity, so `g'' < 0` on `(0,∞)`.  Consequently `g'` is strictly decreasing
from `1/2` to `0`, `g'(s*) = 1/4` has a unique positive solution, `4g(s) - s` has its unique
maximum on `[0,∞)` at `s*`, and `h_c = 4g(s*) - s* ≥ 4g(1) - 1 > 1/2`
(`DGPS.Examples.strict_bessel_concavity_and_fold_parameter`).
-/

open MeasureTheory Real Filter Topology
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments DGPS.Circle.BesselMonotonicity

namespace DGPS.Circle.BesselConcavity

/-- second moment of the tilted measure, unnormalized -/
noncomputable def besselI2Moment (t : ℝ) : ℝ :=
  ∫ θ, angCos θ * Real.exp (t * angCos θ) * angCos θ ∂angHaar

theorem besselI2Moment_interval (t : ℝ) :
    besselI2Moment t = (2 * π)⁻¹ * ∫ s in (0 : ℝ)..2 * π,
      Real.cos s * Real.exp (t * Real.cos s) * Real.cos s := by
  unfold besselI2Moment
  apply integral_ang
  intro s
  simp [angCos, angMode_coe]

theorem besselI2Moment_ne (t : ℝ) (ht : t ≠ 0) :
    besselI2Moment t = besselI 0 t - besselI 1 t / t := by
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) (2 * π),
      HasDerivAt (fun s => Real.sin s * Real.exp (t * Real.cos s))
        (Real.cos s * Real.exp (t * Real.cos s) -
          t * (Real.exp (t * Real.cos s) - Real.cos s * Real.exp (t * Real.cos s) * Real.cos s)) s := by
    intro s _
    have h1 := (Real.hasDerivAt_sin s).mul (((Real.hasDerivAt_cos s).const_mul t).exp)
    refine h1.congr_deriv ?_
    have := Real.sin_sq_add_cos_sq s
    have e : Real.sin s ^ 2 = 1 - Real.cos s ^ 2 := by linarith
    have : Real.sin s * (Real.exp (t * Real.cos s) * (t * -Real.sin s))
        = -t * (Real.sin s ^ 2) * Real.exp (t * Real.cos s) := by ring
    rw [show Real.cos s * Real.exp (t * Real.cos s) + Real.sin s * (Real.exp (t * Real.cos s) * (t * -Real.sin s))
        = Real.cos s * Real.exp (t * Real.cos s) + (-t * (Real.sin s ^ 2) * Real.exp (t * Real.cos s)) by rw [← this]]
    rw [e]; ring
  have hint : IntervalIntegrable (fun s => Real.cos s * Real.exp (t * Real.cos s) -
          t * (Real.exp (t * Real.cos s) - Real.cos s * Real.exp (t * Real.cos s) * Real.cos s))
      MeasureTheory.volume 0 (2 * π) := by
    apply Continuous.intervalIntegrable; fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  simp only [Real.sin_zero, Real.sin_two_pi, zero_mul, sub_zero] at h
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)] at h
  have e0 := besselI_eq_interval 0 t
  have e1 := besselI_eq_interval 1 t
  have e2 := besselI2Moment_interval t
  simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one, Nat.cast_one, one_mul] at e0 e1
  have hpi : (2 * π) ≠ 0 := by positivity
  rw [e0, e1, e2]
  have c1 : ∫ s in (0:ℝ)..2 * π, Real.exp (t * Real.cos s) * Real.cos s
      = ∫ s in (0:ℝ)..2 * π, Real.cos s * Real.exp (t * Real.cos s) := by
    simp_rw [mul_comm]
  rw [c1]
  generalize (∫ s in (0:ℝ)..2 * π, Real.cos s * Real.exp (t * Real.cos s) * Real.cos s) = C at h ⊢
  generalize (∫ s in (0:ℝ)..2 * π, Real.cos s * Real.exp (t * Real.cos s)) = B at h ⊢
  generalize (∫ s in (0:ℝ)..2 * π, Real.exp (t * Real.cos s)) = A at h ⊢
  field_simp
  linarith

theorem besselI2Moment_eq (t : ℝ) : besselI2Moment t = besselI 0 t - besselI1Over t := by
  by_cases ht : t = 0
  · subst ht
    have h0 : besselI 0 0 = 1 := by simp [besselI, angMode_zero]
    have h2 : besselI2Moment 0 = 1 / 2 := by
      have := cosAvg_add_two 0
      rw [cosAvg_zero] at this
      unfold besselI2Moment
      simp only [zero_mul, Real.exp_zero, mul_one]
      have e : (fun θ => angCos θ * angCos θ) = fun θ => angCos θ ^ 2 := by
        funext θ; ring
      rw [e]
      have : cosAvg 2 = 1 / 2 := by simpa using this
      exact this
    rw [h2, h0, besselI1Over_zero]; norm_num
  · rw [besselI2Moment_ne t ht, besselI1Over_of_ne t ht]

theorem continuous_besselI0 : Continuous (besselI 0) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_besselI_zero t).continuousAt

theorem continuous_besselRatio : Continuous besselRatio := by
  have h1 : Continuous (besselI 1) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_besselI 1 t).continuousAt
  exact h1.div continuous_besselI0 fun t => (besselI_zero_pos t).ne'

/-- `g'`, in the form `1 - (I₁/t)/I₀ - g²` (continuous at `0`, value `1/2` there) -/
noncomputable def ratioDeriv (t : ℝ) : ℝ :=
  1 - besselI1Over t / besselI 0 t - besselRatio t ^ 2

/-- `g''` for `t ≠ 0` -/
noncomputable def ratioDeriv2 (t : ℝ) : ℝ :=
  -ratioDeriv t / t + besselRatio t / t ^ 2 - 2 * besselRatio t * ratioDeriv t

theorem hasDerivAt_ratio (t : ℝ) : HasDerivAt besselRatio (ratioDeriv t) t := by
  refine (hasDerivAt_besselRatio t).congr_deriv ?_
  have hE := (besselI_zero_pos t).ne'
  have e := besselI2Moment_eq t
  unfold besselI2Moment at e
  rw [e]
  unfold ratioDeriv besselRatio
  field_simp

theorem deriv_ratio (t : ℝ) : deriv besselRatio t = ratioDeriv t := (hasDerivAt_ratio t).deriv

theorem continuous_ratioDeriv : Continuous ratioDeriv := by
  unfold ratioDeriv
  have := continuous_besselI1Over
  have h0 := continuous_besselI0
  have hg := continuous_besselRatio
  refine Continuous.sub (Continuous.sub continuous_const (this.div h0 fun t => (besselI_zero_pos t).ne')) (hg.pow 2)

theorem ratio_zero : besselRatio 0 = 0 := by
  have := besselRatio_neg 0
  simp only [neg_zero] at this
  linarith

theorem ratioDeriv_zero : ratioDeriv 0 = 1 / 2 := by
  have h0 : besselI 0 0 = 1 := by simp [besselI, angMode_zero]
  unfold ratioDeriv
  rw [besselI1Over_zero, h0, ratio_zero]; norm_num

theorem ratio_div_eq (t : ℝ) (ht : t ≠ 0) : besselRatio t / t = besselI1Over t / besselI 0 t := by
  rw [besselI1Over_of_ne t ht]
  unfold besselRatio
  field_simp

theorem hasDerivAt_ratioDeriv (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt ratioDeriv (ratioDeriv2 t) t := by
  have hg := hasDerivAt_ratio t
  have h2 : HasDerivAt (fun x => 1 - besselRatio x / x - besselRatio x ^ 2)
      (-((ratioDeriv t * t - besselRatio t * 1) / t ^ 2) - 2 * besselRatio t * ratioDeriv t) t := by
    have := ((hasDerivAt_const t (1:ℝ)).sub (hg.div (hasDerivAt_id t) ht)).sub (hg.pow 2)
    refine this.congr_deriv ?_
    simp
  have heq : ratioDeriv =ᶠ[𝓝 t] fun x => 1 - besselRatio x / x - besselRatio x ^ 2 := by
    filter_upwards [isOpen_ne.mem_nhds ht] with x hx
    unfold ratioDeriv
    rw [ratio_div_eq x hx]
  refine (h2.congr_of_eventuallyEq heq).congr_deriv ?_
  unfold ratioDeriv2
  field_simp
  ring

/-- the derivative of `g''` -/
noncomputable def ratioDeriv3 (t : ℝ) : ℝ :=
  -ratioDeriv2 t / t + 2 * ratioDeriv t / t ^ 2 - 2 * besselRatio t / t ^ 3
    - 2 * ratioDeriv t ^ 2 - 2 * besselRatio t * ratioDeriv2 t

theorem hasDerivAt_ratioDeriv2 (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt ratioDeriv2 (ratioDeriv3 t) t := by
  have hg := hasDerivAt_ratio t
  have hV := hasDerivAt_ratioDeriv t ht
  have := ((hV.neg.div (hasDerivAt_id t) ht).add
    (hg.div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht))).sub
    ((hg.const_mul 2).mul hV)
  have hfun : ratioDeriv2 = (-ratioDeriv / id + besselRatio / id ^ 2
      - (fun y => 2 * besselRatio y) * ratioDeriv) := by
    funext x
    simp only [ratioDeriv2, Pi.sub_apply, Pi.add_apply, Pi.div_apply, Pi.neg_apply, Pi.pow_apply,
      Pi.mul_apply, id]
  rw [hfun]
  refine this.congr_deriv ?_
  simp only [ratioDeriv3, id, Pi.neg_apply, Pi.pow_apply]
  field_simp
  ring

theorem ratioDeriv_lt_div (t : ℝ) (ht : 0 < t) : ratioDeriv t < besselRatio t / t := by
  have := (DGPS.Examples.strict_bessel_ratio_inequalities.1 t ht).2.1
  rwa [deriv_ratio] at this

theorem ratioDeriv_lt_half (t : ℝ) (ht : 0 < t) : ratioDeriv t < 1 / 2 :=
  (ratioDeriv_lt_div t ht).trans (ratio_lt_half t ht)

theorem ratioDeriv_pos (t : ℝ) (ht : 0 < t) : 0 < ratioDeriv t := by
  have := (DGPS.Examples.strict_bessel_ratio_inequalities.1 t ht).1
  rwa [deriv_ratio] at this

theorem ratioDeriv3_neg_of_zero (t : ℝ) (ht : 0 < t) (h0 : ratioDeriv2 t = 0) :
    ratioDeriv3 t < 0 := by
  unfold ratioDeriv3
  rw [h0]
  have h1 := ratioDeriv_lt_div t ht
  have h2 : ratioDeriv t / t ^ 2 < besselRatio t / t / t ^ 2 := by gcongr
  have h3 : 2 * ratioDeriv t / t ^ 2 - 2 * besselRatio t / t ^ 3
      = 2 * (ratioDeriv t / t ^ 2 - besselRatio t / t / t ^ 2) := by
    field_simp
  have h4 : 0 ≤ ratioDeriv t ^ 2 := sq_nonneg _
  simp only [neg_zero, zero_div, mul_zero, zero_add, sub_zero]
  linarith

theorem ratioDeriv2_neg (t : ℝ) (ht : 0 < t) : ratioDeriv2 t < 0 := by
  have hcont : ∀ x, 0 < x → ContinuousAt ratioDeriv2 x := fun x hx =>
    (hasDerivAt_ratioDeriv2 x hx.ne').continuousAt
  -- step 1: `g''` is negative somewhere in every initial interval
  have step1 : ∀ a, 0 < a → ∃ s, 0 < s ∧ s < a ∧ ratioDeriv2 s < 0 := by
    intro a ha
    by_contra hcon
    push Not at hcon
    have hmono : MonotoneOn ratioDeriv (Set.Icc 0 a) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 a) continuous_ratioDeriv.continuousOn ?_ ?_
      · intro x hx
        rw [interior_Icc] at hx
        exact (hasDerivAt_ratioDeriv x hx.1.ne').differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        rw [(hasDerivAt_ratioDeriv x hx.1.ne').deriv]
        exact hcon x hx.1 hx.2
    have := hmono (Set.left_mem_Icc.mpr ha.le) (Set.right_mem_Icc.mpr ha.le) ha.le
    rw [ratioDeriv_zero] at this
    linarith [ratioDeriv_lt_half a ha]
  by_contra hne
  push Not at hne
  obtain ⟨s, hs0, hst, hsneg⟩ := step1 t ht
  set A : Set ℝ := {x | x ∈ Set.Icc s t ∧ 0 ≤ ratioDeriv2 x} with hAdef
  have hcontOn : ContinuousOn ratioDeriv2 (Set.Icc s t) := fun x hx =>
    (hcont x (hs0.trans_le hx.1)).continuousWithinAt
  have hAc : IsClosed A := by
    have := hcontOn.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Ici (a := (0:ℝ)))
    exact this
  have hAne : A.Nonempty := ⟨t, ⟨⟨hst.le, le_rfl⟩, hne⟩⟩
  have hAb : BddBelow A := ⟨s, fun x hx => hx.1.1⟩
  have hcA := hAc.csInf_mem hAne hAb
  set c := sInf A with hc
  have hsc : s < c := by
    rcases hcA.1.1.eq_or_lt with h | h
    · exfalso
      have : 0 ≤ ratioDeriv2 s := by
        have := hcA.2
        rwa [← h] at this
      linarith
    · exact h
  have hct : c ≤ t := hcA.1.2
  have hneg : ∀ x, s ≤ x → x < c → ratioDeriv2 x < 0 := by
    intro x hsx hxc
    by_contra hx
    push Not at hx
    have : x ∈ A := ⟨⟨hsx, hxc.le.trans hct⟩, hx⟩
    exact absurd (csInf_le hAb this) (not_le.mpr hxc)
  have hc0 : 0 < c := hs0.trans hsc
  have hWc : ratioDeriv2 c = 0 := by
    refine le_antisymm ?_ hcA.2
    have hlim : Tendsto ratioDeriv2 (𝓝[<] c) (𝓝 (ratioDeriv2 c)) :=
      (hcont c hc0).tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT hsc] with x hx using (hneg x hx.1.le hx.2).le
  have hd := hasDerivAt_ratioDeriv2 c hc0.ne'
  have hd3 := ratioDeriv3_neg_of_zero c hc0 hWc
  have hsl := hasDerivAt_iff_tendsto_slope.mp hd
  have hsl' : Tendsto (slope ratioDeriv2 c) (𝓝[<] c) (𝓝 (ratioDeriv3 c)) :=
    hsl.mono_left (nhdsWithin_mono _ fun x hx => ne_of_lt hx)
  have hev : ∀ᶠ x in 𝓝[<] c, slope ratioDeriv2 c x < 0 := hsl'.eventually (gt_mem_nhds hd3)
  obtain ⟨x, hx1, hx2⟩ := (hev.and (Ioo_mem_nhdsLT hsc)).exists
  have hxc : x < c := hx2.2
  rw [slope_def_field, hWc, sub_zero] at hx1
  have : 0 < ratioDeriv2 x := by
    have hxc' : x - c < 0 := sub_neg.mpr hxc
    by_contra hh
    push Not at hh
    have : 0 ≤ ratioDeriv2 x / (x - c) := div_nonneg_of_nonpos hh hxc'.le
    linarith
  linarith [hneg x hx2.1.le hxc]

theorem strictAntiOn_ratioDeriv : StrictAntiOn ratioDeriv (Set.Ici 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici 0) continuous_ratioDeriv.continuousOn ?_
  intro x hx
  rw [interior_Ici] at hx
  rw [(hasDerivAt_ratioDeriv x (ne_of_gt hx)).deriv]
  exact ratioDeriv2_neg x hx

theorem tendsto_ratioDeriv : Tendsto ratioDeriv atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_ratio ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with t ht using (ratioDeriv_pos t ht).le
  · filter_upwards [eventually_gt_atTop 0] with t ht using (ratioDeriv_lt_div t ht).le

theorem besselI0_one_lt : besselI 0 1 < 4 / 3 := by
  have h := hasSum_besselI_zero 1
  have hg : HasSum (fun j : ℕ => ((1:ℝ) / 4) ^ j) (4 / 3) := by
    have := hasSum_geometric_of_lt_one (r := (1:ℝ) / 4) (by norm_num) (by norm_num)
    convert this using 1; norm_num
  refine hasSum_lt (f := fun j : ℕ => ((1:ℝ) ^ 2 / 4) ^ j / (j.factorial : ℝ) ^ 2)
    (g := fun j : ℕ => ((1:ℝ) / 4) ^ j) (i := 2) (fun j => ?_) ?_ h hg
  · have h1 : (1:ℝ) ≤ (j.factorial : ℝ) ^ 2 := by
      have : (1:ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero j)
      nlinarith
    have h0 : (0:ℝ) ≤ ((1:ℝ) / 4) ^ j := by positivity
    simp only [one_pow]
    exact div_le_self h0 h1
  · norm_num [Nat.factorial]

theorem besselI1Over_one_gt : 1 / 2 < besselI1Over 1 := by
  have h := hasSum_besselI1Over 1
  have hg : HasSum (fun j : ℕ => if j = 0 then (1:ℝ) / 2 else 0) (1 / 2) := by
    simpa using hasSum_ite_eq 0 ((1:ℝ) / 2)
  refine hasSum_lt (i := 1) (fun j => ?_) ?_ hg h
  · by_cases hj : j = 0
    · subst hj; norm_num
    · simp only [hj, ↓reduceIte]; positivity
  · norm_num [Nat.factorial]

theorem four_ratio_one_sub_gt : 1 / 2 < 4 * besselRatio 1 - 1 := by
  have h0 := besselI0_one_lt
  have h0p := besselI_zero_pos 1
  have h1 : besselI 1 1 = besselI1Over 1 := by
    have := besselI1Over_of_ne 1 one_ne_zero
    simpa using this.symm
  have h2 := besselI1Over_one_gt
  have : 3 / 8 < besselRatio 1 := by
    unfold besselRatio
    rw [lt_div_iff₀ h0p, h1]
    nlinarith
  linarith

theorem foldFun_max {s : ℝ} (hs : 0 < s) (h : ratioDeriv s = 1 / 4) :
    ∀ x, 0 ≤ x → x ≠ s → 4 * besselRatio x - x < 4 * besselRatio s - s := by
  have hd : ∀ x, HasDerivAt (fun y => 4 * besselRatio y - y) (4 * ratioDeriv x - 1) x := by
    intro x
    exact (((hasDerivAt_ratio x).const_mul 4).sub (hasDerivAt_id' x)).congr_deriv (by ring)
  have hc : Continuous fun y => 4 * besselRatio y - y :=
    (continuous_const.mul continuous_besselRatio).sub continuous_id
  have hmono : StrictMonoOn (fun y => 4 * besselRatio y - y) (Set.Icc 0 s) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 s) hc.continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    have := strictAntiOn_ratioDeriv (Set.mem_Ici.mpr hx.1.le) (Set.mem_Ici.mpr hs.le) hx.2
    linarith
  have hanti : StrictAntiOn (fun y => 4 * besselRatio y - y) (Set.Ici s) := by
    refine strictAntiOn_of_deriv_neg (convex_Ici s) hc.continuousOn ?_
    intro x hx
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    have := strictAntiOn_ratioDeriv (Set.mem_Ici.mpr hs.le) (Set.mem_Ici.mpr (hs.le.trans hx.le)) hx
    linarith
  intro x hx0 hxs
  rcases lt_or_gt_of_ne hxs with hlt | hgt
  · exact hmono ⟨hx0, hlt.le⟩ ⟨hs.le, le_rfl⟩ hlt
  · exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hgt.le) hgt

end DGPS.Circle.BesselConcavity

namespace DGPS.Examples

open DGPS.Circle.BesselMoments DGPS.Circle.BesselConcavity

/-- EX004: strict Bessel concavity and the fold parameter.  With `g = I₁/I₀` (`besselRatio`):
on `(0,∞)`, `g'` is differentiable with `g'' < 0`; `g'` is continuous and strictly decreasing on
`[0,∞)`, equals `1/2` at `0` and tends to `0` at `∞`; the equation `g'(s) = 1/4` has exactly one
positive solution `s*`; and for it, `s*` is the unique maximizer of `4 g(s) - s` on `s ≥ 0`
(so `h_c = 4 g(s*) - s*` is the unique maximum value), and `h_c > 1/2`. -/
theorem strict_bessel_concavity_and_fold_parameter :
    (∀ t : ℝ, 0 < t → ∃ d : ℝ, HasDerivAt (deriv besselRatio) d t ∧ d < 0) ∧
    (ContinuousOn (deriv besselRatio) (Set.Ici 0) ∧ deriv besselRatio 0 = 1 / 2 ∧
      StrictAntiOn (deriv besselRatio) (Set.Ici 0) ∧
      Filter.Tendsto (deriv besselRatio) Filter.atTop (nhds 0)) ∧
    (∃! s : ℝ, 0 < s ∧ deriv besselRatio s = 1 / 4) ∧
    (∀ s : ℝ, 0 < s → deriv besselRatio s = 1 / 4 →
      (∀ x : ℝ, 0 ≤ x → x ≠ s → 4 * besselRatio x - x < 4 * besselRatio s - s) ∧
        1 / 2 < 4 * besselRatio s - s) := by
  have hder : deriv besselRatio = ratioDeriv := funext deriv_ratio
  rw [hder]
  refine ⟨fun t ht => ⟨ratioDeriv2 t, ?_, ratioDeriv2_neg t ht⟩,
    ⟨continuous_ratioDeriv.continuousOn, ratioDeriv_zero, strictAntiOn_ratioDeriv,
      tendsto_ratioDeriv⟩, ?_, ?_⟩
  · exact hasDerivAt_ratioDeriv t ht.ne'
  · -- existence by the intermediate value theorem, uniqueness by strict monotonicity
    obtain ⟨b, hb⟩ := (tendsto_ratioDeriv.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1 / 4))).and
      (Filter.eventually_gt_atTop 0) |>.exists
    have hivt := intermediate_value_Icc' (le_of_lt hb.2) continuous_ratioDeriv.continuousOn
    have hmem : (1 / 4 : ℝ) ∈ Set.Icc (ratioDeriv b) (ratioDeriv 0) := by
      rw [ratioDeriv_zero]; exact ⟨hb.1.le, by norm_num⟩
    obtain ⟨s, hs, hsv⟩ := hivt hmem
    have hs0 : 0 < s := by
      rcases hs.1.eq_or_lt with h | h
      · rw [← h, ratioDeriv_zero] at hsv; norm_num at hsv
      · exact h
    refine ⟨s, ⟨hs0, hsv⟩, ?_⟩
    rintro y ⟨hy0, hyv⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := strictAntiOn_ratioDeriv (Set.mem_Ici.mpr hy0.le) (Set.mem_Ici.mpr hs0.le) hlt
      linarith
    · have := strictAntiOn_ratioDeriv (Set.mem_Ici.mpr hs0.le) (Set.mem_Ici.mpr hy0.le) hgt
      linarith
  · intro s hs hsv
    refine ⟨foldFun_max hs hsv, ?_⟩
    by_cases h1s : (1:ℝ) = s
    · rw [← h1s]; exact four_ratio_one_sub_gt
    · exact four_ratio_one_sub_gt.trans (foldFun_max hs hsv 1 zero_le_one h1s)

end DGPS.Examples
