import DGPS.Examples.EngineeredRankOneEndpoints
import DGPS.Examples.EngineeredRankOneEstimates

open MeasureTheory Real Set Filter Topology
open scoped ContDiff

/-!
# Engineered drift and ground potential (EX037)

On the lifted angle `t : ℝ` (as in EX031), `b = (log q_h)' = driftB h` is the derivative of
`t ↦ logq h (t : Real.Angle)`, and `Vcal = b² / 4 + b' / 2` is `groundPot h`. We prove
`b(t) = -(h + R_h'(U)) sin t` with `U = 1 - cos t`, and an absolute `C` with `|b'| ≤ C h` and
`Vcal ≥ h² sin² t / 4 - C h` for all `h ≥ 2` and all `t`.

Route: `R_h' = integrand h` satisfies `R_h'(u) u (2-u) = N_h(u)` on all of `ℝ` (EX031 removable
endpoints). Differentiating, and using `u (2-u) = sin² t` and `2 - 2u = 2 cos t` for `u = 1 - cos t`,
gives `b' = -N_h'(U) + (R_h'(U) - h) cos t`, in which the endpoint singularities have cancelled.
Then `0 ≤ R_h' ≤ a_h h` on `[0,2]` (from `N_h ≤ min((a_h h - 1) u, 2 - u)`) and `a_h ≤ 4` give
`|b'| ≤ 8 h`, while `R_h' ≥ 0` gives `b² ≥ h² sin²`.
Main output: `DGPS.Examples.engineered_drift_and_ground_potential`.
-/

namespace DGPS.Examples.EngineeredRankOne

/-- The drift `b = (log q_h)'` on the lifted angle. -/
noncomputable def driftB (h t : ℝ) : ℝ := deriv (fun s : ℝ => logq h (s : Real.Angle)) t

/-- The ground potential `Vcal = b² / 4 + b' / 2`. -/
noncomputable def groundPot (h t : ℝ) : ℝ := driftB h t ^ 2 / 4 + deriv (driftB h) t / 2

theorem drift_Uang (t : ℝ) : Uang (t : Real.Angle) = 1 - Real.cos t := by
  unfold Uang; rw [Real.Angle.cos_coe]

theorem aH_gt_two (h : ℝ) (hh : 0 < h) : 2 < aH h := by
  have h1 := aH_mul h hh
  have h2 : exp (-h * 2) < 1 := by rw [exp_lt_one_iff]; linarith
  have h3 : 0 < exp (-h * 2) := exp_pos _
  by_contra hc
  rw [not_lt] at hc
  have h4 := aH_pos h hh
  nlinarith

theorem aH_le_four (h : ℝ) (hh : 2 ≤ h) : aH h ≤ 4 := by
  have hp : 0 < h := by linarith
  have h1 := aH_mul h hp
  have h2 : exp (-h * 2) ≤ 1 / 2 := by
    have h5 : (4:ℝ) + 1 ≤ exp 4 := by simpa using Real.add_one_le_exp (4:ℝ)
    have h6 : exp 4 ≤ exp (h * 2) := Real.exp_le_exp.2 (by linarith)
    have h7 : exp (-h * 2) * exp (h * 2) = 1 := by rw [← Real.exp_add]; simp
    have h8 := exp_pos (-h * 2)
    nlinarith
  have h4 := aH_pos h hp
  nlinarith

/-- `R_h'(u) u (2-u) = N_h(u)` on all of `ℝ`. -/
theorem integrand_mul (h : ℝ) (hh : 0 < h) (u : ℝ) :
    integrand h u * (u * (2 - u)) = numer h u := by
  by_cases h0 : u = 0
  · subst h0; simp [numer_zero]
  by_cases h2 : u = 2
  · subst h2; simp [numer_two h hh]
  rw [integrand_of_ne h h0 h2]
  have : u * (2 - u) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.2 (Ne.symm h2))
  field_simp

/-- Differentiated form of `R_h'(u) u (2-u) = N_h(u)`. -/
theorem deriv_integrand_identity (h : ℝ) (hh : 0 < h) (u : ℝ) :
    deriv (integrand h) u * (u * (2 - u)) + integrand h u * (2 - 2 * u) =
      aH h * h * exp (-h * u) - 1 := by
  have hd : HasDerivAt (integrand h) (deriv (integrand h) u) u :=
    (((contDiff_integrand h hh).differentiable (by simp)) u).hasDerivAt
  have hp : HasDerivAt (fun v : ℝ => v * (2 - v)) (1 * (2 - u) + u * (0 - 1)) u :=
    (hasDerivAt_id u).mul ((hasDerivAt_const u (2:ℝ)).sub (hasDerivAt_id u))
  have h1 : HasDerivAt (fun v : ℝ => integrand h v * (v * (2 - v)))
      (deriv (integrand h) u * (u * (2 - u)) + integrand h u * (1 * (2 - u) + u * (0 - 1))) u :=
    hd.mul hp
  have e : (fun v : ℝ => integrand h v * (v * (2 - v))) = numer h := funext (integrand_mul h hh)
  rw [e] at h1
  have := h1.unique (hasDerivAt_numer h u)
  linarith

theorem numer_le_two_sub (h : ℝ) (hh : 0 < h) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 2) :
    numer h u ≤ 2 - u := by
  have h1 := aH_mul h hh
  have h2 : exp (-h * 2) ≤ exp (-h * u) := Real.exp_le_exp.2 (by nlinarith [hu.2])
  have h3 := aH_pos h hh
  unfold numer
  nlinarith

theorem numer_le_lin (h : ℝ) (hh : 0 < h) (u : ℝ) :
    numer h u ≤ (aH h * h - 1) * u := by
  have h1 : 1 - exp (-h * u) ≤ h * u := by
    have := Real.add_one_le_exp (-h * u)
    nlinarith
  have h3 := aH_pos h hh
  unfold numer
  nlinarith

theorem integrand_le (h : ℝ) (hh : 2 ≤ h) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 2) :
    integrand h u ≤ aH h * h := by
  have hp : 0 < h := by linarith
  have ha := aH_gt_two h hp
  have hah : 2 * 2 ≤ aH h * h := by nlinarith
  have hcl : IsClosed {v : ℝ | integrand h v ≤ aH h * h} :=
    isClosed_le (contDiff_integrand h hp).continuous continuous_const
  have hsub : Ioo (0:ℝ) 2 ⊆ {v : ℝ | integrand h v ≤ aH h * h} := by
    intro v hv
    have hv' : v ∈ Icc (0:ℝ) 2 := ⟨hv.1.le, hv.2.le⟩
    show integrand h v ≤ aH h * h
    have hpos : 0 < v * (2 - v) := mul_pos hv.1 (by linarith [hv.2])
    have key : numer h v ≤ aH h * h * (v * (2 - v)) := by
      have n1 := numer_le_two_sub h hp hv'
      have n2 := numer_le_lin h hp v
      rcases le_total v 1 with hv1 | hv1
      · nlinarith [hv.1]
      · nlinarith [hv.2]
    rw [integrand_of_ne h hv.1.ne' hv.2.ne, div_le_iff₀ hpos]
    exact key
  have := hcl.closure_subset_iff.2 hsub
  rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 2)] at this
  exact this hu

theorem hasDerivAt_logq_lift (h : ℝ) (hh : 0 < h) (t : ℝ) :
    HasDerivAt (fun s : ℝ => logq h (s : Real.Angle))
      (-(h + integrand h (1 - Real.cos t)) * Real.sin t) t := by
  have e : (fun s : ℝ => logq h (s : Real.Angle)) =
      fun s => -(h * (1 - Real.cos s)) - corr h (1 - Real.cos s) := by
    funext s; unfold logq; rw [drift_Uang]
  rw [e]
  have hU : HasDerivAt (fun s : ℝ => 1 - Real.cos s) (Real.sin t) t := by
    have := (Real.hasDerivAt_cos t).const_sub 1
    simpa using this
  have hc : HasDerivAt (corr h) (integrand h (1 - Real.cos t)) (1 - Real.cos t) :=
    (((contDiff_integrand h hh).continuous).integral_hasStrictDerivAt 0 _).hasDerivAt
  have hcU0 := hc.comp t hU
  have hcU : HasDerivAt (fun s : ℝ => corr h (1 - Real.cos s))
      (integrand h (1 - Real.cos t) * Real.sin t) t := hcU0
  have h1 : HasDerivAt (fun s : ℝ => -(h * (1 - Real.cos s)) - corr h (1 - Real.cos s))
      (-(h * Real.sin t) - integrand h (1 - Real.cos t) * Real.sin t) t :=
    (hU.const_mul h).neg.sub hcU
  exact h1.congr_deriv (by ring)

theorem driftB_eq (h : ℝ) (hh : 0 < h) (t : ℝ) :
    driftB h t = -(h + integrand h (1 - Real.cos t)) * Real.sin t :=
  (hasDerivAt_logq_lift h hh t).deriv

theorem deriv_driftB (h : ℝ) (hh : 0 < h) (t : ℝ) :
    deriv (driftB h) t =
      -(aH h * h * exp (-h * (1 - Real.cos t)) - 1) +
        (integrand h (1 - Real.cos t) - h) * Real.cos t := by
  have e : driftB h = fun s => -(h + integrand h (1 - Real.cos s)) * Real.sin s :=
    funext (driftB_eq h hh)
  have hU : HasDerivAt (fun s : ℝ => 1 - Real.cos s) (Real.sin t) t := by
    have := (Real.hasDerivAt_cos t).const_sub 1
    simpa using this
  have hI : HasDerivAt (integrand h) (deriv (integrand h) (1 - Real.cos t)) (1 - Real.cos t) :=
    (((contDiff_integrand h hh).differentiable (by simp)) _).hasDerivAt
  have hIU0 := hI.comp t hU
  have hIU : HasDerivAt (fun s : ℝ => integrand h (1 - Real.cos s))
      (deriv (integrand h) (1 - Real.cos t) * Real.sin t) t := hIU0
  have h1 : HasDerivAt (fun s : ℝ => -(h + integrand h (1 - Real.cos s)) * Real.sin s)
      (-(deriv (integrand h) (1 - Real.cos t) * Real.sin t) * Real.sin t +
        -(h + integrand h (1 - Real.cos t)) * Real.cos t) t :=
    ((hIU.const_add h).neg).mul (Real.hasDerivAt_sin t)
  rw [e, h1.deriv]
  have key := deriv_integrand_identity h hh (1 - Real.cos t)
  have hs : Real.sin t ^ 2 = (1 - Real.cos t) * (2 - (1 - Real.cos t)) := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hs2 : 2 - 2 * (1 - Real.cos t) = 2 * Real.cos t := by ring
  rw [← hs, hs2] at key
  linear_combination (-1 : ℝ) * key

end DGPS.Examples.EngineeredRankOne

namespace DGPS.Examples

open DGPS.Examples.EngineeredRankOne

/-- EX037: on the lifted angle, `b = (log q_h)' = -(h + R_h'(U)) sin t`; there is an absolute `C`
with `|b'| ≤ C h` and `Vcal = b²/4 + b'/2 ≥ h² sin² t / 4 - C h`, for all `h ≥ 2` and `t`. -/
theorem engineered_drift_and_ground_potential :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 2 ≤ h → ∀ t : ℝ,
      driftB h t = -(h + deriv (corr h) (1 - Real.cos t)) * Real.sin t ∧
      |deriv (driftB h) t| ≤ C * h ∧
      h ^ 2 * Real.sin t ^ 2 / 4 - C * h ≤ groundPot h t := by
  refine ⟨8, by norm_num, fun h hh t => ?_⟩
  have hp : 0 < h := by linarith
  have hu : (1 - Real.cos t) ∈ Icc (0:ℝ) 2 :=
    ⟨by linarith [Real.cos_le_one t], by linarith [Real.neg_one_le_cos t]⟩
  have hI0 := integrand_nonneg h hp hu
  have hI1 := integrand_le h hh hu
  have ha4 := aH_le_four h hh
  have ha2 := aH_gt_two h hp
  have hah : 4 ≤ aH h * h := by nlinarith
  have hah4 : aH h * h ≤ 4 * h := by nlinarith
  have hexp1 : exp (-h * (1 - Real.cos t)) ≤ 1 :=
    exp_le_one_iff.2 (by nlinarith [(hu.1 : (0:ℝ) ≤ 1 - Real.cos t)])
  have hexp0 := exp_pos (-h * (1 - Real.cos t))
  have hcos1 := Real.cos_le_one t
  have hcos2 := Real.neg_one_le_cos t
  have hb' := deriv_driftB h hp t
  have hN1 : aH h * h * exp (-h * (1 - Real.cos t)) ≤ aH h * h := by nlinarith
  have hN0 : 0 ≤ aH h * h * exp (-h * (1 - Real.cos t)) := by positivity
  have hbd : |deriv (driftB h) t| ≤ 8 * h := by
    rw [hb', abs_le]
    have hc1 : |Real.cos t| ≤ 1 := abs_le.2 ⟨hcos2, hcos1⟩
    have hd : |integrand h (1 - Real.cos t) - h| ≤ 4 * h := by
      rw [abs_le]; constructor <;> nlinarith
    have : |(integrand h (1 - Real.cos t) - h) * Real.cos t| ≤ 4 * h := by
      rw [abs_mul]
      calc |integrand h (1 - Real.cos t) - h| * |Real.cos t|
          ≤ (4 * h) * 1 := mul_le_mul hd hc1 (abs_nonneg _) (by linarith)
        _ = 4 * h := by ring
    rw [abs_le] at this
    constructor <;> nlinarith [this.1, this.2]
  have hder : deriv (corr h) (1 - Real.cos t) = integrand h (1 - Real.cos t) := deriv_corr h hp _
  refine ⟨?_, hbd, ?_⟩
  · rw [driftB_eq h hp t, hder]
  · unfold groundPot
    rw [driftB_eq h hp t]
    have hsq : h ^ 2 * Real.sin t ^ 2 ≤ ((-(h + integrand h (1 - Real.cos t)) * Real.sin t)) ^ 2 := by
      have : h ^ 2 ≤ (h + integrand h (1 - Real.cos t)) ^ 2 := by nlinarith
      calc h ^ 2 * Real.sin t ^ 2 ≤ (h + integrand h (1 - Real.cos t)) ^ 2 * Real.sin t ^ 2 :=
            mul_le_mul_of_nonneg_right this (sq_nonneg _)
        _ = _ := by ring
    have := (abs_le.1 hbd).1
    linarith

end DGPS.Examples
