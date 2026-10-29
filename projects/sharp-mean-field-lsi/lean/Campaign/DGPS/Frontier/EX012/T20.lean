import DGPS.Frontier.EX012.T16
import DGPS.Frontier.EX012.T17
import DGPS.Frontier.EX012.T18
import DGPS.Frontier.EX012.T19
import DGPS.Frontier.EX012.T36

/-!
# EX012.20: Stationarity implies the pointwise Euler identity

Task id: EX012.20 (node EX012, leaf formalization).
Title: Stationarity implies the pointwise Euler identity.

For an admissible `u` (`IsAdmSmooth_EX01236`), put `E = E_h(u²)` (`groundE_EX01236 h u`) and
`T = -4 D²u + τ s₁² u - 4 u log u` with `τ = h²`, `D = (2π)⁻¹ ∂ₓ`, `s₁(x) = sin(2πx)`. For every
smooth one-periodic `ξ`, the derivative at `t = 0` of `t ↦ E_h(u_t²)` along the admissible curve
`u_t` of EX012.16 equals `2 ∫₀¹ (T - E u) ξ`. If `u²` minimizes the ground functional among the
admissible smooth densities, then `T = E u` pointwise.

## Provides

* `DGPS.Frontier.EX012.ex012_20_stationarity_implies_pointwise_euler_identity`: for admissible `u`
  and `h : ℝ`, (i) for all smooth one-periodic `ξ`, `HasDerivAt (fun t => groundE_EX01236 h
  (ucurve_EX01216 u ξ t)) (2 * ∫ x in 0..1, (T x - E * u x) * ξ x) 0`; (ii) if
  `groundE_EX01236 h u ≤ groundE_EX01236 h v` for every admissible `v`, then `T x = E * u x` for all `x`.
* `DGPS.Frontier.EX012.ex012_20_stationarity_implies_pointwise_euler_identity_first_variation`:
  part (i) on its own.
* `DGPS.Frontier.EX012.ex012_20_stationarity_implies_pointwise_euler_identity_of_stationary`:
  part (ii) under the weaker hypothesis that the derivative at `0` of `t ↦ E_h(u_t²)` vanishes for
  every smooth one-periodic `ξ`.
* `DGPS.Frontier.EX012.ex012_20_stationarity_implies_pointwise_euler_identity_of_local_min`:
  part (ii) under the hypothesis that `t ↦ E_h(u_t²)` has a local minimum at `0` for every smooth
  one-periodic `ξ`.
* `DGPS.Frontier.EX012.ex012_20_stationarity_implies_pointwise_euler_identity_ground`: part (ii)
  with minimality stated for the named functional `ex010_ground h` over all `AbsoluteDensity 1`.
* `DGPS.Frontier.EX012.euler_T_EX01220`: the function `T`.
* Helpers (suffix `_EX01220`): the extrema lemma, linearity lemmas for interval integrals of
  continuous functions, the formula for `∫ F η`, regularity of `T`, and the vanishing lemma for a
  continuous periodic function with `∫ g² = 0`.

## R5 notes

* `τ = h²` as in the node preamble; `T` is `euler_T_EX01220 h u x = -4 * D (D u) x +
  h ^ 2 * sin (2π x) ^ 2 * u x - 4 * u x * log (u x)` with `D = angD_EX01217`.
* "The derivative along 16" is read as the `HasDerivAt` at `t = 0` of
  `t ↦ groundE_EX01236 h (ucurve_EX01216 u ξ t)` (the displayed `E_h`, with the curve `u_t` of
  EX012.16, which is admissible for `|t| < δ`; the function is defined for every `t`).
* Hypotheses on `u` and `ξ` are those of EX012.16/18/19: `u` admissible, `ξ` smooth
  (`ContDiff ℝ ∞`) and one-periodic. The constants `m = min u`, `M = max u`, `Q = ‖ξ‖∞` required by
  EX012.18 are not assumed: they exist by compactness of the period, and are obtained inside the proof.
* "`u²` is minimizing" is read as: `E_h(u²) ≤ E_h(v²)` for every admissible `v`
  (`IsAdmSmooth_EX01236 v`), i.e. `u²` minimizes among positive smooth normalized densities, the
  class in which EX012.16 produces competitors. The `_ground` variant states minimality for
  `ex010_ground h` over all `AbsoluteDensity 1` (a stronger hypothesis, hence a weaker theorem),
  converted by `ground_smoothDensity_EX01236`. Only a local minimum along each curve is used
  (`_of_local_min`), so any local-minimum reading of the specification is covered by that variant.
* The test function is `ξ = T - E u`; its smoothness and periodicity are proved (it uses
  `u > 0` for `log u`, and EX012.17's smoothness and periodicity lemmas for `D² u`).
* Nonnegative continuous function with zero integral: proved from
  `intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae` and `Measure.eqOn_Ioc_of_ae_eq`
  (open-positivity of Lebesgue measure), then extended to `ℝ` by periodicity.
* Integration by parts is EX012.17 (`∫ D u D η = -∫ D²u η`, `η = ξ - u ∫ uξ` is smooth and
  one-periodic); the entropy derivative is EX012.18 and the kinetic/potential derivative EX012.19.
  The identities `∫ T u = E` and `∫ u η = 0` of the specification's proof appear in the form
  `∫ (2T - 4u) u = 2E - 4`, which combines both.
-/

open MeasureTheory
open scoped ContDiff

namespace DGPS.Frontier.EX012

/-- `T = -4 D²u + τ s₁² u - 4 u log u` with `τ = h²`. -/
noncomputable def euler_T_EX01220 (h : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  -4 * angD_EX01217 (angD_EX01217 u) x + h ^ 2 * Real.sin (2 * Real.pi * x) ^ 2 * u x
    - 4 * u x * Real.log (u x)

theorem exists_extrema_EX01220 {u ξ : ℝ → ℝ} (hu : IsAdmSmooth_EX01236 u)
    (hξ : ContDiff ℝ ∞ ξ) (hξp : Function.Periodic ξ 1) :
    ∃ m M Q : ℝ, IsLeast (Set.range u) m ∧ IsGreatest (Set.range u) M ∧
      IsLUB (Set.range fun x => |ξ x|) Q := by
  have hrange : ∀ f : ℝ → ℝ, Continuous f → Function.Periodic f 1 → IsCompact (Set.range f) := by
    intro f hc hp
    have : Set.range f = f '' Set.Icc 0 1 := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        obtain ⟨z, hz, hfz⟩ := hp.exists_mem_Ico₀ one_pos x
        exact ⟨z, ⟨hz.1, hz.2.le⟩, hfz.symm⟩
      · rintro ⟨x, -, rfl⟩
        exact ⟨x, rfl⟩
    rw [this]
    exact isCompact_Icc.image hc
  obtain ⟨m, hm⟩ := (hrange u hu.smooth.continuous hu.periodic).exists_isLeast
    (Set.range_nonempty u)
  obtain ⟨M, hM⟩ := (hrange u hu.smooth.continuous hu.periodic).exists_isGreatest
    (Set.range_nonempty u)
  have hξabs : Function.Periodic (fun x => |ξ x|) 1 := fun x => by
    show |ξ (x + 1)| = |ξ x|
    rw [hξp x]
  obtain ⟨Q, hQ⟩ := (hrange (fun x => |ξ x|) hξ.continuous.abs hξabs).exists_isGreatest
    (Set.range_nonempty _)
  exact ⟨m, M, Q, hm, hM, hQ.isLUB⟩

theorem integral_two_EX01220 {f₁ f₂ : ℝ → ℝ} (c₁ c₂ : ℝ) (h₁ : Continuous f₁)
    (h₂ : Continuous f₂) :
    ∫ x in (0:ℝ)..1, (c₁ * f₁ x + c₂ * f₂ x)
      = c₁ * (∫ x in (0:ℝ)..1, f₁ x) + c₂ * ∫ x in (0:ℝ)..1, f₂ x := by
  have i₁ : IntervalIntegrable (fun x => c₁ * f₁ x) MeasureTheory.volume 0 1 :=
    (continuous_const.mul h₁).intervalIntegrable _ _
  have i₂ : IntervalIntegrable (fun x => c₂ * f₂ x) MeasureTheory.volume 0 1 :=
    (continuous_const.mul h₂).intervalIntegrable _ _
  rw [intervalIntegral.integral_add i₁ i₂, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

theorem integral_four_EX01220 {f₁ f₂ f₃ f₄ : ℝ → ℝ} (c₁ c₂ c₃ c₄ : ℝ) (h₁ : Continuous f₁)
    (h₂ : Continuous f₂) (h₃ : Continuous f₃) (h₄ : Continuous f₄) :
    ∫ x in (0:ℝ)..1, (c₁ * f₁ x + c₂ * f₂ x + c₃ * f₃ x + c₄ * f₄ x)
      = c₁ * (∫ x in (0:ℝ)..1, f₁ x) + c₂ * (∫ x in (0:ℝ)..1, f₂ x)
        + c₃ * (∫ x in (0:ℝ)..1, f₃ x) + c₄ * ∫ x in (0:ℝ)..1, f₄ x := by
  have i₁ : IntervalIntegrable (fun x => c₁ * f₁ x) MeasureTheory.volume 0 1 :=
    (continuous_const.mul h₁).intervalIntegrable _ _
  have i₂ : IntervalIntegrable (fun x => c₂ * f₂ x) MeasureTheory.volume 0 1 :=
    (continuous_const.mul h₂).intervalIntegrable _ _
  have i₃ : IntervalIntegrable (fun x => c₃ * f₃ x) MeasureTheory.volume 0 1 :=
    (continuous_const.mul h₃).intervalIntegrable _ _
  have i₄ : IntervalIntegrable (fun x => c₄ * f₄ x) MeasureTheory.volume 0 1 :=
    (continuous_const.mul h₄).intervalIntegrable _ _
  rw [intervalIntegral.integral_add ((i₁.add i₂).add i₃) i₄,
    intervalIntegral.integral_add (i₁.add i₂) i₃, intervalIntegral.integral_add i₁ i₂,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem integral_mul_eta_EX01220 {u ξ F : ℝ → ℝ} (hu : Continuous u) (hξ : Continuous ξ)
    (hF : Continuous F) :
    ∫ x in (0:ℝ)..1, F x * eta_EX01216 u ξ x
      = (∫ x in (0:ℝ)..1, F x * ξ x)
        - (∫ x in (0:ℝ)..1, u x * ξ x) * ∫ x in (0:ℝ)..1, F x * u x := by
  have e : ∀ x, F x * eta_EX01216 u ξ x
      = F x * ξ x - (∫ y in (0:ℝ)..1, u y * ξ y) * (F x * u x) := by
    intro x
    unfold eta_EX01216
    ring
  simp_rw [e]
  have i₁ : IntervalIntegrable (fun x => F x * ξ x) MeasureTheory.volume 0 1 :=
    (hF.mul hξ).intervalIntegrable _ _
  have i₂ : IntervalIntegrable (fun x => (∫ y in (0:ℝ)..1, u y * ξ y) * (F x * u x))
      MeasureTheory.volume 0 1 :=
    (continuous_const.mul (hF.mul hu)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub i₁ i₂, intervalIntegral.integral_const_mul]

theorem contDiff_eta_EX01220 {u ξ : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hξ : ContDiff ℝ ∞ ξ) :
    ContDiff ℝ ∞ (eta_EX01216 u ξ) := by
  unfold eta_EX01216
  exact hξ.sub (hu.mul contDiff_const)

theorem periodic_eta_EX01220 {u ξ : ℝ → ℝ} (hu : Function.Periodic u 1)
    (hξ : Function.Periodic ξ 1) : Function.Periodic (eta_EX01216 u ξ) 1 := fun x => by
  unfold eta_EX01216
  rw [hu x, hξ x]

theorem contDiff_sin_EX01220 : ContDiff ℝ ∞ fun x : ℝ => Real.sin (2 * Real.pi * x) :=
  Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)

theorem periodic_sin_EX01220 : Function.Periodic (fun x : ℝ => Real.sin (2 * Real.pi * x)) 1 :=
  fun x => by
    show Real.sin (2 * Real.pi * (x + 1)) = Real.sin (2 * Real.pi * x)
    rw [mul_add, mul_one, Real.sin_add_two_pi]

theorem contDiff_T_EX01220 (h : ℝ) {u : ℝ → ℝ} (hu : IsAdmSmooth_EX01236 u) :
    ContDiff ℝ ∞ (euler_T_EX01220 h u) := by
  have hDD : ContDiff ℝ ∞ (angD_EX01217 (angD_EX01217 u)) :=
    contDiff_angD_EX01217 (contDiff_angD_EX01217 hu.smooth)
  have hlog : ContDiff ℝ ∞ fun x => Real.log (u x) := hu.smooth.log fun x => (hu.pos x).ne'
  unfold euler_T_EX01220
  exact ((contDiff_const.mul hDD).add
    ((contDiff_const.mul (contDiff_sin_EX01220.pow 2)).mul hu.smooth)).sub
    ((contDiff_const.mul hu.smooth).mul hlog)

theorem periodic_T_EX01220 (h : ℝ) {u : ℝ → ℝ} (hu : IsAdmSmooth_EX01236 u) :
    Function.Periodic (euler_T_EX01220 h u) 1 := fun x => by
  have h1 := periodic_angD_EX01217 (periodic_angD_EX01217 hu.periodic) x
  have h2 : Real.sin (2 * Real.pi * (x + 1)) = Real.sin (2 * Real.pi * x) :=
    periodic_sin_EX01220 x
  unfold euler_T_EX01220
  rw [h1, h2, hu.periodic x]

theorem eq_zero_of_integral_mul_self_EX01220 {g : ℝ → ℝ} (hg : Continuous g)
    (hp : Function.Periodic g 1) (h0 : ∫ x in (0:ℝ)..1, g x * g x = 0) : ∀ x, g x = 0 := by
  have hc : Continuous fun x => g x * g x := hg.mul hg
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae (zero_le_one' ℝ)
    (Filter.Eventually.of_forall fun x => mul_self_nonneg (g x))
    (hc.intervalIntegrable _ _)).1 h0
  have heq : Set.EqOn (fun x => g x * g x) 0 (Set.Ioc (0:ℝ) 1) :=
    Measure.eqOn_Ioc_of_ae_eq volume hae hc.continuousOn continuous_const.continuousOn
  have hz : ∀ z ∈ Set.Ioc (0:ℝ) 1, g z = 0 := fun z hz =>
    mul_self_eq_zero.1 (heq hz)
  intro x
  obtain ⟨z, hzI, hxz⟩ := hp.exists_mem_Ico₀ one_pos x
  rw [hxz]
  rcases hzI.1.eq_or_lt with h | h
  · have h1 : g 1 = g 0 := by simpa using hp 0
    rw [← h, ← h1]
    exact hz 1 ⟨one_pos, le_rfl⟩
  · exact hz z ⟨h, hzI.2.le⟩

theorem groundE_expand_EX01220 (h : ℝ) (u : ℝ → ℝ) :
    groundE_EX01236 h u
      = 4 * (∫ x in (0:ℝ)..1, angD_EX01217 u x * angD_EX01217 u x)
        - 4 * (∫ x in (0:ℝ)..1, (u x * Real.log (u x)) * u x)
        + h ^ 2 * ∫ x in (0:ℝ)..1, (Real.sin (2 * Real.pi * x) ^ 2 * u x) * u x := by
  have p1 : ∀ x, ((2 * Real.pi)⁻¹ * deriv u x) ^ 2 = angD_EX01217 u x * angD_EX01217 u x := by
    intro x
    rw [angD_EX01217_apply]
    ring
  have p2 : ∀ x, u x ^ 2 * Real.log (u x) = (u x * Real.log (u x)) * u x := fun x => by ring
  have p3 : ∀ x, Real.sin (2 * Real.pi * x) ^ 2 * u x ^ 2
      = (Real.sin (2 * Real.pi * x) ^ 2 * u x) * u x := fun x => by ring
  unfold groundE_EX01236
  simp only [p1, p2, p3]

theorem firstVariation_value_EX01220 (h : ℝ) {u ξ : ℝ → ℝ} (hu : IsAdmSmooth_EX01236 u)
    (hξ : ContDiff ℝ ∞ ξ) (hξp : Function.Periodic ξ 1) :
    (8 * (∫ x in (0:ℝ)..1, angD_EX01217 u x * angD_EX01217 (eta_EX01216 u ξ) x)
        + 2 * h ^ 2 * ∫ x in (0:ℝ)..1, Real.sin (2 * Real.pi * x) ^ 2 * u x * eta_EX01216 u ξ x)
      - 4 * ∫ x in (0:ℝ)..1, (2 * u x * Real.log (u x) + u x) * eta_EX01216 u ξ x
    = 2 * ∫ x in (0:ℝ)..1, (euler_T_EX01220 h u x - groundE_EX01236 h u * u x) * ξ x := by
  have hus := hu.smooth
  have huc : Continuous u := hus.continuous
  have hξc : Continuous ξ := hξ.continuous
  have hη := contDiff_eta_EX01220 hus hξ
  have hηp := periodic_eta_EX01220 hu.periodic hξp
  have hηc : Continuous (eta_EX01216 u ξ) := hη.continuous
  have hDu : Continuous (angD_EX01217 u) := (contDiff_angD_EX01217 hus).continuous
  have hP : Continuous (angD_EX01217 (angD_EX01217 u)) :=
    (contDiff_angD_EX01217 (contDiff_angD_EX01217 hus)).continuous
  have hlog : Continuous fun x => Real.log (u x) :=
    huc.log fun x => (hu.pos x).ne'
  have hsin : Continuous fun x : ℝ => Real.sin (2 * Real.pi * x) := contDiff_sin_EX01220.continuous
  have hTc : Continuous (euler_T_EX01220 h u) := (contDiff_T_EX01220 h hu).continuous
  have hmass : ∫ x in (0:ℝ)..1, u x * u x = 1 := by simpa [pow_two] using hu.mass
  -- integration by parts
  have bp1 := ex012_17_periodic_angular_integration_parts_by_parts hus hη hu.periodic hηp
  have bp2 := ex012_17_periodic_angular_integration_parts_by_parts hus hus hu.periodic hu.periodic
  -- the integrals of `(2T - 4u) * η`
  have hS : Continuous fun x => Real.sin (2 * Real.pi * x) ^ 2 * u x := (hsin.pow 2).mul huc
  have hL : Continuous fun x => u x * Real.log (u x) := huc.mul hlog
  have hV : (8 * (∫ x in (0:ℝ)..1, angD_EX01217 u x * angD_EX01217 (eta_EX01216 u ξ) x)
        + 2 * h ^ 2 * ∫ x in (0:ℝ)..1, Real.sin (2 * Real.pi * x) ^ 2 * u x * eta_EX01216 u ξ x)
      - 4 * ∫ x in (0:ℝ)..1, (2 * u x * Real.log (u x) + u x) * eta_EX01216 u ξ x
      = ∫ x in (0:ℝ)..1, (2 * euler_T_EX01220 h u x - 4 * u x) * eta_EX01216 u ξ x := by
    have e1 : ∀ x, (2 * u x * Real.log (u x) + u x) * eta_EX01216 u ξ x
        = 2 * ((u x * Real.log (u x)) * eta_EX01216 u ξ x) + 1 * (u x * eta_EX01216 u ξ x) :=
      fun x => by ring
    have e2 : ∀ x, (2 * euler_T_EX01220 h u x - 4 * u x) * eta_EX01216 u ξ x
        = (-8) * (angD_EX01217 (angD_EX01217 u) x * eta_EX01216 u ξ x)
          + (2 * h ^ 2) * ((Real.sin (2 * Real.pi * x) ^ 2 * u x) * eta_EX01216 u ξ x)
          + (-8) * ((u x * Real.log (u x)) * eta_EX01216 u ξ x)
          + (-4) * (u x * eta_EX01216 u ξ x) := by
      intro x
      unfold euler_T_EX01220
      ring
    simp_rw [e1, e2]
    rw [integral_two_EX01220 (f₁ := fun x => u x * Real.log (u x) * eta_EX01216 u ξ x)
        (f₂ := fun x => u x * eta_EX01216 u ξ x) 2 1 (hL.mul hηc) (huc.mul hηc),
      integral_four_EX01220 (f₁ := fun x => angD_EX01217 (angD_EX01217 u) x * eta_EX01216 u ξ x)
        (f₂ := fun x => Real.sin (2 * Real.pi * x) ^ 2 * u x * eta_EX01216 u ξ x)
        (f₃ := fun x => u x * Real.log (u x) * eta_EX01216 u ξ x)
        (f₄ := fun x => u x * eta_EX01216 u ξ x) (-8) (2 * h ^ 2) (-8) (-4)
        (hP.mul hηc) (hS.mul hηc) (hL.mul hηc) (huc.mul hηc),
      bp1]
    ring
  rw [hV, integral_mul_eta_EX01220 (F := fun x => 2 * euler_T_EX01220 h u x - 4 * u x) huc hξc
    ((continuous_const.mul hTc).sub (continuous_const.mul huc))]
  -- `∫ (2T - 4u) u = 2E - 4`
  have hE : ∫ x in (0:ℝ)..1, (2 * euler_T_EX01220 h u x - 4 * u x) * u x
      = 2 * groundE_EX01236 h u - 4 := by
    have e3 : ∀ x, (2 * euler_T_EX01220 h u x - 4 * u x) * u x
        = (-8) * (angD_EX01217 (angD_EX01217 u) x * u x)
          + (2 * h ^ 2) * ((Real.sin (2 * Real.pi * x) ^ 2 * u x) * u x)
          + (-8) * ((u x * Real.log (u x)) * u x)
          + (-4) * (u x * u x) := by
      intro x
      unfold euler_T_EX01220
      ring
    simp_rw [e3]
    rw [integral_four_EX01220 (f₁ := fun x => angD_EX01217 (angD_EX01217 u) x * u x)
        (f₂ := fun x => Real.sin (2 * Real.pi * x) ^ 2 * u x * u x)
        (f₃ := fun x => u x * Real.log (u x) * u x)
        (f₄ := fun x => u x * u x) (-8) (2 * h ^ 2) (-8) (-4)
        (hP.mul huc) (hS.mul huc) (hL.mul huc) (huc.mul huc),
      groundE_expand_EX01220, hmass]
    linarith
  -- `∫ (2T - 4u) ξ = 2 ∫ (T - E u) ξ + (2E - 4) ∫ u ξ`
  have hX : ∫ x in (0:ℝ)..1, (2 * euler_T_EX01220 h u x - 4 * u x) * ξ x
      = 2 * (∫ x in (0:ℝ)..1, (euler_T_EX01220 h u x - groundE_EX01236 h u * u x) * ξ x)
        + (2 * groundE_EX01236 h u - 4) * ∫ x in (0:ℝ)..1, u x * ξ x := by
    have e4 : ∀ x, (2 * euler_T_EX01220 h u x - 4 * u x) * ξ x
        = 2 * ((euler_T_EX01220 h u x - groundE_EX01236 h u * u x) * ξ x)
          + (2 * groundE_EX01236 h u - 4) * (u x * ξ x) := fun x => by ring
    simp_rw [e4]
    rw [integral_two_EX01220
      (f₁ := fun x => (euler_T_EX01220 h u x - groundE_EX01236 h u * u x) * ξ x)
      (f₂ := fun x => u x * ξ x) 2 (2 * groundE_EX01236 h u - 4)
      ((hTc.sub (continuous_const.mul huc)).mul hξc) (huc.mul hξc)]
  rw [hX, hE]
  ring

theorem firstVariation_EX01220 (h : ℝ) {u ξ : ℝ → ℝ} (hu : IsAdmSmooth_EX01236 u)
    (hξ : ContDiff ℝ ∞ ξ) (hξp : Function.Periodic ξ 1) :
    HasDerivAt (fun t => groundE_EX01236 h (ucurve_EX01216 u ξ t))
      (2 * ∫ x in (0:ℝ)..1, (euler_T_EX01220 h u x - groundE_EX01236 h u * u x) * ξ x) 0 := by
  obtain ⟨m, M, Q, hm, hM, hQ⟩ := exists_extrema_EX01220 hu hξ hξp
  have h18 := ex012_18_entropic_first_variation hu hξ hξp hm hM hQ
  have h19 := ex012_19_kinetic_potential_first_variations hu hξ hξp (h ^ 2)
  have hT := h19.sub (h18.const_mul 4)
  have hfun : (fun t => groundE_EX01236 h (ucurve_EX01216 u ξ t))
      = fun t => (4 * (∫ x in (0:ℝ)..1, angD_EX01217 (ucurve_EX01216 u ξ t) x ^ 2)
        + h ^ 2 * ∫ x in (0:ℝ)..1, Real.sin (2 * Real.pi * x) ^ 2 * ucurve_EX01216 u ξ t x ^ 2)
        - 4 * ∫ x in (0:ℝ)..1,
          ucurve_EX01216 u ξ t x ^ 2 * Real.log (ucurve_EX01216 u ξ t x) := by
    funext t
    have p1 : ∀ (v : ℝ → ℝ) (x : ℝ),
        ((2 * Real.pi)⁻¹ * deriv v x) ^ 2 = angD_EX01217 v x ^ 2 := fun v x => by
      rw [angD_EX01217_apply]
    unfold groundE_EX01236
    simp only [p1]
    ring
  rw [hfun]
  refine HasDerivAt.congr_deriv hT ?_
  exact firstVariation_value_EX01220 h hu hξ hξp

/-- Part (i): the first variation along the admissible curve of EX012.16. -/
theorem ex012_20_stationarity_implies_pointwise_euler_identity_first_variation (h : ℝ)
    {u : ℝ → ℝ} (hu : IsAdmSmooth_EX01236 u) {ξ : ℝ → ℝ} (hξ : ContDiff ℝ ∞ ξ)
    (hξp : Function.Periodic ξ 1) :
    HasDerivAt (fun t => groundE_EX01236 h (ucurve_EX01216 u ξ t))
      (2 * ∫ x in (0:ℝ)..1, (euler_T_EX01220 h u x - groundE_EX01236 h u * u x) * ξ x) 0 :=
  firstVariation_EX01220 h hu hξ hξp

/-- Part (ii) under stationarity: the derivative at `0` vanishes for every test function. -/
theorem ex012_20_stationarity_implies_pointwise_euler_identity_of_stationary (h : ℝ)
    {u : ℝ → ℝ} (hu : IsAdmSmooth_EX01236 u)
    (hstat : ∀ ξ : ℝ → ℝ, ContDiff ℝ ∞ ξ → Function.Periodic ξ 1 →
      deriv (fun t => groundE_EX01236 h (ucurve_EX01216 u ξ t)) 0 = 0) :
    ∀ x, euler_T_EX01220 h u x = groundE_EX01236 h u * u x := by
  set ξ₀ : ℝ → ℝ := fun x => euler_T_EX01220 h u x - groundE_EX01236 h u * u x with hξ₀
  have hs : ContDiff ℝ ∞ ξ₀ := (contDiff_T_EX01220 h hu).sub (contDiff_const.mul hu.smooth)
  have hp : Function.Periodic ξ₀ 1 := fun x => by
    simp only [hξ₀]
    rw [periodic_T_EX01220 h hu x, hu.periodic x]
  have hd := (firstVariation_EX01220 h hu hs hp).deriv
  rw [hstat ξ₀ hs hp] at hd
  have h0 : ∫ x in (0:ℝ)..1, ξ₀ x * ξ₀ x = 0 := by
    have := hd.symm
    linarith
  intro x
  have := eq_zero_of_integral_mul_self_EX01220 hs.continuous hp h0 x
  simp only [hξ₀] at this
  linarith

/-- Part (ii) under a local minimum at `0` along every admissible curve. -/
theorem ex012_20_stationarity_implies_pointwise_euler_identity_of_local_min (h : ℝ)
    {u : ℝ → ℝ} (hu : IsAdmSmooth_EX01236 u)
    (hloc : ∀ ξ : ℝ → ℝ, ContDiff ℝ ∞ ξ → Function.Periodic ξ 1 →
      IsLocalMin (fun t => groundE_EX01236 h (ucurve_EX01216 u ξ t)) 0) :
    ∀ x, euler_T_EX01220 h u x = groundE_EX01236 h u * u x :=
  ex012_20_stationarity_implies_pointwise_euler_identity_of_stationary h hu
    fun ξ hξ hξp => (hloc ξ hξ hξp).hasDerivAt_eq_zero
      (firstVariation_EX01220 h hu hξ hξp) |> fun h0 => by
        rw [(firstVariation_EX01220 h hu hξ hξp).deriv]
        exact h0

/-- Stationarity implies the pointwise Euler identity. -/
theorem ex012_20_stationarity_implies_pointwise_euler_identity (h : ℝ) {u : ℝ → ℝ}
    (hu : IsAdmSmooth_EX01236 u) :
    (∀ ξ : ℝ → ℝ, ContDiff ℝ ∞ ξ → Function.Periodic ξ 1 →
      HasDerivAt (fun t => groundE_EX01236 h (ucurve_EX01216 u ξ t))
        (2 * ∫ x in (0:ℝ)..1, (euler_T_EX01220 h u x - groundE_EX01236 h u * u x) * ξ x) 0) ∧
    ((∀ v : ℝ → ℝ, IsAdmSmooth_EX01236 v → groundE_EX01236 h u ≤ groundE_EX01236 h v) →
      ∀ x, euler_T_EX01220 h u x = groundE_EX01236 h u * u x) := by
  refine ⟨fun ξ hξ hξp => firstVariation_EX01220 h hu hξ hξp, fun hmin => ?_⟩
  refine ex012_20_stationarity_implies_pointwise_euler_identity_of_local_min h hu
    fun ξ hξ hξp => ?_
  obtain ⟨m, M, Q, hm, hM, hQ⟩ := exists_extrema_EX01220 hu hξ hξp
  have hm0 : 0 < m := by
    obtain ⟨x, hx⟩ := hm.1
    rw [← hx]
    exact hu.pos x
  have hδ := delta_pos_EX01216 (Q := Q) hm0
  have hS := ex012_16_admissible_normalized_variation hu hξ hξp hm hM hQ
  have hz : ucurve_EX01216 u ξ 0 = u := funext (hS.2.2.2.1)
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0:ℝ) hδ) fun t ht => ?_
  have ht' : |t| < delta_EX01216 m Q := by simpa [Real.dist_eq] using ht
  show groundE_EX01236 h (ucurve_EX01216 u ξ 0) ≤ groundE_EX01236 h (ucurve_EX01216 u ξ t)
  rw [hz]
  exact hmin _ (hS.2.2.1 t ht').1

/-- Part (ii) with minimality stated for `ex010_ground h` over all `AbsoluteDensity 1`. -/
theorem ex012_20_stationarity_implies_pointwise_euler_identity_ground (h : ℝ) {u : ℝ → ℝ}
    (hu : IsAdmSmooth_EX01236 u)
    (hmin : ∀ σ : AbsoluteDensity 1,
      DGPS.Circle.VonMisesSmallField.ex010_ground h (smoothDensity_EX01236 u hu)
        ≤ DGPS.Circle.VonMisesSmallField.ex010_ground h σ) :
    ∀ x, euler_T_EX01220 h u x = groundE_EX01236 h u * u x :=
  (ex012_20_stationarity_implies_pointwise_euler_identity h hu).2 fun v hv => by
    have := hmin (smoothDensity_EX01236 v hv)
    rwa [ground_smoothDensity_EX01236 h hu, ground_smoothDensity_EX01236 h hv] at this

end DGPS.Frontier.EX012
