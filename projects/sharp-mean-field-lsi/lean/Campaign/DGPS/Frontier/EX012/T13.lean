import DGPS.Frontier.EX012.T36

/-!
# EX012.13: Transfer the smooth representative and its mass

Task id: EX012.13 (node EX012, leaf formalization).
Title: Transfer the smooth representative and its mass.

For a minimizing `ρ` of EX011 and its positive smooth representative `r`
(`ρ.density =ᵐ[haar 1] r`), the density representative `r` is Haar measurable and integrable with
`∫ r = 1`, and `u = √r` (read on the lift, `u t = √(r (torusLift fun _ => t))`) is positive,
smooth, one-periodic with `∫₀¹ u² = 1`. The representative equalities used to evaluate the ground
functional at `u²` are proved: `u² = r ∘ pt`, the density of the construction of EX012.36 equals
`r` everywhere and `ρ.density` almost everywhere, and `ex010_ground h ρ` equals
`ex010_ground h (smoothDensity u _)` and the displayed `E_h(u²)`.

## Provides

* `DGPS.Frontier.EX012.ex012_13_transfer_smooth_representative_mass`: for `ρ` and a positive
  smooth representative `r` of `ρ.density`: `r` is measurable and integrable, `∫ r = 1`,
  `r` has a positive lower bound, and `u = √(r ∘ pt)` is smooth, periodic, positive, of mass one,
  with `u² = r ∘ pt`, density of the EX012.36 construction `= r` and `=ᵐ ρ.density`, and the
  ground-functional equalities for every `h`.
* `DGPS.Frontier.EX012.ex012_13_transfer_smooth_representative_mass_ex011`: the same conclusions
  for every ground minimizer `ρ` of EX011 (small `h`), with the representative `r` supplied by
  `DGPS.Examples.uniform_haar_capture_of_ground_minimizers`.
* `DGPS.Frontier.EX012.ex012_13_transfer_smooth_representative_mass_unique`: two continuous
  representatives that agree almost everywhere with the same density are equal everywhere.

## R5 notes

* The main statement is stated for an arbitrary `ρ : AbsoluteDensity 1` and any `r` with the
  three properties delivered by EX011 (`0 < r`, `IsSmoothPeriodic r`, `ρ.density =ᵐ[haar 1] r`);
  the minimizing hypothesis is not needed for the transfer and is therefore not imposed (no
  hypothesis is added, one is not used). The `_ex011` theorem restores the literal reading
  "for each minimizing `ρ` in EX011" by quantifying over the `h0` and minimizers of EX011 and
  obtaining `r` from EX011 itself.
* The specification's `u = √r` is read on the lift: `r` lives on `Torus 1`, so
  `u t = Real.sqrt (r (torusLift fun _ => t))`, a function `ℝ → ℝ` (the form consumed by
  EX012.36, whose `IsAdmSmooth_EX01236` is used as the bundle of the four properties).
* "Haar measurable" is `Measurable r` for the Borel sigma-algebra of `Torus 1`; "`∫ r = 1`" is
  both the Haar integral `∫ x, r x ∂haar 1 = 1` and the interval form `∫ t in 0..1, r (pt t) = 1`
  (the second one is only a corollary of continuity, via `DGPS.integral_haar_one`).
* "`min r > 0`" is read as the existence of a positive lower bound `m ≤ r x` for all `x`, by
  compactness of `Torus 1` and continuity of `r`; it is used for smoothness of the square root
  only through the pointwise positivity `r > 0`.
* Derivatives are taken only of the smooth representative `r` (through `u`); the a.e. class of
  `ρ.density` is used only for integrals and for `ex010_ground` (EX012.36).
* "Full support of Haar" is not used as such; the uniqueness lemma `_unique` is an extra
  public fact (not in the specification) proved from continuity and an open-set argument using
  that nonempty open sets have positive Haar measure.
-/

open MeasureTheory
open scoped ContDiff

namespace DGPS.Frontier.EX012

open DGPS.Circle.VonMisesSmallField

theorem measurable_rep_EX01213 {r : Torus 1 → ℝ} (hsm : IsSmoothPeriodic r) : Measurable r :=
  hsm.continuous_torus.measurable

theorem integrable_rep_EX01213 {r : Torus 1 → ℝ} (hsm : IsSmoothPeriodic r) :
    Integrable r (haar 1) :=
  hsm.continuous_torus.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace r)

theorem lower_bound_rep_EX01213 {r : Torus 1 → ℝ} (hr : ∀ x, 0 < r x)
    (hsm : IsSmoothPeriodic r) : ∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ r x := by
  obtain ⟨x0, -, hx0⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hsm.continuous_torus.continuousOn
  exact ⟨r x0, hr x0, fun x => hx0 (Set.mem_univ x)⟩

theorem mass_rep_EX01213 {ρ : AbsoluteDensity 1} {r : Torus 1 → ℝ}
    (hρ : ρ.density =ᵐ[haar 1] r) : ∫ x, r x ∂haar 1 = 1 := by
  rw [← integral_congr_ae hρ]
  exact ρ.mass_one

theorem ex012_13_transfer_smooth_representative_mass_unique {ρ : AbsoluteDensity 1}
    {r r' : Torus 1 → ℝ} (hsm : IsSmoothPeriodic r) (hsm' : IsSmoothPeriodic r')
    (hρ : ρ.density =ᵐ[haar 1] r) (hρ' : ρ.density =ᵐ[haar 1] r') : r = r' :=
  (Continuous.ae_eq_iff_eq (haar 1) hsm.continuous_torus hsm'.continuous_torus).1
    (hρ.symm.trans hρ')

theorem interval_mass_rep_EX01213 {ρ : AbsoluteDensity 1} {r : Torus 1 → ℝ}
    (hsm : IsSmoothPeriodic r) (hρ : ρ.density =ᵐ[haar 1] r) :
    ∫ t in (0:ℝ)..1, r (torusLift fun _ => t) = 1 := by
  rw [← DGPS.integral_haar_one r hsm.continuous_torus]
  exact mass_rep_EX01213 hρ

theorem adm_sqrt_EX01213 {ρ : AbsoluteDensity 1} {r : Torus 1 → ℝ} (hr : ∀ x, 0 < r x)
    (hsm : IsSmoothPeriodic r) (hρ : ρ.density =ᵐ[haar 1] r) :
    IsAdmSmooth_EX01236 (fun t : ℝ => Real.sqrt (r (torusLift fun _ => t))) := by
  have hrt : ContDiff ℝ ∞ fun t : ℝ => r (torusLift fun _ => t) :=
    hsm.comp (contDiff_pi.2 fun _ => contDiff_id)
  refine ⟨hrt.sqrt fun t => (hr _).ne', fun t => ?_, fun t => Real.sqrt_pos.2 (hr _), ?_⟩
  · simp only [torusLift_one_add]
  · have : ∀ t : ℝ, Real.sqrt (r (torusLift fun _ => t)) ^ 2 = r (torusLift fun _ => t) :=
      fun t => Real.sq_sqrt (hr _).le
    simp only [this]
    exact interval_mass_rep_EX01213 hsm hρ

theorem density_sqrt_EX01213 {ρ : AbsoluteDensity 1} {r : Torus 1 → ℝ} (hr : ∀ x, 0 < r x)
    (hsm : IsSmoothPeriodic r) (hρ : ρ.density =ᵐ[haar 1] r) (x : Torus 1) :
    (smoothDensity_EX01236 _ (adm_sqrt_EX01213 hr hsm hρ)).density x = r x := by
  obtain ⟨t, rfl⟩ := torus_surj_EX01236 x
  show descend_EX01236 _ (adm_sqrt_EX01213 hr hsm hρ).periodic (torusLift fun _ => t) ^ 2 = _
  rw [descend_pt_EX01236]
  exact Real.sq_sqrt (hr _).le

theorem ex012_13_transfer_smooth_representative_mass (ρ : AbsoluteDensity 1) (r : Torus 1 → ℝ)
    (hr : ∀ x, 0 < r x) (hsm : IsSmoothPeriodic r) (hρ : ρ.density =ᵐ[haar 1] r) :
    Measurable r ∧ Integrable r (haar 1) ∧ ∫ x, r x ∂haar 1 = 1 ∧
    ∫ t in (0:ℝ)..1, r (torusLift fun _ => t) = 1 ∧
    (∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ r x) ∧
    ∃ u : ℝ → ℝ, (∀ t, u t = Real.sqrt (r (torusLift fun _ => t))) ∧
      ContDiff ℝ ∞ u ∧ Function.Periodic u 1 ∧ (∀ t, 0 < u t) ∧
      ∫ t in (0:ℝ)..1, u t ^ 2 = 1 ∧
      (∀ t, u t ^ 2 = r (torusLift fun _ => t)) ∧
      ∃ hadm : IsAdmSmooth_EX01236 u,
        (∀ x, (smoothDensity_EX01236 u hadm).density x = r x) ∧
        ρ.density =ᵐ[haar 1] (smoothDensity_EX01236 u hadm).density ∧
        (∀ h : ℝ, ex010_ground h ρ = ex010_ground h (smoothDensity_EX01236 u hadm)) ∧
        (∀ h : ℝ, ex010_ground h ρ = groundE_EX01236 h u) := by
  have hadm := adm_sqrt_EX01213 hr hsm hρ
  have hval := density_sqrt_EX01213 hr hsm hρ
  have hae : ρ.density =ᵐ[haar 1] (smoothDensity_EX01236 _ hadm).density :=
    hρ.mono fun x hx => by rw [hx, hval x]
  refine ⟨measurable_rep_EX01213 hsm, integrable_rep_EX01213 hsm, mass_rep_EX01213 hρ,
    interval_mass_rep_EX01213 hsm hρ, lower_bound_rep_EX01213 hr hsm, _, fun t => rfl,
    hadm.smooth, hadm.periodic, hadm.pos, hadm.mass, fun t => Real.sq_sqrt (hr _).le, hadm,
    hval, hae, fun h => ground_congr_ae_EX01236 h hae, fun h => ?_⟩
  rw [ground_congr_ae_EX01236 h hae, ground_smoothDensity_EX01236]

theorem ex012_13_transfer_smooth_representative_mass_ex011 :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ h : ℝ, 0 < h → h < h0 → ∀ ρ : AbsoluteDensity 1,
      (∀ ρ' : AbsoluteDensity 1, ex010_ground h ρ ≤ ex010_ground h ρ') →
      ∃ r : Torus 1 → ℝ, (∀ x, 0 < r x) ∧ IsSmoothPeriodic r ∧ ρ.density =ᵐ[haar 1] r ∧
        Measurable r ∧ Integrable r (haar 1) ∧ ∫ x, r x ∂haar 1 = 1 ∧
        ∫ t in (0:ℝ)..1, r (torusLift fun _ => t) = 1 ∧
        (∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ r x) ∧
        ∃ u : ℝ → ℝ, (∀ t, u t = Real.sqrt (r (torusLift fun _ => t))) ∧
          ContDiff ℝ ∞ u ∧ Function.Periodic u 1 ∧ (∀ t, 0 < u t) ∧
          ∫ t in (0:ℝ)..1, u t ^ 2 = 1 ∧
          (∀ t, u t ^ 2 = r (torusLift fun _ => t)) ∧
          ∃ hadm : IsAdmSmooth_EX01236 u,
            (∀ x, (smoothDensity_EX01236 u hadm).density x = r x) ∧
            ρ.density =ᵐ[haar 1] (smoothDensity_EX01236 u hadm).density ∧
            (∀ h' : ℝ, ex010_ground h' ρ = ex010_ground h' (smoothDensity_EX01236 u hadm)) ∧
            (∀ h' : ℝ, ex010_ground h' ρ = groundE_EX01236 h' u) := by
  obtain ⟨h0, hh0, hcap, -⟩ := DGPS.Examples.uniform_haar_capture_of_ground_minimizers
  refine ⟨h0, hh0, fun h hpos hlt ρ hmin => ?_⟩
  obtain ⟨-, -, r, hr, hsm, hρ⟩ := hcap h hpos hlt ρ hmin
  exact ⟨r, hr, hsm, hρ, ex012_13_transfer_smooth_representative_mass ρ r hr hsm hρ⟩

end DGPS.Frontier.EX012
