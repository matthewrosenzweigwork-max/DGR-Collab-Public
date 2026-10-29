import DGPS.Circle.VonMisesCaptureEX011

/-!
# EX012.36: Ground-functional and admissible-density definition gate

Task id: EX012.36 (node EX012, gate unit, interface resolution).
Title: Ground-functional and admissible-density definition gate.

## Bindings

Every source object of the specification, the declaration it is bound to, and discrepancies.

| Specification object | Actual declaration (file:line) | Type / binders | Discrepancy |
| --- | --- | --- | --- |
| `ex010_ground h rho` | `DGPS.Circle.VonMisesSmallField.ex010_ground`, `DGPS/Circle/VonMisesSmallField.lean:31` | `(h : ℝ) (ρ : AbsoluteDensity 1) : ℝ`, body `ex010_haarFisher ρ - 2 * circleEntropy ρ + h ^ 2 * ex010_potential ρ` | It is a function of an `AbsoluteDensity 1`, not of a function `u`; the density `u^2` is passed as `smoothDensity_EX01236 u _`. |
| angular Fisher term | `DGPS.Circle.VonMisesSmallField.ex010_haarFisher`, `VonMisesSmallField.lean:23`; `DGPS.Analysis.circleFisherInformation`, `DGPS/Circle/QuantitativeLSI.lean:21` | `ex010_haarFisher ρ = circleFisherInformation ρ / a0`, `circleFisherInformation ρ = 4 * ∫ ‖weakGradient ρ.sqrt _‖^2 ∂haar 1`, `a0 = 4 * π^2` (`DGPS.Circle.AngularNormalization.a0`, `AngularNormalization.lean:224`) | `weakGradient` is the derivative in the lift coordinate `x`, so `‖∇u‖^2 = (u')^2 = a0 (Du)^2` with `D = (2π)⁻¹ ∂ₓ`; the quotient by `a0` gives exactly `4 ∫ (Du)^2`. No rescaling. |
| entropy term | `DGPS.Analysis.circleEntropy`, `QuantitativeLSI.lean:25` | `circleEntropy ρ = (homogeneousEntropy (haar 1) ρ.density).toReal` | For `ρ = u^2` of mass one and `u > 0` it equals `∫ u^2 log u^2`, so `-2 H = -4 ∫ u^2 log u`. |
| potential term | `DGPS.Circle.VonMisesSmallField.ex010_potential`, `VonMisesSmallField.lean:27` | `ex010_potential ρ = ∫ ρ.density x * sinHarm 1 x ^ 2 ∂haar 1` | `sinHarm 1 (pt t) = sin (2π t)`, so this is `∫ s_1^2 u^2`. |
| `AbsoluteDensity 1` | `DGPS.AbsoluteDensity`, `DGPS/Foundations/AbsoluteDensity.lean:35` | structure over `sqrt : Torus d → ℝ` with `sqrt_mem : sqrt ∈ H1Haar d`, `sqrt_nonneg : 0 ≤ᵐ[haar d] sqrt`, `mass_one : ∫ sqrt^2 ∂haar d = 1`; `density = sqrt^2` (`AbsoluteDensity.density`, line 42) | The density is stored through its square root `u`; there is no field `positive` or `smooth`. |
| circle `Torus 1` and Haar integral | `DGPS.Torus`, `DGPS/Foundations/Torus.lean:32`; `DGPS.haar`, `Torus.lean:35`; `DGPS.torusLift`, `Torus.lean:41`; `DGPS.integral_haar_one`, `DGPS/Foundations/SobolevEmbedding.lean:491` | `Torus 1 = Fin 1 → AddCircle 1`; `integral_haar_one (f : Torus 1 → ℝ) (hf : Continuous f) : ∫ f ∂haar 1 = ∫ t in 0..1, f (torusLift fun _ => t)` | The specification integrates over `[0,1]`; the identification with `haar 1` needs continuity of the integrand, which holds for positive smooth `u`. |
| smooth periodic `u` | `DGPS.IsSmoothPeriodic`, `Torus.lean:117` | `IsSmoothPeriodic (φ : Torus d → ℝ) : Prop := ContDiff ℝ ∞ (φ ∘ torusLift)` | The specification speaks of a periodic `u : ℝ → ℝ`; it is transported to the circle by `descend_EX01236` (`Function.Periodic.lift`). |
| weak gradient | `DGPS.weakGradient`, `Torus.lean:137`; `DGPS.IsSmoothPeriodic.isWeakGradient`, `DGPS/Foundations/PeriodicSmoothing.lean:416`; `DGPS.weakGradient_ae_eq`, `DGPS/Foundations/WeakSobolev.lean:175` | `weakGradient (u) (hu : MemH1 u) : Torus d → Tangent d`, equal a.e. to the classical gradient `smoothGrad` for smooth periodic `u` | The chosen weak gradient is only a.e. equal to `coordPartial`; integrals are compared with `integral_congr_ae`. |
| identification of the ground functional | `DGPS.Circle.VonMisesCaptureEX011.ground_eq_ex011`, `DGPS/Circle/VonMisesCaptureEX011.lean:77` | `ex010_ground h ρ = (π^2)⁻¹ * ∫ (weakGradient ρ.sqrt _ x 0)^2 - 2 * ∫ eulF (ρ.sqrt x) + h^2 * ∫ ρ.sqrt x^2 * sinHarm 1 x^2` (with `eulF v = v^2 log v^2`, `DGPS/Examples/ThreeSpeciesCircle/OrdinaryEuler.lean:16`) | None: the common positive scalar of the specification is `1`. |
| captured `rho` | `DGPS.Circle.VonMisesCaptureEX011.uniform_haar_capture_of_ground_minimizers`, `VonMisesCaptureEX011.lean:945` | for ground minimizers: `∃ r : Torus 1 → ℝ, (∀ x, 0 < r x) ∧ IsSmoothPeriodic r ∧ ρ.density =ᵐ[haar 1] r` | EX011 supplies the smooth representative of the density `r`, not of `u = sqrt r`; `u` is recovered as `sqrt (r (pt t))`. |
| a.e. equality of densities implies equal square roots | `DGPS.AbsoluteDensity.sqrt_ae_eq_of_density_ae_eq`, `AbsoluteDensity.lean:59` | `ρ.density =ᵐ σ.density → ρ.sqrt =ᵐ σ.sqrt` | The specification calls the identifier unverified; it exists. |
| `E_h(u^2)` | `groundE_EX01236` (this file) | `(h : ℝ) (u : ℝ → ℝ) : ℝ` | Written with `deriv u`, `Real.log`, `Real.sin (2 * π * t)` and `∫ t in (0:ℝ)..1`. |

## Provides

* `DGPS.Frontier.EX012.descend_EX01236`: descent of a one-periodic `u : ℝ → ℝ` to `Torus 1`.
* `DGPS.Frontier.EX012.IsAdmSmooth_EX01236`: bundle of the hypotheses (smooth, one-periodic, positive, `∫ u^2 = 1`).
* `DGPS.Frontier.EX012.smoothDensity_EX01236`: the `AbsoluteDensity 1` whose square root is `descend u`.
* `DGPS.Frontier.EX012.groundE_EX01236`: the displayed `E_h(u^2)`.
* `DGPS.Frontier.EX012.ground_smoothDensity_EX01236`: `ex010_ground h (smoothDensity u _) = groundE h u`.
* `DGPS.Frontier.EX012.ground_congr_ae_EX01236`: `ex010_ground h` depends only on the a.e. class of the density.
* `DGPS.Frontier.EX012.gate_ex012_36_ground_functional_admissible_density_definition_gate`: the
  square root of the construction at `pt t` is `u t`, and `ex010_ground h` of it is `E_h(u^2)`, with scalar `1`.
* `DGPS.Frontier.EX012.gate_ex012_36_ground_functional_admissible_density_definition_gate_transport`: for
  the captured `ρ` with positive smooth representative `r` (`ρ.density =ᵐ r`), an admissible
  smooth `u` with `u^2 = r ∘ pt`, density of the construction equal to `r` everywhere, and
  `ex010_ground h ρ = ex010_ground h (smoothDensity u _) = E_h(u^2)`.

## R5 notes

* No rescaling occurs: the common positive scalar of the specification is `1` (the angular Fisher
  information is already divided by `a0 = 4π^2`, which turns `∫ (u')^2` into `4 ∫ (Du)^2`).
* `u` is a function on `ℝ`, one-periodic and `C^∞`; the integrals are over `[0,1]` as interval
  integrals (`∫ t in (0:ℝ)..1`), converted from `haar 1` by `integral_haar_one`.
* The hypotheses of the main theorem are exactly those of the specification: smooth, periodic,
  positive, `∫ u^2 = 1`. Positivity is used for continuity of `u^2 log u^2` and in `-2H = -4 ∫ u^2 log u`.
* `D = (2π)⁻¹ ∂ₓ` is written `(2 * π)⁻¹ * deriv u t`; `s_1(x) = sin (2π x)`.
* The Task 13 transport is split in two: `ground_congr_ae_EX01236` (a.e. equal densities give the same
  ground value) and the `_transport` theorem. The latter takes the EX011 output form
  `r` with `ρ.density =ᵐ r`, `r > 0`, `IsSmoothPeriodic r`, and builds `u = sqrt (r ∘ pt)`; `smoothness`
  of `u` uses `r > 0`.
* The existential `∃ hadm : IsAdmSmooth_EX01236 u` quantifies over a proposition so that the
  dependent construction `smoothDensity_EX01236 u hadm` can be named in the conclusion.
* Equality `ex010_ground h ρ = E_h(u^2)` for the captured `ρ` itself is stated through the
  a.e. representative; this is the only meaning available since `ρ.sqrt` is only a.e. determined.
-/

open MeasureTheory
open scoped ContDiff

namespace DGPS.Frontier.EX012

open DGPS.Examples.ThreeSpeciesCircle DGPS.Circle.VonMisesSmallField

/-- Descent of a `1`-periodic function to the circle `Torus 1`. -/
noncomputable def descend_EX01236 (u : ℝ → ℝ) (hper : Function.Periodic u 1) : Torus 1 → ℝ :=
  fun x => hper.lift (x 0)

theorem descend_pt_EX01236 (u : ℝ → ℝ) (hper : Function.Periodic u 1) (t : ℝ) :
    descend_EX01236 u hper (torusLift fun _ => t) = u t := by
  show hper.lift (((t : ℝ) : AddCircle (1:ℝ))) = u t
  exact Function.Periodic.lift_coe hper t

theorem torus_surj_EX01236 (x : Torus 1) : ∃ t : ℝ, torusLift (fun _ => t) = x := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (x 0)
  refine ⟨t, ?_⟩
  ext i
  fin_cases i
  exact ht

theorem isSmoothPeriodic_descend_EX01236 {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) : IsSmoothPeriodic (descend_EX01236 u hper) := by
  have : (descend_EX01236 u hper ∘ torusLift) = fun y : Fin 1 → ℝ => u (y 0) := by
    funext y
    exact descend_pt_EX01236 u hper (y 0)
  unfold IsSmoothPeriodic
  rw [this]
  exact hu.comp (contDiff_apply ℝ ℝ 0)


/-- Hypotheses of a positive smooth periodic `u` of unit `L²` mass on `[0,1]`. -/
structure IsAdmSmooth_EX01236 (u : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ u
  periodic : Function.Periodic u 1
  pos : ∀ t, 0 < u t
  mass : ∫ t in (0:ℝ)..1, u t ^ 2 = 1

theorem continuous_descend_EX01236 {u : ℝ → ℝ} (h : IsAdmSmooth_EX01236 u) :
    Continuous (descend_EX01236 u h.periodic) :=
  (isSmoothPeriodic_descend_EX01236 h.smooth h.periodic).continuous_torus

theorem descend_pos_EX01236 {u : ℝ → ℝ} (h : IsAdmSmooth_EX01236 u) (x : Torus 1) :
    0 < descend_EX01236 u h.periodic x := by
  obtain ⟨t, rfl⟩ := torus_surj_EX01236 x
  rw [descend_pt_EX01236]; exact h.pos t

/-- The `AbsoluteDensity 1` attached to a positive smooth periodic `u`. -/
noncomputable def smoothDensity_EX01236 (u : ℝ → ℝ) (h : IsAdmSmooth_EX01236 u) :
    AbsoluteDensity 1 where
  sqrt := descend_EX01236 u h.periodic
  sqrt_mem := ⟨_, (isSmoothPeriodic_descend_EX01236 h.smooth h.periodic).isWeakGradient⟩
  sqrt_nonneg := Filter.Eventually.of_forall fun x => (descend_pos_EX01236 h x).le
  mass_one := by
    rw [DGPS.integral_haar_one (fun x => descend_EX01236 u h.periodic x ^ 2)
      ((continuous_descend_EX01236 h).pow 2)]
    simp only [descend_pt_EX01236]
    exact h.mass


/-- The displayed `E_h(u^2)`. -/
noncomputable def groundE_EX01236 (h : ℝ) (u : ℝ → ℝ) : ℝ :=
  4 * (∫ t in (0:ℝ)..1, ((2 * Real.pi)⁻¹ * deriv u t) ^ 2)
    - 4 * (∫ t in (0:ℝ)..1, u t ^ 2 * Real.log (u t))
    + h ^ 2 * (∫ t in (0:ℝ)..1, Real.sin (2 * Real.pi * t) ^ 2 * u t ^ 2)

theorem coordPartial_descend_EX01236 {u : ℝ → ℝ} (hadm : IsAdmSmooth_EX01236 u) (t : ℝ) :
    coordPartial 0 (descend_EX01236 u hadm.periodic) (torusLift fun _ => t) = deriv u t := by
  have hs := isSmoothPeriodic_descend_EX01236 hadm.smooth hadm.periodic
  have h1 := hasDerivAt_smooth_one hs t
  have : (fun t : ℝ => descend_EX01236 u hadm.periodic (torusLift fun _ => t)) = u := by
    funext s; exact descend_pt_EX01236 u hadm.periodic s
  rw [this] at h1
  exact h1.deriv.symm

theorem ground_smoothDensity_EX01236 (h : ℝ) {u : ℝ → ℝ} (hadm : IsAdmSmooth_EX01236 u) :
    ex010_ground h (smoothDensity_EX01236 u hadm) = groundE_EX01236 h u := by
  have hs := isSmoothPeriodic_descend_EX01236 hadm.smooth hadm.periodic
  rw [DGPS.Circle.VonMisesCaptureEX011.ground_eq_ex011]
  have hsq : (smoothDensity_EX01236 u hadm).sqrt = descend_EX01236 u hadm.periodic := rfl
  have hae := weakGradient_ae_eq hs.isWeakGradient
  have e1 : ∫ x, (weakGradient (smoothDensity_EX01236 u hadm).sqrt
      (smoothDensity_EX01236 u hadm).sqrt_mem x 0) ^ 2 ∂haar 1
      = ∫ t in (0:ℝ)..1, (deriv u t) ^ 2 := by
    have : ∫ x, (weakGradient (smoothDensity_EX01236 u hadm).sqrt
        (smoothDensity_EX01236 u hadm).sqrt_mem x 0) ^ 2 ∂haar 1
        = ∫ x, (coordPartial 0 (descend_EX01236 u hadm.periodic) x) ^ 2 ∂haar 1 := by
      refine integral_congr_ae (hae.mono fun x hx => ?_)
      have := congrArg (fun y : Tangent 1 => y 0) hx
      simp only [smoothGrad_apply] at this
      exact congrArg (· ^ 2) this
    rw [this, DGPS.integral_haar_one (fun x => coordPartial 0 (descend_EX01236 u hadm.periodic) x ^ 2)
      (hs.continuous_coordPartial 0 |>.pow 2)]
    simp only [coordPartial_descend_EX01236 hadm]
  have e2 : ∫ x, DGPS.Examples.ThreeSpeciesCircle.eulF ((smoothDensity_EX01236 u hadm).sqrt x) ∂haar 1
      = 2 * ∫ t in (0:ℝ)..1, u t ^ 2 * Real.log (u t) := by
    have hc : Continuous fun x => DGPS.Examples.ThreeSpeciesCircle.eulF (descend_EX01236 u hadm.periodic x) :=
      ((continuous_descend_EX01236 hadm).pow 2).mul
        (((continuous_descend_EX01236 hadm).pow 2).log fun x => (pow_pos (descend_pos_EX01236 hadm x) 2).ne')
    rw [hsq, DGPS.integral_haar_one _ hc, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [descend_pt_EX01236, DGPS.Examples.ThreeSpeciesCircle.eulF, Real.log_pow]
    push_cast; ring
  have e3 : ∫ x, (smoothDensity_EX01236 u hadm).sqrt x ^ 2 * sinHarm 1 x ^ 2 ∂haar 1
      = ∫ t in (0:ℝ)..1, Real.sin (2 * Real.pi * t) ^ 2 * u t ^ 2 := by
    have hc : Continuous fun x => descend_EX01236 u hadm.periodic x ^ 2 * sinHarm 1 x ^ 2 :=
      ((continuous_descend_EX01236 hadm).pow 2).mul ((continuous_sinHarm 1).pow 2)
    rw [hsq, DGPS.integral_haar_one _ hc]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [descend_pt_EX01236, sinHarm_pt]
    simp only [Nat.cast_one, mul_one]
    ring
  rw [e1, e2, e3, groundE_EX01236]
  have : ∫ t in (0:ℝ)..1, ((2 * Real.pi)⁻¹ * deriv u t) ^ 2
      = (Real.pi ^ 2)⁻¹ / 4 * ∫ t in (0:ℝ)..1, (deriv u t) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [mul_pow]
    field_simp
    ring
  rw [this]
  ring


theorem ground_congr_ae_EX01236 (h : ℝ) {ρ σ : AbsoluteDensity 1}
    (hρσ : ρ.density =ᵐ[haar 1] σ.density) : ex010_ground h ρ = ex010_ground h σ := by
  have hs := AbsoluteDensity.sqrt_ae_eq_of_density_ae_eq hρσ
  have hg : IsWeakGradient σ.sqrt (weakGradient ρ.sqrt ρ.sqrt_mem) :=
    (isWeakGradient_weakGradient ρ.sqrt_mem).congr_ae hs (Filter.EventuallyEq.refl _ _)
  have hgg := (isWeakGradient_weakGradient σ.sqrt_mem).ae_eq hg
  have hF : DGPS.Analysis.circleFisherInformation ρ = DGPS.Analysis.circleFisherInformation σ := by
    unfold DGPS.Analysis.circleFisherInformation
    congr 1
    refine integral_congr_ae (hgg.mono fun x hx => ?_)
    simp only [hx]
  have hH : DGPS.Analysis.circleEntropy ρ = DGPS.Analysis.circleEntropy σ := by
    unfold DGPS.Analysis.circleEntropy
    rw [homogeneousEntropy_congr_ae hρσ]
  have hP : ex010_potential ρ = ex010_potential σ := by
    unfold ex010_potential
    refine integral_congr_ae (hρσ.mono fun x hx => ?_)
    simp only [hx]
  unfold ex010_ground ex010_haarFisher
  rw [hF, hH, hP]

theorem gate_ex012_36_ground_functional_admissible_density_definition_gate
    (h : ℝ) (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (hpos : ∀ t, 0 < u t) (hmass : ∫ t in (0:ℝ)..1, u t ^ 2 = 1) :
    (∀ t : ℝ, (smoothDensity_EX01236 u ⟨hu, hper, hpos, hmass⟩).sqrt (torusLift fun _ => t) = u t) ∧
    ex010_ground h (smoothDensity_EX01236 u ⟨hu, hper, hpos, hmass⟩) =
      4 * (∫ t in (0:ℝ)..1, ((2 * Real.pi)⁻¹ * deriv u t) ^ 2)
        - 4 * (∫ t in (0:ℝ)..1, u t ^ 2 * Real.log (u t))
        + h ^ 2 * (∫ t in (0:ℝ)..1, Real.sin (2 * Real.pi * t) ^ 2 * u t ^ 2) :=
  ⟨fun t => descend_pt_EX01236 u hper t,
    ground_smoothDensity_EX01236 h ⟨hu, hper, hpos, hmass⟩⟩

theorem gate_ex012_36_ground_functional_admissible_density_definition_gate_transport
    (h : ℝ) (ρ : AbsoluteDensity 1) (r : Torus 1 → ℝ) (hr : ∀ x, 0 < r x)
    (hsm : IsSmoothPeriodic r) (hρ : ρ.density =ᵐ[haar 1] r) :
    ∃ u : ℝ → ℝ, ∃ hadm : IsAdmSmooth_EX01236 u,
      (∀ t : ℝ, u t ^ 2 = r (torusLift fun _ => t)) ∧
      (∀ x, (smoothDensity_EX01236 u hadm).density x = r x) ∧
      ρ.density =ᵐ[haar 1] (smoothDensity_EX01236 u hadm).density ∧
      ex010_ground h ρ = ex010_ground h (smoothDensity_EX01236 u hadm) ∧
      ex010_ground h ρ = groundE_EX01236 h u := by
  have hrt : ContDiff ℝ ∞ fun t : ℝ => r (torusLift fun _ => t) :=
    hsm.comp (contDiff_pi.2 fun _ => contDiff_id)
  have hadm : IsAdmSmooth_EX01236 (fun t : ℝ => Real.sqrt (r (torusLift fun _ => t))) := by
    refine ⟨hrt.sqrt fun t => (hr _).ne', fun t => ?_, fun t => Real.sqrt_pos.2 (hr _), ?_⟩
    · simp only [torusLift_one_add]
    · have : ∀ t : ℝ, Real.sqrt (r (torusLift fun _ => t)) ^ 2 = r (torusLift fun _ => t) :=
        fun t => Real.sq_sqrt (hr _).le
      simp only [this]
      rw [← DGPS.integral_haar_one r hsm.continuous_torus, ← integral_congr_ae hρ]
      exact ρ.mass_one
  have hval : ∀ x, (smoothDensity_EX01236 _ hadm).density x = r x := by
    intro x
    obtain ⟨t, rfl⟩ := torus_surj_EX01236 x
    show descend_EX01236 _ hadm.periodic (torusLift fun _ => t) ^ 2 = _
    rw [descend_pt_EX01236]
    exact Real.sq_sqrt (hr _).le
  have hae : ρ.density =ᵐ[haar 1] (smoothDensity_EX01236 _ hadm).density :=
    hρ.mono fun x hx => by rw [hx, hval x]
  refine ⟨_, hadm, fun t => Real.sq_sqrt (hr _).le, hval, hae,
    ground_congr_ae_EX01236 h hae, ?_⟩
  rw [ground_congr_ae_EX01236 h hae, ground_smoothDensity_EX01236]

end DGPS.Frontier.EX012
