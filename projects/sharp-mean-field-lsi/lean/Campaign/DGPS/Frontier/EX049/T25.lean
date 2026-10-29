import DGPS.Examples.EngineeredGroundState

/-!
# EX049.25: Bind the campaign domain and the named source objects

Task id: EX049.25 (node EX049, the engineered rank-one sharp species).
Title: Bind the campaign domain and the named source objects.

Bindings (source object in the specification, the actual declaration with file:line, its type or
binder list, and any discrepancy with the specification text; every path is under
`Campaign/DGPS/`):

| Source object | Actual declaration (file:line) | Type / binders | Discrepancy |
|---|---|---|---|
| angle circle of period `2π` | `DGPS.Circle.AngularNormalization.AngCircle` (`Circle/AngularNormalization.lean:24`) | `abbrev AngCircle := AddCircle (2 * π)`; definitionally `Real.Angle` | none; the period is `2π` (global instance `fact_two_pi_pos`, `:21`) |
| `angHaar` | `DGPS.Circle.AngularNormalization.angHaar` (`Circle/AngularNormalization.lean:26`) | `abbrev angHaar : Measure AngCircle := AddCircle.haarAddCircle` | none; it is a probability measure (Mathlib instance), and it is the pushforward of normalized Lebesgue measure on any `(a, a + 2π]` (proved here) |
| real angular H1 domain (the domain used in EX049.02) | `DGPS.Circle.AngularNormalization.AngularH1` (`Circle/AngularNormalization.lean:140`), `IsAngularWeakDeriv` (`:134`), `IsSmoothAngular` (`:62`), `angDeriv` (`:65`), `angSec` (`:60`) | `structure IsAngularWeakDeriv (u g : AngCircle → ℝ) : Prop` with fields `memLp : MemLp u 2 angHaar`, `memLp_deriv : MemLp g 2 angHaar`, `ibp : ∀ ψ, IsSmoothAngular ψ → ∫ u * angDeriv ψ ∂angHaar = -∫ g * ψ ∂angHaar`; `AngularH1 u := ∃ g, IsAngularWeakDeriv u g`; `IsSmoothAngular ψ := ContDiff ℝ ∞ (fun s : ℝ => ψ ↑s)`; `angDeriv ψ θ := deriv (fun s : ℝ => ψ ↑s) (angSec θ)` | the Lean domain is the UNWEIGHTED one (`L²` and the pairing are against `angHaar`, real valued). A Lean declaration for EX049.02 does not exist at the base commit, so "the domain used in .02" is bound to this one. The weighted domain (`L²(μ_h)`, the same weak derivative) is a helper structure here and is proved equivalent |
| real-line lift of a function on the circle | `DGPS.Circle.StationaryFlux.lift` (`Circle/StationaryFlux.lean:23`), `angDeriv_coe` (`:41`), `integral_lift_period` (`:114`) | `lift ψ : ℝ → ℝ := fun s => ψ ↑s`; `angDeriv_coe ψ s : angDeriv ψ ↑s = deriv (lift ψ) s` for every `ψ` | none |
| `H¹` on the unit torus | `DGPS.IsWeakGradient` (`Foundations/Torus.lean:126`), `DGPS.MemH1` (`Foundations/Torus.lean:133`), `angularH1_comp_iff` (`Circle/AngularNormalization.lean:309`), `physGrad` (`:143`) | `IsWeakGradient {d} (u : Torus d → ℝ) (g : Torus d → Tangent d) : Prop`; `angularH1_comp_iff u : AngularH1 u ↔ MemH1 (u ∘ angEquiv)` | the torus has period `1`; the gradient is `physGrad g = 2π (g ∘ angEquiv)`, so the angular weak derivative `g` is not the torus gradient but `1/(2π)` times it |
| `A_h = 2 / (1 - e^{-2h})` | `DGPS.Examples.EngineeredRankOne.aH` (`Examples/EngineeredRankOne.lean:20`), `aH_mul` (`:23`) | `aH (h : ℝ) : ℝ := 1 + cosh h / sinh h`; `aH_mul h (hh : 0 < h) : aH h * (1 - exp (-h * 2)) = 2` | different closed form; equal to `A_h` for `0 < h` (proved here, `aH h = Asrc_EX04925 h`); for `h = 0` they differ (`aH 0 = 1`, `2 / 0 = 0`) |
| `N_h(u) = A_h (1 - e^{-hu}) - u` | `DGPS.Examples.EngineeredRankOne.numer` (`Examples/EngineeredRankOne.lean:21`) | `numer (h v : ℝ) : ℝ := aH h * (1 - exp (-h * v)) - v` | none for `0 < h` (`numer h v = Nsrc_EX04925 h v`) |
| `r_h(u) = N_h(u) / (u (2 - u))` on `(0, 2)` | `DGPS.Examples.EngineeredRankOne.integrand` (`Examples/EngineeredRankOne.lean:51`), `integrand_of_ne` (`:56`) | `integrand (h v : ℝ) : ℝ` with `if v = 0 then (aH h * h - 1) / 2 else if v = 2 then -(aH h * h * exp (-h * 2) - 1) / 2 else numer h v / (v * (2 - v))` | the Lean `integrand` is a totalization (continuous extension) of `r_h` to all of `ℝ`; it equals `r_h` off `{0, 2}`. The values at `0` and `2` are irrelevant to every integral and to the open interval `(0, 2)` |
| `R_h(u) = ∫_0^u r_h` and `corr h` | `DGPS.Examples.EngineeredRankOne.corr` (`Examples/EngineeredRankOne.lean:117`), `contDiff_corr` (`Examples/EngineeredRankOneEndpoints.lean:114`), `deriv_corr` (`:122`), `contDiff_integrand` (`:106`) | `corr (h u : ℝ) : ℝ := ∫ v in (0:ℝ)..u, integrand h v` | none; `corr h u = Rsrc_EX04925 h u` for every real `u` (in particular on `[0, 2]`); `corr h` is differentiable on all of `ℝ` and its derivative at `u ∈ (0, 2)` is `r_h(u)`. No condition on extensions off `[0, 2]` is needed or claimed |
| `U = 1 - cos θ` | `DGPS.Examples.EngineeredRankOne.Uang` (`Examples/EngineeredRankOne.lean:131`), `drift_Uang` (`Examples/EngineeredRankOneDrift.lean:31`) | `Uang (θ : AngCircle) : ℝ := 1 - Real.Angle.cos θ`; `drift_Uang t : Uang (t : Real.Angle) = 1 - Real.cos t` | none |
| `Φ_h = hU + R_h(U)` | no Lean declaration; carried by `logq` (`Examples/EngineeredRankOne.lean:149`) | `logq (h : ℝ) (θ : AngCircle) : ℝ := -(h * Uang θ) - corr h (Uang θ)` | `logq h = -Φ_h`; `Phisrc_EX04925` is the helper for `Φ_h`, and `logq h θ = -Phisrc_EX04925 h θ` is proved |
| `Z_h = ∫ e^{-Φ_h} dm` | `DGPS.Examples.EngineeredRankOne.Zh` (`Examples/EngineeredRankOne.lean:159`), `Zh_pos` (`:161`) | `Zh (h : ℝ) : ℝ := ∫ θ, exp (logq h θ) ∂angHaar` | none; `m` is the normalized `angHaar` |
| `q_h = Z_h⁻¹ e^{-Φ_h}` | `DGPS.Examples.EngineeredRankOne.qAng` (`Examples/EngineeredRankOne.lean:168`), `qAng_pos` (`:170`), `integral_qAng` (`:173`) | `qAng (h : ℝ) (θ : AngCircle) : ℝ := (Zh h)⁻¹ * exp (logq h θ)` | none |
| `μ_h = q_h m` (circle) | `DGPS.Examples.EngineeredGroundState.circleReference` (`Examples/EngineeredGroundState.lean:188`), `integral_circleReference` (`:199`) | `circleReference (h : ℝ) : Measure AngCircle := angHaar.withDensity fun θ => ENNReal.ofReal (qAng h θ)` | none; the statement `circleReference h = q_h · angHaar` is the `withDensity` form |
| `μ_h` (unit torus) | `DGPS.Models.engineeredReference` (`Examples/EngineeredRankOne.lean:226`) | `engineeredReference (h : ℝ) : Measure (Torus 1) := (angHaar.withDensity fun θ => ENNReal.ofReal (qAng h θ)).map angEquiv.symm` | transported to the torus through `angEquiv` (period `1`); equal to `(circleReference h).map angEquiv.symm` by `rfl` |
| `b = (log q_h)'` | `DGPS.Examples.EngineeredRankOne.driftB` (`Examples/EngineeredRankOneDrift.lean:26`), `driftB_eq` (`:143`), `Lh` (`Examples/EngineeredGroundState.lean:33`), `hasDerivAt_Lh` (`:47`) | `driftB (h t : ℝ) : ℝ := deriv (fun s : ℝ => logq h (s : Real.Angle)) t` | `driftB` differentiates `logq h = -Φ_h`, not `log q_h`; they differ by the constant `-log Z_h`, so the derivatives agree (proved). `driftB` lives on the lifted angle (`ℝ → ℝ`, `2π`-periodic); on the circle it is read as `driftB h (angSec θ)` |
| `V = b²/4 + b'/2` | `DGPS.Examples.EngineeredRankOne.groundPot` (`Examples/EngineeredRankOneDrift.lean:29`), `groundPot_periodic` (`Examples/EngineeredGroundState.lean:159`), `groundPot_angSec` (`:171`) | `groundPot (h t : ℝ) : ℝ := driftB h t ^ 2 / 4 + deriv (driftB h) t / 2` | none; `b'` is `deriv (driftB h)` on the lifted angle; the circle-level reading is proved against `angDeriv` |
| `M_h(v) = ∫ v² dμ_h`, `E_h(v) = ∫ (v')² dμ_h` | no declarations at the base commit | expressed as `∫ θ, v θ ^ 2 ∂circleReference h` and `∫ θ, g θ ^ 2 ∂circleReference h` | `E_h` is well defined: the angular weak derivative is unique `angHaar`-a.e., hence `μ_h`-a.e. (proved). Both integrals are finite on the domain (proved) |

Provides:
* `DGPS.Frontier.EX049.gate_ex049_25_bind_campaign_domain_named_source_objects`: the
  conjunction of the five parts below, for `0 < h`.
* `DGPS.Frontier.EX049.gate_ex049_25_bind_campaign_domain_named_source_objects_period_haar`:
  period `2π`; `angHaar` is a probability measure and the pushforward of the normalized Lebesgue
  measure on `(a, a + 2π]` for every `a`; its integral formula.
* `DGPS.Frontier.EX049.gate_ex049_25_bind_campaign_domain_named_source_objects_h1_domain`: the
  campaign `H¹` domain `AngularH1` / `IsAngularWeakDeriv` in interval form, its a.e. uniqueness
  and congruence, the equivalence with the weighted `L²(μ_h)` domain for the same weak
  derivative, the finiteness of `M_h` and `E_h`, and the torus bridge.
* `DGPS.Frontier.EX049.gate_ex049_25_bind_campaign_domain_named_source_objects_corr`:
  `aH h = A_h`, `numer = N_h`, `integrand = r_h` on `(0, 2)`, `corr h = R_h` (on `[0, 2]` and in
  fact on `ℝ`), and the derivative `r_h` on `(0, 2)`.
* `DGPS.Frontier.EX049.gate_ex049_25_bind_campaign_domain_named_source_objects_reference`:
  `Uang`, `logq = -Φ_h`, `Zh = Z_h`, `qAng = q_h`, `circleReference = q_h · angHaar`, the
  probability property, and the interval form of `Z_h`.
* `DGPS.Frontier.EX049.gate_ex049_25_bind_campaign_domain_named_source_objects_drift`:
  `driftB = (log q_h)'`, `groundPot = b²/4 + b'/2`, the formula for `driftB` through `r_h`,
  periodicity, and the circle-level reading through `angSec` and `angDeriv`.

R5 notes:
* The specification says that the printed packet omits the definition bodies of `AngCircle`,
  `angHaar`, the H1 carrier, `circleReference`, `corr`, `Zh`, `qAng`, `driftB` and `groundPot`,
  and that no guessed Lean declaration name is supplied. At the base commit every one of them has
  a real definition in the campaign (see the table), so the bridge is the unfolding plus the
  identity of the closed forms, and no premise of the specification fails in Lean.
* Hypothesis `0 < h`. The frozen range is `h ≥ h0 = 2`; the campaign lemmas and every statement
  here use the weaker `0 < h`. For `h ≤ 0` the formula `A_h = 2 / (1 - e^{-2h})` is not the
  campaign `aH` (at `h = 0` the quotient is `2 / 0 = 0`), so some positivity hypothesis on `h` is
  forced; `0 < h` is the one the campaign already uses.
* The only other binding hypotheses are the ones the statements name (`u ∈ Icc 0 2`,
  `u ∈ Ioo 0 2`, smoothness of the test function); no other hypotheses are added.
* `r_h` and `R_h`. The source formulas are printed as `Asrc_EX04925`, `Nsrc_EX04925`,
  `rsrc_EX04925`, `Rsrc_EX04925` with `rsrc u = N u / (u * (2 - u))` at every real `u` (value `0`
  at `u = 0` and at `u = 2`, by Lean's `x / 0 = 0`, irrelevant to the integral). `Rsrc h u` is the
  interval integral of `rsrc h`, which exists because `rsrc h` agrees off `{0, 2}` with the
  continuous `integrand h`. `corr h u = Rsrc_EX04925 h u` is proved for every real `u`, which
  contains the requested `[0, 2]`; no condition on extensions off the interval is required.
* The derivative of `R_h` is stated as `HasDerivAt (corr h) (rsrc_EX04925 h u) u` for
  `u ∈ (0, 2)`. At the endpoints the one-sided statement is not needed.
* The H1 domain. The campaign has exactly one real angular distributional weak-derivative domain,
  `AngularH1` (unweighted: `L²(angHaar)`, test functions the smooth angular functions, pairing
  against `angHaar`). The specification's weighted domain is `u, g ∈ L²(μ_h)` with the same
  distributional pairing. It is encoded by the helper structure `IsAngularWeakDerivW_EX04925`
  whose `ibp` field is literally that of `IsAngularWeakDeriv` and whose `memLp` fields are for
  `circleReference h`. They agree because `q_h` is continuous and positive on the compact circle,
  hence bounded above and below, so `μ_h` and `angHaar` have the same null sets and the same
  `L²` classes (`memLp_circleReference_iff_EX04925`). A weak derivative defined by pairing
  against `μ_h` (a drift-corrected notion) is a different object and is neither used nor claimed.
* Weak derivatives are a.e. classes. The uniqueness is proved here from the torus uniqueness
  (`IsWeakGradient.ae_eq`) and the factor `2π` in `physGrad`; it is the statement of
  `DGPS.FiniteN.Tools.angularWeakDeriv_ae_eq` (`FiniteN/Tools/AngularWeakClassical.lean:25`),
  reproved here to avoid the extra import.
* "Real" means real valued, as in the campaign; no complex domain exists.
* `Φ_h` is not a campaign declaration. `logq h = -Φ_h`; hence `Zh`, `qAng` and `circleReference`
  are compared with the source formulas through `Phisrc_EX04925`.
* `driftB` and `groundPot` are functions on the lifted angle. The identification with `(log q_h)'`
  is through the lift `s ↦ log (qAng h ↑s)`, and the circle-level reading is
  `θ ↦ driftB h (angSec θ)`, whose angular derivative `angDeriv` is `deriv (driftB h) (angSec θ)`.
* The pushforward statement of `angHaar` is for every base point `a` of the fundamental interval
  `(a, a + 2π]`, not a single one.
* `engineeredReference` is on the unit-period torus and is not the circle measure; the relation
  is `rfl` through `angEquiv.symm`.
-/

open MeasureTheory Real Set Filter Topology
open scoped ContDiff ENNReal
open DGPS.Circle.AngularNormalization DGPS.Circle.StationaryFlux DGPS.Examples.EngineeredRankOne
  DGPS.Examples.EngineeredGroundState

namespace DGPS.Frontier.EX049

/-! ### Period and the Haar measure -/

theorem period_EX04925 (x y : ℝ) :
    (x : AngCircle) = (y : AngCircle) ↔ ∃ n : ℤ, x - y = n * (2 * π) := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, by rw [zsmul_eq_mul] at *; linarith⟩

theorem angHaar_eq_map_EX04925 (a : ℝ) :
    angHaar = (ENNReal.ofReal (2 * π))⁻¹ •
      Measure.map ((↑) : ℝ → AngCircle) (volume.restrict (Ioc a (a + 2 * π))) := by
  rw [(AddCircle.measurePreserving_mk (2 * π) a).map_eq, AddCircle.volume_eq_smul_haarAddCircle,
    smul_smul, ENNReal.inv_mul_cancel, one_smul]
  · exact (ENNReal.ofReal_pos.2 Real.two_pi_pos).ne'
  · exact ENNReal.ofReal_ne_top

theorem angHaar_eq_map_normalized_EX04925 (a : ℝ) :
    angHaar = Measure.map ((↑) : ℝ → AngCircle)
      ((ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Ioc a (a + 2 * π))) := by
  rw [Measure.map_smul]
  · exact angHaar_eq_map_EX04925 a
  · exact (AddCircle.measurePreserving_mk (2 * π) a).measurable.aemeasurable

theorem isProbabilityMeasure_normalized_EX04925 (a : ℝ) :
    IsProbabilityMeasure ((ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Ioc a (a + 2 * π))) := by
  refine ⟨?_⟩
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Ioc, show a + 2 * π - a = 2 * π by ring, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 Real.two_pi_pos).ne' ENNReal.ofReal_ne_top

theorem integral_angHaar_interval_EX04925 (a : ℝ) (f : AngCircle → ℝ) :
    ∫ θ, f θ ∂angHaar = (2 * π)⁻¹ * ∫ x in a..a + 2 * π, f (x : AngCircle) := by
  rw [AddCircle.intervalIntegral_preimage (2 * π) a f, AddCircle.integral_haarAddCircle]
  rfl

/-! ### The source formulas for `A_h`, `N_h`, `r_h`, `R_h` -/

noncomputable def Asrc_EX04925 (h : ℝ) : ℝ := 2 / (1 - Real.exp (-(2 * h)))

noncomputable def Nsrc_EX04925 (h u : ℝ) : ℝ := Asrc_EX04925 h * (1 - Real.exp (-(h * u))) - u

noncomputable def rsrc_EX04925 (h u : ℝ) : ℝ := Nsrc_EX04925 h u / (u * (2 - u))

noncomputable def Rsrc_EX04925 (h u : ℝ) : ℝ := ∫ s in (0:ℝ)..u, rsrc_EX04925 h s

theorem aH_eq_Asrc_EX04925 (h : ℝ) (hh : 0 < h) : aH h = Asrc_EX04925 h := by
  have hne : 1 - Real.exp (-(2 * h)) ≠ 0 := by
    have : Real.exp (-(2 * h)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have := aH_mul h hh
  rw [show -h * 2 = -(2 * h) by ring] at this
  unfold Asrc_EX04925
  rw [eq_div_iff hne]
  exact this

theorem numer_eq_Nsrc_EX04925 (h : ℝ) (hh : 0 < h) (v : ℝ) : numer h v = Nsrc_EX04925 h v := by
  unfold numer Nsrc_EX04925
  rw [aH_eq_Asrc_EX04925 h hh, neg_mul]

theorem integrand_eq_rsrc_EX04925 (h : ℝ) (hh : 0 < h) {v : ℝ} (h0 : v ≠ 0) (h2 : v ≠ 2) :
    integrand h v = rsrc_EX04925 h v := by
  rw [integrand_of_ne h h0 h2, numer_eq_Nsrc_EX04925 h hh]
  rfl

theorem corr_eq_Rsrc_EX04925 (h : ℝ) (hh : 0 < h) (u : ℝ) : corr h u = Rsrc_EX04925 h u := by
  unfold corr Rsrc_EX04925
  refine intervalIntegral.integral_congr_ae ?_
  have hc : ({0, 2} : Set ℝ).Countable := Set.toFinite _ |>.countable
  filter_upwards [hc.ae_notMem volume] with v hv _
  have h0 : v ≠ 0 := fun e => hv (by simp [e])
  have h2 : v ≠ 2 := fun e => hv (by simp [e])
  exact integrand_eq_rsrc_EX04925 h hh h0 h2

theorem hasDerivAt_corr_EX04925 (h : ℝ) (hh : 0 < h) {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (corr h) (rsrc_EX04925 h u) u := by
  have := (((contDiff_integrand h hh).continuous).integral_hasStrictDerivAt 0 u).hasDerivAt
  rwa [integrand_eq_rsrc_EX04925 h hh hu.1.ne' hu.2.ne] at this

/-! ### The reference density and measure -/

noncomputable def Phisrc_EX04925 (h : ℝ) (θ : AngCircle) : ℝ :=
  h * Uang θ + Rsrc_EX04925 h (Uang θ)

noncomputable def Zsrc_EX04925 (h : ℝ) : ℝ := ∫ θ, Real.exp (-Phisrc_EX04925 h θ) ∂angHaar

noncomputable def qsrc_EX04925 (h : ℝ) (θ : AngCircle) : ℝ :=
  (Zsrc_EX04925 h)⁻¹ * Real.exp (-Phisrc_EX04925 h θ)

theorem logq_eq_neg_Phisrc_EX04925 (h : ℝ) (hh : 0 < h) (θ : AngCircle) :
    logq h θ = -Phisrc_EX04925 h θ := by
  unfold logq Phisrc_EX04925
  rw [corr_eq_Rsrc_EX04925 h hh]
  ring

theorem Zh_eq_Zsrc_EX04925 (h : ℝ) (hh : 0 < h) : Zh h = Zsrc_EX04925 h := by
  unfold Zh Zsrc_EX04925
  simp_rw [logq_eq_neg_Phisrc_EX04925 h hh]

theorem qAng_eq_qsrc_EX04925 (h : ℝ) (hh : 0 < h) (θ : AngCircle) :
    qAng h θ = qsrc_EX04925 h θ := by
  unfold qAng qsrc_EX04925
  rw [logq_eq_neg_Phisrc_EX04925 h hh, Zh_eq_Zsrc_EX04925 h hh]

theorem circleReference_eq_EX04925 (h : ℝ) (hh : 0 < h) :
    circleReference h = angHaar.withDensity (fun θ => ENNReal.ofReal (qsrc_EX04925 h θ)) := by
  unfold circleReference
  simp_rw [qAng_eq_qsrc_EX04925 h hh]

theorem isProbabilityMeasure_circleReference_EX04925 (h : ℝ) (hh : 0 < h) :
    IsProbabilityMeasure (circleReference h) := by
  constructor
  unfold circleReference
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hi : Integrable (qAng h) angHaar := by
    unfold qAng
    exact ((continuous_exp.comp (continuous_logq h hh)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun θ => (qAng_pos h hh θ).le),
    integral_qAng h hh]
  simp

theorem Zh_interval_EX04925 (h : ℝ) (hh : 0 < h) :
    Zh h = (2 * π)⁻¹ * ∫ t in (0:ℝ)..2 * π,
      Real.exp (-(h * (1 - Real.cos t) + Rsrc_EX04925 h (1 - Real.cos t))) := by
  rw [Zh_eq_Zsrc_EX04925 h hh]
  unfold Zsrc_EX04925
  rw [integral_angHaar_interval_EX04925 0, zero_add]
  congr 1

/-! ### The weighted and Haar domains -/

theorem angularWeakDeriv_ae_eq_EX04925 {u g g' : AngCircle → ℝ} (h : IsAngularWeakDeriv u g)
    (h' : IsAngularWeakDeriv u g') : g =ᵐ[angHaar] g' := by
  have h1 := ((isWeakGradient_comp_iff u g).1 h).ae_eq ((isWeakGradient_comp_iff u g').1 h')
  have h2 : (g ∘ angEquiv) =ᵐ[haar 1] (g' ∘ angEquiv) := by
    filter_upwards [h1] with x hx
    have := congrArg (fun v => v 0) hx
    simp only [physGrad_apply] at this
    exact mul_left_cancel₀ Real.two_pi_pos.ne' this
  have := measurePreserving_angEquiv.symm.quasiMeasurePreserving.ae_eq_comp h2
  simpa [Function.comp_def] using this

theorem isAngularWeakDeriv_congr_EX04925 {u u' g g' : AngCircle → ℝ}
    (hu : u =ᵐ[angHaar] u') (hg : g =ᵐ[angHaar] g') (h : IsAngularWeakDeriv u g) :
    IsAngularWeakDeriv u' g' := by
  refine ⟨h.memLp.ae_eq hu, h.memLp_deriv.ae_eq hg, fun ψ hψ => ?_⟩
  have e1 : ∫ θ, u' θ * angDeriv ψ θ ∂angHaar = ∫ θ, u θ * angDeriv ψ θ ∂angHaar :=
    integral_congr_ae (by filter_upwards [hu] with θ hθ; rw [hθ])
  have e2 : ∫ θ, g' θ * ψ θ ∂angHaar = ∫ θ, g θ * ψ θ ∂angHaar :=
    integral_congr_ae (by filter_upwards [hg] with θ hθ; rw [hθ])
  rw [e1, e2]
  exact h.ibp ψ hψ

theorem exists_bounds_qAng_EX04925 (h : ℝ) (hh : 0 < h) :
    ∃ c C : ℝ, 0 < c ∧ ∀ θ, c ≤ qAng h θ ∧ qAng h θ ≤ C := by
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := AngCircle))
    (continuous_qAng h hh).continuousOn
  obtain ⟨x₁, -, hx₁⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty (α := AngCircle))
    (continuous_qAng h hh).continuousOn
  exact ⟨qAng h x₀, qAng h x₁, qAng_pos h hh x₀, fun θ => ⟨hx₀ (mem_univ θ), hx₁ (mem_univ θ)⟩⟩

theorem memLp_circleReference_iff_EX04925 (h : ℝ) (hh : 0 < h) (f : AngCircle → ℝ) :
    MemLp f 2 (circleReference h) ↔ MemLp f 2 angHaar := by
  obtain ⟨c, C, hc, hb⟩ := exists_bounds_qAng_EX04925 h hh
  have hup : circleReference h ≤ ENNReal.ofReal C • angHaar := by
    unfold circleReference
    rw [← withDensity_const]
    refine withDensity_mono (Eventually.of_forall fun θ => ?_)
    exact ENNReal.ofReal_le_ofReal (hb θ).2
  have hlow : ENNReal.ofReal c • angHaar ≤ circleReference h := by
    unfold circleReference
    rw [← withDensity_const]
    refine withDensity_mono (Eventually.of_forall fun θ => ?_)
    exact ENNReal.ofReal_le_ofReal (hb θ).1
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have hlow' : angHaar ≤ (ENNReal.ofReal c)⁻¹ • circleReference h := by
    rw [Measure.le_iff'] at hlow ⊢
    intro s
    have := hlow s
    simp only [Measure.smul_apply, smul_eq_mul] at this ⊢
    calc angHaar s = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c * angHaar s) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ _ := by gcongr
  constructor
  · intro hf
    exact (hf.smul_measure (ENNReal.inv_ne_top.2 hc0)).mono_measure hlow'
  · intro hf
    exact (hf.smul_measure ENNReal.ofReal_ne_top).mono_measure hup

theorem circleReference_ae_iff_EX04925 (h : ℝ) (hh : 0 < h) (f g : AngCircle → ℝ) :
    f =ᵐ[angHaar] g ↔ f =ᵐ[circleReference h] g := by
  have h1 : circleReference h ≪ angHaar := withDensity_absolutelyContinuous _ _
  have h2 : angHaar ≪ circleReference h :=
    withDensity_absolutelyContinuous' (((continuous_qAng h hh).measurable).ennreal_ofReal.aemeasurable)
      (Eventually.of_forall fun θ => by simpa using qAng_pos h hh θ)
  exact ⟨fun e => e.filter_mono h1.ae_le, fun e => e.filter_mono h2.ae_le⟩

/-- The weighted angular weak-derivative relation: `u` and `g` are in `L²(μ_h)` and `g` is the
distributional angular derivative of `u` (pairing against `angHaar` with smooth test functions). -/
structure IsAngularWeakDerivW_EX04925 (h : ℝ) (u g : AngCircle → ℝ) : Prop where
  memLp : MemLp u 2 (circleReference h)
  memLp_deriv : MemLp g 2 (circleReference h)
  ibp : ∀ ψ : AngCircle → ℝ, IsSmoothAngular ψ →
    ∫ θ, u θ * angDeriv ψ θ ∂angHaar = -∫ θ, g θ * ψ θ ∂angHaar

theorem isAngularWeakDerivW_iff_EX04925 (h : ℝ) (hh : 0 < h) (u g : AngCircle → ℝ) :
    IsAngularWeakDerivW_EX04925 h u g ↔ IsAngularWeakDeriv u g :=
  ⟨fun H => ⟨(memLp_circleReference_iff_EX04925 h hh u).1 H.memLp,
    (memLp_circleReference_iff_EX04925 h hh g).1 H.memLp_deriv, H.ibp⟩,
   fun H => ⟨(memLp_circleReference_iff_EX04925 h hh u).2 H.memLp,
    (memLp_circleReference_iff_EX04925 h hh g).2 H.memLp_deriv, H.ibp⟩⟩

theorem ibp_interval_iff_EX04925 (u g ψ : AngCircle → ℝ) :
    ∫ θ, u θ * angDeriv ψ θ ∂angHaar = -∫ θ, g θ * ψ θ ∂angHaar ↔
      ∫ x in (0:ℝ)..2 * π, u (x : AngCircle) * deriv (fun s : ℝ => ψ (s : AngCircle)) x
        = -∫ x in (0:ℝ)..2 * π, g (x : AngCircle) * ψ (x : AngCircle) := by
  have e1 := integral_lift_period (fun θ => u θ * angDeriv ψ θ)
  have e2 := integral_lift_period (fun θ => g θ * ψ θ)
  have f1 : lift (fun θ => u θ * angDeriv ψ θ)
      = fun x : ℝ => u (x : AngCircle) * deriv (fun s : ℝ => ψ (s : AngCircle)) x := by
    funext x; simp only [lift]; rw [angDeriv_coe]; rfl
  have f2 : lift (fun θ => g θ * ψ θ) = fun x : ℝ => g (x : AngCircle) * ψ (x : AngCircle) := rfl
  rw [f1] at e1
  rw [f2] at e2
  rw [e1, e2]
  have hp : (2 * π) ≠ 0 := Real.two_pi_pos.ne'
  constructor
  · intro H; rw [H]; ring
  · intro H; exact mul_left_cancel₀ hp (by linarith)

theorem isAngularWeakDeriv_iff_interval_EX04925 (u g : AngCircle → ℝ) :
    IsAngularWeakDeriv u g ↔ MemLp u 2 angHaar ∧ MemLp g 2 angHaar ∧
      ∀ ψ : AngCircle → ℝ, IsSmoothAngular ψ →
        ∫ x in (0:ℝ)..2 * π, u (x : AngCircle) * deriv (fun s : ℝ => ψ (s : AngCircle)) x
          = -∫ x in (0:ℝ)..2 * π, g (x : AngCircle) * ψ (x : AngCircle) :=
  ⟨fun H => ⟨H.memLp, H.memLp_deriv, fun ψ hψ => (ibp_interval_iff_EX04925 u g ψ).1 (H.ibp ψ hψ)⟩,
   fun H => ⟨H.1, H.2.1, fun ψ hψ => (ibp_interval_iff_EX04925 u g ψ).2 (H.2.2 ψ hψ)⟩⟩

/-! ### The drift and the ground potential -/

theorem log_qAng_lift_EX04925 (h : ℝ) (hh : 0 < h) (s : ℝ) :
    Real.log (qAng h (s : AngCircle)) = -Real.log (Zh h) + Lh h s := by
  have hZ := Zh_pos h hh
  have e : qAng h (s : AngCircle) = (Zh h)⁻¹ * Real.exp (Lh h s) := rfl
  rw [e, Real.log_mul (inv_ne_zero hZ.ne') (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]

theorem hasDerivAt_log_qAng_EX04925 (h : ℝ) (hh : 0 < h) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.log (qAng h (s : AngCircle))) (driftB h t) t := by
  have e : (fun s : ℝ => Real.log (qAng h (s : AngCircle))) = fun s => -Real.log (Zh h) + Lh h s :=
    funext (log_qAng_lift_EX04925 h hh)
  rw [e]
  exact (hasDerivAt_Lh h hh t).const_add _

theorem driftB_eq_deriv_log_qAng_EX04925 (h : ℝ) (hh : 0 < h) (t : ℝ) :
    driftB h t = deriv (fun s : ℝ => Real.log (qAng h (s : AngCircle))) t :=
  (hasDerivAt_log_qAng_EX04925 h hh t).deriv.symm

theorem groundPot_eq_log_qAng_EX04925 (h : ℝ) (hh : 0 < h) (t : ℝ) :
    groundPot h t = (deriv (fun s : ℝ => Real.log (qAng h (s : AngCircle))) t) ^ 2 / 4 +
      deriv (deriv (fun s : ℝ => Real.log (qAng h (s : AngCircle)))) t / 2 := by
  have e : deriv (fun s : ℝ => Real.log (qAng h (s : AngCircle))) = driftB h :=
    funext fun t => (driftB_eq_deriv_log_qAng_EX04925 h hh t).symm
  rw [e]
  rfl

theorem angDeriv_log_qAng_EX04925 (h : ℝ) (hh : 0 < h) (θ : AngCircle) :
    angDeriv (fun θ => Real.log (qAng h θ)) θ = driftB h (angSec θ) :=
  (driftB_eq_deriv_log_qAng_EX04925 h hh (angSec θ)).symm

theorem driftB_eq_rsrc_EX04925 (h : ℝ) (hh : 0 < h) (t : ℝ) :
    driftB h t = -(h + rsrc_EX04925 h (1 - Real.cos t)) * Real.sin t := by
  rw [driftB_eq h hh]
  by_cases hs : Real.sin t = 0
  · simp [hs]
  · have hsq := Real.sin_sq_add_cos_sq t
    have h0 : 1 - Real.cos t ≠ 0 := by
      intro e
      have hc : Real.cos t = 1 := by linarith
      rw [hc] at hsq
      exact hs (pow_eq_zero_iff two_ne_zero |>.1 (by linarith))
    have h2 : 1 - Real.cos t ≠ 2 := by
      intro e
      have hc : Real.cos t = -1 := by linarith
      rw [hc] at hsq
      exact hs (pow_eq_zero_iff two_ne_zero |>.1 (by linarith))
    rw [integrand_eq_rsrc_EX04925 h hh h0 h2]

theorem driftB_angSec_EX04925 (h : ℝ) (hh : 0 < h) (x : ℝ) :
    driftB h (angSec (x : AngCircle)) = driftB h x := by
  obtain ⟨n, hn⟩ := exists_angSec_eq x
  rw [hn]
  exact (driftB_periodic h hh).int_mul n x

theorem angDeriv_driftB_EX04925 (h : ℝ) (hh : 0 < h) (θ : AngCircle) :
    angDeriv (fun θ => driftB h (angSec θ)) θ = deriv (driftB h) (angSec θ) := by
  have e : (fun s : ℝ => driftB h (angSec (s : AngCircle))) = driftB h :=
    funext (driftB_angSec_EX04925 h hh)
  show deriv (fun s : ℝ => driftB h (angSec (s : AngCircle))) (angSec θ) = _
  rw [e]

/-! ### The public parts -/

theorem gate_ex049_25_bind_campaign_domain_named_source_objects_period_haar :
    (∀ x y : ℝ, (x : AngCircle) = (y : AngCircle) ↔ ∃ n : ℤ, x - y = n * (2 * π)) ∧
    IsProbabilityMeasure angHaar ∧
    (∀ a : ℝ, IsProbabilityMeasure
      ((ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Ioc a (a + 2 * π)))) ∧
    (∀ a : ℝ, angHaar = Measure.map ((↑) : ℝ → AngCircle)
      ((ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Ioc a (a + 2 * π)))) ∧
    (∀ (a : ℝ) (f : AngCircle → ℝ),
      ∫ θ, f θ ∂angHaar = (2 * π)⁻¹ * ∫ x in a..a + 2 * π, f (x : AngCircle)) :=
  ⟨period_EX04925, inferInstance, isProbabilityMeasure_normalized_EX04925,
    angHaar_eq_map_normalized_EX04925, integral_angHaar_interval_EX04925⟩

theorem gate_ex049_25_bind_campaign_domain_named_source_objects_h1_domain
    (h : ℝ) (hh : 0 < h) :
    (∀ u g : AngCircle → ℝ, IsAngularWeakDeriv u g ↔ MemLp u 2 angHaar ∧ MemLp g 2 angHaar ∧
      ∀ ψ : AngCircle → ℝ, IsSmoothAngular ψ →
        ∫ x in (0:ℝ)..2 * π, u (x : AngCircle) * deriv (fun s : ℝ => ψ (s : AngCircle)) x
          = -∫ x in (0:ℝ)..2 * π, g (x : AngCircle) * ψ (x : AngCircle)) ∧
    (∀ (ψ : AngCircle → ℝ) (s : ℝ),
      angDeriv ψ (s : AngCircle) = deriv (fun t : ℝ => ψ (t : AngCircle)) s) ∧
    (∀ u g g' : AngCircle → ℝ, IsAngularWeakDeriv u g → IsAngularWeakDeriv u g' →
      g =ᵐ[angHaar] g') ∧
    (∀ u g g' : AngCircle → ℝ, IsAngularWeakDeriv u g → IsAngularWeakDeriv u g' →
      g =ᵐ[circleReference h] g') ∧
    (∀ u u' g g' : AngCircle → ℝ, u =ᵐ[angHaar] u' → g =ᵐ[angHaar] g' →
      IsAngularWeakDeriv u g → IsAngularWeakDeriv u' g') ∧
    (∀ u g : AngCircle → ℝ, IsAngularWeakDerivW_EX04925 h u g ↔ IsAngularWeakDeriv u g) ∧
    (∀ u : AngCircle → ℝ, (∃ g, IsAngularWeakDerivW_EX04925 h u g) ↔ AngularH1 u) ∧
    (∀ f g : AngCircle → ℝ, f =ᵐ[angHaar] g ↔ f =ᵐ[circleReference h] g) ∧
    (∀ f : AngCircle → ℝ, MemLp f 2 (circleReference h) ↔ MemLp f 2 angHaar) ∧
    (∀ u g : AngCircle → ℝ, IsAngularWeakDeriv u g →
      Integrable (fun θ => u θ ^ 2) (circleReference h) ∧
        Integrable (fun θ => g θ ^ 2) (circleReference h)) ∧
    (∀ u g g' : AngCircle → ℝ, IsAngularWeakDeriv u g → IsAngularWeakDeriv u g' →
      ∫ θ, g θ ^ 2 ∂circleReference h = ∫ θ, g' θ ^ 2 ∂circleReference h) ∧
    (∀ u : AngCircle → ℝ, AngularH1 u ↔ MemH1 (u ∘ angEquiv)) := by
  have hae : ∀ u g g' : AngCircle → ℝ, IsAngularWeakDeriv u g → IsAngularWeakDeriv u g' →
      g =ᵐ[circleReference h] g' := fun u g g' H H' =>
    (circleReference_ae_iff_EX04925 h hh g g').1 (angularWeakDeriv_ae_eq_EX04925 H H')
  refine ⟨isAngularWeakDeriv_iff_interval_EX04925, angDeriv_coe,
    fun u g g' H H' => angularWeakDeriv_ae_eq_EX04925 H H', hae,
    fun u u' g g' hu hg H => isAngularWeakDeriv_congr_EX04925 hu hg H,
    isAngularWeakDerivW_iff_EX04925 h hh,
    fun u => exists_congr fun g => isAngularWeakDerivW_iff_EX04925 h hh u g,
    circleReference_ae_iff_EX04925 h hh, memLp_circleReference_iff_EX04925 h hh,
    fun u g H => ⟨((memLp_circleReference_iff_EX04925 h hh u).2 H.memLp).integrable_sq,
      ((memLp_circleReference_iff_EX04925 h hh g).2 H.memLp_deriv).integrable_sq⟩,
    fun u g g' H H' => integral_congr_ae ?_, angularH1_comp_iff⟩
  filter_upwards [hae u g g' H H'] with θ hθ
  rw [hθ]

theorem gate_ex049_25_bind_campaign_domain_named_source_objects_corr
    (h : ℝ) (hh : 0 < h) :
    aH h = Asrc_EX04925 h ∧
    (∀ v : ℝ, numer h v = Nsrc_EX04925 h v) ∧
    (∀ v ∈ Ioo (0:ℝ) 2, integrand h v = rsrc_EX04925 h v) ∧
    (∀ u ∈ Icc (0:ℝ) 2, corr h u = Rsrc_EX04925 h u) ∧
    (∀ u : ℝ, corr h u = Rsrc_EX04925 h u) ∧
    (∀ u ∈ Ioo (0:ℝ) 2, HasDerivAt (corr h) (rsrc_EX04925 h u) u) ∧
    (∀ u ∈ Ioo (0:ℝ) 2, deriv (corr h) u = rsrc_EX04925 h u) := by
  refine ⟨aH_eq_Asrc_EX04925 h hh, numer_eq_Nsrc_EX04925 h hh,
    fun v hv => integrand_eq_rsrc_EX04925 h hh hv.1.ne' hv.2.ne,
    fun u _ => corr_eq_Rsrc_EX04925 h hh u, corr_eq_Rsrc_EX04925 h hh,
    fun u hu => hasDerivAt_corr_EX04925 h hh hu,
    fun u hu => (hasDerivAt_corr_EX04925 h hh hu).deriv⟩

theorem gate_ex049_25_bind_campaign_domain_named_source_objects_reference
    (h : ℝ) (hh : 0 < h) :
    (∀ t : ℝ, Uang (t : AngCircle) = 1 - Real.cos t) ∧
    (∀ θ : AngCircle, logq h θ = -Phisrc_EX04925 h θ) ∧
    Zh h = Zsrc_EX04925 h ∧
    Zh h = (2 * π)⁻¹ * ∫ t in (0:ℝ)..2 * π,
      Real.exp (-(h * (1 - Real.cos t) + Rsrc_EX04925 h (1 - Real.cos t))) ∧
    0 < Zh h ∧
    (∀ θ : AngCircle, qAng h θ = qsrc_EX04925 h θ) ∧
    (∀ θ : AngCircle, 0 < qAng h θ) ∧
    ∫ θ, qAng h θ ∂angHaar = 1 ∧
    circleReference h = angHaar.withDensity (fun θ => ENNReal.ofReal (qsrc_EX04925 h θ)) ∧
    IsProbabilityMeasure (circleReference h) ∧
    (∀ F : AngCircle → ℝ, ∫ θ, F θ ∂circleReference h = ∫ θ, F θ * qAng h θ ∂angHaar) ∧
    DGPS.Models.engineeredReference h = (circleReference h).map angEquiv.symm :=
  ⟨drift_Uang, logq_eq_neg_Phisrc_EX04925 h hh, Zh_eq_Zsrc_EX04925 h hh,
    Zh_interval_EX04925 h hh, Zh_pos h hh, qAng_eq_qsrc_EX04925 h hh, qAng_pos h hh,
    integral_qAng h hh, circleReference_eq_EX04925 h hh,
    isProbabilityMeasure_circleReference_EX04925 h hh, integral_circleReference h hh, rfl⟩

theorem gate_ex049_25_bind_campaign_domain_named_source_objects_drift
    (h : ℝ) (hh : 0 < h) :
    (∀ s : ℝ, Real.log (qAng h (s : AngCircle)) = -Real.log (Zh h) + Lh h s) ∧
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => Real.log (qAng h (s : AngCircle))) (driftB h t) t) ∧
    (∀ t : ℝ, driftB h t = deriv (fun s : ℝ => Real.log (qAng h (s : AngCircle))) t) ∧
    (∀ t : ℝ, groundPot h t =
      (deriv (fun s : ℝ => Real.log (qAng h (s : AngCircle))) t) ^ 2 / 4 +
        deriv (deriv (fun s : ℝ => Real.log (qAng h (s : AngCircle)))) t / 2) ∧
    (∀ t : ℝ, driftB h t = -(h + rsrc_EX04925 h (1 - Real.cos t)) * Real.sin t) ∧
    Function.Periodic (driftB h) (2 * π) ∧
    Function.Periodic (groundPot h) (2 * π) ∧
    (∀ θ : AngCircle, angDeriv (fun θ => Real.log (qAng h θ)) θ = driftB h (angSec θ)) ∧
    (∀ θ : AngCircle, groundPot h (angSec θ) =
      (driftB h (angSec θ)) ^ 2 / 4 + angDeriv (fun θ => driftB h (angSec θ)) θ / 2) ∧
    (∀ x : ℝ, groundPot h (angSec (x : AngCircle)) = groundPot h x) := by
  refine ⟨log_qAng_lift_EX04925 h hh, hasDerivAt_log_qAng_EX04925 h hh,
    driftB_eq_deriv_log_qAng_EX04925 h hh, groundPot_eq_log_qAng_EX04925 h hh,
    driftB_eq_rsrc_EX04925 h hh, driftB_periodic h hh, groundPot_periodic h hh,
    angDeriv_log_qAng_EX04925 h hh, fun θ => ?_, groundPot_angSec h hh⟩
  unfold groundPot
  rw [angDeriv_driftB_EX04925 h hh]

theorem gate_ex049_25_bind_campaign_domain_named_source_objects (h : ℝ) (hh : 0 < h) :
    ((∀ x y : ℝ, (x : AngCircle) = (y : AngCircle) ↔ ∃ n : ℤ, x - y = n * (2 * π)) ∧
      IsProbabilityMeasure angHaar ∧
      (∀ a : ℝ, IsProbabilityMeasure
        ((ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Ioc a (a + 2 * π)))) ∧
      (∀ a : ℝ, angHaar = Measure.map ((↑) : ℝ → AngCircle)
        ((ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Ioc a (a + 2 * π)))) ∧
      (∀ (a : ℝ) (f : AngCircle → ℝ),
        ∫ θ, f θ ∂angHaar = (2 * π)⁻¹ * ∫ x in a..a + 2 * π, f (x : AngCircle))) ∧
    ((∀ u g : AngCircle → ℝ, IsAngularWeakDeriv u g ↔ MemLp u 2 angHaar ∧ MemLp g 2 angHaar ∧
        ∀ ψ : AngCircle → ℝ, IsSmoothAngular ψ →
          ∫ x in (0:ℝ)..2 * π, u (x : AngCircle) * deriv (fun s : ℝ => ψ (s : AngCircle)) x
            = -∫ x in (0:ℝ)..2 * π, g (x : AngCircle) * ψ (x : AngCircle)) ∧
      (∀ (ψ : AngCircle → ℝ) (s : ℝ),
        angDeriv ψ (s : AngCircle) = deriv (fun t : ℝ => ψ (t : AngCircle)) s) ∧
      (∀ u g g' : AngCircle → ℝ, IsAngularWeakDeriv u g → IsAngularWeakDeriv u g' →
        g =ᵐ[angHaar] g') ∧
      (∀ u g g' : AngCircle → ℝ, IsAngularWeakDeriv u g → IsAngularWeakDeriv u g' →
        g =ᵐ[circleReference h] g') ∧
      (∀ u u' g g' : AngCircle → ℝ, u =ᵐ[angHaar] u' → g =ᵐ[angHaar] g' →
        IsAngularWeakDeriv u g → IsAngularWeakDeriv u' g') ∧
      (∀ u g : AngCircle → ℝ, IsAngularWeakDerivW_EX04925 h u g ↔ IsAngularWeakDeriv u g) ∧
      (∀ u : AngCircle → ℝ, (∃ g, IsAngularWeakDerivW_EX04925 h u g) ↔ AngularH1 u) ∧
      (∀ f g : AngCircle → ℝ, f =ᵐ[angHaar] g ↔ f =ᵐ[circleReference h] g) ∧
      (∀ f : AngCircle → ℝ, MemLp f 2 (circleReference h) ↔ MemLp f 2 angHaar) ∧
      (∀ u g : AngCircle → ℝ, IsAngularWeakDeriv u g →
        Integrable (fun θ => u θ ^ 2) (circleReference h) ∧
          Integrable (fun θ => g θ ^ 2) (circleReference h)) ∧
      (∀ u g g' : AngCircle → ℝ, IsAngularWeakDeriv u g → IsAngularWeakDeriv u g' →
        ∫ θ, g θ ^ 2 ∂circleReference h = ∫ θ, g' θ ^ 2 ∂circleReference h) ∧
      (∀ u : AngCircle → ℝ, AngularH1 u ↔ MemH1 (u ∘ angEquiv))) ∧
    (aH h = Asrc_EX04925 h ∧
      (∀ v : ℝ, numer h v = Nsrc_EX04925 h v) ∧
      (∀ v ∈ Ioo (0:ℝ) 2, integrand h v = rsrc_EX04925 h v) ∧
      (∀ u ∈ Icc (0:ℝ) 2, corr h u = Rsrc_EX04925 h u) ∧
      (∀ u : ℝ, corr h u = Rsrc_EX04925 h u) ∧
      (∀ u ∈ Ioo (0:ℝ) 2, HasDerivAt (corr h) (rsrc_EX04925 h u) u) ∧
      (∀ u ∈ Ioo (0:ℝ) 2, deriv (corr h) u = rsrc_EX04925 h u)) ∧
    ((∀ t : ℝ, Uang (t : AngCircle) = 1 - Real.cos t) ∧
      (∀ θ : AngCircle, logq h θ = -Phisrc_EX04925 h θ) ∧
      Zh h = Zsrc_EX04925 h ∧
      Zh h = (2 * π)⁻¹ * ∫ t in (0:ℝ)..2 * π,
        Real.exp (-(h * (1 - Real.cos t) + Rsrc_EX04925 h (1 - Real.cos t))) ∧
      0 < Zh h ∧
      (∀ θ : AngCircle, qAng h θ = qsrc_EX04925 h θ) ∧
      (∀ θ : AngCircle, 0 < qAng h θ) ∧
      ∫ θ, qAng h θ ∂angHaar = 1 ∧
      circleReference h = angHaar.withDensity (fun θ => ENNReal.ofReal (qsrc_EX04925 h θ)) ∧
      IsProbabilityMeasure (circleReference h) ∧
      (∀ F : AngCircle → ℝ, ∫ θ, F θ ∂circleReference h = ∫ θ, F θ * qAng h θ ∂angHaar) ∧
      DGPS.Models.engineeredReference h = (circleReference h).map angEquiv.symm) ∧
    ((∀ s : ℝ, Real.log (qAng h (s : AngCircle)) = -Real.log (Zh h) + Lh h s) ∧
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => Real.log (qAng h (s : AngCircle))) (driftB h t) t) ∧
      (∀ t : ℝ, driftB h t = deriv (fun s : ℝ => Real.log (qAng h (s : AngCircle))) t) ∧
      (∀ t : ℝ, groundPot h t =
        (deriv (fun s : ℝ => Real.log (qAng h (s : AngCircle))) t) ^ 2 / 4 +
          deriv (deriv (fun s : ℝ => Real.log (qAng h (s : AngCircle)))) t / 2) ∧
      (∀ t : ℝ, driftB h t = -(h + rsrc_EX04925 h (1 - Real.cos t)) * Real.sin t) ∧
      Function.Periodic (driftB h) (2 * π) ∧
      Function.Periodic (groundPot h) (2 * π) ∧
      (∀ θ : AngCircle, angDeriv (fun θ => Real.log (qAng h θ)) θ = driftB h (angSec θ)) ∧
      (∀ θ : AngCircle, groundPot h (angSec θ) =
        (driftB h (angSec θ)) ^ 2 / 4 + angDeriv (fun θ => driftB h (angSec θ)) θ / 2) ∧
      (∀ x : ℝ, groundPot h (angSec (x : AngCircle)) = groundPot h x)) :=
  ⟨gate_ex049_25_bind_campaign_domain_named_source_objects_period_haar,
    gate_ex049_25_bind_campaign_domain_named_source_objects_h1_domain h hh,
    gate_ex049_25_bind_campaign_domain_named_source_objects_corr h hh,
    gate_ex049_25_bind_campaign_domain_named_source_objects_reference h hh,
    gate_ex049_25_bind_campaign_domain_named_source_objects_drift h hh⟩

end DGPS.Frontier.EX049
