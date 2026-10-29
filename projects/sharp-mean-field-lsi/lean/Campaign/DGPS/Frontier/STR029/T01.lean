import DGPS.Examples.ThreeSpeciesCircle.OrdinaryAllOptimizersMain
import DGPS.Circle.AngularNormalization

/-!
# Bindings

Bindings (source object or notion in the specification, the actual declaration with its
file:line, its type or binder list, and any discrepancy with the specification text; file paths
are relative to `Campaign/`):

| Source notion | Actual declaration (file:line) | Type / binders | Discrepancy |
|---|---|---|---|
| Hölder exponent `α` (fixed `1/2`) | `DGPS.Analysis.PeriodicHolder.HolderExponent` (`DGPS/Analysis/PeriodicHolder.lean:601`) | `class HolderExponent (α : ℝ) : Prop` with `pos : 0 < α`, `lt_one : α < 1` | the statements hold for every `[HolderExponent α]`, which contains `α = 1/2`; the instance is `holderExponent_half_STR02901` (a theorem, not an instance) |
| parameter `p = (p₀, p₁, p₂, p₃)` | `DGPS.Examples.ThreeSpeciesCircle.Par` (`DGPS/Examples/ThreeSpeciesCircle/OrdinaryRangeEquation.lean:97`) | `abbrev Par : Type := Fin 4 → ℝ`, coordinates `p 0, p 1, p 2, p 3` | none for the carrier; `Par` carries the sup norm, the specification the Euclidean norm `\|p\|`; `par_norm_equiv_STR02901` gives `‖p‖ ≤ \|p\| ≤ 2 ‖p‖` |
| chart space `W = E ∩ C^{2,α}` | `DGPS.Examples.ThreeSpeciesCircle.Wsp` (`OrdinaryRangeEquation.lean:100`), `DGPS.Analysis.PeriodicHolder.PH.orthSub` (`DGPS/Analysis/PeriodicHolder.lean:1167`), `PH` (`:644`) | `abbrev Wsp (α : ℝ) [HolderExponent α] : Type := PH.orthSub α 2`, a subspace of `PH α 2` | packet functions are `1`-periodic in `x` with `t = 2πx`; the specification's `w` is `2π`-periodic in `t`; identified by `wspToConcrete_STR02901` (bijection onto `{w // IsC2Alpha_STR02901 α w ∧ InE_STR02901 w}`, proved in `_carrier_equiv`) |
| `C^{2,α}` norm `‖u‖∞+‖u'‖∞+‖u''‖∞+[u'']_α` | `DGPS.Analysis.PeriodicHolder.phNorm` (`PeriodicHolder.lean:83`), norm instance on `PH` (`:671`), `supNorm` (`:18`), `holderSeminorm` (`:32`) | `phNorm α 2 f = supNorm f + (supNorm f' + (supNorm f'' + holderSeminorm α f''))` in the variable `x`, seminorm with `\|x-y\|` | the specification uses `t = 2πx` and the circular distance; `c2Norm_STR02901` and `circHolder_STR02901` are the concrete versions; the two norms are not equal but comparable: `c2Norm ≤ ‖f‖` and `K ‖f‖ ≤ c2Norm`, `K = (2π)⁻² (2π)⁻ᵅ` (`_carrier_equiv`); `supNorm`, `holderSeminorm` are junk `0` on unbounded functions, never reached for `C^{2,α}` periodic functions |
| `E` = closed complement of `1, cos t, sin t` | `PH.orthSub` (`PeriodicHolder.lean:1167`) | carrier `{f \| PH.integral k f = 0 ∧ PH.cosCoeff k 1 f = 0 ∧ PH.sinCoeff k 1 f = 0}` | the concrete form is `InE_STR02901 w` (`∫ w dm = ∫ w cos t dm = ∫ w sin t dm = 0`); equivalence `mem_orthSub_iff_InE_STR02901` |
| `ρ(h, u)` and `m(dt) = dt/(2π)` | `DGPS.Examples.ThreeSpeciesCircle.rho` (`OrdinaryRangeEquation.lean:145`), `phiCLM` (`:140`), `PH.normMap` (`PeriodicHolder.lean:957`), `PH.expMap` (`:862`), `PH.integral` (`:937`) | `rho α : Par × Wsp α → PH α 0`, `rho α x = PH.normMap 0 (phiCLM x)` | `rho` is a function of `x`; `rhoT_STR02901`, `meanT_STR02901`, `uT_STR02901` are the `t`-versions and `rho_val_STR02901` proves `(rho α x).val s = rhoT (x.1 2) (uT (x.1 0) (x.1 1) (wT w)) (2π s)` |
| absolute density `ρ` | `DGPS.AbsoluteDensity` (`DGPS/Foundations/AbsoluteDensity.lean:35`), `DGPS.AbsoluteDensity.density` (`:42`), `DGPS.densityMeasure` (`:75`) | `structure AbsoluteDensity (d : ℕ)` with `sqrt`, `sqrt_mem`, `sqrt_nonneg`, `mass_one`; `density x = sqrt x ^ 2` | none; `densityMeasure ρ` is a `ProbabilityMeasure (Torus 1)` |
| Haar measure, torus, lift | `DGPS.haar` (`DGPS/Foundations/Torus.lean:35`), `Torus` (`:32`), `torusLift` (`:41`) | `haar d : Measure (Torus d)`, `torusLift : (Fin d → ℝ) → Torus d` | the packet states densities at `torusLift (fun _ => s)`; transported to `angHaar` by `density_ae_angular_STR02901` |
| angular circle, `m(dt)`, `t ∈ [0, 2π)` | `DGPS.Circle.AngularNormalization.AngCircle` (`DGPS/Circle/AngularNormalization.lean:24`), `angHaar` (`:26`), `angEquiv` (`:39`), `angSec` (`:60`) | `AngCircle := AddCircle (2π)`, `angEquiv : Torus 1 ≃ᵐ AngCircle`, `angSec θ ∈ [0, 2π)` | none; `angSec_angEquiv : angSec (angEquiv x) = 2π * secT x 0` |
| `a₀ = 4π²` | `DGPS.Circle.AngularNormalization.a0` (`AngularNormalization.lean:224`) | `a0 : ℝ := 4 * π ^ 2` | the campaign has four definitions, all `4π²` and definitionally equal: `DGPS.Circle.AngularNormalization.a0` (`:224`), `DGPS.Analysis.CircleMoments.a0` (`DGPS/Analysis/CircleMoments.lean:500`), `DGPS.a0` (`DGPS/Analysis/BoundedPerturbation.lean:35`), `DGPS.Examples.ThreeSpeciesCircle.a0` (`DGPS/Examples/ThreeSpeciesCircle/ElementaryModel.lean:17`); the first is used |
| reference `q_h` | `DGPS.Examples.ThreeSpeciesCircle.referenceDensity` (`DGPS/Examples/ThreeSpeciesCircle/Model.lean:247`), `threefoldReference` (`:264`), `ordinaryReference` (`DGPS/Examples/ThreeSpeciesCircle/OrdinaryOptimizers.lean:97`) | `referenceDensity h : Torus 1 → ℝ`; `ordinaryReference h : BoundedPositiveReference 1` | `qAng_STR02901 h θ = referenceDensity h (angEquiv.symm θ)` is the angular copy |
| entropy `H_h(ρ)` | `DGPS.Examples.ThreeSpeciesCircle.ordinaryEntropy` (`OrdinaryOptimizers.lean:259`), `DGPS.relativeEntropy` (`DGPS/Foundations/RelativeEntropy.lean:26`) | `ordinaryEntropy (h : ℝ) (ρ : AbsoluteDensity 1) : ℝ≥0∞ := relativeEntropy (densityMeasure ρ) (threefoldReference h)` | value in `ℝ≥0∞`; equals `ofReal (∫ g² log g² q_h dm)` (`_entropy`) |
| Fisher information `I_h(ρ)` | `DGPS.Examples.ThreeSpeciesCircle.ordinaryFisher` (`OrdinaryOptimizers.lean:193`), `DGPS.ordinaryRelativeFisher` (`DGPS/Analysis/RelativeFisher.lean:472`) | `ordinaryFisher h ρ : ℝ≥0∞ := ordinaryRelativeFisher (densityMeasure ρ) (ordinaryReference h)` | physical normalization: `ordinaryFisher = ofReal a₀ * angFisher` (`_fisher`); `ordinaryRelativeFisher` is `⊤` outside the finite-information domain |
| `g = √(ρ / q_h)` | `DGPS.Examples.ThreeSpeciesCircle.str025_u` (`OrdinaryOptimizers.lean:966`), `str025_grad` (`:969`) | `str025_u h ρ : Torus 1 → ℝ` | `gAng_STR02901 h ρ θ = str025_u h ρ (angEquiv.symm θ)` is the angular copy; weak derivative `gDerivAng_STR02901` |
| quotient `I/(2H)` | `DGPS.Examples.ThreeSpeciesCircle.str025_quot` (`OrdinaryOptimizers.lean:1411`) | `str025_quot h ρ : ℝ≥0∞ := ordinaryFisher h ρ / (2 * ordinaryEntropy h ρ)` | physical quotient is `a₀` times the angular quotient `angQuot_STR02901` (`_quotient`) |
| angular `H¹` and weak derivative | `DGPS.Circle.AngularNormalization.IsAngularWeakDeriv` (`AngularNormalization.lean:134`), `AngularH1` (`:140`), `physGrad` (`:143`) | `structure IsAngularWeakDeriv (u g : AngCircle → ℝ) : Prop`, `AngularH1 u := ∃ g, IsAngularWeakDeriv u g` | none |
| angular Fisher `4∫ g'² q_h dm` | `angFisher_STR02901` (this file) | `angFisher_STR02901 h g : ℝ≥0∞ := ⨅ (G) (_ : IsAngularWeakDeriv g G), 4 * ∫⁻ ofReal (qAng h θ) * ‖G θ‖ₑ ^ 2` | no angular Fisher information with weight `q_h` exists in the campaign; defined here with value `⊤` when `g ∉ H¹`; unique up to a.e. (`angDeriv_unique_STR02901`) |
| angular entropy `∫ g² log g² q_h dm` | `angEntropy_STR02901` (this file) | `angEntropy_STR02901 h g : ℝ := ∫ g θ ^ 2 * log (g θ ^ 2) * qAng h θ ∂angHaar` | `z log z` at `0` is `0` by the Mathlib convention `log 0 = 0` |
| angular admissible domain | `AngDomain_STR02901` (this file) | nonnegative periodic `H¹` `g` with `∫ g² q_h dm = 1` | none |
| finite competitor, zero deficit | `FiniteInfo_STR02901`, `ZeroDeficit_STR02901` (this file) | `FiniteInfo h ν := IsProbabilityMeasure ν ∧ ordinaryRelativeFisher ν (ordinaryReference h) ≠ ⊤` | the packet has no Lean "ordinary deficit"; `ZeroDeficit h lam ν` is `FiniteInfo ∧ (I).toReal - 2 lam (H).toReal = 0` |
| printed STR028 chart representation | `DGPS.Examples.ThreeSpeciesCircle.IsChartRep_STR028b3` (`DGPS/Examples/ThreeSpeciesCircle/OrdinaryAllOptimizersMain.lean:244`) | `IsChartRep_STR028b3 (h : ℕ → ℝ) (ρ : ℕ → AbsoluteDensity 1) (x : ℕ → Par × Wsp α) : Prop` | `p₃` is stated through `1 + p₃ = (str025_quot).toReal / (4π²)`; `chart_rate_coordinate_STR02901` proves the form `p₃ = I_ang / (2 H_ang) - 1` |
| printed STR028 theorem | `DGPS.Examples.ThreeSpeciesCircle.threefold_allOptimizers_near_three_minima` (`OrdinaryAllOptimizersMain.lean:406`) | `(h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ᶠ j, h j ≠ 0) (ρ) (hpos) (hmin) (α)`, conclusion `∃ x, IsChartRep_STR028b3 h ρ x ∧ ∀ η > 0, ∀ᶠ j, ∃ A B, …` | none; its witness is reused, not rebuilt |
| amplitude minima `(2,0), (-1,±√3)` | `DGPS.Examples.ThreeSpeciesCircle.reducedQuotient` (`DGPS/Examples/ThreeSpeciesCircle/ReducedQuartic.lean:47`), `reducedQuotient_exact_minimizers` (`:259`) | `reducedQuotient A B = -16/15 ↔ (A,B) ∈ {(2,0), (-1,√3), (-1,-√3)}` for `A² + B² ≠ 0` | the printed theorem localizes near the level set `reducedQuotient = -16/15`; the explicit three points come from the fourth conjunct of `reducedQuotient_exact_minimizers` |

Task id: STR029.01 (node STR029; frontier unit; size U, open interface; verification V3; flags
GATE, XH).
Title: Bind the common optimizer witness and the absolute variational domain.

Provides (every declaration is in the namespace `DGPS.Frontier.STR029`):
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational`:
  for every sequence `h_n → 0` with `h_n ≠ 0` eventually and every sequence `ρ_n` of
  positive-entropy global optimizers (the hypotheses of the printed STR028 theorem), one sequence
  `x_n = (p_n, w_n) ∈ Par × Wsp α` satisfies the printed STR028 conclusion (`IsChartRep_STR028b3`
  together with the amplitude localization) and also: amplitude localization at the three
  explicit points; `p_{n,2} = h_n`; `p_{n,3} = I/(2H) - 1` in angular units; eventually the
  angular a.e. identity `ρ_n = ρ(h_n, p_{n,0} cos t + p_{n,1} sin t + w_n)`;
  `|p_n| + ‖w_n‖_{C^{2,α}} → 0`; `w_n` concrete `C^{2,α}`, `2π`-periodic and in `E`; and `g_n`
  angular admissible, of positive entropy, minimizing the angular quotient.
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational_carrier_equiv`:
  the packet chart space is in bijection with the
  concrete `E ∩ C^{2,α}`, the bijection is `f ↦ (t ↦ f(t/2π))`, and the norms are comparable.
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational_norm_equiv`:
  the sup norm and the Euclidean norm on `Par` are
  equivalent, and `x_n → 0` is equivalent to `|p_n| + ‖w_n‖_{C^{2,α}} → 0`.
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational_rho_val`:
  the packet density `rho α x` at `s` is the concrete
  `ρ(p₂, p₀ cos t + p₁ sin t + w)` at `t = 2π s`.
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational_positive_log`:
  `ρ(h, u)` is positive for continuous `u`, with
  logarithm `h cos 3t + u(t) - log ∫ e^{h cos 3s + u(s)} dm`.
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational_entropy`:
  `ordinaryEntropy` is `ofReal` of the angular entropy
  `∫ g² log g² q_h dm`, which is nonnegative.
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational_fisher`:
  `ordinaryFisher` is `ofReal a₀` times the angular Fisher
  information `4 ∫ g'² q_h dm`, which is finite.
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational_fisher_formula`:
  the angular Fisher value is `4 ∫ q_h G²` for any
  weak derivative `G`, and `⊤` when `g ∉ H¹`.
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational_domain`:
  absolute densities correspond to angular admissible `g`
  (surjectively), and a.e. equality of densities is a.e. equality of the `g`'s.
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational_quotient`:
  the physical quotient is `a₀` times the angular
  quotient; the chart rate coordinate is the angular quotient.
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational_optimizer_transfer`:
  global optimality among positive-entropy
  absolute densities is equivalent to global optimality among positive-entropy angular
  admissible `g`.
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational_finite_competitor`:
  finite-information measures are exactly the
  density measures of absolute densities; equal density measures are a.e.-equal densities.
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational_zero_deficit_abs`:
  a zero-deficit competitor is the density
  measure of an absolute density with real `I - 2 lam H = 0`.
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational_zero_deficit_angular`:
  in angular variables the deficit is
  `a₀ (I_ang - 2 (lam/a₀) H_ang)`.
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational_zero_deficit_ennreal`:
  for `0 ≤ lam`, zero deficit is finite
  information plus `I = ofReal (2 lam) * H` in `[0, ⊤]`.
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational_zero_entropy`:
  entropy zero means `g = 1` a.e., and forces zero
  Fisher information.
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational_zero_entropy_measure`:
  a finite-information measure of relative
  entropy zero is `q_h` with zero Fisher information.
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational_reference`:
  `q_h` has zero deficit at every rate.
* `DGPS.Frontier.STR029.gate_str029_01_bind_common_optimizer_witness_absolute_variational_zero_deficit_dichotomy`:
  a zero-deficit competitor is either `q_h`
  or the density measure of an absolute density of positive entropy with quotient `lam`.

R5 notes:
* No hypothesis is added to those of the printed STR028 theorem
  `threefold_allOptimizers_near_three_minima`: `h_n → 0`, `h_n ≠ 0` eventually, `ρ_n` of positive
  entropy and global minimality of `I/(2H)` among positive-entropy absolute densities, and
  `[HolderExponent α]`. The fixed `α = 1/2` of the specification is the case
  `holderExponent_half_STR02901`; the theorems are proved for every `α`.
* The witness is the one produced by the printed theorem, so its conclusion
  (`IsChartRep_STR028b3` and the amplitude localization) is preserved by construction; the new
  conclusions are derived from the same `x`. The conclusion about the three explicit points uses
  the exact minimizer list of `reducedQuotient_exact_minimizers`, with `A² + B² ≠ 0` supplied by
  the printed conclusion.
* `p_{n,2} = h_n` and `p_{n,3} = I/(2H) - 1` hold for every `n` (the specification asks for
  "eventually"); the quantity `I_{h_n}(ρ_n)/(2 H_{h_n}(ρ_n))` is read in angular units: with
  `g = √(ρ / q_h)`, `I = 4 ∫ g'² q_h dm` and `H = ∫ g² log g² q_h dm` for the angular measure
  `m(dt) = dt/(2π)`. The physical `ordinaryFisher` equals `a₀` times this `I`, and
  `ordinaryEntropy` equals `H`, so `str025_quot / a₀ = I/(2H)` and the packet's
  `1 + p₃ = str025_quot / (4π²)` is exactly `p₃ = I/(2H) - 1` (`_quotient`).
* Variables. The packet works in the unit-period variable `x` with `t = 2πx`; the specification
  works in `t`. The a.e. identity is therefore stated over `angHaar` with the section
  `angSec θ ∈ [0, 2π)`, derived from the packet identity which is quantified over unit-period
  representatives `torusLift (fun _ => s) = y`; it holds eventually, as in `IsChartRep_STR028b3`.
  The concrete function is `w_n(t) = (x_n).2 (t/2π)` (`wT_STR02901`).
* Carriers. `Par` is literally `Fin 4 → ℝ`. `Wsp α` is not literally the concrete space of
  `2π`-periodic functions of `t`; the explicit bijection `wspToConcrete_STR02901` onto
  `{w // IsC2Alpha_STR02901 α w ∧ InE_STR02901 w}` is proved. The concrete norm (circular-distance
  Hölder seminorm of `w''`) is not isometric to the packet norm; `c2Norm ≤ ‖f‖` with constant
  `1` and `K ‖f‖ ≤ c2Norm` with `K = (2π)⁻² (2π)⁻ᵅ`. The Euclidean `|p|` and the sup norm of `Par`
  differ by a factor at most `2`. Hence "`x_n → 0` in the packet" and "`|p_n| + ‖w_n‖_{C^{2,α}} → 0`"
  are equivalent (`_norm_equiv`), and the main theorem states the latter for the concrete norms.
  For `2π`-periodic Hölder functions the circular and the real-line Hölder seminorms agree
  (`circHolder_eq_holderSeminorm_STR02901`).
* Domain. The compiled absolute-domain problem (absolute densities, `ordinaryEntropy`,
  `ordinaryFisher`) agrees with the angular problem on nonnegative periodic `H¹` functions
  `g = √(ρ/q_h)` with `∫ g² q_h dm = 1`: every absolute density gives such a `g`, every such `g`
  comes from an absolute density, and a.e. equality of the densities is a.e. equality of the `g`'s
  (`_domain`). Units: entropy is unchanged, Fisher information gains the factor `a₀` (`_entropy`,
  `_fisher`). Optimizer transfer is `_optimizer_transfer`; the main theorem includes that `g_n`
  is a global angular optimizer.
* Convention outside the finite-information domain. `ordinaryRelativeFisher ν P = ⊤` when `ν` is
  not absolutely continuous or the relative square root is not in `H¹`; `angFisher_STR02901 = ⊤`
  when `g` has no weak derivative. A competitor has finite information exactly when it is the
  density measure of an absolute density (`_finite_competitor`), and the deficit
  `I - 2 lam H` is formed only there, with `ENNReal.toReal` of finite numbers (the entropy of a
  finite-information measure is finite, `finiteInfo_entropy_ne_top_STR02901`); no `∞ - ∞` arises.
  For `0 ≤ lam` the same condition reads `I = ofReal (2 lam) * H` in `ℝ≥0∞`
  (`_zero_deficit_ennreal`).
* Zero deficit. The packet has no declaration named as a deficit; `ZeroDeficit_STR02901` is
  defined in this file as `FiniteInfo ∧ I.toReal - 2 lam H.toReal = 0`. Every zero-deficit
  density is covered by `_zero_deficit_abs`, `_zero_deficit_angular` and `_zero_deficit_dichotomy`;
  the entropy-zero branch is `q_h` itself (`_zero_entropy`, `_zero_entropy_measure`,
  `_reference`), the other branch has positive entropy and quotient `lam`.
* Equality convention. Densities are identified by the campaign's a.e. identity
  `ρ.density =ᵐ[haar 1] ρ'.density` (`densityMeasure_eq_iff_STR02901`, `gAng_ae_eq_iff_STR02901`).
  The positive smooth representative of the distinguished branches is `ρ(h, u)` with
  continuous `u = p₀ cos t + p₁ sin t + w` (`_positive_log`): it is strictly positive and its
  logarithm is `h cos 3t + u - log ∫ e^{h cos 3s + u(s)} dm`; the density identity of the main
  theorem identifies `ρ_n` with it a.e.
* Four definitions of `a₀` exist in the campaign (all `4π²`, listed in the Bindings table);
  every statement uses `DGPS.Circle.AngularNormalization.a0`. Two theorems called
  `circleEntropy_eq` also exist (`DGPS/Examples/ThreeSpeciesCircle/OrdinaryOptimizers.lean:262`
  and `DGPS/Circle/AngularNormalization.lean:408`); neither is used by name here.
* `z log z` at `0` is `0` through `Real.log 0 = 0`. The angular entropy is a Bochner integral,
  and `ordinaryEntropy_eq_angEntropy_STR02901` proves that `ordinaryEntropy` is its `ofReal`, so
  no integrability hypothesis is needed for the bridge.
* The proof is complete and uses only the standard foundations (`propext`, `Classical.choice`,
  `Quot.sound`); no equality between the
  upstream `rangeMap` and a variational range map is claimed or needed.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic
  DGPS.Examples.ThreeSpeciesCircle DGPS.Circle.AngularNormalization

namespace DGPS.Frontier.STR029

/-- Circular distance on `ℝ / 2πℤ`. -/
noncomputable def circDist_STR02901 (s t : ℝ) : ℝ :=
  dist ((s : ℝ) : AddCircle (2 * Real.pi)) ((t : ℝ) : AddCircle (2 * Real.pi))

theorem circDist_eq_STR02901 (s t : ℝ) :
    circDist_STR02901 s t =
      |s - t - ((round ((2 * Real.pi)⁻¹ * (s - t)) : ℤ) : ℝ) * (2 * Real.pi)| := by
  unfold circDist_STR02901
  rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq]

theorem circDist_nonneg_STR02901 (s t : ℝ) : 0 ≤ circDist_STR02901 s t := dist_nonneg

theorem circDist_le_abs_STR02901 (s t : ℝ) : circDist_STR02901 s t ≤ |s - t| := by
  unfold circDist_STR02901
  rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq' (p := 2 * Real.pi) (by positivity)]
  have h := round_le ((2 * Real.pi)⁻¹ * (s - t)) 0
  have h2 : (0:ℝ) < 2 * Real.pi := by positivity
  calc 2 * Real.pi * |(2 * Real.pi)⁻¹ * (s - t) - (round ((2 * Real.pi)⁻¹ * (s - t)) : ℝ)|
      ≤ 2 * Real.pi * |(2 * Real.pi)⁻¹ * (s - t) - ((0 : ℤ) : ℝ)| :=
        mul_le_mul_of_nonneg_left h h2.le
    _ = |s - t| := by
        rw [Int.cast_zero, sub_zero, abs_mul, abs_inv, abs_of_pos h2]
        field_simp

/-- Circular-Hölder boundedness. -/
def CircHolderBdd_STR02901 (α : ℝ) (g : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s t, |g s - g t| ≤ C * circDist_STR02901 s t ^ α

/-- Circular-distance Hölder seminorm. -/
noncomputable def circHolder_STR02901 (α : ℝ) (g : ℝ → ℝ) : ℝ :=
  ⨆ p : ℝ × ℝ, |g p.1 - g p.2| / circDist_STR02901 p.1 p.2 ^ α

theorem circHolder_eq_holderSeminorm_STR02901 {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ}
    (hper : Function.Periodic g (2 * Real.pi)) (hb : HolderBdd α g) :
    circHolder_STR02901 α g = holderSeminorm α g := by
  obtain ⟨C, hC0, hC⟩ := hb
  have hbT : BddAbove (Set.range fun p : ℝ × ℝ => |g p.1 - g p.2| / |p.1 - p.2| ^ α) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨p, rfl⟩
    by_cases hp : p.1 = p.2
    · simp [hp, hC0]
    · have : 0 < |p.1 - p.2| ^ α := Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr hp)) _
      rw [div_le_iff₀ this]
      exact hC _ _
  have hS : ∀ s t : ℝ, ∃ q : ℝ × ℝ,
      |g s - g t| / circDist_STR02901 s t ^ α = |g q.1 - g q.2| / |q.1 - q.2| ^ α := by
    intro s t
    set n : ℤ := round ((2 * Real.pi)⁻¹ * (s - t)) with hn
    refine ⟨(s, t + n * (2 * Real.pi)), ?_⟩
    have h1 : g (t + n * (2 * Real.pi)) = g t := (hper.int_mul n) t
    have h2 : |s - (t + n * (2 * Real.pi))| = circDist_STR02901 s t := by
      rw [circDist_eq_STR02901]; congr 1; ring
    simp only [h1, h2]
  have hTS : ∀ s t : ℝ, |g s - g t| / |s - t| ^ α ≤ |g s - g t| / circDist_STR02901 s t ^ α := by
    intro s t
    by_cases hc : circDist_STR02901 s t = 0
    · have : g s = g t := by
        rw [circDist_eq_STR02901] at hc
        have hc' : s - t - ((round ((2 * Real.pi)⁻¹ * (s - t)) : ℤ) : ℝ) * (2 * Real.pi) = 0 :=
          abs_eq_zero.mp hc
        have : s = t + ((round ((2 * Real.pi)⁻¹ * (s - t)) : ℤ) : ℝ) * (2 * Real.pi) := by linarith
        rw [this]; exact (hper.int_mul _) t
      simp [this]
    · have hc0 : 0 < circDist_STR02901 s t := lt_of_le_of_ne (circDist_nonneg_STR02901 s t) (Ne.symm hc)
      exact div_le_div_of_nonneg_left (abs_nonneg _) (Real.rpow_pos_of_pos hc0 _)
        (Real.rpow_le_rpow (circDist_nonneg_STR02901 s t) (circDist_le_abs_STR02901 s t) hα.le)
  have hbS : BddAbove (Set.range fun p : ℝ × ℝ =>
      |g p.1 - g p.2| / circDist_STR02901 p.1 p.2 ^ α) := by
    refine ⟨holderSeminorm α g, ?_⟩
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, hq⟩ := hS p.1 p.2
    simp only [hq]
    exact le_ciSup hbT q
  apply le_antisymm
  · refine ciSup_le fun p => ?_
    obtain ⟨q, hq⟩ := hS p.1 p.2
    simp only [hq]
    exact le_ciSup hbT q
  · refine ciSup_le fun p => ?_
    exact (hTS p.1 p.2).trans (le_ciSup hbS p)

theorem circHolderBdd_iff_STR02901 {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ}
    (hper : Function.Periodic g (2 * Real.pi)) :
    CircHolderBdd_STR02901 α g ↔ HolderBdd α g := by
  constructor
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C, hC0, fun s t => (hC s t).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (circDist_nonneg_STR02901 s t) (circDist_le_abs_STR02901 s t) hα.le) hC0
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C, hC0, fun s t => ?_⟩
    set n : ℤ := round ((2 * Real.pi)⁻¹ * (s - t)) with hn
    have h1 : g (t + n * (2 * Real.pi)) = g t := (hper.int_mul n) t
    have h2 : |s - (t + n * (2 * Real.pi))| = circDist_STR02901 s t := by
      rw [circDist_eq_STR02901]; congr 1; ring
    have := hC s (t + n * (2 * Real.pi))
    rwa [h1, h2] at this


/-! ### Dilations -/

theorem supNorm_dil_STR02901 {c : ℝ} (hc : c ≠ 0) (φ : ℝ → ℝ) :
    supNorm (fun t => φ (c * t)) = supNorm φ := by
  unfold supNorm
  exact (mul_left_surjective₀ hc).iSup_comp (fun y => |φ y|)

theorem supNorm_scale_STR02901 {c : ℝ} (hc : c ≠ 0) (a : ℝ) (φ : ℝ → ℝ) :
    supNorm (fun t => a * φ (c * t)) = |a| * supNorm φ := by
  unfold supNorm
  rw [Real.mul_iSup_of_nonneg (abs_nonneg a)]
  have h := (mul_left_surjective₀ hc).iSup_comp (fun y => |a| * |φ y|)
  simp only [abs_mul]
  exact h

theorem holderSeminorm_scale_STR02901 {α c : ℝ} (hc : c ≠ 0) (a : ℝ) (φ : ℝ → ℝ) :
    holderSeminorm α (fun t => a * φ (c * t)) = |a| * |c| ^ α * holderSeminorm α φ := by
  unfold holderSeminorm
  rw [mul_assoc, Real.mul_iSup_of_nonneg (Real.rpow_nonneg (abs_nonneg c) _),
    Real.mul_iSup_of_nonneg (abs_nonneg a)]
  let e : ℝ × ℝ ≃ ℝ × ℝ := (Equiv.mulLeft₀ c hc).prodCongr (Equiv.mulLeft₀ c hc)
  rw [← e.iSup_comp (g := fun p : ℝ × ℝ => |a| * (|c| ^ α * (|φ p.1 - φ p.2| / |p.1 - p.2| ^ α)))]
  refine iSup_congr fun p => ?_
  have hne : |c| ^ α ≠ 0 := (Real.rpow_pos_of_pos (abs_pos.mpr hc) _).ne'
  have h1 : |c * p.1 - c * p.2| = |c| * |p.1 - p.2| := by rw [← mul_sub, abs_mul]
  have h2 : |a * φ (c * p.1) - a * φ (c * p.2)| = |a| * |φ (c * p.1) - φ (c * p.2)| := by
    rw [← mul_sub, abs_mul]
  have he : ∀ x, (Equiv.mulLeft₀ c hc) x = c * x := fun x => rfl
  simp only [e, Equiv.prodCongr_apply, Prod.map, he, h1, h2]
  rw [Real.mul_rpow (abs_nonneg c) (abs_nonneg _), ← mul_div_assoc, mul_div_mul_left _ _ hne,
    mul_div_assoc]

theorem deriv_dil_STR02901 (c : ℝ) (φ : ℝ → ℝ) :
    deriv (fun t => φ (c * t)) = fun t => c * deriv φ (c * t) := by
  funext t; rw [deriv_comp_mul_left]; rfl

theorem periodic_deriv_STR02901 {w : ℝ → ℝ} {p : ℝ} (h : Function.Periodic w p) :
    Function.Periodic (deriv w) p := fun x => by
  have := deriv_comp_add_const (f := w) p x
  rw [← this]
  congr 1
  funext y
  exact h y

theorem periodic_dil_iff_STR02901 {c : ℝ} (hc : c ≠ 0) (p : ℝ) (φ : ℝ → ℝ) :
    Function.Periodic (fun t => φ (c * t)) p ↔ Function.Periodic φ (c * p) := by
  constructor
  · intro h x
    have := h (c⁻¹ * x)
    simpa [mul_add, mul_inv_cancel_left₀ hc] using this
  · intro h t
    simp only [mul_add]
    exact h (c * t)

theorem differentiable_dil_iff_STR02901 {c : ℝ} (hc : c ≠ 0) (φ : ℝ → ℝ) :
    Differentiable ℝ (fun t => φ (c * t)) ↔ Differentiable ℝ φ := by
  constructor
  · intro h
    have h2 : Differentiable ℝ (fun x => (fun t => φ (c * t)) (c⁻¹ * x)) :=
      h.comp (differentiable_id.const_mul c⁻¹)
    simpa [mul_inv_cancel_left₀ hc] using h2
  · intro h
    exact h.comp (differentiable_id.const_mul c)

theorem continuous_dil_iff_STR02901 {c : ℝ} (hc : c ≠ 0) (φ : ℝ → ℝ) :
    Continuous (fun t => φ (c * t)) ↔ Continuous φ := by
  constructor
  · intro h
    have h2 : Continuous (fun x => (fun t => φ (c * t)) (c⁻¹ * x)) :=
      h.comp (continuous_const.mul continuous_id)
    simpa [mul_inv_cancel_left₀ hc] using h2
  · intro h
    exact h.comp (continuous_const.mul continuous_id)

theorem holderBdd_scale_STR02901 {α : ℝ} (a c : ℝ) {ψ : ℝ → ℝ}
    (h : HolderBdd α ψ) : HolderBdd α (fun t => a * ψ (c * t)) := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨|a| * C * |c| ^ α, by positivity, fun s t => ?_⟩
  have h1 : |c * s - c * t| = |c| * |s - t| := by rw [← mul_sub, abs_mul]
  have h2 := hC (c * s) (c * t)
  rw [h1, Real.mul_rpow (abs_nonneg c) (abs_nonneg _)] at h2
  calc |a * ψ (c * s) - a * ψ (c * t)| = |a| * |ψ (c * s) - ψ (c * t)| := by
        rw [← mul_sub, abs_mul]
    _ ≤ |a| * (C * (|c| ^ α * |s - t| ^ α)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg a)
    _ = |a| * C * |c| ^ α * |s - t| ^ α := by ring

theorem holderBdd_scale_iff_STR02901 {α : ℝ} {a c : ℝ} (ha : a ≠ 0) (hc : c ≠ 0)
    {ψ : ℝ → ℝ} : HolderBdd α (fun t => a * ψ (c * t)) ↔ HolderBdd α ψ := by
  constructor
  · intro h
    have := holderBdd_scale_STR02901 a⁻¹ c⁻¹ h
    convert this using 1
    funext x
    simp [mul_inv_cancel_left₀ hc, ← mul_assoc, inv_mul_cancel₀ ha]
  · exact holderBdd_scale_STR02901 a c

theorem periodic_const_mul_iff_STR02901 {a : ℝ} (ha : a ≠ 0) {ψ : ℝ → ℝ} {p : ℝ} :
    Function.Periodic (fun t => a * ψ t) p ↔ Function.Periodic ψ p := by
  constructor
  · intro h x
    exact mul_left_cancel₀ ha (h x)
  · intro h x
    simp only [h x]

theorem differentiable_const_mul_iff_STR02901 {a : ℝ} (ha : a ≠ 0) {ψ : ℝ → ℝ} :
    Differentiable ℝ (fun t => a * ψ t) ↔ Differentiable ℝ ψ := by
  constructor
  · intro h
    have := h.const_mul a⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ ha] using this
  · intro h
    exact h.const_mul a

theorem continuous_const_mul_iff_STR02901 {a : ℝ} (ha : a ≠ 0) {ψ : ℝ → ℝ} :
    Continuous (fun t => a * ψ t) ↔ Continuous ψ := by
  constructor
  · intro h
    have := h.const_mul a⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ ha] using this
  · intro h
    exact h.const_mul a


/-! ### The concrete `C^{2,α}` carrier -/

/-- The `2π`-periodic function of `t` attached to a unit-period packet function. -/
noncomputable def wT_STR02901 {α : ℝ} [HolderExponent α] {k : ℕ} (f : PH α k) (t : ℝ) : ℝ :=
  f.val (t / (2 * Real.pi))

/-- Concrete `2π`-periodic `C^{2,α}` functions (circular Hölder seminorm for `u''`). -/
def IsC2Alpha_STR02901 (α : ℝ) (w : ℝ → ℝ) : Prop :=
  Function.Periodic w (2 * Real.pi) ∧ Differentiable ℝ w ∧ Differentiable ℝ (deriv w) ∧
    Continuous (deriv (deriv w)) ∧ CircHolderBdd_STR02901 α (deriv (deriv w))

/-- The concrete norm `‖u‖∞ + ‖u'‖∞ + ‖u''‖∞ + [u'']_α` (circular distance). -/
noncomputable def c2Norm_STR02901 (α : ℝ) (w : ℝ → ℝ) : ℝ :=
  supNorm w + supNorm (deriv w) + supNorm (deriv (deriv w)) +
    circHolder_STR02901 α (deriv (deriv w))

theorem deriv2_dil_STR02901 (c : ℝ) (φ : ℝ → ℝ) :
    deriv (deriv (fun t => φ (c * t))) = fun t => c * (c * deriv (deriv φ) (c * t)) := by
  rw [deriv_dil_STR02901]
  funext t
  rw [deriv_const_mul_field, deriv_dil_STR02901]

theorem wT_eq_dil_STR02901 {α : ℝ} [HolderExponent α] {k : ℕ} (f : PH α k) :
    wT_STR02901 f = fun t => f.val ((2 * Real.pi)⁻¹ * t) := by
  funext t; simp only [wT_STR02901, div_eq_inv_mul]

theorem isC2Alpha_dil_iff_STR02901 {α : ℝ} (hα : 0 < α) (φ : ℝ → ℝ) :
    IsC2Alpha_STR02901 α (fun t => φ ((2 * Real.pi)⁻¹ * t)) ↔ IsPH α 2 φ := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hc : (2 * Real.pi)⁻¹ ≠ 0 := inv_ne_zero hpi
  have hcp : (2 * Real.pi)⁻¹ * (2 * Real.pi) = 1 := inv_mul_cancel₀ hpi
  set c := (2 * Real.pi)⁻¹ with hcdef
  have hc2 : c * c ≠ 0 := mul_ne_zero hc hc
  have hd1 := deriv_dil_STR02901 c φ
  have hd2 := deriv2_dil_STR02901 c φ
  have per0 : Function.Periodic (fun t => φ (c * t)) (2 * Real.pi) ↔ Function.Periodic φ 1 := by
    rw [periodic_dil_iff_STR02901 hc, hcp]
  have per1 : Function.Periodic (deriv (fun t => φ (c * t))) (2 * Real.pi) ↔
      Function.Periodic (deriv φ) 1 := by
    rw [hd1]
    exact (periodic_const_mul_iff_STR02901 (ψ := fun t => deriv φ (c * t)) hc).trans
      (by rw [periodic_dil_iff_STR02901 hc, hcp])
  have per2 : Function.Periodic (deriv (deriv (fun t => φ (c * t)))) (2 * Real.pi) ↔
      Function.Periodic (deriv (deriv φ)) 1 := by
    rw [hd2]
    have e : (fun t => c * (c * deriv (deriv φ) (c * t))) =
        fun t => (c * c) * (fun s => deriv (deriv φ) (c * s)) t := by
      funext t; ring
    rw [e]
    exact (periodic_const_mul_iff_STR02901 hc2).trans
      (by rw [periodic_dil_iff_STR02901 hc, hcp])
  have dif1 : Differentiable ℝ (deriv (fun t => φ (c * t))) ↔ Differentiable ℝ (deriv φ) := by
    rw [hd1]
    exact (differentiable_const_mul_iff_STR02901 (ψ := fun t => deriv φ (c * t)) hc).trans
      (differentiable_dil_iff_STR02901 hc _)
  have con2 : Continuous (deriv (deriv (fun t => φ (c * t)))) ↔ Continuous (deriv (deriv φ)) := by
    rw [hd2]
    have e : (fun t => c * (c * deriv (deriv φ) (c * t))) =
        fun t => (c * c) * (fun s => deriv (deriv φ) (c * s)) t := by
      funext t; ring
    rw [e]
    exact (continuous_const_mul_iff_STR02901 hc2).trans (continuous_dil_iff_STR02901 hc _)
  have hol2 : HolderBdd α (deriv (deriv (fun t => φ (c * t)))) ↔ HolderBdd α (deriv (deriv φ)) := by
    rw [hd2]
    have e : (fun t => c * (c * deriv (deriv φ) (c * t))) =
        fun t => (c * c) * deriv (deriv φ) (c * t) := by
      funext t; ring
    rw [e]
    exact holderBdd_scale_iff_STR02901 hc2 hc
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩
    exact ⟨per0.1 h0, (differentiable_dil_iff_STR02901 hc φ).1 h1,
      per1.1 (periodic_deriv_STR02901 h0), dif1.1 h2,
      per2.1 (periodic_deriv_STR02901 (periodic_deriv_STR02901 h0)), con2.1 h3,
      hol2.1 ((circHolderBdd_iff_STR02901 hα
        (periodic_deriv_STR02901 (periodic_deriv_STR02901 h0))).1 h4)⟩
  · rintro ⟨p0, d0, p1, d1, p2, c2, hb⟩
    exact ⟨per0.2 p0, (differentiable_dil_iff_STR02901 hc φ).2 d0, dif1.2 d1, con2.2 c2,
      (circHolderBdd_iff_STR02901 hα (per2.2 p2)).2 (hol2.2 hb)⟩

/-! ### Normalized integrals and the concrete densities -/

/-- Normalized Lebesgue integral over one period `[0, 2π]`: `∫ f dm`, `m(dt) = dt / (2π)`. -/
noncomputable def meanT_STR02901 (f : ℝ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi), f t

/-- Concrete density `ρ(h, u)(t) = e^{h cos 3t + u(t)} / ∫ e^{h cos 3t + u} dm`. -/
noncomputable def rhoT_STR02901 (h : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (h * Real.cos (3 * t) + u t) /
    meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u s))

/-- Concrete reference density `q_h(t) = e^{h cos 3t} / ∫ e^{h cos 3t} dm`. -/
noncomputable def qT_STR02901 (h : ℝ) (t : ℝ) : ℝ :=
  Real.exp (h * Real.cos (3 * t)) / meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s)))

/-- Concrete log-chart function `u = a cos t + b sin t + w`. -/
noncomputable def uT_STR02901 (a b : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  a * Real.cos t + b * Real.sin t + w t

/-- Orthogonality to `1`, `cos t`, `sin t` for a concrete function (membership in `E`). -/
def InE_STR02901 (w : ℝ → ℝ) : Prop :=
  meanT_STR02901 w = 0 ∧ meanT_STR02901 (fun t => w t * Real.cos t) = 0 ∧
    meanT_STR02901 (fun t => w t * Real.sin t) = 0

theorem meanT_eq_unit_STR02901 (F : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, F (2 * Real.pi * x) = meanT_STR02901 F := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_left (fun t => F t) hpi]
  simp [meanT_STR02901, smul_eq_mul]

theorem meanT_pos_STR02901 {F : ℝ → ℝ} (hc : Continuous F) (hpos : ∀ t, 0 < F t) :
    0 < meanT_STR02901 F := by
  unfold meanT_STR02901
  have : 0 < ∫ t in (0 : ℝ)..(2 * Real.pi), F t :=
    intervalIntegral.intervalIntegral_pos_of_pos (hc.intervalIntegrable _ _) hpos (by positivity)
  positivity

theorem besselI_zero_eq_meanT_STR02901 (h : ℝ) :
    besselI 0 h = meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s))) := by
  rw [← meanT_eq_unit_STR02901, ← integral_unit_threePeriods 0 h]
  refine intervalIntegral.integral_congr fun y _ => ?_
  simp only [Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one]
  have e : 2 * Real.pi * 3 * y = 3 * (2 * Real.pi * y) := by ring
  rw [e]

section Carriers

variable {α : ℝ} [HolderExponent α]

theorem isC2Alpha_wT_STR02901 (f : PH α 2) : IsC2Alpha_STR02901 α (wT_STR02901 f) := by
  rw [wT_eq_dil_STR02901]
  exact (isC2Alpha_dil_iff_STR02901 HolderExponent.pos f.val).2 f.isPH

theorem exists_wT_of_isC2Alpha_STR02901 {w : ℝ → ℝ} (hw : IsC2Alpha_STR02901 α w) :
    ∃ f : PH α 2, wT_STR02901 f = w := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have e : w = fun t => (fun x => w (2 * Real.pi * x)) ((2 * Real.pi)⁻¹ * t) := by
    funext t; simp only [mul_inv_cancel_left₀ hpi]
  have h2 : IsPH α 2 (fun x => w (2 * Real.pi * x)) := by
    rw [← isC2Alpha_dil_iff_STR02901 HolderExponent.pos, ← e]; exact hw
  refine ⟨PH.mk _ h2, ?_⟩
  funext t
  simp only [wT_STR02901, PH.val_mk]
  congr 1
  field_simp

theorem wT_injective_STR02901 {k : ℕ} : Function.Injective (wT_STR02901 (α := α) (k := k)) := by
  intro f g h
  apply PH.ext
  funext x
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have := congrFun h (2 * Real.pi * x)
  simpa [wT_STR02901, hpi] using this

theorem c2Norm_wT_eq_STR02901 (f : PH α 2) :
    c2Norm_STR02901 α (wT_STR02901 f) =
      supNorm f.val + (2 * Real.pi)⁻¹ * supNorm (deriv f.val) +
        ((2 * Real.pi)⁻¹) ^ 2 * supNorm (deriv (deriv f.val)) +
        ((2 * Real.pi)⁻¹) ^ 2 * ((2 * Real.pi)⁻¹) ^ α * holderSeminorm α (deriv (deriv f.val)) := by
  have hα : 0 < α := HolderExponent.pos
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hcpos : 0 < (2 * Real.pi)⁻¹ := by positivity
  have hc : (2 * Real.pi)⁻¹ ≠ 0 := hcpos.ne'
  set c := (2 * Real.pi)⁻¹ with hcdef
  have hper := (isC2Alpha_wT_STR02901 f).1
  have hd1 := deriv_dil_STR02901 c f.val
  have hd2 := deriv2_dil_STR02901 c f.val
  have hw : wT_STR02901 f = fun t => f.val (c * t) := wT_eq_dil_STR02901 f
  have e2 : (fun t => c * (c * deriv (deriv f.val) (c * t))) =
      fun t => (c * c) * deriv (deriv f.val) (c * t) := by
    funext t; ring
  have hholder : HolderBdd α (deriv (deriv (wT_STR02901 f))) := by
    rw [hw, hd2, e2]
    exact holderBdd_scale_STR02901 _ _ f.isPH.2.2.2.2.2.2
  unfold c2Norm_STR02901
  rw [circHolder_eq_holderSeminorm_STR02901 hα
    (periodic_deriv_STR02901 (periodic_deriv_STR02901 hper)) hholder]
  rw [hw, hd2, e2, hd1]
  rw [supNorm_dil_STR02901 hc, supNorm_scale_STR02901 hc, supNorm_scale_STR02901 hc,
    holderSeminorm_scale_STR02901 hc]
  rw [abs_of_pos hcpos, abs_of_pos (mul_pos hcpos hcpos)]
  ring


theorem rhoT_pos_STR02901 (h : ℝ) {u : ℝ → ℝ} (hu : Continuous u) (t : ℝ) :
    0 < rhoT_STR02901 h u t := by
  unfold rhoT_STR02901
  refine div_pos (Real.exp_pos _) (meanT_pos_STR02901 (by fun_prop) fun s => Real.exp_pos _)


theorem rho_val_STR02901 (x : Par × Wsp α) (s : ℝ) :
    (rho α x).val s =
      rhoT_STR02901 (x.1 2) (uT_STR02901 (x.1 0) (x.1 1) (wT_STR02901 (x.2 : PH α 2)))
        (2 * Real.pi * s) := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hphi : ∀ y : ℝ, (phiCLM x).val y =
      x.1 2 * Real.cos (3 * (2 * Real.pi * y))
        + uT_STR02901 (x.1 0) (x.1 1) (wT_STR02901 (x.2 : PH α 2)) (2 * Real.pi * y) := by
    intro y
    simp only [phiCLM, u0CLM, uCLM, add_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.smulRight_apply, PH.val_add, PH.val_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, incl2_val, cos3, cosT, sinT, PH.val_trig, trigFun,
      pc_apply, Submodule.subtypeL_apply, uT_STR02901, wT_STR02901, Nat.cast_one, Nat.cast_ofNat]
    have e3 : 2 * Real.pi * 3 * y = 3 * (2 * Real.pi * y) := by ring
    have e1 : 2 * Real.pi * 1 * y = 2 * Real.pi * y := by ring
    have e0 : 2 * Real.pi * y / (2 * Real.pi) = y := by field_simp
    rw [e3, e1, e0]
    simp only [ContinuousLinearMap.coe_snd']
    ring
  have hint : PH.integral 0 (PH.expMap 0 (phiCLM x)) =
      meanT_STR02901 (fun t => Real.exp (x.1 2 * Real.cos (3 * t) +
        uT_STR02901 (x.1 0) (x.1 1) (wT_STR02901 (x.2 : PH α 2)) t)) := by
    rw [PH.integral_apply, ← meanT_eq_unit_STR02901]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [PH.expMap_val, hphi]
  unfold rho PH.normMap
  rw [PH.val_smul, hint]
  simp only [Pi.smul_apply, smul_eq_mul, PH.expMap_val, hphi s, rhoT_STR02901]
  rw [div_eq_inv_mul]

theorem wT_apply_STR02901 {k : ℕ} (f : PH α k) (x : ℝ) :
    wT_STR02901 f (2 * Real.pi * x) = f.val x := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  simp only [wT_STR02901]
  congr 1
  field_simp

theorem mem_orthSub_iff_InE_STR02901 (f : PH α 2) :
    f ∈ PH.orthSub α 2 ↔ InE_STR02901 (wT_STR02901 f) := by
  rw [PH.mem_orthSub, PH.integral_apply, PH.cosCoeff_apply, PH.sinCoeff_apply]
  unfold InE_STR02901
  rw [← meanT_eq_unit_STR02901 (wT_STR02901 f),
    ← meanT_eq_unit_STR02901 (fun t => wT_STR02901 f t * Real.cos t),
    ← meanT_eq_unit_STR02901 (fun t => wT_STR02901 f t * Real.sin t)]
  simp only [wT_apply_STR02901, Nat.cast_one, mul_one]

theorem c2Norm_wT_le_STR02901 (f : PH α 2) : c2Norm_STR02901 α (wT_STR02901 f) ≤ ‖f‖ := by
  have hα : 0 < α := HolderExponent.pos
  rw [c2Norm_wT_eq_STR02901]
  have hn : ‖f‖ = supNorm f.val + (supNorm (deriv f.val) +
      (supNorm (deriv (deriv f.val)) + holderSeminorm α (deriv (deriv f.val)))) := rfl
  rw [hn]
  have hc0 : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hc1 : (2 * Real.pi)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  have hc2 : ((2 * Real.pi)⁻¹) ^ 2 ≤ 1 := pow_le_one₀ hc0 hc1
  have hc3 : ((2 * Real.pi)⁻¹) ^ 2 * ((2 * Real.pi)⁻¹) ^ α ≤ 1 :=
    (mul_le_mul hc2 (Real.rpow_le_one hc0 hc1 hα.le) (by positivity) zero_le_one).trans_eq
      (one_mul 1)
  have a1 := mul_le_of_le_one_left (supNorm_nonneg (deriv f.val)) hc1
  have a2 := mul_le_of_le_one_left (supNorm_nonneg (deriv (deriv f.val))) hc2
  have a3 := mul_le_of_le_one_left (holderSeminorm_nonneg α (deriv (deriv f.val))) hc3
  linarith

theorem c2Norm_wT_ge_STR02901 (f : PH α 2) :
    ((2 * Real.pi)⁻¹) ^ 2 * ((2 * Real.pi)⁻¹) ^ α * ‖f‖ ≤ c2Norm_STR02901 α (wT_STR02901 f) := by
  have hα : 0 < α := HolderExponent.pos
  rw [c2Norm_wT_eq_STR02901]
  have hn : ‖f‖ = supNorm f.val + (supNorm (deriv f.val) +
      (supNorm (deriv (deriv f.val)) + holderSeminorm α (deriv (deriv f.val)))) := rfl
  rw [hn]
  have hc0 : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hc1 : (2 * Real.pi)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  have hK0 : 0 ≤ ((2 * Real.pi)⁻¹) ^ 2 * ((2 * Real.pi)⁻¹) ^ α := by positivity
  have hK1 : ((2 * Real.pi)⁻¹) ^ 2 * ((2 * Real.pi)⁻¹) ^ α ≤ (2 * Real.pi)⁻¹ := by
    have h2 : ((2 * Real.pi)⁻¹) ^ 2 ≤ (2 * Real.pi)⁻¹ := by
      rw [sq]; exact mul_le_of_le_one_left hc0 hc1
    have h3 : ((2 * Real.pi)⁻¹) ^ α ≤ 1 := Real.rpow_le_one hc0 hc1 hα.le
    calc ((2 * Real.pi)⁻¹) ^ 2 * ((2 * Real.pi)⁻¹) ^ α
        ≤ ((2 * Real.pi)⁻¹) ^ 2 * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ (2 * Real.pi)⁻¹ := by rw [mul_one]; exact h2
  have hK2 : ((2 * Real.pi)⁻¹) ^ 2 * ((2 * Real.pi)⁻¹) ^ α ≤ ((2 * Real.pi)⁻¹) ^ 2 := by
    have h3 : ((2 * Real.pi)⁻¹) ^ α ≤ 1 := Real.rpow_le_one hc0 hc1 hα.le
    calc ((2 * Real.pi)⁻¹) ^ 2 * ((2 * Real.pi)⁻¹) ^ α
        ≤ ((2 * Real.pi)⁻¹) ^ 2 * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = ((2 * Real.pi)⁻¹) ^ 2 := mul_one _
  have hK3 : ((2 * Real.pi)⁻¹) ^ 2 * ((2 * Real.pi)⁻¹) ^ α ≤ 1 := by
    refine hK1.trans hc1
  have b0 := mul_le_mul_of_nonneg_right hK3 (supNorm_nonneg f.val)
  have b1 := mul_le_mul_of_nonneg_right hK1 (supNorm_nonneg (deriv f.val))
  have b2 := mul_le_mul_of_nonneg_right hK2 (supNorm_nonneg (deriv (deriv f.val)))
  nlinarith [b0, b1, b2, supNorm_nonneg f.val, supNorm_nonneg (deriv f.val),
    supNorm_nonneg (deriv (deriv f.val)), holderSeminorm_nonneg α (deriv (deriv f.val))]

end Carriers


/-- The reference density `q_h` transported to the angular circle. -/
noncomputable def qAng_STR02901 (h : ℝ) (θ : AngCircle) : ℝ :=
  referenceDensity h (angEquiv.symm θ)

theorem qAng_comp_STR02901 (h : ℝ) (x : Torus 1) :
    qAng_STR02901 h (angEquiv x) = referenceDensity h x := by
  simp [qAng_STR02901]

theorem qAng_pos_STR02901 (h : ℝ) (θ : AngCircle) : 0 < qAng_STR02901 h θ :=
  referenceDensity_pos (h := h) _

theorem measurable_qAng_STR02901 (h : ℝ) : Measurable (qAng_STR02901 h) :=
  (continuous_referenceDensity h).measurable.comp angEquiv.symm.measurable

theorem integral_qAng_STR02901 (h : ℝ) : ∫ θ, qAng_STR02901 h θ ∂angHaar = 1 := by
  rw [← integral_comp_angEquiv]
  simp only [qAng_comp_STR02901]
  exact integral_referenceDensity_eq_one h

/-- The angular square-root density `g = √(ρ / q_h)`. -/
noncomputable def gAng_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) (θ : AngCircle) : ℝ :=
  str025_u h ρ (angEquiv.symm θ)

theorem gAng_comp_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) (x : Torus 1) :
    gAng_STR02901 h ρ (angEquiv x) = str025_u h ρ x := by
  simp [gAng_STR02901]

theorem gAng_comp_eq_div_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) (x : Torus 1) :
    gAng_STR02901 h ρ (angEquiv x) = ρ.sqrt x / Real.sqrt (referenceDensity h x) := by
  rw [gAng_comp_STR02901, str025_u_eq]; rfl

/-- Angular entropy `∫ g² log g² q_h dm`. -/
noncomputable def angEntropy_STR02901 (h : ℝ) (g : AngCircle → ℝ) : ℝ :=
  ∫ θ, g θ ^ 2 * Real.log (g θ ^ 2) * qAng_STR02901 h θ ∂angHaar

/-- Angular Fisher information `4 ∫ g'² q_h dm`, with value `⊤` when `g` has no weak derivative. -/
noncomputable def angFisher_STR02901 (h : ℝ) (g : AngCircle → ℝ) : ℝ≥0∞ :=
  ⨅ (G : AngCircle → ℝ) (_ : IsAngularWeakDeriv g G),
    4 * ∫⁻ θ, ENNReal.ofReal (qAng_STR02901 h θ) * ‖G θ‖ₑ ^ 2 ∂angHaar

theorem angDeriv_unique_STR02901 {g G G' : AngCircle → ℝ} (hG : IsAngularWeakDeriv g G)
    (hG' : IsAngularWeakDeriv g G') : G =ᵐ[angHaar] G' := by
  have h := ((isWeakGradient_comp_iff g G).1 hG).ae_eq ((isWeakGradient_comp_iff g G').1 hG')
  have h2 : ∀ᵐ x ∂haar 1, G (angEquiv x) = G' (angEquiv x) := by
    filter_upwards [h] with x hx
    have h0 := congrArg (fun v : Tangent 1 => v 0) hx
    simp only [physGrad_apply] at h0
    exact mul_left_cancel₀ Real.two_pi_pos.ne' h0
  exact (ae_comp_angEquiv_iff (p := fun θ => G θ = G' θ)).1 h2

theorem angFisher_eq_STR02901 (h : ℝ) {g G : AngCircle → ℝ} (hG : IsAngularWeakDeriv g G) :
    angFisher_STR02901 h g = 4 * ∫⁻ θ, ENNReal.ofReal (qAng_STR02901 h θ) * ‖G θ‖ₑ ^ 2 ∂angHaar := by
  apply le_antisymm
  · exact iInf₂_le G hG
  · refine le_iInf₂ fun G' hG' => ?_
    refine le_of_eq ?_
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [angDeriv_unique_STR02901 hG hG'] with θ hθ
    rw [hθ]

theorem angFisher_eq_top_STR02901 (h : ℝ) {g : AngCircle → ℝ} (hg : ¬ AngularH1 g) :
    angFisher_STR02901 h g = ⊤ :=
  le_antisymm le_top (le_iInf₂ fun G hG => absurd ⟨G, hG⟩ hg)

theorem angFisher_ne_top_STR02901 (h : ℝ) {g G : AngCircle → ℝ} (hG : IsAngularWeakDeriv g G) :
    angFisher_STR02901 h g ≠ ⊤ := by
  rw [angFisher_eq_STR02901 h hG]
  refine ENNReal.mul_ne_top (by norm_num) (ne_of_lt ?_)
  have hint : Integrable (fun θ => G θ ^ 2) angHaar := hG.memLp_deriv.integrable_sq
  calc ∫⁻ θ, ENNReal.ofReal (qAng_STR02901 h θ) * ‖G θ‖ₑ ^ 2 ∂angHaar
      ≤ ∫⁻ θ, ENNReal.ofReal (Real.exp (2 * |h|)) * ‖G θ‖ₑ ^ 2 ∂angHaar :=
        lintegral_mono fun θ => by gcongr; exact referenceDensity_le h _
    _ = ENNReal.ofReal (Real.exp (2 * |h|)) * ∫⁻ θ, ‖G θ‖ₑ ^ 2 ∂angHaar :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        have := hint.hasFiniteIntegral
        simpa [HasFiniteIntegral, enorm_pow] using this

/-- The angular weak derivative `g'` of `gAng`, extracted from the weak gradient `str025_grad`. -/
noncomputable def gDerivAng_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) (θ : AngCircle) : ℝ :=
  str025_grad h ρ (angEquiv.symm θ) 0 / (2 * Real.pi)

theorem isAngularWeakDeriv_gAng_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) :
    IsAngularWeakDeriv (gAng_STR02901 h ρ) (gDerivAng_STR02901 h ρ) := by
  rw [isWeakGradient_comp_iff]
  have e1 : gAng_STR02901 h ρ ∘ angEquiv = str025_u h ρ := funext (gAng_comp_STR02901 h ρ)
  have e2 : physGrad (gDerivAng_STR02901 h ρ) = str025_grad h ρ := physGrad_surj
  rw [e1, e2]
  exact str025_isWeak h ρ

theorem angularH1_gAng_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) : AngularH1 (gAng_STR02901 h ρ) :=
  ⟨_, isAngularWeakDeriv_gAng_STR02901 h ρ⟩

theorem ordinaryFisher_eq_angFisher_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) :
    ordinaryFisher h ρ = ENNReal.ofReal DGPS.Circle.AngularNormalization.a0 * angFisher_STR02901 h (gAng_STR02901 h ρ) := by
  rw [angFisher_eq_STR02901 h (isAngularWeakDeriv_gAng_STR02901 h ρ), str025_fisher_eq]
  have e2 : physGrad (gDerivAng_STR02901 h ρ) = str025_grad h ρ := physGrad_surj
  unfold dirichletEnergy
  have hμ : ((str025_prob h : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) =
      (haar 1).withDensity (fun x => ENNReal.ofReal (referenceDensity h x)) := rfl
  have hmeas : AEMeasurable (fun x => ‖(str025_test h ρ).grad x‖ₑ ^ 2) (haar 1) :=
    (str025_isWeak h ρ).memLp_grad.aestronglyMeasurable.aemeasurable.enorm.pow_const 2
  rw [hμ, lintegral_withDensity_eq_lintegral_mul₀
    (continuous_referenceDensity h).measurable.ennreal_ofReal.aemeasurable hmeas]
  have e3 : ∀ x, (fun x => ENNReal.ofReal (referenceDensity h x)) x * ‖(str025_test h ρ).grad x‖ₑ ^ 2 =
      ENNReal.ofReal DGPS.Circle.AngularNormalization.a0 * ((fun θ => ENNReal.ofReal (qAng_STR02901 h θ) *
        ‖gDerivAng_STR02901 h ρ θ‖ₑ ^ 2) (angEquiv x)) := by
    intro x
    show ENNReal.ofReal (referenceDensity h x) * ‖str025_grad h ρ x‖ₑ ^ 2 = _
    rw [← e2, enorm_physGrad_sq]
    simp only [qAng_comp_STR02901]
    ring
  simp only [Pi.mul_apply]
  rw [lintegral_congr (fun x => e3 x), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_comp_angEquiv (fun θ => ENNReal.ofReal (qAng_STR02901 h θ) *
        ‖gDerivAng_STR02901 h ρ θ‖ₑ ^ 2)]
  ring


theorem gAng_integrand_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) (x : Torus 1) :
    str025_u h ρ x ^ 2 * Real.log (str025_u h ρ x ^ 2) * referenceDensity h x =
      ρ.density x * Real.log (ρ.density x) - ρ.density x * Real.log (referenceDensity h x) := by
  have hq : 0 < referenceDensity h x := referenceDensity_pos (h := h) x
  have hd : ρ.density x = ρ.sqrt x ^ 2 := rfl
  have hu : str025_u h ρ x ^ 2 = ρ.density x / referenceDensity h x := by
    rw [str025_u_eq, div_pow, str025_w_sq, hd]
  rw [hu]
  by_cases h0 : ρ.density x = 0
  · simp [h0]
  · have hpos : 0 < ρ.density x := lt_of_le_of_ne (ρ.density_nonneg x) (Ne.symm h0)
    rw [Real.log_div hpos.ne' hq.ne']
    field_simp

theorem angEntropy_gAng_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) :
    angEntropy_STR02901 h (gAng_STR02901 h ρ) =
      DGPS.Analysis.circleEntropy ρ - ∫ x, ρ.density x * Real.log (referenceDensity h x) ∂haar 1 := by
  unfold angEntropy_STR02901
  rw [← integral_comp_angEquiv (fun θ => gAng_STR02901 h ρ θ ^ 2 * Real.log (gAng_STR02901 h ρ θ ^ 2) *
    qAng_STR02901 h θ)]
  simp only [gAng_comp_STR02901, qAng_comp_STR02901, gAng_integrand_STR02901]
  rw [integral_sub (absoluteDensity_entropy_finite ρ).1 (integrable_density_mul_log_reference h ρ),
    DGPS.Examples.ThreeSpeciesCircle.circleEntropy_eq]

theorem ordinaryEntropy_eq_angEntropy_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) :
    ordinaryEntropy h ρ = ENNReal.ofReal (angEntropy_STR02901 h (gAng_STR02901 h ρ)) := by
  rw [angEntropy_gAng_STR02901, ordinaryEntropy_eq]

theorem angEntropy_gAng_nonneg_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) :
    0 ≤ angEntropy_STR02901 h (gAng_STR02901 h ρ) := by
  unfold angEntropy_STR02901
  rw [← integral_comp_angEquiv (fun θ => gAng_STR02901 h ρ θ ^ 2 * Real.log (gAng_STR02901 h ρ θ ^ 2) *
    qAng_STR02901 h θ)]
  simp only [gAng_comp_STR02901, qAng_comp_STR02901, gAng_integrand_STR02901]
  have hI : Integrable (fun x => ρ.density x * Real.log (ρ.density x) -
      ρ.density x * Real.log (referenceDensity h x)) (haar 1) :=
    (absoluteDensity_entropy_finite ρ).1.sub (integrable_density_mul_log_reference h ρ)
  have hF : Integrable (fun x => ρ.density x * Real.log (ρ.density x) -
      ρ.density x * Real.log (referenceDensity h x) - ρ.density x + referenceDensity h x) (haar 1) :=
    (hI.sub ρ.integrable_density).add (integrable_referenceDensity h)
  have hnn : ∀ x, 0 ≤ ρ.density x * Real.log (ρ.density x) -
      ρ.density x * Real.log (referenceDensity h x) - ρ.density x + referenceDensity h x := by
    intro x
    have hq : 0 < referenceDensity h x := referenceDensity_pos (h := h) x
    by_cases h0 : ρ.density x = 0
    · simp [h0, hq.le]
    · have hpos : 0 < ρ.density x := lt_of_le_of_ne (ρ.density_nonneg x) (Ne.symm h0)
      have := Real.log_le_sub_one_of_pos (div_pos hq hpos)
      rw [Real.log_div hq.ne' hpos.ne'] at this
      have h2 := mul_le_mul_of_nonneg_left this hpos.le
      have h3 : ρ.density x * (referenceDensity h x / ρ.density x - 1) =
          referenceDensity h x - ρ.density x := by field_simp
      nlinarith [h2, h3]
  have h0 : 0 ≤ ∫ x, (ρ.density x * Real.log (ρ.density x) -
      ρ.density x * Real.log (referenceDensity h x) - ρ.density x + referenceDensity h x) ∂haar 1 :=
    integral_nonneg (fun x => hnn x)
  have e1 : ∫ x, (ρ.density x * Real.log (ρ.density x) -
      ρ.density x * Real.log (referenceDensity h x) - ρ.density x + referenceDensity h x) ∂haar 1 =
      ∫ x, (ρ.density x * Real.log (ρ.density x) -
        ρ.density x * Real.log (referenceDensity h x) - ρ.density x) ∂haar 1 +
      ∫ x, referenceDensity h x ∂haar 1 :=
    integral_add (hI.sub ρ.integrable_density) (integrable_referenceDensity h)
  have e2 : ∫ x, (ρ.density x * Real.log (ρ.density x) -
        ρ.density x * Real.log (referenceDensity h x) - ρ.density x) ∂haar 1 =
      ∫ x, (ρ.density x * Real.log (ρ.density x) -
        ρ.density x * Real.log (referenceDensity h x)) ∂haar 1 - ∫ x, ρ.density x ∂haar 1 :=
    integral_sub hI ρ.integrable_density
  rw [e1, e2, ρ.integral_density, integral_referenceDensity_eq_one] at h0
  linarith

/-- The angular admissible domain for the reference `q_h`: periodic `H¹`, nonnegative,
`∫ g² q_h dm = 1`. -/
def AngDomain_STR02901 (h : ℝ) (g : AngCircle → ℝ) : Prop :=
  AngularH1 g ∧ 0 ≤ᵐ[angHaar] g ∧ ∫ θ, g θ ^ 2 * qAng_STR02901 h θ ∂angHaar = 1

theorem density_eq_gAng_sq_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) (x : Torus 1) :
    ρ.density x = gAng_STR02901 h ρ (angEquiv x) ^ 2 * referenceDensity h x := by
  have hq : 0 < referenceDensity h x := referenceDensity_pos (h := h) x
  rw [gAng_comp_eq_div_STR02901, div_pow, Real.sq_sqrt hq.le]
  show ρ.sqrt x ^ 2 = _
  field_simp

theorem angDomain_gAng_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) :
    AngDomain_STR02901 h (gAng_STR02901 h ρ) := by
  refine ⟨angularH1_gAng_STR02901 h ρ, ?_, ?_⟩
  · refine (ae_comp_angEquiv_iff (p := fun θ => (0 : ℝ) ≤ gAng_STR02901 h ρ θ)).1 ?_
    filter_upwards [ρ.sqrt_nonneg] with x hx
    show 0 ≤ gAng_STR02901 h ρ (angEquiv x)
    rw [gAng_comp_eq_div_STR02901]
    exact div_nonneg hx (Real.sqrt_nonneg _)
  · rw [← integral_comp_angEquiv (fun θ => gAng_STR02901 h ρ θ ^ 2 * qAng_STR02901 h θ)]
    simp only [qAng_comp_STR02901]
    have : ∀ x, gAng_STR02901 h ρ (angEquiv x) ^ 2 * referenceDensity h x = ρ.sqrt x ^ 2 := fun x =>
      (density_eq_gAng_sq_STR02901 h ρ x).symm
    simp only [this]
    exact ρ.mass_one

/-- The absolute density with square root `g ∘ angEquiv · √q_h` attached to an angular
admissible `g`. -/
noncomputable def absOfAng_STR02901 (h : ℝ) (g : AngCircle → ℝ) (hg : AngDomain_STR02901 h g) :
    AbsoluteDensity 1 where
  sqrt := fun x => g (angEquiv x) * Real.sqrt (referenceDensity h x)
  sqrt_mem := by
    obtain ⟨G, hG⟩ := (angularH1_comp_iff g).1 hg.1
    have hw := RelativeFisher.mul_rpow_isWeakGradient (ordinaryReference_lip h) (r := (1 / 2 : ℝ))
      (by norm_num) hG
    have e : (fun x => g (angEquiv x) * Real.sqrt (referenceDensity h x)) =
        fun x => (g ∘ angEquiv) x * (ordinaryReference h).density x ^ (1 / 2 : ℝ) := by
      funext x
      show _ = g (angEquiv x) * referenceDensity h x ^ (1 / 2 : ℝ)
      rw [Real.sqrt_eq_rpow]
    rw [mem_H1Haar, e]
    exact ⟨_, hw⟩
  sqrt_nonneg := by
    filter_upwards [(ae_comp_angEquiv_iff (p := fun θ => (0 : ℝ) ≤ g θ)).2 hg.2.1] with x hx
    exact mul_nonneg hx (Real.sqrt_nonneg _)
  mass_one := by
    have h1 := hg.2.2
    rw [← integral_comp_angEquiv (fun θ => g θ ^ 2 * qAng_STR02901 h θ)] at h1
    simp only [qAng_comp_STR02901] at h1
    refine Eq.trans ?_ h1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (g (angEquiv x) * Real.sqrt (referenceDensity h x)) ^ 2 = _
    rw [mul_pow, Real.sq_sqrt (referenceDensity_pos (h := h) x).le]

theorem gAng_absOfAng_STR02901 (h : ℝ) (g : AngCircle → ℝ) (hg : AngDomain_STR02901 h g) :
    gAng_STR02901 h (absOfAng_STR02901 h g hg) = g := by
  funext θ
  obtain ⟨x, rfl⟩ := angEquiv.surjective θ
  rw [gAng_comp_eq_div_STR02901]
  have hq : 0 < Real.sqrt (referenceDensity h x) := Real.sqrt_pos.2 (referenceDensity_pos (h := h) x)
  show g (angEquiv x) * Real.sqrt (referenceDensity h x) / Real.sqrt (referenceDensity h x) = _
  field_simp

theorem exists_abs_of_angDomain_STR02901 (h : ℝ) {g : AngCircle → ℝ} (hg : AngDomain_STR02901 h g) :
    ∃ ρ : AbsoluteDensity 1, gAng_STR02901 h ρ = g :=
  ⟨absOfAng_STR02901 h g hg, gAng_absOfAng_STR02901 h g hg⟩

theorem gAng_ae_eq_iff_STR02901 (h : ℝ) (ρ ρ' : AbsoluteDensity 1) :
    gAng_STR02901 h ρ =ᵐ[angHaar] gAng_STR02901 h ρ' ↔ ρ.density =ᵐ[haar 1] ρ'.density := by
  refine (ae_comp_angEquiv_iff (p := fun θ => gAng_STR02901 h ρ θ = gAng_STR02901 h ρ' θ)).symm.trans ?_
  constructor
  · intro H
    filter_upwards [H] with x hx
    rw [density_eq_gAng_sq_STR02901 h ρ x, density_eq_gAng_sq_STR02901 h ρ' x, hx]
  · intro H
    filter_upwards [AbsoluteDensity.sqrt_ae_eq_of_density_ae_eq H] with x hx
    simp only [gAng_comp_eq_div_STR02901, hx]


/-- The angular rate quotient `I / (2 H)` (value in `[0, ⊤]`). -/
noncomputable def angQuot_STR02901 (h : ℝ) (g : AngCircle → ℝ) : ℝ≥0∞ :=
  angFisher_STR02901 h g / (2 * ENNReal.ofReal (angEntropy_STR02901 h g))

theorem str025_quot_eq_angQuot_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) :
    str025_quot h ρ =
      ENNReal.ofReal DGPS.Circle.AngularNormalization.a0 * angQuot_STR02901 h (gAng_STR02901 h ρ) := by
  unfold str025_quot angQuot_STR02901
  rw [ordinaryFisher_eq_angFisher_STR02901, ordinaryEntropy_eq_angEntropy_STR02901, mul_div_assoc]

theorem str025_quot_toReal_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) :
    (str025_quot h ρ).toReal / (4 * Real.pi ^ 2) =
      (angFisher_STR02901 h (gAng_STR02901 h ρ)).toReal /
        (2 * angEntropy_STR02901 h (gAng_STR02901 h ρ)) := by
  have ha : DGPS.Circle.AngularNormalization.a0 = 4 * Real.pi ^ 2 := rfl
  have hpi : (4 * Real.pi ^ 2) ≠ 0 := by positivity
  rw [str025_quot_eq_angQuot_STR02901, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by rw [ha]; positivity)]
  unfold angQuot_STR02901
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofReal (angEntropy_gAng_nonneg_STR02901 h ρ),
    ha]
  simp only [ENNReal.toReal_ofNat]
  field_simp

theorem ordinaryEntropy_pos_iff_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) :
    0 < ordinaryEntropy h ρ ↔ 0 < angEntropy_STR02901 h (gAng_STR02901 h ρ) := by
  rw [ordinaryEntropy_eq_angEntropy_STR02901, ENNReal.ofReal_pos]

theorem optimizer_transfer_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) :
    (∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' → str025_quot h ρ ≤ str025_quot h ρ') ↔
      (∀ g' : AngCircle → ℝ, AngDomain_STR02901 h g' → 0 < angEntropy_STR02901 h g' →
        angQuot_STR02901 h (gAng_STR02901 h ρ) ≤ angQuot_STR02901 h g') := by
  have ha : (ENNReal.ofReal DGPS.Circle.AngularNormalization.a0) ≠ 0 := by
    have : DGPS.Circle.AngularNormalization.a0 = 4 * Real.pi ^ 2 := rfl
    rw [Ne, ENNReal.ofReal_eq_zero, not_le, this]; positivity
  constructor
  · intro H g' hg' hpos
    obtain ⟨ρ', rfl⟩ := exists_abs_of_angDomain_STR02901 h hg'
    have := H ρ' ((ordinaryEntropy_pos_iff_STR02901 h ρ').2 hpos)
    rw [str025_quot_eq_angQuot_STR02901, str025_quot_eq_angQuot_STR02901] at this
    exact (ENNReal.mul_le_mul_iff_right ha ENNReal.ofReal_ne_top).1 this
  · intro H ρ' hpos
    have := H (gAng_STR02901 h ρ') (angDomain_gAng_STR02901 h ρ')
      ((ordinaryEntropy_pos_iff_STR02901 h ρ').1 hpos)
    rw [str025_quot_eq_angQuot_STR02901, str025_quot_eq_angQuot_STR02901]
    exact mul_le_mul_right this _


/-- Every probability measure with finite ordinary Fisher information relative to `q_h` is the
density measure of an absolute-admissible density. -/
theorem exists_abs_of_finiteFisher_STR02901 (h : ℝ) (ν : Measure (Torus 1)) [IsProbabilityMeasure ν]
    (hF : ordinaryRelativeFisher ν (ordinaryReference h) ≠ ⊤) :
    ∃ ρ : AbsoluteDensity 1, (densityMeasure ρ : Measure (Torus 1)) = ν := by
  have hc : ν ≪ (ordinaryReference h).measure ∧
      relativeSqrt ν (ordinaryReference h) ∈ WeightedH1 (ordinaryReference h) := by
    by_contra hc
    refine hF ?_
    unfold ordinaryRelativeFisher
    rw [dite_eq_right hc]
  obtain ⟨hac, hmem⟩ := hc
  have hνac : ν ≪ haar 1 := hac.trans (ordinaryReference h).measure_ac_haar
  have hsm := (RelativeFisher.relativeSqrt_mem_weightedH1_iff (ordinaryReference_lip h) ν).1 hmem
  have hsq : ∀ x, (Real.sqrt (ν.rnDeriv (haar 1) x).toReal) ^ 2 = (ν.rnDeriv (haar 1) x).toReal :=
    fun x => Real.sq_sqrt ENNReal.toReal_nonneg
  have hmass : ∫ x, (Real.sqrt (ν.rnDeriv (haar 1) x).toReal) ^ 2 ∂haar 1 = 1 := by
    simp only [hsq]
    rw [Measure.integral_toReal_rnDeriv hνac]
    simp
  refine ⟨⟨_, hsm, Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _, hmass⟩, ?_⟩
  show (haar 1).withDensity (fun x => ENNReal.ofReal ((Real.sqrt (ν.rnDeriv (haar 1) x).toReal) ^ 2)) = ν
  have e : (haar 1).withDensity (fun x => ENNReal.ofReal ((Real.sqrt (ν.rnDeriv (haar 1) x).toReal) ^ 2)) =
      (haar 1).withDensity (ν.rnDeriv (haar 1)) := by
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top ν (haar 1)] with x hx
    rw [hsq, ENNReal.ofReal_toReal hx.ne]
  rw [e, Measure.withDensity_rnDeriv_eq ν (haar 1) hνac]

theorem densityMeasure_eq_iff_STR02901 (ρ ρ' : AbsoluteDensity 1) :
    (densityMeasure ρ : Measure (Torus 1)) = densityMeasure ρ' ↔
      ρ.density =ᵐ[haar 1] ρ'.density := by
  have H0 : ∀ σ : AbsoluteDensity 1, (densityMeasure σ : Measure (Torus 1)) =
      (haar 1).withDensity (fun x => ENNReal.ofReal (σ.density x)) := fun σ => rfl
  rw [H0, H0]
  constructor
  · intro H
    have hae := (withDensity_eq_iff_of_sigmaFinite
      ρ.integrable_density.aemeasurable.ennreal_ofReal
      ρ'.integrable_density.aemeasurable.ennreal_ofReal).1 H
    filter_upwards [hae] with x hx
    exact (ENNReal.ofReal_eq_ofReal_iff (ρ.density_nonneg x) (ρ'.density_nonneg x)).1 hx
  · intro H
    refine withDensity_congr_ae ?_
    filter_upwards [H] with x hx
    rw [hx]


/-- The finite-information domain for the ordinary problem at parameter `h`: probability
measures whose ordinary Fisher information relative to `q_h` is finite.  Outside this domain
`ordinaryRelativeFisher = ⊤` (not absolutely continuous, or relative square root not in `H¹`),
and every such competitor has deficit `⊤`; no real-valued `∞ - ∞` is formed. -/
def FiniteInfo_STR02901 (h : ℝ) (ν : Measure (Torus 1)) : Prop :=
  IsProbabilityMeasure ν ∧ ordinaryRelativeFisher ν (ordinaryReference h) ≠ ⊤

theorem finiteInfo_iff_STR02901 (h : ℝ) (ν : Measure (Torus 1)) :
    FiniteInfo_STR02901 h ν ↔ ∃ ρ : AbsoluteDensity 1, (densityMeasure ρ : Measure (Torus 1)) = ν := by
  constructor
  · rintro ⟨hν, hF⟩
    exact exists_abs_of_finiteFisher_STR02901 h ν hF
  · rintro ⟨ρ, rfl⟩
    exact ⟨(densityMeasure ρ).prop, str025_fisher_ne_top h ρ⟩

theorem finiteInfo_entropy_ne_top_STR02901 {h : ℝ} {ν : Measure (Torus 1)}
    (hν : FiniteInfo_STR02901 h ν) : relativeEntropy ν (threefoldReference h) ≠ ⊤ := by
  obtain ⟨ρ, rfl⟩ := (finiteInfo_iff_STR02901 h ν).1 hν
  exact str025_entropy_ne_top h ρ

/-- Zero deficit at rate `lam`: a finite-information competitor with
`I_h(ν) - 2 lam H_h(ν) = 0` (both terms finite real numbers). -/
def ZeroDeficit_STR02901 (h lam : ℝ) (ν : Measure (Torus 1)) : Prop :=
  FiniteInfo_STR02901 h ν ∧
    (ordinaryRelativeFisher ν (ordinaryReference h)).toReal -
      2 * lam * (relativeEntropy ν (threefoldReference h)).toReal = 0

theorem zeroDeficit_iff_abs_STR02901 (h lam : ℝ) (ν : Measure (Torus 1)) :
    ZeroDeficit_STR02901 h lam ν ↔ ∃ ρ : AbsoluteDensity 1,
      (densityMeasure ρ : Measure (Torus 1)) = ν ∧
        (ordinaryFisher h ρ).toReal - 2 * lam * (ordinaryEntropy h ρ).toReal = 0 := by
  constructor
  · rintro ⟨hν, hz⟩
    obtain ⟨ρ, rfl⟩ := (finiteInfo_iff_STR02901 h ν).1 hν
    exact ⟨ρ, rfl, hz⟩
  · rintro ⟨ρ, rfl, hz⟩
    exact ⟨(finiteInfo_iff_STR02901 h _).2 ⟨ρ, rfl⟩, hz⟩

theorem zeroDeficit_iff_ennreal_STR02901 {h lam : ℝ} (hlam : 0 ≤ lam) (ν : Measure (Torus 1)) :
    ZeroDeficit_STR02901 h lam ν ↔ FiniteInfo_STR02901 h ν ∧
      ordinaryRelativeFisher ν (ordinaryReference h) =
        ENNReal.ofReal (2 * lam) * relativeEntropy ν (threefoldReference h) := by
  constructor
  · rintro ⟨hν, hz⟩
    refine ⟨hν, ?_⟩
    have hH := finiteInfo_entropy_ne_top_STR02901 hν
    have hrhs : ENNReal.ofReal (2 * lam) * relativeEntropy ν (threefoldReference h) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hH
    refine (ENNReal.toReal_eq_toReal_iff' hν.2 hrhs).1 ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    linarith
  · rintro ⟨hν, he⟩
    refine ⟨hν, ?_⟩
    rw [he, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    ring

/-- The density-measure form of the zero-deficit predicate in angular variables:
`I_h(ρ) - 2 lam H_h(ρ) = a_0 (∫ 4 g'² q_h dm - 2 (lam / a_0) ∫ g² log g² q_h dm)`. -/
theorem zeroDeficit_densityMeasure_iff_ang_STR02901 (h lam : ℝ) (ρ : AbsoluteDensity 1) :
    ZeroDeficit_STR02901 h lam (densityMeasure ρ : Measure (Torus 1)) ↔
      (angFisher_STR02901 h (gAng_STR02901 h ρ)).toReal -
        2 * (lam / DGPS.Circle.AngularNormalization.a0) *
          angEntropy_STR02901 h (gAng_STR02901 h ρ) = 0 := by
  have ha : DGPS.Circle.AngularNormalization.a0 = 4 * Real.pi ^ 2 := rfl
  have ha0 : DGPS.Circle.AngularNormalization.a0 ≠ 0 := by rw [ha]; positivity
  have hapos : 0 ≤ DGPS.Circle.AngularNormalization.a0 := by rw [ha]; positivity
  have key : (ordinaryFisher h ρ).toReal - 2 * lam * (ordinaryEntropy h ρ).toReal =
      DGPS.Circle.AngularNormalization.a0 *
        ((angFisher_STR02901 h (gAng_STR02901 h ρ)).toReal -
          2 * (lam / DGPS.Circle.AngularNormalization.a0) *
            angEntropy_STR02901 h (gAng_STR02901 h ρ)) := by
    rw [ordinaryFisher_eq_angFisher_STR02901, ordinaryEntropy_eq_angEntropy_STR02901,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hapos,
      ENNReal.toReal_ofReal (angEntropy_gAng_nonneg_STR02901 h ρ)]
    field_simp
  rw [zeroDeficit_iff_abs_STR02901]
  constructor
  · rintro ⟨σ, hσ, hz⟩
    have e1 : ordinaryFisher h σ = ordinaryFisher h ρ := by
      unfold ordinaryFisher; rw [hσ]
    have e2 : ordinaryEntropy h σ = ordinaryEntropy h ρ := by
      unfold ordinaryEntropy; rw [hσ]
    rw [e1, e2, key] at hz
    exact (mul_eq_zero.1 hz).resolve_left ha0
  · intro hz
    refine ⟨ρ, rfl, ?_⟩
    rw [key, hz, mul_zero]


theorem gAng_ae_one_of_entropy_zero_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1)
    (h0 : ordinaryEntropy h ρ = 0) : gAng_STR02901 h ρ =ᵐ[angHaar] fun _ => (1 : ℝ) := by
  have hs := str025_sqrt_eq_of_entropy_zero h ρ h0
  refine (ae_comp_angEquiv_iff (p := fun θ => gAng_STR02901 h ρ θ = 1)).1 ?_
  filter_upwards [hs] with x hx
  show gAng_STR02901 h ρ (angEquiv x) = 1
  rw [gAng_comp_STR02901, str025_u_eq, hx]
  exact div_self (str025_w_pos h x).ne'

theorem angEntropy_one_STR02901 (h : ℝ) : angEntropy_STR02901 h (fun _ => (1 : ℝ)) = 0 := by
  simp [angEntropy_STR02901]

theorem entropy_zero_iff_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) :
    ordinaryEntropy h ρ = 0 ↔ gAng_STR02901 h ρ =ᵐ[angHaar] fun _ => (1 : ℝ) := by
  refine ⟨gAng_ae_one_of_entropy_zero_STR02901 h ρ, fun hae => ?_⟩
  rw [ordinaryEntropy_eq_angEntropy_STR02901]
  have : angEntropy_STR02901 h (gAng_STR02901 h ρ) = 0 := by
    unfold angEntropy_STR02901
    rw [← integral_zero AngCircle ℝ (μ := angHaar)]
    refine integral_congr_ae ?_
    filter_upwards [hae] with θ hθ
    rw [hθ]
    simp
  rw [this, ENNReal.ofReal_zero]

theorem angFisher_eq_zero_of_entropy_zero_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1)
    (h0 : ordinaryEntropy h ρ = 0) : angFisher_STR02901 h (gAng_STR02901 h ρ) = 0 := by
  rw [angFisher_eq_STR02901 h (isAngularWeakDeriv_gAng_STR02901 h ρ)]
  have hone := gAng_ae_one_of_entropy_zero_STR02901 h ρ h0
  have hw : IsWeakGradient (gAng_STR02901 h ρ ∘ angEquiv) (physGrad (gDerivAng_STR02901 h ρ)) :=
    (isWeakGradient_comp_iff _ _).1 (isAngularWeakDeriv_gAng_STR02901 h ρ)
  have hu : (gAng_STR02901 h ρ ∘ angEquiv) =ᵐ[haar 1] fun _ => (1 : ℝ) :=
    (ae_comp_angEquiv_iff (p := fun θ => gAng_STR02901 h ρ θ = 1)).2 hone
  have hw1 : IsWeakGradient (fun _ : Torus 1 => (1 : ℝ)) (physGrad (gDerivAng_STR02901 h ρ)) :=
    hw.congr_ae hu (Filter.EventuallyEq.refl _ _)
  have h0g : physGrad (gDerivAng_STR02901 h ρ) =ᵐ[haar 1] fun _ => 0 :=
    hw1.ae_eq (isWeakGradient_const 1)
  have hG : ∀ᵐ θ ∂angHaar, gDerivAng_STR02901 h ρ θ = 0 := by
    refine (ae_comp_angEquiv_iff (p := fun θ => gDerivAng_STR02901 h ρ θ = 0)).1 ?_
    filter_upwards [h0g] with x hx
    have h1 := congrArg (fun v : Tangent 1 => v 0) hx
    simp only [physGrad_apply] at h1
    have h2 : 2 * Real.pi * gDerivAng_STR02901 h ρ (angEquiv x) = 0 := by simpa using h1
    exact (mul_eq_zero.1 h2).resolve_left Real.two_pi_pos.ne'
  have : ∫⁻ θ, ENNReal.ofReal (qAng_STR02901 h θ) * ‖gDerivAng_STR02901 h ρ θ‖ₑ ^ 2 ∂angHaar =
      ∫⁻ _θ, (0 : ℝ≥0∞) ∂angHaar := by
    refine lintegral_congr_ae ?_
    filter_upwards [hG] with θ hθ
    simp [hθ]
  rw [this, lintegral_zero, mul_zero]

theorem ordinaryFisher_eq_zero_of_entropy_zero_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1)
    (h0 : ordinaryEntropy h ρ = 0) : ordinaryFisher h ρ = 0 := by
  rw [ordinaryFisher_eq_angFisher_STR02901, angFisher_eq_zero_of_entropy_zero_STR02901 h ρ h0,
    mul_zero]

theorem zero_entropy_measure_STR02901 {h : ℝ} {ν : Measure (Torus 1)} (hν : FiniteInfo_STR02901 h ν)
    (h0 : relativeEntropy ν (threefoldReference h) = 0) :
    ν = threefoldReference h ∧ ordinaryRelativeFisher ν (ordinaryReference h) = 0 := by
  obtain ⟨ρ, rfl⟩ := (finiteInfo_iff_STR02901 h ν).1 hν
  have h0' : ordinaryEntropy h ρ = 0 := h0
  exact ⟨relativeEntropy_zero_iff.1 h0, ordinaryFisher_eq_zero_of_entropy_zero_STR02901 h ρ h0'⟩

theorem zeroDeficit_reference_STR02901 (h lam : ℝ) :
    ZeroDeficit_STR02901 h lam (threefoldReference h : Measure (Torus 1)) := by
  have hdom : AngDomain_STR02901 h (fun _ => (1 : ℝ)) := by
    refine ⟨?_, Filter.Eventually.of_forall fun θ => zero_le_one, ?_⟩
    · refine ⟨fun _ => 0, ?_⟩
      rw [isWeakGradient_comp_iff]
      have : ((fun _ : AngCircle => (1 : ℝ)) ∘ angEquiv) = fun _ : Torus 1 => (1 : ℝ) := rfl
      rw [this]
      have h0 : physGrad (fun _ : AngCircle => (0 : ℝ)) = fun _ => 0 := by
        funext x
        ext j
        rw [physGrad_apply]
        simp
      rw [h0]
      exact isWeakGradient_const 1
    · simpa using integral_qAng_STR02901 h
  obtain ⟨ρ₀, hρ₀⟩ := exists_abs_of_angDomain_STR02901 h hdom
  have h0 : ordinaryEntropy h ρ₀ = 0 := by
    rw [entropy_zero_iff_STR02901, hρ₀]
  have hμ : (densityMeasure ρ₀ : Measure (Torus 1)) = threefoldReference h :=
    relativeEntropy_zero_iff.1 h0
  rw [zeroDeficit_iff_abs_STR02901]
  refine ⟨ρ₀, hμ, ?_⟩
  rw [h0, ordinaryFisher_eq_zero_of_entropy_zero_STR02901 h ρ₀ h0]
  simp

theorem zeroDeficit_dichotomy_STR02901 {h lam : ℝ} {ν : Measure (Torus 1)}
    (hz : ZeroDeficit_STR02901 h lam ν) :
    (ν = threefoldReference h ∧ ordinaryRelativeFisher ν (ordinaryReference h) = 0) ∨
      ∃ ρ : AbsoluteDensity 1, (densityMeasure ρ : Measure (Torus 1)) = ν ∧
        0 < ordinaryEntropy h ρ ∧ (str025_quot h ρ).toReal = lam := by
  obtain ⟨ρ, hρ, hdef⟩ := (zeroDeficit_iff_abs_STR02901 h lam ν).1 hz
  by_cases h0 : ordinaryEntropy h ρ = 0
  · left
    subst hρ
    exact ⟨relativeEntropy_zero_iff.1 h0, ordinaryFisher_eq_zero_of_entropy_zero_STR02901 h ρ h0⟩
  · right
    refine ⟨ρ, hρ, pos_iff_ne_zero.2 h0, ?_⟩
    have hpos : 0 < (ordinaryEntropy h ρ).toReal :=
      ENNReal.toReal_pos h0 (str025_entropy_ne_top h ρ)
    unfold str025_quot
    rw [ENNReal.toReal_div, ENNReal.toReal_mul]
    simp only [ENNReal.toReal_ofNat]
    rw [div_eq_iff (by positivity)]
    linarith


/-! ### Rate coordinate, density identity and smallness for the chart sequence -/

section ChartTransfer

variable {α : ℝ} [HolderExponent α]

/-- The fourth chart coordinate is the angular rate `I_h(ρ) / (2 H_h(ρ)) - 1`: the physical
quotient `str025_quot` divided by `a_0 = 4π²` is the angular quotient. -/
theorem chart_rate_coordinate_STR02901 (h : ℝ) (ρ : AbsoluteDensity 1) {p3 : ℝ}
    (hp : 1 + p3 = (str025_quot h ρ).toReal / (4 * Real.pi ^ 2)) :
    p3 = (angFisher_STR02901 h (gAng_STR02901 h ρ)).toReal /
      (2 * angEntropy_STR02901 h (gAng_STR02901 h ρ)) - 1 := by
  rw [str025_quot_toReal_STR02901] at hp
  linarith

/-- The packet density identity (stated for unit-period representatives `torusLift (fun _ => s)`)
gives the angular a.e. identity `ρ = ρ(h, p₀ cos t + p₁ sin t + w)` with respect to `m(dt)` on the
section `[0, 2π)` of `ℝ / 2πℤ`. -/
theorem density_ae_angular_STR02901 (ρ : AbsoluteDensity 1) (x : Par × Wsp α)
    (H : ∀ᵐ y ∂haar 1, ∀ s : ℝ, torusLift (fun _ => s) = y → ρ.density y = (rho α x).val s) :
    ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) =
      rhoT_STR02901 (x.1 2) (uT_STR02901 (x.1 0) (x.1 1) (wT_STR02901 (x.2 : PH α 2))) (angSec θ) := by
  refine (ae_comp_angEquiv_iff (p := fun θ => ρ.density (angEquiv.symm θ) =
      rhoT_STR02901 (x.1 2) (uT_STR02901 (x.1 0) (x.1 1) (wT_STR02901 (x.2 : PH α 2)))
        (angSec θ))).1 ?_
  filter_upwards [H] with y hy
  have hs : torusLift (fun _ : Fin 1 => SharpLSI.secT y 0) = y := by
    have e : (fun _ : Fin 1 => SharpLSI.secT y 0) = SharpLSI.secT y := by
      funext i; rw [Subsingleton.elim i 0]
    rw [e]; exact SharpLSI.liftT_secT y
  show ρ.density (angEquiv.symm (angEquiv y)) = rhoT_STR02901 _ _ (angSec (angEquiv y))
  rw [angEquiv.symm_apply_apply, angSec_angEquiv, hy _ hs, rho_val_STR02901]

/-- Smallness of the packet chart point controls `|p| + ‖w‖_{C^{2,α}}`. -/
theorem tendsto_small_STR02901 {x : ℕ → Par × Wsp α} (hx : Tendsto x atTop (𝓝 0)) :
    Tendsto (fun j => Real.sqrt (∑ i, (x j).1 i ^ 2) +
      c2Norm_STR02901 α (wT_STR02901 ((x j).2 : PH α 2))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun j => (x j).1) atTop (𝓝 0) := by
    exact (continuous_fst.tendsto (0 : Par × Wsp α)).comp hx
  have h2 : Tendsto (fun j => (x j).2) atTop (𝓝 0) := by
    exact (continuous_snd.tendsto (0 : Par × Wsp α)).comp hx
  have n1 : Tendsto (fun j => ‖(x j).1‖) atTop (𝓝 0) := by
    simpa using h1.norm
  have n2 : Tendsto (fun j => ‖((x j).2 : PH α 2)‖) atTop (𝓝 0) := by
    simpa using h2.norm
  have hb : Tendsto (fun j => 2 * ‖(x j).1‖ + ‖((x j).2 : PH α 2)‖) atTop (𝓝 0) := by
    simpa using (n1.const_mul 2).add n2
  refine squeeze_zero (fun j => ?_) (fun j => ?_) hb
  · have := c2Norm_wT_ge_STR02901 ((x j).2 : PH α 2)
    have h0 : 0 ≤ ((2 * Real.pi)⁻¹) ^ 2 * ((2 * Real.pi)⁻¹) ^ α * ‖((x j).2 : PH α 2)‖ := by
      positivity
    have := Real.sqrt_nonneg (∑ i, (x j).1 i ^ 2)
    linarith
  · have hc := c2Norm_wT_le_STR02901 ((x j).2 : PH α 2)
    have hsq : Real.sqrt (∑ i, (x j).1 i ^ 2) ≤ 2 * ‖(x j).1‖ := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have b : ∀ i, (x j).1 i ^ 2 ≤ ‖(x j).1‖ ^ 2 := fun i => by
        have := norm_le_pi_norm (x j).1 i
        rw [Real.norm_eq_abs] at this
        exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
      simp only [Fin.sum_univ_four]
      nlinarith [b 0, b 1, b 2, b 3]
    linarith

/-- The sup norm and the Euclidean norm on the parameter space `Fin 4 → ℝ` are equivalent. -/
theorem par_norm_equiv_STR02901 (p : Par) :
    ‖p‖ ≤ Real.sqrt (∑ i, p i ^ 2) ∧ Real.sqrt (∑ i, p i ^ 2) ≤ 2 * ‖p‖ := by
  constructor
  · refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun i => p i ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  · rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have b : ∀ i, p i ^ 2 ≤ ‖p‖ ^ 2 := fun i => by
      have := norm_le_pi_norm p i
      rw [Real.norm_eq_abs] at this
      exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
    simp only [Fin.sum_univ_four]
    nlinarith [b 0, b 1, b 2, b 3]

/-- Smallness of a packet chart sequence is equivalent to smallness of `|p| + ‖w‖_{C^{2,α}}`
for the concrete (Euclidean, circular-Hölder) norms. -/
theorem tendsto_small_iff_STR02901 (x : ℕ → Par × Wsp α) :
    Tendsto x atTop (𝓝 0) ↔
      Tendsto (fun j => Real.sqrt (∑ i, (x j).1 i ^ 2) +
        c2Norm_STR02901 α (wT_STR02901 ((x j).2 : PH α 2))) atTop (𝓝 0) := by
  refine ⟨tendsto_small_STR02901, fun hs => ?_⟩
  set K : ℝ := ((2 * Real.pi)⁻¹) ^ 2 * ((2 * Real.pi)⁻¹) ^ α with hK
  have hKpos : 0 < K := by positivity
  have hc : ∀ j, 0 ≤ c2Norm_STR02901 α (wT_STR02901 ((x j).2 : PH α 2)) := fun j =>
    (mul_nonneg hKpos.le (norm_nonneg _)).trans (c2Norm_wT_ge_STR02901 ((x j).2 : PH α 2))
  have hb : Tendsto (fun j => (Real.sqrt (∑ i, (x j).1 i ^ 2) +
      c2Norm_STR02901 α (wT_STR02901 ((x j).2 : PH α 2))) * (1 + K⁻¹)) atTop (𝓝 0) := by
    simpa using hs.mul_const (1 + K⁻¹)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hb
  have e : ‖x j‖ = max ‖(x j).1‖ ‖((x j).2 : PH α 2)‖ := rfl
  have h1 := (par_norm_equiv_STR02901 (x j).1).1
  have h2 := c2Norm_wT_ge_STR02901 ((x j).2 : PH α 2)
  have h3 : ‖((x j).2 : PH α 2)‖ ≤ c2Norm_STR02901 α (wT_STR02901 ((x j).2 : PH α 2)) * K⁻¹ := by
    rw [← hK] at h2
    rw [le_mul_inv_iff₀ hKpos]
    linarith
  have h4 := Real.sqrt_nonneg (∑ i, (x j).1 i ^ 2)
  rw [e]
  refine max_le ?_ ?_
  · nlinarith [hc j, inv_nonneg.2 hKpos.le, mul_nonneg (hc j) (inv_nonneg.2 hKpos.le)]
  · nlinarith [hc j, mul_nonneg h4 (inv_nonneg.2 hKpos.le)]

end ChartTransfer


/-! ### Identification of the packet carriers with the concrete ones -/

section CarrierEquiv

variable (α : ℝ) [HolderExponent α]

/-- The concrete `C^{2,α}` function of `t` (orthogonal to `1, cos t, sin t`) attached to a packet
chart-space element `w ∈ Wsp α`, namely `t ↦ w(t / 2π)`. -/
noncomputable def wspToConcrete_STR02901 (f : Wsp α) :
    {w : ℝ → ℝ // IsC2Alpha_STR02901 α w ∧ InE_STR02901 w} :=
  ⟨wT_STR02901 (f : PH α 2), isC2Alpha_wT_STR02901 _,
    (mem_orthSub_iff_InE_STR02901 _).1 f.2⟩

theorem wspToConcrete_bijective_STR02901 :
    Function.Bijective (wspToConcrete_STR02901 α) := by
  constructor
  · intro f g hfg
    have := congrArg Subtype.val hfg
    exact Subtype.ext (wT_injective_STR02901 this)
  · rintro ⟨w, hw, hE⟩
    obtain ⟨f, rfl⟩ := exists_wT_of_isC2Alpha_STR02901 hw
    exact ⟨⟨f, (mem_orthSub_iff_InE_STR02901 f).2 hE⟩, rfl⟩

/-- The packet chart space `Wsp α` is in bijection with the concrete space
`E ∩ C^{2,α}` of `2π`-periodic functions. -/
noncomputable def wspEquiv_STR02901 :
    Wsp α ≃ {w : ℝ → ℝ // IsC2Alpha_STR02901 α w ∧ InE_STR02901 w} :=
  Equiv.ofBijective _ (wspToConcrete_bijective_STR02901 α)

theorem wspEquiv_norm_STR02901 :
    ∃ K : ℝ, 0 < K ∧ ∀ f : Wsp α,
      c2Norm_STR02901 α (wspEquiv_STR02901 α f).1 ≤ ‖f‖ ∧
        K * ‖f‖ ≤ c2Norm_STR02901 α (wspEquiv_STR02901 α f).1 :=
  ⟨((2 * Real.pi)⁻¹) ^ 2 * ((2 * Real.pi)⁻¹) ^ α, by positivity,
    fun f => ⟨c2Norm_wT_le_STR02901 (f : PH α 2), c2Norm_wT_ge_STR02901 (f : PH α 2)⟩⟩

theorem holderExponent_half_STR02901 : HolderExponent (1 / 2 : ℝ) :=
  ⟨by norm_num, by norm_num⟩

end CarrierEquiv

/-! ### Public declarations -/

section Public

/-- **Carrier identification.**  The packet parameter space is literally `Fin 4 → ℝ`, with
coordinates `(a, b, h, γ) = (p 0, p 1, p 2, p 3)`; the packet chart space `Wsp α` is in bijection with
the concrete functions `w` of `t` that are `2π`-periodic, `C^{2,α}` (circular Hölder seminorm for
`w''`) and orthogonal to `1, cos t, sin t`, via `f ↦ (t ↦ f(t / 2π))`; the concrete `C^{2,α}`
norm is bounded above by the packet norm with constant `1` and below by a positive multiple of it. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational_carrier_equiv
    (α : ℝ) [HolderExponent α] :
    Function.Bijective (wspToConcrete_STR02901 α) ∧
      (∀ f : Wsp α, (wspToConcrete_STR02901 α f).1 = fun t => (f : PH α 2).val (t / (2 * Real.pi))) ∧
      (∀ f : Wsp α, ∀ s : ℝ, (wspToConcrete_STR02901 α f).1 (2 * Real.pi * s) = (f : PH α 2).val s) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ f : Wsp α,
        c2Norm_STR02901 α (wspToConcrete_STR02901 α f).1 ≤ ‖f‖ ∧
          K * ‖f‖ ≤ c2Norm_STR02901 α (wspToConcrete_STR02901 α f).1 :=
  ⟨wspToConcrete_bijective_STR02901 α, fun _ => rfl,
    fun f s => wT_apply_STR02901 (f : PH α 2) s, wspEquiv_norm_STR02901 α⟩

/-- **Norm equivalences.**  The sup norm and the Euclidean norm on the parameter space `Par` satisfy
`‖p‖ ≤ |p| ≤ 2 ‖p‖`, and smallness of a packet chart sequence is equivalent to
`|p_n| + ‖w_n‖_{C^{2,α}} → 0` for the Euclidean norm of `p_n` and the concrete `C^{2,α}` norm of
`w_n`. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational_norm_equiv
    (α : ℝ) [HolderExponent α] :
    (∀ p : Par, ‖p‖ ≤ Real.sqrt (∑ i, p i ^ 2) ∧ Real.sqrt (∑ i, p i ^ 2) ≤ 2 * ‖p‖) ∧
      ∀ x : ℕ → Par × Wsp α, Tendsto x atTop (𝓝 0) ↔
        Tendsto (fun j => Real.sqrt (∑ i, (x j).1 i ^ 2) +
          c2Norm_STR02901 α (wT_STR02901 ((x j).2 : PH α 2))) atTop (𝓝 0) :=
  ⟨fun p => par_norm_equiv_STR02901 p, fun x => tendsto_small_iff_STR02901 x⟩

/-- **The packet density in angular variables.**  For `x = (p, w)`,
`rho α x` at the unit-period point `s` is `e^{p₂ cos 3t + p₀ cos t + p₁ sin t + w(t)} / ∫ e^{…} dm`
at `t = 2π s`. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational_rho_val
    (α : ℝ) [HolderExponent α] (x : Par × Wsp α) (s : ℝ) :
    (rho α x).val s =
      rhoT_STR02901 (x.1 2) (uT_STR02901 (x.1 0) (x.1 1) (wT_STR02901 (x.2 : PH α 2)))
        (2 * Real.pi * s) :=
  rho_val_STR02901 x s

/-- **Positive smooth log representation.**  For continuous `u`, the concrete density
`ρ(h, u)` is strictly positive, and its logarithm is `h cos 3t + u(t) - log ∫ e^{h cos 3s + u(s)} dm`. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational_positive_log
    (h : ℝ) {u : ℝ → ℝ} (hu : Continuous u) (t : ℝ) :
    0 < rhoT_STR02901 h u t ∧
      Real.log (rhoT_STR02901 h u t) = h * Real.cos (3 * t) + u t -
        Real.log (meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u s))) := by
  refine ⟨rhoT_pos_STR02901 h hu t, ?_⟩
  have hm : 0 < meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u s)) :=
    meanT_pos_STR02901 (by fun_prop) fun s => Real.exp_pos _
  unfold rhoT_STR02901
  rw [Real.log_div (Real.exp_pos _).ne' hm.ne', Real.log_exp]

/-- **Entropy.**  `ordinaryEntropy` is `∫ g² log g² q_h dm` for `g = √(ρ / q_h)`; this angular
entropy is nonnegative, so the `ENNReal` value is its `ofReal`. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational_entropy
    (h : ℝ) (ρ : AbsoluteDensity 1) :
    ordinaryEntropy h ρ = ENNReal.ofReal (angEntropy_STR02901 h (gAng_STR02901 h ρ)) ∧
      0 ≤ angEntropy_STR02901 h (gAng_STR02901 h ρ) :=
  ⟨ordinaryEntropy_eq_angEntropy_STR02901 h ρ, angEntropy_gAng_nonneg_STR02901 h ρ⟩

/-- **Fisher information.**  `ordinaryFisher` is `a_0` times the angular Fisher information
`4 ∫ g'² q_h dm` of `g = √(ρ / q_h)`; the angular Fisher information is finite on `H¹`. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational_fisher
    (h : ℝ) (ρ : AbsoluteDensity 1) :
    ordinaryFisher h ρ =
        ENNReal.ofReal DGPS.Circle.AngularNormalization.a0 *
          angFisher_STR02901 h (gAng_STR02901 h ρ) ∧
      angFisher_STR02901 h (gAng_STR02901 h ρ) ≠ ⊤ :=
  ⟨ordinaryFisher_eq_angFisher_STR02901 h ρ,
    angFisher_ne_top_STR02901 h (isAngularWeakDeriv_gAng_STR02901 h ρ)⟩

/-- **Angular Fisher formula and convention.**  With a weak derivative `G` the value is
`4 ∫ q_h G² dm`; without any the value is `⊤`. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational_fisher_formula
    (h : ℝ) (g : AngCircle → ℝ) :
    (∀ G : AngCircle → ℝ, IsAngularWeakDeriv g G →
      angFisher_STR02901 h g =
        4 * ∫⁻ θ, ENNReal.ofReal (qAng_STR02901 h θ) * ‖G θ‖ₑ ^ 2 ∂angHaar) ∧
      (¬ AngularH1 g → angFisher_STR02901 h g = ⊤) :=
  ⟨fun _ hG => angFisher_eq_STR02901 h hG, fun hg => angFisher_eq_top_STR02901 h hg⟩

/-- **Domain.**  Every absolute density gives an angular admissible `g`, and every angular
admissible `g` (nonnegative periodic `H¹`, `∫ g² q_h dm = 1`) arises from an absolute density;
a.e. equality of the densities is a.e. equality of the `g`'s. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational_domain
    (h : ℝ) :
    (∀ ρ : AbsoluteDensity 1, AngDomain_STR02901 h (gAng_STR02901 h ρ)) ∧
      (∀ g : AngCircle → ℝ, AngDomain_STR02901 h g →
        ∃ ρ : AbsoluteDensity 1, gAng_STR02901 h ρ = g) ∧
      (∀ ρ ρ' : AbsoluteDensity 1,
        gAng_STR02901 h ρ =ᵐ[angHaar] gAng_STR02901 h ρ' ↔ ρ.density =ᵐ[haar 1] ρ'.density) :=
  ⟨angDomain_gAng_STR02901 h, fun _ hg => exists_abs_of_angDomain_STR02901 h hg,
    gAng_ae_eq_iff_STR02901 h⟩

/-- **Quotient and units.**  The physical quotient is `a_0` times the angular quotient, and the
fourth chart coordinate (`quotient / (4π²)`) is the angular quotient `I / (2H)`. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational_quotient
    (h : ℝ) (ρ : AbsoluteDensity 1) :
    str025_quot h ρ =
        ENNReal.ofReal DGPS.Circle.AngularNormalization.a0 *
          angQuot_STR02901 h (gAng_STR02901 h ρ) ∧
      (str025_quot h ρ).toReal / (4 * Real.pi ^ 2) =
        (angFisher_STR02901 h (gAng_STR02901 h ρ)).toReal /
          (2 * angEntropy_STR02901 h (gAng_STR02901 h ρ)) :=
  ⟨str025_quot_eq_angQuot_STR02901 h ρ, str025_quot_toReal_STR02901 h ρ⟩

/-- **Optimizer transfer.**  Global optimality among positive-entropy absolute densities is the same
as global optimality of `g = √(ρ / q_h)` among positive-entropy angular admissible functions. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational_optimizer_transfer
    (h : ℝ) (ρ : AbsoluteDensity 1) :
    (∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' → str025_quot h ρ ≤ str025_quot h ρ') ↔
      (∀ g' : AngCircle → ℝ, AngDomain_STR02901 h g' → 0 < angEntropy_STR02901 h g' →
        angQuot_STR02901 h (gAng_STR02901 h ρ) ≤ angQuot_STR02901 h g') :=
  optimizer_transfer_STR02901 h ρ

/-- **Finite competitors.**  A probability measure with finite ordinary Fisher information relative
to `q_h` is the density measure of an absolute density; two absolute densities have equal density
measures iff their densities agree a.e. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational_finite_competitor
    (h : ℝ) :
    (∀ ν : Measure (Torus 1), FiniteInfo_STR02901 h ν ↔
      ∃ ρ : AbsoluteDensity 1, (densityMeasure ρ : Measure (Torus 1)) = ν) ∧
      (∀ ρ ρ' : AbsoluteDensity 1, (densityMeasure ρ : Measure (Torus 1)) = densityMeasure ρ' ↔
        ρ.density =ᵐ[haar 1] ρ'.density) :=
  ⟨finiteInfo_iff_STR02901 h, densityMeasure_eq_iff_STR02901⟩

/-- **Zero-deficit competitors (absolute form).**  A zero-deficit competitor at rate `lam` is
exactly the density measure of an absolute density with real `I - 2 lam H = 0`. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational_zero_deficit_abs
    (h lam : ℝ) (ν : Measure (Torus 1)) :
    ZeroDeficit_STR02901 h lam ν ↔ ∃ ρ : AbsoluteDensity 1,
      (densityMeasure ρ : Measure (Torus 1)) = ν ∧
        (ordinaryFisher h ρ).toReal - 2 * lam * (ordinaryEntropy h ρ).toReal = 0 :=
  zeroDeficit_iff_abs_STR02901 h lam ν

/-- **Zero-deficit competitors (angular form, physical factor).**  In angular variables the
deficit of `ρ` at rate `lam` is `a_0 (I_ang - 2 (lam / a_0) H_ang)`. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational_zero_deficit_angular
    (h lam : ℝ) (ρ : AbsoluteDensity 1) :
    ZeroDeficit_STR02901 h lam (densityMeasure ρ : Measure (Torus 1)) ↔
      (angFisher_STR02901 h (gAng_STR02901 h ρ)).toReal -
        2 * (lam / DGPS.Circle.AngularNormalization.a0) *
          angEntropy_STR02901 h (gAng_STR02901 h ρ) = 0 :=
  zeroDeficit_densityMeasure_iff_ang_STR02901 h lam ρ

/-- **Zero deficit with `ENNReal` values.**  For `0 ≤ lam`, zero deficit is finite information plus
the identity `I = ofReal (2 lam) * H` in `[0, ⊤]`. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational_zero_deficit_ennreal
    {h lam : ℝ} (hlam : 0 ≤ lam) (ν : Measure (Torus 1)) :
    ZeroDeficit_STR02901 h lam ν ↔ FiniteInfo_STR02901 h ν ∧
      ordinaryRelativeFisher ν (ordinaryReference h) =
        ENNReal.ofReal (2 * lam) * relativeEntropy ν (threefoldReference h) :=
  zeroDeficit_iff_ennreal_STR02901 hlam ν

/-- **Zero entropy.**  Entropy zero forces `g = 1` a.e. (that is, `ρ = q_h`), and then the Fisher
information vanishes. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational_zero_entropy
    (h : ℝ) (ρ : AbsoluteDensity 1) :
    (ordinaryEntropy h ρ = 0 ↔ gAng_STR02901 h ρ =ᵐ[angHaar] fun _ => (1 : ℝ)) ∧
      (ordinaryEntropy h ρ = 0 → ordinaryFisher h ρ = 0) :=
  ⟨entropy_zero_iff_STR02901 h ρ, ordinaryFisher_eq_zero_of_entropy_zero_STR02901 h ρ⟩

/-- **Zero entropy for measures.**  A finite-information measure of relative entropy zero is `q_h`
and has zero Fisher information. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational_zero_entropy_measure
    {h : ℝ} {ν : Measure (Torus 1)} (hν : FiniteInfo_STR02901 h ν)
    (h0 : relativeEntropy ν (threefoldReference h) = 0) :
    ν = threefoldReference h ∧ ordinaryRelativeFisher ν (ordinaryReference h) = 0 :=
  zero_entropy_measure_STR02901 hν h0

/-- **The reference is zero-deficit.**  `q_h` has zero deficit at every rate. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational_reference
    (h lam : ℝ) : ZeroDeficit_STR02901 h lam (threefoldReference h) :=
  zeroDeficit_reference_STR02901 h lam

/-- **Zero-deficit dichotomy.**  A zero-deficit competitor is either `q_h` (entropy zero, Fisher
zero) or the density measure of an absolute density of positive entropy whose quotient is `lam`. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational_zero_deficit_dichotomy
    {h lam : ℝ} {ν : Measure (Torus 1)} (hz : ZeroDeficit_STR02901 h lam ν) :
    (ν = threefoldReference h ∧ ordinaryRelativeFisher ν (ordinaryReference h) = 0) ∨
      ∃ ρ : AbsoluteDensity 1, (densityMeasure ρ : Measure (Torus 1)) = ν ∧
        0 < ordinaryEntropy h ρ ∧ (str025_quot h ρ).toReal = lam :=
  zeroDeficit_dichotomy_STR02901 hz

end Public


/-! ### The common optimizer witness -/

section Main

/-- **Gate STR029.01.**  Under exactly the hypotheses of the printed STR028 theorem
`threefold_allOptimizers_near_three_minima`, a single chart sequence `x = (p, w)` exists that
simultaneously
1. satisfies the printed STR028 conclusion (`IsChartRep_STR028b3` and the amplitude localization);
2. localizes the amplitude `(p₀ / h, p₁ / h)` near the explicit points `(2, 0)`, `(-1, ±√3)`;
3. has `p₂ = h_n` and `p₃ = I / (2H) - 1` (angular Fisher and entropy of `g = √(ρ / q_h)`) for all `n`;
4. satisfies eventually the angular a.e. density identity `ρ_n = ρ(h_n, p₀ cos t + p₁ sin t + w_n)`
   for the concrete `2π`-periodic `w_n`;
5. has `|p_n| + ‖w_n‖_{C^{2,α}} → 0`;
6. has `w_n` concrete `C^{2,α}`, `2π`-periodic and in `E`;
7. is such that each `g_n = √(ρ_n / q_{h_n})` is angular admissible, of positive entropy, and
   minimizes the angular quotient over all positive-entropy angular admissible competitors. -/
theorem gate_str029_01_bind_common_optimizer_witness_absolute_variational
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ᶠ j in atTop, h j ≠ 0)
    (ρ : ℕ → AbsoluteDensity 1) (hpos : ∀ j, 0 < ordinaryEntropy (h j) (ρ j))
    (hmin : ∀ j, ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy (h j) ρ' →
      ordinaryFisher (h j) (ρ j) / (2 * ordinaryEntropy (h j) (ρ j)) ≤
        ordinaryFisher (h j) ρ' / (2 * ordinaryEntropy (h j) ρ'))
    (α : ℝ) [HolderExponent α] :
    ∃ x : ℕ → Par × Wsp α,
      (IsChartRep_STR028b3 h ρ x ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∃ A B : ℝ, A ^ 2 + B ^ 2 ≠ 0 ∧
          reducedQuotient A B = -16 / 15 ∧
          ((x j).1 0 / h j - A) ^ 2 + ((x j).1 1 / h j - B) ^ 2 < η ^ 2) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∃ A B : ℝ,
        ((A = 2 ∧ B = 0) ∨ (A = -1 ∧ B = Real.sqrt 3) ∨ (A = -1 ∧ B = -Real.sqrt 3)) ∧
          ((x j).1 0 / h j - A) ^ 2 + ((x j).1 1 / h j - B) ^ 2 < ε ^ 2) ∧
      (∀ j, (x j).1 2 = h j) ∧
      (∀ j, (x j).1 3 =
        (angFisher_STR02901 (h j) (gAng_STR02901 (h j) (ρ j))).toReal /
          (2 * angEntropy_STR02901 (h j) (gAng_STR02901 (h j) (ρ j))) - 1) ∧
      (∀ᶠ j in atTop, ∀ᵐ θ ∂angHaar, (ρ j).density (angEquiv.symm θ) =
        rhoT_STR02901 (h j)
          (uT_STR02901 ((x j).1 0) ((x j).1 1) (wT_STR02901 ((x j).2 : PH α 2))) (angSec θ)) ∧
      Tendsto (fun j => Real.sqrt (∑ i, (x j).1 i ^ 2) +
        c2Norm_STR02901 α (wT_STR02901 ((x j).2 : PH α 2))) atTop (𝓝 0) ∧
      (∀ j, IsC2Alpha_STR02901 α (wT_STR02901 ((x j).2 : PH α 2)) ∧
        InE_STR02901 (wT_STR02901 ((x j).2 : PH α 2))) ∧
      (∀ j, AngDomain_STR02901 (h j) (gAng_STR02901 (h j) (ρ j)) ∧
        0 < angEntropy_STR02901 (h j) (gAng_STR02901 (h j) (ρ j)) ∧
        ∀ g' : AngCircle → ℝ, AngDomain_STR02901 (h j) g' → 0 < angEntropy_STR02901 (h j) g' →
          angQuot_STR02901 (h j) (gAng_STR02901 (h j) (ρ j)) ≤ angQuot_STR02901 (h j) g') := by
  obtain ⟨x, hx, hm⟩ := threefold_allOptimizers_near_three_minima h hh hne ρ hpos hmin α
  refine ⟨x, ⟨hx, hm⟩, ?_, fun j => (hx.2.1 j).1, ?_, ?_, tendsto_small_STR02901 hx.1,
    fun j => ⟨isC2Alpha_wT_STR02901 _, (mem_orthSub_iff_InE_STR02901 _).1 (x j).2.2⟩, ?_⟩
  · intro ε hε
    filter_upwards [hm ε hε] with j hj
    obtain ⟨A, B, hAB, hq, hlt⟩ := hj
    exact ⟨A, B, ((reducedQuotient_exact_minimizers.2.2.2.1 A B hAB).2.1 hq), hlt⟩
  · intro j
    exact chart_rate_coordinate_STR02901 (h j) (ρ j) (hx.2.1 j).2
  · filter_upwards [hx.2.2] with j hj
    have := density_ae_angular_STR02901 (ρ j) (x j) hj
    rwa [(hx.2.1 j).1] at this
  · intro j
    refine ⟨angDomain_gAng_STR02901 (h j) (ρ j),
      (ordinaryEntropy_pos_iff_STR02901 (h j) (ρ j)).1 (hpos j), ?_⟩
    refine (optimizer_transfer_STR02901 (h j) (ρ j)).1 ?_
    intro ρ' hρ'
    have := hmin j ρ' hρ'
    exact this

end Main

end DGPS.Frontier.STR029
