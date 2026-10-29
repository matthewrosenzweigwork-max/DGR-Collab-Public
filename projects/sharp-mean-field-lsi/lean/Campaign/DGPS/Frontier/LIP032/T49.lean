import DGPS.Frontier.LIP032.T48
import DGPS.Model.ScalarRate
import DGPS.Model.Drift

/-!
## Bindings (LIP032.49, "OPEN named density, drift, dissipation, and rate binding")

Every row was obtained by printing the actual declaration in this worktree (base `587b363`).
Paths are relative to `Campaign/`. `Frontier.LIP032.` abbreviates `DGPS.Frontier.LIP032.`.

| Source object in the specification | Actual declaration (full name, file:line) | Type / binder list | Discrepancy with the specification text |
|---|---|---|---|
| the torus `X`, Haar probability `m` | `DGPS.Torus` (abbrev), `DGPS.haar` (abbrev), `DGPS/Foundations/Torus.lean:32`, `:35` | `Torus (d : ℕ)`; `haar (d : ℕ) : Measure (Torus d)` | none |
| `AbsoluteDensity 1` | `DGPS.AbsoluteDensity`, `DGPS/Foundations/AbsoluteDensity.lean:35` | structure `(d : ℕ)` with fields `sqrt : Torus d → ℝ`, `sqrt_mem : sqrt ∈ H1Haar d`, `sqrt_nonneg : 0 ≤ᵐ[haar d] sqrt`, `mass_one : ∫ x, sqrt x ^ 2 ∂haar d = 1` | a density is stored through its square root `u`, not as a function `ρ`; the density is `AbsoluteDensity.density = sqrt ^ 2` (`:42`). So `ρ_H` is the structure with `sqrt = fun _ => 1` |
| `H¹(m)`, weak gradient `∇u` | `DGPS.H1Haar` (`AbsoluteDensity.lean:24`), `DGPS.MemH1` (`DGPS/Foundations/Torus.lean:133`), `DGPS.IsWeakGradient` (`:126`), `DGPS.weakGradient` (`:137`), `DGPS.isWeakGradient_weakGradient` (`:140`) | `weakGradient (u : Torus d → ℝ) (hu : MemH1 u) : Torus d → Tangent d`, the `Classical.choose` of the membership proof | the gradient of `√ρ_H` is a chosen representative, determined only a.e. (`DGPS.weakGradient_ae_eq`, `DGPS/Foundations/WeakSobolev.lean:175`); never an explicit formula |
| the probability `ρ m` | `DGPS.densityMeasure`, `AbsoluteDensity.lean:75` (`densityMeasure_coe`, `:79`) | `(ρ : AbsoluteDensity d) : ProbabilityMeasure (Torus d)`, the `withDensity ofReal (sqrt ^ 2)` of `haar d` | a `ProbabilityMeasure`, not a `Measure`; the coercion to `Measure` is `toMeasure` |
| interaction data `A_*` | `Frontier.LIP032.interactionDataStar_LIP03241`, `DGPS/Frontier/LIP032/T41.lean:301`, with `gammaStar_LIP03241` (`:82`), `VStar_LIP03241` (`:86`), `WStar_LIP03241` (`:90`), `momentStar_LIP03241` (`:94`); the structure is `DGPS.InteractionData`, `DGPS/Model/Data.lean:22` | `interactionDataStar_LIP03241 : InteractionData 1`; `V_* = -4 γ²`, `W_*(x,y) = 4 (γ x - γ y)²`, `γ = cosMode` | none |
| the potential `V_* + W_* * (ρ m)` | `DGPS.interactionPotential`, `DGPS/Model/Drift.lean:38` (`interactionPotential_eq`, `:43`) | `(A : InteractionData d) (ρ : AbsoluteDensity d) : Torus d → ℝ`, `x ↦ A.V x + ∫ y, A.W x y ∂(densityMeasure ρ)` | the integral is against the probability `ρ m` (not `ρ` times `dm`); at `ρ_H` it is the Task 48 function `x ↦ V_* x + ∫ y, W_* x y ∂haar 1` (here: `interactionPotential_absoluteRhoH_LIP03249`, the constant `2`) |
| `drift_* : AbsoluteDrift A_*` | `DGPS.AbsoluteDrift`, `DGPS/Model/Drift.lean:104`; uniqueness `DGPS.absoluteDrift_unique` (`:146`), `DGPS.AbsoluteDrift.ae_eq_of_isWeakGradient` (`:121`), `DGPS.IsWeakGradientLp.ae_eq_of_one` (`:56`) | structure `(A : InteractionData d)` with `force : AbsoluteDensity d → Torus d → Tangent d`, `measurable_force : ∀ ρ, Measurable (force ρ)`, `weak_gradient : ∀ ρ, IsWeakGradientLp 1 (interactionPotential A ρ) (force ρ)` | a TOTAL provider: an `L¹` weak gradient is required for EVERY absolute density, not only for `ρ_H`; it is `L¹`, not `L²` (`DGPS.IsWeakGradientLp`, `DGPS/Foundations/PeriodicSmoothing.lean:368`). The explicit `G_*`, `B_*` of the specification are not fields |
| classical gradient of a smooth periodic function | `DGPS.smoothGrad`, `PeriodicSmoothing.lean:405`; `DGPS.IsSmoothPeriodic` (`Torus.lean:117`), `IsSmoothPeriodic.continuous_smoothGrad` (`PeriodicSmoothing.lean:411`), `IsSmoothPeriodic.isWeakGradient` (`:416`) | `smoothGrad (φ : Torus d → ℝ) (x : Torus d) : Tangent d`, the coordinate partials of the lift | used as the force of `drift_*`; it is an `L²` (hence `L¹`) weak gradient of every smooth periodic potential |
| `scalarGap A_* ρ_H` | `DGPS.scalarGap`, `DGPS/Model/ScalarRate.lean:49` (`coe_scalarGap`, `:53`) | `(A : InteractionData d) (ρ : AbsoluteDensity d) : ℝ≥0`, value `densityFreeEnergy A ρ - freeEnergyMinimumReal A` with a nonnegativity proof | valued in `ℝ≥0`; the specification's "`(scalarGap A_* ρ_H : ℝ)`" is the coercion `((scalarGap A_* ρ_H : ℝ≥0) : ℝ)` |
| free energy of a density, minimum `E_{*,min}` | `DGPS.densityFreeEnergy` (`ScalarRate.lean:33`, `coe_densityFreeEnergy` `:36`), `DGPS.freeEnergy` (`DGPS/Model/FreeEnergy.lean:47`), `DGPS.freeEnergyMinimum` (`:53`), `DGPS.freeEnergyMinimumReal` (`:181`), `DGPS.coe_freeEnergyMinimumReal` (`:184`) | `freeEnergy A ν : EReal`; `freeEnergyMinimum A : EReal`; `densityFreeEnergy A ρ : ℝ`; `freeEnergyMinimumReal A = (freeEnergyMinimum A).toReal` | Task 48 works in `EReal`; the campaign gap is real. They are linked by `coe_freeEnergyMinimumReal` |
| the source gap `G_H` | `Frontier.LIP032.gap_LIP03248`, `DGPS/Frontier/LIP032/T48.lean:112` | `((1 / 8 : ℝ) : EReal) ≤ (0 : EReal) - freeEnergyMinimum interactionDataStar_LIP03241` | Task 48 never names `G_H` and states only the lower bound `1/8`, in `EReal`. Here `G_H := gapH_LIP03249 = -freeEnergyMinimumReal A_*` (a real), with `coe_gapH_LIP03249 : ↑G_H = 0 - freeEnergyMinimum A_*` |
| the Task 48 density, measure and free energy | `Frontier.LIP032.rhoH_LIP03248` (`T48.lean:69`), `haarMeasure_LIP03248` (`:72`), `haarMeasure_coe_LIP03248` (`:76`), `sqrt_rhoH_LIP03248` (`:81`), `mem_H1Haar_const_LIP03248` (`:87`), `freeEnergy_haar_LIP03248` (`:105`) | `rhoH_LIP03248 : Torus 1 → ℝ := fun _ => 1`; `haarMeasure_LIP03248 : ProbabilityMeasure (Torus 1)`; `freeEnergy A_* haarMeasure_LIP03248 = 0` | `ρ_H` there is a function, here a campaign structure; the bridge is `sqrt_absoluteRhoH_LIP03249` and `densityMeasure_absoluteRhoH_LIP03249` |
| the Task 48 potential and literal score | `Frontier.LIP032.potential_eq_const_LIP03248` (`T48.lean:155`), `score_zero_ae_LIP03248` (`:160`), `lip032_48_haar_positive_gap_literal_zero_score` (`:176`) | for ALL `g h : Torus 1 → Tangent 1` with `IsWeakGradient (√ρ_H) g` and `IsWeakGradient (V_* + W_* * m) h`: `∀ᵐ x, 2 • g x + √(ρ_H x) • h x = 0` and `∫ ‖2 • g x + √(ρ_H x) • h x‖² ∂haar 1 = 0` | stated for arbitrary weak gradients and `L²` hypotheses, not for the campaign `scalarScore`; bound here by instantiating `g` and `h` (see the R5 notes) |
| `scalarScore`, `scalarDissipation A_* drift_* ρ_H` | `DGPS.scalarScore` (`ScalarRate.lean:61`), `DGPS.scalarDissipation` (`:66`) | `scalarScore A b ρ x = (2:ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • b.force ρ x`; `scalarDissipation A b ρ : ℝ≥0∞ = ∫⁻ x, ENNReal.ofReal (‖scalarScore A b ρ x‖ ^ 2) ∂haar d` | a lower integral in `ℝ≥0∞` (Task 48 has the real Bochner integral); both are stated |
| `scalarRate A_* drift_*` and the quotient | `DGPS.scalarQuotient` (`ScalarRate.lean:71`), `DGPS.scalarRate` (`:77`), `DGPS.scalarRate_le_quotient` (`:80`) | `scalarQuotient A b ρ = scalarDissipation A b ρ / (2 * (scalarGap A ρ : ℝ≥0∞))`; `scalarRate A b = ⨅ ρ : {ρ : AbsoluteDensity d // 0 < scalarGap A ρ}, scalarQuotient A b ρ.1`, the empty infimum is `⊤` | the denominator is `2 * ↑G` in `ℝ≥0∞`; the specification writes `ofReal (2 G_H)`. Equal by `ofReal_two_mul_coe_LIP03249`; the infimum interface is stated with `ofReal (2 * G)` |
| LIP031 premise | `DGPS.Lipschitz.positive_rate_flow_tails_and_limiting_minimizer`, `DGPS/Lipschitz/MinimizerRetraction.lean:744` | takes `A`, `drift : AbsoluteDrift A`, `hr : 0 < r` and `hrate : ENNReal.ofReal r < scalarRate A drift`, among other inputs | for `A_*` that premise is unsatisfiable, see `..._no_positive_rate`; this unit needs none of the LIP031 hypotheses |

# LIP032.49: OPEN named density, drift, dissipation, and rate binding

Task id and title: LIP032.49, "OPEN named density, drift, dissipation, and rate binding" (node LIP032,
contractibility of the minimizer set; gate unit, interface resolution). Result: the density `ρ_H`
and a compatible drift `drift_*` are constructed as campaign objects; the gap, the literal score,
the dissipation and the rate inequality are bound to `scalarGap`, `scalarScore`,
`scalarDissipation` and `scalarRate` of the explicit model `A_*`. All requested identities are
provable for the actual declarations, so no statement issue arises at this unit.

## Provides
* `DGPS.Frontier.LIP032.gate_lip032_49_named_density_drift_dissipation_rate_binding` : MAIN. For
  `ρ_H = absoluteRhoH_LIP03249` and `drift_* = driftStar_LIP03249`: `ρ_H m` is the Haar probability
  and `√ρ_H` is the Task 48 function; the force of `drift_*` at `ρ_H` is an `L²` weak gradient of the
  Task 48 potential; `↑G_H = 0 - E_{*,min}`; `(scalarGap A_* ρ_H : ℝ) = G_H > 0`; the campaign score
  is, pointwise, the Task 48 literal score and vanishes a.e. with zero squared integral;
  `scalarDissipation A_* drift_* ρ_H = 0`; and `scalarRate A_* drift_* ≤ D / ofReal (2 G_H)`.
* `DGPS.Frontier.LIP032.gate_lip032_49_named_density_drift_dissipation_rate_binding_rate_interface` :
  for any `A` and `b`: `scalarRate A b` is the infimum, over positive-gap densities, of
  `D(ρ) / ofReal (2 G(ρ))`, hence at most that quotient at every positive-gap density.
* `DGPS.Frontier.LIP032.gate_lip032_49_named_density_drift_dissipation_rate_binding_any_provider` :
  for EVERY `b : AbsoluteDrift A_*`: the dissipation of `ρ_H` is zero, the rate bound holds, and
  `scalarRate A_* b = 0`.
* `DGPS.Frontier.LIP032.gate_lip032_49_named_density_drift_dissipation_rate_binding_no_positive_rate` :
  for every `b`, there is no real `r > 0` with `ofReal r < scalarRate A_* b` (the LIP031 premise).

Helper declarations (all with the suffix `_LIP03249`, in the `DGPS.Frontier.LIP032` namespace):
* `absoluteRhoH_LIP03249 : AbsoluteDensity 1` : the constant density (`sqrt = fun _ => 1`);
  `sqrt_absoluteRhoH_LIP03249`, `density_absoluteRhoH_LIP03249` : bridges to `rhoH_LIP03248`;
  `densityMeasure_absoluteRhoH_LIP03249` : `ρ_H m = haarMeasure_LIP03248`.
* `interactionPotential_absoluteRhoH_LIP03249` : the campaign potential at `ρ_H` is the constant `2`.
* `integral_WStar_prob_LIP03249`, `interactionPotential_star_eq_LIP03249`,
  `isSmoothPeriodic_interactionPotential_LIP03249` : for any probability, the potential of `A_*` is
  affine in `γ`, hence smooth and periodic.
* `isWeakGradientLp_one_of_isWeakGradient_LIP03249`, `smoothDrift_LIP03249`, `driftStar_LIP03249` :
  an `L²` weak gradient is an `L¹` one; the drift provider built from classical gradients; the named
  `drift_* : AbsoluteDrift A_*`.
* `force_absoluteRhoH_ae_zero_LIP03249`, `weakGradient_absoluteRhoH_ae_zero_LIP03249` : the force of
  any provider and the chosen gradient of `√ρ_H` vanish a.e. at `ρ_H`.
* `isWeakGradient_sqrt_absoluteRhoH_LIP03249`, `isWeakGradient_driftStar_force_LIP03249` : the two
  weak-gradient hypotheses of Task 48, for the chosen gradient and for the force of `drift_*`.
* `scalarScore_absoluteRhoH_eq_LIP03249`, `scalarScore_absoluteRhoH_ae_zero_LIP03249`,
  `scalarDissipation_absoluteRhoH_LIP03249`, `integral_norm_sq_score_absoluteRhoH_LIP03249` : the
  campaign score, its a.e. vanishing, the zero dissipation, and the zero real squared integral.
* `gapH_LIP03249`, `coe_gapH_LIP03249`, `one_eighth_le_gapH_LIP03249`, `gapH_pos_LIP03249` : the real
  gap `G_H = -F_*`, its `EReal` form, `1/8 ≤ G_H`, and `0 < G_H`.
* `densityFreeEnergy_absoluteRhoH_LIP03249`, `coe_scalarGap_absoluteRhoH_LIP03249`,
  `scalarGap_absoluteRhoH_pos_LIP03249` : `F(ρ_H m) = 0`, `(scalarGap A_* ρ_H : ℝ) = G_H`, and the
  positivity of the campaign gap (so `ρ_H` is a competitor in `scalarRate`).
* `ofReal_two_mul_coe_LIP03249` : `ofReal (2 * ↑g) = 2 * ↑g` for `g : ℝ≥0`.

## R5 notes
* No hypothesis is added. The main theorem has no binders: the model is the explicit `A_*` on
  `Torus 1`, `ρ_H` and `drift_*` are the constructed objects named in the statement. The only
  domain restriction is `d = 1`, which comes with `A_*` (Task 41).
* Non-literal reading 1, the objects. `ρ_H` is the campaign structure with `sqrt = fun _ => 1`
  (membership in `H¹` by Task 48, nonnegativity trivial, mass one by `simp`). `drift_*` is read as
  an element of `AbsoluteDrift A_*`; "compatible" is read as: its force at `ρ_H` is a weak gradient
  of the Task 48 potential `V_* + W_* * m`, so the two weak-gradient hypotheses of Task 48 hold for
  the pair (chosen gradient of `√ρ_H`, force of `drift_*`). This is the third conjunct of the main
  theorem.
* Non-literal reading 2, the drift is total. `AbsoluteDrift A_*` must supply an `L¹` weak gradient
  for EVERY absolute density, not only for `ρ_H`. For `A_*` the potential of any `ρ` is
  `(-8 M(ρ m)) γ + 4 ∫ γ² d(ρ m)`, affine in `γ`, hence smooth and periodic, so the force is the
  classical gradient (`smoothGrad`) of the potential at each `ρ`. No derivative is defaulted to
  zero, and the force is not set by cases on `ρ`.
* Non-literal reading 3, the explicit formulas `G_*(x) = 16 π γ(x) σ(x)` and
  `B_*(x,y) = -16 π (γ x - γ y) σ(x)` of the specification are NOT used or bound: the campaign has no
  derivative lemma for `cosMode` that would be needed for it. The force constructed is the classical
  gradient of the actual potential (the quantity these formulas describe), and the
  Haar-averaged force `G_* + ∫ B_* dm = 0` is obtained at `ρ_H` by a.e. uniqueness of `L¹` weak
  gradients from the constant potential. Since all providers agree a.e. (`absoluteDrift_unique`),
  nothing depends on the representative; this is made explicit by the `_any_provider` lemma.
* Non-literal reading 4, the gap. Task 48 states `1/8 ≤ 0 - E_{*,min}` in `EReal` and does not name
  `G_H`. `G_H` is `gapH_LIP03249 = -freeEnergyMinimumReal A_*`; `coe_gapH_LIP03249` shows it is the
  `EReal` expression `0 - E_{*,min}` of Task 48, and `(scalarGap A_* ρ_H : ℝ) = G_H` holds because
  `densityFreeEnergy A_* ρ_H = 0` (Task 48 `freeEnergy_haar_LIP03248`, transported along
  `densityMeasure ρ_H = haarMeasure_LIP03248`). Positivity is `1/8 ≤ G_H` from Task 48.
* Non-literal reading 5, the literal score. The campaign score is
  `2 • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • b.force ρ x`, with `weakGradient` a chosen
  representative. The Task 48 literal score is stated for arbitrary weak gradients `g`, `h`. It is
  bound by instantiating `g := weakGradient ρ_H.sqrt ρ_H.sqrt_mem` and `h := drift_*.force ρ_H`
  (the hypotheses are `isWeakGradient_sqrt_absoluteRhoH_LIP03249` and
  `isWeakGradient_driftStar_force_LIP03249`). The campaign score equals this expression for every `x`
  (not merely a.e.), because `ρ_H.sqrt x = √(rhoH x)` by function equality. The vanishing a.e. and
  the zero real squared integral are the two conjuncts of Task 48 so instantiated; the
  `ℝ≥0∞` dissipation is zero by the a.e. vanishing of the score.
* Non-literal reading 6, the rate interface. `scalarRate` is a `⨅` over the subtype
  `{ρ // 0 < scalarGap A ρ}` of `scalarQuotient`, which divides by `2 * ↑G` in `ℝ≥0∞`. The
  specification writes `ofReal (2 G_H)`. They agree for every `G : ℝ≥0`
  (`ofReal_two_mul_coe_LIP03249`), and the `_rate_interface` lemma states the infimum and its
  `iInf_le` bound with `ofReal (2 * G)`. The final inequality is this bound at the competitor `ρ_H`
  (whose gap is positive) with the gap rewritten by `G_H`. The campaign definition is unchanged,
  and no mismatch other than this normalization arises.
* Consequence recorded, not a statement issue. The right-hand side is `0 / ofReal (2 G_H) = 0` in
  `ℝ≥0∞` (the dissipation is zero), so the displayed inequality says `scalarRate A_* drift_* = 0`
  (the `_any_provider` lemma, for every provider). Hence no real `r > 0` has
  `ofReal r < scalarRate A_* drift` (the `_no_positive_rate` lemma): the positive-rate hypothesis
  of LIP031 cannot hold for `A_*`. This is consistent with the node's statement issue (the isolated
  frozen contractibility sentence omits that hypothesis, FD-001 in `campaign/frontier/DEFECTS.md`);
  this unit neither proves nor assumes the frozen sentence and does not weaken or strengthen it.
* Extra conjuncts of the main theorem are conclusions only: the identification of `ρ_H m` and of
  `ρ_H.sqrt`, the weak-gradient membership of the force, the pointwise identification of the
  campaign score with the literal expression, and the real-integral form of the zero dissipation.
  The conjuncts asked for are the equality `(scalarGap A_* ρ_H : ℝ) = G_H`, `G_H > 0`,
  `scalarDissipation A_* drift_* ρ_H = 0`, and the rate bound.
* Representative choices. `weakGradient` is chosen by `Classical.choose`; `smoothGrad` is the
  classical gradient. All statements about them are either pointwise identities between the
  definitions or a.e. statements via `IsWeakGradient.ae_eq` and `IsWeakGradientLp.ae_eq_of_one`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace DGPS.Frontier.LIP032

/-! ### The named density `ρ_H` -/

/-- The campaign density `ρ_H = 1` on `𝕋¹`: the square root is the constant function `1`. -/
noncomputable def absoluteRhoH_LIP03249 : AbsoluteDensity 1 where
  sqrt := fun _ => 1
  sqrt_mem := mem_H1Haar_const_LIP03248 1
  sqrt_nonneg := Filter.Eventually.of_forall fun _ => zero_le_one
  mass_one := by simp

/-- The square root of `ρ_H` is the square root of the Task 48 constant density. -/
theorem sqrt_absoluteRhoH_LIP03249 :
    absoluteRhoH_LIP03249.sqrt = fun x : Torus 1 => Real.sqrt (rhoH_LIP03248 x) :=
  sqrt_rhoH_LIP03248.symm

/-- The density `(√ρ_H)²` of `ρ_H` is the Task 48 constant density. -/
theorem density_absoluteRhoH_LIP03249 (x : Torus 1) :
    absoluteRhoH_LIP03249.density x = rhoH_LIP03248 x := by
  simp [AbsoluteDensity.density, absoluteRhoH_LIP03249, rhoH_LIP03248]

/-- The probability measure `ρ_H m` is the Haar measure. -/
theorem densityMeasure_absoluteRhoH_LIP03249 :
    densityMeasure absoluteRhoH_LIP03249 = haarMeasure_LIP03248 := by
  apply ProbabilityMeasure.toMeasure_injective
  have h : (fun x : Torus 1 => ENNReal.ofReal (absoluteRhoH_LIP03249.sqrt x ^ 2)) = fun _ => 1 := by
    funext x
    simp [absoluteRhoH_LIP03249]
  rw [densityMeasure_coe, h, withDensity_const, one_smul]
  rfl

/-! ### The equilibrium potential of `A_*` -/

/-- The potential `V_* + W_* * m` seen through the campaign `interactionPotential` is the
constant `2`. -/
theorem interactionPotential_absoluteRhoH_LIP03249 :
    interactionPotential interactionDataStar_LIP03241 absoluteRhoH_LIP03249 = fun _ => 2 := by
  funext x
  unfold interactionPotential
  rw [densityMeasure_absoluteRhoH_LIP03249, haarMeasure_coe_LIP03248]
  exact potential_eq_two_LIP03248 x

/-- The Haar-type integral of `W_*` against an arbitrary probability measure. -/
theorem integral_WStar_prob_LIP03249 (ν : Measure (Torus 1)) [IsProbabilityMeasure ν]
    (x : Torus 1) :
    ∫ y, WStar_LIP03241 x y ∂ν =
      4 * gammaStar_LIP03241 x ^ 2 - (8 * momentStar_LIP03241 ν) * gammaStar_LIP03241 x +
        4 * ∫ y, gammaStar_LIP03241 y ^ 2 ∂ν := by
  have hγ : Continuous gammaStar_LIP03241 := continuous_gammaStar_LIP03241
  have hfun : (fun y => WStar_LIP03241 x y) =
      fun y => (4 * gammaStar_LIP03241 x ^ 2 - (8 * gammaStar_LIP03241 x) * gammaStar_LIP03241 y) +
        4 * gammaStar_LIP03241 y ^ 2 := by
    funext y
    unfold WStar_LIP03241
    ring
  have hI1 : Integrable
      (fun y => 4 * gammaStar_LIP03241 x ^ 2 - (8 * gammaStar_LIP03241 x) * gammaStar_LIP03241 y) ν :=
    integrable_of_continuous_LIP03241 ν (continuous_const.sub (continuous_const.mul hγ))
  have hI2 : Integrable (fun y => 4 * gammaStar_LIP03241 y ^ 2) ν :=
    integrable_of_continuous_LIP03241 ν (continuous_const.mul (hγ.pow 2))
  have hI3 : Integrable (fun y => (8 * gammaStar_LIP03241 x) * gammaStar_LIP03241 y) ν :=
    integrable_of_continuous_LIP03241 ν (continuous_const.mul hγ)
  rw [hfun, integral_add hI1 hI2, integral_sub (integrable_const _) hI3, integral_const,
    integral_const_mul, integral_const_mul]
  simp only [probReal_univ, smul_eq_mul, momentStar_LIP03241]
  ring

/-- For every absolute density `ρ`, the potential `V_* + W_* * (ρ m)` is an affine function of
`γ`, with coefficients depending on the first two moments of `ρ m`. -/
theorem interactionPotential_star_eq_LIP03249 (ρ : AbsoluteDensity 1) :
    interactionPotential interactionDataStar_LIP03241 ρ =
      fun x => (-8 * momentStar_LIP03241 (densityMeasure ρ : Measure (Torus 1))) *
        gammaStar_LIP03241 x +
        4 * ∫ y, gammaStar_LIP03241 y ^ 2 ∂(densityMeasure ρ : Measure (Torus 1)) := by
  funext x
  show VStar_LIP03241 x + ∫ y, WStar_LIP03241 x y ∂(densityMeasure ρ : Measure (Torus 1)) = _
  rw [integral_WStar_prob_LIP03249 (densityMeasure ρ : Measure (Torus 1)) x]
  unfold VStar_LIP03241
  ring

/-- For every absolute density `ρ`, the potential `V_* + W_* * (ρ m)` is smooth and periodic. -/
theorem isSmoothPeriodic_interactionPotential_LIP03249 (ρ : AbsoluteDensity 1) :
    IsSmoothPeriodic (interactionPotential interactionDataStar_LIP03241 ρ) := by
  rw [interactionPotential_star_eq_LIP03249]
  exact (contDiff_const.mul isSmoothPeriodic_gammaStar_LIP03241).add contDiff_const

/-! ### The named drift `drift_*` -/

/-- An `L²` weak gradient is an `L¹` weak gradient (the torus has finite measure). -/
theorem isWeakGradientLp_one_of_isWeakGradient_LIP03249 {d : ℕ} {u : Torus d → ℝ}
    {g : Torus d → Tangent d} (h : IsWeakGradient u g) : IsWeakGradientLp 1 u g :=
  ⟨h.memLp.mono_exponent one_le_two, h.memLp_grad.mono_exponent one_le_two, h.ibp⟩

/-- The drift provider whose force is the classical gradient of the potential, for interaction
data whose potentials `V + W * (ρ m)` are smooth and periodic for every absolute density. -/
noncomputable def smoothDrift_LIP03249 {d : ℕ} (A : InteractionData d)
    (h : ∀ ρ : AbsoluteDensity d, IsSmoothPeriodic (interactionPotential A ρ)) :
    AbsoluteDrift A where
  force ρ := smoothGrad (interactionPotential A ρ)
  measurable_force ρ := (h ρ).continuous_smoothGrad.measurable
  weak_gradient ρ := isWeakGradientLp_one_of_isWeakGradient_LIP03249 (h ρ).isWeakGradient

/-- The campaign drift `drift_*` for `A_*`: the classical gradient of `V_* + W_* * (ρ m)`. -/
noncomputable def driftStar_LIP03249 : AbsoluteDrift interactionDataStar_LIP03241 :=
  smoothDrift_LIP03249 interactionDataStar_LIP03241 isSmoothPeriodic_interactionPotential_LIP03249

/-! ### Force, score and dissipation at `ρ_H` -/

/-- The force of any weak-drift provider vanishes a.e. at `ρ_H`: the potential is the constant `2`
and `L¹` weak gradients are unique a.e. -/
theorem force_absoluteRhoH_ae_zero_LIP03249 (b : AbsoluteDrift interactionDataStar_LIP03241) :
    b.force absoluteRhoH_LIP03249 =ᵐ[haar 1] 0 := by
  have h0 : IsWeakGradientLp 1
      (interactionPotential interactionDataStar_LIP03241 absoluteRhoH_LIP03249)
      (0 : Torus 1 → Tangent 1) := by
    rw [interactionPotential_absoluteRhoH_LIP03249]
    exact isWeakGradientLp_one_of_isWeakGradient_LIP03249 (isWeakGradient_const (d := 1) 2)
  exact b.ae_eq_of_isWeakGradient absoluteRhoH_LIP03249 h0

/-- The chosen weak gradient of `√ρ_H` vanishes a.e. -/
theorem weakGradient_absoluteRhoH_ae_zero_LIP03249 :
    weakGradient absoluteRhoH_LIP03249.sqrt absoluteRhoH_LIP03249.sqrt_mem =ᵐ[haar 1] 0 :=
  weakGradient_ae_eq (isWeakGradient_const (d := 1) (1 : ℝ))

/-- The chosen weak gradient of `√ρ_H` is a weak gradient of the Task 48 function `√ρ_H`. -/
theorem isWeakGradient_sqrt_absoluteRhoH_LIP03249 :
    IsWeakGradient (fun x : Torus 1 => Real.sqrt (rhoH_LIP03248 x))
      (weakGradient absoluteRhoH_LIP03249.sqrt absoluteRhoH_LIP03249.sqrt_mem) := by
  rw [← sqrt_absoluteRhoH_LIP03249]
  exact isWeakGradient_weakGradient absoluteRhoH_LIP03249.sqrt_mem

/-- The force of `drift_*` at `ρ_H` is an `L²` weak gradient of the Task 48 potential
`V_* + W_* * m`. -/
theorem isWeakGradient_driftStar_force_LIP03249 :
    IsWeakGradient (fun x : Torus 1 => VStar_LIP03241 x + ∫ y, WStar_LIP03241 x y ∂haar 1)
      (driftStar_LIP03249.force absoluteRhoH_LIP03249) := by
  have h : IsWeakGradient
      (interactionPotential interactionDataStar_LIP03241 absoluteRhoH_LIP03249)
      (driftStar_LIP03249.force absoluteRhoH_LIP03249) :=
    (isSmoothPeriodic_interactionPotential_LIP03249 absoluteRhoH_LIP03249).isWeakGradient
  rw [interactionPotential_absoluteRhoH_LIP03249] at h
  rw [potential_eq_const_LIP03248]
  exact h

/-- The campaign score at `ρ_H` is the Task 48 literal score `2 g + √ρ_H h` with `g` the chosen
weak gradient of `√ρ_H` and `h` the force of the provider. -/
theorem scalarScore_absoluteRhoH_eq_LIP03249 (b : AbsoluteDrift interactionDataStar_LIP03241)
    (x : Torus 1) :
    scalarScore interactionDataStar_LIP03241 b absoluteRhoH_LIP03249 x =
      (2 : ℝ) • weakGradient absoluteRhoH_LIP03249.sqrt absoluteRhoH_LIP03249.sqrt_mem x +
        Real.sqrt (rhoH_LIP03248 x) • b.force absoluteRhoH_LIP03249 x := by
  unfold scalarScore
  rw [show absoluteRhoH_LIP03249.sqrt x = Real.sqrt (rhoH_LIP03248 x) from
    congrFun sqrt_absoluteRhoH_LIP03249 x]

/-- The campaign score vanishes a.e. at `ρ_H`, for every weak-drift provider. -/
theorem scalarScore_absoluteRhoH_ae_zero_LIP03249 (b : AbsoluteDrift interactionDataStar_LIP03241) :
    ∀ᵐ x ∂haar 1, scalarScore interactionDataStar_LIP03241 b absoluteRhoH_LIP03249 x = 0 := by
  filter_upwards [weakGradient_absoluteRhoH_ae_zero_LIP03249,
    force_absoluteRhoH_ae_zero_LIP03249 b] with x hx1 hx2
  unfold scalarScore
  rw [hx1, hx2]
  simp

/-- The campaign dissipation of `ρ_H` is zero, for every weak-drift provider. -/
theorem scalarDissipation_absoluteRhoH_LIP03249 (b : AbsoluteDrift interactionDataStar_LIP03241) :
    scalarDissipation interactionDataStar_LIP03241 b absoluteRhoH_LIP03249 = 0 := by
  unfold scalarDissipation
  have hz : (fun x => ENNReal.ofReal
      (‖scalarScore interactionDataStar_LIP03241 b absoluteRhoH_LIP03249 x‖ ^ 2)) =ᵐ[haar 1]
      fun _ => 0 := by
    filter_upwards [scalarScore_absoluteRhoH_ae_zero_LIP03249 b] with x hx
    simp [hx]
  rw [lintegral_congr_ae hz]
  simp

/-- The real squared-norm integral of the campaign score at `ρ_H` is zero. -/
theorem integral_norm_sq_score_absoluteRhoH_LIP03249 (b : AbsoluteDrift interactionDataStar_LIP03241) :
    ∫ x, ‖scalarScore interactionDataStar_LIP03241 b absoluteRhoH_LIP03249 x‖ ^ 2 ∂haar 1 = 0 := by
  refine integral_eq_zero_of_ae ?_
  filter_upwards [scalarScore_absoluteRhoH_ae_zero_LIP03249 b] with x hx
  simp [hx]

/-! ### The source gap `G_H` -/

/-- The source gap `G_H = 0 - E_{*,min}` of Task 48, as a real number. -/
noncomputable def gapH_LIP03249 : ℝ := -freeEnergyMinimumReal interactionDataStar_LIP03241

/-- The real gap `G_H` is the Task 48 gap `0 - E_{*,min}` in `EReal`. -/
theorem coe_gapH_LIP03249 :
    ((gapH_LIP03249 : ℝ) : EReal) = (0 : EReal) - freeEnergyMinimum interactionDataStar_LIP03241 := by
  rw [← coe_freeEnergyMinimumReal, ← EReal.coe_zero, ← EReal.coe_sub, gapH_LIP03249, zero_sub]

/-- Task 48 gives `1/8 ≤ G_H`. -/
theorem one_eighth_le_gapH_LIP03249 : (1 / 8 : ℝ) ≤ gapH_LIP03249 := by
  have h := gap_LIP03248
  rw [← coe_gapH_LIP03249, EReal.coe_le_coe_iff] at h
  exact h

theorem gapH_pos_LIP03249 : 0 < gapH_LIP03249 :=
  lt_of_lt_of_le (by norm_num) one_eighth_le_gapH_LIP03249

/-- The campaign free energy of `ρ_H m` is zero (Task 48). -/
theorem densityFreeEnergy_absoluteRhoH_LIP03249 :
    densityFreeEnergy interactionDataStar_LIP03241 absoluteRhoH_LIP03249 = 0 := by
  have h := coe_densityFreeEnergy interactionDataStar_LIP03241 absoluteRhoH_LIP03249
  rw [densityMeasure_absoluteRhoH_LIP03249, freeEnergy_haar_LIP03248] at h
  exact EReal.coe_eq_zero.mp h

/-- The campaign gap `scalarGap A_* ρ_H`, as a real number, is `G_H`. -/
theorem coe_scalarGap_absoluteRhoH_LIP03249 :
    ((scalarGap interactionDataStar_LIP03241 absoluteRhoH_LIP03249 : ℝ≥0) : ℝ) = gapH_LIP03249 := by
  rw [coe_scalarGap, densityFreeEnergy_absoluteRhoH_LIP03249, gapH_LIP03249, zero_sub]

/-- `ρ_H` has positive campaign gap, so it is a competitor in `scalarRate`. -/
theorem scalarGap_absoluteRhoH_pos_LIP03249 :
    0 < scalarGap interactionDataStar_LIP03241 absoluteRhoH_LIP03249 := by
  rw [← NNReal.coe_pos, coe_scalarGap_absoluteRhoH_LIP03249]
  exact gapH_pos_LIP03249

/-! ### The infimum interface -/

/-- The quotient denominator: `ofReal (2 G) = 2 * ↑G` in `ℝ≥0∞` for `G : ℝ≥0`. -/
theorem ofReal_two_mul_coe_LIP03249 (g : ℝ≥0) :
    ENNReal.ofReal (2 * (g : ℝ)) = 2 * (g : ℝ≥0∞) := by
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]

/-- **Infimum interface.** `scalarRate A b` is the infimum over positive-gap densities `ρ` of
`D(ρ) / ofReal (2 G(ρ))`, so it is at most that quotient at every positive-gap density. -/
theorem gate_lip032_49_named_density_drift_dissipation_rate_binding_rate_interface {d : ℕ}
    (A : InteractionData d) (b : AbsoluteDrift A) :
    scalarRate A b =
        ⨅ ρ : {ρ : AbsoluteDensity d // 0 < scalarGap A ρ},
          scalarDissipation A b ρ.1 / ENNReal.ofReal (2 * (scalarGap A ρ.1 : ℝ)) ∧
      ∀ ρ : AbsoluteDensity d, 0 < scalarGap A ρ →
        scalarRate A b ≤ scalarDissipation A b ρ / ENNReal.ofReal (2 * (scalarGap A ρ : ℝ)) := by
  refine ⟨?_, fun ρ hρ => ?_⟩
  · unfold scalarRate scalarQuotient
    exact iInf_congr fun ρ => by rw [ofReal_two_mul_coe_LIP03249]
  · rw [ofReal_two_mul_coe_LIP03249]
    exact scalarRate_le_quotient A b ρ hρ

/-! ### Consequences for every provider -/

/-- For every weak-drift provider `b` of `A_*`: the dissipation of `ρ_H` is zero, the rate is at
most `D / ofReal (2 G_H)`, and hence the rate is zero. -/
theorem gate_lip032_49_named_density_drift_dissipation_rate_binding_any_provider
    (b : AbsoluteDrift interactionDataStar_LIP03241) :
    scalarDissipation interactionDataStar_LIP03241 b absoluteRhoH_LIP03249 = 0 ∧
      scalarRate interactionDataStar_LIP03241 b ≤
        scalarDissipation interactionDataStar_LIP03241 b absoluteRhoH_LIP03249 /
          ENNReal.ofReal (2 * gapH_LIP03249) ∧
      scalarRate interactionDataStar_LIP03241 b = 0 := by
  have hD := scalarDissipation_absoluteRhoH_LIP03249 b
  have hle := (gate_lip032_49_named_density_drift_dissipation_rate_binding_rate_interface
    interactionDataStar_LIP03241 b).2 absoluteRhoH_LIP03249 scalarGap_absoluteRhoH_pos_LIP03249
  rw [coe_scalarGap_absoluteRhoH_LIP03249] at hle
  refine ⟨hD, hle, ?_⟩
  rw [hD, ENNReal.zero_div] at hle
  exact le_antisymm hle zero_le

/-- The positive-rate premise of the LIP031 context, `0 < r` with `ofReal r < scalarRate A drift`,
cannot hold for `A_*` and any provider: the rate of `A_*` is zero. -/
theorem gate_lip032_49_named_density_drift_dissipation_rate_binding_no_positive_rate
    (b : AbsoluteDrift interactionDataStar_LIP03241) :
    ¬ ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r < scalarRate interactionDataStar_LIP03241 b := by
  rintro ⟨r, -, hr⟩
  rw [(gate_lip032_49_named_density_drift_dissipation_rate_binding_any_provider b).2.2] at hr
  exact not_lt_zero hr

/-! ### The binding theorem -/

/-- **LIP032.49.** The constant density `ρ_H`, the compatible drift `drift_*`, the gap `G_H` and
the literal score of Task 48 are bound to the campaign objects `scalarGap`, `scalarScore`,
`scalarDissipation` and `scalarRate` for the explicit model `A_*`. -/
theorem gate_lip032_49_named_density_drift_dissipation_rate_binding :
    -- the density `ρ_H`
    densityMeasure absoluteRhoH_LIP03249 = haarMeasure_LIP03248 ∧
    absoluteRhoH_LIP03249.sqrt = (fun x : Torus 1 => Real.sqrt (rhoH_LIP03248 x)) ∧
    -- the compatible drift `drift_*`
    IsWeakGradient (fun x : Torus 1 => VStar_LIP03241 x + ∫ y, WStar_LIP03241 x y ∂haar 1)
      (driftStar_LIP03249.force absoluteRhoH_LIP03249) ∧
    -- the gap `G_H`
    ((gapH_LIP03249 : ℝ) : EReal) =
      (0 : EReal) - freeEnergyMinimum interactionDataStar_LIP03241 ∧
    ((scalarGap interactionDataStar_LIP03241 absoluteRhoH_LIP03249 : ℝ≥0) : ℝ) = gapH_LIP03249 ∧
    0 < gapH_LIP03249 ∧
    -- the literal score of Task 48 and the dissipation
    (∀ x : Torus 1, scalarScore interactionDataStar_LIP03241 driftStar_LIP03249
        absoluteRhoH_LIP03249 x =
      (2 : ℝ) • weakGradient absoluteRhoH_LIP03249.sqrt absoluteRhoH_LIP03249.sqrt_mem x +
        Real.sqrt (rhoH_LIP03248 x) • driftStar_LIP03249.force absoluteRhoH_LIP03249 x) ∧
    (∀ᵐ x ∂haar 1,
      (2 : ℝ) • weakGradient absoluteRhoH_LIP03249.sqrt absoluteRhoH_LIP03249.sqrt_mem x +
        Real.sqrt (rhoH_LIP03248 x) • driftStar_LIP03249.force absoluteRhoH_LIP03249 x = 0) ∧
    ∫ x, ‖(2 : ℝ) • weakGradient absoluteRhoH_LIP03249.sqrt absoluteRhoH_LIP03249.sqrt_mem x +
        Real.sqrt (rhoH_LIP03248 x) • driftStar_LIP03249.force absoluteRhoH_LIP03249 x‖ ^ 2
      ∂haar 1 = 0 ∧
    scalarDissipation interactionDataStar_LIP03241 driftStar_LIP03249 absoluteRhoH_LIP03249 = 0 ∧
    -- the rate
    scalarRate interactionDataStar_LIP03241 driftStar_LIP03249 ≤
      scalarDissipation interactionDataStar_LIP03241 driftStar_LIP03249 absoluteRhoH_LIP03249 /
        ENNReal.ofReal (2 * gapH_LIP03249) := by
  have hscore := lip032_48_haar_positive_gap_literal_zero_score.2.2.2.2.2.2
    (weakGradient absoluteRhoH_LIP03249.sqrt absoluteRhoH_LIP03249.sqrt_mem)
    (driftStar_LIP03249.force absoluteRhoH_LIP03249)
    isWeakGradient_sqrt_absoluteRhoH_LIP03249 isWeakGradient_driftStar_force_LIP03249
  exact ⟨densityMeasure_absoluteRhoH_LIP03249, sqrt_absoluteRhoH_LIP03249,
    isWeakGradient_driftStar_force_LIP03249, coe_gapH_LIP03249,
    coe_scalarGap_absoluteRhoH_LIP03249, gapH_pos_LIP03249,
    scalarScore_absoluteRhoH_eq_LIP03249 driftStar_LIP03249, hscore.1, hscore.2,
    scalarDissipation_absoluteRhoH_LIP03249 driftStar_LIP03249,
    (gate_lip032_49_named_density_drift_dissipation_rate_binding_any_provider
      driftStar_LIP03249).2.1⟩

end DGPS.Frontier.LIP032
