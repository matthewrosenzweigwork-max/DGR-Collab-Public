import DGPS.Frontier.LIP032.T23
import DGPS.Frontier.LIP032.T28
import DGPS.Lipschitz.MinimizerRetraction

/-!
## Bindings (LIP032.29, "OPEN initial-value and flowGap definition binding")

Every row was obtained by printing the actual declaration in this worktree (base `f80de9b`).
Paths are relative to `Campaign/`. `ns` abbreviates the namespace prefix `DGPS.`.

| Source object in the specification | Actual declaration (full name, file:line) | Type / binder list | Discrepancy with the specification text |
|---|---|---|---|
| the torus `X`, Haar probability `m` | `DGPS.Torus` (abbrev), `DGPS.haar` (abbrev), `DGPS/Foundations/Torus.lean:32`, `:35` | `Torus (d : ℕ)`; `haar (d : ℕ) : Measure (Torus d)` (probability measure instance at `:37`) | none |
| the campaign alias `L2s d` | `DGPS.Lipschitz.L2s`, `DGPS/Lipschitz/MeanFieldLocalFlow.lean:312` | `noncomputable abbrev L2s (d : ℕ) := Lp ℝ 2 (haar d)` | none: it is exactly the real `L²(m)`, so the identification asked for is `rfl` |
| the class `[f]` of Task 23 | `DGPS.Frontier.LIP032.l2Class_LIP03223`, `DGPS/Frontier/LIP032/T23.lean:54` | `(f : Torus d → ℝ) : DGPS.Lipschitz.L2s d` (`MemLp.toLp f` if `MemLp f 2 (haar d)`, else `0`) | total function, junk value `0` off `L²`; never used for the continuous `f` here |
| the minimizer set `S` | no standalone declaration; the predicate `DGPS.freeEnergy A ν = DGPS.freeEnergyMinimum A`, `DGPS/Model/FreeEnergy.lean:47`, `:53` | `freeEnergy (A : InteractionData d) (ν : ProbabilityMeasure (Torus d)) : EReal`; `freeEnergyMinimum (A) : EReal` (an infimum) | membership in `S` is an `EReal` equation, as in LIP032.22, .23, .28 |
| interaction data `A` | `DGPS.InteractionData`, `DGPS/Model/Data.lean:22` | structure `(d : ℕ)`: `V`, `W`, `V_continuous`, `W_continuous`, `W_symm`, `W_diag` | none |
| the density `p_ν = e^{-V-W*ν}/Z` | `DGPS.Lipschitz.gibbsDensity`, `DGPS/Variational/EquilibriumGibbs.lean:119` | `(A : InteractionData d) (μ : Measure (Torus d)) (x : Torus d) : ℝ` | takes a `Measure`, so `p_ν` is `gibbsDensity A (ν : Measure (Torus d))`; `q = p_μ` has no declaration of its own |
| the interpolation density `f_{ν,s}` | `DGPS.Frontier.LIP032.interpolDensity_LIP03222`, `DGPS/Frontier/LIP032/T22.lean:55` | `(A) (μ ν : ProbabilityMeasure (Torus d)) (s : ℝ) (x : Torus d) : ℝ`, value `(1 - s) * p_ν x + s * p_μ x` | `q = p_μ` is built in, so the binder order is `μ ν` |
| the probability `μ_f` | `DGPS.Frontier.LIP032.densityMeasure_LIP03218`, `DGPS/Frontier/LIP032/T18.lean:56` | `(f : Torus d → ℝ) : Measure (Torus d)`, `(haar d).withDensity (ofReal ∘ f)` | a `Measure`; probability-ness is a separate lemma (LIP032.18) |
| the real free energy `E(f)` | `DGPS.Frontier.LIP032.realFreeEnergy_LIP03228`, `DGPS/Frontier/LIP032/T28.lean:55` | `(A : InteractionData d) (f : Torus d → ℝ) : ℝ`, `∫ f log f + ∫ A.V dμ_f + (1/2) ∫ A.W d(μ_f ⊗ μ_f)` | none |
| `h_MF` | `DGPS.Lipschitz.MeanFieldData`, `DGPS/Lipschitz/MeanFieldNonlinearity.lean:34` | `(G : Torus d → Tangent d) (B : Torus d → Torus d → Tangent d) (g b : ℝ) : Prop` (fields `g_nonneg`, `b_nonneg`, `measurable_G`, `measurable_B`, `norm_G_le`, `norm_B_le`) | the second real is called `b` there and `β` in the specification |
| `IsGlobalProbFlow h_MF ρ0 u` | `DGPS.Lipschitz.IsGlobalProbFlow`, `DGPS/Lipschitz/MeanFieldGlobalFlow.lean:719` | `{d} {G} {B} {g b : ℝ} (h : MeanFieldData G B g b) (ρ0 : L2s d) (u : ℝ → L2s d) : Prop`; fields `cont`, `bdd`, `nonneg`, `mass`, `mild` | there is NO field `u 0 = ρ0`; the initial value is a consequence of `mild` at `t = 0` (see `IsGlobalProbFlow.toMild`, `:733`, `MildFlow.u_zero`, `DGPS/Lipschitz/MeanFieldFlowRegularity.lean:166`, `heatL2_zero`, `DGPS/Lipschitz/HeatSemigroupL2.lean:400`) |
| `flowGap A u t` | `DGPS.Lipschitz.flowGap`, `DGPS/Lipschitz/MinimizerRetraction.lean:734` | `(A : InteractionData d) (u : ℝ → L2s d) (t : ℝ) : ℝ`, body `Lipschitz.freeEnergy A.V A.W (u t) - freeEnergyMinimumReal A` | defined for every real `t` (no positive-time restriction), real-valued, so the value at `t = 0` is the definition itself |
| the real-level free energy inside `flowGap` | `DGPS.Lipschitz.freeEnergy`, `DGPS/Lipschitz/MeanFieldDissipation.lean:1176`; `DGPS.Lipschitz.quadE`, `DGPS/Lipschitz/MeanFieldEnergy.lean:243` | `freeEnergy (V) (W) (f : Torus d → ℝ) : ℝ := ∫ f log f dm + ∫ V f dm + 1/2 * quadE W f`; `quadE W f = ∫ W p.1 p.2 * (f p.1 * f p.2) d(m ⊗ m)` | a function-level (density) formula, not a measure-level one; it differs syntactically from `E(f)` and is bridged below |
| the real minimum `F_*` | `DGPS.freeEnergyMinimumReal`, `DGPS/Model/FreeEnergy.lean:181` (and `coe_freeEnergyMinimumReal`, `:184`) | `(A : InteractionData d) : ℝ := (freeEnergyMinimum A).toReal` | none |
| LIP031 | `DGPS.Lipschitz.positive_rate_flow_tails_and_limiting_minimizer`, `DGPS/Lipschitz/MinimizerRetraction.lean:744` | takes `A`, `drift : AbsoluteDrift A`, `hMF`, `hV`, `hWB`, `hr : 0 < r`, `hrate : ofReal r < scalarRate A drift`, `hu : IsGlobalProbFlow hMF ρ0 u` for an arbitrary `ρ0 : L2s d` | the rate hypotheses live only there; this unit needs none of them |
| LIP028 | `DGPS.Lipschitz.global_bounded_flow_and_l1_stability`, `DGPS/Lipschitz/MeanFieldGlobalFlow.lean:914` | `(h : MeanFieldData G B g b)`, existence for a.e. nonnegative, mass-one, a.e. bounded `ρ0 : L2s d` | none |
| bounds `M_V`, `M_W` | `DGPS.Frontier.LIP032.lip032_27_uniform_potential_interaction_bounds_exists`, `DGPS/Frontier/LIP032/T27.lean:64`; `lip032_28_real_free_energy_uniform_gap`, `DGPS/Frontier/LIP032/T28.lean:93` | `∃ M_V M_W, 0 ≤ M_V ∧ 0 ≤ M_W ∧ (∀ x, |A.V x| ≤ M_V) ∧ ∀ x y, |A.W x y| ≤ M_W` | the specification "chooses" the bounds; here they are obtained, or taken as binders in the `_bounds` variant |

# LIP032.29: OPEN initial-value and flowGap definition binding

Task id and title: LIP032.29, "OPEN initial-value and flowGap definition binding" (node LIP032,
contractibility of the minimizer set; gate unit, interface resolution). Result: both required
identities are provable for the actual declarations; the initial value is extracted from the `mild`
field of `IsGlobalProbFlow` and `flowGap` is a definitional real-level gap, bridged to the
measure-level `E(f)` of LIP032.28. No statement issue arises at this unit.

## Provides
* `DGPS.Frontier.LIP032.gate_lip032_29_initial_value_flowgap_definition_binding` : MAIN. For
  minimizers `μ ν`, `s ∈ [0,1]`, `h_MF`, and every `u` with `IsGlobalProbFlow h_MF [f_{ν,s}] u`:
  `u 0 = [f_{ν,s}]` and `flowGap A u 0 = E(f_{ν,s}) - E(p_μ)`.
* `DGPS.Frontier.LIP032.gate_lip032_29_initial_value_flowgap_definition_binding_l2s_class_binding` :
  `L2s d = Lp ℝ 2 (haar d)` (definitional) and `[f] = hf.toLp f` for `f ∈ L²(m)`.
* `DGPS.Frontier.LIP032.gate_lip032_29_initial_value_flowgap_definition_binding_initial_value` :
  every `u` with `IsGlobalProbFlow h ρ0 u` has `u 0 = ρ0`, for an arbitrary `ρ0 : L2s d`.
* `DGPS.Frontier.LIP032.gate_lip032_29_initial_value_flowgap_definition_binding_energy_bridge` :
  `Lipschitz.freeEnergy A.V A.W ⇑[f] = E(f)` for continuous, nonnegative, mass-one `f`.
* `DGPS.Frontier.LIP032.gate_lip032_29_initial_value_flowgap_definition_binding_minimum_real` :
  `freeEnergyMinimumReal A = E(p_μ)` for a minimizer `μ`.
* `DGPS.Frontier.LIP032.gate_lip032_29_initial_value_flowgap_definition_binding_density` : the same
  two identities for any continuous nonnegative mass-one density `f` in place of `f_{ν,s}`.
* `DGPS.Frontier.LIP032.gate_lip032_29_initial_value_flowgap_definition_binding_bounds` : the main
  statement together with `0 ≤ flowGap A u 0 ≤ log C + 2 M_V + M_W` for explicit bounds
  `M_V M_W`, `C = exp (2 (M_V + M_W))`.
* `DGPS.Frontier.LIP032.gate_lip032_29_initial_value_flowgap_definition_binding_minimizer` : for
  `f = p_ν`, `ν` a minimizer: `u 0 = [p_ν]`, `E(p_ν) - E(p_μ) = 0` and `flowGap A u 0 = 0`.
* `DGPS.Frontier.LIP032.gate_lip032_29_initial_value_flowgap_definition_binding_flow_exists` :
  non-vacuity: for every `h_MF` a flow `u` with `IsGlobalProbFlow h_MF [f_{ν,s}] u` exists.

## R5 notes
* Hypotheses of the main theorem are exactly those of the specification context for this unit:
  `A`, minimizers `μ ν` (as `freeEnergy A _ = freeEnergyMinimum A`), `s ∈ [0,1]`, `h_MF`, `u`,
  `h_u`. The bounds `M_V, M_W` are NOT binders of the main theorem: they are obtained inside the
  proof from LIP032.27 (`..._bounds_exists`), which only removes a hypothesis (a stronger
  statement than one with `hV`, `hW`). The `_bounds` variant takes them explicitly, because
  `G_0 = log C + 2 M_V + M_W` mentions them; there `hV`, `hW` are the pointwise bounds
  `|A.V x| ≤ M_V`, `|A.W x y| ≤ M_W`, with no sign assumption on `M_V, M_W` (none is needed);
  `G_0` is written literally as `Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W`.
* No positive-rate hypothesis is used or added: neither `0 < r`, nor `ofReal r < scalarRate A drift`,
  nor `AbsoluteDrift`, `LipschitzData`, `IsWeakGradient` (`h_V`) or the `h_WB` hypothesis. These are
  inputs of LIP031 only. Both conclusions concern the time `t = 0`, which does not involve them.
  The frozen contractibility sentence of the node (which omits those hypotheses, see FD-001 in
  `campaign/frontier/DEFECTS.md`) is neither proved nor assumed here and is not weakened or
  strengthened; this unit is a binding of definitions at time zero.
* `d` is arbitrary (the specification asks for a positive integer; positivity is not used).
* `[f]` is `l2Class_LIP03223 f`. Since `L2s d` is an `abbrev` for `Lp ℝ 2 (haar d)`, the class
  binding of Task 23 to `L2s d` needs no coercion and is `rfl` (the `l2s_class_binding` lemma).
* Initial value: `IsGlobalProbFlow` has no explicit initial-value field. The proof uses only the
  field `mild` at `t = 0`: `IsGlobalProbFlow.toMild` at `T = 0` gives a `MildFlow`, and
  `MildFlow.u_zero` shows `u 0 = heatL2 ρ0 0 + duhamel ... 0 = ρ0` (`heatL2_zero`, and the Duhamel
  integral over `[0,0]` vanishes). Continuity, boundedness, positivity and mass fields are not used
  here, and `ρ0` is arbitrary. The values of `u` at negative times are unconstrained and irrelevant.
* `flowGap` is defined by a closed formula at every real time (no positive-time convention, no
  boundary-continuity theorem is needed), so `flowGap A u 0` is the definition applied to `u 0 = [f]`.
  The only mathematical content is the bridge `Lipschitz.freeEnergy A.V A.W ⇑[f] = E(f)` for
  continuous nonnegative mass-one `f`: the entropy and potential terms by the a.e. equality
  `⇑[f] = f` (LIP032.23) and the test-integral bridge of LIP032.18 (`∫ A.V dμ_f = ∫ f A.V dm`,
  `A.V` being continuous, hence bounded and measurable); the quadratic term by `prod_withDensity` for
  `μ_f ⊗ μ_f` with an a.e. transport on the product space.
* Extended-real and nonnegative-part conversions: none appear in this unit. `Lipschitz.freeEnergy` and
  `E(f)` are real numbers (entropy is the real integral `∫ f log f`). The identification of
  `freeEnergyMinimumReal A = (freeEnergyMinimum A).toReal` with `E(p_μ)` uses LIP032.28(b),
  `freeEnergyMinimum A = ↑(E (p_μ))`, and `EReal.toReal_coe`; LIP032.28 already performed the
  `EReal.coe_ennreal_ofReal` conversion using the entropy lower bound `0 ≤ ∫ f log f` of LIP032.26.
  For the same reason the sign `E(f) - E(q) ≥ 0` is not needed for the identity; it is recorded in the
  `_bounds` variant from LIP032.28(c).
* The statement `flowGap A u 0 = E(f) - E(q)` is stated for `q = p_μ`, as `gibbsDensity A (μ : Measure
  (Torus d))`, matching the form used in LIP032.28.
* Minimizer case: "for `f = p_ν` with `ν ∈ S` the value is zero" is formalized for the density
  `gibbsDensity A (ν : Measure (Torus d))` itself, not for `interpolDensity_LIP03222 A μ ν 0` (which
  equals it only pointwise after `(1 - 0) * p_ν + 0 * p_μ` is simplified). Both the real number
  `E(p_ν) - E(p_μ)` and `flowGap A u 0` are shown to be zero, using `F_* = E(p_μ) = E(p_ν)` for
  every pair of minimizers (this is the gap-zero argument: `E` of a minimizing density is the
  minimum), not a separate uniqueness result. Continuity, nonnegativity, mass one of `p_ν` come
  from LIP032.18(c).
* The membership `ν ∈ S` in the main theorem is only passed to LIP032.22 (where, as in LIP032.23 and
  .28, it is an unused binder); it is kept to match the specification and the upstream statements.
* Non-vacuity: `h_u` is satisfiable for every `h_MF`, by LIP028 applied to the datum `[f_{ν,s}]` (a.e.
  nonnegative, mass one and a.e. bounded by `exp (2 (M_V + M_W))` by LIP032.23). The uniqueness part
  of LIP028 for `t ≥ 0` is not needed.
* The only axioms used are `propext`, `Classical.choice`, `Quot.sound`.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- Binding of the Task 23 class to the campaign alias: `L2s d` is `Lp ℝ 2 (haar d)`, and `[f]` is
`hf.toLp f` for `f ∈ L²(m)`. -/
theorem gate_lip032_29_initial_value_flowgap_definition_binding_l2s_class_binding (d : ℕ) :
    DGPS.Lipschitz.L2s d = Lp ℝ 2 (haar d) ∧
      ∀ {f : Torus d → ℝ} (hf : MemLp f 2 (haar d)), l2Class_LIP03223 f = hf.toLp f :=
  ⟨rfl, fun {f} hf => by simp [l2Class_LIP03223, hf]⟩

/-- The initial value of a global probability flow is its initial datum (from the `mild` field at
`t = 0`). -/
theorem gate_lip032_29_initial_value_flowgap_definition_binding_initial_value
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    {hMF : DGPS.Lipschitz.MeanFieldData G B g β} {ρ0 : DGPS.Lipschitz.L2s d}
    {u : ℝ → DGPS.Lipschitz.L2s d} (hu : DGPS.Lipschitz.IsGlobalProbFlow hMF ρ0 u) :
    u 0 = ρ0 := by
  obtain ⟨_, S⟩ := hu.toMild le_rfl
  exact S.u_zero

/-- The interaction energy of `μ_f` is the quadratic form of the density `f`. -/
theorem interaction_integral_density_LIP03229 (W : Torus d → Torus d → ℝ) {f : Torus d → ℝ}
    (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x) :
    ∫ p, W p.1 p.2 ∂((densityMeasure_LIP03218 f).prod (densityMeasure_LIP03218 f)) =
      ∫ p, W p.1 p.2 * (f p.1 * f p.2) ∂(haar d).prod (haar d) := by
  unfold densityMeasure_LIP03218
  rw [prod_withDensity hf.measurable.ennreal_ofReal hf.measurable.ennreal_ofReal]
  have hm : Measurable (fun z : Torus d × Torus d =>
      ENNReal.ofReal (f z.1) * ENNReal.ofReal (f z.2)) :=
    (hf.measurable.comp measurable_fst).ennreal_ofReal.mul
      (hf.measurable.comp measurable_snd).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall fun p => ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (h0 p.1),
    ENNReal.toReal_ofReal (h0 p.2)]
  ring

/-- The real-level free energy of the class `[f]` is the measure-level energy `E(f)`. -/
theorem gate_lip032_29_initial_value_flowgap_definition_binding_energy_bridge
    (A : InteractionData d) {f : Torus d → ℝ} (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x)
    (h1 : ∫ x, f x ∂haar d = 1) :
    DGPS.Lipschitz.freeEnergy A.V A.W ⇑(l2Class_LIP03223 f) = realFreeEnergy_LIP03228 A f := by
  have hae := l2Class_coe_ae_LIP03223 (memLp_two_of_continuous_LIP03223 hf)
  obtain ⟨CV, hCV⟩ := exists_abs_bound_LIP03227 A.V A.V_continuous
  have hVb := lip032_18_density_probability_test_integral_bridge_integral hf h0 h1
    A.V_continuous.measurable ⟨CV, hCV.2⟩
  have hent : ∫ x, (l2Class_LIP03223 f) x * Real.log ((l2Class_LIP03223 f) x) ∂haar d =
      ∫ x, f x * Real.log (f x) ∂haar d := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  have hpot : ∫ x, A.V x * (l2Class_LIP03223 f) x ∂haar d =
      ∫ x, A.V x ∂densityMeasure_LIP03218 f := by
    rw [hVb.2]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx, mul_comm]
  have hq : DGPS.Lipschitz.quadE A.W ⇑(l2Class_LIP03223 f) =
      ∫ p, A.W p.1 p.2 ∂((densityMeasure_LIP03218 f).prod (densityMeasure_LIP03218 f)) := by
    rw [interaction_integral_density_LIP03229 A.W hf h0]
    unfold DGPS.Lipschitz.quadE
    refine integral_congr_ae ?_
    have h1' := (Measure.quasiMeasurePreserving_fst (μ := haar d) (ν := haar d)).ae_eq_comp hae
    have h2' := (Measure.quasiMeasurePreserving_snd (μ := haar d) (ν := haar d)).ae_eq_comp hae
    filter_upwards [h1', h2'] with p hp1 hp2
    simp only [Function.comp_apply] at hp1 hp2
    rw [hp1, hp2]
  unfold DGPS.Lipschitz.freeEnergy realFreeEnergy_LIP03228
  rw [hent, hpot, hq]

/-- The real minimum `F_*` is `E(p_μ)` for a minimizer `μ`. -/
theorem gate_lip032_29_initial_value_flowgap_definition_binding_minimum_real
    (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))
    (hμ : freeEnergy A μ = freeEnergyMinimum A) :
    freeEnergyMinimumReal A =
      realFreeEnergy_LIP03228 A (DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d))) := by
  obtain ⟨M_V, M_W, -, -, hV, hW⟩ := lip032_27_uniform_potential_interaction_bounds_exists A
  obtain ⟨-, ⟨-, -, hmin⟩, -⟩ :=
    lip032_28_real_free_energy_uniform_gap A M_V M_W hV hW μ hμ μ hμ 0 le_rfl zero_le_one
  unfold freeEnergyMinimumReal
  rw [hmin, EReal.toReal_coe]

/-- The initial value and the initial gap for any continuous nonnegative mass-one density `f`. -/
theorem gate_lip032_29_initial_value_flowgap_definition_binding_density
    (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))
    (hμ : freeEnergy A μ = freeEnergyMinimum A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    {hMF : DGPS.Lipschitz.MeanFieldData G B g β} {f : Torus d → ℝ}
    (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x) (h1 : ∫ x, f x ∂haar d = 1)
    {u : ℝ → DGPS.Lipschitz.L2s d}
    (hu : DGPS.Lipschitz.IsGlobalProbFlow hMF (l2Class_LIP03223 f) u) :
    u 0 = l2Class_LIP03223 f ∧
    DGPS.Lipschitz.flowGap A u 0 =
      realFreeEnergy_LIP03228 A f -
        realFreeEnergy_LIP03228 A (DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d))) := by
  have h := gate_lip032_29_initial_value_flowgap_definition_binding_initial_value hu
  refine ⟨h, ?_⟩
  unfold DGPS.Lipschitz.flowGap
  rw [h, gate_lip032_29_initial_value_flowgap_definition_binding_energy_bridge A hf h0 h1,
    gate_lip032_29_initial_value_flowgap_definition_binding_minimum_real A μ hμ]

/-- **LIP032.29.** Initial-value and `flowGap` definition binding: for the interpolation density
`f_{ν,s}` and every global probability flow `u` started from its class `[f_{ν,s}]`, `u 0 = [f_{ν,s}]`
and `flowGap A u 0 = E(f_{ν,s}) - E(p_μ)`. -/
theorem gate_lip032_29_initial_value_flowgap_definition_binding
    (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (ν : ProbabilityMeasure (Torus d)) (hν : freeEnergy A ν = freeEnergyMinimum A)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β) (u : ℝ → DGPS.Lipschitz.L2s d)
    (hu : DGPS.Lipschitz.IsGlobalProbFlow hMF
      (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) u) :
    u 0 = l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s) ∧
    DGPS.Lipschitz.flowGap A u 0 =
      realFreeEnergy_LIP03228 A (interpolDensity_LIP03222 A μ ν s) -
        realFreeEnergy_LIP03228 A (DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d))) := by
  obtain ⟨M_V, M_W, -, -, hV, hW⟩ := lip032_27_uniform_potential_interaction_bounds_exists A
  obtain ⟨hfc, hf1, hfb, -⟩ :=
    lip032_22_interpolation_bounded_density A M_V M_W hV hW μ hμ ν hν s hs0 hs1
  exact gate_lip032_29_initial_value_flowgap_definition_binding_density A μ hμ hfc
    (fun x => (Real.exp_pos _).le.trans (hfb x).1) hf1 hu

/-- The main statement together with the uniform bounds `0 ≤ flowGap A u 0 ≤ G_0`. -/
theorem gate_lip032_29_initial_value_flowgap_definition_binding_bounds
    (A : InteractionData d) (M_V M_W : ℝ) (hV : ∀ x, |A.V x| ≤ M_V)
    (hW : ∀ x y, |A.W x y| ≤ M_W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (ν : ProbabilityMeasure (Torus d)) (hν : freeEnergy A ν = freeEnergyMinimum A)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β) (u : ℝ → DGPS.Lipschitz.L2s d)
    (hu : DGPS.Lipschitz.IsGlobalProbFlow hMF
      (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) u) :
    u 0 = l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s) ∧
    DGPS.Lipschitz.flowGap A u 0 =
      realFreeEnergy_LIP03228 A (interpolDensity_LIP03222 A μ ν s) -
        realFreeEnergy_LIP03228 A (DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d))) ∧
    0 ≤ DGPS.Lipschitz.flowGap A u 0 ∧
    DGPS.Lipschitz.flowGap A u 0 ≤ Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W := by
  obtain ⟨h0, hgap⟩ :=
    gate_lip032_29_initial_value_flowgap_definition_binding A μ hμ ν hν s hs0 hs1 hMF u hu
  obtain ⟨-, -, hlow, hup⟩ :=
    lip032_28_real_free_energy_uniform_gap A M_V M_W hV hW μ hμ ν hν s hs0 hs1
  exact ⟨h0, hgap, by rw [hgap]; exact hlow, by rw [hgap]; exact hup⟩

/-- For `f = p_ν` with `ν` a minimizer, the initial gap and `E(p_ν) - E(p_μ)` vanish. -/
theorem gate_lip032_29_initial_value_flowgap_definition_binding_minimizer
    (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (ν : ProbabilityMeasure (Torus d)) (hν : freeEnergy A ν = freeEnergyMinimum A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β) (u : ℝ → DGPS.Lipschitz.L2s d)
    (hu : DGPS.Lipschitz.IsGlobalProbFlow hMF
      (l2Class_LIP03223 (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)))) u) :
    u 0 = l2Class_LIP03223 (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d))) ∧
    realFreeEnergy_LIP03228 A (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d))) -
        realFreeEnergy_LIP03228 A (DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d))) = 0 ∧
    DGPS.Lipschitz.flowGap A u 0 = 0 := by
  obtain ⟨hc, h0, h1, -⟩ := lip032_18_density_probability_test_integral_bridge_gibbs A ν hν
  obtain ⟨hu0, hgap⟩ :=
    gate_lip032_29_initial_value_flowgap_definition_binding_density A μ hμ hc h0 h1 hu
  have hEν := gate_lip032_29_initial_value_flowgap_definition_binding_minimum_real A ν hν
  have hEμ := gate_lip032_29_initial_value_flowgap_definition_binding_minimum_real A μ hμ
  have hz : realFreeEnergy_LIP03228 A (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d))) -
      realFreeEnergy_LIP03228 A (DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d))) = 0 := by
    rw [← hEν, ← hEμ]
    exact sub_self _
  exact ⟨hu0, hz, hgap.trans hz⟩

/-- Non-vacuity of `h_u`: a global probability flow from `[f_{ν,s}]` exists for every `h_MF`. -/
theorem gate_lip032_29_initial_value_flowgap_definition_binding_flow_exists
    (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (ν : ProbabilityMeasure (Torus d)) (hν : freeEnergy A ν = freeEnergyMinimum A)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β) :
    ∃ u : ℝ → DGPS.Lipschitz.L2s d, DGPS.Lipschitz.IsGlobalProbFlow hMF
      (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) u := by
  obtain ⟨M_V, M_W, -, -, hV, hW⟩ := lip032_27_uniform_potential_interaction_bounds_exists A
  obtain ⟨-, -, hnn, hint, hbd, -⟩ :=
    lip032_23_canonical_l2_class_representative_transport A M_V M_W hV hW μ hμ ν hν s hs0 hs1
  obtain ⟨u, hu, -⟩ := (DGPS.Lipschitz.global_bounded_flow_and_l1_stability hMF).1 _ hnn hint _ hbd
  exact ⟨u, hu⟩

end DGPS.Frontier.LIP032
