import DGPS.Frontier.STR029.T01
import DGPS.Frontier.STR029.T16
import DGPS.Frontier.STR029.T61
import DGPS.Frontier.STR029.T62

/-!
# STR029.63: Sequential localization gives uniform neighborhood entry

Task id: STR029.63. Title: Sequential localization gives uniform neighborhood entry.

Prerequisites: STR029.01 (the bound common optimizer witness, used through the gate
`gate_str029_01_bind_common_optimizer_witness_absolute_variational`), STR029.61 (recovery of the
scaled rate from the value equation) and STR029.62 (a global optimizer in a positive chart is fully
critical).

Statement. Let `N₀, N₁, N₂ ⊆ ℝ × ℝ × ℝ` be open sets that contain the three limit points
`(2, 0, -16/15)`, `(-1, √3, -16/15)` and `(-1, -√3, -16/15)`. Then there are a graph neighbourhood
`(U, V, ψ)` of the value-equation range map (as in STR029.61) and a radius `η₁ > 0` such that for
every `h ≠ 0` with `|h| < η₁` and every absolute density `ρ` with positive entropy at `h` that is a
global optimizer of the normalized Fisher quotient at `h`, there are chart data `(a, b, w)`
representing `ρ` with `(a, b, h, r) ∈ U`, `wE = ψ (a, b, h, r)` for the element `wE` of `E`
representing `w`, and `(a / h, b / h, r / h ^ 2) ∈ N₀ ∪ N₁ ∪ N₂`, where `r = rateSTR02963 h ρ`
is the physical rate minus one.

Proof route. Suppose the conclusion fails for every radius. Choose, for each `n`, a height `h n`
with `h n ≠ 0` and `|h n| < 1 / (n + 1)` together with an optimizer `ρ n` for which no chart data
place the point in the union. The sequence `h n → 0` lets the STR029.01 gate supply chart
coordinates `(a n, b n)` and a rate coordinate `γ n` equal to the physical rate. STR029.62 and the
chart identity `Jchart = 0` give the reduced value equation, and STR029.61 then yields
`γ n / h n ^ 2 → -16/15` and `(a n / h n, b n / h n)` close to one of the three minimizers. Each
limit point has an open neighbourhood inside `N₀`, `N₁` or `N₂`, so entry holds eventually, which
contradicts the choice of `ρ n`.

Provides:
* `DGPS.Frontier.STR029.str029_63_sequential_localization_gives_uniform_neighborhood_entry`: the
  main statement above.
* `DGPS.Frontier.STR029.rateSTR02963`: the physical rate minus one,
  `(str025_quot h ρ).toReal / (4 π²) - 1`.
* `DGPS.Frontier.STR029.rate_eq_STR02963`: the physical rate equals
  `angFisher.toReal / (2 angEntropy) - 1`, the chart coordinate of STR029.01.
* `DGPS.Frontier.STR029.EntryAt_STR02963`: the chart-level entry predicate for an open set `N`
  at a height `h` and a density `ρ`.
* `DGPS.Frontier.STR029.alg_zero_STR02963`: the identity `F - 2 (1 + (F / (2 E) - 1)) E = 0` for
  `E ≠ 0`.
* `DGPS.Frontier.STR029.jchart_zero_STR02963`: the chart functional `Jchart` vanishes at the
  physical rate on a chart representative of a positive-entropy density.
* `DGPS.Frontier.STR029.step_STR02963`: STR029.62 transported to the physical rate, giving a
  value-equation solution with `Rpar = 0` and `Jchart = 0`.
* `DGPS.Frontier.STR029.norm_wE_STR02963`: the norm of `wE` in the submodule `E` is the
  `C^{2,1/2}` norm of its underlying function.
* `DGPS.Frontier.STR029.sq_lt_pair_STR02963`: `u ^ 2 + v ^ 2 < e ^ 2` gives `|u| < e` and
  `|v| < e`.
* `DGPS.Frontier.STR029.dist_triple_lt_STR02963`: three coordinatewise bounds below `d` give a
  distance below `d` in the product metric of `ℝ × ℝ × ℝ`.
* `DGPS.Frontier.STR029.coord_small_STR02963`: a coordinate of a vector in `Fin 4 → ℝ` is at most
  its Euclidean norm plus a nonnegative constant.
* `DGPS.Frontier.STR029.plane_mem_STR02963`: the three named coordinate pairs lie in
  `minimizers_STR02961`.

R5 notes:
* Open sets. `N₀`, `N₁`, `N₂` are arbitrary open sets (not balls) for the product (sup) metric on
  `ℝ × ℝ × ℝ`. Only the three limit points are assumed to lie in them. The conclusion produces one
  radius `η₁` serving all three sets, and `η₁` does not depend on `h` or on `ρ`. This is the
  uniformity asserted in the title.
* Graph neighbourhood. The triple `(U, V, ψ)` is existentially quantified in the conclusion and is
  not supplied by the hypotheses. Its properties (open sets, the origin lying in both, `ContDiffOn`,
  and the characterization of `Rpar = 0` by `w = ψ p`) are those of STR029.61.
* Domain restriction. The conclusion quantifies over `h ≠ 0` with `|h| < η₁`. The value `h = 0` is
  excluded because `a / h`, `b / h` and `r / h ^ 2` are undefined there.
* Positive entropy and optimality. `0 < ordinaryEntropy h ρ` is required for each `ρ`. Global
  optimality means that `ordinaryFisher / (2 · ordinaryEntropy)` at `ρ` is at most the same ratio
  at every density with positive entropy at the same `h`, as in STR029.62.
* Rate convention. The fourth coordinate is `r = rateSTR02963 h ρ`, the physical rate minus one,
  and not the chart coordinate of STR029.01 itself. `rate_eq_STR02963` identifies the two through
  `str025_quot_toReal_STR02901`. The proof uses this identification in both directions.
* Hölder exponent. The chart witnesses are fixed at exponent `1/2`, the `C^{2,1/2}` class. The
  STR029.01 gate is instantiated at `α = 1/2` with the instance `holderExponent_half_STR02901`.
* Chart witness. The witness is `(a, b, w)` with `IsC2Alpha (1/2) w` and `InE w`, together with an
  element `wE` of the submodule `E` whose underlying function is `w`. The representation of the
  density holds almost everywhere for the angular Haar measure, after the angular equivalence.
* Non-constructive step. The proof chooses the counterexample sequence `(h n, ρ n)` by contradiction,
  with `|h n| < 1 / (n + 1)`. The statement is therefore not constructive in `η₁`.
* Minimizers. Closeness to the three minimizers is measured by `Metric.infDist` in the Euclidean
  plane `plane_STR02961`. The three minimizers are the pairs `(2, 0)`, `(-1, √3)` and `(-1, -√3)`.
-/

open scoped ContDiff
open Filter Topology
open DGPS.Analysis.PeriodicHolder
open MeasureTheory Set
open DGPS.Circle.AngularNormalization
open scoped ENNReal
open DGPS DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Frontier.STR029

/-! ### The physical rate -/

/-- The physical rate minus one: `(str025_quot h ρ).toReal / (4 π²) - 1`. -/
noncomputable def rateSTR02963 (h : ℝ) (ρ : AbsoluteDensity 1) : ℝ :=
  (str025_quot h ρ).toReal / (4 * Real.pi ^ 2) - 1

/-- The physical rate equals the angular Fisher-entropy quotient minus one. -/
theorem rate_eq_STR02963 (h : ℝ) (ρ : AbsoluteDensity 1) :
    rateSTR02963 h ρ = (angFisher_STR02901 h (gAng_STR02901 h ρ)).toReal /
      (2 * angEntropy_STR02901 h (gAng_STR02901 h ρ)) - 1 := by
  unfold rateSTR02963
  rw [str025_quot_toReal_STR02901]

/-- Chart-level entry: some chart representative `(a, b, w)` of `ρ` at height `h` places the
point `(a, b, h, rateSTR02963 h ρ)` in `U`, with the value-equation solution `wE = ψ`, and the
scaled point `(a / h, b / h, rate / h ^ 2)` in `N`. -/
abbrev EntryAt_STR02963 (U : Set Par_STR02916) (ψ : Par_STR02916 → E_STR02969)
    (N : Set (ℝ × ℝ × ℝ)) (h : ℝ) (ρ : AbsoluteDensity 1) : Prop :=
  ∃ (a b : ℝ) (w : ℝ → ℝ),
    (∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h (uT_STR02901 a b w) (angSec θ)) ∧
    IsC2Alpha_STR02901 (1 / 2) w ∧ InE_STR02901 w ∧
    ∃ wE : E_STR02969, (wE : PeriodicC2_STR02969).val = w ∧
      (a, b, h, rateSTR02963 h ρ) ∈ U ∧ wE = ψ (a, b, h, rateSTR02963 h ρ) ∧
      (a / h, b / h, rateSTR02963 h ρ / h ^ 2) ∈ N

/-! ### Algebra and the chart functional -/

/-- The identity `F - 2 (1 + (F / (2 E) - 1)) E = 0` for `E ≠ 0`. -/
theorem alg_zero_STR02963 (F E : ℝ) (hE : E ≠ 0) :
    F - 2 * (1 + (F / (2 * E) - 1)) * E = 0 := by
  have h2 : (2 : ℝ) * E ≠ 0 := mul_ne_zero two_ne_zero hE
  have key : F / (2 * E) * (2 * E) = F := div_mul_cancel₀ F h2
  linear_combination -key

/-- At the physical rate, the chart functional `Jchart` vanishes on the chart representative of a
positive-entropy density. -/
theorem jchart_zero_STR02963 (h : ℝ) (ρ : AbsoluteDensity 1)
    (hpos : 0 < ordinaryEntropy h ρ) (a b : ℝ) (w : ℝ → ℝ) (hw : IsC2Alpha_STR02901 (1 / 2) w)
    (hrep : ∀ᵐ θ ∂angHaar,
      ρ.density (angEquiv.symm θ) = rhoT_STR02901 h (uT_STR02901 a b w) (angSec θ)) :
    Jchart_STR02950 h (rateSTR02963 h ρ) (uT_STR02901 a b w) = 0 := by
  have hu := uT_isC2_STR02962 a b hw
  have hc : Continuous (uT_STR02901 a b w) := hu.2.1.continuous
  have hae := gAng_ae_eq_gLift_STR02962 h ρ hc hrep
  have H0 : angEntropy_STR02901 h (gAng_STR02901 h ρ) =
      entropyChart_STR02949 h (uT_STR02901 a b w) :=
    (angEntropy_congr_STR02962 h hae).trans (angEntropy_gLift_STR02962 h hc)
  have F0 : angFisher_STR02901 h (gAng_STR02901 h ρ) =
      ENNReal.ofReal (fisherChart_STR02949 h (uT_STR02901 a b w)) :=
    (angFisher_congr_STR02962 h hae).trans (angFisher_gLift_STR02962 h hu)
  have hE : angEntropy_STR02901 h (gAng_STR02901 h ρ) ≠ 0 :=
    ((ordinaryEntropy_pos_iff_STR02901 h ρ).1 hpos).ne'
  have hF : (angFisher_STR02901 h (gAng_STR02901 h ρ)).toReal =
      fisherChart_STR02949 h (uT_STR02901 a b w) := by
    rw [F0, ENNReal.toReal_ofReal (fisherChart_nonneg_STR02962 h hc)]
  unfold Jchart_STR02950
  rw [rate_eq_STR02963, hF, ← H0]
  exact alg_zero_STR02963 _ _ hE

/-- STR029.62 transported to the physical rate: a value-equation solution `wE` representing `w`
with `Rpar = 0` at `(a, b, h, rateSTR02963 h ρ)`, and the chart functional vanishes there. -/
theorem step_STR02963 (h : ℝ) (ρ : AbsoluteDensity 1)
    (hpos : 0 < ordinaryEntropy h ρ)
    (hmin : ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
      ordinaryFisher h ρ / (2 * ordinaryEntropy h ρ) ≤
        ordinaryFisher h ρ' / (2 * ordinaryEntropy h ρ'))
    (a b : ℝ) (w : ℝ → ℝ) (hw : IsC2Alpha_STR02901 (1 / 2) w) (hwE : InE_STR02901 w)
    (hrep : ∀ᵐ θ ∂angHaar,
      ρ.density (angEquiv.symm θ) = rhoT_STR02901 h (uT_STR02901 a b w) (angSec θ)) :
    ∃ wE : E_STR02969, (wE : PeriodicC2_STR02969).val = w ∧
      Rpar_STR02916 (a, b, h, rateSTR02963 h ρ) wE = 0 ∧
      Jchart_STR02950 h (rateSTR02963 h ρ) (uT_STR02901 a b w) = 0 := by
  obtain ⟨-, -, wE, hval, hR, -⟩ :=
    str029_62_global_optimizer_positive_chart_fully_critical h ρ hpos hmin a b w hw hwE hrep _ rfl
  refine ⟨wE, hval, ?_, jchart_zero_STR02963 h ρ hpos a b w hw hrep⟩
  rw [rate_eq_STR02963]
  exact hR

/-! ### Norms, coordinates and planar distances -/

/-- The norm of `wE` in `E` is the `C^{2,1/2}` norm of its underlying function. -/
theorem norm_wE_STR02963 (wE : E_STR02969) :
    ‖wE‖ = c2Norm_STR02901 (1 / 2) (wE : PeriodicC2_STR02969).val :=
  PeriodicC2_STR02969.norm_def (wE : PeriodicC2_STR02969)

/-- From `u ^ 2 + v ^ 2 < e ^ 2` with `0 ≤ e`, both `|u|` and `|v|` are below `e`. -/
theorem sq_lt_pair_STR02963 {u v e : ℝ} (he : 0 ≤ e) (h : u ^ 2 + v ^ 2 < e ^ 2) :
    |u| < e ∧ |v| < e :=
  ⟨abs_lt_of_sq_lt_sq (by linarith [sq_nonneg v]) he,
    abs_lt_of_sq_lt_sq (by linarith [sq_nonneg u]) he⟩

/-- Three coordinatewise bounds below `d` give a product-metric distance below `d`. -/
theorem dist_triple_lt_STR02963 {x y z x' y' z' d : ℝ} (h1 : |x - x'| < d)
    (h2 : |y - y'| < d) (h3 : |z - z'| < d) :
    dist ((x, y, z) : ℝ × ℝ × ℝ) (x', y', z') < d := by
  simp only [Prod.dist_eq, Real.dist_eq]
  exact max_lt h1 (max_lt h2 h3)

/-- A coordinate of a vector in `Fin 4 → ℝ` is bounded by its Euclidean norm plus `c`. -/
theorem coord_small_STR02963 (v : Fin 4 → ℝ) {c : ℝ} (hc : 0 ≤ c) (i : Fin 4) :
    |v i| ≤ Real.sqrt (∑ j, v j ^ 2) + c := by
  have h1 : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
    Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg (v j))
      (Finset.mem_univ i)
  have h2 : |v i| ≤ Real.sqrt (∑ j, v j ^ 2) := Real.abs_le_sqrt h1
  linarith

/-- The three named coordinate pairs lie in the minimizer set of STR029.61. -/
theorem plane_mem_STR02963 {A B : ℝ}
    (h : (A = 2 ∧ B = 0) ∨ (A = -1 ∧ B = Real.sqrt 3) ∨ (A = -1 ∧ B = -Real.sqrt 3)) :
    plane_STR02961 A B ∈ minimizers_STR02961 := by
  unfold minimizers_STR02961
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-! ### The main statement -/

/-- Sequential localization gives uniform neighborhood entry. For open sets `N₀, N₁, N₂` around the
three limit points, there is a graph neighbourhood `(U, V, ψ)` and a radius `η₁ > 0` such that
every positive-entropy global optimizer at every height `0 < |h| < η₁` enters `N₀ ∪ N₁ ∪ N₂`
after rescaling, through a chart representative with `wE = ψ (a, b, h, r)`. -/
theorem str029_63_sequential_localization_gives_uniform_neighborhood_entry
    (N₀ N₁ N₂ : Set (ℝ × ℝ × ℝ)) (hN₀ : IsOpen N₀) (hN₁ : IsOpen N₁) (hN₂ : IsOpen N₂)
    (hp₀ : ((2 : ℝ), (0 : ℝ), (-16 / 15 : ℝ)) ∈ N₀)
    (hp₁ : ((-1 : ℝ), Real.sqrt 3, (-16 / 15 : ℝ)) ∈ N₁)
    (hp₂ : ((-1 : ℝ), -Real.sqrt 3, (-16 / 15 : ℝ)) ∈ N₂) :
    ∃ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
      IsOpen U ∧ (0 : Par_STR02916) ∈ U ∧ IsOpen V ∧ (0 : E_STR02969) ∈ V ∧
      ContDiffOn ℝ ∞ ψ U ∧ ψ 0 = 0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
      (∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) ∧
      ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ h : ℝ, h ≠ 0 → |h| < η₁ → ∀ ρ : AbsoluteDensity 1,
        0 < ordinaryEntropy h ρ →
        (∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
          ordinaryFisher h ρ / (2 * ordinaryEntropy h ρ) ≤
            ordinaryFisher h ρ' / (2 * ordinaryEntropy h ρ')) →
        ∃ (a b : ℝ) (w : ℝ → ℝ),
          (∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) =
            rhoT_STR02901 h (uT_STR02901 a b w) (angSec θ)) ∧
          IsC2Alpha_STR02901 (1 / 2) w ∧ InE_STR02901 w ∧
          ∃ wE : E_STR02969, (wE : PeriodicC2_STR02969).val = w ∧
            (a, b, h, rateSTR02963 h ρ) ∈ U ∧ wE = ψ (a, b, h, rateSTR02963 h ρ) ∧
            (a / h, b / h, rateSTR02963 h ρ / h ^ 2) ∈ N₀ ∪ N₁ ∪ N₂ := by
  obtain ⟨U, V, ψ, hU, h0U, hV, h0V, hdiff, hψ0, hψV, hiff, r, -, hbox, hnhds, -, -, -, hseq⟩ :=
    str029_61_recover_scaled_rate_value_equation
  refine ⟨U, V, ψ, hU, h0U, hV, h0V, hdiff, hψ0, hψV, hiff, ?_⟩
  by_contra hcon
  have key : ∀ n : ℕ, ∃ h : ℝ, h ≠ 0 ∧ |h| < 1 / ((n : ℝ) + 1) ∧ ∃ ρ : AbsoluteDensity 1,
      0 < ordinaryEntropy h ρ ∧
      (∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
        ordinaryFisher h ρ / (2 * ordinaryEntropy h ρ) ≤
          ordinaryFisher h ρ' / (2 * ordinaryEntropy h ρ')) ∧
      ¬ EntryAt_STR02963 U ψ (N₀ ∪ N₁ ∪ N₂) h ρ := by
    intro n
    by_contra hn
    apply hcon
    refine ⟨1 / ((n : ℝ) + 1), by positivity, fun h hh0 hlt ρ hpos hopt => ?_⟩
    by_contra hc
    exact hn ⟨h, hh0, hlt, ρ, hpos, hopt, hc⟩
  choose hh hh0 hlt ρs hpos hopt hnc using key
  have := holderExponent_half_STR02901
  have hT : Tendsto hh atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact (hlt n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hne : ∀ᶠ n in atTop, hh n ≠ 0 := Filter.Eventually.of_forall hh0
  obtain ⟨x, -, hamp, -, hp3, hae, htend, hC2E, -⟩ :=
    gate_str029_01_bind_common_optimizer_witness_absolute_variational hh hT hne ρs hpos hopt
      (1 / 2)
  have hγ : ∀ n, (x n).1 3 = rateSTR02963 (hh n) (ρs n) := fun n => by
    rw [hp3 n, rate_eq_STR02963]
  have hcoord : ∀ i : Fin 4, Tendsto (fun n => (x n).1 i) atTop (𝓝 0) := fun i =>
    squeeze_zero_norm (fun n => by
      rw [Real.norm_eq_abs]
      exact coord_small_STR02963 (x n).1
        (c2Norm_nonneg_STR02969 (wT_STR02901 ((x n).2 : PH (1 / 2) 2))) i) htend
  have Tt : Tendsto (fun n => ((x n).1 0, (x n).1 1, hh n, (x n).1 3) : ℕ → Par_STR02916) atTop
      (𝓝 (0 : Par_STR02916)) :=
    (hcoord 0).prodMk_nhds ((hcoord 1).prodMk_nhds (hT.prodMk_nhds (hcoord 3)))
  have hbox_ev : ∀ᶠ n in atTop, ((x n).1 0, (x n).1 1, hh n, (x n).1 3) ∈ box_STR02958 r :=
    Tt.eventually_mem hnhds
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.mp hV 0 h0V
  have hsmall : ∀ᶠ n in atTop,
      c2Norm_STR02901 (1 / 2) (wT_STR02901 ((x n).2 : PH (1 / 2) 2)) < ε₀ := by
    filter_upwards [htend.eventually (gt_mem_nhds hε₀)] with n hn
    have hn' : Real.sqrt (∑ i, (x n).1 i ^ 2) +
        c2Norm_STR02901 (1 / 2) (wT_STR02901 ((x n).2 : PH (1 / 2) 2)) < ε₀ := hn
    have := Real.sqrt_nonneg (∑ i, (x n).1 i ^ 2)
    linarith
  have hpre : ∀ᶠ n in atTop,
      ((x n).1 0, (x n).1 1, hh n, rateSTR02963 (hh n) (ρs n)) ∈ U ∧
      ∃ wE : E_STR02969, (wE : PeriodicC2_STR02969).val =
          wT_STR02901 ((x n).2 : PH (1 / 2) 2) ∧
        wE = ψ ((x n).1 0, (x n).1 1, hh n, rateSTR02963 (hh n) (ρs n)) ∧
        Jchart_STR02950 (hh n) (rateSTR02963 (hh n) (ρs n))
          (uT_STR02901 ((x n).1 0) ((x n).1 1) (wT_STR02901 ((x n).2 : PH (1 / 2) 2))) = 0 := by
    filter_upwards [hae, hbox_ev, hsmall] with n hae_n hbox_n hsmall_n
    obtain ⟨wE, hval, hR, hJ⟩ :=
      step_STR02963 (hh n) (ρs n) (hpos n) (hopt n) ((x n).1 0) ((x n).1 1)
        (wT_STR02901 ((x n).2 : PH (1 / 2) 2)) (hC2E n).1 (hC2E n).2 hae_n
    have hpU : ((x n).1 0, (x n).1 1, hh n, rateSTR02963 (hh n) (ρs n)) ∈ U := by
      rw [← hγ n]
      exact hbox hbox_n
    have hwball : wE ∈ Metric.ball (0 : E_STR02969) ε₀ := by
      rw [Metric.mem_ball, dist_zero_right, norm_wE_STR02963, hval]
      exact hsmall_n
    have hwV : wE ∈ V := hball hwball
    have hψn := (hiff _ hpU wE hwV).1 hR
    exact ⟨hpU, wE, hval, hψn, hJ⟩
  have hFredEv : ∀ᶠ n in atTop, Fred_STR02956 ψ ((x n).1 0, (x n).1 1) (hh n, (x n).1 3) = 0 := by
    filter_upwards [hpre] with n hn
    obtain ⟨-, wE, hval, hψn, hJ⟩ := hn
    show Jchart_STR02950 (hh n) ((x n).1 3)
      (uT_STR02901 ((x n).1 0) ((x n).1 1)
        ((ψ ((x n).1 0, (x n).1 1, hh n, (x n).1 3) : E_STR02969) : PeriodicC2_STR02969).val) = 0
    rw [hγ n, ← hψn, hval]
    exact hJ
  have Tinf : Tendsto (fun n => Metric.infDist
      (plane_STR02961 ((x n).1 0 / hh n) ((x n).1 1 / hh n)) minimizers_STR02961) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hamp ε hε] with n hn
    obtain ⟨A, B, hAB, hlt2⟩ := hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg]
    calc Metric.infDist (plane_STR02961 ((x n).1 0 / hh n) ((x n).1 1 / hh n)) minimizers_STR02961
        ≤ dist (plane_STR02961 ((x n).1 0 / hh n) ((x n).1 1 / hh n)) (plane_STR02961 A B) :=
          Metric.infDist_le_dist_of_mem (plane_mem_STR02963 hAB)
      _ = Real.sqrt (((x n).1 0 / hh n - A) ^ 2 + ((x n).1 1 / hh n - B) ^ 2) :=
          plane_dist_STR02961 _ _ _ _
      _ < ε := (Real.sqrt_lt' hε).2 hlt2
  obtain ⟨-, -, hlim⟩ := hseq (fun n => (x n).1 0) (fun n => (x n).1 1) hh
    (fun n => (x n).1 3) hT hne (hcoord 3) hFredEv hbox_ev Tinf
  have hlim' : Tendsto (fun n => rateSTR02963 (hh n) (ρs n) / hh n ^ 2) atTop
      (𝓝 (-16 / 15)) := by
    simpa only [hγ] using hlim
  obtain ⟨r₀, hr₀, hb₀⟩ := Metric.isOpen_iff.mp hN₀ _ hp₀
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.isOpen_iff.mp hN₁ _ hp₁
  obtain ⟨r₂, hr₂, hb₂⟩ := Metric.isOpen_iff.mp hN₂ _ hp₂
  obtain ⟨δ, hδ, hδ₀, hδ₁, hδ₂⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ r₀ ∧ δ ≤ r₁ ∧ δ ≤ r₂ :=
    ⟨min r₀ (min r₁ r₂), lt_min hr₀ (lt_min hr₁ hr₂), min_le_left _ _,
      le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _) (min_le_right _ _)⟩
  have hs₀ : Metric.ball ((2 : ℝ), (0 : ℝ), (-16 / 15 : ℝ)) δ ⊆ N₀ :=
    (Metric.ball_subset_ball hδ₀).trans hb₀
  have hs₁ : Metric.ball ((-1 : ℝ), Real.sqrt 3, (-16 / 15 : ℝ)) δ ⊆ N₁ :=
    (Metric.ball_subset_ball hδ₁).trans hb₁
  have hs₂ : Metric.ball ((-1 : ℝ), -Real.sqrt 3, (-16 / 15 : ℝ)) δ ⊆ N₂ :=
    (Metric.ball_subset_ball hδ₂).trans hb₂
  have hz : ∀ᶠ n in atTop, |rateSTR02963 (hh n) (ρs n) / hh n ^ 2 - (-16 / 15)| < δ / 2 := by
    filter_upwards [Metric.tendsto_nhds.mp hlim' (δ / 2) (by linarith)] with n hn
    rw [Real.dist_eq] at hn
    exact hn
  have hN : ∀ᶠ n in atTop,
      ((x n).1 0 / hh n, (x n).1 1 / hh n, rateSTR02963 (hh n) (ρs n) / hh n ^ 2) ∈
        N₀ ∪ N₁ ∪ N₂ := by
    filter_upwards [hamp (δ / 2) (by linarith), hz] with n hn hzn
    obtain ⟨A, B, hAB, hlt3⟩ := hn
    obtain ⟨hu, hv⟩ := sq_lt_pair_STR02963 (by linarith : (0 : ℝ) ≤ δ / 2) hlt3
    have hw : |rateSTR02963 (hh n) (ρs n) / hh n ^ 2 - (-16 / 15)| < δ := by linarith
    rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Set.mem_union_left _ (Set.mem_union_left _ (hs₀ (Metric.mem_ball.mpr
        (dist_triple_lt_STR02963 (by linarith) (by linarith) hw))))
    · exact Set.mem_union_left _ (Set.mem_union_right _ (hs₁ (Metric.mem_ball.mpr
        (dist_triple_lt_STR02963 (by linarith) (by linarith) hw))))
    · exact Set.mem_union_right _ (hs₂ (Metric.mem_ball.mpr
        (dist_triple_lt_STR02963 (by linarith) (by linarith) hw)))
  have hev : ∀ᶠ n in atTop, EntryAt_STR02963 U ψ (N₀ ∪ N₁ ∪ N₂) (hh n) (ρs n) := by
    filter_upwards [hae, hpre, hN] with n hae_n hn hN_n
    obtain ⟨hpU, wE, hval, hψn, -⟩ := hn
    exact ⟨(x n).1 0, (x n).1 1, wT_STR02901 ((x n).2 : PH (1 / 2) 2), hae_n, (hC2E n).1,
      (hC2E n).2, wE, hval, hpU, hψn, hN_n⟩
  obtain ⟨n, hn⟩ := hev.exists
  exact hnc n hn

end DGPS.Frontier.STR029
