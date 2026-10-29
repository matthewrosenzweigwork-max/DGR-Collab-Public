import DGPS.Frontier.EX012.T07
import DGPS.Frontier.EX012.T32
import DGPS.Frontier.EX012.T33

/-!
# EX012.34: One common small neighborhood

Task id: EX012.34 (node EX012, one-site complementary range equation).
Title: One common small neighborhood.

Provides:
* `DGPS.Frontier.EX012.ex012_34_one_common_small_neighborhood`: the main statement. For `α` with
  `[HolderExponent α]`, `W = PH.orthSub α 2`, `F = rangeMap_EX01229 α`, `b₂ = bConst_EX01232 α`
  and `M₁ = mConst_EX01232 α`, there are open sets `U ⊆ ℝ × ℝ × ℝ` and `V ⊆ W` containing `0`
  and a total map `w : ℝ × ℝ × ℝ → W` such that the conclusions of EX012.07 hold (`w` is analytic
  on `U`, `w(U) ⊆ V`, `w 0 = 0`, and `F (p, z) = 0 ↔ z = w p` for `p ∈ U`, `z ∈ V`), and for every
  `p = (a, b, τ) ∈ U` one has `‖w p‖ ≤ 1 / (4 b₂)` and `|a| + |b| + √|τ| ≤ min 1 (1 / (8 b₂ M₁))`.
* `DGPS.Frontier.EX012.radius_tendsto_EX01234`: the map `p ↦ |p.1| + |p.2.1| + √|p.2.2|` tends to
  `0` at `0` (continuity of absolute value, addition and the nonnegative square root).

R5 notes:
* The only hypothesis is `[HolderExponent α]`, the campaign form of `0 < α < 1`. No hypothesis is
  added beyond the specification, and no part of the EX012.07 conclusion is weakened.
* "Shrink the parameter neighborhood" is formalized as an existential statement: the conclusion
  re-establishes the EX012.07 package (with the same `F`, `V`, `w` as produced by EX012.07) on a
  parameter neighborhood `U` that carries the two bounds. The new `U` is the interior of the set of
  parameters `p` with `p ∈ U₀`, `‖w p‖ < 1/(4 b₂)` and `r p < min(1, 1/(8 b₂ M₁))`, where `U₀`,
  `V`, `w` are the EX012.07 data. So `U ⊆ U₀` and `U` is open.
* `V` and `w` are not shrunk. The specification shrinks only the parameter neighborhood, and
  "retaining the existence/uniqueness statement of 07" is read as keeping the displayed equivalence
  `F (p, z) = 0 ↔ z = w p` for all `p ∈ U`, `z ∈ V`, together with `w(U) ⊆ V` and analyticity on `U`.
* The bounds are read on the parameter `p = (a, b, τ) ∈ ℝ × ℝ × ℝ` (the first factor of the domain
  of `F`), with `p.1 = a`, `p.2.1 = b`, `p.2.2 = τ`. The quantity `r = |a| + |b| + √|τ|` is written out
  literally, as in EX012.33 (`Real.sqrt |τ|` is nonnegative for every real `τ`).
* `‖w(p)‖` is the norm of `PH.orthSub α 2` (the norm of `PH α 2` restricted to `W`).
* `b₂` and `M₁` are the specification's constants, read as `bConst_EX01232 α = max 1 (…)` and
  `mConst_EX01232 α = max 1 (max ‖c₁‖ ‖s₁‖)` from EX012.32, with `c₁, s₁` in `PH α 2`. Both are at
  least `1` (`one_le_bConst_EX01232`, `one_le_mConst_EX01232`), so the bounds `1/(4 b₂)` and
  `1/(8 b₂ M₁)` are strictly positive. This positivity is what makes the zero of `w` and of `r`
  compatible with the strict inequalities used at `p = 0`.
* The proof uses strict inequalities on the neighborhood (`‖w p‖ < 1/(4 b₂)` and `r p < min …`) and
  weakens them to `≤` in the conclusion, as in the specification ("first choose strict inequalities and
  then weaken them"). Continuity of `w` at `0` comes from analyticity at `0 ∈ U₀`
  (`AnalyticAt.continuousAt`), and `w 0 = 0` gives the first bound at the centre; `r 0 = 0` and the
  continuity of `r` give the second.
* The "finite intersection of neighborhoods" is `Filter.Eventually.and`, and the open set is
  `interior`, so `U` is open and contains `0`. No quantitative bound on `U₀` beyond these two is claimed.
* The specification's library facts (continuity of the implicit map, absolute value, square root,
  finite intersection of neighborhoods) were checked by compilation of this file. No identifier
  is assumed beyond Mathlib declarations used in the proof, and the proof uses no placeholder proof,
  no added axiom declaration and no native evaluation.
* EX012.33 is listed as a prerequisite of the task graph; its bounds are not needed for this
  statement, which states the two bounds directly in terms of `r`, `b₂` and `M₁`.
-/

open DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic
open scoped Topology

namespace DGPS.Frontier.EX012

section Helpers

/-- The map `p ↦ |a| + |b| + √|τ|` for `p = (a, b, τ)` tends to `0` at `0`. -/
theorem radius_tendsto_EX01234 :
    Filter.Tendsto (fun p : ℝ × ℝ × ℝ => |p.1| + |p.2.1| + Real.sqrt |p.2.2|) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun p : ℝ × ℝ × ℝ => |p.1| + |p.2.1| + Real.sqrt |p.2.2|) :=
    ((continuous_abs.comp continuous_fst).add
        (continuous_abs.comp (continuous_fst.comp continuous_snd))).add
      (Real.continuous_sqrt.comp (continuous_abs.comp (continuous_snd.comp continuous_snd)))
  simpa using hc.tendsto (0 : ℝ × ℝ × ℝ)

end Helpers

section Main

variable (α : ℝ) [HolderExponent α]

/-- **EX012.34.** Shrinking the parameter neighborhood of EX012.07 to an open neighborhood `U` of
`0` on which `‖w p‖ ≤ 1/(4 b₂)` and `|a| + |b| + √|τ| ≤ min(1, 1/(8 b₂ M₁))`, with the
existence/uniqueness conclusion of EX012.07 kept on `U × V`. -/
theorem ex012_34_one_common_small_neighborhood :
    ∃ (U : Set (ℝ × ℝ × ℝ)) (V : Set (PH.orthSub α 2)) (w : ℝ × ℝ × ℝ → PH.orthSub α 2),
      IsOpen U ∧ IsOpen V ∧ (0 : ℝ × ℝ × ℝ) ∈ U ∧ (0 : PH.orthSub α 2) ∈ V ∧
      AnalyticOnNhd ℝ w U ∧ Set.MapsTo w U V ∧ w 0 = 0 ∧
      (∀ p ∈ U, ∀ z ∈ V, rangeMap_EX01229 α (p, z) = 0 ↔ z = w p) ∧
      (∀ p ∈ U, ‖w p‖ ≤ 1 / (4 * bConst_EX01232 α)) ∧
      (∀ p ∈ U, |p.1| + |p.2.1| + Real.sqrt |p.2.2| ≤
        min 1 (1 / (8 * bConst_EX01232 α * mConst_EX01232 α))) := by
  obtain ⟨U₀, V, w, hU₀, hV, h0U, h0V, han, hmaps, hw0, huniq⟩ :=
    ex012_07_analytic_implicit_function α
  have hb : 0 < bConst_EX01232 α := by linarith [one_le_bConst_EX01232 α]
  have hm : 0 < mConst_EX01232 α := by linarith [one_le_mConst_EX01232 α]
  have hc : (0 : ℝ) < 1 / (4 * bConst_EX01232 α) := div_pos one_pos (by linarith)
  have hd : (0 : ℝ) < min 1 (1 / (8 * bConst_EX01232 α * mConst_EX01232 α)) :=
    lt_min one_pos (div_pos one_pos (mul_pos (mul_pos (by norm_num) hb) hm))
  have hcont : ContinuousAt w 0 := (han 0 h0U).continuousAt
  have hwn : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ × ℝ), ‖w p‖ < 1 / (4 * bConst_EX01232 α) := by
    have ht : Filter.Tendsto (fun p => ‖w p‖) (𝓝 0) (𝓝 ‖w 0‖) := hcont.norm
    rw [hw0, norm_zero] at ht
    exact Filter.Tendsto.eventually_lt_const hc ht
  have hrn : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ × ℝ),
      |p.1| + |p.2.1| + Real.sqrt |p.2.2| < min 1 (1 / (8 * bConst_EX01232 α * mConst_EX01232 α)) :=
    Filter.Tendsto.eventually_lt_const hd radius_tendsto_EX01234
  have hU : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ × ℝ), p ∈ U₀ := Filter.eventually_mem_set.2 (hU₀.mem_nhds h0U)
  have hev : {p : ℝ × ℝ × ℝ | (p ∈ U₀ ∧ ‖w p‖ < 1 / (4 * bConst_EX01232 α)) ∧
      |p.1| + |p.2.1| + Real.sqrt |p.2.2| <
        min 1 (1 / (8 * bConst_EX01232 α * mConst_EX01232 α))} ∈ 𝓝 (0 : ℝ × ℝ × ℝ) :=
    (hU.and hwn).and hrn
  refine ⟨interior {p : ℝ × ℝ × ℝ | (p ∈ U₀ ∧ ‖w p‖ < 1 / (4 * bConst_EX01232 α)) ∧
      |p.1| + |p.2.1| + Real.sqrt |p.2.2| <
        min 1 (1 / (8 * bConst_EX01232 α * mConst_EX01232 α))},
    V, w, isOpen_interior, hV, mem_interior_iff_mem_nhds.2 hev, h0V,
    fun p hp => han p (interior_subset hp).1.1, fun p hp => hmaps (interior_subset hp).1.1, hw0,
    fun p hp z hz => huniq p (interior_subset hp).1.1 z hz,
    fun p hp => ((interior_subset hp).1.2).le,
    fun p hp => ((interior_subset hp).2).le⟩

end Main

end DGPS.Frontier.EX012
