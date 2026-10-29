import DGPS.Frontier.STR029.T70
import DGPS.Frontier.STR029.T71

/-!
# STR029.17: Assemble the independent second range jet

Task id: STR029.17 (node STR029), "Assemble the independent second range jet".

Statement formalized. Let `ψ` be the smooth range graph of STR029.16, with parameters
`p = (a, b, h, γ)` and values in the Hölder carrier `E`. For every compact set `K` of triples
`(A, B, s)` there are `δ > 0` and `M ≥ 0` such that, for all `(A, B, s) ∈ K` and all `|h| ≤ δ`,
the scaled point `(h A, h B, h, h² s)` lies in the graph domain and
`‖ψ (h A, h B, h, h² s) - h² q_*(A, B)‖_E ≤ M |h|³`, where `q_*` is the explicit second-order
range jet of the specification.

Provides (every declaration is in the namespace `DGPS.Frontier.STR029`):

* `DGPS.Frontier.STR029.str029_17_assemble_independent_second_range_jet`: the main statement. There
  are open sets `U ∋ 0` in `ℝ⁴` and `V ∋ 0` in `E` and a map `ψ`, the graph of STR029.16, such that
  `ψ (h A, h B, h, h² s) = h² q_*(A, B) + O(|h|³)` in the `C^{2,1/2}` norm, uniformly for
  `(A, B, s)` in compact sets.

Supporting declarations (all carry the suffix `_STR02917`):

* `qstarFn_STR02917`: the explicit function `q_*(A, B) : ℝ → ℝ`.
* `qstar_STR02917`: the element `q_*(A, B) ∈ E`.
* `qstarFn_isC2_STR02917`, `qstarFn_inE_STR02917`: `q_*` lies in the `C^{2,1/2}` class and in `E`.
* `qstarFn_eq_STR02917`: `qstarFn_STR02917` equals the function `qstarFun_STR02971` of STR029.71.
* `qstar_eq_STR02917`: `qstar_STR02917` equals the element `qstar_STR02971` of STR029.71.

R5 notes:

* Assembly. No new analytic estimate is proved in this unit. The estimate is the graph form of
  STR029.71, `str029_71_scaled_implicit_derivatives_uniform_range_remainder_graph`. Its proof uses
  the order-two forcing of STR029.70, the implicit derivatives of STR029.71, and the uniform
  third-order Taylor remainder. The displayed remainder conjunct is the statement of this unit.
* Graph. The existential over `(U, V, ψ)` names the graph of STR029.16: the listed properties are
  those of `str029_16_unique_smooth_range_graph`. Because `R(p, w) = 0 ↔ w = ψ p` for `p ∈ U`
  and `w ∈ V`, the value `ψ p` is the unique root in `V`, so `ψ` is not a free choice. No
  hypothesis is added; the existence of the graph is part of the claim.
* Uniformity. "Uniformly for `(A, B, s)` in any fixed compact set" is read as
  `K : Set (ℝ × ℝ × ℝ)` with `IsCompact K`, coordinates ordered `(A, B, s)`. The constants `δ` and
  `M` do not depend on the point of `K`. "For small `h`" is `|h| ≤ δ` with `δ > 0`.
* Parameters. The point `(h A, h B, h, h² s)` is read in `ℝ⁴ = (a, b, h, γ)` with `a = h A`,
  `b = h B` and `γ = h² s`, so `s = γ / h²`.
* Remainder. "`O_{C^{2,α}}(h³)`" is read as the explicit bound `‖·‖_E ≤ M |h|³` in the carrier `E`
  of STR029.69, whose norm is `‖u‖∞ + ‖u'‖∞ + ‖u''‖∞ + [u'']_{1/2}` in the circular distance. The
  exponent is the specified `α = 1/2`. The constant `M` is the bound itself, with no `1/6`
  normalization.
* Added conjunct. The conclusion also states `(h A, h B, h, h² s) ∈ U` for `|h| ≤ δ`, so that `ψ`
  is evaluated on its graph domain. This strengthens the displayed statement; it adds no
  hypothesis.
* Range map. `Rpar_STR02916 (a, b, h, γ) w = Rvar_STR02915 (a, b, h, γ, w)` is the variational
  range map of STR029.15, that is `P` applied to the gradient `G(h, γ, a cos t + b sin t + w)`. It
  is not the Euler range map, and nothing here identifies the two.
* Conventions. The optimizer-chart predicate, the weighted carriers, the AbsoluteDensity domain and
  the entropy, Fisher and deficit conventions enter only through the gradient of STR029.50 to
  STR029.55 as used by STR029.15, and are not restated here. The angular variable `t` carries the
  normalized measure `dt/(2π)`. No angular-to-physical rate conversion (`a₀ = 4π²`) enters.
* The target `q_*`. The specification gives
  `(A/2 + (B² - A²)/12) cos 2t + (-B/2 - AB/6) sin 2t - (A/10) cos 4t - (B/10) sin 4t`, which is
  `qstarFn_STR02917`. STR029.71 wrote the same function as
  `(A/2 - (A² - B²)/12) cos 2t + (-B/2 - AB/6) sin 2t + (-(A/10)) cos 4t + (-(B/10)) sin 4t`.
  The two agree by `ring`, so there is no mismatch; `qstarFn_eq_STR02917` and `qstar_eq_STR02917`
  record the identity, and the main proof transfers STR029.71's remainder through it. The formula
  also solves the forcing equation `-2 (q'' + q) + F(A, B) = 0` of STR029.70 coefficient by
  coefficient; that check was made by hand and is not a Lean claim.
* Not in this statement. The value, first and second derivative of the scaled curve and the
  `C^k` expansion of the logarithmic density are conclusions of STR029.71 and are not restated.
-/

open scoped ContDiff
open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.STR029

/-! ### The explicit range jet `q_*` -/

/-- The explicit function `q_*(A, B)` of the specification:
`(A/2 + (B² - A²)/12) cos 2t + (-B/2 - AB/6) sin 2t - (A/10) cos 4t - (B/10) sin 4t`. -/
noncomputable def qstarFn_STR02917 (A B : ℝ) : ℝ → ℝ := fun t =>
  (A / 2 + (B ^ 2 - A ^ 2) / 12) * Real.cos (2 * t) +
    (-(B / 2) - A * B / 6) * Real.sin (2 * t) -
    (A / 10) * Real.cos (4 * t) - (B / 10) * Real.sin (4 * t)

/-- The specified `q_*` agrees with the function of STR029.71 pointwise. -/
theorem qstarFn_eq_STR02917 (A B : ℝ) : qstarFn_STR02917 A B = qstarFun_STR02971 A B := by
  funext t
  simp only [qstarFn_STR02917, qstarFun_STR02971]
  ring

theorem qstarFn_isC2_STR02917 (A B : ℝ) : IsC2Alpha_STR02901 (1 / 2) (qstarFn_STR02917 A B) := by
  rw [qstarFn_eq_STR02917]
  exact qstarFun_isC2_STR02971 A B

theorem qstarFn_inE_STR02917 (A B : ℝ) : InE_STR02901 (qstarFn_STR02917 A B) := by
  rw [qstarFn_eq_STR02917]
  exact qstarFun_inE_STR02971 A B

/-- The target `q_*(A, B)` as an element of the Hölder carrier `E`. -/
noncomputable def qstar_STR02917 (A B : ℝ) : E_STR02969 :=
  ⟨PeriodicC2_STR02969.mk (qstarFn_STR02917 A B) (qstarFn_isC2_STR02917 A B),
    (str029_69_completeness_closed_complements_range_spaces_E.1 _).2 (qstarFn_inE_STR02917 A B)⟩

/-- The element `q_*(A, B) ∈ E` agrees with the element of STR029.71. -/
theorem qstar_eq_STR02917 (A B : ℝ) : qstar_STR02917 A B = qstar_STR02971 A B := by
  apply Subtype.ext
  apply Subtype.ext
  exact qstarFn_eq_STR02917 A B

/-! ### The main statement -/

/-- **STR029.17.** There are open neighbourhoods `U` of `0` in `ℝ⁴` and `V` of `0` in `E` and a
smooth map `ψ : ℝ⁴ → E`, the graph of STR029.16. For every compact set `K` of triples `(A, B, s)`
there are `δ > 0` and `M ≥ 0` such that for all `(A, B, s) ∈ K` and all `|h| ≤ δ` the scaled point
`(h A, h B, h, h² s)` lies in `U` and `‖ψ (h A, h B, h, h² s) - h² q_*(A, B)‖_E ≤ M |h|³`. -/
theorem str029_17_assemble_independent_second_range_jet :
    ∃ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
      IsOpen U ∧ (0 : Par_STR02916) ∈ U ∧ IsOpen V ∧ (0 : E_STR02969) ∈ V ∧
      ContDiffOn ℝ ∞ ψ U ∧ ψ 0 = 0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
      (∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) ∧
      ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K →
        ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ A B s : ℝ, (A, B, s) ∈ K →
          ∀ h : ℝ, |h| ≤ δ →
            ((h * A, h * B, h, h ^ 2 * s) : Par_STR02916) ∈ U ∧
            ‖ψ ((h * A, h * B, h, h ^ 2 * s) : Par_STR02916) - h ^ 2 • qstar_STR02917 A B‖ ≤
              M * |h| ^ 3 := by
  obtain ⟨U, V, ψ, hU, h0U, hV, h0V, hψ, hψ0, hψV, hiff, hK⟩ :=
    str029_71_scaled_implicit_derivatives_uniform_range_remainder_graph
  refine ⟨U, V, ψ, hU, h0U, hV, h0V, hψ, hψ0, hψV, hiff, ?_⟩
  intro K hKc
  obtain ⟨δ, hδ, M, hM, hall⟩ := hK K hKc
  refine ⟨δ, hδ, M, hM, ?_⟩
  intro A B s hABs h hh
  obtain ⟨hdom, -, -, -, -, -, hest⟩ := hall A B s hABs
  refine ⟨hdom h hh, ?_⟩
  rw [qstar_eq_STR02917]
  exact hest h hh

end DGPS.Frontier.STR029
