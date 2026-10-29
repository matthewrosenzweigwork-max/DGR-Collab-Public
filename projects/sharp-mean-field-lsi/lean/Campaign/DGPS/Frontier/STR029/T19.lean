import DGPS.Frontier.STR029.T56
import DGPS.Frontier.STR029.T57
import DGPS.Frontier.STR029.T58

/-!
# STR029.19: Amplitude-factored unscaled expansion

Task id: STR029.19 (node STR029, frontier unit). Title: Amplitude-factored unscaled expansion.
Prerequisites: STR029.56 (the exact quadratic amplitude factor of the reduced functional
`Fred_STR02956`), STR029.57 (the weight-four polynomial `poly19_STR02957`) and STR029.58 (the
remainder bound that retains the amplitude factor).

Statement formalized. Let `U`, `V`, `ψ` be the data of STR029.57 and STR029.58, and let
`F (a, b, h, γ) = Fred_STR02956 ψ (a, b) (h, γ)` be the reduced functional of the common chart
functional. There are a fixed coordinate neighbourhood (a closed sup-norm box of positive radius
inside `U`) and a function `𝓔` such that, with `R₀ = √(a² + b²)`, on the box
`F = -γ R₀²/2 - 9 h² R₀²/20 - h (a³ - 3 a b²)/12 + R₀⁴/48 + 𝓔`, and for every finite bound `M`
of the operator norms of the derivatives of `F` through order five on the box,
`|𝓔| ≤ M R₀² ((|h| + R₀)³ + |γ| (|h| + R₀) + γ²)`.

## Provides

* `DGPS.Frontier.STR029.str029_19_amplitude_factored_unscaled_expansion`: the main statement. It
  gives the data `U`, `V`, `ψ` with the properties of STR029.57, a radius `r > 0` with the box
  `box_STR02958 r` a neighbourhood of `0` inside `U`, a finite derivative bound `M`, and the function
  `𝓔` with the displayed expansion and the displayed bound for every admissible `M`.
* `DGPS.Frontier.STR029.str029_19_amplitude_factored_unscaled_expansion_poly19`: the displayed
  polynomial is `poly19_STR02957 a b h γ` of STR029.57, for all reals.
* `DGPS.Frontier.STR029.str029_19_amplitude_factored_unscaled_expansion_zero_amplitude`: at zero
  amplitude the remainder `F - poly19_STR02957` vanishes, whenever the slice point `(0, 0, h, γ)`
  lies in the domain `U` of a graph `ψ` that vanishes on the slice (the exact factor of STR029.56).

## R5 notes

1. Data. The statement re-states the data `U`, `V`, `ψ` of STR029.57 (open neighbourhoods of `0`,
   `ψ` smooth on `U` with `ψ 0 = 0`, `ψ p ∈ V`, and `Rpar_STR02916 p w = 0 ↔ w = ψ p` for
   `p ∈ U`, `w ∈ V`) in its own existential prefix, exactly as STR029.58 does. The graph is
   determined by `(U, V)`; no relation to any particular triple is claimed.
2. Coordinate neighbourhood. "A fixed coordinate neighbourhood" is read as the closed sup-norm box
   `box_STR02958 r = closedBall 0 r` of `ℝ × ℝ × ℝ × ℝ`, with `r > 0`, `box_STR02958 r ⊆ U`, and
   `box_STR02958 r ∈ nhds 0`. The coordinates are ordered `(a, b, h, γ)`. The statement is for every
   point of the box, including the points with `a = b = 0`, where `R₀ = 0`.
3. The functional. `F` is `Fred_STR02956 ψ (a, b) (h, γ)` of STR029.56, that is
   `Jchart_STR02950 h γ (a cos t + b sin t + ψ(a, b, h, γ))` with the variational range graph `ψ`
   (the graph of `Rpar_STR02916`). The Euler range map is not used, and nothing is assumed about a
   relation between it and the variational range map. The common optimizer-chart predicate, the
   weighted carriers and the AbsoluteDensity domain enter only through the chart functional
   `Jchart_STR02950` and the carrier `E_STR02969`, as fixed by STR029.49 to STR029.69; their
   identification with `ordinaryEntropy`, `ordinaryFisher` and `AbsoluteDensity 1` is not part of
   this unit.
4. Normalization. The angular variable carries the normalized measure `dt/(2π)` (`meanT_STR02901`).
   No rescaling by `a₀ = 4π²` and no angular-to-physical rate normalization is applied. The
   parameter `γ` is the unscaled coordinate of the reduced functional, not the scaled variable
   `γ / h²`; there is no division by `h`.
5. The remainder. `𝓔` is existential, as a function of the four reals `(a, b, h, γ)`. It is
   constrained by the expansion on the box only; on the box it is `F - poly19_STR02957`, which is
   what the proof supplies. Nothing is claimed for `𝓔` off the box.
6. The constant. "A finite constant `C` that depends only on the derivative bounds through order
   five specified in STR029.58" is read as follows. A finite `M ≥ 0` with
   `‖iteratedFDeriv ℝ k F̂ p‖ ≤ M` for all `p` in the box and all `k ≤ 5` exists, where
   `F̂ = Fhat_STR02958 ψ` is `F` viewed as a function of the four parameters and the norm is the
   operator norm of the continuous multilinear map for the sup norm; derivatives are taken in all
   four variables. For every such `M` the bound holds with `C = M`. The constant is therefore the
   bound itself and depends on nothing else.
7. The polynomial. The displayed polynomial uses `R₀ = R0_STR02918 a b`, which is `√(a² + b²)` by
   definition. It is the polynomial `poly19_STR02957` of STR029.57, as shown by the `_poly19` lemma
   (the two sides agree by unfolding). The proof states the remainder through `poly19_STR02957`.
8. No added hypothesis. The vanishing of `ψ` on the slice `a = b = 0`, the vanishing of the
   quadratic and cubic weighted jet terms and the value of the quartic term are derived inside
   STR029.58 from STR029.56 and STR029.57. None is a hypothesis here.
9. Library facts. No library fact is cited as verified at the pin or assumed. The unit applies
   STR029.58 and rearranges its conclusion.
-/

open scoped ContDiff

namespace DGPS.Frontier.STR029

/-- The displayed polynomial of STR029.19 is the polynomial `poly19_STR02957` of STR029.57. -/
theorem str029_19_amplitude_factored_unscaled_expansion_poly19 (a b h γ : ℝ) :
    poly19_STR02957 a b h γ =
      -(γ * R0_STR02918 a b ^ 2 / 2) - 9 * h ^ 2 * R0_STR02918 a b ^ 2 / 20 -
        h * (a ^ 3 - 3 * a * b ^ 2) / 12 + R0_STR02918 a b ^ 4 / 48 :=
  rfl

/-- At zero amplitude the remainder `F - poly19_STR02957` vanishes: the exact quadratic factor of
STR029.56 gives `F (0, 0, h, γ) = 0`, and the polynomial has the factor `R₀²` in each term. -/
theorem str029_19_amplitude_factored_unscaled_expansion_zero_amplitude
    (U : Set Par_STR02916) (ψ : Par_STR02916 → E_STR02969)
    (hψ0 : ∀ h γ : ℝ, ((0, 0, h, γ) : Par_STR02916) ∈ U → ψ (0, 0, h, γ) = 0)
    (h γ : ℝ) (h0U : ((0, 0, h, γ) : Par_STR02916) ∈ U) :
    Fred_STR02956 ψ (0, 0) (h, γ) - poly19_STR02957 0 0 h γ = 0 := by
  have hz : Fred_STR02956 ψ (0, 0) (h, γ) = 0 :=
    str029_56_exact_quadratic_amplitude_factor_zero U ψ hψ0 (h, γ) h0U
  have hR : R0_STR02918 0 0 = 0 := by
    simp [R0_STR02918]
  have hp : poly19_STR02957 0 0 h γ = 0 := by
    unfold poly19_STR02957
    rw [hR]
    ring
  rw [hp, sub_zero]
  exact hz

/-- STR029.19: amplitude-factored unscaled expansion. On a fixed closed coordinate box inside the
smoothness neighbourhood, `F = -γ R₀²/2 - 9 h² R₀²/20 - h (a³ - 3 a b²)/12 + R₀⁴/48 + 𝓔` with
`|𝓔| ≤ M R₀² ((|h| + R₀)³ + |γ| (|h| + R₀) + γ²)`, for every bound `M` of the operator norms of
the derivatives of `F` of order at most five on the box. -/
theorem str029_19_amplitude_factored_unscaled_expansion :
    ∃ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
      IsOpen U ∧ (0 : Par_STR02916) ∈ U ∧ IsOpen V ∧ (0 : E_STR02969) ∈ V ∧
      ContDiffOn ℝ ∞ ψ U ∧ ψ 0 = 0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
      (∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) ∧
      ∃ r : ℝ, 0 < r ∧ box_STR02958 r ⊆ U ∧ box_STR02958 r ∈ nhds (0 : Par_STR02916) ∧
        (∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ box_STR02958 r, ∀ k : ℕ, k ≤ 5 →
          ‖iteratedFDeriv ℝ k (Fhat_STR02958 ψ) p‖ ≤ M) ∧
        ∃ 𝓔 : ℝ → ℝ → ℝ → ℝ → ℝ,
          (∀ a b h γ : ℝ, ((a, b, h, γ) : Par_STR02916) ∈ box_STR02958 r →
            Fred_STR02956 ψ (a, b) (h, γ) =
              -(γ * R0_STR02918 a b ^ 2 / 2) - 9 * h ^ 2 * R0_STR02918 a b ^ 2 / 20 -
                h * (a ^ 3 - 3 * a * b ^ 2) / 12 + R0_STR02918 a b ^ 4 / 48 + 𝓔 a b h γ) ∧
          ∀ M : ℝ, 0 ≤ M → (∀ p ∈ box_STR02958 r, ∀ k : ℕ, k ≤ 5 →
              ‖iteratedFDeriv ℝ k (Fhat_STR02958 ψ) p‖ ≤ M) →
            ∀ a b h γ : ℝ, ((a, b, h, γ) : Par_STR02916) ∈ box_STR02958 r →
              |𝓔 a b h γ| ≤
                M * R0_STR02918 a b ^ 2 *
                  ((|h| + R0_STR02918 a b) ^ 3 + |γ| * (|h| + R0_STR02918 a b) + γ ^ 2) := by
  obtain ⟨U, V, ψ, hU, h0U, hV, h0V, hψ, hψ0, hψV, hiff, r, hr, hbox, hM, hrem⟩ :=
    str029_58_weighted_remainder_retaining_amplitude_factor
  refine ⟨U, V, ψ, hU, h0U, hV, h0V, hψ, hψ0, hψV, hiff, r, hr, hbox,
    Metric.closedBall_mem_nhds (0 : Par_STR02916) hr, hM,
    fun a b h γ => Fred_STR02956 ψ (a, b) (h, γ) - poly19_STR02957 a b h γ, ?_, ?_⟩
  · intro a b h γ _
    rw [← str029_19_amplitude_factored_unscaled_expansion_poly19]
    ring
  · intro M hM0 hMb a b h γ hp
    exact hrem M hM0 hMb a b h γ hp

end DGPS.Frontier.STR029
