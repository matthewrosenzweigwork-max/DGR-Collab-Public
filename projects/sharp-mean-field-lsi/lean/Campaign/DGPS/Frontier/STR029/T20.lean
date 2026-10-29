import DGPS.Frontier.STR029.T60

/-!
# STR029.20: Smooth reduced function through zero field

Task STR029.20 of frontier packet STR029, "Smooth reduced function through zero field".
For `h ≠ 0` put `V (h, A, B, s) = F (h A, h B, h, h ^ 2 * s) / h ^ 4`, where `F = Fred_STR02956 ψ`
is the reduced functional of the STR029.57 family and `ψ` is its parameter graph. The main
declaration states that `V` extends to a `C^∞` function on an open set containing every point
`(0, z)`, that its value at `h = 0` is `J_4^red A B - s (A ^ 2 + B ^ 2) / 2`, and that every fixed
`z`-derivative converges uniformly on each compact set of parameters as `h → 0`. The proof
applies the division step of STR029.60, which is the coordinate-division lemma of STR029.59
applied to the weighted jet.

Provides:
* `DGPS.Frontier.STR029.str029_20_smooth_reduced_function_through_zero_field`: there are `U`, `V`,
  `ψ` with the STR029.57 properties, an open `O` containing every `(0, z)`, and a function `E`
  that is `C^∞` on `O`, with `E (h, z) = F (h A, h B, h, h ^ 2 * s) / h ^ 4` for `h ≠ 0` and
  `E (0, z) = J_4^red A B - s (A ^ 2 + B ^ 2) / 2`, such that every `n`-th `z`-derivative of the
  division quotient converges uniformly on each compact set as `h → 0`, to the `n`-th derivative
  of the closed form.

R5 notes:
* Family. `U`, `V`, `ψ` are existentially quantified over the STR029.57 family: open neighbourhoods
  of `0`, `ψ` is `C^∞` on `U`, `ψ 0 = 0`, `ψ` takes values in `V`, and `Rpar_STR02916 p w = 0`
  holds exactly for `w = ψ p` when `p ∈ U` and `w ∈ V`. No fixed STR029.16 graph is chosen. The
  weighted remainder bound of STR029.57 is used in the proof but is not stated here, since the
  specification does not state it.
* Parameters. `z = (A, B, s)` is read as `(z 0, z 1, z 2)`. The expression
  `F (h A, h B, h, h ^ 2 * s)` is `Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2)`, which is
  definitionally `Gs_STR02960 ψ (h, z)` of STR029.60.
* Reduced functional. `F` is the variational chart composed with the family's graph `ψ`. The Euler
  range map is not used anywhere. The value `J_4^red` is identified with `Jred_STR02918` of
  STR029.18, whose Lean definition is `R_0 ^ 4 / 48 - P_3 / 12 - 9 R_0 ^ 2 / 20`. The node does not
  print a formula for `J_4^red`, so this identification is a reading for external review.
* Domain of the formula. The equation `E (h, z) = V (h, z)` is claimed only on `O` and only for
  `h ≠ 0`. Nothing is claimed about `E` off `O`.
* Near each point with `h = 0`. Read as one open set `O` containing all of `{0} × ℝ³`, on which
  `E` is `C^∞`. This is stronger than a neighbourhood for each point, because the local
  neighbourhoods are glued into `O`.
* Extension. `E` is existential, and it is constrained only on `O`. On `O` the formula clause and
  the closed-form clause determine `E` completely, so the existential is equivalent to the claim
  that `V` extends smoothly.
* Value at zero. The closed form is stated for every `z`, which is allowed because `(0, z) ∈ O`
  for every `z`.
* Derivative clause. The derivatives are taken of the global Taylor-remainder representative
  `quotientRemainder_STR02959 (Gs_STR02960 ψ) h`, the integral `(1/3!) ∫₀¹ (1-t)³ ∂_h⁴ G(th, z) dt`
  of STR029.59. This representative is defined for all `(h, z)`, whereas `E` is constrained only
  on `O`. The statement does not restate that the representative equals `V` on `O` as a separate
  clause. That agreement is what makes the two readings coincide: `z`-derivatives are local, and
  for `h` near `0` and `z` in a compact set `K` the point `(h, z)` lies in `O` by the tube lemma.
* Limit value. The limit function is the `n`-th derivative of the closed form
  `z ↦ J_4^red (z 0) (z 1) - z 2 (z 0 ^ 2 + z 1 ^ 2) / 2`, which is the value of `V` at `h = 0`.
* Compact sets. "Smaller compact sets" is read as every compact `K ⊆ ℝ³`. This contains every
  smaller compact parameter set, and the uniformity is over `K`.
* Limit along `h`. `h → 0` is read along all real `h`, that is in the filter `𝓝 0`, including
  both signs and `h = 0`. This is stronger than a one-sided limit or a limit in `𝓝[≠] 0`.
* Fixed parameter derivative. Read as the full `n`-th Fréchet derivative `iteratedFDeriv ℝ n` in
  `z`, for every `n : ℕ`. It contains every partial derivative in `(A, B, s)`.
* Division hypotheses. The vanishing of the first three `h`-derivatives at `0` and the value of the
  fourth derivative are proved inside STR029.60 from the STR029.57 bound. They are not exported by
  this statement, because the specification does not list them.
* Rate normalisation. No angular-to-physical rate normalisation is applied. The variable `h` is the
  scaled variable of STR029.57, exactly as in STR029.60.
* Library facts. The statement uses only `ContDiffOn`, `IsCompact`, `TendstoUniformlyOn` and
  `iteratedFDeriv` from Mathlib, and it cites no library fact as verified or assumed.
-/

open scoped ContDiff
open Topology

namespace DGPS.Frontier.STR029

/-- STR029.20. Smooth reduced function through zero field. -/
theorem str029_20_smooth_reduced_function_through_zero_field :
    ∃ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
      IsOpen U ∧ (0 : Par_STR02916) ∈ U ∧ IsOpen V ∧ (0 : E_STR02969) ∈ V ∧
      ContDiffOn ℝ ∞ ψ U ∧ ψ 0 = 0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
      (∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) ∧
      ∃ O : Set (ℝ × (Fin 3 → ℝ)), IsOpen O ∧ (∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O) ∧
        ∃ E : ℝ × (Fin 3 → ℝ) → ℝ, ContDiffOn ℝ ∞ E O ∧
          (∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
            E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4) ∧
          (∀ z : Fin 3 → ℝ, E ((0 : ℝ), z) =
            Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2)) ∧
          ∀ (n : ℕ) (K : Set (Fin 3 → ℝ)), IsCompact K →
            TendstoUniformlyOn
              (fun (h : ℝ) (z : Fin 3 → ℝ) =>
                iteratedFDeriv ℝ n (fun w => quotientRemainder_STR02959 (Gs_STR02960 ψ) h w) z)
              (fun z : Fin 3 → ℝ => iteratedFDeriv ℝ n
                (fun w : Fin 3 → ℝ => Jred_STR02918 (w 0) (w 1) - w 2 * ((w 0 ^ 2 + w 1 ^ 2) / 2))
                z)
              (𝓝 0) K := by
  obtain ⟨U, V, ψ, hU, h0U, hV, h0V, hψC, hψ0, hψV, hRpar, -, O, hO, h0O, hOC, hval, hzero, hlim⟩ :=
    str029_60_apply_division_retain_parameter_derivative_limits
  refine ⟨U, V, ψ, hU, h0U, hV, h0V, hψC, hψ0, hψV, hRpar, O, hO, h0O,
    fun p : ℝ × (Fin 3 → ℝ) => quotientRemainder_STR02959 (Gs_STR02960 ψ) p.1 p.2, hOC,
    ?_, ?_, ?_⟩
  · intro h z hhz hh0
    exact hval h z hhz hh0
  · intro z
    exact hzero z
  · intro n K hK
    have hfun : (fun w : Fin 3 → ℝ => quotientRemainder_STR02959 (Gs_STR02960 ψ) 0 w) =
        fun w : Fin 3 → ℝ => Jred_STR02918 (w 0) (w 1) - w 2 * ((w 0 ^ 2 + w 1 ^ 2) / 2) :=
      funext hzero
    have key := hlim n K hK
    rw [hfun] at key
    exact key

end DGPS.Frontier.STR029
