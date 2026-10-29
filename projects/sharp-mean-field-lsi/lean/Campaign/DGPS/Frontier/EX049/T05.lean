import DGPS.Frontier.EX049.T40

/-!
# EX049.05: Smooth removable profile and its primitive

Task id and title: EX049.05, "Smooth removable profile and its primitive" (node EX049, frontier unit,
leaf formalization, prerequisites EX049.37 to EX049.40).  For a real `h ≥ 2` let
`A = 2 / (1 - e^{-2h})`, `N u = A (1 - e^{-hu}) - u` and `Q u = N u / (u (2 - u))`.  The quotient
`Q` on `(0,2)` has a smooth extension `r` to an open neighborhood of `[0,2]`.  Its values and all its
derivatives on `[0,2]` do not depend on the extension, its endpoint values are
`r 0 = (A h - 1)/2` and `r 2 = (1 - A h e^{-2h})/2`, and for each such extension the primitive
`R u = ∫_0^u r` is smooth on an open neighborhood of `[0,2]` with derivative `r` there.

## Provides
* `DGPS.Frontier.EX049.ex049_05_smooth_removable_profile_primitive` : the main statement, for
  `2 ≤ h`, with five conjuncts.  (i) A smooth extension `g` of `Q` on an open `U ⊇ [0,2]` exists
  with `g 0 = (A h - 1)/2` and `g 2 = (1 - A h e^{-2h})/2`.  (ii) Every smooth extension of `Q` on
  an open `U ⊇ [0,2]` has these same two endpoint values.  (iii) Two smooth extensions agree, with
  all their iterated derivatives, at every point of `[0,2]`.  (iv) For every smooth extension `g`,
  the primitive `u ↦ ∫_0^u g` is `C^∞` on an open `W ⊇ [0,2]`, vanishes at `0`, and has derivative
  `g u` at every `u ∈ W`.  (v) Two smooth extensions have primitives that agree at every point of
  `[0,2]`.

No helper declaration is introduced.  The proof assembles the main theorems of EX049.39 and
EX049.40 and derives conjunct (ii) from the uniqueness in conjunct (iii) of EX049.39.

## R5 notes
* The only hypothesis of the main statement is `2 ≤ h`, the specification's "every `h ≥ 2`".  No
  hypothesis is added, and nothing is weakened.
* "Smooth extension to a neighborhood of `[0,2]`" is read as in EX049.39: a function `g` with
  `ContDiffOn ℝ ∞ g U` for an open set `U ⊇ [0,2]`, where `∞` is the `ℕ∞`-top smoothness class.
  Existence (conjunct (i)) is witnessed with `U = Set.univ`.
* The specification writes `r_h(0)` and `r_h(2)` for "the" extension.  Conjunct (ii) states the
  endpoint values for every smooth extension, which is the literal reading once the restriction is
  shown to be uniquely determined.  It is a strengthening of conjunct (i), obtained from conjunct
  (iii) at `u = 0` and `u = 2` with `k = 0`.
* "Its restriction and derivatives on `[0,2]` are uniquely determined": read as conjunct (iii), the
  equality of values and of every `iteratedDeriv k` at each point of `[0,2]`, for any two extensions
  on any two open neighborhoods.  No uniqueness is claimed outside `[0,2]`, where the quotient is not
  prescribed and the extension is unconstrained.
* `R_h(u) = ∫_0^u r_h(s) ds` is read as the oriented interval integral `∫ s in (0:ℝ)..u, g s`.  For
  `u < 0` this is `-∫_u^0 g`.  The smoothness of `R` and the identity `R' = g` are asserted on the
  explicit open neighborhood `W` of EX049.40, not on all of `ℝ`, because a general extension is
  unconstrained outside `[0,2]`.  The statement does not require `W = U`.
* "`R' = r_h`" is read as `HasDerivAt R (g u) u` at every `u ∈ W`, a two-sided derivative at each
  point of the open set `W`.  This includes all points of `[0,2]`.
* The integrals over `[0,u]` with `u ∈ [0,2]` in conjunct (v) use only the restriction of the
  integrands to `[0,2]`, which is fixed by agreement on `(0,2)` and continuity, as in EX049.40.
* The Lean division convention plays no role in the hypotheses: `Q` enters only through its values on
  `(0,2)`, where the denominators `u` and `2 - u` are nonzero.  The endpoint values in conjuncts (i)
  and (ii) are values of the extension `g`, not of the quotient `Q`.
* The binding of `R_h` to the campaign `corr h`, and of `r_h` to the campaign objects, is not proved
  here.  It is the open task EX049.25, as stated in the specification.
-/

open scoped ContDiff

namespace DGPS.Frontier.EX049

/-- Smooth removable profile and its primitive.  For every real `h ≥ 2`, with `A`, `N` and `Q` as in
EX049.39: (i) a smooth extension of `Q` to an open neighborhood of `[0,2]` exists with endpoint
values `(A h - 1)/2` at `0` and `(1 - A h e^{-2h})/2` at `2`; (ii) every smooth extension of `Q` has
these endpoint values; (iii) two smooth extensions agree on `[0,2]` together with all iterated
derivatives; (iv) every smooth extension `g` has a primitive `u ↦ ∫_0^u g` that is `C^∞` on an open
neighborhood of `[0,2]`, vanishes at `0`, and has derivative `g` there; (v) two smooth extensions
have primitives that agree on `[0,2]`. -/
theorem ex049_05_smooth_removable_profile_primitive (h : ℝ) (hh : 2 ≤ h) :
    let A : ℝ := 2 / (1 - Real.exp (-(2 * h)))
    let N : ℝ → ℝ := fun u => A * (1 - Real.exp (-(h * u))) - u
    let Q : ℝ → ℝ := fun u => N u / (u * (2 - u))
    (∃ g : ℝ → ℝ, ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (0:ℝ) 2 ⊆ U ∧ ContDiffOn ℝ ∞ g U ∧
        (∀ u ∈ Set.Ioo (0:ℝ) 2, g u = Q u) ∧ g 0 = (A * h - 1) / 2 ∧
        g 2 = (1 - A * h * Real.exp (-(2 * h))) / 2) ∧
    (∀ g : ℝ → ℝ, ∀ U : Set ℝ, IsOpen U → Set.Icc (0:ℝ) 2 ⊆ U → ContDiffOn ℝ ∞ g U →
        (∀ u ∈ Set.Ioo (0:ℝ) 2, g u = Q u) →
        g 0 = (A * h - 1) / 2 ∧ g 2 = (1 - A * h * Real.exp (-(2 * h))) / 2) ∧
    (∀ (U₁ U₂ : Set ℝ) (g₁ g₂ : ℝ → ℝ), IsOpen U₁ → IsOpen U₂ →
        Set.Icc (0:ℝ) 2 ⊆ U₁ → Set.Icc (0:ℝ) 2 ⊆ U₂ →
        ContDiffOn ℝ ∞ g₁ U₁ → ContDiffOn ℝ ∞ g₂ U₂ →
        (∀ u ∈ Set.Ioo (0:ℝ) 2, g₁ u = Q u) → (∀ u ∈ Set.Ioo (0:ℝ) 2, g₂ u = Q u) →
        ∀ k : ℕ, ∀ u ∈ Set.Icc (0:ℝ) 2,
          g₁ u = g₂ u ∧ iteratedDeriv k g₁ u = iteratedDeriv k g₂ u) ∧
    (∀ g : ℝ → ℝ, ∀ U : Set ℝ, IsOpen U → Set.Icc (0:ℝ) 2 ⊆ U → ContDiffOn ℝ ∞ g U →
        (∀ u ∈ Set.Ioo (0:ℝ) 2, g u = Q u) →
        ∃ W : Set ℝ, IsOpen W ∧ Set.Icc (0:ℝ) 2 ⊆ W ∧
          ContDiffOn ℝ ∞ (fun x : ℝ => ∫ s in (0:ℝ)..x, g s) W ∧
          (∫ s in (0:ℝ)..(0:ℝ), g s) = 0 ∧
          ∀ u ∈ W, HasDerivAt (fun x : ℝ => ∫ s in (0:ℝ)..x, g s) (g u) u) ∧
    (∀ (U₁ U₂ : Set ℝ) (g₁ g₂ : ℝ → ℝ), IsOpen U₁ → IsOpen U₂ →
        Set.Icc (0:ℝ) 2 ⊆ U₁ → Set.Icc (0:ℝ) 2 ⊆ U₂ →
        ContDiffOn ℝ ∞ g₁ U₁ → ContDiffOn ℝ ∞ g₂ U₂ →
        (∀ u ∈ Set.Ioo (0:ℝ) 2, g₁ u = Q u) → (∀ u ∈ Set.Ioo (0:ℝ) 2, g₂ u = Q u) →
        ∀ u ∈ Set.Icc (0:ℝ) 2,
          ∫ s in (0:ℝ)..u, g₁ s = ∫ s in (0:ℝ)..u, g₂ s) := by
  intro A N Q
  obtain ⟨hex, huniq⟩ := ex049_39_glue_smooth_correction_derivative h hh
  obtain ⟨-, hprim, hind⟩ := ex049_40_primitive_smooth_profile h hh
  refine ⟨hex, ?_, huniq, hprim, hind⟩
  intro g U hU hI hc hQg
  obtain ⟨g₀, U₀, hU₀, hI₀, hc₀, hQ₀, h0, h2⟩ := hex
  obtain ⟨e0, -⟩ := huniq U U₀ g g₀ hU hU₀ hI hI₀ hc hc₀ hQg hQ₀ 0 0 ⟨le_rfl, by norm_num⟩
  obtain ⟨e2, -⟩ := huniq U U₀ g g₀ hU hU₀ hI hI₀ hc hc₀ hQg hQ₀ 0 2 ⟨by norm_num, le_rfl⟩
  exact ⟨e0.trans h0, e2.trans h2⟩

end DGPS.Frontier.EX049
