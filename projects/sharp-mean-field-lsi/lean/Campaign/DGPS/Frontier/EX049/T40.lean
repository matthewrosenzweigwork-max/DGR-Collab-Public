import DGPS.Frontier.EX049.T39

/-!
# EX049.40: Primitive of the smooth profile

Task id and title: EX049.40, "Primitive of the smooth profile" (node EX049, frontier unit,
leaf formalization, prerequisite EX049.39).  For a real `h ≥ 2`, let `A = 2 / (1 - e^{-2h})`,
`N u = A (1 - e^{-hu}) - u` and `Q u = N u / (u (2 - u))`, as in EX049.39.  For a smooth
extension `g` of `Q` from `(0,2)` to an open neighborhood `U` of `[0,2]`, the primitive
`R u = ∫_0^u g(s) ds` is smooth on an open neighborhood of `[0,2]`, satisfies `R 0 = 0` and
`R' = g` there, and its restriction to `[0,2]` does not depend on the extension.

## Provides
* `DGPS.Frontier.EX049.ex049_40_primitive_smooth_profile` : the main statement, for `2 ≤ h`.
  Three conjuncts: (i) a smooth extension of `Q` as in EX049.39 exists; (ii) for every smooth
  extension `g` of `Q` on an open `U ⊇ [0,2]`, there is an open `W ⊇ [0,2]` on which
  `R u = ∫_0^u g` is `C^∞`, with `R 0 = 0` and `HasDerivAt R (g u) u` for `u ∈ W`; (iii) for any two
  smooth extensions `g₁`, `g₂` of `Q`, their primitives agree at every point of `[0,2]`.
* `DGPS.Frontier.EX049.primitive_hasDerivAt_EX04940` : helper; fundamental theorem of calculus for
  the primitive of a function continuous on an open set, at a point whose interval to `0` lies in it.
* `DGPS.Frontier.EX049.enlarged_subset_EX04940` : helper; a compact interval inside an open set
  has a symmetric enlargement `[-δ, 2+δ]` inside it, for some `δ > 0`.
* `DGPS.Frontier.EX049.primitive_hasDerivAt_Ioo_EX04940` : helper; the derivative of the primitive
  at each point of the open interval `(-δ, 2+δ)`.
* `DGPS.Frontier.EX049.primitive_contDiffOn_EX04940` : helper; the primitive is `C^∞` on
  `(-δ, 2+δ)`.
* `DGPS.Frontier.EX049.eqOn_Icc_EX04940` : helper; two functions continuous on neighborhoods of
  `[0,2]` that agree on `(0,2)` agree on `[0,2]`.

## R5 notes
* The only hypothesis of the main statement is `2 ≤ h`, the specification's "every `h ≥ 2`".  No
  hypothesis is added beyond the smooth-extension hypotheses of EX049.39, and nothing is weakened.
* The specification's `r_h` is the smooth extension of EX049.39.  Here it is a generic function `g`
  with `ContDiffOn ℝ ∞ g U` on an open `U ⊇ [0,2]` and `g = Q` on `(0,2)`, the reading of "smooth
  extension to a neighborhood of `[0,2]`" fixed in EX049.39.  Conjunct (i) supplies one such
  extension, so conjuncts (ii) and (iii) are not vacuous.
* `R u = ∫_0^u g(s) ds` is the oriented interval integral `∫ s in (0:ℝ)..u, g s`.  For `u < 0`
  this is `-∫_u^0 g`.  Outside `[0,2]` the values of `R` depend on `g`, and nothing about them is
  claimed beyond the smoothness of `R` and `R' = g` on the neighborhood `W`.
* "Smooth on a neighborhood of `[0,2]`": the neighborhood `W` is the explicit open interval
  `(-δ, 2+δ)`, where `δ > 0` comes from compactness so that `[-δ, 2+δ] ⊆ U`.  `W` is not `U`.  An
  open `U` need not be connected, and the primitive over `[0,u]` for `u` in a different component
  of `U` would integrate `g` on points outside `U`, where `g` is unconstrained.  Choosing `W` inside
  `U` avoids this, and `W` depends on `g` through `U` only.
* "`R' = r_h`": read as `HasDerivAt R (g u) u` at every `u ∈ W`, a two-sided derivative at each
  point of the open set `W`.  This includes all points of `[0,2]`.  No derivative claim is made
  off `W`.
* "Its restriction to `[0,2]` is independent of the extension": read as equality of the values
  `R₁ u = R₂ u` for `u ∈ [0,2]`, where `R₁`, `R₂` are the primitives of two extensions on open
  neighborhoods `U₁`, `U₂`.  Independence of the derivatives on `[0,2]` is not restated here.  It
  is the content of EX049.39 and is not needed for the primitive.
* The integrals over `[0,u]` with `u ∈ [0,2]` use only the restriction of the integrands to
  `[0,2]`.  Their equality is obtained from agreement on `(0,2)` by continuity on `[0,2]`, which is
  the same closure argument as in EX049.39.  No claim is made about two extensions outside `[0,2]`.
* `R 0 = 0` is the integral over the degenerate interval `[0,0]`.
* The binding of `R` to the campaign `corr h` is not proved here.  It is the open task EX049.25,
  as stated in the specification.
* The smoothness class `∞` is the `ℕ∞`-valued top written `∞` under `open scoped ContDiff`, as in
  EX049.39.
-/

open scoped ContDiff

namespace DGPS.Frontier.EX049

/-- A compact interval `[0,2]` inside an open set `U` has a symmetric enlargement
`[-δ, 2+δ]` inside `U`, for some `δ > 0`. -/
lemma enlarged_subset_EX04940 {U : Set ℝ} (hU : IsOpen U) (hI : Set.Icc (0:ℝ) 2 ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ Set.Icc (-δ) (2 + δ) ⊆ U := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 2)).exists_thickening_subset_open
    hU hI
  refine ⟨δ / 2, half_pos hδ, fun x hx => hsub ?_⟩
  rw [Metric.mem_thickening_iff]
  obtain ⟨hx1, hx2⟩ := hx
  rcases le_total x 0 with h0 | h0
  · refine ⟨0, ⟨le_rfl, by norm_num⟩, ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  · rcases le_total x 2 with h2 | h2
    · refine ⟨x, ⟨h0, h2⟩, ?_⟩
      rw [dist_self]
      exact hδ
    · refine ⟨2, ⟨by norm_num, le_rfl⟩, ?_⟩
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith

/-- Fundamental theorem of calculus for the primitive `x ↦ ∫_0^x g` of a function `g` that is
continuous on an open set `U`, at a point `u ∈ U` whose interval `[0,u]` lies in `U`. -/
lemma primitive_hasDerivAt_EX04940 {U : Set ℝ} {g : ℝ → ℝ} (hU : IsOpen U)
    (hg : ContinuousOn g U) {u : ℝ} (hu : u ∈ U) (hI : Set.uIcc (0:ℝ) u ⊆ U) :
    HasDerivAt (fun x : ℝ => ∫ s in (0:ℝ)..x, g s) (g u) u :=
  intervalIntegral.integral_hasDerivAt_right (hg.mono hI).intervalIntegrable
    (hg.stronglyMeasurableAtFilter hU u hu) (hg.continuousAt (hU.mem_nhds hu))

/-- On the open interval `(-δ, 2+δ)`, the primitive of `g` has derivative `g` at every point. -/
lemma primitive_hasDerivAt_Ioo_EX04940 {U : Set ℝ} {g : ℝ → ℝ} (hU : IsOpen U)
    (hc : ContinuousOn g U) {δ : ℝ} (hδpos : 0 < δ) (hδU : Set.Icc (-δ) (2 + δ) ⊆ U)
    {x : ℝ} (hx : x ∈ Set.Ioo (-δ) (2 + δ)) :
    HasDerivAt (fun y : ℝ => ∫ s in (0:ℝ)..y, g s) (g x) x := by
  have h0mem : (0:ℝ) ∈ Set.Icc (-δ) (2 + δ) := ⟨by linarith, by linarith⟩
  have hxmem : x ∈ Set.Icc (-δ) (2 + δ) := ⟨hx.1.le, hx.2.le⟩
  have hI : Set.uIcc (0:ℝ) x ⊆ U := fun y hy => hδU (Set.uIcc_subset_Icc h0mem hxmem hy)
  exact primitive_hasDerivAt_EX04940 hU hc (hδU hxmem) hI

/-- On the open interval `(-δ, 2+δ)`, the primitive of a smooth `g` is `C^∞`. -/
lemma primitive_contDiffOn_EX04940 {U : Set ℝ} {g : ℝ → ℝ} (hU : IsOpen U)
    (hc : ContDiffOn ℝ ∞ g U) {δ : ℝ} (hδpos : 0 < δ) (hδU : Set.Icc (-δ) (2 + δ) ⊆ U) :
    ContDiffOn ℝ ∞ (fun x : ℝ => ∫ s in (0:ℝ)..x, g s) (Set.Ioo (-δ) (2 + δ)) := by
  have hW : IsOpen (Set.Ioo (-δ) (2 + δ)) := isOpen_Ioo
  have hWU : Set.Ioo (-δ) (2 + δ) ⊆ U := fun x hx => by
    have hxIcc : x ∈ Set.Icc (-δ) (2 + δ) := ⟨hx.1.le, hx.2.le⟩
    exact hδU hxIcc
  have hderiv : ∀ x ∈ Set.Ioo (-δ) (2 + δ),
      HasDerivAt (fun y : ℝ => ∫ s in (0:ℝ)..y, g s) (g x) x :=
    fun x hx => primitive_hasDerivAt_Ioo_EX04940 hU hc.continuousOn hδpos hδU hx
  have hdiff : DifferentiableOn ℝ (fun y : ℝ => ∫ s in (0:ℝ)..y, g s)
      (Set.Ioo (-δ) (2 + δ)) :=
    fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt
  have hder_eq : ∀ x ∈ Set.Ioo (-δ) (2 + δ),
      derivWithin (fun y : ℝ => ∫ s in (0:ℝ)..y, g s) (Set.Ioo (-δ) (2 + δ)) x = g x := by
    intro x hx
    rw [derivWithin_of_isOpen hW hx]
    exact (hderiv x hx).deriv
  rw [contDiffOn_infty_iff_derivWithin hW.uniqueDiffOn]
  exact ⟨hdiff, ((hc.mono hWU).congr hder_eq)⟩

/-- Two functions, each continuous on an open neighborhood of `[0,2]`, that agree on `(0,2)`
agree on `[0,2]`. -/
lemma eqOn_Icc_EX04940 {U₁ U₂ : Set ℝ} {g₁ g₂ : ℝ → ℝ} (hI₁ : Set.Icc (0:ℝ) 2 ⊆ U₁)
    (hI₂ : Set.Icc (0:ℝ) 2 ⊆ U₂) (hc₁ : ContDiffOn ℝ ∞ g₁ U₁) (hc₂ : ContDiffOn ℝ ∞ g₂ U₂)
    (hE : ∀ u ∈ Set.Ioo (0:ℝ) 2, g₁ u = g₂ u) : Set.EqOn g₁ g₂ (Set.Icc (0:ℝ) 2) := by
  have h02 : (0:ℝ) ≠ 2 := by norm_num
  have hcl : Set.Icc (0:ℝ) 2 ⊆ closure (Set.Ioo (0:ℝ) 2) :=
    subset_of_eq (closure_Ioo h02).symm
  have hE' : Set.EqOn g₁ g₂ (Set.Ioo (0:ℝ) 2) := fun x hx => hE x hx
  exact hE'.of_subset_closure (hc₁.continuousOn.mono hI₁) (hc₂.continuousOn.mono hI₂)
    Set.Ioo_subset_Icc_self hcl

/-- Primitive of the smooth profile.  For every real `h ≥ 2`, with `A`, `N` and `Q` as in
EX049.39: (i) a smooth extension of `Q` exists; (ii) every smooth extension `g` of `Q` on an open
neighborhood of `[0,2]` has a primitive `u ↦ ∫_0^u g` that is `C^∞` on an open neighborhood of
`[0,2]`, vanishes at `0`, and has derivative `g` there; (iii) two smooth extensions of `Q` have
primitives that agree at every point of `[0,2]`. -/
theorem ex049_40_primitive_smooth_profile (h : ℝ) (hh : 2 ≤ h) :
    let A : ℝ := 2 / (1 - Real.exp (-(2 * h)))
    let N : ℝ → ℝ := fun u => A * (1 - Real.exp (-(h * u))) - u
    let Q : ℝ → ℝ := fun u => N u / (u * (2 - u))
    (∃ g : ℝ → ℝ, ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (0:ℝ) 2 ⊆ U ∧ ContDiffOn ℝ ∞ g U ∧
        ∀ u ∈ Set.Ioo (0:ℝ) 2, g u = Q u) ∧
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
  have hpos : 0 < h := by linarith
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨⟨g, U, hU, hI, hc, hQ, -, -⟩, -⟩ := ex049_39_glue_smooth_correction_derivative h hh
    exact ⟨g, U, hU, hI, hc, hQ⟩
  · intro g U hU hI hc _
    obtain ⟨δ, hδpos, hδU⟩ := enlarged_subset_EX04940 hU hI
    have hsub : Set.Icc (0:ℝ) 2 ⊆ Set.Ioo (-δ) (2 + δ) := fun x hx =>
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact ⟨Set.Ioo (-δ) (2 + δ), isOpen_Ioo, hsub,
      primitive_contDiffOn_EX04940 hU hc hδpos hδU, intervalIntegral.integral_same,
      fun x hx => primitive_hasDerivAt_Ioo_EX04940 hU hc.continuousOn hδpos hδU hx⟩
  · intro U₁ U₂ g₁ g₂ _ _ hI₁ hI₂ hc₁ hc₂ hg₁ hg₂ u hu
    have hE : ∀ x ∈ Set.Ioo (0:ℝ) 2, g₁ x = g₂ x := fun x hx => (hg₁ x hx).trans (hg₂ x hx).symm
    have hEq := eqOn_Icc_EX04940 hI₁ hI₂ hc₁ hc₂ hE
    have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) 2 := ⟨le_rfl, by norm_num⟩
    exact intervalIntegral.integral_congr (fun y hy => hEq (Set.uIcc_subset_Icc h0mem hu hy))

end DGPS.Frontier.EX049
