import DGPS.Frontier.EX049.T38

/-!
# EX049.39: Glue the smooth correction derivative

Task id and title: EX049.39, "Glue the smooth correction derivative" (node EX049, frontier unit,
leaf formalization, prerequisites EX049.37 and EX049.38).  For a real `h ≥ 2` let
`A = 2 / (1 - e^{-2h})`, `N u = A (1 - e^{-hu}) - u`, and `Q u = N u / (u (2 - u))`.  The quotient
profile `Q` on `(0,2)` has a smooth extension to an open neighborhood of `[0,2]`, with the endpoint
values `(A h - 1)/2` at `0` and `(1 - A h e^{-2h})/2` at `2`.  Any two smooth extensions, each on an
open neighborhood of `[0,2]`, agree on `[0,2]` together with all their iterated derivatives there.

The extension is glued from the two local formulas of EX049.38: `(A h J_h(u) - 1)/(2 - u)` on
`u < 3/2`, and `(1 - A h e^{-2h} J_h(u - 2))/u` on `u > 1/2`, where `J_h(v) = ∫_0^1 e^{-h v τ} dτ`.
The two formulas agree with `Q` on `(1/2, 3/2)`, so they glue.

## Provides
* `DGPS.Frontier.EX049.ex049_39_glue_smooth_correction_derivative` : the main statement, for
  `2 ≤ h`. (i) There is `g` and an open `U ⊇ [0,2]` with `g` smooth on `U`, `g = Q` on `(0,2)`,
  `g 0 = (A h - 1)/2` and `g 2 = (1 - A h e^{-2h})/2`. (ii) For any two such extensions `g₁`, `g₂`
  on open neighborhoods `U₁`, `U₂` of `[0,2]`, `g₁ = g₂` and `iteratedDeriv k g₁ = iteratedDeriv k g₂`
  at every point of `[0,2]`, for every `k : ℕ`.
* `DGPS.Frontier.EX049.leftFormula_EX04939`, `rightFormula_EX04939` : helper definitions, the two
  local formulas as functions of `u`.
* `DGPS.Frontier.EX049.glued_EX04939` : helper definition, the glued profile
  `if u < 3/2 then leftFormula else rightFormula`.
* `DGPS.Frontier.EX049.glued_contDiffOn_EX04939` : helper; the glued profile is smooth on `ℝ`.
* `DGPS.Frontier.EX049.continuousOn_iteratedDeriv_EX04939` : helper; the `k`-th iterated derivative
  of a `C^∞` function on an open set is continuous there.

## R5 notes
* The only hypothesis of the main statement is `2 ≤ h`, the specification's "every `h ≥ 2`".  No
  hypothesis is added, and the statement is not weakened.
* `A_h`, `N_h` and `Q_h` are written as `let` bindings in the statement.  `J_h` is written inline
  as the oriented interval integral `∫ τ in (0:ℝ)..1, Real.exp (-(h * u * τ))`, as in EX049.37
  and EX049.38.  `e^{-2h}` is `Real.exp (-(2 * h))` and `e^{-hu}` is `Real.exp (-(h * u))`.
* "Smooth extension to a neighborhood of `[0,2]`" is read as: a function `g` with
  `ContDiffOn ℝ ∞ g U` for an open set `U` containing `Set.Icc 0 2`, where `∞` is the `ℕ∞`-top
  smoothness class.  Existence is proved with `U = Set.univ`, which is a stronger witness.
* "Endpoint values specified in .05" is read as `g 0 = (A h - 1)/2` and
  `g 2 = (1 - A h e^{-2h})/2`, as recorded for EX049.05.  They are the values of the left formula
  at `0` and of the right formula at `2`, where `J_h(0) = 1`.
* "Restriction and derivatives on `[0,2]` are independent of the chosen smooth extension" is read
  as: for any two extensions on any two open neighborhoods, the functions agree on `[0,2]`, and so
  do all their `iteratedDeriv k`.  The derivatives are the derivatives of the functions on `ℝ`, so
  at the endpoints they are the two-sided derivatives of the extension.
* Uniqueness is stated on the closed interval `[0,2]` only.  Nothing is claimed about two extensions
  outside `[0,2]`.  Independence on `[0,2]` is obtained from agreement on `(0,2)` by continuity of
  the derivatives up to the endpoints, not from any claim outside the interval.
* The quotient `Q` is evaluated only on `(0,2)` in the hypotheses.  The Lean division convention
  plays no role there, because `u ≠ 0` and `u ≠ 2` hold on `(0,2)`.  The formula identities of
  EX049.38 are used as they are.
* The denominators `2 - u` and `u` are nonzero on the open sets `u < 3/2` and `u > 1/2`, which is
  what the smoothness of the two local formulas uses.
-/

open scoped ContDiff

namespace DGPS.Frontier.EX049

/-- The left local formula `(A h J_h(u) - 1) / (2 - u)`, with `J_h(u) = ∫_0^1 e^{-h u τ} dτ`. -/
noncomputable def leftFormula_EX04939 (A h u : ℝ) : ℝ :=
  (A * h * (∫ τ in (0:ℝ)..1, Real.exp (-(h * u * τ))) - 1) / (2 - u)

/-- The right local formula `(1 - A h e^{-2h} J_h(u - 2)) / u`. -/
noncomputable def rightFormula_EX04939 (A h u : ℝ) : ℝ :=
  (1 - A * h * Real.exp (-(2 * h)) * (∫ τ in (0:ℝ)..1, Real.exp (-(h * (u - 2) * τ)))) / u

/-- The glued profile: the left formula for `u < 3/2`, the right formula for `3/2 ≤ u`. -/
noncomputable def glued_EX04939 (A h u : ℝ) : ℝ :=
  if u < 3 / 2 then leftFormula_EX04939 A h u else rightFormula_EX04939 A h u

lemma glued_of_lt_EX04939 (A h u : ℝ) (hu : u < 3 / 2) :
    glued_EX04939 A h u = leftFormula_EX04939 A h u := by
  simp [glued_EX04939, hu]

lemma glued_of_ge_EX04939 (A h u : ℝ) (hu : 3 / 2 ≤ u) :
    glued_EX04939 A h u = rightFormula_EX04939 A h u := by
  simp [glued_EX04939, not_lt.mpr hu]

/-- The smooth exponential average `u ↦ J_h(u)` is `C^∞` for `h > 0`, by EX049.37. -/
lemma J_contDiff_EX04939 {h : ℝ} (hh : 0 < h) :
    ContDiff ℝ ∞ (fun u : ℝ => ∫ τ in (0:ℝ)..1, Real.exp (-(h * u * τ))) :=
  (ex049_37_smooth_exponential_average h hh).1

/-- The shifted average `u ↦ J_h(u - 2)` is `C^∞` for `h > 0`. -/
lemma J_shift_contDiff_EX04939 {h : ℝ} (hh : 0 < h) :
    ContDiff ℝ ∞ (fun u : ℝ => ∫ τ in (0:ℝ)..1, Real.exp (-(h * (u - 2) * τ))) := by
  have hsub : ContDiff ℝ ∞ (fun u : ℝ => u - 2) := contDiff_id.sub contDiff_const
  exact (J_contDiff_EX04939 hh).comp hsub

/-- The left formula is `C^∞` on `u < 3/2`, where its denominator `2 - u` does not vanish. -/
lemma leftFormula_contDiffOn_EX04939 (A h : ℝ) (hh : 0 < h) :
    ContDiffOn ℝ ∞ (fun u : ℝ => leftFormula_EX04939 A h u) (Set.Iio (3 / 2 : ℝ)) := by
  have hnum : ContDiff ℝ ∞
      (fun u : ℝ => A * h * (∫ τ in (0:ℝ)..1, Real.exp (-(h * u * τ))) - 1) :=
    (contDiff_const.mul (J_contDiff_EX04939 hh)).sub contDiff_const
  have hden : ContDiff ℝ ∞ (fun u : ℝ => 2 - u) := contDiff_const.sub contDiff_id
  have hne : ∀ x ∈ Set.Iio (3 / 2 : ℝ), (fun u : ℝ => 2 - u) x ≠ 0 := by
    intro x hx
    have hx' : x < 3 / 2 := hx
    show 2 - x ≠ 0
    intro h0
    linarith
  unfold leftFormula_EX04939
  exact hnum.contDiffOn.div hden.contDiffOn hne

/-- The right formula is `C^∞` on `u > 1/2`, where its denominator `u` does not vanish. -/
lemma rightFormula_contDiffOn_EX04939 (A h : ℝ) (hh : 0 < h) :
    ContDiffOn ℝ ∞ (fun u : ℝ => rightFormula_EX04939 A h u) (Set.Ioi (1 / 2 : ℝ)) := by
  have hnum : ContDiff ℝ ∞ (fun u : ℝ =>
      1 - A * h * Real.exp (-(2 * h)) * (∫ τ in (0:ℝ)..1, Real.exp (-(h * (u - 2) * τ)))) :=
    contDiff_const.sub (contDiff_const.mul (J_shift_contDiff_EX04939 hh))
  have hden : ContDiff ℝ ∞ (fun u : ℝ => u) := contDiff_id
  have hne : ∀ x ∈ Set.Ioi (1 / 2 : ℝ), (fun u : ℝ => u) x ≠ 0 := by
    intro x hx
    have hx' : 1 / 2 < x := hx
    show x ≠ 0
    intro h0
    linarith
  unfold rightFormula_EX04939
  exact hnum.contDiffOn.div hden.contDiffOn hne

/-- The quotient `(A (1 - e^{-hu}) - u) / (u (2 - u))` equals the left formula for `u ≠ 0, 2`. -/
lemma quotient_eq_left_EX04939 (A h u : ℝ) (hu0 : u ≠ 0) (hu2 : u ≠ 2) :
    (A * (1 - Real.exp (-(h * u))) - u) / (u * (2 - u)) = leftFormula_EX04939 A h u := by
  have h2u : (2 - u) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu2)
  have hu2ne : u * (2 - u) ≠ 0 := mul_ne_zero hu0 h2u
  unfold leftFormula_EX04939
  rw [numerator_first_EX04938 A h u, div_eq_div_iff hu2ne h2u]
  ring

/-- The quotient `(A (1 - e^{-hu}) - u) / (u (2 - u))` equals the right formula for `u ≠ 0, 2`,
given `A (1 - e^{-2h}) = 2`. -/
lemma quotient_eq_right_EX04939 (A h u : ℝ) (hA : A * (1 - Real.exp (-(2 * h))) = 2)
    (hu0 : u ≠ 0) (hu2 : u ≠ 2) :
    (A * (1 - Real.exp (-(h * u))) - u) / (u * (2 - u)) = rightFormula_EX04939 A h u := by
  have h2u : (2 - u) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu2)
  have hu2ne : u * (2 - u) ≠ 0 := mul_ne_zero hu0 h2u
  unfold rightFormula_EX04939
  rw [numerator_second_EX04938 A h u hA, div_eq_div_iff hu2ne hu0]
  ring

/-- The two local formulas agree at every `u ∈ (0,2)`. -/
lemma left_eq_right_EX04939 (A h u : ℝ) (hA : A * (1 - Real.exp (-(2 * h))) = 2)
    (hu0 : u ≠ 0) (hu2 : u ≠ 2) :
    leftFormula_EX04939 A h u = rightFormula_EX04939 A h u :=
  (quotient_eq_left_EX04939 A h u hu0 hu2).symm.trans
    (quotient_eq_right_EX04939 A h u hA hu0 hu2)

/-- The glued profile equals the quotient on `(0,2)`. -/
lemma glued_eq_quotient_EX04939 (A h u : ℝ) (hA : A * (1 - Real.exp (-(2 * h))) = 2)
    (hu0 : 0 < u) (hu2 : u < 2) :
    glued_EX04939 A h u = (A * (1 - Real.exp (-(h * u))) - u) / (u * (2 - u)) := by
  have hne0 : u ≠ 0 := hu0.ne'
  have hne2 : u ≠ 2 := hu2.ne
  by_cases h3 : u < 3 / 2
  · rw [glued_of_lt_EX04939 A h u h3, quotient_eq_left_EX04939 A h u hne0 hne2]
  · rw [glued_of_ge_EX04939 A h u (not_lt.mp h3), quotient_eq_right_EX04939 A h u hA hne0 hne2]

/-- On `u > 1/2` the glued profile equals the right formula. -/
lemma glued_eq_right_EX04939 (A h : ℝ) (hA : A * (1 - Real.exp (-(2 * h))) = 2) {u : ℝ}
    (hu : 1 / 2 < u) : glued_EX04939 A h u = rightFormula_EX04939 A h u := by
  by_cases h3 : u < 3 / 2
  · rw [glued_of_lt_EX04939 A h u h3]
    exact left_eq_right_EX04939 A h u hA (show (0:ℝ) < u by linarith).ne'
      (show u < 2 by linarith).ne
  · exact glued_of_ge_EX04939 A h u (not_lt.mp h3)

/-- The glued profile is `C^∞` on `ℝ`: near each point it coincides on an open set with one of the
two local formulas, which are smooth there. -/
lemma glued_contDiffOn_EX04939 (A h : ℝ) (hA : A * (1 - Real.exp (-(2 * h))) = 2) (hh : 0 < h) :
    ContDiffOn ℝ ∞ (fun u : ℝ => glued_EX04939 A h u) Set.univ := by
  apply contDiffOn_of_locally_contDiffOn
  intro x _
  by_cases hx : x < 3 / 2
  · refine ⟨Set.Iio (3 / 2 : ℝ), isOpen_Iio, hx, ?_⟩
    refine ((leftFormula_contDiffOn_EX04939 A h hh).mono ?_).congr ?_
    · intro y hy
      exact hy.2
    · intro y hy
      exact glued_of_lt_EX04939 A h y (Set.mem_Iio.mp hy.2)
  · refine ⟨Set.Ioi (1 / 2 : ℝ), isOpen_Ioi, ?_, ?_⟩
    · have hx' : 3 / 2 ≤ x := not_lt.mp hx
      show (1 / 2 : ℝ) < x
      linarith
    refine ((rightFormula_contDiffOn_EX04939 A h hh).mono ?_).congr ?_
    · intro y hy
      exact hy.2
    · intro y hy
      exact glued_eq_right_EX04939 A h hA (Set.mem_Ioi.mp hy.2)

/-- For a function `C^∞` on an open set `U`, every iterated derivative is continuous on `U`. -/
lemma continuousOn_iteratedDeriv_EX04939 {U : Set ℝ} {g : ℝ → ℝ} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (k : ℕ) : ContinuousOn (iteratedDeriv k g) U := by
  have hk : (k : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have h1 := hg.continuousOn_iteratedDerivWithin hk hU.uniqueDiffOn
  exact h1.congr (iteratedDerivWithin_of_isOpen (n := k) hU).symm

/-- Glued smooth correction derivative.  For every real `h ≥ 2`, the quotient profile `Q` on
`(0,2)` has a smooth extension to an open neighborhood of `[0,2]` with endpoint values
`(A h - 1)/2` at `0` and `(1 - A h e^{-2h})/2` at `2`, and any two smooth extensions on open
neighborhoods of `[0,2]` agree on `[0,2]` together with all their iterated derivatives. -/
theorem ex049_39_glue_smooth_correction_derivative (h : ℝ) (hh : 2 ≤ h) :
    let A : ℝ := 2 / (1 - Real.exp (-(2 * h)))
    let N : ℝ → ℝ := fun u => A * (1 - Real.exp (-(h * u))) - u
    let Q : ℝ → ℝ := fun u => N u / (u * (2 - u))
    (∃ g : ℝ → ℝ, ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (0:ℝ) 2 ⊆ U ∧ ContDiffOn ℝ ∞ g U ∧
        (∀ u ∈ Set.Ioo (0:ℝ) 2, g u = Q u) ∧ g 0 = (A * h - 1) / 2 ∧
        g 2 = (1 - A * h * Real.exp (-(2 * h))) / 2) ∧
    (∀ (U₁ U₂ : Set ℝ) (g₁ g₂ : ℝ → ℝ), IsOpen U₁ → IsOpen U₂ →
        Set.Icc (0:ℝ) 2 ⊆ U₁ → Set.Icc (0:ℝ) 2 ⊆ U₂ →
        ContDiffOn ℝ ∞ g₁ U₁ → ContDiffOn ℝ ∞ g₂ U₂ →
        (∀ u ∈ Set.Ioo (0:ℝ) 2, g₁ u = Q u) → (∀ u ∈ Set.Ioo (0:ℝ) 2, g₂ u = Q u) →
        ∀ k : ℕ, ∀ u ∈ Set.Icc (0:ℝ) 2,
          g₁ u = g₂ u ∧ iteratedDeriv k g₁ u = iteratedDeriv k g₂ u) := by
  intro A N Q
  have hA : A * (1 - Real.exp (-(2 * h))) = 2 := A_mul_den_EX04938 hh
  have hQ : ∀ u, Q u = (A * (1 - Real.exp (-(h * u))) - u) / (u * (2 - u)) := fun u => rfl
  have hpos : 0 < h := by linarith
  refine ⟨⟨glued_EX04939 A h, Set.univ, isOpen_univ, Set.subset_univ _,
    glued_contDiffOn_EX04939 A h hA hpos, ?_, ?_, ?_⟩, ?_⟩
  · intro u hu
    rw [hQ u]
    exact glued_eq_quotient_EX04939 A h u hA hu.1 hu.2
  · rw [glued_of_lt_EX04939 A h 0 (by norm_num)]
    unfold leftFormula_EX04939
    simp
  · rw [glued_of_ge_EX04939 A h 2 (by norm_num)]
    unfold rightFormula_EX04939
    simp
  · intro U₁ U₂ g₁ g₂ hU₁ hU₂ hI₁ hI₂ hc₁ hc₂ hg₁ hg₂ k u hu
    have h02 : (0:ℝ) ≠ 2 := by norm_num
    have hcl : Set.Icc (0:ℝ) 2 ⊆ closure (Set.Ioo (0:ℝ) 2) :=
      subset_of_eq (closure_Ioo h02).symm
    have hE : Set.EqOn g₁ g₂ (Set.Ioo (0:ℝ) 2) :=
      fun x hx => (hg₁ x hx).trans (hg₂ x hx).symm
    have hEk : Set.EqOn (iteratedDeriv k g₁) (iteratedDeriv k g₂) (Set.Ioo (0:ℝ) 2) :=
      hE.iteratedDeriv_of_isOpen isOpen_Ioo k
    have hE' : Set.EqOn g₁ g₂ (Set.Icc (0:ℝ) 2) :=
      hE.of_subset_closure (hc₁.continuousOn.mono hI₁) (hc₂.continuousOn.mono hI₂)
        Set.Ioo_subset_Icc_self hcl
    have hEk' : Set.EqOn (iteratedDeriv k g₁) (iteratedDeriv k g₂) (Set.Icc (0:ℝ) 2) :=
      hEk.of_subset_closure ((continuousOn_iteratedDeriv_EX04939 hU₁ hc₁ k).mono hI₁)
        ((continuousOn_iteratedDeriv_EX04939 hU₂ hc₂ k).mono hI₂)
        Set.Ioo_subset_Icc_self hcl
    exact ⟨hE' hu, hEk' hu⟩

end DGPS.Frontier.EX049
