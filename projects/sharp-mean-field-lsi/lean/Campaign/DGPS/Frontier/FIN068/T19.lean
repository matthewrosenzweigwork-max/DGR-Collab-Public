import DGPS.Frontier.FIN068.T04

/-!
Task id and title: FIN068.19, Fixed compact convex domain and derivative bound (module
`DGPS.Frontier.FIN068.T19`).

Provides:
* `DGPS.Frontier.FIN068.fixedRect_FIN06819`: the closed rectangle `{p : ℝ × ℝ | |p.1| ≤ δ ∧ |p.2| ≤ δ}`
  (helper definition, not a claim), with `p.1 = u` and `p.2 = z`.
* `DGPS.Frontier.FIN068.fixedRect_eq_prod_FIN06819`: the rectangle is `Icc (-δ) δ ×ˢ Icc (-δ) δ`.
* `DGPS.Frontier.FIN068.isCompact_fixedRect_FIN06819`: the rectangle is compact.
* `DGPS.Frontier.FIN068.bound_third_FIN06819`: for `J` of class `C^∞` on an open set `U` and a
  compact `K ⊆ U`, some `M ≥ 0` bounds `|D³J(x)[h,v,w]| ≤ M ‖h‖₁ ‖v‖₁ ‖w‖₁` on `K`, where
  `‖(u,z)‖₁ = |u| + |z|` and `D³J(x)` is `iteratedFDeriv ℝ 3 J x`.
* `DGPS.Frontier.FIN068.segment_fixedRect_FIN06819`: for every `δ`, each segment from `0` to a point
  of the rectangle lies in the rectangle.
* `DGPS.Frontier.FIN068.fin068_19_fixed_compact_convex_domain_derivative_bound_each_delta`: for every
  `δ ∈ (0,1)`, the rectangle lies in the smooth patch `(-1,1) × (-1,1)`, every segment from zero to a
  point of it stays in it, and some `M₃ ≥ 0` bounds the third derivative of the lifted potential
  `liftPotential_FIN06804` on the rectangle in the `ℓ¹` form above.
* `DGPS.Frontier.FIN068.fin068_19_fixed_compact_convex_domain_derivative_bound`: there exist
  `δ ∈ (0,1)` with the same three properties (`δ = 1/2` is used).

Proof: the rectangle is a product of closed intervals, hence compact, and lies in the open patch
because `δ < 1`. Segments from zero are `t p` with `t ∈ [0,1]`, and `|t p_i| ≤ |p_i| ≤ δ`. The
third derivative of `liftPotential_FIN06804` is continuous on the open patch (FIN068.04), so its
operator norm is bounded on the compact rectangle. Coordinatewise `ℓ∞ ≤ ℓ¹` gives the `ℓ¹` form.

R5 notes:
* Hypotheses: none are added. The smooth patch is the open rectangle `Set.Ioo (-1) 1 ×ˢ
  Set.Ioo (-1) 1` on which FIN068.04 proves `ContDiffOn ℝ ∞` for the lifted potential. The
  specification's "lies in the smooth patch" is read as containment in this open set.
* The main declaration is the literal existential: "choose `δ ∈ (0,1)`" is `∃ δ`, and "choose
  `M₃ ≥ 0`" is `∃ M₃` after `δ`. The `_each_delta` declaration proves the stronger reading for every
  `δ ∈ (0,1)`. Its hypothesis `0 < δ` is kept from the specification and is not used in the proof,
  so it is named `_hδ0`.
* "Every segment from zero to a point of `B` stays in `B`" is read as `segment ℝ (0 : ℝ × ℝ) p ⊆ B`
  for `p ∈ B`, with `segment` the Mathlib convex segment in `ℝ × ℝ`. Convexity is proved
  coordinatewise, so no normed-space instance is needed.
* The third derivative is Mathlib's Fréchet `iteratedFDeriv ℝ 3 J x` applied to `![h, v, w]`, the
  multilinear map of `J : ℝ × ℝ → ℝ`. It is not a separate partial derivative in `u` and `z`.
* The norm is the `ℓ¹` form, written explicitly as `|h.1| + |h.2|` and not as a Mathlib norm, so the
  bound is `|D³J(x)[h,v,w]| ≤ M₃ (|h.1|+|h.2|)(|v.1|+|v.2|)(|w.1|+|w.2|)`. The proof uses the
  operator norm for the sup norm `‖·‖` on `ℝ × ℝ` and `‖h‖ ≤ |h.1|+|h.2|`. The Euclidean operator
  alternative in the specification is not used.
* `M₃` is only shown to exist (`max C 0`, with `C` from compactness). It is not computed.
* The variable `z` is signed. Nothing requires `z ≥ 0`, and the rectangle is symmetric in both
  coordinates.
* The lifted potential is `liftPotential_FIN06804 q.1 q.2` on `ℝ × ℝ`, as in FIN068.04, so the
  derivative bound is about that function on the compact rectangle.
-/

open MeasureTheory Real
open scoped ContDiff

namespace DGPS.Frontier.FIN068

/-- The closed rectangle `{|u| ≤ δ, |z| ≤ δ}` in `ℝ × ℝ`, with `u = p.1` and `z = p.2`. -/
def fixedRect_FIN06819 (δ : ℝ) : Set (ℝ × ℝ) :=
  {p | |p.1| ≤ δ ∧ |p.2| ≤ δ}

lemma fixedRect_eq_prod_FIN06819 (δ : ℝ) :
    fixedRect_FIN06819 δ = Set.Icc (-δ) δ ×ˢ Set.Icc (-δ) δ := by
  ext p
  simp only [fixedRect_FIN06819, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Icc, abs_le]

lemma isCompact_fixedRect_FIN06819 (δ : ℝ) : IsCompact (fixedRect_FIN06819 δ) := by
  rw [fixedRect_eq_prod_FIN06819]
  exact isCompact_Icc.prod isCompact_Icc

/-- A `C^∞` function on an open set has a bounded third derivative on a compact subset, in the
`ℓ¹` form `|D³J(x)[h,v,w]| ≤ M ‖h‖₁ ‖v‖₁ ‖w‖₁`. -/
lemma bound_third_FIN06819 {J : ℝ × ℝ → ℝ} {U K : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hJ : ContDiffOn ℝ ∞ J U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, ∀ h v w : ℝ × ℝ,
      |iteratedFDeriv ℝ 3 J x ![h, v, w]| ≤
        M * (|h.1| + |h.2|) * (|v.1| + |v.2|) * (|w.1| + |w.2|) := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ 3 J) K := by
    have h1 : ContinuousOn (iteratedFDerivWithin ℝ 3 J U) U :=
      hJ.continuousOn_iteratedFDerivWithin (m := 3) (by simp) hU.uniqueDiffOn
    have h2 : ContinuousOn (iteratedFDeriv ℝ 3 J) U :=
      h1.congr fun x hx => (iteratedFDerivWithin_of_isOpen 3 hU hx).symm
    exact h2.mono hKU
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun x hx h v w => ?_⟩
  have hnorm : ∀ p : ℝ × ℝ, ‖p‖ ≤ |p.1| + |p.2| := by
    intro p
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · rw [Real.norm_eq_abs]
      linarith [abs_nonneg p.2]
    · rw [Real.norm_eq_abs]
      linarith [abs_nonneg p.1]
  have hop := (iteratedFDeriv ℝ 3 J x).le_opNorm ![h, v, w]
  have hCx : ‖iteratedFDeriv ℝ 3 J x‖ ≤ max C 0 := (hC x hx).trans (le_max_left _ _)
  have hprod : ∏ i : Fin 3, ‖(![h, v, w] : Fin 3 → ℝ × ℝ) i‖ = ‖h‖ * ‖v‖ * ‖w‖ := by
    simp [Fin.prod_univ_three]
  rw [hprod] at hop
  have hA : ‖h‖ ≤ |h.1| + |h.2| := hnorm h
  have hB : ‖v‖ ≤ |v.1| + |v.2| := hnorm v
  have hC' : ‖w‖ ≤ |w.1| + |w.2| := hnorm w
  calc |iteratedFDeriv ℝ 3 J x ![h, v, w]|
      = ‖iteratedFDeriv ℝ 3 J x ![h, v, w]‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖iteratedFDeriv ℝ 3 J x‖ * (‖h‖ * ‖v‖ * ‖w‖) := hop
    _ ≤ max C 0 * ((|h.1| + |h.2|) * (|v.1| + |v.2|) * (|w.1| + |w.2|)) := by
        refine mul_le_mul hCx ?_ (by positivity) (le_max_right _ _)
        exact mul_le_mul (mul_le_mul hA hB (norm_nonneg _) (by positivity))
          hC' (norm_nonneg _) (by positivity)
    _ = max C 0 * (|h.1| + |h.2|) * (|v.1| + |v.2|) * (|w.1| + |w.2|) := by ring

/-- Every segment from `0` to a point of the rectangle `{|u| ≤ δ, |z| ≤ δ}` stays in it. -/
lemma segment_fixedRect_FIN06819 (δ : ℝ) :
    ∀ p ∈ fixedRect_FIN06819 δ, segment ℝ (0 : ℝ × ℝ) p ⊆ fixedRect_FIN06819 δ := by
  intro p hp z hz
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  obtain ⟨hp1, hp2⟩ := hp
  have hb1 : b ≤ 1 := by linarith
  have key : ∀ q : ℝ, |q| ≤ δ → |b * q| ≤ δ := by
    intro q hq
    rw [abs_mul, abs_of_nonneg hb]
    nlinarith [mul_nonneg (sub_nonneg.2 hb1) (abs_nonneg q), abs_nonneg q]
  simp only [fixedRect_FIN06819, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, Prod.fst_zero, Prod.snd_zero, smul_eq_mul, mul_zero,
    zero_add]
  exact ⟨key _ hp1, key _ hp2⟩

/-- For every `δ ∈ (0,1)`: the closed rectangle lies in the smooth patch, segments from zero stay in
it, and the third derivative of the lifted potential is bounded there in the `ℓ¹` form. -/
theorem fin068_19_fixed_compact_convex_domain_derivative_bound_each_delta
    (δ : ℝ) (_hδ0 : 0 < δ) (hδ1 : δ < 1) :
    fixedRect_FIN06819 δ ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1 ∧
      (∀ p ∈ fixedRect_FIN06819 δ, segment ℝ (0 : ℝ × ℝ) p ⊆ fixedRect_FIN06819 δ) ∧
      ∃ M₃ : ℝ, 0 ≤ M₃ ∧ ∀ x ∈ fixedRect_FIN06819 δ, ∀ h v w : ℝ × ℝ,
        |iteratedFDeriv ℝ 3 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2) x ![h, v, w]| ≤
          M₃ * (|h.1| + |h.2|) * (|v.1| + |v.2|) * (|w.1| + |w.2|) := by
  have hsub : fixedRect_FIN06819 δ ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1 := by
    rintro p ⟨hp1, hp2⟩
    exact ⟨abs_lt.mp (lt_of_le_of_lt hp1 hδ1), abs_lt.mp (lt_of_le_of_lt hp2 hδ1)⟩
  refine ⟨hsub, segment_fixedRect_FIN06819 δ, ?_⟩
  obtain ⟨hJ, -⟩ := fin068_04_lift_two_ordinary_variables
  exact bound_third_FIN06819 (isOpen_Ioo.prod isOpen_Ioo) hJ
    (isCompact_fixedRect_FIN06819 δ) hsub

/-- Fixed compact convex domain and derivative bound: there is `δ ∈ (0,1)` such that the closed
rectangle `{|u| ≤ δ, |z| ≤ δ}` lies in the smooth patch, every segment from zero to a point of it
stays in it, and some `M₃ ≥ 0` bounds the third derivative of the lifted potential there. -/
theorem fin068_19_fixed_compact_convex_domain_derivative_bound :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      fixedRect_FIN06819 δ ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1 ∧
      (∀ p ∈ fixedRect_FIN06819 δ, segment ℝ (0 : ℝ × ℝ) p ⊆ fixedRect_FIN06819 δ) ∧
      ∃ M₃ : ℝ, 0 ≤ M₃ ∧ ∀ x ∈ fixedRect_FIN06819 δ, ∀ h v w : ℝ × ℝ,
        |iteratedFDeriv ℝ 3 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2) x ![h, v, w]| ≤
          M₃ * (|h.1| + |h.2|) * (|v.1| + |v.2|) * (|w.1| + |w.2|) :=
  ⟨1 / 2, by norm_num, by norm_num,
    fin068_19_fixed_compact_convex_domain_derivative_bound_each_delta (1 / 2)
      (by norm_num) (by norm_num)⟩

end DGPS.Frontier.FIN068
