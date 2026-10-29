import DGPS.Frontier.LIP032.T43
import DGPS.Frontier.LIP032.T46

/-!
# LIP032.47: No contraction by a real intermediate value argument

Task id and title: LIP032.47, "No contraction by a real intermediate value argument" (node LIP032,
contractibility of the minimizer set; leaf formalization on the explicit counterexample model
`A_*`; the statement contains no positive-rate or flow hypothesis and none is used).

## Provides
* `DGPS.Frontier.LIP032.lip032_47_no_contraction_real_intermediate_value_argument_separation`: the
  positive-moment subset `{ν ∈ S_* | 0 < M(ν)}` and the negative-moment subset
  `{ν ∈ S_* | M(ν) < 0}` of the minimizing set `S_*` (`minimizerSetStar_LIP03244`) are nonempty,
  disjoint, clopen in `S_*`, and cover `S_*`. Here `M = momentStar_LIP03241`.
* `DGPS.Frontier.LIP032.lip032_47_no_contraction_real_intermediate_value_argument_no_homotopy`: for
  every `μ_* ∈ S_*` there is no continuous map `H_* : S_* × [0,1] → S_*` with `H_*(ν, 0) = ν` and
  `H_*(ν, 1) = μ_*` for every `ν ∈ S_*`.
* `DGPS.Frontier.LIP032.lip032_47_no_contraction_real_intermediate_value_argument`: MAIN. The
  conjunction of the separation statement and the no-homotopy statement, in the same form.

The auxiliary declarations all carry the suffix `_LIP03247` and are not listed here.

## R5 notes
* Model. `A_* = interactionDataStar_LIP03241` on `𝕋¹ = Torus 1`, with `γ(x) = cos(2πx)`,
  `V_* = -4γ²` and `W_*(x, y) = 4(γ x - γ y)²`. The statement concerns this explicit model only, as
  the specification's counterexample task does. It is not the general contractibility claim.
* No hypothesis. The LIP031 header (`hr`, `hrate`, `hu`) is not referenced, and no positive-rate,
  flow, mean-field or interaction-gradient hypothesis is added. The conditional branch of the node
  is not needed, because the statement is refuted for `A_*` itself.
* Minimizing set. `S_*` is `minimizerSetStar_LIP03244`, the probability measures `ν` with
  `freeEnergy A_* ν = freeEnergyMinimum A_*`, with the subspace topology of the weak topology on
  `ProbabilityMeasure (Torus 1)`. Nonemptiness and the nonzero moment of minimizers are inherited
  from LIP032.43 (LIP017 conjunct 1 and the finiteness of the minimum). The reversal of the moment
  under translation is inherited from LIP032.46.
* Moment. `M(ν) = ∫ γ dν` is `momentStar_LIP03241` applied to the underlying measure of `ν`. It is
  weakly continuous, being the integral of a bounded continuous test function.
* Positive and negative subsets. Read as `{ν ∈ S_* | 0 < M(ν)}` and `{ν ∈ S_* | M(ν) < 0}`, both
  subsets of the subtype `↥minimizerSetStar_LIP03244`. "Clopen" is Mathlib's `IsClopen` in that
  subtype, and "covering" is the equality of their union with `Set.univ`.
* Interval. `[0,1]` is Mathlib's `unitInterval`, with its subspace topology from `ℝ`. The domain
  `S_* × [0,1]` carries the product topology. "Continuous map into `S_*`" means continuous into the
  subtype.
* Endpoint identities. Read as equalities in the subtype `S_*`: `H(ν, 0) = ν` and `H(ν, 1) = μ_*`
  for every `ν ∈ S_*`, which is the quantifier of the frozen node text.
* Starting point. The proof evaluates the homotopy at `T_# μ_*`, where `T(x) = x + 1/2` is the
  translation of LIP032.46. It lies in `S_*` by that task, so no new hypothesis is needed.
* Intermediate value. The real argument uses Mathlib's `intermediate_value_univ₂` on the connected
  space `unitInterval`, applied in both orders of the endpoint signs. This is the fact of LIB15.
* Conclusion. The no-homotopy statement is the literal negation of the existence of such a
  continuous `H_*`, quantified over every `μ_* ∈ S_*`.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

/-- The cosine moment `M(ν) = ∫ γ dν` of a point `ν` of the minimizing set `S_*`. -/
noncomputable def momentS_LIP03247 (ν : ↥minimizerSetStar_LIP03244) : ℝ :=
  momentStar_LIP03241 ((ν : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))

/-- The positive-moment subset `{ν ∈ S_* | 0 < M(ν)}`. -/
noncomputable def posSet_LIP03247 : Set ↥minimizerSetStar_LIP03244 :=
  {ν | 0 < momentS_LIP03247 ν}

/-- The negative-moment subset `{ν ∈ S_* | M(ν) < 0}`. -/
noncomputable def negSet_LIP03247 : Set ↥minimizerSetStar_LIP03244 :=
  {ν | momentS_LIP03247 ν < 0}

/-! ### Continuity of the moment -/

/-- The cosine moment is weakly continuous on the probability measures on `𝕋¹`. -/
theorem continuous_moment_prob_LIP03247 :
    Continuous fun ν : ProbabilityMeasure (Torus 1) =>
      momentStar_LIP03241 (ν : Measure (Torus 1)) := by
  have h := ProbabilityMeasure.continuous_integral_boundedContinuousFunction (X := Torus 1)
    (BoundedContinuousFunction.mkOfCompact ⟨gammaStar_LIP03241, continuous_gammaStar_LIP03241⟩)
  simpa [momentStar_LIP03241] using h

/-- The moment, as a function on the minimizing set `S_*`, is continuous. -/
theorem continuous_momentS_LIP03247 : Continuous momentS_LIP03247 :=
  continuous_moment_prob_LIP03247.comp continuous_subtype_val

/-! ### The minimizing set: nonzero moment, existence, translation -/

/-- Every point of `S_*` has nonzero cosine moment (LIP032.43). -/
theorem moment_ne_zero_S_LIP03247 (ν : ↥minimizerSetStar_LIP03244) :
    momentS_LIP03247 ν ≠ 0 :=
  (lip032_43_strict_negative_minimum_nonzero_cosine_moments.2.2
    (ν : ProbabilityMeasure (Torus 1)) ν.2).2

/-- The minimizing set `S_*` is nonempty (LIP032.43). -/
theorem exists_minimizer_LIP03247 :
    ∃ ν : ProbabilityMeasure (Torus 1), ν ∈ minimizerSetStar_LIP03244 := by
  obtain ⟨ν, hν⟩ := lip032_43_strict_negative_minimum_nonzero_cosine_moments.1
  exact ⟨ν, hν⟩

/-- The translate `T_# μ_*` of a point of `S_*`, regarded as a point of `S_*` (LIP032.46). -/
noncomputable def startPoint_LIP03247 (μ : ↥minimizerSetStar_LIP03244) :
    ↥minimizerSetStar_LIP03244 :=
  ⟨(μ : ProbabilityMeasure (Torus 1)).map halfShift_LIP03246,
    (lip032_46_half_period_translation_preserves_energy_reverses
      (μ : ProbabilityMeasure (Torus 1)) μ.2).1⟩

/-- The translate of a point of `S_*` has the opposite cosine moment (LIP032.46). -/
theorem momentS_startPoint_LIP03247 (μ : ↥minimizerSetStar_LIP03244) :
    momentS_LIP03247 (startPoint_LIP03247 μ) = -momentS_LIP03247 μ :=
  (lip032_46_half_period_translation_preserves_energy_reverses
    (μ : ProbabilityMeasure (Torus 1)) μ.2).2

/-- Both moment signs occur on `S_*`: a minimizer and its translate have opposite moments. -/
theorem exists_pos_and_neg_LIP03247 :
    (∃ p : ↥minimizerSetStar_LIP03244, 0 < momentS_LIP03247 p) ∧
      ∃ n : ↥minimizerSetStar_LIP03244, momentS_LIP03247 n < 0 := by
  obtain ⟨ν0, hν0⟩ := exists_minimizer_LIP03247
  have hne : momentStar_LIP03241 (ν0 : Measure (Torus 1)) ≠ 0 :=
    (lip032_43_strict_negative_minimum_nonzero_cosine_moments.2.2 ν0 hν0).2
  have hT := lip032_46_half_period_translation_preserves_energy_reverses ν0 hν0
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨⟨⟨ν0.map halfShift_LIP03246, hT.1⟩, ?_⟩, ⟨⟨ν0, hν0⟩, hlt⟩⟩
    show 0 < momentStar_LIP03241
      ((ν0.map halfShift_LIP03246 : ProbabilityMeasure (Torus 1)) : Measure (Torus 1))
    linarith [hT.2]
  · refine ⟨⟨⟨ν0, hν0⟩, hgt⟩, ⟨⟨ν0.map halfShift_LIP03246, hT.1⟩, ?_⟩⟩
    show momentStar_LIP03241
      ((ν0.map halfShift_LIP03246 : ProbabilityMeasure (Torus 1)) : Measure (Torus 1)) < 0
    linarith [hT.2]

/-! ### Separation of `S_*` into clopen pieces -/

/-- The positive-moment subset is open in `S_*`. -/
theorem isOpen_posSet_LIP03247 : IsOpen posSet_LIP03247 :=
  (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).preimage continuous_momentS_LIP03247

/-- The negative-moment subset is open in `S_*`. -/
theorem isOpen_negSet_LIP03247 : IsOpen negSet_LIP03247 :=
  (isOpen_Iio : IsOpen (Set.Iio (0 : ℝ))).preimage continuous_momentS_LIP03247

/-- The positive-moment subset is the complement of the negative-moment subset in `S_*`. -/
theorem posSet_eq_compl_LIP03247 : posSet_LIP03247 = negSet_LIP03247ᶜ := by
  ext ν
  rw [Set.mem_compl_iff]
  change 0 < momentS_LIP03247 ν ↔ ¬ momentS_LIP03247 ν < 0
  constructor
  · intro h hn
    exact lt_asymm h hn
  · intro hn
    exact lt_of_le_of_ne (not_lt.1 hn) (Ne.symm (moment_ne_zero_S_LIP03247 ν))

/-- The negative-moment subset is the complement of the positive-moment subset in `S_*`. -/
theorem negSet_eq_compl_LIP03247 : negSet_LIP03247 = posSet_LIP03247ᶜ := by
  ext ν
  rw [Set.mem_compl_iff]
  change momentS_LIP03247 ν < 0 ↔ ¬ 0 < momentS_LIP03247 ν
  constructor
  · intro h hp
    exact lt_asymm hp h
  · intro hp
    exact lt_of_le_of_ne (not_lt.1 hp) (moment_ne_zero_S_LIP03247 ν)

/-- The positive-moment subset is closed in `S_*`. -/
theorem isClosed_posSet_LIP03247 : IsClosed posSet_LIP03247 := by
  rw [posSet_eq_compl_LIP03247]
  exact isClosed_compl_iff.2 isOpen_negSet_LIP03247

/-- The negative-moment subset is closed in `S_*`. -/
theorem isClosed_negSet_LIP03247 : IsClosed negSet_LIP03247 := by
  rw [negSet_eq_compl_LIP03247]
  exact isClosed_compl_iff.2 isOpen_posSet_LIP03247

/-- The positive-moment subset is clopen in `S_*`. -/
theorem isClopen_posSet_LIP03247 : IsClopen posSet_LIP03247 :=
  ⟨isClosed_posSet_LIP03247, isOpen_posSet_LIP03247⟩

/-- The negative-moment subset is clopen in `S_*`. -/
theorem isClopen_negSet_LIP03247 : IsClopen negSet_LIP03247 :=
  ⟨isClosed_negSet_LIP03247, isOpen_negSet_LIP03247⟩

/-- The positive- and negative-moment subsets of `S_*` are disjoint. -/
theorem disjoint_posSet_negSet_LIP03247 : Disjoint posSet_LIP03247 negSet_LIP03247 := by
  rw [Set.disjoint_left]
  intro ν h1 h2
  have hp : 0 < momentS_LIP03247 ν := h1
  have hn : momentS_LIP03247 ν < 0 := h2
  exact lt_asymm hp hn

/-- The positive- and negative-moment subsets cover `S_*`, since no minimizer has zero moment. -/
theorem posSet_union_negSet_LIP03247 : posSet_LIP03247 ∪ negSet_LIP03247 = Set.univ := by
  refine Set.eq_univ_of_forall fun ν => ?_
  rcases lt_or_gt_of_ne (moment_ne_zero_S_LIP03247 ν) with h | h
  · exact Set.mem_union_right _ (show ν ∈ negSet_LIP03247 from h)
  · exact Set.mem_union_left _ (show ν ∈ posSet_LIP03247 from h)

/-! ### The real intermediate value step -/

/-- A continuous real function on `[0,1]` whose endpoint values have opposite weak signs has a
zero. -/
theorem exists_zero_LIP03247 (f : unitInterval → ℝ) (hf : Continuous f)
    (h : (f 0 ≤ 0 ∧ 0 ≤ f 1) ∨ (f 1 ≤ 0 ∧ 0 ≤ f 0)) : ∃ s : unitInterval, f s = 0 := by
  rcases h with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · obtain ⟨s, hs⟩ :=
      intermediate_value_univ₂ (f := f) (g := fun _ => (0 : ℝ)) hf continuous_const h0 h1
    exact ⟨s, hs⟩
  · obtain ⟨s, hs⟩ :=
      intermediate_value_univ₂ (f := f) (g := fun _ => (0 : ℝ)) hf continuous_const h1 h0
    exact ⟨s, hs⟩

/-! ### Public statements -/

/-- **LIP032.47, separation.** The positive- and negative-moment subsets of `S_*` are nonempty,
disjoint, clopen in `S_*`, and cover `S_*`. -/
theorem lip032_47_no_contraction_real_intermediate_value_argument_separation :
    posSet_LIP03247.Nonempty ∧ negSet_LIP03247.Nonempty ∧
      Disjoint posSet_LIP03247 negSet_LIP03247 ∧
      IsClopen posSet_LIP03247 ∧ IsClopen negSet_LIP03247 ∧
      posSet_LIP03247 ∪ negSet_LIP03247 = Set.univ := by
  obtain ⟨⟨p, hp⟩, ⟨n, hn⟩⟩ := exists_pos_and_neg_LIP03247
  exact ⟨⟨p, hp⟩, ⟨n, hn⟩, disjoint_posSet_negSet_LIP03247, isClopen_posSet_LIP03247,
    isClopen_negSet_LIP03247, posSet_union_negSet_LIP03247⟩

/-- **LIP032.47, no homotopy.** For every `μ_* ∈ S_*` there is no continuous `H_* : S_* × [0,1] →
S_*` with `H_*(ν, 0) = ν` and `H_*(ν, 1) = μ_*` for every `ν ∈ S_*`. -/
theorem lip032_47_no_contraction_real_intermediate_value_argument_no_homotopy
    (μ : ↥minimizerSetStar_LIP03244) :
    ¬ ∃ H : ↥minimizerSetStar_LIP03244 × unitInterval → ↥minimizerSetStar_LIP03244,
      Continuous H ∧ (∀ ν : ↥minimizerSetStar_LIP03244, H (ν, 0) = ν) ∧
        ∀ ν : ↥minimizerSetStar_LIP03244, H (ν, 1) = μ := by
  rintro ⟨H, hH, h0, h1⟩
  have hpair : Continuous fun s : unitInterval =>
      ((startPoint_LIP03247 μ, s) : ↥minimizerSetStar_LIP03244 × unitInterval) :=
    continuous_const.prodMk continuous_id
  have hf : Continuous fun s : unitInterval =>
      momentS_LIP03247 (H (startPoint_LIP03247 μ, s)) :=
    continuous_momentS_LIP03247.comp (hH.comp hpair)
  have hA : momentS_LIP03247 (H (startPoint_LIP03247 μ, 0)) = -momentS_LIP03247 μ := by
    rw [h0 (startPoint_LIP03247 μ)]
    exact momentS_startPoint_LIP03247 μ
  have hB : momentS_LIP03247 (H (startPoint_LIP03247 μ, 1)) = momentS_LIP03247 μ := by
    rw [h1 (startPoint_LIP03247 μ)]
  rcases lt_or_gt_of_ne (moment_ne_zero_S_LIP03247 μ) with hneg | hpos
  · have h1' : momentS_LIP03247 (H (startPoint_LIP03247 μ, 1)) ≤ 0 := by linarith
    have h0' : 0 ≤ momentS_LIP03247 (H (startPoint_LIP03247 μ, 0)) := by linarith
    obtain ⟨s, hs⟩ := exists_zero_LIP03247 _ hf (Or.inr ⟨h1', h0'⟩)
    exact moment_ne_zero_S_LIP03247 (H (startPoint_LIP03247 μ, s)) hs
  · have h0' : momentS_LIP03247 (H (startPoint_LIP03247 μ, 0)) ≤ 0 := by linarith
    have h1' : 0 ≤ momentS_LIP03247 (H (startPoint_LIP03247 μ, 1)) := by linarith
    obtain ⟨s, hs⟩ := exists_zero_LIP03247 _ hf (Or.inl ⟨h0', h1'⟩)
    exact moment_ne_zero_S_LIP03247 (H (startPoint_LIP03247 μ, s)) hs

/-- **LIP032.47.** No contraction by a real intermediate value argument: the positive- and
negative-moment subsets of `S_*` form a clopen separation of `S_*`, and for every `μ_* ∈ S_*` there
is no continuous `H_* : S_* × [0,1] → S_*` with `H_*(ν, 0) = ν` and `H_*(ν, 1) = μ_*`. -/
theorem lip032_47_no_contraction_real_intermediate_value_argument :
    (posSet_LIP03247.Nonempty ∧ negSet_LIP03247.Nonempty ∧
      Disjoint posSet_LIP03247 negSet_LIP03247 ∧
      IsClopen posSet_LIP03247 ∧ IsClopen negSet_LIP03247 ∧
      posSet_LIP03247 ∪ negSet_LIP03247 = Set.univ) ∧
    ∀ μ : ↥minimizerSetStar_LIP03244,
      ¬ ∃ H : ↥minimizerSetStar_LIP03244 × unitInterval → ↥minimizerSetStar_LIP03244,
        Continuous H ∧ (∀ ν : ↥minimizerSetStar_LIP03244, H (ν, 0) = ν) ∧
          ∀ ν : ↥minimizerSetStar_LIP03244, H (ν, 1) = μ :=
  ⟨lip032_47_no_contraction_real_intermediate_value_argument_separation,
    lip032_47_no_contraction_real_intermediate_value_argument_no_homotopy⟩

end DGPS.Frontier.LIP032
