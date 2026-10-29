import DGRHS.Decoupling.Prop33FixedTupleSelectorExpansion
import DGRHS.Decoupling.FiniteCubeBanachMixedDegreeSmallBall

/-!
Records-only successor, not installed or compiled. Aggregate the nonempty
fixed-tuple selector-subset contributions by their final Boolean mask. The
empty subset is excluded: it is the degree-zero all-pattern constant from the
fixed-tuple expansion. A nonzero aggregate coefficient has a nonzero finite
summand, hence comes from an injective ordered tuple and a nonempty subset;
its Walsh degree is exactly that subset's cardinality in `[1,k]`. This is the
support hypothesis of the checked Banach mixed-degree small-ball theorem.
No source original-result theorem or full ordered heterogeneous Banach
statement is changed or asserted here.
-/

noncomputable section
open DGRHS.Decoupling.FiniteCube

namespace DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation

abbrev OrderedTuple (n k : ℕ) :=
  DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.OrderedTuple n k

private abbrev Triple (n k : ℕ) := OrderedTuple n k × (Cube k × Cube k)

private noncomputable def selectorSubsetTerm {n k : ℕ} {E : Type*}
    [AddCommMonoid E] [Module ℝ E]
    (ell : Cube k) (σ : Cube n)
    (F : OrderedTuple n k → Cube k → E)
    (t : OrderedTuple n k) (j a : Cube k) : E :=
  (DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.selectorSubsetWeight
      ell j a *
    cubeWalsh n
      (DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.selectorSubsetMask t a)
      σ) • F t j

/-- Sum all nonempty selector-subset terms with the same final Walsh mask. -/
noncomputable def aggregateCoefficient {n k : ℕ} {E : Type*}
    [AddCommMonoid E] [Module ℝ E]
    (ell : Cube k) (F : OrderedTuple n k → Cube k → E) (s : Cube n) : E := by
  classical
  exact ∑ z : Triple n k,
    if z.2.2 ≠ (fun _ => false) ∧
        DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.selectorSubsetMask
          z.1 z.2.2 = s then
      (DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.selectorSubsetWeight
        ell z.2.1 z.2.2) • F z.1 z.2.1
    else 0

/-- The coefficient map reconstructs exactly the aggregate of the
nonempty fixed-tuple Walsh terms. -/
theorem aggregateCoefficient_polynomial_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} (ell : Cube k) (F : OrderedTuple n k → Cube k → E) (σ : Cube n) :
    sourceBanachWalshPolynomial (aggregateCoefficient ell F) σ =
      ∑ z : Triple n k,
        if z.2.2 ≠ (fun _ => false) then
          selectorSubsetTerm ell σ F z.1 z.2.1 z.2.2
        else 0 := by
  classical
  unfold sourceBanachWalshPolynomial
  simp only [aggregateCoefficient]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases ha : z.2.2 ≠ (fun _ => false)
  · rw [Finset.sum_eq_single
      (DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.selectorSubsetMask
        z.1 z.2.2)]
    · simp [ha, selectorSubsetTerm, smul_smul, mul_comm]
    · intro s hs hne
      simp [ha, eq_comm, hne]
    · simp
  · simp [ha]

/-- Every nonzero aggregated coefficient is supported in degrees `1,…,k`. -/
theorem aggregateCoefficient_degree_bounds
    {n k : ℕ} {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (ell : Cube k) (F : OrderedTuple n k → Cube k → E) (s : Cube n)
    (hs : aggregateCoefficient ell F s ≠ 0) :
    1 ≤ cubeWalshDegree n s ∧ cubeWalshDegree n s ≤ k := by
  classical
  let P : OrderedTuple n k → Cube k → Cube n :=
    DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.selectorSubsetMask
  let W : Cube k → Cube k → Cube k → ℝ :=
    DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.selectorSubsetWeight
  have hwitness : ∃ z : Triple n k,
      z.2.2 ≠ (fun _ => false) ∧ P z.1 z.2.2 = s ∧
        W ell z.2.1 z.2.2 • F z.1 z.2.1 ≠ 0 := by
    by_contra hn
    have hterm : ∀ z : Triple n k,
        (if z.2.2 ≠ (fun _ => false) ∧ P z.1 z.2.2 = s then
          W ell z.2.1 z.2.2 • F z.1 z.2.1 else 0) = 0 := by
      intro z
      by_cases ha : z.2.2 ≠ (fun _ => false)
      · by_cases hm : P z.1 z.2.2 = s
        · have hzero : W ell z.2.1 z.2.2 • F z.1 z.2.1 = 0 := by
            by_contra hne
            exact hn ⟨z, ha, hm, hne⟩
          simp [ha, hm, hzero]
        · simp [ha, hm]
      · simp [ha]
    have hsum :
        (∑ z : Triple n k,
          if z.2.2 ≠ (fun _ => false) ∧ P z.1 z.2.2 = s then
            W ell z.2.1 z.2.2 • F z.1 z.2.1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      exact hterm z
    exact hs (by simpa [aggregateCoefficient, P, W] using hsum)
  obtain ⟨⟨t, j, a⟩, ha, hmask, hterm⟩ := hwitness
  have hbounds :=
    DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.selector_subset_degree_bounds
      t a ha
  change DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.selectorSubsetMask t a = s at hmask
  rw [← hmask]
  exact hbounds

/-- The sum over all ordered tuples has constant term `sum_{t,j} F t j`
and nonconstant term equal to the aggregated Walsh polynomial. The factor
`2^k` is kept on the source selector sum. -/
theorem summed_fixed_tuple_selector_identity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} (ell : Cube k) (F : OrderedTuple n k → Cube k → E)
    (σ : Cube n) :
    (2 : ℝ)^k •
      (∑ t : OrderedTuple n k,
        F t (fun q =>
          DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.selectedLabel
            σ ell t q)) =
      (∑ t : OrderedTuple n k, ∑ j : Cube k, F t j) +
        sourceBanachWalshPolynomial (aggregateCoefficient ell F) σ := by
  classical
  let a₀ : Cube k := fun _ => false
  have hzero_sum (t : OrderedTuple n k) (j : Cube k) :
      (∑ a : Cube k,
        if a = a₀ then selectorSubsetTerm ell σ F t j a₀ else 0) =
        selectorSubsetTerm ell σ F t j a₀ := by
    rw [Finset.sum_eq_single a₀]
    · simp
    · intro a ha hne
      simp [eq_comm, hne]
    · simp
  have hsplit_a (t : OrderedTuple n k) (j : Cube k) :
      (∑ a : Cube k, selectorSubsetTerm ell σ F t j a) =
        selectorSubsetTerm ell σ F t j a₀ +
          (∑ a : Cube k,
            if a ≠ a₀ then selectorSubsetTerm ell σ F t j a else 0) := by
    have hpoint (a : Cube k) :
        selectorSubsetTerm ell σ F t j a =
          (if a = a₀ then selectorSubsetTerm ell σ F t j a₀ else 0) +
            (if a ≠ a₀ then selectorSubsetTerm ell σ F t j a else 0) := by
      by_cases ha : a = a₀ <;> simp [ha]
    calc
      _ = ∑ a : Cube k,
          ((if a = a₀ then selectorSubsetTerm ell σ F t j a₀ else 0) +
            (if a ≠ a₀ then selectorSubsetTerm ell σ F t j a else 0)) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hpoint a
      _ = (∑ a : Cube k,
            if a = a₀ then selectorSubsetTerm ell σ F t j a₀ else 0) +
          ∑ a : Cube k,
            if a ≠ a₀ then selectorSubsetTerm ell σ F t j a else 0 :=
          Finset.sum_add_distrib
      _ = _ := by rw [hzero_sum]
  have hempty (t : OrderedTuple n k) :
      (∑ j : Cube k, selectorSubsetTerm ell σ F t j a₀) =
        ∑ j : Cube k, F t j := by
    simpa [a₀, selectorSubsetTerm] using
      (DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.empty_subset_is_all_pattern_constant
        σ ell t (F t))
  have hsplit_j (t : OrderedTuple n k) :
      (∑ j : Cube k, ∑ a : Cube k,
        selectorSubsetTerm ell σ F t j a) =
        (∑ j : Cube k, F t j) +
          ∑ j : Cube k, ∑ a : Cube k,
            if a ≠ a₀ then selectorSubsetTerm ell σ F t j a else 0 := by
    calc
      _ = ∑ j : Cube k,
          (selectorSubsetTerm ell σ F t j a₀ +
            ∑ a : Cube k,
              if a ≠ a₀ then selectorSubsetTerm ell σ F t j a else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hsplit_a t j
      _ = (∑ j : Cube k, selectorSubsetTerm ell σ F t j a₀) +
          ∑ j : Cube k, ∑ a : Cube k,
            if a ≠ a₀ then selectorSubsetTerm ell σ F t j a else 0 :=
          Finset.sum_add_distrib
      _ = _ := by rw [hempty]
  have hfull :
      (2 : ℝ)^k •
        (∑ t : OrderedTuple n k,
          F t (fun q =>
            DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.selectedLabel
              σ ell t q)) =
        ∑ t : OrderedTuple n k, ∑ j : Cube k, ∑ a : Cube k,
          selectorSubsetTerm ell σ F t j a := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    simpa [selectorSubsetTerm] using
      (DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.fixed_tuple_all_pattern_walsh_expansion
        σ ell t (F t))
  calc
    _ = ∑ t : OrderedTuple n k, ∑ j : Cube k, ∑ a : Cube k,
        selectorSubsetTerm ell σ F t j a := hfull
    _ = ∑ t : OrderedTuple n k,
        ((∑ j : Cube k, F t j) +
          ∑ j : Cube k, ∑ a : Cube k,
            if a ≠ a₀ then selectorSubsetTerm ell σ F t j a else 0) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hsplit_j t
    _ = (∑ t : OrderedTuple n k, ∑ j : Cube k, F t j) +
        ∑ t : OrderedTuple n k, ∑ j : Cube k, ∑ a : Cube k,
          if a ≠ a₀ then selectorSubsetTerm ell σ F t j a else 0 :=
      Finset.sum_add_distrib
    _ = (∑ t : OrderedTuple n k, ∑ j : Cube k, F t j) +
        sourceBanachWalshPolynomial (aggregateCoefficient ell F) σ := by
      congr 1
      have hinner (t : OrderedTuple n k) :
          (∑ j : Cube k, ∑ a : Cube k,
            if a ≠ a₀ then selectorSubsetTerm ell σ F t j a else 0) =
          ∑ p : Cube k × Cube k,
            if p.2 ≠ a₀ then selectorSubsetTerm ell σ F t p.1 p.2 else 0 := by
        rw [Fintype.sum_prod_type]
      calc
        _ = ∑ t : OrderedTuple n k, ∑ p : Cube k × Cube k,
              if p.2 ≠ a₀ then selectorSubsetTerm ell σ F t p.1 p.2 else 0 := by
          apply Finset.sum_congr rfl
          intro t ht
          exact hinner t
        _ = ∑ z : Triple n k,
              if z.2.2 ≠ a₀ then selectorSubsetTerm ell σ F z.1 z.2.1 z.2.2 else 0 := by
          rw [Fintype.sum_prod_type]
        _ = sourceBanachWalshPolynomial (aggregateCoefficient ell F) σ := by
          simpa [a₀] using (aggregateCoefficient_polynomial_eq ell F σ).symm

/-- The source scaling is strictly positive for every order `k`. -/
theorem selector_scaling_pos (k : ℕ) : 0 < (2 : ℝ)^k := by
  positivity

/-- The checked translated Banach small-ball estimate applies to the
aggregated nonconstant selector polynomial, with no symmetry assumption on
`F` or on ordered-tuple coefficients. -/
theorem aggregate_translated_cube_norm_event
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} (hk : 0 < k) (ell : Cube k) (F : OrderedTuple n k → Cube k → E) (x : E) :
    cubeAvg (fun ω =>
      if ‖x + sourceBanachWalshPolynomial (aggregateCoefficient ell F) ω‖
          ≥ ‖x‖ then (1 : ℝ) else 0)
      ≥ 1 / (4 * sourceMixedDegreeWeight k) := by
  exact translated_cube_norm_event_of_mixed_walsh_coefficients hk
    (aggregateCoefficient ell F) x
    (fun s hs => aggregateCoefficient_degree_bounds ell F s hs)

#print DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.aggregateCoefficient_polynomial_eq
#print DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.summed_fixed_tuple_selector_identity
#print DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.selector_scaling_pos
#print DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.aggregateCoefficient_degree_bounds
#print DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.aggregate_translated_cube_norm_event
#print axioms DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.aggregateCoefficient_polynomial_eq
#print axioms DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.summed_fixed_tuple_selector_identity
#print axioms DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.selector_scaling_pos
#print axioms DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.aggregateCoefficient_degree_bounds
#print axioms DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation.aggregate_translated_cube_norm_event

end DGRHS.Decoupling.Prop33.OrderedTupleMaskCoefficientAggregation
