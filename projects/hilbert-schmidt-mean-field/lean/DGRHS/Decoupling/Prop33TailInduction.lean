import DGRHS.Decoupling.Prop33MixedPatternBridge

/-!
All-order tail induction for Proposition 3.3 (de la Peña–Montgomery-Smith, Theorem 1).

For every order `k ≥ 1` there is a constant `C_k ≥ 1`, depending only on `k`, such that
for independent (not necessarily identically distributed) coordinates, all ordered
tuple-dependent measurable kernels with values in a real normed space, and all `t > 0`,

  `P(‖∑ f_{i₁…i_k}(ξ_{i₁},…,ξ_{i_k})‖ ≥ t) ≤ C_k P(C_k ‖∑ f_{i₁…i_k}(ξ^{(1)}_{i₁},…,ξ^{(k)}_{i_k})‖ ≥ t)`.

The induction follows the primary proof: three-copy symmetrization, the all-pattern
swap-invariant aggregate with the shifted finite-cube small-ball estimate, and the
conditional order-`p`/order-`q` decoupling of every mixed copy pattern.
-/

noncomputable section
open MeasureTheory DGRHS.Decoupling.FiniteCube DGRHS.Decoupling.Heterogeneous
open scoped BigOperators ENNReal

namespace DGRHS.Decoupling.Prop33

open DGRHS.Decoupling.Prop33.CopySwap DGRHS.Decoupling.Prop33.SelectorTonelliBridge

/-- The canonical `Fintype` instance on ordered injective tuples. -/
abbrev canonFintype (n k : ℕ) : Fintype (OrderedTuple n k) := inferInstance

lemma measurable_pairArrays {S : Type*} [MeasurableSpace S] {ι : Type*} [Fintype ι] :
    Measurable (pairArrays (S := S) (ι := ι)) := by
  refine measurable_pi_iff.mpr ?_
  intro i
  exact ((measurable_pi_apply i).comp measurable_fst).prodMk
    ((measurable_pi_apply i).comp measurable_snd)

section Step
variable {S E : Type*} [MeasurableSpace S] [MeasurableSpace E] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [OpensMeasurableSpace E] [MeasurableAdd₂ E]

/-- The inductive step: lower-order uniform tail bounds with common constant `H ≥ 1`
give the order-`k` bound with an explicit constant. -/
theorem sourceUniformTail_step (k : ℕ) (hk : 2 ≤ k) (H : ℝ) (hH : 1 ≤ H)
    (hLow : ∀ r, 0 < r → r < k → sourceUniformTailAtOrder (S := S) (E := E) r H) :
    sourceUniformTailAtOrder (S := S) (E := E) k
      (3 * (H * H) * (4 * sourceMixedDegreeWeight k + ((mixedPatterns k).card : ℝ)
        + 2 ^ k)) := by
  classical
  intro n marginal hm hrn hF K hK t ht
  have hFeq : hF = canonFintype n k := Subsingleton.elim _ _
  subst hFeq
  have hk0 : 0 < k := by omega
  set A := sourceMixedDegreeWeight k with hA
  have hApos : 0 < A := sourceMixedDegreeWeight_pos hk0
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  set M : ℕ := (mixedPatterns k).card with hM
  have hMpos : 0 < M := Finset.card_pos.mpr (mixedPatterns_nonempty hk)
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hMpos
  set C : ℝ := 3 * (H * H) * (4 * A + (M : ℝ) + 2 ^ k) with hC
  set μ : Measure (Fin n → S) := sourceArrayLaw marginal with hμ
  haveI : IsProbabilityMeasure μ := by
    simp only [hμ, sourceArrayLaw]; infer_instance
  set ρ := sourceCopiesLaw (r := k) marginal with hρ
  set R : ℝ≥0∞ := ρ {z | t ≤ C * ‖sourceOrderDecoupledStatistic K z‖} with hR
  have hU := measurable_sourceOrderStatistic K hK
  -- pattern statistics on pairs of arrays
  have hDm : ∀ j, Measurable (fun xy : (Fin n → S) × (Fin n → S) =>
      sourceCopyPatternStatistic K (pairArrays xy) j) := fun j =>
    (measurable_sourceCopyPatternStatistic K hK j).comp
      measurable_pairArrays
  have hTm : Measurable (fun xy : (Fin n → S) × (Fin n → S) =>
      sourceAllPatternStatistic K (pairArrays xy)) :=
    (measurable_sourceAllPatternStatistic K hK).comp
      measurable_pairArrays
  -- Step 1: three-copy symmetrization
  have h1 := threeCopy_tail μ (sourceOrderStatistic K) hU t
  -- Step 2: deterministic inclusion
  have h2 : {xy : (Fin n → S) × (Fin n → S) |
        2 * t / 3 ≤ ‖sourceOrderStatistic K xy.1 + sourceOrderStatistic K xy.2‖} ⊆
      {xy | t / 3 ≤ ‖sourceAllPatternStatistic K (pairArrays xy)‖} ∪
        ⋃ j ∈ mixedPatterns k,
          {xy | t / (3 * M) ≤ ‖sourceCopyPatternStatistic K (pairArrays xy) j‖} := by
    intro xy hxy
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_exists,
      not_le] at hnot hxy
    obtain ⟨hT, hmix⟩ := hnot
    have hsum : ∑ j ∈ mixedPatterns k, ‖sourceCopyPatternStatistic K (pairArrays xy) j‖ <
        ∑ j ∈ mixedPatterns k, t / (3 * M) :=
      Finset.sum_lt_sum_of_nonempty (mixedPatterns_nonempty hk)
        (fun j hj => hmix j hj)
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have hMt : (M : ℝ) * (t / (3 * M)) = t / 3 := by field_simp
    have hbound := norm_constPatterns_le hk0 K (pairArrays xy)
    rw [copyPattern_allTrue, copyPattern_allFalse] at hbound
    linarith
  -- Step 3: small ball
  set T : ℝ := 2 ^ k with hTdef
  have hTpos : (0 : ℝ) < 2 ^ k := by positivity
  obtain ⟨ℓ, hℓ⟩ := mixedPatterns_nonempty hk
  have h3 : (μ.prod μ) {xy : (Fin n → S) × (Fin n → S) |
        t / 3 ≤ ‖sourceAllPatternStatistic K (pairArrays xy)‖} ≤
      ENNReal.ofReal (4 * A) * (μ.prod μ) {xy |
        t / (3 * 2 ^ k) ≤ ‖sourceCopyPatternStatistic K (pairArrays xy) ℓ‖} := by
    have hSA : MeasurableSet {z : Fin n → S × S |
        t / 3 ≤ ‖sourceAllPatternStatistic K z‖} :=
      measurableSet_le measurable_const (measurable_sourceAllPatternStatistic K hK).norm
    have hSB : MeasurableSet {z : Fin n → S × S |
        t / 3 ≤ ‖(2 : ℝ) ^ k • sourceCopyPatternStatistic K z ℓ‖} :=
      measurableSet_le measurable_const (by
        have : (fun z : Fin n → S × S => ‖(2 : ℝ) ^ k • sourceCopyPatternStatistic K z ℓ‖) =
            fun z => ‖(2 : ℝ) ^ k‖ * ‖sourceCopyPatternStatistic K z ℓ‖ := by
          funext z; exact norm_smul _ _
        rw [this]
        exact (measurable_sourceCopyPatternStatistic K hK ℓ).norm.const_mul _)
    have hpa := pairArrays_measurePreserving marginal
    have eA := hpa.measure_preimage hSA.nullMeasurableSet
    have eB := hpa.measure_preimage hSB.nullMeasurableSet
    have hbridge := allPattern_tail_le_copyPattern_tail hk0 marginal K hK ℓ (t / 3)
    have hset : {xy : (Fin n → S) × (Fin n → S) |
          t / (3 * 2 ^ k) ≤ ‖sourceCopyPatternStatistic K (pairArrays xy) ℓ‖} =
        pairArrays ⁻¹' {z : Fin n → S × S |
          t / 3 ≤ ‖(2 : ℝ) ^ k • sourceCopyPatternStatistic K z ℓ‖} := by
      ext xy
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, norm_smul, norm_pow, Real.norm_ofNat]
      rw [div_le_iff₀ (by positivity)]
      constructor <;> intro h <;> nlinarith [norm_nonneg (sourceCopyPatternStatistic K (pairArrays xy) ℓ)]
    rw [hset]
    calc (μ.prod μ) {xy : (Fin n → S) × (Fin n → S) |
          t / 3 ≤ ‖sourceAllPatternStatistic K (pairArrays xy)‖}
        = (μ.prod μ) (pairArrays ⁻¹' {z : Fin n → S × S |
            t / 3 ≤ ‖sourceAllPatternStatistic K z‖}) := rfl
      _ = heterogeneousPairSamples marginal {z : Fin n → S × S |
            t / 3 ≤ ‖sourceAllPatternStatistic K z‖} := eA
      _ ≤ ENNReal.ofReal (4 * A) * heterogeneousPairSamples marginal
            {z : Fin n → S × S |
              t / 3 ≤ ‖(2 : ℝ) ^ k • sourceCopyPatternStatistic K z ℓ‖} := hbridge
      _ = ENNReal.ofReal (4 * A) * (μ.prod μ) (pairArrays ⁻¹' {z : Fin n → S × S |
            t / 3 ≤ ‖(2 : ℝ) ^ k • sourceCopyPatternStatistic K z ℓ‖}) :=
        congrArg (fun x => ENNReal.ofReal (4 * A) * x) eB.symm
  -- Step 4: mixed patterns
  have h4 : ∀ j ∈ mixedPatterns k, ∀ b : ℝ, 0 < b →
      (μ.prod μ) {xy : (Fin n → S) × (Fin n → S) |
          b ≤ ‖sourceCopyPatternStatistic K (pairArrays xy) j‖} ≤
        ENNReal.ofReal (H * H) *
          ρ {z | b ≤ H * H * ‖sourceOrderDecoupledStatistic K z‖} := by
    intro j hj b hb
    exact mixedPattern_tail_bound hk hrn marginal K hK H hH hLow j hj b hb
  -- inclusion of the rescaled events into the target event
  have hincl : ∀ m : ℝ, 0 < m → 3 * m * (H * H) ≤ C →
      ρ {z | t / (3 * m) ≤ H * H * ‖sourceOrderDecoupledStatistic K z‖} ≤ R := by
    intro m hm hmC
    apply measure_mono
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    have hV := norm_nonneg (sourceOrderDecoupledStatistic K z)
    rw [div_le_iff₀ (by positivity)] at hz
    nlinarith [mul_le_mul_of_nonneg_right hmC hV]
  have hCM : 3 * (M : ℝ) * (H * H) ≤ C := by
    rw [hC]; nlinarith [mul_pos hH0 hH0, pow_pos (two_pos (α := ℝ)) k]
  have hC2 : 3 * (2 ^ k : ℝ) * (H * H) ≤ C := by
    rw [hC]; nlinarith [mul_pos hH0 hH0, pow_pos (two_pos (α := ℝ)) k]
  have hPT : (μ.prod μ) {xy : (Fin n → S) × (Fin n → S) |
        t / 3 ≤ ‖sourceAllPatternStatistic K (pairArrays xy)‖} ≤
      ENNReal.ofReal (4 * A) * (ENNReal.ofReal (H * H) * R) := by
    refine h3.trans ?_
    gcongr
    exact (h4 ℓ hℓ _ (by positivity)).trans (by
      gcongr
      exact hincl (2 ^ k) (by positivity) hC2)
  have hPj : ∀ j ∈ mixedPatterns k, (μ.prod μ) {xy : (Fin n → S) × (Fin n → S) |
        t / (3 * M) ≤ ‖sourceCopyPatternStatistic K (pairArrays xy) j‖} ≤
      ENNReal.ofReal (H * H) * R := by
    intro j hj
    refine (h4 j hj _ (by positivity)).trans ?_
    gcongr
    exact hincl M hMreal hCM
  have hUnion : (μ.prod μ) {xy : (Fin n → S) × (Fin n → S) |
        2 * t / 3 ≤ ‖sourceOrderStatistic K xy.1 + sourceOrderStatistic K xy.2‖} ≤
      ENNReal.ofReal (4 * A) * (ENNReal.ofReal (H * H) * R) +
        (M : ℝ≥0∞) * (ENNReal.ofReal (H * H) * R) := by
    refine (measure_mono h2).trans ?_
    refine (measure_union_le _ _).trans (add_le_add hPT ?_)
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ j ∈ mixedPatterns k, (μ.prod μ) {xy : (Fin n → S) × (Fin n → S) |
          t / (3 * M) ≤ ‖sourceCopyPatternStatistic K (pairArrays xy) j‖}
        ≤ ∑ j ∈ mixedPatterns k, ENNReal.ofReal (H * H) * R :=
          Finset.sum_le_sum hPj
      _ = (M : ℝ≥0∞) * (ENNReal.ofReal (H * H) * R) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hfinal : 3 * (ENNReal.ofReal (4 * A) * (ENNReal.ofReal (H * H) * R) +
        (M : ℝ≥0∞) * (ENNReal.ofReal (H * H) * R)) ≤ ENNReal.ofReal C * R := by
    have hC' : 3 * (H * H) * (4 * A + (M : ℝ)) ≤ C := by
      rw [hC]; nlinarith [mul_pos hH0 hH0, pow_pos (two_pos (α := ℝ)) k]
    calc 3 * (ENNReal.ofReal (4 * A) * (ENNReal.ofReal (H * H) * R) +
          (M : ℝ≥0∞) * (ENNReal.ofReal (H * H) * R))
        = ENNReal.ofReal (3 * (H * H) * (4 * A + (M : ℝ))) * R := by
          have e : ENNReal.ofReal (3 * (H * H) * (4 * A + (M : ℝ))) =
              3 * (ENNReal.ofReal (4 * A) * ENNReal.ofReal (H * H) +
                (M : ℝ≥0∞) * ENNReal.ofReal (H * H)) := by
            have hm1 : ENNReal.ofReal (4 * A * (H * H)) =
                ENNReal.ofReal (4 * A) * ENNReal.ofReal (H * H) :=
              ENNReal.ofReal_mul (by positivity)
            have hm2 : ENNReal.ofReal ((M : ℝ) * (H * H)) =
                (M : ℝ≥0∞) * ENNReal.ofReal (H * H) := by
              rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
            have hm3 : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal (3 * x) = 3 * ENNReal.ofReal x := by
              intro x hx
              rw [ENNReal.ofReal_mul (by norm_num)]
              simp
            rw [show 3 * (H * H) * (4 * A + (M : ℝ)) =
                3 * ((4 * A) * (H * H) + (M : ℝ) * (H * H)) by ring,
              hm3 _ (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
              hm1, hm2]
          rw [e]
          ring
      _ ≤ ENNReal.ofReal C * R := by gcongr
  calc μ {x | t ≤ ‖sourceOrderStatistic K x‖}
      ≤ 3 * (μ.prod μ) {xy | 2 * t / 3 ≤ ‖sourceOrderStatistic K xy.1 +
          sourceOrderStatistic K xy.2‖} := h1
    _ ≤ 3 * (ENNReal.ofReal (4 * A) * (ENNReal.ofReal (H * H) * R) +
        (M : ℝ≥0∞) * (ENNReal.ofReal (H * H) * R)) := by gcongr
    _ ≤ ENNReal.ofReal C * R := hfinal

end Step

/-- The constant of the inductive step (order `k` from the common lower-order constant `H`);
at order one it is `1`. -/
def tailConstStep (k : ℕ) (H : ℝ) : ℝ :=
  if k ≤ 1 then 1
  else 3 * (H * H) * (4 * sourceMixedDegreeWeight k + ((mixedPatterns k).card : ℝ) + 2 ^ k)

/-- The running common constant `H_m ≥ 1`, dominating the constants of all orders `1,…,m`. -/
def tailConstSeq : ℕ → ℝ
  | 0 => 1
  | m + 1 => max (tailConstSeq m) (tailConstStep (m + 1) (tailConstSeq m))

/-- The explicit constant `C_k` of Proposition 3.3, depending only on `k`. -/
def tailConst (k : ℕ) : ℝ := tailConstSeq k

lemma one_le_tailConstStep (k : ℕ) {H : ℝ} (hH : 1 ≤ H) : 1 ≤ tailConstStep k H := by
  unfold tailConstStep
  split_ifs with h
  · exact le_refl _
  · have hk : 0 < k := by omega
    have hA := DGRHS.Decoupling.Prop33.SelectorTonelliBridge.sourceMixedDegreeWeight_pos hk
    have h2 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hHH : 1 ≤ H * H := by nlinarith
    have hM : (0 : ℝ) ≤ ((mixedPatterns k).card : ℝ) := Nat.cast_nonneg _
    nlinarith

section Induction
variable {S E : Type*} [MeasurableSpace S] [MeasurableSpace E] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [OpensMeasurableSpace E] [MeasurableAdd₂ E]

theorem tailConstSeq_spec (m : ℕ) :
    1 ≤ tailConstSeq m ∧
      ∀ r, 0 < r → r ≤ m →
        sourceUniformTailAtOrder (S := S) (E := E) r (tailConstSeq m) := by
  induction m with
  | zero => exact ⟨le_refl _, fun r hr hr0 => absurd hr0 (by omega)⟩
  | succ m ih =>
    obtain ⟨hH, hLow⟩ := ih
    have hc1 := one_le_tailConstStep (m + 1) hH
    have hstep : sourceUniformTailAtOrder (S := S) (E := E) (m + 1)
        (tailConstStep (m + 1) (tailConstSeq m)) := by
      by_cases hm : m = 0
      · subst hm
        simpa [tailConstStep] using (sourceUniformTailAtOrder_one (S := S) (E := E))
      · have hk2 : 2 ≤ m + 1 := by omega
        have hnot : ¬ (m + 1 ≤ 1) := by omega
        simp only [tailConstStep, hnot, ite_false]
        exact sourceUniformTail_step (S := S) (E := E) (m + 1) hk2 (tailConstSeq m) hH
          (fun r hr hrm => hLow r hr (by omega))
    refine ⟨le_trans hH (le_max_left _ _), ?_⟩
    intro r hr hrm
    by_cases hr' : r ≤ m
    · exact sourceUniformTailAtOrder.mono (by linarith) (le_max_left _ _) (hLow r hr hr')
    · have : r = m + 1 := by omega
      subst this
      exact sourceUniformTailAtOrder.mono (by linarith) (le_max_right _ _) hstep

/-- Proposition 3.3 on product laws: for every order `k ≥ 1` the uniform tail inequality holds
with the explicit constant `tailConst k`, which depends only on `k`. -/
theorem sourceUniformTail_tailConst (k : ℕ) (hk : 1 ≤ k) :
    sourceUniformTailAtOrder (S := S) (E := E) k (tailConst k) :=
  (tailConstSeq_spec k).2 k hk le_rfl

end Induction

theorem one_le_tailConst (k : ℕ) : 1 ≤ tailConst k := by
  unfold tailConst
  induction k with
  | zero => exact le_refl _
  | succ m ih => exact le_trans ih (le_max_left _ _)

end DGRHS.Decoupling.Prop33

#print axioms DGRHS.Decoupling.Prop33.sourceUniformTail_step
#print axioms DGRHS.Decoupling.Prop33.sourceUniformTail_tailConst
#print axioms DGRHS.Decoupling.Prop33.one_le_tailConst
