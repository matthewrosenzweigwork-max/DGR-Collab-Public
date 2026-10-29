import Mathlib

/-!
# Degenerate U-statistic moment bound (Section 6, item M2)

For i.i.d. `X₁, …, X_N ∼ μ` and a bounded kernel `D` which is centered in each variable
(`μ`-a.e.), we prove
`E[(∑_{l<m} D(X_l, X_m))^{2k}] ≤ C_k N^{2k} B^{2k}`
with `C_k` independent of `N`, `D`, `μ`, and the underlying type.

Route: expand the power into a sum over tuples of `2k` ordered index pairs; a term whose
integral does not vanish must have every occurring label appearing at least twice (otherwise
integrate out that coordinate and use centering); hence at most `2k` distinct labels occur, and
the number of such tuples is `O_k(N^{2k})`; each term is bounded by `B^{2k}`.
-/

open MeasureTheory

namespace SharpLSI.FL.Sec6

/-! ### Combinatorics -/

/-- Strictly ordered index pairs `(l, m)` with `l < m`. -/
def upPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun q => q.1 < q.2)

lemma mem_upPairs {N : ℕ} {q : Fin N × Fin N} : q ∈ upPairs N ↔ q.1 < q.2 := by
  simp [upPairs]

/-- Tuples of `r` strictly ordered index pairs. -/
def tuples (N r : ℕ) : Finset (Fin r → Fin N × Fin N) :=
  Fintype.piFinset (fun _ : Fin r => upPairs N)

lemma mem_tuples {N r : ℕ} {p : Fin r → Fin N × Fin N} :
    p ∈ tuples N r ↔ ∀ i, (p i).1 < (p i).2 := by
  simp [tuples, Fintype.mem_piFinset, mem_upPairs]

/-- Number of slots in the first position carrying the label `j`. -/
def cnt1 {N r : ℕ} (p : Fin r → Fin N × Fin N) (j : Fin N) : ℕ :=
  (Finset.univ.filter (fun i => (p i).1 = j)).card

/-- Number of slots in the second position carrying the label `j`. -/
def cnt2 {N r : ℕ} (p : Fin r → Fin N × Fin N) (j : Fin N) : ℕ :=
  (Finset.univ.filter (fun i => (p i).2 = j)).card

/-- No label occurs exactly once among the `2r` label slots. -/
def NoSingleton {N r : ℕ} (p : Fin r → Fin N × Fin N) : Prop :=
  ∀ j : Fin N, cnt1 p j + cnt2 p j ≠ 1

instance {N r : ℕ} : DecidablePred (@NoSingleton N r) := fun p => by
  unfold NoSingleton; infer_instance

lemma card_le_of_noSingleton {N r : ℕ} (p : Fin r → Fin N × Fin N) (hp : NoSingleton p)
    (R : Finset (Fin N)) (hR1 : ∀ i, (p i).1 ∈ R) (hR2 : ∀ i, (p i).2 ∈ R)
    (hR : ∀ j ∈ R, (∃ i, (p i).1 = j) ∨ (∃ i, (p i).2 = j)) : R.card ≤ r := by
  have hs1 : ∑ j ∈ R, cnt1 p j = r := by
    have h : (Finset.univ : Finset (Fin r)).card = ∑ j ∈ R, cnt1 p j :=
      Finset.card_eq_sum_card_fiberwise (f := fun i => (p i).1) (fun i _ => hR1 i)
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h.symm
  have hs2 : ∑ j ∈ R, cnt2 p j = r := by
    have h : (Finset.univ : Finset (Fin r)).card = ∑ j ∈ R, cnt2 p j :=
      Finset.card_eq_sum_card_fiberwise (f := fun i => (p i).2) (fun i _ => hR2 i)
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h.symm
  have hge : ∀ j ∈ R, 2 ≤ cnt1 p j + cnt2 p j := by
    intro j hj
    have hne := hp j
    have hpos : 1 ≤ cnt1 p j + cnt2 p j := by
      rcases hR j hj with ⟨i, hi⟩ | ⟨i, hi⟩
      · have : 0 < cnt1 p j :=
          Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
        omega
      · have : 0 < cnt2 p j :=
          Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
        omega
    omega
  have hsum : R.card • 2 ≤ ∑ j ∈ R, (cnt1 p j + cnt2 p j) :=
    Finset.card_nsmul_le_sum R (fun j => cnt1 p j + cnt2 p j) 2 hge
  rw [Finset.sum_add_distrib, hs1, hs2, smul_eq_mul] at hsum
  omega

lemma card_powerset_le (N r : ℕ) (hN : 1 ≤ N) :
    ((Finset.univ : Finset (Finset (Fin N))).filter (fun R => R.card ≤ r)).card ≤
      (r + 1) * N ^ r := by
  have hsub : (Finset.univ : Finset (Finset (Fin N))).filter (fun R => R.card ≤ r) ⊆
      (Finset.range (r + 1)).biUnion
        (fun s => Finset.powersetCard s (Finset.univ : Finset (Fin N))) := by
    intro R hR
    rw [Finset.mem_filter] at hR
    rw [Finset.mem_biUnion]
    exact ⟨R.card, Finset.mem_range.2 (Nat.lt_succ_of_le hR.2),
      Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ s ∈ Finset.range (r + 1),
          (Finset.powersetCard s (Finset.univ : Finset (Fin N))).card := Finset.card_biUnion_le
    _ ≤ ∑ s ∈ Finset.range (r + 1), N ^ r := by
      apply Finset.sum_le_sum
      intro s hs
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      exact (Nat.choose_le_pow N s).trans
        (Nat.pow_le_pow_right hN (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)))
    _ = (r + 1) * N ^ r := by simp

lemma card_noSingleton_le (N r : ℕ) (hN : 1 ≤ N) :
    ((tuples N r).filter (fun p => NoSingleton p)).card ≤ (r + 1) * (r * r + 1) ^ r * N ^ r := by
  have hcover : (tuples N r).filter (fun p => NoSingleton p) ⊆
      ((Finset.univ : Finset (Finset (Fin N))).filter (fun R => R.card ≤ r)).biUnion
        (fun R => Fintype.piFinset (fun _ : Fin r => R ×ˢ R)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨_, hng⟩ := hp
    have hR1 : ∀ i, (p i).1 ∈
        Finset.univ.image (fun i => (p i).1) ∪ Finset.univ.image (fun i => (p i).2) :=
      fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hR2 : ∀ i, (p i).2 ∈
        Finset.univ.image (fun i => (p i).1) ∪ Finset.univ.image (fun i => (p i).2) :=
      fun i => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    rw [Finset.mem_biUnion]
    refine ⟨Finset.univ.image (fun i => (p i).1) ∪ Finset.univ.image (fun i => (p i).2),
      ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      refine card_le_of_noSingleton p hng _ hR1 hR2 ?_
      intro j hj
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hj
      rcases hj with ⟨i, _, hi⟩ | ⟨i, _, hi⟩
      · exact Or.inl ⟨i, hi⟩
      · exact Or.inr ⟨i, hi⟩
    · rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_product]
      exact ⟨hR1 i, hR2 i⟩
  calc _ ≤ _ := Finset.card_le_card hcover
    _ ≤ ∑ R ∈ (Finset.univ : Finset (Finset (Fin N))).filter (fun R => R.card ≤ r),
          (Fintype.piFinset (fun _ : Fin r => R ×ˢ R)).card := Finset.card_biUnion_le
    _ ≤ ∑ R ∈ (Finset.univ : Finset (Finset (Fin N))).filter (fun R => R.card ≤ r),
          (r * r + 1) ^ r := by
        apply Finset.sum_le_sum
        intro R hR
        have hRr : R.card ≤ r := (Finset.mem_filter.1 hR).2
        rw [Fintype.card_piFinset_const, Finset.card_product]
        exact Nat.pow_le_pow_left (Nat.le_succ_of_le (Nat.mul_le_mul hRr hRr)) r
    _ = ((Finset.univ : Finset (Finset (Fin N))).filter (fun R => R.card ≤ r)).card *
          (r * r + 1) ^ r := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (r + 1) * N ^ r * (r * r + 1) ^ r := Nat.mul_le_mul_right _ (card_powerset_le N r hN)
    _ = (r + 1) * (r * r + 1) ^ r * N ^ r := by ring

lemma card_noSingleton_le_all (N r : ℕ) :
    ((tuples N r).filter (fun p => NoSingleton p)).card ≤ (r + 1) * (r * r + 1) ^ r * N ^ r := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hup : upPairs 0 = ∅ := by simp [upPairs]
    calc _ ≤ (tuples 0 r).card := Finset.card_filter_le _ _
      _ = 0 ^ r := by simp [tuples, hup]
      _ ≤ _ := Nat.le_mul_of_pos_left _ (by positivity)
  · exact card_noSingleton_le N r hN

lemma exists_unique_slot {N r : ℕ} (p : Fin r → Fin N × Fin N) (j : Fin N)
    (h : cnt1 p j + cnt2 p j = 1) :
    (∃ i₀, (p i₀).1 = j ∧ (∀ i, i ≠ i₀ → (p i).1 ≠ j) ∧ ∀ i, (p i).2 ≠ j) ∨
    (∃ i₀, (p i₀).2 = j ∧ (∀ i, i ≠ i₀ → (p i).2 ≠ j) ∧ ∀ i, (p i).1 ≠ j) := by
  have hc : (cnt1 p j = 1 ∧ cnt2 p j = 0) ∨ (cnt1 p j = 0 ∧ cnt2 p j = 1) := by omega
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    unfold cnt1 at h1
    unfold cnt2 at h2
    obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.1 h1
    have hmem : i₀ ∈ Finset.univ.filter (fun i => (p i).1 = j) := by
      rw [hi₀]; exact Finset.mem_singleton_self _
    refine ⟨i₀, (Finset.mem_filter.1 hmem).2, ?_, ?_⟩
    · intro i hi hpi
      have : i ∈ Finset.univ.filter (fun i => (p i).1 = j) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hpi⟩
      rw [hi₀, Finset.mem_singleton] at this
      exact hi this
    · intro i hpi
      have : i ∈ Finset.univ.filter (fun i => (p i).2 = j) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hpi⟩
      rw [Finset.card_eq_zero.1 h2] at this
      simp at this
  · right
    unfold cnt1 at h1
    unfold cnt2 at h2
    obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.1 h2
    have hmem : i₀ ∈ Finset.univ.filter (fun i => (p i).2 = j) := by
      rw [hi₀]; exact Finset.mem_singleton_self _
    refine ⟨i₀, (Finset.mem_filter.1 hmem).2, ?_, ?_⟩
    · intro i hi hpi
      have : i ∈ Finset.univ.filter (fun i => (p i).2 = j) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hpi⟩
      rw [hi₀, Finset.mem_singleton] at this
      exact hi this
    · intro i hpi
      have : i ∈ Finset.univ.filter (fun i => (p i).1 = j) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hpi⟩
      rw [Finset.card_eq_zero.1 h1] at this
      simp at this

/-! ### Analysis -/

section Analysis

variable {α : Type} [MeasurableSpace α]

/-- The law of two distinct coordinates of an i.i.d. family is the product measure. -/
lemma measurePreserving_pair (μ : Measure α) [IsProbabilityMeasure μ] (N : ℕ) {l m : Fin N}
    (hlm : l ≠ m) :
    MeasurePreserving (fun ω : Fin N → α => (ω l, ω m)) (Measure.pi fun _ : Fin N => μ)
      (μ.prod μ) := by
  have hind : ProbabilityTheory.iIndepFun (fun (i : Fin N) (ω : Fin N → α) => ω i)
      (Measure.pi fun _ : Fin N => μ) :=
    ProbabilityTheory.iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have h2 := hind.indepFun hlm
  have hl : (Measure.pi fun _ : Fin N => μ).map (fun ω : Fin N → α => ω l) = μ :=
    (measurePreserving_eval (fun _ : Fin N => μ) l).map_eq
  have hm : (Measure.pi fun _ : Fin N => μ).map (fun ω : Fin N → α => ω m) = μ :=
    (measurePreserving_eval (fun _ : Fin N => μ) m).map_eq
  refine ⟨(measurable_pi_apply l).prodMk (measurable_pi_apply m), ?_⟩
  have e : (Measure.pi fun _ : Fin N => μ).map (fun ω : Fin N → α => (ω l, ω m)) =
      ((Measure.pi fun _ : Fin N => μ).map (fun ω : Fin N → α => ω l)).prod
        ((Measure.pi fun _ : Fin N => μ).map (fun ω : Fin N → α => ω m)) :=
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (measurable_pi_apply l).aemeasurable (measurable_pi_apply m).aemeasurable).1 h2
  rw [e, hl, hm]

lemma measurable_term {N r : ℕ} (D : α → α → ℝ) (hD : Measurable (Function.uncurry D))
    (p : Fin r → Fin N × Fin N) :
    Measurable (fun ω : Fin N → α => ∏ i, D (ω (p i).1) (ω (p i).2)) := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin r)),
      Measurable (fun ω : Fin N → α => D (ω (p i).1) (ω (p i).2)) := by
    intro i _
    have h2 : Measurable (fun ω : Fin N → α => (ω (p i).1, ω (p i).2)) :=
      (measurable_pi_apply (p i).1).prodMk (measurable_pi_apply (p i).2)
    exact hD.comp h2
  exact Finset.measurable_prod _ h

lemma ae_abs_term_le (μ : Measure α) [IsProbabilityMeasure μ] {N r : ℕ} (D : α → α → ℝ) (B : ℝ)
    (hB : ∀ᵐ z ∂(μ.prod μ), |D z.1 z.2| ≤ B) (p : Fin r → Fin N × Fin N)
    (hlt : ∀ i, (p i).1 < (p i).2) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Fin N => μ), |∏ i, D (ω (p i).1) (ω (p i).2)| ≤ B ^ r := by
  have hall : ∀ᵐ ω ∂(Measure.pi fun _ : Fin N => μ), ∀ i, |D (ω (p i).1) (ω (p i).2)| ≤ B := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_pair μ N (hlt i).ne).quasiMeasurePreserving.ae hB
  filter_upwards [hall] with ω hω
  rw [Finset.abs_prod]
  calc ∏ i, |D (ω (p i).1) (ω (p i).2)| ≤ ∏ _i : Fin r, B :=
        Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hω i)
    _ = B ^ r := by simp

lemma integrable_term (μ : Measure α) [IsProbabilityMeasure μ] {N r : ℕ} (D : α → α → ℝ) (B : ℝ)
    (hD : Measurable (Function.uncurry D)) (hB : ∀ᵐ z ∂(μ.prod μ), |D z.1 z.2| ≤ B)
    (p : Fin r → Fin N × Fin N) (hlt : ∀ i, (p i).1 < (p i).2) :
    Integrable (fun ω : Fin N → α => ∏ i, D (ω (p i).1) (ω (p i).2))
      (Measure.pi fun _ : Fin N => μ) :=
  Integrable.of_bound (measurable_term D hD p).aestronglyMeasurable (B ^ r)
    ((ae_abs_term_le μ D B hB p hlt).mono fun ω hω => by rwa [Real.norm_eq_abs])

lemma insertNth_apply_eq_of_ne {n : ℕ} {β : Type*} (j k : Fin (n + 1)) (hk : k ≠ j) (x x' : β)
    (y : Fin n → β) :
    (Fin.insertNth (α := fun _ => β) j x y) k = (Fin.insertNth (α := fun _ => β) j x' y) k := by
  obtain ⟨z, rfl⟩ := Fin.exists_succAbove_eq hk
  rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]

/-- Vanishing when the label `j` occurs exactly once, in the first slot of the pair `i₀`:
integrate out the coordinate `j`. -/
lemma integral_term_eq_zero_A (μ : Measure α) [IsProbabilityMeasure μ] {n r : ℕ}
    (D : α → α → ℝ) (hY : ∀ᵐ y ∂μ, ∫ x, D x y ∂μ = 0)
    (a b : Fin r → Fin (n + 1)) (j : Fin (n + 1)) (i₀ : Fin r)
    (ha0 : a i₀ = j) (ha : ∀ i, i ≠ i₀ → a i ≠ j) (hb : ∀ i, b i ≠ j)
    (F : (Fin (n + 1) → α) → ℝ) (hF : ∀ ω, F ω = ∏ i, D (ω (a i)) (ω (b i)))
    (hint : Integrable F (Measure.pi fun _ : Fin (n + 1) => μ)) :
    ∫ ω, F ω ∂(Measure.pi fun _ : Fin (n + 1) => μ) = 0 := by
  obtain ⟨x₀⟩ : Nonempty α := nonempty_of_isProbabilityMeasure μ
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) j
  have hint' := (hmp.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)
    (g := F)).2 hint
  have hsymm : ∀ (x : α) (y : Fin n → α),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) j).symm (x, y) =
        Fin.insertNth (α := fun _ => α) j x y := fun x y => rfl
  have step1 : ∫ ω, F ω ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
      ∫ y, ∫ x, F (Fin.insertNth (α := fun _ => α) j x y) ∂μ ∂(Measure.pi fun _ : Fin n => μ) := by
    rw [← hmp.symm.integral_comp' F]
    have h2 := integral_prod_symm
      (fun z => F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) j).symm z)) hint'
    rw [h2]
    simp only [hsymm]
  obtain ⟨m', hm'⟩ := Fin.exists_succAbove_eq (hb i₀)
  have hae : ∀ᵐ y ∂(Measure.pi fun _ : Fin n => μ), ∫ x, D x (y m') ∂μ = 0 :=
    (measurePreserving_eval (fun _ : Fin n => μ) m').quasiMeasurePreserving.ae hY
  have step2 : ∀ᵐ y ∂(Measure.pi fun _ : Fin n => μ),
      ∫ x, F (Fin.insertNth (α := fun _ => α) j x y) ∂μ = 0 := by
    filter_upwards [hae] with y hy
    have hfac : ∀ x : α, F (Fin.insertNth (α := fun _ => α) j x y) =
        D x (y m') * ∏ i ∈ Finset.univ.erase i₀,
          D ((Fin.insertNth (α := fun _ => α) j x₀ y) (a i))
            ((Fin.insertNth (α := fun _ => α) j x₀ y) (b i)) := by
      intro x
      rw [hF, ← Finset.mul_prod_erase Finset.univ
        (fun i => D ((Fin.insertNth (α := fun _ => α) j x y) (a i))
          ((Fin.insertNth (α := fun _ => α) j x y) (b i))) (Finset.mem_univ i₀)]
      congr 1
      · rw [ha0, Fin.insertNth_apply_same, ← hm', Fin.insertNth_apply_succAbove]
      · refine Finset.prod_congr rfl (fun i hi => ?_)
        have hi0 : i ≠ i₀ := Finset.ne_of_mem_erase hi
        rw [insertNth_apply_eq_of_ne j (a i) (ha i hi0) x x₀ y,
          insertNth_apply_eq_of_ne j (b i) (hb i) x x₀ y]
    calc ∫ x, F (Fin.insertNth (α := fun _ => α) j x y) ∂μ
        = ∫ x, D x (y m') * ∏ i ∈ Finset.univ.erase i₀,
            D ((Fin.insertNth (α := fun _ => α) j x₀ y) (a i))
              ((Fin.insertNth (α := fun _ => α) j x₀ y) (b i)) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall hfac)
      _ = 0 := by rw [integral_mul_const, hy, zero_mul]
  rw [step1]
  calc ∫ y, ∫ x, F (Fin.insertNth (α := fun _ => α) j x y) ∂μ ∂(Measure.pi fun _ : Fin n => μ)
      = ∫ _y, (0 : ℝ) ∂(Measure.pi fun _ : Fin n => μ) := integral_congr_ae step2
    _ = 0 := by simp

/-- Vanishing when some label occurs exactly once. -/
lemma integral_term_eq_zero (μ : Measure α) [IsProbabilityMeasure μ] {N r : ℕ}
    (D : α → α → ℝ) (hX : ∀ᵐ x ∂μ, ∫ y, D x y ∂μ = 0) (hY : ∀ᵐ y ∂μ, ∫ x, D x y ∂μ = 0)
    (a b : Fin r → Fin N) (j : Fin N)
    (hj : (∃ i₀, a i₀ = j ∧ (∀ i, i ≠ i₀ → a i ≠ j) ∧ ∀ i, b i ≠ j) ∨
      (∃ i₀, b i₀ = j ∧ (∀ i, i ≠ i₀ → b i ≠ j) ∧ ∀ i, a i ≠ j))
    (hint : Integrable (fun ω : Fin N → α => ∏ i, D (ω (a i)) (ω (b i)))
      (Measure.pi fun _ : Fin N => μ)) :
    ∫ ω, ∏ i, D (ω (a i)) (ω (b i)) ∂(Measure.pi fun _ : Fin N => μ) = 0 := by
  cases N with
  | zero => exact j.elim0
  | succ n =>
    rcases hj with ⟨i₀, h0, h1, h2⟩ | ⟨i₀, h0, h1, h2⟩
    · exact integral_term_eq_zero_A μ D hY a b j i₀ h0 h1 h2 _ (fun _ => rfl) hint
    · exact integral_term_eq_zero_A μ (fun x y => D y x) hX b a j i₀ h0 h1 h2 _
        (fun _ => rfl) hint

/-- Main estimate for a general exponent `r`. -/
theorem ustat_moment_bound_aux (μ : Measure α) [IsProbabilityMeasure μ] (N r : ℕ)
    (D : α → α → ℝ) (B : ℝ) (hD : Measurable (Function.uncurry D))
    (hB : ∀ᵐ z ∂(μ.prod μ), |D z.1 z.2| ≤ B)
    (hX : ∀ᵐ x ∂μ, ∫ y, D x y ∂μ = 0) (hY : ∀ᵐ y ∂μ, ∫ x, D x y ∂μ = 0) :
    ∫ ω, (∑ l : Fin N, ∑ m : Fin N, if l < m then D (ω l) (ω m) else 0) ^ r
        ∂(Measure.pi fun _ : Fin N => μ) ≤
      (((r + 1) * (r * r + 1) ^ r : ℕ) : ℝ) * (N : ℝ) ^ r * B ^ r := by
  have hB0 : 0 ≤ B := by
    obtain ⟨z, hz⟩ := hB.exists
    exact (abs_nonneg _).trans hz
  have hS : ∀ ω : Fin N → α, (∑ l : Fin N, ∑ m : Fin N, if l < m then D (ω l) (ω m) else 0) =
      ∑ q ∈ upPairs N, D (ω q.1) (ω q.2) := by
    intro ω
    rw [upPairs, Finset.sum_filter]
    exact (Fintype.sum_prod_type' (f := fun l m => if l < m then D (ω l) (ω m) else 0)).symm
  have hexp : ∀ ω : Fin N → α,
      (∑ l : Fin N, ∑ m : Fin N, if l < m then D (ω l) (ω m) else 0) ^ r =
        ∑ p ∈ tuples N r, ∏ i, D (ω (p i).1) (ω (p i).2) := by
    intro ω
    rw [hS ω]
    exact Finset.sum_pow' (upPairs N) (fun q => D (ω q.1) (ω q.2)) r
  have hint : ∀ p ∈ tuples N r,
      Integrable (fun ω : Fin N → α => ∏ i, D (ω (p i).1) (ω (p i).2))
        (Measure.pi fun _ : Fin N => μ) :=
    fun p hp => integrable_term μ D B hD hB p (mem_tuples.1 hp)
  have hbound : ∀ p ∈ tuples N r,
      ∫ ω, ∏ i, D (ω (p i).1) (ω (p i).2) ∂(Measure.pi fun _ : Fin N => μ) ≤
        if NoSingleton p then B ^ r else 0 := by
    intro p hp
    have hlt := mem_tuples.1 hp
    split_ifs with hng
    · calc ∫ ω, ∏ i, D (ω (p i).1) (ω (p i).2) ∂(Measure.pi fun _ : Fin N => μ)
          ≤ ∫ _ω, B ^ r ∂(Measure.pi fun _ : Fin N => μ) :=
            integral_mono_ae (hint p hp) (integrable_const _)
              ((ae_abs_term_le μ D B hB p hlt).mono fun ω hω => (le_abs_self _).trans hω)
        _ = B ^ r := by simp
    · refine le_of_eq ?_
      have hex : ∃ j, cnt1 p j + cnt2 p j = 1 := by
        by_contra h
        exact hng (fun j hj => h ⟨j, hj⟩)
      obtain ⟨j, hj⟩ := hex
      exact integral_term_eq_zero μ D hX hY (fun i => (p i).1) (fun i => (p i).2) j
        (exists_unique_slot p j hj) (hint p hp)
  have hcard := card_noSingleton_le_all N r
  calc ∫ ω, (∑ l : Fin N, ∑ m : Fin N, if l < m then D (ω l) (ω m) else 0) ^ r
        ∂(Measure.pi fun _ : Fin N => μ)
      = ∫ ω, ∑ p ∈ tuples N r, ∏ i, D (ω (p i).1) (ω (p i).2)
        ∂(Measure.pi fun _ : Fin N => μ) :=
        integral_congr_ae (Filter.Eventually.of_forall hexp)
    _ = ∑ p ∈ tuples N r, ∫ ω, ∏ i, D (ω (p i).1) (ω (p i).2)
        ∂(Measure.pi fun _ : Fin N => μ) := integral_finsetSum _ hint
    _ ≤ ∑ p ∈ tuples N r, (if NoSingleton p then B ^ r else 0) := Finset.sum_le_sum hbound
    _ = (((tuples N r).filter (fun p => NoSingleton p)).card : ℝ) * B ^ r := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((r + 1) * (r * r + 1) ^ r * N ^ r : ℕ) : ℝ) * B ^ r :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg hB0 r)
    _ = (((r + 1) * (r * r + 1) ^ r : ℕ) : ℝ) * (N : ℝ) ^ r * B ^ r := by
        push_cast; ring

end Analysis

/-- **Degenerate U-statistic moment bound.** For i.i.d. `X₁, …, X_N ∼ μ` and a bounded kernel `D`
(`|D| ≤ B` a.e.) which is centered in each variable, `E[(∑_{l<m} D(X_l, X_m))^{2k}] ≤
C_k N^{2k} B^{2k}` with `C_k` independent of `N`, `D`, `μ`, `α`. -/
theorem ustat_moment_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
      (N : ℕ) (D : α → α → ℝ) (B : ℝ), Measurable (Function.uncurry D) →
      (∀ᵐ z ∂(μ.prod μ), |D z.1 z.2| ≤ B) →
      (∀ᵐ x ∂μ, ∫ y, D x y ∂μ = 0) → (∀ᵐ y ∂μ, ∫ x, D x y ∂μ = 0) →
      ∫ ω, (∑ l : Fin N, ∑ m : Fin N, if l < m then D (ω l) (ω m) else 0) ^ (2 * k)
          ∂(Measure.pi fun _ : Fin N => μ) ≤ C * (N : ℝ) ^ (2 * k) * B ^ (2 * k) := by
  refine ⟨(((2 * k + 1) * ((2 * k) * (2 * k) + 1) ^ (2 * k) : ℕ) : ℝ), Nat.cast_nonneg _, ?_⟩
  intro α _ μ _ N D B hD hB hX hY
  exact ustat_moment_bound_aux μ N (2 * k) D B hD hB hX hY

end SharpLSI.FL.Sec6
