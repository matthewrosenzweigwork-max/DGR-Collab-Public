import FullLabeledLSI.Defs.F04_Reveal

/-!
# Section 5 infrastructure, part 2: counting lemmas for the random reveal

Exact multiplicity identities (in an arbitrary additive commutative monoid `M`) for the averages over
a uniform `j`-subset `S` and a uniform ordered tuple `I` of distinct labels in `Sᶜ`
(`distinctTuples S k`, F04).

* `injTuples N k`: the injective `k`-tuples in `Fin N`.
* `preSet S I a = S ∪ {I_l : l < a}`.
-/

open Finset

namespace SharpLSI.FL

variable {d N : ℕ}

/-- The injective `k`-tuples of labels in `Fin N`. -/
def injTuples (N k : ℕ) : Finset (Fin k → Fin N) :=
  Finset.univ.filter fun I => Function.Injective I

/-- `S ∪ {I_l : l < a}`. -/
def preSet {k : ℕ} (S : Finset (Fin N)) (I : Fin k → Fin N) (a : ℕ) : Finset (Fin N) :=
  S ∪ (Finset.univ.filter fun l : Fin k => l.val < a).image I

section Count

variable {M : Type*} [AddCommMonoid M]

/-! ### Auxiliary lemmas -/

theorem card_injMaps_aux {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (B : Finset β) :
    ((Finset.univ : Finset (α → β)).filter fun f => Function.Injective f ∧ ∀ x, f x ∈ B).card =
      B.card.descFactorial (Fintype.card α) := by
  rw [← Fintype.card_coe B, ← Fintype.card_embedding_eq, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun e _ => fun x => (e x : β)) ?_ ?_ ?_
  · intro e _
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun x y h => e.injective (Subtype.ext h), fun x => (e x).2⟩
  · intro e _ e' _ h
    ext x
    exact congrFun h x
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    exact ⟨⟨fun x => ⟨f x, hf.2 x⟩, fun x y h => hf.1 (congrArg Subtype.val h)⟩, mem_univ _, rfl⟩

theorem sum_fibre_const_aux {ι κ : Type*} [DecidableEq κ] (r : Finset ι) (r' : Finset κ)
    (g : ι → κ) (hg : ∀ x ∈ r, g x ∈ r') (c : ℕ)
    (hc : ∀ y ∈ r', (r.filter fun x => g x = y).card = c) (φ : κ → M) :
    ∑ x ∈ r, φ (g x) = c • ∑ y ∈ r', φ y := by
  have := Finset.sum_fiberwise_of_maps_to hg (fun x => φ (g x))
  rw [← this, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2] :
    ∀ x ∈ r.filter (fun x => g x = y), φ (g x) = φ y), Finset.sum_const, hc y hy]

theorem sum_pairs_aux {α β : Type*} [Fintype β] [DecidableEq β] (P : Finset α) (t : α → Finset β)
    (f : α → β → M) :
    ∑ a ∈ P, ∑ b ∈ t a, f a b =
      ∑ q ∈ (P ×ˢ (Finset.univ : Finset β)).filter (fun q => q.2 ∈ t q.1), f q.1 q.2 :=
  (Finset.sum_finset_product' (f := f) _ P t (by intro q; simp)).symm


theorem fibre_card_sub_aux (j k m : ℕ) (p : Fin m → Fin k) (hp : Function.Injective p)
    (S : Finset (Fin N)) (hS : S.card = j) (J : Fin m → Fin N) (hJ : J ∈ distinctTuples S m) :
    ((((Finset.univ : Finset (Fin N)).powersetCard j ×ˢ
        (Finset.univ : Finset (Fin k → Fin N))).filter
        (fun q => q.2 ∈ distinctTuples q.1 k)).filter
        (fun q => (q.1, q.2 ∘ p) = (S, J))).card = (N - j - m).descFactorial (k - m) := by
  classical
  obtain ⟨hJi, hJS⟩ := (mem_filter.1 hJ).2
  set B : Finset (Fin N) := (S ∪ Finset.univ.image J)ᶜ with hB
  have hcardA : Fintype.card {l : Fin k // l ∉ Finset.univ.image p} = k - m := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun l : Fin k => l ∉ Finset.univ.image p) =
        (Finset.univ.image p)ᶜ := by ext; simp
    rw [this, Finset.card_compl, Finset.card_image_of_injective _ hp]
    simp
  have hdisj : Disjoint S (Finset.univ.image J) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨l, -, rfl⟩ := mem_image.1 hx'
    exact hJS l hx
  have hcardB : B.card = N - j - m := by
    rw [hB, Finset.card_compl, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ hJi, hS]
    simp [Nat.sub_sub]
  rw [← hcardB, ← hcardA,
    ← card_injMaps_aux (α := {l : Fin k // l ∉ Finset.univ.image p}) B]
  refine Finset.card_bij (fun q _ => fun x : {l : Fin k // l ∉ Finset.univ.image p} => q.2 x.1)
    ?_ ?_ ?_
  · rintro ⟨S', I⟩ hq
    simp only [mem_filter, mem_product, mem_powersetCard, mem_univ, subset_univ, true_and,
      distinctTuples, Prod.mk.injEq] at hq
    obtain ⟨⟨hS'c, hIi, hIS⟩, rfl, hIJ⟩ := hq
    simp only [mem_filter, mem_univ, true_and, hB, mem_compl, mem_union, mem_image, not_or,
      not_exists]
    refine ⟨fun x y h => Subtype.ext (hIi h), fun x => ⟨hIS _, fun l => ?_⟩⟩
    intro hl
    have h1 : I (p l) = J l := congrFun hIJ l
    have := hIi (hl.symm.trans h1.symm)
    exact x.2 (mem_image.2 ⟨l, mem_univ _, this.symm⟩)
  · rintro ⟨S1, I1⟩ hq1 ⟨S2, I2⟩ hq2 h
    simp only [mem_filter, mem_product, mem_powersetCard, mem_univ, subset_univ, true_and,
      distinctTuples, Prod.mk.injEq] at hq1 hq2
    obtain ⟨_, rfl, hI1⟩ := hq1
    obtain ⟨_, rfl, hI2⟩ := hq2
    refine Prod.ext rfl (funext fun l => ?_)
    by_cases hl : l ∈ Finset.univ.image p
    · obtain ⟨a, -, rfl⟩ := mem_image.1 hl
      exact (congrFun hI1 a).trans (congrFun hI2 a).symm
    · exact congrFun h ⟨l, hl⟩
  · intro f hf
    simp only [mem_filter, mem_univ, true_and, hB, mem_compl, mem_union, mem_image, not_or,
      not_exists] at hf
    obtain ⟨hfi, hfB⟩ := hf
    let I : Fin k → Fin N := fun l =>
      if h : l ∈ Finset.univ.image p then J (mem_image.1 h).choose else f ⟨l, h⟩
    have hIp : ∀ a, I (p a) = J a := by
      intro a
      have h : p a ∈ Finset.univ.image p := mem_image_of_mem _ (mem_univ a)
      simp only [I, dif_pos h]
      exact congrArg J (hp ((mem_image.1 h).choose_spec.2))
    have hIf : ∀ x : {l : Fin k // l ∉ Finset.univ.image p}, I x.1 = f x := fun x => by
      simp only [I, dif_neg x.2]
    refine ⟨(S, I), ?_, ?_⟩
    · refine mem_filter.2 ⟨mem_filter.2 ⟨mem_product.2 ⟨mem_powersetCard.2 ⟨subset_univ _, hS⟩,
        mem_univ _⟩, ?_⟩, ?_⟩
      · show I ∈ distinctTuples S k
        refine mem_filter.2 ⟨mem_univ _, ?_, ?_⟩
        · intro l l' h
          by_cases hl : l ∈ Finset.univ.image p <;> by_cases hl' : l' ∈ Finset.univ.image p
          · obtain ⟨a, -, rfl⟩ := mem_image.1 hl
            obtain ⟨a', -, rfl⟩ := mem_image.1 hl'
            rw [hIp, hIp] at h
            rw [hJi h]
          · obtain ⟨a, -, rfl⟩ := mem_image.1 hl
            rw [hIp, show I l' = f ⟨l', hl'⟩ from hIf ⟨l', hl'⟩] at h
            exact absurd h ((hfB ⟨l', hl'⟩).2 a)
          · obtain ⟨a, -, rfl⟩ := mem_image.1 hl'
            rw [hIp, show I l = f ⟨l, hl⟩ from hIf ⟨l, hl⟩] at h
            exact absurd h.symm ((hfB ⟨l, hl⟩).2 a)
          · rw [show I l = f ⟨l, hl⟩ from hIf ⟨l, hl⟩,
              show I l' = f ⟨l', hl'⟩ from hIf ⟨l', hl'⟩] at h
            exact congrArg Subtype.val (hfi h)
        · intro l
          by_cases hl : l ∈ Finset.univ.image p
          · obtain ⟨a, -, rfl⟩ := mem_image.1 hl
            rw [hIp]
            exact hJS a
          · rw [show I l = f ⟨l, hl⟩ from hIf ⟨l, hl⟩]
            exact (hfB ⟨l, hl⟩).1
      · exact Prod.ext rfl (funext hIp)
    · funext x
      exact hIf x

theorem preSet_succ_aux {a : ℕ} (S : Finset (Fin N)) (I : Fin (a + 1) → Fin N) :
    preSet S I a = S ∪ Finset.univ.image (fun x : Fin a => I x.castSucc) := by
  unfold preSet
  congr 1
  ext y
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x.castSucc, x.2, rfl⟩

theorem fibre_card_preSet_aux (j a : ℕ) (T : Finset (Fin N)) (hT : T.card = j + a) (i : Fin N)
    (hi : i ∉ T) :
    ((((Finset.univ : Finset (Fin N)).powersetCard j ×ˢ
        (Finset.univ : Finset (Fin (a + 1) → Fin N))).filter
        (fun q => q.2 ∈ distinctTuples q.1 (a + 1))).filter
        (fun q => (preSet q.1 q.2 a, q.2 (Fin.last a)) = (T, i))).card =
      (j + a).descFactorial a := by
  have key := card_injMaps_aux (α := Fin a) T
  rw [Fintype.card_fin, hT] at key
  rw [← key]
  refine Finset.card_bij (fun q _ => fun x : Fin a => q.2 x.castSucc) ?_ ?_ ?_
  · rintro ⟨S, I⟩ hq
    simp only [mem_filter, mem_product, mem_powersetCard, mem_univ, subset_univ, true_and,
      distinctTuples, Prod.mk.injEq] at hq
    obtain ⟨⟨hSc, hIi, hIS⟩, hpre, -⟩ := hq
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨fun x y h => Fin.castSucc_injective _ (hIi h), fun x => ?_⟩
    rw [← hpre, preSet_succ_aux]
    exact mem_union_right _ (mem_image_of_mem _ (mem_univ x))
  · rintro ⟨S1, I1⟩ hq1 ⟨S2, I2⟩ hq2 h
    simp only [mem_filter, mem_product, mem_powersetCard, mem_univ, subset_univ, true_and,
      distinctTuples, Prod.mk.injEq] at hq1 hq2
    obtain ⟨⟨hS1c, hI1i, hI1S⟩, hpre1, hl1⟩ := hq1
    obtain ⟨⟨hS2c, hI2i, hI2S⟩, hpre2, hl2⟩ := hq2
    have hI : I1 = I2 := by
      funext l
      induction l using Fin.lastCases with
      | last => rw [hl1, hl2]
      | cast x => exact congrFun h x
    subst hI
    have hdisj : ∀ S : Finset (Fin N), (∀ l, I1 l ∉ S) →
        Disjoint S (Finset.univ.image (fun x : Fin a => I1 x.castSucc)) := by
      intro S hS
      rw [Finset.disjoint_left]
      intro y hy hy'
      obtain ⟨x, -, rfl⟩ := mem_image.1 hy'
      exact hS _ hy
    have e1 := Finset.union_sdiff_cancel_right (hdisj S1 hI1S)
    have e2 := Finset.union_sdiff_cancel_right (hdisj S2 hI2S)
    rw [← preSet_succ_aux, hpre1] at e1
    rw [← preSet_succ_aux, hpre2] at e2
    exact Prod.ext (e1.symm.trans e2) rfl
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    obtain ⟨hfi, hfT⟩ := hf
    let I : Fin (a + 1) → Fin N := Fin.snoc (α := fun _ => Fin N) f i
    have hIc : ∀ x : Fin a, I x.castSucc = f x := fun x => by simp [I]
    have hIl : I (Fin.last a) = i := by simp [I]
    set X : Finset (Fin N) := Finset.univ.image f with hX
    have hXT : X ⊆ T := by
      intro y hy
      obtain ⟨x, -, rfl⟩ := mem_image.1 hy
      exact hfT x
    have hXc : X.card = a := by rw [hX, card_image_of_injective _ hfi]; simp
    have hIX : Finset.univ.image (fun x : Fin a => I x.castSucc) = X := by
      rw [hX]; congr 1; funext x; exact hIc x
    refine ⟨(T \ X, I), ?_, ?_⟩
    · refine mem_filter.2 ⟨mem_filter.2 ⟨mem_product.2 ⟨mem_powersetCard.2 ⟨subset_univ _, ?_⟩,
        mem_univ _⟩, ?_⟩, ?_⟩
      · rw [Finset.card_sdiff_of_subset hXT, hT, hXc]; simp
      · show I ∈ distinctTuples (T \ X) (a + 1)
        refine mem_filter.2 ⟨mem_univ _, ?_, ?_⟩
        · intro l l' h
          induction l using Fin.lastCases with
          | last =>
            induction l' using Fin.lastCases with
            | last => rfl
            | cast x' =>
              rw [hIl, hIc] at h
              exact absurd (h ▸ hfT x') hi
          | cast x =>
            induction l' using Fin.lastCases with
            | last =>
              rw [hIl, hIc] at h
              exact absurd (h ▸ hfT x) hi
            | cast x' =>
              rw [hIc, hIc] at h
              rw [hfi h]
        · intro l
          induction l using Fin.lastCases with
          | last =>
            rw [hIl]
            intro h
            exact hi (sdiff_subset h)
          | cast x =>
            rw [hIc]
            intro h
            exact (mem_sdiff.1 h).2 (mem_image_of_mem _ (mem_univ x))
      · show (preSet (T \ X) I a, I (Fin.last a)) = (T, i)
        rw [preSet_succ_aux, hIX, hIl, Finset.sdiff_union_of_subset hXT]
    · funext x
      exact hIc x

/-- Pairs `(S, I)` with `I` a distinct tuple in `Sᶜ` are in bijection with pairs `(I, S)`,
`I` an injective tuple and `S` a `j`-subset of the complement of its range. For a test depending
only on `I` the multiplicity is `C(N-k, j)`. -/
theorem sum_sum_distinctTuples (j k : ℕ) (H : (Fin k → Fin N) → M) :
    ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∑ I ∈ distinctTuples S k, H I =
      (N - k).choose j • ∑ J ∈ injTuples N k, H J := by
  rw [Finset.sum_comm' (t' := injTuples N k)
    (s' := fun I => (Finset.univ.image I)ᶜ.powersetCard j)]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun J hJ => ?_
    have hJ' : Function.Injective J := (Finset.mem_filter.1 hJ).2
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_compl,
      Finset.card_image_of_injective _ hJ']
    simp
  · intro S I
    simp only [distinctTuples, injTuples, mem_powersetCard, mem_filter, mem_univ, true_and,
      subset_iff, mem_compl, mem_image, subset_univ, not_exists]
    constructor
    · rintro ⟨⟨_, hc⟩, hi, hS⟩
      exact ⟨⟨fun x hx l hl => hS l (hl ▸ hx), hc⟩, hi⟩
    · rintro ⟨⟨hsub, hc⟩, hi⟩
      exact ⟨⟨fun _ _ => trivial, hc⟩, hi, fun l hl => hsub hl l rfl⟩

/-- Restricting a distinct tuple in `Sᶜ` to `m` of its positions (`p` injective): every distinct
`m`-tuple in `Sᶜ` extends to a distinct `k`-tuple in `Sᶜ` in `(N - j - m).descFactorial (k - m)`
ways. -/
theorem sum_sum_distinctTuples_sub (j k m : ℕ) (p : Fin m → Fin k) (hp : Function.Injective p)
    (hmk : m ≤ k) (hjk : j + k ≤ N) (G : Finset (Fin N) → (Fin m → Fin N) → M) :
    ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∑ I ∈ distinctTuples S k, G S (I ∘ p) =
      (N - j - m).descFactorial (k - m) •
        ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∑ J ∈ distinctTuples S m, G S J := by
  rw [sum_pairs_aux _ _ (fun S I => G S (I ∘ p)), sum_pairs_aux _ _ G]
  refine sum_fibre_const_aux _ _ (fun q : Finset (Fin N) × (Fin k → Fin N) => (q.1, q.2 ∘ p)) ?_ _ ?_ (fun y => G y.1 y.2)
  · rintro ⟨S, I⟩ hq
    simp only [mem_filter, mem_product, mem_univ, and_true, distinctTuples, true_and] at hq ⊢
    obtain ⟨hS, hIi, hIS⟩ := hq
    exact ⟨hS, hIi.comp hp, fun l => hIS (p l)⟩
  · rintro ⟨S, J⟩ hy
    simp only [mem_filter, mem_product, mem_univ, and_true, mem_powersetCard] at hy
    exact fibre_card_sub_aux j k m p hp S hy.1.2 J hy.2

/-- The pair `(S ∪ {I_l : l < a}, I_a)`, `(S, I)` with `I` a distinct `(a+1)`-tuple in `Sᶜ`, is hit
`(j + a).descFactorial a` times by each pair `(T, i)`, `|T| = j + a`, `i ∉ T`. -/
theorem sum_sum_preSet (j a : ℕ) (hja : j + a < N) (F : Finset (Fin N) → Fin N → M) :
    ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
        ∑ I ∈ distinctTuples S (a + 1), F (preSet S I a) (I (Fin.last a)) =
      (j + a).descFactorial a •
        ∑ T ∈ (Finset.univ : Finset (Fin N)).powersetCard (j + a), ∑ i ∈ Tᶜ, F T i := by
  rw [sum_pairs_aux _ _ (fun S I => F (preSet S I a) (I (Fin.last a))), sum_pairs_aux _ _ F]
  refine sum_fibre_const_aux _ _ (fun q : Finset (Fin N) × (Fin (a + 1) → Fin N) => (preSet q.1 q.2 a, q.2 (Fin.last a))) ?_ _ ?_
    (fun y => F y.1 y.2)
  · rintro ⟨S, I⟩ hq
    simp only [mem_filter, mem_product, mem_univ, and_true, mem_powersetCard, distinctTuples,
      true_and, subset_univ] at hq
    obtain ⟨hSc, hIi, hIS⟩ := hq
    have hdisj : Disjoint S (Finset.univ.image (fun x : Fin a => I x.castSucc)) := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      obtain ⟨x, -, rfl⟩ := mem_image.1 hy'
      exact hIS _ hy
    have hinj : Function.Injective (fun x : Fin a => I x.castSucc) :=
      fun x y h => Fin.castSucc_injective _ (hIi h)
    refine mem_filter.2 ⟨mem_product.2 ⟨mem_powersetCard.2 ⟨subset_univ _, ?_⟩, mem_univ _⟩, ?_⟩
    · show (preSet S I a).card = j + a
      rw [preSet_succ_aux, Finset.card_union_of_disjoint hdisj, card_image_of_injective _ hinj,
        hSc]
      simp
    · show I (Fin.last a) ∈ (preSet S I a)ᶜ
      rw [mem_compl, preSet_succ_aux, mem_union, mem_image]
      rintro (h | ⟨x, -, hx⟩)
      · exact hIS _ h
      · exact absurd (hIi hx) (Fin.castSucc_lt_last x).ne
  · rintro ⟨T, i⟩ hy
    simp only [mem_filter, mem_product, mem_univ, and_true, mem_powersetCard, mem_compl] at hy
    exact fibre_card_preSet_aux j a T hy.1.2 i hy.2

end Count

end SharpLSI.FL
