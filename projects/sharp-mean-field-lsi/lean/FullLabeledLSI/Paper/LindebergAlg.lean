import FullLabeledLSI.Defs.F06_Hybrid

/-!
# Algebra of multilinear label polynomials and influence bookkeeping (Lemma 7.1)

* `polyF f c ω = ∑_j c_j ∏_l f_l(j_l)(ω_l)`: a polynomial multilinear in the label variables `ω_l`,
  where `f l 0 = 1`. The hybrid polynomials `hybEval`/`polyB` are of this form (`lf`, Lindeberg1).
* `cdrop c i m`: the coefficient array of the factor multiplying `f i m (ω i)` in `polyF f c ω`.
* `cZ T a m`: the coefficient array of the normalized sum `a ∑_{l ∈ T} f l (m+1) (ω l)`.
* influence bookkeeping: `∑ᵢ Infᵢ ≤ (L/λ₁) ‖c‖²`, cardinality of retained labels, etc.
-/

open scoped BigOperators

namespace SharpLSI.FL

/-- A polynomial multilinear in the label variables, `∑_j c_j ∏_l f_l(j_l)(ω_l)`. -/
noncomputable def polyF {N J : ℕ} {S : Type*} (f : Fin N → Fin (J + 1) → S → ℝ)
    (c : (Fin N → Fin (J + 1)) → ℝ) (ω : Fin N → S) : ℝ :=
  ∑ j, c j * ∏ l, f l (j l) (ω l)

/-- Freeze label `i` at the value `m` and then remove it: `(cdrop c i m) j = c (j[i := m])` if
`j i = 0` and `0` otherwise. -/
def cdrop {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (i : Fin N) (m : Fin (J + 1)) :
    (Fin N → Fin (J + 1)) → ℝ :=
  fun j => if j i = 0 then c (Function.update j i m) else 0

/-- Coefficients of `a ∑_{l ∈ T} f l (m+1) (ω l)`: the value `a` at the multi-indices
`j = (0,…,m+1 at l,…,0)`, `l ∈ T`. -/
def cZ {N J : ℕ} (T : Finset (Fin N)) (a : ℝ) (m : Fin J) : (Fin N → Fin (J + 1)) → ℝ :=
  fun j => ∑ l ∈ T, if j = Function.update (0 : Fin N → Fin (J + 1)) l m.succ then a else 0

variable {N J : ℕ} {S : Type*}

/-- Reindexing of a sum over multi-indices by the value `m` of the `i`-th coordinate. -/
private lemma sum_eq_sum_update (i : Fin N) (g : (Fin N → Fin (J + 1)) → ℝ) :
    ∑ j', g j' = ∑ m : Fin (J + 1),
      ∑ j ∈ Finset.univ.filter (fun j : Fin N → Fin (J + 1) => j i = 0),
        g (Function.update j i m) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun j' : Fin N → Fin (J + 1) => j' i) g]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_nbij' (fun j' => Function.update j' i 0) (fun j => Function.update j i m)
    ?_ ?_ ?_ ?_ ?_
  · intro a _; simp
  · intro a _; simp
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [Function.update_idem, ← ha, Function.update_eq_self]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [Function.update_idem, ← ha, Function.update_eq_self]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [Function.update_idem, ← ha, Function.update_eq_self]

private lemma polyF_cdrop_eq (f : Fin N → Fin (J + 1) → S → ℝ)
    (c : (Fin N → Fin (J + 1)) → ℝ) (i : Fin N) (m : Fin (J + 1)) (ω : Fin N → S) :
    polyF f (cdrop c i m) ω = ∑ j ∈ Finset.univ.filter (fun j : Fin N → Fin (J + 1) => j i = 0),
      c (Function.update j i m) * ∏ l, f l (j l) (ω l) := by
  unfold polyF cdrop
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]

/-- If `j i = 0` then multiplying by the `i`-th factor with value `m` updates `j`. -/
private lemma mul_prod_update (f : Fin N → Fin (J + 1) → S → ℝ) (hf0 : ∀ l s, f l 0 s = 1)
    (j : Fin N → Fin (J + 1)) (i : Fin N) (m : Fin (J + 1)) (hj : j i = 0) (ω : Fin N → S) :
    f i m (ω i) * ∏ l, f l (j l) (ω l) = ∏ l, f l (Function.update j i m l) (ω l) := by
  classical
  rw [Fintype.prod_eq_mul_prod_compl i (fun l => f l (j l) (ω l)),
    Fintype.prod_eq_mul_prod_compl i (fun l => f l (Function.update j i m l) (ω l))]
  simp only [hj, hf0, one_mul, Function.update_self]
  congr 1
  refine Finset.prod_congr rfl (fun l hl => ?_)
  have : l ≠ i := by simpa using hl
  rw [Function.update_of_ne this]

/-- Decomposition of `polyF` by the value of the `i`-th multi-index. -/
theorem polyF_decomp (f : Fin N → Fin (J + 1) → S → ℝ) (hf0 : ∀ l s, f l 0 s = 1)
    (c : (Fin N → Fin (J + 1)) → ℝ) (i : Fin N) (ω : Fin N → S) :
    polyF f c ω = ∑ m : Fin (J + 1), f i m (ω i) * polyF f (cdrop c i m) ω := by
  unfold polyF
  rw [sum_eq_sum_update i (fun j' => c j' * ∏ l, f l (j' l) (ω l))]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have h := polyF_cdrop_eq f c i m ω
  unfold polyF at h
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j i = 0 := by simpa using hj
  rw [← mul_prod_update f hf0 j i m hj' ω]
  ring

/-- `polyF f (cdrop c i m)` only sees the factors of the labels `l ≠ i`. -/
theorem polyF_cdrop_congr {f g : Fin N → Fin (J + 1) → S → ℝ}
    (hf0 : ∀ l s, f l 0 s = 1) (hg0 : ∀ l s, g l 0 s = 1) (i : Fin N)
    (hfg : ∀ l, l ≠ i → f l = g l) (c : (Fin N → Fin (J + 1)) → ℝ) (m : Fin (J + 1))
    (ω : Fin N → S) : polyF f (cdrop c i m) ω = polyF g (cdrop c i m) ω := by
  rw [polyF_cdrop_eq f c i m ω, polyF_cdrop_eq g c i m ω]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j i = 0 := by simpa using hj
  congr 1
  refine Finset.prod_congr rfl (fun l _ => ?_)
  by_cases hl : l = i
  · subst hl
    rw [hj', hf0, hg0]
  · rw [hfg l hl]

/-- `polyF f (cdrop c i m)` does not depend on the `i`-th variable. -/
theorem polyF_cdrop_update (f : Fin N → Fin (J + 1) → S → ℝ) (hf0 : ∀ l s, f l 0 s = 1)
    (c : (Fin N → Fin (J + 1)) → ℝ) (i : Fin N) (m : Fin (J + 1)) (ω : Fin N → S) (s : S) :
    polyF f (cdrop c i m) (Function.update ω i s) = polyF f (cdrop c i m) ω := by
  rw [polyF_cdrop_eq f c i m _, polyF_cdrop_eq f c i m ω]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j i = 0 := by simpa using hj
  congr 1
  refine Finset.prod_congr rfl (fun l _ => ?_)
  by_cases hl : l = i
  · subst hl
    rw [hj', hf0, hf0]
  · rw [Function.update_of_ne hl]

/-- For `m ≠ 0`: the squared norm of `cdrop c i m` is the mass of `c` on `{j i = m}`. -/
theorem sum_sq_cdrop_le_infl (c : (Fin N → Fin (J + 1)) → ℝ) (i : Fin N) (m : Fin (J + 1))
    (hm : m ≠ 0) : ∑ j, (cdrop c i m j) ^ 2 ≤ infl c i := by
  classical
  have h1 : ∀ j, (cdrop c i m j) ^ 2
      = if j i = 0 then c (Function.update j i m) ^ 2 else 0 := by
    intro j
    unfold cdrop
    split_ifs <;> simp
  simp_rw [h1]
  rw [← Finset.sum_filter]
  unfold infl
  refine Finset.sum_le_sum_of_injOn (fun j => Function.update j i m) ?_ ?_ ?_ ?_
  · intro j hj k hk hjk
    have hj' : j i = 0 := by simpa using hj
    have hk' : k i = 0 := by simpa using hk
    funext l
    by_cases hl : l = i
    · subst hl; rw [hj', hk']
    · have := congrFun hjk l
      simpa [Function.update_of_ne hl] using this
  · intro j' hj'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hj'
    simpa using hm
  · intro j _
    exact le_rfl
  · intro j' _ _
    exact sq_nonneg _

/-- `cdrop` preserves the spectral support (`lam 0 = 0 ≤ lam m`). -/
theorem spectralCoeff_cdrop {lam : ℕ → ℝ} (hlam0 : lam 0 = 0) (hnn : ∀ k, 0 ≤ lam k) {L : ℝ}
    {c : (Fin N → Fin (J + 1)) → ℝ} (hc : SpectralCoeff lam L c) (i : Fin N) (m : Fin (J + 1)) :
    SpectralCoeff lam L (cdrop c i m) := by
  intro j hj
  have hj0 : j i = 0 := by
    by_contra h
    exact hj (by simp [cdrop, h])
  have hcj : c (Function.update j i m) ≠ 0 := by
    intro h
    exact hj (by simp [cdrop, hj0, h])
  refine le_trans ?_ (hc _ hcj)
  refine Finset.sum_le_sum (fun l _ => ?_)
  by_cases hl : l = i
  · subst hl
    simp [hj0, hlam0, hnn]
  · rw [Function.update_of_ne hl]

/-- The multi-index `(0,…,m+1 at l,…,0)`. -/
private abbrev eIdx (l : Fin N) (m : Fin J) : Fin N → Fin (J + 1) :=
  Function.update (0 : Fin N → Fin (J + 1)) l m.succ

private lemma eIdx_self (l : Fin N) (m : Fin J) : eIdx l m l = m.succ := by
  simp [eIdx]

private lemma eIdx_of_ne {l l' : Fin N} (h : l' ≠ l) (m : Fin J) : eIdx l m l' = 0 := by
  simp [eIdx, Function.update_of_ne h]

private lemma eIdx_inj {l l' : Fin N} {m : Fin J} (h : eIdx l m = eIdx l' m) : l = l' := by
  by_contra hne
  have := congrFun h l
  rw [eIdx_self, eIdx_of_ne hne] at this
  exact Fin.succ_ne_zero _ this

private lemma sum_ite_eIdx (T : Finset (Fin N)) (m : Fin J) (b : ℝ) (j : Fin N → Fin (J + 1)) :
    (∑ l ∈ T, if j = eIdx l m then b else 0) = if ∃ l ∈ T, j = eIdx l m then b else 0 := by
  by_cases h : ∃ l ∈ T, j = eIdx l m
  · obtain ⟨l0, hl0, hj⟩ := h
    have hP : ∃ l ∈ T, j = eIdx l m := ⟨l0, hl0, hj⟩
    rw [Finset.sum_eq_single_of_mem l0 hl0]
    · exact (ite_eq_left_of_eq_true b 0 (eq_true hj)).trans (ite_eq_left_of_eq_true b 0 (eq_true hP)).symm
    · intro l _ hne
      have : ¬ j = eIdx l m := fun hjl => hne (eIdx_inj (hj.symm.trans hjl)).symm
      simp [this]
  · refine (Finset.sum_eq_zero (fun l hl => ?_)).trans (by simp [h])
    have : ¬ j = eIdx l m := fun hjl => h ⟨l, hl, hjl⟩
    simp [this]

private lemma cZ_eq (T : Finset (Fin N)) (a : ℝ) (m : Fin J) (j : Fin N → Fin (J + 1)) :
    cZ T a m j = if ∃ l ∈ T, j = eIdx l m then a else 0 :=
  sum_ite_eIdx T m a j

/-- `cZ` realizes the normalized sum as a `polyF`. -/
theorem polyF_cZ (f : Fin N → Fin (J + 1) → S → ℝ) (hf0 : ∀ l s, f l 0 s = 1)
    (T : Finset (Fin N)) (a : ℝ) (m : Fin J) (ω : Fin N → S) :
    polyF f (cZ T a m) ω = a * ∑ l ∈ T, f l m.succ (ω l) := by
  unfold polyF
  have h1 : ∀ j : Fin N → Fin (J + 1), cZ T a m j * ∏ l, f l (j l) (ω l)
      = ∑ l ∈ T, if j = eIdx l m then a * ∏ l, f l (j l) (ω l) else 0 := by
    intro j
    unfold cZ
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.sum_ite_eq' Finset.univ (eIdx l m)
    (fun j => a * ∏ l', f l' (j l') (ω l'))]
  simp only [Finset.mem_univ, ↓reduceIte]
  congr 1
  rw [Finset.prod_eq_single l]
  · rw [eIdx_self]
  · intro l' _ hne
    rw [eIdx_of_ne hne, hf0]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem sum_sq_cZ (T : Finset (Fin N)) (a : ℝ) (m : Fin J) :
    ∑ j, (cZ T a m j) ^ 2 = (T.card : ℝ) * a ^ 2 := by
  have h1 : ∀ j : Fin N → Fin (J + 1), (cZ T a m j) ^ 2
      = ∑ l ∈ T, if j = eIdx l m then a ^ 2 else 0 := by
    intro j
    rw [sum_ite_eIdx, cZ_eq]
    split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ l ∈ T, (∑ j : Fin N → Fin (J + 1), if j = eIdx l m then a ^ 2 else 0) = a ^ 2 := by
    intro l _
    simp
  rw [Finset.sum_congr rfl h2]
  simp

theorem spectralCoeff_cZ {lam : ℕ → ℝ} (hlam0 : lam 0 = 0) (T : Finset (Fin N)) (a : ℝ)
    (m : Fin J) : SpectralCoeff lam (lam ((m : ℕ) + 1)) (cZ T a m) := by
  intro j hj
  rw [cZ_eq] at hj
  have hex : ∃ l ∈ T, j = eIdx l m := by
    by_contra h
    exact hj (by simp [h])
  obtain ⟨l, _, rfl⟩ := hex
  refine le_of_eq ?_
  rw [Finset.sum_eq_single l]
  · rw [eIdx_self]
    simp
  · intro i _ hne
    rw [eIdx_of_ne hne]
    simpa using hlam0
  · intro h; exact absurd (Finset.mem_univ l) h

/-! ### Influence bookkeeping -/

theorem infl_nonneg (c : (Fin N → Fin (J + 1)) → ℝ) (i : Fin N) : 0 ≤ infl c i := by
  unfold infl
  exact Finset.sum_nonneg (fun j _ => sq_nonneg _)

theorem mem_retained_compl_iff (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) (i : Fin N) :
    i ∈ (retained c δ)ᶜ ↔ infl c i ≤ δ := by
  simp [retained]

theorem lowCount_eq_card (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) :
    lowCount c δ = ((retained c δ)ᶜ).card := by
  simp [lowCount, Finset.card_compl]

/-- `∑ᵢ Infᵢ ≤ (L/λ₁) ‖c‖²` on the spectral range. -/
theorem sum_infl_le {lam : ℕ → ℝ} (hlam0 : lam 0 = 0) (hnn : ∀ k, 0 ≤ lam k)
    (hmono : Monotone lam) (hpos : 0 < lam 1) {L : ℝ} {c : (Fin N → Fin (J + 1)) → ℝ}
    (hc : SpectralCoeff lam L c) : ∑ i, infl c i ≤ L / lam 1 * ∑ j, c j ^ 2 := by
  have h1 : ∑ i, infl c i
      = ∑ j, c j ^ 2 * ((Finset.univ.filter (fun i => j i ≠ 0)).card : ℝ) := by
    unfold infl
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [h1, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hcj : c j = 0
  · simp [hcj]
  · have hL := hc j hcj
    have hcard : ((Finset.univ.filter (fun i => j i ≠ 0)).card : ℝ) * lam 1 ≤ L := by
      calc ((Finset.univ.filter (fun i => j i ≠ 0)).card : ℝ) * lam 1
          = ∑ _i ∈ Finset.univ.filter (fun i => j i ≠ 0), lam 1 := by simp
        _ ≤ ∑ i ∈ Finset.univ.filter (fun i => j i ≠ 0), lam (j i) := by
            apply Finset.sum_le_sum
            intro i hi
            have hne : j i ≠ 0 := (Finset.mem_filter.1 hi).2
            apply hmono
            have : (j i : ℕ) ≠ 0 := fun h => hne (Fin.ext h)
            omega
        _ ≤ ∑ i, lam (j i) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun i _ _ => hnn _)
        _ ≤ L := hL
    have : ((Finset.univ.filter (fun i => j i ≠ 0)).card : ℝ) ≤ L / lam 1 :=
      (le_div_iff₀ hpos).2 hcard
    calc c j ^ 2 * ((Finset.univ.filter (fun i => j i ≠ 0)).card : ℝ)
        ≤ c j ^ 2 * (L / lam 1) :=
          mul_le_mul_of_nonneg_left this (sq_nonneg _)
      _ = L / lam 1 * c j ^ 2 := by ring

theorem card_retained_mul_le (c : (Fin N → Fin (J + 1)) → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ((retained c δ).card : ℝ) * δ ≤ ∑ i, infl c i := by
  have h1 : ((retained c δ).card : ℝ) * δ = ∑ _i ∈ retained c δ, δ := by
    simp
  rw [h1]
  calc ∑ _i ∈ retained c δ, δ ≤ ∑ i ∈ retained c δ, infl c i := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [retained, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hi.le
    _ ≤ ∑ i, infl c i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => infl_nonneg c i)

/-- A lower bound on the number of low-influence labels. -/
theorem lowCount_ge {lam : ℕ → ℝ} (hlam0 : lam 0 = 0) (hnn : ∀ k, 0 ≤ lam k)
    (hmono : Monotone lam) (hpos : 0 < lam 1) {L : ℝ} {c : (Fin N → Fin (J + 1)) → ℝ}
    (hc : SpectralCoeff lam L c) {δ : ℝ} (hδ : 0 < δ) :
    (N : ℝ) - L / lam 1 * (∑ j, c j ^ 2) / δ ≤ (lowCount c δ : ℝ) := by
  have hcard_le : (retained c δ).card ≤ N := by
    simpa using Finset.card_le_univ (retained c δ)
  have h1 : ((retained c δ).card : ℝ) * δ ≤ L / lam 1 * ∑ j, c j ^ 2 :=
    (card_retained_mul_le c hδ).trans (sum_infl_le hlam0 hnn hmono hpos hc)
  have h2 : ((retained c δ).card : ℝ) ≤ L / lam 1 * (∑ j, c j ^ 2) / δ :=
    (le_div_iff₀ hδ).2 h1
  have h3 : (lowCount c δ : ℝ) = (N : ℝ) - ((retained c δ).card : ℝ) := by
    unfold lowCount
    rw [Nat.cast_sub hcard_le]
  rw [h3]
  linarith

/-- `∑_{i low} Infᵢ^{3/2} ≤ √δ ∑ᵢ Infᵢ`, written with `√Infᵢ ^ 3`. -/
theorem sum_low_sqrt_cube_le (c : (Fin N → Fin (J + 1)) → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∑ i ∈ (retained c δ)ᶜ, Real.sqrt (infl c i) ^ 3 ≤ Real.sqrt δ * ∑ i, infl c i := by
  calc ∑ i ∈ (retained c δ)ᶜ, Real.sqrt (infl c i) ^ 3
      ≤ ∑ i ∈ (retained c δ)ᶜ, Real.sqrt δ * infl c i := by
        apply Finset.sum_le_sum
        intro i hi
        have hle : infl c i ≤ δ := (mem_retained_compl_iff c δ i).1 hi
        have hnn := infl_nonneg c i
        have hsq : Real.sqrt (infl c i) ^ 2 = infl c i := Real.sq_sqrt hnn
        have hs : Real.sqrt (infl c i) ≤ Real.sqrt δ := Real.sqrt_le_sqrt hle
        have : Real.sqrt (infl c i) ^ 3 = infl c i * Real.sqrt (infl c i) := by
          rw [pow_succ, hsq]
        rw [this]
        nlinarith [mul_le_mul_of_nonneg_left hs hnn]
    _ = Real.sqrt δ * ∑ i ∈ (retained c δ)ᶜ, infl c i := by rw [Finset.mul_sum]
    _ ≤ Real.sqrt δ * ∑ i, infl c i := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => infl_nonneg c i)

/-- `n · (√n)⁻³ = (√n)⁻¹`. -/
theorem nat_mul_inv_sqrt_cube {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * ((Real.sqrt n)⁻¹) ^ 3 = (Real.sqrt n)⁻¹ := by
  have hpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  generalize Real.sqrt (n : ℝ) = r at hpos hsq ⊢
  rw [← hsq]
  field_simp

end SharpLSI.FL
