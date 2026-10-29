import FullLabeledLSI.Infra.HypercontrHybrid3

/-!
# Gaussian monomials as multilinear polynomials in the coordinates `y_{i,m}`

A multi-index `jC : Fin N → Fin (J+1)` corresponds to the monomial
`∏_i gamF (jC i) (y_i) = ∏_{s ∈ suppC jC} y_{s.1, s.2}` with
`suppC jC = {(i, m) | jC i = m+1}`; `jC ↦ suppC jC` is injective and
`|suppC jC| = #{i | jC i ≠ 0}`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace SharpLSI.FL.Hyb

variable {N J : ℕ}

/-- The set of Gaussian coordinates used by the monomial `jC`. -/
def suppC (jC : Fin N → Fin (J + 1)) : Finset (Fin N × Fin J) :=
  Finset.univ.filter fun s => (jC s.1 : ℕ) = (s.2 : ℕ) + 1

lemma mem_suppC {jC : Fin N → Fin (J + 1)} {s : Fin N × Fin J} :
    s ∈ suppC jC ↔ (jC s.1 : ℕ) = (s.2 : ℕ) + 1 := by
  simp [suppC]

lemma suppC_injective : Function.Injective (suppC (N := N) (J := J)) := by
  intro j1 j2 h
  funext i
  apply Fin.ext
  by_cases h0 : (j1 i : ℕ) = 0
  · by_contra hne
    have hpos : (j2 i : ℕ) ≠ 0 := fun h2 => hne (by rw [h0, h2])
    have hlt : (j2 i : ℕ) - 1 < J := by have := (j2 i).isLt; omega
    have hmem : (i, (⟨(j2 i : ℕ) - 1, hlt⟩ : Fin J)) ∈ suppC j2 := by
      rw [mem_suppC]; try dsimp only
      omega
    rw [← h, mem_suppC] at hmem
    try dsimp only at hmem
    omega
  · have hlt : (j1 i : ℕ) - 1 < J := by have := (j1 i).isLt; omega
    have hmem : (i, (⟨(j1 i : ℕ) - 1, hlt⟩ : Fin J)) ∈ suppC j1 := by
      rw [mem_suppC]; try dsimp only
      omega
    rw [h, mem_suppC] at hmem
    try dsimp only at hmem
    omega

lemma prod_gamF_eq (jC : Fin N → Fin (J + 1)) (y : Fin N → Fin J → ℝ) :
    ∏ i, gamF (jC i) (y i) = ∏ s ∈ suppC jC, y s.1 s.2 := by
  unfold suppC
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h0 : (jC i : ℕ) = 0
  · simp [gamF, h0]
  · have hlt : (jC i : ℕ) - 1 < J := by have := (jC i).isLt; omega
    rw [Finset.prod_eq_single (⟨(jC i : ℕ) - 1, hlt⟩ : Fin J)]
    · simp only [gamF, h0, dif_neg, not_false_eq_true]
      rw [if_pos (by try dsimp only
                     omega)]
    · intro m _ hm
      rw [if_neg]
      intro hc
      apply hm
      apply Fin.ext
      try dsimp only at hc ⊢
      omega
    · intro h; exact absurd (Finset.mem_univ _) h

lemma card_suppC (jC : Fin N → Fin (J + 1)) :
    (suppC jC).card = (Finset.univ.filter fun i => jC i ≠ 0).card := by
  refine Finset.card_bij (fun s _ => s.1) ?_ ?_ ?_
  · intro s hs
    rw [mem_suppC] at hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
    intro h0; rw [h0] at hs; simp at hs
  · intro s hs t ht hst
    rw [mem_suppC] at hs ht
    refine Prod.ext hst (Fin.ext ?_)
    have : (jC s.1 : ℕ) = (jC t.1 : ℕ) := by rw [hst]
    omega
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq] at hi
    have hpos : (jC i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    have hlt : (jC i : ℕ) - 1 < J := by have := (jC i).isLt; omega
    exact ⟨(i, ⟨(jC i : ℕ) - 1, hlt⟩), by rw [mem_suppC]; (try dsimp only); omega, rfl⟩

/-- Degree bound: if `lam` is non-negative, `lam m ≥ lam 1 > 0` for `m ≥ 1`, and
`∑ lam (jC i) ≤ L`, then at most `L / lam 1` coordinates are non-zero. -/
lemma card_suppC_le {lam : ℕ → ℝ} (hnn : ∀ m, 0 ≤ lam m) (h1 : 0 < lam 1)
    (hmono : ∀ m, 1 ≤ m → lam 1 ≤ lam m) {L : ℝ} {jC : Fin N → Fin (J + 1)}
    (hL : ∑ i, lam (jC i) ≤ L) : ((suppC jC).card : ℝ) ≤ L / lam 1 := by
  rw [card_suppC, le_div_iff₀ h1]
  calc ((Finset.univ.filter fun i => jC i ≠ 0).card : ℝ) * lam 1
      = ∑ i ∈ Finset.univ.filter (fun i => jC i ≠ 0), lam 1 := by simp [mul_comm]
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => jC i ≠ 0), lam (jC i) := by
        refine Finset.sum_le_sum fun i hi => hmono _ ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq] at hi
        have : (jC i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
        omega
    _ ≤ ∑ i, lam (jC i) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => hnn _)
    _ ≤ L := hL

end SharpLSI.FL.Hyb

end
