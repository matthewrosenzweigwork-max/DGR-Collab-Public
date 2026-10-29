import SharpSymmetricLSI.Paper.Occ10
import SharpSymmetricLSI.Paper.Occ2

/-!
# Labelling sums as generating coefficients (Phase 3, lane D; R28(d))

If `e 0 = 1` and `α` is supported in `{0, …, K-1}`, the labelling sum
`∑_{c ∈ occLabellings α N} ∏ᵢ e_{cᵢ}(Xᵢ)` is the coefficient of `t^α` in
`∏ᵢ (1 + ∑_{k<K} e_{k+1}(Xᵢ) t_k)`.
-/

noncomputable section
open MvPolynomial Finset.HasAntidiagonal

namespace SharpLSI

/-- Restriction of an occupation to the first `K` modes. -/
def finK (K : ℕ) (α : ℕ →₀ ℕ) : Fin K →₀ ℕ := Finsupp.equivFunOnFinite.symm fun k => α k

@[simp] theorem finK_apply (K : ℕ) (α : ℕ →₀ ℕ) (k : Fin K) : finK K α k = α k := rfl

/-- The exponent of a single label. -/
def labelDeg {K : ℕ} (c : Fin (K + 1)) : Fin K →₀ ℕ := Fin.cases 0 (fun k => Finsupp.single k 1) c

theorem labelDeg_apply {K : ℕ} (c : Fin (K + 1)) (k : Fin K) :
    labelDeg c k = if (c : ℕ) = k + 1 then 1 else 0 := by
  induction c using Fin.cases with
  | zero => simp [labelDeg]
  | succ c =>
    simp only [labelDeg, Fin.cases_succ, Fin.val_succ, Nat.add_right_cancel_iff,
      Finsupp.single_apply, Fin.val_inj]

theorem sum_labelDeg_apply {K N : ℕ} (c : Fin N → Fin (K + 1)) (k : Fin K) :
    (∑ i, labelDeg (c i)) k = (Finset.univ.filter fun i => (c i : ℕ) = k + 1).card := by
  rw [Finsupp.finsetSum_apply]
  simp_rw [labelDeg_apply]
  rw [Finset.sum_boole, Nat.cast_id]

theorem labelling_sum_eq_coeff {T : Type*} (e : ℕ → T → ℝ) (he0 : ∀ x, e 0 x = 1) {K N : ℕ}
    (α : ℕ →₀ ℕ) (hK : ∀ n, K ≤ n → α n = 0) (X : Fin N → T) :
    ∑ c ∈ occLabellings α N, ∏ i, e (c i : ℕ) (X i) =
      (genPoly (fun i (k : Fin K) => e (k + 1) (X i))).coeff (finK K α) := by
  classical
  set M := α.support.sup id
  set tm : Fin N → Fin (K + 1) → MvPolynomial (Fin K) ℝ := fun i c =>
    monomial (labelDeg c) (e (c : ℕ) (X i))
  have h1 : ∀ i, 1 + linForm (fun k : Fin K => e (k + 1) (X i)) = ∑ c, tm i c := fun i => by
    rw [Fin.sum_univ_succ]
    simp only [tm, labelDeg, Fin.cases_zero, Fin.cases_succ, Fin.val_zero, Fin.val_succ, he0,
      linForm, C_mul_X_eq_monomial]
    rfl
  have hG : genPoly (fun i (k : Fin K) => e (k + 1) (X i)) =
      ∑ c : Fin N → Fin (K + 1), monomial (∑ i, labelDeg (c i)) (∏ i, e (c i : ℕ) (X i)) := by
    unfold genPoly
    simp_rw [h1]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [tm]
    rw [monomial_sum_prod]
  rw [hG, coeff_sum]
  simp_rw [coeff_monomial]
  rw [← Finset.sum_filter]
  -- the two index sets
  have hcount : ∀ c : Fin N → Fin (K + 1), (∑ i, labelDeg (c i)) = finK K α ↔
      ∀ k : Fin K, (Finset.univ.filter fun i => (c i : ℕ) = k + 1).card = α k := fun c => by
    constructor
    · intro h k; rw [← sum_labelDeg_apply, h, finK_apply]
    · intro h; ext k; rw [sum_labelDeg_apply, h, finK_apply]
  have hpos : ∀ {n : ℕ} {s : Finset (Fin N)} {f : Fin N → ℕ} (i : Fin N), f i = n + 1 →
      (s.filter fun i => f i = n + 1).card = α n → i ∈ s → α n ≠ 0 := fun i hi hc hs => by
    rw [← hc]; exact Finset.card_ne_zero.mpr ⟨i, Finset.mem_filter.mpr ⟨hs, hi⟩⟩
  refine Finset.sum_bij'
    (fun (c : Fin N → Fin (M + 2)) hc (i : Fin N) => (⟨(c i : ℕ), ?_⟩ : Fin (K + 1)))
    (fun (c : Fin N → Fin (K + 1)) hc (i : Fin N) => (⟨(c i : ℕ), ?_⟩ : Fin (M + 2)))
    ?_ ?_ ?_ ?_ ?_
  · -- bound for labellings
    rw [mem_occLabellings] at hc
    by_contra hlt
    have hpos' := hpos (s := Finset.univ) (f := fun i => (c i : ℕ)) i
      (show (c i : ℕ) = ((c i : ℕ) - 1) + 1 by omega) (hc _) (Finset.mem_univ _)
    exact hpos' (hK _ (by omega))
  · -- bound for generating indices
    rw [Finset.mem_filter, hcount] at hc
    by_cases h0 : (c i : ℕ) = 0
    · omega
    have hk : (c i : ℕ) - 1 < K := by have := (c i).2; omega
    have hpos' := hpos (s := Finset.univ) (f := fun i => (c i : ℕ)) (n := (c i : ℕ) - 1) i
      (by omega) (hc.2 ⟨_, hk⟩) (Finset.mem_univ _)
    have hmem : (c i : ℕ) - 1 ∈ α.support := Finsupp.mem_support_iff.mpr hpos'
    have := Finset.le_sup (f := id) hmem
    simp only [id] at this
    omega
  · intro c hc
    rw [Finset.mem_filter, hcount]
    rw [mem_occLabellings] at hc
    exact ⟨Finset.mem_univ _, fun k => hc k⟩
  · intro c hc
    rw [Finset.mem_filter, hcount] at hc
    rw [mem_occLabellings]
    intro n
    by_cases hn : n < K
    · exact hc.2 ⟨n, hn⟩
    · rw [hK n (by omega), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ h
      have h' : (c i : ℕ) = n + 1 := h
      have := (c i).2
      omega
  · intro c hc; rfl
  · intro c hc; rfl
  · intro c hc; rfl

end SharpLSI
