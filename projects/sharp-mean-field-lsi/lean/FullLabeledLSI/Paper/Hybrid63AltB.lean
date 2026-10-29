import FullLabeledLSI.Defs.F05_FiniteRank
import FullLabeledLSI.Defs.F06_Hybrid
import FullLabeledLSI.Paper.Lindeberg1

/-!
# Proposition 6.3, step R1: from `InSpectralRange` to a coefficient array on `Fin (J+1)`

Given a finite set `T` of multi-indices `k : Fin N → ℕ` and coefficients `c`, with every `k ∈ T`
having all entries `≤ J`, the array `c' j = c (castIdx j)` if `castIdx j ∈ T` (else `0`) on
`Fin N → Fin (J+1)` satisfies `polyEval e c' = ∑_{k ∈ T} c_k ∏ e_{k_i}` and the sum identities.
-/

open MeasureTheory

noncomputable section

namespace SharpLSI.FL

variable {d : ℕ}

/-- The cast of a multi-index. -/
def castIdx {N J : ℕ} (j : Fin N → Fin (J + 1)) : Fin N → ℕ := fun i => (j i : ℕ)

theorem castIdx_injective {N J : ℕ} : Function.Injective (castIdx (N := N) (J := J)) := by
  intro j j' h
  funext i
  exact Fin.ext (congrFun h i)

theorem sum_castIdx {N J : ℕ} (T : Finset (Fin N → ℕ)) (hT : ∀ k ∈ T, ∀ i, k i ≤ J)
    {M : Type*} [AddCommMonoid M] (g : (Fin N → ℕ) → M) :
    ∑ j : Fin N → Fin (J + 1), (if castIdx j ∈ T then g (castIdx j) else 0) = ∑ k ∈ T, g k := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun j _ => castIdx j) ?_ ?_ ?_ ?_
  · intro j hj
    simpa using hj
  · intro j _ j' _ h
    exact castIdx_injective h
  · intro k hk
    refine ⟨fun i => ⟨k i, Nat.lt_succ_of_le (hT k hk i)⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hk
    · funext i; rfl
  · intro j _
    rfl

/-- The coefficient array on `Fin (J+1)`. -/
def coefArr {N J : ℕ} (T : Finset (Fin N → ℕ)) (c : (Fin N → ℕ) → ℝ) :
    (Fin N → Fin (J + 1)) → ℝ :=
  fun j => if castIdx j ∈ T then c (castIdx j) else 0

theorem polyEval_coefArr {N J : ℕ} (e : ℕ → Torus d → ℝ) (T : Finset (Fin N → ℕ))
    (hT : ∀ k ∈ T, ∀ i, k i ≤ J) (c : (Fin N → ℕ) → ℝ) (X : Config N d) :
    polyEval e (coefArr (J := J) T c) X = ∑ k ∈ T, c k * ∏ i, e (k i) (X i) := by
  unfold polyEval coefArr
  rw [← sum_castIdx T hT (fun k => c k * ∏ i, e (k i) (X i))]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : castIdx j ∈ T
  · simp only [h, if_true]; rfl
  · simp [h]

theorem sum_sq_coefArr {N J : ℕ} (T : Finset (Fin N → ℕ)) (hT : ∀ k ∈ T, ∀ i, k i ≤ J)
    (c : (Fin N → ℕ) → ℝ) : ∑ j, (coefArr (J := J) T c j) ^ 2 = ∑ k ∈ T, c k ^ 2 := by
  rw [← sum_castIdx T hT (fun k => c k ^ 2)]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold coefArr
  split_ifs <;> simp

theorem energy_coefArr {N J : ℕ} (lam : ℕ → ℝ) (T : Finset (Fin N → ℕ))
    (hT : ∀ k ∈ T, ∀ i, k i ≤ J) (c : (Fin N → ℕ) → ℝ) :
    ∑ j, (∑ i, lam (j i)) * (coefArr (J := J) T c j) ^ 2 =
      ∑ k ∈ T, (∑ i, lam (k i)) * c k ^ 2 := by
  rw [← sum_castIdx T hT (fun k => (∑ i, lam (k i)) * c k ^ 2)]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold coefArr
  split_ifs <;> simp [castIdx]

theorem spectralCoeff_coefArr {N J : ℕ} (lam : ℕ → ℝ) (L : ℝ) (T : Finset (Fin N → ℕ))
    (hL : ∀ k ∈ T, ∑ i, lam (k i) ≤ L) (c : (Fin N → ℕ) → ℝ) :
    SpectralCoeff lam L (coefArr (J := J) T c) := by
  intro j hj
  unfold coefArr at hj
  by_cases h : castIdx j ∈ T
  · exact hL _ h
  · simp [h] at hj

/-- Uniform bound on the spectral range: `lam k ≤ L → k ≤ JL`. -/
theorem exists_JL (lam : ℕ → ℝ) (hmono : Monotone lam) {d : ℕ} (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c)
    (hweyl : ∀ j : ℕ, 1 ≤ j → c * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam j) (L : ℝ) :
    ∃ JL : ℕ, ∀ k : ℕ, lam k ≤ L → k ≤ JL := by
  have hd0 : (0 : ℝ) < 2 / (d : ℝ) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have ht := (tendsto_rpow_atTop hd0).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop (L / c)).and (Filter.eventually_ge_atTop 1) |>.exists
  refine ⟨n, fun k hk => ?_⟩
  by_contra hkn
  push_neg at hkn
  have h1 := hweyl n hn.2
  have h2 : L < c * (n : ℝ) ^ (2 / (d : ℝ)) := by
    have := hn.1
    simp only [Function.comp] at this
    rwa [div_lt_iff₀ hc, mul_comm] at this
  have h3 := hmono hkn.le
  linarith

end SharpLSI.FL

end
