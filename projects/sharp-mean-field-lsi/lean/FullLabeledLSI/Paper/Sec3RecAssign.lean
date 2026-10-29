import Mathlib

/-!
# Proposition 3.2: integer group sizes and label assignments

For fractions `θ` with sum one, integers `n_s(N)` with `∑ₛ n_s(N) = N` and `n_s(N)/N → θ_s`, and for
any such sizes an assignment `a : Fin N → Fin q` with fibres of size `n_s`.
-/

open Filter Topology
open scoped BigOperators

namespace SharpLSI.FL

/-- Integer group sizes: floors for all groups but the last, the remainder for the last. -/
noncomputable def groupSize {q : ℕ} (s0 : Fin q) (θ : Fin q → ℝ) (N : ℕ) (s : Fin q) : ℕ :=
  if s = s0 then N - ∑ t ∈ Finset.univ.erase (s0), ⌊(N : ℝ) * θ t⌋₊
  else ⌊(N : ℝ) * θ s⌋₊

theorem sum_groupSize {q : ℕ} (s0 : Fin q) (θ : Fin q → ℝ) (hθ0 : ∀ s, 0 ≤ θ s) (hθ1 : ∑ s, θ s = 1)
    (N : ℕ) : ∑ s, groupSize s0 θ N s = N := by
  have hle : ∑ t ∈ Finset.univ.erase (s0), ⌊(N : ℝ) * θ t⌋₊ ≤ N := by
    have h1 : (∑ t ∈ Finset.univ.erase (s0), ⌊(N : ℝ) * θ t⌋₊ : ℝ) ≤
        ∑ t ∈ Finset.univ.erase (s0), (N : ℝ) * θ t :=
      Finset.sum_le_sum fun t _ => Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (hθ0 t))
    have h2 : ∑ t ∈ Finset.univ.erase (s0), (N : ℝ) * θ t ≤ N := by
      rw [← Finset.mul_sum]
      have : ∑ t ∈ Finset.univ.erase (s0), θ t ≤ 1 := by
        rw [← hθ1, ← Finset.sum_erase_add _ _ (Finset.mem_univ (s0))]
        linarith [hθ0 (s0)]
      nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact_mod_cast h1.trans h2
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (s0))]
  have hlast : groupSize s0 θ N (s0) =
      N - ∑ t ∈ Finset.univ.erase (s0), ⌊(N : ℝ) * θ t⌋₊ := by simp [groupSize]
  rw [Finset.sum_congr rfl (g := fun t => ⌊(N : ℝ) * θ t⌋₊) (fun t ht => by
    simp [groupSize, Finset.ne_of_mem_erase ht]), hlast]
  omega

theorem tendsto_groupSize {q : ℕ} (s0 : Fin q) (θ : Fin q → ℝ) (hθ0 : ∀ s, 0 ≤ θ s)
    (hθ1 : ∑ s, θ s = 1) (s : Fin q) :
    Tendsto (fun N : ℕ => (groupSize s0 θ N s : ℝ) / N) atTop (𝓝 (θ s)) := by
  have hfl : ∀ t, Tendsto (fun N : ℕ => (⌊(N : ℝ) * θ t⌋₊ : ℝ) / N) atTop (𝓝 (θ t)) := fun t => by
    have := (tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := θ t) (hθ0 t)).comp
      tendsto_natCast_atTop_atTop
    refine this.congr fun N => ?_
    simp [Function.comp, mul_comm]
  by_cases hs : s = s0
  · rw [hs]
    have hsum : ∀ N : ℕ, 1 ≤ N → (groupSize s0 θ N (s0) : ℝ) / N =
        1 - ∑ t ∈ Finset.univ.erase (s0), (⌊(N : ℝ) * θ t⌋₊ : ℝ) / N := fun N hN => by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      have hs := sum_groupSize s0 θ hθ0 hθ1 N
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (s0))] at hs
      have hrest : ∑ t ∈ Finset.univ.erase (s0), groupSize s0 θ N t =
          ∑ t ∈ Finset.univ.erase (s0), ⌊(N : ℝ) * θ t⌋₊ :=
        Finset.sum_congr rfl fun t ht => by simp [groupSize, Finset.ne_of_mem_erase ht]
      rw [hrest] at hs
      have : (groupSize s0 θ N (s0) : ℝ) = N - ∑ t ∈ Finset.univ.erase (s0),
          (⌊(N : ℝ) * θ t⌋₊ : ℝ) := by
        have h2 : (∑ t ∈ Finset.univ.erase (s0), (⌊(N : ℝ) * θ t⌋₊ : ℝ)) +
            (groupSize s0 θ N (s0) : ℝ) = N := by exact_mod_cast hs
        linarith
      rw [this, sub_div, Finset.sum_div, div_self hNpos.ne']
    have hlim : Tendsto (fun N : ℕ => 1 - ∑ t ∈ Finset.univ.erase (s0),
        (⌊(N : ℝ) * θ t⌋₊ : ℝ) / N) atTop (𝓝 (1 - ∑ t ∈ Finset.univ.erase (s0), θ t)) :=
      tendsto_const_nhds.sub (tendsto_finsetSum _ fun t _ => hfl t)
    have e : 1 - ∑ t ∈ Finset.univ.erase (s0), θ t = θ (s0) := by
      rw [← hθ1, ← Finset.sum_erase_add _ _ (Finset.mem_univ (s0))]; ring
    rw [e] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (hsum N hN).symm
  · simpa [groupSize, hs] using hfl s

/-- An assignment of `N` labels to groups with prescribed group sizes. -/
theorem exists_assign {q : ℕ} (n : Fin q → ℕ) (N : ℕ) (h : ∑ s, n s = N) :
    ∃ a : Fin N → Fin q, ∀ s, (Finset.univ.filter fun i => a i = s).card = n s := by
  have hc : Fintype.card (Σ s : Fin q, Fin (n s)) = Fintype.card (Fin N) := by
    simp [Fintype.card_sigma, h]
  let e : Fin N ≃ (Σ s : Fin q, Fin (n s)) := (Fintype.equivOfCardEq hc).symm
  refine ⟨fun i => (e i).1, fun s => ?_⟩
  rw [Finset.card_filter, Fintype.sum_equiv e (fun i => if (e i).1 = s then 1 else 0)
    (fun x : (Σ s : Fin q, Fin (n s)) => if x.1 = s then 1 else 0) (fun i => rfl),
    Fintype.sum_sigma]
  rw [Finset.sum_eq_single s (fun t _ ht => by simp [ht]) (by simp)]
  simp

end SharpLSI.FL
