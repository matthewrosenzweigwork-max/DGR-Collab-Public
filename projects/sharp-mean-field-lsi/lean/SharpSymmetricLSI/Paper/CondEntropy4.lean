import SharpSymmetricLSI.Paper.CondEntropy3

/-!
# Lemma 5.1, (5.3)–(5.4) (Phase 3, lane D; R18)
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal

namespace SharpLSI

variable {d N : ℕ}

section
variable (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (ν : Measure (Config N d))
  [IsProbabilityMeasure ν]

theorem hCondT_mono (hsym : IsSymmetricMeasure ν)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {i i' : ℕ} (hii : i ≤ i') (hi' : i' < N) :
    hCondT ν μ i ≤ hCondT ν μ i' := by
  induction i' with
  | zero => have : i = 0 := by omega
            subst this; exact le_rfl
  | succ i' ih =>
    rcases Nat.eq_or_lt_of_le hii with h | h
    · rw [h]
    · refine (ih (by omega) (by omega)).trans ?_
      simp only [hCondT, dif_pos (show i' < N by omega), dif_pos hi']
      exact hCond_mono μ ν hsym hH hi'

theorem hCondT_ne_top (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) (i : ℕ) :
    hCondT ν μ i ≠ ⊤ := by
  by_cases hi : i < N
  · have := sum_hCondT_le μ ν hH (s := {i}) (by simp [hi])
    simp only [Finset.sum_singleton] at this
    exact ne_top_of_le_ne_top hH this
  · simp [hCondT, hi]

theorem DCondT_eq (hsym : IsSymmetricMeasure ν)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {j k : ℕ} (hj : j < N) (h : j + k ≤ N) :
    DCondT ν j k = (∑ a ∈ Finset.range k, hCondT ν μ (j + a)) - k * hCondT ν μ j := by
  have e := DCond_add μ ν hsym hH hj h
  simp only [DCondT, dif_pos (show j < N ∧ j + k ≤ N from ⟨hj, h⟩)]
  have hk : (k : ℝ≥0∞) * hCondT ν μ j ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (hCondT_ne_top μ ν hH j)
  simp only [hCondT, dif_pos hj] at hk ⊢
  exact ENNReal.eq_sub_of_add_eq hk e.symm

theorem DCondT_le (hsym : IsSymmetricMeasure ν)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {j k : ℕ} (hj : j < N) (h : j + k ≤ N)
    (hk : 1 ≤ k) :
    DCondT ν j k ≤ k * (hCondT ν μ (j + k - 1) - hCondT ν μ j) := by
  rw [DCondT_eq μ ν hsym hH hj h, ENNReal.mul_sub (fun _ _ => by simp)]
  refine tsub_le_tsub_right ?_ _
  calc ∑ a ∈ Finset.range k, hCondT ν μ (j + a) ≤ ∑ _a ∈ Finset.range k, hCondT ν μ (j + k - 1) :=
        Finset.sum_le_sum fun a ha => by
          simp only [Finset.mem_range] at ha
          exact hCondT_mono μ ν hsym hH (by omega) (by omega)
    _ = k * hCondT ν μ (j + k - 1) := by simp

end

/-- The real-number telescoping estimate behind (5.4). -/
theorem telescope_bound {r : ℕ → ℝ} {N M k : ℕ} (hr0 : ∀ i, 0 ≤ r i)
    (hmono : ∀ i i', i ≤ i' → i' < N → r i ≤ r i') (hMN : M ≤ N) (hkM : k ≤ M) (hk : 1 ≤ k) :
    ∑ j ∈ Finset.range (N - M), (k : ℝ) * (r (j + k - 1) - r j) ≤
      (k * (k - 1) : ℝ) / ((M : ℝ) - k + 2) * ∑ i ∈ Finset.range N, r i := by
  rcases Nat.eq_or_lt_of_le hk with hk1 | hk2
  · subst hk1
    simp
  set ℓ := N - M
  set m := k - 1
  have hm : (m : ℝ) = (k : ℝ) - 1 := by simp [m, Nat.cast_sub hk]
  -- telescoping
  have htel : ∑ j ∈ Finset.range ℓ, (r (j + k - 1) - r j) =
      ∑ i ∈ Finset.range m, (r (ℓ + i) - r i) := by
    have e1 : ∀ j, j + k - 1 = j + m := fun j => by omega
    simp_rw [e1]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have A := Finset.sum_range_add r m ℓ
    have B := Finset.sum_range_add r ℓ m
    rw [add_comm m ℓ] at A
    have C : ∑ x ∈ Finset.range ℓ, r (m + x) = ∑ j ∈ Finset.range ℓ, r (j + m) :=
      Finset.sum_congr rfl fun x _ => by rw [add_comm]
    linarith
  have hlast : ∀ i ∈ Finset.range m, r (ℓ + i) - r i ≤ r (ℓ + m - 1) := fun i hi => by
    simp only [Finset.mem_range] at hi
    have := hmono (ℓ + i) (ℓ + m - 1) (by omega) (by omega)
    linarith [hr0 i]
  have hsum1 : ∑ j ∈ Finset.range ℓ, (r (j + k - 1) - r j) ≤ m * r (ℓ + m - 1) := by
    rw [htel]
    calc ∑ i ∈ Finset.range m, (r (ℓ + i) - r i) ≤ ∑ _i ∈ Finset.range m, r (ℓ + m - 1) :=
          Finset.sum_le_sum hlast
      _ = m * r (ℓ + m - 1) := by simp
  -- the last terms
  have hden : (0 : ℝ) < (M : ℝ) - k + 2 := by
    have : (k : ℝ) ≤ M := by exact_mod_cast hkM
    linarith
  have hcount : ((M : ℝ) - k + 2) * r (ℓ + m - 1) ≤ ∑ i ∈ Finset.range N, r i := by
    set s0 := ℓ + m - 1
    have hs : (Finset.Ico s0 N).card = M - k + 2 := by
      rw [Nat.card_Ico]; omega
    have hcast : ((M - k + 2 : ℕ) : ℝ) = (M : ℝ) - k + 2 := by
      rw [Nat.cast_add, Nat.cast_sub hkM]; norm_num
    calc ((M : ℝ) - k + 2) * r s0 = ∑ _i ∈ Finset.Ico s0 N, r s0 := by
          rw [Finset.sum_const, hs, nsmul_eq_mul, hcast]
      _ ≤ ∑ i ∈ Finset.Ico s0 N, r i := Finset.sum_le_sum fun i hi => by
          simp only [Finset.mem_Ico] at hi
          exact hmono s0 i hi.1 hi.2
      _ ≤ ∑ i ∈ Finset.range N, r i := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) (fun i _ _ => hr0 i)
          simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢; omega
  rw [← Finset.mul_sum]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc (k : ℝ) * ∑ j ∈ Finset.range ℓ, (r (j + k - 1) - r j) ≤ k * (m * r (ℓ + m - 1)) :=
        mul_le_mul_of_nonneg_left hsum1 hk0
    _ ≤ k * m * (∑ i ∈ Finset.range N, r i / ((M : ℝ) - k + 2)) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hm0) hk0
        rw [← Finset.sum_div, le_div_iff₀ hden]; linarith
    _ = _ := by rw [← Finset.sum_div, hm]; ring

/-- **Lemma 5.1, (5.3)–(5.4).** -/
theorem summed_dependence_aux (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (ν : Measure (Config N d)) [IsProbabilityMeasure ν] (hsym : IsSymmetricMeasure ν)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) :
    (∀ j, j + 1 < N → hCondT ν μ j ≤ hCondT ν μ (j + 1)) ∧
    ∑ j ∈ Finset.range N, hCondT ν μ j = klDiv ν (Measure.pi fun _ : Fin N => μ) ∧
    (∀ j k, j < N → j + k ≤ N → 1 ≤ k →
      DCondT ν j k = (∑ a ∈ Finset.range k, hCondT ν μ (j + a)) - k * hCondT ν μ j ∧
      DCondT ν j k ≤ k * (hCondT ν μ (j + k - 1) - hCondT ν μ j)) ∧
    (∀ M k, M ≤ N → k ≤ M → 1 ≤ k →
      ∑ j ∈ Finset.range (N - M), DCondT ν j k ≤
        ((k * (k - 1) : ℕ) : ℝ≥0∞) / ((M - k + 2 : ℕ) : ℝ≥0∞) *
          klDiv ν (Measure.pi fun _ : Fin N => μ)) := by
  refine ⟨fun j hj => hCondT_mono μ ν hsym hH (by omega) hj, chain_rule μ ν hH,
    fun j k hj h hk => ⟨DCondT_eq μ ν hsym hH hj h, DCondT_le μ ν hsym hH hj h hk⟩, ?_⟩
  intro M k hMN hkM hk
  set r : ℕ → ℝ := fun i => (hCondT ν μ i).toReal with hr
  have hfin := hCondT_ne_top μ ν hH
  have hr0 : ∀ i, 0 ≤ r i := fun i => ENNReal.toReal_nonneg
  have hmono : ∀ i i', i ≤ i' → i' < N → r i ≤ r i' := fun i i' h1 h2 =>
    ENNReal.toReal_mono (hfin _) (hCondT_mono μ ν hsym hH h1 h2)
  have hb := telescope_bound hr0 hmono hMN hkM hk
  have hterm : ∀ j ∈ Finset.range (N - M), DCondT ν j k ≤
      ENNReal.ofReal ((k : ℝ) * (r (j + k - 1) - r j)) := fun j hj => by
    simp only [Finset.mem_range] at hj
    refine (DCondT_le μ ν hsym hH (by omega) (by omega) hk).trans (le_of_eq ?_)
    have hle : hCondT ν μ j ≤ hCondT ν μ (j + k - 1) :=
      hCondT_mono μ ν hsym hH (by omega) (by omega)
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast, hr]
    congr 1
    rw [← ENNReal.toReal_sub_of_le hle (hfin _), ENNReal.ofReal_toReal]
    exact ne_top_of_le_ne_top (hfin _) tsub_le_self
  have hnn : ∀ j ∈ Finset.range (N - M), 0 ≤ (k : ℝ) * (r (j + k - 1) - r j) := fun j hj => by
    simp only [Finset.mem_range] at hj
    have := hmono j (j + k - 1) (by omega) (by omega)
    exact mul_nonneg (Nat.cast_nonneg k) (by linarith)
  have hden : (0 : ℝ) < (M : ℝ) - k + 2 := by
    have : (k : ℝ) ≤ M := by exact_mod_cast hkM
    linarith
  have hH' : klDiv ν (Measure.pi fun _ : Fin N => μ) = ENNReal.ofReal (∑ i ∈ Finset.range N, r i) := by
    rw [← chain_rule μ ν hH, hr, ← ENNReal.toReal_sum (fun i _ => hfin i), ENNReal.ofReal_toReal]
    rw [chain_rule μ ν hH]; exact hH
  calc ∑ j ∈ Finset.range (N - M), DCondT ν j k
      ≤ ∑ j ∈ Finset.range (N - M), ENNReal.ofReal ((k : ℝ) * (r (j + k - 1) - r j)) :=
        Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (∑ j ∈ Finset.range (N - M), (k : ℝ) * (r (j + k - 1) - r j)) :=
        (ENNReal.ofReal_sum_of_nonneg hnn).symm
    _ ≤ ENNReal.ofReal ((k * (k - 1) : ℝ) / ((M : ℝ) - k + 2) * ∑ i ∈ Finset.range N, r i) :=
        ENNReal.ofReal_le_ofReal hb
    _ = _ := by
        rw [hH', ENNReal.ofReal_mul (div_nonneg (by
          have : (1 : ℝ) ≤ k := by exact_mod_cast hk
          nlinarith) hden.le), ENNReal.ofReal_div_of_pos hden]
        congr 2
        · rw [← ENNReal.ofReal_natCast]; congr 1; push_cast [Nat.cast_sub hk]; ring
        · rw [← ENNReal.ofReal_natCast]; congr 1; push_cast [Nat.cast_sub hkM]; ring

end SharpLSI
