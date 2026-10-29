import Mathlib

/-!
# Section 5 infrastructure, part 5: the counting argument of (5.11)

An abstract statement about nondecreasing sequences: if `∑_{a<N} h_a = H₀ < ∞`, `h` is nondecreasing
on `0..N-1`, and `d_j + k h_j = ∑_{a<k} h_{j+a}` for `j + k ≤ N`, then
`∑_{j<N-M} d_j ≤ k(k-1) H₀/(M-k+2)` for `1 ≤ k ≤ M ≤ N`.
-/

open scoped ENNReal

namespace SharpLSI.FL

theorem mono_of_step (g : ℕ → ℝ) (N : ℕ) (hmono : ∀ a, a + 2 ≤ N → g a ≤ g (a + 1)) :
    ∀ a b, a ≤ b → b < N → g a ≤ g b := by
  intro a b hab
  induction hab with
  | refl => intro _; exact le_rfl
  | @step m hle ih => intro hb; exact (ih (by omega)).trans (hmono _ (by omega))

theorem sum_diff_shift (g : ℕ → ℝ) (k' ℓ : ℕ) :
    ∑ j ∈ Finset.range ℓ, (g (j + k') - g j) =
      ∑ x ∈ Finset.range k', g (ℓ + x) - ∑ x ∈ Finset.range k', g x := by
  have h1 := Finset.sum_range_add g k' ℓ
  have h2 := Finset.sum_range_add g ℓ k'
  rw [Finset.sum_sub_distrib]
  have h3 : ∑ j ∈ Finset.range ℓ, g (j + k') = ∑ j ∈ Finset.range ℓ, g (k' + j) :=
    Finset.sum_congr rfl (fun j _ => by rw [add_comm])
  rw [h3, add_comm k' ℓ] at *
  linarith

theorem real_core (N M k' : ℕ) (hkM : k' + 1 ≤ M) (hMN : M ≤ N) (g e : ℕ → ℝ)
    (hg0 : ∀ a, 0 ≤ g a)
    (hmono : ∀ a, a + 2 ≤ N → g a ≤ g (a + 1))
    (hd : ∀ j, j + (k' + 1) ≤ N →
      e j + ((k' : ℝ) + 1) * g j = ∑ a ∈ Finset.range (k' + 1), g (j + a)) :
    ∑ j ∈ Finset.range (N - M), e j ≤
      ((k' : ℝ) + 1) * k' * (∑ a ∈ Finset.range N, g a) / ((M - (k' + 1) + 2 : ℕ) : ℝ) := by
  have hmono' := mono_of_step g N hmono
  have h1 : ∑ j ∈ Finset.range (N - M), e j ≤
      ∑ j ∈ Finset.range (N - M), ((k' : ℝ) + 1) * (g (j + k') - g j) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_range] at hj
    have h := hd j (by omega)
    have h' : ∑ a ∈ Finset.range (k' + 1), g (j + a) ≤
        ∑ a ∈ Finset.range (k' + 1), g (j + k') := by
      apply Finset.sum_le_sum
      intro a ha
      rw [Finset.mem_range] at ha
      exact hmono' _ _ (by omega) (by omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h'
    push_cast at h'
    nlinarith
  rw [← Finset.mul_sum, sum_diff_shift] at h1
  have h2 : 0 ≤ ∑ x ∈ Finset.range k', g x := Finset.sum_nonneg (fun x _ => hg0 x)
  have hk1 : (0 : ℝ) ≤ (k' : ℝ) + 1 := by positivity
  have h3 : ∑ j ∈ Finset.range (N - M), e j ≤
      ((k' : ℝ) + 1) * ∑ x ∈ Finset.range k', g (N - M + x) := by
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hk1
  have hG : 0 ≤ ∑ a ∈ Finset.range N, g a := Finset.sum_nonneg (fun x _ => hg0 x)
  rcases Nat.eq_zero_or_pos k' with rfl | hpos
  · simp at h3 ⊢
    exact h3
  · obtain ⟨m, rfl⟩ : ∃ m, k' = m + 1 := ⟨k' - 1, by omega⟩
    have hcN : N - M + m < N := by omega
    have h4 : ∑ x ∈ Finset.range (m + 1), g (N - M + x) ≤
        ∑ x ∈ Finset.range (m + 1), g (N - M + m) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [Finset.mem_range] at ha
      exact hmono' _ _ (by omega) hcN
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h4
    have h5 : ((M - m : ℕ) : ℝ) * g (N - M + m) ≤ ∑ a ∈ Finset.range N, g a := by
      have hsub : Finset.Ico (N - M + m) N ⊆ Finset.range N := by
        intro a ha
        rw [Finset.mem_Ico] at ha
        rw [Finset.mem_range]; omega
      calc ((M - m : ℕ) : ℝ) * g (N - M + m)
          = ∑ a ∈ Finset.Ico (N - M + m) N, g (N - M + m) := by
            have hcnt : N - (N - M + m) = M - m := by omega
            rw [Finset.sum_const, Nat.card_Ico, hcnt, nsmul_eq_mul]
        _ ≤ ∑ a ∈ Finset.Ico (N - M + m) N, g a := by
            apply Finset.sum_le_sum
            intro a ha
            rw [Finset.mem_Ico] at ha
            exact hmono' _ _ ha.1 ha.2
        _ ≤ ∑ a ∈ Finset.range N, g a :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => hg0 a)
    have hMm : M - (m + 1 + 1) + 2 = M - m := by omega
    rw [hMm]
    have hpos' : (0 : ℝ) < ((M - m : ℕ) : ℝ) := by
      have : 0 < M - m := by omega
      exact_mod_cast this
    rw [le_div_iff₀ hpos']
    push_cast at h3 h4 ⊢
    have h6 : ((m : ℝ) + 1 + 1) * ((m : ℝ) + 1) * (((M - m : ℕ) : ℝ) * g (N - M + m)) ≤
        ((m : ℝ) + 1 + 1) * ((m : ℝ) + 1) * ∑ a ∈ Finset.range N, g a :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    have h7 : ((m : ℝ) + 1 + 1) * ∑ x ∈ Finset.range (m + 1), g (N - M + x) ≤
        ((m : ℝ) + 1 + 1) * (((m : ℝ) + 1) * g (N - M + m)) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h8 := mul_le_mul_of_nonneg_right (h3.trans h7) hpos'.le
    nlinarith

theorem sum_d_le_of_chain (N M k : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) (hMN : M ≤ N)
    (h dk : ℕ → ℝ≥0∞) (H₀ : ℝ≥0∞) (hfin : H₀ ≠ ⊤)
    (hsum : ∑ a ∈ Finset.range N, h a = H₀)
    (hmono : ∀ a, a + 2 ≤ N → h a ≤ h (a + 1))
    (hd : ∀ j, j + k ≤ N → dk j + k * h j = ∑ a ∈ Finset.range k, h (j + a)) :
    ∑ j ∈ Finset.range (N - M), dk j ≤
      (k * (k - 1) : ℝ≥0∞) * H₀ / ((M - k + 2 : ℕ) : ℝ≥0∞) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hle : ∀ a, a < N → h a ≤ H₀ := fun a ha => by
    rw [← hsum]
    exact Finset.single_le_sum (f := h) (fun _ _ => bot_le) (Finset.mem_range.2 ha)
  have hfa : ∀ a, a < N → h a ≠ ⊤ := fun a ha => ne_top_of_le_ne_top hfin (hle a ha)
  have hdfin : ∀ j, j + (k' + 1) ≤ N → dk j ≠ ⊤ := by
    intro j hj
    have := hd j hj
    have hs : ∑ a ∈ Finset.range (k' + 1), h (j + a) ≠ ⊤ :=
      ENNReal.sum_ne_top.2 (fun a ha => hfa _ (by rw [Finset.mem_range] at ha; omega))
    rw [← this] at hs
    exact ne_top_of_le_ne_top hs le_self_add
  have hreal : ∀ j, j + (k' + 1) ≤ N →
      (dk j).toReal + ((k' : ℝ) + 1) * (h j).toReal =
        ∑ a ∈ Finset.range (k' + 1), (h (j + a)).toReal := by
    intro j hj
    have := congrArg ENNReal.toReal (hd j hj)
    rw [ENNReal.toReal_add (hdfin j hj)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hfa j (by omega))),
      ENNReal.toReal_mul,
      ENNReal.toReal_sum (fun a ha => hfa _ (by rw [Finset.mem_range] at ha; omega))] at this
    push_cast at this
    exact this
  have hcore := real_core N M k' hkM hMN (fun a => (h a).toReal) (fun j => (dk j).toReal)
    (fun a => ENNReal.toReal_nonneg)
    (fun a ha => ENNReal.toReal_mono (hfa (a + 1) (by omega)) (hmono a ha)) hreal
  have hG : ∑ a ∈ Finset.range N, (h a).toReal = H₀.toReal := by
    rw [← hsum, ENNReal.toReal_sum (fun a ha => hfa a (Finset.mem_range.1 ha))]
  have hS : ∑ j ∈ Finset.range (N - M), dk j ≠ ⊤ :=
    ENNReal.sum_ne_top.2 (fun j hj => hdfin j (by rw [Finset.mem_range] at hj; omega))
  have hkk : ((k' + 1 : ℕ) : ℝ≥0∞) * (((k' + 1 : ℕ) : ℝ≥0∞) - 1) = (((k' + 1) * k' : ℕ) : ℝ≥0∞) := by
    push_cast
    rw [ENNReal.add_sub_cancel_right ENNReal.one_ne_top]
  rw [hkk]
  have hd0 : ((M - (k' + 1) + 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    have : M - (k' + 1) + 2 ≠ 0 := by omega
    exact_mod_cast this
  have hR : (((k' + 1) * k' : ℕ) : ℝ≥0∞) * H₀ / ((M - (k' + 1) + 2 : ℕ) : ℝ≥0∞) ≠ ⊤ := by
    rw [div_eq_mul_inv]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hfin)
      (ENNReal.inv_ne_top.2 hd0)
  rw [← ENNReal.toReal_le_toReal hS hR, ENNReal.toReal_sum (fun j hj => hdfin j (by rw [Finset.mem_range] at hj; omega)),
    ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  rw [hG] at hcore
  push_cast at hcore ⊢
  exact hcore

end SharpLSI.FL
