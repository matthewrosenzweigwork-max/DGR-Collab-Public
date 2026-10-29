import FullLabeledLSI.Infra.RevealChain
import FullLabeledLSI.Infra.RevealAvg
import FullLabeledLSI.Infra.RevealSeq

/-!
# Lemma 5.3 (random chain rule): assembly

`h_j`, `d_{j,k}` of F04 are the uniform averages `avg1`, `avgK` of `gRev`, `DRev`; the pointwise
identities `GRev_eq_DRev_add`, `GRev_chain`, `DRev_pair_add` (no finiteness needed) average to
(5.9)-(5.10); (5.11) is `sum_d_le_of_chain`.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

section Avg

variable {N : ℕ}

theorem avgK_add {j k : ℕ} (F G : Finset (Fin N) → (Fin k → Fin N) → ℝ≥0∞) :
    avgK N j k (fun S I => F S I + G S I) = avgK N j k F + avgK N j k G := by
  unfold avgK
  simp only [Finset.sum_add_distrib, mul_add]

theorem avgK_sum {j k : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → Finset (Fin N) → (Fin k → Fin N) → ℝ≥0∞) :
    avgK N j k (fun S I => ∑ a ∈ s, F a S I) = ∑ a ∈ s, avgK N j k (F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [avgK]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [avgK_add, ih]

end Avg

section Chain

variable {d N : ℕ} (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
  (μ : Measure (Torus d)) [IsProbabilityMeasure μ]

theorem hRev_eq_avg1' {j : ℕ} (hj : j < N) : hRev ν μ j = avg1 N j (gRev ν μ) :=
  hRev_eq_avg1 ν μ hj

theorem dRev_eq_avgK' {j k : ℕ} (hjk : j + k ≤ N) :
    dRev ν j k = avgK N j k (fun S I => DRev ν S I) :=
  dRev_eq_avgK ν hjk

/-- (5.10) -/
theorem chain_k {j k : ℕ} (hk : 1 ≤ k) (hjk : j + k ≤ N) :
    dRev ν j k + k * hRev ν μ j = ∑ a ∈ Finset.range k, hRev ν μ (j + a) := by
  have hjN : j < N := by omega
  have h1 : avgK N j k (fun S I => DRev ν S I + ∑ l, gRev ν μ S (I l)) =
      avgK N j k (fun S I => ∑ a : Fin k, gRev ν μ (preSet S I a.val) (I a)) := by
    congr 1
    funext S I
    rw [← GRev_eq_DRev_add, ← GRev_chain]
  rw [avgK_add, avgK_sum, avgK_sum] at h1
  have h2 : ∀ l : Fin k, avgK N j k (fun S I => gRev ν μ S (I l)) = hRev ν μ j := fun l => by
    rw [avgK_marg hjk l, hRev_eq_avg1' ν μ hjN]
  have h3 : ∀ a : Fin k, avgK N j k (fun S I => gRev ν μ (preSet S I a.val) (I a)) =
      hRev ν μ (j + a.val) := fun a => by
    have := avgK_pre (N := N) hjk a.isLt (gRev ν μ)
    rw [hRev_eq_avg1' ν μ (by omega)]
    exact this
  simp only [h2, h3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  rw [dRev_eq_avgK' ν hjk, h1]
  rw [← Finset.sum_range (fun a => hRev ν μ (j + a))]

theorem preSet_one (S : Finset (Fin N)) (I : Fin 2 → Fin N) : preSet S I 1 = insert (I 0) S := by
  ext t
  simp only [preSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert]
  constructor
  · rintro (h | ⟨l, hl, rfl⟩)
    · exact Or.inr h
    · left
      have : l = 0 := by ext; simp at hl ⊢; omega
      rw [this]
  · rintro (rfl | h)
    · right; exact ⟨0, by simp, rfl⟩
    · exact Or.inl h

/-- (5.9), second identity -/
theorem chain_step {j : ℕ} (hj : j + 2 ≤ N) :
    hRev ν μ (j + 1) = hRev ν μ j + dRev ν j 2 := by
  have hjN : j < N := by omega
  have h1 : avgK N j 2 (fun S I => DRev ν S I + gRev ν μ S (I 1)) =
      avgK N j 2 (fun S I => gRev ν μ (preSet S I 1) (I ⟨1, by norm_num⟩)) := by
    congr 1
    funext S I
    have hI : I = ![I 0, I 1] := by
      funext x; fin_cases x <;> rfl
    rw [preSet_one]
    have := DRev_pair_add ν μ S (I 0) (I 1)
    rw [← hI] at this
    exact this
  rw [avgK_add] at h1
  have h2 := avgK_marg (N := N) (j := j) (k := 2) hj (1 : Fin 2) (gRev ν μ)
  have h3 := avgK_pre (N := N) hj (a := 1) (by norm_num) (gRev ν μ)
  rw [h2, h3, ← dRev_eq_avgK' ν hj] at h1
  rw [hRev_eq_avg1' ν μ hjN, hRev_eq_avg1' ν μ (by omega : j + 1 < N)]
  rw [← h1, add_comm]

/-- (5.9), first identity -/
theorem chain_sum :
    ∑ j ∈ Finset.range N, hRev ν μ j = klDiv ν (Measure.pi fun _ : Fin N => μ) := by
  have hc : avgK N 0 N (fun S I => GRev ν μ S I) = klDiv ν (Measure.pi fun _ : Fin N => μ) := by
    rw [← avgK_const (N := N) (j := 0) (k := N) (by omega)
      (klDiv ν (Measure.pi fun _ : Fin N => μ))]
    unfold avgK
    congr 1
    refine Finset.sum_congr rfl fun S hS => ?_
    have hS0 : S = ∅ := Finset.card_eq_zero.1 (Finset.mem_powersetCard.1 hS).2
    subst hS0
    congr 1
    refine Finset.sum_congr rfl fun I hI => ?_
    have hinj : Function.Injective I := by
      have := (Finset.mem_filter.1 hI).2
      exact this.1
    let σ : Equiv.Perm (Fin N) := Equiv.ofBijective I (Finite.injective_iff_bijective.1 hinj)
    have : I = (σ : Fin N → Fin N) := rfl
    rw [this]
    exact GRev_perm ν μ σ
  rw [← hc]
  have h1 : avgK N 0 N (fun S I => GRev ν μ S I) =
      avgK N 0 N (fun S I => ∑ a : Fin N, gRev ν μ (preSet S I a.val) (I a)) := by
    congr 1; funext S I; exact GRev_chain ν μ S I
  rw [h1, avgK_sum]
  have h3 : ∀ a : Fin N, avgK N 0 N (fun S I => gRev ν μ (preSet S I a.val) (I a)) =
      hRev ν μ a.val := fun a => by
    have := avgK_pre (N := N) (j := 0) (k := N) (by omega) a.isLt (gRev ν μ)
    rw [hRev_eq_avg1' ν μ a.isLt]
    simpa using this
  simp only [h3]
  exact (Fin.sum_univ_eq_sum_range (fun a => hRev ν μ a) N).symm

theorem hRev_mono {j : ℕ} (hj : j + 2 ≤ N) : hRev ν μ j ≤ hRev ν μ (j + 1) := by
  rw [chain_step ν μ hj]; exact le_self_add

/-- (5.11) -/
theorem chain_sum_d (k M : ℕ) (hkM : k ≤ M) (hMN : M ≤ N) :
    ∑ j ∈ Finset.range (N - M), dRev ν j k ≤
      (k * (k - 1) : ℝ≥0∞) * klDiv ν (Measure.pi fun _ : Fin N => μ) / ((M - k + 2 : ℕ) : ℝ≥0∞) := by
  by_cases hk : k ≤ 1
  · have : ∀ j ∈ Finset.range (N - M), dRev ν j k = 0 := fun j hj => by
      have hjk : j + k ≤ N := by have := Finset.mem_range.1 hj; omega
      rw [dRev_eq_avgK' ν hjk]
      unfold avgK
      have h0 : ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
          ((Nat.descFactorial (N - j) k : ℝ≥0∞)⁻¹) * ∑ I ∈ distinctTuples S k, DRev ν S I = 0 :=
        Finset.sum_eq_zero fun S _ => by
          rw [Finset.sum_eq_zero (fun I _ => DRev_eq_zero_of_le_one ν S hk I), mul_zero]
      rw [h0, mul_zero]
    rw [Finset.sum_eq_zero this]; exact bot_le
  · push_neg at hk
    by_cases hH : klDiv ν (Measure.pi fun _ : Fin N => μ) = ⊤
    · rw [hH, ENNReal.mul_top, ENNReal.top_div_of_ne_top (by simp)]
      · exact le_top
      · have h1 : (1 : ℝ≥0∞) < k := by exact_mod_cast hk
        have h2 : (0 : ℝ≥0∞) < (k - 1) := by
          have : (1:ℝ≥0∞) < k := h1
          exact tsub_pos_of_lt this
        exact mul_ne_zero (ne_of_gt (lt_trans zero_lt_one h1)) h2.ne'
    · exact sum_d_le_of_chain N M k (by omega) hkM hMN (hRev ν μ) (fun j => dRev ν j k) _ hH
        (chain_sum ν μ) (fun a ha => hRev_mono ν μ ha)
        (fun j hj => chain_k ν μ (by omega) hj)

end Chain

end SharpLSI.FL
