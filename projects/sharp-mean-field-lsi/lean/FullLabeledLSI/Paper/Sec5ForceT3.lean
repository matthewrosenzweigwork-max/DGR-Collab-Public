import FullLabeledLSI.Paper.Sec5ForceMeas
import FullLabeledLSI.Paper.Sec5Products

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

section T3aux

/-- `E_{i ∈ Sᶜ}` of an `S`-independent function is the plain average over all labels. -/
theorem avg1R_const_S (N j : ℕ) (hj : j < N) (g : Fin N → ℝ) :
    avg1R N j (fun _ i => g i) = (N : ℝ)⁻¹ * ∑ i, g i := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  unfold avg1R
  have hS : ∀ S ∈ (Finset.univ : Finset (Fin (n+1))).powersetCard j,
      ((Sᶜ.card : ℕ) : ℝ)⁻¹ * ∑ i ∈ Sᶜ, g i = ((n + 1 - j : ℕ) : ℝ)⁻¹ * ∑ i ∈ Sᶜ, g i := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    rw [Finset.card_compl, Fintype.card_fin, hS.2]
  rw [Finset.sum_congr rfl hS, ← Finset.mul_sum]
  have h2 : ∑ S ∈ (Finset.univ : Finset (Fin (n+1))).powersetCard j, ∑ i ∈ Sᶜ, g i =
      ∑ i, g i * ((n.choose j : ℕ) : ℝ) := by
    have : ∀ S : Finset (Fin (n+1)), ∑ i ∈ Sᶜ, g i = ∑ i, if i ∉ S then g i else 0 := by
      intro S
      rw [← Finset.sum_filter]
      congr 1
      ext; simp
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 2
    have : ((Finset.univ : Finset (Fin (n+1))).powersetCard j).filter (fun S => i ∉ S) =
        (Finset.univ.erase i).powersetCard j := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun x hx => ?_, h1⟩
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        rintro rfl
        exact h2 hx
      · rintro ⟨h1, h2⟩
        refine ⟨h2, fun hi => ?_⟩
        have := h1 hi
        simp at this
    rw [this, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  rw [h2, ← Finset.sum_mul]
  have hk := Nat.choose_mul_succ_eq n j
  have hC : (0 : ℝ) < ((Nat.choose (n+1) j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hnj : (0 : ℝ) < ((n + 1 - j : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < n + 1 - j)
  have hk' : ((n.choose j : ℕ) : ℝ) * ((n : ℝ) + 1) =
      ((Nat.choose (n+1) j : ℕ) : ℝ) * ((n + 1 - j : ℕ) : ℝ) := by
    exact_mod_cast hk
  push_cast at hC ⊢
  field_simp
  linear_combination (∑ i, g i) * hk'

theorem card_injTuples_three (N : ℕ) : (injTuples N 3).card = N.descFactorial 3 := by
  classical
  have := card_injMaps_aux (α := Fin 3) (β := Fin N) Finset.univ
  simp only [Finset.mem_univ, implies_true, and_true, Finset.card_univ, Fintype.card_fin] at this
  exact this

theorem sum_injTuples_three {N : ℕ} (F : (Fin 3 → Fin N) → ℝ) :
    ∑ J ∈ injTuples N 3, F J =
      ∑ i, ∑ l, ∑ m, if (i ≠ l ∧ i ≠ m ∧ l ≠ m) then F ![i, l, m] else 0 := by
  classical
  unfold injTuples
  rw [Finset.sum_filter]
  let e : (Fin 3 → Fin N) ≃ Fin N × Fin N × Fin N :=
    { toFun := fun J => (J 0, J 1, J 2)
      invFun := fun p => ![p.1, p.2.1, p.2.2]
      left_inv := fun J => by funext a; fin_cases a <;> rfl
      right_inv := fun p => rfl }
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  have hi : Function.Injective (![i, l, m] : Fin 3 → Fin N) ↔ (i ≠ l ∧ i ≠ m ∧ l ≠ m) := by
    constructor
    · intro h
      refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
      · exact absurd (h (a₁ := 0) (a₂ := 1) (by simpa using e)) (by decide)
      · exact absurd (h (a₁ := 0) (a₂ := 2) (by simpa using e)) (by decide)
      · exact absurd (h (a₁ := 1) (a₂ := 2) (by simpa using e)) (by decide)
    · rintro ⟨h1, h2, h3⟩ a b hab
      fin_cases a <;> fin_cases b <;> simp_all
  have : e.symm (i, l, m) = ![i, l, m] := rfl
  simp only [this]
  by_cases h : (i ≠ l ∧ i ≠ m ∧ l ≠ m)
  · rw [if_pos (hi.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hi.1 h')), if_neg h]

end T3aux

section T3pt

variable {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}

theorem abs_sum_le_card_mul' {ι : Type*} (s : Finset ι) (f : ι → ℝ) (c : ℝ)
    (h : ∀ x ∈ s, |f x| ≤ c) : |∑ x ∈ s, f x| ≤ s.card * c := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ x ∈ s, |f x| ≤ ∑ x ∈ s, c := Finset.sum_le_sum h
    _ = s.card * c := by simp

/-- The injective-triple part of `N² ∑_k G_{i,k}²`. -/
noncomputable def T3main (bF : Torus d → Torus d → Fin d → ℝ) (N : ℕ) (X : Config N d)
    (i : Fin N) : ℝ :=
  ∑ l, ∑ m, if (i ≠ l ∧ i ≠ m ∧ l ≠ m) then A3 bF (X ∘ ![i, l, m]) else 0

theorem T3_pointwise (hB : ForceRep bF bΔ Bb) {N : ℕ} (hN : 1 ≤ N) (X : Config N d)
    (i : Fin N) :
    |(N : ℝ) ^ 2 * ∑ k, (Gpart bF bΔ N X i k) ^ 2 - T3main bF N X i| ≤
      4 * d * |Bb| ^ 2 * N := by
  set B := |Bb| with hBdef
  have hB0 : 0 ≤ B := abs_nonneg _
  set a : Fin N → Fin d → ℝ := fun l k => if l ≠ i then bF (X i) (X l) k else 0 with ha
  set b : Fin d → ℝ := fun k => bΔ (X i) k with hb
  have ha_le : ∀ l k, |a l k| ≤ B := by
    intro l k
    simp only [ha]
    split_ifs
    · exact (hB.bound _ _ _).trans (le_abs_self _)
    · simpa using hB0
  have hb_le : ∀ k, |b k| ≤ B := fun k => (hB.boundΔ _ _).trans (le_abs_self _)
  have hG : ∀ k, Gpart bF bΔ N X i k = (N : ℝ)⁻¹ * (∑ l, a l k + b k) := fun k => rfl
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : ∀ k, (N : ℝ) ^ 2 * (Gpart bF bΔ N X i k) ^ 2 =
      (∑ l, a l k ^ 2) + (∑ l, ∑ m, if l ≠ m then a l k * a m k else 0) +
        2 * (b k * ∑ l, a l k) + b k ^ 2 := by
    intro k
    have h1 : ∀ l, ∑ m, a l k * a m k =
        a l k ^ 2 + ∑ m, if l ≠ m then a l k * a m k else 0 := by
      intro l
      have h1 : ∑ m, a l k * a m k = ∑ m, ((if l = m then a l k * a m k else 0) +
          (if l ≠ m then a l k * a m k else 0)) :=
        Finset.sum_congr rfl fun m _ => by by_cases h : l = m <;> simp [h]
      rw [h1, Finset.sum_add_distrib, Finset.sum_ite_eq]
      simp [sq]
    have h2 : (∑ l, a l k) ^ 2 = ∑ l, a l k ^ 2 +
        ∑ l, ∑ m, if l ≠ m then a l k * a m k else 0 := by
      rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => h1 l
    rw [hG]
    have h3 : (N : ℝ) ^ 2 * ((N : ℝ)⁻¹ * (∑ l, a l k + b k)) ^ 2 = (∑ l, a l k + b k) ^ 2 := by
      field_simp
    rw [h3]
    linear_combination h2
  have hsum : (N : ℝ) ^ 2 * ∑ k, (Gpart bF bΔ N X i k) ^ 2 =
      (∑ k, ∑ l, a l k ^ 2) + (∑ k, ∑ l, ∑ m, if l ≠ m then a l k * a m k else 0) +
        2 * (∑ k, b k * ∑ l, a l k) + ∑ k, b k ^ 2 := by
    rw [Finset.mul_sum]
    simp_rw [hsq]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.mul_sum]
  have hP : (∑ k, ∑ l, ∑ m, if l ≠ m then a l k * a m k else 0) = T3main bF N X i := by
    rw [Finset.sum_comm]
    unfold T3main
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases h : (i ≠ l ∧ i ≠ m ∧ l ≠ m)
    · obtain ⟨h1, h2, h3⟩ := h
      rw [if_pos ⟨h1, h2, h3⟩]
      simp only [A3, ha, Function.comp, if_pos h3, if_pos (Ne.symm h1), if_pos (Ne.symm h2)]
      simp
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hlm : l = m
      · simp [hlm]
      · have : l = i ∨ m = i := by
          by_contra hc
          push_neg at hc
          exact h ⟨Ne.symm hc.1, Ne.symm hc.2, hlm⟩
        rcases this with h' | h' <;> simp [ha, h']
  have hE1 : |∑ k, ∑ l, a l k ^ 2| ≤ d * (N * B ^ 2) := by
    refine (abs_sum_le_card_mul' _ _ (N * B ^ 2) fun k _ => ?_).trans (by simp)
    refine (abs_sum_le_card_mul' _ _ (B ^ 2) fun l _ => ?_).trans (by simp)
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (ha_le l k) 2
  have hE2 : |2 * (∑ k, b k * ∑ l, a l k)| ≤ 2 * (d * (N * B ^ 2)) := by
    rw [abs_mul, abs_two]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (abs_sum_le_card_mul' _ _ (N * B ^ 2) fun k _ => ?_).trans (by simp)
    rw [abs_mul]
    have h1 : |∑ l, a l k| ≤ N * B := by
      refine (abs_sum_le_card_mul' _ _ B fun l _ => ha_le l k).trans (by simp)
    calc |b k| * |∑ l, a l k| ≤ B * (N * B) :=
          mul_le_mul (hb_le k) h1 (abs_nonneg _) hB0
      _ = N * B ^ 2 := by ring
  have hE3 : |∑ k, b k ^ 2| ≤ d * B ^ 2 := by
    refine (abs_sum_le_card_mul' _ _ (B ^ 2) fun k _ => ?_).trans (by simp)
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb_le k) 2
  rw [hsum, hP]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hdB : 0 ≤ (d : ℝ) * B ^ 2 := by positivity
  have key : (∑ k, ∑ l, a l k ^ 2) + T3main bF N X i + 2 * (∑ k, b k * ∑ l, a l k) +
      ∑ k, b k ^ 2 - T3main bF N X i =
      (∑ k, ∑ l, a l k ^ 2) + 2 * (∑ k, b k * ∑ l, a l k) + ∑ k, b k ^ 2 := by ring
  rw [key]
  calc _ ≤ |∑ k, ∑ l, a l k ^ 2| + |2 * (∑ k, b k * ∑ l, a l k)| + |∑ k, b k ^ 2| := by
        refine (abs_add_three _ _ _)
    _ ≤ d * (N * B ^ 2) + 2 * (d * (N * B ^ 2)) + d * B ^ 2 := by linarith
    _ ≤ 4 * d * B ^ 2 * N := by nlinarith

theorem measurable_A3_T3 (hB : ForceRep bF bΔ Bb) : Measurable (A3 bF) := by
  unfold A3
  have h0 : Measurable fun z : Fin 3 → Torus d => z 0 := measurable_pi_apply 0
  have h1 : Measurable fun z : Fin 3 → Torus d => z 1 := measurable_pi_apply 1
  have h2 : Measurable fun z : Fin 3 → Torus d => z 2 := measurable_pi_apply 2
  refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
  · exact (hB.meas k).comp (h0.prodMk h1)
  · exact (hB.meas k).comp (h0.prodMk h2)

theorem abs_A3_le_T3 (hB : ForceRep bF bΔ Bb) (z : Fin 3 → Torus d) :
    |A3 bF z| ≤ d * |Bb| ^ 2 := by
  unfold A3
  refine (abs_sum_le_card_mul' _ _ (|Bb| ^ 2) fun k _ => ?_).trans (le_of_eq (by simp))
  rw [abs_mul, sq]
  exact mul_le_mul ((hB.bound _ _ _).trans (le_abs_self _))
    ((hB.bound _ _ _).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)

theorem measurable_A3_comp (hB : ForceRep bF bΔ Bb) {N : ℕ} (J : Fin 3 → Fin N) :
    Measurable fun X : Config N d => A3 bF (X ∘ J) :=
  (measurable_A3_T3 hB).comp (measurable_pi_iff.2 fun l => measurable_pi_apply (J l))

theorem measurable_Gpart_T3 (hB : ForceRep bF bΔ Bb) (N : ℕ) (i : Fin N) (k : Fin d) :
    Measurable fun X : Config N d => Gpart bF bΔ N X i k := by
  unfold Gpart
  refine Measurable.const_mul (Measurable.add (Finset.measurable_sum _ fun l _ => ?_) ?_) _
  · have hi : Measurable fun X : Config N d => X i := measurable_pi_apply i
    have hl : Measurable fun X : Config N d => X l := measurable_pi_apply l
    have hm : Measurable fun X : Config N d => bF (X i) (X l) k :=
      (hB.meas k).comp (hi.prodMk hl)
    exact Measurable.ite (MeasurableSet.const _) hm measurable_const
  · exact (hB.measΔ k).comp (measurable_pi_apply i)

theorem measurable_T3term (hB : ForceRep bF bΔ Bb) {N : ℕ} (i l m : Fin N) :
    Measurable fun X : Config N d =>
      if (i ≠ l ∧ i ≠ m ∧ l ≠ m) then A3 bF (X ∘ ![i, l, m]) else 0 := by
  exact Measurable.ite (MeasurableSet.const _) (measurable_A3_comp hB _) measurable_const

theorem integrable_T3term (hB : ForceRep bF bΔ Bb) {N : ℕ} (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (i l m : Fin N) :
    Integrable (fun X : Config N d =>
      if (i ≠ l ∧ i ≠ m ∧ l ≠ m) then A3 bF (X ∘ ![i, l, m]) else 0) ν := by
  refine integrable_of_bdd ν (measurable_T3term hB i l m) (c := d * |Bb| ^ 2) fun X => ?_
  split_ifs
  · exact abs_A3_le_T3 hB _
  · simp only [abs_zero]
    positivity

theorem measurable_T3main (hB : ForceRep bF bΔ Bb) {N : ℕ} (i : Fin N) :
    Measurable fun X : Config N d => T3main bF N X i := by
  unfold T3main
  exact Finset.measurable_sum _ fun l _ => Finset.measurable_sum _ fun m _ =>
    measurable_T3term hB i l m

theorem integrable_T3main (hB : ForceRep bF bΔ Bb) {N : ℕ} (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (i : Fin N) :
    Integrable (fun X : Config N d => T3main bF N X i) ν := by
  unfold T3main
  exact integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun m _ =>
    integrable_T3term hB ν i l m

theorem integral_T3main (hB : ForceRep bF bΔ Bb) {N : ℕ} (ν : Measure (Config N d))
    [IsProbabilityMeasure ν] (i : Fin N) :
    ∫ X, T3main bF N X i ∂ν =
      ∑ l, ∑ m, if (i ≠ l ∧ i ≠ m ∧ l ≠ m) then ∫ X, A3 bF (X ∘ ![i, l, m]) ∂ν else 0 := by
  unfold T3main
  rw [integral_finsetSum _ (fun l _ => integrable_finsetSum _ fun m _ =>
    integrable_T3term hB ν i l m)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_finsetSum _ (fun m _ => integrable_T3term hB ν i l m)]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs
  · rfl
  · simp

theorem T3_int_close (hB : ForceRep bF bΔ Bb) {N : ℕ} (hN : 1 ≤ N)
    (ν : Measure (Config N d)) [IsProbabilityMeasure ν] (i : Fin N) :
    |(N : ℝ) ^ 2 * (∫ X, ∑ k, (Gpart bF bΔ N X i k) ^ 2 ∂ν) - ∫ X, T3main bF N X i ∂ν| ≤
      4 * d * |Bb| ^ 2 * N := by
  have hmH : Measurable fun X : Config N d => ∑ k, (Gpart bF bΔ N X i k) ^ 2 :=
    Finset.measurable_sum _ fun k _ => (measurable_Gpart_T3 hB N i k).pow_const 2
  have hD : Integrable (fun X : Config N d => (N : ℝ) ^ 2 * ∑ k, (Gpart bF bΔ N X i k) ^ 2 -
      T3main bF N X i) ν :=
    integrable_of_bdd ν ((hmH.const_mul _).sub (measurable_T3main hB i))
      (fun X => T3_pointwise hB hN X i)
  have h1 : ∫ X, (N : ℝ) ^ 2 * ∑ k, (Gpart bF bΔ N X i k) ^ 2 ∂ν =
      (∫ X, ((N : ℝ) ^ 2 * ∑ k, (Gpart bF bΔ N X i k) ^ 2 - T3main bF N X i) ∂ν) +
        ∫ X, T3main bF N X i ∂ν := by
    rw [← integral_add hD (integrable_T3main hB ν i)]
    congr 1
    funext X
    ring
  rw [integral_const_mul] at h1
  have h2 : (N : ℝ) ^ 2 * (∫ X, ∑ k, (Gpart bF bΔ N X i k) ^ 2 ∂ν) - ∫ X, T3main bF N X i ∂ν =
      ∫ X, ((N : ℝ) ^ 2 * ∑ k, (Gpart bF bΔ N X i k) ^ 2 - T3main bF N X i) ∂ν := by
    linarith
  rw [h2]
  exact abs_integral_le_of_prob ν _ (fun X => T3_pointwise hB hN X i)

end T3pt

/-- `E|G_I|²` is within `C/N` of `C₃`. -/
theorem T3_close {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}
    (hB : ForceRep bF bΔ Bb) :
    ∃ C : ℝ, ∀ (N : ℕ) (ν : Measure (Config N d)) [IsProbabilityMeasure ν], 3 ≤ N → ∀ j, j < N →
      |avg1R N j (fun S i => ∫ X, ∑ k : Fin d, (Gpart bF bΔ N X i k) ^ 2 ∂ν) -
          globTupleMean ν 3 (A3 bF)| ≤ C / N := by
  classical
  refine ⟨7 * d * |Bb| ^ 2, ?_⟩
  intro N ν _ hN j hj
  have hN1 : 1 ≤ N := by omega
  set B := |Bb| with hBdef
  have hB0 : 0 ≤ B := abs_nonneg _
  set f : Fin N → ℝ := fun i => ∫ X, ∑ k : Fin d, (Gpart bF bΔ N X i k) ^ 2 ∂ν with hf
  have e : avg1R N j (fun S i => ∫ X, ∑ k : Fin d, (Gpart bF bΔ N X i k) ^ 2 ∂ν) =
      (N : ℝ)⁻¹ * ∑ i, f i := avg1R_const_S N j hj f
  rw [e]
  have hx3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  set x : ℝ := (N : ℝ) with hx
  have hx0 : 0 < x := by linarith
  set T : Fin N → ℝ := fun i => ∫ X, T3main bF N X i ∂ν with hT
  have hδ : ∀ i, |x ^ 2 * f i - T i| ≤ 4 * d * B ^ 2 * x := fun i => T3_int_close hB hN1 ν i
  set g := globTupleMean ν 3 (A3 bF) with hg
  set D3 : ℝ := ((N.descFactorial 3 : ℕ) : ℝ) with hD3def
  have hD3 : D3 = x * (x - 1) * (x - 2) := by
    obtain ⟨n, hn⟩ : ∃ n, N = n + 3 := ⟨N - 3, by omega⟩
    have : N.descFactorial 3 = N * ((N - 1) * (N - 2)) := by
      subst hn
      simp [Nat.descFactorial_succ]
      ring
    rw [hD3def, this]
    push_cast [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_sub (by omega : 2 ≤ N)]
    ring
  have hD3pos : 0 < D3 := by
    rw [hD3]
    have : 0 < x - 1 := by linarith
    have : 0 < x - 2 := by linarith
    positivity
  have hP : ∑ i, T i = D3 * g := by
    have h1 : ∑ i, T i = ∑ J ∈ injTuples N 3, ∫ X, A3 bF (X ∘ J) ∂ν := by
      rw [sum_injTuples_three (fun J => ∫ X, A3 bF (X ∘ J) ∂ν)]
      exact Finset.sum_congr rfl fun i _ => integral_T3main hB ν i
    rw [h1, hg]
    unfold globTupleMean
    rw [← hD3def]
    field_simp
  have hgb : |g| ≤ d * B ^ 2 := by
    rw [hg]
    unfold globTupleMean
    rw [← hD3def, abs_mul, abs_inv, abs_of_pos hD3pos]
    have : |∑ J ∈ injTuples N 3, ∫ X, A3 bF (X ∘ J) ∂ν| ≤ D3 * (d * B ^ 2) := by
      refine (abs_sum_le_card_mul' _ _ (d * B ^ 2) fun J _ => ?_).trans
        (le_of_eq (by rw [card_injTuples_three]))
      exact abs_integral_le_of_prob ν _ (fun X => abs_A3_le_T3 hB _)
    rw [inv_mul_le_iff₀ hD3pos]
    exact this
  have hΔ : |∑ i, (x ^ 2 * f i - T i)| ≤ x * (4 * d * B ^ 2 * x) :=
    (abs_sum_le_card_mul' _ _ _ fun i _ => hδ i).trans (le_of_eq (by simp [hx]))
  have hmain : x⁻¹ * ∑ i, f i - g =
      (∑ i, (x ^ 2 * f i - T i)) / x ^ 3 + (D3 / x ^ 3 - 1) * g := by
    have : ∑ i, (x ^ 2 * f i - T i) = x ^ 2 * ∑ i, f i - D3 * g := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hP]
    rw [this]
    field_simp
    ring
  rw [hmain]
  have h1 : |(∑ i, (x ^ 2 * f i - T i)) / x ^ 3| ≤ 4 * d * B ^ 2 / x := by
    rw [abs_div, abs_of_pos (pow_pos hx0 3), div_le_div_iff₀ (by positivity) hx0]
    calc |∑ i, (x ^ 2 * f i - T i)| * x ≤ (x * (4 * d * B ^ 2 * x)) * x :=
          mul_le_mul_of_nonneg_right hΔ hx0.le
      _ = 4 * d * B ^ 2 * x ^ 3 := by ring
  have h2 : |D3 / x ^ 3 - 1| ≤ 3 / x := by
    have : D3 / x ^ 3 - 1 = -(3 * x - 2) / x ^ 2 := by
      rw [hD3]
      field_simp
      ring
    rw [this, abs_div, abs_neg, abs_of_pos (by linarith : 0 < 3 * x - 2),
      abs_of_pos (by positivity : 0 < x ^ 2), div_le_div_iff₀ (by positivity) hx0]
    nlinarith
  calc _ ≤ |(∑ i, (x ^ 2 * f i - T i)) / x ^ 3| + |(D3 / x ^ 3 - 1) * g| := abs_add_le _ _
    _ ≤ 4 * d * B ^ 2 / x + 3 / x * (d * B ^ 2) := by
        rw [abs_mul]
        exact add_le_add h1 (mul_le_mul h2 hgb (abs_nonneg _) (by positivity))
    _ = 7 * d * B ^ 2 / x := by ring

end SharpLSI.FL
