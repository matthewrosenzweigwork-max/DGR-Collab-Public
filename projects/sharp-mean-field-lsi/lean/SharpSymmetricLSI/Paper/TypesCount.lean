import SharpSymmetricLSI.Paper.TorusCells

/-!
# Method of types: counting (Phase 3, lane D; R5)

For `σ : Fin N → C` the type `p_σ(a) = #{i | σ i = a}/N`:
`∏ᵢ p_σ(σ i) = exp(N ∑ₐ p_σ(a) log p_σ(a))` and `∑_σ ∏ᵢ p_σ(σ i) ≤ (N+1)^{|C|}`.
-/

open MeasureTheory Set Filter Finset
open scoped ENNReal

namespace SharpLSI

variable {C : Type*} [Fintype C] [DecidableEq C] {N : ℕ}

/-- `#{i | σ i = a}`. -/
def cnt (σ : Fin N → C) (a : C) : ℕ := (univ.filter fun i => σ i = a).card

theorem cnt_le (σ : Fin N → C) (a : C) : cnt σ a ≤ N := by
  unfold cnt
  exact (card_filter_le _ _).trans (by simp)

theorem sum_comp_eq_cnt {M : Type*} [AddCommMonoid M] (σ : Fin N → C) (f : C → M) :
    ∑ i, f (σ i) = ∑ a, cnt σ a • f a := by
  rw [← sum_fiberwise univ σ (fun i => f (σ i))]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2], sum_const]
  rfl

theorem prod_comp_eq_cnt {M : Type*} [CommMonoid M] (σ : Fin N → C) (f : C → M) :
    ∏ i, f (σ i) = ∏ a, f a ^ cnt σ a := by
  rw [← prod_fiberwise univ σ (fun i => f (σ i))]
  refine prod_congr rfl fun a _ => ?_
  rw [prod_congr rfl fun i hi => by rw [(mem_filter.mp hi).2], prod_const]
  rfl

theorem sum_cnt (σ : Fin N → C) : ∑ a, cnt σ a = N := by
  have := sum_comp_eq_cnt σ (fun _ => (1 : ℕ))
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
  exact this.symm

/-- The type `p_σ`. -/
noncomputable def typ (σ : Fin N → C) (a : C) : ℝ := (cnt σ a : ℝ) / N

theorem typ_nonneg (σ : Fin N → C) (a : C) : 0 ≤ typ σ a := by unfold typ; positivity

theorem sum_typ (hN : 1 ≤ N) (σ : Fin N → C) : ∑ a, typ σ a = 1 := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  simp only [typ, ← sum_div]
  rw [← Nat.cast_sum, sum_cnt, div_self hN0]

theorem prod_typ (hN : 1 ≤ N) (σ : Fin N → C) :
    ∏ i, typ σ (σ i) = Real.exp (N * ∑ a, typ σ a * Real.log (typ σ a)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [prod_comp_eq_cnt σ (typ σ), mul_sum, Real.exp_sum]
  refine prod_congr rfl fun a _ => ?_
  rcases Nat.eq_zero_or_pos (cnt σ a) with h | h
  · simp [h, typ]
  · have hp : 0 < typ σ a := by unfold typ; positivity
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hp]
    congr 1
    simp only [typ]
    field_simp

omit [DecidableEq C] in
/-- `∑_σ ∏ᵢ q(σ i) = (∑ₐ q a)^N`. -/
theorem sum_prod_eq_pow (q : C → ℝ) : ∑ σ : Fin N → C, ∏ i, q (σ i) = (∑ a, q a) ^ N := by
  rw [← Fintype.prod_sum (fun (_ : Fin N) a => q a)]
  simp

/-- The count vector as an element of `C → Fin (N+1)`. -/
def cntV (σ : Fin N → C) : C → Fin (N + 1) := fun a => ⟨cnt σ a, Nat.lt_succ_of_le (cnt_le σ a)⟩

/-- **Number of types**: `∑_σ ∏ᵢ p_σ(σ i) ≤ (N+1)^{|C|}`. -/
theorem sum_prod_typ_le (hN : 1 ≤ N) :
    ∑ σ : Fin N → C, ∏ i, typ σ (σ i) ≤ ((N : ℝ) + 1) ^ Fintype.card C := by
  set T := (univ : Finset (Fin N → C)).image cntV with hT
  set F : (Fin N → C) → (C → Fin (N + 1)) → ℝ := fun σ n => ∏ i, ((n (σ i) : ℕ) : ℝ) / N
  have hF0 : ∀ σ n, 0 ≤ F σ n := fun σ n => prod_nonneg fun i _ => by positivity
  have h1 : ∑ σ : Fin N → C, ∏ i, typ σ (σ i) = ∑ σ : Fin N → C, F σ (cntV σ) := rfl
  have h2 : ∑ σ : Fin N → C, F σ (cntV σ) = ∑ n ∈ T, ∑ σ ∈ univ.filter (fun σ => cntV σ = n),
      F σ (cntV σ) :=
    (sum_fiberwise_of_maps_to (fun σ _ => mem_image_of_mem cntV (mem_univ σ)) _).symm
  have h3 : ∀ n ∈ T, ∑ σ ∈ univ.filter (fun σ => cntV σ = n), F σ (cntV σ) ≤ 1 := by
    intro n hn
    obtain ⟨τ, -, rfl⟩ := mem_image.mp hn
    calc ∑ σ ∈ univ.filter (fun σ => cntV σ = cntV τ), F σ (cntV σ)
        = ∑ σ ∈ univ.filter (fun σ => cntV σ = cntV τ), F σ (cntV τ) :=
          sum_congr rfl fun σ hσ => by rw [(mem_filter.mp hσ).2]
      _ ≤ ∑ σ : Fin N → C, F σ (cntV τ) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun σ _ _ => hF0 σ _
      _ = (∑ a, typ τ a) ^ N := sum_prod_eq_pow (fun a => typ τ a)
      _ = 1 := by rw [sum_typ hN, one_pow]
  have h4 : (T.card : ℝ) ≤ ((N : ℝ) + 1) ^ Fintype.card C := by
    have : T.card ≤ (N + 1) ^ Fintype.card C := by
      calc T.card ≤ (univ : Finset (C → Fin (N + 1))).card := card_le_univ T
        _ = (N + 1) ^ Fintype.card C := by simp
    exact_mod_cast this
  rw [h1, h2]
  calc ∑ n ∈ T, ∑ σ ∈ univ.filter (fun σ => cntV σ = n), F σ (cntV σ) ≤ ∑ _n ∈ T, (1 : ℝ) :=
        sum_le_sum h3
    _ = T.card := by simp
    _ ≤ _ := h4

end SharpLSI
