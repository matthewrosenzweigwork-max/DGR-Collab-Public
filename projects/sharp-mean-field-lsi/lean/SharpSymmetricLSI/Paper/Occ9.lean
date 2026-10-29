import Mathlib

/-!
# Generating polynomial and Newton recursion (Phase 3, lane D; R28(d))

For `a : Fin N → Fin K → ℝ` the generating polynomial `G = ∏ᵢ (1 + ∑ₖ aᵢₖ Xₖ)` has the labelling
sums as coefficients. Its coefficients satisfy the multivariate Newton recursion
`(α_j + 1) [t^{α+e_j}] G = ∑_{β+γ=α} [t^β] G · q_{j,γ}` with
`q_{j,γ} = (-1)^{|γ|} ∑ᵢ aᵢⱼ [t^γ] ℓ_{aᵢ}^{|γ|}`.
-/

noncomputable section
open MvPolynomial Finset.HasAntidiagonal

namespace SharpLSI

variable {K N : ℕ}

/-- The linear form `ℓ_a = ∑ₖ aₖ Xₖ`. -/
def linForm (a : Fin K → ℝ) : MvPolynomial (Fin K) ℝ := ∑ k, C (a k) * X k

/-- The generating polynomial `G = ∏ᵢ (1 + ℓ_{aᵢ})`. -/
def genPoly (a : Fin N → Fin K → ℝ) : MvPolynomial (Fin K) ℝ := ∏ i, (1 + linForm (a i))

/-- The Newton coefficients `q_{j,γ}`. -/
def newtonCoeff (a : Fin N → Fin K → ℝ) (j : Fin K) (γ : Fin K →₀ ℕ) : ℝ :=
  (-1) ^ γ.degree * ∑ i, a i j * (linForm (a i) ^ γ.degree).coeff γ

theorem isHomogeneous_linForm (a : Fin K → ℝ) : (linForm a).IsHomogeneous 1 := by
  unfold linForm
  exact IsHomogeneous.sum _ _ _ fun k _ => by
    rw [C_mul_X_eq_monomial]; exact isHomogeneous_monomial _ (by simp)

theorem pderiv_linForm (a : Fin K → ℝ) (j : Fin K) : pderiv j (linForm a) = C (a j) := by
  classical
  unfold linForm
  rw [map_sum]
  simp_rw [pderiv_C_mul, pderiv_X]
  simp [Pi.single_apply]

theorem degree_le_of_mem_antidiagonal {α : Fin K →₀ ℕ} {x : (Fin K →₀ ℕ) × (Fin K →₀ ℕ)}
    (hx : x ∈ antidiagonal α) : x.2.degree ≤ α.degree ∧ x.1.degree ≤ α.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx, map_add]
  omega

theorem coeff_mul_homogeneous_eq_zero {p h : MvPolynomial (Fin K) ℝ} {n : ℕ}
    (hh : h.IsHomogeneous n) {α : Fin K →₀ ℕ} (hα : α.degree < n) : (p * h).coeff α = 0 := by
  classical
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [hh.coeff_eq_zero (by have := (degree_le_of_mem_antidiagonal hx).1; omega), mul_zero]

theorem pderiv_prod (j : Fin K) (s : Finset (Fin N)) (f : Fin N → MvPolynomial (Fin K) ℝ) :
    pderiv j (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ k ∈ s.erase i, f k) * pderiv j (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Derivation.leibniz, ih, Finset.sum_insert hb, Finset.erase_insert hb,
      smul_eq_mul, smul_eq_mul, Finset.mul_sum]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hib : b ≠ i := fun h => hb (h ▸ hi)
    rw [Finset.erase_insert_of_ne hib, Finset.prod_insert (fun h => hb (Finset.mem_of_mem_erase h))]
    ring

/-- **The multivariate Newton recursion.** -/
theorem newton_genPoly (a : Fin N → Fin K → ℝ) (α : Fin K →₀ ℕ) (j : Fin K) :
    ((α j : ℝ) + 1) * (genPoly a).coeff (α + Finsupp.single j 1) =
      ∑ x ∈ antidiagonal α, (genPoly a).coeff x.1 * newtonCoeff a j x.2 := by
  classical
  set D := α.degree
  set P : Fin N → MvPolynomial (Fin K) ℝ := fun i =>
    ∏ k ∈ Finset.univ.erase i, (1 + linForm (a k)) with hP
  set Q : MvPolynomial (Fin K) ℝ :=
    ∑ i, C (a i j) * ∑ m ∈ Finset.range (D + 1), (-linForm (a i)) ^ m with hQdef
  have hG : ∀ i, genPoly a = (1 + linForm (a i)) * P i := fun i => by
    unfold genPoly; exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hgeom : ∀ i, (1 + linForm (a i)) * ∑ m ∈ Finset.range (D + 1), (-linForm (a i)) ^ m =
      1 - (-linForm (a i)) ^ (D + 1) := fun i => by
    have := geom_sum_mul_neg (-linForm (a i)) (D + 1)
    rw [sub_neg_eq_add] at this
    rw [mul_comm]; exact this
  have hder : pderiv j (genPoly a) = ∑ i, C (a i j) * P i := by
    unfold genPoly
    rw [pderiv_prod]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, pderiv_one, zero_add, pderiv_linForm, mul_comm]
  have hGQ : genPoly a * Q = pderiv j (genPoly a) -
      ∑ i, (C (a i j) * P i) * (-linForm (a i)) ^ (D + 1) := by
    rw [hder, ← Finset.sum_sub_distrib, hQdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hG i]
    calc (1 + linForm (a i)) * P i * (C (a i j) * ∑ m ∈ Finset.range (D + 1), (-linForm (a i)) ^ m)
        = C (a i j) * P i * ((1 + linForm (a i)) *
          ∑ m ∈ Finset.range (D + 1), (-linForm (a i)) ^ m) := by ring
      _ = _ := by rw [hgeom]; ring
  have hhom : ∀ i, ((-linForm (a i)) ^ (D + 1)).IsHomogeneous (D + 1) := fun i => by
    have h1 : (-linForm (a i)).IsHomogeneous 1 := by
      have := (isHomogeneous_C (Fin K) (-1 : ℝ)).mul (isHomogeneous_linForm (a i))
      rwa [map_neg, map_one, neg_one_mul, zero_add] at this
    simpa using h1.pow (D + 1)
  have hcoefGQ : (genPoly a * Q).coeff α = (pderiv j (genPoly a)).coeff α := by
    rw [hGQ, coeff_sub, coeff_sum]
    rw [Finset.sum_eq_zero fun i _ => coeff_mul_homogeneous_eq_zero (hhom i) (by omega), sub_zero]
  have hQ : ∀ γ : Fin K →₀ ℕ, γ.degree ≤ D → Q.coeff γ = newtonCoeff a j γ := fun γ hγ => by
    unfold newtonCoeff
    rw [hQdef, coeff_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hm : ∀ m, ((-linForm (a i)) ^ m).coeff γ = (-1) ^ m * (linForm (a i) ^ m).coeff γ :=
      fun m => by rw [neg_pow, ← map_one C, ← map_neg C, ← map_pow, coeff_C_mul]
    rw [coeff_C_mul, coeff_sum]
    simp_rw [hm]
    rw [Finset.sum_eq_single γ.degree]
    · ring
    · intro m _ hm'
      have := ((isHomogeneous_linForm (a i)).pow m).coeff_eq_zero (d := γ) (by
        simpa using Ne.symm hm')
      rw [this, mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have h1 := coeff_pderiv (i := j) (genPoly a) α
  rw [mul_comm, ← h1, ← hcoefGQ, coeff_mul]
  exact Finset.sum_congr rfl fun x hx => by rw [hQ x.2 (degree_le_of_mem_antidiagonal hx).1]

theorem newtonCoeff_zero (a : Fin N → Fin K → ℝ) (j : Fin K) :
    newtonCoeff a j 0 = ∑ i, a i j := by
  unfold newtonCoeff
  simp

theorem coeff_linForm (b : Fin K → ℝ) (k : Fin K) :
    (linForm b).coeff (Finsupp.single k 1) = b k := by
  classical
  unfold linForm
  rw [coeff_sum]
  simp_rw [C_mul_X_eq_monomial, coeff_monomial, Finsupp.single_left_inj one_ne_zero]
  simp

theorem newtonCoeff_single (a : Fin N → Fin K → ℝ) (j k : Fin K) :
    newtonCoeff a j (Finsupp.single k 1) = -∑ i, a i j * a i k := by
  unfold newtonCoeff
  simp [Finsupp.degree_single, coeff_linForm]

theorem abs_coeff_linForm_pow_le (b : Fin K → ℝ) (m : ℕ) (γ : Fin K →₀ ℕ) :
    |(linForm b ^ m).coeff γ| ≤ (∑ k, |b k|) ^ m := by
  classical
  unfold linForm
  rw [Fintype.sum_pow, Fintype.sum_pow, coeff_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  simp_rw [C_mul_X_eq_monomial]
  rw [← monomial_sum_prod, coeff_monomial]
  split_ifs
  · rw [Finset.abs_prod]
  · rw [abs_zero]; exact Finset.prod_nonneg fun _ _ => abs_nonneg _

theorem abs_newtonCoeff_le (a : Fin N → Fin K → ℝ) (j : Fin K) (γ : Fin K →₀ ℕ) :
    |newtonCoeff a j γ| ≤ ∑ i, (∑ k, |a i k|) ^ (γ.degree + 1) := by
  unfold newtonCoeff
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, pow_succ, mul_comm _ (∑ k, |a i k|)]
  exact mul_le_mul (Finset.single_le_sum (f := fun k => |a i k|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ j)) (abs_coeff_linForm_pow_le _ _ _) (abs_nonneg _)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem genPoly_coeff_zero (a : Fin N → Fin K → ℝ) : (genPoly a).coeff 0 = 1 := by
  rw [← constantCoeff_eq]
  unfold genPoly linForm
  simp [map_prod]

end SharpLSI
