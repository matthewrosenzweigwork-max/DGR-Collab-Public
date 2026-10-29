import SharpSymmetricLSI.Paper.Occ1

/-!
# Orthonormality and symmetry of the occupation basis (Phase 3, lane D; R28)
-/

noncomputable section
open MeasureTheory Finset

namespace SharpLSI

variable {d : ℕ}

section orth
variable {ν : Measure (Torus d)} [IsProbabilityMeasure ν] {e : ℕ → Torus d → ℝ}

theorem mem_occLabellings {α : ℕ →₀ ℕ} {N : ℕ} {c : Fin N → Fin (α.support.sup id + 2)} :
    c ∈ occLabellings α N ↔ ∀ n : ℕ, #{i | (c i : ℕ) = n + 1} = α n := by
  simp [occLabellings]

/-- **`⟨B_α, B_β⟩ = δ_{αβ}`.** -/
theorem integral_occBasis_mul (hL : ∀ i, MemLp (e i) 2 ν)
    (horth : ∀ i j, ∫ x, e i x * e j x ∂ν = if i = j then 1 else 0) {N : ℕ} {α β : ℕ →₀ ℕ}
    (hα : occSize α ≤ N) (hβ : occSize β ≤ N) :
    ∫ X, occBasis e α N X * occBasis e β N X ∂(Measure.pi fun _ : Fin N => ν) =
      if α = β then 1 else 0 := by
  set P := Measure.pi fun _ : Fin N => ν
  set sα := Real.sqrt ((occFactorial α : ℝ) / (N.descFactorial (occSize α) : ℝ))
  set sβ := Real.sqrt ((occFactorial β : ℝ) / (N.descFactorial (occSize β) : ℝ))
  have hprod : ∀ (c : Fin N → ℕ) (c' : Fin N → ℕ),
      ∫ X, ∏ i, (e (c i) (X i) * e (c' i) (X i)) ∂P = if ∀ i, c i = c' i then 1 else 0 := by
    intro c c'
    rw [integral_fintype_prod_eq_prod (f := fun i x => e (c i) x * e (c' i) x)]
    simp_rw [horth]
    rw [Finset.prod_boole]
    simp
  have hint : ∀ (c : Fin N → ℕ) (c' : Fin N → ℕ),
      Integrable (fun X : Config N d => ∏ i, (e (c i) (X i) * e (c' i) (X i))) P := fun c c' =>
    Integrable.fintype_prod (f := fun i x => e (c i) x * e (c' i) x) fun i =>
      (hL _).integrable_mul (hL _)
  have hexp : ∀ X : Config N d, occBasis e α N X * occBasis e β N X =
      sα * sβ * ∑ c ∈ occLabellings α N, ∑ c' ∈ occLabellings β N,
        ∏ i, (e (c i) (X i) * e (c' i) (X i)) := by
    intro X
    unfold occBasis
    rw [mul_mul_mul_comm, Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
    rw [← Finset.prod_mul_distrib]
  simp_rw [hexp]
  rw [integral_const_mul, integral_finsetSum (occLabellings α N)
    (f := fun (c : Fin N → Fin (α.support.sup id + 2)) (X : Config N d) =>
      ∑ c' ∈ occLabellings β N, ∏ i, (e (c i : ℕ) (X i) * e (c' i : ℕ) (X i)))
    fun c _ => integrable_finsetSum _ fun c' _ => hint (fun i => (c i : ℕ)) (fun i => (c' i : ℕ))]
  simp_rw [fun (c : Fin N → Fin (α.support.sup id + 2)) => integral_finsetSum (μ := P)
    (occLabellings β N) (f := fun (c' : Fin N → Fin (β.support.sup id + 2)) (X : Config N d) =>
    ∏ i, (e (c i : ℕ) (X i) * e (c' i : ℕ) (X i))) fun c' _ =>
      hint (fun i => (c i : ℕ)) (fun i => (c' i : ℕ))]
  simp_rw [hprod]
  split_ifs with hab
  · subst hab
    have hq := hα
    have hinner : ∀ c ∈ occLabellings α N, (∑ c' ∈ occLabellings α N,
        if ∀ i, (c i : ℕ) = (c' i : ℕ) then (1 : ℝ) else 0) = 1 := by
      intro c hc
      have : ∀ c' : Fin N → Fin (α.support.sup id + 2),
          (∀ i, (c i : ℕ) = (c' i : ℕ)) ↔ c = c' := fun c' =>
        ⟨fun h => funext fun i => Fin.ext (h i), fun h i => by rw [h]⟩
      simp_rw [this]
      rw [Finset.sum_ite_eq]
      simp [hc]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hc := card_occLabellings α hq
    have hpos : (0 : ℝ) < N.descFactorial (occSize α) := by
      exact_mod_cast Nat.descFactorial_pos.mpr hq
    rw [← Real.sqrt_mul_self (show (0 : ℝ) ≤ #(occLabellings α N) by positivity), ← Real.sqrt_mul
      (by positivity), ← Real.sqrt_mul (by positivity)]
    rw [Real.sqrt_eq_one]
    have hc' : (#(occLabellings α N) : ℝ) * occFactorial α = N.descFactorial (occSize α) := by
      exact_mod_cast hc
    field_simp
    nlinarith [hc']
  · rw [Finset.sum_eq_zero, mul_zero]
    intro c hc
    refine Finset.sum_eq_zero fun c' hc' => ?_
    rw [if_neg]
    intro h
    apply hab
    ext n
    rw [← mem_occLabellings.mp hc n, ← mem_occLabellings.mp hc' n]
    exact congrArg Finset.card (Finset.filter_congr fun i _ => by rw [h i])

end orth

/-- **`B_α` is symmetric.** -/
theorem occBasis_symmetric (e : ℕ → Torus d → ℝ) (α : ℕ →₀ ℕ) (N : ℕ) :
    IsSymmetric (occBasis e α N) := by
  intro σ X
  unfold occBasis
  congr 1
  refine Finset.sum_nbij' (fun c => c ∘ σ.symm) (fun c => c ∘ σ) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    rw [mem_occLabellings] at hc ⊢
    intro n
    rw [← hc n]
    refine Finset.card_bij (fun i _ => σ.symm i) ?_ ?_ ?_
    · intro i hi; simpa using hi
    · intro i _ j _ h; exact σ.symm.injective h
    · intro j hj; exact ⟨σ j, by simpa using hj, by simp⟩
  · intro c hc
    rw [mem_occLabellings] at hc ⊢
    intro n
    rw [← hc n]
    refine Finset.card_bij (fun i _ => σ i) ?_ ?_ ?_
    · intro i hi; simpa using hi
    · intro i _ j _ h; exact σ.injective h
    · intro j hj; exact ⟨σ.symm j, by simpa using hj, by simp⟩
  · intro c _; funext i; simp
  · intro c _; funext i; simp
  · intro c _
    simp only [Function.comp_apply]
    rw [← Equiv.prod_comp σ (fun i => e (c (σ.symm i) : ℕ) (X i))]
    simp

end SharpLSI
