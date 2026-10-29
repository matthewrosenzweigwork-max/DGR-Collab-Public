import FullLabeledLSI.Paper.Sec5Products

/-!
# Lemma 5.4: summation over `j` and the constants
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

theorem inv_succ_le_log_aux (m : ℝ) (hm : 0 < m) : 1 / (m + 1) ≤ Real.log ((m + 1) / m) := by
  have h := Real.one_sub_inv_le_log_of_pos (x := (m + 1) / m) (by positivity)
  have e : 1 - ((m + 1) / m)⁻¹ = 1 / (m + 1) := by
    field_simp
    ring
  linarith

theorem sum_inv_aux (M : ℕ) (hM : 1 ≤ M) (ℓ : ℕ) :
    ∑ i ∈ Finset.range ℓ, (1 : ℝ) / ((M : ℝ) + 1 + i) ≤ Real.log (((M : ℝ) + ℓ) / M) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  induction ℓ with
  | zero => simp [div_self hM'.ne']
  | succ ℓ ih =>
    rw [Finset.sum_range_succ]
    have hpos : (0 : ℝ) < (M : ℝ) + ℓ := by positivity
    have h1 := inv_succ_le_log_aux ((M : ℝ) + ℓ) hpos
    have e : (((M : ℝ) + ((ℓ + 1 : ℕ) : ℝ)) / M) =
        (((M : ℝ) + ℓ + 1) / ((M : ℝ) + ℓ)) * (((M : ℝ) + ℓ) / M) := by
      push_cast
      field_simp
      ring
    rw [e, Real.log_mul (by positivity) (by positivity)]
    have e2 : (M : ℝ) + 1 + (ℓ : ℝ) = (M : ℝ) + ℓ + 1 := by ring
    rw [e2]
    linarith

/-- `∑_{m=M+1}^{N} 1/m ≤ log (N/M)`. -/
theorem sum_inv_sub_le_log {N M : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    ∑ j ∈ Finset.range (N - M), (1 : ℝ) / ((N - j : ℕ) : ℝ) ≤ Real.log ((N : ℝ) / M) := by
  obtain ⟨ℓ, rfl⟩ := Nat.exists_eq_add_of_le' hMN
  have h := sum_inv_aux M hM ℓ
  have hl : ℓ + M - M = ℓ := by omega
  rw [hl]
  have e : ∑ j ∈ Finset.range ℓ, (1 : ℝ) / (((ℓ + M - j : ℕ)) : ℝ) =
      ∑ j ∈ Finset.range ℓ, (fun i : ℕ => (1 : ℝ) / ((M : ℝ) + 1 + i)) j := by
    rw [← Finset.sum_range_reflect (fun i : ℕ => (1 : ℝ) / ((M : ℝ) + 1 + i)) ℓ]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    have : ℓ + M - j = M + 1 + (ℓ - 1 - j) := by omega
    rw [this]
    push_cast
    ring_nf
  rw [e]
  have e3 : ((ℓ + M : ℕ) : ℝ) = (M : ℝ) + ℓ := by push_cast; ring
  rw [e3]
  exact h

/-- Lemma 5.4 (5.12), explicit form. -/
theorem random_products_aux (k : ℕ) (τ : ℝ) (hτ : 0 < τ) (A : (Fin k → Torus d) → ℝ)
    (hA : Measurable A) (hAb : ∃ a, ∀ z, |A z| ≤ a) :
    ∃ C : ℝ, ∀ (N M : ℕ), k ≤ M → M ≤ N → τ ≤ (M : ℝ) / N →
      ∀ (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
        (ν : Measure (Config N d)) [IsProbabilityMeasure ν],
        klDiv ν (Measure.pi fun _ => μ) ≠ ⊤ →
        |∑ j ∈ Finset.range (N - M), condMeanS ν k A j -
            ((N - M : ℕ) : ℝ) * ∫ X, SharpLSI.empiricalTensor k A X ∂ν| ≤
          C * (1 + Real.sqrt (klDiv ν (Measure.pi fun _ => μ)).toReal) := by
  obtain ⟨a0, ha0⟩ := hAb
  have ha : ∀ z, |A z| ≤ max a0 0 := fun z => (ha0 z).trans (le_max_left _ _)
  have a_nonneg : 0 ≤ max a0 0 := le_max_right _ _
  generalize max a0 0 = a at ha a_nonneg
  by_cases hk : k = 0
  · refine ⟨0, ?_⟩
    intro N M hkM hMN hτM μ _ ν _ hH
    subst hk
    have hemp : ∀ X : Config N d, SharpLSI.empiricalTensor 0 A X = A default := by
      intro X
      simp [SharpLSI.empiricalTensor]
      congr 1
      exact Subsingleton.elim _ _
    have key : ∀ j ≤ N, condMeanS ν 0 A j = A default := by
      intro j hj
      have hin : ∀ (S : Finset (Fin N)) (X : Config N d),
          ∫ z, A z ∂Measure.pi (fun _ : Fin 0 => barCond ν S X) = A default := by
        intro S X
        rw [Measure.pi_of_empty, integral_dirac' _ _ hA.stronglyMeasurable]
        congr 1
        exact Subsingleton.elim _ _
      unfold condMeanS
      simp only [hin, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul,
        Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have : (Nat.choose N j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
      field_simp
    have h1 : ∑ j ∈ Finset.range (N - M), condMeanS ν 0 A j = ((N - M : ℕ) : ℝ) * A default := by
      rw [Finset.sum_congr rfl (fun j hj => key j (by have := Finset.mem_range.1 hj; omega))]
      simp
    simp only [hemp, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul, h1]
    simp
  · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
    set K : ℝ := (k : ℝ) * ((k : ℝ) - 1) with hK
    have hK0 : 0 ≤ K := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      rw [hK]; nlinarith
    refine ⟨a * (K * (|Real.log (1 / τ)| + 1) + Real.sqrt (2 * K * k / τ)), ?_⟩
    intro N M hkM hMN hτM μ _ ν _ hH
    have hM1 : 1 ≤ M := le_trans hk1 hkM
    have hN1 : 1 ≤ N := le_trans hM1 hMN
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hkM' : (k : ℝ) ≤ M := by exact_mod_cast hkM
    have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    set Hr : ℝ := (klDiv ν (Measure.pi fun _ => μ)).toReal with hHr
    have hHr0 : 0 ≤ Hr := ENNReal.toReal_nonneg
    set ℓ : ℕ := N - M with hℓ
    have hℓN : (ℓ : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N M
    set x : ℕ → ℝ := fun j => (dRev ν j k).toReal with hx
    have hx0 : ∀ j, 0 ≤ x j := fun j => ENNReal.toReal_nonneg
    -- per-j bound
    have hj : ∀ j ∈ Finset.range ℓ,
        |condMeanS ν k A j - ∫ X, SharpLSI.empiricalTensor k A X ∂ν| ≤
          a * (K / ((N - j : ℕ) : ℝ)) + a * (K / N) + a * Real.sqrt (2 * x j) := by
      intro j hjm
      have hjl := Finset.mem_range.1 hjm
      have h1 := condMeanS_sub_glob ν μ hH hk1 A hA ha (j := j) (by omega)
      have h2 := integral_empiricalTensor_sub_glob ν hN1 A hA ha
      have e : condMeanS ν k A j - ∫ X, SharpLSI.empiricalTensor k A X ∂ν =
          (condMeanS ν k A j - globTupleMean ν k A) +
            (globTupleMean ν k A - ∫ X, SharpLSI.empiricalTensor k A X ∂ν) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      have h1' : |condMeanS ν k A j - globTupleMean ν k A| ≤
          a * (K / ((N - j : ℕ) : ℝ)) + a * Real.sqrt (2 * x j) := by
        refine h1.trans (le_of_eq ?_); simp only [hx, hK]; try ring
      have h2' : |∫ X, SharpLSI.empiricalTensor k A X ∂ν - globTupleMean ν k A| ≤ a * (K / N) := by
        refine h2.trans (le_of_eq ?_); simp only [hK]; try ring
      rw [abs_sub_comm (globTupleMean ν k A)]
      linarith
    -- sums
    have hS1 : ∑ j ∈ Finset.range ℓ, (1 : ℝ) / ((N - j : ℕ) : ℝ) ≤ |Real.log (1 / τ)| := by
      refine (sum_inv_sub_le_log hM1 hMN).trans ?_
      refine le_trans ?_ (le_abs_self _)
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ hM0 hτ]
      have := (le_div_iff₀ hN0).1 hτM
      linarith
    have hchain : ∑ j ∈ Finset.range ℓ, x j ≤ K * Hr / ((M - k + 2 : ℕ) : ℝ) := by
      have hc := chain_sum_d ν μ k M hkM hMN
      have h1 : ((k : ℝ≥0∞) - 1).toReal = (k : ℝ) - 1 := by
        rw [ENNReal.toReal_sub_of_le (by exact_mod_cast hk1) (ENNReal.natCast_ne_top k)]
        simp
      have hRne : (k * (k - 1) : ℝ≥0∞) * klDiv ν (Measure.pi fun _ : Fin N => μ) /
          ((M - k + 2 : ℕ) : ℝ≥0∞) ≠ ⊤ := by
        rw [div_eq_mul_inv]
        refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
          (ENNReal.natCast_ne_top k) (ENNReal.sub_ne_top (ENNReal.natCast_ne_top k))) hH)
          (ENNReal.inv_ne_top.2 ?_)
        exact_mod_cast (by omega : M - k + 2 ≠ 0)
      have hfin : ∀ j ∈ Finset.range ℓ, dRev ν j k ≠ ⊤ := by
        intro j hjm
        refine ne_top_of_le_ne_top (ne_top_of_le_ne_top hRne hc) ?_
        exact Finset.single_le_sum (f := fun j => dRev ν j k) (fun _ _ => bot_le) hjm
      have := ENNReal.toReal_mono hRne hc
      rw [ENNReal.toReal_sum hfin] at this
      refine this.trans (le_of_eq ?_)
      rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_mul, h1,
        ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    have hm : ((M - k + 2 : ℕ) : ℝ) = (M : ℝ) - k + 2 := by
      rw [Nat.cast_add, Nat.cast_sub hkM]; push_cast; ring
    have hm0 : (0 : ℝ) < ((M - k + 2 : ℕ) : ℝ) := by rw [hm]; linarith
    have hratio : (ℓ : ℝ) * τ ≤ k * ((M - k + 2 : ℕ) : ℝ) := by
      have := (le_div_iff₀ hN0).1 hτM
      rw [hm]
      have h3 : (ℓ : ℝ) * τ ≤ M := by nlinarith
      nlinarith
    have hS3 : ∑ j ∈ Finset.range ℓ, Real.sqrt (2 * x j) ≤
        Real.sqrt (2 * K * k / τ) * Real.sqrt Hr := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range ℓ) (fun _ => (1 : ℝ))
        (fun j => Real.sqrt (2 * x j))
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
      have hsq : ∑ j ∈ Finset.range ℓ, Real.sqrt (2 * x j) ^ 2 = 2 * ∑ j ∈ Finset.range ℓ, x j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => Real.sq_sqrt (by linarith [hx0 j])
      rw [hsq] at hcs
      have hb : (ℓ : ℝ) * (2 * ∑ j ∈ Finset.range ℓ, x j) ≤ 2 * K * k / τ * Hr := by
        have h4 : ∑ j ∈ Finset.range ℓ, x j ≤ K * Hr / ((M - k + 2 : ℕ) : ℝ) := hchain
        have h5 : (ℓ : ℝ) * (K * Hr / ((M - k + 2 : ℕ) : ℝ)) ≤ K * k / τ * Hr := by
          rw [mul_div_assoc', div_le_iff₀ hm0, show K * k / τ * Hr = (K * Hr * k) / τ by ring,
            div_mul_eq_mul_div, le_div_iff₀ hτ]
          have : 0 ≤ K * Hr := mul_nonneg hK0 hHr0
          nlinarith
        have h6 : (ℓ : ℝ) * ∑ j ∈ Finset.range ℓ, x j ≤
            (ℓ : ℝ) * (K * Hr / ((M - k + 2 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
        calc (ℓ : ℝ) * (2 * ∑ j ∈ Finset.range ℓ, x j)
            = 2 * ((ℓ : ℝ) * ∑ j ∈ Finset.range ℓ, x j) := by ring
          _ ≤ 2 * (K * k / τ * Hr) := by linarith
          _ = 2 * K * k / τ * Hr := by ring
      rw [← Real.sqrt_mul (by positivity)]
      exact le_trans (le_abs_self _) (Real.abs_le_sqrt (hcs.trans hb))
    -- assemble
    have hsum : |∑ j ∈ Finset.range ℓ, condMeanS ν k A j -
          (ℓ : ℝ) * ∫ X, SharpLSI.empiricalTensor k A X ∂ν| ≤
        a * (K * ∑ j ∈ Finset.range ℓ, (1 : ℝ) / ((N - j : ℕ) : ℝ)) +
          (ℓ : ℝ) * (a * (K / N)) + a * ∑ j ∈ Finset.range ℓ, Real.sqrt (2 * x j) := by
      have e : ∑ j ∈ Finset.range ℓ, condMeanS ν k A j -
          (ℓ : ℝ) * ∫ X, SharpLSI.empiricalTensor k A X ∂ν =
          ∑ j ∈ Finset.range ℓ, (condMeanS ν k A j - ∫ X, SharpLSI.empiricalTensor k A X ∂ν) := by
        rw [Finset.sum_sub_distrib]; simp
      rw [e]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum hj).trans (le_of_eq ?_)
      have e1 : ∑ j ∈ Finset.range ℓ, a * (K / ((N - j : ℕ) : ℝ)) =
          a * (K * ∑ j ∈ Finset.range ℓ, (1 : ℝ) / ((N - j : ℕ) : ℝ)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      have e3 : ∑ j ∈ Finset.range ℓ, a * Real.sqrt (2 * x j) =
          a * ∑ j ∈ Finset.range ℓ, Real.sqrt (2 * x j) := (Finset.mul_sum _ _ _).symm
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e3, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
    have hKN : (ℓ : ℝ) * (a * (K / N)) ≤ a * K := by
      have : (ℓ : ℝ) * (a * (K / N)) = a * K * ((ℓ : ℝ) / N) := by field_simp
      rw [this]
      have h7 : (ℓ : ℝ) / N ≤ 1 := (div_le_one hN0).2 hℓN
      have : 0 ≤ a * K := mul_nonneg a_nonneg hK0
      nlinarith
    have hC1 : 0 ≤ Real.sqrt (2 * K * k / τ) := Real.sqrt_nonneg _
    have hsq0 : 0 ≤ Real.sqrt Hr := Real.sqrt_nonneg _
    have hL0 : 0 ≤ |Real.log (1 / τ)| := abs_nonneg _
    have t1 : a * (K * ∑ j ∈ Finset.range ℓ, (1 : ℝ) / ((N - j : ℕ) : ℝ)) ≤
        a * (K * |Real.log (1 / τ)|) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS1 hK0) a_nonneg
    have t3 : a * ∑ j ∈ Finset.range ℓ, Real.sqrt (2 * x j) ≤
        a * (Real.sqrt (2 * K * k / τ) * Real.sqrt Hr) :=
      mul_le_mul_of_nonneg_left hS3 a_nonneg
    have p1 : 0 ≤ a * (K * (|Real.log (1 / τ)| + 1)) := by positivity
    have p2 : 0 ≤ a * Real.sqrt (2 * K * k / τ) := by positivity
    have p3 : 0 ≤ a * (K * (|Real.log (1 / τ)| + 1)) * Real.sqrt Hr := by positivity
    have p4 : 0 ≤ a * K * |Real.log (1 / τ)| := by positivity
    calc _ ≤ _ := hsum
      _ ≤ a * (K * |Real.log (1 / τ)|) + a * K + a * (Real.sqrt (2 * K * k / τ) * Real.sqrt Hr) := by
        linarith
      _ ≤ _ := by nlinarith

end SharpLSI.FL
