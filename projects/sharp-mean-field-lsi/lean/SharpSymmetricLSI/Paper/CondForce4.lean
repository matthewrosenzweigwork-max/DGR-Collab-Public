import SharpSymmetricLSI.Paper.CondForce2
import SharpSymmetricLSI.Paper.CondForce3

/-!
# Lemma 5.4 (Phase 3, lane D; R21)

Summing the per-`j` bound with Cauchy–Schwarz and the summed dependence (5.4).
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `∑_{j<ℓ} √(2D_{j,k}) ≤ √(2k³) √(H₀/δ)` (Cauchy–Schwarz and (5.4)). -/
theorem sum_sqrt_DCondT_le (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {N : ℕ}
    (ν : Measure (Config N d)) [IsProbabilityMeasure ν] (hsym : IsSymmetricMeasure ν)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {M k : ℕ} (hMN : M ≤ N) (hkM : k ≤ M)
    {δ : ℝ} (hδ : 0 < δ) (hδM : δ ≤ (M : ℝ) / N) (hMN' : M < N) :
    ∑ j ∈ Finset.range (N - M), Real.sqrt (2 * (DCondT ν j k).toReal) ≤
      Real.sqrt (2 * ((k : ℝ) * k * k)) *
        Real.sqrt ((klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal / δ) := by
  set H := (klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal with hHdef
  have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
  have hN : 0 < N := by omega
  set ℓ := N - M with hℓdef
  set Dr : ℕ → ℝ := fun j => (DCondT ν j k).toReal with hDr
  have hS := sum_DCondT_toReal_le μ ν hsym hH hMN hkM
  have hDr0 : ∀ j, 0 ≤ Dr j := fun j => ENNReal.toReal_nonneg
  set S := ∑ j ∈ Finset.range ℓ, Real.sqrt (2 * Dr j) with hSdef
  have hCS : S ^ 2 ≤ ℓ * ∑ j ∈ Finset.range ℓ, 2 * Dr j := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range ℓ) (f := fun j => Real.sqrt (2 * Dr j))
    have h2D : ∀ j, Real.sqrt (2 * Dr j) ^ 2 = 2 * Dr j := fun j =>
      Real.sq_sqrt (by linarith [hDr0 j])
    simpa only [Finset.card_range, h2D] using this
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓN : (ℓ : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N M
  have hNδ : (N : ℝ) * δ ≤ M := by
    rw [le_div_iff₀ hNr] at hδM; linarith
  have hkey : (ℓ : ℝ) * ∑ j ∈ Finset.range ℓ, 2 * Dr j ≤ 2 * ((k : ℝ) * k * k) * (H / δ) := by
    rw [← Finset.mul_sum]
    set m : ℝ := ((M - k + 2 : ℕ) : ℝ) with hm
    have hm' : m = (M : ℝ) - k + 2 := by
      rw [hm]; push_cast [show k ≤ M + 2 by omega]; rw [Nat.cast_sub hkM]
    have hmpos : 0 < m := by
      have : (k : ℝ) ≤ M := by exact_mod_cast hkM
      rw [hm']; linarith
    set Kk : ℝ := ((k * (k - 1) : ℕ) : ℝ) with hKk
    have hKk0 : 0 ≤ Kk := Nat.cast_nonneg _
    have hKM : Kk * M ≤ (k : ℝ) * k * k * m := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp [hKk]
      · have hKk' : Kk = (k : ℝ) * (k - 1) := by
          rw [hKk]; push_cast [Nat.cast_sub hk]; ring
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        have hkM' : (k : ℝ) ≤ M := by exact_mod_cast hkM
        rw [hKk', hm']
        nlinarith [mul_nonneg (sub_nonneg.mpr hk1) (sub_nonneg.mpr hkM'),
          mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ k) (sub_nonneg.mpr hk1))
            (sub_nonneg.mpr hkM')]
    have hsum : ∑ j ∈ Finset.range ℓ, Dr j ≤ Kk / m * H := hS
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range ℓ, Dr j := Finset.sum_nonneg fun j _ => hDr0 j
    calc (ℓ : ℝ) * (2 * ∑ j ∈ Finset.range ℓ, Dr j) ≤ N * (2 * (Kk / m * H)) := by
          apply mul_le_mul hℓN (by linarith) (by linarith) hNr.le
      _ = 2 * H * (N * Kk / m) := by ring
      _ ≤ 2 * H * ((k : ℝ) * k * k / δ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_div_iff₀ hmpos hδ]
          calc (N : ℝ) * Kk * δ = Kk * (N * δ) := by ring
            _ ≤ Kk * M := mul_le_mul_of_nonneg_left hNδ hKk0
            _ ≤ (k : ℝ) * k * k * m := hKM
      _ = 2 * ((k : ℝ) * k * k) * (H / δ) := by ring
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _
  rw [← Real.sqrt_mul (by positivity)]
  exact Real.le_sqrt_of_sq_le (hCS.trans hkey)

/-- **Lemma 5.4.** -/
theorem conditional_force_aux (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) :
    ∃ C : ℝ, ∀ (N M : ℕ) (δ : ℝ) (ν : Measure (Config N d)) [IsProbabilityMeasure ν],
      IsSymmetricMeasure ν →
      klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≠ ⊤ →
      M ≤ N → 3 ≤ M → 0 < δ → δ ≤ (M : ℝ) / N →
      ∑ j ∈ Finset.range (N - M), fcTerm W μ ν j ≤
        C * (1 + Real.sqrt
          ((klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))).toReal / δ)) := by
  have hac := minimizer_ac hyp hμ
  obtain ⟨hbm, Mb, hM0, hbM, hβM, -⟩ := bfixF_props hyp hac
  obtain ⟨-, hβm, -, -⟩ := forceMean_props hyp hac
  set μm := (μ : Measure (Torus d))
  set c : Torus d → Fin d → ℝ := fun x k => -bForceL W (densOf μm) x k with hcdef
  have hc : ∀ k, Measurable fun x => c x k := fun k => (hβm k).neg
  have hcM : ∀ x k, |c x k| ≤ Mb := fun x k => by rw [hcdef, abs_neg]; exact hβM x k
  set K : ℝ := 10 * d * Mb ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K * (1 + Real.sqrt (2 * ((2 : ℝ) * 2 * 2)) + Real.sqrt (2 * ((3 : ℝ) * 3 * 3))), ?_⟩
  intro N M δ ν _ hsym hH hMN hM3 hδ hδM
  set H := (klDiv ν (Measure.pi fun _ : Fin N => μm)).toReal with hHdef
  have hR : 0 ≤ Real.sqrt (H / δ) := Real.sqrt_nonneg _
  rcases Nat.eq_zero_or_pos (N - M) with hℓ | hℓ
  · rw [hℓ]; simp only [Finset.range_zero, Finset.sum_empty]; positivity
  have hMN' : M < N := by omega
  have hνac : ν ≪ Measure.pi fun _ : Fin N => μm := (klDiv_ne_top_iff.mp hH).1
  -- per-j bound
  have hj : ∀ j ∈ Finset.range (N - M), fcTerm W μ ν j ≤
      K * (Real.sqrt (2 * (DCondT ν j 2).toReal) + Real.sqrt (2 * (DCondT ν j 3).toReal) +
        1 / N) := by
    intro j hjr
    rw [Finset.mem_range] at hjr
    have hjN : j < N := by omega
    have h3j : j + 3 ≤ N := by omega
    refine (fcTerm_le hyp hμ ν hνac hjN).trans ?_
    have := sq_diff_le (b := bfixF W μm) hbm hbM μm hM0 hc hcM ν hsym hH hjN h3j
    have e2 : DCondT ν j 2 = DCond ν j 2 hjN (by omega) := by
      unfold DCondT; rw [dif_pos ⟨hjN, by omega⟩]
    have e3 : DCondT ν j 3 = DCond ν j 3 hjN h3j := by
      unfold DCondT; rw [dif_pos ⟨hjN, h3j⟩]
    rw [e2, e3]
    exact this
  refine (Finset.sum_le_sum hj).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have s2 := sum_sqrt_DCondT_le μm ν hsym hH hMN (by omega : 2 ≤ M) hδ hδM hMN'
  have s3 := sum_sqrt_DCondT_le μm ν hsym hH hMN (by omega : 3 ≤ M) hδ hδM hMN'
  have sN : ∑ _j ∈ Finset.range (N - M), (1 : ℝ) / N ≤ 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    rw [mul_one_div, div_le_one hNr]
    exact_mod_cast Nat.sub_le N M
  push_cast at s2 s3
  set a := Real.sqrt (2 * ((2 : ℝ) * 2 * 2))
  set b := Real.sqrt (2 * ((3 : ℝ) * 3 * 3))
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  calc K * (∑ j ∈ Finset.range (N - M), Real.sqrt (2 * (DCondT ν j 2).toReal) +
        ∑ j ∈ Finset.range (N - M), Real.sqrt (2 * (DCondT ν j 3).toReal) +
        ∑ _j ∈ Finset.range (N - M), (1 : ℝ) / N)
      ≤ K * (a * Real.sqrt (H / δ) + b * Real.sqrt (H / δ) + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add s2 s3) sN) hK0
    _ ≤ K * ((1 + a + b) * (1 + Real.sqrt (H / δ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hK0
        have e : (1 + a + b) * (1 + Real.sqrt (H / δ)) =
            a * Real.sqrt (H / δ) + b * Real.sqrt (H / δ) + 1 + (Real.sqrt (H / δ) + a + b) := by
          ring
        rw [e]; linarith
    _ = K * (1 + a + b) * (1 + Real.sqrt (H / δ)) := by ring

end SharpLSI
