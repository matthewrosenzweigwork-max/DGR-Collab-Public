import FullLabeledLSI.Paper.Sec5Chain

/-!
# Lemma 5.4 helpers: with-replacement versus distinct tuples, expansion of `ρ̄_S^{⊗k}`
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

section Birthday

/-- Number of injective tuples with values in `R`. -/
theorem birthday_card_inj {α : Type*} [DecidableEq α] (R : Finset α) (k : ℕ) :
    ((Fintype.piFinset (fun _ : Fin k => R)).filter (fun I => Function.Injective I)).card =
      R.card.descFactorial k := by
  have h : R.card.descFactorial k = Fintype.card (Fin k ↪ R) := by
    rw [Fintype.card_embedding_eq]; simp
  rw [h, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun e _ => fun x => (e x : α)) ?_ ?_ ?_
  · intro e _
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    exact ⟨fun x => (e x).2, fun x y h => e.injective (Subtype.ext h)⟩
  · intro e _ e' _ h
    ext x
    exact congrFun h x
  · intro f hf
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hf
    exact ⟨⟨fun x => ⟨f x, hf.1 x⟩, fun x y h => hf.2 (congrArg Subtype.val h)⟩,
      Finset.mem_univ _, rfl⟩

/-- Lower bound on the falling factorial. -/
theorem birthday_descFactorial_lower (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    (n : ℝ) ^ k * (1 - ((k : ℝ) * ((k : ℝ) - 1)) / (2 * n)) ≤ (n.descFactorial k : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ]
    by_cases hkn : k < n
    · have hkR : (k : ℝ) ≤ n := by exact_mod_cast hkn.le
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      push_cast [Nat.cast_sub hkn.le]
      set x : ℝ := (n : ℝ) ^ k with hx
      have hx0 : 0 < x := by positivity
      set q : ℝ := (k : ℝ) * ((k : ℝ) - 1) / (2 * n) with hq
      have hq0 : 0 ≤ q := by
        rw [hq]; apply div_nonneg _ (by positivity)
        rcases Nat.eq_zero_or_pos k with h | h
        · simp [h]
        · have : (1 : ℝ) ≤ k := by exact_mod_cast h
          nlinarith
      have hrel : ((k : ℝ) + 1) * (((k : ℝ) + 1) - 1) / (2 * n) = q + k / n := by
        rw [hq]; field_simp; ring
      rw [hrel, pow_succ]
      have h1 : ((n : ℝ) - k) * (x * (1 - q)) ≤ ((n : ℝ) - k) * (n.descFactorial k : ℝ) :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      have h2 : x * (n : ℝ) * (1 - (q + k / n)) = x * (n * (1 - q) - k) := by
        field_simp; ring
      rw [h2]
      have h3 : x * (n * (1 - q) - k) ≤ ((n : ℝ) - k) * (x * (1 - q)) := by
        have : ((n : ℝ) - k) * (x * (1 - q)) - x * (n * (1 - q) - k) = x * k * q := by ring
        have : 0 ≤ x * k * q := by positivity
        linarith
      linarith
    · have hkn' : n ≤ k := not_lt.1 hkn
      have hz : n - k = 0 := Nat.sub_eq_zero_of_le hkn'
      rw [hz]
      simp only [zero_mul, Nat.cast_zero]
      have hkR : (n : ℝ) ≤ k := by exact_mod_cast hkn'
      have hk1 : (1 : ℝ) ≤ k := by linarith
      have : 1 ≤ ((k : ℝ) + 1) * (((k : ℝ) + 1) - 1) / (2 * n) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have : (1 - ((k : ℝ) + 1) * (((k : ℝ) + 1) - 1) / (2 * n)) ≤ 0 := by linarith
      push_cast
      have hp : (0 : ℝ) < (n : ℝ) ^ (k + 1) := by positivity
      nlinarith

/-- The average of finitely many probability measures is a probability measure. -/
theorem birthday_avg_isProb {ι T : Type*} [MeasurableSpace T] (R : Finset ι) (hR : R.Nonempty)
    (ρ : ι → Measure T) [∀ i, IsProbabilityMeasure (ρ i)] :
    IsProbabilityMeasure (((R.card : ℝ≥0∞)⁻¹) • ∑ i ∈ R, ρ i) := by
  refine ⟨?_⟩
  have hc : (R.card : ℝ≥0∞) ≠ 0 := by simpa using hR.card_pos.ne'
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, measure_univ,
    Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hc (ENNReal.natCast_ne_top _)

/-- `(ρ̄)^{⊗k}` is the uniform average of the product measures `⊗_l ρ_{I_l}` over `I ∈ R^k`. -/
theorem birthday_pi_avg {ι T : Type*} [MeasurableSpace T] (R : Finset ι) (hR : R.Nonempty)
    (ρ : ι → Measure T) [∀ i, IsProbabilityMeasure (ρ i)] (k : ℕ) :
    Measure.pi (fun _ : Fin k => ((R.card : ℝ≥0∞)⁻¹) • ∑ i ∈ R, ρ i) =
      (((R.card : ℝ≥0∞) ^ k)⁻¹) • ∑ I ∈ Fintype.piFinset (fun _ : Fin k => R),
        Measure.pi (fun l => ρ (I l)) := by
  classical
  have := birthday_avg_isProb R hR ρ
  refine Measure.pi_eq fun s hs => ?_
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, Measure.pi_pi,
    smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_univ_sum, ENNReal.inv_pow]

/-- Integral version of `birthday_pi_avg`. -/
theorem birthday_integral_pi_avg {ι T : Type*} [MeasurableSpace T] (R : Finset ι)
    (hR : R.Nonempty) (ρ : ι → Measure T) [∀ i, IsProbabilityMeasure (ρ i)] (k : ℕ)
    (A : (Fin k → T) → ℝ) (hA : Measurable A) {c : ℝ} (hc : ∀ z, |A z| ≤ c) :
    ∫ z, A z ∂Measure.pi (fun _ : Fin k => ((R.card : ℝ≥0∞)⁻¹) • ∑ i ∈ R, ρ i) =
      (((R.card : ℝ) ^ k)⁻¹ *
        ∑ I ∈ Fintype.piFinset (fun _ : Fin k => R), ∫ z, A z ∂Measure.pi (fun l => ρ (I l))) := by
  rw [birthday_pi_avg R hR ρ k, integral_smul_measure, integral_finsetSum_measure]
  · rw [smul_eq_mul]
    congr 1
    rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  · intro I _
    exact Integrable.of_bound hA.aestronglyMeasurable c
      (Filter.Eventually.of_forall fun z => by simpa using hc z)

/-- With-replacement versus distinct tuples: for a bounded `f` on `R^k` the uniform average over all
tuples and over injective tuples differ by at most `c k (k-1)/|R|`. -/
theorem birthday_avg_diff {α : Type*} [DecidableEq α] (R : Finset α) (hR : 1 ≤ R.card) (k : ℕ)
    (f : (Fin k → α) → ℝ) {c : ℝ} (hf : ∀ I, |f I| ≤ c) :
    |(((R.card : ℝ) ^ k)⁻¹ * ∑ I ∈ Fintype.piFinset (fun _ : Fin k => R), f I) -
        (((R.card.descFactorial k : ℕ) : ℝ)⁻¹ *
          ∑ I ∈ (Fintype.piFinset (fun _ : Fin k => R)).filter (fun I => Function.Injective I),
            f I)| ≤ c * ((k * (k - 1) : ℝ) / R.card) := by
  classical
  have hnR : (1 : ℝ) ≤ R.card := by exact_mod_cast hR
  obtain ⟨a, ha⟩ : R.Nonempty := Finset.card_pos.1 hR
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hf (fun _ => a))
  have hQcard := birthday_card_inj R k
  have hlow := birthday_descFactorial_lower R.card hR k
  set P := Fintype.piFinset (fun _ : Fin k => R) with hP
  have hPcard : (P.card : ℝ) = (R.card : ℝ) ^ k := by
    rw [hP, Fintype.card_piFinset]; simp
  have hPpos : (0 : ℝ) < (R.card : ℝ) ^ k := by positivity
  have hsumP : |∑ I ∈ P, f I| ≤ (R.card : ℝ) ^ k * c := by
    calc _ ≤ ∑ I ∈ P, |f I| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ I ∈ P, c := Finset.sum_le_sum fun I _ => hf I
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hPcard]
  by_cases hk : R.card < k
  · have hd : R.card.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.2 hk
    rw [hd]
    simp only [Nat.cast_zero, inv_zero, zero_mul, sub_zero]
    have h1 : |((R.card : ℝ) ^ k)⁻¹ * ∑ I ∈ P, f I| ≤ c := by
      rw [abs_mul, abs_inv, abs_of_pos hPpos]
      calc _ ≤ ((R.card : ℝ) ^ k)⁻¹ * ((R.card : ℝ) ^ k * c) := by gcongr
        _ = c := by field_simp
    have hk' : (R.card : ℝ) + 1 ≤ k := by exact_mod_cast hk
    have h2 : 1 ≤ (((k : ℝ) * ((k : ℝ) - 1)) / R.card) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    calc _ ≤ c := h1
      _ = c * 1 := (mul_one c).symm
      _ ≤ _ := by gcongr
  · have hk := not_lt.1 hk
    set Q := P.filter (fun I => Function.Injective I) with hQ
    set T := P.filter (fun I => ¬ Function.Injective I) with hT
    have hdnat : 0 < R.card.descFactorial k :=
      Nat.pos_of_ne_zero (fun h => by have := Nat.descFactorial_eq_zero_iff_lt.1 h; omega)
    set dd : ℝ := ((R.card.descFactorial k : ℕ) : ℝ) with hdd
    set PP : ℝ := (R.card : ℝ) ^ k with hPPdef
    have hddpos : 0 < dd := by rw [hdd]; exact_mod_cast hdnat
    have hddle : dd ≤ PP := by rw [hdd, hPPdef]; exact_mod_cast Nat.descFactorial_le_pow _ _
    have hQc : (Q.card : ℝ) = dd := by rw [hQcard]
    have hTc : (T.card : ℝ) = PP - dd := by
      have := Finset.card_filter_add_card_filter_not (s := P) (fun I => Function.Injective I)
      have h' : (Q.card : ℝ) + T.card = P.card := by exact_mod_cast this
      linarith
    have hsplit : ∑ I ∈ P, f I = ∑ I ∈ Q, f I + ∑ I ∈ T, f I :=
      (Finset.sum_filter_add_sum_filter_not P (fun I => Function.Injective I) f).symm
    have hsQ : |∑ I ∈ Q, f I| ≤ dd * c := by
      calc _ ≤ ∑ I ∈ Q, |f I| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ I ∈ Q, c := Finset.sum_le_sum fun I _ => hf I
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hQc]
    have hsT : |∑ I ∈ T, f I| ≤ (PP - dd) * c := by
      calc _ ≤ ∑ I ∈ T, |f I| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ I ∈ T, c := Finset.sum_le_sum fun I _ => hf I
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hTc]
    generalize ∑ I ∈ Q, f I = sQ at hsplit hsQ ⊢
    generalize ∑ I ∈ T, f I = sT at hsplit hsT ⊢
    rw [hsplit]
    have hE : (PP⁻¹ * (sQ + sT) - dd⁻¹ * sQ) = sT / PP - sQ * (PP - dd) / (PP * dd) := by
      field_simp; ring
    rw [hE]
    have hPPne : PP ≠ 0 := hPpos.ne'
    have hb1 : |sT / PP| ≤ (PP - dd) * c / PP := by
      rw [abs_div, abs_of_pos hPpos]
      exact div_le_div_of_nonneg_right hsT hPpos.le
    have hb2 : |sQ * (PP - dd) / (PP * dd)| ≤ (PP - dd) * c / PP := by
      rw [abs_div, abs_mul, abs_of_pos (mul_pos hPpos hddpos), abs_of_nonneg (by linarith : 0 ≤ PP - dd)]
      rw [div_le_div_iff₀ (mul_pos hPpos hddpos) hPpos]
      have : |sQ| * (PP - dd) ≤ dd * c * (PP - dd) :=
        mul_le_mul_of_nonneg_right hsQ (by linarith)
      nlinarith [mul_pos hPpos hddpos]
    have hq : PP - dd ≤ PP * (((k : ℝ) * ((k : ℝ) - 1)) / (2 * R.card)) := by
      linarith
    have hfin : (PP - dd) * c / PP ≤ c * ((k * (k - 1) : ℝ) / R.card) / 2 := by
      rw [div_le_iff₀ hPpos]
      have h1 : (PP - dd) * c ≤ PP * (((k : ℝ) * ((k : ℝ) - 1)) / (2 * R.card)) * c :=
        mul_le_mul_of_nonneg_right hq hc0
      have h2 : PP * (((k : ℝ) * ((k : ℝ) - 1)) / (2 * R.card)) * c =
          c * ((k * (k - 1) : ℝ) / R.card) / 2 * PP := by
        field_simp
      linarith
    calc _ ≤ |sT / PP| + |sQ * (PP - dd) / (PP * dd)| := by
          have := abs_sub (sT / PP) (sQ * (PP - dd) / (PP * dd))
          exact this
      _ ≤ (PP - dd) * c / PP + (PP - dd) * c / PP := add_le_add hb1 hb2
      _ ≤ c * ((k * (k - 1) : ℝ) / R.card) / 2 + c * ((k * (k - 1) : ℝ) / R.card) / 2 :=
          add_le_add hfin hfin
      _ = _ := by ring


end Birthday

section Reveal

variable {d N : ℕ} (ν : Measure (Config N d)) [IsProbabilityMeasure ν]

theorem distinctTuples_eq_filter (S : Finset (Fin N)) (k : ℕ) :
    distinctTuples S k =
      (Fintype.piFinset (fun _ : Fin k => Sᶜ)).filter (fun I => Function.Injective I) := by
  ext I
  simp only [distinctTuples, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
    Finset.mem_compl]
  tauto

/-- The integral against `ρ̄_S^{⊗k}` is the average over all tuples (with replacement) of the
integrals against the product of conditional marginals. -/
theorem integral_pi_barCond (S : Finset (Fin N)) (hS : 1 ≤ Sᶜ.card) (X : Config N d) {k : ℕ}
    (A : (Fin k → Torus d) → ℝ) (hA : Measurable A) {c : ℝ} (hc : ∀ z, |A z| ≤ c) :
    ∫ z, A z ∂Measure.pi (fun _ : Fin k => barCond ν S X) =
      (((Sᶜ.card : ℝ) ^ k)⁻¹ *
        ∑ I ∈ Fintype.piFinset (fun _ : Fin k => Sᶜ),
          ∫ z, A z ∂Measure.pi (fun l => condLawS ν S (I l) (restrictS S X))) := by
  have hR : Sᶜ.Nonempty := Finset.card_pos.1 (by omega)
  exact birthday_integral_pi_avg Sᶜ hR (fun i => condLawS ν S i (restrictS S X)) k A hA hc

end Reveal

end SharpLSI.FL
