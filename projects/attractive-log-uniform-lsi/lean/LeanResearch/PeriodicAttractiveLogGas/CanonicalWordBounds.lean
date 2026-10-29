import LeanResearch.PeriodicAttractiveLogGas.CanonicalRowHolder
import LeanResearch.PeriodicAttractiveLogGas.CanonicalPairCounts
import Mathlib.MeasureTheory.Integral.Pi

/-! Actual row factorization of an ordered word product and its factorial
bound. Multiplicity enumeration is not assumed or supplied by this module. -/

noncomputable section
open MeasureTheory Finset
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas.CanonicalWordBounds
open CanonicalRowHolder CanonicalWordMoments CanonicalPairCounts

variable {m k : ℕ} {α : Fin m → Type*} [∀ i, MeasurableSpace (α i)]
  (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
  (f : ∀ i j, α i → α j → ℝ)

/-- The literal factors whose row index equals i. -/
def rowFiberProduct (r c : Fin (2 * k) → Fin m) (i : Fin m)
    (Y : ∀ j, α j) (x : α i) : ℝ :=
  ∏ ℓ ∈ Finset.univ.filter (fun ℓ => r ℓ = i), f i (c ℓ) x (Y (c ℓ))

omit [∀ i, MeasurableSpace (α i)] in
/-- Grouping a finite word by its actual row fibers. -/
theorem prod_rowFiberProduct (r c : Fin (2 * k) → Fin m) (X Y : ∀ i, α i) :
    (∏ i, rowFiberProduct f r c i Y (X i)) = wordProduct f r c (X, Y) := by
  unfold rowFiberProduct wordProduct
  calc
    (∏ i, ∏ ℓ ∈ Finset.univ.filter (fun ℓ => r ℓ = i), f i (c ℓ) (X i) (Y (c ℓ))) =
        ∏ i, ∏ ℓ ∈ Finset.univ.filter (fun ℓ => r ℓ = i),
          f (r ℓ) (c ℓ) (X (r ℓ)) (Y (c ℓ)) := by
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro ℓ hℓ
      rw [(Finset.mem_filter.mp hℓ).2]
    _ = ∏ ℓ, f (r ℓ) (c ℓ) (X (r ℓ)) (Y (c ℓ)) :=
      Finset.prod_fiberwise Finset.univ r _

omit [∀ i, MeasurableSpace (α i)] in
/-- An unused row contributes the multiplicative identity. -/
theorem rowFiberProduct_eq_one (r c : Fin (2 * k) → Fin m) (i : Fin m)
    (hi : wordMultiplicity r i = 0) (Y : ∀ j, α j) (x : α i) :
    rowFiberProduct f r c i Y x = 1 := by
  have he : Finset.univ.filter (fun ℓ => r ℓ = i) = ∅ := Finset.card_eq_zero.mp hi
  simp [rowFiberProduct, he]

/-- Reindexing a finite set permits direct use of the checked ordered-slot Hölder lemma. -/
theorem integrable_finset_prod_and_integral_abs_le
    {β ι : Type*} [MeasurableSpace β] {μ : Measure β}
    (s : Finset ι) (hs : 1 ≤ s.card) (g : ι → β → ℝ)
    (hg : ∀ ℓ ∈ s, Measurable (g ℓ)) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ ℓ ∈ s, (∫⁻ x, ‖g ℓ x‖ₑ ^ s.card ∂μ) ≤ ENNReal.ofReal K) :
    Integrable (fun x => ∏ ℓ ∈ s, g ℓ x) μ ∧
      (∫ x, |∏ ℓ ∈ s, g ℓ x| ∂μ) ≤ K := by
  classical
  let e : s ≃ Fin s.card := s.equivFin
  have hp (x : β) : (∏ ℓ : Fin s.card, g (e.symm ℓ) x) = ∏ ℓ ∈ s, g ℓ x := by
    calc
      _ = ∏ ℓ : s, g ℓ x := e.symm.prod_comp (fun ℓ : s => g ℓ x)
      _ = ∏ ℓ ∈ s, g ℓ x := Finset.prod_coe_sort s (fun ℓ => g ℓ x)
  have h := integrable_prod_and_integral_abs_le hs (fun ℓ x => g (e.symm ℓ) x)
    (fun ℓ => hg _ (e.symm ℓ).prop) hK0 (fun ℓ => hK _ (e.symm ℓ).prop)
  simpa only [hp] using h

/-- Nonempty row fibers obey the precise source factorial bound almost everywhere. -/
theorem ae_rowFiberProduct_bound
    (hf : ∀ i j, Measurable (Function.uncurry (f i j))) {L : ℝ} (hL : 0 ≤ L)
    (hsource : ∀ p : ℕ, 1 ≤ p → ∀ i j,
      essSup (leftMoment (ν i) (f i j) p) (ν j) +
        essSup (rightMoment (ν j) (f i j) p) (ν i) ≤
          ENNReal.ofReal (2 * L ^ p * (p.factorial : ℝ)))
    (r c : Fin (2 * k) → Fin m) (i : Fin m) (hi : 1 ≤ wordMultiplicity r i) :
    ∀ᵐ Y ∂Measure.pi ν, Integrable (rowFiberProduct f r c i Y) (ν i) ∧
      (∫ x, |rowFiberProduct f r c i Y x| ∂ν i) ≤
        2 * L ^ wordMultiplicity r i * ((wordMultiplicity r i).factorial : ℝ) := by
  have hslots (ℓ : Fin (2 * k)) : ∀ᵐ Y ∂Measure.pi ν,
      leftMoment (ν i) (f i (c ℓ)) (wordMultiplicity r i) (Y (c ℓ)) ≤
        ENNReal.ofReal (2 * L ^ wordMultiplicity r i * ((wordMultiplicity r i).factorial : ℝ)) :=
    (measurePreserving_eval ν (c ℓ)).quasiMeasurePreserving.ae
      (ae_moments_le_of_essSup_sum_le (ν i) (ν (c ℓ)) (f i (c ℓ)) _
        (hsource _ hi i (c ℓ))).1
  filter_upwards [ae_all_iff.mpr hslots] with Y hY
  exact integrable_finset_prod_and_integral_abs_le
    (Finset.univ.filter (fun ℓ => r ℓ = i)) hi (fun ℓ x => f i (c ℓ) x (Y (c ℓ)))
    (fun ℓ _ => (hf i (c ℓ)).comp (measurable_id.prodMk measurable_const))
    (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hL _)) (Nat.cast_nonneg _))
    (fun ℓ _ => hY ℓ)

/-- Product-probability integration separates all row coordinates exactly. -/
theorem integral_wordProduct_rows (r c : Fin (2 * k) → Fin m) (Y : ∀ i, α i) :
    (∫ X, wordProduct f r c (X, Y) ∂Measure.pi ν) =
      ∏ i, ∫ x, rowFiberProduct f r c i Y x ∂ν i := by
  simp_rw [← prod_rowFiberProduct f r c]
  exact integral_fintype_prod_eq_prod _

omit [∀ i, MeasurableSpace (α i)] in
/-- Zero multiplicities have factorial one, so only occupied rows matter. -/
theorem prod_factorial_support (r : Fin (2 * k) → Fin m) :
    (∏ i ∈ nonzeroSupport (wordMultiplicity r), ((wordMultiplicity r i).factorial : ℝ)) =
      ∏ i, ((wordMultiplicity r i).factorial : ℝ) := by
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  have hz : wordMultiplicity r i = 0 := by simpa [nonzeroSupport] using hi
  simp [hz]

omit [∀ i, MeasurableSpace (α i)] in
/-- The row factorial constants combine with the actual total slot count. -/
theorem prod_row_constants (r : Fin (2 * k) → Fin m) (L : ℝ) :
    (∏ i ∈ nonzeroSupport (wordMultiplicity r),
      2 * L ^ wordMultiplicity r i * ((wordMultiplicity r i).factorial : ℝ)) =
      2 ^ (nonzeroSupport (wordMultiplicity r)).card * L ^ (2 * k) *
        ∏ i, ((wordMultiplicity r i).factorial : ℝ) := by
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_pow_eq_pow_sum, sum_nonzeroSupport, sum_wordMultiplicity,
    prod_factorial_support]

/-- Almost every retained primed vector admits all the individual row bounds. -/
theorem ae_abs_integral_wordProduct_le_support
    (hf : ∀ i j, Measurable (Function.uncurry (f i j))) {L : ℝ} (hL : 0 ≤ L)
    (hsource : ∀ p : ℕ, 1 ≤ p → ∀ i j,
      essSup (leftMoment (ν i) (f i j) p) (ν j) +
        essSup (rightMoment (ν j) (f i j) p) (ν i) ≤
          ENNReal.ofReal (2 * L ^ p * (p.factorial : ℝ)))
    (r c : Fin (2 * k) → Fin m) :
    ∀ᵐ Y ∂Measure.pi ν,
      |∫ X, wordProduct f r c (X, Y) ∂Measure.pi ν| ≤
        2 ^ (nonzeroSupport (wordMultiplicity r)).card * L ^ (2 * k) *
          ∏ i, ((wordMultiplicity r i).factorial : ℝ) := by
  have hrows (i : Fin m) : ∀ᵐ Y ∂Measure.pi ν,
      i ∈ nonzeroSupport (wordMultiplicity r) →
        |∫ x, rowFiberProduct f r c i Y x ∂ν i| ≤
          2 * L ^ wordMultiplicity r i * ((wordMultiplicity r i).factorial : ℝ) := by
    by_cases hi : i ∈ nonzeroSupport (wordMultiplicity r)
    · have hn : 1 ≤ wordMultiplicity r i := by
        have := mem_nonzeroSupport.mp hi
        omega
      filter_upwards [ae_rowFiberProduct_bound ν f hf hL hsource r c i hn] with Y hY
      intro _
      exact abs_integral_le_integral_abs.trans hY.2
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hi h))
  filter_upwards [ae_all_iff.mpr hrows] with Y hY
  have hs : (∏ i ∈ nonzeroSupport (wordMultiplicity r),
      ∫ x, rowFiberProduct f r c i Y x ∂ν i) =
      ∏ i, ∫ x, rowFiberProduct f r c i Y x ∂ν i := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    have hz : wordMultiplicity r i = 0 := by simpa [nonzeroSupport] using hi
    simp_rw [rowFiberProduct_eq_one f r c i hz Y]
    simp
  rw [integral_wordProduct_rows ν f r c Y, ← hs, Finset.abs_prod, ← prod_row_constants r L]
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i hi => hY i hi)

/-- Actual word integrability follows from the source extended conditional moments. -/
theorem integrable_wordProduct_of_essSup_sum (hk : 1 ≤ k)
    (hf : ∀ i j, Measurable (Function.uncurry (f i j))) {L : ℝ}
    (hsource : ∀ p : ℕ, 1 ≤ p → ∀ i j,
      essSup (leftMoment (ν i) (f i j) p) (ν j) +
        essSup (rightMoment (ν j) (f i j) p) (ν i) ≤
          ENNReal.ofReal (2 * L ^ p * (p.factorial : ℝ)))
    (r c : Fin (2 * k) → Fin m) :
    Integrable (wordProduct f r c) ((Measure.pi ν).prod (Measure.pi ν)) := by
  have hn : 1 ≤ 2 * k := by omega
  exact integrable_wordProduct ν f hn
    (pairwise_memLp_of_essSup_sum ν f hn hf (hsource _ hn)) r c

/-- The exact source surviving-word estimate. Columns may repeat arbitrarily;
only the row word is required to have no singleton symbol. -/
theorem abs_integral_wordProduct_le (hk : 1 ≤ k)
    (hf : ∀ i j, Measurable (Function.uncurry (f i j))) {L : ℝ} (hL : 0 ≤ L)
    (hsource : ∀ p : ℕ, 1 ≤ p → ∀ i j,
      essSup (leftMoment (ν i) (f i j) p) (ν j) +
        essSup (rightMoment (ν j) (f i j) p) (ν i) ≤
          ENNReal.ofReal (2 * L ^ p * (p.factorial : ℝ)))
    (r c : Fin (2 * k) → Fin m) (hr : r ∈ singletonFreeWords m k) :
    |∫ Z, wordProduct f r c Z ∂(Measure.pi ν).prod (Measure.pi ν)| ≤
      2 ^ k * L ^ (2 * k) * ∏ i, ((wordMultiplicity r i).factorial : ℝ) := by
  have hP := integrable_wordProduct_of_essSup_sum ν f hk hf hsource r c
  have hs := ae_abs_integral_wordProduct_le_support ν f hf hL hsource r c
  have hnorm : ∀ᵐ Y ∂Measure.pi ν,
      ‖∫ X, wordProduct f r c (X, Y) ∂Measure.pi ν‖ ≤
        2 ^ (nonzeroSupport (wordMultiplicity r)).card * L ^ (2 * k) *
          ∏ i, ((wordMultiplicity r i).factorial : ℝ) := by
    simpa only [Real.norm_eq_abs] using hs
  have hb := norm_integral_le_of_norm_le_const hnorm
  have hb' : |∫ Y, ∫ X, wordProduct f r c (X, Y) ∂Measure.pi ν ∂Measure.pi ν| ≤
      2 ^ (nonzeroSupport (wordMultiplicity r)).card * L ^ (2 * k) *
        ∏ i, ((wordMultiplicity r i).factorial : ℝ) := by
    simpa only [Real.norm_eq_abs, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using hb
  rw [integral_prod_symm _ hP]
  refine hb'.trans ?_
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        ((word_support_card_le hr).trans (Nat.min_le_right _ _))
    · exact pow_nonneg hL _
  · exact Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)

end PeriodicAttractiveLogGas.CanonicalWordBounds
