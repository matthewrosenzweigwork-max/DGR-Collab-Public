import DGRHS.Attractive.RowMoments
import Mathlib.Analysis.MeanInequalities

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.Attractive

/-- Equal-exponent Young inequality supplies a proper dominating sum. -/
lemma abs_prod_le_mean_powers {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) :
    |∏ i ∈ s, f i| ≤ (s.card : ℝ)⁻¹ * ∑ i ∈ s, |f i|^s.card := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have hw : ∑ i ∈ s, (s.card : ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hc
  have hroot (i : ι) : (|f i|^s.card : ℝ)^((s.card : ℝ)⁻¹) = |f i| := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), mul_inv_cancel₀ hc,
      Real.rpow_one]
  have h := Real.geom_mean_le_arith_mean_weighted s
    (fun _ ↦ (s.card : ℝ)⁻¹) (fun i ↦ |f i|^s.card)
    (fun _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)) hw
    (fun _ _ ↦ pow_nonneg (abs_nonneg _) _)
  simpa only [hroot, ← Finset.abs_prod, ← Finset.mul_sum] using h

/-- Source row Hölder bound, with properness established by the same domination. -/
lemma row_product_integrable_bound {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : Ω × Ω → ℝ)
    (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (s : Finset ι) (y : ι → Ω) :
    Integrable (fun x ↦ ∏ i ∈ s, h (x,y i)) μ ∧
    (∫ x, |∏ i ∈ s, h (x,y i)| ∂μ) ≤ C^s.card * (s.card.factorial : ℝ) := by
  classical
  by_cases hs : s.Nonempty
  · let M : ℝ := C^s.card * (s.card.factorial : ℝ)
    let g : Ω → ℝ := fun x ↦ (s.card : ℝ)⁻¹ * ∑ i ∈ s, |h (x,y i)|^s.card
    have hp : 1 ≤ s.card := hs.card_pos
    have hg : Integrable g μ :=
      (integrable_finsetSum s (fun i _ ↦ hC.proper s.card hp (y i))).const_mul _
    have hm : AEStronglyMeasurable (fun x ↦ ∏ i ∈ s, h (x,y i)) μ := by
      apply (Finset.measurable_prod s (fun i _ ↦ hh.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable
    have hdom : ∀ᵐ x ∂μ, ‖∏ i ∈ s, h (x,y i)‖ ≤ g x :=
      Filter.Eventually.of_forall fun x ↦ by
        simpa only [Real.norm_eq_abs] using abs_prod_le_mean_powers s hs (fun i ↦ h (x,y i))
    have hi := hg.mono' hm hdom
    refine ⟨hi, ?_⟩
    have hmean : (∫ x, g x ∂μ) ≤ M := by
      unfold g
      rw [integral_const_mul, integral_finsetSum]
      · calc
          _ ≤ (s.card : ℝ)⁻¹ * ∑ _i ∈ s, M :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ hC.bound s.card hp (y i)))
              (inv_nonneg.mpr (Nat.cast_nonneg _))
          _ = M := by
            have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
            simp only [Finset.sum_const,nsmul_eq_mul]
            rw [← mul_assoc,inv_mul_cancel₀ hc,one_mul]
      · intro i _
        exact hC.proper s.card hp (y i)
    exact (integral_mono_ae hi.norm hg hdom).trans hmean
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp

#check @DGRHS.Attractive.row_product_integrable_bound
#print axioms DGRHS.Attractive.row_product_integrable_bound
end DGRHS.Attractive
