import DGRHS.Concentration.FourScale

noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Concentration

lemma absolute_moment_markov {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (m : ℕ)
    (hI : Integrable (fun x ↦ |X x|^m) μ) (t : ℝ) (ht : 0 < t) :
    μ.real {x | t ≤ |X x|} ≤ (∫ x, |X x|^m ∂μ)/t^m := by
  have hp : 0 < t^m := pow_pos ht _
  have hN : 0 ≤ (∫ x, |X x|^m ∂μ)/t^m := by
    exact div_nonneg (integral_nonneg fun x ↦ pow_nonneg (abs_nonneg _) _) hp.le
  have hi := hI.div_const (t^m)
  have hb := hi.measure_le_integral
    (Filter.Eventually.of_forall (fun x ↦ div_nonneg (pow_nonneg (abs_nonneg _) _) hp.le))
    (s := {x | t ≤ |X x|}) (fun x hx ↦ by
      apply (le_div_iff₀ hp).mpr
      simpa only [one_mul] using pow_le_pow_left₀ ht.le hx m)
  have he : (∫ x, |X x|^m/t^m ∂μ) = (∫ x, |X x|^m ∂μ)/t^m := by
    simp only [div_eq_mul_inv,integral_mul_const]
  rw [he] at hb
  exact ENNReal.toReal_le_of_le_ofReal hN hb

lemma absolute_moment_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (m : ℕ)
    (hI : Integrable (fun x ↦ |X x|^m) μ) (R t : ℝ) (hR : 0 ≤ R) (ht : 0 < t)
    (hMoment : (∫ x, |X x|^m ∂μ) ≤ R^m) (hThreshold : Real.exp 1*R ≤ t) :
    μ.real {x | t ≤ |X x|} ≤ Real.exp (-(m : ℝ)) := by
  have hRatio : R/t ≤ Real.exp (-1) := by
    apply (div_le_iff₀ ht).mpr
    have hh := mul_le_mul_of_nonneg_left hThreshold (Real.exp_nonneg (-1))
    have he : Real.exp (-1)*(Real.exp 1*R) = R := by
      rw [← mul_assoc,← Real.exp_add]
      norm_num
    rwa [he] at hh
  calc
    _ ≤ (∫ x, |X x|^m ∂μ)/t^m := absolute_moment_markov μ X m hI t ht
    _ ≤ R^m/t^m := div_le_div_of_nonneg_right hMoment (pow_nonneg ht.le _)
    _ = (R/t)^m := (div_pow _ _ _).symm
    _ ≤ (Real.exp (-1))^m := pow_le_pow_left₀ (div_nonneg hR ht.le) hRatio _
    _ = Real.exp (-(m : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- Actual exponential tail from the checked kernel even moments, at a positive threshold. -/
theorem kernel_even_four_scale_tail {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace.CountablyGenerated Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ) (A B C D : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A)
    (hMeanRight : ∀ i j, ∀ᵐ x ∂μ i, ∫ y, h i j (x,y) ∂ν j = 0)
    (hMeanLeft : ∀ i j, ∀ᵐ y ∂ν j, ∫ x, h i j (x,y) ∂μ i = 0)
    (hRow : ∀ i, ∀ᵐ x ∂μ i, (∑ j, ∫ y, (h i j (x,y))^2 ∂ν j) ≤ B^2)
    (hColumn : ∀ j, ∀ᵐ y ∂ν j, kernelColumnEnergy μ h j y ≤ B^2)
    (hTrace : (∑ i, ∑ j, ∫ p, (h i j p)^2 ∂(μ i).prod (ν j)) ≤ C^2)
    (hTest : ∀ (f : PiLp 2 (fun i ↦ Lp ℝ 2 (μ i)))
      (g : PiLp 2 (fun j ↦ Lp ℝ 2 (ν j))), ‖f‖ ≤ 1 → ‖g‖ ≤ 1 → kernelL2Bilinear μ ν h f g ≤ D)
    (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht : 0 < t)
    (hThreshold : Real.exp 1*(864*glzScale (2*k) A B C D) ≤ t) :
    ((Measure.pi μ).prod (Measure.pi ν)).real {p | t ≤ |kernelDecoupledSum h p|} ≤ Real.exp (-((2*k : ℕ) : ℝ)) := by
  apply absolute_moment_exponential_tail _ (kernelDecoupledSum h) (2*k)
    (kernel_decoupled_moment_integrable μ ν h A hAES hBound (2*k))
    (864*glzScale (2*k) A B C D) t (by unfold glzScale; positivity) ht
    (kernel_even_four_scale_power μ ν h A B C D hA hB hC hD hAES hBound
      hMeanRight hMeanLeft hRow hColumn hTrace hTest k hk) hThreshold

#print axioms DGRHS.Concentration.absolute_moment_markov
#print axioms DGRHS.Concentration.kernel_even_four_scale_tail
#check @DGRHS.Concentration.kernel_even_four_scale_tail
end DGRHS.Concentration
