import DGRHS.Concentration.TailRateArithmetic

noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Concentration

def glzTailConstant : ℝ := Real.exp 1*(55296*Real.exp 1)^2

lemma glzTailConstant_pos : 0 < glzTailConstant := by unfold glzTailConstant; positivity

lemma probability_real_set_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) : μ.real s ≤ 1 := by
  apply ENNReal.toReal_le_of_le_ofReal (by norm_num)
  simpa using (show μ s ≤ μ Set.univ from measure_mono (Set.subset_univ s))

/-- The displayed four-regime minimum tail, for strictly positive source controls. -/
theorem kernel_four_scale_rate_tail {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace.CountablyGenerated Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ) (A B C D : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A)
    (hMeanRight : ∀ i j, ∀ᵐ x ∂μ i, ∫ y, h i j (x,y) ∂ν j = 0)
    (hMeanLeft : ∀ i j, ∀ᵐ y ∂ν j, ∫ x, h i j (x,y) ∂μ i = 0)
    (hRow : ∀ i, ∀ᵐ x ∂μ i, (∑ j, ∫ y, (h i j (x,y))^2 ∂ν j) ≤ B^2)
    (hColumn : ∀ j, ∀ᵐ y ∂ν j, kernelColumnEnergy μ h j y ≤ B^2)
    (hTrace : (∑ i, ∑ j, ∫ p, (h i j p)^2 ∂(μ i).prod (ν j)) ≤ C^2)
    (hTest : ∀ (f : PiLp 2 (fun i ↦ Lp ℝ 2 (μ i)))
      (g : PiLp 2 (fun j ↦ Lp ℝ 2 (ν j))), ‖f‖ ≤ 1 → ‖g‖ ≤ 1 → kernelL2Bilinear μ ν h f g ≤ D)
    (t : ℝ) (ht : 0 < t) :
    ((Measure.pi μ).prod (Measure.pi ν)).real {p | t ≤ |kernelDecoupledSum h p|} ≤
      glzTailConstant*Real.exp (-glzTailRate t A B C D/glzTailConstant) := by
  let b := 55296*Real.exp 1
  let K := 13824*Real.exp 1
  let r := glzTailRate t A B C D
  let v := glzTailRate (t/b) A B C D
  have he : 1 ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp 1]
  have hb : 1 ≤ b := by dsimp [b]; nlinarith
  have hb0 : 0 < b := by linarith
  have hK : 0 < K := by dsimp [K]; positivity
  have hv : 0 ≤ v := glzTailRate_nonneg _ _ _ _ _ (div_nonneg ht.le hb0.le) hA.le hB.le hC.le hD.le
  have hr : 0 ≤ r := glzTailRate_nonneg _ _ _ _ _ ht.le hA.le hB.le hC.le hD.le
  have hlower : r/b^2 ≤ v := glz_rate_scaled_lower t A B C D b ht.le hA.le hB.le hC.le hD.le hb
  have hprob : ((Measure.pi μ).prod (Measure.pi ν)).real {p | t ≤ |kernelDecoupledSum h p|} ≤
      Real.exp 1*Real.exp (-v) := by
    by_cases hv1 : 1 ≤ v
    · have hsc := glz_rate_threshold v (t/b) A B C D hv (div_nonneg ht.le hb0.le) hA hB hC hD le_rfl
      have hth : K*glzRealScale v A B C D ≤ t := by
        calc
          _ ≤ K*(4*(t/b)) := mul_le_mul_of_nonneg_left hsc hK.le
          _ = t := by dsimp [K,b]; field_simp; ring
      have htail := kernel_four_scale_parameter_tail μ ν h A B C D hA.le hB.le hC.le hD.le hAES hBound
        hMeanRight hMeanLeft hRow hColumn hTrace hTest v t hv1 ht hth
      exact htail.trans (by nlinarith [Real.exp_pos (-v)])
    · have ht1 := probability_real_set_le_one ((Measure.pi μ).prod (Measure.pi ν)) {p | t ≤ |kernelDecoupledSum h p|}
      apply ht1.trans
      rw [← Real.exp_add,show (1 : ℝ)+ -v = 1-v by ring]
      have hh := Real.add_one_le_exp (1-v)
      linarith
  have hL : glzTailConstant = Real.exp 1*b^2 := rfl
  have hb2 : 1 ≤ b^2 := by nlinarith
  have hLge : b^2 ≤ glzTailConstant := by rw [hL]; nlinarith
  have hLexp : Real.exp 1 ≤ glzTailConstant := by rw [hL]; nlinarith [Real.exp_pos 1]
  have hdiv : r/glzTailConstant ≤ r/b^2 :=
    div_le_div_of_nonneg_left hr (sq_pos_of_pos hb0) hLge
  have hexp : Real.exp (-v) ≤ Real.exp (-r/glzTailConstant) := by
    apply Real.exp_monotone
    have hh := hdiv.trans hlower
    simpa only [neg_div] using neg_le_neg hh
  exact hprob.trans (mul_le_mul hLexp hexp (Real.exp_nonneg (-v)) glzTailConstant_pos.le)

#print axioms DGRHS.Concentration.kernel_four_scale_rate_tail
#check @DGRHS.Concentration.kernel_four_scale_rate_tail
end DGRHS.Concentration
