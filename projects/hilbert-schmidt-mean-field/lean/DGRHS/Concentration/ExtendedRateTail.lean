import DGRHS.Concentration.ExtendedRateArithmetic

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DGRHS.Concentration

/-- A single universal constant for both iid-coupled and independent-copy endpoints. -/
def glzUniversalTailConstant : ℝ := Real.exp 1*(221184*Real.exp 1)^2
lemma glzUniversalTailConstant_pos : 0 < glzUniversalTailConstant := by
  unfold glzUniversalTailConstant
  positivity

/-- Explicit interpretation of the exponential at infinite rate. -/
def glzExtendedTailBound (t A B C D : ℝ) : ℝ :=
  if glzExtendedRate t A B C D = ∞ then 0 else
    glzUniversalTailConstant*Real.exp (-(glzExtendedRate t A B C D).toReal/glzUniversalTailConstant)

lemma glzExtendedTailBound_positive_scales (t A B C D : ℝ) (ht : 0 ≤ t)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) :
    glzExtendedTailBound t A B C D =
      glzUniversalTailConstant*Real.exp (-glzTailRate t A B C D/glzUniversalTailConstant) := by
  have he : glzExtendedRate t A B C D = ENNReal.ofReal (glzTailRate t A B C D) := by
    simp only [glzExtendedRate,glzRateTerm,ite_eq_right hA.ne',ite_eq_right hB.ne',
      ite_eq_right hC.ne',ite_eq_right hD.ne',glzTailRate,ENNReal.ofReal_min]
    norm_num
  unfold glzExtendedTailBound
  rw [he,ite_eq_right ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (glzTailRate_nonneg t A B C D ht hA.le hB.le hC.le hD.le)]

lemma scalar_even_scale_parameter_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (A B C D : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hI : ∀ k : ℕ, 1 ≤ k → Integrable (fun x ↦ |X x|^(2*k)) μ)
    (hMoment : ∀ k : ℕ, 1 ≤ k → (∫ x, |X x|^(2*k) ∂μ) ≤ (3456*glzScale (2*k) A B C D)^(2*k))
    (u t : ℝ) (hu : 1 ≤ u) (ht : 0 < t)
    (hThreshold : (55296*Real.exp 1)*glzRealScale u A B C D ≤ t) :
    μ.real {x | t ≤ |X x|} ≤ Real.exp (-u) := by
  have hk : 1 ≤ Nat.ceil u := Nat.one_le_ceil_iff.mpr (by linarith)
  have hmu : u ≤ ((2*Nat.ceil u : ℕ) : ℝ) := by
    have ht := Nat.le_ceil u
    push_cast
    linarith [show (0 : ℝ) ≤ (Nat.ceil u : ℝ) from Nat.cast_nonneg _]
  have hs := glz_scale_even_ceil_le u A B C D hu hA hB hC hD
  have hT : Real.exp 1*(3456*glzScale (2*Nat.ceil u) A B C D) ≤ t := by
    calc
      _ ≤ Real.exp 1*(3456*(16*glzRealScale u A B C D)) := by gcongr
      _ = (55296*Real.exp 1)*glzRealScale u A B C D := by ring
      _ ≤ t := hThreshold
  have hbnd := absolute_moment_exponential_tail μ X (2*Nat.ceil u) (hI _ hk)
    (3456*glzScale (2*Nat.ceil u) A B C D) t (by unfold glzScale; positivity) ht (hMoment _ hk) hT
  exact hbnd.trans (Real.exp_monotone (neg_le_neg hmu))

/-- Scalar support from genuine even moments; infinity-rate tail zero follows from
its actual second moment and Markov, and is not an assumed concentration conclusion. -/
lemma scalar_even_scale_extended_rate_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (A B C D : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hI : ∀ k : ℕ, 1 ≤ k → Integrable (fun x ↦ |X x|^(2*k)) μ)
    (hMoment : ∀ k : ℕ, 1 ≤ k → (∫ x, |X x|^(2*k) ∂μ) ≤ (3456*glzScale (2*k) A B C D)^(2*k))
    (t : ℝ) (ht : 0 < t) : μ.real {x | t ≤ |X x|} ≤ glzExtendedTailBound t A B C D := by
  by_cases hinf : glzExtendedRate t A B C D = ∞
  · obtain ⟨rfl,rfl,rfl,rfl⟩ := (glzExtendedRate_top_iff t A B C D).mp hinf
    have hm := hMoment 1 (by omega)
    simp only [glzScale,mul_zero,add_zero,zero_pow (by omega : 2*1 ≠ 0)] at hm
    have hb := absolute_moment_markov μ X 2 (by simpa using hI 1 (by omega)) t ht
    unfold glzExtendedTailBound
    rw [ite_eq_left hinf]
    exact hb.trans (by simpa using div_nonpos_of_nonpos_of_nonneg hm (sq_nonneg t))
  · unfold glzExtendedTailBound
    rw [ite_eq_right hinf]
    let b := 221184*Real.exp 1
    let K := 55296*Real.exp 1
    let r := (glzExtendedRate t A B C D).toReal
    let v := r/b^2
    have he : 1 ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp 1]
    have hb : 1 ≤ b := by dsimp [b]; nlinarith
    have hb0 : 0 < b := by linarith
    have hK : 0 < K := by dsimp [K]; positivity
    have hr : 0 ≤ r := ENNReal.toReal_nonneg
    have hv : 0 ≤ v := div_nonneg hr (sq_nonneg _)
    have hprob : μ.real {x | t ≤ |X x|} ≤ Real.exp 1*Real.exp (-v) := by
      by_cases hv1 : 1 ≤ v
      · have hsc := glz_extended_rate_scaled_threshold t A B C D b ht.le hA hB hC hD hb
        have hth : K*glzRealScale v A B C D ≤ t := by
          calc
            _ ≤ K*(4*(t/b)) := mul_le_mul_of_nonneg_left hsc hK.le
            _ = t := by dsimp [K,b]; field_simp; ring
        have htail := scalar_even_scale_parameter_tail μ X A B C D hA hB hC hD hI hMoment v t hv1 ht hth
        exact htail.trans (by nlinarith [Real.exp_pos (-v)])
      · apply (probability_real_set_le_one μ {x | t ≤ |X x|}).trans
        rw [← Real.exp_add,show (1 : ℝ)+ -v = 1-v by ring]
        have hh := Real.add_one_le_exp (1-v)
        linarith
    have hL : glzUniversalTailConstant = Real.exp 1*b^2 := rfl
    have hb2 : 1 ≤ b^2 := by nlinarith
    have hLge : b^2 ≤ glzUniversalTailConstant := by rw [hL]; nlinarith
    have hLexp : Real.exp 1 ≤ glzUniversalTailConstant := by rw [hL]; nlinarith [Real.exp_pos 1]
    have hdiv : r/glzUniversalTailConstant ≤ r/b^2 :=
      div_le_div_of_nonneg_left hr (sq_pos_of_pos hb0) hLge
    have hexp : Real.exp (-v) ≤ Real.exp (-r/glzUniversalTailConstant) := by
      apply Real.exp_monotone
      simpa only [neg_div] using neg_le_neg hdiv
    exact hprob.trans (mul_le_mul hLexp hexp (Real.exp_nonneg (-v)) glzUniversalTailConstant_pos.le)

/-- Concrete source GLZ independent-copy minimum tail with actual essential A/B/C/D.
Every zero control is covered by the explicit infinity convention. -/
theorem kernel_actual_extended_rate_tail {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace.CountablyGenerated Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ)
    (hh : ∀ i j, MemLp (h i j) ∞ ((μ i).prod (ν j)))
    (hMeanRight : ∀ i j, ∀ᵐ x ∂μ i, ∫ y, h i j (x,y) ∂ν j = 0)
    (hMeanLeft : ∀ i j, ∀ᵐ y ∂ν j, ∫ x, h i j (x,y) ∂μ i = 0)
    (t : ℝ) (ht : 0 < t) :
    ((Measure.pi μ).prod (Measure.pi ν)).real {p | t ≤ |kernelDecoupledSum h p|} ≤
      glzExtendedTailBound t (kernelSourceA μ ν h) (kernelSourceB μ ν h)
        (kernelSourceC μ ν h) (kernelSourceD μ ν h) := by
  obtain ⟨ha,hb,hc,hbound,_,_,_⟩ := kernelSourceABC_controls μ ν h hh
  have hAES := fun i j ↦ (hh i j).aestronglyMeasurable
  have hd := (kernelSourceD_controls μ ν h (kernelSourceA μ ν h) ha hAES hbound).1
  apply scalar_even_scale_extended_rate_tail _ (kernelDecoupledSum h) _ _ _ _ ha hb hc hd
    (fun k _ ↦ kernel_decoupled_moment_integrable μ ν h (kernelSourceA μ ν h) hAES hbound (2*k)) _ t ht
  intro k hk
  have he := kernel_even_four_scale_power_actual μ ν h hh hMeanRight hMeanLeft k hk
  have hsn : 0 ≤ glzScale (2*k) (kernelSourceA μ ν h) (kernelSourceB μ ν h)
      (kernelSourceC μ ν h) (kernelSourceD μ ν h) := by unfold glzScale; positivity
  apply he.trans
  apply pow_le_pow_left₀ (by positivity)
  nlinarith

/-- Concrete source iid symmetric off-diagonal minimum tail, including N=0/1,
all zero controls, and true factor-four decoupling. No desired tail premise is used. -/
theorem iid_actual_extended_rate_tail {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (h : Ω × Ω → ℝ) (hm : Measurable h)
    (hh : MemLp h ∞ (μ.prod μ)) (hsymm : ∀ x y, h (x,y) = h (y,x))
    (hr : ∀ᵐ x ∂μ, ∫ y, h (x,y) ∂μ = 0) (t : ℝ) (ht : 0 < t) :
    (Measure.pi (fun _ : Fin n ↦ μ)).real {ω | t ≤ |iidCoupledSum n h ω|} ≤
      glzExtendedTailBound t (iidSourceA μ n h) (iidSourceB μ n h)
        (iidSourceC μ n h) (iidSourceD μ n h) := by
  obtain ⟨ha,hb,hc,hd⟩ := iid_source_scales_nonneg μ n h hh
  apply scalar_even_scale_extended_rate_tail _ (iidCoupledSum n h) _ _ _ _ ha hb hc hd
    _ (fun k hk ↦ iid_even_four_scale_power μ n h hm hh hsymm hr k hk) t ht
  intro k _
  simpa only [Real.norm_eq_abs] using (iid_coupled_memLp μ n h hh (2*k : ℕ)).integrable_norm_pow'

#print axioms DGRHS.Concentration.glzExtendedTailBound_positive_scales
#print axioms DGRHS.Concentration.scalar_even_scale_extended_rate_tail
#print axioms DGRHS.Concentration.kernel_actual_extended_rate_tail
#print axioms DGRHS.Concentration.iid_actual_extended_rate_tail
#check @DGRHS.Concentration.kernel_actual_extended_rate_tail
#check @DGRHS.Concentration.iid_actual_extended_rate_tail
end DGRHS.Concentration
