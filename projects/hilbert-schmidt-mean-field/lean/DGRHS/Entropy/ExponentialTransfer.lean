/- Exponential-to-entropy transfer with proper competitor integrability
DERIVED from finite KL. Bounded truncations and genuine Fatou exclude the
improper-Bochner fallback. This is a needed DV dependency, not physical input. -/
import DGRHS.Entropy.GibbsEntropyRewrite
import DGRHS.Gaussian.GaussianLogPhaseL2
noncomputable section
open MeasureTheory InformationTheory Filter
open scoped Topology ENNReal
namespace DGRHS.Entropy

theorem entropy_integrable_abs_of_exponential {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (u : Ω→ℝ) (hu : StronglyMeasurable u)
    (hexp : Integrable (fun x=>Real.exp |u x|) μ) (hKL : klDiv ν μ≠∞) :
    Integrable u ν ∧ (∫ x,|u x| ∂ν)≤
      (klDiv ν μ).toReal+Real.log (∫ x,Real.exp |u x| ∂μ) := by
  obtain ⟨hac,hL⟩ := klDiv_ne_top_iff.mp hKL
  let f := fun n : ℕ=>fun x=>min |u x| (n:ℝ)
  have hUm : StronglyMeasurable (fun x=>|u x|) := by
    simpa only [Real.norm_eq_abs] using hu.norm
  have hfm (n : ℕ) : StronglyMeasurable (f n) := (hUm.measurable.min measurable_const).stronglyMeasurable
  have hfp (n : ℕ) (x : Ω) : 0≤f n x := le_min (abs_nonneg _) (Nat.cast_nonneg _)
  have hfi (n : ℕ) : Integrable (f n) ν := by
    apply (integrable_const (n:ℝ)).mono' (hfm n).aestronglyMeasurable
    exact Eventually.of_forall fun x=>by
      rw [Real.norm_of_nonneg (hfp n x)]
      exact min_le_right _ _
  have he (n : ℕ) : Integrable (fun x=>Real.exp (f n x)) μ := by
    apply hexp.mono' (Real.continuous_exp.comp_aestronglyMeasurable (hfm n).aestronglyMeasurable)
    exact Eventually.of_forall fun x=>by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (min_le_left _ _)
  have hb (n : ℕ) : (∫ x,f n x ∂ν)≤
      (klDiv ν μ).toReal+Real.log (∫ x,Real.exp |u x| ∂μ) := by
    have hv := gibbsEntropy_variational_lower μ ν (f n) hac (hfi n) (he n) hL
    have hi : (∫ x,Real.exp (f n x) ∂μ)≤∫ x,Real.exp |u x| ∂μ :=
      integral_mono (he n) hexp fun x=>Real.exp_le_exp.mpr (min_le_left _ _)
    exact hv.trans (add_le_add le_rfl (Real.log_le_log (integral_exp_pos (he n)) hi))
  have hc : ∀ᵐ x ∂ν,Tendsto (fun n=>f n x) atTop (𝓝 |u x|) := by
    apply Eventually.of_forall
    intro x
    have hlarge : ∀ᶠ n : ℕ in atTop,|u x|≤(n:ℝ) :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ=>(n:ℝ)) atTop atTop).eventually
        (eventually_ge_atTop |u x|)
    exact tendsto_const_nhds.congr' (hlarge.mono fun n hn=>(min_eq_left hn).symm)
  obtain ⟨hi,hb⟩ := DGRHS.Gaussian.nonnegative_integrable_of_ae_tendsto_uniform_integral ν f
    (fun x=>|u x|) hfi hfp hUm (fun x=>abs_nonneg _) _ hb hc
  refine ⟨?_,hb⟩
  exact hi.mono' hu.aestronglyMeasurable (Eventually.of_forall fun x=>by rw [Real.norm_eq_abs])
lemma integrable_exp_abs_of_two_signs {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (u : Ω→ℝ) (hu : StronglyMeasurable u)
    (hp : Integrable (fun x=>Real.exp (u x)) μ)
    (hm : Integrable (fun x=>Real.exp (-u x)) μ) :
    Integrable (fun x=>Real.exp |u x|) μ := by
  apply (hp.add hm).mono'
    (Real.continuous_exp.comp_aestronglyMeasurable hu.norm.aestronglyMeasurable)
  apply Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  simp only [Real.norm_eq_abs, Pi.add_apply]
  by_cases h : 0≤u x
  · rw [abs_of_nonneg h]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_neg (lt_of_not_ge h)]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

/-- Both signs have the original individual normalizers. Proper competitor
expectation follows from finite KL; the sharp estimate does not lose log 2. -/
theorem entropy_two_signs_of_exponential {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (u : Ω→ℝ) (hu : StronglyMeasurable u)
    (hp : Integrable (fun x=>Real.exp (u x)) μ)
    (hm : Integrable (fun x=>Real.exp (-u x)) μ) (hKL : klDiv ν μ≠∞) :
    Integrable u ν ∧
      (∫ x,u x ∂ν)≤(klDiv ν μ).toReal+Real.log (∫ x,Real.exp (u x) ∂μ) ∧
      -(∫ x,u x ∂ν)≤(klDiv ν μ).toReal+Real.log (∫ x,Real.exp (-u x) ∂μ) := by
  have hi := (entropy_integrable_abs_of_exponential μ ν u hu
    (integrable_exp_abs_of_two_signs μ u hu hp hm) hKL).1
  obtain ⟨hac,hL⟩ := klDiv_ne_top_iff.mp hKL
  refine ⟨hi,gibbsEntropy_variational_lower μ ν u hac hi hp hL,?_⟩
  simpa only [integral_neg] using
    gibbsEntropy_variational_lower μ ν (fun x=>-u x) hac hi.neg hm hL

theorem entropy_abs_of_two_exponential_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (u : Ω→ℝ) (hu : StronglyMeasurable u)
    (hp : Integrable (fun x=>Real.exp (u x)) μ)
    (hm : Integrable (fun x=>Real.exp (-u x)) μ) (hKL : klDiv ν μ≠∞)
    (C : ℝ) (hCp : (∫ x,Real.exp (u x) ∂μ)≤C)
    (hCm : (∫ x,Real.exp (-u x) ∂μ)≤C) :
    Integrable u ν ∧ |∫ x,u x ∂ν|≤(klDiv ν μ).toReal+Real.log C := by
  obtain ⟨hi,hp',hm'⟩ := entropy_two_signs_of_exponential μ ν u hu hp hm hKL
  refine ⟨hi,abs_le.mpr ⟨?_,?_⟩⟩
  · have h := hm'.trans (add_le_add le_rfl (Real.log_le_log (integral_exp_pos hm) hCm))
    linarith
  · exact hp'.trans (add_le_add le_rfl (Real.log_le_log (integral_exp_pos hp) hCp))

/-- Source eq:expDV with the actual positive epsilon and two signs. -/
theorem entropy_abs_scaled_of_two_exponential_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (u : Ω→ℝ) (hu : StronglyMeasurable u) (ε : ℝ) (hε : 0<ε)
    (hp : Integrable (fun x=>Real.exp (ε*u x)) μ)
    (hm : Integrable (fun x=>Real.exp (-(ε*u x))) μ) (hKL : klDiv ν μ≠∞)
    (C : ℝ) (hCp : (∫ x,Real.exp (ε*u x) ∂μ)≤C)
    (hCm : (∫ x,Real.exp (-(ε*u x)) ∂μ)≤C) :
    Integrable u ν ∧ |∫ x,u x ∂ν|≤ε⁻¹*((klDiv ν μ).toReal+Real.log C) := by
  obtain ⟨hi,hb⟩ := entropy_abs_of_two_exponential_bounds μ ν
    (fun x=>ε*u x) (hu.const_mul ε) hp hm hKL C hCp hCm
  have hiu : Integrable u ν := by
    have h := hi.const_mul ε⁻¹
    simpa only [←mul_assoc,inv_mul_cancel₀ hε.ne',one_mul] using h
  rw [integral_const_mul,abs_mul,abs_of_pos hε] at hb
  have hd : |∫ x,u x ∂ν|≤((klDiv ν μ).toReal+Real.log C)/ε :=
    (le_div_iff₀ hε).mpr (by simpa only [mul_comm] using hb)
  exact ⟨hiu,by simpa only [div_eq_mul_inv,mul_comm] using hd⟩

end DGRHS.Entropy
#check @DGRHS.Entropy.entropy_integrable_abs_of_exponential
#print axioms DGRHS.Entropy.entropy_integrable_abs_of_exponential
#check @DGRHS.Entropy.integrable_exp_abs_of_two_signs
#check @DGRHS.Entropy.entropy_two_signs_of_exponential
#check @DGRHS.Entropy.entropy_abs_of_two_exponential_bounds
#print axioms DGRHS.Entropy.integrable_exp_abs_of_two_signs
#print axioms DGRHS.Entropy.entropy_two_signs_of_exponential
#print axioms DGRHS.Entropy.entropy_abs_of_two_exponential_bounds
#check @DGRHS.Entropy.entropy_abs_scaled_of_two_exponential_bounds
#print axioms DGRHS.Entropy.entropy_abs_scaled_of_two_exponential_bounds
