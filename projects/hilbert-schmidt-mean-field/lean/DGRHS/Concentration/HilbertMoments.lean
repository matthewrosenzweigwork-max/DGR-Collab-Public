import DGRHS.Concentration.CovarianceMoments
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped InnerProductSpace
namespace DGRHS.Concentration

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

omit [MeasurableSpace H] [BorelSpace H] in
lemma empirical_norm_square_integral_le
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → H) (B : ℝ)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B)
    (hMean : ∀ i, ∫ x, Z i x ∂μ i = 0) :
    (∫ ω, (empiricalNormOnProduct Z ω)^2 ∂Measure.pi μ) ≤
      ∑ i, ∫ x, ‖Z i x‖^2 ∂μ i := by
  let b := stdOrthonormalBasis ℝ H
  let X := fun i a x ↦ inner ℝ (b a) (Z i x)
  have hx : ∀ i a, AEStronglyMeasurable (X i a) (μ i) := fun i a ↦
    (by fun_prop : Continuous (fun z : H ↦ inner ℝ (b a) z)).comp_aestronglyMeasurable (hZ i)
  have hxb : ∀ i a, ∀ᵐ x ∂μ i, |X i a x| ≤ B := fun i a ↦ (hB i).mono fun x hh ↦
    (abs_real_inner_le_norm _ _).trans (by simpa using hh)
  have hxc : ∀ i a, (∫ x, X i a x ∂μ i) = 0 := by
    intro i a
    rw [integral_inner (bounded_hilbert_integrable (hZ i) (hB i)),hMean i]
    simp
  have hxI : ∀ i a, Integrable (fun x ↦ (X i a x)^2) (μ i) := fun i a ↦
    (bounded_real_memLp (hx i a) (hxb i a) 2).integrable_sq
  have hsumI : ∀ a, Integrable (fun ω : Fin n → Ω ↦ (∑ i, X i a (ω i))^2) (Measure.pi μ) := by
    intro a
    have hb := centered_product_sum_bounded μ (fun i ↦ X i a) B (fun i ↦ hx i a) (fun i ↦ hxb i a)
    have hs := bounded_square hb.1 hb.2
    simpa only [hxc,sub_zero] using integrable_of_ae_abs_le hs.1 hs.2
  calc
    _ = ∫ ω, ∑ a, (∑ i, X i a (ω i))^2 ∂Measure.pi μ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun ω ↦ ?_
      unfold empiricalNormOnProduct empiricalNorm
      dsimp only
      rw [← b.sum_sq_inner_right]
      simp only [inner_sum]
      rfl
    _ = ∑ a, ∫ ω, (∑ i, X i a (ω i))^2 ∂Measure.pi μ := integral_finsetSum _ (fun a _ ↦ hsumI a)
    _ ≤ ∑ a, ∑ i, ∫ x, (X i a x)^2 ∂μ i := Finset.sum_le_sum fun a _ ↦ by
      simpa only [hxc,sub_zero] using centered_product_sum_square_le μ (fun i ↦ X i a) B (fun i ↦ hx i a) (fun i ↦ hxb i a)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [← integral_finsetSum _ (fun a _ ↦ hxI i a)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ b.sum_sq_inner_right (Z i x)

lemma empirical_norm_mean_le
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → H) (B C : ℝ) (hC : 0 ≤ C)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B)
    (hMean : ∀ i, ∫ x, Z i x ∂μ i = 0)
    (hTrace : (∑ i, ∫ x, ‖Z i x‖^2 ∂μ i) ≤ C^2) :
    (∫ ω, empiricalNormOnProduct Z ω ∂Measure.pi μ) ≤ C := by
  have hw := empirical_norm_product_aestronglyMeasurable μ Z hZ
  have hwb := empirical_norm_product_bounded μ Z B hB
  have hv := variance_nonneg (empiricalNormOnProduct Z) (Measure.pi μ)
  rw [variance_eq_sub (bounded_real_memLp hw hwb 2)] at hv
  simp only [Pi.pow_apply] at hv
  have hs := (empirical_norm_square_integral_le μ Z B hZ hB hMean).trans hTrace
  have hn : 0 ≤ ∫ ω, empiricalNormOnProduct Z ω ∂Measure.pi μ := integral_nonneg fun _ ↦ norm_nonneg _
  nlinarith

/-- One genuine nonnegative Taylor coefficient suffices for an integer moment. -/
lemma bounded_positive_mgf_moment {S : Type*} [MeasurableSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ] {W : S → ℝ} {B : ℝ}
    (hW : AEStronglyMeasurable W μ) (hB : ∀ᵐ x ∂μ, |W x| ≤ B)
    (hpos : ∀ x, 0 ≤ W x) (m : ℕ) (hm : 1 ≤ m) (t : ℝ) (ht : 0 < t)
    (hcgf : cgf W μ t ≤ (m : ℝ)) :
    (∫ x, (W x)^m ∂μ)^(1/(m : ℝ)) ≤ 3*((m : ℝ)/t) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hfacpos : 0 < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hWI := (bounded_real_memLp hW hB m).integrable_norm_pow'
  have hPowI : Integrable (fun x ↦ (W x)^m) μ := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hpos _)] using hWI
  have hs := scalar_mul_ae_bounded hW hB t
  have hf := bounded_exp_positive hs.1 hs.2
  have hmgf : mgf W μ t ≤ Real.exp (m : ℝ) := by
    calc
      _ = Real.exp (cgf W μ t) := (Real.exp_log hf.integral_pos).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcgf
  have hi := integral_mono ((hPowI.const_mul (t^m)).div_const (m.factorial : ℝ)) hf.integrable
    (fun x ↦ by simpa only [mul_pow] using Real.pow_div_factorial_le_exp (t*W x) (mul_nonneg ht.le (hpos x)) m)
  rw [integral_div,integral_const_mul] at hi
  have hscaled : t^m*(∫ x, (W x)^m ∂μ) ≤ (m.factorial : ℝ)*Real.exp (m : ℝ) := by
    have hh := (div_le_iff₀ hfacpos).mp (hi.trans hmgf)
    nlinarith
  have hfac : (m.factorial : ℝ) ≤ (m : ℝ)^m := by exact_mod_cast Nat.factorial_le_pow m
  have hscaled' := hscaled.trans (mul_le_mul_of_nonneg_right hfac (Real.exp_nonneg _))
  let R := (m : ℝ)/t
  have hR : 0 ≤ R := div_nonneg hmpos.le ht.le
  have htR : t*R=(m : ℝ) := by dsimp [R]; field_simp
  have hmul : (∫ x, (W x)^m ∂μ)*(m : ℝ)^m ≤ (Real.exp (m : ℝ)*R^m)*(m : ℝ)^m := by
    calc
      _ = (t^m*(∫ x, (W x)^m ∂μ))*R^m := by rw [← htR,mul_pow]; ring
      _ ≤ ((m : ℝ)^m*Real.exp (m : ℝ))*R^m := mul_le_mul_of_nonneg_right hscaled' (pow_nonneg hR m)
      _ = _ := by ring
  have hQ : 0 ≤ ∫ x, (W x)^m ∂μ := integral_nonneg fun x ↦ pow_nonneg (hpos x) m
  have hbound : (∫ x, (W x)^m ∂μ) ≤ (Real.exp 1*R)^m := by
    simpa only [mul_pow,Real.exp_one_pow] using
      (mul_le_mul_iff_right₀ (pow_pos hmpos m)).mp (by simpa only [mul_comm] using hmul)
  have hr := (Real.rpow_inv_le_iff_of_pos hQ (mul_nonneg (Real.exp_nonneg _) hR) hmpos).mpr
    (by simpa only [Real.rpow_natCast] using hbound)
  have hr' : (∫ x, (W x)^m ∂μ)^(1/(m : ℝ)) ≤ Real.exp 1*R := by simpa only [one_div] using hr
  exact hr'.trans (mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hR)

/-- A positive slack makes the choice valid even when every original scale vanishes. -/
lemma hilbert_moment_parameter (m : ℕ) (hm : 1 ≤ m) (B C D e : ℝ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (he : 0 < e) :
    let R := C+Real.sqrt (m : ℝ)*D+(m : ℝ)*B+e
    let t := (m : ℝ)/(4*R)
    0 < R ∧ 0 < t ∧ t*B ≤ 1/2 ∧ t*C ≤ (m : ℝ)/4 ∧
      t^2*D^2 ≤ (m : ℝ)/16 ∧ t^2*B*C ≤ (m : ℝ)/16 ∧ t*R=(m : ℝ)/4 := by
  dsimp only
  let R := C+Real.sqrt (m : ℝ)*D+(m : ℝ)*B+e
  let t := (m : ℝ)/(4*R)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hR : 0 < R := by dsimp [R]; positivity
  have ht : 0 < t := div_pos hmpos (by positivity)
  have htR : t*R=(m : ℝ)/4 := by dsimp [t]; field_simp
  have hRC : C ≤ R := by dsimp [R]; nlinarith [mul_nonneg (Real.sqrt_nonneg (m : ℝ)) hD,mul_nonneg hmpos.le hB]
  have hRB : (m : ℝ)*B ≤ R := by dsimp [R]; nlinarith [mul_nonneg (Real.sqrt_nonneg (m : ℝ)) hD]
  have hRD : Real.sqrt (m : ℝ)*D ≤ R := by dsimp [R]; nlinarith [mul_nonneg hmpos.le hB]
  have htb := mul_le_mul_of_nonneg_left hRB ht.le
  have htc := mul_le_mul_of_nonneg_left hRC ht.le
  have htd : (m : ℝ)*D^2 ≤ R^2 := by
    have hh := mul_self_le_mul_self (mul_nonneg (Real.sqrt_nonneg _) hD) hRD
    have hh' : (Real.sqrt (m : ℝ)*D)^2 ≤ R^2 := by simpa only [pow_two] using hh
    rw [mul_pow,Real.sq_sqrt hmpos.le] at hh'
    exact hh'
  have hbc : (m : ℝ)*B*C ≤ R^2 := by
    have hh := mul_le_mul hRB hRC hC hR.le
    nlinarith
  have htd' := mul_le_mul_of_nonneg_left htd (sq_nonneg t)
  have hbc' := mul_le_mul_of_nonneg_left hbc (sq_nonneg t)
  have htrsq : t^2*R^2=(m : ℝ)^2/16 := by nlinarith [sq_nonneg (t*R)]
  refine ⟨hR,ht,?_,?_,?_,?_,htR⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/-- Actual bounded Hilbert integer-moment bound; constant 12 replaces tail integration. -/
theorem finite_hilbert_integer_moment
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → H) (B C D : ℝ) (hBpos : 0 ≤ B) (hCpos : 0 ≤ C) (hDpos : 0 ≤ D)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B)
    (hMean : ∀ i, ∫ x, Z i x ∂μ i = 0)
    (hTrace : (∑ i, ∫ x, ‖Z i x‖^2 ∂μ i) ≤ C^2)
    (hWeak : ∀ u : H, ‖u‖ ≤ 1 → (∑ i, ∫ x, (inner ℝ u (Z i x))^2 ∂μ i) ≤ D^2)
    (m : ℕ) (hm : 1 ≤ m) :
    (∫ ω, (empiricalNormOnProduct Z ω)^m ∂Measure.pi μ)^(1/(m : ℝ)) ≤
      12*(C+Real.sqrt (m : ℝ)*D+(m : ℝ)*B) := by
  have hw := empirical_norm_product_aestronglyMeasurable μ Z hZ
  have hwb := empirical_norm_product_bounded μ Z B hB
  have hmean := empirical_norm_mean_le μ Z B C hCpos hZ hB hMean hTrace
  have hEV := empirical_quadratic_expectation_le μ Z B C D hBpos hCpos hZ hB hTrace hWeak
  have hh : ∀ e : ℝ, 0 < e → (∫ ω, (empiricalNormOnProduct Z ω)^m ∂Measure.pi μ)^(1/(m : ℝ)) ≤
      12*(C+Real.sqrt (m : ℝ)*D+(m : ℝ)*B+e) := by
    intro e he
    let R := C+Real.sqrt (m : ℝ)*D+(m : ℝ)*B+e
    let t := (m : ℝ)/(4*R)
    have hp := hilbert_moment_parameter m hm B C D e hBpos hCpos hDpos he
    change 0 < R ∧ 0 < t ∧ t*B ≤ 1/2 ∧ t*C ≤ (m : ℝ)/4 ∧
      t^2*D^2 ≤ (m : ℝ)/16 ∧ t^2*B*C ≤ (m : ℝ)/16 ∧ t*R=(m : ℝ)/4 at hp
    have hc := empirical_norm_centered_cgf_bound μ Z B D hZ hB hMean hWeak t hp.2.1.le hp.2.2.1 hBpos
    have hcgf : cgf (empiricalNormOnProduct Z) (Measure.pi μ) t ≤ (m : ℝ) := by
      have hm' := mul_le_mul_of_nonneg_left hmean hp.2.1.le
      have hv := mul_le_mul_of_nonneg_left hEV (show 0 ≤ 3*t^2 by positivity)
      nlinarith [hp.2.2.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2.1]
    have hb := bounded_positive_mgf_moment hw hwb (fun ω ↦ norm_nonneg _) m hm t hp.2.1 hcgf
    have hR : 3*((m : ℝ)/t)=12*R := by
      have htR := hp.2.2.2.2.2.2
      field_simp [hp.2.1.ne']
      nlinarith
    exact hb.trans_eq hR
  apply le_of_forall_pos_le_add
  intro e he
  have hi := hh (e/12) (by positivity)
  nlinarith

#print axioms DGRHS.Concentration.empirical_norm_mean_le
#print axioms DGRHS.Concentration.bounded_positive_mgf_moment
#print axioms DGRHS.Concentration.hilbert_moment_parameter
#print axioms DGRHS.Concentration.finite_hilbert_integer_moment
#check @DGRHS.Concentration.finite_hilbert_integer_moment
end DGRHS.Concentration
