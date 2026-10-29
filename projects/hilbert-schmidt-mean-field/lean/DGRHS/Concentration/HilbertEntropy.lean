import DGRHS.Concentration.HilbertReplacement
import DGRHS.Concentration.BoundedMGF

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped InnerProductSpace
namespace DGRHS.Concentration

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

lemma empirical_norm_product_aestronglyMeasurable
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → H) (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i)) :
    AEStronglyMeasurable (empiricalNormOnProduct Z) (Measure.pi μ) := by
  have hc : Continuous (empiricalNorm : (Fin n → H) → ℝ) := by
    unfold empiricalNorm
    fun_prop
  exact (hc.measurable.comp_aemeasurable (empirical_product_tuple_aemeasurable μ Z hZ)).aestronglyMeasurable

omit [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
lemma empirical_norm_product_bounded
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → H) (B : ℝ)
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B) :
    ∀ᵐ ω ∂Measure.pi μ, |empiricalNormOnProduct Z ω| ≤ (n : ℝ)*B := by
  have hj : ∀ᵐ ω ∂Measure.pi μ, ∀ i, ‖Z i (ω i)‖ ≤ B := ae_all_iff.mpr fun i ↦
    (measurePreserving_pi_coordinate μ i).quasiMeasurePreserving.ae (hB i)
  filter_upwards [hj] with ω hω
  unfold empiricalNormOnProduct empiricalNorm
  rw [abs_of_nonneg (norm_nonneg _)]
  calc
    _ ≤ ∑ i, ‖Z i (ω i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum fun i _ ↦ hω i
    _ = _ := by simp

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
lemma empirical_quadratic_product_bounded
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → H) (B : ℝ)
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B) :
    ∀ᵐ ω ∂Measure.pi μ, |empiricalQuadraticOnProduct Z ω| ≤ (n : ℝ)*B^2 := by
  have hj : ∀ᵐ ω ∂Measure.pi μ, ∀ i, ‖Z i (ω i)‖ ≤ B := ae_all_iff.mpr fun i ↦
    (measurePreserving_pi_coordinate μ i).quasiMeasurePreserving.ae (hB i)
  filter_upwards [hj] with ω hω
  change |empiricalQuadratic (fun i ↦ Z i (ω i))| ≤ _
  rw [abs_of_nonneg (empirical_quadratic_nonneg _)]
  exact empirical_quadratic_le_uniform _ B hω

/-- Actual H1 and product replacement entropy give norm entropy; no entropy premise. -/
theorem empirical_norm_entropy
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → H) (B D : ℝ)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B)
    (hMean : ∀ i, ∫ x, Z i x ∂μ i = 0)
    (hWeak : ∀ u : H, ‖u‖ ≤ 1 → (∑ i, ∫ x, (inner ℝ u (Z i x))^2 ∂μ i) ≤ D^2)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    functionalEntropy (Measure.pi μ) (fun ω ↦ Real.exp (lam*empiricalNormOnProduct Z ω)) ≤
      lam^2*(∫ ω, Real.exp (lam*empiricalNormOnProduct Z ω)*
        (empiricalQuadraticOnProduct Z ω+D^2) ∂Measure.pi μ) := by
  let W := empiricalNormOnProduct Z
  let V := empiricalQuadraticOnProduct Z
  have hw := empirical_norm_product_aestronglyMeasurable μ Z hZ
  have hwb := empirical_norm_product_bounded μ Z B hB
  have hv := empirical_quadratic_product_aestronglyMeasurable μ Z hZ
  have hvb := empirical_quadratic_product_bounded μ Z B hB
  have hs := scalar_mul_ae_bounded hw hwb lam
  have hf := bounded_exp_positive hs.1 hs.2
  have ha : ∀ᵐ ω ∂Measure.pi μ, |V ω+D^2| ≤ (n : ℝ)*B^2+|D^2| := hvb.mono fun ω hω ↦
    (abs_add_le _ _).trans (add_le_add hω le_rfl)
  have hr := bounded_mul_integrable hf.measurable (hv.add_const (D^2))
    (hf.bounds.mono fun _ hx ↦ abs_le_of_bounds hx.1 hx.2) ha
  have hi := integral_mono_ae (weighted_replacement_variance_integrable μ hw hwb lam) hr
    (Filter.Eventually.of_forall fun ω ↦ mul_le_mul_of_nonneg_left
      (empirical_norm_replacement_variance_le μ Z B D hZ hB hMean hWeak ω) (Real.exp_pos _).le)
  exact (finite_product_conditional_replacement_entropy n μ W ((n : ℝ)*B) hw hwb lam hlam).trans
    (mul_le_mul_of_nonneg_left hi (sq_nonneg lam))

/-- The entropy absorption step, including integrability of the actual quadratic test. -/
theorem empirical_norm_cgf_differential
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → H) (B D : ℝ)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B)
    (hMean : ∀ i, ∫ x, Z i x ∂μ i = 0)
    (hWeak : ∀ u : H, ‖u‖ ≤ 1 → (∑ i, ∫ x, (inner ℝ u (Z i x))^2 ∂μ i) ≤ D^2)
    (lam : ℝ) (hlam : 0 ≤ lam) (hBlam : lam*B ≤ 1/2) (hBpos : 0 ≤ B) :
    lam*deriv (cgf (empiricalNormOnProduct Z) (Measure.pi μ)) lam-
        cgf (empiricalNormOnProduct Z) (Measure.pi μ) lam ≤
      3*lam^2*(D^2+∫ ω, empiricalQuadraticOnProduct Z ω ∂Measure.pi μ) := by
  let W := empiricalNormOnProduct Z
  let V := empiricalQuadraticOnProduct Z
  let M := mgf W (Measure.pi μ) lam
  let E := functionalEntropy (Measure.pi μ) (fun ω ↦ Real.exp (lam*W ω))
  let Q := ∫ ω, Real.exp (lam*W ω)*V ω ∂Measure.pi μ
  let v := ∫ ω, V ω ∂Measure.pi μ
  let G := cgf V (Measure.pi μ) (2*lam^2)
  have hw := empirical_norm_product_aestronglyMeasurable μ Z hZ
  have hwb := empirical_norm_product_bounded μ Z B hB
  have hv := empirical_quadratic_product_aestronglyMeasurable μ Z hZ
  have hvb := empirical_quadratic_product_bounded μ Z B hB
  have hs := scalar_mul_ae_bounded hw hwb lam
  have hf := bounded_exp_positive hs.1 hs.2
  have hM : 0 < M := hf.integral_pos
  have hQ := bounded_mul_integrable hf.measurable hv
    (hf.bounds.mono fun _ hx ↦ abs_le_of_bounds hx.1 hx.2) hvb
  have hvnonneg : 0 ≤ v := integral_nonneg (fun ω ↦ empirical_quadratic_nonneg _)
  have he := empirical_norm_entropy μ Z B D hZ hB hMean hWeak lam hlam
  have hadd := integral_add hQ (hf.integrable.mul_const (D^2))
  have heq : (∫ ω, Real.exp (lam*W ω)*(V ω+D^2) ∂Measure.pi μ) = Q+D^2*M := by
    simp_rw [mul_add]
    rw [hadd,integral_mul_const]
    change Q+M*D^2=Q+D^2*M
    ring
  change E ≤ lam^2*(∫ ω, Real.exp (lam*W ω)*(V ω+D^2) ∂Measure.pi μ) at he
  rw [heq] at he
  have ht := scalar_mul_ae_bounded hv hvb (2*lam^2)
  have hvv := bounded_variational hf ht.1 ht.2
  have htest : (∫ ω, Real.exp (lam*W ω)*((2*lam^2)*V ω) ∂Measure.pi μ) = 2*lam^2*Q := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω ↦ by dsimp only; ring
  change (∫ ω, Real.exp (lam*W ω)*((2*lam^2)*V ω) ∂Measure.pi μ) ≤ E+M*G at hvv
  rw [htest] at hvv
  have habs : E ≤ M*(G+2*lam^2*D^2) := by nlinarith [he,hvv]
  have hprod : 0 ≤ lam*B := mul_nonneg hlam hBpos
  have hsq : lam^2*B^2 ≤ 1/4 := by nlinarith [sq_nonneg (lam*B-1/2)]
  have hden : 0 < 1-(B^2/2)*(2*lam^2) := by nlinarith
  have hg := empirical_quadratic_cgf_bound n μ Z B (2*lam^2) hZ hB
    (by positivity) hden
  have hratio : (2*lam^2*v)/(1-(B^2/2)*(2*lam^2)) ≤ 3*lam^2*v := by
    apply (div_le_iff₀ hden).mpr
    have hd : 2/3 ≤ 1-(B^2/2)*(2*lam^2) := by nlinarith
    have hp := mul_le_mul_of_nonneg_left hd (show 0 ≤ 3*lam^2*v by positivity)
    nlinarith
  have hg' : G ≤ 3*lam^2*v := hg.trans hratio
  have hfinal : E ≤ M*(3*lam^2*(D^2+v)) := habs.trans
    (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg lam,sq_nonneg D]) hM.le)
  have hid := bounded_entropy_cgf_identity hw hwb lam
  change E = M*(lam*deriv (cgf W (Measure.pi μ)) lam-cgf W (Measure.pi μ) lam) at hid
  rw [hid] at hfinal
  exact (mul_le_mul_iff_right₀ hM).mp (by simpa only [mul_comm] using hfinal)

/-- Integrate the actual sub-Gaussian differential inequality at its derivative at zero. -/
lemma quadratic_cgf_calculus (L : ℝ → ℝ) (v theta : ℝ)
    (hL : Differentiable ℝ L) (h0 : L 0=0) (htheta : 0 ≤ theta)
    (hineq : ∀ t, 0 < t → t ≤ theta → t*deriv L t-L t ≤ v*t^2) :
    L theta-theta*deriv L 0 ≤ v*theta^2 := by
  let G := fun t ↦ L t-v*t^2
  have hd : ∀ t, HasDerivAt G (deriv L t-2*v*t) t := by
    intro t
    convert (hL t).hasDerivAt.sub (((hasDerivAt_id t).pow 2).const_mul v) using 1
    · funext x
      dsimp only [G,Pi.sub_apply,Pi.pow_apply,id_eq]
    · dsimp only [id_eq]
      ring
  have hh : ∀ t, 0 < t → t ≤ theta → t*deriv G t-G t ≤ 0*t^2*deriv G t := by
    intro t ht hth
    rw [(hd t).deriv]
    dsimp only [G]
    have hi := hineq t ht hth
    nlinarith
  have hg := self_bounding_cgf_calculus G 0 theta
    (fun t ↦ (hd t).differentiableAt) (by simp [G,h0]) htheta (by norm_num) hh
  rw [(hd 0).deriv] at hg
  dsimp only [G] at hg
  simp only [mul_zero,sub_zero,zero_mul,div_one] at hg
  linarith

/-- Actual centered norm CGF, with all entropy and MGF bounds derived above. -/
theorem empirical_norm_centered_cgf_bound
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → H) (B D : ℝ)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B)
    (hMean : ∀ i, ∫ x, Z i x ∂μ i = 0)
    (hWeak : ∀ u : H, ‖u‖ ≤ 1 → (∑ i, ∫ x, (inner ℝ u (Z i x))^2 ∂μ i) ≤ D^2)
    (lam : ℝ) (hlam : 0 ≤ lam) (hBlam : lam*B ≤ 1/2) (hBpos : 0 ≤ B) :
    cgf (empiricalNormOnProduct Z) (Measure.pi μ) lam-
      lam*(∫ ω, empiricalNormOnProduct Z ω ∂Measure.pi μ) ≤
      3*lam^2*(D^2+∫ ω, empiricalQuadraticOnProduct Z ω ∂Measure.pi μ) := by
  have hw := empirical_norm_product_aestronglyMeasurable μ Z hZ
  have hwb := empirical_norm_product_bounded μ Z B hB
  have hh := quadratic_cgf_calculus (cgf (empiricalNormOnProduct Z) (Measure.pi μ))
    (3*(D^2+∫ ω, empiricalQuadraticOnProduct Z ω ∂Measure.pi μ)) lam
    (fun t ↦ (bounded_hasDerivAt_cgf hw hwb t).differentiableAt) (by simp) hlam
    (fun t ht htl ↦ by
      have hb : t*B ≤ 1/2 := (mul_le_mul_of_nonneg_right htl hBpos).trans hBlam
      have hi := empirical_norm_cgf_differential μ Z B D hZ hB hMean hWeak t ht.le hb hBpos
      convert hi using 1
      ring)
  rw [bounded_cgf_deriv_zero hw hwb] at hh
  convert hh using 1
  ring

#print axioms DGRHS.Concentration.empirical_norm_entropy
#print axioms DGRHS.Concentration.empirical_norm_cgf_differential
#print axioms DGRHS.Concentration.quadratic_cgf_calculus
#print axioms DGRHS.Concentration.empirical_norm_centered_cgf_bound
#check @DGRHS.Concentration.empirical_norm_centered_cgf_bound
end DGRHS.Concentration
