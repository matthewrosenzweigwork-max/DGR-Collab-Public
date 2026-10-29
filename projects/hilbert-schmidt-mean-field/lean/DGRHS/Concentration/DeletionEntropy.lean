import DGRHS.Concentration.FiniteEntropy

noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace DGRHS.Concentration

def entropyPsi (t : ℝ) : ℝ := Real.exp t - t - 1

lemma entropy_comparison_constant {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {c C a : ℝ}
    (hf : PositiveBounded μ f c C) (ha : 0 < a) :
    Integrable (fun x ↦ f x * Real.log (f x / a) - f x + a) μ ∧
    functionalEntropy μ f ≤ ∫ x, f x * Real.log (f x / a) - f x + a ∂μ := by
  let m := ∫ x, f x ∂μ
  have hm : 0 < m := hf.integral_pos
  have heq : (fun x ↦ f x * Real.log (f x / a)) =ᵐ[μ]
      (fun x ↦ f x * Real.log (f x) - f x * Real.log a) := by
    filter_upwards [hf.bounds] with x hx
    rw [Real.log_div (hf.lower_pos.trans_le hx.1).ne' ha.ne']
    ring
  have hc : Integrable (fun x ↦ f x * Real.log a) μ := hf.integrable.mul_const _
  have hq : Integrable (fun x ↦ f x * Real.log (f x / a)) μ :=
    (hf.mul_log_integrable.sub hc).congr heq.symm
  have hsub : Integrable (fun x ↦ f x * Real.log (f x / a) - f x) μ := hq.sub hf.integrable
  have hi : Integrable (fun x ↦ f x * Real.log (f x / a) - f x + a) μ :=
    hsub.add (integrable_const a)
  refine ⟨hi, ?_⟩
  have hR : (∫ x, f x * Real.log (f x / a) - f x + a ∂μ) =
      (∫ x, f x * Real.log (f x) ∂μ) - m * Real.log a - m + a := by
    rw [integral_add hsub (integrable_const a),
      integral_sub hq hf.integrable, integral_congr_ae heq,
      integral_sub hf.mul_log_integrable hc, integral_mul_const]
    simp [m]
  rw [hR]
  have h := Real.log_le_sub_one_of_pos (div_pos ha hm)
  rw [Real.log_div ha.ne' hm.ne'] at h
  have hmul := mul_le_mul_of_nonneg_left h hm.le
  have hcancel : m * (a / m - 1) = a - m := by
    field_simp [hm.ne']
  rw [hcancel] at hmul
  unfold functionalEntropy
  change _ - m * Real.log m ≤ _
  linarith

lemma scalar_mul_ae_bounded {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f μ) (hB : ∀ᵐ x ∂μ, |f x| ≤ B) (lam : ℝ) :
    AEStronglyMeasurable (fun x ↦ lam * f x) μ ∧
      (∀ᵐ x ∂μ, |lam * f x| ≤ |lam| * |B|) := by
  constructor
  · simpa only [Pi.mul_def] using (aestronglyMeasurable_const (b := lam)).mul hf
  · filter_upwards [hB] with x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hx.trans (le_abs_self B)) (abs_nonneg lam)

lemma difference_ae_bounded {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g : Ω → ℝ} {B D : ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hB : ∀ᵐ x ∂μ, |f x| ≤ B) (hD : ∀ᵐ x ∂μ, |g x| ≤ D) :
    AEStronglyMeasurable (fun x ↦ f x - g x) μ ∧
      (∀ᵐ x ∂μ, |f x - g x| ≤ |B| + |D|) := by
  refine ⟨hf.sub hg, ?_⟩
  filter_upwards [hB,hD] with x hx hy
  calc
    |f x - g x| ≤ |f x| + |g x| := by simpa using abs_sub_le (f x) 0 (g x)
    _ ≤ |B| + |D| := add_le_add (hx.trans (le_abs_self _)) (hy.trans (le_abs_self _))

lemma exponential_deletion_identity (lam z a : ℝ) :
    Real.exp (lam*z) * entropyPsi (lam*(a-z)) =
      Real.exp (lam*z) * Real.log (Real.exp (lam*z) / Real.exp (lam*a)) -
        Real.exp (lam*z) + Real.exp (lam*a) := by
  have he : Real.exp (lam*z) * Real.exp (lam*a-lam*z) = Real.exp (lam*a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
  simp only [entropyPsi, mul_sub, mul_one]
  rw [he]
  ring

lemma single_coordinate_entropy_deletion {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {z : Ω → ℝ} {B : ℝ}
    (hz : AEStronglyMeasurable z μ) (hB : ∀ᵐ x ∂μ, |z x| ≤ B)
    (lam a : ℝ) (_hlam : 0 ≤ lam) :
    Integrable (fun x ↦ Real.exp (lam*z x) * entropyPsi (lam*(a-z x))) μ ∧
    functionalEntropy μ (fun x ↦ Real.exp (lam*z x)) ≤
      ∫ x, Real.exp (lam*z x) * entropyPsi (lam*(a-z x)) ∂μ := by
  have hs := scalar_mul_ae_bounded hz hB lam
  have hf := bounded_exp_positive hs.1 hs.2
  have h := entropy_comparison_constant hf (Real.exp_pos (lam*a))
  have heq : (fun x ↦ Real.exp (lam*z x) * entropyPsi (lam*(a-z x))) =ᵐ[μ]
      (fun x ↦ Real.exp (lam*z x) * Real.log (Real.exp (lam*z x) / Real.exp (lam*a)) -
        Real.exp (lam*z x) + Real.exp (lam*a)) :=
    Filter.Eventually.of_forall fun x ↦ exponential_deletion_identity lam (z x) a
  exact ⟨h.1.congr heq.symm, (integral_congr_ae heq).symm ▸ h.2⟩

lemma bounded_deletion_integrand_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {z a : Ω → ℝ} {B D : ℝ}
    (hz : AEStronglyMeasurable z μ) (ha : AEStronglyMeasurable a μ)
    (hB : ∀ᵐ x ∂μ, |z x| ≤ B) (hD : ∀ᵐ x ∂μ, |a x| ≤ D) (lam : ℝ) :
    Integrable (fun x ↦ Real.exp (lam*z x) * entropyPsi (lam*(a x-z x))) μ := by
  have hz' := scalar_mul_ae_bounded hz hB lam
  have ha' := scalar_mul_ae_bounded ha hD lam
  have hf := bounded_exp_positive hz'.1 hz'.2
  have hd := difference_ae_bounded hz ha hB hD
  have hld := scalar_mul_ae_bounded hd.1 hd.2 lam
  have hprod : Integrable (fun x ↦ Real.exp (lam*z x) * (lam*(z x-a x))) μ :=
    bounded_mul_integrable hf.measurable hld.1
      (hf.bounds.mono fun _ hx ↦ abs_le_of_bounds hx.1 hx.2) hld.2
  have hi : Integrable (fun x ↦ Real.exp (lam*z x) * (lam*(z x-a x)) -
      Real.exp (lam*z x) + Real.exp (lam*a x)) μ :=
    (hprod.sub hf.integrable).add (bounded_exp_positive ha'.1 ha'.2).integrable
  apply hi.congr
  exact Filter.Eventually.of_forall fun x ↦ by
    dsimp only
    rw [exponential_deletion_identity,
      Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
    ring

lemma entropyPsi_nonneg (t : ℝ) : 0 ≤ entropyPsi t := by
  have h := Real.add_one_le_exp t
  unfold entropyPsi
  linarith

lemma finite_product_deletion_integrand_integrable {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : (Fin n → Ω) → ℝ) (Z_i : Fin n → (Fin n → Ω) → ℝ) (B : ℝ) (D : Fin n → ℝ)
    (hZ : AEStronglyMeasurable Z (Measure.pi μ))
    (hZi : ∀ i, AEStronglyMeasurable (Z_i i) (Measure.pi μ))
    (hB : ∀ᵐ ω ∂Measure.pi μ, |Z ω| ≤ B)
    (hD : ∀ i, ∀ᵐ ω ∂Measure.pi μ, |Z_i i ω| ≤ D i) (lam : ℝ) :
    Integrable (fun ω ↦ Real.exp (lam*Z ω) *
      (∑ i, entropyPsi (lam*(Z_i i ω-Z ω)))) (Measure.pi μ) := by
  have hs : Integrable (fun ω ↦ ∑ i,
      Real.exp (lam*Z ω) * entropyPsi (lam*(Z_i i ω-Z ω))) (Measure.pi μ) :=
    integrable_finsetSum _ (fun i _ ↦
      bounded_deletion_integrand_integrable hZ (hZi i) hB (hD i) lam)
  apply hs.congr
  exact Filter.Eventually.of_forall fun ω ↦ by
    dsimp only
    rw [Finset.mul_sum]

/-- Coordinate deletion entropy for genuine finite products and invariant deletion functions. -/
theorem finite_product_deletion_entropy {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : (Fin n → Ω) → ℝ) (Z_i : Fin n → (Fin n → Ω) → ℝ) (B : ℝ) (D : Fin n → ℝ)
    (hZ : AEStronglyMeasurable Z (Measure.pi μ))
    (hZi : ∀ i, AEStronglyMeasurable (Z_i i) (Measure.pi μ))
    (hB : ∀ᵐ ω ∂Measure.pi μ, |Z ω| ≤ B)
    (hD : ∀ i, ∀ᵐ ω ∂Measure.pi μ, |Z_i i ω| ≤ D i)
    (hInv : ∀ i ω x, Z_i i (Function.update ω i x) = Z_i i ω)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    functionalEntropy (Measure.pi μ) (fun ω ↦ Real.exp (lam*Z ω)) ≤
      ∫ ω, Real.exp (lam*Z ω) * (∑ i, entropyPsi (lam*(Z_i i ω-Z ω))) ∂Measure.pi μ := by
  let F := fun ω ↦ Real.exp (lam*Z ω)
  let G := fun i ω ↦ F ω * entropyPsi (lam*(Z_i i ω-Z ω))
  have hs := scalar_mul_ae_bounded hZ hB lam
  have hf : PositiveBounded (Measure.pi μ) F (Real.exp (-abs (abs lam * abs B)))
      (Real.exp (abs (abs lam * abs B))) := bounded_exp_positive hs.1 hs.2
  have hG : ∀ i, Integrable (G i) (Measure.pi μ) :=
    fun i ↦ bounded_deletion_integrand_integrable hZ (hZi i) hB (hD i) lam
  have hc : ∀ i, (∫ ω, coordinateEntropy μ F i ω ∂Measure.pi μ) ≤
      ∫ ω, G i ω ∂Measure.pi μ := by
    intro i
    have hpoint : ∀ᵐ ω ∂Measure.pi μ, coordinateEntropy μ F i ω ≤
        ∫ x, G i (Function.update ω i x) ∂μ i := by
      filter_upwards [coordinate_bounded_sections μ hZ hB i] with ω hω
      have h := (single_coordinate_entropy_deletion hω.1 hω.2 lam (Z_i i ω) hlam).2
      have hi : (∫ x, Real.exp (lam*Z (Function.update ω i x)) *
          entropyPsi (lam*(Z_i i ω-Z (Function.update ω i x))) ∂μ i) =
          ∫ x, G i (Function.update ω i x) ∂μ i := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ by dsimp [G,F]; rw [hInv]
      exact hi ▸ h
    have h := integral_mono_ae (coordinate_entropy_integrable μ hf i)
      (coordinate_average_integrable μ (hG i) i) hpoint
    rw [coordinate_integral_identity μ (hG i) i] at h
    exact h
  have ht := finite_product_entropy_tensorization n μ F _ _ hf
  calc
    _ ≤ ∑ i, ∫ ω, G i ω ∂Measure.pi μ := ht.trans (Finset.sum_le_sum fun i _ ↦ hc i)
    _ = ∫ ω, ∑ i, G i ω ∂Measure.pi μ := (integral_finsetSum _ (fun i _ ↦ hG i)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ by dsimp [G,F]; rw [Finset.mul_sum]

lemma finite_product_deletion_entropy_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Fin 0 → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : (Fin 0 → Ω) → ℝ) (Z_i : Fin 0 → (Fin 0 → Ω) → ℝ) (lam : ℝ) :
    functionalEntropy (Measure.pi μ) (fun ω ↦ Real.exp (lam*Z ω)) = 0 ∧
      (∫ ω, Real.exp (lam*Z ω) *
        (∑ i, entropyPsi (lam*(Z_i i ω-Z ω))) ∂Measure.pi μ) = 0 := by
  refine ⟨finite_product_entropy_zero μ (fun ω ↦ Real.exp (lam*Z ω)), ?_⟩
  simp

lemma finite_product_exponential_entropy_const {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (z lam : ℝ) :
    functionalEntropy (Measure.pi μ) (fun _ ↦ Real.exp (lam*z)) = 0 :=
  functionalEntropy_const (Measure.pi μ) (Real.exp (lam*z))

lemma finite_product_deletion_entropy_parameter_zero {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : (Fin n → Ω) → ℝ) (Z_i : Fin n → (Fin n → Ω) → ℝ) :
    functionalEntropy (Measure.pi μ) (fun ω ↦ Real.exp (0*Z ω)) = 0 ∧
      (∫ ω, Real.exp (0*Z ω) *
        (∑ i, entropyPsi (0*(Z_i i ω-Z ω))) ∂Measure.pi μ) = 0 := by
  simp [entropyPsi, functionalEntropy]

#print axioms DGRHS.Concentration.finite_product_deletion_entropy_parameter_zero
#print axioms DGRHS.Concentration.finite_product_deletion_integrand_integrable
#print axioms DGRHS.Concentration.finite_product_deletion_entropy_zero
#print axioms DGRHS.Concentration.finite_product_exponential_entropy_const
#print axioms DGRHS.Concentration.entropy_comparison_constant
#print axioms DGRHS.Concentration.single_coordinate_entropy_deletion
#print axioms DGRHS.Concentration.finite_product_deletion_entropy
#print axioms DGRHS.Concentration.entropyPsi_nonneg
#print axioms DGRHS.Concentration.bounded_deletion_integrand_integrable
#check @DGRHS.Concentration.entropy_comparison_constant
#check @DGRHS.Concentration.single_coordinate_entropy_deletion
#check @DGRHS.Concentration.finite_product_deletion_integrand_integrable
#check @DGRHS.Concentration.finite_product_deletion_entropy
end DGRHS.Concentration
