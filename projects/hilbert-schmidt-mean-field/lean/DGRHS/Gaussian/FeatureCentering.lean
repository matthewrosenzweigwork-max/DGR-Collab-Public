import DGRHS.Gaussian.FeatureProductL2

/-!
Feature-variable centering passes from the honest finite readouts through
product L2 convergence. The estimate uses the probability-space L2 to L1 bound,
Fubini, and norm-integral inequality. It does not infer stochastic Fubini from
an L2 isometry alone.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators InnerProductSpace

namespace DGRHS.Gaussian

noncomputable section

 theorem integral_norm_Lp_two_le_norm {A : Type*} [MeasurableSpace A]
    {ρ : Measure A} [IsProbabilityMeasure ρ] (F : Lp ℝ 2 ρ) :
    (∫ a, ‖F a‖ ∂ρ) ≤ ‖F‖ := by
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable F),
    ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable F)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top F)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))

 theorem ae_feature_mean_zero_of_L2_limit {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] {μ : Measure X} {P : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (F : ℕ → X × Ω → ℝ) (S : ℕ → Lp ℝ 2 (μ.prod P))
    (Z : Lp ℝ 2 (μ.prod P)) (g : X × Ω → ℝ)
    (hS : ∀ n, (S n : X × Ω → ℝ) =ᵐ[μ.prod P] F n)
    (hg : g =ᵐ[μ.prod P] (Z : X × Ω → ℝ))
    (ht : Tendsto S atTop (𝓝 Z))
    (hc : ∀ n ω, (∫ x, F n (x, ω) ∂μ) = 0) :
    (∀ᵐ ω ∂P, Integrable (fun x => g (x, ω)) μ) ∧
    ∀ᵐ ω ∂P, (∫ x, g (x, ω) ∂μ) = 0 := by
  have hg2 : MemLp g 2 (μ.prod P) := (memLp_congr_ae hg).2 (Lp.memLp Z)
  have hgi : Integrable g (μ.prod P) := hg2.integrable (by norm_num)
  have hmi := hgi.integral_prod_right
  have hb : ∀ n, (∫ ω, ‖∫ x, g (x, ω) ∂μ‖ ∂P) ≤ ‖Z - S n‖ := by
    intro n
    have hFi : Integrable (F n) (μ.prod P) :=
      ((Lp.memLp (S n)).integrable (by norm_num)).congr (hS n)
    have hR : ((Z - S n : Lp ℝ 2 (μ.prod P)) : X × Ω → ℝ) =ᵐ[μ.prod P] (fun p => g p - F n p) :=
      (Lp.coeFn_sub Z (S n)).trans (hg.symm.sub (hS n))
    have hRi : Integrable (fun p => g p - F n p) (μ.prod P) :=
      ((Lp.memLp (Z - S n)).integrable (by norm_num)).congr hR
    calc
      _ ≤ ∫ ω, ∫ x, ‖g (x, ω) - F n (x, ω)‖ ∂μ ∂P := by
        apply integral_mono_ae hmi.norm hRi.integral_norm_prod_right
        filter_upwards [hgi.prod_left_ae, hFi.prod_left_ae] with ω hgω hFω
        calc
          _ = ‖∫ x, g (x, ω) - F n (x, ω) ∂μ‖ := by
            rw [integral_sub hgω hFω, hc n ω, sub_zero]
          _ ≤ _ := norm_integral_le_integral_norm _
      _ = ∫ p, ‖g p - F n p‖ ∂μ.prod P := (integral_prod_symm _ hRi.norm).symm
      _ = ∫ p, ‖(Z - S n) p‖ ∂μ.prod P := by
        apply integral_congr_ae
        filter_upwards [hR] with p hp
        rw [hp]
      _ ≤ ‖Z - S n‖ := integral_norm_Lp_two_le_norm (Z - S n)
  have hlim : Tendsto (fun n => ‖Z - S n‖) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n => Z - S n) atTop (𝓝 (Z - Z)) := tendsto_const_nhds.sub ht
    simpa only [sub_self, norm_zero] using hsub.norm
  have ha : (∫ ω, ‖∫ x, g (x, ω) ∂μ‖ ∂P) = 0 :=
    le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hb))
      (integral_nonneg (fun ω => norm_nonneg _))
  refine ⟨hgi.prod_left_ae, ?_⟩
  have hz := (integral_eq_zero_iff_of_nonneg (fun ω => norm_nonneg _)
    hmi.norm).1 ha
  filter_upwards [hz] with ω hω
  exact norm_eq_zero.mp hω

variable {ι H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H] [MeasurableSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]

 theorem integral_featureCoefficient_eq_zero [CompleteSpace H]
    (b : HilbertBasis ι ℝ H) {k : X → H} (hk : MemLp k 2 μ)
    (hmean : (∫ x, k x ∂μ) = 0) (i : ι) :
    (∫ x, b.repr (k x) i ∂μ) = 0 := by
  simp only [b.repr_apply_apply]
  rw [integral_inner (hk.integrable (by norm_num)) (b i), hmean, inner_zero_right]

 theorem integral_indexedPartialEvaluation_feature_zero [CompleteSpace H]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) {k : X → H} (hk : MemLp k 2 μ)
    (hmean : (∫ x, k x ∂μ) = 0) (s : Finset ι) (ω : ℕ → ℝ) :
    (∫ x, indexedPartialEvaluation b f k s x ω ∂μ) = 0 := by
  classical
  unfold indexedPartialEvaluation
  rw [integral_finsetSum s (fun i _ =>
    ((memLp_featureCoefficient b hk i).integrable (by norm_num)).mul_const
      (IsonormalProcess.coord (f i) ω))]
  simp_rw [integral_mul_const, integral_featureCoefficient_eq_zero b hk hmean, zero_mul]
  simp

 theorem ae_featureGaussian_feature_mean_zero [CompleteSpace H] [Countable ι]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    {k : X → H} (hk : MemLp k 2 μ) (hmean : (∫ x, k x ∂μ) = 0)
    (g : X × (ℕ → ℝ) → ℝ)
    (hg : g =ᵐ[μ.prod IsonormalProcess.iidStdGaussian]
      (∑' i, featureGaussianTerm b f hk i : Lp ℝ 2 (μ.prod IsonormalProcess.iidStdGaussian))) :
    (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, Integrable (fun x => g (x, ω)) μ) ∧
    ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, (∫ x, g (x, ω) ∂μ) = 0 := by
  classical
  obtain ⟨ss, hss⟩ : ∃ ss : ℕ → Finset ι, Tendsto ss atTop atTop :=
    exists_seq_tendsto (atTop : Filter (Finset ι))
  apply ae_feature_mean_zero_of_L2_limit
    (fun n p => indexedPartialEvaluation b f k (ss n) p.1 p.2)
    (fun n => ∑ i ∈ ss n, featureGaussianTerm b f hk i)
    (∑' i, featureGaussianTerm b f hk i) g
    (fun n => coeFn_featureGaussianSum b f hk (ss n)) hg
    ((summable_featureGaussianTerm b f hf hk).hasSum.comp hss)
  intro n ω
  exact integral_indexedPartialEvaluation_feature_zero b f hk hmean (ss n) ω

 /-- Actual jointly measurable Gaussian feature evaluation, centered in the
feature variable when the Hilbert-valued feature has Bochner mean zero. -/
 theorem exists_centered_featureGaussian_representative [CompleteSpace H] [Countable ι]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    {k : X → H} (hk : Measurable k) (hk2 : MemLp k 2 μ)
    (hmean : (∫ x, k x ∂μ) = 0) :
    ∃ g : X × (ℕ → ℝ) → ℝ, StronglyMeasurable g ∧
      MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian) ∧
      (∀ᵐ x ∂μ, (fun ω => g (x, ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
        indexedGaussianIsometry b f hf (k x)) ∧
      (∀ᵐ x ∂μ, IsonormalProcess.iidStdGaussian.map (fun ω => g (x, ω)) =
        gaussianReal 0 (Real.toNNReal (‖k x‖ ^ 2))) ∧
      (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, Integrable (fun x => g (x, ω)) μ) ∧
      ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, (∫ x, g (x, ω) ∂μ) = 0 := by
  classical
  obtain ⟨ss, hss⟩ : ∃ ss : ℕ → Finset ι, Tendsto ss atTop atTop :=
    exists_seq_tendsto (atTop : Filter (Finset ι))
  let Z : Lp ℝ 2 (μ.prod IsonormalProcess.iidStdGaussian) :=
    ∑' i, featureGaussianTerm b f hk2 i
  have ht : Tendsto (fun n => ∑ i ∈ ss n, featureGaussianTerm b f hk2 i) atTop (𝓝 Z) :=
    (summable_featureGaussianTerm b f hf hk2).hasSum.comp hss
  have hp : TendstoInMeasure (μ.prod IsonormalProcess.iidStdGaussian)
      (fun n (p : X × (ℕ → ℝ)) => indexedPartialEvaluation b f k (ss n) p.1 p.2)
      atTop (Z : X × (ℕ → ℝ) → ℝ) := by
    apply (tendstoInMeasure_of_tendsto_Lp ht).congr_left
    intro n
    exact coeFn_featureGaussianSum b f hk2 (ss n)
  obtain ⟨g, hg, hgZ, hW, hG⟩ :=
    exists_featureGaussian_representative_of_product_limit b f hf hk hss Z hp
  have hc := ae_featureGaussian_feature_mean_zero b f hf hk2 hmean g hgZ
  exact ⟨g, hg, (memLp_congr_ae hgZ).2 (Lp.memLp Z), hW, hG, hc.1, hc.2⟩

end
end DGRHS.Gaussian

#print axioms DGRHS.Gaussian.ae_feature_mean_zero_of_L2_limit
#print axioms DGRHS.Gaussian.integral_indexedPartialEvaluation_feature_zero
#print axioms DGRHS.Gaussian.ae_featureGaussian_feature_mean_zero
#check DGRHS.Gaussian.ae_feature_mean_zero_of_L2_limit
#check DGRHS.Gaussian.integral_indexedPartialEvaluation_feature_zero
#check DGRHS.Gaussian.ae_featureGaussian_feature_mean_zero

#print axioms DGRHS.Gaussian.exists_centered_featureGaussian_representative
#check DGRHS.Gaussian.exists_centered_featureGaussian_representative
