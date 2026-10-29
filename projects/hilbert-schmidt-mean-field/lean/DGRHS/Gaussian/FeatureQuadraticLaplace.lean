import DGRHS.Gaussian.FeatureModes
import DGRHS.Gaussian.FeatureGaussianModes
import DGRHS.Gaussian.GenericPositiveLaplace

/- Actual source Step4 quadratic Laplace identity for the SAME jointly measurable
feature field and indexed Gaussian process. Spectral data are constructed from
its actual Gram integral operator; no spectral/Q/independence/limit premise. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace
namespace DGRHS.Gaussian
noncomputable section
universe u v
variable {X : Type u} {H : Type v} {ι j : Type*}
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]

/-- Joint product-L2 gives actual spatial L2 sections almost surely. -/
theorem ae_memLp_feature_section (g : X × (ℕ → ℝ) → ℝ)
    (hg : StronglyMeasurable g) (hg2 : MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian)) :
    ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, MemLp (fun x => g (x, ω)) 2 μ := by
  filter_upwards [hg2.integrable_sq.prod_left_ae] with ω hω
  exact (memLp_two_iff_integrable_sq
    (hg.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable).2 hω

theorem integrable_feature_quadratic (g : X × (ℕ → ℝ) → ℝ)
    (hg2 : MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian)) :
    Integrable (fun ω => ∫ x, g (x, ω) ^ 2 ∂μ) IsonormalProcess.iidStdGaussian :=
  hg2.integrable_sq.integral_prod_right

/-- Exact expectation from the same-process isometry, before any spectral choice. -/
theorem integral_feature_quadratic (b : HilbertBasis j ℝ H) (f : j → ℕ)
    (hf : Function.Injective f) (k : X → H) (g : X × (ℕ → ℝ) → ℝ)
    (hg2 : MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian))
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x, ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    (∫ ω, ∫ x, g (x, ω) ^ 2 ∂μ ∂IsonormalProcess.iidStdGaussian) = ∫ x, ‖k x‖ ^ 2 ∂μ := by
  rw [← integral_prod_symm _ hg2.integrable_sq, integral_prod _ hg2.integrable_sq]
  apply integral_congr_ae
  filter_upwards [hW] with x hx
  calc
    _ = ∫ ω, indexedGaussianIsometry b f hf (k x) ω ^ 2 ∂IsonormalProcess.iidStdGaussian :=
      integral_congr_ae (by
        filter_upwards [hx] with ω hω
        rw [hω])
    _ = ‖k x‖ ^ 2 := by
      simp only [pow_two, indexedGaussianIsometry_cov, real_inner_self_eq_norm_sq]

/-- Spatial Parseval for the honest representative, including unbounded sections. -/
theorem feature_section_parseval (e : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (z : X → ℝ) (hz : MemLp z 2 μ) :
    (∫ x, z x ^ 2 ∂μ) = ∑' i, (∫ x, e i x * z x ∂μ) ^ 2 := by
  have hi (i : ι) : inner ℝ (e i) (hz.toLp z) = ∫ x, e i x * z x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hz.coeFn_toLp] with x hx
    simp [hx, RCLike.inner_apply', mul_comm]
  have hp := e.tsum_inner_mul_inner (hz.toLp z) (hz.toLp z)
  rw [real_inner_self_eq_norm_sq, DGRHS.Kernel.norm_toLp_sq hz] at hp
  rw [← hp]
  apply tsum_congr
  intro i
  have hi' : inner ℝ (hz.toLp z) (e i) = ∫ x, e i x * z x ∂μ := by
    rw [real_inner_comm]
    exact hi i
  simp only [hi i, hi', pow_two]

/-- Zero spectral modes of the actual Gram operator have zero synthesis. -/
theorem featureSynthesis_zero_eigenmode (k : X → H) (hk : StronglyMeasurable k)
    (hk2 : MemLp k 2 μ) (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (he : ∀ i, DGRHS.Kernel.integralOperator (featureKernel k)
      (memLp_featureKernel k hk hk2) (e i) = eig i • e i) (i : ι) (hi : eig i = 0) :
    featureSynthesis k hk2 (e i) = 0 := by
  have hn := norm_featureSynthesis_eigenbasis_sq k hk hk2 eig e he i
  rw [hi] at hn
  exact norm_eq_zero.1 (by nlinarith [norm_nonneg (featureSynthesis k hk2 (e i))])

/-- Actual nonzero synthesis mode is its normalized vector times sqrt(eigenvalue). -/
theorem featureSynthesis_eq_sqrt_smul_normalized (k : X → H) (hk : StronglyMeasurable k)
    (hk2 : MemLp k 2 μ) (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (he : ∀ i, DGRHS.Kernel.integralOperator (featureKernel k)
      (memLp_featureKernel k hk hk2) (e i) = eig i • e i) (i : {i // eig i ≠ 0}) :
    featureSynthesis k hk2 (e i) = Real.sqrt (eig i) • normalizedFeatureMode k hk2 eig e i := by
  have hp : 0 < eig i := lt_of_le_of_ne
    (by rw [← norm_featureSynthesis_eigenbasis_sq k hk hk2 eig e he i]; positivity)
    i.property.symm
  simp [normalizedFeatureMode, smul_smul, ne_of_gt (Real.sqrt_pos.2 hp)]

theorem regularizedDet_feature_nonzero (eig : ι → ℝ) (β : ℝ) :
    DGRHS.Kernel.regularizedDet (fun i => β * eig i) =
      DGRHS.Kernel.regularizedDet (fun i : {i // eig i ≠ 0} => β * eig i) := by
  unfold DGRHS.Kernel.regularizedDet
  symm
  apply tprod_subtype_eq_of_mulSupport_subset
    (f := fun i : ι => (1 + β * eig i) * Real.exp (-(β * eig i)))
    (s := {i | eig i ≠ 0})
  intro i hi hz
  exact hi (by simp [hz])

/-- All modes are identified on one full-measure set because the actual basis is countable. -/
theorem ae_feature_quadratic_eq_modes [Countable ι] [Countable j]
    (b : HilbertBasis j ℝ H) (f : j → ℕ) (hf : Function.Injective f)
    (k : X → H) (hk : Measurable k) (hks : StronglyMeasurable k) (hk2 : MemLp k 2 μ)
    (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (he : ∀ i, DGRHS.Kernel.integralOperator (featureKernel k)
      (memLp_featureKernel k hks hk2) (e i) = eig i • e i)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hg2 : MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian))
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x, ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    (fun ω => ∫ x, g (x, ω) ^ 2 ∂μ) =ᵐ[IsonormalProcess.iidStdGaussian]
      (fun ω => familyQuadratic (fun i : {i // eig i ≠ 0} => eig i)
        (fun i => indexedGaussianIsometry b f hf (normalizedFeatureMode k hk2 eig e i) ω)) := by
  have hmode : ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, ∀ i,
      (∫ x, e i x * g (x, ω) ∂μ) = indexedGaussianIsometry b f hf (featureSynthesis k hk2 (e i)) ω :=
    ae_all_iff.2 (fun i => (ae_weighted_featureGaussian_mode_of_fibers b f hf hk hk2 g hg hW (e i)).2)
  have hzero (i : ι) (hi : eig i = 0) :
      (indexedGaussianIsometry b f hf (featureSynthesis k hk2 (e i)) : (ℕ → ℝ) → ℝ)
        =ᵐ[IsonormalProcess.iidStdGaussian] (fun _ => 0) := by
    rw [featureSynthesis_zero_eigenmode k hks hk2 eig e he i hi, map_zero]
    exact Lp.coeFn_zero _ _ _
  have hscale (i : {i // eig i ≠ 0}) :
      (indexedGaussianIsometry b f hf (featureSynthesis k hk2 (e i)) : (ℕ → ℝ) → ℝ)
        =ᵐ[IsonormalProcess.iidStdGaussian]
      (fun ω => Real.sqrt (eig i) * indexedGaussianIsometry b f hf
        (normalizedFeatureMode k hk2 eig e i) ω) := by
    rw [featureSynthesis_eq_sqrt_smul_normalized k hks hk2 eig e he i, map_smul]
    exact Lp.coeFn_smul _ _
  have hzall : ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, ∀ i, eig i = 0 →
      indexedGaussianIsometry b f hf (featureSynthesis k hk2 (e i)) ω = 0 := by
    apply ae_all_iff.2
    intro i
    by_cases hi : eig i = 0
    · exact (hzero i hi).mono (fun ω hω _ => hω)
    · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)
  filter_upwards [ae_memLp_feature_section g hg hg2, hmode, hzall,
    ae_all_iff.2 hscale] with ω hω hm hz hc
  rw [feature_section_parseval e _ hω]
  simp_rw [hm]
  have hr : (∑' i : {i // eig i ≠ 0},
      (indexedGaussianIsometry b f hf (featureSynthesis k hk2 (e i)) ω) ^ 2) =
      ∑' i, (indexedGaussianIsometry b f hf (featureSynthesis k hk2 (e i)) ω) ^ 2 := by
    apply tsum_subtype_eq_of_support_subset
      (f := fun i : ι => (indexedGaussianIsometry b f hf (featureSynthesis k hk2 (e i)) ω) ^ 2)
      (s := {i | eig i ≠ 0})
    intro i hi hzi
    exact hi (by
      change (indexedGaussianIsometry b f hf (featureSynthesis k hk2 (e i)) ω) ^ 2 = 0
      rw [hz i hzi]
      simp)
  rw [← hr]
  apply tsum_congr
  intro i
  rw [hc i, mul_pow, Real.sq_sqrt]
  have hn := norm_featureSynthesis_eigenbasis_sq k hks hk2 eig e he i
  rw [← hn]
  positivity

def featureQuadraticCenteredExp (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (ω : ℕ → ℝ) : ℝ :=
  Real.exp (β * ((∫ x, ‖k x‖ ^ 2 ∂μ) - ∫ x, g (x, ω) ^ 2 ∂μ) / 2)

/-- Laplace formula for spectral data of the actual operator and the same field.
Its spectral hypotheses are discharged by the subsequent construction endpoint. -/
theorem feature_quadratic_laplace_of_eigenbasis [Countable ι] [Countable j]
    (b : HilbertBasis j ℝ H) (f : j → ℕ) (hf : Function.Injective f)
    (k : X → H) (hk : Measurable k) (hks : StronglyMeasurable k) (hk2 : MemLp k 2 μ)
    (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (he : ∀ i, DGRHS.Kernel.integralOperator (featureKernel k)
      (memLp_featureKernel k hks hk2) (e i) = eig i • e i)
    (ha : ∀ i, 0 ≤ eig i) (hs : Summable eig)
    (ht : (∑' i, eig i) = ∫ x, ‖k x‖ ^ 2 ∂μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hg2 : MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian))
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x, ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) (β : ℝ) (hβ : 0 ≤ β) :
    Integrable (featureQuadraticCenteredExp (μ := μ) β k g) IsonormalProcess.iidStdGaussian ∧
      (∫ ω, featureQuadraticCenteredExp (μ := μ) β k g ω ∂IsonormalProcess.iidStdGaussian) =
        (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹ := by
  let a : {i // eig i ≠ 0} → ℝ := fun i => eig i
  let Y : {i // eig i ≠ 0} → (ℕ → ℝ) → ℝ := fun i =>
    indexedGaussianIsometry b f hf (normalizedFeatureMode k hk2 eig e i)
  have ho := orthonormal_normalizedFeatureMode k hks hk2 eig e he
  have hI : iIndepFun Y IsonormalProcess.iidStdGaussian :=
    indexedGaussianIsometry_iIndepFun b f hf _ ho
  have hY : ∀ i, AEMeasurable (Y i) IsonormalProcess.iidStdGaussian :=
    fun i => (Lp.aestronglyMeasurable _).aemeasurable
  have hm : ∀ i, IsonormalProcess.iidStdGaussian.map (Y i) = gaussianReal 0 1 :=
    map_indexedGaussianIsometry_orthonormal b f hf _ ho
  have hat : (∑' i : {i // eig i ≠ 0}, eig i) = ∫ x, ‖k x‖ ^ 2 ∂μ := by
    rw [← ht]
    apply tsum_subtype_eq_of_support_subset (s := {i | eig i ≠ 0})
    intro i hi
    exact hi
  have has : Summable a := hs.subtype _
  have haq : ∀ i, 0 ≤ a i := fun i => ha i
  have heq : featureQuadraticCenteredExp (μ := μ) β k g =ᵐ[IsonormalProcess.iidStdGaussian]
      (fun ω => familyCenteredExp β a (fun i => Y i ω)) := by
    filter_upwards [ae_feature_quadratic_eq_modes b f hf k hk hks hk2 eig e he g hg hg2 hW]
      with ω hω
    simp only [featureQuadraticCenteredExp, familyCenteredExp, a, Y, hat, hω]
  refine ⟨(integrable_familyCenteredExp β hβ a haq has Y hY hI hm).congr heq.symm, ?_⟩
  calc
    _ = ∫ ω, familyCenteredExp β a (fun i => Y i ω) ∂IsonormalProcess.iidStdGaussian :=
      integral_congr_ae heq
    _ = (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * a i)))⁻¹ :=
      integral_familyCenteredExp β hβ a haq has Y hY hI hm
    _ = _ := by rw [regularizedDet_feature_nonzero eig β]

/-- Actual positive feature-kernel factory: eigenvalues, summable trace and the
Laplace identity are obtained from source hypotheses, with the same given field. -/
theorem exists_feature_quadratic_laplace [Countable j]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace.CountablyGenerated X]
    (b : HilbertBasis j ℝ H) (f : j → ℕ) (hf : Function.Injective f)
    (k : X → H) (hk : Measurable k) (hks : StronglyMeasurable k)
    (hk2 : MemLp k 2 μ) (hmean : (∫ x, k x ∂μ) = 0)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hg2 : MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian))
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x, ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    ∃ (ι : Type u) (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ)),
      Countable ι ∧
      (∀ i, DGRHS.Kernel.integralOperator (featureKernel k)
        (memLp_featureKernel k hks hk2) (e i) = eig i • e i) ∧
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧ (∑' i, eig i) = ∫ x, ‖k x‖ ^ 2 ∂μ ∧
      ∀ β : ℝ, 0 ≤ β →
        Integrable (featureQuadraticCenteredExp (μ := μ) β k g) IsonormalProcess.iidStdGaussian ∧
        (∫ ω, featureQuadraticCenteredExp (μ := μ) β k g ω ∂IsonormalProcess.iidStdGaussian) =
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹ := by
  obtain ⟨ι, eig, e, hi, he, ha, hs, ht, _⟩ := exists_featureKernel_spectral_trace k hks hk2 hmean
  letI : Countable ι := hi
  exact ⟨ι, eig, e, hi, he, ha, hs, ht, fun β hβ =>
    feature_quadratic_laplace_of_eigenbasis b f hf k hk hks hk2 eig e he ha hs ht g hg hg2 hW β hβ⟩

end
end DGRHS.Gaussian
#check DGRHS.Gaussian.ae_memLp_feature_section
#print axioms DGRHS.Gaussian.ae_memLp_feature_section
#check DGRHS.Gaussian.feature_section_parseval
#print axioms DGRHS.Gaussian.feature_section_parseval
#check DGRHS.Gaussian.featureSynthesis_zero_eigenmode
#print axioms DGRHS.Gaussian.featureSynthesis_zero_eigenmode
#check DGRHS.Gaussian.featureSynthesis_eq_sqrt_smul_normalized
#print axioms DGRHS.Gaussian.featureSynthesis_eq_sqrt_smul_normalized
#check DGRHS.Gaussian.regularizedDet_feature_nonzero
#print axioms DGRHS.Gaussian.regularizedDet_feature_nonzero
#check DGRHS.Gaussian.ae_feature_quadratic_eq_modes
#print axioms DGRHS.Gaussian.ae_feature_quadratic_eq_modes
#check DGRHS.Gaussian.feature_quadratic_laplace_of_eigenbasis
#print axioms DGRHS.Gaussian.feature_quadratic_laplace_of_eigenbasis
#check DGRHS.Gaussian.exists_feature_quadratic_laplace
#print axioms DGRHS.Gaussian.exists_feature_quadratic_laplace

#check DGRHS.Gaussian.integrable_feature_quadratic
#print axioms DGRHS.Gaussian.integrable_feature_quadratic
#check DGRHS.Gaussian.integral_feature_quadratic
#print axioms DGRHS.Gaussian.integral_feature_quadratic
