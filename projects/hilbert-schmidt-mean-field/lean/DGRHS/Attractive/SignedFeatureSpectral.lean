import DGRHS.Attractive.SignedFeatureChaosLaw
import DGRHS.Gaussian.FeatureQuadraticLaplace
import DGRHS.Kernel.SpectralBounds

/-! Signed Laplace law of the same actual feature field and Gram integral
operator. This is the weak-margin extension of the imported positive-sign
spectral evaluation, retaining exact trace and normalized-mode proofs. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DGRHS.Attractive
open DGRHS.Gaussian
universe u v
variable {X : Type u} {H : Type v} {ι j : Type*}
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]

theorem feature_quadratic_signed_laplace_of_eigenbasis [Countable ι] [Countable j]
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
      indexedGaussianIsometry b f hf (k x)) (β : ℝ) (hmargin : ∀ i, 0 < 1+β*eig i) :
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
  refine ⟨(integral_familyCenteredExp_weak_margin β a haq has (fun i => hmargin i) Y hY hI hm).1.congr heq.symm, ?_⟩
  calc
    _ = ∫ ω, familyCenteredExp β a (fun i => Y i ω) ∂IsonormalProcess.iidStdGaussian :=
      integral_congr_ae heq
    _ = (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * a i)))⁻¹ :=
      (integral_familyCenteredExp_weak_margin β a haq has (fun i => hmargin i) Y hY hI hm).2
    _ = _ := by rw [regularizedDet_feature_nonzero eig β]

/-- The spectrum and trace are constructed from the actual feature Gram
operator. The signed factor margin is derived from that operator norm. -/
theorem exists_feature_signed_quadratic_laplace [Countable j]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace.CountablyGenerated X]
    (b : HilbertBasis j ℝ H) (f : j → ℕ) (hf : Function.Injective f)
    (k : X → H) (hk : StronglyMeasurable k) (hk2 : MemLp k 2 μ)
    (hmean : (∫ x,k x ∂μ)=0)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hg2 : MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian))
    (hW : ∀ᵐ x ∂μ,(fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    ∃ (ι : Type u) (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ)),
      Countable ι ∧
      (∀ i,DGRHS.Kernel.integralOperator (featureKernel k)
        (memLp_featureKernel k hk hk2) (e i)=eig i • e i) ∧
      (∀ i,0≤eig i) ∧ Summable eig ∧ (∑' i,eig i)=∫ x,‖k x‖^2 ∂μ ∧
      ∀ parameter : ℝ,|parameter| *‖DGRHS.Kernel.integralOperator (featureKernel k)
        (memLp_featureKernel k hk hk2)‖<1 →
        Integrable (featureQuadraticCenteredExp (μ := μ) parameter k g) IsonormalProcess.iidStdGaussian ∧
        (∫ ω,featureQuadraticCenteredExp (μ := μ) parameter k g ω ∂IsonormalProcess.iidStdGaussian)=
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => parameter*eig i)))⁻¹ := by
  obtain ⟨ι,eig,e,hi,he,ha,hs,ht,_⟩ := exists_featureKernel_spectral_trace k hk hk2 hmean
  letI : Countable ι := hi
  refine ⟨ι,eig,e,hi,he,ha,hs,ht,fun parameter hmargin => ?_⟩
  have hm : ∀ i,0<1+parameter*eig i := by
    intro i
    have hb := DGRHS.Kernel.integralOperator_eigenvalue_norm_le (featureKernel k)
      (memLp_featureKernel k hk hk2) eig e he i
    have hx : |parameter*eig i|≤|parameter| *‖DGRHS.Kernel.integralOperator (featureKernel k)
        (memLp_featureKernel k hk hk2)‖ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hb) (abs_nonneg _)
    linarith [neg_abs_le (parameter*eig i)]
  exact feature_quadratic_signed_laplace_of_eigenbasis b f hf k hk.measurable hk hk2
    eig e he ha hs ht g hg hg2 hW parameter hm

end DGRHS.Attractive
#check DGRHS.Attractive.feature_quadratic_signed_laplace_of_eigenbasis
#print axioms DGRHS.Attractive.feature_quadratic_signed_laplace_of_eigenbasis
#check DGRHS.Attractive.exists_feature_signed_quadratic_laplace
#print axioms DGRHS.Attractive.exists_feature_signed_quadratic_laplace
