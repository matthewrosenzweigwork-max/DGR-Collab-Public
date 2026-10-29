/- Actual normalized Gram eigenmodes and their finite Gaussian independence.
No independence is inferred from marginal Gaussianity alone. -/
import DGRHS.Gaussian.FeatureEigenspaces
import DGRHS.Gaussian.IndexedGaussianTuple
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace BigOperators Classical
namespace DGRHS.Gaussian
variable {H X ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

lemma inner_featureSynthesis_eigenbasis (k : X → H) (hk : StronglyMeasurable k)
    (hk2 : MemLp k 2 μ) (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (he : ∀ i, DGRHS.Kernel.integralOperator (featureKernel k)
      (memLp_featureKernel k hk hk2) (e i) = eig i • e i) (i j : ι) :
    inner ℝ (featureSynthesis k hk2 (e i)) (featureSynthesis k hk2 (e j)) =
      eig i * (if i = j then 1 else 0) := by
  classical
  change inner ℝ (featureSynthesis k hk2 (e i)) ((featureReadout k hk2).adjoint (e j)) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (((featureReadout k hk2).comp (featureSynthesis k hk2)) (e i)) (e j) = _
  rw [← integralOperator_featureKernel_eq k hk hk2, he i, real_inner_smul_left,
    orthonormal_iff_ite.mp e.orthonormal i j]

noncomputable def normalizedFeatureMode (k : X → H) (hk2 : MemLp k 2 μ)
    (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (i : {i // eig i ≠ 0}) : H :=
  (Real.sqrt (eig i))⁻¹ • featureSynthesis k hk2 (e i)

lemma orthonormal_normalizedFeatureMode (k : X → H) (hk : StronglyMeasurable k)
    (hk2 : MemLp k 2 μ) (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (he : ∀ i, DGRHS.Kernel.integralOperator (featureKernel k)
      (memLp_featureKernel k hk hk2) (e i) = eig i • e i) :
    Orthonormal ℝ (normalizedFeatureMode k hk2 eig e) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  dsimp [normalizedFeatureMode]
  rw [real_inner_smul_left, real_inner_smul_right,
    inner_featureSynthesis_eigenbasis k hk hk2 eig e he]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    have hp : 0 < eig i := lt_of_le_of_ne
      (by rw [← norm_featureSynthesis_eigenbasis_sq k hk hk2 eig e he i]; positivity)
      i.property.symm
    have hs : Real.sqrt (eig i) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
    field_simp
    nlinarith [Real.sq_sqrt hp.le]
  · have hv : (i : ι) ≠ (j : ι) := fun h ↦ hij (Subtype.ext h)
    simp only [ite_false, hv, hij, mul_zero]

/-- The finite joint Gaussian law supplies independence of orthogonal modes. -/
theorem indexedGaussianIsometry_iIndepFun_orthonormal {j E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Countable j] {m : ℕ}
    (b : HilbertBasis j ℝ E) (f : j → ℕ) (hf : Function.Injective f)
    (h : Fin m → E) (hh : Orthonormal ℝ h) :
    iIndepFun (fun i ω ↦ indexedGaussianIsometry b f hf (h i) ω)
      IsonormalProcess.iidStdGaussian := by
  apply (indexedGaussianIsometry_hasGaussianLaw_tuple b f hf h).iIndepFun_of_covariance_eq_zero
  intro i j hij
  rw [covariance_eq_sub (Lp.memLp _) (Lp.memLp _)]
  change (∫ ω, indexedGaussianIsometry b f hf (h i) ω *
    indexedGaussianIsometry b f hf (h j) ω ∂IsonormalProcess.iidStdGaussian) -
    (∫ ω, indexedGaussianIsometry b f hf (h i) ω ∂IsonormalProcess.iidStdGaussian) *
    (∫ ω, indexedGaussianIsometry b f hf (h j) ω ∂IsonormalProcess.iidStdGaussian) = 0
  rw [indexedGaussianIsometry_cov, integral_indexedGaussianIsometry_eq_zero,
    integral_indexedGaussianIsometry_eq_zero]
  simp only [orthonormal_iff_ite.mp hh i j, hij, ite_false, zero_mul, sub_zero]

/-- Independence of the whole orthonormal family follows from all finite restrictions. -/
theorem indexedGaussianIsometry_iIndepFun {j E a : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Countable j]
    (b : HilbertBasis j ℝ E) (f : j → ℕ) (hf : Function.Injective f)
    (h : a → E) (hh : Orthonormal ℝ h) :
    iIndepFun (fun i ω ↦ indexedGaussianIsometry b f hf (h i) ω)
      IsonormalProcess.iidStdGaussian := by
  classical
  rw [iIndepFun_iff_finset]
  intro s
  let q : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  have ho : Orthonormal ℝ (fun i : Fin (Fintype.card s) ↦ h (q i)) :=
    hh.comp (fun i ↦ (q i).val) (Subtype.val_injective.comp q.injective)
  have hi := indexedGaussianIsometry_iIndepFun_orthonormal b f hf
    (fun i : Fin (Fintype.card s) ↦ h (q i)) ho
  exact hi.of_precomp q.surjective

lemma map_indexedGaussianIsometry_orthonormal {j E a : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Countable j]
    (b : HilbertBasis j ℝ E) (f : j → ℕ) (hf : Function.Injective f)
    (h : a → E) (hh : Orthonormal ℝ h) (i : a) :
    IsonormalProcess.iidStdGaussian.map (indexedGaussianIsometry b f hf (h i)) =
      gaussianReal 0 1 := by
  rw [map_indexedGaussianIsometry_eq_gaussianReal, hh.1 i]
  norm_num

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.inner_featureSynthesis_eigenbasis
#print axioms DGRHS.Gaussian.orthonormal_normalizedFeatureMode
#print axioms DGRHS.Gaussian.indexedGaussianIsometry_iIndepFun_orthonormal
#check DGRHS.Gaussian.indexedGaussianIsometry_iIndepFun_orthonormal
#print axioms DGRHS.Gaussian.indexedGaussianIsometry_iIndepFun
#print axioms DGRHS.Gaussian.map_indexedGaussianIsometry_orthonormal
#check DGRHS.Gaussian.indexedGaussianIsometry_iIndepFun
