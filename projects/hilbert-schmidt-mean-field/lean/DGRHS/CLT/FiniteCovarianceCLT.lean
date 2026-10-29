/- UNCHECKED outside the frozen coordinator proof. A finite tuple of arbitrary
mean-zero L2 functions converges to its actual readouts from the SAME constructed
isonormal process. No orthogonality, independent target-coordinate law, favorable
covariance matrix or desired limit theorem is assumed. -/
import DGRHS.CLT.FiniteEigenFeatures
import DGRHS.Gaussian.IndexedGaussianLaw
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.CLT
variable {S E j : Type*} [MeasurableSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype j]
  {μ : Measure S} [IsProbabilityMeasure μ]

lemma coeFn_finiteLpCombination (c : j → ℝ) (e : j → Lp ℝ 2 μ) :
    (⇑(∑ i, c i • e i) : S → ℝ) =ᵐ[μ] fun x => ∑ i, c i * e i x := by
  classical
  have hsum : ∀ s : Finset j,
      (⇑(∑ i ∈ s, c i • e i) : S → ℝ) =ᵐ[μ]
        fun x => ∑ i ∈ s, c i * e i x := by
    intro s
    induction s using Finset.induction with
    | empty =>
        simp only [Finset.sum_empty]
        filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with x hx
        exact hx
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (c i • e i) (∑ k ∈ s, c k • e k),
        Lp.coeFn_smul (c i) (e i), ih] with x ha hs ht
      rw [ha, Pi.add_apply, hs, Pi.smul_apply, ht]
      simp only [Finset.sum_insert hi, smul_eq_mul]
  simpa using hsum Finset.univ

lemma variance_centeredLp (v : Lp ℝ 2 μ) (hv : (∫ x, v x ∂μ) = 0) :
    variance v μ = ‖v‖^2 := by
  rw [variance_eq_sub (Lp.memLp v), hv]
  have hi : (∫ x, (v x)^2 ∂μ) = inner ℝ v v := by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply', conj_trivial, ← pow_two]
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero,
    real_inner_self_eq_norm_sq, Pi.pow_apply] using hi

/-- Finite Lp linearity identifies the projected observable without choosing
pointwise representatives compatible everywhere. -/
lemma inner_finiteEigenFeature_ae (b : HilbertBasis j ℝ E)
    (e : j → Lp ℝ 2 μ) (t : E) :
    (fun x => inner ℝ (finiteEigenFeature b e x) t) =ᵐ[μ]
      (∑ i, inner ℝ (b i) t • e i : Lp ℝ 2 μ) := by
  have he : (fun x => inner ℝ (finiteEigenFeature b e x) t) =
      fun x => ∑ i, inner ℝ (b i) t * e i x := by
    funext x
    simp [finiteEigenFeature, sum_inner, real_inner_smul_left, mul_comm]
  rw [he]
  exact (coeFn_finiteLpCombination _ e).symm

/-- The finite target is constructed from the same actual indexed process on
the background L2 space, including its zero spectral modes. -/
theorem iid_finite_Lp_tuple_clt {ι : Type*} [Countable ι]
    (b : HilbertBasis j ℝ E) (e : j → Lp ℝ 2 μ)
    (he : ∀ i, (∫ x, e i x ∂μ) = 0)
    (h : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (f : ι → ℕ) (hf : Function.Injective f) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → S) => (Real.sqrt n)⁻¹ •
        ∑ i ∈ Finset.range n, finiteEigenFeature b e (ω i)) atTop
      (finiteEigenFeature b (fun i => DGRHS.Gaussian.indexedGaussianIsometry h f hf (e i)))
      (fun _ => Measure.infinitePi (fun _ : ℕ => μ)) IsonormalProcess.iidStdGaussian := by
  classical
  let P := Measure.infinitePi (fun _ : ℕ => μ)
  let X := fun n (ω : ℕ → S) => finiteEigenFeature b e (ω n)
  let W := DGRHS.Gaussian.indexedGaussianIsometry h f hf
  let Y := finiteEigenFeature b (fun i => W (e i))
  have hX : MemLp (X 0) 2 P := (memLp_finiteEigenFeature b e).comp_measurePreserving
    (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) 0)
  have hm : (∫ ω, X 0 ω ∂P) = 0 := by
    rw [(iid_feature_identDistrib μ _ (measurable_finiteEigenFeature b e) 0).integral_eq]
    exact integral_finiteEigenFeature b e he
  have hi : iIndepFun X P := iIndepFun_infinitePi
    (X := fun _ : ℕ => finiteEigenFeature b e)
    (fun _ => measurable_finiteEigenFeature b e)
  have hd : ∀ n, IdentDistrib (X n) (X 0) P P := fun n =>
    (iid_feature_identDistrib μ _ (measurable_finiteEigenFeature b e) n).trans
      (iid_feature_identDistrib μ _ (measurable_finiteEigenFeature b e) 0).symm
  apply finite_dimensional_centered_clt X Y hX hm hi hd
    (measurable_finiteEigenFeature b (fun i => W (e i))).aemeasurable
  intro t
  let v : Lp ℝ 2 μ := ∑ i, inner ℝ (b i) t • e i
  have hv : (∫ x, v x ∂μ) = 0 := by
    rw [integral_congr_ae (coeFn_finiteLpCombination _ e), integral_finsetSum]
    · simp only [integral_const_mul, he, mul_zero, Finset.sum_const_zero]
    · intro i _
      exact ((Lp.memLp (e i)).integrable (by norm_num)).const_mul _
  have hproj : Measurable (fun z : E => inner ℝ z t) :=
    (continuous_id.inner continuous_const).measurable
  have hvar : variance (fun ω => inner ℝ (X 0 ω) t) P = ‖v‖^2 := by
    rw [(measurePreserving_eval_infinitePi (fun _ : ℕ => μ) 0).variance_fun_comp
      (f := fun x => inner ℝ (finiteEigenFeature b e x) t)
        (hproj.comp (measurable_finiteEigenFeature b e)).aemeasurable]
    rw [variance_congr (inner_finiteEigenFeature_ae b e t)]
    exact variance_centeredLp v hv
  have hY : (fun ω => inner ℝ (Y ω) t) =ᵐ[IsonormalProcess.iidStdGaussian] W v := by
    have hw : W v = ∑ i, inner ℝ (b i) t • W (e i) := by
      simp only [v, map_sum, map_smul]
    rw [hw]
    exact inner_finiteEigenFeature_ae b (fun i => W (e i)) t
  rw [hvar]
  refine ⟨(hproj.comp (measurable_finiteEigenFeature b (fun i => W (e i)))).aemeasurable, ?_⟩
  rw [Measure.map_congr hY]
  exact DGRHS.Gaussian.map_indexedGaussianIsometry_eq_gaussianReal h f hf v

end DGRHS.CLT
#print axioms DGRHS.CLT.coeFn_finiteLpCombination
#print axioms DGRHS.CLT.variance_centeredLp
#print axioms DGRHS.CLT.inner_finiteEigenFeature_ae
#print axioms DGRHS.CLT.iid_finite_Lp_tuple_clt
#check DGRHS.CLT.iid_finite_Lp_tuple_clt
