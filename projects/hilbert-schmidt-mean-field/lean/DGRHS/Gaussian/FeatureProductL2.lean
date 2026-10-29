import DGRHS.Gaussian.FeatureRepresentative
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
Product-L2 construction from a square-integrable Hilbert-valued feature map.
All terms use the actual iid Gaussian coordinates. No product-limit assumption
is used in the construction. The coordinate coefficients are those of a genuine
Hilbert basis, including finite and empty index sets.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators InnerProductSpace

namespace DGRHS.Gaussian

noncomputable section

variable {ι H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace H] [BorelSpace H] [MeasurableSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]

 /-- The paper's weighted fourth moment implies the required feature L2 bound,
including beta zero. Integrability is stated explicitly to avoid Lean's
 totalized real integral hiding a divergent positive moment. -/
 theorem memLp_feature_of_exponential_fourth_moment {k : X → H}
    (hk : StronglyMeasurable k) {β : ℝ} (hβ : 0 ≤ β)
    (hM : Integrable (fun x => Real.exp (β * ‖k x‖ ^ 2 / 2) *
      (1 + (‖k x‖ ^ 2) ^ 4)) μ) : MemLp k 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm hk.aestronglyMeasurable).2
  have hD : AEStronglyMeasurable (fun x => ‖k x‖ ^ 2) μ :=
    (show Continuous (fun r : ℝ => r ^ 2) from by fun_prop).comp_aestronglyMeasurable
      hk.aestronglyMeasurable.norm
  apply hM.mono hD
  filter_upwards [] with x
  let D : ℝ := ‖k x‖ ^ 2
  have hD0 : 0 ≤ D := sq_nonneg _
  have hpoly : D ≤ 1 + D ^ 4 := by
    nlinarith [sq_nonneg (D ^ 2 - (1 / 2 : ℝ)), sq_nonneg (D - (1 / 2 : ℝ))]
  have hex : 1 ≤ Real.exp (β * D / 2) := Real.one_le_exp (by positivity)
  change ‖D‖ ≤ ‖Real.exp (β * D / 2) * (1 + D ^ 4)‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hD0,
    abs_of_nonneg (by positivity : 0 ≤ Real.exp (β * D / 2) * (1 + D ^ 4))]
  exact hpoly.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hex
      (by positivity : 0 ≤ 1 + D ^ 4))

 theorem memLp_featureCoefficient (b : HilbertBasis ι ℝ H) {k : X → H}
    (hk : MemLp k 2 μ) (i : ι) : MemLp (fun x => b.repr (k x) i) 2 μ := by
  have hm : AEStronglyMeasurable (fun x => b.repr (k x) i) μ := by
    simp only [b.repr_apply_apply]
    exact (continuous_const.inner continuous_id).comp_aestronglyMeasurable hk.aestronglyMeasurable
  apply hk.of_le hm
  exact Eventually.of_forall (fun x => by
    simpa only [b.repr_apply_apply, b.orthonormal.1 i, one_mul] using
      norm_inner_le_norm (𝕜 := ℝ) (b i) (k x))

 theorem memLp_featureGaussianTerm (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    {k : X → H} (hk : MemLp k 2 μ) (i : ι) :
    MemLp (fun p : X × (ℕ → ℝ) => b.repr (k p.1) i * IsonormalProcess.coord (f i) p.2)
      2 (μ.prod IsonormalProcess.iidStdGaussian) := by
  have hc := memLp_featureCoefficient b hk i
  have hz := IsonormalProcess.memLp_coord (f i)
  apply (memLp_two_iff_integrable_sq
    (hc.aestronglyMeasurable.comp_fst.mul hz.aestronglyMeasurable.comp_snd)).2
  simpa only [Pi.mul_apply, mul_pow] using hc.integrable_sq.mul_prod hz.integrable_sq

 def featureGaussianTerm (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    {k : X → H} (hk : MemLp k 2 μ) (i : ι) :
    Lp ℝ 2 (μ.prod IsonormalProcess.iidStdGaussian) :=
  (memLp_featureGaussianTerm b f hk i).toLp
    (fun p => b.repr (k p.1) i * IsonormalProcess.coord (f i) p.2)

 theorem coeFn_featureGaussianTerm (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    {k : X → H} (hk : MemLp k 2 μ) (i : ι) :
    (featureGaussianTerm b f hk i : X × (ℕ → ℝ) → ℝ) =ᵐ[μ.prod IsonormalProcess.iidStdGaussian]
    (fun p => b.repr (k p.1) i * IsonormalProcess.coord (f i) p.2) :=
  (memLp_featureGaussianTerm b f hk i).coeFn_toLp

 theorem featureGaussianTerm_inner (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    {k : X → H} (hk : MemLp k 2 μ) (i j : ι) :
    inner ℝ (featureGaussianTerm b f hk i) (featureGaussianTerm b f hk j) =
      (∫ x, b.repr (k x) j * b.repr (k x) i ∂μ) *
      (∫ ω, IsonormalProcess.coord (f j) ω * IsonormalProcess.coord (f i) ω
        ∂IsonormalProcess.iidStdGaussian) := by
  rw [L2.inner_def]
  calc
    _ = ∫ p : X × (ℕ → ℝ),
        (b.repr (k p.1) j * b.repr (k p.1) i) *
        (IsonormalProcess.coord (f j) p.2 * IsonormalProcess.coord (f i) p.2)
        ∂μ.prod IsonormalProcess.iidStdGaussian := by
      apply integral_congr_ae
      filter_upwards [coeFn_featureGaussianTerm b f hk i,
        coeFn_featureGaussianTerm b f hk j] with p hi hj
      rw [hi, hj]
      change (b.repr (k p.1) j * IsonormalProcess.coord (f j) p.2) *
        (b.repr (k p.1) i * IsonormalProcess.coord (f i) p.2) = _
      ring
    _ = _ := integral_prod_mul (L := ℝ) (μ := μ) (ν := IsonormalProcess.iidStdGaussian)
      (fun x => b.repr (k x) j * b.repr (k x) i)
      (fun ω => IsonormalProcess.coord (f j) ω * IsonormalProcess.coord (f i) ω)

 theorem featureGaussianTerm_norm_sq (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    {k : X → H} (hk : MemLp k 2 μ) (i : ι) :
    ‖featureGaussianTerm b f hk i‖ ^ 2 = ∫ x, (b.repr (k x) i) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, featureGaussianTerm_inner,
    IsonormalProcess.integral_coord_sq, mul_one]
  simp only [pow_two]

 theorem pairwise_inner_featureGaussianTerm (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) {k : X → H} (hk : MemLp k 2 μ) :
    Pairwise (fun i j => inner ℝ (featureGaussianTerm b f hk i)
      (featureGaussianTerm b f hk j) = 0) := by
  intro i j hij
  rw [featureGaussianTerm_inner,
    IsonormalProcess.integral_coord_mul_of_ne (hf.ne hij.symm), mul_zero]

 theorem summable_norm_sq_featureGaussianTerm (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    {k : X → H} (hk : MemLp k 2 μ) :
    Summable (fun i => ‖featureGaussianTerm b f hk i‖ ^ 2) := by
  classical
  apply summable_of_sum_le (fun i => sq_nonneg _) (c := ∫ x, ‖k x‖ ^ 2 ∂μ)
  intro s
  simp_rw [featureGaussianTerm_norm_sq]
  rw [← integral_finsetSum s (fun i _ => (memLp_featureCoefficient b hk i).integrable_sq)]
  apply integral_mono (integrable_finsetSum s
    (fun i _ => (memLp_featureCoefficient b hk i).integrable_sq))
    ((memLp_two_iff_integrable_sq_norm hk.aestronglyMeasurable).1 hk)
  intro x
  simpa only [b.repr_apply_apply, Real.norm_eq_abs, sq_abs] using
    (b.orthonormal.sum_inner_products_le (k x) (s := s))

 /-- Orthogonal vectors with summable norm-squares have a convergent Hilbert sum.
This includes zero vectors and does not normalize by a possibly zero norm. -/
 theorem summable_of_pairwise_inner_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (v : ι → E)
    (hv : Pairwise (fun i j => inner ℝ (v i) (v j) = 0))
    (hn : Summable (fun i => ‖v i‖ ^ 2)) : Summable v := by
  let V : ι → Submodule ℝ E := fun i => Submodule.span ℝ {v i}
  have hV : OrthogonalFamily ℝ (fun i => V i) (fun i => (V i).subtypeₗᵢ) := by
    intro i j hij a c
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp a.property
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp c.property
    change inner ℝ (a : E) (c : E) = 0
    rw [← hr, ← ht, inner_smul_left, inner_smul_right, hv hij]
    simp
  let w : ∀ i, V i := fun i => ⟨v i, Submodule.mem_span_singleton_self (v i)⟩
  have hn' : Summable (fun i => ‖w i‖ ^ 2) := hn
  exact (hV.summable_iff_norm_sq_summable w).2 hn'

 theorem summable_featureGaussianTerm (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) {k : X → H} (hk : MemLp k 2 μ) :
    Summable (featureGaussianTerm b f hk) :=
  summable_of_pairwise_inner_eq_zero _ (pairwise_inner_featureGaussianTerm b f hf hk)
    (summable_norm_sq_featureGaussianTerm b f hk)

 theorem coeFn_featureGaussianSum (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    {k : X → H} (hk : MemLp k 2 μ) (s : Finset ι) :
    (∑ i ∈ s, featureGaussianTerm b f hk i : Lp ℝ 2 (μ.prod IsonormalProcess.iidStdGaussian))
      =ᵐ[μ.prod IsonormalProcess.iidStdGaussian]
      (fun p => indexedPartialEvaluation b f k s p.1 p.2) := by
  classical
  induction s using Finset.induction with
  | empty =>
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2)
      (μ := μ.prod IsonormalProcess.iidStdGaussian)] with p hp
    simp only [Finset.sum_empty] at *
    rw [hp]
    simp [indexedPartialEvaluation]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (featureGaussianTerm b f hk i)
      (∑ j ∈ s, featureGaussianTerm b f hk j), coeFn_featureGaussianTerm b f hk i, ih]
      with p h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
    simp only [indexedPartialEvaluation, Finset.sum_insert hi]

 /-- The required product limit is constructed from MemLp k 2, rather than assumed. -/
 theorem exists_feature_product_L2_limit (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) {k : X → H} (hk : MemLp k 2 μ)
    {ss : ℕ → Finset ι} (hss : Tendsto ss atTop atTop) :
    ∃ Z : Lp ℝ 2 (μ.prod IsonormalProcess.iidStdGaussian),
      TendstoInMeasure (μ.prod IsonormalProcess.iidStdGaussian)
        (fun n (p : X × (ℕ → ℝ)) => indexedPartialEvaluation b f k (ss n) p.1 p.2)
        atTop (Z : X × (ℕ → ℝ) → ℝ) := by
  let Z := ∑' i, featureGaussianTerm b f hk i
  refine ⟨Z, ?_⟩
  have ht : Tendsto (fun n => ∑ i ∈ ss n, featureGaussianTerm b f hk i) atTop (𝓝 Z) :=
    (summable_featureGaussianTerm b f hf hk).hasSum.comp hss
  apply (tendstoInMeasure_of_tendsto_Lp ht).congr_left
  intro n
  exact coeFn_featureGaussianSum b f hk (ss n)

 theorem exists_featureGaussian_representative [Countable ι]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    {k : X → H} (hk : Measurable k) (hk2 : MemLp k 2 μ) :
    ∃ g : X × (ℕ → ℝ) → ℝ, StronglyMeasurable g ∧
      MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian) ∧
      (∀ᵐ x ∂μ, (fun ω => g (x, ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
        indexedGaussianIsometry b f hf (k x)) ∧
      ∀ᵐ x ∂μ, IsonormalProcess.iidStdGaussian.map (fun ω => g (x, ω)) =
        gaussianReal 0 (Real.toNNReal (‖k x‖ ^ 2)) := by
  obtain ⟨ss, hss⟩ : ∃ ss : ℕ → Finset ι, Tendsto ss atTop atTop :=
    exists_seq_tendsto (atTop : Filter (Finset ι))
  obtain ⟨Z, hZ⟩ := exists_feature_product_L2_limit b f hf hk2 hss
  obtain ⟨g, hg, hgZ, hW, hG⟩ := exists_featureGaussian_representative_of_product_limit b f hf hk hss Z hZ
  exact ⟨g, hg, (memLp_congr_ae hgZ).2 (Lp.memLp Z), hW, hG⟩

 /-- The chosen joint fibers inherit the exact isometry second moments. -/
 theorem ae_featureGaussian_covariance (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) (k : X → H) (g : X × (ℕ → ℝ) → ℝ)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x, ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, (∫ ω, g (x, ω) * g (y, ω) ∂IsonormalProcess.iidStdGaussian) =
      inner ℝ (k x) (k y) := by
  filter_upwards [hW] with x hx
  filter_upwards [hW] with y hy
  calc
    _ = ∫ ω, indexedGaussianIsometry b f hf (k x) ω *
        indexedGaussianIsometry b f hf (k y) ω ∂IsonormalProcess.iidStdGaussian := by
      apply integral_congr_ae
      filter_upwards [hx, hy] with ω hxω hyω
      rw [hxω, hyω]
    _ = _ := indexedGaussianIsometry_cov b f hf (k x) (k y)

 theorem ae_featureGaussian_sample_mean_zero [Countable ι]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (k : X → H) (g : X × (ℕ → ℝ) → ℝ)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x, ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    ∀ᵐ x ∂μ, (∫ ω, g (x, ω) ∂IsonormalProcess.iidStdGaussian) = 0 := by
  filter_upwards [hW] with x hx
  rw [integral_congr_ae hx]
  exact integral_indexedGaussianIsometry_eq_zero b f hf (k x)

end
end DGRHS.Gaussian

#print axioms DGRHS.Gaussian.exists_feature_product_L2_limit
#print axioms DGRHS.Gaussian.exists_featureGaussian_representative
#check DGRHS.Gaussian.exists_feature_product_L2_limit
#check DGRHS.Gaussian.exists_featureGaussian_representative

#print axioms DGRHS.Gaussian.memLp_featureCoefficient
#check DGRHS.Gaussian.memLp_featureCoefficient

#print axioms DGRHS.Gaussian.memLp_featureGaussianTerm
#check DGRHS.Gaussian.memLp_featureGaussianTerm

#print axioms DGRHS.Gaussian.featureGaussianTerm_inner
#check DGRHS.Gaussian.featureGaussianTerm_inner

#print axioms DGRHS.Gaussian.featureGaussianTerm_norm_sq
#check DGRHS.Gaussian.featureGaussianTerm_norm_sq

#print axioms DGRHS.Gaussian.pairwise_inner_featureGaussianTerm
#check DGRHS.Gaussian.pairwise_inner_featureGaussianTerm

#print axioms DGRHS.Gaussian.summable_norm_sq_featureGaussianTerm
#check DGRHS.Gaussian.summable_norm_sq_featureGaussianTerm

#print axioms DGRHS.Gaussian.summable_of_pairwise_inner_eq_zero
#check DGRHS.Gaussian.summable_of_pairwise_inner_eq_zero

#print axioms DGRHS.Gaussian.summable_featureGaussianTerm
#check DGRHS.Gaussian.summable_featureGaussianTerm

#print axioms DGRHS.Gaussian.coeFn_featureGaussianSum
#check DGRHS.Gaussian.coeFn_featureGaussianSum

#print axioms DGRHS.Gaussian.ae_featureGaussian_covariance
#check DGRHS.Gaussian.ae_featureGaussian_covariance

#print axioms DGRHS.Gaussian.ae_featureGaussian_sample_mean_zero
#check DGRHS.Gaussian.ae_featureGaussian_sample_mean_zero

#print axioms DGRHS.Gaussian.memLp_feature_of_exponential_fourth_moment
#check DGRHS.Gaussian.memLp_feature_of_exponential_fourth_moment
