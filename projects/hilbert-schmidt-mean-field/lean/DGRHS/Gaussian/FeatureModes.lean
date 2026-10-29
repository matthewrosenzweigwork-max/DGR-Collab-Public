import DGRHS.Gaussian.FeatureSynthesis
import DGRHS.Gaussian.FeatureCentering

/-!
Weighted feature evaluation for the same actual countable Gaussian isometry.
Product L2 convergence passes through a weighted product-L1 estimate. The
Bochner synthesis coefficient identifies every finite weighted readout.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators InnerProductSpace
namespace DGRHS.Gaussian
noncomputable section

/-- Holder controls a weighted product-L2 representative with the exact L2 norms. -/
theorem integral_norm_weighted_product_le {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] {μ : Measure X} {P : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (a : Lp ℝ 2 μ) (R : Lp ℝ 2 (μ.prod P)) :
    (∫ p, ‖a p.1 * R p‖ ∂μ.prod P) ≤ ‖a‖ * ‖R‖ := by
  have ha : MemLp (fun p : X × Ω => a p.1) 2 (μ.prod P) := (Lp.memLp a).comp_fst P
  have hi : Integrable (fun p : X × Ω => a p.1 * R p) (μ.prod P) :=
    ha.integrable_mul (Lp.memLp R)
  have hh : eLpNorm (fun p : X × Ω => a p.1 * R p) 1 (μ.prod P) ≤
      eLpNorm (fun p : X × Ω => a p.1) 2 (μ.prod P) * eLpNorm R 2 (μ.prod P) := by
    have hpoint : (fun p : X × Ω => a p.1 * R p) =
        (fun p : X × Ω => a p.1) • (fun p : X × Ω => R p) := by
      funext p
      rfl
    rw [hpoint]
    exact eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
      ha.aestronglyMeasurable (Lp.aestronglyMeasurable R)

  have he : eLpNorm (fun p : X × Ω => a p.1) 2 (μ.prod P) = eLpNorm a 2 μ :=
    eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable a) (measurePreserving_fst (μ := μ) (ν := P))
  rw [he] at hh
  rw [integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable]
  simpa only [ENNReal.toReal_mul, ← Lp.norm_def] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top a) (Lp.eLpNorm_ne_top R)) hh

theorem integrable_weighted_product {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] {μ : Measure X} {P : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (a : Lp ℝ 2 μ) (g : X × Ω → ℝ) (hg : MemLp g 2 (μ.prod P)) :
    Integrable (fun p : X × Ω => a p.1 * g p) (μ.prod P) :=
  ((Lp.memLp a).comp_fst P).integrable_mul hg


/-- Weighted section integration is continuous along actual product-L2 limits.
The identified finite sections also converge in Gaussian L2; no stochastic
Fubini identity is assumed. -/
theorem ae_weighted_mean_eq_of_L2_limits {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] {μ : Measure X} {P : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (a : Lp ℝ 2 μ) (F : ℕ → X × Ω → ℝ)
    (S : ℕ → Lp ℝ 2 (μ.prod P)) (Z : Lp ℝ 2 (μ.prod P))
    (g : X × Ω → ℝ) (G : ℕ → Lp ℝ 2 P) (W : Lp ℝ 2 P)
    (hS : ∀ n, (S n : X × Ω → ℝ) =ᵐ[μ.prod P] F n)
    (hg : g =ᵐ[μ.prod P] (Z : X × Ω → ℝ))
    (ht : Tendsto S atTop (𝓝 Z))
    (hG : ∀ n, (fun ω => ∫ x, a x * F n (x, ω) ∂μ) =ᵐ[P] (G n : Ω → ℝ))
    (htG : Tendsto G atTop (𝓝 W)) :
    (∀ᵐ ω ∂P, Integrable (fun x => a x * g (x, ω)) μ) ∧
      (fun ω => ∫ x, a x * g (x, ω) ∂μ) =ᵐ[P] (W : Ω → ℝ) := by
  have hg2 : MemLp g 2 (μ.prod P) := (memLp_congr_ae hg).2 (Lp.memLp Z)
  have hgi := integrable_weighted_product a g hg2
  have hM := hgi.integral_prod_right
  have hW : Integrable (W : Ω → ℝ) P := (Lp.memLp W).integrable (by norm_num)
  have hFi (n : ℕ) : Integrable (fun p : X × Ω => a p.1 * F n p) (μ.prod P) :=
    integrable_weighted_product a (F n) ((memLp_congr_ae (hS n)).1 (Lp.memLp (S n)))
  have hB (n : ℕ) : (∫ ω, ‖(∫ x, a x * g (x, ω) ∂μ) -
      (∫ x, a x * F n (x, ω) ∂μ)‖ ∂P) ≤ ‖a‖ * ‖Z - S n‖ := by
    have hR : ((Z - S n : Lp ℝ 2 (μ.prod P)) : X × Ω → ℝ)
        =ᵐ[μ.prod P] (fun p => g p - F n p) :=
      (Lp.coeFn_sub Z (S n)).trans (hg.symm.sub (hS n))
    have hRi := integrable_weighted_product a (fun p => g p - F n p)
      ((memLp_congr_ae hR).1 (Lp.memLp (Z - S n)))
    calc
      _ ≤ ∫ ω, ∫ x, ‖a x * (g (x, ω) - F n (x, ω))‖ ∂μ ∂P := by
        apply integral_mono_ae (hM.sub (hFi n).integral_prod_right).norm
          hRi.integral_norm_prod_right
        filter_upwards [hgi.prod_left_ae, (hFi n).prod_left_ae] with ω hgω hFω
        calc
          _ = ‖∫ x, a x * (g (x, ω) - F n (x, ω)) ∂μ‖ := by
            change ‖(∫ x, a x * g (x, ω) ∂μ) - (∫ x, a x * F n (x, ω) ∂μ)‖ = _
            simp_rw [mul_sub]
            rw [integral_sub hgω hFω]
          _ ≤ _ := norm_integral_le_integral_norm _
      _ = ∫ p, ‖a p.1 * (g p - F n p)‖ ∂μ.prod P := (integral_prod_symm _ hRi.norm).symm
      _ = ∫ p, ‖a p.1 * (Z - S n) p‖ ∂μ.prod P := by
        apply integral_congr_ae
        filter_upwards [hR] with p hp
        rw [hp]
      _ ≤ ‖a‖ * ‖Z - S n‖ := integral_norm_weighted_product_le a (Z - S n)
  have hC (n : ℕ) : (∫ ω, ‖(∫ x, a x * F n (x, ω) ∂μ) - W ω‖ ∂P) ≤ ‖G n - W‖ := by
    have hD : ((G n - W : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
        (fun ω => (∫ x, a x * F n (x, ω) ∂μ) - W ω) :=
      (Lp.coeFn_sub (G n) W).trans ((hG n).symm.sub (Filter.EventuallyEq.rfl))
    calc
      _ = ∫ ω, ‖(G n - W) ω‖ ∂P := by
        apply integral_congr_ae
        filter_upwards [hD] with ω hω
        rw [hω]
      _ ≤ ‖G n - W‖ := integral_norm_Lp_two_le_norm (G n - W)
  have hbound (n : ℕ) : (∫ ω, ‖(∫ x, a x * g (x, ω) ∂μ) - W ω‖ ∂P) ≤
      ‖a‖ * ‖Z - S n‖ + ‖G n - W‖ := by
    calc
      _ ≤ ∫ ω, ‖(∫ x, a x * g (x, ω) ∂μ) - (∫ x, a x * F n (x, ω) ∂μ)‖ +
          ‖(∫ x, a x * F n (x, ω) ∂μ) - W ω‖ ∂P := by
        apply integral_mono (hM.sub hW).norm
          ((hM.sub (hFi n).integral_prod_right).norm.add
            (((hFi n).integral_prod_right).sub hW).norm)
        intro ω
        simp only [Pi.sub_apply]
        calc
          _ = ‖((∫ x, a x * g (x, ω) ∂μ) - (∫ x, a x * F n (x, ω) ∂μ)) +
              ((∫ x, a x * F n (x, ω) ∂μ) - W ω)‖ := by congr 1; ring
          _ ≤ _ := norm_add_le _ _
      _ = (∫ ω, ‖(∫ x, a x * g (x, ω) ∂μ) - (∫ x, a x * F n (x, ω) ∂μ)‖ ∂P) +
          (∫ ω, ‖(∫ x, a x * F n (x, ω) ∂μ) - W ω‖ ∂P) :=
        integral_add (hM.sub (hFi n).integral_prod_right).norm
          (((hFi n).integral_prod_right).sub hW).norm
      _ ≤ _ := add_le_add (hB n) (hC n)
  have hsub : Tendsto (fun n => ‖Z - S n‖) atTop (𝓝 0) := by
    have h : Tendsto (fun n => Z - S n) atTop (𝓝 (Z - Z)) := tendsto_const_nhds.sub ht
    simpa only [sub_self, norm_zero] using h.norm
  have hsubG : Tendsto (fun n => ‖G n - W‖) atTop (𝓝 0) := by
    have h : Tendsto (fun n => G n - W) atTop (𝓝 (W - W)) := htG.sub tendsto_const_nhds
    simpa only [sub_self, norm_zero] using h.norm
  have hlim : Tendsto (fun n => ‖a‖ * ‖Z - S n‖ + ‖G n - W‖) atTop (𝓝 0) := by
    simpa using (hsub.const_mul ‖a‖).add hsubG
  have hzero : (∫ ω, ‖(∫ x, a x * g (x, ω) ∂μ) - W ω‖ ∂P) = 0 :=
    le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Filter.Eventually.of_forall hbound)) (integral_nonneg (fun _ => norm_nonneg _))
  refine ⟨hgi.prod_left_ae, ?_⟩
  have hz := (integral_eq_zero_iff_of_nonneg (fun _ => norm_nonneg _) (hM.sub hW).norm).1 hzero
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp (norm_eq_zero.mp hω)

variable {ι H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [MeasurableSpace X]
  {μ : Measure X} [IsProbabilityMeasure μ]

theorem integral_weighted_featureCoefficient (b : HilbertBasis ι ℝ H)
    {k : X → H} (hk2 : MemLp k 2 μ) (a : Lp ℝ 2 μ) (i : ι) :
    (∫ x, a x * b.repr (k x) i ∂μ) = b.repr (featureSynthesis k hk2 a) i := by
  simp only [b.repr_apply_apply]
  rw [featureSynthesis_eq_integral, ← integral_inner
    (integrable_featureSynthesis_integrand k hk2 a) (b i)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [inner_smul_right]

theorem integral_weighted_indexedPartialEvaluation (b : HilbertBasis ι ℝ H)
    (f : ι → ℕ) {k : X → H} (hk2 : MemLp k 2 μ) (a : Lp ℝ 2 μ)
    (s : Finset ι) (ω : ℕ → ℝ) :
    (∫ x, a x * indexedPartialEvaluation b f k s x ω ∂μ) =
      indexedPartialEvaluation b f (fun _ : Unit => featureSynthesis k hk2 a) s () ω := by
  classical
  unfold indexedPartialEvaluation
  simp_rw [Finset.mul_sum, ← mul_assoc]
  have hi (i : ι) : Integrable (fun x => a x * b.repr (k x) i *
      IsonormalProcess.coord (f i) ω) μ := by
    simpa only [Pi.mul_apply] using
      ((Lp.memLp a).integrable_mul (memLp_featureCoefficient b hk2 i)).mul_const
        (IsonormalProcess.coord (f i) ω)
  rw [integral_finsetSum s (fun i _ => hi i)]
  simp_rw [integral_mul_const, integral_weighted_featureCoefficient b hk2 a]


/-- Weighted stochastic mode identity for the actual constructed product-L2
representative, with the same W and actual synthesis A. -/
theorem ae_weighted_featureGaussian_mode [Countable ι]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    {k : X → H} (hk2 : MemLp k 2 μ) (g : X × (ℕ → ℝ) → ℝ)
    (hg : g =ᵐ[μ.prod IsonormalProcess.iidStdGaussian]
      (∑' i, featureGaussianTerm b f hk2 i : Lp ℝ 2 (μ.prod IsonormalProcess.iidStdGaussian)))
    (a : Lp ℝ 2 μ) :
    (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, Integrable (fun x => a x * g (x, ω)) μ) ∧
    (fun ω => ∫ x, a x * g (x, ω) ∂μ) =ᵐ[IsonormalProcess.iidStdGaussian]
      (indexedGaussianIsometry b f hf (featureSynthesis k hk2 a) : (ℕ → ℝ) → ℝ) := by
  classical
  obtain ⟨ss, hss⟩ : ∃ ss : ℕ → Finset ι, Tendsto ss atTop atTop :=
    exists_seq_tendsto (atTop : Filter (Finset ι))
  apply ae_weighted_mean_eq_of_L2_limits a
    (fun n p => indexedPartialEvaluation b f k (ss n) p.1 p.2)
    (fun n => ∑ i ∈ ss n, featureGaussianTerm b f hk2 i)
    (∑' i, featureGaussianTerm b f hk2 i) g
    (fun n => indexedLpPartialSum b f (featureSynthesis k hk2 a) (ss n))
    (indexedGaussianIsometry b f hf (featureSynthesis k hk2 a))
    (fun n => coeFn_featureGaussianSum b f hk2 (ss n)) hg
    ((summable_featureGaussianTerm b f hf hk2).hasSum.comp hss)
  · intro n
    filter_upwards [coeFn_indexedLpPartialSum b f (featureSynthesis k hk2 a) (ss n)] with ω hω
    rw [integral_weighted_indexedPartialEvaluation b f hk2 a]
    exact hω.symm
  · exact tendsto_indexedLpPartialSum b f hf (featureSynthesis k hk2 a) hss

/-- The same given joint field is identified with the actual product series
from its same-process fibers. Joint measurability is essential in this adapter. -/
theorem ae_weighted_featureGaussian_mode_of_fibers [Countable ι]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    {k : X → H} (hk : Measurable k) (hk2 : MemLp k 2 μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x, ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) (a : Lp ℝ 2 μ) :
    (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, Integrable (fun x => a x * g (x, ω)) μ) ∧
    (fun ω => ∫ x, a x * g (x, ω) ∂μ) =ᵐ[IsonormalProcess.iidStdGaussian]
      (indexedGaussianIsometry b f hf (featureSynthesis k hk2 a) : (ℕ → ℝ) → ℝ) := by
  classical
  obtain ⟨ss, hss⟩ : ∃ ss : ℕ → Finset ι, Tendsto ss atTop atTop :=
    exists_seq_tendsto (atTop : Filter (Finset ι))
  let Z : Lp ℝ 2 (μ.prod IsonormalProcess.iidStdGaussian) :=
    ∑' i, featureGaussianTerm b f hk2 i
  have ht : Tendsto (fun n => ∑ i ∈ ss n, featureGaussianTerm b f hk2 i)
      atTop (𝓝 Z) := (summable_featureGaussianTerm b f hf hk2).hasSum.comp hss
  have hp : TendstoInMeasure (μ.prod IsonormalProcess.iidStdGaussian)
      (fun n p => indexedPartialEvaluation b f k (ss n) p.1 p.2) atTop
      (Z : X × (ℕ → ℝ) → ℝ) := by
    apply (tendstoInMeasure_of_tendsto_Lp ht).congr_left
    intro n
    exact coeFn_featureGaussianSum b f hk2 (ss n)
  obtain ⟨g0, hg0, hg0Z, hW0, _⟩ :=
    exists_featureGaussian_representative_of_product_limit b f hf hk hss Z hp
  have hgg0 : g =ᵐ[μ.prod IsonormalProcess.iidStdGaussian] g0 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hg.measurable hg0.measurable)).2
    filter_upwards [hW, hW0] with x hx hx0
    exact hx.trans hx0.symm
  exact ae_weighted_featureGaussian_mode b f hf hk2 g (hgg0.trans hg0Z) a

/-- One actually constructed field supplies all weighted modes; the almost
sure exceptional set may depend on the L2 weight. -/
theorem exists_featureGaussian_weighted_modes [Countable ι]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    {k : X → H} (hk : Measurable k) (hk2 : MemLp k 2 μ) :
    ∃ g : X × (ℕ → ℝ) → ℝ, StronglyMeasurable g ∧
      MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian) ∧
      (∀ᵐ x ∂μ, (fun ω => g (x, ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
        indexedGaussianIsometry b f hf (k x)) ∧
      ∀ a : Lp ℝ 2 μ,
        (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, Integrable (fun x => a x * g (x, ω)) μ) ∧
        (fun ω => ∫ x, a x * g (x, ω) ∂μ) =ᵐ[IsonormalProcess.iidStdGaussian]
          (indexedGaussianIsometry b f hf (featureSynthesis k hk2 a) : (ℕ → ℝ) → ℝ) := by
  obtain ⟨g, hg, hg2, hW, _⟩ := exists_featureGaussian_representative b f hf hk hk2
  exact ⟨g, hg, hg2, hW, fun a => ae_weighted_featureGaussian_mode_of_fibers b f hf hk hk2 g hg hW a⟩

end
end DGRHS.Gaussian

#check DGRHS.Gaussian.integral_norm_weighted_product_le
#print axioms DGRHS.Gaussian.integral_norm_weighted_product_le
#check DGRHS.Gaussian.integrable_weighted_product
#print axioms DGRHS.Gaussian.integrable_weighted_product
#check DGRHS.Gaussian.integral_weighted_featureCoefficient
#print axioms DGRHS.Gaussian.integral_weighted_featureCoefficient
#check DGRHS.Gaussian.integral_weighted_indexedPartialEvaluation
#print axioms DGRHS.Gaussian.integral_weighted_indexedPartialEvaluation

#check DGRHS.Gaussian.ae_weighted_mean_eq_of_L2_limits
#print axioms DGRHS.Gaussian.ae_weighted_mean_eq_of_L2_limits
#check DGRHS.Gaussian.ae_weighted_featureGaussian_mode
#print axioms DGRHS.Gaussian.ae_weighted_featureGaussian_mode

#check DGRHS.Gaussian.ae_weighted_featureGaussian_mode_of_fibers
#print axioms DGRHS.Gaussian.ae_weighted_featureGaussian_mode_of_fibers
#check DGRHS.Gaussian.exists_featureGaussian_weighted_modes
#print axioms DGRHS.Gaussian.exists_featureGaussian_weighted_modes
