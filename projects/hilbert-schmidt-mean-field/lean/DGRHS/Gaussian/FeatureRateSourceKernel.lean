import DGRHS.Gaussian.FeatureRateFactory
import Mathlib.Probability.Independence.Basic

/-! Transfer from a source kernel equal to the actual feature Gram kernel
only almost everywhere on the product. Distinct coordinates have product law;
no product-a.e. equality is ever restricted to the diagonal. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DGRHS.Gaussian
universe u v
variable {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

lemma measurePreserving_distinct_particle_pair (N : ℕ) (i l : Fin N) (hil : i ≠ l) :
    MeasurePreserving (fun x : Fin N → X => (x i, x l))
      (Measure.pi (fun _ : Fin N => μ)) (μ.prod μ) := by
  have hi := measurePreserving_eval (fun _ : Fin N => μ) i
  have hl := measurePreserving_eval (fun _ : Fin N => μ) l
  have hind : iIndepFun (fun i (x : Fin N → X) => x i)
      (Measure.pi (fun _ : Fin N => μ)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply l), ?_⟩
  simpa only [hi.map_eq, hl.map_eq] using
    (hind.indepFun hil).map_prod_eq_prod_map_map hi.measurable.aemeasurable hl.measurable.aemeasurable

lemma ae_distinct_particle_pairs_congr {h q : X × X → ℝ}
    (heq : h =ᵐ[μ.prod μ] q) (N : ℕ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ), ∀ i l : Fin N, i ≠ l → h (x i,x l) = q (x i,x l) := by
  apply ae_all_iff.2
  intro i
  apply ae_all_iff.2
  intro l
  by_cases hil : i = l
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hil))
  · filter_upwards [(measurePreserving_distinct_particle_pair N i l hil).quasiMeasurePreserving.ae heq] with x hx
    exact fun _ => hx

lemma integralOperator_eq_of_ae_kernel {h q : X × X → ℝ}
    (hh : MemLp h 2 (μ.prod μ)) (hq : MemLp q 2 (μ.prod μ))
    (heq : h =ᵐ[μ.prod μ] q) :
    DGRHS.Kernel.integralOperator h hh = DGRHS.Kernel.integralOperator q hq := by
  unfold DGRHS.Kernel.integralOperator
  rw [hh.toLp_congr hq heq]

def sourceKernelParticleStatistic (h : X × X → ℝ) (N : ℕ) (x : Fin N → X) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ l : Fin N, if i = l then 0 else h (x i,x l)

lemma ae_sourceKernelParticleStatistic_eq_feature {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (h : X × X → ℝ) (k : X → H)
    (heq : h =ᵐ[μ.prod μ] featureKernel k) (N : ℕ) :
    sourceKernelParticleStatistic h N =ᵐ[Measure.pi (fun _ : Fin N => μ)]
      sourceKernelParticleStatistic (featureKernel k) N := by
  filter_upwards [ae_distinct_particle_pairs_congr heq N] with x hx
  unfold sourceKernelParticleStatistic
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hil : i = l
  · simp only [hil, if_true]
  · simp only [hil, if_false]
    exact hx i l hil

lemma sourceKernelParticleStatistic_feature_exponential {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (β : ℝ) (k : X → H)
    (N : ℕ) (hN : 1 ≤ N) (x : Fin N → X) :
    Real.exp (-β / 2 * sourceKernelParticleStatistic (featureKernel k) N x) =
      Real.exp (-β * (N : ℝ) * featureParticleInteraction k N x) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (lt_of_lt_of_le (by norm_num : 0 < 1) hN))
  unfold sourceKernelParticleStatistic featureParticleInteraction featureKernel
  congr 1
  field_simp
  <;> ring

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
  [MeasurableSpace.CountablyGenerated X]

/-- The true source particle statistic and its actual source integral operator
are transported from product-a.e. feature equality. No diagonal value is used. -/
theorem exists_sourceKernelParticleStatistic_feature_rate
    (β : ℝ) (hβ : 0 ≤ β) (h : X × X → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (hmean : (∫ x, k x ∂μ) = 0) (heq : h =ᵐ[μ.prod μ] featureKernel k) :
    ∃ (ι : Type u) (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ)),
      Countable ι ∧
      (∀ i, DGRHS.Kernel.integralOperator h hh (e i) = eig i • e i) ∧
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧ (∑' i, eig i) = ∫ x, ‖k x‖ ^ 2 ∂μ ∧
      ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x => Real.exp (-β / 2 * sourceKernelParticleStatistic h N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |(∫ x, Real.exp (-β / 2 * sourceKernelParticleStatistic h N x)
          ∂Measure.pi (fun _ : Fin N => μ)) -
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          (26 * β ^ 2 + 12 * β ^ 3) * (∫ x, featureExponentialMomentWeight β k x ∂μ) ^ 2 / (N : ℝ) := by
  obtain ⟨ι, eig, e, hi, he, ha, hs, ht, hRate⟩ :=
    exists_separable_featureParticleInteraction_rate β hβ k hk hM hmean
  have hop := integralOperator_eq_of_ae_kernel hh
    (memLp_featureKernel k hk (memLp_feature_of_exponential_moment β hβ k hk hM)) heq
  refine ⟨ι, eig, e, hi, ?_, ha, hs, ht, fun N hN => ?_⟩
  · intro i
    rw [hop]
    exact he i
  · have hp : (fun x => Real.exp (-β / 2 * sourceKernelParticleStatistic h N x))
        =ᵐ[Measure.pi (fun _ : Fin N => μ)]
        (fun x => Real.exp (-β * (N : ℝ) * featureParticleInteraction k N x)) := by
      filter_upwards [ae_sourceKernelParticleStatistic_eq_feature h k heq N] with x hx
      rw [hx, sourceKernelParticleStatistic_feature_exponential β k N hN]
    exact ⟨(hRate N hN).1.congr hp.symm, by rw [integral_congr_ae hp]; exact (hRate N hN).2⟩

end DGRHS.Gaussian

#check DGRHS.Gaussian.measurePreserving_distinct_particle_pair
#print axioms DGRHS.Gaussian.measurePreserving_distinct_particle_pair
#check DGRHS.Gaussian.ae_distinct_particle_pairs_congr
#print axioms DGRHS.Gaussian.ae_distinct_particle_pairs_congr
#check DGRHS.Gaussian.integralOperator_eq_of_ae_kernel
#print axioms DGRHS.Gaussian.integralOperator_eq_of_ae_kernel
#check DGRHS.Gaussian.sourceKernelParticleStatistic
#print axioms DGRHS.Gaussian.sourceKernelParticleStatistic
#check DGRHS.Gaussian.ae_sourceKernelParticleStatistic_eq_feature
#print axioms DGRHS.Gaussian.ae_sourceKernelParticleStatistic_eq_feature
#check DGRHS.Gaussian.sourceKernelParticleStatistic_feature_exponential
#print axioms DGRHS.Gaussian.sourceKernelParticleStatistic_feature_exponential
#check DGRHS.Gaussian.exists_sourceKernelParticleStatistic_feature_rate
#print axioms DGRHS.Gaussian.exists_sourceKernelParticleStatistic_feature_rate
