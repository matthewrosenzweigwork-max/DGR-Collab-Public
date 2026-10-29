import DGRHS.Gaussian.FeatureRateParticleLaplace
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.Gaussian
universe u v
variable {X : Type u} {H : Type v} {j : Type*}
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def featureParticleInteraction (k : X → H) (N : ℕ) (x : Fin N → X) : ℝ :=
  (2 * (N : ℝ) ^ 2)⁻¹ * ∑ i : Fin N, ∑ l : Fin N,
    if i = l then 0 else inner ℝ (k (x i)) (k (x l))

lemma feature_particle_off_diagonal_sum (k : X → H) (N : ℕ) (x : Fin N → X) :
    (∑ i : Fin N, ∑ l : Fin N, if i = l then 0 else inner ℝ (k (x i)) (k (x l))) =
      ‖∑ i : Fin N, k (x i)‖ ^ 2 - ∑ i : Fin N, ‖k (x i)‖ ^ 2 := by
  classical
  have hs (i : Fin N) : (∑ l : Fin N, inner ℝ (k (x i)) (k (x l))) =
      ‖k (x i)‖ ^ 2 + ∑ l : Fin N, if i = l then 0 else inner ℝ (k (x i)) (k (x l)) := by
    calc
      _ = ∑ l : Fin N, ((if i = l then inner ℝ (k (x i)) (k (x i)) else 0) +
          (if i = l then 0 else inner ℝ (k (x i)) (k (x l)))) := by
        apply Finset.sum_congr rfl
        intro l hl
        by_cases h : i = l
        · subst l
          simp
        · simp only [h, if_false, zero_add]
      _ = _ := by rw [Finset.sum_add_distrib]; simp [real_inner_self_eq_norm_sq]
  have hp : ‖∑ i : Fin N, k (x i)‖ ^ 2 =
      (∑ i : Fin N, ‖k (x i)‖ ^ 2) +
      ∑ i : Fin N, ∑ l : Fin N, if i = l then 0 else inner ℝ (k (x i)) (k (x l)) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum, hs]
    rw [Finset.sum_add_distrib]
  linarith

lemma featureParticleExp_eq_interaction (β : ℝ) (k : X → H)
    (N : ℕ) (hN : 1 ≤ N) (x : Fin N → X) :
    featureParticleExp β k N x = Real.exp (-β * (N : ℝ) * featureParticleInteraction k N x) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (lt_of_lt_of_le (by norm_num : 0 < 1) hN))
  unfold featureParticleExp featureParticleInteraction
  rw [feature_particle_off_diagonal_sum]
  congr 1
  field_simp
  <;> ring

/-- Actual positive feature U-statistic rate. All spectral data are constructed
from its Gram integral operator and no expansion, moment, parity or determinant
identity is assumed. The supplied Gaussian field retains the same hW witness. -/
theorem exists_featureParticleInteraction_rate
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [Countable j]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace.CountablyGenerated X]
    (b : HilbertBasis j ℝ H) (f : j → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (hmean : (∫ x, k x ∂μ) = 0)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    ∃ (ι : Type u) (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ)),
      Countable ι ∧
      (∀ i, DGRHS.Kernel.integralOperator (featureKernel k)
        (memLp_featureKernel k hk (memLp_feature_of_exponential_moment β hβ k hk hM)) (e i) = eig i • e i) ∧
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧ (∑' i, eig i) = ∫ x, ‖k x‖ ^ 2 ∂μ ∧
      ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x => Real.exp (-β * (N : ℝ) * featureParticleInteraction k N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |(∫ x, Real.exp (-β * (N : ℝ) * featureParticleInteraction k N x)
          ∂Measure.pi (fun _ : Fin N => μ)) -
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          (26 * β ^ 2 + 12 * β ^ 3) * (∫ x, featureExponentialMomentWeight β k x ∂μ) ^ 2 / (N : ℝ) := by
  obtain ⟨ι, eig, e, hi, he, ha, hs, ht, hRate⟩ :=
    exists_featureOscillatoryFactor_rate b f hf β hβ k hk hM hmean g hg hW
  refine ⟨ι, eig, e, hi, he, ha, hs, ht, fun N hN => ⟨?_, ?_⟩⟩
  · apply (integrable_featureParticleExp b f hf β hβ k hk hM g hg hW N hN).congr
    exact Filter.Eventually.of_forall (featureParticleExp_eq_interaction β k N hN)
  · have h := (hRate N hN).2
    rw [← integral_featureParticleExp_eq_integral_featureOscillatoryFactor_pow b f hf β hβ k hk hM g hg hW N hN] at h
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    simpa only [featureParticleExp_eq_interaction β k N hN] using h

lemma featureParticleInteraction_rate_source_form (β M Z L : ℝ)
    (hβ : 0 ≤ β) (hM : 0 ≤ M) (N : ℕ) (hN : 1 ≤ N)
    (h : |Z - L| ≤ (26 * β ^ 2 + 12 * β ^ 3) * M ^ 2 / (N : ℝ)) :
    |Z - L| ≤ (26 * β ^ 2 + 12 * β ^ 3) * (1 + M) ^ 3 / (N : ℝ) := by
  apply h.trans
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hN)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (feature_rate_moment_sq_le_source_cube M hM) (by positivity)) hNp.le

end DGRHS.Gaussian

#check DGRHS.Gaussian.featureParticleInteraction
#print axioms DGRHS.Gaussian.featureParticleInteraction

#check DGRHS.Gaussian.feature_particle_off_diagonal_sum
#print axioms DGRHS.Gaussian.feature_particle_off_diagonal_sum

#check DGRHS.Gaussian.featureParticleExp_eq_interaction
#print axioms DGRHS.Gaussian.featureParticleExp_eq_interaction

#check DGRHS.Gaussian.exists_featureParticleInteraction_rate
#print axioms DGRHS.Gaussian.exists_featureParticleInteraction_rate

#check DGRHS.Gaussian.featureParticleInteraction_rate_source_form
#print axioms DGRHS.Gaussian.featureParticleInteraction_rate_source_form
