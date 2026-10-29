import DGRHS.Gaussian.SharpnessConditionalParticles
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {X α : Type*} [MeasurableSpace X]

lemma sharpness_particle_statistic_lower (H : X × X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ p, -B ≤ H p) (N : ℕ) (hN : 1 ≤ N) (x : Fin N → X) :
    -B*(N:ℝ) ≤ sourceKernelParticleStatistic H N x := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have ht (i j : Fin N) : -B ≤ if i = j then 0 else H (x i,x j) := by
    by_cases hij : i = j
    · simp only [hij,if_true]; linarith
    · simp only [hij,if_false]; exact hH _
  have hs : -B*(N:ℝ)*(N:ℝ) ≤ ∑ i : Fin N,∑ j : Fin N,if i = j then 0 else H (x i,x j) := by
    calc
      _ = ∑ _i : Fin N, ∑ _j : Fin N,-B := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ht i j))
  have hp := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg N : (0:ℝ) ≤ N))
  have he : (N:ℝ)⁻¹*(-B*(N:ℝ)*(N:ℝ)) = -B*(N:ℝ) := by field_simp
  rw [he] at hp
  exact hp

lemma sharpness_particle_exponential_integrable {N : ℕ} {ν : Measure (Fin N → X)} [IsFiniteMeasure ν]
    (H : X × X → ℝ) (hi : Integrable (sourceKernelParticleStatistic H N) ν)
    (B : ℝ) (hB : 0 ≤ B) (hH : ∀ p,-B ≤ H p) (hN : 1 ≤ N)
    (β : ℝ) (hβ : 0 ≤ β) :
    Integrable (fun x => Real.exp (-β/2*sourceKernelParticleStatistic H N x)) ν := by
  apply (integrable_const (Real.exp (β/2*B*(N:ℝ)))).mono'
  · exact Real.continuous_exp.comp_aestronglyMeasurable (hi.const_mul (-β/2)).aestronglyMeasurable
  · apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonpos_left (sharpness_particle_statistic_lower H B hB hH N hN x)
      (by linarith : -β/2 ≤ 0)
    convert hh using 1 <;> ring

/-- Actual finite-product conditional Jensen: the conditional mean and
exponential properness are both derived, not hypotheses of the inequality. -/
theorem sharpness_conditional_particle_jensen (μ : Measure X) [IsFiniteMeasure μ]
    (H : X × X → ℝ) (hH : Integrable H (μ.prod μ))
    (B : ℝ) (hB : 0 ≤ B) (hlo : ∀ p,-B ≤ H p)
    (A : α → Set X) (hA : ∀ i, MeasurableSet (A i)) (hm : ∀ i,0 < (μ (A i)).toReal)
    (N : ℕ) (hN : 1 ≤ N) (l : Fin N → α) (β : ℝ) (hβ : 0 ≤ β) :
    Real.exp (-β/2*sourceKernelParticleStatistic
      (fun p : α × α => sharpnessAtomAverage μ H (A p.1) (A p.2)) N l) ≤
      ∫ x,Real.exp (-β/2*sourceKernelParticleStatistic H N x)
        ∂Measure.pi (fun i => sharpnessNormalizedAtom μ (A (l i))) := by
  let ν := fun i : Fin N => sharpnessNormalizedAtom μ (A (l i))
  haveI : ∀ i,IsProbabilityMeasure (ν i) := fun i => sharpnessNormalizedAtom_probability μ _ (hm _)
  have hp := sharpness_conditional_particle_mean μ H hH A hA hm N l
  have hexp := sharpness_particle_exponential_integrable H hp.1 B hB hlo hN β hβ
  have hc := hp.1.const_mul (-β/2)
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall (fun _ => Set.mem_univ _)) hc hexp
  rw [integral_const_mul,hp.2] at hj
  exact hj

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_conditional_particle_jensen
#check @DGRHS.Gaussian.sharpness_conditional_particle_jensen
