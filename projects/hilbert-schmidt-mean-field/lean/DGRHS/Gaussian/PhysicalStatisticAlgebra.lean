import DGRHS.Concentration.MasterEnvelope
import DGRHS.Gaussian.FeatureRateSourceKernel

/-! Actual normalized iid off-diagonal linearity and AE pair lower-bound
transfer. Diagonals are removed by labels; AE pair assertions use independent
DISTINCT coordinates and never a diagonal slice. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian
open DGRHS.Concentration

lemma physical_iidNegativeStatistic_const_smul {X : Type*} (n : ℕ) (W : X × X → ℝ)
    (c : ℝ) (ω : Fin n → X) :
    iidNegativeStatistic n (c • W) ω = c*iidNegativeStatistic n W ω := by
  classical
  have he : iidCoupledSum n (c • W) ω = c*iidCoupledSum n W ω := by
    unfold iidCoupledSum DGRHS.Decoupling.offDiagonalSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i ≠ j <;> simp [hij,Pi.smul_apply,smul_eq_mul]
  unfold iidNegativeStatistic
  rw [he]
  ring

lemma physical_iidNegativeStatistic_add {X : Type*} (n : ℕ) (W V : X × X → ℝ)
    (ω : Fin n → X) :
    iidNegativeStatistic n (W+V) ω = iidNegativeStatistic n W ω + iidNegativeStatistic n V ω := by
  classical
  have he : iidCoupledSum n (W+V) ω = iidCoupledSum n W ω+iidCoupledSum n V ω := by
    unfold iidCoupledSum DGRHS.Decoupling.offDiagonalSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i ≠ j <;> simp [hij]
  unfold iidNegativeStatistic
  rw [he]
  ring

lemma ae_physical_iidNegativeStatistic_congr {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) (W V : X × X → ℝ)
    (he : W =ᵐ[μ.prod μ] V) :
    iidNegativeStatistic n W =ᵐ[Measure.pi (fun _ : Fin n => μ)] iidNegativeStatistic n V := by
  classical
  filter_upwards [ae_distinct_particle_pairs_congr he n] with ω hω
  unfold iidNegativeStatistic iidCoupledSum DGRHS.Decoupling.offDiagonalSum
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i ≠ j
  · simp only [hij,if_true,hω i j hij]
  · simp [hij]

lemma ae_physical_iidNegativeStatistic_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) (hn : 1 ≤ n)
    (W : X × X → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hle : ∀ᵐ p ∂μ.prod μ, -W p ≤ 2*C) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => μ), iidNegativeStatistic n W ω ≤ (n : ℝ)*C := by
  classical
  have hpair : ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => μ),
      ∀ i j : Fin n, i ≠ j → -W (ω i,ω j) ≤ 2*C := by
    apply ae_all_iff.2
    intro i
    apply ae_all_iff.2
    intro j
    by_cases hij : i=j
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hij))
    · filter_upwards [(measurePreserving_distinct_particle_pair n i j hij).quasiMeasurePreserving.ae hle] with ω hω
      exact fun _ => hω
  filter_upwards [hpair] with ω hω
  have hs : -iidCoupledSum n W ω ≤ (n : ℝ)^2*(2*C) := by
    unfold iidCoupledSum DGRHS.Decoupling.offDiagonalSum
    rw [← Finset.sum_neg_distrib]
    simp_rw [← Finset.sum_neg_distrib]
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, 2*C := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : i ≠ j
        · rw [if_pos hij]
          exact hω i j hij
        · rw [if_neg hij,neg_zero]
          positivity
      _ = _ := by simp; ring
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hn)
  unfold iidNegativeStatistic
  rw [div_le_iff₀ (by positivity : 0 < 2*(n : ℝ))]
  nlinarith only [hs]

end DGRHS.Gaussian

#check DGRHS.Gaussian.physical_iidNegativeStatistic_const_smul
#print axioms DGRHS.Gaussian.physical_iidNegativeStatistic_const_smul

#check DGRHS.Gaussian.physical_iidNegativeStatistic_add
#print axioms DGRHS.Gaussian.physical_iidNegativeStatistic_add

#check DGRHS.Gaussian.ae_physical_iidNegativeStatistic_congr
#print axioms DGRHS.Gaussian.ae_physical_iidNegativeStatistic_congr

#check DGRHS.Gaussian.ae_physical_iidNegativeStatistic_bound
#print axioms DGRHS.Gaussian.ae_physical_iidNegativeStatistic_bound
