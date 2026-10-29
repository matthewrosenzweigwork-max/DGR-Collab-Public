import DGRHS.Gaussian.PeriodicTrialProductLaw
import DGRHS.Decoupling.Moment

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace DGRHS.Periodic

lemma iid_offdiagonal_sum_mean {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (H : X × X → ℝ)
    (hH : Integrable H (μ.prod μ)) (N : ℕ) :
    Integrable (fun x : Fin N → X => ∑ i,∑ j,if i=j then 0 else H (x i,x j))
      (Measure.pi (fun _ : Fin N => μ)) ∧
    (∫ x : Fin N → X,∑ i,∑ j,if i=j then 0 else H (x i,x j)
      ∂Measure.pi (fun _ : Fin N => μ)) =
      (N:ℝ)*((N:ℝ)-1)*(∫ p,H p ∂μ.prod μ) := by
  classical
  let ν := Measure.pi (fun _ : Fin N => μ)
  have ht (i j : Fin N) : Integrable (fun x : Fin N → X => if i=j then 0 else H (x i,x j)) ν := by
    by_cases hij : i=j
    · simp only [hij,if_true]; exact integrable_zero _ _ _
    · simp only [hij,if_false]
      exact (DGRHS.Decoupling.pair_eval_measurePreserving μ i j hij).integrable_comp_of_integrable hH
  have hsum : Integrable (fun x : Fin N → X => ∑ i,∑ j,if i=j then 0 else H (x i,x j)) ν :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ht i j))
  refine ⟨hsum,?_⟩
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ht i j))]
  have hrow (i : Fin N) : (∫ x : Fin N → X,∑ j,if i=j then 0 else H (x i,x j) ∂ν) =
      ((N:ℝ)-1)*(∫ p,H p ∂μ.prod μ) := by
    rw [integral_finsetSum _ (fun j _ => ht i j)]
    calc
      _ = ∑ j : Fin N,((∫ p,H p ∂μ.prod μ) - if i=j then (∫ p,H p ∂μ.prod μ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i=j
        · simp [hij]
        · simp only [hij,if_false,sub_zero]
          exact DGRHS.Decoupling.integral_comp_preserving
            (DGRHS.Decoupling.pair_eval_measurePreserving μ i j hij) H hH.aestronglyMeasurable
      _ = _ := by rw [Finset.sum_sub_distrib]; simp; ring
  simp_rw [hrow]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicParticleExponent (β : ℝ) (N : ℕ) (x : Fin N → PeriodicTorus ι) : ℝ :=
  β/(2*(N:ℝ))*∑ i,∑ j,if i=j then 0 else periodicLogKernel (x i-x j)

lemma periodicTrial_particle_exponent_mean (i : ι) (ε β : ℝ) (hε : |ε| ≤ 1/2)
    (N : ℕ) (hN : 1 ≤ N) :
    Integrable (periodicParticleExponent β N)
      (Measure.pi (fun _ : Fin N => periodicCosineTrialMeasure i ε)) ∧
    (∫ x,periodicParticleExponent β N x
      ∂Measure.pi (fun _ : Fin N => periodicCosineTrialMeasure i ε)) =
      β/2*((N:ℝ)-1)*(ε^2/(2*periodicStabilityThreshold ι)) := by
  haveI := periodicCosineTrialMeasure_probability i ε hε
  have h := iid_offdiagonal_sum_mean (periodicCosineTrialMeasure i ε)
    (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (p.1-p.2))
    (periodicCosineTrialMeasure_pair_integrable i ε hε) N
  refine ⟨h.1.const_mul _,?_⟩
  unfold periodicParticleExponent
  rw [integral_const_mul,h.2,periodicCosineTrialMeasure_pair_integral i ε hε]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp
  <;> ring

lemma periodicCosineTrial_log_integrable (i : ι) (ε : ℝ) (hε : |ε| ≤ 1/2) :
    Integrable (fun x => Real.log (periodicCosineTrialDensity i ε x)) (periodicCosineTrialMeasure i ε) := by
  haveI := periodicCosineTrialMeasure_probability i ε hε
  apply DGRHS.Concentration.PositiveBounded.log_integrable (c := 1/2) (C := 3/2)
  exact ⟨(periodicCosineTrialDensity_measurable i ε).aestronglyMeasurable,by norm_num,by norm_num,
    Filter.Eventually.of_forall (periodicCosineTrialDensity_bounds i ε hε)⟩

lemma periodicTrial_particle_log_mean (i : ι) (ε : ℝ) (hε : |ε| ≤ 1/2) (N : ℕ) :
    Integrable (fun x => Real.log (periodicTrialParticleDensity i ε N x))
      (Measure.pi (fun _ : Fin N => periodicCosineTrialMeasure i ε)) ∧
    (∫ x,Real.log (periodicTrialParticleDensity i ε N x)
      ∂Measure.pi (fun _ : Fin N => periodicCosineTrialMeasure i ε)) =
      (N:ℝ)*(∫ x,periodicCosineTrialDensity i ε x * Real.log (periodicCosineTrialDensity i ε x) ∂periodicHaar ι) := by
  classical
  haveI := periodicCosineTrialMeasure_probability i ε hε
  have he (x : Fin N → PeriodicTorus ι) : Real.log (periodicTrialParticleDensity i ε N x) =
      ∑ j,Real.log (periodicCosineTrialDensity i ε (x j)) := by
    apply Real.log_prod
    intro j _
    have h := periodicCosineTrialDensity_bounds i ε hε (x j)
    linarith [h.1]
  have hj (j : Fin N) : Integrable (fun x : Fin N → PeriodicTorus ι =>
      Real.log (periodicCosineTrialDensity i ε (x j)))
      (Measure.pi (fun _ : Fin N => periodicCosineTrialMeasure i ε)) := (measurePreserving_eval (fun _ : Fin N => periodicCosineTrialMeasure i ε) j).integrable_comp_of_integrable (periodicCosineTrial_log_integrable i ε hε)
  simp_rw [he]
  refine ⟨integrable_finsetSum _ (fun j _ => hj j),?_⟩
  rw [integral_finsetSum _ (fun j _ => hj j)]
  have hm (j : Fin N) := DGRHS.Decoupling.integral_comp_preserving
    (measurePreserving_eval (fun _ : Fin N => periodicCosineTrialMeasure i ε) j)
    (fun x => Real.log (periodicCosineTrialDensity i ε x))
    (periodicCosineTrial_log_integrable i ε hε).aestronglyMeasurable
  simp_rw [hm,periodicCosineTrialMeasure_integral i ε hε]
  simp

end DGRHS.Periodic
#print axioms DGRHS.Periodic.iid_offdiagonal_sum_mean
#print axioms DGRHS.Periodic.periodicTrial_particle_exponent_mean
#print axioms DGRHS.Periodic.periodicTrial_particle_log_mean
#check @DGRHS.Periodic.periodicTrial_particle_exponent_mean
