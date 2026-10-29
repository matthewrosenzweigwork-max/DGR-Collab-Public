import DGRHS.Gaussian.PeriodicTrialProbability
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DGRHS.Periodic

lemma ofReal_finite_product {J : Type*} (s : Finset J) (f : J → ℝ)
    (hf : ∀ i,0 ≤ f i) : ENNReal.ofReal (∏ i ∈ s,f i) = ∏ i ∈ s,ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    rw [ENNReal.ofReal_mul (hf i),ih]

/-- Native product uniqueness and genuine restricted product integration
identify the full trial density. No product-law conclusion is assumed. -/
theorem finite_product_withDensity_ofReal {X J : Type*} [MeasurableSpace X] [Fintype J]
    (μ : Measure X) [IsFiniteMeasure μ] (f : J → X → ℝ)
    (hm : ∀ i,Measurable (f i)) (hi : ∀ i,Integrable (f i) μ)
    (hn : ∀ i x,0 ≤ f i x)
    (hp : ∀ i,IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f i x)))) :
    Measure.pi (fun i => μ.withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi (fun _ : J => μ)).withDensity (fun x => ENNReal.ofReal (∏ i,f i (x i))) := by
  classical
  letI : ∀ i,IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f i x))) := hp
  apply Measure.pi_eq
  intro s hs
  have hset : MeasurableSet (Set.univ.pi s) := MeasurableSet.pi countable_univ (fun i _ => hs i)
  rw [withDensity_apply _ hset,Measure.restrict_pi_pi]
  have hip : Integrable (fun x : J → X => ∏ i,f i (x i)) (Measure.pi (fun i => μ.restrict (s i))) :=
    Integrable.fintype_prod (fun i => (hi i).integrableOn)
  rw [← ofReal_integral_eq_lintegral_ofReal hip
    (Filter.Eventually.of_forall fun x => Finset.prod_nonneg (fun i _ => hn i (x i))),
    integral_fintype_prod_eq_prod]
  rw [ofReal_finite_product _ _ (fun i => integral_nonneg (hn i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i),← ofReal_integral_eq_lintegral_ofReal (hi i).integrableOn
    (Filter.Eventually.of_forall fun x => hn i x)]

universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicTrialParticleDensity (i : ι) (ε : ℝ) (N : ℕ) (x : Fin N → PeriodicTorus ι) : ℝ :=
  ∏ j,periodicCosineTrialDensity i ε (x j)

lemma periodicTrialParticleDensity_pos (i : ι) (ε : ℝ) (hε : |ε| ≤ 1/2) (N : ℕ)
    (x : Fin N → PeriodicTorus ι) : 0 < periodicTrialParticleDensity i ε N x := by
  unfold periodicTrialParticleDensity
  apply Finset.prod_pos
  intro j _
  linarith [(periodicCosineTrialDensity_bounds i ε hε (x j)).1]

lemma periodicTrialParticleDensity_measurable (i : ι) (ε : ℝ) (N : ℕ) :
    Measurable (periodicTrialParticleDensity i ε N) := by
  unfold periodicTrialParticleDensity
  exact Finset.measurable_prod _ (fun j _ => (periodicCosineTrialDensity_measurable i ε).comp (measurable_pi_apply j))

lemma periodicTrial_particle_law (i : ι) (ε : ℝ) (hε : |ε| ≤ 1/2) (N : ℕ) :
    Measure.pi (fun _ : Fin N => periodicCosineTrialMeasure i ε) =
      (Measure.pi (fun _ : Fin N => periodicHaar ι)).withDensity
        (fun x => ENNReal.ofReal (periodicTrialParticleDensity i ε N x)) := by
  exact finite_product_withDensity_ofReal (periodicHaar ι) (fun _ : Fin N => periodicCosineTrialDensity i ε)
    (fun _ => periodicCosineTrialDensity_measurable i ε)
    (fun _ => (periodicCosineTrial_positiveBounded i ε hε).integrable)
    (fun _ x => by linarith [(periodicCosineTrialDensity_bounds i ε hε x).1])
    (fun _ => periodicCosineTrialMeasure_probability i ε hε)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.finite_product_withDensity_ofReal
#print axioms DGRHS.Periodic.periodicTrial_particle_law
#check @DGRHS.Periodic.periodicTrial_particle_law
