import DGRHS.Gaussian.PeriodicD11Probability
import DGRHS.Gaussian.PeriodicTrialParticleMean

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal
namespace DGRHS.Periodic
open DGRHS.Gaussian.D11Imported.HighDim
open DGRHS.Gaussian.D11Imported.HighDim.Eleven

def periodicD11ParticleDensity (N : ℕ) (x : Fin N → Torus 11) : ℝ :=
  ∏ j,periodizedProfile (x j)

lemma periodicD11ParticleDensity_pos (N : ℕ) (x : Fin N → Torus 11) :
    0<periodicD11ParticleDensity N x := Finset.prod_pos (fun _ _ => periodizedProfile_pos _)

lemma periodicD11ParticleDensity_measurable (N : ℕ) : Measurable (periodicD11ParticleDensity N) :=
  Finset.measurable_prod _ (fun j _ => periodizedProfile_measurable.comp (measurable_pi_apply j))

lemma periodicD11_particle_law (N : ℕ) :
    Measure.pi (fun _ : Fin N => periodicD11Measure)=
      (Measure.pi (fun _ : Fin N => periodicHaar (Fin 11))).withDensity
        (fun x => ENNReal.ofReal (periodicD11ParticleDensity N x)) := by
  exact finite_product_withDensity_ofReal (periodicHaar (Fin 11)) (fun _ : Fin N => periodizedProfile)
    (fun _ => periodizedProfile_measurable) (fun _ => periodizedProfile_integrable)
    (fun _ x => (periodizedProfile_pos x).le) (fun _ => periodicD11Measure_probability)

lemma periodicD11_particle_exponent_mean (β : ℝ) (N : ℕ) (hN : 1≤N) :
    Integrable (periodicParticleExponent (ι := Fin 11) β N)
      (Measure.pi (fun _ : Fin N => periodicD11Measure)) ∧
    (∫ x,periodicParticleExponent β N x ∂Measure.pi (fun _ : Fin N => periodicD11Measure))=
      β/2*((N:ℝ)-1)*periodicD11GreenEnergy := by
  have h := iid_offdiagonal_sum_mean periodicD11Measure
    (fun p : Torus 11 × Torus 11 => periodicLogKernel (p.1-p.2)) periodicD11Measure_pair_integrable N
  refine ⟨h.1.const_mul _,?_⟩
  unfold periodicParticleExponent
  rw [integral_const_mul,h.2,periodicD11Measure_pair_integral]
  have hn : (N:ℝ)≠0 := by exact_mod_cast (by omega : N≠0)
  field_simp
  <;> ring

lemma periodicD11_log_integrable : Integrable (fun x => Real.log (periodizedProfile x)) periodicD11Measure := by
  obtain ⟨B,hB⟩ := periodizedProfile_bounded
  have hb (x : Torus 11) : periodizedProfile x≤B :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB x)
  apply DGRHS.Concentration.PositiveBounded.log_integrable (c := profileLower) (C := B)
  exact ⟨periodizedProfile_measurable.aestronglyMeasurable,profileLower_pos,
    (periodizedProfile_lower 0).trans (hb 0),Eventually.of_forall fun x => ⟨periodizedProfile_lower x,hb x⟩⟩

lemma periodicD11_particle_log_mean (N : ℕ) :
    Integrable (fun x => Real.log (periodicD11ParticleDensity N x))
      (Measure.pi (fun _ : Fin N => periodicD11Measure)) ∧
    (∫ x,Real.log (periodicD11ParticleDensity N x) ∂Measure.pi (fun _ : Fin N => periodicD11Measure))=
      (N:ℝ)*entropy competitorDensity := by
  classical
  have he (x : Fin N → Torus 11) : Real.log (periodicD11ParticleDensity N x)=
      ∑ j,Real.log (periodizedProfile (x j)) :=
    Real.log_prod (fun j _ => (periodizedProfile_pos (x j)).ne')
  have hj (j : Fin N) : Integrable (fun x : Fin N → Torus 11 => Real.log (periodizedProfile (x j)))
      (Measure.pi (fun _ : Fin N => periodicD11Measure)) :=
    (measurePreserving_eval (fun _ : Fin N => periodicD11Measure) j).integrable_comp_of_integrable
      periodicD11_log_integrable
  simp_rw [he]
  refine ⟨integrable_finsetSum _ (fun j _ => hj j),?_⟩
  rw [integral_finsetSum _ (fun j _ => hj j)]
  have hm (j : Fin N) := DGRHS.Decoupling.integral_comp_preserving
    (measurePreserving_eval (fun _ : Fin N => periodicD11Measure) j)
    (fun x => Real.log (periodizedProfile x)) periodicD11_log_integrable.aestronglyMeasurable
  simp_rw [hm,periodicD11Measure_integral]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rfl

lemma periodicD11ParticleDensity_positiveBounded (N : ℕ) : ∃ C : ℝ,
    DGRHS.Concentration.PositiveBounded (Measure.pi (fun _ : Fin N => periodicHaar (Fin 11)))
      (periodicD11ParticleDensity N) (profileLower^N) C := by
  classical
  obtain ⟨B,hB⟩ := periodizedProfile_bounded
  have hb (x : Torus 11) : periodizedProfile x≤B :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB x)
  refine ⟨B^N,(periodicD11ParticleDensity_measurable N).aestronglyMeasurable,pow_pos profileLower_pos N,
    pow_le_pow_left₀ profileLower_pos.le ((periodizedProfile_lower 0).trans (hb 0)) N,
    Eventually.of_forall fun x => ?_⟩
  constructor
  · have h := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : Fin N => profileLower)
      (g := fun j => periodizedProfile (x j)) (fun _ _ => profileLower_pos.le)
      (fun j _ => periodizedProfile_lower (x j))
    simpa [periodicD11ParticleDensity] using h
  · have h := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun j : Fin N => periodizedProfile (x j))
      (g := fun _ => B) (fun j _ => (periodizedProfile_pos (x j)).le) (fun j _ => hb (x j))
    simpa [periodicD11ParticleDensity] using h

lemma periodicD11ParticleDensity_integral (N : ℕ) :
    (∫ x,periodicD11ParticleDensity N x ∂Measure.pi (fun _ : Fin N => periodicHaar (Fin 11)))=1 := by
  unfold periodicD11ParticleDensity
  rw [integral_fintype_prod_eq_prod]
  change (∏ _ : Fin N,∫ x,periodizedProfile x ∂torusMeasure 11)=1
  simp only [periodizedProfile_integral,Finset.prod_const_one]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicD11_particle_exponent_mean
#print axioms DGRHS.Periodic.periodicD11_particle_log_mean
#print axioms DGRHS.Periodic.periodicD11ParticleDensity_positiveBounded
