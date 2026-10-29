import DGRHS.Gaussian.PeriodicPhysicalGreenIdentification

/-! Exact anchoring of the true physical partition under product Haar measure.
All changes of variables preserve the genuine law and allow infinite integrals. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicPhysicalParticleExponent (β : ℝ) (N : ℕ) (x : Fin N → PeriodicTorus ι) : ℝ :=
  β/(2*(N:ℝ))*∑ i,∑ j,if i=j then 0 else periodicPhysicalGreen (x i-x j)

def periodicPhysicalParticleDensity (β : ℝ) (N : ℕ) (x : Fin N → PeriodicTorus ι) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (periodicPhysicalParticleExponent β N x))

lemma periodicPhysicalParticleDensity_measurable (β : ℝ) (N : ℕ) :
    Measurable (periodicPhysicalParticleDensity (ι := ι) β N) := by
  apply Measurable.ennreal_ofReal
  apply Real.continuous_exp.measurable.comp
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  by_cases h : i=j
  · simp only [h,if_true];exact measurable_const
  · simp only [if_neg h]
    exact periodicPhysicalGreen_measurable.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

lemma periodicPhysicalParticleDensity_translate (β : ℝ) (N : ℕ)
    (a : PeriodicTorus ι) (x : Fin N → PeriodicTorus ι) :
    periodicPhysicalParticleDensity β N (fun i => a+x i)=periodicPhysicalParticleDensity β N x := by
  simp [periodicPhysicalParticleDensity,periodicPhysicalParticleExponent]

def periodicAnchoredDensity (β : ℝ) (n : ℕ) (x : Fin n → PeriodicTorus ι) : ℝ≥0∞ :=
  periodicPhysicalParticleDensity β (n+1) (Fin.cons 0 x)

lemma periodicAnchoredDensity_measurable (β : ℝ) (n : ℕ) :
    Measurable (periodicAnchoredDensity (ι := ι) β n) := by
  apply (periodicPhysicalParticleDensity_measurable β (n+1)).comp
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (measurable_const : Measurable (fun _ : Fin n → PeriodicTorus ι => (0:PeriodicTorus ι)))
  · simpa using (measurable_pi_apply j : Measurable (fun x : Fin n → PeriodicTorus ι => x j))

lemma periodicPhysicalDensity_cons_translate (β : ℝ) (n : ℕ)
    (a : PeriodicTorus ι) (x : Fin n → PeriodicTorus ι) :
    periodicPhysicalParticleDensity β (n+1) (Fin.cons a (fun j => a+x j))=periodicAnchoredDensity β n x := by
  have he : Fin.cons a (fun j => a+x j)=(fun i : Fin (n+1) => a+(Fin.cons (0:PeriodicTorus ι) x : Fin (n+1) → PeriodicTorus ι) i) := by
    funext i
    exact Fin.cases (by simp) (fun j => by simp) i
  rw [he,periodicPhysicalParticleDensity_translate]
  rfl

lemma periodicPhysicalDensity_cons_lintegral (β : ℝ) (n : ℕ) (a : PeriodicTorus ι) :
    (∫⁻ x : Fin n → PeriodicTorus ι,periodicPhysicalParticleDensity β (n+1) (Fin.cons a x)
      ∂Measure.pi (fun _ : Fin n => periodicHaar ι))=
    ∫⁻ x : Fin n → PeriodicTorus ι,periodicAnchoredDensity β n x
      ∂Measure.pi (fun _ : Fin n => periodicHaar ι) := by
  have hpa : MeasurePreserving (fun y : PeriodicTorus ι => a+y) (periodicHaar ι) (periodicHaar ι) := by
    convert (periodicHaar_preserving_sub_left a).comp (periodicHaar_preserving_sub_left (0:PeriodicTorus ι)) using 1
    ext y
    simp
  have hp := measurePreserving_pi (fun _ : Fin n => periodicHaar ι) (fun _ : Fin n => periodicHaar ι)
    (fun _ => hpa)
  have hm : Measurable (fun x : Fin n → PeriodicTorus ι =>
      periodicPhysicalParticleDensity β (n+1) (Fin.cons a x)) := by
    apply (periodicPhysicalParticleDensity_measurable β (n+1)).comp
    apply Measurable.of_eval
    intro i
    exact Fin.cases (by simpa using (measurable_const : Measurable (fun _ : Fin n → PeriodicTorus ι => a)))
      (fun j => by simpa using (measurable_pi_apply j : Measurable (fun x : Fin n → PeriodicTorus ι => x j))) i
  have he := lintegral_map (μ := Measure.pi (fun _ : Fin n => periodicHaar ι)) hm hp.measurable
  rw [hp.map_eq] at he
  simpa only [periodicPhysicalDensity_cons_translate] using he

/-- Exact law of all relative coordinates after separating one particle. -/
theorem periodicAttractivePartition_eq_anchored (β : ℝ) (n : ℕ) :
    periodicAttractivePartition (ι := ι) β (n+1)=
      ∫⁻ x : Fin n → PeriodicTorus ι,periodicAnchoredDensity β n x
        ∂Measure.pi (fun _ : Fin n => periodicHaar ι) := by
  rw [periodicAttractivePartition_eq_physical]
  change (∫⁻ x,periodicPhysicalParticleDensity β (n+1) x ∂Measure.pi (fun _ : Fin (n+1) => periodicHaar ι))=_
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => periodicHaar ι) 0).symm
  rw [hp.lintegral_map_equiv (periodicPhysicalParticleDensity β (n+1))]
  have he (p : PeriodicTorus ι × (Fin n → PeriodicTorus ι)) :
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => PeriodicTorus ι) 0).symm p=Fin.cons p.1 p.2 := by
    ext i
    exact Fin.cases (by simp [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv])
      (fun j => by simp [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]) i
  simp_rw [he]
  have hm : Measurable (fun p : PeriodicTorus ι × (Fin n → PeriodicTorus ι) =>
      periodicPhysicalParticleDensity β (n+1) (Fin.cons p.1 p.2)) := by
    apply (periodicPhysicalParticleDensity_measurable β (n+1)).comp
    apply Measurable.of_eval
    intro i
    exact Fin.cases (by simpa using (measurable_fst : Measurable (fun p : PeriodicTorus ι × (Fin n → PeriodicTorus ι) => p.1)))
      (fun j => by simpa [Function.comp_def] using ((measurable_pi_apply j).comp measurable_snd :
        Measurable (fun p : PeriodicTorus ι × (Fin n → PeriodicTorus ι) => p.2 j))) i
  rw [lintegral_prod _ hm.aemeasurable]
  simp only [periodicPhysicalDensity_cons_lintegral,lintegral_const,measure_univ,mul_one]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicAttractivePartition_eq_anchored
#check @DGRHS.Periodic.periodicAttractivePartition_eq_anchored
