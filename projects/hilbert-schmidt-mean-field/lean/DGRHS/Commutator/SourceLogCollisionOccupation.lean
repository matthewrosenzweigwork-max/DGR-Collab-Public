import DGRHS.Commutator.SourceRieszCollisionOccupation
import DGRHS.Dynamics.SourceLogDynamicEntropy

/-! Actual logarithmic Gibbs finite entropy gives zero collision occupation.
This uses the literal logarithmic Gibbs law and its true free energy. The
Fubini occupation lemma alone is interaction-independent. No all-time
noncollision or singular-force integrability is inferred. New body awaits
restricted compiler feedback and independent exact source review. -/
noncomputable section
open MeasureTheory InformationTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
open DGRHS.CLT DGRHS.Gaussian DGRHS.Dynamics DGRHS.Entropy
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceLog_finiteKL_collision_free
    [Nonempty ι] (β : ℝ≥0) (ρ : E→ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (N : ℕ)
    (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure (sourceLogSingularGibbs β ρ N)]
    (hKL : klDiv ν (sourceLogSingularGibbs β ρ N)≠∞) :
    ∀ᵐ x ∂ν,∀ i j : Fin N,i≠j → x i≠x j := by
  have hAC := (klDiv_ne_top_iff.mp hKL).1
  have hG : sourceLogSingularGibbs β ρ N ≪
      Measure.pi (fun _:Fin N=>gaussianRieszDensityMeasure ρ) :=
    withDensity_absolutelyContinuous _ _
  exact (hAC.trans hG).ae_le (density_iid_collision_free ρ N)

lemma sourceLog_finiteKL_particle_collision_time
    [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (β : ℝ≥0) (N : ℕ)
    (ρ : ℝ→E→ℝ) (X : ℝ→Ω→Fin N→E) (hXm : Measurable (Function.uncurry X))
    (hρ : ∀ r∈Ioc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hG : ∀ r∈Ioc 0 T,IsProbabilityMeasure (sourceLogSingularGibbs β (ρ r) N))
    (hKL : ∀ r∈Ioc 0 T,klDiv (P.map (X r)) (sourceLogSingularGibbs β (ρ r) N)≠∞) :
    ∀ᵐ ω ∂P,∀ᵐ r ∂volume.restrict (Ioc 0 T),∀ i j : Fin N,i≠j → X r ω i≠X r ω j := by
  apply sourceRiesz_collision_time_occupation P T N X hXm
  intro r hr
  letI := hρ r hr
  letI := hG r hr
  have hXr : Measurable (X r) := hXm.comp (measurable_const.prodMk measurable_id)
  letI : IsProbabilityMeasure (P.map (X r)) :=
    (Measure.isProbabilityMeasure_map_iff hXr.aemeasurable).mpr inferInstance
  have hcf := sourceLog_finiteKL_collision_free β (ρ r) N (P.map (X r)) (hKL r hr)
  have hmp : MeasurePreserving (X r) P (P.map (X r)) := ⟨hXr,rfl⟩
  exact hmp.quasiMeasurePreserving.ae hcf


theorem sourceLog_gronwall_particle_collision_time
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ≥0)
    (β : ℝ≥0) (M : ℝ) (hβ : 0<(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (hM : 0≤M)
    (N : ℕ) (hN : 1≤N) (ρ : ℝ→E→ℝ) (X : ℝ→Ω→Fin N→E)
    (hXm : Measurable (fun p:Icc (0:ℝ) (T:ℝ)×Ω=>X p.1 p.2))
    (hprob : ∀ r∈Icc 0 (T:ℝ),IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hρ : ∀ r∈Icc 0 (T:ℝ),∀ᵐ z ∂volume,ρ r z≤M)
    (hpair : ∀ r∈Icc 0 (T:ℝ),Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure (ρ r)).prod (gaussianRieszDensityMeasure (ρ r))))
    (G D : ℝ→ℝ)
    (hE : ∀ r∈Icc 0 (T:ℝ),sourceLogCollisionFreeEnergy β (ρ r) M N (P.map (X r))≤
      (G r:EReal)*sourceLogCollisionFreeEnergy β (ρ 0) M N (sourceLogSingularGibbs β (ρ 0) N)+
        (D r/(N:ℝ):ℝ)) :
    ∀ᵐ ω ∂P,∀ᵐ r ∂volume.restrict (Ioc 0 (T:ℝ)),
      ∀ i j:Fin N,i≠j → X r ω i≠X r ω j := by
  have hdpos : 0<Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hdpos
  let Xe := sourceRieszParticleRealHorizonExtension T N X
  have hXem := sourceRieszParticleRealHorizonExtension_measurable T N X hXm
  have he (r:ℝ) (hr:r∈Icc 0 (T:ℝ)) : Xe r=X r :=
    sourceRieszParticleRealHorizonExtension_eq T N X r hr
  have hp (r:ℝ) (hr:r∈Ioc 0 (T:ℝ)) :
      IsProbabilityMeasure (sourceLogSingularGibbs β (ρ r) N) := by
    letI := hprob r ⟨hr.1.le,hr.2⟩
    exact sourceLogSingularGibbs_probability β hd (ρ r) M hM
      (hρ r ⟨hr.1.le,hr.2⟩) (hpair r ⟨hr.1.le,hr.2⟩) N
  have hKL (r:ℝ) (hr:r∈Ioc 0 (T:ℝ)) :
      klDiv (P.map (Xe r)) (sourceLogSingularGibbs β (ρ r) N)≠∞ := by
    have hr' : r∈Icc 0 (T:ℝ) := ⟨hr.1.le,hr.2⟩
    letI := hprob 0 ⟨le_rfl,T.coe_nonneg⟩
    letI := hprob r hr'
    have hm : Measurable (Xe r) := hXem.comp (measurable_const.prodMk measurable_id)
    letI : IsProbabilityMeasure (P.map (Xe r)) :=
      (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
    exact (sourceLog_dynamic_entropy_from_gronwall β hβ hd (ρ 0) (ρ r) M M hM hM
      (hρ 0 ⟨le_rfl,T.coe_nonneg⟩) (hρ r hr')
      (hpair 0 ⟨le_rfl,T.coe_nonneg⟩) (hpair r hr') N hN (P.map (Xe r)) (G r) (D r)
      (by simpa only [he r hr'] using hE r hr')).1
  have hc := sourceLog_finiteKL_particle_collision_time P (T:ℝ) β N ρ Xe hXem
    (fun r hr=>hprob r ⟨hr.1.le,hr.2⟩) hp hKL
  filter_upwards [hc] with ω hω
  filter_upwards [hω,ae_restrict_mem measurableSet_Ioc] with r hr hrT
  simpa only [he r ⟨hrT.1.le,hrT.2⟩] using hr

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.sourceLog_finiteKL_collision_free
#print axioms DGRHS.Commutator.sourceLog_finiteKL_collision_free
#check @DGRHS.Commutator.sourceLog_finiteKL_particle_collision_time
#print axioms DGRHS.Commutator.sourceLog_finiteKL_particle_collision_time
#check @DGRHS.Commutator.sourceLog_gronwall_particle_collision_time
#print axioms DGRHS.Commutator.sourceLog_gronwall_particle_collision_time
