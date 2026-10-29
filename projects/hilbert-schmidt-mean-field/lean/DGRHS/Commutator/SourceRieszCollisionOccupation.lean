import DGRHS.CLT.SourceRieszSingularGibbs
import DGRHS.Commutator.SourceRieszDynamicEntropy
import DGRHS.Commutator.SourceRieszFiniteHorizonSDE
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-! UNCOMPILED collision convention adapter. Finite KL with respect to the
literal Gibbs law implies collision-free configurations at each fixed time.
Joint measurability and Fubini then give zero time occupation almost surely.
This does not assert all-time noncollision or singular-force integrability. -/
noncomputable section
open MeasureTheory InformationTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
open DGRHS.CLT DGRHS.Gaussian
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceRiesz_finiteKL_collision_free
    [Nonempty ι] (s β : ℝ) (ρ : E→ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (N : ℕ)
    (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure (sourceRieszSingularGibbs s β ρ N)]
    (hKL : klDiv ν (sourceRieszSingularGibbs s β ρ N)≠∞) :
    ∀ᵐ x ∂ν,∀ i j : Fin N,i≠j → x i≠x j := by
  have hAC := (klDiv_ne_top_iff.mp hKL).1
  have hG : sourceRieszSingularGibbs s β ρ N ≪
      Measure.pi (fun _:Fin N=>gaussianRieszDensityMeasure ρ) :=
    withDensity_absolutelyContinuous _ _
  exact (hAC.trans hG).ae_le (density_iid_collision_free ρ N)

lemma sourceRiesz_collision_time_occupation
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (N : ℕ)
    (X : ℝ→Ω→Fin N→E) (hXm : Measurable (Function.uncurry X))
    (hc : ∀ r∈Ioc 0 T,∀ᵐ ω ∂P,∀ i j : Fin N,i≠j → X r ω i≠X r ω j) :
    ∀ᵐ ω ∂P,∀ᵐ r ∂volume.restrict (Ioc 0 T),∀ i j : Fin N,i≠j → X r ω i≠X r ω j := by
  have he (i j : Fin N) : ∀ᵐ ω ∂P,∀ᵐ r ∂volume.restrict (Ioc 0 T),
      i≠j → X r ω i≠X r ω j := by
    by_cases hij : i=j
    · exact ae_of_all _ (fun ω=>ae_of_all _ (fun r h=>False.elim (h hij)))
    · have hm : MeasurableSet {p:ℝ×Ω | X p.1 p.2 i≠X p.1 p.2 j} :=
        (measurableSet_eq_fun ((measurable_pi_apply i).comp hXm)
          ((measurable_pi_apply j).comp hXm)).compl
      have ht : ∀ᵐ r ∂volume.restrict (Ioc 0 T),∀ᵐ ω ∂P,X r ω i≠X r ω j := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact (hc r hr).mono (fun ω hω=>hω i j hij)
      exact ((Measure.ae_ae_comm hm).mp ht).mono
        (fun ω hω=>hω.mono (fun r hr _=>hr))
  filter_upwards [ae_all_iff.2 (fun i=>ae_all_iff.2 (fun j=>he i j))] with ω hω
  exact ae_all_iff.2 (fun i=>ae_all_iff.2 (fun j=>hω i j))


/-- The actual particle-law KL hypotheses suffice; no pointwise collision law
is supplied by the user. Their finiteness is supplied in the dynamic consumer
by the already proved physical free-energy/Gronwall entropy estimate. -/
lemma sourceRiesz_finiteKL_particle_collision_time
    [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P] (T s β : ℝ) (N : ℕ)
    (ρ : ℝ→E→ℝ) (X : ℝ→Ω→Fin N→E) (hXm : Measurable (Function.uncurry X))
    (hρ : ∀ r∈Ioc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hG : ∀ r∈Ioc 0 T,IsProbabilityMeasure (sourceRieszSingularGibbs s β (ρ r) N))
    (hKL : ∀ r∈Ioc 0 T,klDiv (P.map (X r)) (sourceRieszSingularGibbs s β (ρ r) N)≠∞) :
    ∀ᵐ ω ∂P,∀ᵐ r ∂volume.restrict (Ioc 0 T),∀ i j : Fin N,i≠j → X r ω i≠X r ω j := by
  apply sourceRiesz_collision_time_occupation P T N X hXm
  intro r hr
  letI := hρ r hr
  letI := hG r hr
  have hXr : Measurable (X r) := hXm.comp (measurable_const.prodMk measurable_id)
  letI : IsProbabilityMeasure (P.map (X r)) :=
    (Measure.isProbabilityMeasure_map_iff hXr.aemeasurable).mpr inferInstance
  have hcf := sourceRiesz_finiteKL_collision_free s β (ρ r) N (P.map (X r)) (hKL r hr)
  have hmp : MeasurePreserving (X r) P (P.map (X r)) := ⟨hXr,rfl⟩
  exact hmp.quasiMeasurePreserving.ae hcf


/-- Actual source free-energy control implies zero collision-time occupation
from only horizon-restricted joint measurability. Gibbs properness and finite
particle-law KL are derived here; they are not extra original assumptions. -/
theorem sourceRiesz_gronwall_particle_collision_time
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ≥0)
    (s β M : ℝ) (hs : 0<s) (hβ : 0<β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M)
    (N : ℕ) (hN : 1≤N) (ρ : ℝ→E→ℝ) (X : ℝ→Ω→Fin N→E)
    (hXm : Measurable (fun p:Icc (0:ℝ) (T:ℝ)×Ω=>X p.1 p.2))
    (hprob : ∀ r∈Icc 0 (T:ℝ),IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hρ : ∀ r∈Icc 0 (T:ℝ),∀ᵐ z ∂volume,ρ r z≤M)
    (G D : ℝ→ℝ)
    (hE : ∀ r∈Icc 0 (T:ℝ),
      sourceRieszTransportExtendedFreeEnergy (ρ r) s M β N (P.map (X r))≤
        (G r:EReal)*sourceRieszTransportExtendedFreeEnergy (ρ 0) s M β N
          (sourceRieszSingularGibbs s β (ρ 0) N)+(D r/(N:ℝ):ℝ)) :
    ∀ᵐ ω ∂P,∀ᵐ r ∂volume.restrict (Ioc 0 (T:ℝ)),
      ∀ i j : Fin N,i≠j → X r ω i≠X r ω j := by
  have hdpos : 0<Fintype.card ι := by
    exact_mod_cast (show (0:ℝ)<(Fintype.card ι:ℝ) by linarith)
  letI : Nonempty ι := Fintype.card_pos_iff.mp hdpos
  let Xe := sourceRieszParticleRealHorizonExtension T N X
  have hXem := sourceRieszParticleRealHorizonExtension_measurable T N X hXm
  have he (r:ℝ) (hr:r∈Icc 0 (T:ℝ)) : Xe r=X r :=
    sourceRieszParticleRealHorizonExtension_eq T N X r hr
  have hp (r:ℝ) (hr:r∈Ioc 0 (T:ℝ)) :
      IsProbabilityMeasure (sourceRieszSingularGibbs s β (ρ r) N) := by
    letI := hprob r ⟨hr.1.le,hr.2⟩
    exact sourceRieszSingularGibbs_probability s β hs hβ.le (by linarith) (ρ r) M hM
      (hρ r ⟨hr.1.le,hr.2⟩) N
  have hKL (r:ℝ) (hr:r∈Ioc 0 (T:ℝ)) :
      klDiv (P.map (Xe r)) (sourceRieszSingularGibbs s β (ρ r) N)≠∞ := by
    have hr' : r∈Icc 0 (T:ℝ) := ⟨hr.1.le,hr.2⟩
    letI := hprob 0 ⟨le_rfl,T.coe_nonneg⟩
    letI := hprob r hr'
    have hm : Measurable (Xe r) := hXem.comp (measurable_const.prodMk measurable_id)
    letI : IsProbabilityMeasure (P.map (Xe r)) :=
      (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
    exact (sourceRieszDynamic_entropy_from_gronwall s β M hs hβ hd hM (ρ 0) (ρ r)
      (hρ 0 ⟨le_rfl,T.coe_nonneg⟩) (hρ r hr') N hN (P.map (Xe r)) (G r) (D r)
      (by simpa only [he r hr'] using hE r hr')).1
  have hc := sourceRiesz_finiteKL_particle_collision_time P (T:ℝ) s β N ρ Xe hXem
    (fun r hr=>hprob r ⟨hr.1.le,hr.2⟩) hp hKL
  filter_upwards [hc] with ω hω
  filter_upwards [hω,ae_restrict_mem measurableSet_Ioc] with r hr hrT
  simpa only [he r ⟨hrT.1.le,hrT.2⟩] using hr

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.sourceRiesz_finiteKL_collision_free
#print axioms DGRHS.Commutator.sourceRiesz_finiteKL_collision_free
#check @DGRHS.Commutator.sourceRiesz_collision_time_occupation
#print axioms DGRHS.Commutator.sourceRiesz_collision_time_occupation

#check @DGRHS.Commutator.sourceRiesz_finiteKL_particle_collision_time
#print axioms DGRHS.Commutator.sourceRiesz_finiteKL_particle_collision_time

#check @DGRHS.Commutator.sourceRiesz_gronwall_particle_collision_time
#print axioms DGRHS.Commutator.sourceRiesz_gronwall_particle_collision_time
