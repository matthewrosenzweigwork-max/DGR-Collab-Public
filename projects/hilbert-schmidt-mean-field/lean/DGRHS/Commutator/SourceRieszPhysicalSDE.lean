import DGRHS.Commutator.SourceRieszCollisionOccupation
import DGRHS.Commutator.SourceRieszDynamicForceEmpirical

/-! UNCOMPILED literal-force adapter. Zero collision-time occupation makes
all off-diagonal forces equal to the native gradient of the singular source
potential almost everywhere in time. The given SDE drift integrability is
transported through this equality; it is not inferred from noncollision.
No all-time noncollision claim is used or proved. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι Ω : Type*} [Fintype ι] [mΩ : MeasurableSpace Ω]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceRieszParticleSDEDrift_eq_physical
    (s : ℝ) (hs : 0<s) (N : ℕ) (x : Fin N→E)
    (hx : ∀ i j:Fin N,i≠j → x i≠x j) (i : Fin N) :
    sourceRieszParticleSDEDrift s N x i=
      -((N:ℝ)⁻¹) • ∑ j ∈ Finset.univ.erase i,gradient (sourceRieszPotential s) (x i-x j) := by
  classical
  unfold sourceRieszParticleSDEDrift
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact sourceRieszForce_eq_gradient s hs
    (sub_ne_zero.mpr (hx i j (Finset.mem_erase.mp hj).1.symm))

/-- The source's actual gradient-potential SDE and its proper time drift are
consequences of the finite-horizon weak SDE plus zero collision occupation.
The latter is derived from the original free-energy estimate by the imported
sourceRiesz_gronwall_particle_collision_time theorem. -/
theorem SourceRieszFiniteHorizonWeakSDE.physical_equation
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (hs : 0<s) (N : ℕ) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (h : SourceRieszFiniteHorizonWeakSDE P F T s β N X B)
    (hc : ∀ᵐ ω ∂P,∀ᵐ r ∂volume.restrict (Ioc 0 (T:ℝ)),
      ∀ i j:Fin N,i≠j → X r ω i≠X r ω j) :
    ∀ᵐ ω ∂P,
      (∀ i:Fin N,IntegrableOn
        (fun r:ℝ=>-((N:ℝ)⁻¹) • ∑ j ∈ Finset.univ.erase i,
          gradient (sourceRieszPotential s) (X r ω i-X r ω j)) (Ioc 0 (T:ℝ))) ∧
      ∀ r:ℝ≥0,r≤T → ∀ i:Fin N,
        X (r:ℝ) ω i=X 0 ω i+
          (∫ u in Ioc 0 (r:ℝ),-((N:ℝ)⁻¹) • ∑ j ∈ Finset.univ.erase i,
            gradient (sourceRieszPotential s) (X u ω i-X u ω j))+
          Real.sqrt (2/β) • (sourceRieszParticleBrownianVector N B i r ω-
            sourceRieszParticleBrownianVector N B i 0 ω) := by
  classical
  filter_upwards [hc,h.drift_integrable,h.equation] with ω hcf hI hE
  have he (i:Fin N) :
      (fun r:ℝ=>sourceRieszParticleSDEDrift s N (X r ω) i)=ᵐ[volume.restrict (Ioc 0 (T:ℝ))]
        (fun r:ℝ=>-((N:ℝ)⁻¹) • ∑ j ∈ Finset.univ.erase i,
          gradient (sourceRieszPotential s) (X r ω i-X r ω j)) := by
    filter_upwards [hcf] with r hr
    exact sourceRieszParticleSDEDrift_eq_physical s hs N (X r ω) hr i
  refine ⟨fun i=>(hI i).congr (he i),?_⟩
  intro r hr i
  have her :
      (fun u:ℝ=>sourceRieszParticleSDEDrift s N (X u ω) i)=ᵐ[volume.restrict (Ioc 0 (r:ℝ))]
        (fun u:ℝ=>-((N:ℝ)⁻¹) • ∑ j ∈ Finset.univ.erase i,
          gradient (sourceRieszPotential s) (X u ω i-X u ω j)) := by
    change ∀ᵐ u ∂volume.restrict (Ioc 0 (r:ℝ)),
      sourceRieszParticleSDEDrift s N (X u ω) i=
        -((N:ℝ)⁻¹) • ∑ j ∈ Finset.univ.erase i,
          gradient (sourceRieszPotential s) (X u ω i-X u ω j)
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mp (he i)] with u hu hur
    exact hu ⟨hur.1,hur.2.trans hr⟩
  rw [←integral_congr_ae her]
  exact hE r hr i

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.sourceRieszParticleSDEDrift_eq_physical
#print axioms DGRHS.Commutator.sourceRieszParticleSDEDrift_eq_physical
#check @DGRHS.Commutator.SourceRieszFiniteHorizonWeakSDE.physical_equation
#print axioms DGRHS.Commutator.SourceRieszFiniteHorizonWeakSDE.physical_equation
