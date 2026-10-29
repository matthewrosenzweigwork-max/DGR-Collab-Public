import DGRHS.Commutator.SourceLogPrimitiveForceBridge
import DGRHS.Commutator.SourceRieszFiniteHorizonSDE
import DGRHS.CLT.SourceLogSingularIdentification

/-! Literal source logarithmic gradient SDE and initial Gibbs data.
Zero collision occupation identifies its actual proper drift integral with
force-zero technical Brownian data. No Riesz Gibbs/potential at zero is used.
New source body awaits actual restricted compiler feedback and exact review. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
open DGRHS.CLT
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

structure SourceLogFiniteHorizonWeakSDE
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (N : ℕ) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) : Prop where
  brownian : SourceRieszFilteredBrownianFamily P F B
  measurable_on_horizon : Measurable (fun p:Icc (0:ℝ) (T:ℝ)×Ω=>X p.1 p.2)
  adapted_on_horizon : ∀ i,∀ r:ℝ≥0,r≤T → StronglyMeasurable[F r] (fun ω=>X (r:ℝ) ω i)
  continuous_on_horizon : ∀ i,∀ᵐ ω ∂P,ContinuousOn (fun r:ℝ≥0=>X (r:ℝ) ω i) (Icc 0 T)
  drift_integrable : ∀ᵐ ω ∂P,∀ i,
    IntegrableOn (fun r:ℝ=>-((N:ℝ)⁻¹) • ∑ j ∈ Finset.univ.erase i,
      gradient sourceLogPotential (X r ω i-X r ω j)) (Ioc 0 (T:ℝ))
  equation : ∀ᵐ ω ∂P,∀ r:ℝ≥0,r≤T → ∀ i,
    X (r:ℝ) ω i=X 0 ω i+
      (∫ u in Ioc 0 (r:ℝ),-((N:ℝ)⁻¹) • ∑ j ∈ Finset.univ.erase i,
        gradient sourceLogPotential (X u ω i-X u ω j))+
      Real.sqrt (2/β) • (sourceRieszParticleBrownianVector N B i r ω-
        sourceRieszParticleBrownianVector N B i 0 ω)

structure SourceLogInitialGibbsBrownianData
    (P : Measure Ω) (β : ℝ≥0) (ρ : E→ℝ) (N : ℕ)
    (X₀ : Ω→Fin N→E) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) : Prop where
  initial_gibbs : P.map X₀=sourceLogSingularGibbs β ρ N
  initial_independent_drivers : IndepFun X₀ (fun ω=>fun b r=>B b r ω) P

lemma SourceLogFiniteHorizonWeakSDE.to_zero
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (N : ℕ) (X : ℝ→Ω→Fin N→E) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (h : SourceLogFiniteHorizonWeakSDE P F T β N X B)
    (hc : ∀ᵐ ω ∂P,∀ᵐ r ∂volume.restrict (Ioc 0 (T:ℝ)),
      ∀ i j:Fin N,i≠j → X r ω i≠X r ω j) :
    SourceRieszFiniteHorizonWeakSDE P F T 0 β N X B := by
  refine ⟨h.brownian,h.measurable_on_horizon,h.adapted_on_horizon,h.continuous_on_horizon,?_,?_⟩
  · filter_upwards [h.drift_integrable,hc] with ω hi he
    intro i
    apply (hi i).congr
    filter_upwards [he] with r hr
    exact (sourceLogParticleSDEDrift_eq_physical N (X r ω) hr i).symm
  · filter_upwards [h.equation,hc] with ω he hcω
    intro r hr i
    have hid : (∫ u in Ioc 0 (r:ℝ),sourceRieszParticleSDEDrift 0 N (X u ω) i)=
        ∫ u in Ioc 0 (r:ℝ),-((N:ℝ)⁻¹) • ∑ j ∈ Finset.univ.erase i,
          gradient sourceLogPotential (X u ω i-X u ω j) := by
      apply integral_congr_ae
      have hsub : volume.restrict (Ioc 0 (r:ℝ))≤volume.restrict (Ioc 0 (T:ℝ)) :=
        Measure.restrict_mono (Ioc_subset_Ioc_right (show (r:ℝ)≤(T:ℝ) from hr)) le_rfl
      filter_upwards [ae_mono hsub hcω] with u hu
      exact sourceLogParticleSDEDrift_eq_physical N (X u ω) hu i
    rw [hid]
    exact he r hr i

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.SourceLogFiniteHorizonWeakSDE
#print axioms DGRHS.Commutator.SourceLogFiniteHorizonWeakSDE
#check @DGRHS.Commutator.SourceLogInitialGibbsBrownianData
#print axioms DGRHS.Commutator.SourceLogInitialGibbsBrownianData
#check @DGRHS.Commutator.SourceLogFiniteHorizonWeakSDE.to_zero
#print axioms DGRHS.Commutator.SourceLogFiniteHorizonWeakSDE.to_zero
