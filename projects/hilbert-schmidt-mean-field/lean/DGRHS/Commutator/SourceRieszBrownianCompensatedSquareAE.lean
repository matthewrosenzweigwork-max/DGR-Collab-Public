import DGRHS.Commutator.SourceRieszBrownianCompensatedSquare
import DGRHS.Commutator.SourceRieszBrownianConditionalEnergyAE

/-! The actual completed Brownian integral squared minus its actual time-energy
is a native martingale in the supplied full filtration. The conditional energy
identity is derived from elementary Brownian increments and density upstream;
no compensator or conditional isometry is an input. This scalar statement does
not assert the cross-driver bracket or the particle SDE realization. -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)

variable (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
variable (hind : ∀ s t,s≤t →
  Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)
variable (hBc : ∀ᵐ ω ∂P,Continuous (fun r=>B r ω))

include hB hBa hind hBc in
theorem sourceRieszBrownianContinuousProcess_compensated_square_of_ae_continuous
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    Martingale (fun t ω=>(sourceRieszBrownianContinuousProcess P F T B g t ω)^2-
      sourceRieszBrownianEnergy P F T g t ω) F P := by
  let M := sourceRieszBrownianContinuousProcess P F T B g
  let Q := sourceRieszBrownianEnergy P F T g
  have hM := sourceRieszBrownianContinuousProcess_martingale_of_ae_continuous P F T B hB hBa hind hBc g
  have hQ := sourceRieszBrownianEnergy_adapted P F T g
  have hiM t : Integrable (fun ω=>(M t ω)^2) P := (hM.2.1 t).integrable_sq
  have hiQ t : Integrable (Q t) P := sourceRieszBrownianEnergy_integrable P F T g t
  have ha : StronglyAdapted F (fun t ω=>(M t ω)^2-Q t ω) :=
    fun t=>(hM.1.stronglyAdapted t).pow 2 |>.sub (hQ t)
  refine ⟨ha,?_⟩
  intro s t hst
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (F.le s) ((hiM t).sub (hiQ t))
    (fun A hA hfinite=>((hiM s).sub (hiQ s)).integrableOn) ?_ (ha s).aestronglyMeasurable
  intro A hA hfinite
  have hm := sourceRieszBrownianContinuousProcess_square_energy_of_ae_continuous P F T B hB hBa hind hBc g s t hst A hA
  rw [sourceRieszBrownianEnergy_interval_trim P F T g s t A hA] at hm
  have hq := sourceRieszBrownianEnergy_interval_setIntegral P F T g s t hst A (F.le s _ hA)
  change (∫ ω in A,(M t ω)^2-(M s ω)^2 ∂P)=_ at hm
  change (∫ ω in A,Q t ω-Q s ω ∂P)=_ at hq
  rw [integral_sub (hiM t).integrableOn (hiM s).integrableOn] at hm
  rw [integral_sub (hiQ t).integrableOn (hiQ s).integrableOn] at hq
  rw [integral_sub (hiM s).integrableOn (hiQ s).integrableOn,
    integral_sub (hiM t).integrableOn (hiQ t).integrableOn]
  linarith

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_compensated_square_of_ae_continuous
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_compensated_square_of_ae_continuous
