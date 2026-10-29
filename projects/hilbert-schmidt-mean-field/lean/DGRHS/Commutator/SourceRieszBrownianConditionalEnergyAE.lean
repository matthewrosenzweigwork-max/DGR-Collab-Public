import DGRHS.Commutator.SourceRieszBrownianConditionalIsometryAE
import DGRHS.Commutator.SourceRieszBrownianContinuousMartingaleAE

/-! Actual conditional energy identities for the constructed continuous Brownian
integral. Testing on every event in the left-endpoint sigma-algebra is derived
from the finite common-driver isometry and native martingale projection.
This is not yet a multidriver bracket construction. -/
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
theorem sourceRieszBrownianContinuousProcess_increment_energy_of_ae_continuous
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (s t : ℝ≥0) (hst : s≤t) (A : Set Ω) (hA : MeasurableSet[F s] A) :
    (∫ ω in A,(sourceRieszBrownianContinuousProcess P F T B g t ω-
      sourceRieszBrownianContinuousProcess P F T B g s ω)^2 ∂P)=
      ∫ p in Ioc s t ×ˢ A,(g p)^2 ∂sourceRieszBrownianPredictableMeasure P F T := by
  rw [←sourceRieszBrownianProcessL2_conditional_isometry_no_continuity P F T B hB hBa hind g s t hst A hA,
    sourceRieszL2Indicator_norm_sq]
  apply setIntegral_congr_ae (F.le s _ hA)
  filter_upwards [sourceRieszBrownianContinuousProcess_modification_of_ae_continuous P F T B hB hBa hind hBc g t,
    sourceRieszBrownianContinuousProcess_modification_of_ae_continuous P F T B hB hBa hind hBc g s,
    Lp.coeFn_sub (sourceRieszBrownianProcessL2 P F T B hB hBa hind g t)
      (sourceRieszBrownianProcessL2 P F T B hB hBa hind g s)] with ω ht hs hd _
  exact congrArg (fun z:ℝ=>z^2) ((congrArg₂ (fun x y:ℝ=>x-y) ht hs).trans hd.symm)

include hB hBa hind hBc in
theorem sourceRieszBrownianContinuousProcess_past_increment_zero_of_ae_continuous
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (s t : ℝ≥0) (hst : s≤t) (Z : Ω→ℝ)
    (hZ : StronglyMeasurable[F s] Z) (hZL : MemLp Z 2 P) :
    Integrable (fun ω=>Z ω*(sourceRieszBrownianContinuousProcess P F T B g t ω-
      sourceRieszBrownianContinuousProcess P F T B g s ω)) P ∧
    (∫ ω,Z ω*(sourceRieszBrownianContinuousProcess P F T B g t ω-
      sourceRieszBrownianContinuousProcess P F T B g s ω) ∂P)=0 := by
  let M := sourceRieszBrownianContinuousProcess P F T B g
  have hm := sourceRieszBrownianContinuousProcess_martingale_of_ae_continuous P F T B hB hBa hind hBc g
  have hd : MemLp (fun ω=>M t ω-M s ω) 2 P := (hm.2.1 t).sub (hm.2.1 s)
  have hi := hZL.integrable_mul hd
  have he : P[fun ω=>M t ω-M s ω | F s]=ᵐ[P] (fun _=>0) := by
    have hsub := condExp_sub ((hm.2.1 t).integrable one_le_two) ((hm.2.1 s).integrable one_le_two) (F s)
    change P[fun ω=>M t ω-M s ω | F s]=ᵐ[P]
      (fun ω=>(P[M t | F s]) ω-(P[M s | F s]) ω) at hsub
    rw [condExp_of_stronglyMeasurable (F.le s) (hm.1.stronglyAdapted s)
      ((hm.2.1 s).integrable one_le_two)] at hsub
    filter_upwards [hsub,hm.1.condExp_ae_eq hst] with ω hω hproj
    change (P[M t | F s]) ω=M s ω at hproj
    change (P[fun ω=>M t ω-M s ω | F s]) ω=(P[M t | F s]) ω-M s ω at hω
    simpa only [hproj,sub_self] using hω
  have hp := condExp_mul_of_stronglyMeasurable_left hZ hi (hd.integrable one_le_two)
  change P[fun ω=>Z ω*(M t ω-M s ω) | F s]=ᵐ[P]
    (fun ω=>Z ω*(P[fun ω=>M t ω-M s ω | F s]) ω) at hp
  have hz : P[fun ω=>Z ω*(M t ω-M s ω) | F s]=ᵐ[P] (fun _=>0) := by
    filter_upwards [hp,he] with ω hω h0
    simpa only [Pi.mul_apply,h0,mul_zero] using hω
  refine ⟨hi,?_⟩
  rw [←integral_condExp (F.le s),integral_congr_ae hz,integral_zero]

include hB hBa hind hBc in
theorem sourceRieszBrownianContinuousProcess_square_energy_of_ae_continuous
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (s t : ℝ≥0) (hst : s≤t) (A : Set Ω) (hA : MeasurableSet[F s] A) :
    (∫ ω in A, (sourceRieszBrownianContinuousProcess P F T B g t ω)^2-
      (sourceRieszBrownianContinuousProcess P F T B g s ω)^2 ∂P)=
      ∫ p in Ioc s t ×ˢ A,(g p)^2 ∂sourceRieszBrownianPredictableMeasure P F T := by
  let M := sourceRieszBrownianContinuousProcess P F T B g
  have hm := sourceRieszBrownianContinuousProcess_martingale_of_ae_continuous P F T B hB hBa hind hBc g
  have hAm : MeasurableSet A := F.le s _ hA
  have hZ := (hm.1.stronglyAdapted s).indicator hA
  have hZL := (hm.2.1 s).indicator hAm
  have hz := (sourceRieszBrownianContinuousProcess_past_increment_zero_of_ae_continuous P F T B hB hBa hind hBc
    g s t hst (A.indicator (M s)) hZ hZL).2
  have hcross : (∫ ω in A,M s ω*(M t ω-M s ω) ∂P)=0 := by
    rw [←integral_indicator hAm]
    convert hz using 1
    congr 1
    funext ω
    by_cases hω : ω∈A <;> simp [hω,M]
  have hdi : Integrable (fun ω=>(M t ω-M s ω)^2) P := ((hm.2.1 t).sub (hm.2.1 s)).integrable_sq
  have hci : Integrable (fun ω=>M s ω*(M t ω-M s ω)) P :=
    (hm.2.1 s).integrable_mul ((hm.2.1 t).sub (hm.2.1 s))
  have he : (fun ω=>(M t ω)^2-(M s ω)^2)=
      fun ω=>(M t ω-M s ω)^2+2*(M s ω*(M t ω-M s ω)) := by funext ω;ring
  change (∫ ω in A,(M t ω)^2-(M s ω)^2 ∂P)=_
  rw [he,integral_add hdi.integrableOn (hci.const_mul 2).integrableOn,integral_const_mul,hcross,mul_zero,add_zero]
  exact sourceRieszBrownianContinuousProcess_increment_energy_of_ae_continuous P F T B hB hBa hind hBc g s t hst A hA

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_increment_energy_of_ae_continuous
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_increment_energy_of_ae_continuous
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_past_increment_zero_of_ae_continuous
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_past_increment_zero_of_ae_continuous
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_square_energy_of_ae_continuous
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_square_energy_of_ae_continuous
