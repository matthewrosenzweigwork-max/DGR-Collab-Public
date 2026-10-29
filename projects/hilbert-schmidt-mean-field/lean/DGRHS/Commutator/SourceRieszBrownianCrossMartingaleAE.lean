import DGRHS.Commutator.SourceRieszBrownianCrossMartingale
import DGRHS.Commutator.SourceRieszBrownianCrossIsometryAE
import DGRHS.Commutator.SourceRieszBrownianConditionalEnergyAE

/-! Products of completed integrals against distinct Brownian drivers are
native martingales. Conditional cross increments vanish by the proved finite
pairing and density argument. Past-increment terms vanish by each actual
integral's native martingale property. Shared random coefficients are allowed. -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal RealInnerProductSpace
namespace DGRHS.Commutator

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
variable (B C : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C P)
variable (hBa : StronglyAdapted F B) (hCa : StronglyAdapted F C)
variable (hindB : ∀ s t,s≤t →
  Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)
variable (hindC : ∀ s t,s≤t →
  Indep (MeasurableSpace.comap (fun ω=>C t ω-C s ω) (borel ℝ)) (F s) P)
variable (hd : IndepFun (fun ω=>fun r=>B r ω) (fun ω=>fun r=>C r ω) P)
variable (hp : ∀ s t u,s≤t → s≤u →
  Indep (MeasurableSpace.comap (fun ω=>(B t ω-B s ω,C u ω-C s ω)) inferInstance) (F s) P)
variable (hBc : ∀ᵐ ω ∂P,Continuous (fun r=>B r ω)) (hCc : ∀ᵐ ω ∂P,Continuous (fun r=>C r ω))

include hB hC hBa hCa hindB hindC hd hp hBc hCc in
theorem sourceRieszBrownianContinuousProcess_cross_increment_zero_of_ae_continuous
    (g h : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (s t : ℝ≥0) (hst : s≤t) (A : Set Ω) (hA : MeasurableSet[F s] A) :
    (∫ ω in A,(sourceRieszBrownianContinuousProcess P F T B g t ω-
        sourceRieszBrownianContinuousProcess P F T B g s ω)*
      (sourceRieszBrownianContinuousProcess P F T C h t ω-
        sourceRieszBrownianContinuousProcess P F T C h s ω) ∂P)=0 := by
  have ho := sourceRieszBrownianProcessL2_cross_conditional_no_continuity P F T B C hB hC hBa hCa hindB hindC hd hp
    g h s t hst A hA
  rw [sourceRieszL2Indicator_inner] at ho
  rw [←ho]
  apply setIntegral_congr_ae (F.le s _ hA)
  filter_upwards [sourceRieszBrownianContinuousProcess_modification_of_ae_continuous P F T B hB hBa hindB hBc g t,
    sourceRieszBrownianContinuousProcess_modification_of_ae_continuous P F T B hB hBa hindB hBc g s,
    Lp.coeFn_sub (sourceRieszBrownianProcessL2 P F T B hB hBa hindB g t)
      (sourceRieszBrownianProcessL2 P F T B hB hBa hindB g s),
    sourceRieszBrownianContinuousProcess_modification_of_ae_continuous P F T C hC hCa hindC hCc h t,
    sourceRieszBrownianContinuousProcess_modification_of_ae_continuous P F T C hC hCa hindC hCc h s,
    Lp.coeFn_sub (sourceRieszBrownianProcessL2 P F T C hC hCa hindC h t)
      (sourceRieszBrownianProcessL2 P F T C hC hCa hindC h s)] with ω hBt hBs hBd hCt hCs hCd _
  exact congrArg₂ (fun x y:ℝ=>x*y)
    ((congrArg₂ (fun x y:ℝ=>x-y) hBt hBs).trans hBd.symm)
    ((congrArg₂ (fun x y:ℝ=>x-y) hCt hCs).trans hCd.symm)

include hB hC hBa hCa hindB hindC hd hp hBc hCc in
theorem sourceRieszBrownianContinuousProcess_cross_martingale_of_ae_continuous
    (g h : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    Martingale (fun t ω=>sourceRieszBrownianContinuousProcess P F T B g t ω*
      sourceRieszBrownianContinuousProcess P F T C h t ω) F P := by
  let M := sourceRieszBrownianContinuousProcess P F T B g
  let N := sourceRieszBrownianContinuousProcess P F T C h
  have hM := sourceRieszBrownianContinuousProcess_martingale_of_ae_continuous P F T B hB hBa hindB hBc g
  have hN := sourceRieszBrownianContinuousProcess_martingale_of_ae_continuous P F T C hC hCa hindC hCc h
  have ha : StronglyAdapted F (fun t ω=>M t ω*N t ω) := fun t=>(hM.1.stronglyAdapted t).mul (hN.1.stronglyAdapted t)
  have hi t : Integrable (fun ω=>M t ω*N t ω) P := (hM.2.1 t).integrable_mul (hN.2.1 t)
  refine ⟨ha,?_⟩
  intro s t hst
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hi t)
    (fun A hA hfinite=>(hi s).integrableOn) ?_ (ha s).aestronglyMeasurable
  intro A hA hfinite
  have hAm := F.le s _ hA
  have hz1 := (sourceRieszBrownianContinuousProcess_past_increment_zero_of_ae_continuous P F T C hC hCa hindC hCc
    h s t hst (A.indicator (M s)) ((hM.1.stronglyAdapted s).indicator hA) ((hM.2.1 s).indicator hAm)).2
  have hz2 := (sourceRieszBrownianContinuousProcess_past_increment_zero_of_ae_continuous P F T B hB hBa hindB hBc
    g s t hst (A.indicator (N s)) ((hN.1.stronglyAdapted s).indicator hA) ((hN.2.1 s).indicator hAm)).2
  have hc1 : (∫ ω in A,M s ω*(N t ω-N s ω) ∂P)=0 := by
    rw [←integral_indicator hAm]
    convert hz1 using 1
    congr 1
    funext ω
    by_cases hω : ω∈A <;> simp [hω,N]
  have hc2 : (∫ ω in A,N s ω*(M t ω-M s ω) ∂P)=0 := by
    rw [←integral_indicator hAm]
    convert hz2 using 1
    congr 1
    funext ω
    by_cases hω : ω∈A <;> simp [hω,M]
  have hcross := sourceRieszBrownianContinuousProcess_cross_increment_zero_of_ae_continuous P F T B C hB hC hBa hCa
    hindB hindC hd hp hBc hCc g h s t hst A hA
  have hdi : Integrable (fun ω=>(M t ω-M s ω)*(N t ω-N s ω)) P :=
    ((hM.2.1 t).sub (hM.2.1 s)).integrable_mul ((hN.2.1 t).sub (hN.2.1 s))
  have hci1 : Integrable (fun ω=>M s ω*(N t ω-N s ω)) P :=
    (hM.2.1 s).integrable_mul ((hN.2.1 t).sub (hN.2.1 s))
  have hci2 : Integrable (fun ω=>N s ω*(M t ω-M s ω)) P :=
    (hN.2.1 s).integrable_mul ((hM.2.1 t).sub (hM.2.1 s))
  have he : (fun ω=>M t ω*N t ω-M s ω*N s ω)=
      fun ω=>(M t ω-M s ω)*(N t ω-N s ω)+M s ω*(N t ω-N s ω)+N s ω*(M t ω-M s ω) := by
    funext ω
    ring
  have hsi : Integrable (fun ω=>(M t ω-M s ω)*(N t ω-N s ω)+
      M s ω*(N t ω-N s ω)) P := by
    exact (integrable_add_iff_integrable_left' hci1).mpr hdi
  have hz : (∫ ω in A,M t ω*N t ω-M s ω*N s ω ∂P)=0 := by
    rw [he,integral_add hsi.integrableOn hci2.integrableOn,
      integral_add hdi.integrableOn hci1.integrableOn,hc1,hc2]
    simpa only [add_zero] using hcross
  rw [integral_sub (hi t).integrableOn (hi s).integrableOn] at hz
  linarith

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_cross_increment_zero_of_ae_continuous
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_cross_increment_zero_of_ae_continuous
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_cross_martingale_of_ae_continuous
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_cross_martingale_of_ae_continuous
