import DGRHS.Commutator.SourceRieszBrownianEventExpansionAE

/-! Event-conditioned cross orthogonality of the actual completed Brownian
integrals. Finite adapted rectangles give zero cross pairing; two independent
density passages extend that identity to arbitrary predictable L2 integrands.
No independence of the completed stochastic integrals is asserted. -/
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

include hd hp in
private lemma finite_cross_isometry (c d : SourceRieszBrownianAtom F T →₀ ℝ)
    (s t : ℝ≥0) (hst : s≤t) (A : Set Ω) (hA : MeasurableSet[F s] A) :
    ⟪sourceRieszL2Indicator P A (F.le s _ hA)
      (sourceRieszBrownianProcessL2 P F T B hB hBa hindB (sourceRieszBrownianAtomAssembly P F T c) t-
       sourceRieszBrownianProcessL2 P F T B hB hBa hindB (sourceRieszBrownianAtomAssembly P F T c) s),
     sourceRieszL2Indicator P A (F.le s _ hA)
      (sourceRieszBrownianProcessL2 P F T C hC hCa hindC (sourceRieszBrownianAtomAssembly P F T d) t-
       sourceRieszBrownianProcessL2 P F T C hC hCa hindC (sourceRieszBrownianAtomAssembly P F T d) s)⟫=0 := by
  obtain ⟨a,b,H,hab,hH,hbH,heH⟩ := sourceRieszBrownianProcessL2_eventcut_expansion_no_continuity P F T B hB hBa hindB c s t hst A hA
  obtain ⟨u,v,J,huv,hJ,hbJ,heJ⟩ := sourceRieszBrownianProcessL2_eventcut_expansion_no_continuity P F T C hC hCa hindC d s t hst A hA
  have hcros i j := sourceRiesz_brownian_cross_rectangle P F B C hB hC hBa hCa hindB hindC hd hp
    (a i) (b i) (u j) (v j) (hab i) (huv j) (H i) (J j) (hH i) (hJ j)
    ‖c i‖₊ ‖d j‖₊ (ae_of_all _ (hbH i)) (ae_of_all _ (hbJ j))
  rw [L2.inner_def]
  calc
    _ = ∫ ω,(∑ i∈c.support,H i ω*(B (b i) ω-B (a i) ω))*
        (∑ j∈d.support,J j ω*(C (v j) ω-C (u j) ω)) ∂P := by
      apply integral_congr_ae
      filter_upwards [heH,heJ] with ω h1 h2
      rw [h1,h2]
      change (∑ j∈d.support,J j ω*(C (v j) ω-C (u j) ω))*
        (∑ i∈c.support,H i ω*(B (b i) ω-B (a i) ω))=_
      exact mul_comm _ _
    _ = 0 := by
      simp_rw [Finset.sum_mul_sum]
      rw [integral_finsetSum _ (fun i hi=>integrable_finsetSum _ fun j hj=>(hcros i j).1)]
      apply Finset.sum_eq_zero
      intro i hi
      rw [integral_finsetSum _ (fun j hj=>(hcros i j).1)]
      exact Finset.sum_eq_zero fun j hj=>(hcros i j).2

include hd hp in
theorem sourceRieszBrownianProcessL2_cross_conditional_no_continuity
    (g h : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (s t : ℝ≥0) (hst : s≤t) (A : Set Ω) (hA : MeasurableSet[F s] A) :
    ⟪sourceRieszL2Indicator P A (F.le s _ hA)
      (sourceRieszBrownianProcessL2 P F T B hB hBa hindB g t-
       sourceRieszBrownianProcessL2 P F T B hB hBa hindB g s),
     sourceRieszL2Indicator P A (F.le s _ hA)
      (sourceRieszBrownianProcessL2 P F T C hC hCa hindC h t-
       sourceRieszBrownianProcessL2 P F T C hC hCa hindC h s)⟫=0 := by
  let U := fun g=>sourceRieszL2Indicator P A (F.le s _ hA)
    (sourceRieszBrownianProcessL2 P F T B hB hBa hindB g t-sourceRieszBrownianProcessL2 P F T B hB hBa hindB g s)
  let V := fun g=>sourceRieszL2Indicator P A (F.le s _ hA)
    (sourceRieszBrownianProcessL2 P F T C hC hCa hindC g t-sourceRieszBrownianProcessL2 P F T C hC hCa hindC g s)
  have hU : Continuous U := (sourceRieszL2Indicator P A (F.le s _ hA)).continuous.comp
    ((sourceRieszBrownianProcessL2_continuous P F T B hB hBa hindB t).sub
      (sourceRieszBrownianProcessL2_continuous P F T B hB hBa hindB s))
  have hV : Continuous V := (sourceRieszL2Indicator P A (F.le s _ hA)).continuous.comp
    ((sourceRieszBrownianProcessL2_continuous P F T C hC hCa hindC t).sub
      (sourceRieszBrownianProcessL2_continuous P F T C hC hCa hindC s))
  have hdense := sourceRieszBrownianAtomAssembly_dense P F T
  have hfin c d : ⟪U (sourceRieszBrownianAtomAssembly P F T c),V (sourceRieszBrownianAtomAssembly P F T d)⟫=0 :=
    finite_cross_isometry P F T B C hB hC hBa hCa hindB hindC hd hp c d s t hst A hA
  have hleft c : ∀ h,⟪U (sourceRieszBrownianAtomAssembly P F T c),V h⟫=0 := by
    intro h
    exact congrFun (DenseRange.equalizer hdense (continuous_const.inner hV) continuous_const (funext (hfin c))) h
  exact congrFun (DenseRange.equalizer hdense (hU.inner continuous_const) continuous_const (funext fun c=>hleft c h)) g

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianProcessL2_cross_conditional_no_continuity
#print axioms DGRHS.Commutator.sourceRieszBrownianProcessL2_cross_conditional_no_continuity
