import DGRHS.Commutator.SourceRieszBrownianEventCut
import DGRHS.Commutator.SourceRieszBrownianMaximalAE

/-! Event-weighted interval isometry for actual Brownian increments in the supplied
full filtration. The event is measurable at the left endpoint; no conditional
isometry or bracket identity is an input. The finite proof zeros future
coefficients before applying the independently proved full-filtration isometry. -/
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

private lemma increment_clamp (a b s t : ℝ≥0) (hab : a≤b) (hst : s≤t) (ω : Ω) :
    (B (min t b) ω-B (min t a) ω)-(B (min s b) ω-B (min s a) ω)=
      B (min t (max s b)) ω-B (min t (max s a)) ω := by
  by_cases hbs : b≤s
  · simp only [max_eq_left hbs,max_eq_left (hab.trans hbs),min_eq_right hbs,
      min_eq_right (hab.trans hbs),min_eq_right (hbs.trans hst),min_eq_right (hab.trans (hbs.trans hst)),sub_self]
  · have hsb : s≤b := le_of_not_ge hbs
    rw [max_eq_right hsb,min_eq_left hsb]
    by_cases hsa : s≤a
    · simp only [max_eq_right hsa,min_eq_left hsa,sub_self,sub_zero]
    · have has : a≤s := le_of_not_ge hsa
      simp only [max_eq_left has,min_eq_right has,min_eq_right (has.trans hst),min_eq_right hst]
      ring

private lemma finite_conditional_isometry (c : SourceRieszBrownianAtom F T →₀ ℝ)
    (s t : ℝ≥0) (hst : s≤t) (A : Set Ω) (hA : MeasurableSet[F s] A) :
    ‖sourceRieszL2Indicator P A (F.le s _ hA)
      (sourceRieszBrownianProcessL2 P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c) t-
       sourceRieszBrownianProcessL2 P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c) s)‖^2=
    ‖sourceRieszBrownianEventCut P F T s t A hA (sourceRieszBrownianAtomAssembly P F T c)‖^2 := by
  classical
  let H := fun (D : SourceRieszBrownianAtom F T) ω=>
    if D.a≤t then c D*D.value ω*A.indicator (fun _=>1) ω else 0
  let a := fun D : SourceRieszBrownianAtom F T=>min t (max s D.a)
  let b := fun D : SourceRieszBrownianAtom F T=>min t (max s D.b)
  have hH (D : SourceRieszBrownianAtom F T) : StronglyMeasurable[F (a D)] (H D) := by
    by_cases hd : D.a≤t
    · simp only [H,if_pos hd]
      exact (stronglyMeasurable_const.mul (D.value_measurable.mono
        (F.mono (le_min hd (le_max_right s D.a))))).mul
        (stronglyMeasurable_const.indicator (F.mono (le_min hst (le_max_left s D.a)) _ hA))
    · simp only [H,if_neg hd]
      exact stronglyMeasurable_const
  have hb (D : SourceRieszBrownianAtom F T) (ω : Ω) : ‖H D ω‖≤(‖c D‖₊:ℝ) := by
    by_cases hd : D.a≤t
    · by_cases hω : ω∈A
      · simp only [H,if_pos hd,indicator_of_mem hω,mul_one,norm_mul]
        simpa using mul_le_mul_of_nonneg_left (D.value_bound ω) (norm_nonneg (c D))
      · simp [H,hd,hω]
    · simp [H,hd]
  have hi := sourceRiesz_brownian_finite_isometry P F B hB hBa hind c.support a b
    (fun D _=>min_le_min_left t (max_le_max_left s D.hab)) H
    (fun D _=>hH D) (fun D=>‖c D‖₊) (fun D _=>hb D)
  have hI (ω : Ω) : (∑ D∈c.support,H D ω*(B (b D) ω-B (a D) ω))=
      A.indicator (fun ω=>sourceRieszBrownianElementaryProcess F T B c t ω-
        sourceRieszBrownianElementaryProcess F T B c s ω) ω := by
    by_cases hω : ω∈A
    · rw [indicator_of_mem hω,sourceRieszBrownianElementaryProcess_apply,
        sourceRieszBrownianElementaryProcess_apply,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro D _
      by_cases hd : D.a≤t
      · simp only [H,if_pos hd,indicator_of_mem hω,mul_one,a,b]
        rw [←mul_sub,increment_clamp B D.a D.b s t D.hab hst ω]
      · have hta : t≤D.a := le_of_not_ge hd
        simp only [H,if_neg hd,zero_mul,min_eq_left hta,min_eq_left (hta.trans D.hab),
          min_eq_left (hst.trans hta),min_eq_left (hst.trans (hta.trans D.hab)),sub_self,mul_zero]
    · rw [indicator_of_notMem hω]
      apply Finset.sum_eq_zero
      intro D _
      simp [H,hω]
  have hV (p : ℝ≥0×Ω) : (∑ D∈c.support,sourceRieszBrownianBand (a D) (b D) (H D) p)=
      (Ioc s t ×ˢ A).indicator (sourceRieszBrownianAtomRawAssembly F T c) p := by
    by_cases hpA : p.2∈A
    · by_cases ht : p.1∈Ioc s t
      · rw [indicator_of_mem (show p∈Ioc s t ×ˢ A from ⟨ht,hpA⟩),sourceRieszBrownianAtomRawAssembly_apply]
        apply Finset.sum_congr rfl
        intro D _
        by_cases hp : p.1∈Ioc D.a D.b
        · have hd : D.a≤t := hp.1.le.trans ht.2
          simp [sourceRieszBrownianBand,a,b,sourceRieszBrownianBand_interval_inter D.a D.b s t D.hab hst,
            H,hd,hpA,hp,ht,SourceRieszBrownianAtom.integrand]
        · simp [sourceRieszBrownianBand,a,b,sourceRieszBrownianBand_interval_inter D.a D.b s t D.hab hst,
            hp,ht,SourceRieszBrownianAtom.integrand]
      · rw [indicator_of_notMem (show p∉Ioc s t ×ˢ A from fun h=>ht h.1)]
        apply Finset.sum_eq_zero
        intro D _
        simp [sourceRieszBrownianBand,a,b,sourceRieszBrownianBand_interval_inter D.a D.b s t D.hab hst,ht]
    · rw [indicator_of_notMem (show p∉Ioc s t ×ˢ A from fun h=>hpA h.2)]
      apply Finset.sum_eq_zero
      intro D _
      simp [sourceRieszBrownianBand,H,hpA]
  rw [sourceRiesz_L2_norm_sq,sourceRieszBrownianEventCut_raw_norm P F T s t A hA c]
  have he : (fun ω=>(sourceRieszL2Indicator P A (F.le s _ hA)
      (sourceRieszBrownianProcessL2 P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c) t-
       sourceRieszBrownianProcessL2 P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c) s) ω)^2)=ᵐ[P]
      fun ω=>(∑ D∈c.support,H D ω*(B (b D) ω-B (a D) ω))^2 := by
    filter_upwards [sourceRieszL2Indicator_coe P A (F.le s _ hA) _,Lp.coeFn_sub
      (sourceRieszBrownianProcessL2 P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c) t)
      (sourceRieszBrownianProcessL2 P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c) s),
      sourceRieszBrownianElementaryProcess_ae_no_continuity P F T B hB hBa hind c t,
      sourceRieszBrownianElementaryProcess_ae_no_continuity P F T B hB hBa hind c s] with ω h1 h2 h3 h4
    rw [h1,hI]
    by_cases hω : ω∈A
    · rw [indicator_of_mem hω,indicator_of_mem hω]
      exact congrArg (fun z:ℝ=>z^2) (h2.trans (congrArg₂ (fun x y:ℝ=>x-y) h3 h4))
    · rw [indicator_of_notMem hω,indicator_of_notMem hω]
  rw [integral_congr_ae he]
  convert hi.2.2.2 using 1
  congr 1
  funext p
  exact congrArg (fun z:ℝ=>z^2) (hV p).symm

theorem sourceRieszBrownianProcessL2_conditional_isometry_no_continuity
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (s t : ℝ≥0) (hst : s≤t) (A : Set Ω) (hA : MeasurableSet[F s] A) :
    ‖sourceRieszL2Indicator P A (F.le s _ hA)
      (sourceRieszBrownianProcessL2 P F T B hB hBa hind g t-
       sourceRieszBrownianProcessL2 P F T B hB hBa hind g s)‖^2=
    ∫ p in Ioc s t ×ˢ A,(g p)^2 ∂sourceRieszBrownianPredictableMeasure P F T := by
  rw [←@sourceRieszL2Indicator_norm_sq (ℝ≥0×Ω) F.predictable (sourceRieszBrownianPredictableMeasure P F T)
    (Ioc s t ×ˢ A) (measurableSet_predictable_Ioc_prod s t hA) g]
  apply congrFun (DenseRange.equalizer (sourceRieszBrownianAtomAssembly_dense P F T)
    (((sourceRieszL2Indicator P A (F.le s _ hA)).continuous.comp
      ((sourceRieszBrownianProcessL2_continuous P F T B hB hBa hind t).sub
        (sourceRieszBrownianProcessL2_continuous P F T B hB hBa hind s))).norm.pow 2)
    ((sourceRieszBrownianEventCut P F T s t A hA).continuous.norm.pow 2) (funext fun c=>?_)) g
  exact finite_conditional_isometry P F T B hB hBa hind c s t hst A hA

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianProcessL2_conditional_isometry_no_continuity
#print axioms DGRHS.Commutator.sourceRieszBrownianProcessL2_conditional_isometry_no_continuity
