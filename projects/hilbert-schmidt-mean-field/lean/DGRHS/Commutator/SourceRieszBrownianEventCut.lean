import DGRHS.Commutator.SourceRieszBrownianContinuousMartingale

/-! Event-and-time cuts for the actual predictable L2 domain. The indicator
continuous-linear-map construction extends the licensed truncation adaptation
in SourceRieszBrownianTruncation. No conditional isometry or bracket is assumed. -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace DGRHS.Commutator
section Indicator
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (S : Set α) (hS : MeasurableSet S)

def sourceRieszL2Indicator :
    Lp ℝ 2 (μ) →L[ℝ]
      Lp ℝ 2 (μ) :=
  LinearMap.mkContinuous
    { toFun := fun g=>((Lp.memLp g).indicator hS).toLp
        (S.indicator (g : α→ℝ))
      map_add' := fun g k=>by
        apply Lp.ext
        filter_upwards [((Lp.memLp (g+k)).indicator hS).coeFn_toLp,
          Lp.coeFn_add (((Lp.memLp g).indicator hS).toLp _)
            (((Lp.memLp k).indicator hS).toLp _),
          ((Lp.memLp g).indicator hS).coeFn_toLp,
          ((Lp.memLp k).indicator hS).coeFn_toLp,Lp.coeFn_add g k]
          with p h1 h2 h3 h4 h5
        rw [h1,h2,Pi.add_apply,h3,h4]
        by_cases hp : p∈S
        · simp only [indicator_of_mem hp,h5,Pi.add_apply]
        · simp only [indicator_of_notMem hp,zero_add]
      map_smul' := fun c g=>by
        apply Lp.ext
        filter_upwards [((Lp.memLp (c • g)).indicator hS).coeFn_toLp,
          Lp.coeFn_smul c (((Lp.memLp g).indicator hS).toLp _),
          ((Lp.memLp g).indicator hS).coeFn_toLp,Lp.coeFn_smul c g]
          with p h1 h2 h3 h4
        rw [h1,RingHom.id_apply,h2,Pi.smul_apply,h3]
        by_cases hp : p∈S
        · simp only [indicator_of_mem hp,h4,Pi.smul_apply,smul_eq_mul]
        · simp only [indicator_of_notMem hp,smul_zero] }
    1 (fun g=>by
      simp only [LinearMap.coe_mk,AddHom.coe_mk]
      rw [one_mul,Lp.norm_toLp,Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_lt_top g).ne (eLpNorm_indicator_le _ hS))

lemma sourceRieszL2Indicator_coe
    (g : Lp ℝ 2 (μ)) :
    (sourceRieszL2Indicator μ S hS g : α→ℝ)
      =ᵐ[μ] S.indicator (g : α→ℝ) :=
  ((Lp.memLp g).indicator hS).coeFn_toLp

lemma sourceRieszL2Indicator_norm_sq
    (g : Lp ℝ 2 (μ)) :
    ‖sourceRieszL2Indicator μ S hS g‖^2=
      ∫ p in S,(g p)^2 ∂μ := by
  rw [sourceRiesz_L2_norm_sq,←integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [sourceRieszL2Indicator_coe μ S hS g] with p hp
  rw [hp]
  by_cases h : p∈S <;> simp [h]

end Indicator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T s t : ℝ≥0)
variable (A : Set Ω) (hA : MeasurableSet[F s] A)

def sourceRieszBrownianEventCut := @sourceRieszL2Indicator (ℝ≥0×Ω) F.predictable
  (sourceRieszBrownianPredictableMeasure P F T) (Ioc s t ×ˢ A)
  (measurableSet_predictable_Ioc_prod s t hA)

lemma sourceRieszBrownianEventCut_raw_norm (c : SourceRieszBrownianAtom F T →₀ ℝ) :
    ‖sourceRieszBrownianEventCut P F T s t A hA (sourceRieszBrownianAtomAssembly P F T c)‖^2=
      ∫ p,((Ioc s t ×ˢ A).indicator (sourceRieszBrownianAtomRawAssembly F T c) p)^2
        ∂sourceRieszBrownianTime.prod P := by
  let u := (Ioc s t ×ˢ A).indicator (sourceRieszBrownianAtomRawAssembly F T c)
  have hm : StronglyMeasurable[F.predictable] u :=
    (sourceRieszBrownianAtomRawAssembly_predictable F T c).indicator
      (measurableSet_predictable_Ioc_prod s t hA)
  rw [sourceRiesz_L2_norm_sq]
  have he : (fun p=>(sourceRieszBrownianEventCut P F T s t A hA (sourceRieszBrownianAtomAssembly P F T c) p)^2)
      =ᵐ[sourceRieszBrownianPredictableMeasure P F T] fun p=>(u p)^2 := by
    filter_upwards [@sourceRieszL2Indicator_coe (ℝ≥0×Ω) F.predictable (sourceRieszBrownianPredictableMeasure P F T)
      (Ioc s t ×ˢ A) (measurableSet_predictable_Ioc_prod s t hA) (sourceRieszBrownianAtomAssembly P F T c),
      sourceRieszBrownianAtomAssembly_coe P F T c] with p h1 h2
    dsimp only [sourceRieszBrownianEventCut]
    rw [h1]
    by_cases hp : p∈Ioc s t ×ˢ A <;> simp [u,hp,h2]
  rw [integral_congr_ae he]
  have hm2 : StronglyMeasurable[F.predictable] (fun p=>(u p)^2) := hm.pow 2
  rw [sourceRieszBrownianPredictableMeasure,←integral_trim (sourceRiesz_predictable_le_product F) hm2,
    sourceRieszBrownianTimeOn,Measure.restrict_prod_eq_prod_univ,
    ←integral_indicator (measurableSet_Ioc.prod (MeasurableSet.univ : MeasurableSet (univ : Set Ω)))]
  apply integral_congr_ae
  filter_upwards with p
  by_cases hp : p.1∈Ioc 0 T
  · exact indicator_of_mem (show p∈Ioc 0 T ×ˢ (univ : Set Ω) from ⟨hp,mem_univ _⟩) _
  · rw [indicator_of_notMem (show p∉Ioc 0 T ×ˢ (univ : Set Ω) from fun h=>hp h.1)]
    by_cases ht : p∈Ioc s t ×ˢ A
    · rw [indicator_of_mem ht,sourceRieszBrownianAtomRawAssembly_support F T c p hp]
      norm_num
    · rw [indicator_of_notMem ht]
      norm_num

lemma sourceRieszBrownianBand_interval_inter (a b s t : ℝ≥0) (hab : a≤b) (hst : s≤t) :
    Ioc (min t (max s a)) (min t (max s b))=Ioc a b∩Ioc s t := by
  rw [Ioc_inter_Ioc]
  by_cases hbs : b≤s
  · rw [max_eq_left hbs,max_eq_left (hab.trans hbs),Ioc_self,
      Ioc_eq_empty (not_lt.mpr ((min_le_left b t).trans (hbs.trans (le_max_right a s))))]
  · have hsb : s≤b := le_of_not_ge hbs
    rw [max_eq_right hsb]
    by_cases hta : t≤a
    · rw [min_eq_left (hta.trans (le_max_right s a)),min_eq_left (hta.trans hab),Ioc_self,
        Ioc_eq_empty (not_lt.mpr ((min_le_right b t).trans (hta.trans (le_max_left a s))))]
    · have hat : a≤t := le_of_not_ge hta
      rw [min_eq_right (max_le hst hat),max_comm s a,min_comm t b]

end DGRHS.Commutator

#check @DGRHS.Commutator.sourceRieszL2Indicator
#print axioms DGRHS.Commutator.sourceRieszL2Indicator

#check @DGRHS.Commutator.sourceRieszL2Indicator_coe
#print axioms DGRHS.Commutator.sourceRieszL2Indicator_coe

#check @DGRHS.Commutator.sourceRieszL2Indicator_norm_sq
#print axioms DGRHS.Commutator.sourceRieszL2Indicator_norm_sq

#check @DGRHS.Commutator.sourceRieszBrownianEventCut
#print axioms DGRHS.Commutator.sourceRieszBrownianEventCut

#check @DGRHS.Commutator.sourceRieszBrownianEventCut_raw_norm
#print axioms DGRHS.Commutator.sourceRieszBrownianEventCut_raw_norm

#check @DGRHS.Commutator.sourceRieszBrownianBand_interval_inter
#print axioms DGRHS.Commutator.sourceRieszBrownianBand_interval_inter
