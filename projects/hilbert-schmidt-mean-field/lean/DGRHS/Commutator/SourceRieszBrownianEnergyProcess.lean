import DGRHS.Commutator.SourceRieszBrownianConditionalEnergy
import Mathlib.MeasureTheory.Integral.Prod

/-! The actual time integral of the squared predictable integrand, with proper
integrability and adaptedness in the supplied full filtration. Native
predictable-to-progressive measurability is used with a deterministic cutoff. -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)

def sourceRieszBrownianEnergy (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (t : ℝ≥0) (ω : Ω) : ℝ := ∫ r in Ioc 0 t,(g (r,ω))^2 ∂sourceRieszBrownianTimeOn T

lemma sourceRieszBrownianEnergy_product_integrable
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    Integrable (fun p=>(g p)^2) ((sourceRieszBrownianTimeOn T).prod P) :=
  integrable_of_integrable_trim (sourceRiesz_predictable_le_product F) (Lp.memLp g).integrable_sq

lemma sourceRieszBrownianEnergy_integrable
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (t : ℝ≥0) :
    Integrable (sourceRieszBrownianEnergy P F T g t) P := by
  have hi : Integrable (fun p=>(g p)^2) (((sourceRieszBrownianTimeOn T).restrict (Ioc 0 t)).prod P) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact (sourceRieszBrownianEnergy_product_integrable P F T g).integrableOn
  exact hi.integral_prod_right

lemma sourceRieszBrownianEnergy_adapted
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    StronglyAdapted F (sourceRieszBrownianEnergy P F T g) := by
  intro t
  have hp : IsStronglyPredictable F (fun r ω=>g (r,ω)) := Lp.stronglyMeasurable g
  have hr := hp.isStronglyProgressive t
  have hfun : sourceRieszBrownianEnergy P F T g t = fun ω =>
      ∫ r, (Ioc 0 t ×ˢ (univ:Set Ω)).indicator
        (fun p : ℝ≥0×Ω => (g (min p.1 t,p.2))^2) (r,ω) ∂sourceRieszBrownianTimeOn T := by
    funext ω
    rw [sourceRieszBrownianEnergy,←integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with r
    by_cases h : r∈Ioc 0 t
    · simp [h,min_eq_left h.2]
    · simp [h]
  rw [hfun]
  letI : MeasurableSpace Ω := F t
  have hm : Measurable (fun p : ℝ≥0×Ω=>(⟨min p.1 t,Set.mem_Iic.mpr (min_le_right p.1 t)⟩,p.2) : ℝ≥0×Ω→Iic t×Ω) :=
    (measurable_fst.min measurable_const).subtype_mk.prodMk measurable_snd
  have hc : StronglyMeasurable (fun p : ℝ≥0×Ω=>g (min p.1 t,p.2)) := hr.comp_measurable hm
  have hs := (hc.pow 2).indicator ((measurableSet_Ioc (a:=(0:ℝ≥0)) (b:=t)).prod
    (MeasurableSet.univ : MeasurableSet (univ:Set Ω)))
  exact hs.integral_prod_left' (μ:=sourceRieszBrownianTimeOn T)

lemma sourceRieszBrownianEnergy_setIntegral
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (t : ℝ≥0) (A : Set Ω) :
    (∫ ω in A,sourceRieszBrownianEnergy P F T g t ω ∂P)=
      ∫ p in Ioc 0 t ×ˢ A,(g p)^2 ∂(sourceRieszBrownianTimeOn T).prod P := by
  have hi : Integrable (fun p=>(g p)^2)
      (((sourceRieszBrownianTimeOn T).restrict (Ioc 0 t)).prod (P.restrict A)) := by
    rw [Measure.prod_restrict]
    exact (sourceRieszBrownianEnergy_product_integrable P F T g).integrableOn
  rw [←Measure.prod_restrict]
  exact (integral_prod_symm _ hi).symm

lemma sourceRieszBrownianEnergy_interval_trim
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (s t : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[F s] A) :
    (∫ p in Ioc s t ×ˢ A,(g p)^2 ∂sourceRieszBrownianPredictableMeasure P F T)=
      ∫ p in Ioc s t ×ˢ A,(g p)^2 ∂(sourceRieszBrownianTimeOn T).prod P := by
  have hS := measurableSet_predictable_Ioc_prod s t hA
  have hm : StronglyMeasurable[F.predictable] ((Ioc s t ×ˢ A).indicator (fun p=>(g p)^2)) :=
    ((Lp.stronglyMeasurable g).pow 2).indicator hS
  rw [←integral_indicator hS]
  change (∫ p,(Ioc s t ×ˢ A).indicator (fun p=>(g p)^2) p
    ∂((sourceRieszBrownianTimeOn T).prod P).trim (sourceRiesz_predictable_le_product F))=_
  rw [←integral_trim (sourceRiesz_predictable_le_product F) hm,
    integral_indicator (measurableSet_Ioc.prod (F.le s _ hA))]

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianEnergy
#print axioms DGRHS.Commutator.sourceRieszBrownianEnergy
#check @DGRHS.Commutator.sourceRieszBrownianEnergy_product_integrable
#print axioms DGRHS.Commutator.sourceRieszBrownianEnergy_product_integrable
#check @DGRHS.Commutator.sourceRieszBrownianEnergy_integrable
#print axioms DGRHS.Commutator.sourceRieszBrownianEnergy_integrable
#check @DGRHS.Commutator.sourceRieszBrownianEnergy_adapted
#print axioms DGRHS.Commutator.sourceRieszBrownianEnergy_adapted
#check @DGRHS.Commutator.sourceRieszBrownianEnergy_setIntegral
#print axioms DGRHS.Commutator.sourceRieszBrownianEnergy_setIntegral
#check @DGRHS.Commutator.sourceRieszBrownianEnergy_interval_trim
#print axioms DGRHS.Commutator.sourceRieszBrownianEnergy_interval_trim
