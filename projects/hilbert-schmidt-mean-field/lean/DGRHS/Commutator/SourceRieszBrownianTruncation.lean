/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the preserved MathFin LICENSE.
Authors: Raphael Coelho
DGR adaptation by Codex: deterministic cutoff on the supplied full-filtration
predictable L2 space, with direct native indicator and norm proofs.
-/
import DGRHS.Commutator.SourceRieszBrownianIntegral

/-! Selected truncation CLM proof from MathFin ItoIntegralProcessIsometry.lean,
revision f085fd572075c934827f1eb92c4a085941cd21e5, preserved with Apache-2.0 license. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T t : ℝ≥0)

private lemma hband : MeasurableSet[F.predictable] (Ioc 0 t ×ˢ (univ : Set Ω)) :=
  measurableSet_predictable_Ioc_prod 0 t MeasurableSet.univ

def sourceRieszBrownianTruncation :
    Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T) →L[ℝ]
      Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T) :=
  LinearMap.mkContinuous
    { toFun := fun g=>((Lp.memLp g).indicator (hband F t)).toLp
        ((Ioc 0 t ×ˢ (univ : Set Ω)).indicator (g : ℝ≥0×Ω→ℝ))
      map_add' := fun g k=>by
        apply Lp.ext
        filter_upwards [((Lp.memLp (g+k)).indicator (hband F t)).coeFn_toLp,
          Lp.coeFn_add (((Lp.memLp g).indicator (hband F t)).toLp _)
            (((Lp.memLp k).indicator (hband F t)).toLp _),
          ((Lp.memLp g).indicator (hband F t)).coeFn_toLp,
          ((Lp.memLp k).indicator (hband F t)).coeFn_toLp,Lp.coeFn_add g k]
          with p h1 h2 h3 h4 h5
        rw [h1,h2,Pi.add_apply,h3,h4]
        simp only [indicator_apply,h5,Pi.add_apply]
        split_ifs <;> ring
      map_smul' := fun c g=>by
        apply Lp.ext
        filter_upwards [((Lp.memLp (c • g)).indicator (hband F t)).coeFn_toLp,
          Lp.coeFn_smul c (((Lp.memLp g).indicator (hband F t)).toLp _),
          ((Lp.memLp g).indicator (hband F t)).coeFn_toLp,Lp.coeFn_smul c g]
          with p h1 h2 h3 h4
        rw [h1,RingHom.id_apply,h2,Pi.smul_apply,h3]
        simp only [indicator_apply,h4,Pi.smul_apply,smul_eq_mul]
        split_ifs <;> ring }
    1 (fun g=>by
      simp only [LinearMap.coe_mk,AddHom.coe_mk]
      rw [one_mul,Lp.norm_toLp,Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_lt_top g).ne (eLpNorm_indicator_le _ (hband F t)))

lemma sourceRieszBrownianTruncation_coe
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    (sourceRieszBrownianTruncation P F T t g : ℝ≥0×Ω→ℝ)
      =ᵐ[sourceRieszBrownianPredictableMeasure P F T] (Ioc 0 t ×ˢ (univ : Set Ω)).indicator (g : ℝ≥0×Ω→ℝ) :=
  ((Lp.memLp g).indicator (hband F t)).coeFn_toLp

lemma sourceRieszBrownianTruncation_norm_sq
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    ‖sourceRieszBrownianTruncation P F T t g‖^2=
      ∫ p in Ioc 0 t ×ˢ (univ : Set Ω),(g p)^2 ∂sourceRieszBrownianPredictableMeasure P F T := by
  rw [sourceRiesz_L2_norm_sq,←integral_indicator (hband F t)]
  apply integral_congr_ae
  filter_upwards [sourceRieszBrownianTruncation_coe P F T t g] with p hp
  rw [hp]
  by_cases h : p∈Ioc 0 t ×ˢ (univ : Set Ω) <;> simp [h]

lemma sourceRieszBrownianBand_time_inter (a b t : ℝ≥0) (hab : a≤b) :
    Ioc (min t a) (min t b)=Ioc a b∩Ioc 0 t := by
  rw [Ioc_inter_Ioc,max_eq_left (show (0:ℝ≥0)≤a from bot_le)]
  by_cases hta : t≤a
  · rw [min_eq_left hta,min_eq_left (hta.trans hab),Ioc_self,
      Ioc_eq_empty (not_lt.mpr ((min_le_right b t).trans hta))]
  · rw [min_eq_right (le_of_not_ge hta),min_comm t b]

end DGRHS.Commutator

#check @DGRHS.Commutator.sourceRieszBrownianTruncation
#print axioms DGRHS.Commutator.sourceRieszBrownianTruncation

#check @DGRHS.Commutator.sourceRieszBrownianTruncation_coe
#print axioms DGRHS.Commutator.sourceRieszBrownianTruncation_coe

#check @DGRHS.Commutator.sourceRieszBrownianTruncation_norm_sq
#print axioms DGRHS.Commutator.sourceRieszBrownianTruncation_norm_sq

#check @DGRHS.Commutator.sourceRieszBrownianBand_time_inter
#print axioms DGRHS.Commutator.sourceRieszBrownianBand_time_inter
