/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the preserved MathFin LICENSE.
Authors: Raphael Coelho
DGR adaptation by Codex: time-measure and band geometry separated from the
source's natural filtration; predictability is proved in the supplied filtration.
-/
import DGRHS.Commutator.SourceRieszParticlePredictable
import Mathlib.MeasureTheory.Integral.Prod

/-! Selected adaptation of MathFin/Foundations/ItoIntegralL2.lean at revision
f085fd572075c934827f1eb92c4a085941cd21e5: Lebesgue time, elementary bands,
proper L2 and the actual time-overlap inner product. The original source and
Apache-2.0 license are preserved in particle-martingale-public-reuse. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def sourceRieszBrownianTime : Measure ℝ≥0 := Measure.comap ((↑) : ℝ≥0→ℝ) volume

lemma sourceRieszBrownianTime_Ioc (a b : ℝ≥0) :
    sourceRieszBrownianTime (Ioc a b)=ENNReal.ofReal ((b:ℝ)-(a:ℝ)) := by
  have hm : MeasurableEmbedding ((↑) : ℝ≥0→ℝ) := NNReal.isClosedEmbedding_coe.measurableEmbedding
  have he : ((↑) : ℝ≥0→ℝ) '' Ioc a b=Ioc (a:ℝ) (b:ℝ) := by
    ext x
    simp only [mem_image,mem_Ioc]
    constructor
    · rintro ⟨y,⟨hay,hyb⟩,rfl⟩
      exact ⟨hay,hyb⟩
    · rintro ⟨hax,hxb⟩
      have hx : 0≤x := (a.coe_nonneg.trans hax.le)
      exact ⟨⟨x,hx⟩,⟨hax,hxb⟩,rfl⟩
  rw [sourceRieszBrownianTime,hm.comap_apply,he,Real.volume_Ioc]

instance sourceRieszBrownianTime_finiteOnCompacts : IsFiniteMeasureOnCompacts sourceRieszBrownianTime :=
  IsFiniteMeasureOnCompacts.comap' volume NNReal.continuous_coe NNReal.isClosedEmbedding_coe.measurableEmbedding

instance sourceRieszBrownianTime_sigmaFinite : SigmaFinite sourceRieszBrownianTime := inferInstance

lemma sourceRieszBrownianTime_Ioc_inter (a b c d : ℝ≥0) :
    sourceRieszBrownianTime (Ioc a b∩Ioc c d)=ENNReal.ofReal (min (b:ℝ) (d:ℝ)-max (a:ℝ) (c:ℝ)) := by
  rw [Ioc_inter_Ioc,sourceRieszBrownianTime_Ioc,NNReal.coe_min,NNReal.coe_max]

def sourceRieszBrownianBand (a b : ℝ≥0) (Z : Ω→ℝ) : ℝ≥0×Ω→ℝ :=
  fun p=>(Ioc a b).indicator (fun _=>(1:ℝ)) p.1*Z p.2

lemma sourceRieszBrownianBand_indicator (a b : ℝ≥0) (Z : Ω→ℝ) :
    sourceRieszBrownianBand a b Z=(Ioc a b ×ˢ (univ : Set Ω)).indicator (fun p=>Z p.2) := by
  funext p
  simp only [sourceRieszBrownianBand,indicator_apply,mem_prod,mem_univ,and_true]
  split_ifs <;> simp

lemma sourceRieszBrownianBand_memLp (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : ℝ≥0) (Z : Ω→ℝ) (hm : StronglyMeasurable Z)
    (K : ℝ≥0) (hb : ∀ ω,‖Z ω‖≤(K:ℝ)) :
    MemLp (sourceRieszBrownianBand a b Z) 2 (sourceRieszBrownianTime.prod P) := by
  haveI : IsFiniteMeasure (sourceRieszBrownianTime.restrict (Ioc a b)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ,univ_inter,sourceRieszBrownianTime_Ioc]
        exact ENNReal.ofReal_lt_top⟩
  rw [sourceRieszBrownianBand_indicator,memLp_indicator_iff_restrict (measurableSet_Ioc.prod MeasurableSet.univ),
    ←Measure.prod_restrict,Measure.restrict_univ]
  exact MemLp.of_bound (hm.comp_measurable measurable_snd).aestronglyMeasurable K
    (ae_of_all _ fun p=>hb p.2)

lemma sourceRieszBrownianBand_predictable (F : Filtration ℝ≥0 mΩ)
    (a b : ℝ≥0) (Z : Ω→ℝ) (hZ : StronglyMeasurable[F a] Z) :
    StronglyMeasurable[F.predictable] (sourceRieszBrownianBand a b Z) := by
  let U := fun r ω=>sourceRieszBrownianBand a b Z (r,ω)
  have hUa : StronglyAdapted F U := by
    intro r
    by_cases hr : r∈Ioc a b
    · have he : U r=Z := by funext ω;simp only [U,sourceRieszBrownianBand,indicator_of_mem hr,one_mul]
      rw [he]
      exact hZ.mono (F.mono hr.1.le)
    · have he : U r=fun _=>0 := by funext ω;simp only [U,sourceRieszBrownianBand,indicator_of_notMem hr,zero_mul]
      rw [he]
      exact stronglyMeasurable_const
  have he (ω) : (fun r=>U r ω)=
      (fun r=>(if r≤b then (1:ℝ) else 0)*(1-(if r≤a then (1:ℝ) else 0))*Z ω) := by
    funext r
    by_cases ha : r≤a <;> by_cases hb : r≤b <;>
      simp [U,sourceRieszBrownianBand,indicator_apply,mem_Ioc,ha,hb,not_lt.mpr,lt_of_not_ge]
  have hUc (ω) (r) : ContinuousWithinAt (fun u=>U u ω) (Iio r) r := by
    rw [he]
    exact ((sourceRiesz_cutoff_leftContinuous b r).mul
      (continuousWithinAt_const.sub (sourceRiesz_cutoff_leftContinuous a r))).mul continuousWithinAt_const
  exact sourceRiesz_adapted_predictable_of_leftContinuous hUa hUc

theorem sourceRieszBrownianBand_pairing (P : Measure Ω) [IsProbabilityMeasure P]
    (a b c d : ℝ≥0) (Z Y : Ω→ℝ) :
    (∫ p,sourceRieszBrownianBand a b Z p*sourceRieszBrownianBand c d Y p
      ∂sourceRieszBrownianTime.prod P)=
      (∫ ω,Z ω*Y ω ∂P)*max 0 (min (b:ℝ) (d:ℝ)-max (a:ℝ) (c:ℝ)) := by
  have he : (fun p=>sourceRieszBrownianBand a b Z p*sourceRieszBrownianBand c d Y p)=
      (fun p : ℝ≥0×Ω=>((Ioc a b).indicator (fun _=>(1:ℝ)) p.1*
        (Ioc c d).indicator (fun _=>(1:ℝ)) p.1)*(Z p.2*Y p.2)) := by
    funext p
    dsimp only [sourceRieszBrownianBand]
    ring
  rw [he,integral_prod_mul
    (fun r : ℝ≥0=>(Ioc a b).indicator (fun _=>(1:ℝ)) r*(Ioc c d).indicator (fun _=>(1:ℝ)) r)
    (fun ω=>Z ω*Y ω),mul_comm]
  congr 1
  have hi (r : ℝ≥0) : (Ioc a b).indicator (fun _=>(1:ℝ)) r*
      (Ioc c d).indicator (fun _=>(1:ℝ)) r=(Ioc a b∩Ioc c d).indicator (1 : ℝ≥0→ℝ) r := by
    rw [inter_indicator_one]
    rfl
  simp_rw [hi]
  rw [integral_indicator_one (measurableSet_Ioc.inter measurableSet_Ioc),
    Measure.real_def,sourceRieszBrownianTime_Ioc_inter,ENNReal.toReal_ofReal',max_comm]

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianTime
#print axioms DGRHS.Commutator.sourceRieszBrownianTime
#check @DGRHS.Commutator.sourceRieszBrownianTime_Ioc
#print axioms DGRHS.Commutator.sourceRieszBrownianTime_Ioc
#print axioms DGRHS.Commutator.sourceRieszBrownianTime_finiteOnCompacts
#print axioms DGRHS.Commutator.sourceRieszBrownianTime_sigmaFinite
#check @DGRHS.Commutator.sourceRieszBrownianTime_Ioc_inter
#print axioms DGRHS.Commutator.sourceRieszBrownianTime_Ioc_inter
#check @DGRHS.Commutator.sourceRieszBrownianBand
#print axioms DGRHS.Commutator.sourceRieszBrownianBand
#check @DGRHS.Commutator.sourceRieszBrownianBand_indicator
#print axioms DGRHS.Commutator.sourceRieszBrownianBand_indicator
#check @DGRHS.Commutator.sourceRieszBrownianBand_memLp
#print axioms DGRHS.Commutator.sourceRieszBrownianBand_memLp
#check @DGRHS.Commutator.sourceRieszBrownianBand_predictable
#print axioms DGRHS.Commutator.sourceRieszBrownianBand_predictable
#check @DGRHS.Commutator.sourceRieszBrownianBand_pairing
#print axioms DGRHS.Commutator.sourceRieszBrownianBand_pairing
#check @DGRHS.Commutator.sourceRieszBrownianTime_finiteOnCompacts
#check @DGRHS.Commutator.sourceRieszBrownianTime_sigmaFinite
