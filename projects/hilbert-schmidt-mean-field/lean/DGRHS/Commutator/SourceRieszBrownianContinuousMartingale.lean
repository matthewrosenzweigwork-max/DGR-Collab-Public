import DGRHS.Commutator.SourceRieszBrownianContinuousPaths
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the preserved MathFin LICENSE.
The convergence-in-measure uniqueness strategy adapts MathFin/Foundations/
ItoIntegralProcessContinuousModification.lean at f085fd572075c934827f1eb92c4a085941cd21e5.
The measurable-limsup construction is strongly adapted without augmentation;
this file identifies it with the actual completed Brownian integral and proves
its native martingale and exact energy properties. Paths are continuous almost
surely. No conditional bracket or multidriver covariance is asserted here.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
variable (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
variable (hind : ∀ s t,s≤t →
  Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)
variable (hBc : ∀ ω,Continuous (fun r=>B r ω))

include hBc in
theorem sourceRieszBrownianContinuousProcess_modification
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (t : ℝ≥0) :
    sourceRieszBrownianContinuousProcess P F T B g t=ᵐ[P]
      (sourceRieszBrownianProcessL2 P F T B hB hBa hind g t : Ω→ℝ) := by
  let c := (sourceRieszBrownianApproxSeq P F T g).choose
  have hc := (sourceRieszBrownianApproxSeq P F T g).choose_spec
  let V n := sourceRieszBrownianElementaryProcess F T B (c n) t
  have hVa : ∀ n,AEStronglyMeasurable (V n) P := fun n=>
    ((sourceRieszBrownianElementaryProcess_martingale P F T B hB hBa hind hBc (c n)).2 t).aestronglyMeasurable
  have hVm : TendstoInMeasure P V atTop (sourceRieszBrownianContinuousProcess P F T B g t) := by
    apply tendstoInMeasure_of_tendsto_ae hVa
    filter_upwards [sourceRieszBrownianContinuousProcess_tendsto P F T B hB hBa hind hBc g] with ω hω using hω t
  have ha : Tendsto (fun n=>sourceRieszBrownianAtomAssembly P F T (c n)) atTop (𝓝 g) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n=>norm_nonneg _) hc
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have hL := ((sourceRieszBrownianProcessL2_continuous P F T B hB hBa hind t).tendsto g).comp ha
  have hLm : TendstoInMeasure P V atTop
      (sourceRieszBrownianProcessL2 P F T B hB hBa hind g t : Ω→ℝ) :=
    TendstoInMeasure.congr_left
      (fun n=>sourceRieszBrownianElementaryProcess_ae P F T B hB hBa hind hBc (c n) t)
      (tendstoInMeasure_of_tendsto_Lp hL)
  exact tendstoInMeasure_ae_unique hVm hLm

include hB hBa hind hBc in
theorem sourceRieszBrownianContinuousProcess_martingale
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    Martingale (sourceRieszBrownianContinuousProcess P F T B g) F P ∧
      (∀ t,MemLp (sourceRieszBrownianContinuousProcess P F T B g t) 2 P) ∧
      (∀ᵐ ω ∂P,Continuous (fun t=>sourceRieszBrownianContinuousProcess P F T B g t ω)) := by
  have he t := sourceRieszBrownianContinuousProcess_modification P F T B hB hBa hind hBc g t
  have hm := sourceRieszBrownianProcess_martingale P F T B hB hBa hind g
  refine ⟨hm.1.congr (sourceRieszBrownianContinuousProcess_adapted P F T B hB hBa hind hBc g)
    (fun t=>?_),fun t=>?_,sourceRieszBrownianContinuousProcess_ae_continuous P F T B hB hBa hind hBc g⟩
  · exact ((he t).trans (sourceRieszBrownianProcessL2_coe P F T B hB hBa hind g t)).symm
  · exact (memLp_congr_ae (he t).symm).mp (Lp.memLp _)

lemma sourceRieszBrownianContinuousProcess_zero
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (ω : Ω) :
    sourceRieszBrownianContinuousProcess P F T B g 0 ω=0 := by
  simp [sourceRieszBrownianContinuousProcess,sourceRieszBrownianElementaryProcess_apply]

include hBc in
lemma sourceRieszBrownianContinuousProcess_terminal
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    sourceRieszBrownianContinuousProcess P F T B g T=ᵐ[P]
      (sourceRieszBrownianIntegral P F T B hB hBa hind g : Ω→ℝ) := by
  have h := sourceRieszBrownianContinuousProcess_modification P F T B hB hBa hind hBc g T
  rwa [sourceRieszBrownianProcessL2_terminal P F T B hB hBa hind hBc] at h

include hB hBa hind hBc in
theorem sourceRieszBrownianContinuousProcess_second_moment
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (t : ℝ≥0) :
    Integrable (fun ω=>(sourceRieszBrownianContinuousProcess P F T B g t ω)^2) P ∧
      (∫ ω,(sourceRieszBrownianContinuousProcess P F T B g t ω)^2 ∂P)=
        ∫ p in Ioc 0 t ×ˢ (univ : Set Ω),(g p)^2 ∂sourceRieszBrownianPredictableMeasure P F T := by
  refine ⟨((sourceRieszBrownianContinuousProcess_martingale P F T B hB hBa hind hBc g).2.1 t).integrable_sq,?_⟩
  rw [←sourceRieszBrownianProcessL2_norm_sq P F T B hB hBa hind hBc g t,sourceRiesz_L2_norm_sq]
  apply integral_congr_ae
  filter_upwards [sourceRieszBrownianContinuousProcess_modification P F T B hB hBa hind hBc g t] with ω hω
  rw [hω]

include hB hBa hind hBc in
theorem sourceRieszBrownianContinuousProcess_initial_weighted_zero
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (t : ℝ≥0)
    (Z : Ω→ℝ) (hZ : StronglyMeasurable[F 0] Z) (hZL : MemLp Z 2 P) :
    Integrable (fun ω=>Z ω*sourceRieszBrownianContinuousProcess P F T B g t ω) P ∧
      (∫ ω,Z ω*sourceRieszBrownianContinuousProcess P F T B g t ω ∂P)=0 := by
  have he := (sourceRieszBrownianContinuousProcess_modification P F T B hB hBa hind hBc g t).trans
    (sourceRieszBrownianProcessL2_coe P F T B hB hBa hind g t)
  have he' : (fun ω=>Z ω*sourceRieszBrownianContinuousProcess P F T B g t ω)=ᵐ[P]
      (fun ω=>Z ω*sourceRieszBrownianProcess P F T B hB hBa hind g t ω) :=
    he.mono (fun ω hω=>by dsimp only;rw [hω])
  have hz := sourceRieszBrownianProcess_initial_weighted_zero P F T B hB hBa hind hBc g t Z hZ hZL
  exact ⟨hz.1.congr he'.symm,(integral_congr_ae he').trans hz.2⟩

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_modification
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_modification
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_martingale
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_martingale
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_zero
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_zero
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_terminal
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_terminal
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_second_moment
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_second_moment
#check @DGRHS.Commutator.sourceRieszBrownianContinuousProcess_initial_weighted_zero
#print axioms DGRHS.Commutator.sourceRieszBrownianContinuousProcess_initial_weighted_zero
