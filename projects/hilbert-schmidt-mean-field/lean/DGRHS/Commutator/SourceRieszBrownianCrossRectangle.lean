/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the preserved MathFin LICENSE.
Authors: Raphael Coelho
The split at the later start follows the licensed selected scalar rectangle
proof in SourceRieszBrownianRectangleIsometry. The cross-driver argument uses
joint future independence in the full filtration and independent driver paths.
-/
import DGRHS.Commutator.SourceRieszBrownianCrossConditional

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private lemma cross_rectangle_left
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (B C : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C P)
    (hBa : StronglyAdapted F B) (hCa : StronglyAdapted F C)
    (hindC : ∀ s t,s≤t →
      Indep (MeasurableSpace.comap (fun ω=>C t ω-C s ω) (borel ℝ)) (F s) P)
    (hd : IndepFun (fun ω=>fun r=>B r ω) (fun ω=>fun r=>C r ω) P)
    (hp : ∀ s t u,s≤t → s≤u →
      Indep (MeasurableSpace.comap (fun ω=>(B t ω-B s ω,C u ω-C s ω)) inferInstance) (F s) P)
    (a b c d : ℝ≥0) (hab : a≤b) (hcd : c≤d) (hac : a≤c)
    (H J : Ω→ℝ) (hH : StronglyMeasurable[F a] H) (hJ : StronglyMeasurable[F c] J)
    (K L : ℝ≥0) (hbH : ∀ᵐ ω ∂P,‖H ω‖≤(K:ℝ)) (hbJ : ∀ᵐ ω ∂P,‖J ω‖≤(L:ℝ)) :
    (∫ ω,(H ω*(B b ω-B a ω))*(J ω*(C d ω-C c ω)) ∂P)=0 := by
  have hBm r : Measurable (B r) := ((hBa r).mono (F.le r)).measurable
  have hCm r : Measurable (C r) := ((hCa r).mono (F.le r)).measurable
  have hHJ : StronglyMeasurable[F c] (fun ω=>H ω*J ω) := (hH.mono (F.mono hac)).mul hJ
  have hbHJ : ∀ᵐ ω ∂P,‖H ω*J ω‖≤(K:ℝ)*(L:ℝ) := by
    filter_upwards [hbH,hbJ] with ω hh hj
    rw [norm_mul]
    exact mul_le_mul hh hj (norm_nonneg _) K.coe_nonneg
  have hprodL (u v) : MemLp (fun ω=>H ω*J ω*(B v ω-B u ω)) 2 P :=
    sourceRiesz_memLp_bounded_mul P _ _ (hHJ.mono (F.le c)).aestronglyMeasurable
      (hB.hasLaw_sub v u).hasGaussianLaw.memLp_two ((K:ℝ)*(L:ℝ)) hbHJ
  by_cases hbc : b≤c
  · have hZ : StronglyMeasurable[F c] (fun ω=>H ω*J ω*(B b ω-B a ω)) :=
      hHJ.mul (((hBa b).mono (F.mono hbc)).sub ((hBa a).mono (F.mono hac)))
    have hz := (sourceRiesz_brownian_mean_adapted_increment P F C hC hCm c d hcd
      (hindC c d hcd) _ hZ (hprodL a b)).2
    rw [←hz]
    exact integral_congr_ae (ae_of_all _ fun ω=>by ring)
  · have hcb : c≤b := le_of_not_ge hbc
    have hZ : StronglyMeasurable[F c] (fun ω=>H ω*J ω*(B c ω-B a ω)) :=
      hHJ.mul ((hBa c).sub ((hBa a).mono (F.mono hac)))
    obtain ⟨hi0,h0⟩ := sourceRiesz_brownian_mean_adapted_increment P F C hC hCm c d hcd
      (hindC c d hcd) _ hZ (hprodL a c)
    obtain ⟨hi1,h1⟩ := sourceRiesz_brownian_cross_bounded_increment P F B C hB hC hBm hCm hd
      c b d (hp c b d hcb hcd) _ hHJ ((K:ℝ)*(L:ℝ)) hbHJ
    have he : (∫ ω,(H ω*(B b ω-B a ω))*(J ω*(C d ω-C c ω)) ∂P)=
        (∫ ω,H ω*J ω*(B c ω-B a ω)*(C d ω-C c ω) ∂P)+
        (∫ ω,H ω*J ω*(B b ω-B c ω)*(C d ω-C c ω) ∂P) := by
      rw [←integral_add hi0 hi1]
      exact integral_congr_ae (ae_of_all _ fun ω=>by ring)
    rw [he,h0,h1,zero_add]

theorem sourceRiesz_brownian_cross_rectangle
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (B C : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hC : IsPreBrownianReal C P)
    (hBa : StronglyAdapted F B) (hCa : StronglyAdapted F C)
    (hindB : ∀ s t,s≤t →
      Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)
    (hindC : ∀ s t,s≤t →
      Indep (MeasurableSpace.comap (fun ω=>C t ω-C s ω) (borel ℝ)) (F s) P)
    (hd : IndepFun (fun ω=>fun r=>B r ω) (fun ω=>fun r=>C r ω) P)
    (hp : ∀ s t u,s≤t → s≤u →
      Indep (MeasurableSpace.comap (fun ω=>(B t ω-B s ω,C u ω-C s ω)) inferInstance) (F s) P)
    (a b c d : ℝ≥0) (hab : a≤b) (hcd : c≤d)
    (H J : Ω→ℝ) (hH : StronglyMeasurable[F a] H) (hJ : StronglyMeasurable[F c] J)
    (K L : ℝ≥0) (hbH : ∀ᵐ ω ∂P,‖H ω‖≤(K:ℝ)) (hbJ : ∀ᵐ ω ∂P,‖J ω‖≤(L:ℝ)) :
    Integrable (fun ω=>(H ω*(B b ω-B a ω))*(J ω*(C d ω-C c ω))) P ∧
      (∫ ω,(H ω*(B b ω-B a ω))*(J ω*(C d ω-C c ω)) ∂P)=0 := by
  have hHL := sourceRiesz_memLp_bounded_mul P H _ (hH.mono (F.le a)).aestronglyMeasurable
    (hB.hasLaw_sub b a).hasGaussianLaw.memLp_two K hbH
  have hJL := sourceRiesz_memLp_bounded_mul P J _ (hJ.mono (F.le c)).aestronglyMeasurable
    (hC.hasLaw_sub d c).hasGaussianLaw.memLp_two L hbJ
  refine ⟨hHL.integrable_mul hJL,?_⟩
  rcases le_total a c with hac | hca
  · exact cross_rectangle_left P F B C hB hC hBa hCa hindC hd hp a b c d hab hcd hac H J hH hJ K L hbH hbJ
  · have hp' : ∀ s t u,s≤t → s≤u →
        Indep (MeasurableSpace.comap (fun ω=>(C t ω-C s ω,B u ω-B s ω)) inferInstance) (F s) P := by
      intro s t u hst hsu
      exact sourceRiesz_indep_pair_swap P (F s) _ _ (hp s u t hsu hst)
    have hz := cross_rectangle_left P F C B hC hB hCa hBa hindB hd.symm hp' c d a b hcd hab hca J H hJ hH L K hbJ hbH
    rw [←hz]
    exact integral_congr_ae (ae_of_all _ fun ω=>mul_comm _ _)

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_brownian_cross_rectangle
#print axioms DGRHS.Commutator.sourceRiesz_brownian_cross_rectangle
