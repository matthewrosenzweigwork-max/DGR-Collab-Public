/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the preserved MathFin LICENSE.
Authors: Raphael Coelho
DGR adaptation by Codex: arbitrary full filtration, almost-everywhere bounds,
proper integrability, and sequential conditional pairing in place of the
source's scalar-natural-filtration future-process factorization.
-/
import DGRHS.Commutator.SourceRieszBrownianPairing

/-! The actual predictable-rectangle Ito pairing. This adapts the split at the
later start in MathFin/Foundations/ItoIsometryAdapted.lean, revision
f085fd572075c934827f1eb92c4a085941cd21e5. Exact original source and license
are preserved with ITO_ISOMETRY_ADDITIONAL_PROVENANCE.json in own records.
All conditional calculations use the supplied full filtration. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private lemma sourceRiesz_brownian_rectangle_pairing_left
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
    (hind : ∀ s t,s≤t →
      Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)
    (a b c d : ℝ≥0) (hab : a≤b) (hcd : c≤d) (hac : a≤c)
    (H J : Ω→ℝ) (hH : StronglyMeasurable[F a] H) (hJ : StronglyMeasurable[F c] J)
    (K L : ℝ≥0) (hbH : ∀ᵐ ω ∂P,‖H ω‖≤(K:ℝ)) (hbJ : ∀ᵐ ω ∂P,‖J ω‖≤(L:ℝ)) :
    (∫ ω,(H ω*(B b ω-B a ω))*(J ω*(B d ω-B c ω)) ∂P)=
      (∫ ω,H ω*J ω ∂P)*max 0 (min (b:ℝ) (d:ℝ)-max (a:ℝ) (c:ℝ)) := by
  have hBm (r) : Measurable (B r) := ((hBa r).mono (F.le r)).measurable
  have hHJ : StronglyMeasurable[F c] (fun ω=>H ω*J ω) := (hH.mono (F.mono hac)).mul hJ
  have hbHJ : ∀ᵐ ω ∂P,‖H ω*J ω‖≤(K:ℝ)*(L:ℝ) := by
    filter_upwards [hbH,hbJ] with ω hh hj
    rw [norm_mul]
    exact mul_le_mul hh hj (norm_nonneg _) K.coe_nonneg
  have hprodL (u v) : MemLp (fun ω=>H ω*J ω*(B v ω-B u ω)) 2 P :=
    sourceRiesz_memLp_bounded_mul P _ _ (hHJ.mono (F.le c)).aestronglyMeasurable
      (hB.hasLaw_sub v u).hasGaussianLaw.memLp_two ((K:ℝ)*(L:ℝ)) hbHJ
  rw [max_eq_right (show (a:ℝ)≤(c:ℝ) from hac)]
  by_cases hbc : b≤c
  · have hZ : StronglyMeasurable[F c] (fun ω=>H ω*J ω*(B b ω-B a ω)) :=
      hHJ.mul (((hBa b).mono (F.mono hbc)).sub ((hBa a).mono (F.mono hac)))
    have hz := (sourceRiesz_brownian_mean_adapted_increment P F B hB hBm c d hcd
      (hind c d hcd) _ hZ (hprodL a b)).2
    have hzero : max (0:ℝ) (min (b:ℝ) (d:ℝ)-(c:ℝ))=0 :=
      max_eq_left (sub_nonpos.mpr ((min_le_left _ _).trans (show (b:ℝ)≤(c:ℝ) from hbc)))
    rw [hzero,mul_zero,←hz]
    exact integral_congr_ae (ae_of_all _ fun ω=>by ring)
  · have hcb : c≤b := le_of_not_ge hbc
    have hZ : StronglyMeasurable[F c] (fun ω=>H ω*J ω*(B c ω-B a ω)) :=
      hHJ.mul ((hBa c).sub ((hBa a).mono (F.mono hac)))
    obtain ⟨hi0,h0⟩ := sourceRiesz_brownian_mean_adapted_increment P F B hB hBm c d hcd
      (hind c d hcd) _ hZ (hprodL a c)
    obtain ⟨hi1,h1⟩ := sourceRiesz_brownian_common_start_pairing P F B hB hBa hind
      c b d hcb hcd _ hHJ ((K:ℝ)*(L:ℝ)) hbHJ
    have he : (∫ ω,(H ω*(B b ω-B a ω))*(J ω*(B d ω-B c ω)) ∂P)=
        (∫ ω,H ω*J ω*(B c ω-B a ω)*(B d ω-B c ω) ∂P)+
        (∫ ω,H ω*J ω*(B b ω-B c ω)*(B d ω-B c ω) ∂P) := by
      rw [←integral_add hi0 hi1]
      exact integral_congr_ae (ae_of_all _ fun ω=>by ring)
    rw [he,h0,h1,zero_add,NNReal.coe_min,
      max_eq_right (sub_nonneg.mpr (le_min (show (c:ℝ)≤(b:ℝ) from hcb) (show (c:ℝ)≤(d:ℝ) from hcd)))]

theorem sourceRiesz_brownian_rectangle_pairing
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
    (hind : ∀ s t,s≤t →
      Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)
    (a b c d : ℝ≥0) (hab : a≤b) (hcd : c≤d)
    (H J : Ω→ℝ) (hH : StronglyMeasurable[F a] H) (hJ : StronglyMeasurable[F c] J)
    (K L : ℝ≥0) (hbH : ∀ᵐ ω ∂P,‖H ω‖≤(K:ℝ)) (hbJ : ∀ᵐ ω ∂P,‖J ω‖≤(L:ℝ)) :
    Integrable (fun ω=>(H ω*(B b ω-B a ω))*(J ω*(B d ω-B c ω))) P ∧
      (∫ ω,(H ω*(B b ω-B a ω))*(J ω*(B d ω-B c ω)) ∂P)=
        (∫ ω,H ω*J ω ∂P)*max 0 (min (b:ℝ) (d:ℝ)-max (a:ℝ) (c:ℝ)) := by
  have hHL := sourceRiesz_memLp_bounded_mul P H _ (hH.mono (F.le a)).aestronglyMeasurable
    (hB.hasLaw_sub b a).hasGaussianLaw.memLp_two K hbH
  have hJL := sourceRiesz_memLp_bounded_mul P J _ (hJ.mono (F.le c)).aestronglyMeasurable
    (hB.hasLaw_sub d c).hasGaussianLaw.memLp_two L hbJ
  refine ⟨hHL.integrable_mul hJL,?_⟩
  rcases le_total a c with hac | hca
  · exact sourceRiesz_brownian_rectangle_pairing_left P F B hB hBa hind a b c d hab hcd hac H J hH hJ K L hbH hbJ
  · have he : (fun ω=>(H ω*(B b ω-B a ω))*(J ω*(B d ω-B c ω)))=
        (fun ω=>(J ω*(B d ω-B c ω))*(H ω*(B b ω-B a ω))) := by
      funext ω
      ring
    rw [he,sourceRiesz_brownian_rectangle_pairing_left P F B hB hBa hind c d a b hcd hab hca J H hJ hH L K hbJ hbH,
      min_comm (d:ℝ) (b:ℝ),max_comm (c:ℝ) (a:ℝ)]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun ω=>mul_comm _ _)

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_brownian_rectangle_pairing
#print axioms DGRHS.Commutator.sourceRiesz_brownian_rectangle_pairing
