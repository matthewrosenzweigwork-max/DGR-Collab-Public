/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the preserved MathFin LICENSE.
Authors: Raphael Coelho
DGR adaptation by Codex: arbitrary supplied full filtration and explicit finite
families, consuming actual product-L2 bands and the checked rectangle pairing.
-/
import DGRHS.Commutator.SourceRieszBrownianRectangleIsometry
import DGRHS.Commutator.SourceRieszBrownianTime

/-! The finite elementary Ito isometry, including proper integrability on both
sides. Adaptation of the finite-sum assembly argument in the preserved
MathFin/Foundations/ItoIntegralL2.lean at f085fd572075c934827f1eb92c4a085941cd21e5.
No favorable norm identity is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma sourceRiesz_integral_finset_sum_sq {κ : Type*} (P : Measure Ω)
    (S : Finset κ) (f : κ→Ω→ℝ) (hf : ∀ i∈S,MemLp (f i) 2 P) :
    (∫ ω,(∑ i∈S,f i ω)^2 ∂P)=∑ i∈S,∑ j∈S,∫ ω,f i ω*f j ω ∂P := by
  have hi (i) (hi : i∈S) (j) (hj : j∈S) : Integrable (fun ω=>f i ω*f j ω) P :=
    (hf i hi).integrable_mul (hf j hj)
  have he (ω) : (∑ i∈S,f i ω)^2=∑ i∈S,∑ j∈S,f i ω*f j ω := by
    rw [pow_two,Finset.sum_mul_sum]
  simp_rw [he]
  rw [integral_finsetSum _ (fun i hiS=>integrable_finsetSum _ fun j hjS=>hi i hiS j hjS)]
  exact Finset.sum_congr rfl fun i hiS=>integral_finsetSum _ fun j hjS=>hi i hiS j hjS

theorem sourceRiesz_brownian_finite_isometry {κ : Type*}
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
    (hind : ∀ s t,s≤t →
      Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)
    (S : Finset κ) (a b : κ→ℝ≥0) (hab : ∀ i∈S,a i≤b i)
    (H : κ→Ω→ℝ) (hH : ∀ i∈S,StronglyMeasurable[F (a i)] (H i))
    (K : κ→ℝ≥0) (hb : ∀ i∈S,∀ ω,‖H i ω‖≤(K i:ℝ)) :
    let I := fun ω=>∑ i∈S,H i ω*(B (b i) ω-B (a i) ω)
    let Φ := fun p=>∑ i∈S,sourceRieszBrownianBand (a i) (b i) (H i) p
    MemLp I 2 P ∧ MemLp Φ 2 (sourceRieszBrownianTime.prod P) ∧
      StronglyMeasurable[F.predictable] Φ ∧
      (∫ ω,(I ω)^2 ∂P)=∫ p,(Φ p)^2 ∂sourceRieszBrownianTime.prod P := by
  dsimp only
  let U := fun i ω=>H i ω*(B (b i) ω-B (a i) ω)
  let V := fun i=>sourceRieszBrownianBand (a i) (b i) (H i)
  have hUL (i) (hi : i∈S) : MemLp (U i) 2 P :=
    sourceRiesz_memLp_bounded_mul P (H i) _ ((hH i hi).mono (F.le (a i))).aestronglyMeasurable
      (hB.hasLaw_sub (b i) (a i)).hasGaussianLaw.memLp_two (K i) (ae_of_all _ (hb i hi))
  have hVL (i) (hi : i∈S) : MemLp (V i) 2 (sourceRieszBrownianTime.prod P) :=
    sourceRieszBrownianBand_memLp P (a i) (b i) (H i) ((hH i hi).mono (F.le (a i))) (K i) (hb i hi)
  have hVp (i) (hi : i∈S) : StronglyMeasurable[F.predictable] (V i) :=
    sourceRieszBrownianBand_predictable F (a i) (b i) (H i) (hH i hi)
  refine ⟨memLp_finsetSum S hUL,memLp_finsetSum S hVL,?_,?_⟩
  · apply Measurable.stronglyMeasurable
    apply Finset.measurable_sum
    intro i hi
    exact (hVp i hi).measurable
  · change (∫ ω,(∑ i∈S,U i ω)^2 ∂P)=∫ p,(∑ i∈S,V i p)^2 ∂sourceRieszBrownianTime.prod P
    rw [sourceRiesz_integral_finset_sum_sq P S U hUL,
      sourceRiesz_integral_finset_sum_sq (sourceRieszBrownianTime.prod P) S V hVL]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact (sourceRiesz_brownian_rectangle_pairing P F B hB hBa hind (a i) (b i) (a j) (b j)
      (hab i hi) (hab j hj) (H i) (H j) (hH i hi) (hH j hj) (K i) (K j)
      (ae_of_all _ (hb i hi)) (ae_of_all _ (hb j hj))).2.trans
        (sourceRieszBrownianBand_pairing P (a i) (b i) (a j) (b j) (H i) (H j)).symm

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_integral_finset_sum_sq
#print axioms DGRHS.Commutator.sourceRiesz_integral_finset_sum_sq
#check @DGRHS.Commutator.sourceRiesz_brownian_finite_isometry
#print axioms DGRHS.Commutator.sourceRiesz_brownian_finite_isometry
