/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the preserved MathFin LICENSE.
Authors: Raphael Coelho
DGR adaptation by Codex: full-filtration stopped finite sums and native L2
conditional-expectation process, without an assumed time-isometry identity.
-/
import DGRHS.Commutator.SourceRieszBrownianElementaryAE
import DGRHS.Commutator.SourceRieszBrownianTruncation

/-! Time-indexed actual Brownian isometry. The density/truncation strategy adapts
MathFin ItoIntegralProcessIsometry.lean at f085fd572075c934827f1eb92c4a085941cd21e5.
Inactive random coefficients are explicitly zeroed before their start time so
that the finite isometry is invoked with the correct earlier filtration. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)

private lemma trunc_raw_norm (c : SourceRieszBrownianAtom F T →₀ ℝ) (t : ℝ≥0) :
    ‖sourceRieszBrownianTruncation P F T t (sourceRieszBrownianAtomAssembly P F T c)‖^2=
      ∫ p,((Ioc 0 t ×ˢ (univ : Set Ω)).indicator (sourceRieszBrownianAtomRawAssembly F T c) p)^2
        ∂sourceRieszBrownianTime.prod P := by
  let u := (Ioc 0 t ×ˢ (univ : Set Ω)).indicator (sourceRieszBrownianAtomRawAssembly F T c)
  have hm : StronglyMeasurable[F.predictable] u :=
    (sourceRieszBrownianAtomRawAssembly_predictable F T c).indicator
      (measurableSet_predictable_Ioc_prod 0 t MeasurableSet.univ)
  rw [sourceRiesz_L2_norm_sq]
  have he : (fun p=>(sourceRieszBrownianTruncation P F T t (sourceRieszBrownianAtomAssembly P F T c) p)^2)
      =ᵐ[sourceRieszBrownianPredictableMeasure P F T] fun p=>(u p)^2 := by
    filter_upwards [sourceRieszBrownianTruncation_coe P F T t (sourceRieszBrownianAtomAssembly P F T c),
      sourceRieszBrownianAtomAssembly_coe P F T c] with p h1 h2
    rw [h1]
    by_cases hp : p∈Ioc 0 t ×ˢ (univ : Set Ω) <;> simp [u,hp,h2]
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
    by_cases ht : p∈Ioc 0 t ×ˢ (univ : Set Ω)
    · rw [indicator_of_mem ht,sourceRieszBrownianAtomRawAssembly_support F T c p hp]
      norm_num
    · rw [indicator_of_notMem ht]
      norm_num

variable (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
variable (hind : ∀ s t,s≤t →
  Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)

private lemma finite_time_isometry (c : SourceRieszBrownianAtom F T →₀ ℝ) (t : ℝ≥0) :
    ‖sourceRieszBrownianProcessL2 P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c) t‖^2=
      ‖sourceRieszBrownianTruncation P F T t (sourceRieszBrownianAtomAssembly P F T c)‖^2 := by
  let H := fun (A : SourceRieszBrownianAtom F T) ω=>if A.a≤t then c A*A.value ω else 0
  have hH (A : SourceRieszBrownianAtom F T) : StronglyMeasurable[F (min t A.a)] (H A) := by
    by_cases ha : A.a≤t
    · simp only [H,if_pos ha]
      exact stronglyMeasurable_const.mul (A.value_measurable.mono (F.mono (le_min ha le_rfl)))
    · simp only [H,if_neg ha]
      exact stronglyMeasurable_const
  have hb (A : SourceRieszBrownianAtom F T) (ω : Ω) : ‖H A ω‖≤(‖c A‖₊ : ℝ) := by
    dsimp only [H]
    split_ifs
    · rw [norm_mul]
      simpa using mul_le_mul_of_nonneg_left (A.value_bound ω) (norm_nonneg (c A))
    · simp
  have hi := sourceRiesz_brownian_finite_isometry P F B hB hBa hind c.support
    (fun A=>min t A.a) (fun A=>min t A.b) (fun A _=>min_le_min_left t A.hab) H
    (fun A _=>hH A) (fun A=>‖c A‖₊) (fun A _=>hb A)
  have hI (ω) : (∑ A∈c.support,H A ω*(B (min t A.b) ω-B (min t A.a) ω))=
      ∑ A∈c.support,(c A*A.value ω)*(B (min t A.b) ω-B (min t A.a) ω) := by
    apply Finset.sum_congr rfl
    intro A _
    by_cases ha : A.a≤t
    · simp [H,ha]
    · have ht : t≤A.a := le_of_not_ge ha
      simp [H,ha,min_eq_left ht,min_eq_left (ht.trans A.hab)]
  have hV (p : ℝ≥0×Ω) : (∑ A∈c.support,sourceRieszBrownianBand (min t A.a) (min t A.b) (H A) p)=
      (Ioc 0 t ×ˢ (univ : Set Ω)).indicator (sourceRieszBrownianAtomRawAssembly F T c) p := by
    by_cases ht : p.1∈Ioc 0 t
    · rw [indicator_of_mem (show p∈Ioc 0 t ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩),
        sourceRieszBrownianAtomRawAssembly_apply]
      apply Finset.sum_congr rfl
      intro A _
      by_cases hp : p.1∈Ioc A.a A.b
      · have ha : A.a≤t := hp.1.le.trans ht.2
        have hp' : p.1∈Ioc A.a (min t A.b) := ⟨hp.1,le_min ht.2 hp.2⟩
        simp [sourceRieszBrownianBand,sourceRieszBrownianBand_time_inter A.a A.b t A.hab,
          H,ha,hp,hp',ht,SourceRieszBrownianAtom.integrand]
      · simp [sourceRieszBrownianBand,sourceRieszBrownianBand_time_inter A.a A.b t A.hab,
          hp,SourceRieszBrownianAtom.integrand]
    · rw [indicator_of_notMem (show p∉Ioc 0 t ×ˢ (univ : Set Ω) from fun h=>ht h.1)]
      apply Finset.sum_eq_zero
      intro A _
      simp [sourceRieszBrownianBand,sourceRieszBrownianBand_time_inter A.a A.b t A.hab,ht]
  rw [sourceRiesz_L2_norm_sq,trunc_raw_norm P F T c t]
  have hproc := (sourceRieszBrownianProcessL2_coe P F T B hB hBa hind
    (sourceRieszBrownianAtomAssembly P F T c) t).trans
      (sourceRieszBrownianProcess_elementary_no_continuity P F T B hB hBa hind c t)
  have he : (fun ω=>(sourceRieszBrownianProcessL2 P F T B hB hBa hind
      (sourceRieszBrownianAtomAssembly P F T c) t ω)^2)=ᵐ[P]
      fun ω=>(∑ A∈c.support,H A ω*(B (min t A.b) ω-B (min t A.a) ω))^2 := by
    filter_upwards [hproc] with ω hω
    rw [hω,hI]
  rw [integral_congr_ae he]
  convert hi.2.2.2 using 1
  congr 1
  funext p
  exact congrArg (fun x : ℝ=>x^2) (hV p).symm

theorem sourceRieszBrownianProcessL2_norm_sq_no_continuity (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (t : ℝ≥0) : ‖sourceRieszBrownianProcessL2 P F T B hB hBa hind g t‖^2=
      ∫ p in Ioc 0 t ×ˢ (univ : Set Ω),(g p)^2 ∂sourceRieszBrownianPredictableMeasure P F T := by
  rw [←sourceRieszBrownianTruncation_norm_sq P F T t g]
  apply congrFun (DenseRange.equalizer (sourceRieszBrownianAtomAssembly_dense P F T)
    ((sourceRieszBrownianProcessL2_continuous P F T B hB hBa hind t).norm.pow 2)
    ((sourceRieszBrownianTruncation P F T t).continuous.norm.pow 2) (funext fun c=>?_)) g
  exact finite_time_isometry P F T B hB hBa hind c t

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianProcessL2_norm_sq_no_continuity
#print axioms DGRHS.Commutator.sourceRieszBrownianProcessL2_norm_sq_no_continuity
