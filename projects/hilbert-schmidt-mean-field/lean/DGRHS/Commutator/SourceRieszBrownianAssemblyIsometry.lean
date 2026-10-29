/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the preserved MathFin LICENSE.
Authors: Raphael Coelho
DGR adaptation by Codex: direct Finsupp rectangle assembly in a supplied full
filtration, consuming the independently proved finite Brownian isometry.
-/
import DGRHS.Commutator.SourceRieszBrownianDensity
import DGRHS.Commutator.SourceRieszBrownianFiniteIsometry

/-! Selected L2 assembly argument adapted from MathFin/Foundations/ItoIntegralL2.lean
and ItoIntegralCLM.lean, revision f085fd572075c934827f1eb92c4a085941cd21e5.
No favorable norm identity is assumed. The native predictable domain is finite
horizon; the concrete Brownian sums use precisely the same driver. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal InnerProductSpace
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma sourceRiesz_L2_norm_sq {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    (g : Lp ℝ 2 μ) : ‖g‖^2=∫ x,(g x)^2 ∂μ := by
  have h : ⟪g,g⟫_ℝ=‖g‖^2 := real_inner_self_eq_norm_sq g
  rw [L2.inner_def] at h
  rw [←h]
  apply integral_congr_ae
  filter_upwards with x
  change g x*g x=(g x)^2
  ring

variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)

lemma sourceRieszBrownianAtomRawAssembly_predictable (c : SourceRieszBrownianAtom F T →₀ ℝ) :
    StronglyMeasurable[F.predictable] (sourceRieszBrownianAtomRawAssembly F T c) := by
  have he : sourceRieszBrownianAtomRawAssembly F T c=
      fun p=>∑ A∈c.support,c A*A.integrand p := funext (sourceRieszBrownianAtomRawAssembly_apply F T c)
  rw [he]
  apply Measurable.stronglyMeasurable
  exact Finset.measurable_sum _ fun A _=>measurable_const.mul A.predictable.measurable

lemma sourceRieszBrownianAtomRawAssembly_support (c : SourceRieszBrownianAtom F T →₀ ℝ)
    (p : ℝ≥0×Ω) (hp : p.1∉Ioc 0 T) : sourceRieszBrownianAtomRawAssembly F T c p=0 := by
  rw [sourceRieszBrownianAtomRawAssembly_apply]
  exact Finset.sum_eq_zero fun A _=>by rw [A.support_horizon p hp,mul_zero]

lemma sourceRieszBrownianAtomAssembly_norm_sq (c : SourceRieszBrownianAtom F T →₀ ℝ) :
    ‖sourceRieszBrownianAtomAssembly P F T c‖^2=
      ∫ p,(sourceRieszBrownianAtomRawAssembly F T c p)^2 ∂sourceRieszBrownianTime.prod P := by
  rw [sourceRiesz_L2_norm_sq]
  have he : (fun p=>(sourceRieszBrownianAtomAssembly P F T c p)^2)
      =ᵐ[sourceRieszBrownianPredictableMeasure P F T]
        fun p=>(sourceRieszBrownianAtomRawAssembly F T c p)^2 := by
    filter_upwards [sourceRieszBrownianAtomAssembly_coe P F T c] with p hp
    rw [hp]
  rw [integral_congr_ae he]
  have hm : StronglyMeasurable[F.predictable]
      (fun p=>(sourceRieszBrownianAtomRawAssembly F T c p)^2) :=
    (sourceRieszBrownianAtomRawAssembly_predictable F T c).pow 2
  rw [sourceRieszBrownianPredictableMeasure,←integral_trim (sourceRiesz_predictable_le_product F) hm,
    sourceRieszBrownianTimeOn,Measure.restrict_prod_eq_prod_univ,
    ←integral_indicator (measurableSet_Ioc.prod (MeasurableSet.univ : MeasurableSet (univ : Set Ω)))]
  apply integral_congr_ae
  filter_upwards with p
  by_cases hp : p.1∈Ioc 0 T
  · exact indicator_of_mem (show p∈Ioc 0 T ×ˢ (univ : Set Ω) from ⟨hp,mem_univ _⟩) _
  · rw [indicator_of_notMem (show p∉Ioc 0 T ×ˢ (univ : Set Ω) from fun h=>hp h.1),
      sourceRieszBrownianAtomRawAssembly_support F T c p hp]
    norm_num

def sourceRieszBrownianItoRawAssembly (B : ℝ≥0→Ω→ℝ) :
    (SourceRieszBrownianAtom F T →₀ ℝ) →ₗ[ℝ] (Ω→ℝ) :=
  Finsupp.linearCombination ℝ (fun A ω=>A.value ω*(B A.b ω-B A.a ω))

lemma sourceRieszBrownianItoRawAssembly_apply (B : ℝ≥0→Ω→ℝ)
    (c : SourceRieszBrownianAtom F T →₀ ℝ) (ω : Ω) :
    sourceRieszBrownianItoRawAssembly F T B c ω=
      ∑ A∈c.support,(c A*A.value ω)*(B A.b ω-B A.a ω) := by
  simp [sourceRieszBrownianItoRawAssembly,Finsupp.linearCombination_apply,Finsupp.sum,mul_assoc]

variable (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
variable (hind : ∀ s t,s≤t →
  Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)

include hB hBa hind in
lemma sourceRieszBrownianItoRawAssembly_isometry (c : SourceRieszBrownianAtom F T →₀ ℝ) :
    MemLp (sourceRieszBrownianItoRawAssembly F T B c) 2 P ∧
      (∫ ω,(sourceRieszBrownianItoRawAssembly F T B c ω)^2 ∂P)=
        ∫ p,(sourceRieszBrownianAtomRawAssembly F T c p)^2 ∂sourceRieszBrownianTime.prod P := by
  let H := fun (A : SourceRieszBrownianAtom F T) ω=>c A*A.value ω
  have hH (A : SourceRieszBrownianAtom F T) : StronglyMeasurable[F A.a] (H A) :=
    stronglyMeasurable_const.mul A.value_measurable
  have hb (A : SourceRieszBrownianAtom F T) (ω : Ω) : ‖H A ω‖≤(‖c A‖₊ : ℝ) := by
    dsimp only [H]
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_left (A.value_bound ω) (norm_nonneg (c A))
  have hi := sourceRiesz_brownian_finite_isometry P F B hB hBa hind c.support
    (fun A=>A.a) (fun A=>A.b) (fun A _=>A.hab) H (fun A _=>hH A)
    (fun A=>‖c A‖₊) (fun A _=>hb A)
  have hI : sourceRieszBrownianItoRawAssembly F T B c=
      fun ω=>∑ A∈c.support,H A ω*(B A.b ω-B A.a ω) :=
    funext (sourceRieszBrownianItoRawAssembly_apply F T B c)
  have hV : sourceRieszBrownianAtomRawAssembly F T c=
      fun p=>∑ A∈c.support,sourceRieszBrownianBand A.a A.b (H A) p := by
    funext p
    rw [sourceRieszBrownianAtomRawAssembly_apply]
    apply Finset.sum_congr rfl
    intro A _
    dsimp [SourceRieszBrownianAtom.integrand,sourceRieszBrownianBand,H]
    ring
  rw [hI,hV]
  exact ⟨hi.1,hi.2.2.2⟩

def sourceRieszBrownianItoAssembly : (SourceRieszBrownianAtom F T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 P where
  toFun c := (sourceRieszBrownianItoRawAssembly_isometry P F T B hB hBa hind c).1.toLp _
  map_add' c d := by
    rw [←MemLp.toLp_add (sourceRieszBrownianItoRawAssembly_isometry P F T B hB hBa hind c).1
      (sourceRieszBrownianItoRawAssembly_isometry P F T B hB hBa hind d).1]
    congr 1
    exact map_add (sourceRieszBrownianItoRawAssembly F T B) c d
  map_smul' r c := by
    simp only [RingHom.id_apply]
    rw [←MemLp.toLp_const_smul r (sourceRieszBrownianItoRawAssembly_isometry P F T B hB hBa hind c).1]
    congr 1
    exact map_smul (sourceRieszBrownianItoRawAssembly F T B) r c

lemma sourceRieszBrownianItoAssembly_coe (c : SourceRieszBrownianAtom F T →₀ ℝ) :
    (sourceRieszBrownianItoAssembly P F T B hB hBa hind c : Ω→ℝ)
      =ᵐ[P] sourceRieszBrownianItoRawAssembly F T B c :=
  (sourceRieszBrownianItoRawAssembly_isometry P F T B hB hBa hind c).1.coeFn_toLp

theorem sourceRieszBrownianAssembly_isometry (c : SourceRieszBrownianAtom F T →₀ ℝ) :
    ‖sourceRieszBrownianItoAssembly P F T B hB hBa hind c‖=
      ‖sourceRieszBrownianAtomAssembly P F T c‖ := by
  have he : ‖sourceRieszBrownianItoAssembly P F T B hB hBa hind c‖^2=
      ‖sourceRieszBrownianAtomAssembly P F T c‖^2 := by
    rw [sourceRiesz_L2_norm_sq,sourceRieszBrownianAtomAssembly_norm_sq]
    have ha : (fun ω=>(sourceRieszBrownianItoAssembly P F T B hB hBa hind c ω)^2)
        =ᵐ[P] fun ω=>(sourceRieszBrownianItoRawAssembly F T B c ω)^2 := by
      filter_upwards [sourceRieszBrownianItoAssembly_coe P F T B hB hBa hind c] with ω hω
      rw [hω]
    rw [integral_congr_ae ha]
    exact (sourceRieszBrownianItoRawAssembly_isometry P F T B hB hBa hind c).2
  nlinarith [norm_nonneg (sourceRieszBrownianItoAssembly P F T B hB hBa hind c),
    norm_nonneg (sourceRieszBrownianAtomAssembly P F T c)]

end DGRHS.Commutator

#check @DGRHS.Commutator.sourceRiesz_L2_norm_sq
#print axioms DGRHS.Commutator.sourceRiesz_L2_norm_sq

#check @DGRHS.Commutator.sourceRieszBrownianAtomRawAssembly_predictable
#print axioms DGRHS.Commutator.sourceRieszBrownianAtomRawAssembly_predictable

#check @DGRHS.Commutator.sourceRieszBrownianAtomRawAssembly_support
#print axioms DGRHS.Commutator.sourceRieszBrownianAtomRawAssembly_support

#check @DGRHS.Commutator.sourceRieszBrownianAtomAssembly_norm_sq
#print axioms DGRHS.Commutator.sourceRieszBrownianAtomAssembly_norm_sq

#check @DGRHS.Commutator.sourceRieszBrownianItoRawAssembly
#print axioms DGRHS.Commutator.sourceRieszBrownianItoRawAssembly

#check @DGRHS.Commutator.sourceRieszBrownianItoRawAssembly_apply
#print axioms DGRHS.Commutator.sourceRieszBrownianItoRawAssembly_apply

#check @DGRHS.Commutator.sourceRieszBrownianItoRawAssembly_isometry
#print axioms DGRHS.Commutator.sourceRieszBrownianItoRawAssembly_isometry

#check @DGRHS.Commutator.sourceRieszBrownianItoAssembly
#print axioms DGRHS.Commutator.sourceRieszBrownianItoAssembly

#check @DGRHS.Commutator.sourceRieszBrownianItoAssembly_coe
#print axioms DGRHS.Commutator.sourceRieszBrownianItoAssembly_coe

#check @DGRHS.Commutator.sourceRieszBrownianAssembly_isometry
#print axioms DGRHS.Commutator.sourceRieszBrownianAssembly_isometry
