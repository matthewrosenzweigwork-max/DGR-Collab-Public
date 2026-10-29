import DGRHS.Commutator.SourceRieszBrownianElementaryAE
import DGRHS.Commutator.SourceRieszBrownianElementaryProcess

/-!
AE-continuous maximal estimates on the supplied filtration. The dense-time
argument identifies the maximal event only almost everywhere; no completion
of the filtration or time-zero null-set premise is used. The elementary
process is the identical frozen raw assembly.

Copyright (c) 2025 Rémy Degenne and Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the preserved LICENSE.
The two elementary submartingale helpers adapt the same pinned sources
attributed in SourceRieszBrownianMaximal. The norm-tail deduction retains
Raphael Coelho's Apache-2.0 provenance recorded in
SourceRieszBrownianElementaryProcess. No unfinished upstream assertion is used.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Finset Function TopologicalSpace
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {ι Ω : Type*} [LinearOrder ι] {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}

private lemma submartingale_indexComap {Y : ι→Ω→ℝ} (hY : Submartingale Y F P)
    {ι' : Type*} [Preorder ι'] {f : ι'→ι} (hf : Monotone f) :
    Submartingale (Y ∘ f) (sourceRieszFiltrationIndexComap F hf) P :=
  ⟨fun i=>hY.stronglyAdapted (f i),fun _ _ hij=>hY.ae_le_condExp (hf hij),
    fun i=>hY.integrable (f i)⟩

private lemma martingale_norm {X : ι→Ω→ℝ} (hX : Martingale X F P) :
    Submartingale (fun t ω=>‖X t ω‖) F P := by
  refine ⟨fun i=>continuous_norm.comp_stronglyMeasurable (hX.stronglyAdapted i),?_,
    fun i=>(hX.integrable i).norm⟩
  intro i j hij
  calc
    _ =ᵐ[P] fun ω=>‖(P[X j | F i]) ω‖ := (hX.condExp_ae_eq hij).fun_comp norm |>.symm
    _ ≤ᵐ[P] P[fun ω=>‖X j ω‖ | F i] :=
      convexOn_univ_norm.map_condExp_le_univ (F.le i) continuous_norm.lowerSemicontinuous
        (hX.integrable j) (hX.integrable j).norm

/-- Continuous-time strict-tail bound, proved by a countable dense set. -/
theorem sourceRiesz_martingale_ae_continuous_maximal
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0→Ω→ℝ} (hX : Martingale X F P)
    (hc : ∀ᵐ ω ∂P,Continuous (fun t=>X t ω)) (T : ℝ≥0) {ε : ℝ} (hε : 0<ε) :
    P {ω | ∃ t, t≤T ∧ ε<‖X t ω‖} ≤ ENNReal.ofReal (ε⁻¹*(∫ ω,‖X T ω‖ ∂P)) := by
  obtain ⟨D,hDc,hDd⟩ := TopologicalSpace.exists_countable_dense (Iic T)
  let S : Set (Iic T) := insert ⟨T,by simp⟩ D
  have hSc : S.Countable := hDc.insert _
  letI : Countable S := hSc.to_subtype
  let topS : S := ⟨⟨T,by simp⟩,mem_insert _ _⟩
  have hS : Dense S := hDd.mono (subset_insert _ _)
  have hm : Monotone (fun s:S=>(s.val:ℝ≥0)) := fun _ _ h=>h
  have he : {ω | ∃ t,t≤T ∧ ε<‖X t ω‖}=ᵐ[P]
      {ω | ∃ s:S,s≤topS ∧ ε<‖X s.val ω‖} := by
    filter_upwards [hc] with ω hω
    apply propext
    change (∃ t,t≤T ∧ ε<‖X t ω‖) ↔ (∃ s:S,s≤topS ∧ ε<‖X s.val ω‖)
    constructor
    · rintro ⟨t,ht,h⟩
      have hcont : Continuous (fun s:Iic T=>‖X s ω‖) := hω.norm.comp continuous_subtype_val
      obtain ⟨s,hs,hval⟩ := hS.exists_mem_open (isOpen_lt continuous_const hcont) ⟨⟨t,ht⟩,h⟩
      exact ⟨⟨s,hs⟩,s.property,hval⟩
    · rintro ⟨s,hs,h⟩
      exact ⟨s.val,s.val.property,h⟩
  rw [measure_congr he]
  exact sourceRiesz_submartingale_countable_maximal
    (submartingale_indexComap (martingale_norm hX) hm) (fun _ _=>norm_nonneg _) topS hε

variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
variable (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
variable (hind : ∀ s t,s≤t →
  Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)
variable (hBc : ∀ᵐ ω ∂P,Continuous (fun r=>B r ω))

include hBc in
lemma sourceRieszBrownianElementaryProcess_ae_continuous (c : SourceRieszBrownianAtom F T →₀ ℝ)
    : ∀ᵐ ω ∂P,Continuous (fun t=>sourceRieszBrownianElementaryProcess F T B c t ω) := by
  filter_upwards [hBc] with ω hω
  simp only [sourceRieszBrownianElementaryProcess_apply]
  apply continuous_finset_sum _ fun A _=>?_
  exact continuous_const.mul ((hω.comp (continuous_id.min continuous_const)).sub
    (hω.comp (continuous_id.min continuous_const)))

lemma sourceRieszBrownianElementaryProcess_ae_no_continuity (c : SourceRieszBrownianAtom F T →₀ ℝ) (t : ℝ≥0) :
    (sourceRieszBrownianProcessL2 P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c) t : Ω→ℝ)
      =ᵐ[P] sourceRieszBrownianElementaryProcess F T B c t := by
  exact (sourceRieszBrownianProcessL2_coe P F T B hB hBa hind _ t).trans
    ((sourceRieszBrownianProcess_elementary_no_continuity P F T B hB hBa hind c t).trans
      (ae_of_all _ fun ω=>(sourceRieszBrownianElementaryProcess_apply F T B c t ω).symm))

include hB hBa hind in
theorem sourceRieszBrownianElementaryProcess_martingale_no_continuity (c : SourceRieszBrownianAtom F T →₀ ℝ) :
    Martingale (sourceRieszBrownianElementaryProcess F T B c) F P ∧
      ∀ t,MemLp (sourceRieszBrownianElementaryProcess F T B c t) 2 P := by
  have hs (A : SourceRieszBrownianAtom F T) :=
    sourceRiesz_brownian_elementary_martingale P F B hB hBa hind A.a A.b A.hab
      (fun ω=>c A*A.value ω) (stronglyMeasurable_const.mul A.value_measurable)
      ‖c A‖ (norm_nonneg _) (ae_of_all _ fun ω=>by
        rw [←Real.norm_eq_abs,norm_mul]
        simpa using mul_le_mul_of_nonneg_left (A.value_bound ω) (norm_nonneg (c A)))
  have ha : StronglyAdapted F (sourceRieszBrownianElementaryProcess F T B c) := by
    intro t
    have he : sourceRieszBrownianElementaryProcess F T B c t=
      fun ω=>∑ A∈c.support,(c A*A.value ω)*(B (min t A.b) ω-B (min t A.a) ω) :=
      funext (sourceRieszBrownianElementaryProcess_apply F T B c t)
    rw [he]
    have hsum : (fun ω=>∑ A∈c.support,(c A*A.value ω)*(B (min t A.b) ω-B (min t A.a) ω))=
        ∑ A∈c.support,(fun ω=>(c A*A.value ω)*(B (min t A.b) ω-B (min t A.a) ω)) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [hsum]
    exact Finset.stronglyMeasurable_sum c.support fun A _=>(hs A).1.stronglyAdapted t
  have hm := sourceRieszBrownianProcess_martingale P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c)
  refine ⟨hm.1.congr ha (fun t=>?_),fun t=>?_⟩
  · exact (sourceRieszBrownianProcessL2_coe P F T B hB hBa hind _ t).symm.trans
      (sourceRieszBrownianElementaryProcess_ae_no_continuity P F T B hB hBa hind c t)
  · exact (memLp_congr_ae (sourceRieszBrownianElementaryProcess_ae_no_continuity P F T B hB hBa hind c t)).mp (Lp.memLp _)

include hB hBa hind hBc in
theorem sourceRieszBrownianElementaryProcess_ae_maximal (c : SourceRieszBrownianAtom F T →₀ ℝ)
    {ε : ℝ} (hε : 0<ε) :
    P {ω | ∃ t,t≤T ∧ ε<‖sourceRieszBrownianElementaryProcess F T B c t ω‖} ≤
      ENNReal.ofReal (ε⁻¹*‖sourceRieszBrownianAtomAssembly P F T c‖) := by
  have hm := sourceRieszBrownianElementaryProcess_martingale_no_continuity P F T B hB hBa hind c
  refine (sourceRiesz_martingale_ae_continuous_maximal hm.1
    (sourceRieszBrownianElementaryProcess_ae_continuous P F T B hBc c) T hε).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hε.le)
  let I := sourceRieszBrownianIntegral P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c)
  have he : (I : Ω→ℝ)=ᵐ[P] sourceRieszBrownianElementaryProcess F T B c T := by
    have hh := sourceRieszBrownianElementaryProcess_ae_no_continuity P F T B hB hBa hind c T
    rwa [sourceRieszBrownianProcessL2_terminal_no_continuity P F T B hB hBa hind] at hh
  have he' := integral_congr_ae (he.fun_comp norm)
  simp only [Function.comp_apply] at he'
  rw [←he',←sourceRieszBrownianIntegral_norm P F T B hB hBa hind]
  change (∫ ω,‖I ω‖ ∂P)≤‖I‖
  rw [Lp.norm_def,←ENNReal.toReal_ofReal (integral_nonneg (fun ω=>norm_nonneg (I ω))),
    ofReal_integral_norm_eq_lintegral_enorm ((Lp.memLp I).integrable one_le_two),
    ←eLpNorm_one_eq_lintegral_enorm]
  exact ENNReal.toReal_mono (Lp.eLpNorm_lt_top I).ne
    (eLpNorm_le_eLpNorm_of_exponent_le one_le_two)
  exact (Lp.memLp I).aestronglyMeasurable

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_martingale_ae_continuous_maximal
#print axioms DGRHS.Commutator.sourceRiesz_martingale_ae_continuous_maximal
#check @DGRHS.Commutator.sourceRieszBrownianElementaryProcess_ae_continuous
#print axioms DGRHS.Commutator.sourceRieszBrownianElementaryProcess_ae_continuous
#check @DGRHS.Commutator.sourceRieszBrownianElementaryProcess_ae_no_continuity
#print axioms DGRHS.Commutator.sourceRieszBrownianElementaryProcess_ae_no_continuity
#check @DGRHS.Commutator.sourceRieszBrownianElementaryProcess_martingale_no_continuity
#print axioms DGRHS.Commutator.sourceRieszBrownianElementaryProcess_martingale_no_continuity
#check @DGRHS.Commutator.sourceRieszBrownianElementaryProcess_ae_maximal
#print axioms DGRHS.Commutator.sourceRieszBrownianElementaryProcess_ae_maximal
