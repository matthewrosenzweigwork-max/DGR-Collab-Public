import DGRHS.Commutator.SourceRieszBrownianMaximal

/-! Concrete continuous elementary Brownian integrals for the supplied full
filtration. The norm-tail deduction follows the proved weak-maximal argument
in Raphael Coelho's Apache-2.0 MathFin/Foundations/ItoIntegralProcessContinuousModification,
f085fd572075c934827f1eb92c4a085941cd21e5, with preserved source and license.
Here no upstream maximal theorem with unfinished dependencies is imported. -/
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

def sourceRieszBrownianElementaryProcess (c : SourceRieszBrownianAtom F T →₀ ℝ)
    (t : ℝ≥0) : Ω→ℝ := sourceRieszBrownianItoRawAssembly F T (fun s=>B (min t s)) c

lemma sourceRieszBrownianElementaryProcess_apply (c : SourceRieszBrownianAtom F T →₀ ℝ)
    (t : ℝ≥0) (ω : Ω) : sourceRieszBrownianElementaryProcess F T B c t ω=
      ∑ A∈c.support,(c A*A.value ω)*(B (min t A.b) ω-B (min t A.a) ω) :=
  sourceRieszBrownianItoRawAssembly_apply F T _ c ω

lemma sourceRieszBrownianElementaryProcess_sub (c d : SourceRieszBrownianAtom F T →₀ ℝ)
    (t : ℝ≥0) : sourceRieszBrownianElementaryProcess F T B (c-d) t=
      sourceRieszBrownianElementaryProcess F T B c t-sourceRieszBrownianElementaryProcess F T B d t :=
  map_sub (sourceRieszBrownianItoRawAssembly F T _) c d

include hBc in
lemma sourceRieszBrownianElementaryProcess_continuous (c : SourceRieszBrownianAtom F T →₀ ℝ)
    (ω : Ω) : Continuous (fun t=>sourceRieszBrownianElementaryProcess F T B c t ω) := by
  simp only [sourceRieszBrownianElementaryProcess_apply]
  apply continuous_finset_sum _ fun A _=>?_
  exact continuous_const.mul (((hBc ω).comp (continuous_id.min continuous_const)).sub
    ((hBc ω).comp (continuous_id.min continuous_const)))

include hBc in
lemma sourceRieszBrownianElementaryProcess_ae (c : SourceRieszBrownianAtom F T →₀ ℝ) (t : ℝ≥0) :
    (sourceRieszBrownianProcessL2 P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c) t : Ω→ℝ)
      =ᵐ[P] sourceRieszBrownianElementaryProcess F T B c t := by
  exact (sourceRieszBrownianProcessL2_coe P F T B hB hBa hind _ t).trans
    ((sourceRieszBrownianProcess_elementary P F T B hB hBa hind hBc c t).trans
      (ae_of_all _ fun ω=>(sourceRieszBrownianElementaryProcess_apply F T B c t ω).symm))

include hB hBa hind hBc in
theorem sourceRieszBrownianElementaryProcess_martingale (c : SourceRieszBrownianAtom F T →₀ ℝ) :
    Martingale (sourceRieszBrownianElementaryProcess F T B c) F P ∧
      ∀ t,MemLp (sourceRieszBrownianElementaryProcess F T B c t) 2 P := by
  have hs (A : SourceRieszBrownianAtom F T) :=
    sourceRiesz_brownian_elementary_integral P F B hB hBa hBc hind A.a A.b A.hab
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
      (sourceRieszBrownianElementaryProcess_ae P F T B hB hBa hind hBc c t)
  · exact (memLp_congr_ae (sourceRieszBrownianElementaryProcess_ae P F T B hB hBa hind hBc c t)).mp (Lp.memLp _)

include hB hBa hind hBc in
theorem sourceRieszBrownianElementaryProcess_maximal (c : SourceRieszBrownianAtom F T →₀ ℝ)
    {ε : ℝ} (hε : 0<ε) :
    P {ω | ∃ t,t≤T ∧ ε<‖sourceRieszBrownianElementaryProcess F T B c t ω‖} ≤
      ENNReal.ofReal (ε⁻¹*‖sourceRieszBrownianAtomAssembly P F T c‖) := by
  have hm := sourceRieszBrownianElementaryProcess_martingale P F T B hB hBa hind hBc c
  refine (sourceRiesz_martingale_continuous_maximal hm.1
    (sourceRieszBrownianElementaryProcess_continuous F T B hBc c) T hε).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hε.le)
  let I := sourceRieszBrownianIntegral P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c)
  have he : (I : Ω→ℝ)=ᵐ[P] sourceRieszBrownianElementaryProcess F T B c T := by
    have hh := sourceRieszBrownianElementaryProcess_ae P F T B hB hBa hind hBc c T
    rwa [sourceRieszBrownianProcessL2_terminal P F T B hB hBa hind hBc] at hh
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
#check @DGRHS.Commutator.sourceRieszBrownianElementaryProcess
#print axioms DGRHS.Commutator.sourceRieszBrownianElementaryProcess
#check @DGRHS.Commutator.sourceRieszBrownianElementaryProcess_apply
#print axioms DGRHS.Commutator.sourceRieszBrownianElementaryProcess_apply
#check @DGRHS.Commutator.sourceRieszBrownianElementaryProcess_sub
#print axioms DGRHS.Commutator.sourceRieszBrownianElementaryProcess_sub
#check @DGRHS.Commutator.sourceRieszBrownianElementaryProcess_continuous
#print axioms DGRHS.Commutator.sourceRieszBrownianElementaryProcess_continuous
#check @DGRHS.Commutator.sourceRieszBrownianElementaryProcess_ae
#print axioms DGRHS.Commutator.sourceRieszBrownianElementaryProcess_ae
#check @DGRHS.Commutator.sourceRieszBrownianElementaryProcess_martingale
#print axioms DGRHS.Commutator.sourceRieszBrownianElementaryProcess_martingale
#check @DGRHS.Commutator.sourceRieszBrownianElementaryProcess_maximal
#print axioms DGRHS.Commutator.sourceRieszBrownianElementaryProcess_maximal
