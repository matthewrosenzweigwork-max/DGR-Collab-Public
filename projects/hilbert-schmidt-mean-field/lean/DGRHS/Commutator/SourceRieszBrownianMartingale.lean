/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the preserved MathFin LICENSE.
Authors: Raphael Coelho
DGR adaptation by Codex: native conditional-expectation process relative to the
supplied full filtration, identified with actual elementary Brownian sums.
-/
import DGRHS.Commutator.SourceRieszBrownianIntegral
import DGRHS.Commutator.SourceRieszBrownianStepMartingale

/-! The time-indexed L2 martingale of the constructed Brownian integral. Selected
conditional projection/density strategy from MathFin ItoIntegralProcessGeneral.lean,
revision f085fd572075c934827f1eb92c4a085941cd21e5, preserved with its license.
The process is strongly adapted by its native conditional-expectation representative.
Continuity of a modification is a separate, not assumed, next obligation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
variable (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
variable (hind : ∀ s t,s≤t →
  Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)

def sourceRieszBrownianProcessL2 (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (t : ℝ≥0) : Lp ℝ 2 P :=
  condExpL2 ℝ ℝ (F.le t) (sourceRieszBrownianIntegral P F T B hB hBa hind g)

def sourceRieszBrownianProcess (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (t : ℝ≥0) : Ω→ℝ := P[(sourceRieszBrownianIntegral P F T B hB hBa hind g : Ω→ℝ) | F t]

lemma sourceRieszBrownianProcessL2_coe (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (t : ℝ≥0) : (sourceRieszBrownianProcessL2 P F T B hB hBa hind g t : Ω→ℝ)
      =ᵐ[P] sourceRieszBrownianProcess P F T B hB hBa hind g t := by
  have h := (Lp.memLp (sourceRieszBrownianIntegral P F T B hB hBa hind g)).condExpL2_ae_eq_condExp
    (𝕜:=ℝ) (F.le t)
  rwa [Lp.toLp_coeFn] at h

lemma sourceRieszBrownianProcessL2_continuous (t : ℝ≥0) :
    Continuous (fun g=>sourceRieszBrownianProcessL2 P F T B hB hBa hind g t) :=
  (continuous_subtype_val.comp (condExpL2 ℝ ℝ (F.le t)).continuous).comp
    (sourceRieszBrownianIntegral P F T B hB hBa hind).continuous

lemma sourceRieszBrownianProcessL2_norm_le (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (t : ℝ≥0) : ‖sourceRieszBrownianProcessL2 P F T B hB hBa hind g t‖≤‖g‖ := by
  exact (norm_condExpL2_coe_le (F.le t) _).trans_eq (sourceRieszBrownianIntegral_norm P F T B hB hBa hind g)

theorem sourceRieszBrownianProcess_martingale (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    Martingale (sourceRieszBrownianProcess P F T B hB hBa hind g) F P ∧
      ∀ t,MemLp (sourceRieszBrownianProcess P F T B hB hBa hind g t) 2 P := by
  refine ⟨martingale_condExp _ F P,?_⟩
  intro t
  exact (memLp_congr_ae (sourceRieszBrownianProcessL2_coe P F T B hB hBa hind g t)).mp
    (Lp.memLp (sourceRieszBrownianProcessL2 P F T B hB hBa hind g t))

variable (hBc : ∀ ω,Continuous (fun r=>B r ω))
include hB hBa hind hBc in
lemma sourceRieszBrownianItoRawAssembly_projection (c : SourceRieszBrownianAtom F T →₀ ℝ)
    (t : ℝ≥0) : P[sourceRieszBrownianItoRawAssembly F T B c | F t]=ᵐ[P]
      fun ω=>∑ A∈c.support,(c A*A.value ω)*(B (min t A.b) ω-B (min t A.a) ω) := by
  let U := fun (A : SourceRieszBrownianAtom F T) ω=>(c A*A.value ω)*(B A.b ω-B A.a ω)
  let V := fun (A : SourceRieszBrownianAtom F T) (r : ℝ≥0) ω=>
    (c A*A.value ω)*(B (min r A.b) ω-B (min r A.a) ω)
  have hs (A : SourceRieszBrownianAtom F T) :=
    sourceRiesz_brownian_elementary_integral P F B hB hBa hBc hind A.a A.b A.hab
      (fun ω=>c A*A.value ω) (stronglyMeasurable_const.mul A.value_measurable)
      ‖c A‖ (norm_nonneg _) (ae_of_all _ fun ω=>by
        rw [←Real.norm_eq_abs,norm_mul]
        simpa using mul_le_mul_of_nonneg_left (A.value_bound ω) (norm_nonneg (c A)))
  have hterminal (A : SourceRieszBrownianAtom F T) : V A (max t A.b)=U A := by
    funext ω
    dsimp only [V,U]
    rw [min_eq_right (le_max_right t A.b),
      min_eq_right (A.hab.trans (le_max_right t A.b))]
  have hi (A : SourceRieszBrownianAtom F T) : Integrable (U A) P := by
    rw [←hterminal A]
    exact ((hs A).2.1 _).integrable one_le_two
  have hp (A : SourceRieszBrownianAtom F T) : P[U A | F t]=ᵐ[P] V A t := by
    rw [←hterminal A]
    exact (hs A).1.2 t (max t A.b) (le_max_left t A.b)
  have hall (S : Finset (SourceRieszBrownianAtom F T)) :
      P[∑ A∈S,U A | F t]=ᵐ[P] ∑ A∈S,V A t := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | insert A S hAS ih =>
      rw [Finset.sum_insert hAS,Finset.sum_insert hAS]
      exact (condExp_add (hi A) (integrable_finsetSum' S (fun A _=>hi A)) (F t)).trans ((hp A).add ih)
  have he : sourceRieszBrownianItoRawAssembly F T B c=∑ A∈c.support,U A := by
    funext ω
    simpa only [Finset.sum_apply] using sourceRieszBrownianItoRawAssembly_apply F T B c ω
  rw [he]
  exact (hall c.support).trans (ae_of_all _ fun ω=>by simp only [Finset.sum_apply,V])

include hBc in
lemma sourceRieszBrownianProcess_elementary (c : SourceRieszBrownianAtom F T →₀ ℝ) (t : ℝ≥0) :
    sourceRieszBrownianProcess P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c) t
      =ᵐ[P] fun ω=>∑ A∈c.support,(c A*A.value ω)*(B (min t A.b) ω-B (min t A.a) ω) := by
  apply (condExp_congr_ae (sourceRieszBrownianIntegral_elementary_coe P F T B hB hBa hind c)).trans
  have he : (fun ω=>∑ A∈c.support,(c A*A.value ω)*(B A.b ω-B A.a ω))=
      sourceRieszBrownianItoRawAssembly F T B c :=
    (funext (sourceRieszBrownianItoRawAssembly_apply F T B c)).symm
  rw [he]
  exact sourceRieszBrownianItoRawAssembly_projection P F T B hB hBa hind hBc c t

include hBc in
lemma sourceRieszBrownianProcessL2_terminal (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    sourceRieszBrownianProcessL2 P F T B hB hBa hind g T=
      sourceRieszBrownianIntegral P F T B hB hBa hind g := by
  apply congrFun (DenseRange.equalizer (sourceRieszBrownianAtomAssembly_dense P F T)
    (sourceRieszBrownianProcessL2_continuous P F T B hB hBa hind T)
    (sourceRieszBrownianIntegral P F T B hB hBa hind).continuous (funext fun c=>?_)) g
  simp only [Function.comp_apply]
  apply Lp.ext
  filter_upwards [sourceRieszBrownianProcessL2_coe P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c) T,
    sourceRieszBrownianProcess_elementary P F T B hB hBa hind hBc c T,
    sourceRieszBrownianIntegral_elementary_coe P F T B hB hBa hind c] with ω h1 h2 h3
  rw [h1,h2,h3]
  apply Finset.sum_congr rfl
  intro A _
  rw [min_eq_right A.hbT,min_eq_right (A.hab.trans A.hbT)]

include hBc in
lemma sourceRieszBrownianProcessL2_zero (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    sourceRieszBrownianProcessL2 P F T B hB hBa hind g 0=0 := by
  apply congrFun (DenseRange.equalizer (sourceRieszBrownianAtomAssembly_dense P F T)
    (sourceRieszBrownianProcessL2_continuous P F T B hB hBa hind 0)
    continuous_const (funext fun c=>?_)) g
  simp only [Function.comp_apply]
  apply Lp.ext
  filter_upwards [sourceRieszBrownianProcessL2_coe P F T B hB hBa hind (sourceRieszBrownianAtomAssembly P F T c) 0,
    sourceRieszBrownianProcess_elementary P F T B hB hBa hind hBc c 0,Lp.coeFn_zero (E:=ℝ) (p:=2) (μ:=P)] with ω h1 h2 h3
  simp only [h1,h2,h3,min_eq_left (show (0:ℝ≥0)≤_ from bot_le),sub_self,mul_zero,Finset.sum_const_zero,Pi.zero_apply]

end DGRHS.Commutator

#check @DGRHS.Commutator.sourceRieszBrownianProcessL2
#print axioms DGRHS.Commutator.sourceRieszBrownianProcessL2

#check @DGRHS.Commutator.sourceRieszBrownianProcess
#print axioms DGRHS.Commutator.sourceRieszBrownianProcess

#check @DGRHS.Commutator.sourceRieszBrownianProcessL2_coe
#print axioms DGRHS.Commutator.sourceRieszBrownianProcessL2_coe

#check @DGRHS.Commutator.sourceRieszBrownianProcessL2_continuous
#print axioms DGRHS.Commutator.sourceRieszBrownianProcessL2_continuous

#check @DGRHS.Commutator.sourceRieszBrownianProcessL2_norm_le
#print axioms DGRHS.Commutator.sourceRieszBrownianProcessL2_norm_le

#check @DGRHS.Commutator.sourceRieszBrownianProcess_martingale
#print axioms DGRHS.Commutator.sourceRieszBrownianProcess_martingale

#check @DGRHS.Commutator.sourceRieszBrownianItoRawAssembly_projection
#print axioms DGRHS.Commutator.sourceRieszBrownianItoRawAssembly_projection

#check @DGRHS.Commutator.sourceRieszBrownianProcess_elementary
#print axioms DGRHS.Commutator.sourceRieszBrownianProcess_elementary

#check @DGRHS.Commutator.sourceRieszBrownianProcessL2_terminal
#print axioms DGRHS.Commutator.sourceRieszBrownianProcessL2_terminal

#check @DGRHS.Commutator.sourceRieszBrownianProcessL2_zero
#print axioms DGRHS.Commutator.sourceRieszBrownianProcessL2_zero
