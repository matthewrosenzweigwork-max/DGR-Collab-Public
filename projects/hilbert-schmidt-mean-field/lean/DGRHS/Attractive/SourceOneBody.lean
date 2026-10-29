/- Development candidate. Source TeX2496–2531.
Pinned native finite Jensen and the already checked proper exponential CS are
reused. Actual canonical doubled moments remain an upstream obligation. -/
import DGRHS.CLT.SourceEnergyTilt
import DGRHS.Decoupling.Moment
import Mathlib.Analysis.Convex.Jensen
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.Attractive
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

lemma empirical_function_aemeasurable (F : S → ℝ) (hF : AEMeasurable F μ) (N : ℕ) :
    AEMeasurable (fun x : Fin N → S => ∑ i : Fin N,F (x i))
      (Measure.pi (fun _ : Fin N => μ)) := by
  classical
  have hc : ∀ i : Fin N,AEMeasurable (fun x : Fin N → S => F (x i))
      (Measure.pi (fun _ : Fin N => μ)) := fun i =>
    hF.comp_quasiMeasurePreserving
      (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving
  have hs : ∀ s : Finset (Fin N),AEMeasurable (fun x : Fin N → S => ∑ i ∈ s,F (x i))
      (Measure.pi (fun _ : Fin N => μ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using
        (aemeasurable_const : AEMeasurable (fun _ : Fin N → S => (0 : ℝ)) _)
    | @insert i s hi ih =>
        convert (hc i).add ih using 1
        funext x
        simp only [Finset.sum_insert hi,Pi.add_apply]
  exact hs Finset.univ

theorem empirical_exponential_bound (F : S → ℝ) (hF : Integrable F μ) (c : ℝ)
    (hc : Integrable (fun x => Real.exp (c*F x)) μ) (N : ℕ) (hN : 0 < N) :
    Integrable (fun x : Fin N → S => Real.exp ((N : ℝ)⁻¹*∑ i : Fin N,c*F (x i)))
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → S,Real.exp ((N : ℝ)⁻¹*∑ i : Fin N,c*F (x i))
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ ∫ x,Real.exp (c*F x) ∂μ := by
  classical
  let P := Measure.pi (fun _ : Fin N => μ)
  let G := fun x : Fin N → S => (N : ℝ)⁻¹*∑ i : Fin N,Real.exp (c*F (x i))
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hcoord : ∀ i : Fin N,Integrable (fun x : Fin N → S => Real.exp (c*F (x i))) P :=
    fun i => (measurePreserving_eval (fun _ : Fin N => μ) i).integrable_comp_of_integrable hc
  have hG : Integrable G P :=
    (integrable_finset_sum _ (fun i _ => hcoord i)).const_mul _
  have hJ : ∀ x : Fin N → S,
      Real.exp ((N : ℝ)⁻¹*∑ i : Fin N,c*F (x i)) ≤ G x := by
    intro x
    have hw : (∑ _i : Fin N,(N : ℝ)⁻¹) = 1 := by simp [hn]
    simpa only [smul_eq_mul,←Finset.mul_sum,G] using
      convexOn_exp.map_sum_le
        (t := Finset.univ) (w := fun _ : Fin N => (N : ℝ)⁻¹)
        (p := fun i => c*F (x i))
        (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg N)) hw (fun i _ => Set.mem_univ _)
  have hm := (empirical_function_aemeasurable (fun x => c*F x)
    (hF.aestronglyMeasurable.aemeasurable.const_mul c) N).const_mul (N : ℝ)⁻¹
  have hi : Integrable (fun x : Fin N → S => Real.exp ((N : ℝ)⁻¹*∑ i : Fin N,c*F (x i))) P :=
    hG.mono' (Real.measurable_exp.comp_aemeasurable hm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hJ x)
  refine ⟨hi,(integral_mono hi hG hJ).trans_eq ?_⟩
  dsimp [G]
  rw [integral_const_mul,integral_finset_sum _ (fun i _ => hcoord i)]
  have he : ∀ i : Fin N,(∫ x : Fin N → S,Real.exp (c*F (x i)) ∂P) =
      ∫ x,Real.exp (c*F x) ∂μ := by
    intro i
    exact DGRHS.Decoupling.integral_comp_preserving
      (measurePreserving_eval (fun _ : Fin N => μ) i)
      (fun y : S => Real.exp (c*F y)) hc.aestronglyMeasurable
  simp_rw [he]
  simp [hn]

theorem source_one_body_reduction (h : S × S → ℝ) (F : S → ℝ)
    (hF : Integrable F μ) (I β : ℝ) (hβ : 0 ≤ β)
    (hTail : Integrable (fun x => Real.exp (2*β*F x)) μ)
    (N : ℕ) (hN : 0 < N)
    (hCanonical : Integrable (fun x : Fin N → S => Real.exp
      (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
      (Measure.pi (fun _ : Fin N => μ))) :
    Integrable (fun x : Fin N → S => Real.exp (DGRHS.CLT.sourceParticleExponent h F I β N x))
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → S,Real.exp (DGRHS.CLT.sourceParticleExponent h F I β N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤
      Real.exp (β*|I|)*Real.sqrt (∫ x : Fin N → S,Real.exp
        (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
        ∂Measure.pi (fun _ : Fin N => μ))*Real.sqrt (∫ x,Real.exp (2*β*F x) ∂μ) := by
  let P := Measure.pi (fun _ : Fin N => μ)
  let X := fun x : Fin N → S => -β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x
  let Y := fun x : Fin N → S => β*((N : ℝ)⁻¹*∑ i : Fin N,F (x i))
  have hx : Integrable (fun x => Real.exp (2*X x)) P := by
    convert hCanonical using 1
    funext x
    congr 1
    dsimp [X]
    ring
  have hX : AEMeasurable X P := by
    have hm := Real.measurable_log.comp_aemeasurable hx.aestronglyMeasurable.aemeasurable
    have hm' : AEMeasurable (fun x => 2*X x) P := by
      simpa only [Function.comp_def,Real.log_exp] using hm
    convert hm'.const_mul (1/2 : ℝ) using 1
    funext x
    ring
  have hY : AEMeasurable Y P :=
    ((empirical_function_aemeasurable F hF.aestronglyMeasurable.aemeasurable N).const_mul _).const_mul _
  obtain ⟨hy',hb'⟩ := empirical_exponential_bound F hF (2*β) hTail N hN
  have he : (fun x : Fin N → S => Real.exp ((N : ℝ)⁻¹*∑ i : Fin N,(2*β)*F (x i))) =
      fun x => Real.exp (2*Y x) := by
    funext x
    congr 1
    rw [←Finset.mul_sum]
    dsimp [Y]
    ring
  rw [he] at hy' hb'
  obtain ⟨hi,hb⟩ := DGRHS.CLT.exponential_sum_integral_cs X Y hX hY hx hy'
  have hs : (fun x : Fin N → S => Real.exp (DGRHS.CLT.sourceParticleExponent h F I β N x)) =
      fun x => Real.exp (-β*I)*Real.exp (X x+Y x) := by
    funext x
    rw [←Real.exp_add]
    congr 1
    dsimp [DGRHS.CLT.sourceParticleExponent,X,Y]
    ring
  rw [hs]
  refine ⟨hi.const_mul _,?_⟩
  rw [integral_const_mul]
  have hI : Real.exp (-β*I) ≤ Real.exp (β*|I|) :=
    Real.exp_le_exp.mpr (by nlinarith [neg_le_abs I])
  have hb'' := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-β*I)).le
  have hxid : (∫ x,Real.exp (2*X x) ∂P) = ∫ x : Fin N → S,
      Real.exp (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x) ∂P := by
    congr 1
    funext x
    congr 1
    dsimp [X]
    ring
  rw [hxid] at hb''
  exact hb''.trans (by
    have hprod := mul_le_mul hI (Real.sqrt_le_sqrt hb') (Real.sqrt_nonneg _) (Real.exp_pos _).le
    have hlast := mul_le_mul_of_nonneg_left hprod (Real.sqrt_nonneg (∫ x : Fin N → S,
      Real.exp (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x) ∂P))
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hlast)
end DGRHS.Attractive
#print axioms DGRHS.Attractive.empirical_exponential_bound
#print axioms DGRHS.Attractive.source_one_body_reduction
#check @DGRHS.Attractive.source_one_body_reduction
