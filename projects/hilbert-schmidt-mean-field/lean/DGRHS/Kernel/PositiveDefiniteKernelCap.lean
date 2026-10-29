/- Source lem:PDdeterministicDiagonalBound, first inequality. A genuinely
finite-Gram definition for the arbitrary real two-body kernel; no feature map,
stationarity or continuity is assumed. Measure-centering positivity remains
separate; this file proves the pointwise cap and every proper integral used. -/
import DGRHS.Kernel.Centering
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.Kernel

/-- The manuscript's real symmetric positive-definite two-body kernel condition. -/
structure IsPositiveDefiniteKernel {Ω : Type*} (q : Ω → Ω → ℝ) : Prop where
  symmetric : ∀ x y,q x y=q y x
  gram_nonneg : ∀ (n : ℕ) (x : Fin n → Ω) (c : Fin n → ℝ),
    0≤∑ i,∑ j,c i*c j*q (x i) (x j)

lemma IsPositiveDefiniteKernel.diagonal_nonneg {Ω : Type*} {q : Ω → Ω → ℝ}
    (hq : IsPositiveDefiniteKernel q) (x : Ω) : 0≤q x x := by
  simpa using hq.gram_nonneg 1 (fun _ => x) (fun _ => 1)

lemma IsPositiveDefiniteKernel.abs_le_diagonal_cap {Ω : Type*} {q : Ω → Ω → ℝ}
    (hq : IsPositiveDefiniteKernel q) (M : ℝ) (hcap : ∀ x,q x x≤M)
    (x y : Ω) : |q x y|≤M := by
  have hp := hq.gram_nonneg 2 ![x,y] ![(1:ℝ),1]
  have hm := hq.gram_nonneg 2 ![x,y] ![(1:ℝ),-1]
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    one_mul,mul_one,neg_mul,mul_neg,neg_neg] at hp hm
  rw [hq.symmetric y x] at hp hm
  apply abs_le.mpr
  constructor <;> nlinarith [hcap x,hcap y]

lemma positiveDefiniteKernel_centered_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (q : Ω → Ω → ℝ)
    (hq : IsPositiveDefiniteKernel q)
    (hmeas : Measurable (Function.uncurry q)) (M : ℝ)
    (hcap : ∀ x,q x x≤M) :
    Integrable (Function.uncurry q) (μ.prod μ) ∧
      (∀ x,Integrable (fun y => q x y) μ) ∧
      (∀ y,Integrable (fun x => q x y) μ) ∧
      ∀ x y,|DGRHS.centeredKernel μ q x y|≤4*M := by
  have hb : ∀ x y,|q x y|≤M := hq.abs_le_diagonal_cap M hcap
  have hi : Integrable (Function.uncurry q) (μ.prod μ) :=
    Integrable.of_bound hmeas.aestronglyMeasurable M (Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs,Function.uncurry] using hb z.1 z.2)
  have hrow : ∀ x,Integrable (fun y => q x y) μ := fun x =>
    Integrable.of_bound (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hb x y)
  have hcol : ∀ y,Integrable (fun x => q x y) μ := fun y =>
    Integrable.of_bound (hmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x y)
  refine ⟨hi,hrow,hcol,?_⟩
  have hp : ∀ x,|DGRHS.potential μ q x|≤M := fun x => by
    simpa [DGRHS.potential,Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => q x y)
        (C := M) (Filter.Eventually.of_forall fun y => by
          simpa only [Real.norm_eq_abs] using hb x y)
  have hs : ∀ y,|DGRHS.secondPotential μ q y|≤M := fun y => by
    simpa [DGRHS.secondPotential,Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => q x y)
        (C := M) (Filter.Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs] using hb x y)
  have hm : |∫ z,q z.1 z.2 ∂μ.prod μ|≤M := by
    simpa [Real.norm_eq_abs,Function.uncurry] using
      norm_integral_le_of_norm_le_const (μ := μ.prod μ) (f := Function.uncurry q)
        (C := M) (Filter.Eventually.of_forall fun z => by
          simpa only [Real.norm_eq_abs,Function.uncurry] using hb z.1 z.2)
  intro x y
  unfold DGRHS.centeredKernel
  calc
    _ ≤ |q x y-DGRHS.potential μ q x-DGRHS.secondPotential μ q y|+
        |∫ z,q z.1 z.2 ∂μ.prod μ| := abs_add_le _ _
    _ ≤ |q x y-DGRHS.potential μ q x|+|DGRHS.secondPotential μ q y|+
        |∫ z,q z.1 z.2 ∂μ.prod μ| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ |q x y|+|DGRHS.potential μ q x|+|DGRHS.secondPotential μ q y|+
        |∫ z,q z.1 z.2 ∂μ.prod μ| := add_le_add (add_le_add (abs_sub _ _) le_rfl) le_rfl
    _ ≤ M+M+M+M := add_le_add (add_le_add (add_le_add (hb x y) (hp x)) (hs y)) hm
    _ = _ := by ring

end DGRHS.Kernel
#check @DGRHS.Kernel.positiveDefiniteKernel_centered_cap
#print axioms DGRHS.Kernel.IsPositiveDefiniteKernel.diagonal_nonneg
#print axioms DGRHS.Kernel.IsPositiveDefiniteKernel.abs_le_diagonal_cap
#print axioms DGRHS.Kernel.positiveDefiniteKernel_centered_cap
