import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Logic.Equiv.Sum

/-! Exact integration over disjoint coordinate blocks. The measurable
change of variables is proved from the product measures on rectangles.
Integrability is supplied separately before the real integral identity. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace PeriodicAttractiveLogGas.BlockProductIntegration

variable {ι κ A : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [MeasurableSpace A]

/-- Regroup coordinates by the fibres of an actual finite map. -/
def split (q : ι → κ) : (ι → A) ≃ᵐ (∀ b : κ, {i : ι // q i = b} → A) where
  toFun X b i := X i
  invFun Y i := Y (q i) ⟨i, rfl⟩
  left_inv X := rfl
  right_inv Y := by
    funext b i
    rcases i with ⟨i, hi⟩
    subst b
    rfl
  measurable_toFun := measurable_pi_iff.mpr fun b =>
    measurable_pi_iff.mpr fun i => measurable_pi_apply i.val
  measurable_invFun := measurable_pi_iff.mpr fun i =>
    (measurable_pi_apply (⟨i, rfl⟩ : {j : ι // q j = q i})).comp
      (measurable_pi_apply (q i))

@[simp] theorem split_apply (q : ι → κ) (X : ι → A) (b : κ) (i : {i : ι // q i = b}) :
    split q X b i = X i := rfl

@[simp] theorem split_symm_apply (q : ι → κ) (Y : ∀ b : κ, {i : ι // q i = b} → A) (i : ι) :
    (split q).symm Y i = Y (q i) ⟨i, rfl⟩ := rfl

theorem measurePreserving_split (q : ι → κ) (μ : ι → Measure A)
    [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (split (A := A) q) (Measure.pi μ)
      (Measure.pi fun b : κ => Measure.pi fun i : {i : ι // q i = b} => μ i) := by
  classical
  let e := split (A := A) q
  have hi : MeasurePreserving e.symm
      (Measure.pi fun b : κ => Measure.pi fun i : {i : ι // q i = b} => μ i)
      (Measure.pi μ) := by
    refine ⟨e.symm.measurable, (Measure.pi_eq fun s hs => ?_).symm⟩
    have hpre : e.symm ⁻¹' pi univ s =
        pi univ (fun b : κ => pi univ (fun i : {i : ι // q i = b} => s i)) := by
      ext Y
      constructor
      · intro h b _ i _
        rcases i with ⟨i, hi⟩
        subst b
        exact h i (mem_univ i)
      · intro h i _
        exact h (q i) (mem_univ _) ⟨i, rfl⟩ (mem_univ _)
    rw [MeasurableEquiv.map_apply, hpre, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    simpa only [Fintype.prod_sigma, Equiv.sigmaFiberEquiv_apply] using
      (Equiv.sigmaFiberEquiv q).prod_comp (fun i => μ i (s i))
  exact hi.symm e.symm

theorem integrable_block_product (q : ι → κ) (μ : ι → Measure A)
    [∀ i, SigmaFinite (μ i)]
    (F : ∀ b : κ, ({i : ι // q i = b} → A) → ℝ)
    (hF : ∀ b, Integrable (F b) (Measure.pi fun i : {i : ι // q i = b} => μ i)) :
    Integrable (fun X : ι → A => ∏ b : κ, F b (fun i => X i)) (Measure.pi μ) := by
  exact (measurePreserving_split q μ).integrable_comp_of_integrable
    (Integrable.fintype_prod_dep hF)

theorem integral_block_product (q : ι → κ) (μ : ι → Measure A)
    [∀ i, SigmaFinite (μ i)]
    (F : ∀ b : κ, ({i : ι // q i = b} → A) → ℝ)
    (hF : ∀ b, Integrable (F b) (Measure.pi fun i : {i : ι // q i = b} => μ i)) :
    (∫ X : ι → A, ∏ b : κ, F b (fun i => X i) ∂Measure.pi μ) =
      ∏ b : κ, ∫ Y, F b Y ∂Measure.pi (fun i : {i : ι // q i = b} => μ i) := by
  calc
    _ = ∫ Y, ∏ b : κ, F b (Y b)
        ∂Measure.pi (fun b : κ => Measure.pi fun i : {i : ι // q i = b} => μ i) :=
      (measurePreserving_split q μ).integral_comp
        (split (A := A) q).measurableEmbedding _
    _ = _ := integral_fintype_prod_eq_prod F

end PeriodicAttractiveLogGas.BlockProductIntegration
