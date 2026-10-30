import DGPS.Lipschitz.T01HessianCoercivity
import DGPS.Lipschitz.EquilibriumManifold
import DGPS.Equilibrium.GaussianRate

/-!
# Actual inverse-Hessian perturbations for Gaussian comparison

For a continuous Lipschitz representative of a centered L2 test, its inverse-Hessian image
has a continuous Lipschitz representative solving `h + T h = g` pointwise. Full support of
the reference is used only to upgrade a continuous a.e. equality to a pointwise equality.
The scalar-rate/Gaussian-rate inequality still needs the dissipation expansion along its tilt.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- Construct the actual covariance perturbation, retaining its reference measure and
quadratic form. No older semiconvex hypothesis or Gaussian-rate inequality is used. -/
theorem exists_t01_covariance_perturbation (A : InteractionData d) (hA : LipschitzData A)
    (μ : ProbabilityMeasure (Torus d)) [(μ : Measure (Torus d)).IsOpenPosMeasure]
    (hH : IsCoerciveDensityHessian A μ) (f : centeredL2 μ) (g : C(Torus d, ℝ))
    (hfg : (fun x => g x) =ᵐ[(μ : Measure (Torus d))] (f : Lp ℝ 2 (μ : Measure (Torus d))))
    {Lg : ℝ} (hg : TorusLipschitzWith Lg (fun x => g x)) :
    ∃ h : C(Torus d, ℝ),
      (∃ L : ℝ, TorusLipschitzWith L (fun x => h x)) ∧
      ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ h =
        ((densityCovariance A μ hH f : centeredL2 μ) : Lp ℝ 2 (μ : Measure (Torus d))) ∧
      (∫ x, h x ∂(μ : Measure (Torus d))) = 0 ∧
      (∀ x, h x + centeredOperatorC A (μ : Measure (Torus d)) h x = g x) ∧
      (∫ x, g x * h x ∂(μ : Measure (Torus d))) =
        inner ℝ f (densityCovariance A μ hH f) := by
  let u : centeredL2 μ := densityCovariance A μ hH f
  let h : C(Torus d, ℝ) := g - Tcont A (μ : Measure (Torus d)) u.1
  have hgL : ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ g = f.1 := by
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp (p := 2) (μ := (μ : Measure (Torus d)))
      (𝕜 := ℝ) g).trans hfg
  have hHu : u.1 + centeredOperator A (μ : Measure (Torus d)) u.1 = f.1 := by
    have he := congrArg Subtype.val (densityHessian_densityCovariance A μ hH f)
    change u.1 + DGPS.kernelOp A μ u.1 = f.1 at he
    rwa [← centeredOperator_eq_kernelOp A μ] at he
  have hclass : ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ h = u.1 := by
    dsimp only [h]
    rw [map_sub, hgL]
    change f.1 - centeredOperator A (μ : Measure (Torus d)) u.1 = u.1
    exact sub_eq_iff_eq_add.mpr hHu.symm
  have hha : (fun x => h x) =ᵐ[(μ : Measure (Torus d))] u.1 := by
    have he := ContinuousMap.coeFn_toLp (p := 2) (μ := (μ : Measure (Torus d))) (𝕜 := ℝ) h
    rw [hclass] at he
    exact he.symm
  have hsumL : ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ
      (h + centeredOperatorC A (μ : Measure (Torus d)) h) =
      ContinuousMap.toLp 2 (μ : Measure (Torus d)) ℝ g := by
    rw [map_add, toLp_centeredOperatorC, hclass, hgL]
    exact hHu
  have hsumae : (fun x => (h + centeredOperatorC A (μ : Measure (Torus d)) h) x)
      =ᵐ[(μ : Measure (Torus d))] (fun x => g x) := by
    have he := ContinuousMap.coeFn_toLp (p := 2) (μ := (μ : Measure (Torus d))) (𝕜 := ℝ)
      (h + centeredOperatorC A (μ : Measure (Torus d)) h)
    rw [hsumL] at he
    exact he.symm.trans
      (ContinuousMap.coeFn_toLp (p := 2) (μ := (μ : Measure (Torus d))) (𝕜 := ℝ) g)
  have hpoint := MeasureTheory.Measure.eq_of_ae_eq hsumae
    (h + centeredOperatorC A (μ : Measure (Torus d)) h).continuous g.continuous
  refine ⟨h, ?_, hclass, ?_, fun x => congrFun hpoint x, ?_⟩
  · obtain ⟨LT, hLT⟩ := kernel_integral_lipschitz A hA (μ : Measure (Torus d)) u.1
    have hT : TorusLipschitzWith LT
        (fun x => Tcont A (μ : Measure (Torus d)) u.1 x) := by
      intro x y
      simpa only [Tcont_apply] using hLT x y
    have hs := lip034_lipschitz_add hg (lip034_lipschitz_smul hT (-1))
    refine ⟨Lg + |(-1 : ℝ)| * LT, fun x y => ?_⟩
    change |(g x - Tcont A (μ : Measure (Torus d)) u.1 x) -
      (g y - Tcont A (μ : Measure (Torus d)) u.1 y)| ≤ _
    simpa only [neg_one_mul, sub_eq_add_neg] using hs x y
  · rw [← integral_toLp_eq μ h, hclass]
    exact u.2
  · change (∫ x, g x * h x ∂(μ : Measure (Torus d))) = inner ℝ f.1 u.1
    rw [inner_eq_integral]
    exact integral_congr_ae ((hfg.and hha).mono fun x hx => by
      change g x * h x = f.1 x * u.1 x
      exact congrArg₂ (fun a b : ℝ => a * b) hx.1 hx.2)

end DGPS.Lipschitz
