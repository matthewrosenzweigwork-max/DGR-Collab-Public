import DGRHS.Concentration.MomentTail
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Concentration

def glzRealScale (u A B C D : ℝ) : ℝ :=
  Real.sqrt u*C+u*D+u*Real.sqrt u*B+u^2*A

lemma glz_scale_even_ceil_le (u A B C D : ℝ) (hu : 1 ≤ u)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    glzScale (2*Nat.ceil u) A B C D ≤ 16*glzRealScale u A B C D := by
  have hu0 : 0 ≤ u := by linarith
  have hk := Nat.ceil_lt_add_one hu0
  have hm : ((2*Nat.ceil u : ℕ) : ℝ) ≤ 4*u := by push_cast; linarith
  have hm0 : 0 ≤ ((2*Nat.ceil u : ℕ) : ℝ) := Nat.cast_nonneg _
  have hs : Real.sqrt ((2*Nat.ceil u : ℕ) : ℝ) ≤ 2*Real.sqrt u := by
    nlinarith [Real.sq_sqrt hm0,Real.sq_sqrt hu0,
      Real.sqrt_nonneg ((2*Nat.ceil u : ℕ) : ℝ),Real.sqrt_nonneg u]
  have h1 := mul_le_mul_of_nonneg_right hs hC
  have h2 := mul_le_mul_of_nonneg_right hm hD
  have h3 : ((2*Nat.ceil u : ℕ) : ℝ)*Real.sqrt ((2*Nat.ceil u : ℕ) : ℝ)*B ≤ (4*u)*(2*Real.sqrt u)*B := by gcongr
  have h4 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm0 hm 2) hA
  have hsum := add_le_add (add_le_add (add_le_add h1 h2) h3) h4
  change glzScale (2*Nat.ceil u) A B C D ≤ _
  unfold glzScale glzRealScale
  nlinarith [mul_nonneg (Real.sqrt_nonneg u) hC,mul_nonneg hu0 hD,
    mul_nonneg (mul_nonneg hu0 (Real.sqrt_nonneg u)) hB]

/-- All real tail parameters, from actual even moments by explicit ceiling control. -/
theorem kernel_four_scale_parameter_tail {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace.CountablyGenerated Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ) (A B C D : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A)
    (hMeanRight : ∀ i j, ∀ᵐ x ∂μ i, ∫ y, h i j (x,y) ∂ν j = 0)
    (hMeanLeft : ∀ i j, ∀ᵐ y ∂ν j, ∫ x, h i j (x,y) ∂μ i = 0)
    (hRow : ∀ i, ∀ᵐ x ∂μ i, (∑ j, ∫ y, (h i j (x,y))^2 ∂ν j) ≤ B^2)
    (hColumn : ∀ j, ∀ᵐ y ∂ν j, kernelColumnEnergy μ h j y ≤ B^2)
    (hTrace : (∑ i, ∑ j, ∫ p, (h i j p)^2 ∂(μ i).prod (ν j)) ≤ C^2)
    (hTest : ∀ (f : PiLp 2 (fun i ↦ Lp ℝ 2 (μ i)))
      (g : PiLp 2 (fun j ↦ Lp ℝ 2 (ν j))), ‖f‖ ≤ 1 → ‖g‖ ≤ 1 → kernelL2Bilinear μ ν h f g ≤ D)
    (u t : ℝ) (hu : 1 ≤ u) (ht : 0 < t)
    (hThreshold : (13824*Real.exp 1)*glzRealScale u A B C D ≤ t) :
    ((Measure.pi μ).prod (Measure.pi ν)).real {p | t ≤ |kernelDecoupledSum h p|} ≤ Real.exp (-u) := by
  have hu0 : 0 ≤ u := by linarith
  have hk : 1 ≤ Nat.ceil u := Nat.one_le_ceil_iff.mpr (by linarith)
  have hm : u ≤ ((2*Nat.ceil u : ℕ) : ℝ) := by
    have hh := Nat.le_ceil u
    push_cast
    linarith [show (0 : ℝ) ≤ (Nat.ceil u : ℝ) from Nat.cast_nonneg _]
  have hscale := glz_scale_even_ceil_le u A B C D hu hA hB hC hD
  have hT : Real.exp 1*(864*glzScale (2*Nat.ceil u) A B C D) ≤ t := by
    calc
      _ ≤ Real.exp 1*(864*(16*glzRealScale u A B C D)) := by gcongr
      _ = (13824*Real.exp 1)*glzRealScale u A B C D := by ring
      _ ≤ t := hThreshold
  have hb := kernel_even_four_scale_tail μ ν h A B C D hA hB hC hD hAES hBound
    hMeanRight hMeanLeft hRow hColumn hTrace hTest (Nat.ceil u) hk t ht hT
  exact hb.trans (Real.exp_monotone (neg_le_neg hm))

#print axioms DGRHS.Concentration.glz_scale_even_ceil_le
#print axioms DGRHS.Concentration.kernel_four_scale_parameter_tail
#check @DGRHS.Concentration.kernel_four_scale_parameter_tail
end DGRHS.Concentration
