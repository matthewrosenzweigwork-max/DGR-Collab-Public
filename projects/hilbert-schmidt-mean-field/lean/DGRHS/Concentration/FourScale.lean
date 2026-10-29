import DGRHS.Concentration.FourScaleArithmetic
import DGRHS.Concentration.ScalarReduction

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace Topology
namespace DGRHS.Concentration

/-- The four source scales, without a particle-number normalization. -/
def glzScale (m : ℕ) (A B C D : ℝ) : ℝ :=
  Real.sqrt (m : ℝ)*C+(m : ℝ)*D+(m : ℝ)*Real.sqrt (m : ℝ)*B+(m : ℝ)^2*A

/-- Actual scalar even-moment four-scale comparison. Countable generation is
required only on the second coordinate, for the constructed strong L2 row map.
No Hilbert moment, Rosenthal, MGF, tensorization, or independence conclusion is a premise. -/
theorem kernel_even_four_scale_power {Ω Ψ : Type*}
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
    (k : ℕ) (hk : 1 ≤ k) :
    (∫ p, |kernelDecoupledSum h p|^(2*k) ∂(Measure.pi μ).prod (Measure.pi ν)) ≤
      (864*glzScale (2*k) A B C D)^(2*k) := by
  have hr := scalar_even_moment_reduction μ ν h A B C hA hB hAES hBound hMeanRight hMeanLeft hColumn hTrace k hk
  have hv := kernel_row_variance_moment μ ν h A B C D hA hB hC hD hAES hBound hMeanLeft hRow hTrace hTest k hk
  dsimp only at hr
  have hc : 0 ≤ (6*Real.sqrt ((2*k : ℕ) : ℝ))^(2*k) := by positivity
  have ht := hr.trans (add_le_add (mul_le_mul_of_nonneg_left hv hc) le_rfl)
  exact ht.trans (four_scale_power_bound A B C D hA hB hC hD (2*k) (by omega))

/-- The genuine L(2k) norm bound, with zero source scales and empty index sets allowed. -/
theorem kernel_even_four_scale {Ω Ψ : Type*}
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
    (k : ℕ) (hk : 1 ≤ k) :
    (∫ p, |kernelDecoupledSum h p|^(2*k) ∂(Measure.pi μ).prod (Measure.pi ν))^(1/((2*k : ℕ) : ℝ)) ≤
      864*glzScale (2*k) A B C D := by
  have ht := kernel_even_four_scale_power μ ν h A B C D hA hB hC hD hAES hBound
    hMeanRight hMeanLeft hRow hColumn hTrace hTest k hk
  have hn : 0 ≤ ∫ p, |kernelDecoupledSum h p|^(2*k) ∂(Measure.pi μ).prod (Measure.pi ν) :=
    integral_nonneg fun p ↦ pow_nonneg (abs_nonneg _) _
  have hp : 0 < ((2*k : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*k by omega)
  have hR : 0 ≤ 864*glzScale (2*k) A B C D := by unfold glzScale; positivity
  have hb := (Real.rpow_inv_le_iff_of_pos hn hR hp).mpr (by simpa only [Real.rpow_natCast] using ht)
  simpa only [one_div] using hb

#print axioms DGRHS.Concentration.kernel_even_four_scale_power
#print axioms DGRHS.Concentration.kernel_even_four_scale
#check @DGRHS.Concentration.kernel_even_four_scale
end DGRHS.Concentration
