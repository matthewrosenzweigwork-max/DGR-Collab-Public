import DGRHS.Concentration.RowWeak

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace Topology
namespace DGRHS.Concentration

/-- The actual conditional-variance high moment, with every Hilbert hypothesis
constructed from the bounded canonical kernel and its source A/B/C/D controls. -/
theorem kernel_row_variance_moment {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace.CountablyGenerated Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ) (A B C D : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A)
    (hMeanLeft : ∀ i j, ∀ᵐ y ∂ν j, ∫ x, h i j (x,y) ∂μ i = 0)
    (hEnergy : ∀ i, ∀ᵐ x ∂μ i, (∑ j, ∫ y, (h i j (x,y))^2 ∂ν j) ≤ B^2)
    (hTrace : (∑ i, ∑ j, ∫ p, (h i j p)^2 ∂(μ i).prod (ν j)) ≤ C^2)
    (hTest : ∀ (f : PiLp 2 (fun i ↦ Lp ℝ 2 (μ i)))
      (g : PiLp 2 (fun j ↦ Lp ℝ 2 (ν j))), ‖f‖ ≤ 1 → ‖g‖ ≤ 1 → kernelL2Bilinear μ ν h f g ≤ D)
    (k : ℕ) (hk : 1 ≤ k) :
    (∫ ω, (kernelColumnVariance ν h ω)^k ∂Measure.pi μ) ≤
      (12*(C+Real.sqrt ((2*k : ℕ) : ℝ)*D+((2*k : ℕ) : ℝ)*B))^(2*k) := by
  let Z := fun i x ↦ rowTuple ν (h i) x
  have hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i) := fun i ↦
    rowTuple_aestronglyMeasurable (μ i) ν (h i) A (hAES i) (hBound i)
  have hZB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B := fun i ↦
    rowTuple_bounded (μ i) ν (h i) A B hB (hAES i) (hBound i) (hEnergy i)
  have hZM : ∀ i, ∫ x, Z i x ∂μ i = 0 := fun i ↦
    rowTuple_centered (μ i) ν (h i) A B hA hB (hAES i) (hBound i) (hEnergy i) (hMeanLeft i)
  have hZT := rowTuple_trace_bound μ ν h A C hAES hBound hTrace
  have hZW := rowTuple_weak_variance_bound μ ν h A B D hB hD hAES hBound hEnergy hTest
  have ht := hilbert_integer_moment μ Z B C D hB hC hD hZ hZB hZM hZT hZW (2*k) (by omega)
  have he : (∫ ω, (empiricalNormOnProduct Z ω)^(2*k) ∂Measure.pi μ) =
      ∫ ω, (kernelColumnVariance ν h ω)^k ∂Measure.pi μ := by
    apply integral_congr_ae
    filter_upwards [rowTuple_sum_norm_square μ ν h A hAES hBound] with ω hω
    change ‖∑ i, rowTuple ν (h i) (ω i)‖^(2*k) = _
    rw [pow_mul,hω]
  rw [he] at ht
  have hn : 0 ≤ ∫ ω, (kernelColumnVariance ν h ω)^k ∂Measure.pi μ :=
    integral_nonneg fun ω ↦ pow_nonneg
      (Finset.sum_nonneg fun j _ ↦ integral_nonneg fun y ↦ sq_nonneg _) _
  have hp : 0 < ((2*k : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*k by omega)
  have hR : 0 ≤ 12*(C+Real.sqrt ((2*k : ℕ) : ℝ)*D+((2*k : ℕ) : ℝ)*B) := by positivity
  have hb := (Real.rpow_inv_le_iff_of_pos hn hR hp).mp (by simpa only [one_div] using ht)
  simpa only [Real.rpow_natCast] using hb

#print axioms DGRHS.Concentration.kernel_row_variance_moment
#check @DGRHS.Concentration.kernel_row_variance_moment
end DGRHS.Concentration
