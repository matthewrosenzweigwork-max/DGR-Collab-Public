import DGRHS.Concentration.RowSection
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace Topology
namespace DGRHS.Concentration

/-- The finite Hilbert tuple of actual L2 sections, with varying column laws. -/
def rowTuple {Ω Ψ : Type*} [MeasurableSpace Ψ] {q : ℕ}
    (ν : Fin q → Measure Ψ) (h : Fin q → Ω × Ψ → ℝ) (x : Ω) :
    PiLp 2 (fun j ↦ Lp ℝ 2 (ν j)) :=
  WithLp.toLp 2 (fun j ↦ rowSection (ν j) (h j) x)

lemma rowTuple_apply {Ω Ψ : Type*} [MeasurableSpace Ψ] {q : ℕ}
    (ν : Fin q → Measure Ψ) (h : Fin q → Ω × Ψ → ℝ) (x : Ω) (j : Fin q) :
    rowTuple ν h x j = rowSection (ν j) (h j) x := rfl

lemma rowTuple_norm_square {Ω Ψ : Type*} [MeasurableSpace Ψ] {q : ℕ}
    (ν : Fin q → Measure Ψ) (h : Fin q → Ω × Ψ → ℝ) (x : Ω)
    (hx : ∀ j, MemLp (fun y ↦ h j (x,y)) 2 (ν j)) :
    ‖rowTuple ν h x‖^2 = ∑ j, ∫ y, (h j (x,y))^2 ∂ν j := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl (fun j _ ↦ rowSection_norm_square (ν j) (h j) x (hx j))

/-- Actual strong measurability of the finite row tuple. -/
theorem rowTuple_aestronglyMeasurable {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace.CountablyGenerated Ψ]
    {q : ℕ} (μ : Measure Ω) (ν : Fin q → Measure Ψ)
    [IsProbabilityMeasure μ] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin q → Ω × Ψ → ℝ) (A : ℝ)
    (hAES : ∀ j, AEStronglyMeasurable (h j) (μ.prod (ν j)))
    (hBound : ∀ j, ∀ᵐ p ∂μ.prod (ν j), |h j p| ≤ A) :
    AEStronglyMeasurable (rowTuple ν h) μ := by
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : ∀ j, MeasurableSpace (Lp ℝ 2 (ν j)) := fun j ↦ borel (Lp ℝ 2 (ν j))
  let : ∀ j, BorelSpace (Lp ℝ 2 (ν j)) := fun j ↦ ⟨rfl⟩
  have hp : AEMeasurable (fun x j ↦ rowSection (ν j) (h j) x) μ :=
    aemeasurable_pi_iff.mpr (fun j ↦
      (rowSection_aestronglyMeasurable μ (ν j) (h j) A (hAES j) (hBound j)).aemeasurable)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun j ↦ Lp ℝ 2 (ν j))).symm.continuous.comp_aestronglyMeasurable
    hp.aestronglyMeasurable

lemma rowTuple_bounded {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {q : ℕ} (μ : Measure Ω) (ν : Fin q → Measure Ψ)
    [IsProbabilityMeasure μ] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin q → Ω × Ψ → ℝ) (A B : ℝ) (hB : 0 ≤ B)
    (hAES : ∀ j, AEStronglyMeasurable (h j) (μ.prod (ν j)))
    (hBound : ∀ j, ∀ᵐ p ∂μ.prod (ν j), |h j p| ≤ A)
    (hEnergy : ∀ᵐ x ∂μ, (∑ j, ∫ y, (h j (x,y))^2 ∂ν j) ≤ B^2) :
    ∀ᵐ x ∂μ, ‖rowTuple ν h x‖ ≤ B := by
  have hs : ∀ᵐ x ∂μ, ∀ j, MemLp (fun y ↦ h j (x,y)) 2 (ν j) :=
    ae_all_iff.mpr (fun j ↦ bounded_kernel_sections_memLp μ (ν j) (h j) A (hAES j) (hBound j))
  filter_upwards [hs,hEnergy] with x hx he
  rw [← rowTuple_norm_square ν h x hx] at he
  nlinarith [norm_nonneg (rowTuple ν h x)]

lemma rowTuple_integrable {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace.CountablyGenerated Ψ]
    {q : ℕ} (μ : Measure Ω) (ν : Fin q → Measure Ψ)
    [IsProbabilityMeasure μ] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin q → Ω × Ψ → ℝ) (A B : ℝ) (hB : 0 ≤ B)
    (hAES : ∀ j, AEStronglyMeasurable (h j) (μ.prod (ν j)))
    (hBound : ∀ j, ∀ᵐ p ∂μ.prod (ν j), |h j p| ≤ A)
    (hEnergy : ∀ᵐ x ∂μ, (∑ j, ∫ y, (h j (x,y))^2 ∂ν j) ≤ B^2) :
    Integrable (rowTuple ν h) μ :=
  bounded_hilbert_integrable (rowTuple_aestronglyMeasurable μ ν h A hAES hBound)
    (rowTuple_bounded μ ν h A B hB hAES hBound hEnergy)

/-- True Bochner centering, derived from first-coordinate canonicality. -/
theorem rowTuple_centered {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace.CountablyGenerated Ψ]
    {q : ℕ} (μ : Measure Ω) (ν : Fin q → Measure Ψ)
    [IsProbabilityMeasure μ] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin q → Ω × Ψ → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAES : ∀ j, AEStronglyMeasurable (h j) (μ.prod (ν j)))
    (hBound : ∀ j, ∀ᵐ p ∂μ.prod (ν j), |h j p| ≤ A)
    (hEnergy : ∀ᵐ x ∂μ, (∑ j, ∫ y, (h j (x,y))^2 ∂ν j) ≤ B^2)
    (hMean : ∀ j, ∀ᵐ y ∂ν j, ∫ x, h j (x,y) ∂μ = 0) :
    (∫ x, rowTuple ν h x ∂μ) = 0 := by
  have hI := rowTuple_integrable μ ν h A B hB hAES hBound hEnergy
  apply integral_eq_zero_of_forall_integral_inner_eq_zero ℝ (rowTuple ν h) hI
  intro g
  have hRI : ∀ j, Integrable (rowSection (ν j) (h j)) μ := fun j ↦
    bounded_hilbert_integrable (rowSection_aestronglyMeasurable μ (ν j) (h j) A (hAES j) (hBound j))
      (rowSection_bounded μ (ν j) (h j) A hA (hAES j) (hBound j))
  have hInner : ∀ j, Integrable (fun x ↦ inner ℝ (g j) (rowSection (ν j) (h j) x)) μ :=
    fun j ↦ (hRI j).const_inner (g j)
  calc
    (∫ x, inner ℝ g (rowTuple ν h x) ∂μ) =
        ∫ x, ∑ j, inner ℝ (g j) (rowSection (ν j) (h j) x) ∂μ := rfl
    _ = ∑ j, ∫ x, inner ℝ (g j) (rowSection (ν j) (h j) x) ∂μ :=
      integral_finsetSum Finset.univ (fun j _ ↦ hInner j)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [integral_inner (hRI j),rowSection_centered μ (ν j) (h j) A hA (hAES j) (hBound j) (hMean j)]
      simp

#check @DGRHS.Concentration.rowTuple_centered
#print axioms DGRHS.Concentration.rowTuple_centered
#print axioms DGRHS.Concentration.rowTuple_aestronglyMeasurable
#print axioms DGRHS.Concentration.rowTuple_norm_square
#print axioms DGRHS.Concentration.rowTuple_bounded
end DGRHS.Concentration
