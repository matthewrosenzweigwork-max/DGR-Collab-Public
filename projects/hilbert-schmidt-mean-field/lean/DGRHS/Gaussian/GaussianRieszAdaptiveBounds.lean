import DGRHS.Gaussian.GaussianRieszAdaptiveComparison

/-! Actual adaptive band and deterministic cap, with cutoff-independent
coefficients for the genuine master size supremum. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianRieszAdaptiveBand (s η δ β A : ℝ) (n : ℕ) (u : ℝ)
    (ρ : EuclideanSpace ℝ ι → ℝ) : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℝ :=
  gaussianRieszMasterBand s
    (max (gaussianRieszAdaptiveScale δ A (n : ℝ) u (Fintype.card ι : ℝ) s) η) δ (2*β) ρ

def gaussianRieszAdaptiveCap (s η δ β A : ℝ) (n : ℕ) (u : ℝ) (ι : Type*) [Fintype ι] : ℝ :=
  1+4*β*(gaussianRieszSourceCoefficient s/s*
    (max (gaussianRieszAdaptiveScale δ A (n : ℝ) u (Fintype.card ι : ℝ) s) η)^(-s))

def gaussianRieszAdaptiveC0 (s δ β : ℝ) : ℝ :=
  1+8*β*(gaussianRieszSourceCoefficient s/s)*δ^(-s)

def gaussianRieszAdaptiveC1 (s β A : ℝ) (ι : Type*) [Fintype ι] : ℝ :=
  8*β*(gaussianRieszSourceCoefficient s/s)*A^(s/((Fintype.card ι : ℝ)-s))

lemma gaussianRieszAdaptiveBand_parameters (δ A u s η : ℝ) (n : ℕ)
    (hδ : 0 < δ) (hA : 0 < A) (hu : 1 ≤ u) (hn : 1 ≤ n) (hηδ : η ≤ δ) :
    0 < max (gaussianRieszAdaptiveScale δ A (n : ℝ) u (Fintype.card ι : ℝ) s) η ∧
      max (gaussianRieszAdaptiveScale δ A (n : ℝ) u (Fintype.card ι : ℝ) s) η ≤ δ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hn)
  have h := gaussianRieszAdaptiveScale_pos_le δ A (n : ℝ) u (Fintype.card ι : ℝ) s hδ hA hn' (by linarith)
  exact ⟨h.1.trans_le (le_max_left _ _),max_le h.2 hηδ⟩

lemma gaussianRieszAdaptiveBand_cap_ess_bounds (s η δ β A : ℝ) (hs : 0 < s)
    (hηδ : η ≤ δ) (hδ : 0 < δ) (hβ : 0 ≤ β) (hA : 0 < A)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu : 1 ≤ u) :
    0 ≤ gaussianRieszAdaptiveC0 s δ β ∧ 0 ≤ gaussianRieszAdaptiveC1 s β A ι ∧
      0 < gaussianRieszAdaptiveCap s η δ β A n u ι ∧
      gaussianRieszAdaptiveCap s η δ β A n u ι ≤
        gaussianRieszAdaptiveC0 s δ β+gaussianRieszAdaptiveC1 s β A ι*((n : ℝ)/u)^(s/((Fintype.card ι : ℝ)-s)) ∧
      (eLpNormEssSup (gaussianRieszAdaptiveBand s η δ β A n u ρ)
        ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))).toReal ≤
        gaussianRieszAdaptiveC0 s δ β+gaussianRieszAdaptiveC1 s β A ι*((n : ℝ)/u)^(s/((Fintype.card ι : ℝ)-s)) := by
  let α := max (gaussianRieszAdaptiveScale δ A (n : ℝ) u (Fintype.card ι : ℝ) s) η
  have hα := gaussianRieszAdaptiveBand_parameters (ι := ι) δ A u s η n hδ hA hu hn hηδ
  have hc : 0 ≤ gaussianRieszSourceCoefficient s/s := div_nonneg (gaussianRieszSourceCoefficient_pos s hs).le hs.le
  have hD : 0 ≤ gaussianRieszSourceCoefficient s/s*α^(-s) := mul_nonneg hc (Real.rpow_nonneg hα.1.le _)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hn)
  have hp := gaussianRieszAdaptiveScale_inverse_power_le δ A (n : ℝ) u (Fintype.card ι : ℝ) s η
    hδ hA hn' (by linarith) hs (by linarith : 0 < (Fintype.card ι : ℝ)-s)
  have hb := mul_le_mul_of_nonneg_left hp (mul_nonneg (by positivity : 0 ≤ 8*β) hc)
  have hupper : 1+8*β*(gaussianRieszSourceCoefficient s/s*α^(-s)) ≤
      gaussianRieszAdaptiveC0 s δ β+gaussianRieszAdaptiveC1 s β A ι*((n : ℝ)/u)^(s/((Fintype.card ι : ℝ)-s)) := by
    unfold gaussianRieszAdaptiveC0 gaussianRieszAdaptiveC1
    dsimp only [α]
    nlinarith only [hb]
  have he := essential_gaussianRieszMasterBand_le s α δ (2*β) hs hα.1 hα.2 ha ρ M hM hρ
  rw [abs_of_nonneg (by linarith : 0 ≤ 2*β)] at he
  refine ⟨?_,?_,?_,?_,?_⟩
  · unfold gaussianRieszAdaptiveC0
    positivity
  · unfold gaussianRieszAdaptiveC1
    positivity
  · change 0 < 1+4*β*(gaussianRieszSourceCoefficient s/s*α^(-s))
    positivity
  · change 1+4*β*(gaussianRieszSourceCoefficient s/s*α^(-s)) ≤ _
    nlinarith [mul_nonneg hβ hD]
  · change (eLpNormEssSup (gaussianRieszMasterBand s α δ (2*β) ρ) _).toReal ≤ _
    nlinarith only [he,hupper]

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianRieszAdaptiveBand
#print axioms DGRHS.Gaussian.gaussianRieszAdaptiveBand

#check DGRHS.Gaussian.gaussianRieszAdaptiveCap
#print axioms DGRHS.Gaussian.gaussianRieszAdaptiveCap

#check DGRHS.Gaussian.gaussianRieszAdaptiveC0
#print axioms DGRHS.Gaussian.gaussianRieszAdaptiveC0

#check DGRHS.Gaussian.gaussianRieszAdaptiveC1
#print axioms DGRHS.Gaussian.gaussianRieszAdaptiveC1

#check DGRHS.Gaussian.gaussianRieszAdaptiveBand_parameters
#print axioms DGRHS.Gaussian.gaussianRieszAdaptiveBand_parameters

#check DGRHS.Gaussian.gaussianRieszAdaptiveBand_cap_ess_bounds
#print axioms DGRHS.Gaussian.gaussianRieszAdaptiveBand_cap_ess_bounds
