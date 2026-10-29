import DGRHS.Attractive.CanonicalArrayIntegrals

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.Attractive
variable {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ}

def pairedArrayProduct (h : Ω × Ω → ℝ) (i j : Fin m → Fin n)
    (z : Fin n → Ω × Ω) : ℝ := ∏ l : Fin m, h ((z (i l)).1,(z (j l)).2)

lemma arraysEquiv_preserving (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow Ω Ω (Fin n))
      (DGRHS.Decoupling.productSamples (ι := Fin n) μ)
      ((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ))) :=
  measurePreserving_arrowProdEquivProdArrow Ω Ω (Fin n) (fun _ ↦ μ) (fun _ ↦ μ)

lemma pairedArrayProduct_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (i j : Fin m → Fin n) :
    Integrable (pairedArrayProduct h i j) (DGRHS.Decoupling.productSamples μ) := by
  exact (arraysEquiv_preserving μ n).integrable_comp_of_integrable
    (arrayProduct_integrable μ h hh C hC i j)

lemma pairedArrayProduct_integral (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (i j : Fin m → Fin n) :
    (∫ z, pairedArrayProduct h i j z ∂DGRHS.Decoupling.productSamples μ) =
      ∫ z, arrayProduct h i j z
        ∂((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ))) :=
  DGRHS.Decoupling.integral_comp_preserving (arraysEquiv_preserving μ n)
    (arrayProduct h i j) (arrayProduct_measurable h hh i j).aestronglyMeasurable

theorem pairedArrayProduct_abs_integral_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (i j : Fin m → Fin n) :
    |∫ z, pairedArrayProduct h i j z ∂DGRHS.Decoupling.productSamples μ| ≤
      C^m * ∏ a : Fin n, ((multiplicity i a).factorial : ℝ) := by
  rw [pairedArrayProduct_integral μ h hh]
  exact canonical_array_integral_abs_le μ h hh C hC i j

theorem pairedArrayProduct_singleton (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (hs : ∀ x y, h (x,y) = h (y,x))
    (hc : ∀ᵐ y ∂μ, ∫ x, h (x,y) ∂μ = 0) (i j : Fin m → Fin n)
    (ha : (∃ a, multiplicity i a = 1) ∨ ∃ a, multiplicity j a = 1) :
    (∫ z, pairedArrayProduct h i j z ∂DGRHS.Decoupling.productSamples μ) = 0 := by
  rw [pairedArrayProduct_integral μ h hh]
  rcases ha with ⟨a,ha⟩ | ⟨a,ha⟩
  · exact canonical_array_singleton_left μ h hh C hC hc i j a ha
  · exact canonical_array_singleton_right μ h hh C hC hs hc i j a ha

/-- Source2533: the actual row hypothesis supplies the missing high joint Lp
input to the already checked scalar factor-four decoupling theorem. -/
theorem row_factorial_even_decoupling (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (hs : ∀ x y, h (x,y) = h (y,x))
    (hc : ∀ᵐ y ∂μ, ∫ x, h (x,y) ∂μ = 0) (n k : ℕ) (hk : 1 ≤ k) :
    (∫ x : Fin n → Ω, |DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (x i,x j))|^(2*k)
      ∂Measure.pi (fun _ ↦ μ)) ≤
      4^(2*k) * ∫ z : (Fin n → Ω) × (Fin n → Ω),
        |DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (z.1 i,z.2 j))|^(2*k)
          ∂((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ))) := by
  have hr : ∀ᵐ x ∂μ, ∫ y, h (x,y) ∂μ = 0 := by
    filter_upwards [hc] with x hx
    calc
      (∫ y, h (x,y) ∂μ) = ∫ y, h (y,x) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun y ↦ hs x y)
      _ = 0 := hx
  exact DGRHS.Decoupling.scalar_even_moment_decoupling_symmetric μ n h hh hs k hk
    (joint_memLp μ h hh C hC (2*k) (by omega)) hr

#check @DGRHS.Attractive.pairedArrayProduct_abs_integral_le
#check @DGRHS.Attractive.pairedArrayProduct_singleton
#check @DGRHS.Attractive.row_factorial_even_decoupling
#print axioms DGRHS.Attractive.pairedArrayProduct_integrable
#print axioms DGRHS.Attractive.pairedArrayProduct_abs_integral_le
#print axioms DGRHS.Attractive.pairedArrayProduct_singleton
#print axioms DGRHS.Attractive.row_factorial_even_decoupling
end DGRHS.Attractive
