import DGRHS.Gaussian.GaussianShortRangeL2
import Mathlib.MeasureTheory.Group.Integral

/-! Actual bounded-density probability source transfer of the sharp short-range
Gaussian Riesz L2 rate. Density domination and every translated proper section
are proved; no pair integrability or rate bound is assumed. -/
noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianRieszDensityMeasure (ρ : EuclideanSpace ℝ ι → ℝ) : Measure (EuclideanSpace ℝ ι) :=
  volume.withDensity (fun x => ENNReal.ofReal (ρ x))

lemma gaussianRieszDensityMeasure_le (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ)
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    gaussianRieszDensityMeasure ρ ≤ ENNReal.ofReal M • volume := by
  unfold gaussianRieszDensityMeasure
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards [hρ] with x hx
  exact ENNReal.ofReal_le_ofReal hx

lemma integrable_sq_sub_density (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ)
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (F : EuclideanSpace ℝ ι → ℝ)
    (hF : Integrable (fun z => F z ^ 2) volume) (x : EuclideanSpace ℝ ι) :
    Integrable (fun y => F (x - y) ^ 2) (gaussianRieszDensityMeasure ρ) := by
  exact ((hF.comp_sub_left x).smul_measure ENNReal.ofReal_ne_top).mono_measure
    (gaussianRieszDensityMeasure_le ρ M hρ)

lemma integral_sq_sub_density_le (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (F : EuclideanSpace ℝ ι → ℝ)
    (hF : Integrable (fun z => F z ^ 2) volume) (x : EuclideanSpace ℝ ι) :
    (∫ y, F (x - y) ^ 2 ∂gaussianRieszDensityMeasure ρ) ≤ M * ∫ z, F z ^ 2 := by
  calc
    _ ≤ ∫ y, F (x - y) ^ 2 ∂(ENNReal.ofReal M • volume) :=
      integral_mono_measure (gaussianRieszDensityMeasure_le ρ M hρ)
        (Filter.Eventually.of_forall (fun y => sq_nonneg _))
        ((hF.comp_sub_left x).smul_measure ENNReal.ofReal_ne_top)
    _ = _ := by
      rw [integral_smul_measure, integral_sub_left_eq_self (fun z => F z ^ 2) volume x, ENNReal.toReal_ofReal hM]
      rfl

lemma integrable_sq_sub_density_product (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (F : EuclideanSpace ℝ ι → ℝ)
    (hFm : StronglyMeasurable F) (hF : Integrable (fun z => F z ^ 2) volume) :
    Integrable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => F (p.1 - p.2) ^ 2)
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  have hm : StronglyMeasurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      F (p.1 - p.2) ^ 2) := (hFm.comp_measurable (by fun_prop)).pow 2
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall (integrable_sq_sub_density ρ M hρ F hF)
  · apply (integrable_const (M * ∫ z, F z ^ 2)).mono'
      hm.norm.integral_prod_right'.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    simp_rw [Real.norm_of_nonneg (sq_nonneg _)]
    rw [Real.norm_of_nonneg (integral_nonneg (fun y => sq_nonneg _))]
    exact integral_sq_sub_density_le ρ M hM hρ F hF x

lemma integral_sq_sub_density_product_le (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (F : EuclideanSpace ℝ ι → ℝ)
    (hFm : StronglyMeasurable F) (hF : Integrable (fun z => F z ^ 2) volume) :
    (∫ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, F (p.1 - p.2) ^ 2
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ≤ M * ∫ z, F z ^ 2 := by
  have hi := integrable_sq_sub_density_product ρ M hM hρ F hFm hF
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _ : EuclideanSpace ℝ ι, (M * ∫ z, F z ^ 2) ∂gaussianRieszDensityMeasure ρ :=
      integral_mono_ae hi.integral_prod_left (integrable_const _)
        (Filter.Eventually.of_forall (integral_sq_sub_density_le ρ M hM hρ F hF))
    _ = _ := by simp

lemma memLp_gaussianRieszEuclideanShortRange_source (s η : ℝ) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    MemLp (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      gaussianRieszEuclideanShortRange s η (p.1 - p.2)) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  have hm := stronglyMeasurable_gaussianRieszEuclideanShortRange (ι := ι) s η hη ha
  apply (memLp_two_iff_integrable_sq (hm.comp_measurable (by fun_prop)).aestronglyMeasurable).2
  exact integrable_sq_sub_density_product ρ M hM hρ _ hm
    ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).1
      (memLp_gaussianRieszEuclideanShortRange s η hη ha))

lemma integral_gaussianRieszEuclideanShortRange_source_sq_sharp (s η : ℝ) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    (∫ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι,
      gaussianRieszEuclideanShortRange s η (p.1 - p.2) ^ 2
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ≤
      M * (gaussianRieszSourceCoefficient s ^ 2 * Real.pi ^ ((Fintype.card ι : ℝ) / 2) /
        (((Fintype.card ι : ℝ) / 2 - s) ^ 2)) * η ^ ((Fintype.card ι : ℝ) - 2 * s) := by
  have hm := stronglyMeasurable_gaussianRieszEuclideanShortRange (ι := ι) s η hη ha
  have hi := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).1
    (memLp_gaussianRieszEuclideanShortRange s η hη ha)
  calc
    _ ≤ M * ∫ z : EuclideanSpace ℝ ι, gaussianRieszEuclideanShortRange s η z ^ 2 :=
      integral_sq_sub_density_product_le ρ M hM hρ _ hm hi
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left
        (integral_gaussianRieszEuclideanShortRange_sq_sharp (ι := ι) s η hη ha) hM
      simpa only [mul_assoc] using h

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianRieszDensityMeasure
#print axioms DGRHS.Gaussian.gaussianRieszDensityMeasure
#check DGRHS.Gaussian.gaussianRieszDensityMeasure_le
#print axioms DGRHS.Gaussian.gaussianRieszDensityMeasure_le
#check DGRHS.Gaussian.integrable_sq_sub_density
#print axioms DGRHS.Gaussian.integrable_sq_sub_density
#check DGRHS.Gaussian.integral_sq_sub_density_le
#print axioms DGRHS.Gaussian.integral_sq_sub_density_le
#check DGRHS.Gaussian.integrable_sq_sub_density_product
#print axioms DGRHS.Gaussian.integrable_sq_sub_density_product
#check DGRHS.Gaussian.integral_sq_sub_density_product_le
#print axioms DGRHS.Gaussian.integral_sq_sub_density_product_le
#check DGRHS.Gaussian.memLp_gaussianRieszEuclideanShortRange_source
#print axioms DGRHS.Gaussian.memLp_gaussianRieszEuclideanShortRange_source
#check DGRHS.Gaussian.integral_gaussianRieszEuclideanShortRange_source_sq_sharp
#print axioms DGRHS.Gaussian.integral_gaussianRieszEuclideanShortRange_source_sq_sharp
