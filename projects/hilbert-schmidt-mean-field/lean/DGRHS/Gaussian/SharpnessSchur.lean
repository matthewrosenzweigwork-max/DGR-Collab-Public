import DGRHS.Gaussian.SharpnessPositiveForm
import DGRHS.Gaussian.SharpnessRieszRows

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

/-- The Schur quadratic bound is proved on actual bounded tests before any
finite compression is constructed. No full-kernel L2 premise is used. -/
theorem sharpness_centered_riesz_bounded_form_le (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (f : EuclideanSpace ℝ ι → ℝ) (hf : StronglyMeasurable f)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ x, ‖f x‖ ≤ K) :
    |∫ p, hoeffdingCentered (gaussianRieszDensityMeasure ρ)
      (gaussianRieszPhysicalPair s) p * f p.1 * f p.2
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)| ≤
    (4 * gaussianRieszPhysicalPotentialConstant s M ι) *
      ∫ x, (f x)^2 ∂gaussianRieszDensityMeasure ρ := by
  let μ := gaussianRieszDensityMeasure ρ
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let L := 4 * gaussianRieszPhysicalPotentialConstant s M ι
  have hiH := sharpness_centered_riesz_integrable s hs ha ρ M hM hρ
  have hiG := (sharpness_centered_riesz_bounded_form_nonneg s hs ha ρ M hM hρ f hf K hK hbound).1
  have hsym : ∀ x y, H (x,y) = H (y,x) := by
    intro x y
    change gaussianRieszPhysicalPair s (x,y) - DGRHS.potential μ _ x -
      DGRHS.secondPotential μ _ y + _ =
      gaussianRieszPhysicalPair s (y,x) - DGRHS.potential μ _ y -
      DGRHS.secondPotential μ _ x + _
    rw [DGRHS.secondPotential_eq_potential μ _ (sharpness_riesz_pair_symmetric s)]
    rw [sharpness_riesz_pair_symmetric s x y]
    ring
  have hfSq : Integrable (fun x => (f x)^2) μ := by
    apply (integrable_const (K^2)).mono' (hf.pow 2).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖(f x)^2‖ ≤ K^2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := hbound x
    rw [Real.norm_eq_abs] at hb
    nlinarith [sq_abs (f x), mul_nonneg (sub_nonneg.mpr hb) (add_nonneg hK (abs_nonneg (f x)))]
  let G1 := fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => |H p| * (f p.1)^2
  let G2 := fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => |H p| * (f p.2)^2
  have hib (j : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
      (hjm : Measurable j) : Integrable (fun p => |H p| *(f (j p))^2) (μ.prod μ) := by
    have hi := hiH.abs.bdd_mul ((hf.comp_measurable hjm).pow 2).aestronglyMeasurable
      (c := K^2) (Eventually.of_forall fun p => by
        change ‖(f (j p))^2‖ ≤ K^2
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hb := hbound (j p)
        rw [Real.norm_eq_abs] at hb
        nlinarith [sq_abs (f (j p)), mul_nonneg (sub_nonneg.mpr hb) (add_nonneg hK (abs_nonneg (f (j p))))])
    simpa only [Function.comp_apply, Pi.pow_apply, mul_comm] using hi
  have hi1 : Integrable G1 (μ.prod μ) := hib Prod.fst measurable_fst
  have hi2 : Integrable G2 (μ.prod μ) := hib Prod.snd measurable_snd
  have hb1 : (∫ p, G1 p ∂μ.prod μ) ≤ L * ∫ x, (f x)^2 ∂μ := by
    rw [integral_prod _ hi1, ← integral_const_mul]
    apply integral_mono_ae hi1.integral_prod_left (hfSq.const_mul L)
    apply Eventually.of_forall
    intro x
    change (∫ y, |H (x,y)| * (f x)^2 ∂μ) ≤ L*(f x)^2
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_right
      (sharpness_centered_riesz_row_bound s hs ha ρ M hM hρ x).2 (sq_nonneg _)
  have he2 : (∫ p, G2 p ∂μ.prod μ) = ∫ p, G1 p ∂μ.prod μ := by
    rw [integral_prod_symm _ hi2, integral_prod _ hi1]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    change |H (y,x)| *(f x)^2 = |H (x,y)| *(f x)^2
    rw [hsym y x]
  calc
    _ ≤ ∫ p, |H p * f p.1 * f p.2| ∂μ.prod μ := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun p => H p*f p.1*f p.2) (μ := μ.prod μ)
    _ ≤ ∫ p, (G1 p+G2 p)/2 ∂μ.prod μ := by
      apply integral_mono_ae hiG.abs ((hi1.add hi2).div_const 2)
      apply Eventually.of_forall
      intro p
      change |H p*f p.1*f p.2| ≤ (|H p| *(f p.1)^2+|H p| *(f p.2)^2)/2
      rw [abs_mul, abs_mul]
      have hy : |f p.1| *|f p.2| ≤ ((f p.1)^2+(f p.2)^2)/2 := by
        nlinarith [sq_nonneg (|f p.1|-|f p.2|), sq_abs (f p.1), sq_abs (f p.2)]
      have hh := mul_le_mul_of_nonneg_left hy (abs_nonneg (H p))
      nlinarith
    _ = ((∫ p, G1 p ∂μ.prod μ)+(∫ p, G2 p ∂μ.prod μ))/2 := by
      rw [integral_div, integral_add hi1 hi2]
    _ ≤ _ := by rw [he2]; linarith

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_centered_riesz_bounded_form_le
#check @DGRHS.Gaussian.sharpness_centered_riesz_bounded_form_le
