import DGRHS.Attractive.SignedGaussianMoments

/-! Actual fourth-power spatial Jensen, with properness proved before use.
The generic support lemma is instantiated below with joint Gaussian moments;
no source remainder moment or rate is an assumption. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Attractive
open DGRHS.Gaussian
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

lemma integrable_lower_powers_of_fourth (f : X → ℝ)
    (hm : AEStronglyMeasurable f μ) (h4 : Integrable (fun x => f x^4) μ) :
    Integrable f μ ∧ Integrable (fun x => f x^2) μ := by
  have h2 : Integrable (fun x => f x^2) μ := by
    apply ((integrable_const (1:ℝ)).add h4).mono' (hm.pow 2)
    filter_upwards [] with x
    change ‖f x^2‖ ≤ 1+f x^4
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (f x^2-1/2)]
  refine ⟨?_, h2⟩
  apply ((integrable_const (1:ℝ)).add h2).mono' hm
  filter_upwards [] with x
  change ‖f x‖ ≤ 1+f x^2
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|f x|-1/2), sq_abs (f x)]

lemma integral_fourth_mean_le (f : X → ℝ)
    (hm : AEStronglyMeasurable f μ) (h4 : Integrable (fun x => f x^4) μ) :
    (∫ x, f x ∂μ)^4 ≤ ∫ x, f x^4 ∂μ := by
  obtain ⟨h1,h2⟩ := integrable_lower_powers_of_fourth f hm h4
  have hs := integral_sq_mean_le f h1 h2
  have hss := integral_sq_mean_le (fun x => f x^2) h2
    (by simpa only [← pow_mul] using h4)
  have hp : 0 ≤ ∫ x, f x^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hh := mul_self_le_mul_self (sq_nonneg (∫ x, f x ∂μ)) hs
  have hss' : (∫ x,f x^2 ∂μ)^2≤∫ x,f x^4 ∂μ := by
    convert hss using 1
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  calc
    (∫ x,f x ∂μ)^4 = (∫ x,f x ∂μ)^2*(∫ x,f x ∂μ)^2 := by ring
    _ ≤ (∫ x,f x^2 ∂μ)*(∫ x,f x^2 ∂μ) := hh
    _ = (∫ x,f x^2 ∂μ)^2 := by ring
    _ ≤ ∫ x,f x^4 ∂μ := hss'


lemma spatial_fourth_moment (f : X × Ω → ℝ) (hm : StronglyMeasurable f)
    (h4 : Integrable (fun p => f p^4) (μ.prod P)) :
    Integrable (fun ω => (∫ x, f (x,ω) ∂μ)^4) P ∧
      (∫ ω, (∫ x, f (x,ω) ∂μ)^4 ∂P) ≤ ∫ p, f p^4 ∂μ.prod P := by
  have hle : ∀ᵐ ω ∂P, (∫ x, f (x,ω) ∂μ)^4 ≤ ∫ x, f (x,ω)^4 ∂μ := by
    filter_upwards [h4.prod_left_ae] with ω hω
    exact integral_fourth_mean_le _
      ((hm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable) hω
  have hi : Integrable (fun ω => (∫ x, f (x,ω) ∂μ)^4) P := by
    apply h4.integral_prod_right.mono' (hm.integral_prod_left'.pow 4).aestronglyMeasurable
    filter_upwards [hle] with ω hω
    change ‖(∫ x,f (x,ω) ∂μ)^4‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hω
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, ∫ x, f (x,ω)^4 ∂μ ∂P := integral_mono_ae hi h4.integral_prod_right hle
    _ = _ := (integral_prod_symm _ h4).symm

end DGRHS.Attractive
#check DGRHS.Attractive.integral_fourth_mean_le
#print axioms DGRHS.Attractive.integral_fourth_mean_le
#check DGRHS.Attractive.spatial_fourth_moment
#print axioms DGRHS.Attractive.spatial_fourth_moment
