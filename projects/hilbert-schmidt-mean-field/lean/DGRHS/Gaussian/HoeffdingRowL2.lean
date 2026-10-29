import DGRHS.Gaussian.HoeffdingLinearity

/-! Proper product L2 and an actual raw row-square bound imply a centered
row-square bound. All marginal bounds are derived by Jensen and Fubini. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Gaussian
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

set_option maxHeartbeats 1000000 in
lemma ae_row_sq_hoeffdingCentered_le (W : X × X → ℝ) (hWm : StronglyMeasurable W)
    (hW : MemLp W 2 (μ.prod μ)) (K : ℝ)
    (hrow : ∀ᵐ x ∂μ, (∫ y, W (x,y)^2 ∂μ) ≤ K) :
    ∀ᵐ x ∂μ, (∫ y, hoeffdingCentered μ W (x,y)^2 ∂μ) ≤ 16*K := by
  let m1 : X → ℝ := fun x => ∫ y, W (x,y) ∂μ
  let m2 : X → ℝ := fun y => ∫ x, W (x,y) ∂μ
  let c : ℝ := ∫ p, W p ∂μ.prod μ
  have h1 := memLp_firstMarginal μ W hWm hW
  have h2 := memLp_secondMarginal μ W hWm hW
  have hcen := memLp_hoeffdingCentered μ W hWm hW
  have hj : (∫ p, W p^2 ∂μ.prod μ) ≤ K := by
    rw [integral_prod _ hW.integrable_sq]
    calc
      _ ≤ ∫ _ : X, K ∂μ := integral_mono_ae hW.integrable_sq.integral_prod_left (integrable_const K) hrow
      _ = _ := by simp
  have hm2le : (∫ y, m2 y^2 ∂μ) ≤ K :=
    (integral_sq_secondMarginal_le μ W hWm hW).trans hj
  have hcle : c^2 ≤ K :=
    (integral_sq_mean_le W (hW.integrable (by norm_num)) hW.integrable_sq).trans hj
  have hp (w u v z : ℝ) : (w-u-v+z)^2 ≤ 4*(w^2+u^2+v^2+z^2) := by
    nlinarith only [sq_nonneg (w+u), sq_nonneg (w+v), sq_nonneg (w-z),
      sq_nonneg (u-v), sq_nonneg (u+z), sq_nonneg (v+z)]
  filter_upwards [hrow, ae_sq_firstMarginal_le μ W hW,
    hW.integrable_sq.prod_right_ae, hcen.integrable_sq.prod_right_ae] with x hx hx1 hix hic
  have hm1le : m1 x^2 ≤ K := hx1.trans hx
  calc
    _ ≤ ∫ y, 4*(W (x,y)^2+m1 x^2+m2 y^2+c^2) ∂μ :=
      integral_mono_ae hic
        ((((hix.add (integrable_const (m1 x^2))).add h2.integrable_sq).add (integrable_const (c^2))).const_mul 4)
        (Filter.Eventually.of_forall (fun y => hp _ _ _ _))
    _ = 4*((∫ y,W (x,y)^2 ∂μ)+m1 x^2+(∫ y,m2 y^2 ∂μ)+c^2) := by
      rw [integral_const_mul, integral_add _ (integrable_const (c^2)),
        integral_add _ h2.integrable_sq, integral_add hix (integrable_const (m1 x^2))]
      · simp [m2]
      · exact hix.add (integrable_const (m1 x^2))
      · exact (hix.add (integrable_const (m1 x^2))).add h2.integrable_sq
    _ ≤ _ := by linarith

end DGRHS.Gaussian
#check DGRHS.Gaussian.ae_row_sq_hoeffdingCentered_le
#print axioms DGRHS.Gaussian.ae_row_sq_hoeffdingCentered_le
