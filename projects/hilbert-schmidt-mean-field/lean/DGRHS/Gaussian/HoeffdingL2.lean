import DGRHS.Gaussian.FeatureRateMoments
import DGRHS.Kernel.Separated
import DGRHS.Kernel.Centering

/-! Actual quantitative Hoeffding centering on a probability source.
All marginal square integrability and Jensen bounds come from proper product L2.
No centering operator/norm conclusion is an assumption. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Gaussian
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

lemma ae_sq_firstMarginal_le (W : X × X → ℝ) (hW : MemLp W 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, (∫ y, W (x,y) ∂μ) ^ 2 ≤ ∫ y, W (x,y) ^ 2 ∂μ := by
  have hi := hW.integrable (by norm_num)
  filter_upwards [hi.prod_right_ae, hW.integrable_sq.prod_right_ae] with x hx hx2
  exact integral_sq_mean_le _ hx hx2

lemma ae_sq_secondMarginal_le (W : X × X → ℝ) (hW : MemLp W 2 (μ.prod μ)) :
    ∀ᵐ y ∂μ, (∫ x, W (x,y) ∂μ) ^ 2 ≤ ∫ x, W (x,y) ^ 2 ∂μ := by
  have hi := hW.integrable (by norm_num)
  filter_upwards [hi.prod_left_ae, hW.integrable_sq.prod_left_ae] with y hy hy2
  exact integral_sq_mean_le _ hy hy2

lemma memLp_firstMarginal (W : X × X → ℝ) (hWm : StronglyMeasurable W)
    (hW : MemLp W 2 (μ.prod μ)) : MemLp (fun x => ∫ y, W (x,y) ∂μ) 2 μ := by
  apply (memLp_two_iff_integrable_sq hWm.integral_prod_right'.aestronglyMeasurable).2
  apply hW.integrable_sq.integral_prod_left.mono'
    (hWm.integral_prod_right'.pow 2).aestronglyMeasurable
  filter_upwards [ae_sq_firstMarginal_le μ W hW] with x hx
  change ‖(∫ y, W (x,y) ∂μ) ^ 2‖ ≤ _
  simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hx

lemma memLp_secondMarginal (W : X × X → ℝ) (hWm : StronglyMeasurable W)
    (hW : MemLp W 2 (μ.prod μ)) : MemLp (fun y => ∫ x, W (x,y) ∂μ) 2 μ := by
  apply (memLp_two_iff_integrable_sq hWm.integral_prod_left'.aestronglyMeasurable).2
  apply hW.integrable_sq.integral_prod_right.mono'
    (hWm.integral_prod_left'.pow 2).aestronglyMeasurable
  filter_upwards [ae_sq_secondMarginal_le μ W hW] with y hy
  change ‖(∫ x, W (x,y) ∂μ) ^ 2‖ ≤ _
  simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hy

lemma integral_sq_firstMarginal_le (W : X × X → ℝ) (hWm : StronglyMeasurable W)
    (hW : MemLp W 2 (μ.prod μ)) :
    (∫ x, (∫ y, W (x,y) ∂μ) ^ 2 ∂μ) ≤ ∫ p, W p ^ 2 ∂μ.prod μ := by
  calc
    _ ≤ ∫ x, (∫ y, W (x,y) ^ 2 ∂μ) ∂μ :=
      integral_mono_ae (memLp_firstMarginal μ W hWm hW).integrable_sq
        hW.integrable_sq.integral_prod_left (ae_sq_firstMarginal_le μ W hW)
    _ = _ := (integral_prod _ hW.integrable_sq).symm

lemma integral_sq_secondMarginal_le (W : X × X → ℝ) (hWm : StronglyMeasurable W)
    (hW : MemLp W 2 (μ.prod μ)) :
    (∫ y, (∫ x, W (x,y) ∂μ) ^ 2 ∂μ) ≤ ∫ p, W p ^ 2 ∂μ.prod μ := by
  calc
    _ ≤ ∫ y, (∫ x, W (x,y) ^ 2 ∂μ) ∂μ :=
      integral_mono_ae (memLp_secondMarginal μ W hWm hW).integrable_sq
        hW.integrable_sq.integral_prod_right (ae_sq_secondMarginal_le μ W hW)
    _ = _ := (integral_prod_symm _ hW.integrable_sq).symm

lemma memLp_hoeffdingCentered (W : X × X → ℝ) (hWm : StronglyMeasurable W)
    (hW : MemLp W 2 (μ.prod μ)) :
    MemLp (fun p : X × X => DGRHS.centeredKernel μ (fun x y => W (x,y)) p.1 p.2) 2 (μ.prod μ) := by
  exact ((hW.sub ((memLp_firstMarginal μ W hWm hW).comp_fst μ)).sub
    ((memLp_secondMarginal μ W hWm hW).comp_snd μ)).add (memLp_const _)

lemma integral_sq_hoeffdingCentered_le (W : X × X → ℝ) (hWm : StronglyMeasurable W)
    (hW : MemLp W 2 (μ.prod μ)) :
    (∫ p : X × X, DGRHS.centeredKernel μ (fun x y => W (x,y)) p.1 p.2 ^ 2 ∂μ.prod μ) ≤
      16 * ∫ p, W p ^ 2 ∂μ.prod μ := by
  let m1 : X → ℝ := fun x => ∫ y, W (x,y) ∂μ
  let m2 : X → ℝ := fun y => ∫ x, W (x,y) ∂μ
  let c : ℝ := ∫ p, W p ∂μ.prod μ
  have h1 := memLp_firstMarginal μ W hWm hW
  have h2 := memLp_secondMarginal μ W hWm hW
  have hp (w u v c : ℝ) : (w - u - v + c) ^ 2 ≤ 4 * (w ^ 2 + u ^ 2 + v ^ 2 + c ^ 2) := by
    nlinarith only [sq_nonneg (w+u), sq_nonneg (w+v), sq_nonneg (w-c),
      sq_nonneg (u-v), sq_nonneg (u+c), sq_nonneg (v+c)]
  have hm1 : (∫ p : X × X, m1 p.1 ^ 2 ∂μ.prod μ) = ∫ x, m1 x ^ 2 ∂μ := by
    rw [integral_prod _ (h1.integrable_sq.comp_fst μ)]
    simp [m1]
  have hm2 : (∫ p : X × X, m2 p.2 ^ 2 ∂μ.prod μ) = ∫ y, m2 y ^ 2 ∂μ := by
    rw [integral_prod_symm _ (h2.integrable_sq.comp_snd μ)]
    simp [m2]
  have hm1le := integral_sq_firstMarginal_le μ W hWm hW
  have hm2le := integral_sq_secondMarginal_le μ W hWm hW
  have hcle : c ^ 2 ≤ ∫ p, W p ^ 2 ∂μ.prod μ :=
    integral_sq_mean_le _ (hW.integrable (by norm_num)) hW.integrable_sq
  calc
    _ ≤ ∫ p : X × X, 4 * (W p ^ 2 + m1 p.1 ^ 2 + m2 p.2 ^ 2 + c ^ 2) ∂μ.prod μ :=
      integral_mono_ae (memLp_hoeffdingCentered μ W hWm hW).integrable_sq
        ((((hW.integrable_sq.add (h1.integrable_sq.comp_fst μ)).add
          (h2.integrable_sq.comp_snd μ)).add (integrable_const (c ^ 2))).const_mul 4)
        (Filter.Eventually.of_forall (fun p => hp _ _ _ _))
    _ = 4 * ((∫ p, W p ^ 2 ∂μ.prod μ) + (∫ x, m1 x ^ 2 ∂μ) +
        (∫ y, m2 y ^ 2 ∂μ) + c ^ 2) := by
      rw [integral_const_mul, integral_add _ (integrable_const (c ^ 2)),
        integral_add _ (h2.integrable_sq.comp_snd μ),
        integral_add hW.integrable_sq (h1.integrable_sq.comp_fst μ), hm1, hm2]
      · simp
      · exact hW.integrable_sq.add (h1.integrable_sq.comp_fst μ)
      · exact (hW.integrable_sq.add (h1.integrable_sq.comp_fst μ)).add (h2.integrable_sq.comp_snd μ)
    _ ≤ _ := by dsimp [m1,m2] at *; linarith

set_option maxHeartbeats 1000000 in
lemma norm_hoeffdingCentered_le (W : X × X → ℝ) (hWm : StronglyMeasurable W)
    (hW : MemLp W 2 (μ.prod μ)) :
    ‖(memLp_hoeffdingCentered μ W hWm hW).toLp
      (fun p : X × X => DGRHS.centeredKernel μ (fun x y => W (x,y)) p.1 p.2)‖ ≤ 4 * ‖hW.toLp W‖ := by
  have hs : ‖(memLp_hoeffdingCentered μ W hWm hW).toLp
      (fun p : X × X => DGRHS.centeredKernel μ (fun x y => W (x,y)) p.1 p.2)‖ ^ 2 ≤
      16 * ‖hW.toLp W‖ ^ 2 := by
    rw [DGRHS.Kernel.norm_toLp_sq, DGRHS.Kernel.norm_toLp_sq]
    exact integral_sq_hoeffdingCentered_le μ W hWm hW
  nlinarith [norm_nonneg ((memLp_hoeffdingCentered μ W hWm hW).toLp
    (fun p : X × X => DGRHS.centeredKernel μ (fun x y => W (x,y)) p.1 p.2)), norm_nonneg (hW.toLp W)]

end DGRHS.Gaussian

#check DGRHS.Gaussian.ae_sq_firstMarginal_le
#print axioms DGRHS.Gaussian.ae_sq_firstMarginal_le
#check DGRHS.Gaussian.ae_sq_secondMarginal_le
#print axioms DGRHS.Gaussian.ae_sq_secondMarginal_le
#check DGRHS.Gaussian.memLp_firstMarginal
#print axioms DGRHS.Gaussian.memLp_firstMarginal
#check DGRHS.Gaussian.memLp_secondMarginal
#print axioms DGRHS.Gaussian.memLp_secondMarginal
#check DGRHS.Gaussian.integral_sq_firstMarginal_le
#print axioms DGRHS.Gaussian.integral_sq_firstMarginal_le
#check DGRHS.Gaussian.integral_sq_secondMarginal_le
#print axioms DGRHS.Gaussian.integral_sq_secondMarginal_le
#check DGRHS.Gaussian.memLp_hoeffdingCentered
#print axioms DGRHS.Gaussian.memLp_hoeffdingCentered
#check DGRHS.Gaussian.integral_sq_hoeffdingCentered_le
#print axioms DGRHS.Gaussian.integral_sq_hoeffdingCentered_le

#check DGRHS.Gaussian.norm_hoeffdingCentered_le
#print axioms DGRHS.Gaussian.norm_hoeffdingCentered_le
