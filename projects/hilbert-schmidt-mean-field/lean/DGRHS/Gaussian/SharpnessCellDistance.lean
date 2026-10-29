import DGRHS.Gaussian.SharpnessInitialCube
import DGRHS.Gaussian.SharpnessDyadic

noncomputable section
open MeasureTheory Set BoxIntegral
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma sharpness_norm_le_coordinate_cap [Nonempty ι] (u : EuclideanSpace ℝ ι)
    {T : ℝ} (hT : 0 ≤ T) (hu : ∀ i, |u i| ≤ T) :
    ‖u‖ ≤ (Fintype.card ι : ℝ)*T := by
  have hs : ‖u‖^2 ≤ (Fintype.card ι : ℝ)*T^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : ι, T^2 := Finset.sum_le_sum (fun i _ => by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hu i) 2)
      _ = _ := by simp
  have hd : (1:ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  have hdd : (Fintype.card ι : ℝ) ≤ (Fintype.card ι : ℝ)^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hdd (sq_nonneg T)
  have ht : 0 ≤ (Fintype.card ι : ℝ)*T := by positivity
  nlinarith [norm_nonneg u]

/-- Every point in the two actual cells is close when one genuine pair in
those cells is close.  This supplies the source cell-displacement estimate. -/
lemma sharpness_two_cell_distance [Nonempty ι] (J K : Box ι) {δ R : ℝ}
    (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (hJ : ∀ i, J.upper i-J.lower i = δ) (hK : ∀ i, K.upper i-K.lower i = δ)
    {x y : ι → ℝ} (hx : x ∈ J) (hy : y ∈ K) (hxy : dist x y ≤ R)
    {u v : EuclideanSpace ℝ ι} (hu : WithLp.ofLp u ∈ J) (hv : WithLp.ofLp v ∈ K) :
    ‖u-v‖ ≤ (Fintype.card ι : ℝ)*(R+2*δ) := by
  apply sharpness_norm_le_coordinate_cap (u-v) (by positivity)
  intro i
  have hdist : |x i-y i| ≤ R := by
    simpa only [Real.dist_eq] using (dist_pi_le_iff hR).mp hxy i
  have hab := abs_le.mp hdist
  change ∀ i, x i ∈ Ioc (J.lower i) (J.upper i) at hx
  change ∀ i, y i ∈ Ioc (K.lower i) (K.upper i) at hy
  change ∀ i, u i ∈ Ioc (J.lower i) (J.upper i) at hu
  change ∀ i, v i ∈ Ioc (K.lower i) (K.upper i) at hv
  change |u i-v i| ≤ R+2*δ
  exact abs_le.mpr ⟨by linarith [(hx i).2,(hy i).1,(hu i).1,(hv i).2,hab.1,hJ i,hK i],
    by linarith [(hx i).1,(hy i).2,(hu i).2,(hv i).1,hab.2,hJ i,hK i]⟩

lemma sharpness_two_cell_distance_shell [Nonempty ι] (J K : Box ι) {δ R : ℝ}
    (hδ : 0 ≤ δ) (hR : 0 ≤ R) (hδR : δ ≤ R/4)
    (hJ : ∀ i, J.upper i-J.lower i = δ) (hK : ∀ i, K.upper i-K.lower i = δ)
    {x y : ι → ℝ} (hx : x ∈ J) (hy : y ∈ K) (hxy : dist x y ≤ R)
    {u v : EuclideanSpace ℝ ι} (hu : WithLp.ofLp u ∈ J) (hv : WithLp.ofLp v ∈ K) :
    ‖u-v‖ ≤ (3/2 : ℝ)*(Fintype.card ι : ℝ)*R := by
  have hh := sharpness_two_cell_distance J K hδ hR hJ hK hx hy hxy hu hv
  have hd : (0:ℝ) ≤ Fintype.card ι := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hδR hd]

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_norm_le_coordinate_cap
#print axioms DGRHS.Gaussian.sharpness_two_cell_distance_shell
#check @DGRHS.Gaussian.sharpness_two_cell_distance_shell
