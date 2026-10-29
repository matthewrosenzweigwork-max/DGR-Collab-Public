import DGRHS.Gaussian.PeriodicGaussianLatticeBounds
import DGRHS.Gaussian.PeriodicLocalLogCore

/-! Actual summable nonzero lattice images of the short-scale logarithmic
heat kernel. The bounded remainder is derived uniformly on the full centered
fundamental cube, rather than assumed as a Green-kernel hypothesis. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicLocalLogCore_nonneg (r : ℝ) : 0≤periodicLocalLogCore r := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact mul_nonneg (inv_nonneg.mpr ht.1.le) (Real.exp_pos _).le

lemma periodicLocalLogCore_measurable : Measurable periodicLocalLogCore := by
  have hm : Measurable (fun p : ℝ × ℝ => p.2⁻¹*Real.exp (-p.1^2/(2*p.2^2))) := by fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma periodic_nonzero_image_norm_pos (x : EuclideanSpace ℝ ι)
    (hx : ∀ i,|x i|≤1/2) (k : PeriodicFrequency ι) (hk : k≠0) :
    0<‖x+periodicFrequencyVector k‖ := by
  have ha := periodic_lattice_shift_norm_square x hx k
  have hb := periodicFrequency_norm_sq_ge_one hk
  have hn := norm_nonneg (x+periodicFrequencyVector k)
  nlinarith

lemma periodicLocalLogCore_image_bound (x : EuclideanSpace ℝ ι)
    (hx : ∀ i,|x i|≤1/2) (k : PeriodicFrequency ι) (hk : k≠0) :
    periodicLocalLogCore ‖x+periodicFrequencyVector k‖ ≤
      periodicLocalLogCore (Real.sqrt (1/8))*Real.exp (-‖periodicFrequencyVector k‖^2/16) := by
  have hi := periodicLocalLogCore_integrable _ (periodic_nonzero_image_norm_pos x hx k hk)
  have hi2 := (periodicLocalLogCore_integrable (Real.sqrt (1/8)) (by positivity)).mul_const
    (Real.exp (-‖periodicFrequencyVector k‖^2/16))
  have hb : ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) 1),
      t⁻¹*Real.exp (-‖x+periodicFrequencyVector k‖^2/(2*t^2)) ≤
        (t⁻¹*Real.exp (-(Real.sqrt (1/8))^2/(2*t^2)))*Real.exp (-‖periodicFrequencyVector k‖^2/16) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have h := mul_le_mul_of_nonneg_left (periodic_nonzero_lattice_gaussian_bound x hx k hk t ht.1 ht.2)
      (inv_nonneg.mpr ht.1.le)
    rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤1/8)]
    have he : -(1/8:ℝ)/(2*t^2)= -1/(16*t^2) := by ring
    rw [he]
    simpa only [mul_assoc] using h
  have h := integral_mono_ae hi hi2 hb
  rw [integral_mul_const] at h
  exact h

def periodicNonzeroImageTerm (x : EuclideanSpace ℝ ι) (k : PeriodicFrequency ι) : ℝ :=
  if k=0 then 0 else periodicLocalLogCore ‖x+periodicFrequencyVector k‖

def periodicNonzeroImageRemainder (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑' k : PeriodicFrequency ι,periodicNonzeroImageTerm x k

def periodicImageRemainderBound (ι : Type u) [Fintype ι] : ℝ :=
  periodicLocalLogCore (Real.sqrt (1/8))*
    ∑' k : PeriodicFrequency ι,Real.exp (-‖periodicFrequencyVector k‖^2/16)

lemma periodicNonzeroImageTerm_nonneg (x : EuclideanSpace ℝ ι) (k : PeriodicFrequency ι) :
    0≤periodicNonzeroImageTerm x k := by
  unfold periodicNonzeroImageTerm
  split_ifs
  · rfl
  · exact periodicLocalLogCore_nonneg _

lemma periodicNonzeroImageTerm_bound (x : EuclideanSpace ℝ ι)
    (hx : ∀ i,|x i|≤1/2) (k : PeriodicFrequency ι) :
    periodicNonzeroImageTerm x k≤periodicLocalLogCore (Real.sqrt (1/8))*
      Real.exp (-‖periodicFrequencyVector k‖^2/16) := by
  unfold periodicNonzeroImageTerm
  split_ifs with hk
  · exact mul_nonneg (periodicLocalLogCore_nonneg _) (Real.exp_pos _).le
  · exact periodicLocalLogCore_image_bound x hx k hk

lemma summable_periodicNonzeroImageTerm (x : EuclideanSpace ℝ ι)
    (hx : ∀ i,|x i|≤1/2) : Summable (periodicNonzeroImageTerm x) := by
  have hs : Summable (fun k : PeriodicFrequency ι => Real.exp (-‖periodicFrequencyVector k‖^2/16)) := by
    exact (summable_periodicGaussian (ι := ι) (1/16) (by norm_num)).congr
      (fun k => by congr 1; ring)
  exact (hs.mul_left (periodicLocalLogCore (Real.sqrt (1/8)))).of_nonneg_of_le
    (periodicNonzeroImageTerm_nonneg x) (periodicNonzeroImageTerm_bound x hx)

/-- A genuine finite uniform physical lattice-image bound. -/
theorem periodicNonzeroImageRemainder_bounds (x : EuclideanSpace ℝ ι)
    (hx : ∀ i,|x i|≤1/2) :
    0≤periodicNonzeroImageRemainder x ∧ periodicNonzeroImageRemainder x≤periodicImageRemainderBound ι := by
  have hs : Summable (fun k : PeriodicFrequency ι => Real.exp (-‖periodicFrequencyVector k‖^2/16)) := by
    exact (summable_periodicGaussian (ι := ι) (1/16) (by norm_num)).congr
      (fun k => by congr 1; ring)
  refine ⟨tsum_nonneg (periodicNonzeroImageTerm_nonneg x),?_⟩
  have h := Summable.tsum_le_tsum (periodicNonzeroImageTerm_bound x hx)
    (summable_periodicNonzeroImageTerm x hx) (hs.mul_left (periodicLocalLogCore (Real.sqrt (1/8))))
  simpa only [periodicNonzeroImageRemainder,periodicImageRemainderBound,tsum_mul_left] using h

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLocalLogCore_nonneg
#print axioms DGRHS.Periodic.periodicLocalLogCore_measurable
#print axioms DGRHS.Periodic.periodic_nonzero_image_norm_pos
#print axioms DGRHS.Periodic.periodicLocalLogCore_image_bound
#print axioms DGRHS.Periodic.summable_periodicNonzeroImageTerm
#print axioms DGRHS.Periodic.periodicNonzeroImageRemainder_bounds
#check @DGRHS.Periodic.periodicNonzeroImageRemainder_bounds
