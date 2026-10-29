import DGRHS.Gaussian.LogPhysicalConvolution

/-! Log-tail cancellation before L2 estimation. The source pairwise log L1
assumption gives log(1+norm) L1, while min of the two independent tails has
an actual integrable square. No raw logarithmic L2 tail is assumed.
Source SHA256 6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def logTailAdjustedPair (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : ℝ :=
  logPhysicalPair p + Real.log (1+‖p.1‖) + Real.log (1+‖p.2‖)

lemma logTailAdjustedPair_nonneg (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    0 ≤ logTailAdjustedPair p := by
  have h := logPhysicalPair_lower p
  unfold logTailAdjustedPair
  linarith

lemma logTailAdjustedPair_le_ordered (q : ℝ) (hq : 0 < q)
    (x y : EuclideanSpace ℝ ι) (hxy : ‖x‖ ≤ ‖y‖) :
    logTailAdjustedPair (x,y) ≤ gaussianRieszPhysicalPair q (x,y) +
      2*Real.log (1+‖x‖) + Real.log 2 := by
  have hx0 : 0 ≤ Real.log (1+‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
  by_cases hy : ‖y‖ ≤ 2*‖x‖+1
  · have hL := Real.log_le_log (by positivity : 0 < 1+‖y‖)
      (show 1+‖y‖ ≤ 2*(1+‖x‖) by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (1+‖x‖) ≠ 0)] at hL
    have hR := logPhysicalPair_upper q hq (x,y)
    unfold logTailAdjustedPair
    linarith
  · have hn := norm_sub_le x (x-y)
    simp only [sub_sub_cancel] at hn
    have hr : 0 < ‖x-y‖ := by linarith [norm_nonneg x]
    have hL := Real.log_le_log (by positivity : 0 < 1+‖y‖)
      (show 1+‖y‖ ≤ 2*‖x-y‖ by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hr.ne'] at hL
    have hR : 0 ≤ gaussianRieszPhysicalPair q (x,y) := by unfold gaussianRieszPhysicalPair; positivity
    unfold logTailAdjustedPair logPhysicalPair
    linarith

lemma logTailAdjustedPair_le (q : ℝ) (hq : 0 < q)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    logTailAdjustedPair p ≤ gaussianRieszPhysicalPair q p +
      2*min (Real.log (1+‖p.1‖)) (Real.log (1+‖p.2‖)) + Real.log 2 := by
  by_cases hxy : ‖p.1‖ ≤ ‖p.2‖
  · have hL := Real.log_le_log (by positivity : 0 < 1+‖p.1‖) (by linarith : 1+‖p.1‖ ≤ 1+‖p.2‖)
    rw [min_eq_left hL]
    exact logTailAdjustedPair_le_ordered q hq p.1 p.2 hxy
  · have hL := Real.log_le_log (by positivity : 0 < 1+‖p.2‖) (by linarith : 1+‖p.2‖ ≤ 1+‖p.1‖)
    rw [min_eq_right hL]
    have h := logTailAdjustedPair_le_ordered q hq p.2 p.1 (le_of_not_ge hxy)
    have he : logTailAdjustedPair (p.2,p.1) = logTailAdjustedPair p := by
      simp only [logTailAdjustedPair, logPhysicalPair, norm_sub_rev]
      ring
    rw [he] at h
    simpa only [gaussianRieszPhysicalPair, norm_sub_rev] using h

lemma min_sq_le_product (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (min a b)^2 ≤ a*b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr h)]
  · rw [min_eq_right h]
    nlinarith [mul_nonneg hb (sub_nonneg.mpr h)]

lemma logTailAdjustedPair_sq_bound (q : ℝ) (hq : 0 < q)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (logTailAdjustedPair p)^2 ≤ 3*(gaussianRieszPhysicalPair q p)^2 +
      12*(Real.log (1+‖p.1‖)*Real.log (1+‖p.2‖)) + 3*(Real.log 2)^2 := by
  have h1 := logTailAdjustedPair_nonneg p
  have h2 := logTailAdjustedPair_le q hq p
  have ha : 0 ≤ Real.log (1+‖p.1‖) := Real.log_nonneg (by linarith [norm_nonneg p.1])
  have hb : 0 ≤ Real.log (1+‖p.2‖) := Real.log_nonneg (by linarith [norm_nonneg p.2])
  have hR : 0 ≤ gaussianRieszPhysicalPair q p := by unfold gaussianRieszPhysicalPair; positivity
  have hm : 0 ≤ min (Real.log (1+‖p.1‖)) (Real.log (1+‖p.2‖)) := le_min ha hb
  have hc : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsq : (logTailAdjustedPair p)^2 ≤
      (gaussianRieszPhysicalPair q p + 2*min (Real.log (1+‖p.1‖)) (Real.log (1+‖p.2‖)) + Real.log 2)^2 := by
    nlinarith
  have hmin := min_sq_le_product _ _ ha hb
  nlinarith [sq_nonneg (gaussianRieszPhysicalPair q p-2*min (Real.log (1+‖p.1‖)) (Real.log (1+‖p.2‖))),
    sq_nonneg (gaussianRieszPhysicalPair q p-Real.log 2),
    sq_nonneg (2*min (Real.log (1+‖p.1‖)) (Real.log (1+‖p.2‖))-Real.log 2)]

lemma stronglyMeasurable_logTailAdjustedPair : StronglyMeasurable (logTailAdjustedPair (ι := ι)) := by
  unfold logTailAdjustedPair logPhysicalPair
  apply Measurable.stronglyMeasurable
  exact ((Real.measurable_log.comp (by fun_prop)).neg.add
    (Real.measurable_log.comp (by fun_prop))).add (Real.measurable_log.comp (by fun_prop))

lemma memLp_logTailAdjustedPair (q : ℝ) (hq : 0 < q)
    (hd : 0 < (Fintype.card ι : ℝ)/2-q)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    MemLp logTailAdjustedPair 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  let μ := gaussianRieszDensityMeasure ρ
  have ht := integrable_log_one_add_norm_of_pair_log μ hpair
  have hR := memLp_gaussianRieszPhysicalPair q hq hd ρ M hM hρ
  have hbound := ((hR.integrable_sq.const_mul 3).add ((ht.mul_prod ht).const_mul 12)).add
    (integrable_const (3*(Real.log 2)^2))
  apply (memLp_two_iff_integrable_sq stronglyMeasurable_logTailAdjustedPair.aestronglyMeasurable).2
  refine hbound.mono' (stronglyMeasurable_logTailAdjustedPair.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall (fun p => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact logTailAdjustedPair_sq_bound q hq p

lemma hoeffdingCentered_separable_sum (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ] (f : EuclideanSpace ℝ ι → ℝ) (hf : Integrable f μ)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    hoeffdingCentered μ (fun z => f z.1+f z.2) p = 0 := by
  have h1 := hf.comp_fst μ
  have h2 := hf.comp_snd μ
  have he1 : (∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, f z.1 ∂μ.prod μ) = ∫ x, f x ∂μ := by
    rw [integral_prod _ h1]
    simp
  have he2 : (∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, f z.2 ∂μ.prod μ) = ∫ x, f x ∂μ := by
    rw [integral_prod_symm _ h2]
    simp
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  change f p.1+f p.2 - (∫ y, f p.1+f y ∂μ) - (∫ x, f x+f p.2 ∂μ) +
    (∫ z, f z.1+f z.2 ∂μ.prod μ) = 0
  rw [integral_add (integrable_const _) hf, integral_add hf (integrable_const _), integral_add h1 h2]
  simp only [integral_const, probReal_univ, one_smul, he1, he2]
  ring

lemma memLp_logPhysicalCenteredPair (q : ℝ) (hq : 0 < q)
    (hd : 0 < (Fintype.card ι : ℝ)/2-q)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    MemLp (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  let μ := gaussianRieszDensityMeasure ρ
  let f : EuclideanSpace ℝ ι → ℝ := fun x => Real.log (1+‖x‖)
  let S : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℝ := fun p => f p.1+f p.2
  have hf := integrable_log_one_add_norm_of_pair_log μ hpair
  have hS : Integrable S (μ.prod μ) := (hf.comp_fst μ).add (hf.comp_snd μ)
  have hJ := memLp_logTailAdjustedPair q hq hd ρ M hM hρ hpair
  have heS : (logTailAdjustedPair (ι := ι) - S) = logPhysicalPair := by
    funext p
    simp only [Pi.sub_apply, logTailAdjustedPair, S, f]
    ring
  have he : hoeffdingCentered μ logPhysicalPair =ᵐ[μ.prod μ]
      hoeffdingCentered μ logTailAdjustedPair := by
    have h := ae_hoeffdingCentered_sub μ logTailAdjustedPair S (hJ.integrable (by norm_num)) hS
    rw [heS] at h
    filter_upwards [h] with p hp
    have hz : hoeffdingCentered μ S p = 0 := hoeffdingCentered_separable_sum μ f hf p
    simpa only [Pi.sub_apply, hz, sub_zero] using hp
  exact (memLp_congr_ae he).2 (memLp_hoeffdingCentered μ _ stronglyMeasurable_logTailAdjustedPair hJ)

lemma logPhysical_source_proper_bounds (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (x : EuclideanSpace ℝ ι) :
    Integrable (fun y => logPhysicalPair (x,y)) (gaussianRieszDensityMeasure ρ) ∧
    -Real.log (1+‖x‖)-logPhysicalTailIntegral (gaussianRieszDensityMeasure ρ) ≤
      logPhysicalPotential (gaussianRieszDensityMeasure ρ) x ∧
    logPhysicalPotential (gaussianRieszDensityMeasure ρ) x ≤
      gaussianRieszPhysicalPotentialConstant ((Fintype.card ι : ℝ)/4) M ι :=
  logPhysicalPotential_proper_bounds ((Fintype.card ι : ℝ)/4) (by positivity)
    (by linarith) ρ M hM hρ hpair x

lemma memLp_logPhysicalCenteredPair_source (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    MemLp (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) :=
  memLp_logPhysicalCenteredPair ((Fintype.card ι : ℝ)/4) (by positivity)
    (by linarith) ρ M hM hρ hpair

end DGRHS.Gaussian

#check @DGRHS.Gaussian.logTailAdjustedPair
#print axioms DGRHS.Gaussian.logTailAdjustedPair

#check @DGRHS.Gaussian.logTailAdjustedPair_nonneg
#print axioms DGRHS.Gaussian.logTailAdjustedPair_nonneg

#check @DGRHS.Gaussian.logTailAdjustedPair_le_ordered
#print axioms DGRHS.Gaussian.logTailAdjustedPair_le_ordered

#check @DGRHS.Gaussian.logTailAdjustedPair_le
#print axioms DGRHS.Gaussian.logTailAdjustedPair_le

#check @DGRHS.Gaussian.min_sq_le_product
#print axioms DGRHS.Gaussian.min_sq_le_product

#check @DGRHS.Gaussian.logTailAdjustedPair_sq_bound
#print axioms DGRHS.Gaussian.logTailAdjustedPair_sq_bound

#check @DGRHS.Gaussian.stronglyMeasurable_logTailAdjustedPair
#print axioms DGRHS.Gaussian.stronglyMeasurable_logTailAdjustedPair

#check @DGRHS.Gaussian.memLp_logTailAdjustedPair
#print axioms DGRHS.Gaussian.memLp_logTailAdjustedPair

#check @DGRHS.Gaussian.hoeffdingCentered_separable_sum
#print axioms DGRHS.Gaussian.hoeffdingCentered_separable_sum

#check @DGRHS.Gaussian.memLp_logPhysicalCenteredPair
#print axioms DGRHS.Gaussian.memLp_logPhysicalCenteredPair

#check @DGRHS.Gaussian.logPhysical_source_proper_bounds
#print axioms DGRHS.Gaussian.logPhysical_source_proper_bounds

#check @DGRHS.Gaussian.memLp_logPhysicalCenteredPair_source
#print axioms DGRHS.Gaussian.memLp_logPhysicalCenteredPair_source
