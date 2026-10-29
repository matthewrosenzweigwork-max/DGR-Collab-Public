import DGRHS.Gaussian.LogPhysicalCenteredL2

/-! every-x two-sided potential tail and actual exponential-tail equivalence. -/
noncomputable section
open MeasureTheory Real
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma logPhysicalPotential_tail_upper (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (x : EuclideanSpace ℝ ι) :
    logPhysicalPotential (gaussianRieszDensityMeasure ρ) x + Real.log (1 + ‖x‖) ≤
      gaussianRieszPhysicalPotentialConstant ((Fintype.card ι : ℝ) / 4) M ι +
        logPhysicalTailIntegral (gaussianRieszDensityMeasure ρ) + Real.log 2 := by
  let μ := gaussianRieszDensityMeasure ρ
  let q : ℝ := (Fintype.card ι : ℝ) / 4
  have hq : 0 < q := by dsimp [q]; positivity
  have hqd : 0 < (Fintype.card ι : ℝ)/2-q := by dsimp [q]; linarith
  have hlog := logPhysical_source_proper_bounds hd ρ M hM hρ hpair x
  have ht := integrable_log_one_add_norm_of_pair_log μ hpair
  have hR := gaussianRieszPhysicalPotential_bound q hq hqd ρ M hM hρ x
  have hb := integral_mono (hlog.1.add (integrable_const (Real.log (1+‖x‖))))
    ((hR.1.add ht).add (integrable_const (Real.log 2))) (fun y => by
      have hp := logTailAdjustedPair_le q hq (x,y)
      have hm := min_le_right (Real.log (1+‖x‖)) (Real.log (1+‖y‖))
      dsimp [logTailAdjustedPair] at hp
      change logPhysicalPair (x,y) + Real.log (1+‖x‖) ≤
        gaussianRieszPhysicalPair q (x,y) + Real.log (1+‖y‖) + Real.log 2
      linarith)
  have hRu := hR.2.2
  change (∫ y, gaussianRieszPhysicalPair q (x,y) ∂μ) ≤
    gaussianRieszPhysicalPotentialConstant q M ι at hRu
  have hb' : logPhysicalPotential μ x + Real.log (1+‖x‖) ≤
      (∫ y, gaussianRieszPhysicalPair q (x,y) ∂μ) + logPhysicalTailIntegral μ + Real.log 2 := by
    change (∫ y, logPhysicalPair (x,y) + Real.log (1+‖x‖) ∂μ) ≤
      ∫ y, (gaussianRieszPhysicalPair q (x,y) + Real.log (1+‖y‖)) + Real.log 2 ∂μ at hb
    have hRa : Integrable (fun y => gaussianRieszPhysicalPair q (x,y) + Real.log (1+‖y‖)) μ := hR.1.add ht
    have heR : (∫ y,(gaussianRieszPhysicalPair q (x,y) + Real.log (1+‖y‖)) + Real.log 2 ∂μ) =
        (∫ y,gaussianRieszPhysicalPair q (x,y) ∂μ) + logPhysicalTailIntegral μ + Real.log 2 := by
      calc
        _ = (∫ y,gaussianRieszPhysicalPair q (x,y) + Real.log (1+‖y‖) ∂μ) +
            ∫ _ : EuclideanSpace ℝ ι,Real.log 2 ∂μ := integral_add hRa (integrable_const _)
        _ = _ := by rw [integral_add hR.1 ht]; simp [logPhysicalTailIntegral, μ]
    rw [heR,integral_add hlog.1 (integrable_const _)] at hb
    simpa [logPhysicalPotential, logPhysicalTailIntegral] using hb
  exact hb'.trans (by linarith)

lemma integral_norm_logPhysicalPair_section_le (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (x : EuclideanSpace ℝ ι) :
    (∫ y, ‖logPhysicalPair (x,y)‖ ∂gaussianRieszDensityMeasure ρ) ≤
      gaussianRieszPhysicalPotentialConstant ((Fintype.card ι : ℝ)/4) M ι +
        Real.log (1+‖x‖) + logPhysicalTailIntegral (gaussianRieszDensityMeasure ρ) := by
  let μ := gaussianRieszDensityMeasure ρ
  let q : ℝ := (Fintype.card ι : ℝ)/4
  have hq : 0 < q := by dsimp [q]; positivity
  have hqd : 0 < (Fintype.card ι : ℝ)/2-q := by dsimp [q]; linarith
  have hi := (logPhysical_source_proper_bounds hd ρ M hM hρ hpair x).1
  have ht := integrable_log_one_add_norm_of_pair_log μ hpair
  have hR := gaussianRieszPhysicalPotential_bound q hq hqd ρ M hM hρ x
  have hb := integral_mono hi.norm
    ((hR.1.add (integrable_const (Real.log (1+‖x‖)))).add ht)
    (fun y => logPhysicalPair_norm_bound q hq (x,y))
  have hRu := hR.2.2
  change (∫ y, gaussianRieszPhysicalPair q (x,y) ∂μ) ≤
    gaussianRieszPhysicalPotentialConstant q M ι at hRu
  have hb' : (∫ y, ‖logPhysicalPair (x,y)‖ ∂μ) ≤
      (∫ y, gaussianRieszPhysicalPair q (x,y) ∂μ) + Real.log (1+‖x‖) + logPhysicalTailIntegral μ := by
    change (∫ y, ‖logPhysicalPair (x,y)‖ ∂μ) ≤
      ∫ y, (gaussianRieszPhysicalPair q (x,y) + Real.log (1+‖x‖)) + Real.log (1+‖y‖) ∂μ at hb
    have hRa : Integrable (fun y => gaussianRieszPhysicalPair q (x,y) + Real.log (1+‖x‖)) μ :=
      hR.1.add (integrable_const _)
    have heR : (∫ y,(gaussianRieszPhysicalPair q (x,y) + Real.log (1+‖x‖)) + Real.log (1+‖y‖) ∂μ) =
        (∫ y,gaussianRieszPhysicalPair q (x,y) ∂μ) + Real.log (1+‖x‖) + logPhysicalTailIntegral μ := by
      calc
        _ = (∫ y,gaussianRieszPhysicalPair q (x,y) + Real.log (1+‖x‖) ∂μ) +
            ∫ y,Real.log (1+‖y‖) ∂μ := integral_add hRa ht
        _ = _ := by rw [integral_add hR.1 (integrable_const _)]; simp [logPhysicalTailIntegral, μ]
    rw [heR] at hb
    exact hb
  exact hb'.trans (by linarith)

lemma integrable_log_spatial_exponential_of_potential (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (c : ℝ) (hc : 0 ≤ c)
    (he : Integrable (fun x => Real.exp (-c * logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
      (gaussianRieszDensityMeasure ρ)) :
    Integrable (fun x => Real.exp (c * Real.log (1+‖x‖))) (gaussianRieszDensityMeasure ρ) := by
  let μ := gaussianRieszDensityMeasure ρ
  let C := gaussianRieszPhysicalPotentialConstant ((Fintype.card ι : ℝ)/4) M ι +
    logPhysicalTailIntegral μ + Real.log 2
  have hm : Measurable (fun x : EuclideanSpace ℝ ι => Real.exp (c * Real.log (1+‖x‖))) := by fun_prop
  apply (he.const_mul (Real.exp (c*C))).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := logPhysicalPotential_tail_upper hd ρ M hM hρ hpair x
    have hm := mul_le_mul_of_nonneg_left h hc
    dsimp [C]
    nlinarith)

lemma integrable_log_potential_exponential_of_spatial
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (c : ℝ) (hc : 0 ≤ c)
    (he : Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (c * Real.log (1+‖x‖)))
      (gaussianRieszDensityMeasure ρ)) :
    Integrable (fun x => Real.exp (-c * logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
      (gaussianRieszDensityMeasure ρ) := by
  let μ := gaussianRieszDensityMeasure ρ
  have hp := logPhysicalPotential_integrable μ hpair
  have hm := Real.continuous_exp.comp_aestronglyMeasurable (hp.aestronglyMeasurable.const_mul (-c))
  apply (he.const_mul (Real.exp (c * logPhysicalTailIntegral μ))).mono' hm
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := (logPhysical_source_proper_bounds hd ρ M hM hρ hpair x).2.1
    have hm := mul_le_mul_of_nonneg_left h hc
    nlinarith)

end DGRHS.Gaussian

#check @DGRHS.Gaussian.logPhysicalPotential_tail_upper
#print axioms DGRHS.Gaussian.logPhysicalPotential_tail_upper

#check @DGRHS.Gaussian.integral_norm_logPhysicalPair_section_le
#print axioms DGRHS.Gaussian.integral_norm_logPhysicalPair_section_le

#check @DGRHS.Gaussian.integrable_log_spatial_exponential_of_potential
#print axioms DGRHS.Gaussian.integrable_log_spatial_exponential_of_potential

#check @DGRHS.Gaussian.integrable_log_potential_exponential_of_spatial
#print axioms DGRHS.Gaussian.integrable_log_potential_exponential_of_spatial

