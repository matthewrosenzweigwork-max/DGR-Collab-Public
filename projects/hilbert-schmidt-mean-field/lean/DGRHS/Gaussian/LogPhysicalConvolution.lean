import DGRHS.Gaussian.LogPhysicalPotential

/-! Proper every-x convolution for the literal physical logarithmic kernel.
The local power majorant is an auxiliary integrability estimate; the physical
kernel remains -log(norm). Source pair-log integrability supplies the tail.
Source SHA256 6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian

lemma neg_log_le_power_majorant (r q : ℝ) (hr : 0 ≤ r) (hq : 0 < q) :
    -Real.log r ≤ r^(-q)/q := by
  simpa only [Real.log_inv, ← Real.rpow_neg_eq_inv_rpow] using
    Real.log_le_rpow_div (inv_nonneg.mpr hr) hq

lemma log_le_log_one_add (r : ℝ) (hr : 0 ≤ r) :
    Real.log r ≤ Real.log (1+r) := by
  by_cases hz : r = 0
  · simp [hz]
  · exact Real.log_le_log (lt_of_le_of_ne hr (Ne.symm hz)) (by linarith)

lemma abs_log_le_power_and_log (r q : ℝ) (hr : 0 ≤ r) (hq : 0 < q) :
    |Real.log r| ≤ r^(-q)/q + Real.log (1+r) := by
  have hp : 0 ≤ r^(-q)/q := by positivity
  have hl : 0 ≤ Real.log (1+r) := Real.log_nonneg (by linarith)
  have hn := neg_log_le_power_majorant r q hr hq
  have hu := log_le_log_one_add r hr
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable {ι : Type*} [Fintype ι]

def logPhysicalPotential (μ : Measure (EuclideanSpace ℝ ι))
    (x : EuclideanSpace ℝ ι) : ℝ := ∫ y, logPhysicalPair (x,y) ∂μ

def logPhysicalTailIntegral (μ : Measure (EuclideanSpace ℝ ι)) : ℝ :=
  ∫ y, Real.log (1+‖y‖) ∂μ

lemma logPhysicalPair_upper (q : ℝ) (hq : 0 < q)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    logPhysicalPair p ≤ gaussianRieszPhysicalPair q p :=
  neg_log_le_power_majorant _ q (norm_nonneg _) hq

lemma logPhysicalPair_lower (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    -Real.log (1+‖p.1‖)-Real.log (1+‖p.2‖) ≤ logPhysicalPair p := by
  have hl := (log_le_log_one_add ‖p.1-p.2‖ (norm_nonneg _)).trans
    (log_one_add_norm_sub_le p.1 p.2)
  unfold logPhysicalPair
  linarith

lemma logPhysicalPair_norm_bound (q : ℝ) (hq : 0 < q)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    ‖logPhysicalPair p‖ ≤ gaussianRieszPhysicalPair q p +
      Real.log (1+‖p.1‖)+Real.log (1+‖p.2‖) := by
  have hl := abs_log_le_power_and_log ‖p.1-p.2‖ q (norm_nonneg _) hq
  have ht := log_one_add_norm_sub_le p.1 p.2
  simp only [logPhysicalPair, Real.norm_eq_abs, abs_neg, gaussianRieszPhysicalPair]
  linarith

lemma logPhysicalPotential_proper_bounds (q : ℝ) (hq : 0 < q)
    (hd : 0 < (Fintype.card ι : ℝ)/2-q)
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
      gaussianRieszPhysicalPotentialConstant q M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  have htail := integrable_log_one_add_norm_of_pair_log μ hpair
  have hR := gaussianRieszPhysicalPotential_bound q hq hd ρ M hM hρ x
  have hi : Integrable (fun y => logPhysicalPair (x,y)) μ := by
    refine ((hR.1.add (integrable_const (Real.log (1+‖x‖)))).add htail).mono'
      ((Real.measurable_log.comp (by fun_prop : Measurable (fun y => ‖x-y‖))).neg).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => ?_))
    exact logPhysicalPair_norm_bound q hq (x,y)
  refine ⟨hi, ?_, ?_⟩
  · have hb := integral_mono ((integrable_const (-Real.log (1+‖x‖))).sub htail) hi
      (fun y => logPhysicalPair_lower (x,y))
    simpa [logPhysicalPotential, logPhysicalTailIntegral, integral_sub, htail] using hb
  · have hb := integral_mono hi hR.1 (fun y => logPhysicalPair_upper q hq (x,y))
    exact hb.trans hR.2.2

lemma logPhysicalPotential_integrable (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ] (hpair : Integrable logPhysicalPair (μ.prod μ)) :
    Integrable (logPhysicalPotential μ) μ := hpair.integral_prod_left

end DGRHS.Gaussian

#check @DGRHS.Gaussian.neg_log_le_power_majorant
#print axioms DGRHS.Gaussian.neg_log_le_power_majorant

#check @DGRHS.Gaussian.log_le_log_one_add
#print axioms DGRHS.Gaussian.log_le_log_one_add

#check @DGRHS.Gaussian.abs_log_le_power_and_log
#print axioms DGRHS.Gaussian.abs_log_le_power_and_log

#check @DGRHS.Gaussian.logPhysicalPotential
#print axioms DGRHS.Gaussian.logPhysicalPotential

#check @DGRHS.Gaussian.logPhysicalTailIntegral
#print axioms DGRHS.Gaussian.logPhysicalTailIntegral

#check @DGRHS.Gaussian.logPhysicalPair_upper
#print axioms DGRHS.Gaussian.logPhysicalPair_upper

#check @DGRHS.Gaussian.logPhysicalPair_lower
#print axioms DGRHS.Gaussian.logPhysicalPair_lower

#check @DGRHS.Gaussian.logPhysicalPair_norm_bound
#print axioms DGRHS.Gaussian.logPhysicalPair_norm_bound

#check @DGRHS.Gaussian.logPhysicalPotential_proper_bounds
#print axioms DGRHS.Gaussian.logPhysicalPotential_proper_bounds

#check @DGRHS.Gaussian.logPhysicalPotential_integrable
#print axioms DGRHS.Gaussian.logPhysicalPotential_integrable
