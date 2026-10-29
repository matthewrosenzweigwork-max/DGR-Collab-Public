import DGRHS.Gaussian.GaussianLogCutoffPositivity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Supporting development. The actual centered full logarithmic operator is positive
by the derived cutoff positivity and actual centered-short operator norm rate. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma stronglyMeasurable_logPhysicalPair :
    StronglyMeasurable (logPhysicalPair (E := EuclideanSpace ℝ ι)) := by
  unfold logPhysicalPair
  exact (Real.measurable_log.comp (by fun_prop)).neg.stronglyMeasurable

lemma stronglyMeasurable_logPhysicalCenteredPair
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    StronglyMeasurable (hoeffdingCentered μ logPhysicalPair) :=
  stronglyMeasurable_hoeffdingCentered μ _ stronglyMeasurable_logPhysicalPair

lemma logPhysicalCenteredPair_symmetric
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (x y : EuclideanSpace ℝ ι) :
    hoeffdingCentered μ logPhysicalPair (x,y) = hoeffdingCentered μ logPhysicalPair (y,x) := by
  exact DGRHS.centeredKernel_symmetric μ (fun a b => logPhysicalPair (a,b))
    (fun a b => by unfold logPhysicalPair; rw [norm_sub_rev]) x y

lemma logPhysicalCenteredPair_canonical
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hpair : Integrable logPhysicalPair (μ.prod μ)) :
    ∀ᵐ x ∂μ, ∫ y, hoeffdingCentered μ logPhysicalPair (x,y) ∂μ = 0 :=
  DGRHS.integral_centeredKernel_right μ (fun x y => logPhysicalPair (x,y)) hpair

lemma logPhysicalCenteredOperator_positive (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    ∀ v, 0 ≤ inner ℝ v (logPhysicalCenteredOperator hd ρ M hM hρ hpair v) := by
  let η : ℕ → ℝ := fun N => 1/((N : ℝ)+1)
  have hη (N : ℕ) : 0 < η N := by dsimp [η]; positivity
  let A := fun N => gaussianLogTruncatedOperator (η N) (hη N) hd ρ M hM hρ hpair
  let T := logPhysicalCenteredOperator hd ρ M hM hρ hpair
  have hpow : Tendsto (fun N => (η N)^((Fintype.card ι : ℝ)/2)) atTop (𝓝 0) := by
    simpa only [η, Function.comp_def,Real.zero_rpow (by linarith : (Fintype.card ι : ℝ)/2 ≠ 0)] using
      ((Real.continuousAt_rpow_const 0 _ (Or.inr (by linarith : 0 ≤ (Fintype.card ι : ℝ)/2))).tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hc : Tendsto (fun N => ‖A N-T‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun N => norm_nonneg _) _
      (by simpa only [mul_zero, mul_assoc] using (hpow.const_mul (4*(Real.sqrt (M*Real.pi^((Fintype.card ι : ℝ)/2))/((Fintype.card ι : ℝ)/2)))))
    intro N
    rw [norm_sub_rev]
    exact norm_logPhysicalCenteredOperator_sub_cutoff_le (η N) (hη N) hd ρ M hM hρ hpair
  exact DGRHS.Kernel.nonnegative_operator_of_tendsto T A
    (tendsto_iff_norm_sub_tendsto_zero.mpr hc)
    (fun N => gaussianLogTruncatedOperator_positive (η N) (hη N) hd ρ M hM hρ hpair)

lemma logPhysicalCenteredPair_operator_positive (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (hh : MemLp (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair) 2
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    ∀ v, 0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair) hh v) := by
  simpa only [logPhysicalCenteredOperator] using
    logPhysicalCenteredOperator_positive hd ρ M hM hρ hpair

end DGRHS.Gaussian
#check @DGRHS.Gaussian.logPhysicalCenteredOperator_positive
#print axioms DGRHS.Gaussian.logPhysicalCenteredOperator_positive

#check @DGRHS.Gaussian.logPhysicalCenteredPair_operator_positive
#print axioms DGRHS.Gaussian.logPhysicalCenteredPair_operator_positive

#check @DGRHS.Gaussian.stronglyMeasurable_logPhysicalPair
#print axioms DGRHS.Gaussian.stronglyMeasurable_logPhysicalPair
#check @DGRHS.Gaussian.stronglyMeasurable_logPhysicalCenteredPair
#print axioms DGRHS.Gaussian.stronglyMeasurable_logPhysicalCenteredPair
#check @DGRHS.Gaussian.logPhysicalCenteredPair_symmetric
#print axioms DGRHS.Gaussian.logPhysicalCenteredPair_symmetric
#check @DGRHS.Gaussian.logPhysicalCenteredPair_canonical
#print axioms DGRHS.Gaussian.logPhysicalCenteredPair_canonical
