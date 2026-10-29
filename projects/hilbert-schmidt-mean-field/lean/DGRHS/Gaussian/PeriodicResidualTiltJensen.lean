import DGRHS.Gaussian.PeriodicFirstShellResidual
import DGRHS.Gaussian.PeriodicTrialParticleMean
import Mathlib.Analysis.Convex.Integral

/-! Actual bounded density product laws and extended residual Jensen.
The residual mean is derived from the genuine Fourier bounded-test form;
no residual expectation or exponential properness conclusion is supplied. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicBoundedDensityLaw (F : PeriodicTorus ι → ℝ) : Measure (PeriodicTorus ι) :=
  (periodicHaar ι).withDensity (fun x => ENNReal.ofReal (F x))

lemma periodicBoundedDensityLaw_probability (F : PeriodicTorus ι → ℝ)
    (hi : Integrable F (periodicHaar ι)) (hn : ∀ x,0≤F x)
    (hmean : (∫ x,F x ∂periodicHaar ι)=1) : IsProbabilityMeasure (periodicBoundedDensityLaw F) := by
  constructor
  unfold periodicBoundedDensityLaw
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn),hmean]
  norm_num

lemma periodicBoundedDensityLaw_residual_pair (F : PeriodicTorus ι → ℝ)
    (hf : Measurable F) (hn : ∀ x,0≤F x) (B : ℝ) (hb : ∀ x,‖F x‖≤B) :
    Integrable (periodicFirstShellResidualPair (ι := ι))
      ((periodicBoundedDensityLaw F).prod (periodicBoundedDensityLaw F)) ∧
    (∫ p,periodicFirstShellResidualPair p
      ∂(periodicBoundedDensityLaw F).prod (periodicBoundedDensityLaw F)) =
      ∫ p,periodicFirstShellResidualPair p*F p.1*F p.2
        ∂(periodicHaar ι).prod (periodicHaar ι) := by
  have hB : 0≤B := (norm_nonneg (F 0)).trans (hb 0)
  have hi := periodic_bounded_pair_test_integrable periodicFirstShellResidualPair
    periodicFirstShellResidualPair_integrable F hf.aestronglyMeasurable B hB hb
  have hd : Measurable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      ENNReal.ofReal (F p.1)*ENNReal.ofReal (F p.2)) :=
    (hf.ennreal_ofReal.comp measurable_fst).mul (hf.ennreal_ofReal.comp measurable_snd)
  have ht : ∀ᵐ p ∂(periodicHaar ι).prod (periodicHaar ι),
      ENNReal.ofReal (F p.1)*ENNReal.ofReal (F p.2)<⊤ :=
    Eventually.of_forall fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have he (p : PeriodicTorus ι × PeriodicTorus ι) :
      (ENNReal.ofReal (F p.1)*ENNReal.ofReal (F p.2)).toReal*periodicFirstShellResidualPair p =
        periodicFirstShellResidualPair p*F p.1*F p.2 := by
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (hn _),ENNReal.toReal_ofReal (hn _)]
    ring
  rw [periodicBoundedDensityLaw,prod_withDensity hf.ennreal_ofReal hf.ennreal_ofReal]
  constructor
  · apply (integrable_withDensity_iff_integrable_smul' hd ht).mpr
    exact hi.congr (Eventually.of_forall fun p => (he p).symm)
  · rw [integral_withDensity_eq_integral_toReal_smul hd ht]
    exact integral_congr_ae (Eventually.of_forall he)

/-- Extended Jensen derives a lower bound without assuming the exponential
is proper. When its lintegral is finite, properness is derived first. -/
lemma periodic_extended_exp_jensen {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (U : X → ℝ) (hU : Integrable U μ) :
    ENNReal.ofReal (Real.exp (∫ x,U x ∂μ)) ≤ ∫⁻ x,ENNReal.ofReal (Real.exp (U x)) ∂μ := by
  by_cases ht : (∫⁻ x,ENNReal.ofReal (Real.exp (U x)) ∂μ)=⊤
  · rw [ht];exact le_top
  have hi : Integrable (fun x => Real.exp (U x)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable
      (Real.continuous_exp.comp_aestronglyMeasurable hU.aestronglyMeasurable)
      (Eventually.of_forall fun x => (Real.exp_pos _).le)).mp ht
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal (convexOn_exp.map_integral_le
    Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall fun _ => mem_univ _) hU hi)

/-- Actual iid residual exponential expectation is at least one under each
bounded normalized positive tilt of Haar. The desired mean and moment bound
are conclusions, not inputs. -/
theorem periodic_residual_tilt_extended_lower (F : PeriodicTorus ι → ℝ)
    (hf : Measurable F) (hn : ∀ x,0≤F x) (B : ℝ) (hb : ∀ x,‖F x‖≤B)
    (hmean : (∫ x,F x ∂periodicHaar ι)=1) (β : ℝ) (hβ : 0≤β) (N : ℕ) (hN : 1≤N) :
    (1:ℝ≥0∞) ≤ ∫⁻ x : Fin N → PeriodicTorus ι,
      ENNReal.ofReal (Real.exp (β/(2*(N:ℝ))*∑ i,∑ j,
        if i=j then 0 else periodicFirstShellResidualPair (x i,x j)))
      ∂Measure.pi (fun _ => periodicBoundedDensityLaw F) := by
  let ν := periodicBoundedDensityLaw F
  have hB : 0≤B := (norm_nonneg (F 0)).trans (hb 0)
  have hiF : Integrable F (periodicHaar ι) := (integrable_const B).mono'
    hf.aestronglyMeasurable (Eventually.of_forall hb)
  haveI : IsProbabilityMeasure ν := periodicBoundedDensityLaw_probability F hiF hn hmean
  have hp := periodicBoundedDensityLaw_residual_pair F hf hn B hb
  have hm : 0≤∫ p,periodicFirstShellResidualPair p ∂ν.prod ν := by
    rw [hp.2]
    exact periodicFirstShellResidual_bounded_form_nonneg F hf.aestronglyMeasurable B hb
  have hs := iid_offdiagonal_sum_mean ν periodicFirstShellResidualPair hp.1 N
  have hj := periodic_extended_exp_jensen (Measure.pi (fun _ : Fin N => ν))
    (fun x => β/(2*(N:ℝ))*∑ i,∑ j,if i=j then 0 else periodicFirstShellResidualPair (x i,x j))
    (hs.1.const_mul _)
  rw [integral_const_mul,hs.2] at hj
  have hc : 0≤β/(2*(N:ℝ))*((N:ℝ)*((N:ℝ)-1)*(∫ p,periodicFirstShellResidualPair p ∂ν.prod ν)) := by
    have hNr : (1:ℝ)≤N := by exact_mod_cast hN
    exact mul_nonneg (div_nonneg hβ (by positivity))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (by linarith)) hm)
  have he : 1≤Real.exp (β/(2*(N:ℝ))*((N:ℝ)*((N:ℝ)-1)*(∫ p,periodicFirstShellResidualPair p ∂ν.prod ν))) :=
    Real.one_le_exp_iff.mpr hc
  exact (show (1:ℝ≥0∞)≤ENNReal.ofReal _ by exact_mod_cast ENNReal.ofReal_le_ofReal he).trans hj

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicBoundedDensityLaw_probability
#print axioms DGRHS.Periodic.periodicBoundedDensityLaw_residual_pair
#print axioms DGRHS.Periodic.periodic_extended_exp_jensen
#print axioms DGRHS.Periodic.periodic_residual_tilt_extended_lower
#check @DGRHS.Periodic.periodic_residual_tilt_extended_lower
