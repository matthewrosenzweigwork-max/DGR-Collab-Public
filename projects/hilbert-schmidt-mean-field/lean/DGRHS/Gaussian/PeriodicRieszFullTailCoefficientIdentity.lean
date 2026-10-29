import DGRHS.Gaussian.PeriodicPositiveMellinTail
import DGRHS.Gaussian.PeriodicRieszHeatL2
import DGRHS.Gaussian.PeriodicUnshiftedMellinFourier
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Exact Fourier coefficient and domination leaf for
`periodicRieszPhysicalTail`, the same infinite Ioi(ε) physical tail consumed
by `20261006T074448Z_PeriodicRieszUniformHighCoefficientCutoff.lean`.

This proof integrates the actual shifted heat integrand over the full interval
Ioi(ε), applies product integrability before Fubini, keeps the subtracted
zero mode, and compares the resulting scalar tail to the full Mellin integral.
It does not replace the tail by a finite time band.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The exact checked full-positive-time Fourier-product integrability API
restricts to the infinite tail `Ioi ε`; no separate heat-envelope product
integrability theorem is needed for this consumer. -/
lemma periodicRieszTailFourierProduct_integrable (s τ ε : ℝ)
    (hs : 0 < s) (hτ : 0 ≤ τ) (hε : 0 < ε) (k : PeriodicFrequency ι) :
    Integrable
      (fun q : ℝ × PeriodicTorus ι =>
        UnitAddTorus.mFourier (-k) q.2 *
          periodicUnshiftedMellinHeatIntegrand
            (((Fintype.card ι : ℝ) - s) / 2 - 1) τ q.1 q.2)
      ((volume.restrict (Ioi ε)).prod (periodicHaar ι)) := by
  let p : ℝ := ((Fintype.card ι : ℝ) - s) / 2 - 1
  let f := fun q : ℝ × PeriodicTorus ι =>
    UnitAddTorus.mFourier (-k) q.2 *
      periodicUnshiftedMellinHeatIntegrand p τ q.1 q.2
  have hf : Measurable f :=
    (((UnitAddTorus.mFourier (-k)).continuous.measurable.comp measurable_snd).mul
      (periodicUnshiftedMellinHeatIntegrand_measurable p τ))
  have htime : Integrable
      (fun t : ℝ => periodicHeatDiagonalGlobalConstant ι * t ^ (-s / 2 - 1))
      (volume.restrict (Ioi ε)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s / 2 - 1 < -1) hε).const_mul
      (periodicHeatDiagonalGlobalConstant ι)
  apply (integrable_prod_iff hf.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := hε.trans ht
    have hrow := periodicUnshiftedMellinHeatIntegrand_row (ι := ι) p τ t hτ htpos
    have hrow' : Integrable (fun x => f (t, x)) (periodicHaar ι) := by
      dsimp [f]
      exact hrow.bdd_mul (UnitAddTorus.mFourier (-k)).continuous.aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [periodic_mFourier_norm_apply])
    simpa only [f] using hrow'
  · apply htime.mono'
      hf.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := hε.trans ht
    have hrow := periodicUnshiftedMellinHeatIntegrand_row (ι := ι) p τ t hτ htpos
    have hrow' : Integrable (fun x => f (t, x)) (periodicHaar ι) := by
      dsimp [f]
      exact hrow.bdd_mul (UnitAddTorus.mFourier (-k)).continuous.aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [periodic_mFourier_norm_apply])
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (f (t, x)))]
    calc
      (∫ x, ‖f (t, x)‖ ∂periodicHaar ι) ≤
          ∫ x, periodicHeatDiagonalGlobalConstant ι * t ^ (-s / 2 - 1)
            ∂periodicHaar ι := by
        apply integral_mono_ae hrow'.norm (integrable_const _)
        filter_upwards [] with x
        have hreal : periodicUnshiftedMellinHeatIntegrand p τ t x =
            ((t ^ p * ((periodicGaussianHeat (t + τ) x).re - 1) : ℝ) : ℂ) := by
          simp only [periodicUnshiftedMellinHeatIntegrand, Complex.ofReal_mul,
            Complex.ofReal_sub, Complex.ofReal_one]
          rw [← periodicGaussianHeat_eq_re (t + τ)
            (add_pos_of_pos_of_nonneg htpos hτ)]
        dsimp [f]
        rw [norm_mul, periodic_mFourier_norm_apply, one_mul, hreal, Complex.norm_real]
        simpa only [p] using
          periodicRieszMellin_tail_weight_bound s τ t htpos hτ x
      _ = periodicHeatDiagonalGlobalConstant ι * t ^ (-s / 2 - 1) := by simp

/-- The real tail, viewed as a complex integral, is the actual Ioi(ε) heat
integral. The equality uses reality of the periodized heat at every positive
time, not a choice of an a.e. representative. -/
lemma periodicRieszMellinTail_coe_integral (s τ ε : ℝ)
    (hτ : 0 ≤ τ) (hε : 0 < ε) (x : PeriodicTorus ι) :
    (periodicRieszMellinTail (ι := ι) s τ ε x : ℂ) =
      ∫ t : ℝ in Ioi ε,
        periodicUnshiftedMellinHeatIntegrand
          (((Fintype.card ι : ℝ) - s) / 2 - 1) τ t x := by
  let p : ℝ := ((Fintype.card ι : ℝ) - s) / 2 - 1
  calc
    _ = ∫ t : ℝ in Ioi ε,
        ((t ^ p * ((periodicGaussianHeat (t + τ) x).re - 1) : ℝ) : ℂ) :=
      ((@RCLike.ofRealLI ℂ _).integral_comp_comm _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hheat : 0 < t + τ := add_pos_of_pos_of_nonneg (hε.trans ht) hτ
      simp only [periodicUnshiftedMellinHeatIntegrand, Complex.ofReal_mul,
        Complex.ofReal_sub, Complex.ofReal_one]
      rw [← periodicGaussianHeat_eq_re (t + τ) hheat]

/-- Exact Fourier coefficient for the actual infinite Mellin tail. Product
integrability is established before the two integrals are interchanged. -/
lemma periodicRieszMellinTail_fourier_integral (s τ ε : ℝ)
    (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hτ : 0 ≤ τ) (hε : 0 < ε) (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff
        (fun x => (periodicRieszMellinTail (ι := ι) s τ ε x : ℂ)) k =
      ∫ t : ℝ in Ioi ε, ((t ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) : ℝ) : ℂ) *
        ((Real.exp (-(t + τ) * ‖periodicFrequencyVector k‖ ^ 2) : ℂ) -
          if k = 0 then 1 else 0) := by
  let p : ℝ := ((Fintype.card ι : ℝ) - s) / 2 - 1
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := ι)
  have hsd : s < (Fintype.card ι : ℝ) := by linarith
  have hp : -1 < p := by dsimp [p]; linarith
  rw [periodic_mFourierCoeff_eq_integral]
  simp_rw [periodicRieszMellinTail_coe_integral s τ ε hτ hε,
    ← integral_const_mul]
  rw [← integral_integral_swap
    (periodicRieszTailFourierProduct_integrable s τ ε hs hτ hε k)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [periodicUnshiftedMellinHeatIntegrand]
  conv_lhs => arg 2; ext x; rw [mul_left_comm]
  rw [integral_const_mul, periodicGaussianHeat_centered_fourier
    (t + τ) (add_pos_of_pos_of_nonneg (hε.trans ht) hτ)]

/-- The subtracted heat mass removes the zero Fourier mode exactly. -/
lemma periodicRieszMellinTail_fourier_zero (s τ ε : ℝ)
    (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hτ : 0 ≤ τ) (hε : 0 < ε) :
    UnitAddTorus.mFourierCoeff
      (fun x => (periodicRieszMellinTail (ι := ι) s τ ε x : ℂ)) 0 = 0 := by
  rw [periodicRieszMellinTail_fourier_integral s τ ε hs hs2 hτ hε]
  simp [periodicFrequencyVector_zero]

/-- Nonzero modes are the genuine Ioi(ε) Mellin-Laplace tails. -/
lemma periodicRieszMellinTail_fourier_nonzero (s τ ε : ℝ)
    (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hτ : 0 ≤ τ) (hε : 0 < ε) (k : PeriodicFrequency ι) (hk : k ≠ 0) :
    UnitAddTorus.mFourierCoeff
      (fun x => (periodicRieszMellinTail (ι := ι) s τ ε x : ℂ)) k =
        ((∫ t : ℝ in Ioi ε,
          t ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
            Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * (t + τ))) : ℝ) : ℂ) := by
  rw [periodicRieszMellinTail_fourier_integral s τ ε hs hs2 hτ hε k]
  simp only [if_neg hk, sub_zero, ← Complex.ofReal_mul]
  have he : (fun t : ℝ => t ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
      Real.exp (-(t + τ) * ‖periodicFrequencyVector k‖ ^ 2)) =
      fun t : ℝ => t ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
        Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * (t + τ))) := by
    funext t
    congr 2
    ring
  calc
    _ = ((∫ t : ℝ in Ioi ε,
        t ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
          Real.exp (-(t + τ) * ‖periodicFrequencyVector k‖ ^ 2) : ℝ) : ℂ) :=
      (@RCLike.ofRealLI ℂ _).integral_comp_comm _
    _ = _ := by rw [he]

/-- The physical prefactor acts on the exact tail coefficient without changing
its normalization. -/
theorem periodicRieszPhysicalTail_fourier (s τ ε : ℝ)
    (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hτ : 0 ≤ τ) (hε : 0 < ε) (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff
        (fun x => (periodicRieszPhysicalTail (ι := ι) s τ ε x : ℂ)) k =
      if hk : k = 0 then 0 else
        ((periodicRieszMellinFactor ι s *
          ∫ t : ℝ in Ioi ε,
            t ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
              Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * (t + τ))) : ℝ) : ℂ) := by
  unfold periodicRieszPhysicalTail
  rw [periodic_mFourierCoeff_real_const_mul]
  by_cases hk : k = 0
  · subst k
    rw [periodicRieszMellinTail_fourier_zero s τ ε hs hs2 hτ hε]
    simp [periodicFrequencyVector_zero]
  · rw [periodicRieszMellinTail_fourier_nonzero s τ ε hs hs2 hτ hε k hk]
    simp [hk, Complex.ofReal_mul]

/-- The scalar coefficient of a positive full tail is dominated by the
full source coefficient. The full scalar integral is the same Laplace/Mellin
integral as the `ε=0` source coefficient; nonnegativity follows from its
integrand and the interval split at ε. -/
lemma periodicRieszPhysicalTail_fourier_norm_le (s τ ε : ℝ)
    (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hτ : 0 ≤ τ) (hε : 0 < ε) (k : PeriodicFrequency ι) :
    ‖UnitAddTorus.mFourierCoeff
        (fun x => (periodicRieszPhysicalTail (ι := ι) s τ ε x : ℂ)) k‖ ≤
      ‖periodicRieszFourierCoeff s k‖ := by
  by_cases hk : k = 0
  · subst k
    rw [periodicRieszPhysicalTail_fourier s τ ε hs hs2 hτ hε]
    simp
  · let p : ℝ := ((Fintype.card ι : ℝ) - s) / 2 - 1
    let lam : ℝ := ‖periodicFrequencyVector k‖ ^ 2
    have hp : -1 < p := by dsimp [p]; linarith
    have hlam : 0 < lam := sq_pos_of_pos (periodicFrequency_norm_pos hk)
    have hfull : IntegrableOn
        (fun t : ℝ => t ^ p * Real.exp (-(lam * (t + τ)))) (Ioi 0) :=
      periodicUnshiftedMellin_integrable p τ lam hp hlam
    have htail : IntegrableOn
        (fun t : ℝ => t ^ p * Real.exp (-(lam * (t + τ)))) (Ioi ε) :=
      hfull.mono_set (Ioi_subset_Ioi hε.le)
    have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hfull hε.le
    rw [intervalIntegral.integral_of_le hε.le] at hsplit
    have hshort : 0 ≤ ∫ t : ℝ in Ioc 0 ε,
        t ^ p * Real.exp (-(lam * (t + τ))) := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (Real.rpow_nonneg ht.1.le p) (Real.exp_pos _).le
    have htail_le :
        (∫ t : ℝ in Ioi ε, t ^ p * Real.exp (-(lam * (t + τ)))) ≤
          ∫ t : ℝ in Ioi 0, t ^ p * Real.exp (-(lam * (t + τ))) := by
      linarith
    have hfactor : 0 ≤ periodicRieszMellinFactor ι s :=
      (periodicRieszMellinFactor_pos (ι := ι) s hs).le
    have hexp : 0 ≤ Real.exp (-(lam * τ)) := (Real.exp_pos _).le
    have htailIntegral : 0 ≤
        ∫ t : ℝ in Ioi ε, t ^ p * Real.exp (-(lam * (t + τ))) :=
      integral_nonneg_of_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (Real.rpow_nonneg (hε.trans ht).le p) (Real.exp_pos _).le)
    have htailScalar : 0 ≤ periodicRieszMellinFactor ι s *
        ∫ t : ℝ in Ioi ε, t ^ p * Real.exp (-(lam * (t + τ))) :=
      mul_nonneg hfactor htailIntegral
    have hfullScalar : periodicRieszMellinFactor ι s *
        (∫ t : ℝ in Ioi 0, t ^ p * Real.exp (-(lam * (t + τ)))) =
        (periodicRieszHeatFourierCoeff s τ k).re := by
      have hsource := periodicRieszMellinGreen_fourier (ι := ι) s τ
        (by linarith : s < (Fintype.card ι : ℝ)) hτ k
      have hlap := periodicUnshiftedMellin_laplace p τ lam hp hlam
      have hgreen := periodicUnshiftedMellinHeatGreen_fourier_nonzero p τ hp hτ k hk
      unfold periodicRieszMellinGreen at hsource
      rw [periodic_mFourierCoeff_real_const_mul, hgreen] at hsource
      have hreal := congrArg Complex.re hsource
      have hsourceR : periodicRieszMellinFactor ι s *
          (Real.exp (-(lam * τ)) *
            ((1 / lam) ^ (p + 1) * Real.Gamma (p + 1))) =
          (periodicRieszHeatFourierCoeff s τ k).re := by
        simpa [lam, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
          ← Complex.ofReal_neg, ← Complex.ofReal_exp] using hreal
      calc
        periodicRieszMellinFactor ι s *
            (∫ t : ℝ in Ioi 0, t ^ p * Real.exp (-(lam * (t + τ)))) =
            periodicRieszMellinFactor ι s *
              (Real.exp (-(lam * τ)) *
                ((1 / lam) ^ (p + 1) * Real.Gamma (p + 1))) := by
          rw [hlap]
        _ = (periodicRieszHeatFourierCoeff s τ k).re := hsourceR
    have hboundScalar : periodicRieszMellinFactor ι s *
        ∫ t : ℝ in Ioi ε, t ^ p * Real.exp (-(lam * (t + τ))) ≤
        (periodicRieszHeatFourierCoeff s τ k).re := by
      rw [← hfullScalar]
      exact mul_le_mul_of_nonneg_left htail_le hfactor
    rw [periodicRieszPhysicalTail_fourier s τ ε hs hs2 hτ hε k]
    simp only [dif_neg hk]
    have htail_re_nonneg := htailScalar
    calc
      _ = periodicRieszMellinFactor ι s *
          ∫ t : ℝ in Ioi ε, t ^ p * Real.exp (-(lam * (t + τ))) := by
        have htailScalar' : 0 ≤ periodicRieszMellinFactor ι s *
            ∫ t : ℝ in Ioi ε,
              t ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
                Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * (t + τ))) := by
          simpa [p, lam] using htail_re_nonneg
        rw [Complex.norm_real, Real.norm_of_nonneg htailScalar']
      _ ≤ (periodicRieszHeatFourierCoeff s τ k).re := hboundScalar
      _ ≤ ‖periodicRieszFourierCoeff s k‖ := by
        have hnorm := norm_periodicRieszHeatFourierCoeff_le s τ hτ k
        exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans hnorm)

/-- The interface expected by the full-tail finite-set cutoff lemma. -/
def periodicRieszPhysicalTailCoeffNN (s τ ε : ℝ) (k : PeriodicFrequency ι) : NNReal :=
  ⟨‖UnitAddTorus.mFourierCoeff
      (fun x => (periodicRieszPhysicalTail (ι := ι) s τ ε x : ℂ)) k‖, norm_nonneg _⟩

lemma periodicRieszPhysicalTailCoeffNN_le (s τ ε : ℝ)
    (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hτ : 0 ≤ τ) (hε : 0 < ε) (k : PeriodicFrequency ι) :
    periodicRieszPhysicalTailCoeffNN s τ ε k ≤
      ⟨‖periodicRieszFourierCoeff s k‖, norm_nonneg _⟩ := by
  change ‖UnitAddTorus.mFourierCoeff
      (fun x => (periodicRieszPhysicalTail (ι := ι) s τ ε x : ℂ)) k‖ ≤
    ‖periodicRieszFourierCoeff s k‖
  exact periodicRieszPhysicalTail_fourier_norm_le s τ ε hs hs2 hτ hε k

end DGRHS.Periodic

#check DGRHS.Periodic.periodicRieszTailFourierProduct_integrable
#print axioms DGRHS.Periodic.periodicRieszTailFourierProduct_integrable
#check DGRHS.Periodic.periodicRieszMellinTail_coe_integral
#print axioms DGRHS.Periodic.periodicRieszMellinTail_coe_integral
#check DGRHS.Periodic.periodicRieszMellinTail_fourier_integral
#print axioms DGRHS.Periodic.periodicRieszMellinTail_fourier_integral
#check DGRHS.Periodic.periodicRieszMellinTail_fourier_zero
#print axioms DGRHS.Periodic.periodicRieszMellinTail_fourier_zero
#check DGRHS.Periodic.periodicRieszMellinTail_fourier_nonzero
#print axioms DGRHS.Periodic.periodicRieszMellinTail_fourier_nonzero
#check DGRHS.Periodic.periodicRieszPhysicalTail_fourier
#print axioms DGRHS.Periodic.periodicRieszPhysicalTail_fourier
#check DGRHS.Periodic.periodicRieszPhysicalTail_fourier_norm_le
#print axioms DGRHS.Periodic.periodicRieszPhysicalTail_fourier_norm_le
#check DGRHS.Periodic.periodicRieszPhysicalTailCoeffNN
#print axioms DGRHS.Periodic.periodicRieszPhysicalTailCoeffNN
#check DGRHS.Periodic.periodicRieszPhysicalTailCoeffNN_le
#print axioms DGRHS.Periodic.periodicRieszPhysicalTailCoeffNN_le
