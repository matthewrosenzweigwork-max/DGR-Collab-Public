import DGRHS.Gaussian.PeriodicLogTruncatedFeature
import DGRHS.Gaussian.PeriodicLogMellinTail
import DGRHS.Gaussian.PeriodicUnshiftedMellinFourier
import DGRHS.Gaussian.PeriodicL1FourierUniqueness

/-!
Packet P9h, unit 3 (LOG, part 3): the lower-cut (long heat-time) piece of the periodic LOG kernel.

`periodicLogMellinFactor · ∫_{t>ε} t^{d/2-1}(p_t - 1) dt` has Fourier coefficients
`c_ε(k) = F_L ∫_{t>ε} t^{d/2-1} e^{-t‖k‖²} dt` (`k ≠ 0`, zero mode `0`), dominated by
`2^{d/2} ĝ(k) e^{-ε‖k‖²/2}`; it is almost everywhere the continuous positive Fourier kernel of these
coefficients (the `s = 0` analogue of `PeriodicRieszLowerCutFeature`, TeX 1248-1262).
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Real Fourier coefficients of the lower-cut LOG family. -/
def periodicLogLCCoeff (ε : ℝ) (k : PeriodicFrequency ι) : ℝ :=
  if k = 0 then 0 else
    periodicLogMellinFactor ι *
      ∫ t : ℝ in Ioi ε, t ^ periodicLogMellinExponent ι *
        Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * t))

lemma periodicLogLCCoeff_zero (ε : ℝ) : periodicLogLCCoeff ε (0 : PeriodicFrequency ι) = 0 := by
  simp [periodicLogLCCoeff]

lemma periodicLogLCCoeff_of_ne (ε : ℝ) {k : PeriodicFrequency ι} (hk : k ≠ 0) :
    periodicLogLCCoeff ε k = periodicLogMellinFactor ι *
      ∫ t : ℝ in Ioi ε, t ^ periodicLogMellinExponent ι *
        Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * t)) := by
  simp [periodicLogLCCoeff, hk]

lemma periodicLogLCCoeff_nonneg (ε : ℝ) (hε : 0 ≤ ε) (k : PeriodicFrequency ι) :
    0 ≤ periodicLogLCCoeff ε k := by
  by_cases hk : k = 0
  · subst k; rw [periodicLogLCCoeff_zero]
  · rw [periodicLogLCCoeff_of_ne ε hk]
    refine mul_nonneg periodicLogMellinFactor_pos.le (setIntegral_nonneg measurableSet_Ioi ?_)
    intro t ht
    exact mul_nonneg (Real.rpow_nonneg (hε.trans (le_of_lt ht)) _) (Real.exp_pos _).le

lemma periodicLogLCCoeff_neg (ε : ℝ) (k : PeriodicFrequency ι) :
    periodicLogLCCoeff ε (-k) = periodicLogLCCoeff ε k := by
  unfold periodicLogLCCoeff
  simp only [neg_eq_zero, periodicFrequencyVector_neg, norm_neg]

/-! ### Fourier coefficients of the physical tail -/

/-- The long-time tail (physical, with the Mellin factor). -/
def periodicLogPhysicalTail (ε : ℝ) (x : PeriodicTorus ι) : ℝ :=
  periodicLogMellinFactor ι * periodicLogMellinTail 0 ε x

lemma periodicLogTailFourierProduct_integrable (ε : ℝ) (hε : 0 < ε) (k : PeriodicFrequency ι) :
    Integrable
      (fun q : ℝ × PeriodicTorus ι =>
        UnitAddTorus.mFourier (-k) q.2 *
          periodicUnshiftedMellinHeatIntegrand (periodicLogMellinExponent ι) 0 q.1 q.2)
      ((volume.restrict (Ioi ε)).prod (periodicHaar ι)) := by
  let p : ℝ := periodicLogMellinExponent ι
  let f := fun q : ℝ × PeriodicTorus ι =>
    UnitAddTorus.mFourier (-k) q.2 * periodicUnshiftedMellinHeatIntegrand p 0 q.1 q.2
  have hf : Measurable f :=
    (((UnitAddTorus.mFourier (-k)).continuous.measurable.comp measurable_snd).mul
      (periodicUnshiftedMellinHeatIntegrand_measurable p 0))
  have htime : Integrable (periodicLogTailEnvelope ι) (volume.restrict (Ioi ε)) :=
    periodicLogTailEnvelope_integrableOn ε hε
  apply (integrable_prod_iff hf.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := hε.trans ht
    have hrow := periodicUnshiftedMellinHeatIntegrand_row (ι := ι) p 0 t le_rfl htpos
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
    have hrow := periodicUnshiftedMellinHeatIntegrand_row (ι := ι) p 0 t le_rfl htpos
    have hrow' : Integrable (fun x => f (t, x)) (periodicHaar ι) := by
      dsimp [f]
      exact hrow.bdd_mul (UnitAddTorus.mFourier (-k)).continuous.aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [periodic_mFourier_norm_apply])
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (f (t, x)))]
    calc
      (∫ x, ‖f (t, x)‖ ∂periodicHaar ι) ≤
          ∫ x, periodicLogTailEnvelope ι t ∂periodicHaar ι := by
        apply integral_mono_ae hrow'.norm (integrable_const _)
        filter_upwards [] with x
        have hreal : periodicUnshiftedMellinHeatIntegrand p 0 t x =
            ((t ^ p * ((periodicGaussianHeat (t + 0) x).re - 1) : ℝ) : ℂ) := by
          simp only [periodicUnshiftedMellinHeatIntegrand, Complex.ofReal_mul,
            Complex.ofReal_sub, Complex.ofReal_one]
          rw [← periodicGaussianHeat_eq_re (t + 0) (by linarith)]
        dsimp [f]
        rw [norm_mul, periodic_mFourier_norm_apply, one_mul, hreal, Complex.norm_real]
        exact periodicLogTail_integrand_le 0 t htpos le_rfl x
      _ = periodicLogTailEnvelope ι t := by simp

lemma periodicLogMellinTail_coe_integral (ε : ℝ) (hε : 0 < ε) (x : PeriodicTorus ι) :
    (periodicLogMellinTail (ι := ι) 0 ε x : ℂ) =
      ∫ t : ℝ in Ioi ε,
        periodicUnshiftedMellinHeatIntegrand (periodicLogMellinExponent ι) 0 t x := by
  let p : ℝ := periodicLogMellinExponent ι
  calc
    _ = ∫ t : ℝ in Ioi ε,
        ((t ^ p * ((periodicGaussianHeat (t + 0) x).re - 1) : ℝ) : ℂ) :=
      ((@RCLike.ofRealLI ℂ _).integral_comp_comm _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hheat : 0 < t + 0 := by have := hε.trans ht; linarith
      simp only [periodicUnshiftedMellinHeatIntegrand, Complex.ofReal_mul,
        Complex.ofReal_sub, Complex.ofReal_one]
      rw [← periodicGaussianHeat_eq_re (t + 0) hheat]

lemma periodicLogMellinTail_fourier_integral (ε : ℝ) (hε : 0 < ε) (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff
        (fun x => (periodicLogMellinTail (ι := ι) 0 ε x : ℂ)) k =
      ∫ t : ℝ in Ioi ε, ((t ^ periodicLogMellinExponent ι : ℝ) : ℂ) *
        ((Real.exp (-(t + 0) * ‖periodicFrequencyVector k‖ ^ 2) : ℂ) -
          if k = 0 then 1 else 0) := by
  rw [periodic_mFourierCoeff_eq_integral]
  simp_rw [periodicLogMellinTail_coe_integral ε hε, ← integral_const_mul]
  rw [← integral_integral_swap (periodicLogTailFourierProduct_integrable ε hε k)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [periodicUnshiftedMellinHeatIntegrand]
  conv_lhs => arg 2; ext x; rw [mul_left_comm]
  rw [integral_const_mul, periodicGaussianHeat_centered_fourier
    (t + 0) (by have := hε.trans ht; linarith)]

lemma periodicLogMellinTail_fourier_zero (ε : ℝ) (hε : 0 < ε) :
    UnitAddTorus.mFourierCoeff
      (fun x => (periodicLogMellinTail (ι := ι) 0 ε x : ℂ)) 0 = 0 := by
  rw [periodicLogMellinTail_fourier_integral ε hε]
  simp [periodicFrequencyVector_zero]

lemma periodicLogMellinTail_fourier_nonzero (ε : ℝ) (hε : 0 < ε) (k : PeriodicFrequency ι)
    (hk : k ≠ 0) :
    UnitAddTorus.mFourierCoeff
      (fun x => (periodicLogMellinTail (ι := ι) 0 ε x : ℂ)) k =
        ((∫ t : ℝ in Ioi ε,
          t ^ periodicLogMellinExponent ι *
            Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * t)) : ℝ) : ℂ) := by
  rw [periodicLogMellinTail_fourier_integral ε hε k]
  simp only [ite_eq_right hk, sub_zero, ← Complex.ofReal_mul]
  have he : (fun t : ℝ => t ^ periodicLogMellinExponent ι *
      Real.exp (-(t + 0) * ‖periodicFrequencyVector k‖ ^ 2)) =
      fun t : ℝ => t ^ periodicLogMellinExponent ι *
        Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * t)) := by
    funext t
    congr 2
    ring
  calc
    _ = ((∫ t : ℝ in Ioi ε,
        t ^ periodicLogMellinExponent ι *
          Real.exp (-(t + 0) * ‖periodicFrequencyVector k‖ ^ 2) : ℝ) : ℂ) :=
      (@RCLike.ofRealLI ℂ _).integral_comp_comm _
    _ = _ := by rw [he]

theorem periodicLogPhysicalTail_fourier_LC (ε : ℝ) (hε : 0 < ε) (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (fun x => (periodicLogPhysicalTail (ι := ι) ε x : ℂ)) k =
      (periodicLogLCCoeff ε k : ℂ) := by
  unfold periodicLogPhysicalTail
  rw [periodic_mFourierCoeff_real_const_mul]
  by_cases hk : k = 0
  · subst k
    rw [periodicLogMellinTail_fourier_zero ε hε]
    simp [periodicLogLCCoeff_zero]
  · rw [periodicLogMellinTail_fourier_nonzero ε hε k hk, periodicLogLCCoeff_of_ne ε hk]
    simp [Complex.ofReal_mul]

/-- Heat-shift domination: `c_ε(k) ≤ 2^{d/2} T_{ε/2}(k)`. -/
lemma periodicLogLCCoeff_le_trunc (ε : ℝ) (hε : 0 < ε) (k : PeriodicFrequency ι) :
    periodicLogLCCoeff ε k ≤ (2 : ℝ) ^ ((Fintype.card ι : ℝ) / 2) * periodicLogTruncCoeff (ε / 2) k := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  by_cases hk : k = 0
  · subst k
    rw [periodicLogLCCoeff_zero, periodicLogTruncCoeff_zero]; simp
  · rw [periodicLogLCCoeff_of_ne ε hk]
    set r : ℝ := ‖periodicFrequencyVector k‖ with hr
    have hrpos : 0 < r := periodicFrequency_norm_pos hk
    set p : ℝ := periodicLogMellinExponent ι with hp
    have hp1 : -1 < p := periodicLogMellinExponent_gt
    have hq : 0 < r ^ 2 / 2 := by positivity
    have hF := (periodicLogMellinFactor_pos (ι := ι)).le
    have hint : ∀ q : ℝ, 0 < q →
        IntegrableOn (fun t : ℝ => t ^ p * Real.exp (-(q * t))) (Ioi ε) := by
      intro q hq0
      have h0 := periodicUnshiftedMellin_integrable p 0 q hp1 hq0
      simp only [add_zero] at h0
      exact h0.mono_set (Ioi_subset_Ioi hε.le)
    have hint0 : IntegrableOn (fun t : ℝ => t ^ p * Real.exp (-((r ^ 2 / 2) * t))) (Ioi 0) := by
      have h0 := periodicUnshiftedMellin_integrable p 0 (r ^ 2 / 2) hp1 hq
      simpa only [add_zero] using h0
    have hpt : ∀ t ∈ Ioi ε, t ^ p * Real.exp (-(r ^ 2 * t)) ≤
        Real.exp (-(r ^ 2 * (ε / 2))) * (t ^ p * Real.exp (-((r ^ 2 / 2) * t))) := by
      intro t ht
      have ht' : ε < t := ht
      have htp : 0 ≤ t ^ p := Real.rpow_nonneg (hε.le.trans ht'.le) _
      have he : Real.exp (-(r ^ 2 * t)) ≤
          Real.exp (-(r ^ 2 * (ε / 2))) * Real.exp (-((r ^ 2 / 2) * t)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr ht'.le)]
      calc t ^ p * Real.exp (-(r ^ 2 * t)) ≤
          t ^ p * (Real.exp (-(r ^ 2 * (ε / 2))) * Real.exp (-((r ^ 2 / 2) * t))) :=
            mul_le_mul_of_nonneg_left he htp
        _ = _ := by ring
    have h1 : (∫ t : ℝ in Ioi ε, t ^ p * Real.exp (-(r ^ 2 * t))) ≤
        ∫ t : ℝ in Ioi ε, Real.exp (-(r ^ 2 * (ε / 2))) *
          (t ^ p * Real.exp (-((r ^ 2 / 2) * t))) :=
      setIntegral_mono_on (hint (r ^ 2) (by positivity))
        ((hint (r ^ 2 / 2) hq).const_mul _) measurableSet_Ioi hpt
    have h2 : (∫ t : ℝ in Ioi ε, t ^ p * Real.exp (-((r ^ 2 / 2) * t))) ≤
        ∫ t : ℝ in Ioi 0, t ^ p * Real.exp (-((r ^ 2 / 2) * t)) := by
      apply setIntegral_mono_set hint0
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le
      · exact Eventually.of_forall (Ioi_subset_Ioi hε.le)
    have h3 : (∫ t : ℝ in Ioi 0, t ^ p * Real.exp (-((r ^ 2 / 2) * t))) =
        (1 / (r ^ 2 / 2)) ^ (p + 1) * Real.Gamma (p + 1) := by
      have := periodicUnshiftedMellin_laplace p 0 (r ^ 2 / 2) hp1 hq
      simpa only [add_zero, mul_zero, neg_zero, Real.exp_zero, one_mul] using this
    have hint_le : (∫ t : ℝ in Ioi ε, t ^ p * Real.exp (-(r ^ 2 * t))) ≤
        Real.exp (-(r ^ 2 * (ε / 2))) *
          ((1 / (r ^ 2 / 2)) ^ (p + 1) * Real.Gamma (p + 1)) := by
      refine h1.trans ?_
      rw [integral_const_mul]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      refine h2.trans (le_of_eq h3)
    have hmul := mul_le_mul_of_nonneg_left hint_le hF
    have hgam := periodicLogMellinFactor_mul_gamma_eq k hk
    have hp1' : p + 1 = (Fintype.card ι : ℝ) / 2 := by
      rw [hp, periodicLogMellinExponent_add_one]
    have hpow : (1 / (r ^ 2 / 2)) ^ (p + 1) = (2 : ℝ) ^ (p + 1) * (1 / r ^ 2) ^ (p + 1) := by
      have e1 : 1 / (r ^ 2 / 2) = 2 * (1 / r ^ 2) := by field_simp
      rw [e1, Real.mul_rpow (by norm_num) (by positivity)]
    refine hmul.trans (le_of_eq ?_)
    rw [periodicLogTruncCoeff_eq_of_ne (ε / 2) hk]
    have hgam' : periodicLogMellinFactor ι * ((1 / r ^ 2) ^ (periodicLogMellinExponent ι + 1) *
        Real.Gamma (periodicLogMellinExponent ι + 1)) =
        periodicLogConstant ι / (2 * Real.pi * r) ^ (Fintype.card ι) := by
      simpa only [mul_zero, neg_zero, Real.exp_zero, one_mul] using hgam
    rw [← hp] at hgam'
    have hcoef : periodicLogConstant ι / (2 * Real.pi * r) ^ (Fintype.card ι) =
        periodicLogConstant ι / (2 * Real.pi) ^ (Fintype.card ι) * (r⁻¹) ^ (Fintype.card ι) := by
      have hr0 : r ≠ 0 := hrpos.ne'
      rw [mul_pow, inv_pow]
      field_simp
    calc periodicLogMellinFactor ι * (Real.exp (-(r ^ 2 * (ε / 2))) *
          ((1 / (r ^ 2 / 2)) ^ (p + 1) * Real.Gamma (p + 1)))
        = Real.exp (-(r ^ 2 * (ε / 2))) * (2 : ℝ) ^ (p + 1) *
            (periodicLogMellinFactor ι * ((1 / r ^ 2) ^ (p + 1) * Real.Gamma (p + 1))) := by
          rw [hpow]; ring
      _ = Real.exp (-(r ^ 2 * (ε / 2))) * (2 : ℝ) ^ (p + 1) *
            (periodicLogConstant ι / (2 * Real.pi) ^ (Fintype.card ι) * (r⁻¹) ^ (Fintype.card ι)) := by
          rw [hgam', hcoef]
      _ = _ := by rw [hp1']; ring

lemma periodicLogLCCoeff_summable (ε : ℝ) (hε : 0 < ε) :
    Summable (periodicLogLCCoeff (ι := ι) ε) :=
  ((periodicLogTruncCoeff_summable (ι := ι) (ε / 2) (by positivity)).mul_left
    ((2 : ℝ) ^ ((Fintype.card ι : ℝ) / 2))).of_nonneg_of_le
    (periodicLogLCCoeff_nonneg ε hε.le) (periodicLogLCCoeff_le_trunc ε hε)

/-- The continuous positive Fourier kernel of the lower-cut coefficients. -/
abbrev periodicLogLCKernel (ε : ℝ) : PeriodicTorus ι → ℝ :=
  periodicPositiveFourierKernel (periodicLogLCCoeff (ι := ι) ε)

/-- For `ε > 0` the physical tail is a.e. the continuous positive Fourier kernel. -/
theorem periodicLogPhysicalTail_ae_LCKernel (ε : ℝ) (hε : 0 < ε) :
    periodicLogPhysicalTail ε =ᵐ[periodicHaar ι] periodicLogLCKernel ε := by
  have ha := periodicLogLCCoeff_nonneg (ι := ι) ε hε.le
  have hsum := periodicLogLCCoeff_summable (ι := ι) ε hε
  have hev := periodicLogLCCoeff_neg (ι := ι) ε
  have hint : Integrable (fun x : PeriodicTorus ι => (periodicLogLCKernel ε x : ℂ))
      (periodicHaar ι) :=
    ((periodicPositiveFourierKernel_continuous _ ha hsum).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).ofReal
  have h := periodicL1_fourier_unique (fun x : PeriodicTorus ι => (periodicLogPhysicalTail ε x : ℂ))
    (fun x => (periodicLogLCKernel ε x : ℂ))
    ((periodicLogMellinTail_integrable 0 ε le_rfl hε.le).const_mul _).ofReal hint (fun k => by
      rw [periodicLogPhysicalTail_fourier_LC ε hε,
        periodicPositiveFourierKernel_fourierCoeff _ ha hsum hev])
  filter_upwards [h] with x hx
  exact Complex.ofReal_injective hx

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLogPhysicalTail_ae_LCKernel
#print axioms DGRHS.Periodic.periodicLogLCCoeff_le_trunc
