import DGRHS.Gaussian.PeriodicRieszTruncatedFeature
import DGRHS.Gaussian.PeriodicRieszFullTailCoefficientIdentity
import DGRHS.Gaussian.PeriodicPositiveMellinTail

/-!
Packet P9f, unit 1 (part 1): the time-lower-cut Mellin family on the torus.

`g_ε := periodicRieszPhysicalTail s 0 ε` is the heat-time integral
`F_s ∫_{t > ε} t^{(d-s)/2-1} (p_t - 1) dt` (the torus form of the Gaussian-profile Mellin lower cut
`eq:HCRStruncDef`, TeX 1248-1262, with `ε = η²`).  Its Fourier coefficients are the incomplete
Gamma integrals `F_s ∫_{t>ε} t^{(d-s)/2-1} e^{-t‖k‖²} dt` (`k ≠ 0`, zero mode `0`); they satisfy
`0 ≤ c_ε(k) ≤ 2^{(d-s)/2} ĝ(k) e^{-ε‖k‖²/2}`, so they inherit summability, square-root
summability and the diagonal bound `Σ_k c_ε(k) ≲ ε^{-s/2}` from the heat-shift coefficients of P9d.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Real Fourier coefficients of the lower-cut family: `F_s ∫_{t>ε} t^p e^{-‖k‖² t} dt` for `k ≠ 0`
and `0` for the zero mode. -/
def periodicRieszLCCoeff (s ε : ℝ) (k : PeriodicFrequency ι) : ℝ :=
  if k = 0 then 0 else
    periodicRieszMellinFactor ι s *
      ∫ t : ℝ in Ioi ε, t ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
        Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * t))

lemma periodicRieszLCCoeff_zero (s ε : ℝ) : periodicRieszLCCoeff s ε (0 : PeriodicFrequency ι) = 0 := by
  simp [periodicRieszLCCoeff]

lemma periodicRieszLCCoeff_of_ne (s ε : ℝ) {k : PeriodicFrequency ι} (hk : k ≠ 0) :
    periodicRieszLCCoeff s ε k = periodicRieszMellinFactor ι s *
      ∫ t : ℝ in Ioi ε, t ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
        Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * t)) := by
  simp [periodicRieszLCCoeff, hk]

lemma periodicRieszLCCoeff_nonneg (s ε : ℝ) (hs0 : 0 < s) (hε : 0 ≤ ε) (k : PeriodicFrequency ι) :
    0 ≤ periodicRieszLCCoeff s ε k := by
  by_cases hk : k = 0
  · subst k; rw [periodicRieszLCCoeff_zero]
  · rw [periodicRieszLCCoeff_of_ne s ε hk]
    refine mul_nonneg (periodicRieszMellinFactor_pos s hs0).le (setIntegral_nonneg measurableSet_Ioi ?_)
    intro t ht
    exact mul_nonneg (Real.rpow_nonneg (hε.trans (le_of_lt ht)) _) (Real.exp_pos _).le

lemma periodicRieszLCCoeff_neg (s ε : ℝ) (k : PeriodicFrequency ι) :
    periodicRieszLCCoeff s ε (-k) = periodicRieszLCCoeff s ε k := by
  unfold periodicRieszLCCoeff
  simp only [neg_eq_zero, periodicFrequencyVector_neg, norm_neg]

/-- The real Fourier coefficient is the (real part of the) actual complex Fourier coefficient of the
physical tail. -/
lemma periodicRieszPhysicalTail_fourier_LC (s ε : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hε : 0 < ε) (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (fun x => (periodicRieszPhysicalTail (ι := ι) s 0 ε x : ℂ)) k =
      (periodicRieszLCCoeff s ε k : ℂ) := by
  rw [periodicRieszPhysicalTail_fourier s 0 ε hs0 hs2 le_rfl hε k]
  by_cases hk : k = 0
  · subst k; simp [periodicRieszLCCoeff_zero]
  · simp only [dite_eq_right hk, periodicRieszLCCoeff_of_ne s ε hk, add_zero]

/-- Heat-shift domination: `c_ε(k) ≤ 2^{(d-s)/2} T_{ε/2}(k)`. -/
lemma periodicRieszLCCoeff_le_trunc (s ε : ℝ) (hs0 : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hε : 0 < ε) (k : PeriodicFrequency ι) :
    periodicRieszLCCoeff s ε k ≤
      (2 : ℝ) ^ (((Fintype.card ι : ℝ) - s) / 2) * periodicRieszTruncCoeff s (ε / 2) k := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  by_cases hk : k = 0
  · subst k
    rw [periodicRieszLCCoeff_zero, periodicRieszTruncCoeff_zero]; simp
  · rw [periodicRieszLCCoeff_of_ne s ε hk, periodicRieszTruncCoeff_eq_of_ne s (ε / 2) hk]
    set r : ℝ := ‖periodicFrequencyVector k‖ with hr
    have hrpos : 0 < r := periodicFrequency_norm_pos hk
    set p : ℝ := ((Fintype.card ι : ℝ) - s) / 2 - 1 with hp
    have hp1 : -1 < p := by rw [hp]; linarith
    have hq : 0 < r ^ 2 / 2 := by positivity
    have hF := (periodicRieszMellinFactor_pos (ι := ι) s hs0).le
    -- integrability of the two Gaussian-Mellin integrands on `Ioi ε`
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
    have hpow : (1 / (r ^ 2 / 2)) ^ (p + 1) = (2 : ℝ) ^ (p + 1) * r ^ (s - (Fintype.card ι : ℝ)) := by
      have e1 : 1 / (r ^ 2 / 2) = 2 * (1 / r ^ 2) := by field_simp
      rw [e1, Real.mul_rpow (by norm_num) (by positivity), periodic_inverse_square_rpow r _ hrpos.le]
      congr 2
      rw [hp]; ring
    have hAm : periodicRieszFourierAmplitude ι s =
        periodicRieszMellinFactor ι s * Real.Gamma (p + 1) := by
      unfold periodicRieszFourierAmplitude
      rw [hp]; ring_nf
    have hint_le : (∫ t : ℝ in Ioi ε, t ^ p * Real.exp (-(r ^ 2 * t))) ≤
        Real.exp (-(r ^ 2 * (ε / 2))) *
          ((2 : ℝ) ^ (p + 1) * r ^ (s - (Fintype.card ι : ℝ)) * Real.Gamma (p + 1)) := by
      refine h1.trans ?_
      rw [integral_const_mul]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      refine h2.trans ?_
      rw [h3, hpow]
    have hp1' : p + 1 = ((Fintype.card ι : ℝ) - s) / 2 := by rw [hp]; ring
    calc periodicRieszMellinFactor ι s * ∫ t : ℝ in Ioi ε, t ^ p * Real.exp (-(r ^ 2 * t))
        ≤ periodicRieszMellinFactor ι s * (Real.exp (-(r ^ 2 * (ε / 2))) *
          ((2 : ℝ) ^ (p + 1) * r ^ (s - (Fintype.card ι : ℝ)) * Real.Gamma (p + 1))) :=
          mul_le_mul_of_nonneg_left hint_le hF
      _ = (2 : ℝ) ^ (((Fintype.card ι : ℝ) - s) / 2) *
          (Real.exp (-(r ^ 2 * (ε / 2))) *
            (periodicRieszFourierAmplitude ι s * r ^ (s - (Fintype.card ι : ℝ)))) := by
          rw [hAm, hp1']; ring

lemma periodicRieszLCCoeff_summable (s ε : ℝ) (hs0 : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hε : 0 < ε) : Summable (periodicRieszLCCoeff (ι := ι) s ε) :=
  ((periodicRieszTruncCoeff_summable (ι := ι) s (ε / 2) hs0 hs2 (by positivity)).mul_left
    ((2 : ℝ) ^ (((Fintype.card ι : ℝ) - s) / 2))).of_nonneg_of_le
    (periodicRieszLCCoeff_nonneg s ε hs0 hε.le) (periodicRieszLCCoeff_le_trunc s ε hs0 hs2 hε)

lemma periodicRieszLCCoeff_sqrt_summable (s ε : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hε : 0 < ε) :
    Summable (fun k : PeriodicFrequency ι => Real.sqrt (periodicRieszLCCoeff s ε k)) := by
  refine ((periodicRieszTruncCoeff_sqrt_summable (ι := ι) s (ε / 2) hs0 hs2 (by positivity)).mul_left
    (Real.sqrt ((2 : ℝ) ^ (((Fintype.card ι : ℝ) - s) / 2)))).of_nonneg_of_le
    (fun k => Real.sqrt_nonneg _) (fun k => ?_)
  rw [← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt (periodicRieszLCCoeff_le_trunc s ε hs0 hs2 hε k)

/-- The continuous positive Fourier kernel of the lower-cut coefficients. -/
abbrev periodicRieszLCKernel (s ε : ℝ) : PeriodicTorus ι → ℝ :=
  periodicPositiveFourierKernel (periodicRieszLCCoeff (ι := ι) s ε)

/-- For `ε > 0` the physical tail (the lower-cut Mellin family) is a.e. the continuous positive
Fourier kernel. -/
theorem periodicRieszPhysicalTail_ae_LCKernel (s ε : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hε : 0 < ε) :
    periodicRieszPhysicalTail s 0 ε =ᵐ[periodicHaar ι] periodicRieszLCKernel s ε := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hsd : s < (Fintype.card ι : ℝ) := by linarith
  have ha := periodicRieszLCCoeff_nonneg (ι := ι) s ε hs0 hε.le
  have hsum := periodicRieszLCCoeff_summable (ι := ι) s ε hs0 hs2 hε
  have hev := periodicRieszLCCoeff_neg (ι := ι) s ε
  have hint : Integrable (fun x : PeriodicTorus ι => (periodicRieszLCKernel s ε x : ℂ))
      (periodicHaar ι) :=
    ((periodicPositiveFourierKernel_continuous _ ha hsum).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).ofReal
  have h := periodicL1_fourier_unique (fun x : PeriodicTorus ι => (periodicRieszPhysicalTail s 0 ε x : ℂ))
    (fun x => (periodicRieszLCKernel s ε x : ℂ))
    (periodicRieszPhysicalTail_integrable s 0 ε hsd le_rfl hε.le).ofReal hint (fun k => by
      rw [periodicRieszPhysicalTail_fourier_LC s ε hs0 hs2 hε,
        periodicPositiveFourierKernel_fourierCoeff _ ha hsum hev])
  filter_upwards [h] with x hx
  exact Complex.ofReal_injective hx

/-- `0 ≤ ĝ_ε(k) ≤ ĝ(k)`: the lower-cut coefficient is dominated by the source coefficient. -/
lemma periodicRieszLCCoeff_le_source (s ε : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hε : 0 < ε) (k : PeriodicFrequency ι) :
    periodicRieszLCCoeff s ε k ≤ ‖periodicRieszFourierCoeff s k‖ := by
  have h := periodicRieszPhysicalTail_fourier_norm_le (ι := ι) s 0 ε hs0 hs2 le_rfl hε k
  rw [periodicRieszPhysicalTail_fourier_LC s ε hs0 hs2 hε, Complex.norm_real,
    Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

/-- Diagonal of the lower-cut feature: `Σ_k c_ε(k) ≤ C ε^{-s/2}` for `0 < ε ≤ 1`. -/
theorem periodicRieszLCCoeff_tsum_le (s : ℝ) (hs0 : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∑' k : PeriodicFrequency ι, periodicRieszLCCoeff s ε k ≤ C * ε ^ (-s / 2) := by
  obtain ⟨C0, hC0, hC⟩ := periodicRieszTruncCoeff_tsum_le (ι := ι) s hs0 hs2
  refine ⟨(2 : ℝ) ^ (((Fintype.card ι : ℝ) - s) / 2) * (C0 * (2 : ℝ) ^ (s / 2)), by positivity, ?_⟩
  intro ε hε hε1
  have hεh : 0 < ε / 2 := by positivity
  have hsT := periodicRieszTruncCoeff_summable (ι := ι) s (ε / 2) hs0 hs2 hεh
  have h1 : ∑' k, periodicRieszLCCoeff (ι := ι) s ε k ≤
      ∑' k, (2 : ℝ) ^ (((Fintype.card ι : ℝ) - s) / 2) * periodicRieszTruncCoeff (ι := ι) s (ε / 2) k :=
    (periodicRieszLCCoeff_summable s ε hs0 hs2 hε).tsum_le_tsum
      (periodicRieszLCCoeff_le_trunc s ε hs0 hs2 hε) (hsT.mul_left _)
  rw [tsum_mul_left] at h1
  refine h1.trans ?_
  have h2 := hC (ε / 2) hεh (by linarith)
  have h3 : (ε / 2) ^ (-s / 2) = (2 : ℝ) ^ (s / 2) * ε ^ (-s / 2) := by
    rw [Real.div_rpow hε.le (by norm_num), show (-s / 2) = -(s / 2) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
    ring
  rw [h3] at h2
  calc (2 : ℝ) ^ (((Fintype.card ι : ℝ) - s) / 2) * ∑' k, periodicRieszTruncCoeff (ι := ι) s (ε / 2) k
      ≤ (2 : ℝ) ^ (((Fintype.card ι : ℝ) - s) / 2) * (C0 * ((2 : ℝ) ^ (s / 2) * ε ^ (-s / 2))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

end DGRHS.Periodic
