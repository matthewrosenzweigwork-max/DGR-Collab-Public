import DGRHS.Gaussian.PeriodicRieszStrictCutoffRealification
import DGRHS.Gaussian.PeriodicLatticeShellSums

/-!
Packet P9a, unit 3 (Parseval half): the L²(Haar) norm of the real strict
high-frequency periodic Riesz kernel is exactly the weighted lattice tail sum,
hence `≤ A_s² C K^{2s-d}` (eq. CtailFourier / BtailFourier at `μ = Haar`,
TeX 1377-1405).
-/

noncomputable section
open MeasureTheory
open scoped ENNReal lp

namespace DGRHS.Periodic.RealifiedStrictCutoff

universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Parseval for the native torus Fourier basis. -/
lemma norm_sq_eq_tsum_fourierCoeff (f : Lp ℂ 2 (periodicHaar ι)) :
    ‖f‖ ^ 2 = ∑' k : PeriodicFrequency ι, ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 := by
  have h1 : ‖(periodicFourierBasis (ι := ι)).repr f‖ = ‖f‖ :=
    (periodicFourierBasis (ι := ι)).repr.norm_map f
  have h2 := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    ((periodicFourierBasis (ι := ι)).repr f)
  rw [h1] at h2
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h2
  rw [h2]
  apply tsum_congr
  intro k
  rw [periodicFourierBasis_repr]

/-- The real kernel is the real structure of the complex strict-high element, so
their L² norms agree. -/
lemma norm_strictHighKernel_toLp (s K : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    ‖(strictHighKernel_memLp s K hs2).toLp (strictHighKernel s K hs2)‖ =
      ‖strictHighL2 s K hs2‖ := by
  set g : Lp ℝ 2 (periodicHaar ι) :=
    (strictHighKernel_memLp s K hs2).toLp (strictHighKernel s K hs2) with hg
  have hc : realToComplexL2 g = strictHighL2 s K hs2 := by
    apply Lp.ext
    filter_upwards [realToComplexL2_coe_ae g, (strictHighKernel_memLp s K hs2).coeFn_toLp,
      strictHighKernel_coe_ae s K hs2] with x h1 h2 h3
    rw [h1]
    have : (g x) = strictHighKernel s K hs2 x := h2
    rw [this]
    exact h3
  rw [← hc, realToComplexL2_norm]

/-- Exact Parseval identity for the strict high kernel. -/
theorem integral_sq_strictHighKernel_eq (s K : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    ∫ x, strictHighKernel s K hs2 x ^ 2 ∂periodicHaar ι =
      (periodicRieszFourierAmplitude ι s) ^ 2 *
        ∑' k : PeriodicFrequency ι,
          (if K < ‖periodicFrequencyVector k‖ then
            ‖periodicFrequencyVector k‖ ^ (2 * (s - (Fintype.card ι : ℝ))) else 0) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := ι)
  have hsd : s < (Fintype.card ι : ℝ) := by linarith
  have hg := (strictHighKernel_memLp s K hs2)
  calc ∫ x, strictHighKernel s K hs2 x ^ 2 ∂periodicHaar ι
      = ‖hg.toLp (strictHighKernel s K hs2)‖ ^ 2 :=
        (DGRHS.Kernel.norm_toLp_sq hg).symm
    _ = ‖strictHighL2 s K hs2‖ ^ 2 := by rw [norm_strictHighKernel_toLp]
    _ = ∑' k : PeriodicFrequency ι,
          ‖UnitAddTorus.mFourierCoeff (strictHighL2 s K hs2) k‖ ^ 2 :=
        norm_sq_eq_tsum_fourierCoeff _
    _ = ∑' k : PeriodicFrequency ι, (periodicRieszFourierAmplitude ι s) ^ 2 *
          (if K < ‖periodicFrequencyVector k‖ then
            ‖periodicFrequencyVector k‖ ^ (2 * (s - (Fintype.card ι : ℝ))) else 0) := by
        apply tsum_congr
        intro k
        rw [strictHighL2_fourierCoeff]
        by_cases hk : K < ‖periodicFrequencyVector k‖
        · simp only [strictHighCoeff, periodicRieszStrictHighCoeff, ite_eq_left hk]
          rw [norm_periodicRieszFourierCoeff_sq s hsd k]
        · simp [strictHighCoeff, periodicRieszStrictHighCoeff, hk]
    _ = _ := tsum_mul_left

/-- `∫ g_{>K}² ≤ A² C K^{2s-d}` for `K ≥ 1`, uniformly in `K`. -/
theorem integral_sq_strictHighKernel_le (s : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℝ, 1 ≤ K →
      ∫ x, strictHighKernel s K hs2 x ^ 2 ∂periodicHaar ι ≤
        C * K ^ (2 * s - (Fintype.card ι : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := periodicFrequency_tail_sum_le (ι := ι) s hs2
  refine ⟨(periodicRieszFourierAmplitude ι s) ^ 2 * C, by positivity, ?_⟩
  intro K hK
  rw [integral_sq_strictHighKernel_eq, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC K hK) (sq_nonneg _)

end DGRHS.Periodic.RealifiedStrictCutoff

#print axioms DGRHS.Periodic.RealifiedStrictCutoff.norm_sq_eq_tsum_fourierCoeff
#print axioms DGRHS.Periodic.RealifiedStrictCutoff.norm_strictHighKernel_toLp
#print axioms DGRHS.Periodic.RealifiedStrictCutoff.integral_sq_strictHighKernel_eq
#print axioms DGRHS.Periodic.RealifiedStrictCutoff.integral_sq_strictHighKernel_le
