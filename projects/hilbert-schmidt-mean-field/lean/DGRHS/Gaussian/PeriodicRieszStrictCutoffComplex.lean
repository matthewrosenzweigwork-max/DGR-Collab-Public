import DGRHS.Gaussian.PeriodicRieszL2Fourier
import DGRHS.Gaussian.PeriodicConvolutionMultiplier
import DGRHS.Gaussian.PeriodicL1FourierUniqueness
import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. This file constructs the actual
strict high-frequency projection of the source-normalized periodic Riesz L2
element, proves its Fourier coefficients, and identifies its convolution on
L2 inputs with the bounded Fourier multiplier operator by Haar-L1 uniqueness.

The source cutoff convention is strict: `K < ‖k‖`; equality belongs to the
removed low-frequency part. The multiplier rate is the source coefficient
amplitude times `K^(s-d)`. This module stops at the complex Haar operator;
the source real-kernel identification needed to compose it with the real
density compression is in `PeriodicRieszStrictCutoffRealification`.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal lp Convolution

namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

local instance periodicStrictCutoffCircleMeasureSpace :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

private def strictCutoffScalar (K : ℝ) (k : PeriodicFrequency ι) : ℂ :=
  if K < ‖periodicFrequencyVector k‖ then 1 else 0

/-- The bounded diagonal operator on the Fourier coefficient space. -/
private noncomputable def periodicFourierDiagonalMultiplier
    (m : PeriodicFrequency ι → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hm : ∀ k, ‖m k‖ ≤ L) :
    ℓ²(PeriodicFrequency ι, ℂ) →L[ℂ] ℓ²(PeriodicFrequency ι, ℂ) :=
  lp.mapCLM 2
    (fun k : PeriodicFrequency ι => m k • ContinuousLinearMap.id ℂ ℂ)
    hL (by
      intro k
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using hm k)

private lemma periodicFourierDiagonalMultiplier_apply
    (m : PeriodicFrequency ι → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hm : ∀ k, ‖m k‖ ≤ L) (f : ℓ²(PeriodicFrequency ι, ℂ))
    (k : PeriodicFrequency ι) :
    periodicFourierDiagonalMultiplier (ι := ι) m L hL hm f k =
      m k * f k := by
  rfl

private lemma periodicFourierDiagonalMultiplier_norm_le
    (m : PeriodicFrequency ι → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hm : ∀ k, ‖m k‖ ≤ L) :
    ‖periodicFourierDiagonalMultiplier (ι := ι) m L hL hm‖ ≤ L := by
  exact lp.norm_mapCLM_le 2
    (fun k : PeriodicFrequency ι => m k • ContinuousLinearMap.id ℂ ℂ)
    hL (by
      intro k
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using hm k)

private lemma strictCutoffScalar_norm_le (K : ℝ) :
    ∀ k : PeriodicFrequency ι,
      ‖strictCutoffScalar (ι := ι) K k‖ ≤ (1 : ℝ) := by
  intro k
  by_cases hk : K < ‖periodicFrequencyVector k‖ <;>
    simp [strictCutoffScalar, hk]

/-- The strict high-frequency projection in the actual native torus Fourier
basis. Its boundary convention is `‖k‖ = K` removed. -/
noncomputable def periodicStrictCutoffProjection (K : ℝ) :
    Lp ℂ 2 (periodicHaar ι) →L[ℂ] Lp ℂ 2 (periodicHaar ι) :=
  (periodicFourierBasis (ι := ι)).repr.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((periodicFourierDiagonalMultiplier (ι := ι)
        (strictCutoffScalar (ι := ι) K) 1 (by norm_num)
        (strictCutoffScalar_norm_le (ι := ι) K)).comp
      (periodicFourierBasis (ι := ι)).repr.toLinearIsometry.toContinuousLinearMap)

lemma periodicFourierBasis_repr_strictCutoffProjection (K : ℝ)
    (f : Lp ℂ 2 (periodicHaar ι)) (k : PeriodicFrequency ι) :
    (periodicFourierBasis (ι := ι)).repr
      (periodicStrictCutoffProjection (ι := ι) K f) k =
      strictCutoffScalar (ι := ι) K k *
        (periodicFourierBasis (ι := ι)).repr f k := by
  change (periodicFourierBasis (ι := ι)).repr
      ((periodicFourierBasis (ι := ι)).repr.symm
        (periodicFourierDiagonalMultiplier (ι := ι)
          (strictCutoffScalar (ι := ι) K) 1 (by norm_num)
          (strictCutoffScalar_norm_le (ι := ι) K)
          ((periodicFourierBasis (ι := ι)).repr f))) k = _
  rw [(periodicFourierBasis (ι := ι)).repr.apply_symm_apply]
  exact periodicFourierDiagonalMultiplier_apply (ι := ι)
    (strictCutoffScalar (ι := ι) K) 1 (by norm_num)
    (strictCutoffScalar_norm_le (ι := ι) K) _ k

/-- Actual source Riesz L2 element after deleting every mode of norm at most
`K`. This definition uses the source coefficient sequence itself and does not
presuppose a pointwise kernel representative. -/
noncomputable def periodicRieszStrictHighL2 (s K : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) :
    Lp ℂ 2 (periodicHaar ι) :=
  periodicStrictCutoffProjection (ι := ι) K (periodicRieszL2 s hs)

def periodicRieszStrictHighCoeff (s K : ℝ) (k : PeriodicFrequency ι) : ℂ :=
  if K < ‖periodicFrequencyVector k‖ then periodicRieszFourierCoeff s k else 0

lemma periodicRieszStrictHighL2_fourierCoeff (s K : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (periodicRieszStrictHighL2 s K hs) k =
      periodicRieszStrictHighCoeff s K k := by
  change UnitAddTorus.mFourierCoeff
    (periodicStrictCutoffProjection (ι := ι) K (periodicRieszL2 s hs)) k = _
  rw [← periodicFourierBasis_repr, periodicFourierBasis_repr_strictCutoffProjection,
    periodicFourierBasis_repr, periodicRieszL2_fourierCoeff]
  by_cases hk : K < ‖periodicFrequencyVector k‖ <;>
    simp [periodicRieszStrictHighCoeff, strictCutoffScalar, hk]

lemma periodicRieszStrictHighL2_integrable (s K : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) :
    Integrable (periodicRieszStrictHighL2 s K hs : PeriodicTorus ι → ℂ)
      (periodicHaar ι) :=
  MemLp.integrable (by norm_num) (Lp.memLp _)

/-- The source coefficient estimate at a strict high mode. Positivity of the
normalizing amplitude and the negative exponent are both used; `K ≥ 1` also
keeps the zero mode out of the high region. -/
lemma periodicRieszStrictHighCoeff_norm_le (s K : ℝ)
    (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hK : 1 ≤ K)
    (k : PeriodicFrequency ι) :
    ‖periodicRieszStrictHighCoeff s K k‖ ≤
      periodicRieszFourierAmplitude ι s * K^(s - (Fintype.card ι : ℝ)) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := ι)
  have hsd : s < (Fintype.card ι : ℝ) := by linarith
  have hA : 0 < periodicRieszFourierAmplitude ι s :=
    periodicRieszFourierAmplitude_pos s hs hsd
  have hKpos : 0 < K := by linarith
  by_cases hk : K < ‖periodicFrequencyVector k‖
  · have hk0 : k ≠ 0 := by
      intro hzero
      subst k
      simp only [periodicFrequencyVector_zero, norm_zero] at hk
      linarith
    have hmode : K ≤ ‖periodicFrequencyVector k‖ := le_of_lt hk
    rw [periodicRieszStrictHighCoeff, if_pos hk]
    calc
      ‖periodicRieszFourierCoeff s k‖ =
          periodicRieszFourierAmplitude ι s *
            ‖periodicFrequencyVector k‖^(s-(Fintype.card ι : ℝ)) := by
        rw [periodicRieszFourierCoeff, if_neg hk0, Complex.norm_real,
          Real.norm_eq_abs, abs_mul, abs_of_pos hA,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      _ ≤ periodicRieszFourierAmplitude ι s * K^(s-(Fintype.card ι : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hKpos hmode (by linarith)) hA.le
  · simp [periodicRieszStrictHighCoeff, hk]
    positivity

/-- The bounded diagonal Fourier multiplier on the actual Haar `L²` space.
This is the concrete Parseval operator; no final operator norm is an input. -/
noncomputable def periodicFourierMultiplier (m : PeriodicFrequency ι → ℂ)
    (L : ℝ) (hL : 0 ≤ L) (hm : ∀ k, ‖m k‖ ≤ L) :
    Lp ℂ 2 (periodicHaar ι) →L[ℂ] Lp ℂ 2 (periodicHaar ι) :=
  (periodicFourierBasis (ι := ι)).repr.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((periodicFourierDiagonalMultiplier (ι := ι) m L hL hm).comp
      (periodicFourierBasis (ι := ι)).repr.toLinearIsometry.toContinuousLinearMap)

lemma periodicFourierBasis_repr_periodicFourierMultiplier
    (m : PeriodicFrequency ι → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hm : ∀ k, ‖m k‖ ≤ L) (f : Lp ℂ 2 (periodicHaar ι))
    (k : PeriodicFrequency ι) :
    (periodicFourierBasis (ι := ι)).repr
      (periodicFourierMultiplier (ι := ι) m L hL hm f) k =
      m k * (periodicFourierBasis (ι := ι)).repr f k := by
  change (periodicFourierBasis (ι := ι)).repr
      ((periodicFourierBasis (ι := ι)).repr.symm
        (periodicFourierDiagonalMultiplier (ι := ι) m L hL hm
          ((periodicFourierBasis (ι := ι)).repr f))) k = _
  rw [(periodicFourierBasis (ι := ι)).repr.apply_symm_apply]
  exact periodicFourierDiagonalMultiplier_apply (ι := ι) m L hL hm _ k

lemma periodicFourierMultiplier_norm_le (m : PeriodicFrequency ι → ℂ)
    (L : ℝ) (hL : 0 ≤ L) (hm : ∀ k, ‖m k‖ ≤ L) :
    ‖periodicFourierMultiplier (ι := ι) m L hL hm‖ ≤ L := by
  apply ContinuousLinearMap.opNorm_le_bound _ hL
  intro f
  change ‖(periodicFourierBasis (ι := ι)).repr.symm
      (periodicFourierDiagonalMultiplier (ι := ι) m L hL hm
        ((periodicFourierBasis (ι := ι)).repr f))‖ ≤ L * ‖f‖
  rw [(periodicFourierBasis (ι := ι)).repr.symm.norm_map]
  calc
    ‖periodicFourierDiagonalMultiplier (ι := ι) m L hL hm
        ((periodicFourierBasis (ι := ι)).repr f)‖ ≤
      L * ‖(periodicFourierBasis (ι := ι)).repr f‖ :=
        (periodicFourierDiagonalMultiplier (ι := ι) m L hL hm).le_opNorm _ |>.trans
          (mul_le_mul_of_nonneg_right
            (periodicFourierDiagonalMultiplier_norm_le (ι := ι) m L hL hm)
            (norm_nonneg _))
    _ = L * ‖f‖ := by rw [(periodicFourierBasis (ι := ι)).repr.norm_map]

/-- Full strict-cutoff convolution eigenidentity in Fourier coordinates. The
convolution is shown a.e. equal to the bounded Parseval multiplier, so in
particular it has an actual Haar L² representative. -/
lemma periodicRieszStrictHigh_convolution_ae_eq_multiplier
    (s K : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ))
    (L : ℝ) (hL : 0 ≤ L)
    (hcoeff : ∀ k, ‖periodicRieszStrictHighCoeff s K k‖ ≤ L)
    (f : Lp ℂ 2 (periodicHaar ι)) :
    (f ⋆[ContinuousLinearMap.mul ℂ ℂ, periodicHaar ι]
        (periodicRieszStrictHighL2 s K hs : PeriodicTorus ι → ℂ)) =ᵐ[periodicHaar ι]
      (periodicFourierMultiplier (ι := ι)
        (periodicRieszStrictHighCoeff s K) L hL hcoeff f :
          PeriodicTorus ι → ℂ) := by
  apply periodicL1_fourier_unique
  · have hF : Integrable (f : PeriodicTorus ι → ℂ) (periodicHaar ι) :=
      MemLp.integrable (by norm_num) (Lp.memLp f)
    exact (hF.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ)
      (periodicRieszStrictHighL2_integrable s K hs)).integral_prod_left
  · exact MemLp.integrable (by norm_num)
      (Lp.memLp (periodicFourierMultiplier (ι := ι)
        (periodicRieszStrictHighCoeff s K) L hL hcoeff f))
  · intro k
    rw [periodic_mFourierCoeff_convolution
      (MemLp.integrable (by norm_num) (Lp.memLp f))
      (periodicRieszStrictHighL2_integrable s K hs),
      periodicRieszStrictHighL2_fourierCoeff]
    calc
      (UnitAddTorus.mFourierCoeff f k) *
          periodicRieszStrictHighCoeff s K k =
        (periodicFourierBasis (ι := ι)).repr f k *
          periodicRieszStrictHighCoeff s K k := by
            rw [← periodicFourierBasis_repr]
      _ = (periodicFourierBasis (ι := ι)).repr
          (periodicFourierMultiplier (ι := ι)
            (periodicRieszStrictHighCoeff s K) L hL hcoeff f) k := by
          rw [periodicFourierBasis_repr_periodicFourierMultiplier]
          ring
      _ = UnitAddTorus.mFourierCoeff
          (periodicFourierMultiplier (ι := ι)
            (periodicRieszStrictHighCoeff s K) L hL hcoeff f) k := by
          rw [periodicFourierBasis_repr]

/-- Source coefficient decay gives the exact Haar multiplier rate for the
strict cutoff. Here `d = card ι`; this uses the source normalization in
`periodicRieszFourierAmplitude`. -/
lemma periodicRieszStrictHigh_multiplier_norm_le (s K : ℝ)
    (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hK : 1 ≤ K) :
    ‖periodicFourierMultiplier (ι := ι)
      (periodicRieszStrictHighCoeff s K)
      (periodicRieszFourierAmplitude ι s * K^(s-(Fintype.card ι : ℝ)))
      (by
        have hd : 0 < (Fintype.card ι : ℝ) := by
          exact_mod_cast Fintype.card_pos (α := ι)
        have hsd : s < (Fintype.card ι : ℝ) := by linarith
        have hA : 0 < periodicRieszFourierAmplitude ι s :=
          periodicRieszFourierAmplitude_pos s hs hsd
        have hKpos : 0 < K := by linarith
        exact mul_nonneg hA.le (Real.rpow_nonneg hKpos.le _))
      (periodicRieszStrictHighCoeff_norm_le s K hs hs2 hK)‖ ≤
        periodicRieszFourierAmplitude ι s * K^(s-(Fintype.card ι : ℝ)) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := ι)
  have hsd : s < (Fintype.card ι : ℝ) := by linarith
  have hA : 0 < periodicRieszFourierAmplitude ι s :=
    periodicRieszFourierAmplitude_pos s hs hsd
  have hKpos : 0 < K := by linarith
  have hL : 0 ≤ periodicRieszFourierAmplitude ι s * K^(s-(Fintype.card ι : ℝ)) :=
    mul_nonneg hA.le (Real.rpow_nonneg hKpos.le _)
  exact periodicFourierMultiplier_norm_le _ _ hL
    (periodicRieszStrictHighCoeff_norm_le s K hs hs2 hK)

end DGRHS.Periodic

/- Direct interface and allowed-axiom audit for every public declaration in this bounded complex cutoff unit. -/
#check DGRHS.Periodic.periodicStrictCutoffProjection
#print axioms DGRHS.Periodic.periodicStrictCutoffProjection
#check DGRHS.Periodic.periodicFourierBasis_repr_strictCutoffProjection
#print axioms DGRHS.Periodic.periodicFourierBasis_repr_strictCutoffProjection
#check DGRHS.Periodic.periodicRieszStrictHighL2
#print axioms DGRHS.Periodic.periodicRieszStrictHighL2
#check DGRHS.Periodic.periodicRieszStrictHighCoeff
#print axioms DGRHS.Periodic.periodicRieszStrictHighCoeff
#check DGRHS.Periodic.periodicRieszStrictHighL2_fourierCoeff
#print axioms DGRHS.Periodic.periodicRieszStrictHighL2_fourierCoeff
#check DGRHS.Periodic.periodicRieszStrictHighL2_integrable
#print axioms DGRHS.Periodic.periodicRieszStrictHighL2_integrable
#check DGRHS.Periodic.periodicRieszStrictHighCoeff_norm_le
#print axioms DGRHS.Periodic.periodicRieszStrictHighCoeff_norm_le
#check DGRHS.Periodic.periodicFourierMultiplier
#print axioms DGRHS.Periodic.periodicFourierMultiplier
#check DGRHS.Periodic.periodicFourierBasis_repr_periodicFourierMultiplier
#print axioms DGRHS.Periodic.periodicFourierBasis_repr_periodicFourierMultiplier
#check DGRHS.Periodic.periodicFourierMultiplier_norm_le
#print axioms DGRHS.Periodic.periodicFourierMultiplier_norm_le
#check DGRHS.Periodic.periodicRieszStrictHigh_convolution_ae_eq_multiplier
#print axioms DGRHS.Periodic.periodicRieszStrictHigh_convolution_ae_eq_multiplier
#check DGRHS.Periodic.periodicRieszStrictHigh_multiplier_norm_le
#print axioms DGRHS.Periodic.periodicRieszStrictHigh_multiplier_norm_le
