import DGRHS.Gaussian.PeriodicRieszStrictCutoffComplex
import DGRHS.Kernel.Operator
import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed.
Import-front successor for the realification proposal
`PeriodicRieszStrictCutoffRealification_20261006T093400Z.lean` (aa89).

It imports the staged complex strict-cutoff provider once and aliases its
source L² element, coefficient sequence, Fourier multiplier, and convolution
identity. The remaining body proves coefficient reality, constructs the real
Haar L² kernel, and transfers the exact multiplier bound to the real Haar
integral operator for every L² input.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal lp Convolution InnerProductSpace ComplexConjugate

namespace DGRHS.Periodic.RealifiedStrictCutoff
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

local instance periodicStrictRealifiedCircleMeasureSpace :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- Reuse the checked-integration target's strict-cutoff objects by exact aliases.
The predecessor module `PeriodicRieszStrictCutoffComplex` is imported directly. -/
abbrev strictHighL2 (s K : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) : Lp ℂ 2 (periodicHaar ι) :=
  DGRHS.Periodic.periodicRieszStrictHighL2 (ι := ι) s K hs

abbrev strictHighCoeff (s K : ℝ) (k : PeriodicFrequency ι) : ℂ :=
  DGRHS.Periodic.periodicRieszStrictHighCoeff (ι := ι) s K k

lemma strictHighL2_fourierCoeff (s K : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (strictHighL2 s K hs) k = strictHighCoeff s K k :=
  DGRHS.Periodic.periodicRieszStrictHighL2_fourierCoeff s K hs k

lemma strictHighCoeff_neg (s K : ℝ) (k : PeriodicFrequency ι) :
    strictHighCoeff s K (-k) = strictHighCoeff s K k := by
  unfold strictHighCoeff periodicRieszStrictHighCoeff
  simp [periodicFrequencyVector_neg, periodicRieszFourierCoeff_neg]

lemma conj_strictHighCoeff (s K : ℝ) (k : PeriodicFrequency ι) :
    conj (strictHighCoeff s K k) = strictHighCoeff s K k := by
  unfold strictHighCoeff periodicRieszStrictHighCoeff
  split_ifs
  · exact conj_periodicRieszFourierCoeff s k
  · simp

/-- The cutoff preserves source reality: the exact opposite-frequency
symmetry and real-valued source coefficients imply conjugation invariance in
the actual quotient L² space. -/
lemma strictHighL2_star (s K : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    star (strictHighL2 s K hs) = strictHighL2 s K hs := by
  apply (periodicFourierBasis (ι := ι)).repr.injective
  apply lp.ext
  funext k
  simp only [periodicFourierBasis_repr]
  rw [periodic_mFourierCoeff_star,
    strictHighL2_fourierCoeff, strictHighL2_fourierCoeff,
    strictHighCoeff_neg, conj_strictHighCoeff]

lemma strictHighL2_conj_ae (s K : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) :
    (fun x => conj (strictHighL2 s K hs x)) =ᵐ[periodicHaar ι]
      strictHighL2 s K hs := by
  have h := Lp.coeFn_star (strictHighL2 s K hs)
  rw [strictHighL2_star] at h
  exact h.symm

def strictHighKernel (s K : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ))
    (x : PeriodicTorus ι) : ℝ := (strictHighL2 s K hs x).re

lemma strictHighKernel_memLp (s K : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) :
    MemLp (strictHighKernel s K hs) 2 (periodicHaar ι) :=
  (Lp.memLp (strictHighL2 s K hs)).re

lemma strictHighKernel_coe_ae (s K : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) :
    (fun x => (strictHighKernel s K hs x : ℂ)) =ᵐ[periodicHaar ι]
      strictHighL2 s K hs := by
  filter_upwards [strictHighL2_conj_ae s K hs] with x hx
  exact RCLike.conj_eq_iff_re.mp hx

lemma strictHighKernel_pair_memLp (s K : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) :
    MemLp (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      strictHighKernel s K hs (p.1-p.2)) 2
      ((periodicHaar ι).prod (periodicHaar ι)) :=
  (strictHighKernel_memLp s K hs).comp_measurePreserving
    periodicHaar_preserving_difference

abbrev fourierMultiplier (m : PeriodicFrequency ι → ℂ)
    (L : ℝ) (hL : 0 ≤ L) (hm : ∀ k, ‖m k‖ ≤ L) :
    Lp ℂ 2 (periodicHaar ι) →L[ℂ] Lp ℂ 2 (periodicHaar ι) :=
  DGRHS.Periodic.periodicFourierMultiplier (ι := ι) m L hL hm

lemma repr_fourierMultiplier (m : PeriodicFrequency ι → ℂ)
    (L : ℝ) (hL : 0 ≤ L) (hm : ∀ k, ‖m k‖ ≤ L)
    (f : Lp ℂ 2 (periodicHaar ι)) (k : PeriodicFrequency ι) :
    (periodicFourierBasis (ι := ι)).repr (fourierMultiplier (ι := ι) m L hL hm f) k =
      m k * (periodicFourierBasis (ι := ι)).repr f k :=
  DGRHS.Periodic.periodicFourierBasis_repr_periodicFourierMultiplier
    (ι := ι) m L hL hm f k

lemma fourierMultiplier_norm_le (m : PeriodicFrequency ι → ℂ)
    (L : ℝ) (hL : 0 ≤ L) (hm : ∀ k, ‖m k‖ ≤ L) :
    ‖fourierMultiplier (ι := ι) m L hL hm‖ ≤ L :=
  DGRHS.Periodic.periodicFourierMultiplier_norm_le (ι := ι) m L hL hm

lemma strictHighConvolution_ae_eq_multiplier
    (s K : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ))
    (L : ℝ) (hL : 0 ≤ L)
    (hcoeff : ∀ k, ‖strictHighCoeff s K k‖ ≤ L)
    (f : Lp ℂ 2 (periodicHaar ι)) :
    (f ⋆[ContinuousLinearMap.mul ℂ ℂ,periodicHaar ι]
        (strictHighL2 s K hs : PeriodicTorus ι → ℂ)) =ᵐ[periodicHaar ι]
      (fourierMultiplier (ι := ι) (strictHighCoeff s K) L hL hcoeff f :
        PeriodicTorus ι → ℂ) :=
  DGRHS.Periodic.periodicRieszStrictHigh_convolution_ae_eq_multiplier
    (ι := ι) s K hs L hL hcoeff f

/-- Norm-preserving realification map on every L² element. Its proof uses
`MemLp.ofReal` and the pointwise identity `‖(x:ℂ)‖=‖x‖`, so it applies to all
quotient classes, not only bounded functions. -/
noncomputable def realToComplexL2 (f : Lp ℝ 2 (periodicHaar ι)) :
    Lp ℂ 2 (periodicHaar ι) :=
  (Lp.memLp f).ofReal.toLp (fun x => (f x : ℂ))

lemma realToComplexL2_coe_ae (f : Lp ℝ 2 (periodicHaar ι)) :
    (realToComplexL2 f : PeriodicTorus ι → ℂ) =ᵐ[periodicHaar ι]
      (fun x => (f x : ℂ)) :=
  (Lp.memLp f).ofReal.coeFn_toLp

lemma realToComplexL2_norm (f : Lp ℝ 2 (periodicHaar ι)) :
    ‖realToComplexL2 f‖ = ‖f‖ := by
  have he : eLpNorm (fun x => (f x : ℂ)) 2 (periodicHaar ι) =
      eLpNorm (fun x => f x) 2 (periodicHaar ι) :=
    eLpNorm_congr_norm_ae (Lp.memLp f).ofReal.aestronglyMeasurable
      (Lp.memLp f).aestronglyMeasurable (Filter.Eventually.of_forall fun x => by simp)
  rw [realToComplexL2, Lp.norm_toLp _ (Lp.memLp f).ofReal,
    Lp.norm_def]
  exact congrArg ENNReal.toReal he

noncomputable def strictHighHaarOperator (s K : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) :
    Lp ℝ 2 (periodicHaar ι) →L[ℝ] Lp ℝ 2 (periodicHaar ι) :=
  DGRHS.Kernel.integralOperator
    (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      strictHighKernel s K hs (p.1-p.2))
    (strictHighKernel_pair_memLp s K hs)

/-- The real Haar row integral and the complex Fourier convolution agree for
all L² inputs. Properness is supplied by the actual L² kernel operators and
the probability-Haar L²-to-L¹ embedding; no bounded-test reduction occurs. -/
lemma strictHighHaarOperator_complexification_ae
    (s K : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ))
    (L : ℝ) (hL : 0 ≤ L)
    (hcoeff : ∀ k, ‖strictHighCoeff s K k‖ ≤ L)
    (f : Lp ℝ 2 (periodicHaar ι)) :
    (realToComplexL2
      (strictHighHaarOperator s K hs f) : PeriodicTorus ι → ℂ) =ᵐ[periodicHaar ι]
      (fourierMultiplier (ι := ι) (strictHighCoeff s K) L hL hcoeff
        (realToComplexL2 f) : PeriodicTorus ι → ℂ) := by
  have hconv := strictHighConvolution_ae_eq_multiplier
      (ι := ι) s K hs L hL hcoeff (realToComplexL2 f)
  have hkernel : (fun x => (strictHighKernel s K hs x : ℂ)) =ᵐ[periodicHaar ι]
      strictHighL2 s K hs := strictHighKernel_coe_ae s K hs
  have hinput := realToComplexL2_coe_ae f
  have hT := DGRHS.Kernel.integralOperator_apply_ae
      (fun p : PeriodicTorus ι × PeriodicTorus ι =>
        strictHighKernel s K hs (p.1-p.2))
      (strictHighKernel_pair_memLp s K hs) f
  have hJ := realToComplexL2_coe_ae (strictHighHaarOperator s K hs f)
  have hconvReal :
      (realToComplexL2 (strictHighHaarOperator s K hs f) :
          PeriodicTorus ι → ℂ) =ᵐ[periodicHaar ι]
        (realToComplexL2 f ⋆[ContinuousLinearMap.mul ℂ ℂ,periodicHaar ι]
          (strictHighL2 s K hs : PeriodicTorus ι → ℂ)) := by
    filter_upwards [hT, hJ] with x hxT hxJ
    have hxT' : (strictHighHaarOperator s K hs f : PeriodicTorus ι → ℝ) x =
        ∫ y, strictHighKernel s K hs (x - y) * f y ∂periodicHaar ι := hxT
    rw [hxJ, hxT']
    have hrowK := strictHighKernel_memLp s K hs
    have hrowC := Lp.memLp (strictHighL2 s K hs)
    have hrK : MemLp (fun y => strictHighKernel s K hs (x-y)) 2
        (periodicHaar ι) :=
      hrowK.comp_measurePreserving (periodicHaar_preserving_sub_left x)
    have hrC : MemLp (fun y => strictHighL2 s K hs (x-y)) 2
        (periodicHaar ι) :=
      hrowC.comp_measurePreserving (periodicHaar_preserving_sub_left x)
    have hrealI : Integrable
        (fun y => strictHighKernel s K hs (x-y) * f y) (periodicHaar ι) :=
      hrK.integrable_mul (Lp.memLp f)
    have hcomplexI : Integrable
        (fun y => (f y : ℂ) * strictHighL2 s K hs (x-y)) (periodicHaar ι) :=
      (Lp.memLp f).ofReal.integrable_mul hrC
    have hroweq := (periodicHaar_preserving_sub_left x).quasiMeasurePreserving.ae_eq_comp
      hkernel
    calc
      ((∫ y, strictHighKernel s K hs (x-y) * f y ∂periodicHaar ι : ℝ) : ℂ) =
          ∫ y, ((strictHighKernel s K hs (x-y) * f y : ℝ) : ℂ)
            ∂periodicHaar ι :=
        ((@RCLike.ofRealLI ℂ _).integral_comp_comm _).symm
      _ = ∫ y, (f y : ℂ) * strictHighL2 s K hs (x-y) ∂periodicHaar ι := by
        apply integral_congr_ae
        filter_upwards [hroweq] with y hy
        have hy' : ((strictHighKernel s K hs (x-y) : ℝ) : ℂ) =
            strictHighL2 s K hs (x-y) := hy
        rw [Complex.ofReal_mul, hy']
        ring
      _ = (realToComplexL2 f ⋆[ContinuousLinearMap.mul ℂ ℂ,periodicHaar ι]
            (strictHighL2 s K hs : PeriodicTorus ι → ℂ)) x := by
        rw [convolution_mul]
        apply integral_congr_ae
        filter_upwards [hinput] with y hy
        rw [hy]
  exact hconvReal.trans hconv

/-- The complex multiplier norm yields the exact same bound for the real
strict-cutoff Haar integral operator. This uses its actual all-L²
complexification identity, not only a bounded-test quadratic-form estimate. -/
lemma strictHighHaarOperator_norm_le
    (s K : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hK : 1 ≤ K) :
    ‖strictHighHaarOperator s K hs2‖ ≤
      periodicRieszFourierAmplitude ι s * K^(s-(Fintype.card ι : ℝ)) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := ι)
  have hsd : s < (Fintype.card ι : ℝ) := by linarith
  have hA : 0 < periodicRieszFourierAmplitude ι s :=
    periodicRieszFourierAmplitude_pos s hs hsd
  have hKpos : 0 < K := by linarith
  let L := periodicRieszFourierAmplitude ι s * K^(s-(Fintype.card ι : ℝ))
  have hL : 0 ≤ L := mul_nonneg hA.le (Real.rpow_nonneg hKpos.le _)
  have hcoeff : ∀ k : PeriodicFrequency ι, ‖strictHighCoeff s K k‖ ≤ L := by
    intro k
    by_cases hk : K < ‖periodicFrequencyVector k‖
    · have hk0 : k ≠ 0 := by
        intro hzero
        subst k
        simp only [periodicFrequencyVector_zero, norm_zero] at hk
        linarith
      rw [strictHighCoeff, periodicRieszStrictHighCoeff, ite_eq_left hk]
      calc
        ‖periodicRieszFourierCoeff s k‖ =
            periodicRieszFourierAmplitude ι s *
              ‖periodicFrequencyVector k‖^(s-(Fintype.card ι : ℝ)) := by
          rw [periodicRieszFourierCoeff, ite_eq_right hk0, Complex.norm_real,
            Real.norm_eq_abs, abs_mul, abs_of_pos hA,
            abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        _ ≤ L := by
          dsimp [L]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hKpos (le_of_lt hk) (by linarith)) hA.le
    · rw [strictHighCoeff, periodicRieszStrictHighCoeff, ite_eq_right hk, norm_zero]
      exact hL
  have hintertwine := strictHighHaarOperator_complexification_ae
    s K hs2 L hL hcoeff
  have hmult := fourierMultiplier_norm_le
    (ι := ι) (strictHighCoeff s K) L hL hcoeff
  apply ContinuousLinearMap.opNorm_le_bound _ hL
  intro f
  rw [← realToComplexL2_norm (strictHighHaarOperator s K hs2 f)]
  have heq := hintertwine f
  calc
    ‖realToComplexL2 (strictHighHaarOperator s K hs2 f)‖ =
        ‖fourierMultiplier (ι := ι) (strictHighCoeff s K) L hL hcoeff
          (realToComplexL2 f)‖ := by
            have heqLp : realToComplexL2 (strictHighHaarOperator s K hs2 f) =
                fourierMultiplier (ι := ι) (strictHighCoeff s K) L hL hcoeff
                  (realToComplexL2 f) := Lp.ext heq
            rw [heqLp]
    _ ≤ ‖fourierMultiplier (ι := ι) (strictHighCoeff s K)
        L hL hcoeff‖ * ‖realToComplexL2 f‖ :=
        (fourierMultiplier (ι := ι) (strictHighCoeff s K) L hL hcoeff).le_opNorm _
    _ ≤ L * ‖realToComplexL2 f‖ :=
        mul_le_mul_of_nonneg_right hmult (norm_nonneg _)
    _ = L * ‖f‖ := by rw [realToComplexL2_norm]

end DGRHS.Periodic.RealifiedStrictCutoff

#print axioms DGRHS.Periodic.RealifiedStrictCutoff.strictHighHaarOperator_complexification_ae
#print axioms DGRHS.Periodic.RealifiedStrictCutoff.strictHighHaarOperator_norm_le
