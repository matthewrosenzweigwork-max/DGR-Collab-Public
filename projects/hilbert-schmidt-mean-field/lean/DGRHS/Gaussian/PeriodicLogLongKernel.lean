import DGRHS.Gaussian.PeriodicLogLCKernel
import DGRHS.Gaussian.PeriodicRieszLongKernel

/-!
Packet P9h, unit 3 (LOG, part 4): the long heat-time piece of the periodic LOG kernel as a smooth
cosine series with all derivatives bounded (the `s = 0` analogue of `PeriodicRieszLongKernel`).
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The smooth long LOG kernel: cosine series of the lower-cut coefficients. -/
def periodicLogLongKernel (ε : ℝ) (z : E) : ℝ :=
  ∑' k : PeriodicFrequency ι,
    periodicLogLCCoeff ε k * Real.cos (2 * Real.pi * periodicPhase k z)

lemma periodicLogLCCoeff_le_gauss (ε : ℝ) (hε : 0 < ε) (k : PeriodicFrequency ι) :
    periodicLogLCCoeff ε k ≤
      (2 : ℝ) ^ ((Fintype.card ι : ℝ) / 2) * (periodicLogConstant ι / (2 * Real.pi) ^ (Fintype.card ι)) *
        Real.exp (-(ε / 2) * ‖periodicFrequencyVector k‖ ^ 2) := by
  have h1 := periodicLogLCCoeff_le_trunc ε hε k
  have h2 := periodicLogTruncCoeff_le (ι := ι) (ε / 2) k
  calc _ ≤ (2 : ℝ) ^ ((Fintype.card ι : ℝ) / 2) * periodicLogTruncCoeff (ε / 2) k := h1
    _ ≤ (2 : ℝ) ^ ((Fintype.card ι : ℝ) / 2) *
        (periodicLogConstant ι / (2 * Real.pi) ^ (Fintype.card ι) *
          Real.exp (-(ε / 2) * ‖periodicFrequencyVector k‖ ^ 2)) := by
        gcongr
    _ = _ := by ring

lemma summable_periodicLogLCCoeff_pow (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    Summable fun k : PeriodicFrequency ι =>
      periodicLogLCCoeff ε k * (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ j := by
  have hs := (summable_pow_mul_exp_neg_lattice (ι := ι) (ε / 2) (by positivity) j).mul_left
    ((2 : ℝ) ^ ((Fintype.card ι : ℝ) / 2) * (periodicLogConstant ι / (2 * Real.pi) ^ (Fintype.card ι)) *
      (2 * Real.pi) ^ j)
  refine hs.of_nonneg_of_le (fun k => mul_nonneg (periodicLogLCCoeff_nonneg ε hε.le k)
    (by positivity)) (fun k => ?_)
  rw [mul_pow, ← mul_assoc]
  calc periodicLogLCCoeff ε k * (2 * Real.pi) ^ j * ‖periodicFrequencyVector k‖ ^ j
      ≤ ((2 : ℝ) ^ ((Fintype.card ι : ℝ) / 2) * (periodicLogConstant ι / (2 * Real.pi) ^ (Fintype.card ι)) *
          Real.exp (-(ε / 2) * ‖periodicFrequencyVector k‖ ^ 2)) * (2 * Real.pi) ^ j *
          ‖periodicFrequencyVector k‖ ^ j := by
        gcongr
        exact periodicLogLCCoeff_le_gauss ε hε k
    _ = _ := by ring

lemma norm_iteratedFDeriv_logLongTerm_le (ε : ℝ) (hε : 0 < ε) (k : PeriodicFrequency ι)
    (j : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ j (fun z : E => periodicLogLCCoeff ε k *
        Real.cos (2 * Real.pi * periodicPhase k z)) z‖ ≤
      periodicLogLCCoeff ε k * (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ j := by
  have hc : ContDiffAt ℝ j (fun z : E => Real.cos (2 * Real.pi * periodicPhase k z)) z :=
    (contDiff_periodicCosMode k (j : ℕ∞)).contDiffAt
  change ‖iteratedFDeriv ℝ j (periodicLogLCCoeff ε k •
    (fun z : E => Real.cos (2 * Real.pi * periodicPhase k z))) z‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply hc, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (periodicLogLCCoeff_nonneg ε hε.le k)]
  exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_periodicCosMode_le k j z)
    (periodicLogLCCoeff_nonneg ε hε.le k)

lemma contDiff_periodicLogLongKernel (ε : ℝ) (hε : 0 < ε) (N : ℕ∞) :
    ContDiff ℝ N (periodicLogLongKernel (ι := ι) ε) := by
  unfold periodicLogLongKernel
  refine contDiff_tsum (f := fun (k : PeriodicFrequency ι) (z : E) =>
      periodicLogLCCoeff ε k * Real.cos (2 * Real.pi * periodicPhase k z))
    (v := fun j k => periodicLogLCCoeff ε k * (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ j)
    (fun k => contDiff_const.mul (contDiff_periodicCosMode k N))
    (fun j _ => summable_periodicLogLCCoeff_pow ε hε j) ?_
  intro j k z _
  exact norm_iteratedFDeriv_logLongTerm_le ε hε k j z

/-- All derivatives of the smooth long LOG kernel are bounded, uniformly in the point. -/
lemma norm_iteratedFDeriv_periodicLogLongKernel_le (ε : ℝ) (hε : 0 < ε) (j : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ j (periodicLogLongKernel (ι := ι) ε) z‖ ≤
      ∑' k : PeriodicFrequency ι,
        periodicLogLCCoeff ε k * (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ j := by
  unfold periodicLogLongKernel
  have hv := summable_periodicLogLCCoeff_pow (ι := ι) ε hε j
  have h := iteratedFDeriv_tsum_apply (𝕜 := ℝ) (N := (j : ℕ∞))
    (f := fun (k : PeriodicFrequency ι) (z : E) =>
      periodicLogLCCoeff ε k * Real.cos (2 * Real.pi * periodicPhase k z))
    (v := fun j k => periodicLogLCCoeff ε k * (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ j)
    (fun k => contDiff_const.mul (contDiff_periodicCosMode k j))
    (fun i _ => summable_periodicLogLCCoeff_pow ε hε i)
    (fun i k z _ => norm_iteratedFDeriv_logLongTerm_le ε hε k i z) (k := j) le_rfl z
  rw [h]
  have hb : ∀ k, ‖iteratedFDeriv ℝ j (fun z : E => periodicLogLCCoeff ε k *
        Real.cos (2 * Real.pi * periodicPhase k z)) z‖ ≤
      periodicLogLCCoeff ε k * (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ j :=
    fun k => norm_iteratedFDeriv_logLongTerm_le ε hε k j z
  have hsn : Summable fun k => ‖iteratedFDeriv ℝ j (fun z : E => periodicLogLCCoeff ε k *
        Real.cos (2 * Real.pi * periodicPhase k z)) z‖ :=
    hv.of_nonneg_of_le (fun k => norm_nonneg _) hb
  exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hb hv)

lemma periodicLogLongKernel_neg (ε : ℝ) (z : E) :
    periodicLogLongKernel (ι := ι) ε (-z) = periodicLogLongKernel ε z := by
  unfold periodicLogLongKernel
  refine tsum_congr fun k => ?_
  have : periodicPhase k (-z) = -periodicPhase k z := by simp [periodicPhase]
  rw [this, mul_neg, Real.cos_neg]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.contDiff_periodicLogLongKernel
#print axioms DGRHS.Periodic.norm_iteratedFDeriv_periodicLogLongKernel_le
