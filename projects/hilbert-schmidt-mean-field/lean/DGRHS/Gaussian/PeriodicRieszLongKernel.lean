import DGRHS.Gaussian.PeriodicHeatRealSeries
import DGRHS.Gaussian.PeriodicRieszLowerCutFeature
import DGRHS.Gaussian.PeriodicLocalTsumDeriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
Packet P9h, unit 2 (part 8): the long heat-time piece of the periodic Riesz kernel as a smooth cosine
series with all derivatives bounded.

`periodicRieszLongKernel s ε z = Σ_k ĝ_ε(k) cos(2π⟨k,z⟩)` where `ĝ_ε = periodicRieszLCCoeff s ε` are the
lower-cut Fourier coefficients (heat time `> ε`).  For `ε > 0` the coefficients decay like
`e^{-ε‖k‖²/2}`, so the series is `C^∞` with `sup_z ‖D^j L(z)‖ ≤ Σ_k ĝ_ε(k) (2π‖k‖)^j < ∞`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

lemma abs_iteratedDeriv_cos_sin_le (n : ℕ) :
    (∀ t : ℝ, |iteratedDeriv n Real.cos t| ≤ 1) ∧ (∀ t : ℝ, |iteratedDeriv n Real.sin t| ≤ 1) := by
  induction n with
  | zero =>
    exact ⟨fun t => by simpa using Real.abs_cos_le_one t, fun t => by simpa using Real.abs_sin_le_one t⟩
  | succ n ih =>
    constructor
    · intro t
      rw [iteratedDeriv_succ', Real.deriv_cos', show (fun x => -Real.sin x) = -Real.sin from rfl,
        iteratedDeriv_neg]
      simpa using ih.2 t
    · intro t
      rw [iteratedDeriv_succ', Real.deriv_sin]
      exact ih.1 t

/-- The cosine mode `z ↦ cos(2π⟨k,z⟩)` as a continuous linear phase composed with `cos`. -/
def periodicPhaseCLM (k : PeriodicFrequency ι) : E →L[ℝ] ℝ :=
  (2 * Real.pi) • innerSL ℝ (periodicFrequencyVector k)

lemma periodicPhaseCLM_apply (k : PeriodicFrequency ι) (z : E) :
    periodicPhaseCLM k z = 2 * Real.pi * periodicPhase k z := by
  simp [periodicPhaseCLM, periodicPhase]

lemma norm_periodicPhaseCLM_le (k : PeriodicFrequency ι) :
    ‖periodicPhaseCLM k‖ ≤ 2 * Real.pi * ‖periodicFrequencyVector k‖ := by
  unfold periodicPhaseCLM
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  gcongr
  rw [innerSL_apply_norm]

lemma periodicCosMode_eq (k : PeriodicFrequency ι) :
    (fun z : E => Real.cos (2 * Real.pi * periodicPhase k z)) = Real.cos ∘ periodicPhaseCLM k := by
  funext z
  simp [periodicPhaseCLM_apply]

lemma contDiff_periodicCosMode (k : PeriodicFrequency ι) (N : ℕ∞) :
    ContDiff ℝ N (fun z : E => Real.cos (2 * Real.pi * periodicPhase k z)) := by
  rw [periodicCosMode_eq]
  exact Real.contDiff_cos.comp (periodicPhaseCLM k).contDiff

lemma norm_iteratedFDeriv_periodicCosMode_le (k : PeriodicFrequency ι) (j : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ j (fun z : E => Real.cos (2 * Real.pi * periodicPhase k z)) z‖ ≤
      (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ j := by
  rw [periodicCosMode_eq]
  rw [(periodicPhaseCLM k).iteratedFDeriv_comp_right (Real.contDiff_cos (n := ((j : ℕ) : WithTop ℕ∞))) z le_rfl]
  have h := (iteratedFDeriv ℝ j Real.cos (periodicPhaseCLM k z)).norm_compContinuousLinearMap_le
    (fun _ : Fin j => periodicPhaseCLM k)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have h1 : ‖iteratedFDeriv ℝ j Real.cos (periodicPhaseCLM k z)‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact (abs_iteratedDeriv_cos_sin_le j).1 _
  calc _ ≤ ‖iteratedFDeriv ℝ j Real.cos (periodicPhaseCLM k z)‖ * ‖periodicPhaseCLM k‖ ^ j := h
    _ ≤ 1 * (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ j := by
        gcongr
        exact norm_periodicPhaseCLM_le k
    _ = _ := one_mul _

/-- Polynomially weighted Gaussian sums over the lattice. -/
lemma summable_pow_mul_exp_neg_lattice (a : ℝ) (ha : 0 < a) (j : ℕ) :
    Summable fun k : PeriodicFrequency ι =>
      ‖periodicFrequencyVector k‖ ^ j * Real.exp (-a * ‖periodicFrequencyVector k‖ ^ 2) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = Fintype.card ι + j := ⟨_, rfl⟩
  have hs := (summable_periodicFrequency_inv_doubleDimension (ι := ι)).mul_left
    ((n.factorial : ℝ) / a ^ n)
  have h0 := periodic_zero_spike_summable (ι := ι) (1 : ℝ)
  refine (hs.add h0).of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
  by_cases hk : k = 0
  · subst k
    simp only [periodicFrequencyVector_zero, norm_zero, ↓reduceIte]
    have h1 : (0 : ℝ) ^ j * Real.exp (-a * 0 ^ 2) ≤ 1 := by
      rcases Nat.eq_zero_or_pos j with h | h
      · simp [h]
      · simp [zero_pow h.ne']
    have h2 : 0 ≤ (n.factorial : ℝ) / a ^ n * ((0 : ℝ)⁻¹) ^ (2 * Fintype.card ι) := by positivity
    exact h1.trans (le_add_of_nonneg_left h2)
  · simp only [hk, ↓reduceIte, add_zero]
    set r := ‖periodicFrequencyVector k‖ with hr
    have hr1 : 1 ≤ r := by
      have := periodicFrequency_norm_sq_ge_one hk
      nlinarith [norm_nonneg (periodicFrequencyVector k)]
    have hrpos : 0 < r := by linarith
    have hexp := periodic_gaussian_inverse_power_bound a r ha hrpos n
    have hri : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
    have hrj : r ^ j * r⁻¹ ^ (2 * j) = r⁻¹ ^ j := by
      rw [inv_pow, inv_pow]
      field_simp
      ring
    calc r ^ j * Real.exp (-a * r ^ 2) ≤ r ^ j * ((n.factorial : ℝ) / a ^ n * r⁻¹ ^ (2 * n)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (n.factorial : ℝ) / a ^ n * (r⁻¹ ^ (2 * Fintype.card ι) * (r ^ j * r⁻¹ ^ (2 * j))) := by
          rw [hn, show 2 * (Fintype.card ι + j) = 2 * Fintype.card ι + 2 * j by ring, pow_add]; ring
      _ ≤ (n.factorial : ℝ) / a ^ n * (r⁻¹ ^ (2 * Fintype.card ι) * 1) := by
          gcongr
          rw [hrj]
          exact pow_le_one₀ (by positivity) hri
      _ = _ := by ring


/-- The smooth long kernel: cosine series of the lower-cut coefficients. -/
def periodicRieszLongKernel (s ε : ℝ) (z : E) : ℝ :=
  ∑' k : PeriodicFrequency ι,
    periodicRieszLCCoeff s ε k * Real.cos (2 * Real.pi * periodicPhase k z)

lemma periodicRieszLCCoeff_le_gauss (s ε : ℝ) (hs0 : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hε : 0 < ε) (k : PeriodicFrequency ι) :
    periodicRieszLCCoeff s ε k ≤
      (2 : ℝ) ^ (((Fintype.card ι : ℝ) - s) / 2) * periodicRieszFourierAmplitude ι s *
        Real.exp (-(ε / 2) * ‖periodicFrequencyVector k‖ ^ 2) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hsd : s < (Fintype.card ι : ℝ) := by linarith
  have h1 := periodicRieszLCCoeff_le_trunc s ε hs0 hs2 hε k
  have h2 := periodicRieszTruncCoeff_le s (ε / 2) hs0 hsd k
  calc _ ≤ (2 : ℝ) ^ (((Fintype.card ι : ℝ) - s) / 2) * periodicRieszTruncCoeff s (ε / 2) k := h1
    _ ≤ (2 : ℝ) ^ (((Fintype.card ι : ℝ) - s) / 2) *
        (periodicRieszFourierAmplitude ι s * Real.exp (-(ε / 2) * ‖periodicFrequencyVector k‖ ^ 2)) := by
        gcongr
    _ = _ := by ring

lemma summable_periodicRieszLCCoeff_pow (s ε : ℝ) (hs0 : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hε : 0 < ε) (j : ℕ) :
    Summable fun k : PeriodicFrequency ι =>
      periodicRieszLCCoeff s ε k * (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ j := by
  have hs := (summable_pow_mul_exp_neg_lattice (ι := ι) (ε / 2) (by positivity) j).mul_left
    ((2 : ℝ) ^ (((Fintype.card ι : ℝ) - s) / 2) * periodicRieszFourierAmplitude ι s *
      (2 * Real.pi) ^ j)
  refine hs.of_nonneg_of_le (fun k => mul_nonneg (periodicRieszLCCoeff_nonneg s ε hs0 hε.le k)
    (by positivity)) (fun k => ?_)
  rw [mul_pow, ← mul_assoc]
  calc periodicRieszLCCoeff s ε k * (2 * Real.pi) ^ j * ‖periodicFrequencyVector k‖ ^ j
      ≤ ((2 : ℝ) ^ (((Fintype.card ι : ℝ) - s) / 2) * periodicRieszFourierAmplitude ι s *
          Real.exp (-(ε / 2) * ‖periodicFrequencyVector k‖ ^ 2)) * (2 * Real.pi) ^ j *
          ‖periodicFrequencyVector k‖ ^ j := by
        gcongr
        exact periodicRieszLCCoeff_le_gauss s ε hs0 hs2 hε k
    _ = _ := by ring

lemma norm_iteratedFDeriv_longTerm_le (s ε : ℝ) (hs0 : 0 < s) (hε : 0 < ε) (k : PeriodicFrequency ι)
    (j : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ j (fun z : E => periodicRieszLCCoeff s ε k *
        Real.cos (2 * Real.pi * periodicPhase k z)) z‖ ≤
      periodicRieszLCCoeff s ε k * (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ j := by
  have hc : ContDiffAt ℝ j (fun z : E => Real.cos (2 * Real.pi * periodicPhase k z)) z :=
    (contDiff_periodicCosMode k (j : ℕ∞)).contDiffAt
  change ‖iteratedFDeriv ℝ j (periodicRieszLCCoeff s ε k •
    (fun z : E => Real.cos (2 * Real.pi * periodicPhase k z))) z‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply hc, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (periodicRieszLCCoeff_nonneg s ε hs0 hε.le k)]
  exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_periodicCosMode_le k j z)
    (periodicRieszLCCoeff_nonneg s ε hs0 hε.le k)

lemma contDiff_periodicRieszLongKernel (s ε : ℝ) (hs0 : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hε : 0 < ε) (N : ℕ∞) : ContDiff ℝ N (periodicRieszLongKernel (ι := ι) s ε) := by
  unfold periodicRieszLongKernel
  refine contDiff_tsum (f := fun (k : PeriodicFrequency ι) (z : E) =>
      periodicRieszLCCoeff s ε k * Real.cos (2 * Real.pi * periodicPhase k z))
    (v := fun j k => periodicRieszLCCoeff s ε k * (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ j)
    (fun k => contDiff_const.mul (contDiff_periodicCosMode k N))
    (fun j _ => summable_periodicRieszLCCoeff_pow s ε hs0 hs2 hε j) ?_
  intro j k z _
  exact norm_iteratedFDeriv_longTerm_le s ε hs0 hε k j z

/-- All derivatives of the smooth long kernel are bounded, uniformly in the point. -/
lemma norm_iteratedFDeriv_periodicRieszLongKernel_le (s ε : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hε : 0 < ε) (j : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ j (periodicRieszLongKernel (ι := ι) s ε) z‖ ≤
      ∑' k : PeriodicFrequency ι,
        periodicRieszLCCoeff s ε k * (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ j := by
  unfold periodicRieszLongKernel
  have hv := summable_periodicRieszLCCoeff_pow s ε hs0 hs2 hε j
  have h := iteratedFDeriv_tsum_apply (𝕜 := ℝ) (N := (j : ℕ∞))
    (f := fun (k : PeriodicFrequency ι) (z : E) =>
      periodicRieszLCCoeff s ε k * Real.cos (2 * Real.pi * periodicPhase k z))
    (v := fun j k => periodicRieszLCCoeff s ε k * (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ j)
    (fun k => contDiff_const.mul (contDiff_periodicCosMode k j))
    (fun i _ => summable_periodicRieszLCCoeff_pow s ε hs0 hs2 hε i)
    (fun i k z _ => norm_iteratedFDeriv_longTerm_le s ε hs0 hε k i z) (k := j) le_rfl z
  rw [h]
  have hb : ∀ k, ‖iteratedFDeriv ℝ j (fun z : E => periodicRieszLCCoeff s ε k *
        Real.cos (2 * Real.pi * periodicPhase k z)) z‖ ≤
      periodicRieszLCCoeff s ε k * (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ j :=
    fun k => norm_iteratedFDeriv_longTerm_le s ε hs0 hε k j z
  have hsn : Summable fun k => ‖iteratedFDeriv ℝ j (fun z : E => periodicRieszLCCoeff s ε k *
        Real.cos (2 * Real.pi * periodicPhase k z)) z‖ :=
    hv.of_nonneg_of_le (fun k => norm_nonneg _) hb
  exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hb hv)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.contDiff_periodicRieszLongKernel
#print axioms DGRHS.Periodic.norm_iteratedFDeriv_periodicRieszLongKernel_le
