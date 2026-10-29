import Mathlib
import DGPS.Examples.PositiveH1.Nonlinear
import DGPS.Examples.PositiveH1.Fourier
import DGPS.Analysis.CircleMoments

open MeasureTheory Filter Topology
open DGPS.Examples.PositiveH1.Fourier DGPS.Examples.PositiveH1.Model

/-!
# First harmonic recovery and normalized Taylor bounds (H1013)

For `0 < |t| ≤ 1/2` the density `ρ_t = 1 + t cos (2π x)` on the unit Haar circle is smooth,
positive and normalized; its nonconstant Fourier support is `{±1}`, so the spectral sums
`P(ρ_t) = Σ_{n ≥ 2} a_n |ρ̂_t(n)|²` and `Q(ρ_t) = Σ_{n ≥ 2} (2πn)² a_n |ρ̂_t(n)|²` vanish and
`R′ * ρ_t = 0` (so the actual convolution force of the positive `H¹` model vanishes). The entropy
and Fisher information Taylor estimates and the limit `I/(2H) → a₀` are those of H1044
(`DGPS.Analysis.CircleMoments.circle_first_harmonic_estimates`).

Placement note: the preparation names `DGPS/Examples/PositiveH1/Nonlinear.lean`; the declaration
is placed in this separate module `DGPS.Examples.PositiveH1.Harmonic` (concurrent edits of
`Nonlinear.lean`).
-/

namespace DGPS.Examples.PositiveH1.Harmonic

open DGPS.Analysis.CircleMoments (firstHarmonic firstHarmonicDensity firstHarmonicEntropy
  firstHarmonicFisher a0)

/-- `P(ρ) = Σ_{n ≥ 2} a_n |ρ̂(n)|²` (`a n = 0` for `n < 2`). -/
noncomputable def specP (ρ : Torus 1 → ℝ) : ℝ :=
  ∑' n : ℕ, a n * ‖fourierCoeff ρ (freq n)‖ ^ 2

/-- `Q(ρ) = Σ_{n ≥ 2} (2πn)² a_n |ρ̂(n)|²` (`a n = 0` for `n < 2`). -/
noncomputable def specQ (ρ : Torus 1 → ℝ) : ℝ :=
  ∑' n : ℕ, (2 * Real.pi * n) ^ 2 * a n * ‖fourierCoeff ρ (freq n)‖ ^ 2

theorem cosMode_one_eq : DGPS.Analysis.CircleMoments.cosMode = Fourier.cosMode 1 := by
  funext x
  simp [DGPS.Analysis.CircleMoments.cosMode, Fourier.cosMode]

theorem coeff_firstHarmonic (t : ℝ) (k : Fin 1 → ℤ) (h0 : k ≠ 0) (h1 : k ≠ freq 1)
    (h2 : k ≠ -freq 1) : fourierCoeff (firstHarmonic t) k = 0 := by
  rw [fourierCoeff_eq_integral]
  have hfun : ∀ y : Torus 1, UnitAddTorus.mFourier (-k) y * ((firstHarmonic t y : ℝ) : ℂ) =
      UnitAddTorus.mFourier (-k) y + ((t / 2 : ℝ) : ℂ) *
        (UnitAddTorus.mFourier (-k + freq 1) y + UnitAddTorus.mFourier (-k + -freq 1) y) := by
    intro y
    have hc : ((firstHarmonic t y : ℝ) : ℂ) = 1 + (t : ℂ) *
        ((UnitAddTorus.mFourier (freq 1) y + UnitAddTorus.mFourier (-freq 1) y) / 2) := by
      have := cosMode_ofReal 1 y
      rw [← cosMode_one_eq] at this
      simp only [firstHarmonic, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one, this]
      simp
    rw [hc, UnitAddTorus.mFourier_add, UnitAddTorus.mFourier_add]
    push_cast
    ring
  simp_rw [hfun]
  have hi : Integrable (fun x : Torus 1 => ((t / 2 : ℝ) : ℂ) *
      (UnitAddTorus.mFourier (-k + freq 1) x + UnitAddTorus.mFourier (-k + -freq 1) x))
      (haar 1) :=
    ((integrable_mFourier _).add (integrable_mFourier _)).const_mul _
  rw [integral_add (integrable_mFourier _) hi, integral_const_mul,
    integral_add (integrable_mFourier _) (integrable_mFourier _),
    integral_mFourier, integral_mFourier, integral_mFourier]
  have e0 : (-k = 0) ↔ False := by simpa using h0
  have e1 : (-k + freq 1 = 0) ↔ False := by
    constructor
    · intro h; exact h1 (by funext i; have := congrFun h i; simp [freq] at this ⊢; omega)
    · exact False.elim
  have e2 : (-k + -freq 1 = 0) ↔ False := by
    constructor
    · intro h; exact h2 (by funext i; have := congrFun h i; simp [freq] at this ⊢; omega)
    · exact False.elim
  simp [e0, e1, e2]

theorem coeff_freq_firstHarmonic (t : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    fourierCoeff (firstHarmonic t) (freq n) = 0 := by
  have key : ∀ m : ℤ, (m ≠ 0) → (m ≠ 1) → (m ≠ -1) → fourierCoeff (firstHarmonic t) (freq m) = 0 := by
    intro m hm0 hm1 hm2
    refine coeff_firstHarmonic t _ ?_ ?_ ?_
    · intro h; exact hm0 (by simpa [freq] using congrFun h 0)
    · intro h; exact hm1 (by simpa [freq] using congrFun h 0)
    · intro h; exact hm2 (by simpa [freq] using congrFun h 0)
  exact key n (by omega) (by omega) (by omega)

theorem specP_firstHarmonic (t : ℝ) : specP (firstHarmonic t) = 0 := by
  unfold specP
  have : ∀ n : ℕ, a n * ‖fourierCoeff (firstHarmonic t) (freq n)‖ ^ 2 = 0 := by
    intro n
    by_cases hn : 2 ≤ n
    · rw [coeff_freq_firstHarmonic t hn]; simp
    · rw [a_zero_of_lt (by omega)]; simp
  simp [this]

theorem specQ_firstHarmonic (t : ℝ) : specQ (firstHarmonic t) = 0 := by
  unfold specQ
  have : ∀ n : ℕ, (2 * Real.pi * n) ^ 2 * a n * ‖fourierCoeff (firstHarmonic t) (freq n)‖ ^ 2 = 0 := by
    intro n
    by_cases hn : 2 ≤ n
    · rw [coeff_freq_firstHarmonic t hn]; simp
    · rw [a_zero_of_lt (by omega)]; simp
  simp [this]

/-! ### `R′ * ρ_t = 0` -/

open DGPS.Examples.PositiveH1.Nonlinear (conv lift1 lift1_sub)

theorem integral_odd_eq_zero {f : Torus 1 → ℝ} (hf : ∀ x, f (-x) = - f x) :
    ∫ x, f x ∂haar 1 = 0 := by
  have : (haar 1).IsNegInvariant := Pi.isNegInvariant_volume
  have h := integral_neg_eq_self f (haar 1)
  simp_rw [hf] at h
  rw [integral_neg] at h
  linarith

theorem integral_dRM_mul_eq_zero (M : ℕ) {g : Torus 1 → ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → ∫ x, sinMode n x * g x ∂haar 1 = 0) (hgc : Continuous g) :
    ∫ x, dRM M x * g x ∂haar 1 = 0 := by
  simp_rw [dRM_eq, Finset.sum_mul]
  have hi : ∀ n ∈ Finset.Icc 2 M, Integrable (fun x => dcoef n * sinMode n x * g x) (haar 1) :=
    fun n _ => (memLp_two_of_continuous (((continuous_sinMode n).const_mul _).mul hgc)).integrable
      one_le_two
  rw [integral_finsetSum _ hi]
  refine Finset.sum_eq_zero fun n hn => ?_
  have hn2 : 2 ≤ n := (Finset.mem_Icc.1 hn).1
  have : ∀ x, dcoef n * sinMode n x * g x = dcoef n * (sinMode n x * g x) := fun x => by ring
  simp_rw [this]
  rw [integral_const_mul, hg n hn2, mul_zero]

theorem integral_dR_mul_eq_zero {g : Torus 1 → ℝ} (hgc : Continuous g)
    (hg : ∀ M : ℕ, ∫ x, dRM M x * g x ∂haar 1 = 0) : ∫ x, dR x * g x ∂haar 1 = 0 := by
  have hgm : MemLp g 2 (haar 1) := memLp_two_of_continuous hgc
  set c := Real.sqrt (∫ x, g x ^ 2 ∂haar 1)
  have hle : ∀ L : ℕ, 1 ≤ L → |∫ x, dR x * g x ∂haar 1| ≤ B L * c := by
    intro L hL
    have e : ∫ x, dR x * g x ∂haar 1 = ∫ x, (dR x - dRM L x) * g x ∂haar 1 := by
      have h1 : Integrable (fun x => dR x * g x) (haar 1) := memLp_dR.integrable_mul hgm
      have h2 : Integrable (fun x => dRM L x * g x) (haar 1) := (memLp_dRM L).integrable_mul hgm
      have : ∀ x, (dR x - dRM L x) * g x = dR x * g x - dRM L x * g x := fun x => by ring
      simp_rw [this]
      rw [integral_sub h1 h2, hg L, sub_zero]
    rw [e]
    refine (Nonlinear.abs_integral_mul_le (memLp_dR.sub (memLp_dRM L)) hgm).trans ?_
    have := integral_sq_dR_sub hL
    simp only [Pi.sub_apply]
    rw [this, Real.sqrt_sq (by unfold B; exact Real.sqrt_nonneg _)]
  have ht : Tendsto (fun L : ℕ => B L * c) atTop (𝓝 0) := by
    simpa using tendsto_B.mul_const c
  have : |∫ x, dR x * g x ∂haar 1| ≤ 0 :=
    ge_of_tendsto ht (by filter_upwards [eventually_ge_atTop 1] with L hL using hle L hL)
  exact abs_nonpos_iff.1 this

theorem firstHarmonic_sub (t : ℝ) (z w : ℝ) :
    firstHarmonic t (lift1 z - lift1 w) = 1 + t * (Real.cos (2 * Real.pi * z) *
      DGPS.Analysis.CircleMoments.cosMode (lift1 w) + Real.sin (2 * Real.pi * z) * sinMode 1 (lift1 w)) := by
  have e : lift1 z - lift1 w = lift1 (z - w) := (lift1_sub z w).symm
  have h1 : ∀ u : ℝ, DGPS.Analysis.CircleMoments.cosMode (lift1 u) = Real.cos (2 * Real.pi * u) := by
    intro u
    exact DGPS.Analysis.CircleMoments.cosMode_lift _
  have h2 : ∀ u : ℝ, sinMode 1 (lift1 u) = Real.sin (2 * Real.pi * u) := by
    intro u
    have := sinMode_lift 1 u
    rw [Nat.cast_one, mul_one] at this
    exact this
  unfold firstHarmonic
  rw [e, h1, h1, h2, mul_sub, Real.cos_sub]

theorem conv_dR_firstHarmonic (t : ℝ) (x : Torus 1) : conv dR (firstHarmonic t) x = 0 := by
  obtain ⟨z, rfl⟩ := Nonlinear.lift1_exists x
  have hcos : Continuous DGPS.Analysis.CircleMoments.cosMode :=
    DGPS.Analysis.CircleMoments.continuous_cosMode
  have hsin : Continuous (sinMode 1) := continuous_sinMode 1
  have hpt : ∀ y : Torus 1, dR y * firstHarmonic t (lift1 z - y) =
      dR y + (t * Real.cos (2 * Real.pi * z)) * (dR y * DGPS.Analysis.CircleMoments.cosMode y) +
        (t * Real.sin (2 * Real.pi * z)) * (dR y * sinMode 1 y) := by
    intro y
    obtain ⟨w, rfl⟩ := Nonlinear.lift1_exists y
    rw [firstHarmonic_sub]; ring
  have hI0 : Integrable dR (haar 1) := memLp_dR.integrable one_le_two
  have hIc : Integrable (fun y => dR y * DGPS.Analysis.CircleMoments.cosMode y) (haar 1) :=
    memLp_dR.integrable_mul (memLp_two_of_continuous hcos)
  have hIs : Integrable (fun y => dR y * sinMode 1 y) (haar 1) :=
    memLp_dR.integrable_mul (memLp_two_of_continuous hsin)
  have o0 : ∫ y, dR y ∂haar 1 = 0 := by
    have := integral_dR_mul_eq_zero (g := fun _ => (1:ℝ)) continuous_const (fun M => by
      simpa using integral_odd_eq_zero (f := dRM M) (dRM_neg M))
    simpa using this
  have oc : ∫ y, dR y * DGPS.Analysis.CircleMoments.cosMode y ∂haar 1 = 0 := by
    refine integral_dR_mul_eq_zero hcos fun M => ?_
    refine integral_dRM_mul_eq_zero M (fun n _ => integral_odd_eq_zero fun y => ?_) hcos
    rw [sinMode_neg, cosMode_one_eq, cosMode_neg]; ring
  have os : ∫ y, dR y * sinMode 1 y ∂haar 1 = 0 := by
    refine integral_dR_mul_eq_zero hsin fun M => ?_
    refine integral_dRM_mul_eq_zero M (fun n hn => ?_) hsin
    rw [integral_sinMode_mul n 1 (by omega) le_rfl]
    simp; omega
  show ∫ y, dR y * firstHarmonic t (lift1 z - y) ∂haar 1 = 0
  simp_rw [hpt]
  have hA : Integrable (fun y => dR y + (t * Real.cos (2 * Real.pi * z)) *
      (dR y * DGPS.Analysis.CircleMoments.cosMode y)) (haar 1) := hI0.add (hIc.const_mul _)
  rw [integral_add hA (hIs.const_mul _),
    integral_add hI0 (hIc.const_mul _), integral_const_mul, integral_const_mul, o0, oc, os]
  simp

theorem force_firstHarmonic {t : ℝ} (ht : |t| < 1) (x : Torus 1) :
    Nonlinear.positiveH1Drift.force (firstHarmonicDensity t ht) x = 0 := by
  show (EuclideanSpace.single (0 : Fin 1)
    (kappa * conv dR (firstHarmonicDensity t ht).density x) : Tangent 1) = 0
  rw [DGPS.Analysis.CircleMoments.firstHarmonicDensity_density ht, conv_dR_firstHarmonic]
  simp

/-- **H1013.** First harmonic recovery and normalized Taylor bounds: for `0 < |t| ≤ 1/2`,
`ρ_t = 1 + t cos (2π x)` is smooth, positive, normalized, `P(ρ_t) = Q(ρ_t) = 0`, `R′ * ρ_t = 0`
(hence the positive-`H¹` convolution force of `ρ_t` vanishes), `H(ρ_t) > 0`,
`|H(ρ_t) - t²/4| ≤ C t⁴`, `|I(ρ_t) - a₀ t²/2| ≤ C t⁴`, and `I/(2H) → a₀` as `t → 0`. -/
theorem first_harmonic_recovery_and_normalized_taylor_bounds :
    a0 = 4 * Real.pi ^ 2 ∧
    ∃ C : ℝ, 0 < C ∧
      (∀ t : ℝ, ∀ ht : |t| < 1, t ≠ 0 → |t| ≤ 1 / 2 →
        IsSmoothPeriodic (firstHarmonic t) ∧
        (∀ x, 0 < firstHarmonic t x) ∧
        ∫ x, firstHarmonic t x ∂haar 1 = 1 ∧
        specP (firstHarmonic t) = 0 ∧ specQ (firstHarmonic t) = 0 ∧
        (∀ x, conv dR (firstHarmonic t) x = 0) ∧
        (∀ x, Nonlinear.positiveH1Drift.force (firstHarmonicDensity t ht) x = 0) ∧
        0 < relativeEntropy (densityMeasure (firstHarmonicDensity t ht) : Measure (Torus 1))
          (haar 1) ∧
        relativeEntropy (densityMeasure (firstHarmonicDensity t ht) : Measure (Torus 1))
          (haar 1) ≠ ⊤ ∧
        |firstHarmonicEntropy t - t ^ 2 / 4| ≤ C * |t| ^ 4 ∧
        |firstHarmonicFisher t - a0 * t ^ 2 / 2| ≤ C * |t| ^ 4) ∧
      Tendsto (fun t : ℝ => firstHarmonicFisher t / (2 * firstHarmonicEntropy t))
        (𝓝[≠] 0) (𝓝 a0) := by
  obtain ⟨h0, C, hC, h, hlim⟩ := DGPS.Analysis.CircleMoments.circle_first_harmonic_estimates
  refine ⟨h0, C, hC, fun t ht ht0 hle => ?_, hlim⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h t ht ht0 hle
  exact ⟨h1, h2, h3, specP_firstHarmonic t, specQ_firstHarmonic t, conv_dR_firstHarmonic t,
    force_firstHarmonic ht, h5, h6, h7, h8⟩

end DGPS.Examples.PositiveH1.Harmonic
