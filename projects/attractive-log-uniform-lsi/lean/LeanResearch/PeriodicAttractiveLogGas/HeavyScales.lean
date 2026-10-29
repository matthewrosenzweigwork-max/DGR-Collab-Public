import LeanResearch.PeriodicAttractiveLogGas.SmoothOccupations
import LeanResearch.PeriodicAttractiveLogGas.GreenCovarianceBounds
import Mathlib.Algebra.Order.Floor.Semiring

/-! The exact finite number of scales and resolution threshold used in
Section 4.4. Analytic constants c,K,C_h remain explicit parameters for the
later actual Green/virial instantiation. No admissibility or growth bound
is assumed. The final scalar counting lemma must still be applied to the
actual radial particle counts; it is not by itself Lemma 4.8. -/

noncomputable section
open Set Metric
open scoped BigOperators

namespace PeriodicAttractiveLogGas.HeavyScales

def scaleCount (β₀ δ c : ℝ) : ℕ :=
  ⌈Real.log (2 / δ) / Real.log (1 + c * (4 - β₀))⌉₊

def resolution (β₀ δ c K Ch : ℝ) : ℝ :=
  max (16 * K * (2 * K) ^ (scaleCount β₀ δ c - 1))
    (32 * β₀ * Ch * (2 * K) ^ (scaleCount β₀ δ c - 1) / (4 - β₀))

def scaleRadius (J : ℕ) (K : ℝ) (m : ℕ) : ℝ := (2 / J) * (2 * K) ^ m

theorem scaleCount_pos {β₀ δ c : ℝ} (hβ : β₀ < 4) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hc : 0 < c) : 0 < scaleCount β₀ δ c := by
  apply Nat.ceil_pos.mpr
  apply div_pos
  · apply Real.log_pos
    apply (lt_div_iff₀ hδ).mpr
    linarith
  · apply Real.log_pos
    nlinarith

/-- The actual logarithmic ceiling ensures the multiplicative count
growth reaches the reciprocal starting fraction. -/
theorem scaleCount_power {β₀ δ c : ℝ} (hβ : β₀ < 4) (hδ : 0 < δ)
    (hc : 0 < c) :
    2 / δ ≤ (1 + c * (4 - β₀)) ^ scaleCount β₀ δ c := by
  have ha : 1 < 1 + c * (4 - β₀) := by nlinarith
  have hlog := Real.log_pos ha
  have hceil := Nat.le_ceil (Real.log (2 / δ) / Real.log (1 + c * (4 - β₀)))
  apply (Real.log_le_log_iff (by positivity) (pow_pos (by linarith) _)).mp
  rw [Real.log_pow]
  exact (div_le_iff₀ hlog).mp hceil

theorem scaleRadius_pos {J : ℕ} {K : ℝ} (hJ : 0 < J) (hK : 0 < K) (m : ℕ) :
    0 < scaleRadius J K m := by unfold scaleRadius; positivity

theorem scaleRadius_succ (J : ℕ) (K : ℝ) (m : ℕ) :
    scaleRadius J K (m + 1) = (2 * K) * scaleRadius J K m := by
  unfold scaleRadius
  rw [pow_succ]
  ring

theorem scaleRadius_mono {J : ℕ} {K : ℝ} (hK : 1 ≤ 2 * K) {m n : ℕ} (hmn : m ≤ n) :
    scaleRadius J K m ≤ scaleRadius J K n :=
  mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK hmn) (by positivity)

theorem resolution_positive {β₀ δ c K Ch : ℝ} (hK : 0 < K) :
    0 < resolution β₀ δ c K Ch := by
  exact lt_of_lt_of_le (by positivity) (le_max_left _ _)

theorem mesh_pos {β₀ δ c K Ch : ℝ} {J : ℕ} (hK : 0 < K)
    (hJ : resolution β₀ δ c K Ch ≤ J) : 0 < J := by
  exact_mod_cast (lt_of_lt_of_le (resolution_positive hK) hJ)

/-- Every scale used for the collective test satisfies all three source
smallness bounds; the last counting radius is deliberately excluded. -/
theorem scale_admissibility {β₀ δ c K Ch : ℝ} {J m : ℕ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hK : 8 ≤ K) (hCh : 0 ≤ Ch)
    (hJ : resolution β₀ δ c K Ch ≤ J) (hm : m < scaleCount β₀ δ c) :
    scaleRadius J K m ≤ 1 / (8 * K) ∧ 1 / (8 * K) ≤ 1 / 64 ∧
      2 * K * scaleRadius J K m ≤ 1 / 4 ∧
      16 * β₀ * Ch * scaleRadius J K m ≤ 4 - β₀ := by
  have hKp : 0 < K := by linarith
  have hJp : (0 : ℝ) < J := by exact_mod_cast mesh_pos hKp hJ
  have hgap : 0 < 4 - β₀ := by linarith
  have hp : (2 * K) ^ m ≤ (2 * K) ^ (scaleCount β₀ δ c - 1) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hmesh1 : 16 * K * (2 * K) ^ (scaleCount β₀ δ c - 1) ≤ J :=
    (le_max_left _ _).trans hJ
  have hmesh2 : 32 * β₀ * Ch * (2 * K) ^ (scaleCount β₀ δ c - 1) / (4 - β₀) ≤ J :=
    (le_max_right _ _).trans hJ
  have h8 : 8 * K * scaleRadius J K m ≤ 1 := by
    rw [show 8 * K * scaleRadius J K m = 16 * K * (2 * K) ^ m / J by
      unfold scaleRadius; ring]
    apply (div_le_one hJp).mpr
    exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans hmesh1
  have hs : scaleRadius J K m ≤ 1 / (8 * K) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * K)).mpr
    simpa only [mul_comm] using h8
  refine ⟨hs, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < 8 * K)).mpr
    linarith
  · nlinarith
  · rw [show 16 * β₀ * Ch * scaleRadius J K m = 32 * β₀ * Ch * (2 * K) ^ m / J by
      unfold scaleRadius; ring]
    apply (div_le_iff₀ hJp).mpr
    have he := (div_le_iff₀ hgap).mp hmesh2
    have hi := mul_le_mul_of_nonneg_left hp (show 0 ≤ 32 * β₀ * Ch by positivity)
    nlinarith

theorem cutoff_ball_lt_initial_scale {J : ℕ} (hJ : 0 < J) (K : ℝ) :
    Real.sqrt 2 / J < scaleRadius J K 0 := by
  simp only [scaleRadius, pow_zero, mul_one]
  apply div_lt_div_of_pos_right _ (by exact_mod_cast hJ)
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- A bounded sequence of particle counts starting above the heavy
fraction cannot grow by the specified factor at every selected scale.
Actual shell support/count comparisons supply this lemma's count data
later; it imposes no separation of individual particles. -/
theorem exists_nonexpanding_scale {β₀ δ c : ℝ} {N : ℕ}
    (hβ : β₀ < 4) (hδ : 0 < δ) (hc : 0 < c)
    (count : ℕ → ℝ) (hstart : δ * N / 2 < count 0)
    (hfinal : count (scaleCount β₀ δ c) ≤ N) :
    ∃ m < scaleCount β₀ δ c,
      count (m + 1) ≤ (1 + c * (4 - β₀)) * count m := by
  by_contra hh
  push Not at hh
  let a := 1 + c * (4 - β₀)
  have ha : 0 < a := by dsimp [a]; nlinarith
  have hg (m : ℕ) (hm : m ≤ scaleCount β₀ δ c) :
      a ^ m * (δ * N / 2) < count m := by
    induction m with
    | zero => simpa only [pow_zero, one_mul] using hstart
    | succ m ih =>
      have hi := ih (by omega)
      have hs := hh m (by omega)
      have ht := mul_lt_mul_of_pos_left hi ha
      rw [pow_succ]
      change a ^ m * a * (δ * N / 2) < _
      nlinarith
  have hbound : (N : ℝ) ≤ a ^ scaleCount β₀ δ c * (δ * N / 2) := by
    have h := mul_le_mul_of_nonneg_right (scaleCount_power hβ hδ hc)
      (show 0 ≤ δ * N / 2 by positivity)
    have he : 2 / δ * (δ * (N : ℝ) / 2) = N := by field_simp
    simpa only [he] using h
  exact (not_lt_of_ge hfinal) (hbound.trans_lt (hg _ le_rfl))

/-- The source C_h: the supremum of the actual ordinary remainder
derivative norm on the closed quarter ball. -/
def remainderGradientBound : ℝ :=
  sSup ((fun x : PlanarSpace ↦ ‖fderiv ℝ smoothGreenLogRemainder x‖) ''
    closedBall (0 : PlanarSpace) (1 / 4 : ℝ))

theorem remainder_gradient_norm_le {x : PlanarSpace}
    (hx : x ∈ closedBall (0 : PlanarSpace) (1 / 4 : ℝ)) :
    ‖fderiv ℝ smoothGreenLogRemainder x‖ ≤ remainderGradientBound := by
  obtain ⟨M, _, hM⟩ := exists_smoothGreenLogRemainder_quarter_bounds
  have hb : BddAbove ((fun x : PlanarSpace ↦ ‖fderiv ℝ smoothGreenLogRemainder x‖) ''
      closedBall (0 : PlanarSpace) (1 / 4 : ℝ)) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (hM y hy).2.1
  exact le_csSup hb ⟨x, hx, rfl⟩

theorem remainderGradientBound_nonneg : 0 ≤ remainderGradientBound :=
  (norm_nonneg _).trans (remainder_gradient_norm_le
    (show (0 : PlanarSpace) ∈ closedBall 0 (1 / 4 : ℝ) by simp))

def virialConstant (β₀ : ℝ) : ℝ := 228 + 168 * β₀ * ConditionalLawEstimates.kernelConstant

def separationConstant (β₀ : ℝ) : ℝ := 1 / (64 * virialConstant β₀)

def separationRadius (β₀ : ℝ) : ℝ :=
  max 8 (4 + Real.sqrt (5120 * β₀ * GreenCovarianceBounds.hessianConstant / (4 - β₀)))

theorem virialConstant_ge {β₀ : ℝ} (hβ : 0 ≤ β₀) : 228 ≤ virialConstant β₀ := by
  have hK := ConditionalLawEstimates.kernelConstant_pos
  unfold virialConstant
  apply le_add_of_nonneg_right
  positivity

theorem separationConstant_pos {β₀ : ℝ} (hβ : 0 ≤ β₀) : 0 < separationConstant β₀ := by
  have h := virialConstant_ge hβ
  unfold separationConstant
  positivity

theorem separation_fraction_lt {β₀ : ℝ} (hβ : 0 ≤ β₀) :
    2 * separationConstant β₀ * (4 - β₀) < 1 / 8 := by
  have h := virialConstant_ge hβ
  rw [show 2 * separationConstant β₀ * (4 - β₀) = (4 - β₀) / (32 * virialConstant β₀) by
    unfold separationConstant; ring]
  apply (div_lt_iff₀ (by positivity : 0 < 32 * virialConstant β₀)).mpr
  linarith

theorem separationRadius_ge_eight (β₀ : ℝ) : 8 ≤ separationRadius β₀ := le_max_left _ _

/-- Exact far-field error allowed by the source choice K_0. -/
theorem far_error_bound {β₀ K : ℝ} (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4)
    (hK : separationRadius β₀ ≤ K) :
    320 * β₀ * GreenCovarianceBounds.hessianConstant / (K - 4) ^ 2 ≤ (4 - β₀) / 16 := by
  have h8 : 8 ≤ K := (separationRadius_ge_eight β₀).trans hK
  have hgap : 0 < 4 - β₀ := by linarith
  have hC := GreenCovarianceBounds.hessianConstant_pos
  have hr : Real.sqrt (5120 * β₀ * GreenCovarianceBounds.hessianConstant / (4 - β₀)) ≤ K - 4 := by
    have h := (le_max_right (8 : ℝ) _).trans hK
    change 4 + Real.sqrt (5120 * β₀ * GreenCovarianceBounds.hessianConstant / (4 - β₀)) ≤ K at h
    linarith
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (by linarith : 0 ≤ K - 4)).mpr hr
  rw [Real.sq_sqrt (by positivity)] at hs
  have hm := (div_le_iff₀ hgap).mp hs
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < K - 4))).mpr
  nlinarith

def sourceScaleCount (β₀ δ : ℝ) : ℕ := scaleCount β₀ δ (separationConstant β₀)

def sourceResolution (β₀ δ : ℝ) : ℝ :=
  resolution β₀ δ (separationConstant β₀) (separationRadius β₀) remainderGradientBound

theorem sourceScaleCount_pos {β₀ δ : ℝ} (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4)
    (hδ : 0 < δ) (hδ1 : δ < 1) : 0 < sourceScaleCount β₀ δ :=
  scaleCount_pos hβ hδ hδ1 (separationConstant_pos hβ₀)

/-- The actual source parameters, chosen before N and J, satisfy every
radius restriction for every sufficiently fine resolution. -/
theorem source_scale_admissibility {β₀ δ : ℝ} {J m : ℕ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hJ : sourceResolution β₀ δ ≤ J)
    (hm : m < sourceScaleCount β₀ δ) :
    scaleRadius J (separationRadius β₀) m ≤ 1 / (8 * separationRadius β₀) ∧
      1 / (8 * separationRadius β₀) ≤ 1 / 64 ∧
      2 * separationRadius β₀ * scaleRadius J (separationRadius β₀) m ≤ 1 / 4 ∧
      16 * β₀ * remainderGradientBound * scaleRadius J (separationRadius β₀) m ≤ 4 - β₀ :=
  scale_admissibility hβ₀ hβ (separationRadius_ge_eight β₀)
    remainderGradientBound_nonneg hJ hm

end PeriodicAttractiveLogGas.HeavyScales
