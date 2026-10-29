import SharpSymmetricLSI.Paper.LamSym5

/-!
# (2.8) (lane s42): the variance of the linear test statistics

Section 8.5: for `f_N = ∑_{i<n} v_i Z_{N,i}` (the fluctuations `Z_{N,i} = fluct e N i`), the
Gibbs variances converge to `⟨v, C v⟩`, given the convergence in law of the fluctuations (R27,
`gaussian_limit_law`) and a uniform moment bound `∫ exp(a f_N²) dP_N ≤ B` (the bound the linear
test drafts derive from `lintegral_exp_sq_sum_le`).

* `tendsto_integral_pow_of_law`: convergence in law of real random variables `Y_N → ν` plus a
  uniform fourth moment bound gives `∫ Y_N^k → ∫ x^k dν` for `k ≤ 3` (truncation at level `M`,
  error `≤ 2B/M^{4-k}`), and `x^k ∈ L¹(ν)`.
* `tendsto_var_linStat`: the variance limit.
-/

open MeasureTheory Filter Topology ProbabilityTheory Finset
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

/-- Truncation at level `M`. -/
def clipF (M x : ℝ) : ℝ := max (-M) (min x M)

theorem continuous_clipF (M : ℝ) : Continuous (clipF M) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem abs_clipF_le {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : |clipF M x| ≤ M := by
  unfold clipF; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

theorem clipF_eq {M x : ℝ} (h : |x| ≤ M) : clipF M x = x := by
  unfold clipF; rw [abs_le] at h
  rw [min_eq_left h.2, max_eq_right h.1]

theorem abs_clipF {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : |clipF M x| = min |x| M := by
  rcases le_or_gt |x| M with h | h
  · rw [clipF_eq h, min_eq_left h]
  · rw [min_eq_right h.le]
    unfold clipF
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx] at h
      rw [min_eq_right h.le, max_eq_right (by linarith), abs_of_nonneg hM]
    · rw [abs_of_neg hx] at h
      rw [min_eq_left (by linarith), max_eq_left (by linarith), abs_neg, abs_of_nonneg hM]

theorem abs_clipF_le_abs {M x : ℝ} (hM : 0 ≤ M) : |clipF M x| ≤ |x| := by
  rcases le_or_gt |x| M with h | h
  · rw [clipF_eq h]
  · exact (abs_clipF_le hM x).trans h.le

/-- `|x^k - clip(x)^k| ≤ 2 x⁴ / M^{4-k}` for `k ≤ 4`, `M > 0`. -/
theorem abs_pow_sub_clip_le {M : ℝ} (hM : 0 < M) {k : ℕ} (hk : k ≤ 4) (x : ℝ) :
    |x ^ k - clipF M x ^ k| ≤ 2 * x ^ 4 / M ^ (4 - k) := by
  rcases le_or_gt |x| M with h | h
  · rw [clipF_eq h, sub_self, abs_zero]; positivity
  · have h1 : |x ^ k - clipF M x ^ k| ≤ 2 * |x| ^ k := by
      refine (abs_sub _ _).trans ?_
      rw [abs_pow, abs_pow]
      have := pow_le_pow_left₀ (abs_nonneg _) (abs_clipF_le_abs hM.le (x := x)) k
      linarith
    have h2 : |x| ^ k * M ^ (4 - k) ≤ x ^ 4 := by
      calc |x| ^ k * M ^ (4 - k) ≤ |x| ^ k * |x| ^ (4 - k) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM.le h.le _) (by positivity)
        _ = |x| ^ 4 := by rw [← pow_add, Nat.add_sub_cancel' hk]
        _ = x ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
    refine h1.trans ?_
    rw [le_div_iff₀ (by positivity)]
    nlinarith [h2]

/-- The bounded continuous function `clip(x)^k`. -/
noncomputable def clipPow (M : ℝ) (hM : 0 ≤ M) (k : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => clipF M x ^ k, (continuous_clipF M).pow k⟩
    (2 * M ^ k) fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      refine (abs_sub _ _).trans ?_
      rw [abs_pow, abs_pow]
      have h1 := pow_le_pow_left₀ (abs_nonneg _) (abs_clipF_le hM x) k
      have h2 := pow_le_pow_left₀ (abs_nonneg _) (abs_clipF_le hM y) k
      linarith

theorem clipPow_apply {M : ℝ} (hM : 0 ≤ M) (k : ℕ) (x : ℝ) :
    clipPow M hM k x = clipF M x ^ k := rfl

section law
variable {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] {P : ∀ N, Measure (Ω N)}
  [∀ N, IsProbabilityMeasure (P N)] {Y : ∀ N, Ω N → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- The truncation error. -/
theorem abs_integral_pow_sub_clip_le {α : Type*} [MeasurableSpace α] {m : Measure α}
    [IsProbabilityMeasure m] {Z : α → ℝ} (hZ : AEStronglyMeasurable Z m)
    (h4 : Integrable (fun ω => Z ω ^ 4) m) {M : ℝ} (hM : 0 < M) {k : ℕ} (hk : k ≤ 4) :
    Integrable (fun ω => Z ω ^ k) m ∧
      |∫ ω, Z ω ^ k ∂m - ∫ ω, clipF M (Z ω) ^ k ∂m| ≤ 2 * (∫ ω, Z ω ^ 4 ∂m) / M ^ (4 - k) := by
  have hc : Integrable (fun ω => clipF M (Z ω) ^ k) m :=
    Integrable.of_bound (((continuous_clipF M).pow k).comp_aestronglyMeasurable hZ) (M ^ k)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_clipF_le hM.le _) k)
  have hdiff : Integrable (fun ω => Z ω ^ k - clipF M (Z ω) ^ k) m :=
    Integrable.mono' (h4.const_mul (2 / M ^ (4 - k)))
      ((hZ.pow k).sub (((continuous_clipF M).pow k).comp_aestronglyMeasurable hZ))
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact (abs_pow_sub_clip_le hM hk (Z ω)).trans (le_of_eq (by ring)))
  have hk' : Integrable (fun ω => Z ω ^ k) m := (hdiff.add hc).congr
    (Eventually.of_forall fun ω => by simp)
  refine ⟨hk', ?_⟩
  rw [← integral_sub hk' hc]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ ω, |Z ω ^ k - clipF M (Z ω) ^ k| ∂m ≤ ∫ ω, 2 * Z ω ^ 4 / M ^ (4 - k) ∂m :=
        integral_mono hdiff.abs ((h4.const_mul 2).div_const _)
          fun ω => abs_pow_sub_clip_le hM hk (Z ω)
    _ = _ := by rw [integral_div, integral_const_mul]

/-- **Moments converge** under convergence in law and a uniform fourth moment bound. -/
theorem tendsto_integral_pow_of_law (hYm : ∀ N, AEStronglyMeasurable (Y N) (P N))
    (hlaw : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun N => ∫ ω, g (Y N ω) ∂P N) atTop (𝓝 (∫ x, g x ∂ν)))
    {B : ℝ} (hB : ∀ᶠ N in atTop, Integrable (fun ω => Y N ω ^ 4) (P N) ∧
      ∫ ω, Y N ω ^ 4 ∂P N ≤ B) {k : ℕ} (hk : k ≤ 3) :
    Integrable (fun x : ℝ => x ^ k) ν ∧
      Tendsto (fun N => ∫ ω, Y N ω ^ k ∂P N) atTop (𝓝 (∫ x, x ^ k ∂ν)) := by
  obtain ⟨N0, hN0⟩ := hB.exists_forall_of_atTop
  have hB0 : 0 ≤ B := (integral_nonneg fun _ => by positivity).trans (hN0 N0 le_rfl).2
  -- the fourth moment of `ν`
  have h4ν : Integrable (fun x : ℝ => x ^ 4) ν := by
    have hm : ∀ m : ℕ, ∫ x, clipF (m + 1) x ^ 4 ∂ν ≤ B := fun m => by
      have hl := hlaw (clipPow (m + 1) (by positivity) 4)
      simp only [clipPow_apply] at hl
      refine le_of_tendsto hl ?_
      filter_upwards [hB] with N ⟨hi, hb⟩
      refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity) hi
        (Eventually.of_forall fun ω => ?_)) hb
      show clipF (m + 1) (Y N ω) ^ 4 ≤ Y N ω ^ 4
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul]
      exact pow_le_pow_left₀ (sq_nonneg _) (by
        rw [← sq_abs, ← sq_abs (Y N ω)]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_clipF_le_abs (by positivity)) 2) 2
    refine ⟨(continuous_pow 4).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => by positivity)]
    have hconv : Tendsto (fun m : ℕ => ∫⁻ x, ENNReal.ofReal (clipF (m + 1) x ^ 4) ∂ν) atTop
        (𝓝 (∫⁻ x, ENNReal.ofReal (x ^ 4) ∂ν)) := by
      refine lintegral_tendsto_of_tendsto_of_monotone (fun m => ?_) ?_ ?_
      · exact (ENNReal.measurable_ofReal.comp ((continuous_clipF _).pow 4).measurable).aemeasurable
      · refine Eventually.of_forall fun x m m' hmm => ENNReal.ofReal_le_ofReal ?_
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul]
        refine pow_le_pow_left₀ (sq_nonneg _) ?_ 2
        rw [← sq_abs, ← sq_abs (clipF _ x)]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        rw [abs_clipF (by positivity), abs_clipF (by positivity)]
        have : (m : ℝ) ≤ m' := by exact_mod_cast hmm
        exact min_le_min_left _ (by linarith)
      · refine Eventually.of_forall fun x => ?_
        refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ⌈|x|⌉₊] with m hm
        rw [clipF_eq (by
          have := Nat.le_ceil |x|
          have h2 : (⌈|x|⌉₊ : ℝ) ≤ m := by exact_mod_cast hm
          linarith)]
    refine lt_of_le_of_lt (le_of_tendsto' hconv (b := ENNReal.ofReal B) fun m => ?_)
      ENNReal.ofReal_lt_top
    rw [← ofReal_integral_eq_lintegral_ofReal _ (Eventually.of_forall fun _ => by positivity)]
    · exact ENNReal.ofReal_le_ofReal (hm m)
    · exact Integrable.of_bound (((continuous_clipF _).pow 4).aestronglyMeasurable) (((m : ℝ) + 1) ^ 4)
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_clipF_le (by positivity) x) 4)
  have hidν : AEStronglyMeasurable (fun x : ℝ => x) ν := aestronglyMeasurable_id
  obtain ⟨hkν, -⟩ := abs_integral_pow_sub_clip_le hidν h4ν one_pos (by omega : k ≤ 4)
  refine ⟨hkν, ?_⟩
  set Bν := ∫ x, x ^ 4 ∂ν
  have hBν0 : 0 ≤ Bν := integral_nonneg fun _ => by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M : ℝ := 1 + 6 * (B + Bν) / ε
  have hM1 : 1 ≤ M := by
    have : 0 ≤ 6 * (B + Bν) / ε := by positivity
    simp only [M]; linarith
  have hM0 : 0 < M := by linarith
  have hMk : M ≤ M ^ (4 - k) := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ (4 - k) := pow_le_pow_right₀ hM1 (by omega)
  have hsmall : ∀ b : ℝ, 0 ≤ b → b ≤ B + Bν → 2 * b / M ^ (4 - k) < ε / 3 + 0 := by
    intro b hb0 hb
    rw [add_zero, div_lt_iff₀ (by positivity)]
    have hεM : ε / 3 * M = ε / 3 + 2 * (B + Bν) := by
      simp only [M]; field_simp; ring
    have : ε / 3 * M ≤ ε / 3 * M ^ (4 - k) := mul_le_mul_of_nonneg_left hMk (by positivity)
    linarith
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp (hlaw (clipPow M hM0.le k)) (ε / 3) (by linarith)
  refine ⟨max N0 N1, fun N hN => ?_⟩
  have hNb := hN0 N (le_of_max_le_left hN)
  have hc := hN1 N (le_of_max_le_right hN)
  simp only [clipPow_apply, Real.dist_eq] at hc
  obtain ⟨-, e1⟩ := abs_integral_pow_sub_clip_le (hYm N) hNb.1 hM0 (by omega : k ≤ 4)
  obtain ⟨-, e2⟩ := abs_integral_pow_sub_clip_le hidν h4ν hM0 (by omega : k ≤ 4)
  have b1 := hsmall _ (integral_nonneg fun _ => by positivity) (hNb.2.trans (by linarith))
  have b2 := hsmall Bν hBν0 (by linarith)
  rw [Real.dist_eq]
  calc |∫ ω, Y N ω ^ k ∂P N - ∫ x, x ^ k ∂ν| ≤
      |∫ ω, Y N ω ^ k ∂P N - ∫ ω, clipF M (Y N ω) ^ k ∂P N| +
        |∫ ω, clipF M (Y N ω) ^ k ∂P N - ∫ x, clipF M x ^ k ∂ν| +
        |∫ x, clipF M x ^ k ∂ν - ∫ x, x ^ k ∂ν| := by
        refine (abs_sub_le _ (∫ x, clipF M x ^ k ∂ν) _).trans ?_
        exact add_le_add (abs_sub_le _ (∫ ω, clipF M (Y N ω) ^ k ∂P N) _) le_rfl
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [abs_sub_comm (∫ x, clipF M x ^ k ∂ν)]
        have := lt_of_le_of_lt e1 b1
        have := lt_of_le_of_lt e2 b2
        linarith
    _ = ε := by ring

end law

end SharpLSI
