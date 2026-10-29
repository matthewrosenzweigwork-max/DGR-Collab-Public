import DGPS.Examples.PositiveH1.Nonlinear
import DGPS.Examples.PositiveH1.Fourier

/-!
# H1010: weak Fourier cross term

For an admissible density `σ` (including a barycenter), `P(σ)` and `Q(σ)` are finite and
`∫ σ′ (R′ * σ) dm = Q(σ)`. Proof: finite cutoff `R_M′` by Fourier computation, then the `L²` tail
estimate `‖R′ - R_M′‖₂ = B_M → 0` passes the pairing to the limit.
-/

open MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace DGPS.Examples.PositiveH1.CrossTerm

open DGPS.Examples.PositiveH1.Fourier DGPS.Examples.PositiveH1.Nonlinear

theorem mFourier_sub (k : Fin 1 → ℤ) (x y : Torus 1) :
    UnitAddTorus.mFourier k (x - y) = UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) y := by
  rw [UnitAddTorus.mFourier_neg]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Finset.univ_unique,
    Finset.prod_singleton, Pi.sub_apply]
  rw [sub_eq_add_neg]
  simp only [fourier_apply, smul_add, smul_neg, AddCircle.toCircle_add, Circle.coe_mul,
    fourier_neg']

/-- complex pairing with a mode. -/
theorem integral_mode_conv {u : Torus 1 → ℝ} (k : Fin 1 → ℤ)
    (x : Torus 1) :
    ∫ y, (u y : ℂ) * UnitAddTorus.mFourier k (x - y) ∂haar 1
      = UnitAddTorus.mFourier k x * fourierCoeff u k := by
  have hfun : ∀ y, (u y : ℂ) * UnitAddTorus.mFourier k (x - y)
      = UnitAddTorus.mFourier k x * (UnitAddTorus.mFourier (-k) y * (u y : ℂ)) := by
    intro y; rw [mFourier_sub]; ring
  simp_rw [hfun]
  rw [integral_const_mul, ← fourierCoeff_eq_integral]

theorem integral_sin_conv {u : Torus 1 → ℝ} (hu : Integrable u (haar 1)) (n : ℕ) (x : Torus 1) :
    ∫ y, u y * sinMode n (x - y) ∂haar 1
      = (UnitAddTorus.mFourier (freq n) x * fourierCoeff u (freq n)).im := by
  have hint : Integrable (fun y => (u y : ℂ) * UnitAddTorus.mFourier (freq n) (x - y)) (haar 1) := by
    refine Integrable.mono' hu.norm
      (hu.ofReal.aestronglyMeasurable.mul
        ((UnitAddTorus.mFourier (freq n)).continuous.comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun y => by simp [norm_mFourier_apply])
  rw [← integral_mode_conv (u := u) (freq n) x]
  have h := integral_im hint
  simp only [RCLike.im_to_complex] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [sinMode, Complex.im_ofReal_mul]
  rfl

theorem integral_pair_im {w : Torus 1 → ℝ} (hw : Integrable w (haar 1)) (k : Fin 1 → ℤ) (c : ℂ) :
    ∫ x, w x * (UnitAddTorus.mFourier k x * c).im ∂haar 1
      = (c * conj (fourierCoeff w k)).im := by
  have hint : Integrable (fun x => (w x : ℂ) * (UnitAddTorus.mFourier k x * c)) (haar 1) := by
    have := (integrable_mFourier_mul hw k).mul_const c
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only; ring
  have h1 : ∫ x, (w x : ℂ) * (UnitAddTorus.mFourier k x * c) ∂haar 1
      = c * conj (fourierCoeff w k) := by
    rw [← fourierCoeff_neg, fourierCoeff_eq_integral, neg_neg, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only; ring
  have h2 := integral_im hint
  simp only [RCLike.im_to_complex] at h2
  rw [h1] at h2
  rw [← h2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp

theorem fourierCoeff_densityDeriv (σ : AbsoluteDensity 1) (n : ℕ) :
    fourierCoeff (densityDeriv σ) (freq n)
      = 2 * Real.pi * Complex.I * (n : ℂ) * fourierCoeff σ.density (freq n) := by
  obtain ⟨_, _, _, hw, h5, _⟩ := admissibleRegularity σ
  have h := fourierCoeff_weakGradient hw 0 (freq n)
  have hf : (fun y => ((2 * σ.sqrt y) • weakGradient σ.sqrt σ.sqrt_mem y) 0) = densityDeriv σ :=
    funext fun y => h5 y
  rw [hf] at h
  simpa [freq] using h

theorem pair_sin (σ : AbsoluteDensity 1) (n : ℕ) :
    ∫ x, densityDeriv σ x * conv σ.density (sinMode n) x ∂haar 1
      = -(2 * Real.pi * n) * ‖fourierCoeff σ.density (freq n)‖ ^ 2 := by
  have h1 : ∀ x, conv σ.density (sinMode n) x
      = (UnitAddTorus.mFourier (freq n) x * fourierCoeff σ.density (freq n)).im :=
    fun x => integral_sin_conv σ.integrable_density n x
  simp_rw [h1]
  rw [integral_pair_im ((memLp_densityDeriv σ).integrable one_le_two), fourierCoeff_densityDeriv]
  set c := fourierCoeff σ.density (freq n)
  have e : c * conj (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * c)
      = (-(2 * Real.pi * n) : ℝ) * Complex.I * (c * conj c) := by
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast]
    push_cast; ring
  rw [e, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp [-Complex.ofReal_pow]

theorem conv_dRM {f : Torus 1 → ℝ} (hf : MemLp f 2 (haar 1)) (M : ℕ) (x : Torus 1) :
    conv f (dRM M) x = ∑ n ∈ Finset.Icc 2 M, dcoef n * conv f (sinMode n) x := by
  unfold conv
  simp_rw [dRM_eq, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => by simp only; ring)
  · intro n _
    have h2 : MemLp (fun y => dcoef n * sinMode n (x - y)) 2 (haar 1) :=
      memLp_of_cont (continuous_const.mul ((continuous_sinMode n).comp
        (continuous_const.sub continuous_id))) 2
    exact (hf.integrable_mul h2).congr (Eventually.of_forall fun y => by simp only [Pi.mul_apply])

/-- The `n`-th term of the series `Q`. -/
noncomputable def qTerm (σ : AbsoluteDensity 1) (n : ℕ) : ℝ :=
  (2 * Real.pi * n) ^ 2 * a n * ‖fourierCoeff σ.density (freq n)‖ ^ 2

theorem qTerm_nonneg (σ : AbsoluteDensity 1) (n : ℕ) : 0 ≤ qTerm σ n :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (a_nonneg n)) (sq_nonneg _)

theorem qTerm_zero_of_lt (σ : AbsoluteDensity 1) {n : ℕ} (h : n < 2) : qTerm σ n = 0 := by
  simp [qTerm, a_zero_of_lt h]

theorem dcoef_mul {n : ℕ} (hn : 2 ≤ n) (N : ℝ) :
    dcoef n * (-(2 * Real.pi * n) * N) = (2 * Real.pi * n) ^ 2 * a n * N := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have e1 : (n : ℝ) ^ (-(3 / 4 : ℝ)) * n = (n : ℝ) ^ (1 / 4 : ℝ) := by
    calc (n : ℝ) ^ (-(3 / 4 : ℝ)) * n = (n : ℝ) ^ (-(3 / 4 : ℝ)) * (n : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
      _ = (n : ℝ) ^ (-(3 / 4 : ℝ) + 1) := (Real.rpow_add hn0 _ _).symm
      _ = (n : ℝ) ^ (1 / 4 : ℝ) := by norm_num
  have e2 : (n : ℝ) ^ (-(7 / 4 : ℝ)) * (n : ℝ) ^ 2 = (n : ℝ) ^ (1 / 4 : ℝ) := by
    calc (n : ℝ) ^ (-(7 / 4 : ℝ)) * (n : ℝ) ^ 2
        = (n : ℝ) ^ (-(7 / 4 : ℝ)) * (n : ℝ) ^ (2 : ℝ) := by rw [Real.rpow_two]
      _ = (n : ℝ) ^ (-(7 / 4 : ℝ) + 2) := (Real.rpow_add hn0 _ _).symm
      _ = (n : ℝ) ^ (1 / 4 : ℝ) := by norm_num
  have h3 : a n = (n : ℝ) ^ (-(7 / 4 : ℝ)) := by simp [a, hn]
  rw [h3]
  have : dcoef n * (-(2 * Real.pi * n) * N)
      = (2 * Real.pi) ^ 2 * ((n : ℝ) ^ (-(3 / 4 : ℝ)) * n) * N := by unfold dcoef; ring
  rw [this, e1]
  have : (2 * Real.pi * n) ^ 2 * (n : ℝ) ^ (-(7 / 4 : ℝ)) * N
      = (2 * Real.pi) ^ 2 * ((n : ℝ) ^ (-(7 / 4 : ℝ)) * (n : ℝ) ^ 2) * N := by ring
  rw [this, e2]

theorem partial_eq (σ : AbsoluteDensity 1) (M : ℕ) :
    ∫ x, densityDeriv σ x * conv σ.density (dRM M) x ∂haar 1
      = ∑ n ∈ Finset.range (M + 1), qTerm σ n := by
  have hσ' : MemLp (densityDeriv σ) 2 (haar 1) := memLp_densityDeriv σ
  have hint : ∀ n ∈ Finset.Icc 2 M, Integrable
      (fun x => densityDeriv σ x * (dcoef n * conv σ.density (sinMode n) x)) (haar 1) := by
    intro n _
    have hc : Continuous (fun x => dcoef n * conv σ.density (sinMode n) x) :=
      continuous_const.mul (conv_continuous σ.integrable_density (continuous_sinMode n))
    exact hσ'.integrable_mul (memLp_of_cont hc 2)
  simp_rw [conv_dRM (memLp_density_two σ) M, Finset.mul_sum]
  rw [integral_finsetSum _ hint]
  have h1 : ∀ n ∈ Finset.Icc 2 M,
      ∫ x, densityDeriv σ x * (dcoef n * conv σ.density (sinMode n) x) ∂haar 1 = qTerm σ n := by
    intro n hn
    have e : ∀ x, densityDeriv σ x * (dcoef n * conv σ.density (sinMode n) x)
        = dcoef n * (densityDeriv σ x * conv σ.density (sinMode n) x) := fun x => by ring
    simp_rw [e]
    rw [integral_const_mul, pair_sin]
    exact dcoef_mul (Finset.mem_Icc.mp hn).1 _
  rw [Finset.sum_congr rfl h1]
  refine Finset.sum_subset ?_ fun n _ hn => qTerm_zero_of_lt σ ?_
  · intro n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
  · by_contra hc
    exact hn (Finset.mem_Icc.mpr ⟨by omega, by
      have := Finset.mem_range.mp ‹n ∈ Finset.range (M + 1)›; omega⟩)

theorem B_nonneg (M : ℕ) : 0 ≤ B M := by
  rw [B_eq]; exact Real.sqrt_nonneg _

theorem conv_sub_dRM (σ : AbsoluteDensity 1) {M : ℕ} (hM : 1 ≤ M) (x : Torus 1) :
    |conv σ.density dR x - conv σ.density (dRM M) x|
      ≤ Real.sqrt (∫ y, σ.density y ^ 2 ∂haar 1) * B M := by
  have hσ := memLp_density_two σ
  have h1 : conv σ.density dR x - conv σ.density (dRM M) x
      = conv σ.density (fun y => dR y - dRM M y) x := by
    unfold conv
    have i1 : Integrable (fun y => σ.density y * dR (x - y)) (haar 1) :=
      hσ.integrable_mul (memLp_sub_left memLp_dR x)
    have i2 : Integrable (fun y => σ.density y * dRM M (x - y)) (haar 1) :=
      hσ.integrable_mul (memLp_sub_left (memLp_dRM M) x)
    rw [← integral_sub i1 i2]
    exact integral_congr_ae (Eventually.of_forall fun y => by simp only [mul_sub])
  rw [h1]
  have hm : MemLp (fun y => dR y - dRM M y) 2 (haar 1) := memLp_dR.sub (memLp_dRM M)
  have h2 := conv_bound hσ hm x
  rw [integral_sq_dR_sub hM, Real.sqrt_sq (B_nonneg M)] at h2
  exact h2

theorem tendsto_partial (σ : AbsoluteDensity 1) :
    Tendsto (fun M : ℕ => ∫ x, densityDeriv σ x * conv σ.density (dRM M) x ∂haar 1) atTop
      (𝓝 (∫ x, densityDeriv σ x * conv dR σ.density x ∂haar 1)) := by
  have hσ' : MemLp (densityDeriv σ) 2 (haar 1) := memLp_densityDeriv σ
  have hT : Integrable (fun x => densityDeriv σ x * conv dR σ.density x) (haar 1) :=
    hσ'.integrable_mul (memLp_of_cont (continuous_driftField σ) 2)
  have hTM : ∀ M : ℕ, Integrable (fun x => densityDeriv σ x * conv σ.density (dRM M) x) (haar 1) :=
    fun M => hσ'.integrable_mul
      (memLp_of_cont (conv_continuous σ.integrable_density (continuous_dRM M)) 2)
  set K := Real.sqrt (∫ y, σ.density y ^ 2 ∂haar 1) with hK
  have hbound : ∀ M : ℕ, 1 ≤ M →
      ‖(∫ x, densityDeriv σ x * conv σ.density (dRM M) x ∂haar 1)
        - ∫ x, densityDeriv σ x * conv dR σ.density x ∂haar 1‖
        ≤ (K * ∫ x, ‖densityDeriv σ x‖ ∂haar 1) * B M := by
    intro M hM
    rw [norm_sub_rev, ← integral_sub hT (hTM M)]
    have hg : Integrable (fun x => ‖densityDeriv σ x‖ * (K * B M)) (haar 1) :=
      (hσ'.integrable one_le_two).norm.mul_const _
    refine (norm_integral_le_of_norm_le hg (Eventually.of_forall fun x => ?_)).trans ?_
    · rw [← mul_sub, norm_mul, conv_comm dR σ.density x]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact conv_sub_dRM σ hM x
    · rw [integral_mul_const]; apply le_of_eq; ring
  have hlim : Tendsto (fun M : ℕ => (K * ∫ x, ‖densityDeriv σ x‖ ∂haar 1) * B M) atTop (𝓝 0) := by
    simpa using tendsto_B.const_mul (K * ∫ x, ‖densityDeriv σ x‖ ∂haar 1)
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun M => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with M hM using hbound M hM

/-- `P(σ) = Σ a_n |σ̂(n)|²`, with `σ̂(n)` the `n`-th Fourier coefficient of the density of `σ`. -/
noncomputable def P (σ : AbsoluteDensity 1) : ℝ :=
  ∑' n : ℕ, a n * ‖fourierCoeff σ.density (freq n)‖ ^ 2

/-- `Q(σ) = Σ (2πn)² a_n |σ̂(n)|²`. -/
noncomputable def Q (σ : AbsoluteDensity 1) : ℝ :=
  ∑' n : ℕ, (2 * Real.pi * n) ^ 2 * a n * ‖fourierCoeff σ.density (freq n)‖ ^ 2

theorem hasSum_qTerm (σ : AbsoluteDensity 1) :
    HasSum (qTerm σ) (∫ x, densityDeriv σ x * conv dR σ.density x ∂haar 1) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (qTerm_nonneg σ)]
  refine (tendsto_add_atTop_iff_nat 1).mp ?_
  simpa only [partial_eq] using tendsto_partial σ

theorem summable_P_term (σ : AbsoluteDensity 1) :
    Summable fun n : ℕ => a n * ‖fourierCoeff σ.density (freq n)‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (a_nonneg n) (sq_nonneg _))
    (fun n => ?_) (hasSum_qTerm σ).summable
  by_cases hn : n < 2
  · rw [qTerm_zero_of_lt σ hn]; simp [a_zero_of_lt hn]
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast (not_lt.mp hn)
    have hp := Real.pi_gt_three
    have h3 : (1 : ℝ) ≤ 2 * Real.pi * n := by nlinarith
    have h1 : (1 : ℝ) ≤ (2 * Real.pi * n) ^ 2 := by nlinarith
    unfold qTerm
    have := mul_nonneg (a_nonneg n) (sq_nonneg ‖fourierCoeff σ.density (freq n)‖)
    nlinarith

/-- **H1010.** For every admissible density `σ`, the series `P(σ) = Σ a_n |σ̂(n)|²` and
`Q(σ) = Σ (2πn)² a_n |σ̂(n)|²` converge, and `∫ σ′ (R′ * σ) dm = Q(σ)`. -/
theorem weak_fourier_cross_term (σ : AbsoluteDensity 1) :
    Summable (fun n : ℕ => a n * ‖fourierCoeff σ.density (freq n)‖ ^ 2) ∧
    Summable (fun n : ℕ => (2 * Real.pi * n) ^ 2 * a n * ‖fourierCoeff σ.density (freq n)‖ ^ 2) ∧
    ∫ x, densityDeriv σ x * conv dR σ.density x ∂haar 1 = Q σ :=
  ⟨summable_P_term σ, (hasSum_qTerm σ).summable, (hasSum_qTerm σ).tsum_eq.symm⟩

/-- The same for the barycenter of a finite species family. -/
theorem weak_fourier_cross_term_barycenter (F : SpeciesFamily 1) :
    Summable (fun n : ℕ => a n * ‖fourierCoeff (barycenter F).density (freq n)‖ ^ 2) ∧
    Summable (fun n : ℕ => (2 * Real.pi * n) ^ 2 * a n *
      ‖fourierCoeff (barycenter F).density (freq n)‖ ^ 2) ∧
    ∫ x, densityDeriv (barycenter F) x * conv dR (barycenter F).density x ∂haar 1
      = Q (barycenter F) :=
  weak_fourier_cross_term (barycenter F)

end DGPS.Examples.PositiveH1.CrossTerm
