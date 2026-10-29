import SharpSymmetricLSI.Paper.RefSpectrum9

/-!
# R23 (6.1), part 10: one step of the `L^p` bootstrap

For `-Δe = g` (Fourier form), `|e| ≤ B` a.e., weak gradient `G`, and `N = 2^{m+1}`:
`∫|Gₖ|^{2N} ≤ ((2N-1)BA)^N ∫|g|^N` (`grad_step`). Proof: Gagliardo–Nirenberg and the
second-derivative bound for `e_t = e^{tΔ}e`, `∂ₖe_t = e^{tΔ}Gₖ`, and Fatou as `t ↓ 0`.
-/

open MeasureTheory Filter Topology Complex
open scoped ENNReal Real ContDiff NNReal
open UnitAddTorus

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem enorm_rpow_eq_ofReal (x : ℝ) {P : ℝ} (hP : 0 ≤ P) :
    ‖x‖ₑ ^ P = ENNReal.ofReal (|x| ^ P) := by
  rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hP]

theorem lintegral_enorm_pow_eq_of_continuous {f : UnitAddTorus ι → ℝ} (hf : Continuous f) (N : ℕ) :
    ∫⁻ x, ‖f x‖ₑ ^ (N : ℝ) = ENNReal.ofReal (∫ x, |f x| ^ N) := by
  rw [ofReal_integral_eq_lintegral_ofReal (f := fun x => |f x| ^ N)
    (by exact integrable_of_continuous_torus (hf.abs.pow N))
    (Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [enorm_rpow_eq_ofReal _ (Nat.cast_nonneg N), Real.rpow_natCast]

/-- **One bootstrap step.** -/
theorem grad_step (m : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ (e g : UnitAddTorus ι → ℝ)
    (G : UnitAddTorus ι → ι → ℝ), MemLp e 2 volume → MemLp g 2 volume → IsWeakGrad e G →
    (∀ k, MemLp (fun y => G y k) 2 volume) →
    (∀ k, mFourierCoeff (fun y => (g y : ℂ)) k =
      4 * π ^ 2 * (∑ j, ((k j : ℂ)) ^ 2) * mFourierCoeff (fun y => (e y : ℂ)) k) →
    ∀ B : ℝ, (∀ᵐ y ∂volume, |e y| ≤ B) → ∀ k,
      ∫⁻ y, ‖G y k‖ₑ ^ ((2 : ℝ) ^ (m + 2)) ≤
        ENNReal.ofReal (((2 * 2 ^ (m + 1) - 1) * B) ^ (2 ^ (m + 1)) * A ^ (2 ^ (m + 1))) *
          ∫⁻ y, ‖g y‖ₑ ^ ((2 : ℝ) ^ (m + 1)) := by
  obtain ⟨A, hA0, hA⟩ := heat_d2_bound (ι := ι) m
  refine ⟨A, hA0, fun e g G he hg hw hG hcf B hB k => ?_⟩
  set N : ℕ := 2 ^ (m + 1)
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hB0 : 0 ≤ B := by
    obtain ⟨y, hy⟩ := hB.exists
    exact (abs_nonneg _).trans hy
  have hNr : ((2 : ℝ) ^ (m + 1)) = (N : ℝ) := by simp [N]
  have h2Nr : ((2 : ℝ) ^ (m + 2)) = ((2 * N : ℕ) : ℝ) := by simp [N, pow_succ]; ring
  have hGi : ∀ k, Integrable (fun y => G y k) := fun k => (hG k).integrable one_le_two
  -- the smoothed bound, uniformly in `t`
  have hsm : ∀ t, 0 < t → ∫⁻ y, ‖heatT t (fun y => G y k) y‖ₑ ^ ((2 * N : ℕ) : ℝ) ≤
      ENNReal.ofReal (((2 * N - 1) * B) ^ N * A ^ N) * ∫⁻ y, ‖g y‖ₑ ^ (N : ℝ) := by
    intro t ht
    have h2 := heat_smooth2 he ht
    have hBt : ∀ y, |heatT t e y| ≤ B := fun y =>
      abs_heatT_le ht (he.integrable one_le_two).aestronglyMeasurable hB y
    have hgn := gn_torus h2 hBt k hN1
    have hVc : Continuous (dpart (heatT t e) k) :=
      continuous_of_liftT' (contDiff_dpart (n := 1) h2 k).continuous
    have hWc : Continuous (dpart (dpart (heatT t e) k) k) :=
      continuous_of_liftT' (contDiff_dpart (n := 0) (contDiff_dpart (n := 1) h2 k) k).continuous
    have hgrad := heat_grad he ht hw hGi k
    have hd2 := hA e g he hg hcf t ht k k
    rw [hNr] at hd2
    calc ∫⁻ y, ‖heatT t (fun y => G y k) y‖ₑ ^ ((2 * N : ℕ) : ℝ)
        = ∫⁻ y, ‖dpart (heatT t e) k y‖ₑ ^ ((2 * N : ℕ) : ℝ) :=
          lintegral_congr_ae (hgrad.mono fun y hy => by simp only [hy])
      _ = ENNReal.ofReal (∫ y, |dpart (heatT t e) k y| ^ (2 * N)) :=
          lintegral_enorm_pow_eq_of_continuous hVc _
      _ ≤ ENNReal.ofReal (((2 * N - 1) * B) ^ N * ∫ y, |dpart (dpart (heatT t e) k) k y| ^ N) :=
          ENNReal.ofReal_le_ofReal hgn
      _ = ENNReal.ofReal (((2 * N - 1) * B) ^ N) *
            ∫⁻ y, ‖dpart (dpart (heatT t e) k) k y‖ₑ ^ (N : ℝ) := by
          have hc : 0 ≤ ((2 * (N : ℝ) - 1) * B) ^ N := by
            have : (1 : ℝ) ≤ 2 * N - 1 := by
              have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
              linarith
            positivity
          rw [ENNReal.ofReal_mul hc, lintegral_enorm_pow_eq_of_continuous hWc]
      _ ≤ ENNReal.ofReal (((2 * N - 1) * B) ^ N) *
            (ENNReal.ofReal A ^ (N : ℝ) * ∫⁻ y, ‖g y‖ₑ ^ (N : ℝ)) := mul_le_mul' le_rfl hd2
      _ = ENNReal.ofReal (((2 * N - 1) * B) ^ N * A ^ N) * ∫⁻ y, ‖g y‖ₑ ^ (N : ℝ) := by
          rw [← mul_assoc, ENNReal.rpow_natCast, ← ENNReal.ofReal_pow hA0,
            ← ENNReal.ofReal_mul (by
              have : (1 : ℝ) ≤ 2 * N - 1 := by
                have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
                linarith
              positivity)]
  -- Fatou along `t = 1/(n+1)`
  set ts : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hts : ∀ n, 0 < ts n := fun n => by positivity
  have hts0 : Tendsto ts atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => hts n⟩
  have hL1 := (tendsto_heatT_L1 (hGi k)).comp hts0
  obtain ⟨ns, -, hae⟩ := exists_subseq_ae_of_tendsto_lintegral
    (fun n => (continuous_heatT (hts n) (hGi k)).aestronglyMeasurable)
    (hGi k).aestronglyMeasurable hL1
  rw [h2Nr, hNr]
  calc ∫⁻ y, ‖G y k‖ₑ ^ ((2 * N : ℕ) : ℝ)
      = ∫⁻ y, liminf (fun n => ‖heatT (ts (ns n)) (fun y => G y k) y‖ₑ ^ ((2 * N : ℕ) : ℝ))
          atTop := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with y hy
        have := ((continuous_enorm.tendsto _).comp hy).ennrpow_const ((2 * N : ℕ) : ℝ)
        exact this.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ y, ‖heatT (ts (ns n)) (fun y => G y k) y‖ₑ ^ ((2 * N : ℕ) : ℝ))
          atTop :=
        lintegral_liminf_le' fun n =>
          ((continuous_heatT (hts _) (hGi k)).enorm.measurable.pow_const _).aemeasurable
    _ ≤ ENNReal.ofReal (((2 * N - 1) * B) ^ N * A ^ N) * ∫⁻ y, ‖g y‖ₑ ^ (N : ℝ) :=
        liminf_le_of_frequently_le' (Frequently.of_forall fun n => hsm _ (hts _))

end SharpLSI
