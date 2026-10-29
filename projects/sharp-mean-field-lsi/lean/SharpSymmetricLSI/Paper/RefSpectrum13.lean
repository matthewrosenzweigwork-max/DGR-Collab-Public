import SharpSymmetricLSI.Paper.RefSpectrum12

/-!
# R23 (6.1), part 13: `W^{2,p}` for every finite `p`

For an eigenpair, the second weak derivatives `∂_l∂_k e` exist in `L²` by Fourier synthesis
(`ĝ = 4π²|κ|²ê ∈ ℓ²`), and `e^{tΔ}∂_l∂_k e = ∂_l∂_k e_t`, so Fatou and the second-derivative
bound give `∂_l∂_k e ∈ L^{2^{m+1}}` for all `m` (`w2p`).
-/

open MeasureTheory Filter Topology Complex
open scoped ENNReal Real ContDiff NNReal ComplexConjugate
open UnitAddTorus

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Fatou for `e^{tΔ}` as `t ↓ 0`. -/
theorem lintegral_le_of_heatT {f : UnitAddTorus ι → ℝ} (hf : Integrable f) {P : ℝ} (hP : 0 ≤ P)
    {M : ℝ≥0∞} (h : ∀ t, 0 < t → ∫⁻ y, ‖heatT t f y‖ₑ ^ P ≤ M) :
    ∫⁻ y, ‖f y‖ₑ ^ P ≤ M := by
  set ts : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hts : ∀ n, 0 < ts n := fun n => by positivity
  have hts0 : Tendsto ts atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => hts n⟩
  have hL1 := (tendsto_heatT_L1 hf).comp hts0
  obtain ⟨ns, -, hae⟩ := exists_subseq_ae_of_tendsto_lintegral
    (fun n => (continuous_heatT (hts n) hf).aestronglyMeasurable) hf.aestronglyMeasurable hL1
  calc ∫⁻ y, ‖f y‖ₑ ^ P
      = ∫⁻ y, liminf (fun n => ‖heatT (ts (ns n)) f y‖ₑ ^ P) atTop := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with y hy
        exact (((continuous_enorm.tendsto _).comp hy).ennrpow_const P).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ y, ‖heatT (ts (ns n)) f y‖ₑ ^ P) atTop :=
        lintegral_liminf_le' fun n => ((continuous_heatT (hts _) hf).enorm.measurable.pow_const _).aemeasurable
    _ ≤ M := liminf_le_of_frequently_le' (Frequently.of_forall fun n => h _ (hts _))

theorem memLp_of_lintegral_rpow_lt_top {f : UnitAddTorus ι → ℝ}
    (hf : AEStronglyMeasurable f volume) {P : ℝ} (hP : 0 < P)
    (h : ∫⁻ y, ‖f y‖ₑ ^ P < ⊤) : MemLp f (ENNReal.ofReal P) volume := by
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hP) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hP.le]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) h.ne

/-- `|κ_l κ_k| ≤ |κ|²`. -/
theorem abs_mul_le_sum_sq (κ : ι → ℤ) (k l : ι) :
    |(κ l : ℝ)| * |(κ k : ℝ)| ≤ ∑ i, ((κ i : ℝ)) ^ 2 := by
  have hk : ((κ k : ℝ)) ^ 2 ≤ ∑ i, ((κ i : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun i => ((κ i : ℝ)) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
  have hl : ((κ l : ℝ)) ^ 2 ≤ ∑ i, ((κ i : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun i => ((κ i : ℝ)) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ l)
  nlinarith [sq_abs ((κ k : ℝ)), sq_abs ((κ l : ℝ)), sq_nonneg (|(κ k : ℝ)| - |(κ l : ℝ)|)]

/-- The symbol `(2πiκ_l)(2πiκ_k)`. -/
noncomputable def d2c (k l : ι) (κ : ι → ℤ) : ℂ := (2 * π * I * κ l) * (2 * π * I * κ k)

theorem norm_d2c_le (k l : ι) (κ : ι → ℤ) : ‖d2c k l κ‖ ≤ 4 * π ^ 2 * ∑ i, ((κ i : ℝ)) ^ 2 := by
  have e : ‖d2c k l κ‖ = 4 * π ^ 2 * (|(κ l : ℝ)| * |(κ k : ℝ)|) := by
    simp only [d2c, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
      Complex.norm_intCast, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (abs_mul_le_sum_sq κ k l) (by positivity)

/-- **Second weak derivatives** of a solution of `-Δe = g`, `g ∈ L²`, by synthesis. -/
theorem exists_d2 {e g : UnitAddTorus ι → ℝ} (he : MemLp e 2 volume) (hg : MemLp g 2 volume)
    (hcf : ∀ κ, mFourierCoeff (fun y => (g y : ℂ)) κ =
      4 * π ^ 2 * (∑ j, ((κ j : ℂ)) ^ 2) * mFourierCoeff (fun y => (e y : ℂ)) κ) (k l : ι) :
    ∃ H : UnitAddTorus ι → ℝ, MemLp H 2 volume ∧
      ∀ κ, mFourierCoeff (fun y => (H y : ℂ)) κ = d2c k l κ * mFourierCoeff (fun y => (e y : ℂ)) κ := by
  set a := mFourierCoeff fun y => (e y : ℂ)
  have hs : Summable fun κ => ‖d2c k l κ * a κ‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun κ => by positivity) (fun κ => ?_)
      (hasSum_sq_mFourierCoeff_real hg).summable
    rw [hcf κ, norm_mul, norm_mul]
    have h1 : ‖(4 * π ^ 2 * ∑ j, ((κ j : ℂ)) ^ 2 : ℂ)‖ = 4 * π ^ 2 * ∑ i, ((κ i : ℝ)) ^ 2 := by
      have : (4 * π ^ 2 * ∑ j, ((κ j : ℂ)) ^ 2 : ℂ) = ((4 * π ^ 2 * ∑ i, ((κ i : ℝ)) ^ 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [h1]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right (norm_d2c_le k l κ) (norm_nonneg _)) 2
  have hsym : ∀ κ, d2c k l (-κ) * a (-κ) = conj (d2c k l κ * a κ) := by
    intro κ
    have := cf_neg e κ
    simp only [cf] at this
    simp only [a, this, d2c, map_mul, Complex.conj_I, Pi.neg_apply, Int.cast_neg, Complex.conj_ofReal,
      map_intCast, map_ofNat]
    ring
  obtain ⟨H, hH2, hHc⟩ := exists_of_cf hs hsym
  exact ⟨H, hH2, hHc⟩

/-- `e^{tΔ}` of a synthesized second derivative is the classical one of `e_t`. -/
theorem heatT_d2 {e H : UnitAddTorus ι → ℝ} (he : MemLp e 2 volume) (hH : MemLp H 2 volume)
    {k l : ι} (hHc : ∀ κ, mFourierCoeff (fun y => (H y : ℂ)) κ =
      d2c k l κ * mFourierCoeff (fun y => (e y : ℂ)) κ) {t : ℝ} (ht : 0 < t) :
    heatT t H =ᵐ[volume] dpart (dpart (heatT t e) k) l := by
  have h2 := heat_smooth2 he ht
  have hHi := hH.integrable one_le_two
  have hc1 : Continuous (heatT t H) := continuous_heatT ht hHi
  have hc2 : Continuous (dpart (dpart (heatT t e) k) l) :=
    continuous_of_liftT' (contDiff_dpart (n := 0) (contDiff_dpart (n := 1) h2 k) l).continuous
  refine ae_eq_of_cf_eq (memLp_of_continuous_torus hc1 _) (memLp_of_continuous_torus hc2 _)
    fun κ => ?_
  rw [mFourierCoeff_heatT ht hHi, hHc, cf_dpart (contDiff_dpart (n := 1) h2 k) l κ,
    cf_dpart (h2.of_le (by norm_num)) k κ, mFourierCoeff_heatT ht (he.integrable one_le_two), d2c]
  ring

end SharpLSI
