import SharpSymmetricLSI.Paper.AppAReg1

/-!
# `L²_t H¹_x` regularity of linear mild solutions (2)

`∫_{(0,T]} ∑ₙ λₙ |ρ̂_u(n)|² du < ∞`; hence for a.e. `u`, `ρ_u ∈ H¹` with
`∫ |∇ρ_u|² = ∑ₙ λₙ |ρ̂_u(n)|²` (`LinMild.ae_isWeakGrad`).
-/

open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped Real ENNReal ComplexConjugate

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A real function in `L²` with `∑ λₙ |f̂(n)|² < ∞` has an `L²` weak gradient with coefficients
`2πi nⱼ f̂(n)` and `∑ⱼ ∫ gⱼ² = ∑ λₙ |f̂(n)|²`. -/
theorem exists_isWeakGrad_of_summable {f : UnitAddTorus ι → ℝ} (hf : MemLp f 2 volume)
    (hs : Summable fun n => lamN n * ‖cf f n‖ ^ 2) :
    ∃ g : UnitAddTorus ι → ι → ℝ, IsWeakGrad f g ∧ (∀ j, MemLp (fun y => g y j) 2 volume) ∧
      (∀ j n, cf (fun y => g y j) n = 2 * π * I * n j * cf f n) ∧
      ∑ j, ∫ y, g y j ^ 2 = ∑' n, lamN n * ‖cf f n‖ ^ 2 := by
  have hnorm : ∀ j n, ‖(2 * π * I * n j : ℂ) * cf f n‖ ^ 2 = 4 * π ^ 2 * ((n j : ℝ)) ^ 2 * ‖cf f n‖ ^ 2 :=
    fun j n => by
      rw [norm_mul, mul_pow]
      have := sum_norm_two_pi_sq (fun i => if i = j then n j else 0)
      congr 1
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_two,
        show ((n j : ℤ) : ℂ) = (((n j : ℤ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [mul_pow, mul_pow, mul_pow, sq_abs]; ring
  have hle : ∀ j n, 4 * π ^ 2 * ((n j : ℝ)) ^ 2 * ‖cf f n‖ ^ 2 ≤ lamN n * ‖cf f n‖ ^ 2 :=
    fun j n => by
      unfold lamN
      gcongr
      exact Finset.single_le_sum (f := fun i => ((n i : ℝ)) ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ j)
  have hsj : ∀ j, Summable fun n => ‖(2 * π * I * n j : ℂ) * cf f n‖ ^ 2 := fun j =>
    hs.of_nonneg_of_le (fun n => sq_nonneg _) fun n => by rw [hnorm]; exact hle j n
  have hconj : ∀ j n, (2 * π * I * ((-n) j : ℤ) : ℂ) * cf f (-n) =
      conj ((2 * π * I * n j : ℂ) * cf f n) := fun j n => by
    rw [cf_neg, map_mul, map_mul, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal,
      map_ofNat, map_intCast]
    simp only [Pi.neg_apply, Int.cast_neg]; ring
  choose g hg2 hgc using fun j => exists_of_cf (hsj j) (hconj j)
  refine ⟨fun y j => g j y, isWeakGrad_of_cf hf hg2 fun j k => hgc j k, hg2, fun j n => hgc j n, ?_⟩
  have hP : ∀ j, ∫ y, g j y ^ 2 = ∑' n, 4 * π ^ 2 * ((n j : ℝ)) ^ 2 * ‖cf f n‖ ^ 2 := fun j => by
    rw [← (hasSum_sq_mFourierCoeff_real (hg2 j)).tsum_eq]
    congr 1; funext n
    have := hgc j n
    simp only [cf] at this
    rw [this, ← hnorm]
  simp_rw [hP]
  rw [← Summable.tsum_finsetSum fun j _ => (hsj j).congr fun n => hnorm j n]
  congr 1; funext n
  rw [← Finset.sum_mul, lamN, Finset.mul_sum]

namespace LinMild

variable {ρ₀ : UnitAddTorus ι → ℝ} {ρ : ℝ → UnitAddTorus ι → ℝ}
  {N : ℝ → UnitAddTorus ι → ι → ℝ} {A : ℝ} (h : LinMild ρ₀ ρ N A)
include h

/-- The Dirichlet energy, in Fourier form. -/
noncomputable def dirE (ρ : ℝ → UnitAddTorus ι → ℝ) (u : ℝ) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (lamN n * ‖cf (ρ u) n‖ ^ 2)

omit h in
theorem measurable_dirE (h : LinMild ρ₀ ρ N A) : Measurable (dirE ρ) :=
  Measurable.ennreal_tsum fun n => ENNReal.measurable_ofReal.comp
    (measurable_const.mul ((h.measurable_cf_section n).norm.pow_const 2))

/-- **`L²_t H¹_x`.** -/
theorem lintegral_dirE_le {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K)
    (hT : 0 ≤ T) :
    ∫⁻ u in Ioc 0 T, dirE ρ u ≤ ∑' n, ENNReal.ofReal (‖cf ρ₀ n‖ ^ 2 + 2 * modeW N T n) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) T)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  unfold dirE
  have hm : ∀ n, AEMeasurable (fun u => ENNReal.ofReal (lamN n * ‖cf (ρ u) n‖ ^ 2))
      (volume.restrict (Ioc 0 T)) := fun n => (ENNReal.measurable_ofReal.comp
    (measurable_const.mul ((h.measurable_cf_section n).norm.pow_const 2))).aemeasurable
  rw [lintegral_tsum hm]
  refine ENNReal.tsum_le_tsum fun n => ?_
  have hi : Integrable (fun u => lamN n * ‖cf (ρ u) n‖ ^ 2) (volume.restrict (Ioc 0 T)) :=
    ((integrable_const (K ^ 2)).mono' ((h.measurable_cf_section n).norm.pow_const 2).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (h.norm_cf_le (h.measurable_section u)
          (hK u ⟨hu.1.le, hu.2⟩) n) 2))).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun u =>
    mul_nonneg (lamN_nonneg n) (sq_nonneg _)), integral_const_mul]
  exact ENNReal.ofReal_le_ofReal (h.lam_integral_norm_cf_sq_le hK0 hK hT n)

theorem lintegral_dirE_lt_top {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K)
    (hT : 0 ≤ T) : ∫⁻ u in Ioc 0 T, dirE ρ u < ⊤ := by
  refine (h.lintegral_dirE_le hK0 hK hT).trans_lt ?_
  have hc := (hasSum_sq_mFourierCoeff_real (h.memLp_two_section hK ⟨le_rfl, hT⟩)).summable
  rw [h.init] at hc
  have hs : Summable fun n => ‖cf ρ₀ n‖ ^ 2 + 2 * modeW N T n :=
    hc.add ((h.summable_modeW hK0 hK).mul_left 2)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by
    have : 0 ≤ modeW N T n := setIntegral_nonneg measurableSet_Ioc fun v _ =>
      Finset.sum_nonneg fun k _ => sq_nonneg _
    positivity) hs]
  exact ENNReal.ofReal_lt_top

/-- **For a.e. `u`, `ρ_u ∈ H¹`.** -/
theorem ae_isWeakGrad {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K)
    (hT : 0 ≤ T) :
    ∀ᵐ u ∂(volume.restrict (Ioc 0 T)), ∃ g : UnitAddTorus ι → ι → ℝ, IsWeakGrad (ρ u) g ∧
      (∀ j, MemLp (fun y => g y j) 2 volume) ∧
      (∀ j n, cf (fun y => g y j) n = 2 * π * I * n j * cf (ρ u) n) ∧
      ENNReal.ofReal (∑ j, ∫ y, g y j ^ 2) = dirE ρ u := by
  have hfin := ae_lt_top' (h.measurable_dirE.aemeasurable) (h.lintegral_dirE_lt_top hK0 hK hT).ne
  filter_upwards [hfin, ae_restrict_mem measurableSet_Ioc] with u hu hmem
  have hs : Summable fun n => lamN n * ‖cf (ρ u) n‖ ^ 2 := by
    have := ENNReal.summable_toReal hu.ne
    refine this.congr fun n => ?_
    rw [ENNReal.toReal_ofReal (mul_nonneg (lamN_nonneg n) (sq_nonneg _))]
  obtain ⟨g, hg, hg2, hgc, hgE⟩ :=
    exists_isWeakGrad_of_summable (h.memLp_two_section hK ⟨hmem.1.le, hmem.2⟩) hs
  refine ⟨g, hg, hg2, hgc, ?_⟩
  rw [hgE, dirE, ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (lamN_nonneg n) (sq_nonneg _)) hs]

end LinMild

end SharpLSI
