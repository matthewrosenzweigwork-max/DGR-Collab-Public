import SharpSymmetricLSI.Paper.AppAFourier2
import SharpSymmetricLSI.Paper.AppAPos2

/-!
# Positivity (3): linear mild solutions in Fourier modes

`LinMild ρ₀ ρ N A`: `ρ_t = e^{tΔ}ρ₀ + ∫_{(0,t]} ∇·e^{(t-u)Δ} N_u du` for `t > 0`, `ρ_0 = ρ₀`,
jointly measurable, locally bounded, `|N_u| ≤ A|ρ_u|`. Then each Fourier coefficient
`a_n(t) = ρ̂_t(n)` satisfies `a_n(t) = e^{-λ_n t} ρ̂₀(n) + ∫_{(0,t]} e^{-λ_n(t-u)} b_n(u) du` with
`b_n(u) = ∑ₖ 2πi nₖ N̂_{u,k}(n)` and `λ_n = 4π²|n|²` (`cf_linMild`).
-/

open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped Real ENNReal

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A linear mild solution with flux bounded by the density. -/
structure LinMild (ρ₀ : UnitAddTorus ι → ℝ) (ρ : ℝ → UnitAddTorus ι → ℝ)
    (N : ℝ → UnitAddTorus ι → ι → ℝ) (A : ℝ) : Prop where
  meas : Measurable (Function.uncurry ρ)
  measN : ∀ k, Measurable fun p : ℝ × UnitAddTorus ι => N p.1 p.2 k
  meas0 : Measurable ρ₀
  init : ρ 0 = ρ₀
  bdd : ∀ T, ∃ K, 0 ≤ K ∧ ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K
  A_nonneg : 0 ≤ A
  flux : ∀ u, 0 ≤ u → ∀ y k, |N u y k| ≤ A * |ρ u y|
  mild : ∀ t, 0 < t → ∀ x, ρ t x = heatT t ρ₀ x + duhamel N t x

/-- `λ_n = 4π²|n|²`. -/
noncomputable def lamN (n : ι → ℤ) : ℝ := 4 * π ^ 2 * ∑ i, ((n i : ℝ)) ^ 2

theorem lamN_nonneg (n : ι → ℤ) : 0 ≤ lamN n := by unfold lamN; positivity

theorem heatMult_eq_exp (t : ℝ) (n : ι → ℤ) : heatMult t n = Real.exp (-lamN n * t) := by
  unfold heatMult lamN
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- The forcing of mode `n`, truncated after time `T`. -/
noncomputable def modeB (N : ℝ → UnitAddTorus ι → ι → ℝ) (T : ℝ) (n : ι → ℤ) (u : ℝ) : ℂ :=
  if u ∈ Icc 0 T then ∑ k, 2 * π * I * n k * cf (fun z => N u z k) n else 0

theorem cf_add {f g : UnitAddTorus ι → ℝ} (hf : Integrable f) (hg : Integrable g) (n : ι → ℤ) :
    cf (fun x => f x + g x) n = cf f n + cf g n := by
  have := cf_sum (Finset.univ : Finset (Fin 2)) (g := ![f, g]) (fun k _ => by
    fin_cases k
    · exact hf
    · exact hg) n
  simpa [Fin.sum_univ_two] using this

theorem appA_integrable_of_abs_le' {f : UnitAddTorus ι → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ x, |f x| ≤ C) : Integrable f :=
  (MemLp.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hb x)).integrable le_top

namespace LinMild

variable {ρ₀ : UnitAddTorus ι → ℝ} {ρ : ℝ → UnitAddTorus ι → ℝ}
  {N : ℝ → UnitAddTorus ι → ι → ℝ} {A : ℝ} (h : LinMild ρ₀ ρ N A)
include h

theorem measurable_section (u : ℝ) : Measurable (ρ u) := h.meas.comp measurable_prodMk_left

theorem measurable_sectionN (u : ℝ) (k : ι) : Measurable fun z => N u z k :=
  (h.measN k).comp measurable_prodMk_left

theorem abs_N_le {T K : ℝ} (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K) {u : ℝ} (hu : u ∈ Icc 0 T)
    (y : UnitAddTorus ι) (k : ι) : |N u y k| ≤ A * K :=
  (h.flux u hu.1 y k).trans (mul_le_mul_of_nonneg_left (hK u hu y) h.A_nonneg)

theorem measurable_cfN (n : ι → ℤ) (k : ι) : Measurable fun u => cf (fun z => N u z k) n := by
  simp only [cf]
  simp_rw [mFourierCoeff_eq_integral]
  have hm : StronglyMeasurable (fun p : ℝ × UnitAddTorus ι => mFourier (-n) p.2 • ((N p.1 p.2 k : ℝ) : ℂ)) :=
    (((mFourier (-n)).continuous.measurable.comp measurable_snd).smul
      (Complex.measurable_ofReal.comp (h.measN k))).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

theorem measurable_modeB (T : ℝ) (n : ι → ℤ) : Measurable (modeB N T n) := by
  unfold modeB
  refine Measurable.ite measurableSet_Icc ?_ measurable_const
  exact Finset.measurable_sum _ fun k _ => measurable_const.mul (h.measurable_cfN n k)

theorem norm_cf_le {f : UnitAddTorus ι → ℝ} (hf : Measurable f) {K : ℝ} (hK : ∀ x, |f x| ≤ K)
    (n : ι → ℤ) : ‖cf f n‖ ≤ K := by
  simp only [cf]
  rw [mFourierCoeff_eq_integral]
  refine (norm_integral_le_of_norm_le_const (C := K) (Eventually.of_forall fun x => ?_)).trans
    (by simp)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_of_le_one_left (abs_nonneg _) (norm_mFourier_le _ _)).trans (hK x)

theorem norm_modeB_le {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K) (n : ι → ℤ)
    (u : ℝ) :
    ‖modeB N T n u‖ ≤ ∑ k : ι, 2 * π * |(n k : ℝ)| * (A * K) := by
  unfold modeB
  split_ifs with huT
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul]
    have h1 : ‖(2 * π * I * n k : ℂ)‖ = 2 * π * |(n k : ℝ)| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_two,
        show ((n k : ℤ) : ℂ) = (((n k : ℤ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (h.norm_cf_le (h.measurable_sectionN u k)
      (fun z => h.abs_N_le hK huT z k) n) (by positivity)
  · simp only [norm_zero]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (by positivity)
      (mul_nonneg h.A_nonneg hK0)

/-- **Fourier modes of a linear mild solution.** -/
theorem cf_eq_mode {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K) (n : ι → ℤ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    cf (ρ t) n = (Real.exp (-lamN n * t) : ℂ) * cf ρ₀ n + modeD (lamN n) (modeB N T n) t := by
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    simp [modeD, h.init]
  have hρ₀b : ∀ x, |ρ₀ x| ≤ K := fun x => by rw [← h.init]; exact hK 0 ⟨le_rfl, ht.1.trans ht.2⟩ x
  have hmild : ρ t = fun x => heatT t ρ₀ x + duhamel N t x := funext (h.mild t hpos)
  have hHm : Measurable (heatT t ρ₀) := (measurable_heatT_joint h.meas0).comp measurable_prodMk_left
  have hHb : ∀ x, |heatT t ρ₀ x| ≤ K := fun x =>
    abs_heatT_le hpos h.meas0.aestronglyMeasurable (Eventually.of_forall hρ₀b) x
  have hDm : Measurable (duhamel N t) := (measurable_duhamel h.measN).comp measurable_prodMk_left
  have hDb : ∀ x, |duhamel N t x| ≤ 2 * K := fun x => by
    have e : duhamel N t x = ρ t x - heatT t ρ₀ x := by rw [h.mild t hpos x]; ring
    rw [e]
    exact (abs_sub _ _).trans (by linarith [hK t ht x, hHb x])
  rw [hmild, cf_add (appA_integrable_of_abs_le' hHm hHb) (appA_integrable_of_abs_le' hDm hDb),
    cf_heatT hpos h.meas0 hρ₀b, heatMult_eq_exp,
    cf_duhamel h.measN hpos (mul_nonneg h.A_nonneg hK0) (fun u hu y k =>
      h.abs_N_le hK ⟨hu.1.le, hu.2.le.trans ht.2⟩ y k)]
  congr 1
  unfold modeD
  rw [integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  simp only [modeB, if_pos (show u ∈ Icc 0 T from ⟨hu.1.le, hu.2.le.trans ht.2⟩),
    heatMult_eq_exp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast; ring

end LinMild

end SharpLSI
