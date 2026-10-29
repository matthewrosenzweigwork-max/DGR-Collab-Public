import SharpSymmetricLSI.Infra.CZTorus6
import SharpSymmetricLSI.Infra.HeatTorus8

/-!
# R23 (6.1), part 1: heat-semigroup facts used for the regularity bootstrap

* `summable_prod_pi`: products `∏ᵢ fᵢ(kᵢ)` of summable nonnegative families are summable on `ℤ^ι`;
  hence `∑ₖ |k|² e^{-4π²|k|²t} < ∞` (`summable_sq_heatMult`).
* `mFourierCoeff_heatT`: `(e^{tΔ}f)^(k) = e^{-4π²|k|²t} f̂(k)`.
* `lintegral_heatT_rpow_le`: `e^{tΔ}` is a contraction of `L^P`, `P > 1` (Jensen/Hölder against the
  probability density `P_t`).
-/

open MeasureTheory Filter Topology Complex
open scoped ENNReal Real
open UnitAddTorus

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem summable_prod_pi (f : ι → ℤ → ℝ) (hf0 : ∀ i n, 0 ≤ f i n) (hf : ∀ i, Summable (f i)) :
    Summable fun k : ι → ℤ => ∏ i, f i (k i) := by
  refine summable_of_sum_le (c := ∏ i, ∑' n, f i n)
    (fun k => Finset.prod_nonneg fun i _ => hf0 i _) fun u => ?_
  set T : ι → Finset ℤ := fun i => u.image (fun k => k i)
  have hsub : u ⊆ Fintype.piFinset T := fun k hk =>
    Fintype.mem_piFinset.mpr fun i => Finset.mem_image_of_mem _ hk
  calc ∑ k ∈ u, ∏ i, f i (k i) ≤ ∑ k ∈ Fintype.piFinset T, ∏ i, f i (k i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun k _ _ => Finset.prod_nonneg fun i _ => hf0 i _)
    _ = ∏ i, ∑ n ∈ T i, f i n := (Finset.prod_univ_sum T fun i n => f i n).symm
    _ ≤ ∏ i, ∑' n, f i n := by
        apply Finset.prod_le_prod₀
        · intro i _; exact Finset.sum_nonneg fun n _ => hf0 i n
        · intro i _; exact (hf i).sum_le_tsum _ (fun n _ => hf0 i n)

theorem summable_sq_heatMult {t : ℝ} (ht : 0 < t) :
    Summable fun k : ι → ℤ => (∑ i, ((k i : ℝ)) ^ 2) * heatMult t k := by
  have e : ∀ k : ι → ℤ, (∑ i, ((k i : ℝ)) ^ 2) * heatMult t k =
      ∑ j, ∏ i, (if i = j then ((k i : ℝ)) ^ 2 else 1) * Real.exp (-(4 * π ^ 2) * (k i : ℝ) ^ 2 * t) := by
    intro k
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ j, heatMult]
    simp
  rw [show (fun k : ι → ℤ => (∑ i, ((k i : ℝ)) ^ 2) * heatMult t k) = _ from funext e]
  refine summable_sum fun j _ => summable_prod_pi
    (fun i (n : ℤ) => (if i = j then ((n : ℝ)) ^ 2 else 1) * Real.exp (-(4 * π ^ 2) * (n : ℝ) ^ 2 * t))
    (fun i n => mul_nonneg (by split_ifs <;> positivity) (Real.exp_pos _).le) fun i => ?_
  have h0 : ∀ n : ℤ, Real.exp (-(4 * π ^ 2) * (n : ℝ) ^ 2 * t) = heatBound 1 0 t n := by
    intro n; simp only [heatBound]; congr 1; ring
  have h2 : ∀ n : ℤ, ((n : ℝ)) ^ 2 * Real.exp (-(4 * π ^ 2) * (n : ℝ) ^ 2 * t) =
      heatBound 1 2 t n / (2 * π) ^ 2 := by
    intro n; simp only [heatBound]
    rw [Int.cast_abs, sq_abs]
    field_simp
    congr 1; ring
  by_cases hij : i = j
  · simp only [hij, if_true]
    simp_rw [h2]
    exact (summable_heatBound 1 2 ht).div_const _
  · simp only [hij, if_false, one_mul]
    simp_rw [h0]
    exact summable_heatBound 1 0 ht

theorem mFourier_add_pt (k : ι → ℤ) (a b : UnitAddTorus ι) :
    mFourier k (a + b) = mFourier k a * mFourier k b := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- **Fourier coefficients of `e^{tΔ}f`.** -/
theorem mFourierCoeff_heatT {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ} (hf : Integrable f)
    (k : ι → ℤ) :
    mFourierCoeff (fun y => (heatT t f y : ℂ)) k =
      heatMult t k * mFourierCoeff (fun y => (f y : ℂ)) k := by
  have hint := heatP_measurePreserving_integrable ht hf
  have hint' : Integrable (fun p : UnitAddTorus ι × UnitAddTorus ι =>
      mFourier (-k) p.1 * (((heatP t p.2 * f (p.1 - p.2)) : ℝ) : ℂ)) (volume.prod volume) :=
    (hint.ofReal (𝕜 := ℂ)).bdd_mul (c := 1)
      ((map_continuous (mFourier (-k))).comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p => norm_mFourier_le _ _)
  rw [mFourierCoeff_eq_integral]
  have e1 : ∀ x, mFourier (-k) x • (heatT t f x : ℂ) =
      ∫ z, mFourier (-k) x * (((heatP t z * f (x - z)) : ℝ) : ℂ) := by
    intro x
    rw [heatT_eq ht hf.aestronglyMeasurable, smul_eq_mul, ← integral_complex_ofReal,
      ← integral_const_mul]
  simp_rw [e1]
  rw [integral_integral_swap hint']
  have e2 : ∀ z, ∫ x, mFourier (-k) x * (((heatP t z * f (x - z)) : ℝ) : ℂ) =
      ((heatP t z : ℂ) * mFourier (-k) z) * mFourierCoeff (fun y => (f y : ℂ)) k := by
    intro z
    have e3 : ∀ x, mFourier (-k) x * (((heatP t z * f (x - z)) : ℝ) : ℂ) =
        ((heatP t z : ℂ) * mFourier (-k) z) * (mFourier (-k) (x - z) * (f (x - z) : ℂ)) := by
      intro x
      have : mFourier (-k) x = mFourier (-k) (x - z) * mFourier (-k) z := by
        rw [← mFourier_add_pt, sub_add_cancel]
      rw [this]; push_cast; ring
    simp_rw [e3]
    rw [integral_const_mul, integral_sub_right_eq_self (fun y => mFourier (-k) y * (f y : ℂ)) z,
      mFourierCoeff_eq_integral]
    rfl
  simp_rw [e2]
  rw [integral_mul_const, heatP_fourier ht]

theorem heatT_congr_ae {t : ℝ} (ht : 0 < t) {f g : UnitAddTorus ι → ℝ}
    (hf : AEStronglyMeasurable f volume) (hfg : f =ᵐ[volume] g) (x : UnitAddTorus ι) :
    heatT t f x = heatT t g x := by
  rw [heatT_eq ht hf, heatT_eq ht (hf.congr hfg)]
  refine integral_congr_ae ?_
  have h := (Measure.measurePreserving_sub_left (volume : Measure (UnitAddTorus ι)) x).quasiMeasurePreserving.ae_eq hfg
  filter_upwards [h] with z hz
  simp only [Function.comp] at hz
  rw [hz]

theorem lintegral_heatT_rpow_le_of_measurable {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ}
    (hf : Integrable f) (hfm : Measurable f) {P : ℝ} (hP : 1 < P) :
    ∫⁻ x, ‖heatT t f x‖ₑ ^ P ≤ ∫⁻ x, ‖f x‖ₑ ^ P := by
  have hP0 : 0 < P := by linarith
  set a : UnitAddTorus ι → ℝ≥0∞ := fun z => ENNReal.ofReal (heatP t z)
  have ham : Measurable a := (measurable_heatP ht).ennreal_ofReal
  have ha1 : ∫⁻ z, a z = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_heatP ht)
      (Eventually.of_forall fun z => (heatP_pos ht z).le), integral_heatP ht, ENNReal.ofReal_one]
  have hjoint : Measurable fun p : UnitAddTorus ι × UnitAddTorus ι => ‖f (p.1 - p.2)‖ₑ :=
    (hfm.comp measurable_sub).enorm
  have hpt : ∀ x, ‖heatT t f x‖ₑ ≤ ∫⁻ z, a z * ‖f (x - z)‖ₑ := by
    intro x
    rw [heatT_eq ht hf.aestronglyMeasurable]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    congr 1; funext z
    rw [enorm_mul, ← ofReal_norm_eq_enorm (heatP t z), Real.norm_of_nonneg (heatP_pos ht z).le]
  calc ∫⁻ x, ‖heatT t f x‖ₑ ^ P
      ≤ ∫⁻ x, (∫⁻ z, a z * ‖f (x - z)‖ₑ) ^ P :=
        lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) hP0.le
    _ ≤ ∫⁻ x, (∫⁻ z, a z) ^ (P - 1) * ∫⁻ z, a z * ‖f (x - z)‖ₑ ^ P :=
        lintegral_mono fun x => lintegral_mul_rpow_le ham.aemeasurable
          (hjoint.comp (measurable_const.prodMk measurable_id)).aemeasurable hP
    _ = ∫⁻ z, a z * ∫⁻ x, ‖f (x - z)‖ₑ ^ P := by
        simp_rw [ha1, ENNReal.one_rpow, one_mul]
        rw [lintegral_lintegral_swap ((ham.comp measurable_snd).mul
          (hjoint.pow_const P)).aemeasurable]
        refine lintegral_congr fun z => ?_
        have hm : Measurable fun x : UnitAddTorus ι => ‖f (x - z)‖ₑ ^ P :=
          ((hfm.comp (measurable_sub_const z)).enorm).pow_const P
        rw [lintegral_const_mul _ hm]
    _ = ∫⁻ z, a z * ∫⁻ x, ‖f x‖ₑ ^ P := by
        refine lintegral_congr fun z => ?_
        rw [lintegral_sub_right_eq_self (fun x => ‖f x‖ₑ ^ P) z]
    _ = ∫⁻ x, ‖f x‖ₑ ^ P := by rw [lintegral_mul_const _ ham, ha1, one_mul]

/-- **`e^{tΔ}` is an `L^P` contraction**, `P > 1`. -/
theorem lintegral_heatT_rpow_le {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ}
    (hf : Integrable f) {P : ℝ} (hP : 1 < P) :
    ∫⁻ x, ‖heatT t f x‖ₑ ^ P ≤ ∫⁻ x, ‖f x‖ₑ ^ P := by
  set g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : Integrable g := hf.congr hfg
  have e1 : heatT t f = heatT t g := funext (heatT_congr_ae ht hf.aestronglyMeasurable hfg)
  have e2 : ∫⁻ x, ‖f x‖ₑ ^ P = ∫⁻ x, ‖g x‖ₑ ^ P :=
    lintegral_congr_ae (hfg.mono fun x hx => by simp only [hx])
  rw [e1, e2]
  exact lintegral_heatT_rpow_le_of_measurable ht hg
    hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable hP

end SharpLSI
