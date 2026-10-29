import SharpSymmetricLSI.Infra.CZTorus5
import SharpSymmetricLSI.Paper.RefSpectrum1
import SharpSymmetricLSI.Paper.FourierSynth

/-!
# Section 8.5 (Corollary 8.4), part 1: Fourier coefficients of smooth functions

For a smooth function `u` on `𝕋^ι`:
* `(∂_i² u)^(k) = -4π² k_i² û(k)` (`cf_dpart2`);
* `∏_i (1 + k_i²) |û(k)|` is bounded, hence `û` is absolutely summable (`summable_cf_of_smooth`);
* `u(x) = ∑_k û(k) e_k(x)` (`hasSum_cf_series`).
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped Real ComplexConjugate ContDiff

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isSmoothT_dpart {u : UnitAddTorus ι → ℝ} (hu : IsSmoothT u) (i : ι) :
    IsSmoothT (dpart u i) := by
  unfold IsSmoothT at *
  rw [dpart_comp_liftT]
  exact (hu.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

theorem continuous_of_isSmoothT {u : UnitAddTorus ι → ℝ} (hu : IsSmoothT u) : Continuous u :=
  continuous_of_liftT' hu.continuous

theorem cf_dpart2 {u : UnitAddTorus ι → ℝ} (hu : IsSmoothT u) (i : ι) (k : ι → ℤ) :
    cf (dpart (dpart u i) i) k = -(4 * (π : ℂ) ^ 2 * (k i : ℂ) ^ 2) * cf u k := by
  have h1 : ContDiff ℝ 1 (u ∘ liftT) := ContDiff.of_le hu (by exact_mod_cast le_top)
  have h2 : ContDiff ℝ 1 (dpart u i ∘ liftT) :=
    ContDiff.of_le (isSmoothT_dpart hu i) (by exact_mod_cast le_top)
  have e1 := cf_dpart h2 i k
  have e2 := cf_dpart h1 i k
  simp only [cf] at e1 e2 ⊢
  rw [e1, e2]
  have : (I : ℂ) ^ 2 = -1 := I_sq
  linear_combination (4 * (π : ℂ) ^ 2 * (k i : ℂ) ^ 2 * mFourierCoeff (fun y => (u y : ℂ)) k) * this

theorem norm_cf_le {f : UnitAddTorus ι → ℝ} {C : ℝ} (hf : ∀ y, |f y| ≤ C) (k : ι → ℤ) :
    ‖cf f k‖ ≤ C := by
  simp only [cf, SharpLSI.mFourierCoeff_eq_integral]
  have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure (UnitAddTorus ι)))
    (f := fun t => mFourier (-k) t • (f t : ℂ)) (C := C) (Eventually.of_forall fun t => by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (abs_nonneg _) (norm_mFourier_le _ _)).trans (hf t))
  simpa using h

theorem exists_abs_le_of_smooth {u : UnitAddTorus ι → ℝ} (hu : IsSmoothT u) :
    ∃ C, ∀ y, |u y| ≤ C := by
  obtain ⟨C, hC⟩ := bounded_lift (v := u) hu.continuous
  exact ⟨C, fun y => by simpa using hC y⟩

/-- `u - (4π²)⁻¹ ∂_i² u`. -/
noncomputable def shiftOp (i : ι) (u : UnitAddTorus ι → ℝ) (y : UnitAddTorus ι) : ℝ :=
  u y - (4 * π ^ 2)⁻¹ * dpart (dpart u i) i y

theorem isSmoothT_shiftOp {u : UnitAddTorus ι → ℝ} (hu : IsSmoothT u) (i : ι) :
    IsSmoothT (shiftOp i u) := by
  have h : shiftOp i u ∘ liftT = fun x => (u ∘ liftT) x -
      (4 * π ^ 2)⁻¹ * (dpart (dpart u i) i ∘ liftT) x := rfl
  unfold IsSmoothT
  rw [h]
  exact hu.sub (contDiff_const.mul (isSmoothT_dpart (isSmoothT_dpart hu i) i))

theorem cf_shiftOp {u : UnitAddTorus ι → ℝ} (hu : IsSmoothT u) (i : ι) (k : ι → ℤ) :
    cf (shiftOp i u) k = (1 + (k i : ℂ) ^ 2) * cf u k := by
  have hc1 : Continuous u := continuous_of_isSmoothT hu
  have hc2 : Continuous (dpart (dpart u i) i) := continuous_of_isSmoothT
    (isSmoothT_dpart (isSmoothT_dpart hu i) i)
  have hi : ∀ {f : UnitAddTorus ι → ℝ}, Continuous f →
      Integrable (fun t => mFourier (-k) t • (f t : ℂ)) volume := fun {f} hf =>
    integrable_of_continuous_torus ((mFourier (-k)).continuous.smul (Complex.continuous_ofReal.comp hf))
  have e : (fun t => mFourier (-k) t • ((shiftOp i u t : ℝ) : ℂ)) =
      fun t => mFourier (-k) t • (u t : ℂ) -
        ((4 * π ^ 2 : ℂ))⁻¹ • (mFourier (-k) t • (dpart (dpart u i) i t : ℂ)) := by
    funext t
    simp only [shiftOp, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_inv,
      smul_eq_mul]
    push_cast
    ring
  have hcf := cf_dpart2 hu i k
  simp only [cf, SharpLSI.mFourierCoeff_eq_integral] at hcf ⊢
  have h2 : Integrable (fun t => ((4 * π ^ 2 : ℂ))⁻¹ • (mFourier (-k) t • (dpart (dpart u i) i t : ℂ)))
      volume := by
    have hi2 : Integrable (fun t => mFourier (-k) t • (dpart (dpart u i) i t : ℂ)) volume := hi hc2
    exact Integrable.smul ((4 * (π : ℂ) ^ 2)⁻¹) hi2
  rw [e, integral_sub (hi hc1) h2, integral_smul, hcf]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h4 : ((4 * (π : ℂ) ^ 2))⁻¹ * (4 * (π : ℂ) ^ 2 * (k i : ℂ) ^ 2) = (k i : ℂ) ^ 2 := by
    field_simp
  rw [smul_eq_mul]
  linear_combination (∫ t, mFourier (-k) t • (u t : ℂ)) * h4

theorem exists_prod_bound {u : UnitAddTorus ι → ℝ} (hu : IsSmoothT u) (S : Finset ι) :
    ∃ C, ∀ k : ι → ℤ, (∏ i ∈ S, (1 + ((k i : ℤ) : ℝ) ^ 2)) * ‖cf u k‖ ≤ C := by
  induction S using Finset.induction_on generalizing u with
  | empty =>
    obtain ⟨C, hC⟩ := exists_abs_le_of_smooth hu
    exact ⟨C, fun k => by simpa using norm_cf_le hC k⟩
  | insert j S hj ih =>
    obtain ⟨C, hC⟩ := ih (isSmoothT_shiftOp hu j)
    refine ⟨C, fun k => ?_⟩
    have h := hC k
    rw [cf_shiftOp hu j k, norm_mul] at h
    have hn : ‖(1 + (k j : ℂ) ^ 2)‖ = 1 + ((k j : ℤ) : ℝ) ^ 2 := by
      have : (1 + (k j : ℂ) ^ 2) = ((1 + ((k j : ℤ) : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hn] at h
    rw [Finset.prod_insert hj]
    calc (1 + ((k j : ℤ) : ℝ) ^ 2) * (∏ i ∈ S, (1 + ((k i : ℤ) : ℝ) ^ 2)) * ‖cf u k‖
        = (∏ i ∈ S, (1 + ((k i : ℤ) : ℝ) ^ 2)) * ((1 + ((k j : ℤ) : ℝ) ^ 2) * ‖cf u k‖) := by ring
      _ ≤ C := h

theorem summable_inv_one_add_sq : Summable fun n : ℤ => 1 / (1 + ((n : ℤ) : ℝ) ^ 2) := by
  have h2 : Summable fun n : ℤ => 1 / ((n : ℝ)) ^ 2 := Real.summable_one_div_int_pow.mpr (by norm_num)
  have h3 : Summable fun n : ℤ => (if n = 0 then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by simp at hn; simp [hn]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (h2.add h3)
  by_cases hn : n = 0
  · subst hn; simp
  · simp only [hn, ite_false, add_zero]
    have : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    exact one_div_le_one_div_of_le this (by linarith)

theorem summable_cf_of_smooth {u : UnitAddTorus ι → ℝ} (hu : IsSmoothT u) :
    Summable fun k : ι → ℤ => ‖cf u k‖ := by
  obtain ⟨C, hC⟩ := exists_prod_bound hu Finset.univ
  have hs : Summable fun k : ι → ℤ => ∏ i, (1 / (1 + ((k i : ℤ) : ℝ) ^ 2)) :=
    summable_prod_pi (fun _ n => 1 / (1 + ((n : ℤ) : ℝ) ^ 2)) (fun _ n => by positivity)
      fun _ => summable_inv_one_add_sq
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hs.mul_left C)
  have hP : 0 < ∏ i, (1 + ((k i : ℤ) : ℝ) ^ 2) := Finset.prod_pos fun i _ => by positivity
  have h := hC k
  have e : ∏ i, (1 / (1 + ((k i : ℤ) : ℝ) ^ 2)) = (∏ i, (1 + ((k i : ℤ) : ℝ) ^ 2))⁻¹ := by
    rw [← Finset.prod_inv_distrib]; simp
  rw [e, ← div_eq_mul_inv, le_div_iff₀ hP]
  linarith

theorem hasSum_cf_series {u : UnitAddTorus ι → ℝ} (hu : IsSmoothT u) (x : UnitAddTorus ι) :
    HasSum (fun k : ι → ℤ => cf u k * mFourier k x) (u x : ℂ) := by
  set F : C(UnitAddTorus ι, ℂ) := ⟨fun y => (u y : ℂ),
    Complex.continuous_ofReal.comp (continuous_of_isSmoothT hu)⟩ with hF
  have hs : Summable (mFourierCoeff F) := (summable_cf_of_smooth hu).of_norm
  have := hasSum_mFourier_series_apply_of_summable hs x
  simpa [hF, cf, smul_eq_mul] using this

end Sec8
end SharpLSI.FL
