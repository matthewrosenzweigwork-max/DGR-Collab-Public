import FullLabeledLSI.Paper.Sec8Fourier2
import SharpSymmetricLSI.Defs.D12_Cosine

/-!
# Section 8.5 (Corollary 8.4), part 3: the excess kernels

For a smooth `G` on `𝕋^ι` with `Re Ĝ(k) ≥ 0` for `k ≠ 0` the two kernels
`K₁ = G - ∫G` and `K₂ = -2ΔG - a K₁` (`a = 4π²`) have `Re K̂ᵢ(k) ≥ 0` for every `k`, hence are of
positive type (`Sec8Fourier2`).
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped Real ComplexConjugate ContDiff

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isSmoothT_lap {G : UnitAddTorus ι → ℝ} (hG : IsSmoothT G) : IsSmoothT (lap G) := by
  have h : lap G ∘ liftT = fun x => ∑ i, (dpart (dpart G i) i ∘ liftT) x := by
    funext x; simp [lap]
  unfold IsSmoothT
  rw [h]
  exact ContDiff.sum fun i _ => isSmoothT_dpart (isSmoothT_dpart hG i) i

theorem cf_lin {f g : UnitAddTorus ι → ℝ} (hf : Continuous f) (hg : Continuous g) (α β : ℝ)
    (k : ι → ℤ) : cf (fun y => α * f y + β * g y) k = α * cf f k + β * cf g k := by
  have hi : ∀ {h : UnitAddTorus ι → ℝ}, Continuous h →
      Integrable (fun t => mFourier (-k) t • (h t : ℂ)) volume := fun {h} hh =>
    integrable_of_continuous_torus ((mFourier (-k)).continuous.smul
      (Complex.continuous_ofReal.comp hh))
  simp only [cf, SharpLSI.mFourierCoeff_eq_integral]
  have e : (fun t => mFourier (-k) t • (((α * f t + β * g t : ℝ)) : ℂ)) =
      fun t => (α : ℂ) • (mFourier (-k) t • (f t : ℂ)) + (β : ℂ) • (mFourier (-k) t • (g t : ℂ)) := by
    funext t
    simp only [Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul]
    ring
  have h1 : Integrable (fun t => (α : ℂ) • (mFourier (-k) t • (f t : ℂ))) volume := by
    have : Integrable (fun t => mFourier (-k) t • (f t : ℂ)) volume := hi hf
    exact Integrable.smul (α : ℂ) this
  have h2 : Integrable (fun t => (β : ℂ) • (mFourier (-k) t • (g t : ℂ))) volume := by
    have : Integrable (fun t => mFourier (-k) t • (g t : ℂ)) volume := hi hg
    exact Integrable.smul (β : ℂ) this
  rw [e, integral_add h1 h2, integral_smul, integral_smul, smul_eq_mul, smul_eq_mul]

theorem cf_const (c : ℝ) (k : ι → ℤ) : cf (fun _ => c) k = if k = 0 then (c : ℂ) else 0 := by
  simp only [cf, SharpLSI.mFourierCoeff_eq_integral, smul_eq_mul]
  rw [integral_mul_const, integral_mFourier]
  by_cases hk : k = 0
  · simp [hk]
  · have : -k ≠ 0 := neg_ne_zero.mpr hk
    simp [hk, this]

/-- The mean `∫ G`. -/
noncomputable def meanT (G : UnitAddTorus ι → ℝ) : ℝ := ∫ y, G y

theorem cf_zero_eq_mean (G : UnitAddTorus ι → ℝ) : cf G 0 = (meanT G : ℂ) := by
  simp only [cf, SharpLSI.mFourierCoeff_eq_integral, smul_eq_mul, neg_zero, mFourier_zero,
    ContinuousMap.one_apply, one_mul, meanT]
  exact integral_complex_ofReal

/-- `K₁ = G - ∫G`. -/
noncomputable def K1 (G : UnitAddTorus ι → ℝ) (z : UnitAddTorus ι) : ℝ := G z - meanT G

/-- `K₂ = -2ΔG - a K₁`. -/
noncomputable def K2 (G : UnitAddTorus ι → ℝ) (z : UnitAddTorus ι) : ℝ :=
  -2 * lap G z - aCos * K1 G z

theorem isSmoothT_K1 {G : UnitAddTorus ι → ℝ} (hG : IsSmoothT G) : IsSmoothT (K1 G) := by
  have h : K1 G ∘ liftT = fun x => (G ∘ liftT) x - meanT G := rfl
  unfold IsSmoothT; rw [h]; exact hG.sub contDiff_const

theorem isSmoothT_K2 {G : UnitAddTorus ι → ℝ} (hG : IsSmoothT G) : IsSmoothT (K2 G) := by
  have h : K2 G ∘ liftT = fun x => -2 * (lap G ∘ liftT) x - aCos * (K1 G ∘ liftT) x := rfl
  unfold IsSmoothT; rw [h]
  exact (contDiff_const.mul (isSmoothT_lap hG)).sub (contDiff_const.mul (isSmoothT_K1 hG))

theorem cf_K1 {G : UnitAddTorus ι → ℝ} (hG : IsSmoothT G) (k : ι → ℤ) :
    cf (K1 G) k = if k = 0 then 0 else cf G k := by
  have h := cf_lin (f := G) (g := fun _ => (1 : ℝ)) (continuous_of_isSmoothT hG) continuous_const
    1 (-meanT G) k
  have e : (K1 G) = fun y => 1 * G y + (-meanT G) * 1 := by funext y; simp [K1]; ring
  rw [e, h]
  have h1 : cf (fun _ : UnitAddTorus ι => (1 : ℝ)) k = if k = 0 then 1 else 0 := by
    rw [cf_const]; simp
  rw [h1]
  by_cases hk : k = 0
  · subst hk; simp [cf_zero_eq_mean]
  · simp [hk]

theorem cf_lap {G : UnitAddTorus ι → ℝ} (hG : IsSmoothT G) (k : ι → ℤ) :
    cf (lap G) k = -(4 * (π : ℂ) ^ 2 * ∑ i, (k i : ℂ) ^ 2) * cf G k := by
  have hc : ∀ i, Continuous (dpart (dpart G i) i) := fun i =>
    continuous_of_isSmoothT (isSmoothT_dpart (isSmoothT_dpart hG i) i)
  have hi : ∀ i, Integrable (fun t => mFourier (-k) t • (dpart (dpart G i) i t : ℂ)) volume :=
    fun i => integrable_of_continuous_torus ((mFourier (-k)).continuous.smul
      (Complex.continuous_ofReal.comp (hc i)))
  have e : (fun t => mFourier (-k) t • ((lap G t : ℝ) : ℂ)) =
      fun t => ∑ i, mFourier (-k) t • (dpart (dpart G i) i t : ℂ) := by
    funext t
    simp only [lap, Complex.ofReal_sum, smul_eq_mul, Finset.mul_sum]
  have h := fun i => cf_dpart2 hG i k
  simp only [cf, SharpLSI.mFourierCoeff_eq_integral] at h ⊢
  rw [e, integral_finsetSum _ fun i _ => hi i]
  simp_rw [h]
  rw [← Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]

theorem one_le_sum_sq {k : ι → ℤ} (hk : k ≠ 0) : (1 : ℝ) ≤ ∑ i, ((k i : ℤ) : ℝ) ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h; push Not at h; exact hk (funext h)
  have h1 : (1 : ℝ) ≤ ((k i : ℤ) : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (k i) ^ 2 := by nlinarith [sq_pos_of_ne_zero hi]
    exact_mod_cast this
  exact h1.trans (Finset.single_le_sum (f := fun j => ((k j : ℤ) : ℝ) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

theorem cf_K2 {G : UnitAddTorus ι → ℝ} (hG : IsSmoothT G) (k : ι → ℤ) :
    cf (K2 G) k = if k = 0 then 0 else
      ((8 * (π : ℂ) ^ 2 * ∑ i, (k i : ℂ) ^ 2) - 4 * (π : ℂ) ^ 2) * cf G k := by
  have h := cf_lin (f := lap G) (g := K1 G) (continuous_of_isSmoothT (isSmoothT_lap hG))
    (continuous_of_isSmoothT (isSmoothT_K1 hG)) (-2) (-aCos) k
  have e : K2 G = fun y => (-2) * lap G y + (-aCos) * K1 G y := by funext y; simp [K2]; ring
  rw [e, h, cf_lap hG, cf_K1 hG]
  by_cases hk : k = 0
  · subst hk; simp
  · simp only [hk, ite_false, aCos]
    push_cast
    ring

theorem re_cf_K1_nonneg {G : UnitAddTorus ι → ℝ} (hG : IsSmoothT G)
    (hGk : ∀ k : ι → ℤ, k ≠ 0 → 0 ≤ (cf G k).re) (k : ι → ℤ) : 0 ≤ (cf (K1 G) k).re := by
  rw [cf_K1 hG]
  by_cases hk : k = 0
  · simp [hk]
  · simpa [hk] using hGk k hk

theorem re_cf_K2_nonneg {G : UnitAddTorus ι → ℝ} (hG : IsSmoothT G)
    (hGk : ∀ k : ι → ℤ, k ≠ 0 → 0 ≤ (cf G k).re) (k : ι → ℤ) : 0 ≤ (cf (K2 G) k).re := by
  rw [cf_K2 hG]
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ite_false]
    have hS := one_le_sum_sq hk
    have e : (8 * (π : ℂ) ^ 2 * ∑ i, (k i : ℂ) ^ 2 - 4 * (π : ℂ) ^ 2) =
        ((8 * π ^ 2 * (∑ i, ((k i : ℤ) : ℝ) ^ 2) - 4 * π ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.re_ofReal_mul]
    refine mul_nonneg ?_ (hGk k hk)
    nlinarith [Real.pi_pos, sq_nonneg π, mul_pos Real.pi_pos Real.pi_pos]

end Sec8
end SharpLSI.FL
