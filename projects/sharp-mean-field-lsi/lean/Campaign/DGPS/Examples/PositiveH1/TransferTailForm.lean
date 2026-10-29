import Mathlib
import DGPS.Examples.PositiveH1.TransferTail

/-!
# Positive potential tail form bound (H1032)

For `κ ≥ 0`, all `N`, `M` and `ψ ∈ H¹(m^N)` with weak gradient `g`,
`∫ T_{N,M} ψ² dm^N ≤ κ A_M ‖ψ‖₂² + 4 κ C_M ‖∇ψ‖₂²`
(Tonelli on the Fourier-tail series and the coordinate multiplier H1031 squared with
`(s+t)² ≤ 2 s² + 2 t²`).  With `ψ = f √p_N` (H1028) and `κ = 1/100`:
`∫ f² T_{N,M} dP_N ≤ 32 κ C_M E_N(f) + (κ A_M + 8 κ C_M) ‖f‖₂²`.
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
open DGPS
open DGPS.Examples.PositiveH1.Particle DGPS.Examples.PositiveH1.Fourier

namespace DGPS.Examples.PositiveH1.Transfer

theorem h1032_C_nonneg (M : ℕ) : 0 ≤ C M := by
  unfold C
  refine tsum_nonneg fun n => ?_
  split_ifs
  · exact div_nonneg (a_nonneg n) (sq_nonneg _)
  · exact le_rfl

theorem h1032_summable_C (M : ℕ) :
    Summable fun n : ℕ => if M < n then a n / (2 * Real.pi * (n : ℝ)) ^ 2 else 0 := by
  have hs := (summable_tailA M).mul_left (1 / (4 * Real.pi ^ 2))
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · split_ifs
    · exact div_nonneg (a_nonneg n) (sq_nonneg _)
    · exact le_rfl
  · by_cases hn : M < n
    · simp only [hn, ite_true]
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hpi := Real.pi_pos
      have h4 : 4 * Real.pi ^ 2 ≤ (2 * Real.pi * (n : ℝ)) ^ 2 := by
        have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
        have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2)
        nlinarith
      have ha := a_nonneg n
      calc a n / (2 * Real.pi * n) ^ 2 ≤ a n / (4 * Real.pi ^ 2) :=
            div_le_div_of_nonneg_left ha (by positivity) h4
        _ = 1 / (4 * Real.pi ^ 2) * a n := by ring
    · simp [hn]

/-- Per-mode bound: `∫ |Z_{N,n} ψ|² ≤ 2 ‖ψ‖² + 8 (2π n)⁻² ‖∇ψ‖²`. -/
theorem h1032_mode_bound (N : ℕ+) (n : ℕ) (hn : n ≠ 0)
    {ψ : ParticleSpace 1 N → ℝ} {g : ParticleSpace 1 N → Fin N → Tangent 1}
    (hg : IsParticleHaarWeakGradient N ψ g) :
    ∫ x, ‖Particle.Z N n x * (ψ x : ℂ)‖ ^ 2 ∂particleHaar 1 N ≤
      2 * ∫ x, ψ x ^ 2 ∂particleHaar 1 N +
        8 * (1 / (2 * Real.pi * (n : ℝ)) ^ 2) *
          ∫ x, particleTangentNormSq (g x) ∂particleHaar 1 N := by
  have h := particle_fourier_coordinate_multiplier N n hn hg
  set I := ∫ x, ‖Particle.Z N n x * (ψ x : ℂ)‖ ^ 2 ∂particleHaar 1 N with hI
  set u := ∫ x, ψ x ^ 2 ∂particleHaar 1 N with hu
  set v := ∫ x, particleTangentNormSq (g x) ∂particleHaar 1 N with hv
  have hI0 : 0 ≤ I := integral_nonneg fun x => sq_nonneg _
  have hu0 : 0 ≤ u := integral_nonneg fun x => sq_nonneg _
  have hv0 : 0 ≤ v := integral_nonneg fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpi := Real.pi_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  set s := Real.sqrt u
  set t := 2 / (2 * Real.pi * n) * Real.sqrt v with ht
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := by positivity
  have h1 : I ≤ (s + t) ^ 2 := by
    calc I = Real.sqrt I ^ 2 := (Real.sq_sqrt hI0).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  have h2 : (s + t) ^ 2 ≤ 2 * s ^ 2 + 2 * t ^ 2 := by nlinarith [sq_nonneg (s - t)]
  have hs2 : s ^ 2 = u := Real.sq_sqrt hu0
  have ht2 : t ^ 2 = 4 * (1 / (2 * Real.pi * (n : ℝ)) ^ 2) * v := by
    rw [ht, mul_pow, div_pow, Real.sq_sqrt hv0]
    field_simp
    ring
  rw [hs2, ht2] at h2
  linarith

theorem positive_potential_tail_form_haar (κ : ℝ) (hκ : 0 ≤ κ) (N : ℕ+) (M : ℕ)
    {ψ : ParticleSpace 1 N → ℝ} {g : ParticleSpace 1 N → Fin N → Tangent 1}
    (hg : IsParticleHaarWeakGradient N ψ g) :
    ∫ x, tailT κ N M x * ψ x ^ 2 ∂particleHaar 1 N ≤
      κ * tailA M * ∫ x, ψ x ^ 2 ∂particleHaar 1 N +
        4 * κ * C M * ∫ x, particleTangentNormSq (g x) ∂particleHaar 1 N := by
  set u := ∫ x, ψ x ^ 2 ∂particleHaar 1 N with hu
  set v := ∫ x, particleTangentNormSq (g x) ∂particleHaar 1 N with hv
  have hu0 : 0 ≤ u := integral_nonneg fun x => sq_nonneg _
  have hv0 : 0 ≤ v := integral_nonneg fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _
  let F : ℕ → ParticleSpace 1 N → ℝ := fun n x =>
    if M < n then a n * ‖Particle.Z N n x * (ψ x : ℂ)‖ ^ 2 else 0
  let b : ℕ → ℝ := fun n =>
    (if M < n then a n else 0) * (2 * u) +
      (8 * v) * (if M < n then a n / (2 * Real.pi * (n : ℝ)) ^ 2 else 0)
  have hψ2 : Integrable (fun x => ψ x ^ 2) (particleHaar 1 N) := hg.memLp.integrable_sq
  have hFint : ∀ n, Integrable (F n) (particleHaar 1 N) := by
    intro n
    by_cases hn : M < n
    · simp only [F, hn, ite_true]
      refine Integrable.const_mul ?_ _
      refine Integrable.mono' (hψ2.const_mul (N : ℝ)) ?_ (Eventually.of_forall fun x => ?_)
      · exact ((((continuous_const.mul (continuous_S N n)).aestronglyMeasurable).mul
          (Complex.continuous_ofReal.comp_aestronglyMeasurable
          hg.memLp.aestronglyMeasurable)).norm.pow 2)
      · rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow, Complex.norm_real,
          Real.norm_eq_abs, sq_abs]
        have := norm_Z_sq_le N n x
        nlinarith [sq_nonneg (ψ x)]
    · simp only [F, hn, ite_false]
      exact integrable_zero _ _ _
  have hFnn : ∀ n x, 0 ≤ F n x := by
    intro n x
    simp only [F]
    split_ifs
    · exact mul_nonneg (a_nonneg n) (sq_nonneg _)
    · exact le_rfl
  have hFb : ∀ n, ∫ x, F n x ∂particleHaar 1 N ≤ b n := by
    intro n
    by_cases hn : M < n
    · simp only [F, b, hn, ite_true]
      rw [integral_const_mul]
      have hm := h1032_mode_bound N n (by omega) hg
      have ha := a_nonneg n
      calc a n * ∫ x, ‖Particle.Z N n x * (ψ x : ℂ)‖ ^ 2 ∂particleHaar 1 N
          ≤ a n * (2 * u + 8 * (1 / (2 * Real.pi * (n : ℝ)) ^ 2) * v) :=
            mul_le_mul_of_nonneg_left hm ha
        _ = _ := by ring
    · simp only [F, b, hn, ite_false]
      simp
  have hbs : Summable b := by
    refine Summable.add ((summable_tailA M).mul_right _) ((h1032_summable_C M).mul_left _)
  have hFs : Summable fun n => ∫ x, ‖F n x‖ ∂particleHaar 1 N := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => ?_) hbs
    have : ∫ x, ‖F n x‖ ∂particleHaar 1 N = ∫ x, F n x ∂particleHaar 1 N :=
      integral_congr_ae (Eventually.of_forall fun x => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (hFnn n x)])
    rw [this]; exact hFb n
  have hT : ∀ x, tailT κ N M x * ψ x ^ 2 = κ / 2 * ∑' n, F n x := by
    intro x
    unfold tailT
    rw [mul_assoc, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun n => ?_
    simp only [F]
    split_ifs
    · rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]; ring
    · simp
  simp_rw [hT]
  rw [integral_const_mul, ← integral_tsum_of_summable_integral_norm hFint hFs]
  have hsum : ∑' n, ∫ x, F n x ∂particleHaar 1 N ≤ ∑' n, b n :=
    Summable.tsum_le_tsum hFb ((Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun x => hFnn n x) hFb hbs)) hbs
  have hbt : ∑' n, b n = tailA M * (2 * u) + (8 * v) * C M := by
    simp only [b]
    rw [Summable.tsum_add ((summable_tailA M).mul_right _) ((h1032_summable_C M).mul_left _),
      tsum_mul_right, tsum_mul_left]
    rfl
  have := mul_le_mul_of_nonneg_left (hsum.trans hbt.le) (by linarith : 0 ≤ κ / 2)
  nlinarith [this]

/-- H1032: the positive potential tail form bound, on `H¹(m^N)` and on `H¹(P_N)` at `κ = 1/100`. -/
theorem positive_potential_tail_form_bound (N : ℕ+) (M : ℕ) :
    (∀ (ψ : ParticleSpace 1 N → ℝ) (g : ParticleSpace 1 N → Fin N → Tangent 1),
        IsParticleHaarWeakGradient N ψ g →
      ∫ x, tailT (1 / 100) N M x * ψ x ^ 2 ∂particleHaar 1 N ≤
        (1 / 100) * tailA M * ∫ x, ψ x ^ 2 ∂particleHaar 1 N +
          4 * (1 / 100) * C M * ∫ x, particleTangentNormSq (g x) ∂particleHaar 1 N) ∧
    ∀ f : ParticleH1 (kernelData (1 / 100)) N,
      ∫ x, f x ^ 2 * tailT (1 / 100) N M x ∂particleLaw (kernelData (1 / 100)) N ≤
        32 * (1 / 100) * C M * particleEnergy (kernelData (1 / 100)) N f +
          ((1 / 100) * tailA M + 8 * (1 / 100) * C M) *
            ∫ x, f x ^ 2 ∂particleLaw (kernelData (1 / 100)) N := by
  refine ⟨fun ψ g hg => positive_potential_tail_form_haar (1 / 100) (by norm_num) N M hg, ?_⟩
  intro f
  obtain ⟨-, hW, -, h4⟩ := ground_state_map_on_every_rough_particle_test N f.1 f.2
    (particleWeakGradient f) (isParticleWeakGradient_particleWeakGradient f)
  set ψ : ParticleSpace 1 N → ℝ := fun x => f x * Real.sqrt (p (1 / 100) N x) with hψ
  set g' : ParticleSpace 1 N → Fin N → Tangent 1 := fun x i =>
    Real.sqrt (p (1 / 100) N x) • particleWeakGradient f x i -
      ((1 / 2 : ℝ) * (f x * Real.sqrt (p (1 / 100) N x))) • roughForce (1 / 100) N x i with hg'
  have hmain := positive_potential_tail_form_haar (1 / 100) (by norm_num) N M hW
  set E := particleEnergy (kernelData (1 / 100)) N f with hE
  set u2 := ∫ x, f x ^ 2 ∂particleLaw (kernelData (1 / 100)) N with hu2
  have eψ : ∫ x, ψ x ^ 2 ∂particleHaar 1 N = u2 := by
    rw [hu2, DGPS.Particle.integral_particleLaw]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [density_eq, hψ]
    rw [mul_pow, Real.sq_sqrt (p_nonneg' (1 / 100) N x)]
    ring
  have eX : ∫ x, f x ^ 2 * tailT (1 / 100) N M x ∂particleLaw (kernelData (1 / 100)) N =
      ∫ x, tailT (1 / 100) N M x * ψ x ^ 2 ∂particleHaar 1 N := by
    rw [DGPS.Particle.integral_particleLaw]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show particleDensity (kernelData (1 / 100)) N x * (f x ^ 2 * tailT (1 / 100) N M x) =
      tailT (1 / 100) N M x * ψ x ^ 2
    simp only [density_eq, hψ]
    rw [mul_pow, Real.sq_sqrt (p_nonneg' (1 / 100) N x)]
    ring
  rw [eX]
  rw [eψ] at hmain
  have hCM := h1032_C_nonneg M
  have hcoef : 0 ≤ 4 * (1 / 100 : ℝ) * C M := by positivity
  have h4' : ∫ x, particleTangentNormSq (g' x) ∂particleHaar 1 N ≤ 8 * E + 2 * u2 := h4
  have h5 := mul_le_mul_of_nonneg_left h4' hcoef
  nlinarith [hmain, h5]

end DGPS.Examples.PositiveH1.Transfer
