import Mathlib
import DGPS.Examples.PositiveH1.Fourier
import DGPS.Particle.Gibbs
import DGPS.Particle.DiagonalForce

open MeasureTheory
open DGPS DGPS.Examples.PositiveH1.Fourier


/-!
# Positive particle potential and uniform normalizer (H1020)

For the model `V = 0`, `W(x, y) = κ (R(x - y) - R(0))` on `𝕋¹` (`kernelData κ`), with
`Z_{N,n} = N^{-1/2} Σ_j exp(2π i n x_j)`, `U_N = (κ/2) Σ_{n ≥ 2} a_n |Z_{N,n}|²`,
`K_N = ∫ e^{-U_N} dm^N`, `p_N = K_N⁻¹ e^{-U_N}`, we prove (for `κ ≥ 0`, every `N ≥ 1`)
`∫ |Z_{N,n}|² = 1` (`n ≥ 1`), `|Z_{N,n}|² ≤ N`, `U_N ≥ 0`, `∫ U_N = κ A / 2`,
`H_N = U_N - κ N A / 2`, `e^{-κA/2} ≤ K_N ≤ 1`, `p_N ≤ e^{κA/2}`, `Z_N = e^{κNA/2} K_N`,
`particleDensity = p_N`, and `U_N - U_{N,M} = T_{N,M} ≥ 0`.

Reading choices: `exp(2π i n x_j)` is `UnitAddTorus.mFourier (fun _ => n) (x j)` (as in `cosMode`);
the truncation `U_{N,M}` sums over `2 ≤ n ≤ M` and `T_{N,M}` over `n > M` (indicator `tsum`);
`κ` is a real parameter with `0 ≤ κ`; the Hamiltonian statement is about the actual
`DGPS.particleHamiltonian (kernelData κ) N`.
-/

namespace DGPS.Examples.PositiveH1.Particle

noncomputable def mode (n : ℕ) (y : Torus 1) : ℂ :=
  UnitAddTorus.mFourier (fun _ : Fin 1 => (n : ℤ)) y

theorem mode_lift (n : ℕ) (z : ℝ) :
    mode n (torusLift (fun _ => z)) = Complex.exp (((2 * Real.pi * n * z : ℝ) : ℂ) * Complex.I) := by
  simp only [mode, UnitAddTorus.mFourier, ContinuousMap.coe_mk, Finset.univ_unique,
      Finset.prod_singleton, torusLift, SharpLSI.liftT]
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem norm_mode (n : ℕ) (y : Torus 1) : ‖mode n y‖ = 1 := by
  simpa [mode] using norm_mFourier_apply (fun _ : Fin 1 => (n : ℤ)) y

theorem mode_sub (n : ℕ) (x y : Torus 1) :
    mode n (x - y) = mode n x * (starRingEnd ℂ) (mode n y) := by
  obtain ⟨z, rfl⟩ := torus_exists_lift x
  obtain ⟨w, rfl⟩ := torus_exists_lift y
  have : (torusLift (fun _ => z) : Torus 1) - torusLift (fun _ => w) = torusLift (fun _ => z - w) := by
    funext i; simp [torusLift, SharpLSI.liftT]
  rw [this, mode_lift, mode_lift, mode_lift, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

theorem cosMode_eq_re (n : ℕ) (x : Torus 1) : cosMode n x = (mode n x).re := rfl

theorem integral_mode (n : ℕ) (hn : n ≠ 0) : ∫ y, mode n y ∂haar 1 = 0 := by
  unfold mode
  rw [integral_mFourier]
  have : (fun _ : Fin 1 => (n : ℤ)) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this; exact hn this
  simp [this]


/-- `Z_{N,n} = N^{-1/2} Σ_j exp(2π i n x_j)`. -/
noncomputable def Z (N : ℕ+) (n : ℕ) (x : ParticleSpace 1 N) : ℂ :=
  (((Real.sqrt (N : ℝ))⁻¹ : ℝ) : ℂ) * ∑ j, mode n (x j)

noncomputable def S (N : ℕ+) (n : ℕ) (x : ParticleSpace 1 N) : ℂ := ∑ j, mode n (x j)

theorem norm_Z_sq (N : ℕ+) (n : ℕ) (x : ParticleSpace 1 N) :
    ‖Z N n x‖ ^ 2 = ‖S N n x‖ ^ 2 / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  unfold Z S
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    inv_pow, Real.sq_sqrt hN.le]
  field_simp

theorem norm_S_le (N : ℕ+) (n : ℕ) (x : ParticleSpace 1 N) : ‖S N n x‖ ≤ N := by
  unfold S
  refine (norm_sum_le _ _).trans ?_
  simp [norm_mode]

theorem norm_Z_sq_le (N : ℕ+) (n : ℕ) (x : ParticleSpace 1 N) : ‖Z N n x‖ ^ 2 ≤ N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  rw [norm_Z_sq, div_le_iff₀ hN]
  have := norm_S_le N n x
  nlinarith [norm_nonneg (S N n x)]

theorem normSq_S_complex (N : ℕ+) (n : ℕ) (x : ParticleSpace 1 N) :
    (((‖S N n x‖ ^ 2 : ℝ)) : ℂ) = ∑ i, ∑ j, mode n (x i) * (starRingEnd ℂ) (mode n (x j)) := by
  have h := Complex.mul_conj' (S N n x)
  rw [Complex.ofReal_pow, ← h]
  unfold S
  rw [map_sum, Finset.sum_mul_sum]

theorem normSq_S_cos (N : ℕ+) (n : ℕ) (x : ParticleSpace 1 N) :
    ‖S N n x‖ ^ 2 = ∑ i, ∑ j, cosMode n (x i - x j) := by
  have h := congrArg Complex.re (normSq_S_complex N n x)
  simp only [Complex.ofReal_re, Complex.re_sum] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [cosMode_eq_re, mode_sub]

theorem integral_normSq_S (N : ℕ+) (n : ℕ) (hn : n ≠ 0) :
    ∫ x, ‖S N n x‖ ^ 2 ∂particleHaar 1 N = N := by
  have hc : ∀ i j : Fin N, ∫ x : ParticleSpace 1 N,
      mode n (x i) * (starRingEnd ℂ) (mode n (x j)) ∂particleHaar 1 N = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [ite_true]
      have : ∀ x : ParticleSpace 1 N, mode n (x i) * (starRingEnd ℂ) (mode n (x i)) = 1 := by
        intro x
        rw [Complex.mul_conj', norm_mode]
        simp
      simp [this]
    · simp only [hij, ite_false]
      let f : (k : Fin N) → Torus 1 → ℂ := fun k y =>
        if k = i then mode n y else if k = j then (starRingEnd ℂ) (mode n y) else 1
      have hf : ∀ x : ParticleSpace 1 N, ∏ k, f k (x k) =
          mode n (x i) * (starRingEnd ℂ) (mode n (x j)) := by
        intro x
        rw [Finset.prod_eq_mul_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij]
        · simp [f, Ne.symm hij]
        · intro k _ hk
          simp [f, hk.1, hk.2]
      have := integral_fintype_prod_eq_prod (𝕜 := ℂ) (μ := fun _ : Fin N => haar 1) f
      simp_rw [hf] at this
      unfold particleHaar
      rw [this]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp [f, integral_mode n hn]
  have h1 : ((∫ x, ‖S N n x‖ ^ 2 ∂particleHaar 1 N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← integral_complex_ofReal]
    simp_rw [normSq_S_complex]
    have hint : ∀ i j : Fin N, Integrable (fun x : ParticleSpace 1 N =>
        mode n (x i) * (starRingEnd ℂ) (mode n (x j))) (particleHaar 1 N) := by
      intro i j
      have hm : Continuous (mode n) := (UnitAddTorus.mFourier (fun _ : Fin 1 => (n : ℤ))).continuous
      have : Continuous fun x : ParticleSpace 1 N =>
          mode n (x i) * (starRingEnd ℂ) (mode n (x j)) :=
        (hm.comp (continuous_apply i)).mul
          (Complex.continuous_conj.comp (hm.comp (continuous_apply j)))
      exact this.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hint _ j), hc]
    simp
  exact_mod_cast h1


theorem continuous_mode (n : ℕ) : Continuous (mode n) :=
  (UnitAddTorus.mFourier (fun _ : Fin 1 => (n : ℤ))).continuous

theorem continuous_S (N : ℕ+) (n : ℕ) : Continuous (S N n) :=
  continuous_finsetSum _ fun j _ => (continuous_mode n).comp (continuous_apply j)

theorem continuous_normSq_Z (N : ℕ+) (n : ℕ) : Continuous fun x => ‖Z N n x‖ ^ 2 := by
  have : Continuous (Z N n) := continuous_const.mul (continuous_S N n)
  fun_prop

/-- The potential `U_N = (κ/2) Σ_{n ≥ 2} a_n |Z_{N,n}|²`. -/
noncomputable def U (κ : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) : ℝ :=
  κ / 2 * ∑' n : ℕ, a n * ‖Z N n x‖ ^ 2

/-- The truncated potential `U_{N,M} = (κ/2) Σ_{2 ≤ n ≤ M} a_n |Z_{N,n}|²`. -/
noncomputable def UM (κ : ℝ) (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) : ℝ :=
  κ / 2 * ∑ n ∈ Finset.Icc 2 M, a n * ‖Z N n x‖ ^ 2

/-- The tail `T_{N,M} = (κ/2) Σ_{n > M} a_n |Z_{N,n}|²`. -/
noncomputable def tailT (κ : ℝ) (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) : ℝ :=
  κ / 2 * ∑' n : ℕ, if M < n then a n * ‖Z N n x‖ ^ 2 else 0

/-- The normalizer `K_N = ∫ e^{-U_N} dm^N`. -/
noncomputable def K (κ : ℝ) (N : ℕ+) : ℝ :=
  ∫ x, Real.exp (-U κ N x) ∂particleHaar 1 N

/-- The density `p_N = K_N⁻¹ e^{-U_N}`. -/
noncomputable def p (κ : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) : ℝ :=
  (K κ N)⁻¹ * Real.exp (-U κ N x)

/-- The interaction data `V = 0`, `W(x,y) = κ (R(x - y) - R(0))` on `𝕋¹`. -/
noncomputable def kernelData (κ : ℝ) : InteractionData 1 where
  V := fun _ => 0
  W := fun x y => κ * (R (x - y) - R 0)
  V_continuous := continuous_const
  W_continuous := continuous_const.mul
    ((continuous_R.comp (continuous_fst.sub continuous_snd)).sub continuous_const)
  W_symm := fun x y => by rw [show y - x = -(x - y) from (neg_sub x y).symm, R_neg]
  W_diag := fun x => by simp

theorem summable_modes (N : ℕ+) (x : ParticleSpace 1 N) :
    Summable fun n : ℕ => a n * ‖Z N n x‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (a_nonneg n) (sq_nonneg _))
    (fun n => mul_le_mul_of_nonneg_left (norm_Z_sq_le N n x) (a_nonneg n))
    (a_summable.mul_right (N : ℝ))

theorem tsum_modes_nonneg (N : ℕ+) (x : ParticleSpace 1 N) :
    0 ≤ ∑' n : ℕ, a n * ‖Z N n x‖ ^ 2 :=
  tsum_nonneg fun n => mul_nonneg (a_nonneg n) (sq_nonneg _)

theorem U_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (N : ℕ+) (x : ParticleSpace 1 N) : 0 ≤ U κ N x :=
  mul_nonneg (by linarith) (tsum_modes_nonneg N x)

theorem hamiltonian_eq (κ : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    particleHamiltonian (kernelData κ) N x = U κ N x - κ * N * A / 2 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hcos : ∀ i j : Fin N, Summable fun n : ℕ => a n * cosMode n (x i - x j) :=
    fun i j => summable_term _
  have h1 : ∑ i, ∑ j, R (x i - x j) = N * ∑' n : ℕ, a n * ‖Z N n x‖ ^ 2 := by
    have e1 : ∀ i, ∑ j, R (x i - x j) = ∑' n : ℕ, ∑ j, a n * cosMode n (x i - x j) := by
      intro i
      exact (Summable.tsum_finsetSum (fun j _ => hcos i j)).symm
    simp_rw [e1]
    rw [← Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hcos i j))]
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp_rw [← Finset.mul_sum]
    rw [← normSq_S_cos, norm_Z_sq]
    field_simp
  simp only [particleHamiltonian, kernelData, Finset.sum_const_zero, zero_add]
  simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib, h1, R_zero]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold U
  field_simp


theorem continuous_U (κ : ℝ) (N : ℕ+) : Continuous (U κ N) := by
  have h : U κ N = fun x => particleHamiltonian (kernelData κ) N x + κ * N * A / 2 := by
    funext x; rw [hamiltonian_eq]; ring
  rw [h]
  exact (DGPS.Particle.particleHamiltonian_continuous (kernelData κ) N).add continuous_const

theorem integral_mode_term (N : ℕ+) (n : ℕ) :
    ∫ x, a n * ‖Z N n x‖ ^ 2 ∂particleHaar 1 N = a n := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  by_cases hn : n < 2
  · simp [a_zero_of_lt hn]
  · have hn0 : n ≠ 0 := by omega
    simp_rw [norm_Z_sq]
    rw [integral_const_mul, integral_div, integral_normSq_S N n hn0]
    field_simp

theorem integrable_mode_term (N : ℕ+) (n : ℕ) :
    Integrable (fun x : ParticleSpace 1 N => a n * ‖Z N n x‖ ^ 2) (particleHaar 1 N) :=
  (continuous_const.mul (continuous_normSq_Z N n)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integrable_U (κ : ℝ) (N : ℕ+) : Integrable (U κ N) (particleHaar 1 N) :=
  (continuous_U κ N).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_U (κ : ℝ) (N : ℕ+) : ∫ x, U κ N x ∂particleHaar 1 N = κ * A / 2 := by
  unfold U
  rw [integral_const_mul]
  have hs : Summable fun n : ℕ => ∫ x, ‖a n * ‖Z N n x‖ ^ 2‖ ∂particleHaar 1 N := by
    have : (fun n : ℕ => ∫ x, ‖a n * ‖Z N n x‖ ^ 2‖ ∂particleHaar 1 N) = a := by
      funext n
      have h : (fun x : ParticleSpace 1 N => ‖a n * ‖Z N n x‖ ^ 2‖)
          = fun x => a n * ‖Z N n x‖ ^ 2 :=
        funext fun x => Real.norm_of_nonneg (mul_nonneg (a_nonneg n) (sq_nonneg _))
      rw [h, integral_mode_term]
    rw [this]; exact a_summable
  rw [← integral_tsum_of_summable_integral_norm (integrable_mode_term N) hs]
  simp_rw [integral_mode_term]
  unfold A
  ring


theorem integrable_exp_neg_U (κ : ℝ) (N : ℕ+) :
    Integrable (fun x => Real.exp (-U κ N x)) (particleHaar 1 N) :=
  (Real.continuous_exp.comp (continuous_U κ N).neg).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem K_le_one {κ : ℝ} (hκ : 0 ≤ κ) (N : ℕ+) : K κ N ≤ 1 := by
  unfold K
  calc ∫ x, Real.exp (-U κ N x) ∂particleHaar 1 N ≤ ∫ _x, (1 : ℝ) ∂particleHaar 1 N :=
        integral_mono (integrable_exp_neg_U κ N) (integrable_const _) fun x => by
          simpa using U_nonneg hκ N x
    _ = 1 := by simp

theorem exp_le_K (κ : ℝ) (N : ℕ+) : Real.exp (-(κ * A / 2)) ≤ K κ N := by
  unfold K
  set c : ℝ := -(κ * A / 2) with hc
  have hmono : ∫ x, Real.exp c * (1 + (-U κ N x - c)) ∂particleHaar 1 N
      ≤ ∫ x, Real.exp (-U κ N x) ∂particleHaar 1 N := by
    refine integral_mono ?_ (integrable_exp_neg_U κ N) fun x => ?_
    · exact ((integrable_const (1 : ℝ)).add
        ((integrable_U κ N).neg.sub (integrable_const c))).const_mul _
    · have h := Real.add_one_le_exp (-U κ N x - c)
      have : Real.exp (-U κ N x) = Real.exp c * Real.exp (-U κ N x - c) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  refine le_trans (le_of_eq ?_) hmono
  rw [integral_const_mul]
  have : ∫ x, (1 + (-U κ N x - c)) ∂particleHaar 1 N = 1 := by
    have hI : Integrable (fun x : ParticleSpace 1 N => -U κ N x - c) (particleHaar 1 N) :=
      (integrable_U κ N).neg.sub (integrable_const c)
    have h3 : ∫ x, (-U κ N x - c) ∂particleHaar 1 N = -(κ * A / 2) - c := by
      rw [integral_sub (f := fun x => -U κ N x) (g := fun _ => c) (integrable_U κ N).neg (integrable_const c), integral_neg, integral_U]
      simp
    rw [integral_add (integrable_const (1 : ℝ)) hI, h3]
    simp [hc]
  rw [this, mul_one]

theorem K_pos (κ : ℝ) (N : ℕ+) : 0 < K κ N := lt_of_lt_of_le (Real.exp_pos _) (exp_le_K κ N)

theorem p_le {κ : ℝ} (hκ : 0 ≤ κ) (N : ℕ+) (x : ParticleSpace 1 N) :
    p κ N x ≤ Real.exp (κ * A / 2) := by
  unfold p
  have hK := K_pos κ N
  have h1 : (K κ N)⁻¹ ≤ Real.exp (κ * A / 2) := by
    rw [inv_le_comm₀ hK (Real.exp_pos _), ← Real.exp_neg]
    exact exp_le_K κ N
  have h2 : Real.exp (-U κ N x) ≤ 1 := by simpa using U_nonneg hκ N x
  calc (K κ N)⁻¹ * Real.exp (-U κ N x) ≤ (K κ N)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hK.le)
    _ ≤ _ := by rw [mul_one]; exact h1

theorem partition_eq (κ : ℝ) (N : ℕ+) :
    particlePartition (kernelData κ) N = Real.exp (κ * N * A / 2) * K κ N := by
  unfold particlePartition K
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hamiltonian_eq]
  rw [← Real.exp_add]; congr 1; ring

theorem density_eq (κ : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    particleDensity (kernelData κ) N x = p κ N x := by
  unfold particleDensity p
  have := (Real.exp_pos (κ * N * A / 2)).ne'
  have h2 : Real.exp (-(U κ N x - κ * N * A / 2)) = Real.exp (-U κ N x) * Real.exp (κ * N * A / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [partition_eq, hamiltonian_eq, mul_inv, h2]
  field_simp

theorem U_sub_UM (κ : ℝ) (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) :
    U κ N x - UM κ N M x = tailT κ N M x := by
  unfold U UM tailT
  have hs := summable_modes N x
  have hsplit : (fun n : ℕ => a n * ‖Z N n x‖ ^ 2) =
      (fun n => if n ≤ M then a n * ‖Z N n x‖ ^ 2 else 0) +
      (fun n => if M < n then a n * ‖Z N n x‖ ^ 2 else 0) := by
    funext n
    by_cases h : n ≤ M
    · simp [h, not_lt.mpr h]
    · simp [h, not_le.mp h]
  have h1 : Summable fun n : ℕ => if n ≤ M then a n * ‖Z N n x‖ ^ 2 else 0 :=
    summable_of_ne_finset_zero (s := Finset.range (M + 1)) (fun n hn => by
      have : ¬ n ≤ M := by simpa [Nat.lt_succ_iff] using hn
      simp [this])
  have h2 : Summable fun n : ℕ => if M < n then a n * ‖Z N n x‖ ^ 2 else 0 := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
    · split_ifs
      · exact mul_nonneg (a_nonneg n) (sq_nonneg _)
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact mul_nonneg (a_nonneg n) (sq_nonneg _)
  have h1sum : ∑' n : ℕ, (if n ≤ M then a n * ‖Z N n x‖ ^ 2 else 0)
      = ∑ n ∈ Finset.Icc 2 M, a n * ‖Z N n x‖ ^ 2 := by
    rw [tsum_eq_sum (s := Finset.range (M + 1)) (fun n hn => by
      have : ¬ n ≤ M := by simpa [Nat.lt_succ_iff] using hn
      simp [this])]
    rw [Finset.sum_congr rfl (g := fun n => a n * ‖Z N n x‖ ^ 2) (fun n hn => by
      have : n ≤ M := by simpa [Nat.lt_succ_iff] using hn
      simp [this])]
    symm
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      simp only [Finset.mem_range]; omega
    · intro n _ hn
      have : n < 2 := by
        by_contra hc
        apply hn
        simp only [Finset.mem_Icc]
        constructor <;> [omega; (simp only [Finset.mem_range] at *; omega)]
      simp [a_zero_of_lt this]
  have : ∑' n : ℕ, a n * ‖Z N n x‖ ^ 2 = (∑' n : ℕ, (if n ≤ M then a n * ‖Z N n x‖ ^ 2 else 0)) +
      ∑' n : ℕ, if M < n then a n * ‖Z N n x‖ ^ 2 else 0 := by
    rw [hsplit]
    exact h1.tsum_add h2
  rw [this, h1sum]
  ring

theorem tailT_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) :
    0 ≤ tailT κ N M x := by
  unfold tailT
  refine mul_nonneg (by linarith) (tsum_nonneg fun n => ?_)
  split_ifs
  · exact mul_nonneg (a_nonneg n) (sq_nonneg _)
  · exact le_rfl

/-- H1020: positive particle potential and uniform normalizer. -/
theorem positive_particle_potential_and_uniform_normalizer (κ : ℝ) (hκ : 0 ≤ κ) (N : ℕ+) :
    (∀ n : ℕ, 1 ≤ n → ∫ x, ‖Z N n x‖ ^ 2 ∂particleHaar 1 N = 1) ∧
    (∀ (n : ℕ) (x : ParticleSpace 1 N), ‖Z N n x‖ ^ 2 ≤ N) ∧
    (∀ x : ParticleSpace 1 N, Summable fun n : ℕ => a n * ‖Z N n x‖ ^ 2) ∧
    (∀ x : ParticleSpace 1 N, 0 ≤ U κ N x) ∧
    Integrable (U κ N) (particleHaar 1 N) ∧ ∫ x, U κ N x ∂particleHaar 1 N = κ * A / 2 ∧
    (∀ x : ParticleSpace 1 N,
      particleHamiltonian (kernelData κ) N x = U κ N x - κ * N * A / 2) ∧
    Real.exp (-(κ * A / 2)) ≤ K κ N ∧ K κ N ≤ 1 ∧
    (∀ x : ParticleSpace 1 N, p κ N x ≤ Real.exp (κ * A / 2)) ∧
    particlePartition (kernelData κ) N = Real.exp (κ * N * A / 2) * K κ N ∧
    (∀ x : ParticleSpace 1 N, particleDensity (kernelData κ) N x = p κ N x) ∧
    (∀ (M : ℕ) (x : ParticleSpace 1 N),
      U κ N x - UM κ N M x = tailT κ N M x ∧ 0 ≤ tailT κ N M x) := by
  refine ⟨?_, norm_Z_sq_le N, summable_modes N, U_nonneg hκ N, integrable_U κ N, integral_U κ N,
    hamiltonian_eq κ N, exp_le_K κ N, K_le_one hκ N, p_le hκ N, partition_eq κ N,
    density_eq κ N, fun M x => ⟨U_sub_UM κ N M x, tailT_nonneg hκ N M x⟩⟩
  intro n hn
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  simp_rw [norm_Z_sq]
  rw [integral_div, integral_normSq_S N n (by omega)]
  field_simp

/-! ### H1026: the weak rough particle gradient -/

section Translate

variable {d : ℕ}

theorem fderiv_lift_periodic {φ : Torus d → ℝ} (z : Fin d → ℝ) (m : Fin d → ℤ) :
    fderiv ℝ (φ ∘ torusLift) (z + SharpLSI.intVec m) = fderiv ℝ (φ ∘ torusLift) z := by
  have h : (fun w => (φ ∘ torusLift) (w + SharpLSI.intVec m)) = φ ∘ torusLift := by
    funext w; simp [SharpLSI.liftT_add_intVec]
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := φ ∘ torusLift) (SharpLSI.intVec m) (x := z)
  rw [h] at this
  exact this.symm

theorem translate_comp_lift (φ : Torus d → ℝ) (y : Torus d) :
    (fun x => φ (x + y)) ∘ torusLift = fun z => (φ ∘ torusLift) (z + SharpLSI.secT y) := by
  funext z
  simp only [Function.comp, SharpLSI.liftT_add, SharpLSI.liftT_secT]

theorem isSmoothPeriodic_translate {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) (y : Torus d) :
    IsSmoothPeriodic (fun x => φ (x + y)) := by
  unfold IsSmoothPeriodic
  rw [translate_comp_lift]
  exact hφ.comp (contDiff_id.add contDiff_const)

theorem coordPartial_translate {φ : Torus d → ℝ} (j : Fin d) (y x : Torus d) :
    coordPartial j (fun x => φ (x + y)) x = coordPartial j φ (x + y) := by
  unfold coordPartial
  rw [translate_comp_lift]
  have h1 := fderiv_comp_add_right (𝕜 := ℝ) (f := φ ∘ torusLift) (SharpLSI.secT y)
    (x := SharpLSI.secT x)
  rw [h1]
  obtain ⟨m, hm⟩ := SharpLSI.secT_liftT_eq (SharpLSI.secT x + SharpLSI.secT y)
  have e : SharpLSI.liftT (SharpLSI.secT x + SharpLSI.secT y) = x + y := by
    rw [SharpLSI.liftT_add, SharpLSI.liftT_secT, SharpLSI.liftT_secT]
  rw [e] at hm
  rw [hm, fderiv_lift_periodic]

/-- Weak gradients are translation covariant. -/
theorem isWeakGradient_translate {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) (y : Torus d) :
    IsWeakGradient (fun x => u (x - y)) (fun x => g (x - y)) where
  memLp := h.memLp.comp_measurePreserving (measurePreserving_sub_right _ y)
  memLp_grad := h.memLp_grad.comp_measurePreserving (measurePreserving_sub_right _ y)
  ibp φ hφ j := by
    have hs := h.ibp _ (isSmoothPeriodic_translate hφ y) j
    simp only [coordPartial_translate] at hs
    have e1 : ∫ x, u (x - y) * coordPartial j φ x ∂haar d =
        ∫ x, u x * coordPartial j φ (x + y) ∂haar d := by
      rw [← integral_add_right_eq_self (fun x => u (x - y) * coordPartial j φ x) y]
      simp
    have e2 : ∫ x, g (x - y) j * φ x ∂haar d = ∫ x, g x j * φ (x + y) ∂haar d := by
      rw [← integral_add_right_eq_self (fun x => g (x - y) j * φ x) y]
      simp
    rw [e1, hs, e2]

end Translate

section Pair

variable {N : ℕ+}

/-- The pair-difference map `x ↦ x_i - x_j` as an additive homomorphism. -/
noncomputable def pairDiffHom (i j : Fin N) : ParticleSpace 1 N →+ Torus 1 where
  toFun x := x i - x j
  map_zero' := by simp
  map_add' x y := by simp [sub_add_sub_comm]

/-- For `i ≠ j`, the pair map `x ↦ x_i - x_j` is Haar preserving `(𝕋¹)^N → 𝕋¹`. -/
theorem measurePreserving_pairDiff {i j : Fin N} (hij : i ≠ j) :
    MeasurePreserving (fun x : ParticleSpace 1 N => x i - x j) (particleHaar 1 N) (haar 1) := by
  have hc : Continuous (pairDiffHom i j) :=
    (continuous_apply i).sub (continuous_apply j)
  have hs : Function.Surjective (pairDiffHom i j) := by
    intro t
    refine ⟨Pi.single i t, ?_⟩
    simp [pairDiffHom, hij.symm]
  have h1 : (haar 1).IsAddHaarMeasure := by
    rw [DGPS.haar_eq_pi_haarAddCircle]; infer_instance
  have h2 : (particleHaar 1 N).IsAddHaarMeasure := by
    unfold particleHaar; exact MeasureTheory.Measure.pi.isAddHaarMeasure (fun _ => haar 1)
  have hmeas : Measurable (pairDiffHom i j) := hc.measurable
  have h3 : ((particleHaar 1 N).map (pairDiffHom i j)).IsAddHaarMeasure :=
    MeasureTheory.Measure.isAddHaarMeasure_map (particleHaar 1 N) (pairDiffHom i j) hc hs (by
      rw [Filter.cocompact_eq_bot, Filter.cocompact_eq_bot]; exact Filter.tendsto_bot)
  have h4 : IsProbabilityMeasure ((particleHaar 1 N).map (pairDiffHom i j)) :=
    ⟨by rw [Measure.map_apply hmeas MeasurableSet.univ]; simp⟩
  refine ⟨hmeas, ?_⟩
  exact MeasureTheory.Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure
    (μ' := (particleHaar 1 N).map (pairDiffHom i j)) (μ := haar 1)

end Pair

section Core

variable {d : ℕ}

/-- The computation of `DGPS.Lipschitz.df_core`, with the bounded `B` replaced by an `L²`
pair force (only the pairs `i ≠ j` are used). -/
theorem core_rough {V : Torus d → ℝ} {gV gδ : Torus d → Tangent d}
    {F : Torus d → Torus d → ℝ} {B : Torus d → Torus d → Tangent d}
    (hsymm : ∀ x y, F x y = F y x) (hFc : Continuous (Function.uncurry F))
    (N : ℕ+)
    (hBmem : ∀ i j : Fin N, i ≠ j →
      MemLp (fun x : ParticleSpace d N => B (x i) (x j)) 2 (particleHaar d N))
    (hB : ∀ y, IsWeakGradient (fun x => F x y) (fun x => B x y))
    (hV : IsWeakGradient V gV) (hδ : IsWeakGradient (fun x => F x x) gδ) :
    IsParticleHaarWeakGradient N
      (fun x : ParticleSpace d N => ∑ i, V (x i) + (1 / (2 * (N : ℝ))) * ∑ i, ∑ j, F (x i) (x j))
      (fun x i => gV (x i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) +
        (2 * (N : ℝ))⁻¹ • gδ (x i)) := by
  have hmeas2 : ∀ i j : Fin N, Measurable fun x : ParticleSpace d N => (x i, x j) := fun i j =>
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus d × Torus d)).exists_bound_of_continuousOn
    hFc.continuousOn
  have hFmem : ∀ i j : Fin N, MemLp (fun x : ParticleSpace d N => F (x i) (x j)) 2
      (particleHaar d N) := fun i j =>
    MemLp.of_bound (hFc.measurable.comp (hmeas2 i j)).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => hC (x i, x j) (Set.mem_univ _))
  have hf : MemLp (fun x : ParticleSpace d N =>
      ∑ i, V (x i) + (1 / (2 * (N : ℝ))) * ∑ i, ∑ j, F (x i) (x j)) 2 (particleHaar d N) := by
    have h1 : MemLp (fun x : ParticleSpace d N => ∑ i, V (x i)) 2 (particleHaar d N) :=
      memLp_finsetSum _ fun i _ => Lipschitz.df_memLp_comp_eval hV.memLp i
    have h2 : MemLp (fun x : ParticleSpace d N => ∑ i, ∑ j, F (x i) (x j)) 2
        (particleHaar d N) :=
      memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => hFmem i j
    exact h1.add (h2.const_mul _)
  have hg : MemLp (fun (x : ParticleSpace d N) (i : Fin N) => gV (x i) +
      (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) + (2 * (N : ℝ))⁻¹ • gδ (x i)) 2
      (particleHaar d N) := by
    refine memLp_pi_iff.2 fun i => ?_
    have h1 := Lipschitz.df_memLp_comp_eval_tangent (N := N) hV.memLp_grad i
    have h2 : MemLp (fun x : ParticleSpace d N => ∑ j ∈ Finset.univ.erase i, B (x i) (x j)) 2
        (particleHaar d N) :=
      memLp_finsetSum _ fun j hj => hBmem i j (Finset.ne_of_mem_erase hj).symm
    have h3 := Lipschitz.df_memLp_comp_eval_tangent (N := N) hδ.memLp_grad i
    have h4 : MemLp (fun x : ParticleSpace d N =>
        (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j)) 2 (particleHaar d N) :=
      h2.const_smul ((N : ℝ)⁻¹)
    have h5 : MemLp (fun x : ParticleSpace d N => (2 * (N : ℝ))⁻¹ • gδ (x i)) 2
        (particleHaar d N) := h3.const_smul ((2 * (N : ℝ))⁻¹)
    have h6 : MemLp (fun x : ParticleSpace d N =>
        gV (x i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j)) 2 (particleHaar d N) :=
      h1.add h4
    exact h6.add h5
  refine ⟨hf, hg, fun φ hφ i l => ?_⟩
  refine Lipschitz.df_ibp_of_slice
    (g := fun (x : ParticleSpace d N) (i : Fin N) => gV (x i) +
      (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) + (2 * (N : ℝ))⁻¹ • gδ (x i))
    i l hf (memLp_particleCoord hg i l) (fun x => ?_) hφ
  have e1 : (fun t => ∑ a, V (Function.update x i t a) + (1 / (2 * (N : ℝ))) *
      ∑ a, ∑ b, F (Function.update x i t a) (Function.update x i t b)) =
      fun t => (V t + ∑ a ∈ Finset.univ.erase i, V (x a)) + (1 / (2 * (N : ℝ))) *
        ((F t t + 2 * ∑ b ∈ Finset.univ.erase i, F t (x b)) +
          ∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase i, F (x a) (x b)) := by
    funext t
    rw [Lipschitz.df_sum_update_eq i x t V, Lipschitz.df_double_sum_update_eq i x t F hsymm]
  have e2 : (fun t => gV (Function.update x i t i) +
      (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i,
        B (Function.update x i t i) (Function.update x i t j) +
      (2 * (N : ℝ))⁻¹ • gδ (Function.update x i t i)) =
      fun t => (gV t + 0) + (1 / (2 * (N : ℝ))) •
        ((gδ t + (2 : ℝ) • ∑ b ∈ Finset.univ.erase i, B t (x b)) + 0) := by
    funext t
    simp only [Function.update_self]
    have : ∑ j ∈ Finset.univ.erase i, B t (Function.update x i t j) =
        ∑ j ∈ Finset.univ.erase i, B t (x j) :=
      Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [this]
    module
  rw [e1, e2]
  refine (hV.add (Lipschitz.df_isWeakGradient_const _)).add
    (((hδ.add ((Lipschitz.df_isWeakGradient_sum _ fun b _ => hB (x b)).smul 2)).add
      (Lipschitz.df_isWeakGradient_const _)).smul _)

end Core

/-- The weak force `x ↦ (κ/N) ∑_{j≠i} R′(xᵢ - xⱼ)` (as a tangent vector in `ℝ¹`), with `R′ = dR`
the `L²` weak derivative of `R` from H1003. -/
noncomputable def roughForce (κ : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) (i : Fin N) : Tangent 1 :=
  (κ / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
    (EuclideanSpace.single (0 : Fin 1) (dR (x i - x j)) : Tangent 1)

theorem roughForce_apply (κ : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) (i : Fin N) :
    roughForce κ N x i 0 = κ / (N : ℝ) * ∑ j ∈ Finset.univ.erase i, dR (x i - x j) := by
  simp [roughForce, Finset.sum_apply]

theorem measurable_dR : Measurable dR :=
  (Lp.stronglyMeasurable (Classical.choose exists_limit_fL)).measurable

/-- H1026: weak rough particle gradient. For each fixed `N ≥ 1` (and every real `κ`),
`U_N ∈ L^∞ ∩ H¹((𝕋¹)^N)` with weak gradient `∂ᵢ U_N = (κ/N) ∑_{j≠i} R′(xᵢ - xⱼ)`
(here `R′ = dR` is the `L²` weak derivative of `R`, H1003); the original Hamiltonian `H_N`
(`kernelData κ`) has the same weak gradient, both with respect to Haar measure `m^N` and in the
Gibbs `H¹(P_N)` sense. The `i`-th component is `roughForce κ N x i`, whose coordinate is
`κ/N * ∑_{j≠i} dR (xᵢ - xⱼ)` (`roughForce_apply`). -/
theorem weak_rough_particle_gradient (κ : ℝ) (N : ℕ+) :
    MemLp (U κ N) ⊤ (particleHaar 1 N) ∧
    IsParticleHaarWeakGradient N (U κ N) (roughForce κ N) ∧
    MemParticleHaarH1 N (U κ N) ∧
    IsParticleWeakGradient (kernelData κ) N (U κ N) (roughForce κ N) ∧
    IsParticleHaarWeakGradient N (particleHamiltonian (kernelData κ) N) (roughForce κ N) ∧
    IsParticleWeakGradient (kernelData κ) N (particleHamiltonian (kernelData κ) N)
      (roughForce κ N) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  set F : Torus 1 → Torus 1 → ℝ := fun x y => κ * (R (x - y) - R 0) with hFdef
  set B : Torus 1 → Torus 1 → Tangent 1 :=
    fun x y => κ • (EuclideanSpace.single (0 : Fin 1) (dR (x - y)) : Tangent 1) with hBdef
  have hsymm : ∀ x y, F x y = F y x := fun x y => by
    simp only [hFdef]; rw [show y - x = -(x - y) from (neg_sub x y).symm, R_neg]
  have hFc : Continuous (Function.uncurry F) :=
    continuous_const.mul ((continuous_R.comp (continuous_fst.sub continuous_snd)).sub
      continuous_const)
  have hBmem : ∀ i j : Fin N, i ≠ j →
      MemLp (fun x : ParticleSpace 1 N => B (x i) (x j)) 2 (particleHaar 1 N) := by
    intro i j hij
    exact (memLp_grad_dR.const_smul κ).comp_measurePreserving (measurePreserving_pairDiff hij)
  have hB : ∀ y, IsWeakGradient (fun x => F x y) (fun x => B x y) := by
    intro y
    have h1 := ((isWeakGradient_translate weak_gradient_R y).add
      (Lipschitz.df_isWeakGradient_const (d := 1) (-R 0))).smul κ
    have e1 : (fun x => F x y) = fun x => κ * (R (x - y) + -R 0) := by
      funext x; simp [hFdef, sub_eq_add_neg]
    have e2 : (fun x => B x y) = fun x => κ •
        ((EuclideanSpace.single (0 : Fin 1) (dR (x - y)) : Tangent 1) + 0) := by
      funext x; simp [hBdef]
    rw [e1, e2]
    exact h1
  have hV : IsWeakGradient (fun _ : Torus 1 => κ * A / 2) (fun _ => 0) :=
    Lipschitz.df_isWeakGradient_const _
  have hδ : IsWeakGradient (fun x => F x x) (fun _ => 0) := by
    have : (fun x => F x x) = fun _ => (0 : ℝ) := by funext x; simp [hFdef]
    rw [this]; exact isWeakGradient_zero
  have hcore := core_rough (V := fun _ : Torus 1 => κ * A / 2) (gV := fun _ => 0)
    (gδ := fun _ => 0) hsymm hFc N hBmem hB hV hδ
  have hfun : (fun (x : ParticleSpace 1 N) (i : Fin N) => (0 : Tangent 1) +
      (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) + (2 * (N : ℝ))⁻¹ • (0 : Tangent 1))
      = roughForce κ N := by
    funext x i
    simp only [roughForce, hBdef, smul_zero, zero_add, add_zero, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_eq_mul_inv, mul_comm κ]
  rw [hfun] at hcore
  have hcore0 := core_rough (V := fun _ : Torus 1 => (0 : ℝ)) (gV := fun _ => 0)
    (gδ := fun _ => 0) hsymm hFc N hBmem hB (Lipschitz.df_isWeakGradient_const _) hδ
  rw [hfun] at hcore0
  have hHeq : particleHamiltonian (kernelData κ) N = fun x : ParticleSpace 1 N =>
      ∑ i, (fun _ : Torus 1 => (0 : ℝ)) (x i) + (1 / (2 * (N : ℝ))) * ∑ i, ∑ j, F (x i) (x j) :=
    rfl
  have hUeq : U κ N = fun x : ParticleSpace 1 N =>
      ∑ i, (fun _ : Torus 1 => κ * A / 2) (x i) + (1 / (2 * (N : ℝ))) * ∑ i, ∑ j, F (x i) (x j) := by
    funext x
    have h := hamiltonian_eq κ N x
    have h2 : particleHamiltonian (kernelData κ) N x =
        (1 / (2 * (N : ℝ))) * ∑ i, ∑ j, F (x i) (x j) := by
      rw [hHeq]; simp
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [h2] at h
    linarith
  rw [← hHeq] at hcore0
  rw [← hUeq] at hcore
  have hUc : MemLp (U κ N) ⊤ (particleHaar 1 N) := by
    obtain ⟨C, hC⟩ := (isCompact_univ (X := ParticleSpace 1 N)).exists_bound_of_continuousOn
      (continuous_U κ N).continuousOn
    exact MemLp.of_bound (continuous_U κ N).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ _))
  have hGU : IsParticleHaarWeakGradient N (U κ N) (roughForce κ N) := hcore
  have hGH : IsParticleHaarWeakGradient N (particleHamiltonian (kernelData κ) N)
      (roughForce κ N) := hcore0
  exact ⟨hUc, hGU, ⟨_, hGU⟩, (isParticleWeakGradient_iff _ _ _ _).2 hGU, hGH,
    (isParticleWeakGradient_iff _ _ _ _).2 hGH⟩


end DGPS.Examples.PositiveH1.Particle
