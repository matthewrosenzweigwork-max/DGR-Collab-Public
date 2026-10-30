import DGPS.Examples.ThreeSpeciesCircle.GaussianReferenceGram
import DGPS.Frontier.STR029.T35

/-! A genuine full-weak reference gap on the kernel of the two elementary
first-feature functionals. This excludes a first reference eigendirection
annihilated by both features, without asserting that either is an eigenfunction. -/

noncomputable section
open MeasureTheory Filter Set Real
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem haar_first_penalty (f g : ℝ → ℝ)
    (hfg : IsPeriodicWeakDerivative_STR02933 f g) (h0 : normInt_STR02933 f = 0) :
    4 * normInt_STR02933 (fun t => f t ^ 2) ≤ normInt_STR02933 (fun t => g t ^ 2) +
      6 * ((normInt_STR02933 (fun t => f t * Real.cos t)) ^ 2 +
        (normInt_STR02933 (fun t => f t * Real.sin t)) ^ 2) := by
  obtain ⟨⟨hA, hL⟩, ⟨hB, hD⟩⟩ :=
    str029_34_parseval_adapter_periodic_weak_domain_parseval f g hfg h0
  let A : ℕ → ℝ := fun n => cosCoeff_STR02933 f (n + 1) ^ 2 + sinCoeff_STR02933 f (n + 1) ^ 2
  let B : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) ^ 2 * A n
  change Summable A at hA
  change Summable B at hB
  change normInt_STR02933 (fun t => f t ^ 2) = (1 / 2) * ∑' n, A n at hL
  change normInt_STR02933 (fun t => g t ^ 2) = (1 / 2) * ∑' n, B n at hD
  have hAt : Summable (fun n => A (n + 1)) := hA.comp_injective (by
    intro m n he
    change m + 1 = n + 1 at he
    omega)
  have hBt : Summable (fun n => B (n + 1)) := hB.comp_injective (by
    intro m n he
    change m + 1 = n + 1 at he
    omega)
  have ht : 4 * (∑' n, A (n + 1)) ≤ ∑' n, B (n + 1) := by
    rw [← tsum_mul_left]
    apply Summable.tsum_le_tsum _ (hAt.mul_left 4) hBt
    intro n
    have hn : (2 : ℝ) ≤ ((n + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n + 1 + 1 by omega)
    have hfreq : (4 : ℝ) ≤ ((n + 1 + 1 : ℕ) : ℝ) ^ 2 := by nlinarith only [hn]
    have hAn : 0 ≤ A (n + 1) := by dsimp [A]; positivity
    exact mul_le_mul_of_nonneg_right hfreq hAn
  have hAs := hA.sum_add_tsum_nat_add 1
  have hBs := hB.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hAs hBs
  have hB0 : B 0 = A 0 := by simp [B]
  rw [hB0] at hBs
  have hA0 : A 0 = 4 * ((normInt_STR02933 (fun t => f t * Real.cos t)) ^ 2 +
      (normInt_STR02933 (fun t => f t * Real.sin t)) ^ 2) := by
    simp only [A, zero_add, cosCoeff_STR02933, sinCoeff_STR02933, Nat.cast_one, one_mul]
    ring
  nlinarith only [ht, hAs, hBs, hL, hD, hA0]

private theorem weighted_zero_haar_moment (q f φ : ℝ → ℝ)
    (hq : Continuous q) (hf : MemLp f 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hφ : Continuous φ) (hφb : ∀ t, |φ t| ≤ 1)
    (hqb : ∀ t, |q t - 1| ≤ (1 / 10 : ℝ))
    (hzero : normInt_STR02933 (fun t => f t * φ t * q t) = 0) :
    (normInt_STR02933 (fun t => f t * φ t)) ^ 2 ≤
      (1 / 100 : ℝ) * normInt_STR02933 (fun t => f t ^ 2) := by
  let ψ : ℝ → ℝ := fun t => φ t * (1 - q t)
  have hψ : Continuous ψ := by dsimp [ψ]; fun_prop
  have hψb (t : ℝ) : |ψ t| ≤ (1 / 10 : ℝ) := by
    dsimp only [ψ]
    rw [abs_mul, abs_sub_comm]
    exact (mul_le_mul (hφb t) (hqb t) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)
  have hψ2 : normInt_STR02933 (fun t => ψ t ^ 2) ≤ (1 / 100 : ℝ) := by
    have hp (t : ℝ) : ψ t ^ 2 ≤ (1 / 100 : ℝ) := by
      have hs := pow_le_pow_left₀ (abs_nonneg (ψ t)) (hψb t) 2
      norm_num at hs
      exact hs
    calc
      _ ≤ normInt_STR02933 (fun _ => (1 / 100 : ℝ)) :=
        normInt_mono_STR02935 (integrable_continuous_STR02934 (hψ.pow 2))
          (integrable_continuous_STR02934 continuous_const) hp
      _ = _ := normInt_const_STR02935 _
  have he : normInt_STR02933 (fun t => f t * ψ t) =
      normInt_STR02933 (fun t => f t * φ t) := by
    have hfun : (fun t => f t * ψ t) = fun t => f t * φ t - f t * φ t * q t := by
      funext t; dsimp [ψ]; ring
    rw [hfun, normInt_sub_STR02902]
    · rw [hzero, sub_zero]
    · exact integrable_mul_memLp_STR02935 hf (memLp_of_continuous_STR02935 hφ)
    · exact integrable_cmul_STR02935 hq hf (memLp_of_continuous_STR02935 hφ) |>.congr
        (Eventually.of_forall fun t => by ring)
  have hcs := cs_normInt_STR02935 hf (memLp_of_continuous_STR02935 hψ)
  rw [he] at hcs
  have hL : 0 ≤ normInt_STR02933 (fun t => f t ^ 2) := normInt_nonneg_STR02935 fun t => sq_nonneg _
  exact hcs.trans ((mul_le_mul_of_nonneg_left hψ2 hL).trans_eq (by ring))

/-- The actual reference has a separated angular gap on the full periodic weak
H1 domain with zero Haar mean and zero actual weighted first-feature moments. -/
theorem threefold_reference_constrained_gap_angular (h : ℝ) (hh : |h| ≤ 1 / 1000)
    (f g : ℝ → ℝ) (hfg : IsPeriodicWeakDerivative_STR02933 f g)
    (h0 : normInt_STR02933 f = 0)
    (hc : normInt_STR02933 (fun t => f t * Real.cos t * qT_STR02904 h t) = 0)
    (hs : normInt_STR02933 (fun t => f t * Real.sin t * qT_STR02904 h t) = 0) :
    2 * normInt_STR02933 (fun t => f t ^ 2 * qT_STR02904 h t) ≤
      normInt_STR02933 (fun t => g t ^ 2 * qT_STR02904 h t) := by
  have hq := continuous_qT_STR02904 h
  have hnear (t : ℝ) : |qT_STR02904 h t - 1| ≤ (1 / 10 : ℝ) := by
    have ht := (str029_04_reference_symmetries_quantitative_density_bounds_bounds h hh).2.1 t
    linarith only [ht, hh]
  have hqlo (t : ℝ) : (9 / 10 : ℝ) ≤ qT_STR02904 h t := by have ht := (abs_le.mp (hnear t)).1; linarith
  have hqhi (t : ℝ) : qT_STR02904 h t ≤ (11 / 10 : ℝ) := by have ht := (abs_le.mp (hnear t)).2; linarith
  have hc2 := weighted_zero_haar_moment (qT_STR02904 h) f Real.cos hq hfg.1.2
    Real.continuous_cos Real.abs_cos_le_one hnear hc
  have hs2 := weighted_zero_haar_moment (qT_STR02904 h) f Real.sin hq hfg.1.2
    Real.continuous_sin Real.abs_sin_le_one hnear hs
  have hFourier := haar_first_penalty f g hfg h0
  have hL : 0 ≤ normInt_STR02933 (fun t => f t ^ 2) := normInt_nonneg_STR02935 fun t => sq_nonneg _
  have hf2 := integrable_sq_STR02935 hfg.1.2
  have hg2 := integrable_sq_STR02935 hfg.2.1.2
  have hqf := integrable_cmul_STR02935 hq hfg.1.2 hfg.1.2
  have hqg := integrable_cmul_STR02935 hq hfg.2.1.2 hfg.2.1.2
  have hF : normInt_STR02933 (fun t => f t ^ 2 * qT_STR02904 h t) ≤
      (11 / 10 : ℝ) * normInt_STR02933 (fun t => f t ^ 2) := by
    rw [← normInt_mul_const_STR02933]
    apply normInt_mono_STR02935
    · exact hqf.congr (Eventually.of_forall fun t => by ring)
    · exact hf2.const_mul _
    · intro t; exact mul_le_mul_of_nonneg_left (hqhi t) (sq_nonneg _) |>.trans_eq (by ring)
  have hD : (9 / 10 : ℝ) * normInt_STR02933 (fun t => g t ^ 2) ≤
      normInt_STR02933 (fun t => g t ^ 2 * qT_STR02904 h t) := by
    rw [← normInt_mul_const_STR02933]
    apply normInt_mono_STR02935
    · exact hg2.const_mul _
    · exact hqg.congr (Eventually.of_forall fun t => by ring)
    · intro t; exact (mul_le_mul_of_nonneg_right (hqlo t) (sq_nonneg _)).trans_eq (by ring)
  nlinarith only [hc2, hs2, hFourier, hL, hF, hD]

end DGPS.Examples.ThreeSpeciesCircle
