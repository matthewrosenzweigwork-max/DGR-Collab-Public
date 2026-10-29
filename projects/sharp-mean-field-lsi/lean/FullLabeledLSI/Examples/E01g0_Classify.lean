import FullLabeledLSI.Examples.E01g0_Circle
import SharpSymmetricLSI.Paper.RefSpectrum2
import SharpSymmetricLSI.Paper.RefSpectrum6
import SharpSymmetricLSI.Paper.RefSpectrum17
import SharpSymmetricLSI.Paper.EntFinite

/-!
# Lane D, helper E01g0: classification of reference eigenbases of Haar measure on the circle

For `IsRefEigenbasis (haar 1) e lam` and `j ≥ 1` there is `N_j ≥ 1` with `lam j = aCos N_j²` and
`e_j` has Fourier support in `{±N_j}`; every `N ≥ 1` occurs.  (Task A, steps 1-3 of PLAN.md.)
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped Real ComplexConjugate ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

/-- The index function `fun _ : Fin 1 => n`. -/
def K1 (n : ℤ) : Fin 1 → ℤ := fun _ => n

theorem K1_zero : K1 0 = 0 := rfl

theorem K1_neg (n : ℤ) : -K1 n = K1 (-n) := rfl

theorem K1_eq_iff (n m : ℤ) : K1 n = K1 m ↔ n = m := by
  constructor
  · intro h; exact congrFun h 0
  · intro h; rw [h]

theorem eq_K1 (k : Fin 1 → ℤ) : k = K1 (k 0) := by
  funext i; fin_cases i; rfl

theorem K1_ne_zero {n : ℤ} (hn : n ≠ 0) : K1 n ≠ 0 := by
  intro h; exact hn (congrFun h 0)

theorem cf_zero_eq (u : Torus 1 → ℝ) : cf u 0 = ((∫ y, u y : ℝ) : ℂ) := by
  simp only [cf, SharpLSI.mFourierCoeff_eq_integral, neg_zero, mFourier_zero, ContinuousMap.one_apply,
    smul_eq_mul, one_mul]
  exact integral_complex_ofReal

theorem mFourier_K1 (n : ℤ) (x : Torus 1) : mFourier (K1 n) x = fourier n (x 0) := by
  simp [mFourier, K1]

theorem chat_eq (C : Torus 1 → ℝ) (n : ℤ) : chat C n = (cf C (K1 n)).re := by
  unfold chat
  congr 1
  simp only [cf, SharpLSI.mFourierCoeff_eq_integral, smul_eq_mul]
  congr 1; funext x
  rw [K1_neg, mFourier_K1]

theorem cf_one (m : Fin 1 → ℤ) :
    cf (fun _ : Torus 1 => (1 : ℝ)) m = if m = 0 then 1 else 0 := by
  simp only [cf, SharpLSI.mFourierCoeff_eq_integral, smul_eq_mul, Complex.ofReal_one, mul_one]
  rw [integral_mFourier']
  simp

theorem natAbs_sq_real (n : ℤ) : ((n.natAbs : ℕ) : ℝ) ^ 2 = (n : ℝ) ^ 2 := by
  rw [← Int.cast_natCast, ← Int.cast_pow, ← Int.cast_pow, Int.natAbs_sq]

/-- Step 1: eigen equation in Fourier form. -/
theorem eigen_coeff {e : ℕ → Torus 1 → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (haar 1) e lam)
    (j : ℕ) (n : ℤ) : ((aCos : ℂ) * (n : ℂ) ^ 2 - (lam j : ℂ)) * cf (e j) (K1 n) = 0 := by
  have hH := he.memH1 j
  have hw : IsWeakGrad (e j) (weakGrad (e j)) := isWeakGrad_weakGrad hH.1
  have h1 : (volume : Measure (Torus 1)) ≤ ENNReal.ofReal 1 • volume := by simp
  have hint : Integrable (e j) volume := hH.2.1.integrable one_le_two
  have hG : ∀ k : Fin 1, Integrable (fun y => weakGrad (e j) y k) volume := fun k =>
    (memLp_grad_vol (P := volume) (a := 1) (b := 1) h1 h1 hH k).integrable one_le_two
  have hg : Integrable (fun y => lam j * e j y) volume := hint.const_mul _
  have heq : ∀ Θ : (Fin 1 → ℝ) → ℝ, ContDiff ℝ ∞ Θ → IsPer Θ →
      ∫ y, ∑ k, weakGrad (e j) y k * Dk Θ k (secT y) = ∫ y, (lam j * e j y) * Θ (secT y) := by
    intro Θ hΘ hp
    have hco : (fun y => Θ (secT y)) ∘ liftT = Θ := by funext x; exact hp.secT_liftT x
    have hφ : MemH1 volume (fun y => Θ (secT y)) := memH1_of_contDiff (by rw [hco]; exact hΘ)
    have h := he.eigen j _ hφ
    have hae := weakGrad_ae_eq_of_contDiff (f := fun y => Θ (secT y))
      (by rw [hco]; exact hΘ.of_le (by exact_mod_cast le_top))
    have e1 : ∫ x, ∑ k, weakGrad (e j) x k * weakGrad (fun y => Θ (secT y)) x k ∂haar 1 =
        ∫ y, ∑ k, weakGrad (e j) y k * Dk Θ k (secT y) := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with y hy
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hy]
      simp only [hco, Dk]
    rw [← e1, h, ← integral_const_mul]
    congr 1; funext y; ring
  have key := cf_of_weak_eq hw hint hG hg heq (K1 n)
  have e2 : cf (fun y => lam j * e j y) (K1 n) = (lam j : ℂ) * cf (e j) (K1 n) := by
    simp only [cf, SharpLSI.mFourierCoeff_eq_integral, smul_eq_mul, Complex.ofReal_mul]
    rw [← integral_const_mul]
    congr 1; funext y; ring
  have e3 : ∑ i : Fin 1, ((K1 n i : ℤ) : ℂ) ^ 2 = (n : ℂ) ^ 2 := by simp [K1]
  rw [show UnitAddTorus.mFourierCoeff (fun y => ((lam j * e j y : ℝ) : ℂ)) (K1 n) =
    cf (fun y => lam j * e j y) (K1 n) from rfl, e2, e3] at key
  unfold aCos
  push_cast
  linear_combination (-1 : ℂ) * key

/-- Fourier support of an eigenfunction: `lam j = aCos N²`, `e j` supported on `±N`. -/
theorem exists_N {e : ℕ → Torus 1 → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (haar 1) e lam)
    {j : ℕ} (hj : 1 ≤ j) :
    ∃ N : ℕ, 1 ≤ N ∧ lam j = aCos * (N : ℝ) ^ 2 ∧
      ∀ k : Fin 1 → ℤ, cf (e j) k ≠ 0 → k = K1 N ∨ k = -K1 N := by
  have hH := he.memH1 j
  have hL2 : MemLp (e j) 2 volume := hH.2.1
  have hP := hasSum_sq_mFourierCoeff_real hL2
  have hnorm : ∫ y, e j y ^ 2 = 1 := by
    have := he.orthonormal j j
    simp only [if_true] at this
    simpa [sq] using this
  have hmean : cf (e j) 0 = 0 := by
    rw [cf_zero_eq]
    have := he.orthonormal 0 j
    rw [if_neg (by omega), he.zero] at this
    simp only [one_mul] at this
    simp [this]
  -- some nonzero coefficient
  have hex : ∃ k : Fin 1 → ℤ, cf (e j) k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    simp only [hcon, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hP
    have := hasSum_zero.unique hP
    rw [hnorm] at this
    exact zero_ne_one this
  obtain ⟨k0, hk0⟩ := hex
  have hk0ne : k0 ≠ 0 := fun h => hk0 (by rw [h]; exact hmean)
  set n := k0 0 with hn
  have hkn : k0 = K1 n := eq_K1 k0
  have hn0 : n ≠ 0 := fun h => hk0ne (by rw [hkn, h]; rfl)
  have hl : lam j = aCos * (n : ℝ) ^ 2 := by
    have h := eigen_coeff he j n
    rw [← hkn] at h
    rcases mul_eq_zero.mp h with h | h
    · have h' : ((aCos * (n : ℝ) ^ 2 - lam j : ℝ) : ℂ) = 0 := by push_cast; exact h
      have := Complex.ofReal_eq_zero.mp h'
      linarith
    · exact absurd h hk0
  refine ⟨n.natAbs, Int.natAbs_pos.mpr hn0, ?_, ?_⟩
  · rw [hl, natAbs_sq_real]
  · intro k hk
    have hkm : k = K1 (k 0) := eq_K1 k
    have h := eigen_coeff he j (k 0)
    rw [← hkm] at h
    have h2 : (aCos : ℂ) * ((k 0 : ℤ) : ℂ) ^ 2 - (lam j : ℂ) = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h hk
    have h3 : aCos * ((k 0 : ℤ) : ℝ) ^ 2 = lam j := by
      have : ((aCos * ((k 0 : ℤ) : ℝ) ^ 2 : ℝ) : ℂ) = (lam j : ℂ) := by push_cast; linear_combination h2
      exact_mod_cast this
    have hapos : 0 < aCos := by unfold aCos; positivity
    have h4 : ((k 0 : ℤ) : ℝ) ^ 2 = (n : ℝ) ^ 2 := by
      have : aCos * ((k 0 : ℤ) : ℝ) ^ 2 = aCos * (n : ℝ) ^ 2 := by rw [h3, hl]
      exact mul_left_cancel₀ hapos.ne' this
    have h5 : (k 0) ^ 2 = n ^ 2 := by exact_mod_cast h4
    have h6 := sq_eq_sq_iff_eq_or_eq_neg.mp h5
    have h7 := Int.natAbs_eq n
    generalize n.natAbs = N at h7 ⊢
    rcases h6 with h6 | h6
    · rcases h7 with h7 | h7
      · left; rw [hkm, h6, h7]
      · right; rw [hkm, K1_neg, h6, h7]
    · rcases h7 with h7 | h7
      · right; rw [hkm, K1_neg, h6, h7]
      · left; rw [hkm, h6, h7]; simp

/-- Every `N ≥ 1` occurs as the frequency of some eigenfunction. -/
theorem exists_index {e : ℕ → Torus 1 → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (haar 1) e lam)
    (N : ℕ) (hN : 1 ≤ N) : ∃ j, 1 ≤ j ∧ lam j = aCos * (N : ℝ) ^ 2 := by
  by_contra H
  push_neg at H
  set f : Torus 1 → ℝ := fun y => 2 * ((1 : ℂ) * mFourier (K1 N) y).re with hf
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hk : K1 (N : ℤ) ≠ 0 := K1_ne_zero hNz
  have hfc : Continuous f := by
    simp only [hf]
    exact continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul (mFourier _).continuous))
  have hfL : MemLp f 2 volume := hfc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcf : ∀ m, cf f m = (if m = K1 N then 1 else 0) + (if m = -K1 N then 1 else 0) := by
    intro m
    have := cf_two_re 1 (K1 N) hk m
    simp only [map_one] at this
    exact this
  have horth : ∀ j, ∫ x, f x * e j x = 0 := by
    intro j
    have hP := hasSum_prod_cf_real hfL ((he.memH1 j).2.1)
    have hall : ∀ m, conj (cf f m) * cf (e j) m = 0 := by
      intro m
      by_cases h : cf f m = 0
      · simp [h]
      · by_cases h2 : cf (e j) m = 0
        · simp [h2]
        · exfalso
          have hm : m = K1 N ∨ m = -K1 N := by
            rw [hcf m] at h
            by_cases h1 : m = K1 N
            · exact Or.inl h1
            · by_cases h3 : m = -K1 N
              · exact Or.inr h3
              · simp [h1, h3] at h
          have hmZ : ∃ a : ℤ, m = K1 a ∧ (a = N ∨ a = -N) := by
            rcases hm with hm | hm
            · exact ⟨N, hm, Or.inl rfl⟩
            · exact ⟨-N, by rw [hm, K1_neg], Or.inr rfl⟩
          obtain ⟨a, ha, haN⟩ := hmZ
          rcases Nat.eq_zero_or_pos j with hj | hj
          · subst hj
            have hz : cf (e 0) m = if m = 0 then 1 else 0 := by
              rw [he.zero]; exact cf_one m
            have hm0 : m ≠ 0 := by
              rw [ha]; apply K1_ne_zero; omega
            rw [hz, if_neg hm0] at h2
            exact h2 rfl
          · obtain ⟨M, hM1, hlam, hsupp⟩ := exists_N he hj
            have hs := hsupp m h2
            have hsZ : ∃ b : ℤ, m = K1 b ∧ (b = M ∨ b = -M) := by
              rcases hs with hs | hs
              · exact ⟨M, hs, Or.inl rfl⟩
              · exact ⟨-M, by rw [hs, K1_neg], Or.inr rfl⟩
            obtain ⟨b, hb, hbM⟩ := hsZ
            have hab : a = b := (K1_eq_iff _ _).mp (ha.symm.trans hb)
            have hMN : M = N := by omega
            exact H j hj (by rw [hlam, hMN])
    simp only [hall] at hP
    have := hasSum_zero.unique hP
    exact_mod_cast this.symm
  have hz := he.complete f hfL horth
  have h1 : cf f (K1 N) = 1 := by
    rw [hcf, if_pos rfl, if_neg (ne_neg_self hk)]; simp
  have h2 : cf f (K1 N) = 0 := by
    simp only [cf, SharpLSI.mFourierCoeff_eq_integral]
    rw [integral_congr_ae (g := fun _ => (0 : ℂ))]
    · simp
    · filter_upwards [hz] with y hy
      simp [hy]
  rw [h1] at h2
  exact one_ne_zero h2

end SharpLSI.FL.Ex.LaneD
