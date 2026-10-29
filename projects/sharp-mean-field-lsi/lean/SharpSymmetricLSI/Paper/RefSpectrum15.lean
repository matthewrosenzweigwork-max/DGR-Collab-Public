import SharpSymmetricLSI.Paper.RefSpectrum14

/-!
# R23 (6.1), part 15: uniform `C^{1,β}` bounds for the smoothed eigenfunctions

For `N = 2^{m+1} > d`, Morrey's inequality, the second-derivative bound and the moment bounds give,
uniformly in `t > 0`: `|∂ₖe_t(x) - ∂ₖe_t(y)| ≤ K(1+λ)^q dist(x,y)^{1-d/N}` and
`|∂ₖe_t| ≤ K(1+λ)^q` (`holder_bound`).
-/

open MeasureTheory Filter Topology Complex
open scoped ENNReal Real ContDiff NNReal
open UnitAddTorus

namespace SharpLSI

variable {d : ℕ} {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C) (hρc : Continuous ρ)
  {Lσ : ℝ≥0} (hσ : LipschitzWith Lσ (recipD ρ ∘ liftT))
include hρ hρc hσ

omit hρ hρc hσ in
theorem rpow_inv_le_one_add {x : ℝ} (hx : 0 ≤ x) {N : ℝ} (hN : 1 ≤ N) : x ^ (1 / N) ≤ 1 + x := by
  rcases le_total x 1 with h | h
  · have := Real.rpow_le_one hx h (by positivity : (0 : ℝ) ≤ 1 / N)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h (by rw [div_le_one (by linarith)]; exact hN :
      1 / N ≤ 1)
    rw [Real.rpow_one] at this
    linarith

/-- **Uniform Hölder and sup bounds for `∂ₖe_t`.** -/
theorem holder_bound (hd : 1 ≤ d) (m : ℕ) (hN : (d : ℝ) < (2 : ℝ) ^ (m + 1)) :
    ∃ K : ℝ, ∃ q : ℕ, 0 ≤ K ∧ ∀ e lam, IsEig (densMeasure ρ) e lam → ∀ t, 0 < t →
      ∀ (k : Fin d) (x y : Torus d),
        |dpart (heatT t e) k x - dpart (heatT t e) k y| ≤
          K * (1 + lam) ^ q * dist x y ^ (1 - (d : ℝ) / (2 : ℝ) ^ (m + 1)) := by
  haveI := hρ.isProb
  obtain ⟨Kg, qg, hKg, hmom⟩ := moments hρ hρc hσ hd m
  obtain ⟨A, hA0, hA⟩ := heat_d2_bound (ι := Fin d) m
  set N : ℕ := 2 ^ (m + 1)
  have hNr : ((2 : ℝ) ^ (m + 1)) = (N : ℝ) := by simp [N]
  rw [hNr] at hN ⊢
  have hN2 : 2 ≤ N := by
    have : 2 ^ 1 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [N] using this
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNd : (0 : ℝ) < N - d := by linarith
  set Kc : ℝ := 2 * N / (N - d) * (1 + d ^ N * A ^ N * Kg)
  refine ⟨Kc, qg, by positivity, fun e lam h t ht k x y => ?_⟩
  have hlam := h.lam_nonneg hρ
  have hev : MemLp e 2 volume := memLp_vol hρ.haar_le_smul h.1
  have hg := memLp_srcG hρ hρc hσ h.1 lam
  have hcf := cf_srcG hρ hρc hσ h.1 h.2.2
  have h2 := heat_smooth2 hev ht
  set V := dpart (heatT t e) k
  have hV1 : ContDiff ℝ 1 (V ∘ liftT) := contDiff_dpart (n := 1) h2 k
  have hmor := morrey_torus hV1 (by simpa using hN) hN2 x y
  simp only [Fintype.card_fin] at hmor
  have hK1 : 0 ≤ 2 * dist x y ^ (1 - (d : ℝ) / N) * (N / (N - d)) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg dist_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) hNd.le)
  -- the second-derivative integral
  set Jr : ℝ := d ^ N * A ^ N * (Kg * (1 + lam) ^ qg)
  have hJr : 0 ≤ Jr := by positivity
  have hgm := (hmom e lam h).2
  have hNc : ((2 ^ (m + 1) : ℕ) : ℝ) = (N : ℝ) := rfl
  have hJ : ∫⁻ z, ENNReal.ofReal (∑ i, |dpart V i z|) ^ (N : ℝ) ≤ ENNReal.ofReal Jr := by
    have hpt : ∀ z, ENNReal.ofReal (∑ i, |dpart V i z|) ^ (N : ℝ) ≤
        ENNReal.ofReal ((d : ℝ) ^ (N - 1)) * ∑ i, ‖dpart V i z‖ₑ ^ (N : ℝ) := by
      intro z
      rw [ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Nat.cast_nonneg _)]
      have := Real.rpow_sum_le_const_mul_sum_rpow (s := Finset.univ)
        (f := fun i => dpart V i z) (p := (N : ℝ)) hN1
      simp only [Finset.card_univ, Fintype.card_fin] at this
      rw [show ((d : ℕ) : ℝ) ^ ((N : ℝ) - 1) = (d : ℝ) ^ (N - 1) by
        rw [← Real.rpow_natCast, Nat.cast_sub (by omega)]; push_cast; rfl] at this
      refine (ENNReal.ofReal_le_ofReal this).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _)
        (Nat.cast_nonneg _)]
    have hVi : ∀ i, Continuous (dpart V i) := fun i =>
      continuous_of_liftT' (contDiff_dpart (n := 0) hV1 i).continuous
    calc ∫⁻ z, ENNReal.ofReal (∑ i, |dpart V i z|) ^ (N : ℝ)
        ≤ ∫⁻ z, ENNReal.ofReal ((d : ℝ) ^ (N - 1)) * ∑ i, ‖dpart V i z‖ₑ ^ (N : ℝ) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal ((d : ℝ) ^ (N - 1)) * ∑ i, ∫⁻ z, ‖dpart V i z‖ₑ ^ (N : ℝ) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_finset_sum' _ fun i _ => ((hVi i).measurable.enorm.pow_const _).aemeasurable]
      _ ≤ ENNReal.ofReal ((d : ℝ) ^ (N - 1)) *
            ∑ _i : Fin d, ENNReal.ofReal A ^ (N : ℝ) * ENNReal.ofReal (Kg * (1 + lam) ^ qg) := by
          gcongr with i
          have h1 := hA e (srcG ρ lam e) hev hg hcf t ht k i
          rw [hNr] at h1
          rw [hNc] at hgm
          exact h1.trans (mul_le_mul' le_rfl hgm)
      _ = ENNReal.ofReal Jr := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg hA0
            (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul
            (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          simp only [Jr, Real.rpow_natCast]
          rw [show (d : ℝ) ^ N = (d : ℝ) ^ (N - 1) * d by
            rw [← pow_succ]; congr 1; omega]
          ring
  -- assemble
  have hJ' : (∫⁻ z, ENNReal.ofReal (∑ i, |dpart V i z|) ^ (N : ℝ)) ^ (1 / (N : ℝ)) ≤
      ENNReal.ofReal (Jr ^ (1 / (N : ℝ))) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hJr (by positivity)]
    exact ENNReal.rpow_le_rpow hJ (by positivity)
  have hfin := hmor.trans (mul_le_mul' le_rfl hJ')
  rw [← ENNReal.ofReal_mul hK1, ← ofReal_norm_eq_enorm, Real.norm_eq_abs,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK1 (Real.rpow_nonneg hJr _))] at hfin
  have hpoly : Jr ^ (1 / (N : ℝ)) ≤ (1 + d ^ N * A ^ N * Kg) * (1 + lam) ^ qg := by
    have h1 := rpow_inv_le_one_add hJr hN1
    have h2 : (1 : ℝ) ≤ (1 + lam) ^ qg := one_le_pow₀ (by linarith)
    have : Jr = d ^ N * A ^ N * Kg * (1 + lam) ^ qg := by simp only [Jr]; ring
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ d ^ N * A ^ N * Kg) (by linarith : (0 : ℝ) ≤ (1 + lam) ^ qg - 1)]
  refine hfin.trans ?_
  have hdist : 0 ≤ dist x y ^ (1 - (d : ℝ) / N) := Real.rpow_nonneg dist_nonneg _
  calc 2 * dist x y ^ (1 - (d : ℝ) / N) * (N / (N - d)) * Jr ^ (1 / (N : ℝ))
      = 2 * N / (N - d) * Jr ^ (1 / (N : ℝ)) * dist x y ^ (1 - (d : ℝ) / N) := by ring
    _ ≤ 2 * N / (N - d) * ((1 + d ^ N * A ^ N * Kg) * (1 + lam) ^ qg) *
          dist x y ^ (1 - (d : ℝ) / N) := by gcongr
    _ = Kc * (1 + lam) ^ qg * dist x y ^ (1 - (d : ℝ) / N) := by simp only [Kc]; ring

end SharpLSI
