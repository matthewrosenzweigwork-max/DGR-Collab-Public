import DGPS.FiniteN.AnisotropicQuarticPhysicalStrip

/-! Actual normalized enlarged-strip mass at the quartic scale. -/

open MeasureTheory Filter Topology Set
open DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066

namespace DGPS.FiniteN

private theorem quartic_strip_scale_budget (N k : ℝ) (hN : 0 < N) :
    N * (k * N ^ (-(1 / 4 : ℝ))) ^ 4 = k ^ 4 := by
  have hs : (N ^ (-(1 / 4 : ℝ))) ^ 4 = N⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num [Real.rpow_neg_one]
  rw [mul_pow, hs]
  field_simp [hN.ne']
  <;> ring

private theorem quartic_strip_gaussian_scale (N c : ℝ) (hN : 0 < N) (hc : 0 < c) :
    Real.sqrt (Real.pi / (N * c)) = Real.sqrt (Real.pi / c) * N ^ (-(1 / 2 : ℝ)) := by
  rw [show Real.pi / (N * c) = (Real.pi / c) * N⁻¹ by
      field_simp [hN.ne', hc.ne']
      <;> ring,
    Real.sqrt_mul (by positivity : 0 ≤ Real.pi / c), Real.sqrt_inv,
    Real.sqrt_eq_rpow N, Real.rpow_neg hN.le]

private theorem quartic_strip_normalization_power (N : ℝ) (hN : 0 < N) :
    N ^ (1 / 4 : ℝ) = N * N ^ (-(1 / 4 : ℝ)) * N ^ (-(1 / 2 : ℝ)) := by
  calc
    _ = N ^ (((1 : ℝ) + -(1 / 4 : ℝ)) + -(1 / 2 : ℝ)) := by norm_num
    _ = _ := by rw [Real.rpow_add hN, Real.rpow_add hN, Real.rpow_one]

/-- A fixed longitudinal strip and every fixed multiple of the quartic transverse
width have normalized mass at most a constant times `N^(1/4)*exp(-N*Delta)`.
The actual unique minimum and positive gap are constructed internally and retained. -/
theorem quartic_normalized_rare_strip_upper :
    ∃ t δ : ℝ, 1 < t ∧ 0 < δ ∧ δ ≤ 1 ∧
      (∀ w, quarticPsi_FIN066 !₂[t, 0] ≤ quarticPsi_FIN066 w) ∧
      (∀ w, quarticPsi_FIN066 w ≤ quarticPsi_FIN066 !₂[t, 0] → w = !₂[t, 0]) ∧
      0 < quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0] ∧
      ∀ k : ℝ, 0 < k → ∃ C N0 : ℝ, 0 < C ∧ 1 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
        ((imsEta N quarticPsi_FIN066)
          (quarticRareStrip δ (k * N ^ (-(1 / 4 : ℝ))))).toReal ≤
            C * N ^ (1 / 4 : ℝ) * Real.exp
              (-(N * (quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0]))) := by
  obtain ⟨δ, c, K, hδ, hδ1, hc, hK, hraw⟩ := quartic_physical_rare_strip_raw_upper
  obtain ⟨t, ht, hroot, hmin, huniq, hcrit, hH, hnorm, htail⟩ := quartic_auxiliary_laplace_data
  obtain ⟨L, hL, A, hA, M, hM, hnorm⟩ := hnorm
  have hgap : 0 < quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0] := by
    have hle := hmin !₂[-4, 0]
    have hne : quarticPsi_FIN066 !₂[-4, 0] ≠ quarticPsi_FIN066 !₂[t, 0] := by
      intro he
      have hx := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) (huniq !₂[-4, 0] he.le)
      change (-4 : ℝ) = t at hx
      linarith
    exact sub_pos.mpr (lt_of_le_of_ne hle hne.symm)
  refine ⟨t, δ, ht, hδ, hδ1, hmin, huniq, hgap, fun k hk => ?_⟩
  have hlim : Tendsto (fun N : ℝ => (k * N ^ (-(1 / 4 : ℝ))) ^ 2) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul k).pow 2
    simpa only [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h
  obtain ⟨Mδ, hMδ⟩ := eventually_atTop.mp
    ((hlim.eventually (gt_mem_nhds hδ)).mono fun N h => h.le)
  let C := Real.exp (K * k ^ 4) * Real.sqrt (Real.pi / c) * (2 * k) / L
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, max M Mδ, hC, hM.trans (le_max_left _ _), fun N hN => ?_⟩
  have hNM : M ≤ N := (le_max_left _ _).trans hN
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one (hM.trans hNM)
  let s := k * N ^ (-(1 / 4 : ℝ))
  have hs : 0 ≤ s := mul_nonneg hk.le (Real.rpow_pos_of_pos hNp _).le
  have hsδ : s ^ 2 ≤ δ := hMδ N ((le_max_right _ _).trans hN)
  have hb := hraw N s (k ^ 4) hNp hs (by positivity) hsδ
    (quartic_strip_scale_budget N k hNp).le
  have hZN := (hnorm N hNM).1
  have hZ := quartic_partition_pos N hNp
  let E := Real.exp (-(N * (quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0])))
  have hExp : E * Real.exp (-(N * quarticPsi_FIN066 !₂[t, 0])) =
      Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0])) := by
    dsimp only [E]
    rw [← Real.exp_add]
    congr 1
    ring
  have hAlg : (C * N ^ (1 / 4 : ℝ) * E) *
      (L * N⁻¹ * Real.exp (-(N * quarticPsi_FIN066 !₂[t, 0]))) =
        (Real.exp (K * k ^ 4) * Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0]))) *
          Real.sqrt (Real.pi / (N * c)) * (2 * s) := by
    rw [quartic_strip_normalization_power N hNp, quartic_strip_gaussian_scale N c hNp hc]
    calc
      _ = (Real.exp (K * k ^ 4) * Real.sqrt (Real.pi / c) * (2 * s) *
          N ^ (-(1 / 2 : ℝ))) * (E * Real.exp (-(N * quarticPsi_FIN066 !₂[t, 0]))) := by
        dsimp only [C, s]
        field_simp [hL.ne', hNp.ne']
        <;> ring
      _ = _ := by rw [hExp]; ring
  have hSm : MeasurableSet (quarticRareStrip δ s) := by
    exact (isClosed_le (show Continuous (fun w : EuclideanSpace ℝ (Fin 2) => |w 0 + 4|) by fun_prop)
      (continuous_const (y := δ))).measurableSet.inter
      (isClosed_le (show Continuous (fun w : EuclideanSpace ℝ (Fin 2) => |w 1|) by fun_prop)
        (continuous_const (y := s))).measurableSet
  rw [TiltedXY.Fin049.imsEta_real_FIN049 N quarticPsi_FIN066 hZ (quarticRareStrip δ s) hSm]
  apply (div_le_iff₀ hZ).mpr
  exact hb.trans (hAlg.symm.le.trans
    (mul_le_mul_of_nonneg_left hZN (by positivity : 0 ≤ C * N ^ (1 / 4 : ℝ) * E)))

end DGPS.FiniteN
