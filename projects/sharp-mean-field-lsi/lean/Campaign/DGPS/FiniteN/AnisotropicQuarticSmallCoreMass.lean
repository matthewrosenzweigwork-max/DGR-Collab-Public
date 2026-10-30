import DGPS.FiniteN.AnisotropicQuarticRareMass

/-! Actual lower mass for every smaller fixed multiple of the quartic rare core. -/

open MeasureTheory Filter Topology
open DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066

namespace DGPS.FiniteN

/-- Shrinking the rare rectangle by any fixed positive factor changes only its
constant, not the quartic power or the actual saddle-to-minimum exponential gap. -/
theorem quartic_small_rare_core_mass_lower :
    ∃ t : ℝ, 1 < t ∧
      (∀ w, quarticPsi_FIN066 !₂[t, 0] ≤ quarticPsi_FIN066 w) ∧
      (∀ w, quarticPsi_FIN066 w ≤ quarticPsi_FIN066 !₂[t, 0] → w = !₂[t, 0]) ∧
      0 < quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0] ∧
      ∀ k : ℝ, 0 < k → k ≤ 1 → ∃ c M : ℝ, 0 < c ∧ 1 ≤ M ∧ ∀ N : ℝ, M ≤ N →
        c * N ^ (1 / 4 : ℝ) * Real.exp
            (-(N * (quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0]))) ≤
          ((imsEta N quarticPsi_FIN066) (quarticRareRectangle (k * N ^ (-(1 / 4 : ℝ))))).toReal := by
  obtain ⟨δ, B, hδ, hδ1, hB, hraw⟩ := quartic_rare_rectangle_raw_mass
  obtain ⟨t, ht, hroot, hmin, huniq, hcrit, hH, hnorm, htail⟩ := quartic_auxiliary_laplace_data
  obtain ⟨L, hL, A, hA, M0, hM0, hnorm⟩ := hnorm
  have hgap : 0 < quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0] := by
    have hle := hmin !₂[-4, 0]
    have hne : quarticPsi_FIN066 !₂[-4, 0] ≠ quarticPsi_FIN066 !₂[t, 0] := by
      intro he
      have hx := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) (huniq !₂[-4, 0] he.le)
      change (-4 : ℝ) = t at hx
      linarith
    exact sub_pos.mpr (lt_of_le_of_ne hle hne.symm)
  refine ⟨t, ht, hmin, huniq, hgap, fun k hk hk1 => ?_⟩
  have hlim : Tendsto (fun N : ℝ => k * N ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul k
  obtain ⟨Mδ, hMδ⟩ := eventually_atTop.mp
    ((hlim.eventually (gt_mem_nhds hδ)).mono fun N h => h.le)
  let c := 4 * k ^ 3 * Real.exp (-B) / A
  refine ⟨c, max M0 Mδ, by dsimp only [c]; positivity,
    hM0.trans (le_max_left _ _), fun N hN => ?_⟩
  have hNM : M0 ≤ N := (le_max_left _ _).trans hN
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one (hM0.trans hNM)
  let s := k * N ^ (-(1 / 4 : ℝ))
  have hs : 0 ≤ s := mul_nonneg hk.le (Real.rpow_pos_of_pos hNp _).le
  have hsδ : s ≤ δ := hMδ N ((le_max_right _ _).trans hN)
  have hp4 : (N ^ (-(1 / 4 : ℝ))) ^ 4 = N⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    norm_num [Real.rpow_neg_one]
  have hscaleeq : N * s ^ 4 = k ^ 4 := by
    dsimp only [s]
    rw [mul_pow, hp4]
    field_simp [hNp.ne']
    <;> ring
  have hscale : N * s ^ 4 ≤ 1 := by
    rw [hscaleeq]
    simpa only [one_pow] using pow_le_pow_left₀ hk.le hk1 4
  have hvol0 : N * (N ^ (-(1 / 4 : ℝ))) ^ 3 = N ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    calc
      _ = N ^ (1 : ℝ) * N ^ (-(1 / 4 : ℝ) * (3 : ℕ)) := by rw [Real.rpow_one]
      _ = N ^ ((1 : ℝ) + -(1 / 4 : ℝ) * (3 : ℕ)) := (Real.rpow_add hNp _ _).symm
      _ = _ := by norm_num
  have hvol : N * s ^ 3 = k ^ 3 * N ^ (1 / 4 : ℝ) := by
    dsimp only [s]
    rw [mul_pow]
    calc
      _ = k ^ 3 * (N * (N ^ (-(1 / 4 : ℝ))) ^ 3) := by ring
      _ = _ := by rw [hvol0]
  have hvoldiv : k ^ 3 * N ^ (1 / 4 : ℝ) * N⁻¹ = s ^ 3 := by
    rw [← hvol]
    field_simp [hNp.ne']
    <;> ring
  have hrawN := (hraw N s hNp hs hsδ hscale).1
  have hZN := (hnorm N hNM).2
  have hZ := quartic_partition_pos N hNp
  let E := Real.exp (-(N * (quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0])))
  have hExp : E * Real.exp (-(N * quarticPsi_FIN066 !₂[t, 0])) =
      Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0])) := by
    dsimp only [E]
    rw [← Real.exp_add]
    congr 1
    ring
  have hAlg : (c * N ^ (1 / 4 : ℝ) * E) *
      (A * N⁻¹ * Real.exp (-(N * quarticPsi_FIN066 !₂[t, 0]))) =
        4 * s ^ 3 * (Real.exp (-B) * Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0]))) := by
    calc
      _ = (4 * (k ^ 3 * N ^ (1 / 4 : ℝ) * N⁻¹) * Real.exp (-B)) *
          (E * Real.exp (-(N * quarticPsi_FIN066 !₂[t, 0]))) := by
        dsimp only [c]
        field_simp [hA.ne']
        <;> ring
      _ = _ := by
        rw [hvoldiv, hExp]
        ring
  rw [TiltedXY.Fin049.imsEta_real_FIN049 N quarticPsi_FIN066 hZ
    (quarticRareRectangle s) (quarticRareRectangle_measurable s)]
  apply (le_div_iff₀ hZ).mpr
  exact (mul_le_mul_of_nonneg_left hZN (by positivity : 0 ≤ c * N ^ (1 / 4 : ℝ) * E)).trans
    (hAlg.le.trans hrawN)

end DGPS.FiniteN
