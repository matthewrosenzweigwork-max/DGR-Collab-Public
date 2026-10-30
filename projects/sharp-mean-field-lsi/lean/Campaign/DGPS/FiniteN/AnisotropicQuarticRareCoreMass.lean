import DGPS.FiniteN.AnisotropicQuarticRareMass

/-! The actual normalized rare core has the quartic prefactor, with the same
actual minimum used in the genuine Laplace normalizer. -/

open MeasureTheory Filter Topology
open DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066

namespace DGPS.FiniteN

private theorem quartic_scale_power (N : ℝ) (hN : 0 < N) (n : ℕ) :
    (N ^ (-(1 / 4 : ℝ))) ^ n = N ^ (-(1 / 4 : ℝ) * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]

private theorem quartic_scale_four (N : ℝ) (hN : 0 < N) :
    N * (N ^ (-(1 / 4 : ℝ))) ^ 4 = 1 := by
  rw [quartic_scale_power N hN, show -(1 / 4 : ℝ) * (4 : ℕ) = -1 by norm_num,
    Real.rpow_neg_one, mul_inv_cancel₀ hN.ne']

private theorem quartic_scale_volume (N : ℝ) (hN : 0 < N) :
    N * (N ^ (-(1 / 4 : ℝ))) ^ 3 = N ^ (1 / 4 : ℝ) := by
  rw [quartic_scale_power N hN]
  calc
    _ = N ^ (1 : ℝ) * N ^ (-(1 / 4 : ℝ) * (3 : ℕ)) := by rw [Real.rpow_one]
    _ = N ^ ((1 : ℝ) + -(1 / 4 : ℝ) * (3 : ℕ)) := (Real.rpow_add hN _ _).symm
    _ = _ := by norm_num

/-- A concrete rare core has normalized probability comparable to
`N^(1/4) * exp(-N*Delta)`, where Delta is the actual positive saddle-to-minimum gap.
Every constant and threshold is fixed before particle number. -/
theorem quartic_rare_core_mass :
    ∃ t : ℝ, 1 < t ∧
      (∀ w, quarticPsi_FIN066 !₂[t, 0] ≤ quarticPsi_FIN066 w) ∧
      (∀ w, quarticPsi_FIN066 w ≤ quarticPsi_FIN066 !₂[t, 0] → w = !₂[t, 0]) ∧
      0 < quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0] ∧
      ∃ c C N0 : ℝ, 0 < c ∧ 0 < C ∧ 1 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
        c * N ^ (1 / 4 : ℝ) * Real.exp
            (-(N * (quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0]))) ≤
          ((imsEta N quarticPsi_FIN066) (quarticRareRectangle (N ^ (-(1 / 4 : ℝ))))).toReal ∧
        ((imsEta N quarticPsi_FIN066) (quarticRareRectangle (N ^ (-(1 / 4 : ℝ))))).toReal ≤
          C * N ^ (1 / 4 : ℝ) * Real.exp
            (-(N * (quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0]))) := by
  obtain ⟨δ, B, hδ, hδ1, hB, hraw⟩ := quartic_rare_rectangle_raw_mass
  obtain ⟨t, ht, hroot, hmin, huniq, hcrit, hH, hnorm, htail⟩ := quartic_auxiliary_laplace_data
  obtain ⟨L, hL, A, hA, M, hM, hnorm⟩ := hnorm
  have hgap : 0 < quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0] := by
    have hle := hmin !₂[-4, 0]
    have hne : quarticPsi_FIN066 !₂[-4, 0] ≠ quarticPsi_FIN066 !₂[t, 0] := by
      intro he
      have hw := huniq !₂[-4, 0] he.le
      have hx := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) hw
      change (-4 : ℝ) = t at hx
      linarith
    exact sub_pos.mpr (lt_of_le_of_ne hle hne.symm)
  have hsmall : ∀ᶠ N : ℝ in atTop, N ^ (-(1 / 4 : ℝ)) ≤ δ := by
    have hlim := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
    exact (hlim.eventually (gt_mem_nhds hδ)).mono fun _ h => h.le
  obtain ⟨Mδ, hMδ⟩ := eventually_atTop.mp hsmall
  let c := 4 * Real.exp (-B) / A
  let C := 4 * Real.exp B / L
  refine ⟨t, ht, hmin, huniq, hgap, c, C, max M Mδ, by dsimp [c]; positivity,
    by dsimp [C]; positivity, hM.trans (le_max_left _ _), fun N hN => ?_⟩
  have hNM : M ≤ N := (le_max_left _ _).trans hN
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one (hM.trans hNM)
  let s := N ^ (-(1 / 4 : ℝ))
  have hs : 0 ≤ s := (Real.rpow_pos_of_pos hNp _).le
  have hsδ : s ≤ δ := hMδ N ((le_max_right _ _).trans hN)
  have hscale : N * s ^ 4 ≤ 1 := (quartic_scale_four N hNp).le
  have hrawN := hraw N s hNp hs hsδ hscale
  have hZN := hnorm N hNM
  have hZ := quartic_partition_pos N hNp
  let E := Real.exp (-(N * (quarticPsi_FIN066 !₂[-4, 0] - quarticPsi_FIN066 !₂[t, 0])))
  have hE : 0 < E := Real.exp_pos _
  have hExp : E * Real.exp (-(N * quarticPsi_FIN066 !₂[t, 0])) =
      Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0])) := by
    dsimp only [E]
    rw [← Real.exp_add]
    congr 1
    ring
  have hvol : N ^ (1 / 4 : ℝ) = N * s ^ 3 := (quartic_scale_volume N hNp).symm
  have hloEq : (c * N ^ (1 / 4 : ℝ) * E) *
      (A * N⁻¹ * Real.exp (-(N * quarticPsi_FIN066 !₂[t, 0]))) =
      4 * s ^ 3 * (Real.exp (-B) * Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0]))) := by
    rw [hvol]
    calc
      _ = (4 * s ^ 3 * Real.exp (-B)) *
          (E * Real.exp (-(N * quarticPsi_FIN066 !₂[t, 0]))) := by
        dsimp only [c]
        field_simp [hA.ne', hNp.ne']
        <;> ring
      _ = _ := by rw [hExp]; ring
  have hhiEq : (C * N ^ (1 / 4 : ℝ) * E) *
      (L * N⁻¹ * Real.exp (-(N * quarticPsi_FIN066 !₂[t, 0]))) =
      4 * s ^ 3 * (Real.exp B * Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0]))) := by
    rw [hvol]
    calc
      _ = (4 * s ^ 3 * Real.exp B) *
          (E * Real.exp (-(N * quarticPsi_FIN066 !₂[t, 0]))) := by
        dsimp only [C]
        field_simp [hL.ne', hNp.ne']
        <;> ring
      _ = _ := by rw [hExp]; ring
  rw [TiltedXY.Fin049.imsEta_real_FIN049 N quarticPsi_FIN066 hZ
    (quarticRareRectangle s) (quarticRareRectangle_measurable s)]
  constructor
  · apply (le_div_iff₀ hZ).mpr
    exact (mul_le_mul_of_nonneg_left hZN.2 (by positivity : 0 ≤ c * N ^ (1 / 4 : ℝ) * E)).trans
      (hloEq.le.trans hrawN.1)
  · apply (div_le_iff₀ hZ).mpr
    exact hrawN.2.trans (hhiEq.symm.le.trans
      (mul_le_mul_of_nonneg_left hZN.1 (by positivity : 0 ≤ C * N ^ (1 / 4 : ℝ) * E)))

end DGPS.FiniteN
