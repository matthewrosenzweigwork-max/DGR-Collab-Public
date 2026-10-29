import FullLabeledLSI.Nonvacuity.Prop82.E2_Harmonics

/-!
# Lane E, part 3: admissibility of the heat-direction family and the sign of the defect

DRAFT written in the cloud without a compiler (lane E, cloud thread).

For a smooth optimizer `ρ` with `0 < firstMode ρ`, the densities `ρ_s = ρ + s ρ''` are admissible
for `|s|` small, so the defect `fS ρ s := realDiss ρ_s - 2 R realGap ρ_s` is nonnegative near `0`
and vanishes at `0`.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82.HeatE

/-- `gap_eq_real` of `Model.lean` needs `Admissible`, which includes the positivity of the gap
that we want to prove; this version asks only for the nonnegativity, mass and finite entropy. -/
theorem gap_eq_real_of_finite {rho : Torus 1 → Real} (h0 : ∀ x, 0 ≤ rho x)
    (h1 : ∫ x, rho x ∂haar 1 = 1) (hfin : klDiv (densMeasure rho) (haar 1) ≠ ⊤) :
    gap cosV (cosW 1) (densMeasure rho) = (realGap rho : EReal) := by
  have hkl : klDiv (densMeasure rho) (haar 1) = ENNReal.ofReal (entropy rho) :=
    (ENNReal.ofReal_toReal hfin).symm
  rw [(cosine_free_energy_aux (by norm_num : (0 : Real) < 1)).2.2.2.1 rho h0 h1,
    hkl, EReal.coe_ennreal_ofReal, max_eq_left (entropy_nonneg rho), ← EReal.coe_add]
  congr 1
  unfold realGap
  ring

theorem sp_gap_eq_real {rho : Torus 1 → Real} (h : SmoothProbability rho) :
    gap cosV (cosW 1) (densMeasure rho) = (realGap rho : EReal) :=
  gap_eq_real_of_finite h.nonneg h.mass
    (klDiv_densMeasure_ne_top_of_continuous (smooth_continuous h.smooth) h.nonneg h.mass)

theorem sp_realGap_pos {rho : Torus 1 → Real}
    (hQ : 0 < firstMode rho) : 0 < realGap rho := by
  unfold realGap
  have := entropy_nonneg rho
  linarith

theorem sp_admissible_of_firstMode {rho : Torus 1 → Real}
    (h : SmoothProbability rho) (hQ : 0 < firstMode rho) :
    Admissible cosV (cosW 1) rho := by
  refine h.admissible ?_
  rw [sp_gap_eq_real h]
  exact_mod_cast sp_realGap_pos hQ

/-- The defect functional along the heat-direction family. -/
noncomputable def fS (rho : Torus 1 → Real) (s : Real) : Real :=
  realDiss (rhoS rho s) - 2 * realRate * realGap (rhoS rho s)

theorem fS_zero {rho : Torus 1 → Real} (h : SmoothOptimizer rho) : fS rho 0 = 0 := by
  unfold fS
  rw [rhoS_zero, h.raw.real_equation]
  ring

theorem fS_nonneg_of_admissible {rho : Torus 1 → Real}
    (h : Admissible cosV (cosW 1) rho) : 0 ≤ realDiss rho - 2 * realRate * realGap rho := by
  have hG := realGap_pos h
  have hq := realRate_le_realQuotient h
  rw [le_div_iff₀ (by positivity)] at hq
  linarith

/-- Near `0` the defect is nonnegative and the family is a smooth probability density. -/
theorem exists_good_interval {rho : Torus 1 → Real} (hrho : SmoothProbability rho)
    (hQ : 0 < firstMode rho) :
    ∃ m s0 : Real, 0 < m ∧ 0 < s0 ∧ s0 < 1 / (2 * aCos) ∧ (∀ x, m ≤ rho x) ∧
      (∀ s, |s| ≤ s0 → ∀ x, m / 2 ≤ rhoS rho s x) ∧
      (∀ s, |s| ≤ s0 → SmoothProbability (rhoS rho s)) ∧
      (∀ s, |s| ≤ s0 → 0 < firstMode (rhoS rho s)) ∧
      (∀ s, |s| ≤ s0 → 0 ≤ fS rho s) := by
  obtain ⟨m, s1, hm, hs1, hmrho, hlow⟩ := rhoS_lower hrho
  have ha := a_pos
  set s0 := min s1 (1 / (4 * aCos)) with hs0
  have hs0pos : 0 < s0 := lt_min hs1 (by positivity)
  have hs0le1 : s0 ≤ s1 := min_le_left _ _
  have hs0le2 : s0 ≤ 1 / (4 * aCos) := min_le_right _ _
  have hsmall : s0 < 1 / (2 * aCos) := by
    refine lt_of_le_of_lt hs0le2 ?_
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hlow' : ∀ s, |s| ≤ s0 → ∀ x, m / 2 ≤ rhoS rho s x :=
    fun s hs => hlow s (hs.trans hs0le1)
  have hsp : ∀ s, |s| ≤ s0 → SmoothProbability (rhoS rho s) :=
    fun s hs => smoothProbability_rhoS hrho hm hlow' hs
  have hQs : ∀ s, |s| ≤ s0 → 0 < firstMode (rhoS rho s) := by
    intro s hs
    rw [firstMode_rhoS hrho.smooth]
    have h1 : aCos * s ≤ aCos * s0 := mul_le_mul_of_nonneg_left (le_trans (le_abs_self s) hs) ha.le
    have h2 : aCos * s0 ≤ 1 / 4 := by
      calc aCos * s0 ≤ aCos * (1 / (4 * aCos)) := mul_le_mul_of_nonneg_left hs0le2 ha.le
        _ = 1 / 4 := by field_simp
    have h3 : 0 < 1 - aCos * s := by linarith
    exact mul_pos (pow_pos h3 2) hQ
  refine ⟨m, s0, hm, hs0pos, hsmall, hmrho, hlow', hsp, hQs, fun s hs => ?_⟩
  exact fS_nonneg_of_admissible (sp_admissible_of_firstMode (hsp s hs) (hQs s hs))

end SharpLSI.FL.Prop82.HeatE
