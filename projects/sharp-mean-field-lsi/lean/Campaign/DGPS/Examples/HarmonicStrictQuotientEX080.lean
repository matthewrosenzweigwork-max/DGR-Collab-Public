import DGPS.Examples.HarmonicSubcriticalRateEX079

/-!
# Strict quotient and both nonattainment conclusions (EX080)

For `0 ≤ k < 1` put `r = 4π² (1 - k)`. For every finite species family `F` with positive gap
`G = G_θ` put `E = ∑ θ_s H(ρ_s | Haar)` and `D = D_θ`. Then the quotient `Q = D / (2G)` satisfies

* `Q - r ≥ r E² / (12 G) ≥ r E / 12 > 0` (real form), and
* `ofReal (r + r E / 12) ≤ Q` in `ℝ≥0∞`, hence `ofReal r < Q`.

With `r_* = r_ms = r` (EX079), neither the scalar nor the multispecies positive-gap infimum is
attained. Scalar competitors are one-species families `SpeciesFamily.single ρ`, so the scalar
statements are the species statements for them (`speciesGap_single`, `speciesQuotient_single`).
The endpoint `k = 0` is included.

Route. EX078 gives `(1 - k) E² / 12 ≤ (D - 2 a0 (1 - k) G) / (2 a0)` with `a0 = 4π²`. EX076 gives
`G ≤ E`, so `0 < G` forces `E > 0`. Clearing denominators gives the real chain and the polynomial
bound `(r + r E / 12) · 2G ≤ D`; `ENNReal.le_div_iff_mul_le` turns the latter into the `ℝ≥0∞` bound.

Design choices (R5 notes).
* The listed module `DGPS/Examples/HarmonicNonattainment.lean` already holds the EX076 content
  (`subcritical_harmonic_model_and_gap`), so this result is placed in the new module
  `DGPS/Examples/HarmonicStrictQuotientEX080.lean`, as was done for EX079.
* The rate values `r_* = r_ms = r` (EX079) are part of the conclusion, so the nonattainment
  statements refer to the infimum value `r` itself.
* The `k = 0` endpoint needs no separate argument: all hypotheses are `0 ≤ k < 1`.
* Helper lemmas carry the suffix `_ex080`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace DGPS.Examples

/-- EX080 helper: the real algebra of the strict quotient, from the EX078 deficit bound
`(1 - k) E² / 12 ≤ (D - 2 a0 (1 - k) G) / (2 a0)` and `0 < G ≤ E`. -/
theorem quotient_chain_ex080 (k E G D : ℝ) (hk1 : k < 1) (hG : 0 < G) (hGE : G ≤ E)
    (hdef : (1 - k) * E ^ 2 / 12 ≤
      (D - 2 * (4 * Real.pi ^ 2 * (1 - k)) * G) / (2 * (4 * Real.pi ^ 2))) :
    0 < 4 * Real.pi ^ 2 * (1 - k) * E / 12 ∧
    4 * Real.pi ^ 2 * (1 - k) * E / 12 ≤ 4 * Real.pi ^ 2 * (1 - k) * E ^ 2 / (12 * G) ∧
    4 * Real.pi ^ 2 * (1 - k) * E ^ 2 / (12 * G) ≤ D / (2 * G) - 4 * Real.pi ^ 2 * (1 - k) ∧
    (4 * Real.pi ^ 2 * (1 - k) + 4 * Real.pi ^ 2 * (1 - k) * E / 12) * (2 * G) ≤ D := by
  have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
  have hpi0 : 4 * Real.pi ^ 2 ≠ 0 := hpi.ne'
  have hG0 : G ≠ 0 := hG.ne'
  have hk : 0 < 1 - k := by linarith
  have hr0 : 0 < 4 * Real.pi ^ 2 * (1 - k) := mul_pos hpi hk
  have hE : 0 < E := lt_of_lt_of_le hG hGE
  have hrE : 0 ≤ 4 * Real.pi ^ 2 * (1 - k) * (E * (E - G)) :=
    mul_nonneg hr0.le (mul_nonneg hE.le (sub_nonneg.2 hGE))
  have h2 : 4 * Real.pi ^ 2 * (1 - k) * E ^ 2 / 12 ≤
      (D - 2 * (4 * Real.pi ^ 2 * (1 - k)) * G) / 2 := by
    have h := mul_le_mul_of_nonneg_left hdef hpi.le
    have e1 : 4 * Real.pi ^ 2 * ((1 - k) * E ^ 2 / 12) =
        4 * Real.pi ^ 2 * (1 - k) * E ^ 2 / 12 := by
      ring
    have e2 : 4 * Real.pi ^ 2 *
        ((D - 2 * (4 * Real.pi ^ 2 * (1 - k)) * G) / (2 * (4 * Real.pi ^ 2))) =
        (D - 2 * (4 * Real.pi ^ 2 * (1 - k)) * G) / 2 := by
      field_simp
    rw [e1, e2] at h
    exact h
  refine ⟨div_pos (mul_pos hr0 hE) (by norm_num), ?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by norm_num) (mul_pos (by norm_num) hG)]
    nlinarith [hrE]
  · have e3 : D / (2 * G) - 4 * Real.pi ^ 2 * (1 - k) =
        ((D - 2 * (4 * Real.pi ^ 2 * (1 - k)) * G) / 2) / G := by
      field_simp
    have e4 : 4 * Real.pi ^ 2 * (1 - k) * E ^ 2 / (12 * G) =
        (4 * Real.pi ^ 2 * (1 - k) * E ^ 2 / 12) / G := by
      rw [div_div]
    rw [e3, e4]
    exact div_le_div_of_nonneg_right h2 hG.le
  · nlinarith [hrE, h2]

/-- EX080 helper: the `ℝ≥0∞` strict lower bound `ofReal (r + r E / 12) ≤ D / (2 G)` for a
positive-gap species family of the first-harmonic model. -/
theorem quotient_lower_ex080 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (b : DGPS.AbsoluteDrift (DGPS.Models.attractiveXY (2 * k) 0)) (F : DGPS.SpeciesFamily 1)
    (hG : 0 < DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F) :
    ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k) +
        4 * Real.pi ^ 2 * (1 - k) * (∑ s, F.weight s * (DGPS.relativeEntropy
          (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) /
          12) ≤
      DGPS.speciesQuotient (DGPS.Models.attractiveXY (2 * k) 0) b F := by
  obtain ⟨hD, hdef⟩ := quantitative_positive_harmonic_deficit k hk0 hk1 b F
  have hGE := ((subcritical_harmonic_model_and_gap k hk0 hk1).2.2.2.2.2.2.2 F).2.2.1
  have hGpos : (0 : ℝ) < (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ) :=
    NNReal.coe_pos.mpr hG
  obtain ⟨-, -, -, hpoly⟩ := quotient_chain_ex080 k _ _ _ hk1 hGpos hGE hdef
  have hG2 : (2 : ℝ≥0∞) * (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ≥0∞) ≠ 0 :=
    mul_ne_zero two_ne_zero (ENNReal.coe_ne_zero.mpr hG.ne')
  have hGt : (2 : ℝ≥0∞) * (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top
  have hc : 0 ≤ 4 * Real.pi ^ 2 * (1 - k) + 4 * Real.pi ^ 2 * (1 - k) *
      (∑ s, F.weight s * (DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) / 12 := by
    have hk' : 0 ≤ 1 - k := by linarith
    have hE : 0 < ∑ s, F.weight s * (DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal :=
      lt_of_lt_of_le hGpos hGE
    have hr : 0 ≤ 4 * Real.pi ^ 2 * (1 - k) := mul_nonneg (by positivity) hk'
    exact add_nonneg hr (div_nonneg (mul_nonneg hr hE.le) (by norm_num))
  unfold DGPS.speciesQuotient
  rw [ENNReal.le_div_iff_mul_le (Or.inl hG2) (Or.inl hGt), two_mul_coe_ex079,
    ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_toReal hD]
  exact ENNReal.ofReal_le_ofReal hpoly

/-- EX080 helper: the quotient of a positive-gap species family lies strictly above the rate
value `ofReal r`, `r = 4π² (1 - k)`. -/
theorem quotient_gt_ex080 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (b : DGPS.AbsoluteDrift (DGPS.Models.attractiveXY (2 * k) 0)) (F : DGPS.SpeciesFamily 1)
    (hG : 0 < DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F) :
    ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k)) <
      DGPS.speciesQuotient (DGPS.Models.attractiveXY (2 * k) 0) b F := by
  have h := quotient_lower_ex080 k hk0 hk1 b F hG
  have hGE := ((subcritical_harmonic_model_and_gap k hk0 hk1).2.2.2.2.2.2.2 F).2.2.1
  have hGpos : (0 : ℝ) < (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ) :=
    NNReal.coe_pos.mpr hG
  have hE : 0 < ∑ s, F.weight s * (DGPS.relativeEntropy
      (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal :=
    lt_of_lt_of_le hGpos hGE
  have hk' : 0 < 1 - k := by linarith
  have hr : 0 < 4 * Real.pi ^ 2 * (1 - k) := mul_pos (by positivity) hk'
  have hstep : 0 < 4 * Real.pi ^ 2 * (1 - k) *
      (∑ s, F.weight s * (DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) / 12 :=
    div_pos (mul_pos hr hE) (by norm_num)
  have hlt : ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k)) < ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k) +
      4 * Real.pi ^ 2 * (1 - k) * (∑ s, F.weight s * (DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) / 12) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  exact lt_of_lt_of_le hlt h

/-- EX080: strict quotient and both nonattainment conclusions. For `0 ≤ k < 1` and
`r = 4π² (1 - k)`:

* for every finite species family `F` of positive gap, with `E = ∑ θ_s H(ρ_s | Haar)`,
  `G = G_θ` and `D = D_θ`, the quotient `Q = D / (2G)` satisfies `Q - r ≥ r E² / (12G) ≥ rE/12 > 0`
  and `ofReal (r + r E / 12) ≤ Q`;
* the same holds for every positive-gap scalar density `ρ` (one-species family), with `E = H(ρ|Haar)`;
* `r_* = r_ms = r` (EX079), and no positive-gap scalar density or finite positive-gap species
  family attains the infimum `r`, that is, `Q ≠ r_*` and `Q ≠ r_ms`. The endpoint `k = 0` is
  included. -/
theorem strict_quotient_and_both_nonattainment_conclusions (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (b : DGPS.AbsoluteDrift (DGPS.Models.attractiveXY (2 * k) 0)) :
    (∀ F : DGPS.SpeciesFamily 1, 0 < DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F →
      DGPS.speciesDissipation (DGPS.Models.attractiveXY (2 * k) 0) b F ≠ ⊤ ∧
      0 < 4 * Real.pi ^ 2 * (1 - k) * (∑ s, F.weight s * (DGPS.relativeEntropy
          (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) /
          12 ∧
      4 * Real.pi ^ 2 * (1 - k) * (∑ s, F.weight s * (DGPS.relativeEntropy
          (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) /
          12 ≤
        4 * Real.pi ^ 2 * (1 - k) * (∑ s, F.weight s * (DGPS.relativeEntropy
          (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) ^ 2 /
          (12 * (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ)) ∧
      4 * Real.pi ^ 2 * (1 - k) * (∑ s, F.weight s * (DGPS.relativeEntropy
          (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) ^ 2 /
          (12 * (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ)) ≤
        (DGPS.speciesDissipation (DGPS.Models.attractiveXY (2 * k) 0) b F).toReal /
          (2 * (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ)) -
          4 * Real.pi ^ 2 * (1 - k) ∧
      ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k) +
          4 * Real.pi ^ 2 * (1 - k) * (∑ s, F.weight s * (DGPS.relativeEntropy
            (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1))
            (DGPS.haar 1)).toReal) / 12) ≤
        DGPS.speciesQuotient (DGPS.Models.attractiveXY (2 * k) 0) b F) ∧
    (∀ ρ : DGPS.AbsoluteDensity 1, 0 < DGPS.scalarGap (DGPS.Models.attractiveXY (2 * k) 0) ρ →
      ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k) +
          4 * Real.pi ^ 2 * (1 - k) * (DGPS.relativeEntropy
            (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal / 12) ≤
        DGPS.scalarQuotient (DGPS.Models.attractiveXY (2 * k) 0) b ρ) ∧
    DGPS.scalarRate (DGPS.Models.attractiveXY (2 * k) 0) b =
      ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k)) ∧
    DGPS.speciesRate (DGPS.Models.attractiveXY (2 * k) 0) b =
      ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k)) ∧
    (∀ ρ : DGPS.AbsoluteDensity 1, 0 < DGPS.scalarGap (DGPS.Models.attractiveXY (2 * k) 0) ρ →
      DGPS.scalarQuotient (DGPS.Models.attractiveXY (2 * k) 0) b ρ ≠
        DGPS.scalarRate (DGPS.Models.attractiveXY (2 * k) 0) b) ∧
    (∀ F : DGPS.SpeciesFamily 1, 0 < DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F →
      DGPS.speciesQuotient (DGPS.Models.attractiveXY (2 * k) 0) b F ≠
        DGPS.speciesRate (DGPS.Models.attractiveXY (2 * k) 0) b) := by
  have hrate := subcritical_sharp_rate_by_first_harmonic_trials k hk0 hk1 b
  have hscalar := hrate.2.1
  have hspecies := hrate.2.2.1
  refine ⟨?_, ?_, hscalar, hspecies, ?_, ?_⟩
  · intro F hG
    obtain ⟨hD, hdef⟩ := quantitative_positive_harmonic_deficit k hk0 hk1 b F
    have hGE := ((subcritical_harmonic_model_and_gap k hk0 hk1).2.2.2.2.2.2.2 F).2.2.1
    have hGpos : (0 : ℝ) < (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ) :=
      NNReal.coe_pos.mpr hG
    obtain ⟨h1, h2, h3, -⟩ := quotient_chain_ex080 k _ _ _ hk1 hGpos hGE hdef
    exact ⟨hD, h1, h2, h3, quotient_lower_ex080 k hk0 hk1 b F hG⟩
  · intro ρ hρ
    have hG : 0 < DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0)
        (DGPS.SpeciesFamily.single ρ) := by
      rw [DGPS.speciesGap_single]
      exact hρ
    have h := quotient_lower_ex080 k hk0 hk1 b (DGPS.SpeciesFamily.single ρ) hG
    rw [single_entropy_sum_ex079, DGPS.speciesQuotient_single] at h
    exact h
  · intro ρ hρ
    have hG : 0 < DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0)
        (DGPS.SpeciesFamily.single ρ) := by
      rw [DGPS.speciesGap_single]
      exact hρ
    have h := quotient_gt_ex080 k hk0 hk1 b (DGPS.SpeciesFamily.single ρ) hG
    rw [DGPS.speciesQuotient_single] at h
    rw [hscalar]
    exact h.ne'
  · intro F hF
    rw [hspecies]
    exact (quotient_gt_ex080 k hk0 hk1 b F hF).ne'

end DGPS.Examples
