import DGPS.Structural.SmallRateCircle
import DGPS.Variational.ScoreDecomposition
import DGPS.Foundations.RateArithmetic

/-!
STR018: an improving family has small absolute dissipation.

With `ℓ = frozenLSRateInf`, `M = totalOscillation`, `M > 0`, and
`0 < r_* ≤ min {ℓ/9, e^(-M)/(4M)}`: a positive-gap family with `D/(2G) < r_*` satisfies
`G < ℓ M/(ℓ - r_*) ≤ 2M` and `D < 4 M r_* ≤ e^(-M)`; in particular `D(ρ̄) ≤ D < e^(-M)`.

R5 notes: `ℓ` enters through `(frozenLSRateInf A).toReal`; the hypothesis `0 < r_* ≤ ℓ.toReal/9`
forces `ℓ ≠ ⊤`. Route: STR017 fourth conjunct plus elementary arithmetic.
-/

open scoped ENNReal NNReal

namespace DGPS.Structural

variable {d : ℕ}

theorem improvingFamily_gap_and_dissipation_small (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) (F : SpeciesFamily d) (rs : ℝ)
    (hM : 0 < totalOscillation A) (hrs : 0 < rs)
    (h9 : rs ≤ (frozenLSRateInf A).toReal / 9)
    (hexp : rs ≤ Real.exp (-totalOscillation A) / (4 * totalOscillation A))
    (hG : 0 < speciesGap A F)
    (himp : speciesDissipation A b F / (2 * (speciesGap A F : ℝ≥0∞)) < ENNReal.ofReal rs) :
    (speciesGap A F : ℝ) <
        (frozenLSRateInf A).toReal * totalOscillation A /
          ((frozenLSRateInf A).toReal - rs) ∧
      (frozenLSRateInf A).toReal * totalOscillation A /
          ((frozenLSRateInf A).toReal - rs) ≤ 2 * totalOscillation A ∧
      speciesDissipation A b F ≠ ⊤ ∧
      (speciesDissipation A b F).toReal < 4 * totalOscillation A * rs ∧
      4 * totalOscillation A * rs ≤ Real.exp (-totalOscillation A) ∧
      speciesDissipation A b F < ENNReal.ofReal (Real.exp (-totalOscillation A)) ∧
      scalarDissipation A b (barycenter F) ≤ speciesDissipation A b F ∧
      scalarDissipation A b (barycenter F) < ENNReal.ofReal (Real.exp (-totalOscillation A)) := by
  set M := totalOscillation A with hMdef
  set G : ℝ := (speciesGap A F : ℝ) with hGdef
  set D := speciesDissipation A b F with hD
  have hGpos : 0 < G := by exact_mod_cast hG
  have h4 := (speciesGap_le_frozenEntropy_add_amplitude A hLip b F).2.2.2
  have h3 := (speciesGap_le_frozenEntropy_add_amplitude A hLip b F).2.2.1
  have h34 : 2 * frozenLSRateInf A * ENNReal.ofReal (G - M) ≤ D := h4.trans h3
  -- D < 2 rs G
  have hlt : D < ENNReal.ofReal rs * (2 * (speciesGap A F : ℝ≥0∞)) :=
    (ENNReal.div_lt_iff (Or.inl (two_mul_gap_ne_zero hG))
      (Or.inl (two_mul_gap_ne_top _))).1 himp
  have hrhs : ENNReal.ofReal rs * (2 * (speciesGap A F : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (two_mul_gap_ne_top _)
  have hDtop : D ≠ ⊤ := ne_top_of_lt hlt
  have hDlt : D.toReal < rs * (2 * G) := by
    have := (ENNReal.toReal_lt_toReal hDtop hrhs).2 hlt
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hrs.le, hGdef] using this
  set L := (frozenLSRateInf A).toReal with hL
  have hLpos : 0 < L := by linarith
  have hltop : frozenLSRateInf A ≠ ⊤ := by
    intro h; rw [hL, h] at hLpos; simp at hLpos
  have hreal : 2 * L * (G - M) ≤ D.toReal := by
    have := ENNReal.toReal_mono hDtop h34
    have e : (2 * frozenLSRateInf A * ENNReal.ofReal (G - M)).toReal =
        2 * L * max (G - M) 0 := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal' ]
      simp [hL]
    rw [e] at this
    have : 2 * L * (G - M) ≤ 2 * L * max (G - M) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    linarith
  have hLr : 0 < L - rs := by linarith
  have hgap : G < L * M / (L - rs) := by
    rw [lt_div_iff₀ hLr]; nlinarith
  have hgap2 : L * M / (L - rs) ≤ 2 * M := by
    rw [div_le_iff₀ hLr]; nlinarith
  have hDM : D.toReal < 4 * M * rs := by nlinarith
  have hexp' : 4 * M * rs ≤ Real.exp (-M) := by
    have := (le_div_iff₀ (by positivity : 0 < 4 * M)).1 hexp
    linarith
  have hDe : D < ENNReal.ofReal (Real.exp (-M)) := by
    rw [← ENNReal.ofReal_toReal hDtop]
    exact (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).2 (hDM.trans_le hexp')
  have hdec : scalarDissipation A b (barycenter F) ≤ D := by
    rw [hD, SpeciesFamily.speciesDissipation_decomposition]
    exact le_self_add
  exact ⟨hgap, hgap2, hDtop, hDM, hexp', hDe, hdec, hdec.trans_lt hDe⟩
