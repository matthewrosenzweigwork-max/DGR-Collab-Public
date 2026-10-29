import DGPS.Structural.ImprovingFamilySmall
import DGPS.Structural.CircleDensityRatio
import DGPS.Structural.BarycenterOrdinaryLSI
import DGPS.Structural.HarmonicRateComparison
import DGPS.Variational.SpeciesInclusion
import DGPS.Foundations.RateArithmetic

/-!
# STR021: exact small-rate circle equality

For direct Lipschitz circle data with `M > 0` and `0 < r_* ≤ min {ℓ/9, e^{-M}/(4M)}` we have
`r_ms = r_*` (`speciesRate_eq_scalarRate_of_small_frozen_rate`), and in particular the canonical
T07 form with `a₀ = 4π²` (`speciesRate_eq_scalarRate_of_small_circle_rate`).

Route: a finite positive-gap family with quotient `< r_*` (no optimizer) is improving; STR018–STR020
give its barycenter an ordinary LS rate `≥ r_*` and identify the species information; then
`D ≥ 2 r_* g + 2 r_* S = 2 r_* G` contradicts strict improvement.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace DGPS.Structural

/-- Core step. If `r_* = ofReal rs` with `0 < rs ≤ min {ℓ/9, e^{-M}/(4M)}` then `r_ms ≥ r_*`. -/
theorem scalarRate_le_speciesRate_of_small (A : InteractionData 1) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) (rs : ℝ) (hM : 0 < totalOscillation A) (hrs : 0 < rs)
    (hr : scalarRate A b = ENNReal.ofReal rs)
    (h9 : rs ≤ (frozenLSRateInf A).toReal / 9)
    (hexp : rs ≤ Real.exp (-totalOscillation A) / (4 * totalOscillation A)) :
    scalarRate A b ≤ speciesRate A b := by
  by_contra hcon
  rw [not_le, hr] at hcon
  obtain ⟨⟨F, hG⟩, hlt⟩ := iInf_lt_iff.1 hcon
  change speciesQuotient A b F < ENNReal.ofReal rs at hlt
  have himp : speciesDissipation A b F / (2 * (speciesGap A F : ℝ≥0∞)) < ENNReal.ofReal rs := hlt
  have h18 := improvingFamily_gap_and_dissipation_small A hLip b F rs hM hrs h9 hexp hG himp
  have hDtop : speciesDissipation A b F ≠ ⊤ := h18.2.2.1
  have hR := smallFrozenInformation_circle_densityRatio A hLip b F rs hM hrs h9 hexp hG himp
  obtain ⟨Q, hQ⟩ := circleDensityRatio_exists_reference hR
  have hQm : Q.measure = (densityMeasure (barycenter F) : Measure (Torus 1)) := by
    rw [densityMeasure_coe]
    exact withDensity_congr_ae (hQ.mono fun x hx => by
      show ENNReal.ofReal (Q.density x) = ENNReal.ofReal ((barycenter F).density x)
      rw [hx])
  have hLS := (barycenterLSRate_ge_frozen_ninth F hR Q hQ).1
  have hrsLS : ENNReal.ofReal rs ≤ ordinaryLSRate Q := by
    refine le_trans ?_ hLS
    have hℓtop : frozenLSRateInf A ≠ ⊤ :=
      (frozenLSRateInf_ge_lowerBound one_pos A).2.2.ne
    rw [← ENNReal.ofReal_toReal hℓtop, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- scalar part: `2 r_* g ≤ D(ρ̄)`
  have hdec := speciesDissipation_decomposition A b F
  have ha : ENNReal.ofReal (2 * rs * (scalarGap A (barycenter F) : ℝ)) ≤
      scalarDissipation A b (barycenter F) := by
    by_cases hg : 0 < scalarGap A (barycenter F)
    · have h1 := scalarRate_le_quotient A b (barycenter F) hg
      rw [hr] at h1
      unfold scalarQuotient at h1
      have h2 := (ENNReal.le_div_iff_mul_le (Or.inl (two_mul_gap_ne_zero hg))
          (Or.inl (two_mul_gap_ne_top _))).1 h1
      refine le_trans (le_of_eq ?_) h2
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
      ring
    · have : (scalarGap A (barycenter F) : ℝ) = 0 := by
        rw [nonpos_iff_eq_zero.1 (not_lt.1 hg)]; rfl
      rw [this, mul_zero, ENNReal.ofReal_zero]; exact bot_le
  -- species part: `2 r_* H_s ≤ I_s`
  set Hs : Fin F.count → ℝ := fun s => (relativeEntropy
    (densityMeasure (F.density s) : Measure (Torus 1))
    (densityMeasure (barycenter F) : Measure (Torus 1))).toReal with hHs
  have hHfin : ∀ s, relativeEntropy (densityMeasure (F.density s) : Measure (Torus 1))
      (densityMeasure (barycenter F) : Measure (Torus 1)) ≠ ⊤ := fun s =>
    (F.relativeEntropy_species s).2.1
  have hterm : ∀ s, ENNReal.ofReal (F.weight s * (2 * rs * Hs s)) ≤
      ENNReal.ofReal (F.weight s) * F.scoreInformation s := by
    intro s
    have hH0 : 0 ≤ Hs s := ENNReal.toReal_nonneg
    have hνac : (densityMeasure (F.density s) : Measure (Torus 1)) ≪ Q.measure :=
      Measure.AbsolutelyContinuous.trans (by
        rw [densityMeasure_coe]; exact withDensity_absolutelyContinuous _ _)
        Q.haar_ac_measure
    have hls := two_mul_lsRate_mul_relativeEntropy_le Q _ hνac
    rw [(positiveH1Circle_reference_information_eq_score F hR Q hQ s).2, hQm] at hls
    rw [ENNReal.ofReal_mul (F.weight_nonneg s)]
    refine mul_le_mul' le_rfl (le_trans (le_of_eq ?_) (le_trans
      (mul_le_mul' (mul_le_mul' le_rfl hrsLS) le_rfl) hls))
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat, hHs]
    simp only
    rw [ENNReal.ofReal_toReal (hHfin s)]
  have hsum : ENNReal.ofReal (2 * rs * (speciesGap A F : ℝ)) ≤ speciesDissipation A b F := by
    have hdecG := F.speciesGap_decomposition A
    have hS : 2 * rs * (speciesGap A F : ℝ) = 2 * rs * (scalarGap A (barycenter F) : ℝ) +
        ∑ s, F.weight s * (2 * rs * Hs s) := by
      rw [hdecG, mul_add, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun s _ => by simp only [hHs]; ring
    have hn : ∀ s ∈ Finset.univ, 0 ≤ F.weight s * (2 * rs * Hs s) := fun s _ =>
      mul_nonneg (F.weight_nonneg s) (mul_nonneg (by positivity) ENNReal.toReal_nonneg)
    rw [hS, ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg hn),
      ENNReal.ofReal_sum_of_nonneg hn, hdec.2]
    exact add_le_add ha (Finset.sum_le_sum fun s _ => hterm s)
  have hG2 : (speciesGap A F : ℝ≥0∞) = ENNReal.ofReal (speciesGap A F : ℝ) :=
    (ENNReal.ofReal_coe_nnreal).symm
  have hle : ENNReal.ofReal rs ≤ speciesDissipation A b F / (2 * (speciesGap A F : ℝ≥0∞)) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (two_mul_gap_ne_zero hG))
      (Or.inl (two_mul_gap_ne_top _))]
    refine le_trans (le_of_eq ?_) hsum
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat, ← hG2]
    ring
  exact absurd himp (not_lt.2 hle)

/-- **STR021 (sharper form).** For direct Lipschitz circle data with `M > 0` and
`0 < r_* ≤ min {ℓ/9, e^{-M}/(4M)}` (both thresholds inclusive, `ℓ` the actual frozen LSI
infimum), `r_ms = r_*`. -/
theorem speciesRate_eq_scalarRate_of_small_frozen_rate (A : InteractionData 1)
    (hLip : LipschitzData A) (hM : 0 < totalOscillation A)
    (hpos : 0 < scalarRate A (lipschitz_absoluteDrift A hLip))
    (hsmall : scalarRate A (lipschitz_absoluteDrift A hLip) ≤
      ENNReal.ofReal (min ((frozenLSRateInf A).toReal / 9)
        (Real.exp (-totalOscillation A) / (4 * totalOscillation A)))) :
    speciesRate A (lipschitz_absoluteDrift A hLip) =
      scalarRate A (lipschitz_absoluteDrift A hLip) := by
  set b := lipschitz_absoluteDrift A hLip with hb
  have hfin : scalarRate A b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsmall
  set rs := (scalarRate A b).toReal with hrsdef
  have hrs : 0 < rs := ENNReal.toReal_pos hpos.ne' hfin
  have hr : scalarRate A b = ENNReal.ofReal rs := (ENNReal.ofReal_toReal hfin).symm
  have hmin0 : 0 ≤ min ((frozenLSRateInf A).toReal / 9)
      (Real.exp (-totalOscillation A) / (4 * totalOscillation A)) :=
    le_min (by positivity) (by positivity)
  have hle : rs ≤ min ((frozenLSRateInf A).toReal / 9)
      (Real.exp (-totalOscillation A) / (4 * totalOscillation A)) :=
    (ENNReal.ofReal_le_ofReal_iff hmin0).1 (hr ▸ hsmall)
  exact le_antisymm (speciesRate_le_scalarRate A b)
    (scalarRate_le_speciesRate_of_small A hLip b rs hM hrs hr (hle.trans (min_le_left _ _))
      (hle.trans (min_le_right _ _)))

/-- **STR021 / T07.** On the circle with direct Lipschitz data, `M > 0` and
`0 < r_* ≤ e^{-M} min {a₀/9, 1/(4M)}` (inclusive), `r_ms = r_*`. -/
theorem speciesRate_eq_scalarRate_of_small_circle_rate (A : InteractionData 1)
    (hLip : LipschitzData A) (hM : 0 < totalOscillation A)
    (hpos : 0 < scalarRate A (lipschitz_absoluteDrift A hLip))
    (hsmall : scalarRate A (lipschitz_absoluteDrift A hLip) ≤
      ENNReal.ofReal (Real.exp (-totalOscillation A) *
        min (a0 / 9) (1 / (4 * totalOscillation A)))) :
    speciesRate A (lipschitz_absoluteDrift A hLip) =
      scalarRate A (lipschitz_absoluteDrift A hLip) := by
  refine speciesRate_eq_scalarRate_of_small_frozen_rate A hLip hM hpos
    (hsmall.trans (ENNReal.ofReal_le_ofReal ?_))
  have hℓ := frozenLSRateInf_ge_lowerBound one_pos A
  have hℓr : a0 * Real.exp (-totalOscillation A) ≤ (frozenLSRateInf A).toReal := by
    have := ENNReal.toReal_mono hℓ.2.2.ne hℓ.2.1
    rw [ENNReal.toReal_ofReal hℓ.1.le] at this
    simpa [a0] using this
  have hE := Real.exp_pos (-totalOscillation A)
  rw [le_min_iff]
  constructor
  · calc Real.exp (-totalOscillation A) * min (a0 / 9) (1 / (4 * totalOscillation A))
        ≤ Real.exp (-totalOscillation A) * (a0 / 9) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hE.le
      _ ≤ _ := by linarith
  · calc Real.exp (-totalOscillation A) * min (a0 / 9) (1 / (4 * totalOscillation A))
        ≤ Real.exp (-totalOscillation A) * (1 / (4 * totalOscillation A)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hE.le
      _ = _ := by ring

end DGPS.Structural
