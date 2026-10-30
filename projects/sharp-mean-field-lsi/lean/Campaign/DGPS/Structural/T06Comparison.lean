import DGPS.Structural.T06AmplitudeBound
import DGPS.Structural.T06RatioArithmetic
import DGPS.Lipschitz.T01Positivity

noncomputable section
open scoped ENNReal
namespace DGPS.Structural

/-- The complete direct-Lipschitz frozen-Gibbs comparison, including finite
positive real witnesses, the separate harmonic bound, and the amplitude ratio. -/
theorem frozenGibbs_scalar_species_comparison
    (d : ℕ) (hd : 0 < d) (A : DGPS.InteractionData d)
    (hLip : DGPS.LipschitzData A)
    (hpos : 0 < DGPS.scalarRate A (DGPS.lipschitz_absoluteDrift A hLip)) :
  let b := DGPS.lipschitz_absoluteDrift A hLip
  ∃ hs : DGPS.FiniteRate (DGPS.scalarRate A b),
  ∃ hm : DGPS.FiniteRate (DGPS.speciesRate A b),
  ∃ hl : DGPS.FiniteRate (DGPS.frozenLSRateInf A),
    let rs := DGPS.realRate (DGPS.scalarRate A b) hs
    let rm := DGPS.realRate (DGPS.speciesRate A b) hm
    let ell := DGPS.realRate (DGPS.frozenLSRateInf A) hl
    let B := DGPS.interactionOscillation A
    let M := DGPS.totalOscillation A
    0 < rs ∧ 0 < rm ∧ 0 < ell ∧
    DGPS.a0 * Real.exp (-M) ≤ ell ∧
    rs * ell / (rs + ell) ≤ rm ∧ rm ≤ rs ∧
    1 ≤ rs/rm ∧ rs/rm ≤ 1 + (1+B/2) * Real.exp (2*M) := by
  let b := DGPS.lipschitz_absoluteDrift A hLip
  have hs : DGPS.FiniteRate (DGPS.scalarRate A b) := DGPS.Lipschitz.scalarRate_ne_top hd A hLip b
  have hinc := speciesRate_le_scalarRate A b
  have hm : DGPS.FiniteRate (DGPS.speciesRate A b) := ne_top_of_le_ne_top hs hinc
  have hl : DGPS.FiniteRate (DGPS.frozenLSRateInf A) := (frozenLSRateInf_ge_lowerBound hd A).2.2.ne
  have hsp := DGPS.Lipschitz.speciesRate_pos_of_scalarRate_pos hd A hLip b hpos
  have hrs : 0 < (scalarRate A b).toReal := ENNReal.toReal_pos hpos.ne' hs
  have hrm : 0 < (speciesRate A b).toReal := ENNReal.toReal_pos hsp.ne' hm
  have hell : 0 < (frozenLSRateInf A).toReal := ENNReal.toReal_pos (frozenLSRateInf_pos A).ne' hl
  have hlower : a0 * Real.exp (-totalOscillation A) ≤ (frozenLSRateInf A).toReal := by
    have hh := ENNReal.toReal_mono hl (frozenLSRateInf_lower_bound d hd A)
    simpa only [ENNReal.toReal_ofReal (mul_pos a0_pos (Real.exp_pos _)).le] using hh
  have hharm : (scalarRate A b).toReal * (frozenLSRateInf A).toReal /
      ((scalarRate A b).toReal + (frozenLSRateInf A).toReal) ≤ (speciesRate A b).toReal := by
    have hh := ENNReal.toReal_mono hm (speciesRate_ge_harmonicMean_frozenLS hd A hLip b hpos hs).1
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (scalarRate A b).toReal *
      (frozenLSRateInf A).toReal / ((scalarRate A b).toReal + (frozenLSRateInf A).toReal))] using hh
  have hle : (speciesRate A b).toReal ≤ (scalarRate A b).toReal := ENNReal.toReal_mono hs hinc
  have ha0 := a0_pos
  have hB := DGPS.interactionOscillation_nonneg A
  have hupper : (scalarRate A b).toReal ≤ a0 * (1 + DGPS.interactionOscillation A / 2) *
      Real.exp (totalOscillation A) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (scalarRate_le_amplitude_bound d hd A hLip hpos)
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ a0 *
      (1 + DGPS.interactionOscillation A / 2) * Real.exp (totalOscillation A))] using hh
  have hratio := DGPS.Lipschitz.t06_scalar_species_ratio_arithmetic hrs hrm hell hle hharm hlower hupper hB
  exact ⟨hs, hm, hl, hrs, hrm, hell, hlower, hharm, hle, hratio⟩

/-- Required real-valued scalar/species amplitude-ratio projection. All finite
and positive rate witnesses are conclusions, rather than input assumptions. -/
theorem scalarSpecies_ratio_le_amplitude_bound
    (d : ℕ) (hd : 0 < d) (A : DGPS.InteractionData d)
    (hLip : DGPS.LipschitzData A)
    (hpos : 0 < DGPS.scalarRate A (DGPS.lipschitz_absoluteDrift A hLip)) :
    let b := DGPS.lipschitz_absoluteDrift A hLip
    ∃ hs : DGPS.FiniteRate (DGPS.scalarRate A b),
    ∃ hm : DGPS.FiniteRate (DGPS.speciesRate A b),
      let rs := DGPS.realRate (DGPS.scalarRate A b) hs
      let rm := DGPS.realRate (DGPS.speciesRate A b) hm
      0 < rs ∧ 0 < rm ∧ 1 ≤ rs / rm ∧
        rs / rm ≤ 1 + (1 + DGPS.interactionOscillation A / 2) * Real.exp (2 * DGPS.totalOscillation A) := by
  obtain ⟨hs, hm, hl, hrs, hrm, hell, hlower, hharm, hle, hratio⟩ :=
    frozenGibbs_scalar_species_comparison d hd A hLip hpos
  exact ⟨hs, hm, hrs, hrm, hratio⟩

end DGPS.Structural
