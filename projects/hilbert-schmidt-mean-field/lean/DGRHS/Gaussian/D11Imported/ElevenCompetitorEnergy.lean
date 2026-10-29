/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.ElevenEnergyData

/-! The strict competitor-energy bound from all one hundred certified
positive shells, transferred to the actual infinite Fourier energy. -/
noncomputable section
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven.Shell

lemma certified_row (i : Fin 100) :
    ((EnergyData.entry i).energyFloor:ℝ)/10^12 <
      ((thetaPolynomial^11).coeff (i.val+1):ℝ)/2 * weight (i.val+1) := by
  have h := EnergyData.accepted i
  have hc := of_decide_eq_true h
  change 0 < (EnergyData.entry i).rootFloor ∧ _ ∧ _ ∧ _ ∧ _ ∧
    ((EnergyData.entry i).energyFloor:ℚ)/10^12 < (EnergyData.entry i).lower (i.val+1) at hc
  have hr : ((EnergyData.entry i).energyFloor:ℝ)/10^12 <
      ((EnergyData.entry i).lower (i.val+1):ℝ) := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr hc.2.2.2.2.2
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat] using hh
  have hl := entry_lower_le_shell (by omega : 0 < i.val + 1) h
  rw [← shellArray_coeff 11 (by omega : i.val + 1 < 101), stage11_correct]
  exact hr.trans_le hl

lemma certified_finite_energy :
    2*((14475384292906:ℝ)/10^12) <
      ∑ m ∈ Finset.range 101, ((thetaPolynomial^11).coeff m:ℝ)*weight m := by
  have hl : (14475384292906:ℝ)/10^12 ≤
      ∑ i : Fin 100, ((EnergyData.entry i).energyFloor:ℝ)/10^12 := by
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast EnergyData.floor_sum
  have hr : (∑ i : Fin 100, ((EnergyData.entry i).energyFloor:ℝ)/10^12) <
      ∑ i : Fin 100, ((thetaPolynomial^11).coeff (i.val+1):ℝ)/2 * weight (i.val+1) := by
    apply Finset.sum_lt_sum
    · exact fun i _ => (certified_row i).le
    · exact ⟨0, Finset.mem_univ _, certified_row 0⟩
  have hs : (∑ m ∈ Finset.range 101, ((thetaPolynomial^11).coeff m:ℝ)*weight m) =
      2*(∑ i : Fin 100, ((thetaPolynomial^11).coeff (i.val+1):ℝ)/2 * weight (i.val+1)) := by
    rw [show 101=100+1 by rfl, Finset.sum_range_succ', weight_zero, mul_zero, add_zero,
      ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  linarith

end DGRHS.Gaussian.D11Imported.HighDim.Eleven.Shell

namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

theorem competitor_energy (ρ : ProbabilityDensity 11) (hρ : ρ.value = periodizedProfile) :
    ENNReal.ofReal (2*((14475384292906:ℝ)/10^12)) < spectralEnergy ρ := by
  apply lt_of_lt_of_le _ (Shell.finite_shell_energy_le ρ hρ)
  exact (ENNReal.ofReal_lt_ofReal_iff (by
    have h := Shell.certified_finite_energy
    linarith)).mpr Shell.certified_finite_energy

#print axioms competitor_energy
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
