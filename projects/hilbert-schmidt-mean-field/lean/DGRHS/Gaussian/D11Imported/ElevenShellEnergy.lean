/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.ElevenShellPolynomial
import DGRHS.Gaussian.D11Imported.ElevenPeriodizedFourier

/-! The certified finite shells bound the genuine extended Fourier energy.
This is a lower bound obtained by retaining a finite set of actual frequency
vectors; the infinite energy is not replaced by its truncation. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven.Shell

def weight (m : ℕ) : ℝ := (Real.sqrt (m:ℝ)^11)⁻¹ *
  fourierProfile (2*Real.pi*Real.sqrt (m:ℝ)/5)^2

lemma weight_nonneg (m : ℕ) : 0 ≤ weight m := by unfold weight; positivity
lemma weight_zero : weight 0 = 0 := by simp [weight]

lemma truncated_sum_le_box (d N : ℕ) (F : ℕ → ℝ) (hF : ∀ m, 0 ≤ F m) :
    (∑ m ∈ Finset.range N, ((thetaPolynomial^d).coeff m:ℝ)*F m) ≤
      ∑ x : Fin d → Fin 21, F (radius d x) := by
  calc
    _ = ∑ x : Fin d → Fin 21, ∑ m ∈ Finset.range N,
        if radius d x=m then F m else 0 := by
      simp_rw [coefficient_count, Finset.natCast_card_filter, Finset.sum_mul,
        ite_mul, one_mul, zero_mul]
      exact Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x _
      rw [Finset.sum_ite_eq]
      split_ifs
      · exact le_rfl
      · exact hF _

lemma finite_shell_energy_le (ρ : ProbabilityDensity 11) (hρ : ρ.value = periodizedProfile) :
    ENNReal.ofReal (∑ m ∈ Finset.range 101, ((thetaPolynomial^11).coeff m:ℝ)*weight m) ≤
      spectralEnergy ρ := by
  let g : Frequency 11 → ℝ≥0∞ := fun k =>
    ENNReal.ofReal ((frequencyLength k^11)⁻¹ * ‖fourierCoeff ρ.value k‖^2)
  have hz : g 0 = 0 := by simp [g, frequencyLength]
  have hs : Function.support g ⊆ {k : Frequency 11 | k ≠ 0} := by
    intro k hk hk0
    exact hk (hk0 ▸ hz)
  have ht : (∑' k : Frequency 11, g k) = spectralEnergy ρ :=
    (tsum_subtype_eq_of_support_subset hs).symm
  have he (x : Fin 11 → Fin 21) : ENNReal.ofReal (weight (radius 11 x)) = g (vector 11 x) := by
    dsimp [g, weight]
    rw [hρ, periodizedProfile_fourier, length_eq_sqrt_radius]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ ENNReal.ofReal (∑ x : Fin 11 → Fin 21, weight (radius 11 x)) :=
      ENNReal.ofReal_le_ofReal (truncated_sum_le_box 11 101 weight weight_nonneg)
    _ = ∑ x : Fin 11 → Fin 21, g (vector 11 x) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => weight_nonneg _)]
      exact Finset.sum_congr rfl (fun x _ => he x)
    _ ≤ ∑' k : Frequency 11, g k := by
      simpa only [tsum_fintype] using ENNReal.tsum_comp_le_tsum_of_injective (vector_injective 11) g
    _ = _ := ht

#print axioms finite_shell_energy_le
end DGRHS.Gaussian.D11Imported.HighDim.Eleven.Shell
