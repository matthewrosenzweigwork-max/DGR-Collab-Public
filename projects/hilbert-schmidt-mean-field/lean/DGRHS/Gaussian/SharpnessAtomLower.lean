import DGRHS.Gaussian.SharpnessCompression
import DGRHS.Gaussian.SharpnessCellDistance

noncomputable section
open MeasureTheory Set Filter BoxIntegral
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

/-- Proper normalized physical block lower bound. Collision exclusion follows
from the actual density law; no block or HS lower bound is assumed. -/
theorem sharpness_centered_atom_average_lower (s T : ℝ) (hs : 0 < s) (hT : 0 < T)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (A B : Set (EuclideanSpace ℝ ι)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAm : 0 < (gaussianRieszDensityMeasure ρ A).toReal)
    (hBm : 0 < (gaussianRieszDensityMeasure ρ B).toReal)
    (hdist : ∀ u ∈ A, ∀ v ∈ B, ‖u-v‖ ≤ T)
    (hlocal : ∀ u ∈ A, ∀ v ∈ B, u ≠ v → gaussianRieszPhysicalPair s (u,v)/2 ≤
      hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s) (u,v)) :
    T^(-s)/(2*s) ≤ sharpnessAtomAverage (gaussianRieszDensityMeasure ρ)
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s)) A B := by
  let μ := gaussianRieszDensityMeasure ρ
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  have hc : 0 < Fintype.card ι := by
    exact_mod_cast (show (0:ℝ) < Fintype.card ι by linarith)
  have : Nonempty ι := Fintype.card_pos_iff.mp hc
  have hiH : Integrable H (μ.prod μ) := sharpness_centered_riesz_integrable s hs ha ρ M hM hρ
  have hi : Integrable H ((μ.restrict A).prod (μ.restrict B)) := by
    rw [Measure.prod_restrict]
    exact hiH.restrict
  have hpoint : ∀ᵐ p ∂(μ.restrict A).prod (μ.restrict B), T^(-s)/(2*s) ≤ H p := by
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (hA.prod hB),
      ae_restrict_of_ae (ae_gaussianRieszDensity_pair_ne ρ)] with p hp hne
    have hn : 0 < ‖p.1-p.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hr := Real.rpow_le_rpow_of_nonpos hn (hdist p.1 hp.1 p.2 hp.2) (neg_nonpos.mpr hs.le)
    have hw : T^(-s)/(2*s) ≤ gaussianRieszPhysicalPair s p/2 := by
      unfold gaussianRieszPhysicalPair
      have hh := div_le_div_of_nonneg_right hr hs.le
      rw [mul_comm (2:ℝ) s, div_mul_eq_div_div]
      exact div_le_div_of_nonneg_right hh (by norm_num)
    exact hw.trans (hlocal p.1 hp.1 p.2 hp.2 hne)
  have hb := integral_mono_ae (integrable_const (T^(-s)/(2*s))) hi hpoint
  have hmass : (μ.restrict A).prod (μ.restrict B) univ = μ A * μ B := by
    rw [← Set.univ_prod_univ, Measure.prod_prod]
    simp
  rw [MeasureTheory.integral_const, smul_eq_mul, Measure.real, hmass, ENNReal.toReal_mul] at hb
  change T^(-s)/(2*s) ≤ sharpnessAtomIntegral μ H A B/((μ A).toReal*(μ B).toReal)
  apply (le_div_iff₀ (mul_pos hAm hBm)).mpr
  dsimp [sharpnessAtomIntegral]
  nlinarith [hb]

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_centered_atom_average_lower
#check @DGRHS.Gaussian.sharpness_centered_atom_average_lower
