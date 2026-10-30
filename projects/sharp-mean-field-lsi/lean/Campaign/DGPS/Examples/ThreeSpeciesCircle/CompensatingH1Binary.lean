import DGPS.Lipschitz.T01DilutionComplement
import DGPS.Lipschitz.T01SpeciesReferenceQuotient

/-! The actual compensating binary species on the full weighted-H1 domain.
This uses the checked weak Sobolev complement, not the smooth EX017 carrier. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle
open DGPS.Lipschitz

section Data
variable (P : BoundedPositiveReference 1) (hP : P.hasPositiveLipschitzDensity)
  (g : Torus 1 → ℝ) (hg : g ∈ WeightedH1 P) (hg0 : ∀ x, 0 ≤ g x)
  (hmass : ∫ x, g x ^ 2 ∂P.measure = 1) (M : ℝ) (hgM : ∀ x, |g x| ≤ M)
  (t : ℝ) (ht0 : 0 < t) (hthalf : t ≤ 1 / 2) (htM : t * M ^ 2 ≤ 1 / 2)

include hg hgM ht0 hthalf htM in
private theorem complement_mem : t01DilutionComplement t 1 g ∈ WeightedH1 P :=
  t01DilutionComplement_mem P hg hgM ht0.le hthalf (by norm_num)
    (by simpa only [mul_one] using htM)

include hg hgM ht0 hthalf htM hmass in
private theorem complement_mass : ∫ x, t01DilutionComplement t 1 g x ^ 2 ∂P.measure = 1 :=
  t01DilutionComplement_mass P hg hgM ht0.le hthalf (by norm_num)
    (by simpa only [mul_one] using htM) (by simpa only [one_mul] using hmass)

/-- The genuine compensating species with relative square root supplied by the
full-H1 weak chain rule. -/
def compensatingH1Species : AbsoluteDensity 1 :=
  t01RelativeAbsoluteDensity P hP (t01DilutionComplement t 1 g)
    (complement_mem P g hg M hgM t ht0 hthalf htM)
    (t01DilutionComplement_nonneg t 1 g)
    (complement_mass P g hg hmass M hgM t ht0 hthalf htM)

/-- The two actual species have weights t and 1-t. -/
def compensatingH1Binary : SpeciesFamily 1 :=
  SpeciesFamily.twoSpecies t ht0 (by linarith)
    (t01RelativeAbsoluteDensity P hP g hg hg0 hmass)
    (compensatingH1Species P hP g hg hmass M hgM t ht0 hthalf htM)

theorem compensatingH1Species_density (x : Torus 1) :
    (compensatingH1Species P hP g hg hmass M hgM t ht0 hthalf htM).density x =
      (P.density x - t * (t01RelativeAbsoluteDensity P hP g hg hg0 hmass).density x) / (1 - t) := by
  rw [compensatingH1Species, t01RelativeAbsoluteDensity_density,
    t01RelativeAbsoluteDensity_density]
  have hs := t01DilutionComplement_sq g hgM ht0.le hthalf
    (by norm_num : (0 : ℝ) ≤ 1) (by simpa only [mul_one] using htM) x
  have hd : 1 - t ≠ 0 := by linarith
  apply (eq_div_iff hd).2
  simp only [mul_one] at hs
  nlinarith [congrArg (fun z : ℝ => P.density x * z) hs]

/-- The compensating pair has EXACTLY the original reference barycenter. -/
theorem compensatingH1Binary_barycenter :
    (densityMeasure (barycenter (compensatingH1Binary P hP g hg hg0 hmass M hgM t ht0 hthalf htM)) :
      Measure (Torus 1)) = P.measure := by
  apply t01_relative_twoSpecies_barycenter P hP g (t01DilutionComplement t 1 g) hg
    (complement_mem P g hg M hgM t ht0 hthalf htM) hg0 (t01DilutionComplement_nonneg t 1 g)
    hmass (complement_mass P g hg hmass M hgM t ht0 hthalf htM) t ht0 (by linarith)
  intro x
  have hs := t01DilutionComplement_sq g hgM ht0.le hthalf
    (by norm_num : (0 : ℝ) ≤ 1) (by simpa only [mul_one] using htM) x
  simp only [mul_one] at hs
  linarith

/-- Actual complement Fisher information is quadratically small in the small
species weight, with its true native weak gradient and physical factor four. -/
theorem compensatingH1Species_fisher_bound :
    ordinaryRelativeFisher
      (densityMeasure (compensatingH1Species P hP g hg hmass M hgM t ht0 hthalf htM)) P ≤
      ENNReal.ofReal (32 * t ^ 2 * M ^ 2 *
        ∫ x, ‖weightedGradient P g hg x‖ ^ 2 ∂P.measure) := by
  rw [compensatingH1Species, t01_relative_fisher_real_energy]
  apply ENNReal.ofReal_le_ofReal
  have hs := t01DilutionComplement_energy_bound P hg hgM ht0.le hthalf
    (by norm_num : (0 : ℝ) ≤ 1) (by simpa only [mul_one] using htM)
    (complement_mem P g hg M hgM t ht0 hthalf htM)
  simp only [one_pow, mul_one] at hs
  linarith

/-- Quadratic KL bound for the ACTUAL compensating species. Only full weighted
H1 admissibility and a bounded relative root are used, not spatial smoothness. -/
theorem compensatingH1Species_entropy_bound :
    relativeEntropy
      (densityMeasure (compensatingH1Species P hP g hg hmass M hgM t ht0 hthalf htM)) P.measure ≤
      ENNReal.ofReal (4 * t ^ 2 * (M ^ 2 + 1) ^ 2) := by
  let v := t01DilutionComplement t 1 g
  have hv := complement_mem P g hg M hgM t ht0 hthalf htM
  have hv1 := complement_mass P g hg hmass M hgM t ht0 hthalf htM
  have hden : 0 < 1 - t := by linarith
  have hpoint (x : Torus 1) :
      InformationTheory.klFun (v x ^ 2) ≤ 4 * t ^ 2 * (M ^ 2 + 1) ^ 2 := by
    have hg2 : g x ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs (g x)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hgM x) 2
    have hs := t01DilutionComplement_sq g hgM ht0.le hthalf
      (by norm_num : (0 : ℝ) ≤ 1) (by simpa only [mul_one] using htM) x
    simp only [mul_one] at hs
    change (1 - t) * v x ^ 2 = 1 - t * g x ^ 2 at hs
    have hrad : 0 < 1 - t * g x ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hg2 ht0.le]
    have hvp : 0 < v x ^ 2 := by nlinarith
    have hkl : InformationTheory.klFun (v x ^ 2) ≤ (v x ^ 2 - 1) ^ 2 := by
      have hl := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hvp) hvp.le
      dsimp only [InformationTheory.klFun]
      nlinarith
    have heq : v x ^ 2 - 1 = t * (1 - g x ^ 2) / (1 - t) := by
      apply (eq_div_iff hden.ne').2
      nlinarith
    have hgdiff : |1 - g x ^ 2| ≤ M ^ 2 + 1 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (g x), sq_nonneg M]
    have hvdiff : |v x ^ 2 - 1| ≤ 2 * t * (M ^ 2 + 1) := by
      rw [heq, abs_div, abs_of_pos hden, abs_mul, abs_of_pos ht0]
      apply (div_le_iff₀ hden).2
      have hm := mul_le_mul_of_nonneg_left hgdiff ht0.le
      nlinarith [mul_nonneg ht0.le (sq_nonneg M),
        mul_nonneg (show 0 ≤ 1 - 2 * t by linarith) (show 0 ≤ t * (M ^ 2 + 1) by positivity)]
    have hsq := pow_le_pow_left₀ (abs_nonneg (v x ^ 2 - 1)) hvdiff 2
    rw [sq_abs] at hsq
    nlinarith
  rw [compensatingH1Species, t01RelativeAbsoluteDensity_entropy,
    homogeneousEntropy_eq_lintegral_klFun (by rw [hv1]; exact one_ne_zero), hv1]
  simp only [div_one, one_mul]
  calc (∫⁻ x, ENNReal.ofReal (InformationTheory.klFun (v x ^ 2)) ∂P.measure) ≤
      ∫⁻ _x, ENNReal.ofReal (4 * t ^ 2 * (M ^ 2 + 1) ^ 2) ∂P.measure :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpoint x)
    _ = _ := by simp

end Data
end DGPS.Examples.ThreeSpeciesCircle
