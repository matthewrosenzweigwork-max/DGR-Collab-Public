import DGPS.Examples.ThreeSpeciesCircle.InteractingCrossEntropy
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryDeficitCompactness

/-! Actual bounded interacting quotients control the full weighted ordinary information.
The bound is uniform over the original finite species count and every positive weight. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- At fixed h and admissible coupling, the actual quotient supplies a weighted ordinary
Fisher bound. No bound on species count, positive weights, information or entropy is assumed.
The true dissipation is proved finite before taking its real value. -/
theorem elementaryModel_boundedQuotient_weighted_information {h : ℝ} (hh : 0 < h) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (b : AbsoluteDrift (modelData h ε)) (M : ℝ), 0 ≤ M →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ F : SpeciesFamily 1,
          0 < speciesGap (modelData h ε) F →
          speciesQuotient (modelData h ε) b F ≤ ENNReal.ofReal M →
          (∑ i, F.weight i * (ordinaryFisher h (F.density i)).toReal) ≤ C := by
  obtain ⟨ε0, hε0, hεmax, hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  obtain ⟨K, hK, hC⟩ := elementaryC_family_entropy_bound hh 0
  refine ⟨ε0, hε0, hεmax, fun ε hε hεε0 b M hM => ?_⟩
  let T := 3 * M + ε * K
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  let η := 1 / (2 * (T + 1))
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨B, hB, hbudget⟩ := ordinaryEntropy_information_bound h η hη
  refine ⟨2 * T * B, by positivity, fun F hGpos hq => ?_⟩
  let E := ∑ i, F.weight i * (ordinaryEntropy h (F.density i)).toReal
  let I := ∑ i, F.weight i * (ordinaryFisher h (F.density i)).toReal
  let G : ℝ := speciesGap (modelData h ε) F
  let D := (speciesDissipation (modelData h ε) b F).toReal
  have hE : 0 ≤ E := Finset.sum_nonneg fun i _ => mul_nonneg (F.weight_nonneg i) ENNReal.toReal_nonneg
  have hI : 0 ≤ I := Finset.sum_nonneg fun i _ => mul_nonneg (F.weight_nonneg i) ENNReal.toReal_nonneg
  have hG : 0 < G := hGpos
  obtain ⟨hDfin, hDactual⟩ := elementaryModel_speciesDissipation_expansion h ε b F
  have hD : D = I + ε * elementaryC h 0 (barycenter F) + ε ^ 2 * elementaryJ h (barycenter F) := by
    change D = I + 2 * ε * _ + ε ^ 2 * elementaryJ h (barycenter F) at hDactual
    rw [hDactual]
    unfold elementaryC
    ring
  have hDq : D ≤ 2 * M * G := by
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hq
    unfold speciesQuotient at hr
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.coe_toReal, ENNReal.toReal_ofReal hM] at hr
    have hm := (div_le_iff₀ (by positivity : 0 < 2 * G)).mp hr
    change D ≤ _ at hm
    nlinarith
  have hCρ : |elementaryC h 0 (barycenter F)| ≤ K * E := hC F
  have hDlower : I - ε * K * E ≤ D := by
    have hc := mul_le_mul_of_nonneg_left (abs_le.mp hCρ).1 hε.le
    have hj := mul_nonneg (sq_nonneg ε) (elementaryJ_nonneg h (barycenter F))
    nlinarith
  have hgapF : G ≤ (3 / 2 : ℝ) * E := (hgap ε hε hεε0 F).2
  have hIE : I ≤ T * E := by
    have hg := mul_le_mul_of_nonneg_left hgapF (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)
    dsimp only [T]
    nlinarith
  have hEI : E ≤ η * I + B := by
    have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hbudget (F.density i)) (F.weight_nonneg i)
    have he (i : Fin F.count) :
        F.weight i * (η * (ordinaryFisher h (F.density i)).toReal + B) =
          η * (F.weight i * (ordinaryFisher h (F.density i)).toReal) + B * F.weight i := by ring
    simp_rw [he] at hs
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, F.weight_sum, mul_one] at hs
    exact hs
  have hηT : T * η ≤ 1 / 2 := by
    dsimp only [η]
    rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 2 * (T + 1))]
    linarith
  have h1 := mul_le_mul_of_nonneg_left hEI hT
  have h2 := mul_le_mul_of_nonneg_right hηT hI
  change I ≤ 2 * T * B
  nlinarith

end DGPS.Examples.ThreeSpeciesCircle
