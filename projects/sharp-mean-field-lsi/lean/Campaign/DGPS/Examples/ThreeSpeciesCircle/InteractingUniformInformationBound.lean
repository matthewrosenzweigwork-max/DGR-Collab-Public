import DGPS.Examples.ThreeSpeciesCircle.InteractingCrossEntropy
import DGPS.Variational.SpeciesInclusion
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryDeficitCompactness

/-! Actual bounded interacting quotients control the full weighted ordinary information.
The bound is uniform over the original finite species count and every positive weight. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- At fixed h, one quotient bound supplies a weighted ordinary Fisher bound UNIFORMLY
over the entire small coupling interval, with the constant chosen before epsilon. No bound on species count, positive weights, information or entropy is assumed.
The true dissipation is proved finite before taking its real value. -/
theorem elementaryModel_uniform_boundedQuotient_information {h : ℝ} (hh : 0 < h) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ M : ℝ, 0 ≤ M →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1),
          0 < speciesGap (modelData h ε) F →
          speciesQuotient (modelData h ε) b F ≤ ENNReal.ofReal M →
          (∑ i, F.weight i * (ordinaryFisher h (F.density i)).toReal) ≤ C := by
  obtain ⟨εG, hεG, hεmax, hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  obtain ⟨K, hK, hC⟩ := elementaryC_family_entropy_bound hh 0
  let ε0 := min εG 1
  refine ⟨ε0, lt_min hεG one_pos, (min_le_left _ _).trans hεmax, fun M hM => ?_⟩
  let T := 3 * M + K
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  let η := 1 / (2 * (T + 1))
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨B, hB, hbudget⟩ := ordinaryEntropy_information_bound h η hη
  refine ⟨2 * T * B, by positivity, fun ε hε hεε0 b F hGpos hq => ?_⟩
  have heG : ε < εG := hεε0.trans_le (min_le_left _ _)
  have he1 : ε ≤ 1 := (hεε0.trans_le (min_le_right _ _)).le
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
  have hgapF : G ≤ (3 / 2 : ℝ) * E := (hgap ε hε heG F).2
  have hIE : I ≤ T * E := by
    have hg := mul_le_mul_of_nonneg_left hgapF (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)
    have heK := mul_le_mul_of_nonneg_right he1 (mul_nonneg hK.le hE)
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

/-- The same common information constant applies to every actual scalar competitor
throughout the fixed coupling interval; it is selected before epsilon and the drift. -/
theorem elementaryModel_uniform_scalar_information {h : ℝ} (hh : 0 < h) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ M : ℝ, 0 ≤ M →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ (b : AbsoluteDrift (modelData h ε)) (ρ : AbsoluteDensity 1),
          0 < scalarGap (modelData h ε) ρ →
          scalarQuotient (modelData h ε) b ρ ≤ ENNReal.ofReal M →
          (ordinaryFisher h ρ).toReal ≤ C := by
  obtain ⟨ε0, hε0, hεmax, hmain⟩ := elementaryModel_uniform_boundedQuotient_information hh
  refine ⟨ε0, hε0, hεmax, fun M hM => ?_⟩
  obtain ⟨C, hC, hF⟩ := hmain M hM
  refine ⟨C, hC, fun ε hε hεsmall b ρ hG hq => ?_⟩
  have hi := hF ε hε hεsmall b (SpeciesFamily.single ρ)
    (by rw [speciesGap_single]; exact hG)
    (by rw [speciesQuotient_single]; exact hq)
  simpa only [sum_single_count, SpeciesFamily.single_weight, SpeciesFamily.single_density, one_mul] using hi

end DGPS.Examples.ThreeSpeciesCircle
