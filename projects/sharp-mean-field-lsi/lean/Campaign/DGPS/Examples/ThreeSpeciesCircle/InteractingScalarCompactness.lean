import DGPS.Examples.ThreeSpeciesCircle.InteractingCrossEntropy
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryOptimizers
import DGPS.Variational.SpeciesInclusion

/-! Actual bounded scalar quotients imply ordinary quotient bounds, hence genuine
one-dimensional compactness on the original absolute H1 domain. The limiting actual
gap is not assumed positive or asserted positive by this first compactness leaf. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The full-domain actual scalar dissipation, with its finite real value established
by the genuine one-species square identity. -/
theorem elementaryModel_scalarDissipation_real (h ε : ℝ)
    (b : AbsoluteDrift (modelData h ε)) (ρ : AbsoluteDensity 1) :
    scalarDissipation (modelData h ε) b ρ ≠ ⊤ ∧
      (scalarDissipation (modelData h ε) b ρ).toReal =
        (ordinaryFisher h ρ).toReal + ε * elementaryC h 0 ρ + ε ^ 2 * elementaryJ h ρ := by
  obtain ⟨hD, hnonneg⟩ := elementaryModel_oneSpecies_dissipation h ε b ρ ρ
  have he : (ordinaryFisher h ρ).toReal + ε * elementaryC h 0 ρ + ε ^ 2 * elementaryJ h ρ =
      (ordinaryFisher h ρ).toReal +
        2 * ε * (∫ x, ρ.density x * elementaryAK h (densityMeasure ρ) x ∂haar 1) +
        ε ^ 2 * (∫ x, ρ.density x * (elementaryKprime h (densityMeasure ρ) x) ^ 2 ∂haar 1) := by
    unfold elementaryC elementaryJ
    ring
  change scalarDissipation (modelData h ε) b ρ = _ at hD
  refine ⟨by rw [hD]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [he, hD, ENNReal.toReal_ofReal hnonneg]

/-- On an actual h-dependent coupling interval, a bound on the interacting scalar
quotient gives a bound on the ordinary quotient. No information bound, smoothness,
positive density, desired rate or positive-gap limit is a premise. -/
theorem elementaryModel_scalar_boundedQuotient_transfer {h : ℝ} (hh : 0 < h) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (b : AbsoluteDrift (modelData h ε)) (M : ℝ), 0 ≤ M →
        ∃ L : ℝ≥0, ∀ ρ : AbsoluteDensity 1,
          0 < scalarGap (modelData h ε) ρ →
          scalarQuotient (modelData h ε) b ρ ≤ ENNReal.ofReal M →
          0 < ordinaryEntropy h ρ ∧ str025_quot h ρ ≤ L := by
  obtain ⟨ε0, hε0, hεmax, hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  obtain ⟨K, hK, hC⟩ := elementaryC_family_entropy_bound hh 0
  refine ⟨ε0, hε0, hεmax, fun ε hε hεε0 b M hM => ?_⟩
  let T := 3 * M + ε * K
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  let L : ℝ≥0 := ⟨T / 2, by positivity⟩
  refine ⟨L, fun ρ hGpos hq => ?_⟩
  let G : ℝ := scalarGap (modelData h ε) ρ
  let H := (ordinaryEntropy h ρ).toReal
  let I := (ordinaryFisher h ρ).toReal
  let D := (scalarDissipation (modelData h ε) b ρ).toReal
  have hG : 0 < G := hGpos
  have hH : 0 ≤ H := ENNReal.toReal_nonneg
  have hI : 0 ≤ I := ENNReal.toReal_nonneg
  have hgapρ : G ≤ (3 / 2 : ℝ) * H := by
    have hg := (hgap ε hε hεε0 (SpeciesFamily.single ρ)).2
    simpa only [speciesGap_single, sum_single_count, SpeciesFamily.single_weight,
      SpeciesFamily.single_density, one_mul] using hg
  have hHpos : 0 < H := by nlinarith
  have hHp : 0 < ordinaryEntropy h ρ := by
    exact pos_iff_ne_zero.mpr (by intro hz; simp only [H, hz, ENNReal.toReal_zero] at hHpos; linarith)
  obtain ⟨hDfin, hDval⟩ := elementaryModel_scalarDissipation_real h ε b ρ
  have hDq : D ≤ 2 * M * G := by
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hq
    unfold scalarQuotient at hr
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.coe_toReal, ENNReal.toReal_ofReal hM] at hr
    have hm := (div_le_iff₀ (by positivity : 0 < 2 * G)).mp hr
    dsimp only [D, G] at *
    nlinarith
  have hCρ : |elementaryC h 0 ρ| ≤ K * H := by
    have hc := hC (SpeciesFamily.single ρ)
    have he : elementaryC h 0 (barycenter (SpeciesFamily.single ρ)) = elementaryC h 0 ρ := by
      unfold elementaryC
      simp_rw [densityMeasure_barycenter_single, barycenter_single_density]
    rw [he] at hc
    simpa only [sum_single_count, SpeciesFamily.single_weight,
      SpeciesFamily.single_density, one_mul] using hc
  have hDlower : I - ε * K * H ≤ D := by
    change D = I + ε * elementaryC h 0 ρ + ε ^ 2 * elementaryJ h ρ at hDval
    have hc := mul_le_mul_of_nonneg_left (abs_le.mp hCρ).1 hε.le
    have hj := mul_nonneg (sq_nonneg ε) (elementaryJ_nonneg h ρ)
    nlinarith
  have hIH : I ≤ T * H := by
    have hg := mul_le_mul_of_nonneg_left hgapρ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)
    dsimp only [T]
    nlinarith
  refine ⟨hHp, ?_⟩
  change ordinaryFisher h ρ / (2 * ordinaryEntropy h ρ) ≤ (L : ℝ≥0∞)
  have hden0 : 2 * ordinaryEntropy h ρ ≠ 0 := mul_ne_zero (by norm_num) hHp.ne'
  have hdent : 2 * ordinaryEntropy h ρ ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (str025_entropy_ne_top h ρ)
  apply (ENNReal.div_le_iff hden0 hdent).2
  rw [← ENNReal.ofReal_toReal (str025_fisher_ne_top h ρ),
    ← ENNReal.ofReal_toReal (str025_entropy_ne_top h ρ)]
  have hL : (L : ℝ≥0∞) = ENNReal.ofReal (T / 2) := (ENNReal.ofReal_coe_nnreal).symm
  rw [hL, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ T / 2)]
  apply ENNReal.ofReal_le_ofReal
  change I ≤ T / 2 * (2 * H)
  nlinarith

/-- Actual interacting bounded-quotient compactness at a fixed admissible coupling.
The Fisher bound is derived from the actual quotient through the proved transfer.
The conclusion deliberately retains a possibly zero-gap limit for the next exclusion step. -/
theorem elementaryModel_scalar_boundedQuotient_compactness {h : ℝ} (hh : 0 < h) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ (b : AbsoluteDrift (modelData h ε)) (M : ℝ), 0 ≤ M →
      ∀ ρ : ℕ → AbsoluteDensity 1,
        (∀ n, 0 < scalarGap (modelData h ε) (ρ n)) →
        (∀ n, scalarQuotient (modelData h ε) b (ρ n) ≤ ENNReal.ofReal M) →
        ∃ B : ℝ, 0 ≤ B ∧
          (∀ n, DGPS.Analysis.circleFisherInformation (ρ n) ≤ B ∧
            DGPS.Analysis.circleEntropy (ρ n) ≤ B) ∧
          ∃ (φ : ℕ → ℕ) (ρL : AbsoluteDensity 1) (η : ℕ → ℝ),
            StrictMono φ ∧ Tendsto η atTop (𝓝 0) ∧
            (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n)).sqrt x - ρL.sqrt x| ≤ η n) ∧
            Tendsto (fun n => DGPS.Analysis.circleEntropy (ρ (φ n))) atTop
              (𝓝 (DGPS.Analysis.circleEntropy ρL)) ∧
            Tendsto (fun n => ordinaryEntropy h (ρ (φ n))) atTop (𝓝 (ordinaryEntropy h ρL)) ∧
            ENNReal.ofReal (DGPS.Analysis.circleFisherInformation ρL) ≤
              liminf (fun n => ENNReal.ofReal (DGPS.Analysis.circleFisherInformation (ρ (φ n)))) atTop ∧
            ordinaryFisher h ρL ≤ liminf (fun n => ordinaryFisher h (ρ (φ n))) atTop := by
  obtain ⟨ε0, hε0, hεmax, htransfer⟩ := elementaryModel_scalar_boundedQuotient_transfer hh
  refine ⟨ε0, hε0, hεmax, fun ε hε hεε0 b M hM ρ hpos hq => ?_⟩
  obtain ⟨L, hL⟩ := htransfer ε hε hεε0 b M hM
  exact circle_boundedQuotient_compactness (abs_nonneg h) L h le_rfl ρ
    (fun n => (hL (ρ n) (hpos n) (hq n)).1)
    (fun n => (hL (ρ n) (hpos n) (hq n)).2)

end DGPS.Examples.ThreeSpeciesCircle
