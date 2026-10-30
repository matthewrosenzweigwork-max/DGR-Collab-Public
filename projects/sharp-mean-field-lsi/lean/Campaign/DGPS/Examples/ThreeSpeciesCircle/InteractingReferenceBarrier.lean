import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarCompactness
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryReferenceLocalStability

/-! Actual quadratic reference estimates in the original Haar square-root H1 metric.
All constants precede the full original absolute-density competitor and the coupling. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Bounded entropy Taylor control at the actual reference in the original H1 metric.
Only a.e. positivity of the stored competitor root is used. -/
theorem ordinaryReference_entropy_quadratic (h : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ ρ : AbsoluteDensity 1,
      ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ (str025_w h) ≤ η →
      (ordinaryEntropy h ρ).toReal ≤
        5 * ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ (str025_w h) ^ 2 := by
  let m := Real.exp (-|h|)
  have hm : 0 < m := Real.exp_pos _
  refine ⟨m / 4, by positivity, fun ρ hnear => ?_⟩
  let d := ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ (str025_w h)
  have hclose : ∀ᵐ x ∂haar 1, |str025_u h ρ x - 1| ≤ (1 / 4 : ℝ) := by
    have hrel := ordinaryRoot_relative_ae_near (ordinaryReferenceAbsolute h) ρ
      (str025_w h) (str025_continuous_w h) (str025_w_pos h) (EventuallyEq.refl _ _)
      hm (str025_w_ge h) (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (show ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ (str025_w h) ≤ m * (1 / 4) by
        convert hnear using 1 <;> ring)
    simpa only [str025_u_eq] using hrel
  have ht := str025_entropy_close h ρ (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) hclose
  rw [← str025_Hr_eq] at ht
  let L := ∫ x, (ρ.sqrt x - str025_w h x) ^ 2 ∂haar 1
  have hL : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  have hH : (ordinaryEntropy h ρ).toReal ≤ (9 / 2 : ℝ) * L := by
    rw [ordinaryEntropy_eq, ENNReal.toReal_ofReal']
    apply max_le
    · have hh := (abs_le.mp ht).2
      change _ ≤ (9 / 2 : ℝ) * L
      linarith
    · positivity
  have hu := ρ.memLp_sqrt.sub (ordinaryReferenceAbsolute h).memLp_sqrt
  change MemLp (fun x => ρ.sqrt x - str025_w h x) 2 (haar 1) at hu
  let A := (eLpNorm (fun x => ρ.sqrt x - str025_w h x) 2 (haar 1)).toReal
  let B := (eLpNorm (fun x => weakGradient ρ.sqrt ρ.sqrt_mem x -
    weakGradient (ordinaryReferenceAbsolute h).sqrt (ordinaryReferenceAbsolute h).sqrt_mem x)
      2 (haar 1)).toReal
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hA2 : A ^ 2 = L := by
    dsimp only [A, L]
    rw [toReal_eLpNorm_two hu, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
  have hd : d = A + B := rfl
  change (ordinaryEntropy h ρ).toReal ≤ 5 * d ^ 2
  nlinarith [sq_nonneg B, mul_nonneg hA hB]

/-- Both actual interaction corrections are quadratic near the reference. The coupling
threshold, neighborhood and constant are fixed before epsilon and every original competitor. -/
theorem elementaryModel_reference_quadratic_bounds {h : ℝ} (hh : 0 < h) (a : ℝ) :
    ∃ ε0 η K : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 < η ∧ 0 < K ∧
      ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ ρ : AbsoluteDensity 1,
        ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ (str025_w h) ≤ η →
        |elementaryC h a ρ| ≤
          K * ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ (str025_w h) ^ 2 ∧
        (scalarGap (modelData h ε) ρ : ℝ) ≤
          K * ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ (str025_w h) ^ 2 := by
  obtain ⟨ε0, hε0, hεmax, hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  obtain ⟨η, hη, hH⟩ := ordinaryReference_entropy_quadratic h
  obtain ⟨Kc, hKc, hC⟩ := elementaryC_family_entropy_bound hh a
  let K := 8 + 5 * Kc
  refine ⟨ε0, η, K, hε0, hεmax, hη, by dsimp [K]; positivity,
    fun ε hε hεε0 ρ hnear => ?_⟩
  let d := ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ (str025_w h)
  have hHρ : (ordinaryEntropy h ρ).toReal ≤ 5 * d ^ 2 := hH ρ hnear
  have hCρ : |elementaryC h a ρ| ≤ Kc * (ordinaryEntropy h ρ).toReal := by
    have hc := hC (SpeciesFamily.single ρ)
    have he : elementaryC h a (barycenter (SpeciesFamily.single ρ)) = elementaryC h a ρ := by
      unfold elementaryC
      simp_rw [densityMeasure_barycenter_single, barycenter_single_density]
    rw [he] at hc
    simpa only [sum_single_count, SpeciesFamily.single_weight,
      SpeciesFamily.single_density, one_mul] using hc
  have hg : (scalarGap (modelData h ε) ρ : ℝ) ≤ (3 / 2 : ℝ) * (ordinaryEntropy h ρ).toReal := by
    have hg := (hgap ε hε hεε0 (SpeciesFamily.single ρ)).2
    simpa only [speciesGap_single, sum_single_count, SpeciesFamily.single_weight,
      SpeciesFamily.single_density, one_mul] using hg
  constructor
  · have hm := mul_le_mul_of_nonneg_left hHρ hKc.le
    dsimp only [K]
    nlinarith [sq_nonneg d]
  · dsimp only [K]
    nlinarith [mul_nonneg hKc.le (sq_nonneg d)]

/-- Exact actual scalar deficit at any real comparison rate, obtained from the proved
model identities rather than a stationarity or attainment assumption. -/
theorem elementaryModel_scalar_deficit_real {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) (ρ : AbsoluteDensity 1) (a : ℝ) :
    (scalarDissipation (modelData h ε) b ρ).toReal - 2 * a * (scalarGap (modelData h ε) ρ : ℝ) =
      (ordinaryFisher h ρ).toReal - 2 * a * (ordinaryEntropy h ρ).toReal +
        ε * elementaryC h a ρ + ε ^ 2 * elementaryJ h ρ := by
  have hD := (elementaryModel_scalarDissipation_real h ε b ρ).2
  have hG : (scalarGap (modelData h ε) ρ : ℝ) =
      (ordinaryEntropy h ρ).toReal + ε / 2 * elementaryQ h (densityMeasure ρ) := by
    have hg := elementaryModel_speciesGap_expansion hh hε hεmax (SpeciesFamily.single ρ)
    simpa only [speciesGap_single, sum_single_count, SpeciesFamily.single_weight,
      SpeciesFamily.single_density, one_mul, densityMeasure_barycenter_single] using hg
  have hC : elementaryC h a ρ = elementaryC h 0 ρ - a * elementaryQ h (densityMeasure ρ) := by
    unfold elementaryC
    ring
  rw [hD, hG, hC]
  ring

/-- The actual scalar quotient has a strict barrier above the canonical ordinary rate
in a genuine original-H1 neighborhood of the reference. No scalar optimizer, positive-gap
limit or desired barrier is assumed. Thresholds are fixed after h and before epsilon/b/rho. -/
theorem elementaryModel_reference_strict_barrier :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ r ε0 η : ℝ, (ordinaryLSRate (ordinaryReference h)).toReal < r ∧
        0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 < η ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
            ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ (str025_w h) ≤ η →
            ENNReal.ofReal r ≤ scalarQuotient (modelData h ε) b ρ := by
  obtain ⟨δ, hδ, hlocal⟩ := threefold_reference_localHaar_stability
  refine ⟨δ, hδ, fun h hh hhd => ?_⟩
  obtain ⟨ηL, c, hηL, hc, hstab⟩ := hlocal h hh hhd
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  obtain ⟨εQ, ηQ, K, hεQ, hεQmax, hηQ, hK, hquad⟩ :=
    elementaryModel_reference_quadratic_bounds hh a
  let ε0 := min εQ (c / (2 * K))
  let η := min ηL ηQ
  let r := a + c / (4 * K)
  have hε0 : 0 < ε0 := lt_min hεQ (div_pos hc (by positivity))
  have hη : 0 < η := lt_min hηL hηQ
  have har : a < r := by
    have hp := div_pos hc (by positivity : 0 < 4 * K)
    dsimp only [r]
    linarith
  have hr : 0 < r := ha.trans_lt har
  refine ⟨r, ε0, η, har, hε0, (min_le_left _ _).trans hεQmax, hη,
    fun ε hε hεε0 b ρ hGpos hnear => ?_⟩
  let d := ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ (str025_w h)
  let G : ℝ := scalarGap (modelData h ε) ρ
  let D := (scalarDissipation (modelData h ε) b ρ).toReal
  have hG : 0 < G := hGpos
  have hS := hstab ρ (hnear.trans (min_le_left _ _))
  obtain ⟨hC, hGap⟩ := hquad ε hε (hεε0.trans_le (min_le_left _ _)) ρ
    (hnear.trans (min_le_right _ _))
  have hεK : ε * K ≤ c / 2 := by
    have he := (lt_div_iff₀ (by positivity : 0 < 2 * K)).mp
      (hεε0.trans_le (min_le_right _ _))
    nlinarith
  have hD := elementaryModel_scalar_deficit_real hh hε
    (hεε0.trans_le ((min_le_left _ _).trans hεQmax)) b ρ a
  have hClo := mul_le_mul_of_nonneg_left (abs_le.mp hC).1 hε.le
  have hJ := mul_nonneg (sq_nonneg ε) (elementaryJ_nonneg h ρ)
  have hKD := mul_le_mul_of_nonneg_right hεK (sq_nonneg d)
  have hDef : c / 2 * d ^ 2 ≤ D - 2 * a * G := by
    change c * d ^ 2 ≤ _ at hS
    change D - 2 * a * G = _ at hD
    nlinarith
  have hBarrier : 2 * r * G ≤ D := by
    have hm := mul_le_mul_of_nonneg_left hGap
      (div_nonneg hc.le (by positivity : 0 ≤ 2 * K))
    have he : c / (2 * K) * (K * d ^ 2) = c / 2 * d ^ 2 := by
      field_simp [hK.ne']
    change c / (2 * K) * G ≤ c / (2 * K) * (K * d ^ 2) at hm
    rw [he] at hm
    have hrEq : 2 * r * G = 2 * a * G + c / (2 * K) * G := by
      dsimp only [r]
      field_simp [hK.ne'] <;> ring
    rw [hrEq]
    linarith
  have hDfin := (elementaryModel_scalarDissipation_real h ε b ρ).1
  have hden0 : 2 * (scalarGap (modelData h ε) ρ : ℝ≥0∞) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast hGpos.ne')
  have hdent : 2 * (scalarGap (modelData h ε) ρ : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
  unfold scalarQuotient
  apply (ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdent)).2
  rw [← ENNReal.ofReal_toReal hDfin]
  have hden : 2 * (scalarGap (modelData h ε) ρ : ℝ≥0∞) = ENNReal.ofReal (2 * G) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_coe_nnreal]
  rw [hden, ← ENNReal.ofReal_mul hr.le]
  apply ENNReal.ofReal_le_ofReal
  nlinarith

end DGPS.Examples.ThreeSpeciesCircle
