import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesCorrections
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesAttainment
import DGPS.Examples.ThreeSpeciesCircle.InteractingUniformInformationBound

/-! Genuine positive-weight species splitting for full-family minimizer comparisons.
The added species has strictly positive weight; no zero-weight competitor or lower
bound on the original weight is introduced. Quantitative localization is downstream. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Replace a positive fraction of one original species by another actual density,
retaining every original species with positive weight and adding one actual label. -/
def finiteSpeciesSplit (F : SpeciesFamily 1) (s : Fin F.count) (τ : AbsoluteDensity 1)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) : SpeciesFamily 1 where
  count := ⟨(F.count : ℕ) + 1, Nat.succ_pos _⟩
  weight := Fin.cases (t * F.weight s)
    (fun i => F.weight i - if i = s then t * F.weight s else 0)
  weight_pos := by
    classical
    change ∀ i : Fin ((F.count : ℕ) + 1),
      (0 : ℝ) < Fin.cases (motive := fun _ : Fin ((F.count : ℕ) + 1) => ℝ) (t * F.weight s)
        (fun j => F.weight j - if j = s then t * F.weight s else 0) i
    intro i
    refine Fin.cases (mul_pos ht (F.weight_pos s)) (fun j => ?_) i
    change 0 < F.weight j - if j = s then t * F.weight s else 0
    by_cases hj : j = s
    · simp only [hj, if_true]
      have hh := mul_pos (sub_pos.mpr ht1) (F.weight_pos s)
      nlinarith only [hh]
    · simpa only [if_neg hj, sub_zero] using F.weight_pos j
  weight_sum := by
    classical
    change (∑ i : Fin ((F.count : ℕ) + 1),
      Fin.cases (motive := fun _ : Fin ((F.count : ℕ) + 1) => ℝ) (t * F.weight s)
        (fun j => F.weight j - if j = s then t * F.weight s else 0) i) = (1 : ℝ)
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    rw [Finset.sum_sub_distrib, F.weight_sum]
    have hs : (∑ i : Fin F.count, if i = s then t * F.weight s else 0) = t * F.weight s := by simp
    rw [hs]
    ring
  density := Fin.cases τ F.density

/-- Every real-valued species statistic has the exact affine split formula. -/
theorem finiteSpeciesSplit_weighted_statistic (F : SpeciesFamily 1) (s : Fin F.count)
    (τ : AbsoluteDensity 1) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (L : AbsoluteDensity 1 → ℝ) :
    (∑ i, (finiteSpeciesSplit F s τ t ht ht1).weight i *
      L ((finiteSpeciesSplit F s τ t ht ht1).density i)) =
      (∑ i, F.weight i * L (F.density i)) +
        t * F.weight s * (L τ - L (F.density s)) := by
  classical
  change (∑ i : Fin ((F.count : ℕ) + 1),
    (Fin.cases (t * F.weight s) (fun j => F.weight j - if j = s then t * F.weight s else 0) i) *
      L (Fin.cases τ F.density i)) = _
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  have he (i : Fin F.count) :
      (F.weight i - if i = s then t * F.weight s else 0) * L (F.density i) =
        F.weight i * L (F.density i) -
          if i = s then t * F.weight s * L (F.density s) else 0 := by
    by_cases hi : i = s <;> simp only [hi, ite_true, ite_false]
    · ring
    · ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  have hs : (∑ i : Fin F.count, if i = s then t * F.weight s * L (F.density s) else 0) =
      t * F.weight s * L (F.density s) := by simp
  rw [hs]
  ring

/-- The exact barycenter observable change is linear in the fraction and original
weight; the original densities have only their canonical H1 regularity. -/
theorem finiteSpeciesSplit_moment (F : SpeciesFamily 1) (s : Fin F.count)
    (τ : AbsoluteDensity 1) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (g : Torus 1 → ℝ) (hg : Continuous g) :
    (∫ x, g x ∂(densityMeasure (barycenter (finiteSpeciesSplit F s τ t ht ht1)) : Measure (Torus 1))) =
      (∫ x, g x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) +
        t * F.weight s * ((∫ x, g x ∂(densityMeasure τ : Measure (Torus 1))) -
          ∫ x, g x ∂(densityMeasure (F.density s) : Measure (Torus 1))) := by
  rw [Structural.budget_integral_barycenter _ hg, Structural.budget_integral_barycenter _ hg]
  exact finiteSpeciesSplit_weighted_statistic F s τ ht ht1
    (fun ρ => ∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1)))

/-- True Hellinger distance controls the genuine split observable error with the
FULL small factor t times the active weight. No square root of that weight is lost. -/
theorem finiteSpeciesSplit_moment_error (F : SpeciesFamily 1) (s : Fin F.count)
    (τ : AbsoluteDensity 1) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {g : Torus 1 → ℝ} (hg : Continuous g) {B : ℝ} (hB : 0 ≤ B)
    (hgB : ∀ x, |g x| ≤ B) :
    |(∫ x, g x ∂(densityMeasure (barycenter (finiteSpeciesSplit F s τ t ht ht1)) : Measure (Torus 1))) -
      (∫ x, g x ∂(densityMeasure (barycenter F) : Measure (Torus 1)))| ≤
      2 * B * (t * F.weight s) * Real.sqrt (rootDistanceSq (F.density s) τ) := by
  rw [finiteSpeciesSplit_moment F s τ ht ht1 g hg, add_sub_cancel_left,
    abs_mul, abs_of_pos (mul_pos ht (F.weight_pos s)), abs_sub_comm]
  have he := mul_le_mul_of_nonneg_left
    (absolute_moment_error_le_root_distance (F.density s) τ hg hB hgB)
      (mul_pos ht (F.weight_pos s)).le
  convert he using 1 <;> ring

/-- Both ACTUAL changing-force corrections admit a constant before every family,
active label, replacement density and fraction, retaining the entire t*weight gain. -/
theorem finiteSpeciesSplit_correction_error (h a : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F : SpeciesFamily 1) (s : Fin F.count) (τ : AbsoluteDensity 1)
      (t : ℝ) (ht : 0 < t) (ht1 : t < 1),
      |elementaryC h a (barycenter (finiteSpeciesSplit F s τ t ht ht1)) -
        elementaryC h a (barycenter F)| ≤
          K * (t * F.weight s) * Real.sqrt (rootDistanceSq (F.density s) τ) ∧
      |elementaryJ h (barycenter (finiteSpeciesSplit F s τ t ht ht1)) -
        elementaryJ h (barycenter F)| ≤
          K * (t * F.weight s) * Real.sqrt (rootDistanceSq (F.density s) τ) := by
  obtain ⟨M, hM, hobs⟩ := elementaryCorrection_coordinates_bound h
  obtain ⟨L, hL, hLip⟩ := elementaryCorrection_moment_lipschitz h a
  refine ⟨2 * M * L, by positivity, fun F s τ t ht ht1 => ?_⟩
  have hw := F.weight_pos s
  have hd : 0 ≤ 2 * M * (t * F.weight s) * Real.sqrt (rootDistanceSq (F.density s) τ) :=
    by positivity
  have he := hLip (barycenter (finiteSpeciesSplit F s τ t ht ht1)) (barycenter F)
    (2 * M * (t * F.weight s) * Real.sqrt (rootDistanceSq (F.density s) τ)) hd
    (fun i => finiteSpeciesSplit_moment_error F s τ ht ht1
      (continuous_elementaryCorrectionObservable h i) hM.le (hobs i))
  constructor
  · convert he.1 using 1 <;> ring
  · convert he.2 using 1 <;> ring

/-- Full-rate cost is nonnegative even on zero-gap actual families. Thus genuine
species splitting and merging need no extra positive-gap preservation premise. -/
theorem elementaryModel_speciesRate_cost_nonneg (h ε : ℝ)
    (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1) :
    0 ≤ (speciesDissipation (modelData h ε) b F).toReal -
      2 * (speciesRate (modelData h ε) b).toReal * (speciesGap (modelData h ε) F : ℝ) := by
  by_cases hG : speciesGap (modelData h ε) F = 0
  · simp only [hG, NNReal.coe_zero, mul_zero, sub_zero]
    exact ENNReal.toReal_nonneg
  have hGp : 0 < speciesGap (modelData h ε) F := pos_iff_ne_zero.mpr hG
  have hGr : 0 < (speciesGap (modelData h ε) F : ℝ) := hGp
  have hDfin := (elementaryModel_speciesDissipation_expansion h ε b F).1
  have hden : (2 : ℝ≥0∞) * (speciesGap (modelData h ε) F : ℝ≥0∞) ≠ 0 := by positivity
  have hQfin : speciesQuotient (modelData h ε) b F ≠ ⊤ := by
    unfold speciesQuotient
    exact ENNReal.div_ne_top hDfin hden
  have he := ENNReal.toReal_mono hQfin (speciesRate_le (modelData h ε) b F hGp)
  unfold speciesQuotient at he
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal] at he
  have hm := (le_div_iff₀ (by positivity : 0 < (2 : ℝ) * (speciesGap (modelData h ε) F : ℝ))).1 he
  nlinarith only [hm]

/-- The actual quotient cannot lie more than linearly below the ordinary rate,
uniformly before every species count and positive weight. -/
theorem elementaryModel_quotient_lower_ordinary_linear {h : ℝ} (hh : 0 < h) :
    ∃ K ε0 : ℝ, 0 < K ∧ 0 < ε0 ∧ ε0 ≤ epsMax h ∧
      ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1),
          0 < speciesGap (modelData h ε) F →
            (ordinaryLSRate (ordinaryReference h)).toReal - K * ε ≤
              (speciesQuotient (modelData h ε) b F).toReal := by
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  obtain ⟨K, hK, hC⟩ := elementaryC_family_entropy_bound hh a
  obtain ⟨ε0, hε0, hεmax, hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  refine ⟨K, ε0, hK, hε0, hεmax, fun ε hε hεsmall b F hGp => ?_⟩
  let E := ∑ i, F.weight i * (ordinaryEntropy h (F.density i)).toReal
  let G : ℝ := speciesGap (modelData h ε) F
  have hG : 0 < G := hGp
  obtain ⟨hD0, hJ, hDfinite, _, hdef⟩ :=
    elementaryModel_exactDeficitExpansion hh hε (hεsmall.trans_le hεmax) b F
  have hClo := mul_le_mul_of_nonneg_left (abs_le.mp (hC F)).1 hε.le
  have hJε := mul_nonneg (sq_nonneg ε) hJ
  have hE : E ≤ 2 * G := by
    have hg := (hgap ε hε hεsmall F).1
    change (1 / 2 : ℝ) * E ≤ G at hg
    linarith
  have hE' := mul_le_mul_of_nonneg_left hE (mul_nonneg hε.le hK.le)
  have hD : 2 * (a - K * ε) * G ≤ (speciesDissipation (modelData h ε) b F).toReal := by
    change (speciesDissipation (modelData h ε) b F).toReal - 2 * a * G = _ at hdef
    change ε * -(K * E) ≤ ε * elementaryC h a (barycenter F) at hClo
    nlinarith only [hdef, hD0, hJε, hClo, hE']
  unfold speciesQuotient
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal]
  change a - K * ε ≤ (speciesDissipation (modelData h ε) b F).toReal / (2 * G)
  apply (le_div_iff₀ (by positivity : 0 < 2 * G)).2
  nlinarith only [hD]

/-- Actual full-rate equality gives exactly zero real cost at a positive-gap
attaining family, with actual finite dissipation established first. -/
theorem elementaryModel_speciesRate_cost_eq_zero (h ε : ℝ)
    (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1)
    (hG : 0 < speciesGap (modelData h ε) F)
    (hmin : speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b) :
    (speciesDissipation (modelData h ε) b F).toReal -
      2 * (speciesRate (modelData h ε) b).toReal * (speciesGap (modelData h ε) F : ℝ) = 0 := by
  have hDfin := (elementaryModel_speciesDissipation_expansion h ε b F).1
  have hGr : 0 < (speciesGap (modelData h ε) F : ℝ) := hG
  have he := congrArg ENNReal.toReal hmin
  unfold speciesQuotient at he
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal] at he
  have hm := (div_eq_iff (by positivity : (2 : ℝ) * (speciesGap (modelData h ε) F : ℝ) ≠ 0)).1 he
  nlinarith only [hm]

end DGPS.Examples.ThreeSpeciesCircle
