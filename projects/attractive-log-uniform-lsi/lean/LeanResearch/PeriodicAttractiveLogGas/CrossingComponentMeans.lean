import LeanResearch.PeriodicAttractiveLogGas.ConditionalVarianceAssembly
import LeanResearch.PeriodicAttractiveLogGas.ConditionalNormCrossing

/-! Actual component crossing means and mixture exponential transfer for
source lines 2905–2920. The probabilities are the original two-cell Gibbs
laws and their existing crossing probability, not substituted observables. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace PeriodicAttractiveLogGas.CrossingComponentMeans

open MeshCells MeshAdjacentCells LabelOccupations CellRestrictions OneCoordinateConditionals
open BoundaryCovarianceSplitting ConditionalSourceDerivatives ConditionalLawEstimates
open ConditionalVarianceAssembly CollectiveCovarianceBounds CollectiveGradientBounds
open CoordinateOscillation ConditionalKernelL2

variable {n J : ℕ}

/-- Measurability of the original joint crossing probability follows from
its already proved representation as the actual resampling average. -/
theorem measurable_crossing (hJ : 0 < J) (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2) (β : ℝ) :
    Measurable (crossingProbability hJ i a r β) := by
  rw [← siteAverage_indicator_eq_crossingProbability hJ η i a r β]
  exact measurable_siteAverage _ (measurable_leftIndicator hJ i a) i

theorem crossing_bounds (hJ : 0 < J) (i : Fin (n + 1))
    (a : MeshIndex J) (r : Fin 2) (β : ℝ) (X : Configuration (n + 1)) :
    0 ≤ crossingProbability hJ i a r β X ∧ crossingProbability hJ i a r β X ≤ 1 := by
  exact ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩

theorem measurable_outside_crossing (hJ : 0 < J) (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2) (β : ℝ) :
    Measurable (outsideCrossingProbability hJ β i a r) := by
  have hh := (measurable_crossing hJ η i a r β).comp
    ((measurable_insertSite i).comp ((measurable_const : Measurable (fun _ : Configuration n => (0 : Torus))).prodMk measurable_id))
  unfold outsideCrossingProbability
  simpa only [Function.comp_def, crossingProbability, removeSite_insertSite, id_eq] using hh

/-- The actual crossing probability has mean equal to the actual label
mixing coefficient. -/
theorem crossing_mean (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ n + 1)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    (∫ X, crossingProbability hJ i a r β X
      ∂twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β) =
      (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal :=
  (adjacent_integrability_and_crossing hJ hJ2 hN η i a r hβ hsub
    (f := fun _ => (0 : ℝ)) measurable_const (B := 0) (fun _ => by simp)).2.2.2.1

/-- Bounded outside test functions satisfy the actual two tilted marginal
identities. The identity is proved from stationary resampling and the
original specified-label mixture, before any concentration estimate. -/
theorem weighted_outside_integrals (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ n + 1)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {F : Configuration n → ℝ} (hF : Measurable F) {B : ℝ} (hB : ∀ Y, |F Y| ≤ B) :
    let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
    let p := (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal
    let q := crossingProbability hJ i a r β
    (∫ X, q X * F (removeSite i X) ∂P) =
      p * ∫ X, F (removeSite i X) ∂labelGibbsMeasure hJ (Function.update η i a) β ∧
    (∫ X, (1 - q X) * F (removeSite i X) ∂P) =
      (1 - p) * ∫ X, F (removeSite i X)
        ∂labelGibbsMeasure hJ (Function.update η i (nextCell J hJ a r)) β := by
  let b := nextCell J hJ a r
  let P := twoCellGibbsMeasure hJ η i a b β
  let p := (twoCellMixingWeight hJ η i a b β).toReal
  let q := crossingProbability hJ i a r β
  let g := fun X => F (removeSite i X)
  let I := leftIndicator hJ i a
  let κ := adjacentKernels hJ η i a r β
  have hab : a ≠ b := Ne.symm (nextCell_ne J hJ hJ2 a r)
  let : IsProbabilityMeasure P := isProbabilityMeasure_twoCellGibbsMeasure hJ hN η i hab hβ hsub
  let := isProbabilityMeasure_labelGibbsMeasure hJ hN (Function.update η i a) hβ hsub
  let := isProbabilityMeasure_labelGibbsMeasure hJ hN (Function.update η i b) hβ hsub
  have hgm : Measurable g := hF.comp (measurable_removeSite i)
  have hgb : ∀ X, |g X| ≤ B := fun X => hB _
  have hg : MemLp g 2 P := DensityMoments.memLp_of_bounded hgm ⟨B, hgb⟩ 2
  have hI : MemLp I 2 P := DensityMoments.memLp_of_bounded
    (measurable_leftIndicator hJ i a) ⟨1, indicator_bound _⟩ 2
  have hq : MemLp q 2 P := DensityMoments.memLp_of_bounded
    (measurable_crossing hJ η i a r β) ⟨1, fun X => by
      rw [abs_of_nonneg (crossing_bounds hJ i a r β X).1]
      exact (crossing_bounds hJ i a r β X).2⟩ 2
  have hsite : siteAverage κ (fun X => g X * I X) i = fun X => g X * q X := by
    funext X
    change (∫ z, g (Function.update X i z) * I (Function.update X i z) ∂κ i X) = _
    simp_rw [← CoordinateConditionalKernels.insertSite_eq_update, g, removeSite_insertSite]
    rw [integral_const_mul]
    simp_rw [CoordinateConditionalKernels.insertSite_eq_update]
    change F (removeSite i X) * siteAverage κ I i X = _
    rw [siteAverage_indicator_eq_crossingProbability]
  have hprod := ConditionalVarianceIntegral.integral_siteAverage κ P
    (preservesLaw_adjacentKernels hJ hJ2 hN η i a r hβ hsub)
    (hgm.mul (measurable_leftIndicator hJ i a)) (hg.integrable_mul hI) i
  change (∫ X, siteAverage κ (fun X => g X * I X) i X ∂P) =
    ∫ X, g X * I X ∂P at hprod
  rw [hsite] at hprod
  have hedge := twoCell_indicator_covariance hJ hN η i hab hβ hsub hgm hgb
  change (∫ X, I X ∂P) = p ∧ _ at hedge
  have hcov := hedge.2
  rw [covariance_eq_sub hg hI, hedge.1] at hcov
  simp only [Pi.mul_apply] at hcov
  rw [← hprod] at hcov
  have hmix := integral_two_label_mixture
    (twoCellMixingWeight_le_one hJ hN η i a b hβ hsub)
    (twoCellGibbsMeasure_eq_mixture hJ hN η i hab hβ hsub)
    ((DensityMoments.memLp_of_bounded hgm ⟨B, hgb⟩ 2).integrable (by norm_num))
    ((DensityMoments.memLp_of_bounded hgm ⟨B, hgb⟩ 2).integrable (by norm_num))
  change (∫ X, g X ∂P) = p * _ + (1 - p) * _ at hmix
  have hleft : (∫ X, q X * g X ∂P) = p *
      ∫ X, g X ∂labelGibbsMeasure hJ (Function.update η i a) β := by
    simp_rw [mul_comm (q _)]
    have hmixp := congrArg (fun z : ℝ => z * p) hmix
    nlinarith [hcov, hmixp]
  refine ⟨hleft, ?_⟩
  change (∫ X, (1 - q X) * g X ∂P) = _
  simp_rw [sub_mul, one_mul]
  have hqg : Integrable (fun X => q X * g X) P := hq.integrable_mul hg
  rw [integral_sub (hg.integrable (by norm_num)) hqg, hleft]
  linarith [hmix]

/-- Exact means under the two original component Gibbs laws. All cap and
mesh hypotheses remain those of the source crossing bounds. -/
theorem component_crossing_means {β β₀ δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r) :
    let hJ := mesh_pos hmesh
    let b := nextCell J hJ a r
    let P := twoCellGibbsMeasure hJ η i a b β
    let p := (twoCellMixingWeight hJ η i a b β).toReal
    let q := crossingProbability hJ i a r β
    (∫ X, q X ∂labelGibbsMeasure hJ (Function.update η i a) β) = p + variance q P / p ∧
    (∫ X, q X ∂labelGibbsMeasure hJ (Function.update η i b) β) = p - variance q P / (1 - p) := by
  let hJ := mesh_pos hmesh
  let b := nextCell J hJ a r
  let P := twoCellGibbsMeasure hJ η i a b β
  let p := (twoCellMixingWeight hJ η i a b β).toReal
  let q := crossingProbability hJ i a r β
  let : IsProbabilityMeasure P := isProbabilityMeasure_twoCellGibbsMeasure hJ hN η i
    (Ne.symm (nextCell_ne J hJ (mesh_two_le hmesh) a r)) hβ (hβ₀.trans_lt hsub)
  have hrange := LabelRatioTransport.adjacent_mixing_range hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm
  have hc := lowerBound_pos β₀
  have hp : 0 < p := by dsimp [p, b, hJ]; linarith [hrange.1]
  have hp1 : 0 < 1 - p := by dsimp [p, b, hJ]; linarith [hrange.2]
  have hq : MemLp q 2 P := DensityMoments.memLp_of_bounded
    (measurable_crossing hJ η i a r β) ⟨1, fun X => by
      rw [abs_of_nonneg (crossing_bounds hJ i a r β X).1]
      exact (crossing_bounds hJ i a r β X).2⟩ 2
  have hmean : (∫ X, q X ∂P) = p := crossing_mean hJ (mesh_two_le hmesh) hN η i a r hβ (hβ₀.trans_lt hsub)
  have ht := weighted_outside_integrals hJ (mesh_two_le hmesh) hN η i a r hβ (hβ₀.trans_lt hsub)
    (measurable_outside_crossing hJ η i a r β) (B := 1) (fun Y => by
      have hh := crossing_bounds hJ i a r β (insertSite i 0 Y)
      simp only [crossingProbability, removeSite_insertSite] at hh
      unfold outsideCrossingProbability
      rw [abs_of_nonneg hh.1]
      exact hh.2)
  change (∫ X, q X * q X ∂P) = p * (∫ X, q X ∂labelGibbsMeasure hJ (Function.update η i a) β) ∧
    (∫ X, (1 - q X) * q X ∂P) = (1 - p) * (∫ X, q X ∂labelGibbsMeasure hJ (Function.update η i b) β) at ht
  have hv : variance q P = (∫ X, q X ^ 2 ∂P) - p ^ 2 := by
    rw [variance_eq_sub hq, hmean]
    rfl
  have hl := ht.1
  simp_rw [← sq] at hl
  have hr := ht.2
  simp_rw [sub_mul, one_mul, ← sq] at hr
  rw [integral_sub (hq.integrable (by norm_num)) hq.integrable_sq, hmean] at hr
  constructor
  · have he : (∫ X, q X ∂labelGibbsMeasure hJ (Function.update η i a) β) * p =
        (p + variance q P / p) * p := by
      field_simp [hp.ne']
      nlinarith [hl, hv]
    exact (mul_right_cancel₀ hp.ne') he
  · have he : (∫ X, q X ∂labelGibbsMeasure hJ (Function.update η i b) β) * (1 - p) =
        (p - variance q P / (1 - p)) * (1 - p) := by
      field_simp [hp1.ne']
      nlinarith [hr, hv]
    exact (mul_right_cancel₀ hp1.ne') he

/-- Measurable indicator tests turn the actual weighted integral identity
into a literal density equality; no topological regularity is needed. -/
theorem measure_eq_withDensity_of_tests {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {w : Ω → ℝ} (hw : Measurable w) (hb : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    {p : ℝ} (hp : 0 < p)
    (htest : ∀ (F : Ω → ℝ), Measurable F → ∀ B : ℝ, (∀ x, |F x| ≤ B) →
      p * (∫ x, F x ∂ν) = ∫ x, w x * F x ∂μ) :
    ν = μ.withDensity (fun x => ENNReal.ofReal (w x / p)) := by
  have hi : Integrable w μ := (DensityMoments.memLp_of_bounded hw
    ⟨1, fun x => by rw [abs_of_nonneg (hb x).1]; exact (hb x).2⟩ 1).integrable le_rfl
  ext s hs
  rw [withDensity_apply _ hs, ← ofReal_integral_eq_lintegral_ofReal
    (hi.div_const p).integrableOn (Eventually.of_forall fun x => div_nonneg (hb x).1 hp.le),
    integral_div]
  have ht := htest (s.indicator (fun _ => 1)) (measurable_const.indicator hs) 1 (indicator_bound s)
  have he : (fun x => w x * s.indicator (fun _ => (1 : ℝ)) x) = s.indicator w := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  have hone : (∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂ν) = ν.real s := by
    simpa only [smul_eq_mul, mul_one] using (integral_indicator_const (μ := ν) (1 : ℝ) hs)
  rw [he, hone, integral_indicator hs] at ht
  rw [← ENNReal.ofReal_toReal (measure_ne_top ν s)]
  congr 1
  apply (eq_div_iff hp.ne').mpr
  change ν.real s * p = _
  linarith [ht]

/-- Source eq:two-cell-tilted-marginals for the original outside maps,
with the actual original crossing probability and mixing weight. -/
theorem component_outside_marginals {β β₀ δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r) :
    let hJ := mesh_pos hmesh
    let b := nextCell J hJ a r
    let P := twoCellGibbsMeasure hJ η i a b β
    let p := (twoCellMixingWeight hJ η i a b β).toReal
    let q := outsideCrossingProbability hJ β i a r
    (labelGibbsMeasure hJ (Function.update η i a) β).map (removeSite i) =
      (P.map (removeSite i)).withDensity (fun Y => ENNReal.ofReal (q Y / p)) ∧
    (labelGibbsMeasure hJ (Function.update η i b) β).map (removeSite i) =
      (P.map (removeSite i)).withDensity (fun Y => ENNReal.ofReal ((1 - q Y) / (1 - p))) := by
  let hJ := mesh_pos hmesh
  let b := nextCell J hJ a r
  let P := twoCellGibbsMeasure hJ η i a b β
  let p := (twoCellMixingWeight hJ η i a b β).toReal
  let q := outsideCrossingProbability hJ β i a r
  let : IsProbabilityMeasure P := isProbabilityMeasure_twoCellGibbsMeasure hJ hN η i
    (Ne.symm (nextCell_ne J hJ (mesh_two_le hmesh) a r)) hβ (hβ₀.trans_lt hsub)
  let := isProbabilityMeasure_labelGibbsMeasure hJ hN (Function.update η i a) hβ (hβ₀.trans_lt hsub)
  let := isProbabilityMeasure_labelGibbsMeasure hJ hN (Function.update η i b) hβ (hβ₀.trans_lt hsub)
  have hrange := LabelRatioTransport.adjacent_mixing_range hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm
  have hc := lowerBound_pos β₀
  have hp : 0 < p := by dsimp [p, b, hJ]; linarith [hrange.1]
  have hp1 : 0 < 1 - p := by dsimp [p, b, hJ]; linarith [hrange.2]
  have hqm : Measurable q := measurable_outside_crossing hJ η i a r β
  have hqb : ∀ Y, 0 ≤ q Y ∧ q Y ≤ 1 := fun Y => by
    simpa only [q, outsideCrossingProbability, crossingProbability, removeSite_insertSite] using
      crossing_bounds hJ i a r β (insertSite i 0 Y)
  constructor
  · apply measure_eq_withDensity_of_tests hqm hqb hp
    intro F hF B hB
    have hm : (∫ Y, q Y * F Y ∂P.map (removeSite i)) =
        ∫ X, q (removeSite i X) * F (removeSite i X) ∂P := by
      simpa only [Pi.mul_apply] using integral_map_of_stronglyMeasurable
        (μ := P) (measurable_removeSite i) (hqm.mul hF).stronglyMeasurable
    rw [integral_map_of_stronglyMeasurable (measurable_removeSite i) hF.stronglyMeasurable, hm]
    exact (weighted_outside_integrals hJ (mesh_two_le hmesh) hN η i a r hβ
      (hβ₀.trans_lt hsub) hF hB).1.symm
  · apply measure_eq_withDensity_of_tests (measurable_const.sub hqm)
      (fun Y => by
        change 0 ≤ 1 - q Y ∧ 1 - q Y ≤ 1
        exact ⟨sub_nonneg.mpr (hqb Y).2, by linarith [(hqb Y).1]⟩) hp1
    intro F hF B hB
    have hm : (∫ Y, (1 - q Y) * F Y ∂P.map (removeSite i)) =
        ∫ X, (1 - q (removeSite i X)) * F (removeSite i X) ∂P := by
      simpa only [Pi.mul_apply, Pi.sub_apply] using integral_map_of_stronglyMeasurable
        (μ := P) (measurable_removeSite i) ((measurable_const.sub hqm).mul hF).stronglyMeasurable
    simp only [Pi.sub_apply]
    rw [integral_map_of_stronglyMeasurable (measurable_removeSite i) hF.stronglyMeasurable, hm]
    exact (weighted_outside_integrals hJ (mesh_two_le hmesh) hN η i a r hβ
      (hβ₀.trans_lt hsub) hF hB).2.symm

/-- Exact source c1/N deviation bound for both original component means.
The coefficient is written literally using the existing source constants. -/
theorem component_mean_deviations {β β₀ δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r) :
    let hJ := mesh_pos hmesh
    let b := nextCell J hJ a r
    let p := (twoCellMixingWeight hJ η i a b β).toReal
    let q := crossingProbability hJ i a r β
    let c₁ := finePoincareConstant β₀ * crossingConstantSquared β₀ δ GreenCovarianceBounds.hessianConstant /
      (8 * lowerBound β₀)
    |(∫ X, q X ∂labelGibbsMeasure hJ (Function.update η i a) β) - p| ≤ c₁ / (n + 1 : ℕ) ∧
    |(∫ X, q X ∂labelGibbsMeasure hJ (Function.update η i b) β) - p| ≤ c₁ / (n + 1 : ℕ) := by
  let hJ := mesh_pos hmesh
  let b := nextCell J hJ a r
  let P := twoCellGibbsMeasure hJ η i a b β
  let p := (twoCellMixingWeight hJ η i a b β).toReal
  let q := crossingProbability hJ i a r β
  let A := finePoincareConstant β₀ * crossingConstantSquared β₀ δ GreenCovarianceBounds.hessianConstant
  let D := A / (8 * lowerBound β₀) / (n + 1 : ℕ)
  have hA : 0 ≤ A := mul_nonneg (finePoincareConstant_nonneg β₀)
    (crossingConstantSquared_nonneg β₀ hδ₀.le GreenCovarianceBounds.hessianConstant)
  have hc := lowerBound_pos β₀
  have hNN : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hr := LabelRatioTransport.adjacent_mixing_range hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm
  change lowerBound β₀ / 2 ≤ p ∧ p ≤ 1 - lowerBound β₀ / 2 at hr
  have hp : 0 < p := by linarith [hr.1]
  have hp1 : 0 < 1 - p := by linarith [hr.2]
  have hv := twoCell_crossing_variance hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm
  change variance q P ≤ A / (4 * (n + 1 : ℕ)) * (p * (1 - p)) at hv
  have hv' : variance q P ≤ A / (16 * (n + 1 : ℕ)) := by
    have hh := hv.trans (mul_le_mul_of_nonneg_left (CrossingLogistic.bernoulli_factor_le p)
      (div_nonneg hA (by positivity)))
    (convert hh using 1; ring)
  have he : A / (16 * (n + 1 : ℕ)) = D * (lowerBound β₀ / 2) := by
    dsimp [D]
    (field_simp [hc.ne', hNN.ne']; ring)
  have hva : variance q P / p ≤ D := (div_le_iff₀ hp).mpr
    (hv'.trans (he.trans_le (mul_le_mul_of_nonneg_left hr.1 hD)))
  have hvb : variance q P / (1 - p) ≤ D := (div_le_iff₀ hp1).mpr
    (hv'.trans (he.trans_le (mul_le_mul_of_nonneg_left (by linarith [hr.2]) hD)))
  have hm := component_crossing_means hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm
  change _ = p + variance q P / p ∧ _ = p - variance q P / (1 - p) at hm
  constructor
  · rw [hm.1, add_sub_cancel_left, abs_of_nonneg (div_nonneg (variance_nonneg _ _) hp.le)]
    exact hva
  · rw [hm.2, sub_sub_cancel_left, abs_neg,
      abs_of_nonneg (div_nonneg (variance_nonneg _ _) hp1.le)]
    exact hvb

/-- Shifting a genuinely integrable exponential from a nearby center. -/
theorem shift_exponential {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} {lam a p d s : ℝ}
    (hi : Integrable (fun x => Real.exp (lam * (f x - a))) μ)
    (hb : (∫ x, Real.exp (lam * (f x - a)) ∂μ) ≤ Real.exp s)
    (ha : |a - p| ≤ d) :
    Integrable (fun x => Real.exp (lam * (f x - p))) μ ∧
      (∫ x, Real.exp (lam * (f x - p)) ∂μ) ≤ Real.exp (|lam| * d + s) := by
  have he : (fun x => Real.exp (lam * (f x - p))) =
      fun x => Real.exp (lam * (a - p)) * Real.exp (lam * (f x - a)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  have hs : lam * (a - p) ≤ |lam| * d := calc
    _ ≤ |lam * (a - p)| := le_abs_self _
    _ = |lam| * |a - p| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
  rw [he]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  calc
    _ ≤ Real.exp (lam * (a - p)) * Real.exp s :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = Real.exp (lam * (a - p) + s) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hs])

/-- Mixing two actual centered exponential bounds with their actual center
deviation gives the source common-center bound. No mixture LSI is assumed. -/
theorem mixture_exponential_transfer {Ω : Type*} [MeasurableSpace Ω]
    {μ μa μb : Measure Ω} {f : Ω → ℝ} {p lam c₁ c₂ N : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hmix : μ = ENNReal.ofReal p • μa + ENNReal.ofReal (1 - p) • μb)
    (ha : |(∫ x, f x ∂μa) - p| ≤ c₁ / N)
    (hb : |(∫ x, f x ∂μb) - p| ≤ c₁ / N)
    (hIa : Integrable (fun x => Real.exp (lam * (f x - ∫ y, f y ∂μa))) μa)
    (hIb : Integrable (fun x => Real.exp (lam * (f x - ∫ y, f y ∂μb))) μb)
    (hEa : (∫ x, Real.exp (lam * (f x - ∫ y, f y ∂μa)) ∂μa) ≤ Real.exp (c₂ * lam ^ 2 / N))
    (hEb : (∫ x, Real.exp (lam * (f x - ∫ y, f y ∂μb)) ∂μb) ≤ Real.exp (c₂ * lam ^ 2 / N)) :
    Integrable (fun x => Real.exp (lam * (f x - p))) μ ∧
      (∫ x, Real.exp (lam * (f x - p)) ∂μ) ≤ Real.exp ((|lam| * c₁ + c₂ * lam ^ 2) / N) := by
  obtain ⟨hIa', hEa'⟩ := shift_exponential hIa hEa ha
  obtain ⟨hIb', hEb'⟩ := shift_exponential hIb hEb hb
  have hi : Integrable (fun x => Real.exp (lam * (f x - p))) μ := by
    rw [hmix]
    exact (hIa'.smul_measure ENNReal.ofReal_ne_top).add_measure
      (hIb'.smul_measure ENNReal.ofReal_ne_top)
  refine ⟨hi, ?_⟩
  rw [ConditionalNormCrossing.integral_mixture hp hp1 hmix hIa' hIb']
  have hh := add_le_add (mul_le_mul_of_nonneg_left hEa' hp)
    (mul_le_mul_of_nonneg_left hEb' (sub_nonneg.mpr hp1))
  (convert hh using 1; ring_nf)

/-- The source linear exponential transfer for the original two-cell law.
Only the two component-centered exponential bounds remain inputs; their
Herbst derivation is a separate unit. The actual center deviations, mixture
identity and resulting integrability are conclusions of this development. -/
theorem crossing_exponential_transfer {β β₀ δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r) (lam c₂ : ℝ)
    (hcomponents : ∀ c : MeshIndex J, c = a ∨ c = nextCell J (mesh_pos hmesh) a r →
      let Pc := labelGibbsMeasure (mesh_pos hmesh) (Function.update η i c) β
      let q := crossingProbability (mesh_pos hmesh) i a r β
      Integrable (fun X => Real.exp (lam * (q X - ∫ Y, q Y ∂Pc))) Pc ∧
      (∫ X, Real.exp (lam * (q X - ∫ Y, q Y ∂Pc)) ∂Pc) ≤ Real.exp (c₂ * lam ^ 2 / (n + 1 : ℕ))) :
    let hJ := mesh_pos hmesh
    let b := nextCell J hJ a r
    let P := twoCellGibbsMeasure hJ η i a b β
    let p := (twoCellMixingWeight hJ η i a b β).toReal
    let q := crossingProbability hJ i a r β
    let c₁ := finePoincareConstant β₀ * crossingConstantSquared β₀ δ GreenCovarianceBounds.hessianConstant /
      (8 * lowerBound β₀)
    Integrable (fun X => Real.exp (lam * (q X - p))) P ∧
      (∫ X, Real.exp (lam * (q X - p)) ∂P) ≤ Real.exp ((|lam| * c₁ + c₂ * lam ^ 2) / (n + 1 : ℕ)) := by
  let hJ := mesh_pos hmesh
  let b := nextCell J hJ a r
  let P := twoCellGibbsMeasure hJ η i a b β
  let p := (twoCellMixingWeight hJ η i a b β).toReal
  have hc := twoCellMixingWeight_le_one hJ hN η i a b hβ (hβ₀.trans_lt hsub)
  have hct : twoCellMixingWeight hJ η i a b β ≠ ⊤ := ne_top_of_le_ne_top (by simp) hc
  have hpp : ENNReal.ofReal p = twoCellMixingWeight hJ η i a b β := ENNReal.ofReal_toReal hct
  have hpc : ENNReal.ofReal (1 - p) = 1 - twoCellMixingWeight hJ η i a b β := by
    rw [ENNReal.ofReal_sub 1 ENNReal.toReal_nonneg, ENNReal.ofReal_one, hpp]
  have hmix : P = ENNReal.ofReal p • labelGibbsMeasure hJ (Function.update η i a) β +
      ENNReal.ofReal (1 - p) • labelGibbsMeasure hJ (Function.update η i b) β := by
    rw [hpp, hpc]
    exact twoCellGibbsMeasure_eq_mixture hJ hN η i
      (Ne.symm (nextCell_ne J hJ (mesh_two_le hmesh) a r)) hβ (hβ₀.trans_lt hsub)
  have hr := LabelRatioTransport.adjacent_mixing_range hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm
  have hp1 : p ≤ 1 := by
    have hh := lowerBound_pos β₀
    change _ ≤ p ∧ p ≤ _ at hr
    linarith [hr.2]
  have hd := component_mean_deviations hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm
  have ha := hcomponents a (Or.inl rfl)
  have hb := hcomponents b (Or.inr rfl)
  exact mixture_exponential_transfer ENNReal.toReal_nonneg hp1 hmix hd.1 hd.2 ha.1 hb.1 ha.2 hb.2

end PeriodicAttractiveLogGas.CrossingComponentMeans
