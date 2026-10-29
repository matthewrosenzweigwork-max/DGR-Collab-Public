import LeanResearch.PeriodicAttractiveLogGas.CutPhaseIsoperimetry
import LeanResearch.PeriodicAttractiveLogGas.StationaryIsoperimetricReduction

/-! The literal sharp physical square-torus isoperimetric input.
The source's perimeter-two alternative is proved by oriented displacement
cancellation. In the complementary case, coordinate cuts replace the
contractible-disk nesting argument; the planar sharp constant is proved
from Brunn--Minkowski and the actual regular-level coarea derivative.
This is an alternative proof of the geometric prerequisite, not an
assumption of that prerequisite or a claim of separate semantic review. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace PeriodicAttractiveLogGas.StationarySharpIsoperimetry
open StationaryCoarea StationarySard StationaryDistribution StationaryLevelGeometry
  StationaryLevelBoundary StationaryCoordinateCuts StationaryCutDomain CutPhaseIsoperimetry
  StationaryBoundaryCancellation StationaryIsoperimetricReduction

theorem affine_gradient {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (σ t : ℝ) (z : Torus) :
    torusOrdinaryGradient (fun x ↦ σ * (v x - t)) z = σ • torusOrdinaryGradient v z := by
  let V : C(Torus, ℝ) := ⟨v, continuous_of_contDiff_lift (hv.of_le (by simp))⟩
  let f := SmoothPair.ofTorusContDiffLift V hv
  let T : ℝ → ℝ := fun r ↦ σ * (r - t)
  have hT : ContDiff ℝ ∞ T := contDiff_const.mul (contDiff_id.sub contDiff_const)
  have hderiv (r : ℝ) : deriv T r = σ := by
    simpa only [T, id_eq, mul_one] using (((hasDerivAt_id r).sub_const t).const_mul σ).deriv
  calc
    torusOrdinaryGradient (fun x ↦ σ * (v x - t)) z = (f.compSmooth T hT).torusGradient z :=
      (torusGradient_eq_ordinary (f.compSmooth T hT) z).symm
    _ = deriv T (f.torusValue z) • f.torusGradient z := torusGradient_compSmooth f T hT z
    _ = σ • torusOrdinaryGradient v z := by
      rw [hderiv, torusGradient_eq_ordinary]
      rfl

theorem strict_sublevel_mass {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {t : ℝ} (ht : t ∉ torusCriticalValues v) :
    torusMeasure.real {z | v z < t} = 1 - rank v t := by
  have hn : ∀ᵐ z ∂torusMeasure, v z ≠ t := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using torusMeasure_regular_level_eq_zero hv ht
  have he : {z | v z < t} =ᵐ[torusMeasure] {z | t < v z}ᶜ := by
    filter_upwards [hn] with z hz
    apply propext
    change (v z < t) ↔ ¬ t < v z
    constructor
    · exact fun h ↦ not_lt_of_ge h.le
    · intro h
      exact lt_of_le_of_ne (le_of_not_gt h) hz
  calc
    torusMeasure.real {z | v z < t} = torusMeasure.real {z | t < v z}ᶜ :=
      congrArg ENNReal.toReal (measure_congr he)
    _ = 1 - rank v t := by
      rw [measureReal_compl (isOpen_lt continuous_const (continuous_of_contDiff_lift hv)).measurableSet]
      simp only [rank, Measure.real, measure_univ, ENNReal.toReal_one]

theorem sharp_physical_superlevel_isoperimetry {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    SharpPhysicalSuperlevelIsoperimetry v := by
  intro t ht
  have hv1 : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)) := hv.of_le (by simp)
  let P : ℝ := physicalCurveMeasure.real (frontier {z | t < v z})
  have hP : 0 ≤ P := ENNReal.toReal_nonneg
  have hprofile4 : StationaryRearrangement.profile (rank v t) ≤ 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  by_cases hlarge : 2 ≤ P
  · exact hprofile4.trans (by nlinarith only [hlarge])
  have hsmall : P < 2 := lt_of_not_ge hlarge
  obtain ⟨p, hcut⟩ := exists_coordinate_cuts hv ht hsmall
  obtain ⟨σ, hσ, hphase⟩ := cross_phase_sign (continuous_of_contDiff_lift hv1) p hcut
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  let w : Torus → ℝ := fun z ↦ σ * (v z - t)
  have hw : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ w (torusQuotient x)) :=
    contDiff_const.mul (hv.sub contDiff_const)
  have hzero (z : Torus) : w z = 0 ↔ v z = t := by
    change σ * (v z - t) = 0 ↔ v z = t
    rw [mul_eq_zero, or_iff_right hσne, sub_eq_zero]
  have hreg : (0 : ℝ) ∉ torusCriticalValues w := by
    rintro ⟨z, hzg, hz⟩
    change torusOrdinaryGradient w z = 0 at hzg
    rw [affine_gradient hv σ t z] at hzg
    exact ht ⟨z, (smul_eq_zero.mp hzg).resolve_left hσne, (hzero z).mp hz⟩
  have hc : ∀ z ∈ coordinateCross (torusQuotient (centeredLift p)), w z < 0 := by
    rw [torusQuotient_centeredLift]
    exact hphase
  have hiso := cut_phase_isoperimetric (centeredLift p) (hw.of_le (by simp)) hc hreg
  have hset : {z | w z = 0} = {z | v z = t} := by ext z; exact hzero z
  rw [hset, ← frontier_strict_superlevel_eq hv1 ht] at hiso
  change 2 * Real.sqrt (rank w 0) * Real.sqrt Real.pi ≤ P at hiso
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * Real.sqrt (rank w 0) * Real.sqrt Real.pi) hiso 2
  rw [mul_pow, mul_pow, Real.sq_sqrt (rank_nonneg w 0), Real.sq_sqrt Real.pi_pos.le] at hsquare
  have hbound : 4 * Real.pi * rank w 0 ≤ P ^ 2 := by nlinarith only [hsquare]
  have hrank : rank w 0 = rank v t ∨ rank w 0 = 1 - rank v t := by
    rcases hσ with rfl | rfl
    · left
      unfold rank w
      congr 1
      ext z
      change (0 < 1 * (v z - t)) ↔ t < v z
      simp only [one_mul, sub_pos]
    · right
      have he : {z : Torus | 0 < (-1 : ℝ) * (v z - t)} = {z | v z < t} := by
        ext z
        change (0 < (-1 : ℝ) * (v z - t)) ↔ v z < t
        constructor <;> intro h <;> linarith
      change torusMeasure.real {z | 0 < (-1 : ℝ) * (v z - t)} = 1 - rank v t
      rw [he]
      exact strict_sublevel_mass hv1 ht
  rcases hrank with hr | hr
  · rw [hr] at hbound
    exact (min_le_left _ _).trans hbound
  · rw [hr] at hbound
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans hbound

end PeriodicAttractiveLogGas.StationarySharpIsoperimetry
