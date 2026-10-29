import LeanResearch.PeriodicAttractiveLogGas.ReferenceDensityDomain
import LeanResearch.PeriodicAttractiveLogGas.ReferenceConvolutionGradient

/-! Actual occupation mixture and source invariance of the normalized cell
reference map. This unit does not assert existence of a fixed point. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.ReferenceMapInvariance

open MeshCells LabelOccupations ReferenceResidual ReferenceSelfTerms
  ReferenceConvolutionContinuity ReferenceDensityDomain ReferencePotentialBounds

/-- Literal source weights, including zero weights for empty cells. -/
def occupationWeight {J N : ℕ} (η : LabelVector J N) (a : MeshIndex J) : ℝ :=
  (occupation η a : ℝ) / N

theorem occupationWeight_nonneg {J N : ℕ} (η : LabelVector J N) (a : MeshIndex J) :
    0 ≤ occupationWeight η a := by unfold occupationWeight; positivity

theorem sum_occupationWeight {J N : ℕ} (hN : 0 < N) (η : LabelVector J N) :
    ∑ a, occupationWeight η a = 1 := by
  simp only [occupationWeight, ← Finset.sum_div, ← Nat.cast_sum, sum_occupation]
  exact div_self (by exact_mod_cast hN.ne')

theorem occupationWeight_le {J N : ℕ} (hN : 0 < N) {t : ℝ} {η : LabelVector J N}
    (hη : OccupationCap t η) (a : MeshIndex J) : occupationWeight η a ≤ t := by
  exact (div_le_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mpr (hη a)

/-- This exact finite identity identifies the cell mixture with the particle
average, without excluding repeated labels or unoccupied cells. -/
theorem sum_occupation_mul {J N : ℕ} (η : LabelVector J N) (f : MeshIndex J → ℝ) :
    (∑ a, (occupation η a : ℝ) * f a) = ∑ i, f (η i) := by
  classical
  have hh := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (Fin N))) (t := Finset.univ) (g := η)
    (fun _ _ => Finset.mem_univ _) f
  simpa only [Finset.sum_const, nsmul_eq_mul, occupation] using hh

theorem sum_occupationWeight_mul {J N : ℕ} (η : LabelVector J N) (f : MeshIndex J → ℝ) :
    (∑ a, occupationWeight η a * f a) = (∑ i, f (η i)) / N := by
  simp_rw [occupationWeight, div_mul_eq_mul_div]
  rw [← Finset.sum_div, sum_occupation_mul]

/-- The genuine probability mixture in the source, prior to any fixed point. -/
def mixture {J N : ℕ} {hJ : 0 < J} (η : LabelVector J N) (φ : DensityFamily hJ) :
    Measure Torus := ∑ a, ENNReal.ofReal (occupationWeight η a) • familyMeasures φ a

theorem mixture_probability {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    (η : LabelVector J N) (φ : DensityFamily hJ) : IsProbabilityMeasure (mixture η φ) := by
  constructor
  simp only [mixture, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => occupationWeight_nonneg η a),
    sum_occupationWeight hN η, ENNReal.ofReal_one]

/-- Disjointness, rather than a separate global estimate for each cell,
retains the sharp occupation factor in the density bound. -/
theorem sum_cell_restrictions {J : ℕ} (hJ : 0 < J) :
    (∑ a : MeshIndex J, torusMeasure.restrict (meshCell J hJ a)) = torusMeasure := by
  have hh := Measure.restrict_iUnion (μ := torusMeasure)
    (pairwiseDisjoint_meshCell J hJ) (measurableSet_meshCell J hJ)
  simpa only [iUnion_meshCell, Measure.restrict_univ, Measure.sum_fintype] using hh.symm

theorem mixture_le_haar {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    {t : ℝ} {η : LabelVector J N} (hη : OccupationCap t η) (φ : DensityFamily hJ) :
    mixture η φ ≤ ENNReal.ofReal (Real.exp 1 * t * (J : ℝ)^2) • torusMeasure := by
  classical
  have hterm (a : MeshIndex J) :
      ENNReal.ofReal (occupationWeight η a) • familyMeasures φ a ≤
        (ENNReal.ofReal t * ENNReal.ofReal (Real.exp 1) * (J : ℝ≥0∞)^2) •
          torusMeasure.restrict (meshCell J hJ a) := by
    calc
      _ ≤ ENNReal.ofReal (occupationWeight η a) •
          (ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a) :=
        smul_le_smul_left _ (φ a).law_le
      _ = (ENNReal.ofReal (occupationWeight η a) * ENNReal.ofReal (Real.exp 1) *
          (J : ℝ≥0∞)^2) • torusMeasure.restrict (meshCell J hJ a) := by
        rw [meshCellMeasure, smul_smul, smul_smul, mul_assoc]
      _ ≤ _ := by
        apply Measure.le_iff.mpr
        intro s hs
        simp only [Measure.smul_apply, smul_eq_mul]
        gcongr
        exact occupationWeight_le hN hη a
  calc
    _ ≤ ∑ a : MeshIndex J,
        (ENNReal.ofReal t * ENNReal.ofReal (Real.exp 1) * (J : ℝ≥0∞)^2) •
          torusMeasure.restrict (meshCell J hJ a) := Finset.sum_le_sum fun a _ => hterm a
    _ = (ENNReal.ofReal t * ENNReal.ofReal (Real.exp 1) * (J : ℝ≥0∞)^2) • torusMeasure := by
      rw [← Finset.smul_sum, sum_cell_restrictions hJ]
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos 1).le
        ((occupationWeight_nonneg η (η ⟨0, hN⟩)).trans (occupationWeight_le hN hη _))),
        ENNReal.ofReal_mul (Real.exp_pos 1).le, ENNReal.ofReal_pow (Nat.cast_nonneg J),
        ENNReal.ofReal_natCast, mul_comm (ENNReal.ofReal t)]

theorem mixture_green_integrable {J N : ℕ} {hJ : 0 < J}
    (η : LabelVector J N) (φ : DensityFamily hJ) (x : Torus) :
    Integrable (greenKernel x) (mixture η φ) := by
  apply integrable_finsetSum_measure.mpr
  intro a _
  exact ((global_potential_bound hJ a (familyMeasures φ a) (φ a).law_le x).1).smul_measure
    ENNReal.ofReal_ne_top

/-- Equality at every pole, justified by genuine integrability before
finite linearity. The right side is the existing particle-average object. -/
theorem potential_mixture_eq_averagePotential {J N : ℕ} {hJ : 0 < J}
    (η : LabelVector J N) (φ : DensityFamily hJ) (x : Torus) :
    potential (mixture η φ) x = averagePotential (familyMeasures φ) η x := by
  unfold potential mixture
  rw [integral_finsetSum_measure (fun a _ =>
    ((global_potential_bound hJ a (familyMeasures φ a) (φ a).law_le x).1).smul_measure
      ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal (occupationWeight_nonneg η _),
    smul_eq_mul]
  exact sum_occupationWeight_mul η (fun a => potential (familyMeasures φ a) x)

/-- The equality with the original Green representative is only used
under the actual absolutely continuous law, never pointwise at its pole. -/
theorem mixture_original_green {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    {t : ℝ} {η : LabelVector J N} (hη : OccupationCap t η) (φ : DensityFamily hJ)
    (x : Torus) :
    Integrable (fun y => greenRealRepresentative (x - y)) (mixture η φ) ∧
      (∫ y, greenRealRepresentative (x - y) ∂mixture η φ) =
        averagePotential (familyMeasures φ) η x := by
  have hac : mixture η φ ≪ torusMeasure := Measure.absolutelyContinuous_of_le_smul
    (mixture_le_haar hN hη φ)
  have he : greenKernel x =ᵐ[mixture η φ] fun y => greenRealRepresentative (x - y) :=
    hac.ae_le ((torusMeasure.measurePreserving_sub_left x).quasiMeasurePreserving.ae
      regularGreenRepresentative_ae)
  exact ⟨(mixture_green_integrable η φ x).congr he,
    (integral_congr_ae he).symm.trans (potential_mixture_eq_averagePotential η φ x)⟩

/-- Exact supplied source oscillation estimate, now for the actual
occupation mixture and the existing averagePotential. -/
theorem source_averagePotential_oscillation {J N : ℕ} {hJ : 0 < J} (hN : 0 < N)
    {t β β₀ C₁ : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC : 0 ≤ C₁)
    (hk : GreenFarOscillation.KernelGradientBound C₁)
    {η : LabelVector J N} (hη : OccupationCap t η) (φ : DensityFamily hJ)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (a : MeshIndex J) {x y : Torus}
    (hx : x ∈ closure (meshCell J hJ a)) (hy : y ∈ closure (meshCell J hJ a)) :
    |β * averagePotential (familyMeasures φ) η x -
      β * averagePotential (familyMeasures φ) η y| ≤
        4 * β₀ * C₁ * Real.sqrt (Real.pi * Real.exp 1 * t) := by
  let := mixture_probability hN η φ
  have hh := ReferenceConvolutionGradient.source_cell_oscillation hJ ht hβ hβ₀ hC hk
    (mixture_le_haar hN hη φ) hscale a hx hy
  simpa only [potential_mixture_eq_averagePotential] using hh

/-- Source map invariance. No desired oscillation or family-existence
premise is assumed; both source numerical conditions are kept literally. -/
theorem source_referenceMap_mem {J N : ℕ} {hJ : 0 < J} (hN : 2 ≤ N)
    {t β β₀ C₁ : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC : 0 ≤ C₁)
    (hk : GreenFarOscillation.KernelGradientBound C₁)
    {η : LabelVector J N} (hη : OccupationCap t η) (φ : DensityFamily hJ)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (hsmall : 4 * β₀ * C₁ * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1) :
    referenceMap (by omega : 0 < N) η hβ φ ∈ admissibleDomain hJ := by
  apply referenceMap_mem_of_oscillation
  intro a x hx y hy
  exact (source_averagePotential_oscillation (by omega) ht hβ hβ₀ hC hk hη φ
    hscale a hx hy).trans hsmall

/-- The stronger pointwise bound on every full closed cell includes
unoccupied cells; the map membership theorem only needs its AE version. -/
theorem source_referenceMapValue_bounds {J N : ℕ} {hJ : 0 < J} (hN : 2 ≤ N)
    {t β β₀ C₁ : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC : 0 ≤ C₁)
    (hk : GreenFarOscillation.KernelGradientBound C₁)
    {η : LabelVector J N} (hη : OccupationCap t η) (φ : DensityFamily hJ)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (hsmall : 4 * β₀ * C₁ * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1)
    (a : MeshIndex J) {x : Torus} (hx : x ∈ closure (meshCell J hJ a)) :
    Real.exp (-1) ≤ referenceMapValue η β φ a x ∧ referenceMapValue η β φ a x ≤ Real.exp 1 := by
  apply referenceMapValue_bounds_of_oscillation (by omega) η hβ φ a _ hx
  intro x hx y hy
  exact (source_averagePotential_oscillation (by omega) ht hβ hβ₀ hC hk hη φ
    hscale a hx hy).trans hsmall

/-- Concrete self-map on the exact real Banach-space domain. -/
def sourceMapOnDomain {J N : ℕ} {hJ : 0 < J} (hN : 2 ≤ N)
    {t β β₀ C₁ : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC : 0 ≤ C₁)
    (hk : GreenFarOscillation.KernelGradientBound C₁)
    {η : LabelVector J N} (hη : OccupationCap t η)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (hsmall : 4 * β₀ * C₁ * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1) :
    ↥(admissibleDomain hJ) → ↥(admissibleDomain hJ) := fun φ =>
  ⟨referenceMap (by omega) η hβ ((familyHomeomorph hJ).symm φ),
    source_referenceMap_mem hN ht hβ hβ₀ hC hk hη _ hscale hsmall⟩

theorem continuous_sourceMapOnDomain {J N : ℕ} {hJ : 0 < J} (hN : 2 ≤ N)
    {t β β₀ C₁ : ℝ} (ht : 0 < t) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC : 0 ≤ C₁)
    (hk : GreenFarOscillation.KernelGradientBound C₁)
    {η : LabelVector J N} (hη : OccupationCap t η)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (hsmall : 4 * β₀ * C₁ * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1) :
    Continuous (sourceMapOnDomain (hJ := hJ) hN ht hβ hβ₀ hC hk hη hscale hsmall) :=
  ((continuous_referenceMap (by omega) η hβ).comp (familyHomeomorph hJ).symm.continuous).subtype_mk _

end PeriodicAttractiveLogGas.ReferenceMapInvariance
