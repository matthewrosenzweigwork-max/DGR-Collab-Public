import LeanResearch.PeriodicAttractiveLogGas.SeparatedCoercivity
import LeanResearch.PeriodicAttractiveLogGas.HeavyLocalization
import LeanResearch.PeriodicAttractiveLogGas.HeavyCoercivityConstants

/-! Source `thm:heavy-coercivity`: actual localization on the heavy region,
with the source constants and one particle threshold for every finer mesh.
Every local geometric, analytic and support hypothesis is discharged from the
constructed partition. The development note records centralized verification. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal

namespace PeriodicAttractiveLogGas.HeavyCoercivity

open MeshCells SmoothOccupations HeavyScales HeavyPartition SeparatedRadius
open HeavyLocalization HeavyCoercivityConstants

/-- The actual product on a source open set satisfies separated coercivity
with the retained inverse-square mesh factor. All local hypotheses come from
the constructed radius, mass, hard shell count and cutoff support. -/
theorem localized_coercivity {N J : ℕ} (hN : 0 < N) {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hβ₀ : 0 ≤ β₀) (hβ4 : β₀ < 4)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hJ : sourceResolution β₀ δ ≤ J)
    (hthreshold : 8 / δ ≤ (N : ℝ))
    (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y)))
    (a : MeshIndex J) (m : Fin (sourceScaleCount β₀ δ)) :
    (∫ X, localizedValue hN (source_mesh_pos hJ) hδ β₀ F a m X ^ 2
      ∂gibbsMeasure greenRealRepresentative N β) ≤
      (coercivityConstant β₀ δ / (2 * (J : ℝ) ^ 2 * N)) *
        ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
          (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β)
          (localizedValue hN (source_mesh_pos hJ) hδ β₀ F a m)
          (localized_lift_lipschitz hN hβ₀ hβ4 hδ hJ F hF a m)) := by
  obtain ⟨hsmall, hKsmall, houter, hscale⟩ := source_scale_admissibility hβ₀ hβ4 hJ m.isLt
  have hδhalf : 0 < δ / 2 := by positivity
  have hδhalf1 : δ / 2 < 1 := by linarith
  have hthreshold' : 4 / (δ / 2) ≤ (N : ℝ) := by
    convert hthreshold using 1
    field_simp
    ring
  have hmass : ∀ X ∈ separatedOpenSet N J (source_mesh_pos hJ) β₀ δ a m,
      (δ / 2) * N < mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X := by
    intro X hX
    convert (separatedOpenSet_conditions hN hβ₀ hβ4 hδ hJ a m hX).1 using 1
    ring
  have hshell : ∀ X ∈ separatedOpenSet N J (source_mesh_pos hJ) β₀ δ a m,
      (CollectiveSecondMoment.shellCount (cellCenter J a)
        (scaleRadius J (separationRadius β₀) m) (separationRadius β₀) X : ℝ) <
        2 * separationConstant β₀ * (4 - β₀) *
          mass (cellCenter J a) (scaleRadius J (separationRadius β₀) m) X := by
    intro X hX
    simpa only [mul_assoc] using openSet_shellCount_lt hN hβ₀ hβ4 hδ hJ a m hX
  have hlocal := SeparatedCoercivity.separated_coercivity hβ hβle hβ4
    (source_radius_pos hJ m) (hsmall.trans hKsmall) houter hscale le_rfl
    hδhalf hδhalf1 hthreshold' (cellCenter J a)
    (separatedOpenSet N J (source_mesh_pos hJ) β₀ δ a m)
    (isOpen_separatedOpenSet hN (source_mesh_pos hJ) hδ β₀ a m) hmass hshell
    (localizedValue hN (source_mesh_pos hJ) hδ β₀ F a m)
    (localized_lift_lipschitz hN hβ₀ hβ4 hδ hJ F hF a m)
    (fun X hX ↦ localizedValue_eq_zero_off_openSet hN (source_mesh_pos hJ) hδ F a m hX)
  apply hlocal.trans
  apply mul_le_mul_of_nonneg_right
    (separated_scale_coefficient_le hN (source_mesh_pos hJ) hβ4 hδ m.isLt)
  unfold ambientEnergy graphEnergy
  positivity

/-- Source `thm:heavy-coercivity`, with its explicit constants. The particle
threshold depends only on the coupling bound and occupation threshold, and the
same threshold works for every mesh satisfying the source resolution bound.
The observable is an arbitrary real physical Lipschitz function; no symmetry
or collision support condition is imposed. -/
theorem heavy_coercivity {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ4 : β₀ < 4) (hδ : 0 < δ) (hδ1 : δ < 1)
    {N J : ℕ} (hJ : sourceResolution β₀ δ ≤ J) (hN : particleThreshold β₀ δ ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀)
    (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y)))
    (hsupport : ∀ X, maximumOccupation N J (source_mesh_pos hJ) X ≤ δ → F X = 0) :
    (∫ X, F X ^ 2 ∂gibbsMeasure greenRealRepresentative N β) ≤
      (coercivityConstant β₀ δ / ((J : ℝ) ^ 2 * N)) *
        ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
          (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF) := by
  have hNpos : 0 < N := threshold_positive hδ hN
  let I : ℝ := ∫ X, F X ^ 2 ∂gibbsMeasure greenRealRepresentative N β
  let E : ℝ := ambientEnergy (configurationLipschitzAmbient
    (gibbsMeasure greenRealRepresentative N β)
    (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF)
  let e : MeshIndex J → Fin (sourceScaleCount β₀ δ) → ℝ := fun a m ↦
    ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
      (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β)
      (localizedValue hNpos (source_mesh_pos hJ) hδ β₀ F a m)
      (localized_lift_lipschitz hNpos hβ₀ hβ4 hδ hJ F hF a m))
  let p : ℝ := coercivityConstant β₀ δ / (2 * (J : ℝ) ^ 2 * N)
  let b : ℝ := 32 * (sourceScaleCount β₀ δ : ℝ) ^ 2 *
    scaleGradientConstant β₀ δ ^ 2 * (J : ℝ) ^ 2 / (δ ^ 3 * N)
  have hI : 0 ≤ I := integral_nonneg fun X ↦ sq_nonneg (F X)
  have hp : 0 ≤ p := div_nonneg (coercivityConstant_pos hβ4 hδ).le (by positivity)
  have hsum : I ≤ p * ∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ), e a m := by
    calc
      I = ∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
          ∫ X, localizedValue hNpos (source_mesh_pos hJ) hδ β₀ F a m X ^ 2
            ∂gibbsMeasure greenRealRepresentative N β :=
        localized_l2_identity hNpos hβ₀ hβ4 hδ hδ1 hJ β F hsupport
      _ ≤ ∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ), p * e a m := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro m _
        exact localized_coercivity hNpos hβ hβle hβ₀ hβ4 hδ hδ1 hJ
          (threshold_eight hN) F hF a m
      _ = _ := by simp only [Finset.mul_sum]
  have hlocalization : (∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ), e a m) ≤
      E + b * I := localized_energy_le hNpos hβ₀ hβ4 hδ hδ1 hJ β F hF hsupport
  have hbound : I ≤ p * E +
      (16 * coercivityConstant β₀ δ * (sourceScaleCount β₀ δ : ℝ) ^ 2 *
        scaleGradientConstant β₀ δ ^ 2 / (δ ^ 3 * (N : ℝ) ^ 2)) * I := by
    calc
      I ≤ p * (E + b * I) := hsum.trans (mul_le_mul_of_nonneg_left hlocalization hp)
      _ = p * E + (p * b) * I := by ring
      _ = _ := by
        rw [show p * b = 16 * coercivityConstant β₀ δ * (sourceScaleCount β₀ δ : ℝ) ^ 2 *
          scaleGradientConstant β₀ δ ^ 2 / (δ ^ 3 * (N : ℝ) ^ 2) from
            spatial_partition_coefficient_identity (source_mesh_pos hJ)]
  have hhalf : I ≤ p * E + (1 / 2) * I :=
    hbound.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (absorption_coefficient_le hβ₀ hβ4 hδ hN) hI))
  have hp_eq : p = (coercivityConstant β₀ δ / ((J : ℝ) ^ 2 * N)) / 2 := by
    dsimp [p]
    ring
  rw [hp_eq] at hhalf
  exact absorb_half hhalf

end PeriodicAttractiveLogGas.HeavyCoercivity
