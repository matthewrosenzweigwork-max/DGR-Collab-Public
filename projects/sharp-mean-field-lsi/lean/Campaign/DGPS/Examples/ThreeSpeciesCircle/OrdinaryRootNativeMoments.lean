import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootFormIntegrals
import DGPS.Examples.ThreeSpeciesCircle.InteractingFeatureGeneratorIdentities

/-! Exact six native moments in the actual angular chart. This identifies the
original probability and physical generator with the analytic angular integrals;
no coefficient or sign bound is a premise. -/

noncomputable section
open MeasureTheory
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem angular_point (t : ℝ) :
    angEquiv.symm (t : AngCircle) = pt (t / (2 * Real.pi)) := by
  rw [MeasurableEquiv.symm_apply_eq, angEquiv_apply]
  change (t : AngCircle) = angRescale ((t / (2 * Real.pi) : ℝ) : UnitAddCircle)
  rw [angRescale_mk]
  congr 1
  field_simp

private theorem angular_cos (k : ℕ) (t : ℝ) :
    cosHarm k (angEquiv.symm (t : AngCircle)) = Real.cos ((k : ℝ) * t) := by
  rw [angular_point, cosHarm_pt]
  congr 1
  field_simp
  <;> ring

private theorem angular_sin (k : ℕ) (t : ℝ) :
    sinHarm k (angEquiv.symm (t : AngCircle)) = Real.sin ((k : ℝ) * t) := by
  rw [angular_point, sinHarm_pt]
  congr 1
  field_simp
  <;> ring

/-- Every actual native harmonic moment is its normalized angular integral. -/
theorem ordinaryChart_native_harmonic_moments (h : ℝ) (u : ℝ → ℝ) (σ : AbsoluteDensity 1)
    (hσ : ∀ θ : AngCircle, σ.density (angEquiv.symm θ) = rhoT_STR02901 h u (angSec θ))
    (k : ℕ) :
    (∫ x, cosHarm k x ∂(densityMeasure σ : Measure (Torus 1))) =
      normInt_STR02933 (fun t => Real.cos ((k : ℝ) * t) * rhoT_STR02901 h u t) ∧
    (∫ x, sinHarm k x ∂(densityMeasure σ : Measure (Torus 1))) =
      normInt_STR02933 (fun t => Real.sin ((k : ℝ) * t) * rhoT_STR02901 h u t) := by
  constructor
  · rw [ordinaryChart_integral_native h u σ hσ (cosHarm k)]
    congr 1
    funext t
    rw [angular_cos]
    ring
  · rw [ordinaryChart_integral_native h u σ hσ (sinHarm k)]
    congr 1
    funext t
    rw [angular_sin]
    ring

/-- The SAME original six native moments equal the actual angular expressions,
including all physical generator corrections. -/
theorem ordinaryChart_native_six_moments {h : ℝ} (hh : 0 < h) (u : ℝ → ℝ)
    (σ : AbsoluteDensity 1)
    (hσ : ∀ θ : AngCircle, σ.density (angEquiv.symm θ) = rhoT_STR02901 h u (angSec θ)) :
    let ρ := rhoT_STR02901 h u
    let C := normInt_STR02933 (fun t => Real.cos t * ρ t) / h
    let S := normInt_STR02933 (fun t => Real.sin t * ρ t) / h
    let B := 15 / (4 * h ^ 3) *
      (normInt_STR02933 (fun t => ρ t * Real.cos (3 * t)) - referenceMean h)
    momC h (densityMeasure σ) = C ∧ momS h (densityMeasure σ) = S ∧ momB h (densityMeasure σ) = B ∧
    (∫ x, elementaryFeatureGenerator h (featureC h) x ∂(densityMeasure σ : Measure (Torus 1))) =
      a0 * C + 3 * a0 / 2 * (normInt_STR02933 (fun t => Real.cos (4 * t) * ρ t) -
        normInt_STR02933 (fun t => Real.cos (2 * t) * ρ t)) ∧
    (∫ x, elementaryFeatureGenerator h (featureS h) x ∂(densityMeasure σ : Measure (Torus 1))) =
      a0 * S + 3 * a0 / 2 * (normInt_STR02933 (fun t => Real.sin (4 * t) * ρ t) +
        normInt_STR02933 (fun t => Real.sin (2 * t) * ρ t)) ∧
    (∫ x, elementaryFeatureGenerator h (featureB h) x ∂(densityMeasure σ : Measure (Torus 1))) =
      9 * a0 * B + 135 * a0 / (8 * h ^ 2) *
        (normInt_STR02933 (fun t => Real.cos (6 * t) * ρ t) - besselI 2 h / besselI 0 h) := by
  dsimp only
  let μ : Measure (Torus 1) := densityMeasure σ
  have iC : Integrable (featureC h) μ :=
    (featureC_continuous h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have iS : Integrable (featureS h) μ :=
    (featureS_continuous h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have iB : Integrable (featureB h) μ :=
    (featureB_continuous h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ic (k : ℕ) : Integrable (cosHarm k) μ :=
    (continuous_cosHarm k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have is (k : ℕ) : Integrable (sinHarm k) μ :=
    (continuous_sinHarm k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hc : momC h (densityMeasure σ) =
      normInt_STR02933 (fun t => Real.cos t * rhoT_STR02901 h u t) / h := by
    unfold momC featureC
    rw [integral_div, (ordinaryChart_native_harmonic_moments h u σ hσ 1).1]
    simp only [Nat.cast_one, one_mul]
  have hs : momS h (densityMeasure σ) =
      normInt_STR02933 (fun t => Real.sin t * rhoT_STR02901 h u t) / h := by
    unfold momS featureS
    rw [integral_div, (ordinaryChart_native_harmonic_moments h u σ hσ 1).2]
    simp only [Nat.cast_one, one_mul]
  have hb : momB h (densityMeasure σ) = 15 / (4 * h ^ 3) *
      (normInt_STR02933 (fun t => rhoT_STR02901 h u t * Real.cos (3 * t)) - referenceMean h) := by
    unfold momB
    have he : featureB h = fun x => 15 / (4 * h ^ 3) * (cosHarm 3 x - referenceMean h) := by
      funext x; unfold featureB; ring
    rw [he, integral_const_mul, integral_sub (ic 3) (integrable_const _), integral_const,
      (ordinaryChart_native_harmonic_moments h u σ hσ 3).1]
    simp only [probReal_univ, one_smul, smul_eq_mul, one_mul, Nat.cast_ofNat]
    congr 2
    congr 1
    funext t
    ring
  have icdiff : Integrable (fun x => cosHarm 4 x - cosHarm 2 x) μ := (ic 4).sub (ic 2)
  have issum : Integrable (fun x => sinHarm 4 x + sinHarm 2 x) μ := (is 4).add (is 2)
  have ibdiff : Integrable (fun x => cosHarm 6 x - besselI 2 h / besselI 0 h) μ :=
    (ic 6).sub (integrable_const _)
  refine ⟨hc, hs, hb, ?_, ?_, ?_⟩
  · simp_rw [elementaryFeatureGenerator_C hh]
    rw [integral_add (iC.const_mul _) (icdiff.const_mul _),
      integral_const_mul, integral_const_mul, integral_sub (ic 4) (ic 2),
      (ordinaryChart_native_harmonic_moments h u σ hσ 4).1,
      (ordinaryChart_native_harmonic_moments h u σ hσ 2).1]
    change a0 * momC h (densityMeasure σ) + _ = _
    rw [hc]
    simp only [Nat.cast_ofNat]
  · simp_rw [elementaryFeatureGenerator_S hh]
    rw [integral_add (iS.const_mul _) (issum.const_mul _),
      integral_const_mul, integral_const_mul, integral_add (is 4) (is 2),
      (ordinaryChart_native_harmonic_moments h u σ hσ 4).2,
      (ordinaryChart_native_harmonic_moments h u σ hσ 2).2]
    change a0 * momS h (densityMeasure σ) + _ = _
    rw [hs]
    simp only [Nat.cast_ofNat]
  · simp_rw [elementaryFeatureGenerator_B hh]
    rw [integral_add (iB.const_mul _) (ibdiff.const_mul _),
      integral_const_mul, integral_const_mul, integral_sub (ic 6) (integrable_const _),
      integral_const, (ordinaryChart_native_harmonic_moments h u σ hσ 6).1]
    simp only [probReal_univ, one_smul, smul_eq_mul, one_mul, Nat.cast_ofNat]
    change 9 * a0 * momB h (densityMeasure σ) + _ = _
    rw [hb]

end DGPS.Examples.ThreeSpeciesCircle
