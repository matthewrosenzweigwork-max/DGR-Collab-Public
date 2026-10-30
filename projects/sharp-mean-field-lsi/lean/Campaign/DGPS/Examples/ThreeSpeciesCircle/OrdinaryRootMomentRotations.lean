import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootGraphData
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootFormIntegrals
import DGPS.Examples.ThreeSpeciesCircle.InteractingGeneratorCentering
import DGPS.Circle.VonMisesParity

/-! Actual same-graph root rotations transport both feature and generator
moments. Spatial C3 covariance of the reference differential operator is
proved directly. No kernel-generator commutation or root evenness is used. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029
open DGPS.Circle.VonMisesParity

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem pt_add (t s : ℝ) : pt t + pt s = pt (t + s) := by
  exact (SharpLSI.liftT_add (fun _ : Fin 1 => t) (fun _ : Fin 1 => s)).symm

private theorem angPoint_turn (t s : ℝ) :
    angEquiv.symm ((t + 2 * Real.pi * s : ℝ) : AngCircle) =
      angEquiv.symm (t : AngCircle) + pt s := by
  apply angEquiv.injective
  rw [angEquiv.apply_symm_apply]
  change ((t + 2 * Real.pi * s : ℝ) : AngCircle) =
    angRescale ((angEquiv.symm (t : AngCircle)) 0 + (pt s) 0)
  rw [map_add]
  change ((t + 2 * Real.pi * s : ℝ) : AngCircle) =
    angRescale ((angEquiv.symm (t : AngCircle)) 0) + angRescale ((s : ℝ) : UnitAddCircle)
  rw [angRescale_mk]
  change ((t + 2 * Real.pi * s : ℝ) : AngCircle) =
    angEquiv (angEquiv.symm (t : AngCircle)) + ((2 * Real.pi * s : ℝ) : AngCircle)
  rw [angEquiv.apply_symm_apply, AddCircle.coe_add]

/-- The SAME actual root family is a translated probability family. The
identity holds for every real observable, with no smoothness premise. -/
theorem ordinaryRoot_integral_rotation (D : OrdinaryRootGraphData) (h : ℝ)
    (hh : h ∈ Set.Ioo (-D.radius) D.radius) (σ : Fin 3 → AbsoluteDensity 1)
    (hσ : ∀ j θ, (σ j).density (angEquiv.symm θ) =
      rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ))
    (j : Fin 3) (f : Torus 1 → ℝ) :
    (∫ x, f x ∂(densityMeasure (σ j) : Measure (Torus 1))) =
      ∫ x, f (x + pt ((j : ℕ) / 3)) ∂(densityMeasure (σ 0) : Measure (Torus 1)) := by
  let s : ℝ := (j : ℕ) / 3
  let δ : ℝ := 2 * Real.pi * s
  let ρ0 : ℝ → ℝ := rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z 0 h))
  have hrot (t : ℝ) : rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) t = ρ0 (t - δ) := by
    fin_cases j
    · simp [ρ0, δ, s]
    · convert (D.density_rotations h hh t).1 using 1 <;> dsimp [ρ0, δ, s] <;> congr 2 <;> ring
    · convert (D.density_rotations h hh t).2 using 1 <;> dsimp [ρ0, δ, s] <;> congr 2 <;> ring
  let F : ℝ → ℝ := fun t => ρ0 t * f (angEquiv.symm ((t + δ : ℝ) : AngCircle))
  have hpρ : Function.Periodic ρ0 (2 * Real.pi) :=
    periodic_rho_STR02950 h (chartU_isC2_STR02924 D.ψ h (D.Z 0 h)).1
  have hpF : Function.Periodic F (2 * Real.pi) := by
    intro t
    dsimp only [F]
    rw [hpρ t, show t + 2 * Real.pi + δ = (t + δ) + 2 * Real.pi by ring,
      AddCircle.coe_add_period]
  rw [ordinaryChart_integral_native h _ (σ j) (hσ j) f,
    ordinaryChart_integral_native h _ (σ 0) (hσ 0) (fun x => f (x + pt s))]
  have hsft := normInt_shift_STR02904 hpF (-δ)
  rw [← normInt_eq_STR02935, ← normInt_eq_STR02935] at hsft
  have hl : (fun t => rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) t *
      f (angEquiv.symm (t : AngCircle))) = fun t => F (t + -δ) := by
    funext t
    rw [hrot]
    dsimp only [F]
    rw [show t + -δ + δ = t by ring]
    rfl
  have hr : (fun t => ρ0 t * f (angEquiv.symm (t : AngCircle) + pt s)) = F := by
    funext t
    dsimp only [F, δ]
    rw [angPoint_turn]
  rw [hl]
  change normInt_STR02933 (fun t => F (t + -δ)) = normInt_STR02933
    (fun t => ρ0 t * f (angEquiv.symm (t : AngCircle) + pt s))
  rw [hr]
  exact hsft

private theorem featureC_turn (h s : ℝ) (x : Torus 1) :
    featureC h (x + pt s) = Real.cos (2 * Real.pi * s) * featureC h x -
      Real.sin (2 * Real.pi * s) * featureS h x := by
  obtain ⟨t, rfl⟩ := circ_exists_pt x
  rw [pt_add]
  simp only [featureC, featureS, cosHarm_pt, sinHarm_pt, Nat.cast_one, mul_one]
  rw [mul_add, Real.cos_add]
  ring

private theorem featureS_turn (h s : ℝ) (x : Torus 1) :
    featureS h (x + pt s) = Real.sin (2 * Real.pi * s) * featureC h x +
      Real.cos (2 * Real.pi * s) * featureS h x := by
  obtain ⟨t, rfl⟩ := circ_exists_pt x
  rw [pt_add]
  simp only [featureC, featureS, cosHarm_pt, sinHarm_pt, Nat.cast_one, mul_one]
  rw [mul_add, Real.sin_add]
  ring

private theorem featureB_thirdTurn (h : ℝ) (j : Fin 3) (x : Torus 1) :
    featureB h (x + pt ((j : ℕ) / 3)) = featureB h x := by
  obtain ⟨t, rfl⟩ := circ_exists_pt x
  rw [pt_add]
  simp only [featureB, cosHarm_pt, Nat.cast_ofNat]
  rw [show 2 * Real.pi * 3 * (t + (j : ℕ) / 3) =
    2 * Real.pi * 3 * t + (j : ℕ) * (2 * Real.pi) by ring,
    Real.cos_add_nat_mul_two_pi]

private theorem sigT_thirdTurn (h : ℝ) (j : Fin 3) (x : Torus 1) :
    sigT h (x + pt ((j : ℕ) / 3)) = sigT h x := by
  obtain ⟨t, rfl⟩ := circ_exists_pt x
  rw [pt_add, sigT_lift, sigT_lift]
  unfold sg0
  rw [show 6 * Real.pi * (t + (j : ℕ) / 3) =
    6 * Real.pi * t + (j : ℕ) * (2 * Real.pi) by ring,
    Real.sin_add_nat_mul_two_pi]

private theorem generator_thirdTurn (h : ℝ) (j : Fin 3) (φ : Torus 1 → ℝ) (x : Torus 1) :
    elementaryFeatureGenerator h (fun y => φ (y + pt ((j : ℕ) / 3))) x =
      elementaryFeatureGenerator h φ (x + pt ((j : ℕ) / 3)) := by
  have he : (fun y => coordPartial 0 (fun z => φ (z + pt ((j : ℕ) / 3))) y) =
      fun y => coordPartial 0 φ (y + pt ((j : ℕ) / 3)) :=
    funext fun y => coordPartial_translate 0 _ y
  unfold elementaryFeatureGenerator
  rw [he, coordPartial_translate, coordPartial_translate, sigT_thirdTurn]

/-- Both first-harmonic feature and true generator vectors rotate in the
same C3 representation; the third-feature pair is invariant. -/
theorem elementarySixObservable_thirdTurn (h : ℝ) (j : Fin 3) (x : Torus 1) :
    let s : ℝ := (j : ℕ) / 3
    let c := Real.cos (2 * Real.pi * s)
    let d := Real.sin (2 * Real.pi * s)
    elementaryFeatureGenerator h (featureC h) (x + pt s) =
      c * elementaryFeatureGenerator h (featureC h) x -
        d * elementaryFeatureGenerator h (featureS h) x ∧
    elementaryFeatureGenerator h (featureS h) (x + pt s) =
      d * elementaryFeatureGenerator h (featureC h) x +
        c * elementaryFeatureGenerator h (featureS h) x ∧
    elementaryFeatureGenerator h (featureB h) (x + pt s) =
      elementaryFeatureGenerator h (featureB h) x := by
  dsimp only
  have hC : (fun y => featureC h (y + pt ((j : ℕ) / 3))) = fun y =>
      Real.cos (2 * Real.pi * ((j : ℕ) / 3)) * featureC h y +
      (-Real.sin (2 * Real.pi * ((j : ℕ) / 3))) * featureS h y + 0 * featureB h y := by
    funext y
    rw [featureC_turn]
    ring
  have hS : (fun y => featureS h (y + pt ((j : ℕ) / 3))) = fun y =>
      Real.sin (2 * Real.pi * ((j : ℕ) / 3)) * featureC h y +
      Real.cos (2 * Real.pi * ((j : ℕ) / 3)) * featureS h y + 0 * featureB h y := by
    funext y
    rw [featureS_turn]
    ring
  have hB : (fun y => featureB h (y + pt ((j : ℕ) / 3))) = featureB h :=
    funext (featureB_thirdTurn h j)
  constructor
  · rw [← generator_thirdTurn, hC, elementaryFeatureGenerator_linear3 h (featureC h) (featureS h) (featureB h)
      (smooth_featureC h) (smooth_featureS h) (smooth_featureB h)]
    ring
  constructor
  · rw [← generator_thirdTurn, hS, elementaryFeatureGenerator_linear3 h (featureC h) (featureS h) (featureB h)
      (smooth_featureC h) (smooth_featureS h) (smooth_featureB h)]
    ring
  · rw [← generator_thirdTurn, hB]

/-- The full six actual native moments at every SAME-D root rotate together.
The two vectors are arbitrary and independent; no zero sine moment is assumed. -/
theorem ordinaryRoot_six_moment_rotations (D : OrdinaryRootGraphData) (h : ℝ)
    (hh : h ∈ Set.Ioo (-D.radius) D.radius) (σ : Fin 3 → AbsoluteDensity 1)
    (hσ : ∀ j θ, (σ j).density (angEquiv.symm θ) =
      rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) (j : Fin 3) :
    let c := Real.cos (2 * Real.pi * ((j : ℕ) / 3))
    let d := Real.sin (2 * Real.pi * ((j : ℕ) / 3))
    let AC := fun i => ∫ x, elementaryFeatureGenerator h (featureC h) x
      ∂(densityMeasure (σ i) : Measure (Torus 1))
    let AS := fun i => ∫ x, elementaryFeatureGenerator h (featureS h) x
      ∂(densityMeasure (σ i) : Measure (Torus 1))
    let AB := fun i => ∫ x, elementaryFeatureGenerator h (featureB h) x
      ∂(densityMeasure (σ i) : Measure (Torus 1))
    momC h (densityMeasure (σ j)) = c * momC h (densityMeasure (σ 0)) - d * momS h (densityMeasure (σ 0)) ∧
    momS h (densityMeasure (σ j)) = d * momC h (densityMeasure (σ 0)) + c * momS h (densityMeasure (σ 0)) ∧
    momB h (densityMeasure (σ j)) = momB h (densityMeasure (σ 0)) ∧
    AC j = c * AC 0 - d * AS 0 ∧ AS j = d * AC 0 + c * AS 0 ∧ AB j = AB 0 := by
  dsimp only
  have hi (f : Torus 1 → ℝ) (hf : Continuous f) :
      Integrable f (densityMeasure (σ 0) : Measure (Torus 1)) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hc := hi _ (featureC_continuous h)
  have hs := hi _ (featureS_continuous h)
  have hAc := hi (elementaryFeatureGenerator h (featureC h))
    (continuous_elementaryFeatureGenerator h (featureC h) (smooth_featureC h))
  have hAs := hi (elementaryFeatureGenerator h (featureS h))
    (continuous_elementaryFeatureGenerator h (featureS h) (smooth_featureS h))
  have hrot := ordinaryRoot_integral_rotation D h hh σ hσ j
  have hgen := fun x => elementarySixObservable_thirdTurn h j x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold momC momS
    rw [hrot]
    simp_rw [featureC_turn]
    rw [integral_sub (hc.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul]
  · unfold momC momS
    rw [hrot]
    simp_rw [featureS_turn]
    rw [integral_add (hc.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul]
  · unfold momB
    rw [hrot]
    simp_rw [featureB_thirdTurn]
  · rw [hrot]
    simp_rw [(hgen _).1]
    rw [integral_sub (hAc.const_mul _) (hAs.const_mul _), integral_const_mul, integral_const_mul]
  · rw [hrot]
    simp_rw [(hgen _).2.1]
    rw [integral_add (hAc.const_mul _) (hAs.const_mul _), integral_const_mul, integral_const_mul]
  · rw [hrot]
    simp_rw [(hgen _).2.2]

end DGPS.Examples.ThreeSpeciesCircle
