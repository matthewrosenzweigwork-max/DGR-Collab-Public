import DGPS.Examples.ThreeSpeciesCircle.InteractingDensityTurn

/-! Exact native kernel and scalar-deficit covariance under the actual third
turns. The original kernel and diagonal gauge are retained. No classifier or
implicit-function domain invariance is assumed. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029 DGPS.Circle.VonMisesParity

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem pt_add (s t : ℝ) : pt s + pt t = pt (s + t) :=
  (SharpLSI.liftT_add (fun _ : Fin 1 => s) (fun _ : Fin 1 => t)).symm

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

private theorem featureB_turn (h : ℝ) (j : Fin 3) (x : Torus 1) :
    featureB h (x + pt ((j : ℕ) / 3)) = featureB h x := by
  obtain ⟨t, rfl⟩ := circ_exists_pt x
  rw [pt_add]
  simp only [featureB, cosHarm_pt, Nat.cast_ofNat]
  rw [show 2 * Real.pi * 3 * (t + (j : ℕ) / 3) =
    2 * Real.pi * 3 * t + (j : ℕ) * (2 * Real.pi) by ring,
    Real.cos_add_nat_mul_two_pi]

/-- Simultaneous C3 covariance of the actual unscaled kernel, including its diagonal. -/
theorem kernelK_interactingThirdTurn (h : ℝ) (j : Fin 3) (x y : Torus 1) :
    kernelK h (x + pt ((j : ℕ) / 3)) (y + pt ((j : ℕ) / 3)) = kernelK h x y := by
  unfold kernelK
  rw [featureC_turn, featureC_turn, featureS_turn, featureS_turn, featureB_turn, featureB_turn]
  have ht := Real.sin_sq_add_cos_sq (2 * Real.pi * ((j : ℕ) / 3))
  linear_combination kAlpha * (featureC h x * featureC h y + featureS h x * featureS h y) * ht

/-- The true potential follows by exact law transport and kernel invariance. -/
theorem elementaryKernelMean_interactingThirdTurn (h : ℝ) (j : Fin 3)
    (ρ : AbsoluteDensity 1) (x : Torus 1) :
    elementaryKernelMean h (densityMeasure (interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ))
      (x + pt ((j : ℕ) / 3)) = elementaryKernelMean h (densityMeasure ρ) x := by
  calc
    _ = ∫ y, kernelK h (x + pt ((j : ℕ) / 3)) y
        ∂(densityMeasure (interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ) : Measure (Torus 1)) :=
      (integral_kernelK_eq_mean _ _ _).symm
    _ = ∫ y, kernelK h (x + pt ((j : ℕ) / 3)) (y + pt ((j : ℕ) / 3))
        ∂(densityMeasure ρ : Measure (Torus 1)) := interactingDensityTranslate_integral _ _ _
    _ = ∫ y, kernelK h x y ∂(densityMeasure ρ : Measure (Torus 1)) :=
      integral_congr_ae (Eventually.of_forall fun y => kernelK_interactingThirdTurn h j x y)
    _ = _ := integral_kernelK_eq_mean _ _ _

/-- Actual physical force covariance, obtained by differentiating the true
potential identity rather than replacing features by generator eigenfunctions. -/
theorem elementaryKprime_interactingThirdTurn (h : ℝ) (j : Fin 3)
    (ρ : AbsoluteDensity 1) (x : Torus 1) :
    elementaryKprime h (densityMeasure (interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ))
      (x + pt ((j : ℕ) / 3)) = elementaryKprime h (densityMeasure ρ) x := by
  have he : (fun y => elementaryKernelMean h
      (densityMeasure (interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ))
        (y + pt ((j : ℕ) / 3))) = elementaryKernelMean h (densityMeasure ρ) :=
    funext (elementaryKernelMean_interactingThirdTurn h j ρ)
  have hd := congrArg (fun f : Torus 1 → ℝ => coordPartial 0 f x) he
  rw [coordPartial_translate] at hd
  exact hd

/-- The actual reference generator commutes with the third-turn pullback. -/
theorem elementaryFeatureGenerator_interactingThirdTurn (h : ℝ) (j : Fin 3)
    (f : Torus 1 → ℝ) (x : Torus 1) :
    elementaryFeatureGenerator h (fun y => f (y + pt ((j : ℕ) / 3))) x =
      elementaryFeatureGenerator h f (x + pt ((j : ℕ) / 3)) := by
  have he : (fun y => coordPartial 0 (fun z => f (z + pt ((j : ℕ) / 3))) y) =
      fun y => coordPartial 0 f (y + pt ((j : ℕ) / 3)) :=
    funext fun y => coordPartial_translate 0 _ y
  unfold elementaryFeatureGenerator
  rw [he, coordPartial_translate, coordPartial_translate, sigT_interactingThirdTurn]

/-- Covariance of the actual generator applied to the kernel potential. -/
theorem elementaryAK_interactingThirdTurn (h : ℝ) (j : Fin 3)
    (ρ : AbsoluteDensity 1) (x : Torus 1) :
    elementaryAK h (densityMeasure (interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ))
      (x + pt ((j : ℕ) / 3)) = elementaryAK h (densityMeasure ρ) x := by
  have he : (fun y => elementaryKprime h
      (densityMeasure (interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ))
        (y + pt ((j : ℕ) / 3))) = elementaryKprime h (densityMeasure ρ) :=
    funext (elementaryKprime_interactingThirdTurn h j ρ)
  have hd := congrArg (fun f : Torus 1 → ℝ => coordPartial 0 f x) he
  rw [coordPartial_translate] at hd
  unfold elementaryAK
  rw [hd, elementaryKprime_interactingThirdTurn, sigT_interactingThirdTurn]

/-- Genuine quadratic kernel moment covariance for every original density. -/
theorem elementaryQ_interactingThirdTurn (h : ℝ) (j : Fin 3) (ρ : AbsoluteDensity 1) :
    elementaryQ h (densityMeasure (interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ)) =
      elementaryQ h (densityMeasure ρ) := by
  unfold elementaryQ
  rw [interactingDensityTranslate_integral]
  exact integral_congr_ae (Eventually.of_forall (elementaryKernelMean_interactingThirdTurn h j ρ))

theorem elementaryJ_interactingThirdTurn (h : ℝ) (j : Fin 3) (ρ : AbsoluteDensity 1) :
    elementaryJ h (interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ) = elementaryJ h ρ := by
  unfold elementaryJ
  rw [← Structural.budget_integral_densityMeasure, ← Structural.budget_integral_densityMeasure,
    interactingDensityTranslate_integral]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => congrArg (fun z : ℝ => z ^ 2)
    (elementaryKprime_interactingThirdTurn h j ρ x)

theorem elementaryC_interactingThirdTurn (h r : ℝ) (j : Fin 3) (ρ : AbsoluteDensity 1) :
    elementaryC h r (interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ) = elementaryC h r ρ := by
  unfold elementaryC
  rw [← Structural.budget_integral_densityMeasure, ← Structural.budget_integral_densityMeasure,
    interactingDensityTranslate_integral, elementaryQ_interactingThirdTurn]
  congr 2
  exact integral_congr_ae (Eventually.of_forall (elementaryAK_interactingThirdTurn h j ρ))

/-- Exact physical scalar-deficit covariance, on the full absolute-H1 domain.
The real rate and coupling are unchanged; neither needs a minimizer hypothesis. -/
theorem elementaryScalarDeficit_interactingThirdTurn (h ε r : ℝ) (j : Fin 3) (ρ : AbsoluteDensity 1) :
    let τ := interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ
    (ordinaryFisher h τ).toReal - 2 * r * (ordinaryEntropy h τ).toReal +
        ε * elementaryC h r τ + ε ^ 2 * elementaryJ h τ =
      (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal +
        ε * elementaryC h r ρ + ε ^ 2 * elementaryJ h ρ := by
  simp only [ordinaryFisher_interactingThirdTurn, ordinaryEntropy_interactingThirdTurn,
    elementaryC_interactingThirdTurn, elementaryJ_interactingThirdTurn]

end DGPS.Examples.ThreeSpeciesCircle
