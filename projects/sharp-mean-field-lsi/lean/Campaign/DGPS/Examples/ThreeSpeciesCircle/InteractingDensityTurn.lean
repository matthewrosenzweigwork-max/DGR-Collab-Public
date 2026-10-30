import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootMomentRotations
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarWeakEuler

/-! Actual third-turn action on the FULL absolute-H1 density domain, its law,
and the two ordinary physical functionals. No optimizer or pointwise stored-root
regularity premise occurs. The sign is the same positive law turn as the retained
ordinary root rotations: density at x is the old density at x-a. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029 DGPS.Circle.VonMisesParity

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Push the original probability density forward by a torus translation. -/
def interactingDensityTranslate (a : Torus 1) (ρ : AbsoluteDensity 1) : AbsoluteDensity 1 where
  sqrt x := ρ.sqrt (x - a)
  sqrt_mem := ⟨_, isWeakGradient_translate (isWeakGradient_weakGradient ρ.sqrt_mem) a⟩
  sqrt_nonneg := (measurePreserving_sub_right (haar 1) a).quasiMeasurePreserving.ae ρ.sqrt_nonneg
  mass_one := by
    simpa only [Function.comp_apply] using
      (integral_sub_right_eq_self (μ := haar 1) (fun x => ρ.sqrt x ^ 2) a).trans ρ.mass_one

theorem interactingDensityTranslate_density (a : Torus 1) (ρ : AbsoluteDensity 1) (x : Torus 1) :
    (interactingDensityTranslate a ρ).density x = ρ.density (x - a) := rfl

/-- Exact probability-law transport, for every real observable. -/
theorem interactingDensityTranslate_integral (a : Torus 1) (ρ : AbsoluteDensity 1) (f : Torus 1 → ℝ) :
    (∫ x, f x ∂(densityMeasure (interactingDensityTranslate a ρ) : Measure (Torus 1))) =
      ∫ x, f (x + a) ∂(densityMeasure ρ : Measure (Torus 1)) := by
  rw [Structural.budget_integral_densityMeasure, Structural.budget_integral_densityMeasure]
  have he := integral_sub_right_eq_self (μ := haar 1) (fun x => ρ.density x * f (x + a)) a
  simpa only [interactingDensityTranslate_density, sub_add_cancel] using he

private theorem pt_add (s t : ℝ) : pt s + pt t = pt (s + t) :=
  (SharpLSI.liftT_add (fun _ : Fin 1 => s) (fun _ : Fin 1 => t)).symm

/-- Exact invariance of the physical reference under every retained third turn. -/
theorem referenceDensity_interactingThirdTurn (h : ℝ) (j : Fin 3) (x : Torus 1) :
    referenceDensity h (x + pt ((j : ℕ) / 3)) = referenceDensity h x := by
  obtain ⟨t, rfl⟩ := circ_exists_pt x
  rw [pt_add, referenceDensity_pt, referenceDensity_pt,
    show 2 * Real.pi * 3 * (t + (j : ℕ) / 3) =
      2 * Real.pi * 3 * t + (j : ℕ) * (2 * Real.pi) by ring,
    Real.cos_add_nat_mul_two_pi]

/-- The reference score, including its physical scale, has the same invariance. -/
theorem sigT_interactingThirdTurn (h : ℝ) (j : Fin 3) (x : Torus 1) :
    sigT h (x + pt ((j : ℕ) / 3)) = sigT h x := by
  obtain ⟨t, rfl⟩ := circ_exists_pt x
  rw [pt_add, sigT_lift, sigT_lift]
  unfold sg0
  rw [show 6 * Real.pi * (t + (j : ℕ) / 3) =
    6 * Real.pi * t + (j : ℕ) * (2 * Real.pi) by ring,
    Real.sin_add_nat_mul_two_pi]

/-- The full physical ordinary entropy is unchanged, on the original H1 domain. -/
theorem ordinaryEntropy_interactingThirdTurn (h : ℝ) (j : Fin 3) (ρ : AbsoluteDensity 1) :
    ordinaryEntropy h (interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ) = ordinaryEntropy h ρ := by
  let a := pt ((j : ℕ) / 3)
  have hq (x : Torus 1) : referenceDensity h (x - a) = referenceDensity h x := by
    have he := referenceDensity_interactingThirdTurn h j (x - a)
    simpa only [a, sub_add_cancel] using he.symm
  rw [ordinaryEntropy_eq, ordinaryEntropy_eq, circleEntropy_eq, circleEntropy_eq]
  congr 1
  have he0 := integral_sub_right_eq_self (μ := haar 1)
    (fun x => ρ.density x * Real.log (ρ.density x)) a
  have he1 := integral_sub_right_eq_self (μ := haar 1)
    (fun x => ρ.density x * Real.log (referenceDensity h x)) a
  simp only [interactingDensityTranslate_density] at *
  rw [he0]
  congr 1
  simpa only [hq] using he1

/-- The full physical ordinary Fisher information is unchanged. The weak
stored-root gradient is transported AE; no smooth representative is assumed. -/
theorem ordinaryFisher_interactingThirdTurn (h : ℝ) (j : Fin 3) (ρ : AbsoluteDensity 1) :
    ordinaryFisher h (interactingDensityTranslate (pt ((j : ℕ) / 3)) ρ) = ordinaryFisher h ρ := by
  let a := pt ((j : ℕ) / 3)
  let τ := interactingDensityTranslate a ρ
  have hg : weakGradient τ.sqrt τ.sqrt_mem =ᵐ[haar 1]
      fun x => weakGradient ρ.sqrt ρ.sqrt_mem (x - a) :=
    (isWeakGradient_weakGradient τ.sqrt_mem).ae_eq
      (isWeakGradient_translate (isWeakGradient_weakGradient ρ.sqrt_mem) a)
  have hs (x : Torus 1) : sigT h x = sigT h (x - a) := by
    have he := sigT_interactingThirdTurn h j (x - a)
    simpa only [a, sub_add_cancel] using he
  have hscore := logScore_ae_eq h
  rw [ordinaryFisher_eq, ordinaryFisher_eq]
  congr 1
  calc
    _ = ∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem (x - a) 0 -
        ρ.sqrt (x - a) * sigT h (x - a)) ^ 2 ∂haar 1 := by
      apply integral_congr_ae
      filter_upwards [hg, hscore] with x hx hxs
      change (2 * weakGradient τ.sqrt τ.sqrt_mem x 0 - ρ.sqrt (x - a) * logScore h x) ^ 2 = _
      rw [hx, hxs, hs]
    _ = ∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * sigT h x) ^ 2 ∂haar 1 :=
      integral_sub_right_eq_self (μ := haar 1)
        (fun x => (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * sigT h x) ^ 2) a
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hscore] with x hx
      rw [hx]

end DGPS.Examples.ThreeSpeciesCircle
