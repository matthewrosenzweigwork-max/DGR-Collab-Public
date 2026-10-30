import DGPS.Examples.ThreeSpeciesCircle.InteractingDensityTurn
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootLocalStability
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! Exact transport of the original Haar square-root H1 distance and the SAME
ordinary-root labels under the physical positive third-turn. No interacting
classification or invariant-neighborhood assumption is used. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029 DGPS.Circle.VonMisesParity

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The original stored-root Haar H1 distance is unchanged by simultaneous
physical translation, with the actual chosen gradients identified only AE. -/
theorem ordinaryRootH1Deviation_translate (a : Torus 1) (σ ρ : AbsoluteDensity 1) :
    ordinaryRootH1Deviation (interactingDensityTranslate a σ) (interactingDensityTranslate a ρ)
      (interactingDensityTranslate a σ).sqrt = ordinaryRootH1Deviation σ ρ σ.sqrt := by
  let τ := interactingDensityTranslate a ρ
  let ω := interactingDensityTranslate a σ
  have hρ := (isWeakGradient_weakGradient τ.sqrt_mem).ae_eq
    (isWeakGradient_translate (isWeakGradient_weakGradient ρ.sqrt_mem) a)
  have hσ := (isWeakGradient_weakGradient ω.sqrt_mem).ae_eq
    (isWeakGradient_translate (isWeakGradient_weakGradient σ.sqrt_mem) a)
  have hg : (fun x => weakGradient τ.sqrt τ.sqrt_mem x - weakGradient ω.sqrt ω.sqrt_mem x)
      =ᵐ[haar 1] (fun x => weakGradient ρ.sqrt ρ.sqrt_mem (x - a) -
        weakGradient σ.sqrt σ.sqrt_mem (x - a)) := by
    filter_upwards [hρ, hσ] with x hx hy
    rw [hx, hy]
  have hFn := eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞))
    (ρ.memLp_sqrt.sub σ.memLp_sqrt).aestronglyMeasurable
    (measurePreserving_sub_right (haar 1) a)
  have hGn := eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞))
    ((isWeakGradient_weakGradient ρ.sqrt_mem).memLp_grad.sub
      (isWeakGradient_weakGradient σ.sqrt_mem).memLp_grad).aestronglyMeasurable
    (measurePreserving_sub_right (haar 1) a)
  unfold ordinaryRootH1Deviation
  rw [eLpNorm_congr_ae hg]
  change (eLpNorm ((fun x => ρ.sqrt x - σ.sqrt x) ∘ fun x => x - a) 2 (haar 1)).toReal +
      (eLpNorm ((fun x => weakGradient ρ.sqrt ρ.sqrt_mem x - weakGradient σ.sqrt σ.sqrt_mem x) ∘
        fun x => x - a) 2 (haar 1)).toReal = _
  exact congrArg₂ (fun x y : ℝ≥0∞ => x.toReal + y.toReal) hFn hGn

/-- Changing the reference record to an equal actual probability law preserves
its original stored-root H1 distance. -/
theorem ordinaryRootH1Deviation_reference_law (σ τ ρ : AbsoluteDensity 1)
    (hlaw : densityMeasure σ = densityMeasure τ) :
    ordinaryRootH1Deviation σ ρ σ.sqrt = ordinaryRootH1Deviation τ ρ τ.sqrt := by
  have hs := AbsoluteDensity.sqrt_ae_eq_of_density_ae_eq
    ((densityMeasure_eq_iff_STR02901 σ τ).1 (congrArg Subtype.val hlaw))
  have hg := (isWeakGradient_weakGradient σ.sqrt_mem).ae_eq
    ((isWeakGradient_weakGradient τ.sqrt_mem).congr_ae hs.symm (EventuallyEq.refl _ _))
  have hf : (fun x => ρ.sqrt x - σ.sqrt x) =ᵐ[haar 1] fun x => ρ.sqrt x - τ.sqrt x :=
    hs.mono fun x hx => by dsimp only; rw [hx]
  have hG : (fun x => weakGradient ρ.sqrt ρ.sqrt_mem x - weakGradient σ.sqrt σ.sqrt_mem x)
      =ᵐ[haar 1] fun x => weakGradient ρ.sqrt ρ.sqrt_mem x - weakGradient τ.sqrt τ.sqrt_mem x :=
    hg.mono fun x hx => by dsimp only; rw [hx]
  unfold ordinaryRootH1Deviation
  rw [eLpNorm_congr_ae hf, eLpNorm_congr_ae hG]

private theorem pt_add (t s : ℝ) : pt t + pt s = pt (t + s) :=
  (SharpLSI.liftT_add (fun _ : Fin 1 => t) (fun _ : Fin 1 => s)).symm

private theorem third_shift (j : Fin 3) :
    pt (((j + 1 : Fin 3) : ℕ) / 3) = pt ((j : ℕ) / 3) + pt (1 / 3) := by
  rw [pt_add]
  fin_cases j
  · congr 1
    norm_num
  · congr 1
    norm_num
  · norm_num [Fin.add_def]
    funext i
    simpa only [pt, torusLift, SharpLSI.liftT, zero_add] using
      (AddCircle.coe_add_period (1 : ℝ) 0).symm

/-- The SAME retained root laws cycle under the actual positive third-turn. -/
theorem ordinaryRoot_law_thirdTurn (D : OrdinaryRootGraphData) (h : ℝ)
    (hh : h ∈ Set.Ioo (-D.radius) D.radius) (σ : Fin 3 → AbsoluteDensity 1)
    (hσ : ∀ j θ, (σ j).density (angEquiv.symm θ) =
      rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) (j : Fin 3) :
    densityMeasure (σ (j + 1)) = densityMeasure (interactingDensityTranslate (pt (1 / 3)) (σ j)) := by
  letI : IsProbabilityMeasure (densityMeasure (σ (j + 1)) : Measure (Torus 1)) := (densityMeasure (σ (j + 1))).property
  letI : IsProbabilityMeasure (densityMeasure (interactingDensityTranslate (pt (1 / 3)) (σ j)) : Measure (Torus 1)) := (densityMeasure (interactingDensityTranslate (pt (1 / 3)) (σ j))).property
  apply Subtype.ext
  change (densityMeasure (σ (j + 1)) : Measure (Torus 1)) =
    (densityMeasure (interactingDensityTranslate (pt (1 / 3)) (σ j)) : Measure (Torus 1))
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [ordinaryRoot_integral_rotation D h hh σ hσ (j + 1) f,
    interactingDensityTranslate_integral,
    ordinaryRoot_integral_rotation D h hh σ hσ j (fun x => f (x + pt (1 / 3)))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by dsimp only; rw [third_shift, add_assoc]

/-- Original H1 localization has an exact cyclic label under physical rotation;
no independently chosen nearest-root assignment is compared. -/
theorem ordinaryRootH1Deviation_thirdTurn (D : OrdinaryRootGraphData) (h : ℝ)
    (hh : h ∈ Set.Ioo (-D.radius) D.radius) (σ : Fin 3 → AbsoluteDensity 1)
    (hσ : ∀ j θ, (σ j).density (angEquiv.symm θ) =
      rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ))
    (j : Fin 3) (ρ : AbsoluteDensity 1) :
    ordinaryRootH1Deviation (σ (j + 1)) (interactingDensityTranslate (pt (1 / 3)) ρ)
      (σ (j + 1)).sqrt = ordinaryRootH1Deviation (σ j) ρ (σ j).sqrt := by
  rw [ordinaryRootH1Deviation_reference_law _ _ _ (ordinaryRoot_law_thirdTurn D h hh σ hσ j)]
  exact ordinaryRootH1Deviation_translate _ _ _

end DGPS.Examples.ThreeSpeciesCircle
