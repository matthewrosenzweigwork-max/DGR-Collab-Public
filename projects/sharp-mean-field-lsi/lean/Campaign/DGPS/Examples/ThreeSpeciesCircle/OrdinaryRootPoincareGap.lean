import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootFullCoercivity
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootFormIntegrals
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootCenteredTest

/-!
# Strict native Poincare gaps at the actual ordinary equality roots

The full original weighted H1 domain is retained. Haar centering, the actual Schur
coercivity theorem, and exact angular variance and energy identities give the native
rate inequality. No spectral-gap or form-coercivity conclusion is assumed.
-/

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem haar_integral_eq_angular (f : Torus 1 → ℝ) :
    (∫ x, f x ∂haar 1) =
      normInt_STR02933 (fun t => f (angEquiv.symm (t : AngCircle))) := by
  calc
    _ = ∫ θ, f (angEquiv.symm θ) ∂angHaar := by
      simpa only [angEquiv.symm_apply_apply] using
        integral_comp_angEquiv (fun θ : AngCircle => f (angEquiv.symm θ))
    _ = _ := by
      have he : (fun θ : AngCircle => f (angEquiv.symm θ)) =
          fun θ => (fun t : ℝ => f (angEquiv.symm (t : AngCircle))) (angSec θ) := by
        funext θ
        change f (angEquiv.symm θ) = f (angEquiv.symm ((angSec θ : ℝ) : AngCircle))
        rw [coe_angSec_STR02962]
      rw [he, integral_angSec_STR02962 (fun t => f (angEquiv.symm (t : AngCircle)))]
      exact (normInt_eq_meanT_STR02962 _).symm

/-- A quantitative native Poincare lower bound on the SAME retained root charts.
Every native weighted H1 test is centered internally, with its original gradient. -/
theorem ordinaryRoot_native_poincare_lower (D : OrdinaryRootGraphData) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ δ ≤ D.radius ∧
      ∀ h : ℝ, 0 < h → h < δ → ∀ j : Fin 3, ∀ σ : AbsoluteDensity 1,
        (∀ θ : AngCircle, σ.density (angEquiv.symm θ) =
          rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) →
        ENNReal.ofReal (DGPS.Circle.AngularNormalization.a0 * (1 + h ^ 2 * D.Z j h 2 + (4 * c / 5) * h ^ 2)) ≤
          poincareRate (densityMeasure σ) := by
  obtain ⟨c, δc, hc, hδc, hδcr, hcoer⟩ := ordinaryRoot_fullWeak_coercivity D
  obtain ⟨C, _, hrem⟩ := D.log_bound
  obtain ⟨δσ, hδσ, hδσr, hσbound⟩ := ordinaryRoot_threefold_density_near_one
    D.ψ D.Z D.radius D.radius_pos C hrem D.density_rotations
  obtain ⟨δa, hδa, hδar, haparam⟩ := ordinaryRoot_angular_parameter_bounds D
  let δ := min δc (min δσ δa)
  have hδ : 0 < δ := lt_min hδc (lt_min hδσ hδa)
  refine ⟨c, δ, hc, hδ, (min_le_left _ _).trans hδcr, fun h hh hhd j σ hσ => ?_⟩
  have hhδc : h < δc := hhd.trans_le (min_le_left _ _)
  have hhδσ : h < δσ := hhd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhδa : h < δa := hhd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hρbound := hσbound h (by rwa [abs_of_pos hh]) j
  have ha := (haparam h (by rwa [abs_of_pos hh]) j).1
  obtain ⟨u, hu, hupos, hurep⟩ := ordinaryChart_positiveContinuousRoot h
    (chartU_isC2_STR02924 D.ψ h (D.Z j h)) σ hσ
  have ha0 : 0 < DGPS.Circle.AngularNormalization.a0 := by unfold DGPS.Circle.AngularNormalization.a0; positivity
  apply (le_poincareRate_iff_forall _ _).2
  intro f hf
  let fc := ordinaryRoot_haarCenteredTest σ f
  let F : ℝ → ℝ := fun t => fc.fn (angEquiv.symm (t : AngCircle))
  let G : ℝ → ℝ := fun t => (2 * Real.pi)⁻¹ * fc.grad (angEquiv.symm (t : AngCircle)) 0
  let ρ := rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h))
  let a := 1 + h ^ 2 * D.Z j h 2
  let V := weightedVariance (densityMeasure σ) f.fn
  let H := normInt_STR02933 (fun t => G t ^ 2 + F t ^ 2)
  let E := normInt_STR02933 (fun t => ρ t * G t ^ 2)
  let η := (4 * c / 5) * h ^ 2
  have hFG : IsPeriodicWeakDerivative_STR02933 F G :=
    ordinaryRoot_nativeTest_periodicH1 σ u hu hupos hurep fc
  have hF0 : normInt_STR02933 F = 0 := by
    rw [← haar_integral_eq_angular fc.fn]
    exact ordinaryRoot_haarCenteredTest_mean_zero σ f
  have hC : c * h ^ 2 * H ≤ E - a * V := by
    have hhC := hcoer h hh hhδc j F G hFG hF0
    have hV := ordinaryChart_native_variance h _ σ hσ fc
    rw [ordinaryRoot_haarCenteredTest_variance] at hV
    change V = normInt_STR02933 (fun t => ρ t * F t ^ 2) -
      (normInt_STR02933 (fun t => ρ t * F t)) ^ 2 at hV
    unfold ordinaryRootHessianQuadratic at hhC
    change c * h ^ 2 * H ≤ E - a *
      (normInt_STR02933 (fun t => ρ t * F t ^ 2) -
        (normInt_STR02933 (fun t => ρ t * F t)) ^ 2) at hhC
    rwa [← hV] at hhC
  have hρcont : Continuous ρ :=
    continuous_rho_STR02950 h (chartU_isC2_STR02924 D.ψ h (D.Z j h)).2.1.continuous
  have hIρ : Integrable (fun t => ρ t * F t ^ 2)
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    simpa only [pow_two] using integrable_cmul_STR02935 hρcont hFG.1.2 hFG.1.2
  have hupper : normInt_STR02933 (fun t => ρ t * F t ^ 2) ≤
      (5 / 4 : ℝ) * normInt_STR02933 (fun t => F t ^ 2) := by
    have hm := normInt_mono_STR02935 hIρ (hFG.1.2.integrable_sq.const_mul (5 / 4))
      (fun t => mul_le_mul_of_nonneg_right (hρbound t).2 (sq_nonneg (F t)))
    rwa [normInt_mul_const_STR02933] at hm
  have hFH : normInt_STR02933 (fun t => F t ^ 2) ≤ H := by
    dsimp only [H]
    rw [normInt_add_STR02934 hFG.2.1.2.integrable_sq hFG.1.2.integrable_sq]
    linarith [normInt_nonneg_STR02935 (fun t => sq_nonneg (G t))]
  have hVU : V ≤ (5 / 4 : ℝ) * H := by
    have hV := ordinaryChart_native_variance h _ σ hσ fc
    rw [ordinaryRoot_haarCenteredTest_variance] at hV
    change V = normInt_STR02933 (fun t => ρ t * F t ^ 2) -
      (normInt_STR02933 (fun t => ρ t * F t)) ^ 2 at hV
    nlinarith [sq_nonneg (normInt_STR02933 (fun t => ρ t * F t))]
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hηV : η * V ≤ c * h ^ 2 * H := by
    have hm := mul_le_mul_of_nonneg_left hVU hη
    dsimp only [η] at hm ⊢
    nlinarith
  have hineq : (a + η) * V ≤ E := by nlinarith
  have hE := ordinaryChart_native_energy h _ σ hσ fc
  rw [ordinaryRoot_haarCenteredTest_energy] at hE
  change dirichletEnergy (densityMeasure σ) f = ENNReal.ofReal (DGPS.Circle.AngularNormalization.a0 * E) at hE
  rw [hE]
  change ENNReal.ofReal (DGPS.Circle.AngularNormalization.a0 * (a + η)) * ENNReal.ofReal V ≤ ENNReal.ofReal (DGPS.Circle.AngularNormalization.a0 * E)
  rw [← ENNReal.ofReal_mul (mul_nonneg ha0.le (add_nonneg ha hη))]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [mul_le_mul_of_nonneg_left hineq ha0.le]

/-- The actual ordinary family has a strict native Poincare gap on one common interval.
The roots, graph, coefficient, and canonical rate all come from the SAME producer. -/
theorem threefold_ordinaryRoots_strictPoincareGap :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ σ : Fin 3 → AbsoluteDensity 1,
        (∀ j, 0 < ordinaryEntropy h (σ j)) ∧
        (∀ j, str025_quot h (σ j) = ordinaryLSRate (ordinaryReference h)) ∧
        (∀ j (τ : AbsoluteDensity 1), 0 < ordinaryEntropy h τ →
          str025_quot h (σ j) ≤ str025_quot h τ) ∧
        (∀ i j : Fin 3, i ≠ j → ¬ (σ i).density =ᵐ[haar 1] (σ j).density) ∧
        (∀ τ : AbsoluteDensity 1, 0 < ordinaryEntropy h τ →
          (∀ η : AbsoluteDensity 1, 0 < ordinaryEntropy h η → str025_quot h τ ≤ str025_quot h η) →
          ∃ j : Fin 3, τ.density =ᵐ[haar 1] (σ j).density) ∧
        ∀ j : Fin 3, ordinaryLSRate (ordinaryReference h) < poincareRate (densityMeasure (σ j)) := by
  obtain ⟨D⟩ := exists_ordinaryRootGraphData
  obtain ⟨c, δ, hc, hδ, hδr, hlower⟩ := ordinaryRoot_native_poincare_lower D
  obtain ⟨δa, hδa, _, haparam⟩ := ordinaryRoot_angular_parameter_bounds D
  let ε := min δ δa
  refine ⟨ε, lt_min hδ hδa, fun h hh hhe => ?_⟩
  have hhd : h < δ := hhe.trans_le (min_le_left _ _)
  have hha : h < δa := hhe.trans_le (min_le_right _ _)
  obtain ⟨σ, hσ, hpos, hquot, hmin, hdist, hall, hfin, hrate⟩ :=
    D.roots h hh (hhd.trans_le hδr)
  refine ⟨σ, hpos, hquot, hmin, hdist, hall, fun j => ?_⟩
  have ha := (haparam h (by rwa [abs_of_pos hh]) j).1
  have ha0 : 0 < DGPS.Circle.AngularNormalization.a0 := by unfold DGPS.Circle.AngularNormalization.a0; positivity
  apply lt_of_lt_of_le _ (hlower h hh hhd j (σ j) (hσ j))
  rw [← ENNReal.ofReal_toReal hfin, hrate j]
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
  nlinarith [mul_pos ha0 (mul_pos (by positivity : 0 < 4 * c / 5) (sq_pos_of_pos hh))]

end DGPS.Examples.ThreeSpeciesCircle
