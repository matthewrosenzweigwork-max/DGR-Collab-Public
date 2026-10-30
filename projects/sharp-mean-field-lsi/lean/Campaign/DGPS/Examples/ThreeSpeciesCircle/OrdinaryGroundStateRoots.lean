import DGPS.Examples.ThreeSpeciesCircle.OrdinaryGroundState
import DGPS.Frontier.STR029.CloseB

/-!
# Ground-state transforms on the actual ordinary three-root family

The positive physical representatives are constructed from the SAME pointwise chart densities.
No root regularity, optimizer property, or ground-state identity is a public premise of the
existential three-root theorem. The generic chart helper also applies without reselecting roots.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- A genuine positive periodic chart density supplies a positive continuous physical root,
including a.e. identification with the square root stored in an arbitrary absolute density. -/
theorem ordinaryChart_positiveContinuousRoot (h : ℝ) {v : ℝ → ℝ}
    (hv : IsC2Alpha_STR02901 (1 / 2) v) (σ : AbsoluteDensity 1)
    (hσ : ∀ θ : AngCircle, σ.density (angEquiv.symm θ) = rhoT_STR02901 h v (angSec θ)) :
    ∃ u : Torus 1 → ℝ, Continuous u ∧ (∀ x, 0 < u x) ∧ σ.sqrt =ᵐ[haar 1] u := by
  have hp := periodic_rho_STR02950 h hv.1
  have hc : Continuous (fun θ : AngCircle => rhoT_STR02901 h v (angSec θ)) := by
    change Continuous (AddCircle.liftIoc (2 * Real.pi) 0 (rhoT_STR02901 h v))
    exact AddCircle.liftIoc_zero_continuous (by simpa using (hp 0).symm)
      (continuous_rho_STR02950 h hv.2.1.continuous).continuousOn
  have ha : Continuous (angEquiv : Torus 1 → AngCircle) := by
    change Continuous (fun x : Torus 1 => angHomeo (x 0))
    exact angHomeo.continuous.comp (continuous_apply 0)
  have hd : σ.density = fun x => rhoT_STR02901 h v (angSec (angEquiv x)) := by
    funext x
    simpa only [angEquiv.symm_apply_apply] using hσ (angEquiv x)
  have hdc : Continuous σ.density := by rw [hd]; exact hc.comp ha
  have hdp : ∀ x, 0 < σ.density x := by
    intro x
    rw [hd]
    exact rhoT_pos_STR02901 h hv.2.1.continuous _
  refine ⟨fun x => Real.sqrt (σ.density x), hdc.sqrt,
    fun x => Real.sqrt_pos.mpr (hdp x), ?_⟩
  filter_upwards [σ.sqrt_nonneg] with x hx
  exact (Real.sqrt_sq hx).symm

/-- The actual SAME CloseB ordinary roots satisfy the canonical exact transform against
EVERY full absolute-H1 competitor. Root positivity and regularity are discharged internally. -/
theorem threefold_ordinaryRoots_groundStateIdentity :
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
        ∀ j : Fin 3, ∃ u : Torus 1 → ℝ,
          Continuous u ∧ (∀ x, 0 < u x) ∧ (σ j).sqrt =ᵐ[haar 1] u ∧
          ∀ ρ : AbsoluteDensity 1, ∃ hw : MemH1 (fun x => ρ.sqrt x / u x),
            relativeEntropy (densityMeasure ρ : Measure (Torus 1))
              (densityMeasure (σ j) : Measure (Torus 1)) ≠ ⊤ ∧
            (ordinaryFisher h ρ).toReal - 2 * (ordinaryLSRate (ordinaryReference h)).toReal *
              (ordinaryEntropy h ρ).toReal =
              4 * (∫ x, (σ j).density x *
                (weakGradient (fun y => ρ.sqrt y / u y) hw x 0) ^ 2 ∂haar 1) -
              2 * (ordinaryLSRate (ordinaryReference h)).toReal *
                (relativeEntropy (densityMeasure ρ : Measure (Torus 1))
                  (densityMeasure (σ j) : Measure (Torus 1))).toReal := by
  obtain ⟨ψ, Z, δ, C, hδ, hC, hreg, hrot, hreflect, hmain, hlog⟩ :=
    threefold_ordinaryRate_expansion
  refine ⟨δ, hδ, fun h hh hδh => ?_⟩
  obtain ⟨-, -, σ, hσ, hpos, hquot, -, hmin, hdist, hall, -, -⟩ := hmain h hh hδh
  refine ⟨σ, hpos, hquot, hmin, hdist, hall, fun j => ?_⟩
  obtain ⟨u, hu, hupos, hurep⟩ := ordinaryChart_positiveContinuousRoot h
    (chartU_isC2_STR02924 ψ h (Z j h)) (σ j) (hσ j)
  refine ⟨u, hu, hupos, hurep, fun ρ => ?_⟩
  refine ⟨ordinaryEquality_relativeRoot_memH1 (σ j) ρ u hu hupos hurep, ?_⟩
  exact ordinaryEquality_groundStateIdentity h (σ j) (hpos j) (hmin j) u hu hupos hurep ρ

end DGPS.Examples.ThreeSpeciesCircle
