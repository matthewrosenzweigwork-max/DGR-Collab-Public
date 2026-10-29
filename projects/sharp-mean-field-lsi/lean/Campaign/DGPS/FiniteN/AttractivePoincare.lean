import DGPS.FiniteN.AttractiveLandscape.Calculus
import DGPS.FiniteN.AttractiveLandscape.Entropy
import DGPS.FiniteN.AttractiveLandscape.AbstractInertia
import DGPS.FiniteN.AttractiveLandscape.Inertia

/-!
# Attractive finite rank auxiliary landscape (FIN047)

For continuous `U : Torus d → ℝ` and `Φ : Torus d → ℝ^r` with `‖Φ‖ ≤ L` (smoothness is not
needed), set `ζ(z) = ∫ e^{⟪z,Φ⟫ - U} dm`, `q_z = e^{⟪z,Φ⟫ - U} dm / ζ(z)` and
`ψ(z) = ‖z‖²/2 - log ζ(z)`.  The main theorem
`DGPS.FiniteN.attractive_finite_rank_auxiliary_landscape` records:

* `ψ` is `C^∞`, `∇ψ(z) = z - q_z Φ`, `D²ψ(z) = I - Cov_{q_z} Φ`;
* `‖∇ψ(z)‖ ≥ ‖z‖ - L`, `ψ(z) ≥ ‖z‖²/2 - L‖z‖ - log ζ(0)`, `(1 - L²) I ≤ D²ψ ≤ I` and
  `r - L² ≤ Δψ ≤ r`;
* critical points of `ψ` correspond to stationary fixed points of the attractive mean-field map;
* the inertia (negative index, nullity, coercivity) of `D²ψ(z)` agrees with that of the
  centered free-energy Hessian `densityHessian` at `q_z` (DEF026);
* a unique nondegenerate global free-energy minimizer gives a unique nondegenerate global
  minimum of `ψ`, and conversely.
-/

open MeasureTheory
open scoped RealInnerProductSpace ContDiff

namespace DGPS.FiniteN

open DGPS.FiniteN.AttractiveLandscape

variable {d r : ℕ} {U : Torus d → ℝ} {Φ : Torus d → Feature r}

/-- **FIN047.**  The attractive finite-rank auxiliary landscape. -/
theorem attractive_finite_rank_auxiliary_landscape (hU : Continuous U) (hΦ : Continuous Φ)
    {L : ℝ} (hL : ∀ x, ‖Φ x‖ ≤ L) :
    -- regularity, gradient and Hessian formulas
    ContDiff ℝ ∞ (psi U Φ) ∧
    (∀ z, IsProbabilityMeasure (gibbs U Φ z)) ∧
    (∀ z, featureMean U Φ z = ∫ x, Φ x ∂(gibbs U Φ z)) ∧
    (∀ z, gradient (psi U Φ) z = z - featureMean U Φ z) ∧
    (∀ z v w, fderiv ℝ (fderiv ℝ (psi U Φ)) z v w = ⟪v, w⟫ - featureCov U Φ z v w) ∧
    -- coercivity, growth and bounded Hessian / Laplacian
    (∀ z, ‖z‖ - L ≤ ‖gradient (psi U Φ) z‖) ∧
    (∀ z, ‖z‖ ^ 2 / 2 - L * ‖z‖ - Real.log (zeta U Φ 0) ≤ psi U Φ z) ∧
    (∀ z v, (1 - L ^ 2) * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (psi U Φ)) z v v ∧
      fderiv ℝ (fderiv ℝ (psi U Φ)) z v v ≤ ‖v‖ ^ 2) ∧
    (∀ z, (r : ℝ) - L ^ 2 ≤ Laplacian.laplacian (psi U Φ) z ∧
      Laplacian.laplacian (psi U Φ) z ≤ r) ∧
    -- critical points of `ψ` correspond to stationary fixed points
    (∀ z, fderiv ℝ (psi U Φ) z = 0 →
      IsStationaryFixedPoint hU hΦ (gibbsPM hU hΦ z) ∧
        measureMean Φ (gibbsPM hU hΦ z : Measure (Torus d)) = z) ∧
    (∀ ρ : ProbabilityMeasure (Torus d), IsStationaryFixedPoint hU hΦ ρ →
      fderiv ℝ (psi U Φ) (measureMean Φ (ρ : Measure (Torus d))) = 0 ∧
        ρ = gibbsPM hU hΦ (measureMean Φ (ρ : Measure (Torus d)))) ∧
    -- inertia of `D²ψ(z)` equals inertia of the centered free-energy Hessian at `q_z`
    (∀ z (n : ℕ),
      (HasNegativeSubspace (fun v : Feature r => fderiv ℝ (fderiv ℝ (psi U Φ)) z v v) n ↔
        HasNegativeSubspace
          (fun f : centeredL2 (gibbsPM hU hΦ z) =>
            ⟪f, densityHessian (attractiveData hU hΦ) (gibbsPM hU hΦ z) f⟫) n) ∧
      Module.finrank ℝ (LinearMap.ker ((fderiv ℝ (fderiv ℝ (psi U Φ)) z :
          Feature r →L[ℝ] Feature r →L[ℝ] ℝ) : Feature r →ₗ[ℝ] (Feature r →L[ℝ] ℝ))) =
        Module.finrank ℝ (LinearMap.ker
          ((densityHessian (attractiveData hU hΦ) (gibbsPM hU hΦ z) :
            centeredL2 (gibbsPM hU hΦ z) →L[ℝ] centeredL2 (gibbsPM hU hΦ z)) :
            centeredL2 (gibbsPM hU hΦ z) →ₗ[ℝ] centeredL2 (gibbsPM hU hΦ z))) ∧
      ((∃ c : ℝ, 0 < c ∧ ∀ v : Feature r,
          c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (psi U Φ)) z v v) ↔
        IsCoerciveDensityHessian (attractiveData hU hΦ) (gibbsPM hU hΦ z))) ∧
    -- a unique nondegenerate free-energy minimizer gives a unique nondegenerate minimum of `ψ`
    (∀ μ : ProbabilityMeasure (Torus d), IsFreeEnergyMinimizer hU hΦ μ →
      (∀ ν, IsFreeEnergyMinimizer hU hΦ ν → ν = μ) →
      IsCoerciveDensityHessian (attractiveData hU hΦ) μ →
      μ = gibbsPM hU hΦ (measureMean Φ (μ : Measure (Torus d))) ∧
      (∀ y, psi U Φ (measureMean Φ (μ : Measure (Torus d))) ≤ psi U Φ y) ∧
      (∀ y, psi U Φ y ≤ psi U Φ (measureMean Φ (μ : Measure (Torus d))) →
        y = measureMean Φ (μ : Measure (Torus d))) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ v : Feature r,
        c * ‖v‖ ^ 2 ≤
          fderiv ℝ (fderiv ℝ (psi U Φ)) (measureMean Φ (μ : Measure (Torus d))) v v) ∧
    -- and conversely
    (∀ z₀ : Feature r, (∀ y, psi U Φ z₀ ≤ psi U Φ y) →
      (∀ y, psi U Φ y ≤ psi U Φ z₀ → y = z₀) →
      (∃ c : ℝ, 0 < c ∧ ∀ v : Feature r,
        c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (psi U Φ)) z₀ v v) →
      IsFreeEnergyMinimizer hU hΦ (gibbsPM hU hΦ z₀) ∧
      (∀ ν, IsFreeEnergyMinimizer hU hΦ ν → ν = gibbsPM hU hΦ z₀) ∧
      IsCoerciveDensityHessian (attractiveData hU hΦ) (gibbsPM hU hΦ z₀)) := by
  refine ⟨contDiff_psi_infty hU hΦ, isProbabilityMeasure_gibbs hU hΦ, fun z => rfl,
    gradient_psi hU hΦ, hessian_psi hU hΦ, norm_sub_le_norm_gradient_psi hU hΦ hL,
    psi_lower_bound hU hΦ hL, ?_, laplacian_psi_bounds hU hΦ hL, ?_, ?_, ?_, ?_, ?_⟩
  · intro z v
    rw [hessian_psi hU hΦ, real_inner_self_eq_norm_sq]
    have h1 := featureCov_self_nonneg (U := U) (Φ := Φ) z v
    have h2 := featureCov_self_le hU hΦ hL z v
    constructor <;> nlinarith
  · intro z hz
    refine ⟨isStationaryFixedPoint_gibbs_of_critical hU hΦ hz, ?_⟩
    exact (fderiv_psi_eq_zero_iff hU hΦ z).1 hz
  · intro ρ hρ
    refine ⟨critical_of_fixedPoint hU hΦ hρ, ?_⟩
    exact Subtype.ext (eq_gibbs_of_fixedPoint hU hΦ hρ)
  · intro z n
    exact ⟨hasNegativeSubspace_hessian_iff hU hΦ z n, finrank_ker_hessian_eq hU hΦ z,
      coercive_hessian_iff hU hΦ z⟩
  · intro μ hmin huniq hcoer
    have hμ : μ = gibbsPM hU hΦ (measureMean Φ (μ : Measure (Torus d))) :=
      Subtype.ext (measure_eq_gibbs_of_minimizer hU hΦ μ hmin)
    have hmin' := psi_min_of_minimizer hU hΦ μ hmin
    refine ⟨hμ, hmin', ?_, ?_⟩
    · intro y hy
      have hy' : ∀ w, psi U Φ y ≤ psi U Φ w := fun w => hy.trans (hmin' w)
      have h1 := huniq _ (isFreeEnergyMinimizer_gibbs_of_psi_min hU hΦ hy')
      have h2 := featureMean_eq_of_psi_min hU hΦ hy'
      rw [← h1]
      exact ((measureMean_gibbsPM hU hΦ y).trans h2).symm
    · have h := hcoer
      rw [hμ] at h
      exact (coercive_hessian_iff hU hΦ _).2 h
  · intro z₀ hz huniq hc
    have hmin := isFreeEnergyMinimizer_gibbs_of_psi_min hU hΦ hz
    refine ⟨hmin, ?_, (coercive_hessian_iff hU hΦ z₀).1 hc⟩
    intro ν hν
    have hν' : ν = gibbsPM hU hΦ (measureMean Φ (ν : Measure (Torus d))) :=
      Subtype.ext (measure_eq_gibbs_of_minimizer hU hΦ ν hν)
    have h1 := psi_min_of_minimizer hU hΦ ν hν
    have h2 : measureMean Φ (ν : Measure (Torus d)) = z₀ := huniq _ (h1 z₀)
    rw [hν', h2]

end DGPS.FiniteN
