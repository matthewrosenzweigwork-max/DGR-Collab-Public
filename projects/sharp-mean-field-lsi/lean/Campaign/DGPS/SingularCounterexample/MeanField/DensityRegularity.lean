import DGPS.Examples.PositiveH1.Nonlinear

open MeasureTheory

namespace DGPS.SingularCounterexample

/-- Reuse the one-dimensional regular representative and weak-gradient result for every
absolute density. -/
theorem density_regular (ρ : AbsoluteDensity 1) :
    (∃ U : Torus 1 → ℝ, Continuous U ∧
      (∃ M : ℝ, ∀ x, |U x| ≤ M) ∧ U =ᵐ[haar 1] ρ.sqrt ∧
        ∀ a b : ℝ,
          U (DGPS.Examples.PositiveH1.Nonlinear.lift1 b) -
              U (DGPS.Examples.PositiveH1.Nonlinear.lift1 a) =
            ∫ t in a..b,
              weakGradient ρ.sqrt ρ.sqrt_mem
                (DGPS.Examples.PositiveH1.Nonlinear.lift1 t) 0) ∧
      MemLp ρ.density ⊤ (haar 1) ∧
      IsWeakGradient ρ.density
        (fun x => (2 * ρ.sqrt x) • weakGradient ρ.sqrt ρ.sqrt_mem x) :=
  DGPS.Examples.PositiveH1.Nonlinear.density_regular ρ

/-- The density weak derivative is the existing square-root product field. -/
theorem density_weak_gradient (ρ : AbsoluteDensity 1) :
    IsWeakGradient ρ.density
      (fun x => (2 * ρ.sqrt x) • weakGradient ρ.sqrt ρ.sqrt_mem x) :=
  (density_regular ρ).2.2

/-- The canonical scalar derivative of an absolute density. -/
noncomputable abbrev densityDeriv (ρ : AbsoluteDensity 1) : Torus 1 → ℝ :=
  DGPS.Examples.PositiveH1.Nonlinear.densityDeriv ρ

theorem memLp_densityDeriv (ρ : AbsoluteDensity 1) :
    MemLp (densityDeriv ρ) 2 (haar 1) :=
  DGPS.Examples.PositiveH1.Nonlinear.memLp_densityDeriv ρ

theorem conv_densityDeriv_continuous (k : Torus 1 → ℝ)
    (hk : MemLp k 2 (haar 1)) (ρ : AbsoluteDensity 1) :
    Continuous (DGPS.Examples.PositiveH1.Nonlinear.conv k (densityDeriv ρ)) :=
  DGPS.Examples.PositiveH1.Nonlinear.conv_continuous_L2 hk (memLp_densityDeriv ρ)

theorem conv_densityDeriv_bound (k : Torus 1 → ℝ)
    (hk : MemLp k 2 (haar 1)) (ρ : AbsoluteDensity 1) (x : Torus 1) :
    |DGPS.Examples.PositiveH1.Nonlinear.conv k (densityDeriv ρ) x| ≤
      Real.sqrt (∫ y, k y ^ 2 ∂haar 1) *
        Real.sqrt (∫ y, (densityDeriv ρ y) ^ 2 ∂haar 1) :=
  DGPS.Examples.PositiveH1.Nonlinear.conv_bound hk (memLp_densityDeriv ρ) x

theorem conv_density_ibp (k : Torus 1 → ℝ) (hk : Integrable k (haar 1))
    (ρ : AbsoluteDensity 1) {φ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) :
    ∫ x, DGPS.Examples.PositiveH1.Nonlinear.conv k ρ.density x * coordPartial 0 φ x ∂haar 1 =
      -∫ x, DGPS.Examples.PositiveH1.Nonlinear.conv k (densityDeriv ρ) x * φ x ∂haar 1 := by
  exact DGPS.Examples.PositiveH1.Nonlinear.conv_ibp hk ρ.integrable_density
    ((memLp_densityDeriv ρ).integrable (by norm_num))
    (fun ψ hψ => DGPS.Examples.PositiveH1.Nonlinear.density_ibp ρ hψ) φ hφ

end DGPS.SingularCounterexample
