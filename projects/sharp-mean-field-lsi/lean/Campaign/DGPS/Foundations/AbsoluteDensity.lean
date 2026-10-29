import DGPS.Foundations.WeakSobolev

/-!
# Absolute-admissible probability densities (DEF002)

INTERFACES/common_lemmas.md DEF002. An absolute-admissible probability density is `ρ = u²` with
`u ∈ H¹(m)`, `u ≥ 0` a.e. and `∫ u² dm = 1`. This parametrization is equivalent to
`ρ ≥ 0`, `∫ ρ dm = 1`, `√ρ ∈ H¹(m)`, modulo a.e. equality (`density_sqrt_equivalence`).

`H1Haar d` is realised as the set of functions `u : 𝕋^d → ℝ` with `MemH1 u` (DEF001), so that
membership is written `u ∈ H1Haar d`. Membership is invariant under a.e. equality
(`mem_H1Haar_congr_ae`). The square root `u` of a density is determined a.e. by `ρ`
(`AbsoluteDensity.sqrt_ae_eq_of_density_ae_eq`).
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS

variable {d : ℕ}

/-- `H¹(m)` on the torus, as a set of real functions (DEF001/DEF002). -/
def H1Haar (d : ℕ) : Set (Torus d → ℝ) := {u | MemH1 u}

theorem mem_H1Haar {u : Torus d → ℝ} : u ∈ H1Haar d ↔ MemH1 u := Iff.rfl

theorem mem_H1Haar_congr_ae {u v : Torus d → ℝ} (hu : u ∈ H1Haar d) (h : u =ᵐ[haar d] v) :
    v ∈ H1Haar d := by
  obtain ⟨g, hg⟩ := hu
  exact ⟨g, hg.congr_ae h (Filter.EventuallyEq.refl _ _)⟩

/-- An absolute-admissible probability density `ρ = u²` (DEF002), stored through its square
root `u ∈ H¹(m)`, `u ≥ 0` a.e., `∫ u² dm = 1`. -/
structure AbsoluteDensity (d : ℕ) where
  sqrt : Torus d → ℝ
  sqrt_mem : sqrt ∈ H1Haar d
  sqrt_nonneg : 0 ≤ᵐ[haar d] sqrt
  mass_one : ∫ x, sqrt x ^ 2 ∂haar d = 1

/-- The density `ρ = u²`. -/
def AbsoluteDensity.density (ρ : AbsoluteDensity d) : Torus d → ℝ := fun x => ρ.sqrt x ^ 2

theorem AbsoluteDensity.density_nonneg (ρ : AbsoluteDensity d) (x : Torus d) :
    0 ≤ ρ.density x := sq_nonneg _

theorem AbsoluteDensity.memLp_sqrt (ρ : AbsoluteDensity d) : MemLp ρ.sqrt 2 (haar d) :=
  ρ.sqrt_mem.choose_spec.memLp

theorem AbsoluteDensity.integrable_density (ρ : AbsoluteDensity d) :
    Integrable ρ.density (haar d) :=
  ρ.memLp_sqrt.integrable_sq

theorem AbsoluteDensity.integral_density (ρ : AbsoluteDensity d) :
    ∫ x, ρ.density x ∂haar d = 1 :=
  ρ.mass_one

/-- The square root is determined a.e. by the density. -/
theorem AbsoluteDensity.sqrt_ae_eq_of_density_ae_eq {ρ σ : AbsoluteDensity d}
    (h : ρ.density =ᵐ[haar d] σ.density) : ρ.sqrt =ᵐ[haar d] σ.sqrt := by
  filter_upwards [h, ρ.sqrt_nonneg, σ.sqrt_nonneg] with x hx h1 h2
  have := congrArg Real.sqrt hx
  simp only [AbsoluteDensity.density] at this
  rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at this

theorem isProbabilityMeasure_withDensity_sq (ρ : AbsoluteDensity d) :
    IsProbabilityMeasure ((haar d).withDensity fun x => ENNReal.ofReal (ρ.density x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ρ.integrable_density
      (Filter.Eventually.of_forall ρ.density_nonneg),
    ρ.integral_density, ENNReal.ofReal_one]

/-- The probability measure `ρ m = u² m` of an absolute-admissible density (DEF002). -/
noncomputable def densityMeasure (ρ : AbsoluteDensity d) : ProbabilityMeasure (Torus d) :=
  ⟨(haar d).withDensity fun x => ENNReal.ofReal (ρ.density x),
    isProbabilityMeasure_withDensity_sq ρ⟩

theorem densityMeasure_coe (ρ : AbsoluteDensity d) :
    (densityMeasure ρ : Measure (Torus d)) =
      (haar d).withDensity fun x => ENNReal.ofReal (ρ.sqrt x ^ 2) := rfl

/-- DEF002: a function `ρ` is a.e. equal to `u²` for an absolute-admissible `u` iff `ρ ≥ 0` a.e.,
`∫ ρ dm = 1` and `√ρ ∈ H¹(m)`. -/
theorem density_sqrt_equivalence (ρ : Torus d → ℝ) :
    (∃ A : AbsoluteDensity d, ρ =ᵐ[haar d] A.density) ↔
      (0 ≤ᵐ[haar d] ρ ∧ ∫ x, ρ x ∂haar d = 1 ∧ (fun x => Real.sqrt (ρ x)) ∈ H1Haar d) := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [hA] with x hx
      rw [hx]; exact A.density_nonneg x
    · rw [integral_congr_ae hA]; exact A.integral_density
    · refine mem_H1Haar_congr_ae A.sqrt_mem ?_
      filter_upwards [hA, A.sqrt_nonneg] with x hx h0
      rw [hx, AbsoluteDensity.density, Real.sqrt_sq h0]
  · rintro ⟨h0, h1, hH⟩
    have hsq : (fun x => Real.sqrt (ρ x) ^ 2) =ᵐ[haar d] ρ := by
      filter_upwards [h0] with x hx
      exact Real.sq_sqrt hx
    refine ⟨⟨fun x => Real.sqrt (ρ x), hH,
      Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _, ?_⟩, hsq.symm⟩
    rw [integral_congr_ae hsq, h1]

end DGPS
