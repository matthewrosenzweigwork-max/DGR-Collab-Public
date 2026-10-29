import DGPS.Foundations.SobolevCalculus
import DGPS.Model.SpeciesFamily

/-!
# Barycenter square-root chain rule (DEF012)

INTERFACES/definitions.md §3. For a finite species family `F` with species roots `u_s`
(`ρ_s = u_s²`) and weights `θ_s`, the barycenter is `ρ̄ = ∑ θ_s u_s²`, an absolute-admissible
density whose canonical square root is `h = (∑ θ_s u_s²)^{1/2}`.

* `DGPS.barycenter`: the barycenter as an `AbsoluteDensity` (`sqrt = h`).
* `DGPS.barycenter_gradient`: `h ∈ H¹(m)` with gradient `∑ θ_s u_s ∇u_s / h` on `{h > 0}`,
  `0` on `{h = 0}`, and `|∇h|² ≤ ∑ θ_s |∇u_s|²` (pointwise and in integrated form).
* `DGPS.species_div_barycenter_bound`: `u_s ≤ θ_s^(-1/2) h`.

Route: FOU003 Euclidean-norm chain rule `IsWeakGradient.norm_vec` applied to the vector
`(√θ_s u_s)_s`, whose norm is `h`.
-/

open MeasureTheory

namespace DGPS.SpeciesFamily

variable {d : ℕ}

/-- The weak gradient `∇u_s` of the square root of the `s`-th species density. -/
noncomputable def sqrtGradient (F : SpeciesFamily d) (s : Fin F.count) : Torus d → Tangent d :=
  weakGradient (F.density s).sqrt (F.density s).sqrt_mem

theorem isWeakGradient_sqrtGradient (F : SpeciesFamily d) (s : Fin F.count) :
    IsWeakGradient (F.density s).sqrt (F.sqrtGradient s) :=
  isWeakGradient_weakGradient (F.density s).sqrt_mem

/-- The barycenter density `∑ θ_s u_s²`, as a function on the torus. -/
noncomputable def barycenterDensity (F : SpeciesFamily d) (x : Torus d) : ℝ :=
  ∑ s, F.weight s * (F.density s).sqrt x ^ 2

/-- The square root `h = (∑ θ_s u_s²)^{1/2}` of the barycenter. -/
noncomputable def barycenterSqrt (F : SpeciesFamily d) (x : Torus d) : ℝ :=
  Real.sqrt (F.barycenterDensity x)

/-- The chain-rule gradient `(∑ θ_s u_s ∇u_s) / h` (zero where `h = 0`, by `inv_zero`). -/
noncomputable def barycenterGrad (F : SpeciesFamily d) (x : Torus d) : Tangent d :=
  (F.barycenterSqrt x)⁻¹ • ∑ s, F.weight s • (F.density s).sqrt x • F.sqrtGradient s x

theorem barycenterDensity_nonneg (F : SpeciesFamily d) (x : Torus d) :
    0 ≤ F.barycenterDensity x :=
  Finset.sum_nonneg fun s _ => mul_nonneg (F.weight_nonneg s) (sq_nonneg _)

theorem barycenterSqrt_nonneg (F : SpeciesFamily d) (x : Torus d) : 0 ≤ F.barycenterSqrt x :=
  Real.sqrt_nonneg _

theorem barycenterSqrt_sq (F : SpeciesFamily d) (x : Torus d) :
    F.barycenterSqrt x ^ 2 = F.barycenterDensity x :=
  Real.sq_sqrt (F.barycenterDensity_nonneg x)

/-- The vector `(√θ_s u_s)_s` whose Euclidean norm is `h`. -/
noncomputable def scaledRoots (F : SpeciesFamily d) (s : Fin F.count) : Torus d → ℝ :=
  fun x => Real.sqrt (F.weight s) * (F.density s).sqrt x

theorem eNorm_scaledRoots (F : SpeciesFamily d) : eNorm F.scaledRoots = F.barycenterSqrt := by
  funext x
  unfold eNorm barycenterSqrt barycenterDensity scaledRoots
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_pow, Real.sq_sqrt (F.weight_nonneg s)]

theorem eNormGrad_scaledRoots (F : SpeciesFamily d) :
    eNormGrad F.scaledRoots (fun s x => Real.sqrt (F.weight s) • F.sqrtGradient s x)
      = F.barycenterGrad := by
  funext x
  unfold eNormGrad barycenterGrad
  rw [eNorm_scaledRoots]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [scaledRoots, smul_smul]
  have h1 : Real.sqrt (F.weight s) * (F.density s).sqrt x * Real.sqrt (F.weight s)
      = F.weight s * (F.density s).sqrt x := by
    have := Real.mul_self_sqrt (F.weight_nonneg s)
    calc _ = (Real.sqrt (F.weight s) * Real.sqrt (F.weight s)) * (F.density s).sqrt x := by ring
      _ = _ := by rw [this]
  rw [h1, mul_smul]

theorem isWeakGradient_barycenterSqrt (F : SpeciesFamily d) :
    IsWeakGradient F.barycenterSqrt F.barycenterGrad := by
  have h := IsWeakGradient.norm_vec (u := F.scaledRoots)
    (g := fun s x => Real.sqrt (F.weight s) • F.sqrtGradient s x) (fun s => by
      have := (F.isWeakGradient_sqrtGradient s).smul (Real.sqrt (F.weight s))
      exact this)
  rwa [eNorm_scaledRoots, eNormGrad_scaledRoots] at h

end DGPS.SpeciesFamily

namespace DGPS

variable {d : ℕ}

/-- The barycenter `ρ̄ = ∑ θ_s u_s²` of a finite species family (DEF012), as an
absolute-admissible density with square root `h = (∑ θ_s u_s²)^{1/2}`. -/
noncomputable def barycenter (F : SpeciesFamily d) : AbsoluteDensity d where
  sqrt := F.barycenterSqrt
  sqrt_mem := ⟨F.barycenterGrad, F.isWeakGradient_barycenterSqrt⟩
  sqrt_nonneg := Filter.Eventually.of_forall F.barycenterSqrt_nonneg
  mass_one := by
    have e : (fun x => F.barycenterSqrt x ^ 2)
        = fun x => ∑ s, F.weight s * (F.density s).sqrt x ^ 2 := funext F.barycenterSqrt_sq
    have hint : ∀ s ∈ Finset.univ, Integrable
        (fun x => F.weight s * (F.density s).sqrt x ^ 2) (haar d) := fun s _ =>
      ((F.density s).integrable_density).const_mul (F.weight s)
    have hone : ∀ s, ∫ x, (F.density s).sqrt x ^ 2 ∂haar d = 1 := fun s => (F.density s).mass_one
    rw [e, integral_finsetSum _ hint]
    simp_rw [integral_const_mul, hone, mul_one]
    exact F.weight_sum

end DGPS

namespace DGPS.SpeciesFamily

variable {d : ℕ}

theorem barycenter_sqrt (F : SpeciesFamily d) : (barycenter F).sqrt = F.barycenterSqrt := rfl

theorem barycenter_density_apply (F : SpeciesFamily d) (x : Torus d) :
    (barycenter F).density x = ∑ s, F.weight s * (F.density s).sqrt x ^ 2 :=
  F.barycenterSqrt_sq x

end DGPS.SpeciesFamily

namespace DGPS

variable {d : ℕ}

/-- DEF012 chain rule. For a finite species family, `h = (barycenter F).sqrt ∈ H¹(m)` with
weak gradient `∇h = (∑ θ_s u_s ∇u_s) / h` (everywhere defined, `0` on `{h = 0}`), and
`|∇h|² ≤ ∑ θ_s |∇u_s|²` pointwise and in integrated form. -/
theorem barycenter_gradient (F : SpeciesFamily d) :
    IsWeakGradient (barycenter F).sqrt F.barycenterGrad ∧
      (∀ x, 0 < (barycenter F).sqrt x →
        F.barycenterGrad x = ((barycenter F).sqrt x)⁻¹ •
          ∑ s, F.weight s • (F.density s).sqrt x • F.sqrtGradient s x) ∧
      (∀ x, (barycenter F).sqrt x = 0 → F.barycenterGrad x = 0) ∧
      (∀ x, ‖F.barycenterGrad x‖ ^ 2 ≤ ∑ s, F.weight s * ‖F.sqrtGradient s x‖ ^ 2) ∧
      ∫ x, ‖F.barycenterGrad x‖ ^ 2 ∂haar d
        ≤ ∑ s, F.weight s * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar d := by
  have hpt : ∀ x, ‖F.barycenterGrad x‖ ^ 2 ≤ ∑ s, F.weight s * ‖F.sqrtGradient s x‖ ^ 2 := by
    intro x
    have h := norm_eNormGrad_le F.scaledRoots
      (fun s x => Real.sqrt (F.weight s) • F.sqrtGradient s x) x
    rw [SpeciesFamily.eNormGrad_scaledRoots] at h
    refine h.trans (le_of_eq (Finset.sum_congr rfl fun s _ => ?_))
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (F.weight_nonneg s)]
  refine ⟨F.isWeakGradient_barycenterSqrt, fun x _ => rfl, fun x hx => ?_, hpt, ?_⟩
  · have : F.barycenterSqrt x = 0 := hx
    simp [SpeciesFamily.barycenterGrad, this]
  · have hG := F.isWeakGradient_barycenterSqrt.memLp_grad
    have hi : ∀ s, Integrable (fun x => ‖F.sqrtGradient s x‖ ^ 2) (haar d) := fun s =>
      (memLp_two_iff_integrable_sq_norm
        (F.isWeakGradient_sqrtGradient s).memLp_grad.aestronglyMeasurable).1
        (F.isWeakGradient_sqrtGradient s).memLp_grad
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ fun s _ => (hi s).const_mul (F.weight s)]
    exact integral_mono
      ((memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).1 hG)
      (integrable_finsetSum _ fun s _ => (hi s).const_mul (F.weight s)) hpt

/-- DEF012: `θ_s u_s² ≤ h²`, i.e. `u_s ≤ θ_s^(-1/2) h`, pointwise (no sign condition needed
beyond `h ≥ 0`). -/
theorem SpeciesFamily.species_div_barycenter_bound_pointwise (F : SpeciesFamily d) (s : Fin F.count)
    (x : Torus d) :
    (F.density s).sqrt x ≤ (F.weight s) ^ (-1 / 2 : ℝ) * (barycenter F).sqrt x := by
  have hθ := F.weight_pos s
  have h1 : F.weight s * (F.density s).sqrt x ^ 2 ≤ F.barycenterDensity x :=
    Finset.single_le_sum (f := fun s => F.weight s * (F.density s).sqrt x ^ 2)
      (fun i _ => mul_nonneg (F.weight_nonneg i) (sq_nonneg _)) (Finset.mem_univ s)
  have h2 : Real.sqrt (F.weight s) * |(F.density s).sqrt x| ≤ F.barycenterSqrt x := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hθ.le]
    exact Real.sqrt_le_sqrt h1
  have e : (F.weight s) ^ (-1 / 2 : ℝ) = (Real.sqrt (F.weight s))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hθ.le]
    norm_num
  have hs : 0 < Real.sqrt (F.weight s) := Real.sqrt_pos.2 hθ
  show _ ≤ _ * F.barycenterSqrt x
  rw [e, inv_mul_eq_div, le_div_iff₀ hs]
  calc (F.density s).sqrt x * Real.sqrt (F.weight s)
      ≤ |(F.density s).sqrt x| * Real.sqrt (F.weight s) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hs.le
    _ = Real.sqrt (F.weight s) * |(F.density s).sqrt x| := mul_comm _ _
    _ ≤ _ := h2

/-- DEF012: `u_s ≤ θ_s^(-1/2) h` almost everywhere (indeed everywhere). -/
theorem species_div_barycenter_bound (F : SpeciesFamily d) (s : Fin F.count) :
    ∀ᵐ x ∂haar d,
      (F.density s).sqrt x ≤ (F.weight s) ^ (-1 / 2 : ℝ) * (barycenter F).sqrt x :=
  Filter.Eventually.of_forall (F.species_div_barycenter_bound_pointwise s)

/-- The quotient form: `u_s / h ≤ θ_s^(-1/2)` on `{h > 0}`. -/
theorem species_div_barycenter_le (F : SpeciesFamily d) (s : Fin F.count) (x : Torus d)
    (hx : 0 < (barycenter F).sqrt x) :
    (F.density s).sqrt x / (barycenter F).sqrt x ≤ (F.weight s) ^ (-1 / 2 : ℝ) := by
  rw [div_le_iff₀ hx, mul_comm _ ((barycenter F).sqrt x)]
  rw [mul_comm]
  exact F.species_div_barycenter_bound_pointwise s x

end DGPS
