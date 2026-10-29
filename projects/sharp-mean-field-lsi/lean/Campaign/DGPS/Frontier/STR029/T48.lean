import DGPS.Frontier.STR029.T54

/-!
# STR029.48: Derivative of the normalized density

Task id: STR029.48 (node STR029, frontier unit, leaf formalization).
Title: Derivative of the normalized density.

For a real parameter `h` and elements `u, v` of the periodic Hölder algebra, the Fréchet
derivative in `u` of the logarithmic partition function is the density average of `v`, and the
Fréchet derivative of the normalized density is the density times the centred `v`.

## Provides

* `DGPS.Frontier.STR029.str029_48_derivative_normalized_density`: one conjunction.  (1) The
  Fréchet derivative in `u` of `w ↦ log Z(h,w)`, applied to `v`, equals the normalised mean
  `∫ v ρ dm` with `ρ = ρ(h,u)`.  (2) The Fréchet derivative in `u` of `w ↦ ρ(h,w)`, applied to
  `v`, equals `ρ · (v - ∫ v ρ dm · 1)`.
* `DGPS.Frontier.STR029.hasFDerivAt_expLin_STR02948`: the map `w ↦ exp (h cos 3t + w)` has
  Fréchet derivative multiplication by `exp (h cos 3t + u)` at `u`.
* `DGPS.Frontier.STR029.hasFDerivAt_Z_STR02948`: the same for `w ↦ Z(h,w)`, with derivative the
  mean functional composed with that multiplication.
* `DGPS.Frontier.STR029.hasFDerivAt_logZ_STR02948`: the derivative of `w ↦ log Z(h,w)`.
* `DGPS.Frontier.STR029.hasFDerivAt_invZ_STR02948`: the derivative of `w ↦ (Z(h,w))⁻¹`.
* `DGPS.Frontier.STR029.hasFDerivAt_rho_STR02948`: the derivative of `w ↦ ρ(h,w)`.
* `DGPS.Frontier.STR029.mean_rho_STR02948`: the identity `∫ v ρ dm = Z⁻¹ ∫ (exp · v) dm`.

Auxiliary declarations carry the suffix `_STR02948`.  The derivatives are taken in the carrier
`PeriodicHolder_STR02968` and use `Z_STR02954`, `rho_STR02954`, `exp_smooth_STR02954`,
`fderiv_exp_STR02954`, `Z_pos_STR02954` and `ext_STR02954` from STR029.54.

## R5 notes

* The carrier is the periodic Hölder space `PeriodicHolder_STR02968` with exponent `1/2`, as fixed
  in the node preamble, not the `C^{2,α}` space named in the statement.  The statement is
  therefore proved for all `u, v` in this larger carrier.  The `C^{2,α}` case is the special case
  in which `u` and `v` lie in that subspace; the subspace inclusion is not formalized here.
* `D_u F[v]` is read as the Fréchet derivative `fderiv ℝ F u` applied to `v`.  Since `F` is
  Fréchet differentiable on the whole carrier, this coincides with the Gâteaux (directional)
  derivative `lim_{s→0} (F(u + s v) - F(u)) / s` in any direction `v`.
* No mean-zero constraint is imposed on `u`, and `h` is an arbitrary real number.  The
  partition function is positive at every point, so the derivatives hold globally and no
  neighbourhood of `u` is needed.  The positivity is `Z_pos_STR02954`.
* `∫ f ρ` is the normalised Haar mean `meanT_STR02901` of the pointwise product, that is
  `(2π)⁻¹ ∫_0^{2π} f ρ dt`.  The integral `∫ v ρ` in the statement is read in this sense.
* The density `ρ(h,u)` is the Hölder-algebra element `rho_STR02954 (h, u)`, whose pointwise
  value is `rhoT_STR02901` by `rho_val_STR02954`.  The scalar `1 / Z` appears as the inverse of
  `Z_STR02954`.
* The product `ρ (v - c · 1)` is the pointwise product in the Hölder algebra, with `1` the
  constant function `1`.
* The inverse is differentiated through `hasDerivAt_inv` composed with the Fréchet derivative of
  `Z`.  The derivative of `Z` is the mean functional composed with multiplication by the
  exponential, so no extra regularity beyond the smoothness of `exp` in STR029.54 is used.
-/

open Filter Topology Function NormedSpace
open scoped ContDiff

namespace DGPS.Frontier.STR029

theorem hasFDerivAt_expLin_STR02948 (h : ℝ) (u : PeriodicHolder_STR02968) :
    HasFDerivAt (fun w : PeriodicHolder_STR02968 => exp (h • c3_STR02954 + w))
      (ContinuousLinearMap.mul ℝ PeriodicHolder_STR02968 (exp (h • c3_STR02954 + u))) u := by
  have hd : DifferentiableAt ℝ (exp : PeriodicHolder_STR02968 → PeriodicHolder_STR02968)
      (h • c3_STR02954 + u) :=
    (exp_smooth_STR02954.differentiable (by simp)).differentiableAt
  have hexp := hd.hasFDerivAt
  rw [fderiv_exp_STR02954] at hexp
  have hadd : HasFDerivAt (fun w : PeriodicHolder_STR02968 => h • c3_STR02954 + w)
      (ContinuousLinearMap.id ℝ PeriodicHolder_STR02968) u :=
    (hasFDerivAt_id u).const_add (h • c3_STR02954)
  exact HasFDerivAt.comp u hexp hadd

theorem hasFDerivAt_Z_STR02948 (h : ℝ) (u : PeriodicHolder_STR02968) :
    HasFDerivAt (fun w : PeriodicHolder_STR02968 => Z_STR02954 (h, w))
      (meanCLM_STR02954.comp (ContinuousLinearMap.mul ℝ PeriodicHolder_STR02968
        (exp (h • c3_STR02954 + u)))) u :=
  HasFDerivAt.comp u meanCLM_STR02954.hasFDerivAt (hasFDerivAt_expLin_STR02948 h u)

theorem hasFDerivAt_logZ_STR02948 (h : ℝ) (u : PeriodicHolder_STR02968) :
    HasFDerivAt (fun w : PeriodicHolder_STR02968 => Real.log (Z_STR02954 (h, w)))
      ((Z_STR02954 (h, u))⁻¹ • meanCLM_STR02954.comp (ContinuousLinearMap.mul ℝ
        PeriodicHolder_STR02968 (exp (h • c3_STR02954 + u)))) u :=
  (hasFDerivAt_Z_STR02948 h u).log (Z_pos_STR02954 (h, u)).ne'

theorem hasFDerivAt_invZ_STR02948 (h : ℝ) (u : PeriodicHolder_STR02968) :
    HasFDerivAt (fun w : PeriodicHolder_STR02968 => (Z_STR02954 (h, w))⁻¹)
      ((-(Z_STR02954 (h, u) ^ 2)⁻¹) • meanCLM_STR02954.comp (ContinuousLinearMap.mul ℝ
        PeriodicHolder_STR02968 (exp (h • c3_STR02954 + u)))) u :=
  (hasDerivAt_inv (Z_pos_STR02954 (h, u)).ne').comp_hasFDerivAt u
    (hasFDerivAt_Z_STR02948 h u)

theorem hasFDerivAt_rho_STR02948 (h : ℝ) (u : PeriodicHolder_STR02968) :
    HasFDerivAt (fun w : PeriodicHolder_STR02968 => rho_STR02954 (h, w))
      ((Z_STR02954 (h, u))⁻¹ • ContinuousLinearMap.mul ℝ PeriodicHolder_STR02968
          (exp (h • c3_STR02954 + u)) +
        ((-(Z_STR02954 (h, u) ^ 2)⁻¹) • meanCLM_STR02954.comp (ContinuousLinearMap.mul ℝ
          PeriodicHolder_STR02968 (exp (h • c3_STR02954 + u)))).smulRight
            (exp (h • c3_STR02954 + u))) u :=
  (hasFDerivAt_invZ_STR02948 h u).smul (hasFDerivAt_expLin_STR02948 h u)

theorem mean_rho_STR02948 (h : ℝ) (u v : PeriodicHolder_STR02968) :
    meanT_STR02901 (fun t => v.val t * (rho_STR02954 (h, u)).val t)
      = (Z_STR02954 (h, u))⁻¹ * meanCLM_STR02954 (exp (h • c3_STR02954 + u) * v) := by
  have hfun : (fun t => v.val t * (rho_STR02954 (h, u)).val t)
      = (Z_STR02954 (h, u))⁻¹ • ((exp (h • c3_STR02954 + u)).val * v.val) := by
    funext t
    simp only [rho_STR02954, PeriodicHolder_STR02968.val_smul, Pi.smul_apply, smul_eq_mul,
      Pi.mul_apply]
    ring
  rw [hfun, meanT_smul_STR02953, meanCLM_apply_STR02954, val_mul_STR02954]

theorem str029_48_derivative_normalized_density (h : ℝ) (u v : PeriodicHolder_STR02968) :
    fderiv ℝ (fun w : PeriodicHolder_STR02968 => Real.log (Z_STR02954 (h, w))) u v
        = meanT_STR02901 (fun t => v.val t * (rho_STR02954 (h, u)).val t) ∧
      fderiv ℝ (fun w : PeriodicHolder_STR02968 => rho_STR02954 (h, w)) u v
        = rho_STR02954 (h, u) * (v - (meanT_STR02901 (fun t => v.val t * (rho_STR02954 (h, u)).val t)
            • (1 : PeriodicHolder_STR02968))) := by
  refine ⟨?_, ?_⟩
  · rw [(hasFDerivAt_logZ_STR02948 h u).fderiv]
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mul_apply', smul_eq_mul]
    rw [mean_rho_STR02948]
  · rw [(hasFDerivAt_rho_STR02948 h u).fderiv, mean_rho_STR02948]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mul_apply', smul_eq_mul]
    apply ext_STR02954
    funext t
    simp only [rho_STR02954, PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_sub,
      PeriodicHolder_STR02968.val_smul, val_mul_STR02954, val_one_STR02954, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring

end DGPS.Frontier.STR029
