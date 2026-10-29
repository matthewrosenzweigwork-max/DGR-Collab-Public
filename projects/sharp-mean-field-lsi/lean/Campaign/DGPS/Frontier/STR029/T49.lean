import DGPS.Frontier.STR029.T48

/-!
# STR029.49: First variations of entropy and Fisher information

Task id: STR029.49 (node STR029, frontier unit, leaf formalization).
Title: First variations of entropy and Fisher information.

For a real parameter `h` and `2π`-periodic functions `u, v` of class `C^{2,1/2}`, put
`ρ = ρ(h,u) = exp (h cos 3t + u) / Z(h,u)`, `E_ρ = ∫ u ρ` and `I = ∫ u'^2 ρ`, where `∫` is the
normalised Haar mean.  In the logarithmic chart the entropy is `H = ∫ u ρ - log Z + log Z_h`
and the Fisher information is `I = ∫ u'^2 ρ`.  The first variation of `H` in the direction `v` is
`∫ ρ (u - E_ρ) v` and the first variation of `I` in the direction `v` is
`2 ∫ u' v' ρ + ∫ ρ (u'^2 - I) v`.

## Provides

* `DGPS.Frontier.STR029.str029_49_first_variations_entropy_fisher_information`: one conjunction.
  (1) `s ↦ H(u + s v)` has derivative `∫ ρ (u - E_ρ) v` at `s = 0`.  (2) `s ↦ I(u + s v)` has
  derivative `2 ∫ u' v' ρ + ∫ ρ (u'^2 - I) v` at `s = 0`.
* `DGPS.Frontier.STR029.str029_49_first_variations_entropy_fisher_information_entropy_deriv`:
  the `deriv` form of part (1): `deriv (s ↦ H(u + s v)) 0 = ∫ ρ (u - E_ρ) v`.
* `DGPS.Frontier.STR029.str029_49_first_variations_entropy_fisher_information_fisher_deriv`:
  the `deriv` form of part (2): `deriv (s ↦ I(u + s v)) 0 = 2 ∫ u' v' ρ + ∫ ρ (u'^2 - I) v`.
* `DGPS.Frontier.STR029.entropyChart_STR02949`: the entropy `∫ u ρ - log Z(h,u) + log Z_h` of
  the density `ρ(h,u)` in the logarithmic chart.
* `DGPS.Frontier.STR029.fisherChart_STR02949`: the Fisher information `∫ u'^2 ρ(h,u)` in the
  logarithmic chart.

Auxiliary declarations carry the suffix `_STR02949`.  They lift `u, v, u', v'` into the periodic
Hölder algebra of STR029.68 and STR029.54 (`c0_of_c2_STR02949`, `el_STR02949`, `dEl_STR02949`),
differentiate along the line `U + s V` (`hasDerivAt_path_STR02949`,
`hasDerivAt_rho_path_STR02949`, `hasDerivAt_logZ_path_STR02949`), identify the chart quantities
with algebra expressions (`entropyChart_path_STR02949`, `fisherChart_path_STR02949`), and close
the algebra (`entropy_algebra_STR02949`, `fisher_algebra_STR02949`,
`hasDerivAt_entropy_path_STR02949`, `hasDerivAt_fisher_path_STR02949`).  The derivatives of
`log Z(h,·)` and `ρ(h,·)` come from `str029_48_derivative_normalized_density` and the Fréchet
derivative lemmas of STR029.48.

## R5 notes

* The operator `D` is read as the directional (Gâteaux) derivative at `u` in the direction `v`,
  formalised as `HasDerivAt (fun s => F (fun t => u t + s * v t)) (value) 0` for `F = H` and
  `F = I`.  A Fréchet derivative on a bundled `C^{2,α}` normed space is not claimed: the campaign
  library has no such bundled carrier at this commit, and `u ↦ u'` is not defined on the Hölder
  carrier of STR029.68.  The `deriv` forms of the two parts are also provided.
* The carrier is the concrete predicate `IsC2Alpha_STR02901 (1 / 2)` on plain functions `u, v`
  with `α = 1/2` fixed in the node preamble.  No Haar-mean-zero constraint is imposed on `u` or
  `v`, and `h` is an arbitrary real number.  Nothing beyond the two predicates is assumed.
* The "fixed Hölder neighbourhood" of the specification is not needed.  `H` and `I` are defined
  and differentiable at every `C^{2,α}` function `u` (the partition function is positive at every
  point, by STR029.48 and STR029.54), so the restriction to a neighbourhood is vacuous and the
  derivatives are proved at every `u`.
* Bounded integration is realised by the bounded linear mean functional `meanCLM_STR02954` on the
  periodic Hölder algebra.  Its composition with the Fréchet derivatives of STR029.48 and the
  product rule replaces the interchange of derivative and integral.  No dominated convergence
  argument is used.
* `∫ f` is the normalised Haar mean `meanT_STR02901 f = (2π)⁻¹ ∫_0^{2π} f dt`, and `ρ` is
  `rhoT_STR02901 h u`, that is `exp (h cos 3t + u t) / ∫ exp (h cos 3s + u s) ds`.  The centred
  integrands are the pointwise expressions `ρ (u - E_ρ) v` and `ρ (u'^2 - I) v`, with
  `E_ρ = meanT (u ρ)` and `I = meanT (u'^2 ρ)`.
* `H` and `I` are the explicit chart formulas of the specification, given by
  `entropyChart_STR02949` and `fisherChart_STR02949`.  The constant `log Z_h` is
  `log (meanT (exp (h cos 3t)))`, independent of `u`, so it has zero derivative.  No identification
  with `ordinaryEntropy`, `ordinaryFisher` or `AbsoluteDensity`, and no angular-to-physical rate
  normalisation, is made here; the node preamble assigns that identification to STR029.01.
* `u, v, u', v'` are lifted into `PeriodicHolder_STR02968` (exponent `1/2`) by the embedding
  theorem `str029_53_holder_multiplication_bounded_linear_operations_embeddings`, with the
  exponent hypothesis supplied by `holderExponent_half_STR02901`.  The line `U + s V` stays in
  the algebra, and STR029.48 is applied along it with the chain rule.
* `D(u'^2)[v] = 2 u' v'` is obtained as the derivative at `s = 0` of `(u' + s v')^2` in the
  commutative algebra, using `deriv (u + s v) = u' + s v'` (`deriv_path_STR02949`).
-/

open Filter Topology Function NormedSpace
open scoped ContDiff

namespace DGPS.Frontier.STR029

/-- The entropy in the logarithmic chart, `H_h(u) = ∫ u ρ - log Z(h,u) + log Z_h`. -/
noncomputable def entropyChart_STR02949 (h : ℝ) (u : ℝ → ℝ) : ℝ :=
  meanT_STR02901 (fun t => u t * rhoT_STR02901 h u t) -
    Real.log (meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u s))) +
    Real.log (meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s))))

/-- The Fisher information in the logarithmic chart, `I_h(u) = ∫ u'^2 ρ`. -/
noncomputable def fisherChart_STR02949 (h : ℝ) (u : ℝ → ℝ) : ℝ :=
  meanT_STR02901 (fun t => deriv u t ^ 2 * rhoT_STR02901 h u t)

/-- A `C^{2,1/2}` function and its derivative are `C^{0,1/2}` (the embeddings of STR029.53). -/
theorem c0_of_c2_STR02949 {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    IsC0Alpha_STR02953 (1 / 2) u ∧ IsC0Alpha_STR02953 (1 / 2) (deriv u) := by
  have := holderExponent_half_STR02901
  obtain ⟨h1, h2, -⟩ := str029_53_holder_multiplication_bounded_linear_operations_embeddings
    (α := 1 / 2)
  exact ⟨h1.1 u hu, h2.1 u hu⟩

/-- A `C^{2,1/2}` function is periodic Hölder of exponent `1/2`. -/
theorem isPerHolder_of_c2_STR02949 {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    IsPerHolder_STR02968 (1 / 2) u :=
  let h1 := (c0_of_c2_STR02949 hu).1
  ⟨h1.1, continuous_of_circHolderBdd_STR02953 half_pos_STR02968 h1.2, h1.2⟩

/-- The derivative of a `C^{2,1/2}` function is periodic Hölder of exponent `1/2`. -/
theorem isPerHolder_deriv_of_c2_STR02949 {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    IsPerHolder_STR02968 (1 / 2) (deriv u) :=
  let h1 := (c0_of_c2_STR02949 hu).2
  ⟨h1.1, continuous_of_circHolderBdd_STR02953 half_pos_STR02968 h1.2, h1.2⟩

/-- The Hölder-algebra element attached to a `C^{2,α}` function. -/
noncomputable def el_STR02949 {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    PeriodicHolder_STR02968 :=
  PeriodicHolder_STR02968.mk u (isPerHolder_of_c2_STR02949 hu)

/-- The Hölder-algebra element attached to the derivative of a `C^{2,α}` function. -/
noncomputable def dEl_STR02949 {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    PeriodicHolder_STR02968 :=
  PeriodicHolder_STR02968.mk (deriv u) (isPerHolder_deriv_of_c2_STR02949 hu)

/-- The underlying function of `el_STR02949 hu` is `u`. -/
theorem el_val_STR02949 {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    (el_STR02949 hu).val = u := rfl

/-- The underlying function of `dEl_STR02949 hu` is `deriv u`. -/
theorem dEl_val_STR02949 {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    (dEl_STR02949 hu).val = deriv u := rfl

/-- The line `s ↦ U + s V` in the Hölder algebra has derivative `V`. -/
theorem hasDerivAt_path_STR02949 (U V : PeriodicHolder_STR02968) :
    HasDerivAt (fun s : ℝ => U + s • V) V 0 := by
  have := ((hasDerivAt_id (0 : ℝ)).smul_const V).const_add U
  simpa using this

/-- The derivative of `u + s v` is `u' + s v'`. -/
theorem deriv_path_STR02949 {u v : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u)
    (hv : IsC2Alpha_STR02901 (1 / 2) v) (s : ℝ) :
    deriv (fun t => u t + s * v t) = fun t => deriv u t + s * deriv v t := by
  funext t
  exact deriv_add (hu.2.1 t) ((hv.2.1 t).const_mul s) |>.trans (by rw [deriv_const_mul_field])

/-- The Haar mean of a pointwise product of algebra elements is the mean functional on their
product. -/
theorem mean_eq_meanCLM_STR02949 (A B : PeriodicHolder_STR02968) :
    meanT_STR02901 (fun t => A.val t * B.val t) = meanCLM_STR02954 (A * B) := rfl

/-- Derivative of the density along the line `U + s V`, from STR029.48. -/
theorem hasDerivAt_rho_path_STR02949 (h : ℝ) (U V : PeriodicHolder_STR02968) :
    HasDerivAt (fun s : ℝ => rho_STR02954 (h, U + s • V))
      (rho_STR02954 (h, U) * (V - meanCLM_STR02954 (V * rho_STR02954 (h, U)) •
        (1 : PeriodicHolder_STR02968))) 0 := by
  have hγ := hasDerivAt_path_STR02949 U V
  have hl : HasFDerivAt (𝕜 := ℝ) (fun w : PeriodicHolder_STR02968 => rho_STR02954 (h, w))
      (fderiv ℝ (fun w : PeriodicHolder_STR02968 => rho_STR02954 (h, w)) U)
      ((fun s : ℝ => U + s • V) 0) := by
    simp only [zero_smul, add_zero]
    exact (hasFDerivAt_rho_STR02948 h U).differentiableAt.hasFDerivAt
  have key := hl.comp_hasDerivAt (0 : ℝ) hγ
  have e := (str029_48_derivative_normalized_density h U V).2
  rw [mean_eq_meanCLM_STR02949] at e
  exact key.congr_deriv e

/-- Derivative of `log Z` along the line `U + s V`, from STR029.48. -/
theorem hasDerivAt_logZ_path_STR02949 (h : ℝ) (U V : PeriodicHolder_STR02968) :
    HasDerivAt (fun s : ℝ => Real.log (Z_STR02954 (h, U + s • V)))
      (meanCLM_STR02954 (V * rho_STR02954 (h, U))) 0 := by
  have hγ := hasDerivAt_path_STR02949 U V
  have hl : HasFDerivAt (𝕜 := ℝ) (fun w : PeriodicHolder_STR02968 => Real.log (Z_STR02954 (h, w)))
      (fderiv ℝ (fun w : PeriodicHolder_STR02968 => Real.log (Z_STR02954 (h, w))) U)
      ((fun s : ℝ => U + s • V) 0) := by
    simp only [zero_smul, add_zero]
    exact (hasFDerivAt_logZ_STR02948 h U).differentiableAt.hasFDerivAt
  have key := hl.comp_hasDerivAt (0 : ℝ) hγ
  have e := (str029_48_derivative_normalized_density h U V).1
  rw [mean_eq_meanCLM_STR02949] at e
  exact key.congr_deriv e

/-- The chart entropy of `u + s v` as an expression in the Hölder algebra. -/
theorem entropyChart_path_STR02949 (h : ℝ) {u v : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u)
    (hv : IsC2Alpha_STR02901 (1 / 2) v) (s : ℝ) :
    entropyChart_STR02949 h (fun t => u t + s * v t) =
      meanCLM_STR02954 ((el_STR02949 hu + s • el_STR02949 hv) *
          rho_STR02954 (h, el_STR02949 hu + s • el_STR02949 hv)) -
        Real.log (Z_STR02954 (h, el_STR02949 hu + s • el_STR02949 hv)) +
        Real.log (meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s)))) := by
  set W := el_STR02949 hu + s • el_STR02949 hv with hW
  have hWv : W.val = fun t => u t + s * v t := rfl
  have hZ : Z_STR02954 (h, W) =
      meanT_STR02901 (fun r => Real.exp (h * Real.cos (3 * r) + (fun t => u t + s * v t) r)) :=
    Z_eq_meanT_STR02954 (h, W)
  unfold entropyChart_STR02949
  rw [← hZ]
  congr 2
  rw [meanCLM_apply_STR02954]
  congr 1
  funext t
  rw [val_mul_STR02954]
  have hr : rhoT_STR02901 h (fun t => u t + s * v t) t = (rho_STR02954 (h, W)).val t :=
    (rho_val_STR02954 (h, W) t).symm
  simp only [Pi.mul_apply, hr]
  rfl

/-- The chart Fisher information of `u + s v` as an expression in the Hölder algebra. -/
theorem fisherChart_path_STR02949 (h : ℝ) {u v : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u)
    (hv : IsC2Alpha_STR02901 (1 / 2) v) (s : ℝ) :
    fisherChart_STR02949 h (fun t => u t + s * v t) =
      meanCLM_STR02954 ((dEl_STR02949 hu + s • dEl_STR02949 hv) *
        (dEl_STR02949 hu + s • dEl_STR02949 hv) *
          rho_STR02954 (h, el_STR02949 hu + s • el_STR02949 hv)) := by
  set W := el_STR02949 hu + s • el_STR02949 hv with hW
  unfold fisherChart_STR02949
  rw [deriv_path_STR02949 hu hv s, meanCLM_apply_STR02954]
  congr 1
  funext t
  have hr : rhoT_STR02901 h (fun t => u t + s * v t) t = (rho_STR02954 (h, W)).val t :=
    (rho_val_STR02954 (h, W) t).symm
  rw [hr]
  simp only [val_mul_STR02954, PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_smul,
    Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dEl_val_STR02949]
  ring

/-- Algebra identity closing the entropy derivative: the `∫ V ρ` terms cancel. -/
theorem entropy_algebra_STR02949 (ρ U V : PeriodicHolder_STR02968) :
    meanCLM_STR02954 (V * ρ + U * (ρ * (V - meanCLM_STR02954 (V * ρ) •
        (1 : PeriodicHolder_STR02968)))) - meanCLM_STR02954 (V * ρ) =
      meanCLM_STR02954 (ρ * (U - meanCLM_STR02954 (U * ρ) • (1 : PeriodicHolder_STR02968)) * V) := by
  have e1 : U * (ρ * (V - meanCLM_STR02954 (V * ρ) • (1 : PeriodicHolder_STR02968))) =
      U * ρ * V - meanCLM_STR02954 (V * ρ) • (U * ρ) := by
    apply ext_STR02954
    funext t
    simp only [PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_smul,
      val_mul_STR02954, val_one_STR02954, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have e2 : ρ * (U - meanCLM_STR02954 (U * ρ) • (1 : PeriodicHolder_STR02968)) * V =
      U * ρ * V - meanCLM_STR02954 (U * ρ) • (V * ρ) := by
    apply ext_STR02954
    funext t
    simp only [PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_smul,
      val_mul_STR02954, val_one_STR02954, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  rw [e1, e2, map_add, map_sub, map_sub, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

/-- Algebra identity closing the Fisher derivative. -/
theorem fisher_algebra_STR02949 (ρ D D' V : PeriodicHolder_STR02968) :
    meanCLM_STR02954 ((D' * D + D * D') * ρ + D * D * (ρ * (V - meanCLM_STR02954 (V * ρ) •
        (1 : PeriodicHolder_STR02968)))) =
      2 * meanCLM_STR02954 (D * D' * ρ) +
        meanCLM_STR02954 (ρ * (D * D - meanCLM_STR02954 (D * D * ρ) •
          (1 : PeriodicHolder_STR02968)) * V) := by
  have e1 : (D' * D + D * D') * ρ + D * D * (ρ * (V - meanCLM_STR02954 (V * ρ) •
        (1 : PeriodicHolder_STR02968))) =
      (2 : ℝ) • (D * D' * ρ) + (D * D * ρ * V - meanCLM_STR02954 (V * ρ) • (D * D * ρ)) := by
    apply ext_STR02954
    funext t
    simp only [PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_sub,
      PeriodicHolder_STR02968.val_smul, val_mul_STR02954, val_one_STR02954, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have e2 : ρ * (D * D - meanCLM_STR02954 (D * D * ρ) • (1 : PeriodicHolder_STR02968)) * V =
      D * D * ρ * V - meanCLM_STR02954 (D * D * ρ) • (V * ρ) := by
    apply ext_STR02954
    funext t
    simp only [PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_smul,
      val_mul_STR02954, val_one_STR02954, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  rw [e1, e2, map_add, map_sub, map_sub, map_smul, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

/-- Derivative at `0` of the entropy expression along `U + s V`. -/
theorem hasDerivAt_entropy_path_STR02949 (h : ℝ) (U V : PeriodicHolder_STR02968) (C : ℝ) :
    HasDerivAt (fun s : ℝ => meanCLM_STR02954 ((U + s • V) * rho_STR02954 (h, U + s • V)) -
        Real.log (Z_STR02954 (h, U + s • V)) + C)
      (meanCLM_STR02954 (rho_STR02954 (h, U) * (U - meanCLM_STR02954 (U * rho_STR02954 (h, U)) •
        (1 : PeriodicHolder_STR02968)) * V)) 0 := by
  have hprod := (hasDerivAt_path_STR02949 U V).mul (hasDerivAt_rho_path_STR02949 h U V)
  have hm := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hprod
  have key := (hm.sub (hasDerivAt_logZ_path_STR02949 h U V)).add_const C
  refine key.congr_deriv ?_
  simp only [zero_smul, add_zero]
  exact entropy_algebra_STR02949 _ _ _

/-- Derivative at `0` of the Fisher expression along `U + s V`, `D + s D'`. -/
theorem hasDerivAt_fisher_path_STR02949 (h : ℝ) (U V D D' : PeriodicHolder_STR02968) :
    HasDerivAt (fun s : ℝ => meanCLM_STR02954 ((D + s • D') * (D + s • D') *
        rho_STR02954 (h, U + s • V)))
      (2 * meanCLM_STR02954 (D * D' * rho_STR02954 (h, U)) +
        meanCLM_STR02954 (rho_STR02954 (h, U) * (D * D - meanCLM_STR02954 (D * D *
          rho_STR02954 (h, U)) • (1 : PeriodicHolder_STR02968)) * V)) 0 := by
  have hP := hasDerivAt_path_STR02949 D D'
  have hprod := (hP.mul hP).mul (hasDerivAt_rho_path_STR02949 h U V)
  have key := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hprod
  refine key.congr_deriv ?_
  simp only [Pi.mul_apply, zero_smul, add_zero]
  exact fisher_algebra_STR02949 _ _ _ _

/-- First variations of the entropy and the Fisher information in the logarithmic chart.  With
`ρ = ρ(h,u)`, `E_ρ = ∫ u ρ` and `I = ∫ u'^2 ρ`, the derivative at `s = 0` of `s ↦ H(u + s v)` is
`∫ ρ (u - E_ρ) v`, and that of `s ↦ I(u + s v)` is `2 ∫ u' v' ρ + ∫ ρ (u'^2 - I) v`. -/
theorem str029_49_first_variations_entropy_fisher_information (h : ℝ) {u v : ℝ → ℝ}
    (hu : IsC2Alpha_STR02901 (1 / 2) u) (hv : IsC2Alpha_STR02901 (1 / 2) v) :
    HasDerivAt (fun s : ℝ => entropyChart_STR02949 h (fun t => u t + s * v t))
        (meanT_STR02901 (fun t => rhoT_STR02901 h u t *
          (u t - meanT_STR02901 (fun r => u r * rhoT_STR02901 h u r)) * v t)) 0 ∧
      HasDerivAt (fun s : ℝ => fisherChart_STR02949 h (fun t => u t + s * v t))
        (2 * meanT_STR02901 (fun t => deriv u t * deriv v t * rhoT_STR02901 h u t) +
          meanT_STR02901 (fun t => rhoT_STR02901 h u t *
            (deriv u t ^ 2 - meanT_STR02901 (fun r => deriv u r ^ 2 * rhoT_STR02901 h u r)) *
              v t)) 0 := by
  set U := el_STR02949 hu with hUdef
  set V := el_STR02949 hv with hVdef
  set D := dEl_STR02949 hu with hDdef
  set D' := dEl_STR02949 hv with hD'def
  have hr : ∀ t, rhoT_STR02901 h u t = (rho_STR02954 (h, U)).val t := fun t =>
    (rho_val_STR02954 (h, U) t).symm
  refine ⟨?_, ?_⟩
  · have hfun : (fun s : ℝ => entropyChart_STR02949 h (fun t => u t + s * v t)) =
        fun s => meanCLM_STR02954 ((U + s • V) * rho_STR02954 (h, U + s • V)) -
          Real.log (Z_STR02954 (h, U + s • V)) +
          Real.log (meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s)))) :=
      funext fun s => entropyChart_path_STR02949 h hu hv s
    rw [hfun]
    refine (hasDerivAt_entropy_path_STR02949 h U V _).congr_deriv ?_
    rw [meanCLM_apply_STR02954]
    congr 1
    funext t
    have hE : meanT_STR02901 (fun r => u r * rhoT_STR02901 h u r) =
        meanCLM_STR02954 (U * rho_STR02954 (h, U)) := by
      rw [meanCLM_apply_STR02954]
      congr 1
      funext r
      rw [val_mul_STR02954, Pi.mul_apply, hr r]
      rfl
    rw [hE, hr t]
    simp only [val_mul_STR02954, PeriodicHolder_STR02968.val_sub,
      PeriodicHolder_STR02968.val_smul, val_one_STR02954, Pi.mul_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, mul_one]
    rfl
  · have hfun : (fun s : ℝ => fisherChart_STR02949 h (fun t => u t + s * v t)) =
        fun s => meanCLM_STR02954 ((D + s • D') * (D + s • D') *
          rho_STR02954 (h, U + s • V)) :=
      funext fun s => fisherChart_path_STR02949 h hu hv s
    rw [hfun]
    refine (hasDerivAt_fisher_path_STR02949 h U V D D').congr_deriv ?_
    have hI : meanT_STR02901 (fun r => deriv u r ^ 2 * rhoT_STR02901 h u r) =
        meanCLM_STR02954 (D * D * rho_STR02954 (h, U)) := by
      rw [meanCLM_apply_STR02954]
      congr 1
      funext r
      rw [val_mul_STR02954, Pi.mul_apply, val_mul_STR02954, Pi.mul_apply, hr r]
      simp only [hDdef, dEl_val_STR02949]
      ring
    have hJ : meanT_STR02901 (fun t => deriv u t * deriv v t * rhoT_STR02901 h u t) =
        meanCLM_STR02954 (D * D' * rho_STR02954 (h, U)) := by
      rw [meanCLM_apply_STR02954]
      congr 1
      funext r
      rw [val_mul_STR02954, Pi.mul_apply, val_mul_STR02954, Pi.mul_apply, hr r]
      rfl
    rw [hI, hJ, meanCLM_apply_STR02954 (rho_STR02954 (h, U) * _ * V)]
    congr 2
    funext t
    rw [hr t]
    simp only [val_mul_STR02954, PeriodicHolder_STR02968.val_sub,
      PeriodicHolder_STR02968.val_smul, val_one_STR02954, Pi.mul_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, hDdef, dEl_val_STR02949]
    rw [show V.val t = v t from rfl]
    ring

/-- The `deriv` form of the first variation of the entropy: `DH[v] = ∫ ρ (u - E_ρ) v`. -/
theorem str029_49_first_variations_entropy_fisher_information_entropy_deriv (h : ℝ)
    {u v : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) (hv : IsC2Alpha_STR02901 (1 / 2) v) :
    deriv (fun s : ℝ => entropyChart_STR02949 h (fun t => u t + s * v t)) 0 =
      meanT_STR02901 (fun t => rhoT_STR02901 h u t *
        (u t - meanT_STR02901 (fun r => u r * rhoT_STR02901 h u r)) * v t) :=
  (str029_49_first_variations_entropy_fisher_information h hu hv).1.deriv

/-- The `deriv` form of the first variation of the Fisher information:
`DI[v] = 2 ∫ u' v' ρ + ∫ ρ (u'^2 - I) v`. -/
theorem str029_49_first_variations_entropy_fisher_information_fisher_deriv (h : ℝ)
    {u v : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) (hv : IsC2Alpha_STR02901 (1 / 2) v) :
    deriv (fun s : ℝ => fisherChart_STR02949 h (fun t => u t + s * v t)) 0 =
      2 * meanT_STR02901 (fun t => deriv u t * deriv v t * rhoT_STR02901 h u t) +
        meanT_STR02901 (fun t => rhoT_STR02901 h u t *
          (deriv u t ^ 2 - meanT_STR02901 (fun r => deriv u r ^ 2 * rhoT_STR02901 h u r)) *
            v t) :=
  (str029_49_first_variations_entropy_fisher_information h hu hv).2.deriv

end DGPS.Frontier.STR029
