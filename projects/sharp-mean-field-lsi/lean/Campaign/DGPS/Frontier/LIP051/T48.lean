import DGPS.Frontier.LIP051.T46
import DGPS.Frontier.LIP051.T47
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# LIP051.48: Remove unit-variance normalization in the scalar limit

Task id `LIP051.48`, title "Remove unit-variance normalization in the scalar limit" (node LIP051,
"Joint Gaussian and quadratic fluctuation limit", size M, leaf formalization, verification V1).
Source: `frontier_decomposition_20261024/nodes/LIP051.md`, the `LIP051.48` statement and proof.

## Provides

* `DGPS.Frontier.LIP051.lip051_48_remove_unit_variance_normalization_scalar_limit`: for a
  probability measure `μ` on a measurable space, a real Hilbert basis `e` of `L²(μ)` with
  `e 0 = 1`, measurable representatives `f j` of the classes `e j`, and any `r : ℕ` and
  `v : Fin r → ℝ`, the characteristic functions of the scalar combinations
  `∑_{j<r} v_j Z_{N,j}` with `Z_{N,j} = N^{-1/2} ∑_{l<N} f_{j+1}(X_l)`, under the product law
  `μ^N` on `Fin N → α`, converge to `exp(-(1/2) ∑_j v_j²)`.
* Helpers (all suffixed `_LIP05148`): `integral_exp_zero_LIP05148` (the characteristic function of
  a centred, almost surely vanishing variable is one), `charFun_scaled_LIP05148` (the one-coordinate
  characteristic function of `Y/σ` at `cσ` equals the integral of `exp(i c Y)`), and
  `exponent_LIP05148` (the exponent of the joint sum is the scalar sum of the projection `Y_v`).

## R5 notes

1. Positive modes (FD-002 reading). The coordinate `j : Fin r` is paired with the basis index
   `(j : ℕ) + 1`, as in LIP051.46. Index zero, the constant mode `e 0 = 1`, does not occur in any
   `Z_{N,j}`. The constant mode would give `Z_{N,0} = √N` identically, which cannot converge to a
   centred Gaussian, so no reading with index zero is adopted. The hypothesis `he0` enters only
   through LIP051.46, which uses it to obtain the positive-mode mean zero.
2. Target binder. The vector `v ∈ ℝ^r` is realised as `Fin r → ℝ`, and `r : ℕ` is the number of
   coordinates. The specification's `ℝ`-valued Gaussian target `exp(-(1/2)∑ v_j²)` is written as
   the complex exponential of the real number `-(1/2) * ∑ v_j²`, cast to `ℂ`. The characteristic
   functions are complex-valued and the limit is taken in `ℂ`.
3. The normalisation is written as the real power `(N : ℝ) ^ (-(1/2 : ℝ))`, as in the
   specification's `N^{-1/2}`. It is identified with `(√N)⁻¹` by `rpow_neg_half_LIP05147` from
   LIP051.47 for every `N`, including `N = 0`; the limit does not depend on the value at `N = 0`.
4. Hypotheses. The ambient space `α` is an arbitrary measurable space with a probability measure
   `μ`. The campaign identification of `S.mu`, `Torus d` and `S.e` belongs to LIP051.01 and is not
   part of this file. The Hilbert basis `e`, the constant `he0 : e 0 = Lp.const 2 μ 1`, the
   measurable representatives `f` with `f j =ᵐ[μ] e j`, and the measurability of each `f j` are
   exactly the hypotheses of LIP051.46. No moment, boundedness or continuity hypothesis is added.
5. Sample space and law. The sample space is `Fin N → α` with `Q_N = Measure.pi (fun _ => μ)` and
   coordinates `x l`, the same product law as in LIP051.47.
6. Degenerate case `∑ v_j² = 0`. LIP051.46 gives `Y_v =ᵐ[μ] 0`. The characteristic function of
   `Y_v` at any scale is then one, so both sides equal one. No separate null-set argument on the
   product space is needed, because LIP051.47 converts the joint integral into an `N`th power.
7. Non-degenerate case `σ = √(∑ v_j²) > 0`. The standardised variable `Y_v / σ` has mean zero and
   second moment one, by LIP051.46. The pinned Mathlib lemma
   `ProbabilityTheory.tendsto_charFun_inv_sqrt_mul_pow` applies to it with argument `σ`, and the
   scaling identity `(σ/√N)(Y_v/σ) = Y_v/√N` identifies its `N`th power with the joint integral.
8. The statement uses only the scalar combination `Y_v`; it does not use the kernel `K`, the
   diagonal convention, `U_N`, the Wick object or any tilt. Convergence under the tilted particle
   law is outside this unit and is not asserted.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DGPS.Frontier.LIP051

/-- The characteristic function of an almost surely vanishing variable is one. -/
lemma integral_exp_zero_LIP05148 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (Y : α → ℝ) (hY : Y =ᵐ[μ] 0) (c : ℝ) :
    ∫ y, Complex.exp (Complex.I * (c : ℂ) * (Y y : ℂ)) ∂μ = 1 := by
  rw [integral_congr_ae (g := fun _ => (1 : ℂ))]
  · simp
  · filter_upwards [hY] with y hy
    simp [hy]

/-- Scaling identity: the integral of `exp (i c Y)` equals the characteristic function of `Y / σ`
at `c σ`, for a nonzero scale `σ`. -/
lemma charFun_scaled_LIP05148 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (Y : α → ℝ) (hY : Measurable Y) (σ c : ℝ) (hσ : σ ≠ 0) :
    ∫ x, Complex.exp (Complex.I * (c : ℂ) * (Y x : ℂ)) ∂μ
      = charFun (μ.map (fun x => Y x / σ)) (c * σ) := by
  rw [charFun_apply_real, integral_map (hY.div_const σ).aemeasurable
    (Measurable.aestronglyMeasurable (by fun_prop))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hσC : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ
  push_cast
  field_simp

/-- Rearrangement of the joint exponent: the scalar combination `∑_j v_j Z_{N,j}` with
`Z_{N,j} = c ∑_l f_{j+1}(x_l)` equals `c ∑_l Y_v(x_l)` inside the complex exponent. -/
lemma exponent_LIP05148 {α : Type*} (f : ℕ → α → ℝ) (r N : ℕ) (v : Fin r → ℝ) (c : ℝ)
    (x : Fin N → α) :
    Complex.I * ∑ j : Fin r, (v j : ℂ) * ((c * ∑ l : Fin N, f ((j : ℕ) + 1) (x l) : ℝ) : ℂ)
      = Complex.I * (c : ℂ) * ∑ l : Fin N, ((∑ j : Fin r, v j * f ((j : ℕ) + 1) (x l) : ℝ) : ℂ) := by
  have hsum : ∑ j : Fin r, (v j : ℂ) * ((c * ∑ l : Fin N, f ((j : ℕ) + 1) (x l) : ℝ) : ℂ)
      = (c : ℂ) * ∑ l : Fin N, ((∑ j : Fin r, v j * f ((j : ℕ) + 1) (x l) : ℝ) : ℂ) := by
    push_cast
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hsum, mul_assoc]

/-- **LIP051.48.** For a probability measure `μ`, a real Hilbert basis `e` of `L²(μ)` with
`e 0 = 1` and measurable representatives `f j` of the classes `e j`, and for every `r` and
`v : Fin r → ℝ`, the characteristic functions of `∑_{j<r} v_j N^{-1/2} ∑_{l<N} f_{j+1}(X_l)` under
`μ^N` converge to `exp (-(1/2) ∑_j v_j²)`. The positive-mode indexing is that of LIP051.46. -/
theorem lip051_48_remove_unit_variance_normalization_scalar_limit
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (f : ℕ → α → ℝ) (hfm : ∀ j, Measurable (f j)) (hfe : ∀ j, f j =ᵐ[μ] (e j : α → ℝ))
    (r : ℕ) (v : Fin r → ℝ) :
    Tendsto (fun N : ℕ => ∫ x : Fin N → α,
        Complex.exp (Complex.I * ∑ j : Fin r, (v j : ℂ) *
          (((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l : Fin N, f ((j : ℕ) + 1) (x l) : ℝ) : ℂ))
        ∂(Measure.pi fun _ : Fin N => μ))
      atTop (𝓝 (Complex.exp (((-(1 / 2 : ℝ)) * ∑ j : Fin r, v j ^ 2 : ℝ) : ℂ))) := by
  obtain ⟨hYm, -, hmean, hsec, hzero⟩ :=
    lip051_46_moments_scalar_feature_projection μ e he0 f hfm hfe r v
  set Yv : α → ℝ := fun x => ∑ j : Fin r, v j * f ((j : ℕ) + 1) x with hYv
  set S : ℝ := ∑ j : Fin r, v j ^ 2 with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg (v j)
  have hint : ∀ N : ℕ, ∫ x : Fin N → α,
      Complex.exp (Complex.I * ∑ j : Fin r, (v j : ℂ) *
        (((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l : Fin N, f ((j : ℕ) + 1) (x l) : ℝ) : ℂ))
      ∂(Measure.pi fun _ : Fin N => μ)
      = (∫ y, Complex.exp (Complex.I * (((N : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Yv y : ℂ)) ∂μ)
          ^ N := by
    intro N
    simp_rw [exponent_LIP05148 f r N v]
    exact integral_exp_sum_LIP05147 μ Yv N _
  rcases hSnn.eq_or_lt with hS0 | hSpos
  · -- Degenerate case: `Y_v = 0` almost everywhere, both sides equal one.
    have hY0 : Yv =ᵐ[μ] 0 := hzero hS0.symm
    refine Tendsto.congr (fun N => (hint N).symm) ?_
    simp only [integral_exp_zero_LIP05148 μ Yv hY0, one_pow, ← hS0, mul_zero,
      Complex.ofReal_zero, Complex.exp_zero]
    exact tendsto_const_nhds
  · -- Non-degenerate case: apply the scalar characteristic-function power limit to `Y_v / σ`.
    set σ : ℝ := Real.sqrt S with hσdef
    have hσpos : 0 < σ := Real.sqrt_pos.mpr hSpos
    have hσsq : σ ^ 2 = S := Real.sq_sqrt hSpos.le
    have hY'm : Measurable (fun x => Yv x / σ) := hYm.div_const σ
    have hY'mean : μ[fun x => Yv x / σ] = 0 := by
      rw [integral_div, hmean, zero_div]
    have hY'sq : μ[(fun x => Yv x / σ) ^ 2] = 1 := by
      have hfun : ((fun x => Yv x / σ) ^ 2 : α → ℝ) = fun x => Yv x ^ 2 / S := by
        funext x
        simp only [Pi.pow_apply]
        rw [div_pow, hσsq]
      rw [hfun, integral_div, hsec]
      exact div_self hSpos.ne'
    have hlim := tendsto_charFun_inv_sqrt_mul_pow hY'm.aemeasurable hY'mean hY'sq σ
    have hlimeq : Complex.exp (-(σ : ℂ) ^ 2 / 2)
        = Complex.exp (((-(1 / 2 : ℝ)) * S : ℝ) : ℂ) := by
      congr 1
      rw [← hσsq]
      push_cast
      ring
    rw [hlimeq] at hlim
    refine Tendsto.congr (fun N => ?_) hlim
    rw [hint N, charFun_scaled_LIP05148 μ Yv hYm σ _ hσpos.ne', rpow_neg_half_LIP05147]

end DGPS.Frontier.LIP051
