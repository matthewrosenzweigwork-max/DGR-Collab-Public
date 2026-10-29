import DGPS.Frontier.STR029.T53
import DGPS.Frontier.STR029.T54
import DGPS.Frontier.STR029.T55

/-!
# STR029.15: Smooth variational range map

Task id: STR029.15 (node STR029, frontier unit).
Title: Smooth variational range map.

Statement: the map `R(a, b, h, γ, w) = P G(h, γ, a cos t + b sin t + w)` on `ℝ × ℝ × ℝ × ℝ × E`
is smooth on a common open neighbourhood of zero, satisfies `R 0 = 0`, and has the derivative
in the direction `w` at zero equal to `-2 (∂_t² + 1)`.

## Provides

* `DGPS.Frontier.STR029.str029_15_smooth_variational_range_map`: the main statement. There is an
  open set `U` containing zero on which `R` is `C^∞` as a map into `Y`, `R 0 = 0`, and for every
  `w ∈ E` and every `t` the value at `t` of `D_w R(0) w` is `-2 (w'' t + w t)`.
* `DGPS.Frontier.STR029.str029_15_smooth_variational_range_map_pointwise`: the pointwise formula
  `R(a, b, h, γ, w)(t) = P(gradG(h, γ, a cos + b sin + w))(t)`, with `gradG` the gradient of
  STR029.50.

The variational range map is `Rvar_STR02915 x = PY (Gmap (paramMap_STR02915 x))`. Here
`paramMap_STR02915 (a, b, h, γ, w) = (h, γ, a cos + b sin + w)` is the chart into
`ℝ × ℝ × C^{2,1/2}`, `Gmap_STR02955` is the gradient map of STR029.55, and `PY_STR02955` is the
projection `P` of STR029.53 with values in `Y`. The analytic estimates come from STR029.53,
STR029.54 and STR029.55 and are only assembled in this file.

## R5 notes

* No hypothesis is added. The statement has no assumptions beyond the carriers and the gradient
  of STR029.50 through STR029.55.
* "Smooth on a common neighbourhood of zero" is read as: there is an open set `U` containing
  zero with `R` `C^∞` on `U`. The proof takes `U = univ`, so `R` is `C^∞` on all of
  `ℝ × ℝ × ℝ × ℝ × E`. This is stronger than the wording and is not a restriction.
* The domain is `ℝ⁴ × E` with `E` the closed subspace of `C^{2,1/2}` of mean zero functions
  orthogonal to `cos` and `sin`. The codomain of `R` is `Y`, the closed subspace of `C^{0,1/2}`
  with the same constraints, obtained from `P` by corestriction.
* The coordinates are ordered `(a, b, h, γ, w)`. The parameters `a, b, h, γ` are real and `w`
  ranges over `E`. The product space carries the product normed space structure from Mathlib.
* The chart function `a cos t + b sin t + w` lives in `C^{2,1/2}`. Membership of `cos` and `sin`
  in `C^{2,1/2}` is proved in this file (`cos_isC2_STR02915`, `sin_isC2_STR02915`), using the
  Hölder bound `c0_of_deriv_STR02953` with exponent `1/2`.
* `P` is the projection `projP_STR02953` of STR029.53 on `C^{0,1/2}`, namely
  `Pf = f - ∫ f - 2 (∫ f cos) cos - 2 (∫ f sin) sin` with the normalized measure
  `dt/(2π)`. `G` is `gradG_STR02950` of STR029.50, with the density `rho_STR02954` of
  STR029.54. The design choice of defining `R` directly as `P` applied to the gradient is kept;
  no Euler equation and no projected Euler range map are used or assumed to coincide with `R`.
* `D_w R(0)` is read as the Fréchet derivative at zero of `w ↦ R(0, 0, 0, 0, w)` from `E` to
  `Y`, applied to `w`. This is the partial derivative in the `w` direction only. The identity
  `-2 (∂_t² + 1)` is read pointwise on the periodic representative: `∂_t` is `deriv` and `∂_t²`
  is `deriv (deriv ·)`, evaluated at `t`.
* `R 0 = 0` is read as the value at the origin of `ℝ⁴ × E`, where all of `a, b, h, γ, w` are zero.
* The angular variable `t` is the periodic variable with normalized measure `dt/(2π)`. The
  normalization `t = 2πx`, `a0 = 4π²` and the angular-to-physical rate conversion do not enter
  this unit.
* The optimizer-chart predicate, the weighted carriers, the AbsoluteDensity domain and the
  entropy and Fisher conventions are not used directly here. They enter only through the
  gradient of STR029.50 and the carriers of STR029.68 and STR029.69.
-/

open scoped ContDiff
open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.STR029

/-! ### The functions `cos` and `sin` in `C^{2,1/2}` -/

theorem cos_isC2_STR02915 : IsC2Alpha_STR02901 (1 / 2) Real.cos := by
  have hper : Function.Periodic Real.cos (2 * Real.pi) := Real.cos_periodic
  have hd : Differentiable ℝ Real.cos := Real.differentiable_cos
  have h1 : deriv Real.cos = fun x => -Real.sin x := Real.deriv_cos'
  have hdd : deriv (deriv Real.cos) = fun t => -Real.cos t := by
    funext t
    rw [h1]
    exact ((Real.hasDerivAt_sin t).neg).deriv
  have hd1 : Differentiable ℝ (deriv Real.cos) := by
    rw [h1]
    fun_prop
  have hc : Continuous (deriv (deriv Real.cos)) := by
    rw [hdd]
    fun_prop
  have hneg : Function.Periodic (fun t : ℝ => -Real.cos t) (2 * Real.pi) := fun t => by
    simp [Real.cos_add_two_pi]
  have hnegd : Differentiable ℝ (fun t : ℝ => -Real.cos t) := by fun_prop
  have hb : Bdd (deriv (fun t : ℝ => -Real.cos t)) := ⟨1, fun x => by
    have h : deriv (fun t : ℝ => -Real.cos t) x = - -Real.sin x :=
      ((Real.hasDerivAt_cos x).neg).deriv
    rw [h, neg_neg]
    exact Real.abs_sin_le_one x⟩
  obtain ⟨⟨-, h2⟩, -⟩ :=
    c0_of_deriv_STR02953 (α := 1 / 2) half_pos_STR02968 (by norm_num) hneg hnegd hb
  unfold IsC2Alpha_STR02901
  refine ⟨hper, hd, hd1, hc, ?_⟩
  rw [hdd]
  exact h2

theorem sin_isC2_STR02915 : IsC2Alpha_STR02901 (1 / 2) Real.sin := by
  have hper : Function.Periodic Real.sin (2 * Real.pi) := Real.sin_periodic
  have hd : Differentiable ℝ Real.sin := Real.differentiable_sin
  have h1 : deriv Real.sin = Real.cos := Real.deriv_sin
  have hdd : deriv (deriv Real.sin) = fun t => -Real.sin t := by
    funext t
    rw [h1]
    exact (Real.hasDerivAt_cos t).deriv
  have hd1 : Differentiable ℝ (deriv Real.sin) := by
    rw [h1]
    exact Real.differentiable_cos
  have hc : Continuous (deriv (deriv Real.sin)) := by
    rw [hdd]
    fun_prop
  have hneg : Function.Periodic (fun t : ℝ => -Real.sin t) (2 * Real.pi) := fun t => by
    simp [Real.sin_add_two_pi]
  have hnegd : Differentiable ℝ (fun t : ℝ => -Real.sin t) := by fun_prop
  have hb : Bdd (deriv (fun t : ℝ => -Real.sin t)) := ⟨1, fun x => by
    have h : deriv (fun t : ℝ => -Real.sin t) x = -Real.cos x :=
      ((Real.hasDerivAt_sin x).neg).deriv
    rw [h, abs_neg]
    exact Real.abs_cos_le_one x⟩
  obtain ⟨⟨-, h2⟩, -⟩ :=
    c0_of_deriv_STR02953 (α := 1 / 2) half_pos_STR02968 (by norm_num) hneg hnegd hb
  unfold IsC2Alpha_STR02901
  refine ⟨hper, hd, hd1, hc, ?_⟩
  rw [hdd]
  exact h2

/-- The function `cos` as an element of `C^{2,1/2}`. -/
noncomputable def cosC2_STR02915 : PeriodicC2_STR02969 :=
  PeriodicC2_STR02969.mk Real.cos cos_isC2_STR02915

/-- The function `sin` as an element of `C^{2,1/2}`. -/
noncomputable def sinC2_STR02915 : PeriodicC2_STR02969 :=
  PeriodicC2_STR02969.mk Real.sin sin_isC2_STR02915

theorem cosC2_val_STR02915 : cosC2_STR02915.val = Real.cos := rfl

theorem sinC2_val_STR02915 : sinC2_STR02915.val = Real.sin := rfl

/-! ### The chart `(a, b, h, γ, w) ↦ (h, γ, a cos + b sin + w)` -/

/-- The chart from `ℝ × ℝ × ℝ × ℝ × E` into `ℝ × ℝ × C^{2,1/2}`. -/
noncomputable def paramMap_STR02915 (x : ℝ × ℝ × ℝ × ℝ × E_STR02969) :
    ℝ × ℝ × PeriodicC2_STR02969 :=
  (x.2.2.1, x.2.2.2.1,
    x.1 • cosC2_STR02915 + x.2.1 • sinC2_STR02915 + ((x.2.2.2.2 : E_STR02969) : PeriodicC2_STR02969))

theorem paramMap_smooth_STR02915 : ContDiff ℝ ∞ paramMap_STR02915 := by
  have hE : ContDiff ℝ ∞ (fun x : ℝ × ℝ × ℝ × ℝ × E_STR02969 =>
      ((x.2.2.2.2 : E_STR02969) : PeriodicC2_STR02969)) :=
    E_STR02969.subtypeL.contDiff.comp
      (contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd)))
  have h1 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × ℝ × ℝ × E_STR02969 => x.1) := contDiff_fst
  have h2 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × ℝ × ℝ × E_STR02969 => x.2.1) :=
    contDiff_fst.comp contDiff_snd
  have h3 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × ℝ × ℝ × E_STR02969 => x.2.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp contDiff_snd)
  have h4 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × ℝ × ℝ × E_STR02969 => x.2.2.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))
  have hc : ContDiff ℝ ∞ (fun x : ℝ × ℝ × ℝ × ℝ × E_STR02969 => x.1 • cosC2_STR02915) :=
    h1.smul contDiff_const
  have hs : ContDiff ℝ ∞ (fun x : ℝ × ℝ × ℝ × ℝ × E_STR02969 => x.2.1 • sinC2_STR02915) :=
    h2.smul contDiff_const
  unfold paramMap_STR02915
  exact ContDiff.prodMk h3 (ContDiff.prodMk h4 ((hc.add hs).add hE))

/-! ### The variational range map -/

/-- The variational range map `R = P G ∘ chart` on `ℝ × ℝ × ℝ × ℝ × E`, with values in `Y`. -/
noncomputable def Rvar_STR02915 (x : ℝ × ℝ × ℝ × ℝ × E_STR02969) : Y_STR02969 :=
  PY_STR02955 (Gmap_STR02955 (paramMap_STR02915 x))

theorem Rvar_smooth_STR02915 : ContDiff ℝ ∞ Rvar_STR02915 :=
  PY_STR02955.contDiff.comp (Gmap_smooth_STR02955.comp paramMap_smooth_STR02915)

theorem paramMap_zero_STR02915 : paramMap_STR02915 0 = 0 := by
  simp [paramMap_STR02915]

theorem Rvar_zero_STR02915 : Rvar_STR02915 0 = 0 := by
  unfold Rvar_STR02915
  rw [paramMap_zero_STR02915, Gmap_zero_STR02955, map_zero]

/-- The embedding `v ↦ (0, 0, v)` of `E` into `ℝ × ℝ × E`. -/
noncomputable def Lzero_STR02915 : E_STR02969 →L[ℝ] ℝ × ℝ × E_STR02969 :=
  (0 : E_STR02969 →L[ℝ] ℝ).prod ((0 : E_STR02969 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E_STR02969))

theorem Lzero_apply_STR02915 (v : E_STR02969) : Lzero_STR02915 v = (0, 0, v) := by
  simp [Lzero_STR02915]

theorem Rvar_eq_Rmap_STR02915 (h γ : ℝ) (v : E_STR02969) :
    Rvar_STR02915 (0, 0, h, γ, v) = Rmap_STR02955 (h, γ, v) := by
  have hp : paramMap_STR02915 (0, 0, h, γ, v) = incl_STR02955 (h, γ, v) := by
    simp [paramMap_STR02915, incl_STR02955]
  unfold Rvar_STR02915 Rmap_STR02955
  rw [hp]

theorem Rvar_comp_STR02915 :
    (fun v : E_STR02969 => Rvar_STR02915 (0, 0, 0, 0, v)) = Rmap_STR02955 ∘ Lzero_STR02915 := by
  funext v
  rw [Function.comp_apply, Lzero_apply_STR02915]
  exact Rvar_eq_Rmap_STR02915 0 0 v

theorem fderivRvar_STR02915 (w : E_STR02969) :
    fderiv ℝ (fun v : E_STR02969 => Rvar_STR02915 (0, 0, 0, 0, v)) 0 w =
      fderiv ℝ Rmap_STR02955 0 ((0 : ℝ), (0 : ℝ), w) := by
  rw [Rvar_comp_STR02915]
  have hR : DifferentiableAt ℝ Rmap_STR02955 (Lzero_STR02915 0) := by
    rw [map_zero]
    exact (Rmap_smooth_STR02955.differentiable (by simp)) 0
  rw [fderiv_comp (0 : E_STR02969) hR Lzero_STR02915.differentiableAt, map_zero]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv, Lzero_apply_STR02915]

/-! ### Pointwise formula -/

theorem paramMap_val_STR02915 (a b : ℝ) (w : E_STR02969) :
    (a • cosC2_STR02915 + b • sinC2_STR02915 + ((w : E_STR02969) : PeriodicC2_STR02969)).val =
      uT_STR02901 a b ((w : E_STR02969) : PeriodicC2_STR02969).val := by
  funext s
  simp only [PeriodicC2_STR02969.val_add, PeriodicC2_STR02969.val_smul, cosC2_val_STR02915,
    sinC2_val_STR02915, Pi.add_apply, Pi.smul_apply, smul_eq_mul, uT_STR02901]

/-- Pointwise formula: the variational range map at `(a, b, h, γ, w)` is `P` of the gradient of
STR029.50 evaluated at the chart function `a cos + b sin + w`. -/
theorem str029_15_smooth_variational_range_map_pointwise
    (x : ℝ × ℝ × ℝ × ℝ × E_STR02969) (t : ℝ) :
    ((Rvar_STR02915 x : Y_STR02969) : PeriodicHolder_STR02968).val t =
      projP_STR02953 (gradG_STR02950 x.2.2.1 x.2.2.2.1
        (uT_STR02901 x.1 x.2.1 ((x.2.2.2.2 : E_STR02969) : PeriodicC2_STR02969).val)) t := by
  have hu : (paramMap_STR02915 x).2.2.val =
      uT_STR02901 x.1 x.2.1 ((x.2.2.2.2 : E_STR02969) : PeriodicC2_STR02969).val :=
    paramMap_val_STR02915 x.1 x.2.1 x.2.2.2.2
  have hG : (Gmap_STR02955 (paramMap_STR02915 x)).val =
      gradG_STR02950 x.2.2.1 x.2.2.2.1
        (uT_STR02901 x.1 x.2.1 ((x.2.2.2.2 : E_STR02969) : PeriodicC2_STR02969).val) := by
    rw [← hu]
    exact Gfun_val_STR02955 x.2.2.1 x.2.2.2.1 (paramMap_STR02915 x).2.2
  unfold Rvar_STR02915
  rw [PY_val_STR02955, PCLM_val_STR02955, hG]

/-! ### Main statement -/

/-- STR029.15, smooth variational range map. The map `R(a, b, h, γ, w) = P G(h, γ, a cos + b sin + w)`
is `C^∞` on the open set `U = univ`, which contains zero; `R 0 = 0`; and for every `w ∈ E` and
every `t` the value at `t` of the derivative of `w ↦ R(0, 0, 0, 0, w)` at zero, applied to `w`,
equals `-2 (w'' t + w t)`. -/
theorem str029_15_smooth_variational_range_map :
    ∃ U : Set (ℝ × ℝ × ℝ × ℝ × E_STR02969), IsOpen U ∧ (0 : ℝ × ℝ × ℝ × ℝ × E_STR02969) ∈ U ∧
      ContDiffOn ℝ ∞ Rvar_STR02915 U ∧ Rvar_STR02915 0 = 0 ∧
      ∀ (w : E_STR02969) (t : ℝ),
        ((fderiv ℝ (fun v : E_STR02969 => Rvar_STR02915 (0, 0, 0, 0, v)) 0 w : Y_STR02969) :
            PeriodicHolder_STR02968).val t =
          -2 * (deriv (deriv (w : PeriodicC2_STR02969).val) t + (w : PeriodicC2_STR02969).val t) :=
  ⟨Set.univ, isOpen_univ, Set.mem_univ _, Rvar_smooth_STR02915.contDiffOn, Rvar_zero_STR02915,
    fun w t => by
      rw [fderivRvar_STR02915]
      exact fderivR_STR02955 w t⟩

end DGPS.Frontier.STR029
