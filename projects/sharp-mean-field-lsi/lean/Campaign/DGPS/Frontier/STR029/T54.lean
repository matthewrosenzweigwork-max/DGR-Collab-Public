import DGPS.Frontier.STR029.T53
import DGPS.Frontier.STR029.T68

/-!
# STR029.54: Smooth exponential normalization in the Hölder algebra

Task id: STR029.54 (node STR029, frontier unit, leaf formalization).
Title: Smooth exponential normalization in the Hölder algebra.

The carrier is `PeriodicHolder_STR02968` (the periodic Hölder space with exponent `1/2`, from
STR029.68), made into a commutative normed algebra over `ℝ` with the product of STR029.53.  The
parameter space is `ℝ × PeriodicHolder_STR02968` with the bounded linear map
`(h, u) ↦ h cos 3t + u`.

## Provides

* `DGPS.Frontier.STR029.str029_54_smooth_exponential_normalization_holder_algebra`: one
  conjunction.  (1) `NormedSpace.exp` is `C^∞` on the Hölder algebra.  (2) Its `n`th derivative
  is `exp w * v₁ ⋯ vₙ`.  (3) That derivative has norm at most `e^R ∏ ‖vᵢ‖` when `‖w‖ ≤ R`.
  (4) The partition function `Z(h,u) = ∫ e^{h cos 3t + u} dm` is positive and equals the
  normalised Haar mean `meanT_STR02901` of the pointwise exponential.  (5) `1/Z`, `log Z` and
  `ρ = e^{h cos 3t + u}/Z` are `C^∞`.  (6) `ρ` has the pointwise value `rhoT_STR02901`.
  (7) For every derivative order `n` and every `R` there is one constant bounding the `n`th
  derivative norms of `Z`, `1/Z`, `log Z` and `ρ` on the region
  `‖h cos 3t + u‖ ≤ R` and `Z ≥ 1/2`.

Auxiliary declarations carry the suffix `_STR02954`.  The main ones are
`instNormedCommRing_STR02954`, `instNormedAlgebra_STR02954` and `instNormOneClass_STR02954`
(the algebra structure), `exp_val_STR02954` (identification with the pointwise exponential),
`iteratedFDeriv_exp_STR02954` (derivative formula), `norm_exp_le_STR02954`, `Z_STR02954`,
`rho_STR02954`, and the per-order bound lemmas `invZ_bound_each_STR02954`,
`logZ_bound_each_STR02954` and `rho_bound_each_STR02954`.

## R5 notes

* The carrier is the concrete space `PeriodicHolder_STR02968` with `α = 1/2`, as fixed in the node
  preamble.  Its ring structure is built here from `c0_mul_STR02953` (submultiplicativity), so
  the norm is the `C^{0,1/2}` norm and `‖1‖ = 1`.  The instances are given explicit names with the
  suffix `_STR02954` to avoid collisions with other units.
* Smoothness means `ContDiff ℝ ∞` on the product space `ℝ × PeriodicHolder_STR02968`, where the
  mean-zero constraint on `u` is not imposed (the statement does not require it).
* "Near zero" is read more strongly: `Z > 0` holds at every point of the parameter space, since
  the integrand is a positive continuous function.  Consequently `1/Z`, `log Z` and `ρ` are smooth
  globally, not only near zero.
* The mean is the normalised Haar mean `meanT_STR02901` (that is, `∫ · dm` with
  `m(dt) = dt/(2π)`); it is packaged as a bounded linear functional of norm at most one.
* The uniform bounds are stated as `∃ C` depending on `(n, R)` and valid on the set
  `{‖h cos 3t + u‖ ≤ R, Z ≥ 1/2}`; the derivative norms are those of the globally smooth
  functions on the whole parameter space, evaluated at points of that set.  This reads
  "smaller bounded neighborhoods" as that set; no openness or boundedness in `(h, u)` is needed.
* The proof sketch gives the explicit constants `2 n! A^n` with `A = 1 + 4 e^R`.  The constants
  here come instead from the Faà di Bruno estimate (`norm_iteratedFDeriv_comp_le'`), the Leibniz
  estimate (`norm_iteratedFDeriv_smul_le`) and the closed forms of the scalar derivatives of
  `z ↦ 1/z` and `log` on `z ≥ 1/2`; they depend only on `(n, R)` and on the fixed norms of the
  mean functional and of the linear parametrisation.  Only the existence of a bound is
  claimed, which is what the statement requires.
* The upper bound `Z ≤ max 1 (‖mean‖ e^R)` is used to control `log Z`.
* `NormedSpace.exp` is used without an explicit field argument, with the real scalar field fixed
  by the `NormedAlgebra ℝ` instance.
-/

open Filter Topology Function NormedSpace
open scoped ContDiff

namespace DGPS.Frontier.STR029

theorem isC0_val_STR02954 (f : PeriodicHolder_STR02968) :
    IsC0Alpha_STR02953 (1 / 2) f.val :=
  ⟨f.isPerHolder.1, f.isPerHolder.2.2⟩

theorem norm_eq_c0Norm_STR02954 (f : PeriodicHolder_STR02968) :
    ‖f‖ = c0Norm_STR02953 (1 / 2) f.val := rfl

theorem mul_mem_STR02954 (f g : PeriodicHolder_STR02968) :
    IsPerHolder_STR02968 (1 / 2) (f.val * g.val) := by
  obtain ⟨h1, -⟩ := c0_mul_STR02953 half_pos_STR02968 (isC0_val_STR02954 f) (isC0_val_STR02954 g)
  exact ⟨h1.1, continuous_of_circHolderBdd_STR02953 half_pos_STR02968 h1.2, h1.2⟩

theorem one_mem_STR02954 : IsPerHolder_STR02968 (1 / 2) (fun _ : ℝ => (1 : ℝ)) :=
  ⟨fun _ => rfl, continuous_const, 0, le_rfl, fun s t => by simp⟩

theorem ext_STR02954 {f g : PeriodicHolder_STR02968} (h : f.val = g.val) : f = g := Subtype.ext h

noncomputable instance instMul_STR02954 : Mul PeriodicHolder_STR02968 :=
  ⟨fun f g => PeriodicHolder_STR02968.mk (f.val * g.val) (mul_mem_STR02954 f g)⟩

noncomputable instance instOne_STR02954 : One PeriodicHolder_STR02968 :=
  ⟨PeriodicHolder_STR02968.mk (fun _ => 1) one_mem_STR02954⟩

theorem val_mul_STR02954 (f g : PeriodicHolder_STR02968) : (f * g).val = f.val * g.val := rfl

theorem val_one_STR02954 : (1 : PeriodicHolder_STR02968).val = fun _ => 1 := rfl

theorem norm_mul_le_STR02954 (f g : PeriodicHolder_STR02968) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ :=
  (c0_mul_STR02953 half_pos_STR02968 (isC0_val_STR02954 f) (isC0_val_STR02954 g)).2

noncomputable instance instNormedCommRing_STR02954 : NormedCommRing PeriodicHolder_STR02968 where
  __ := (inferInstance : NormedAddCommGroup PeriodicHolder_STR02968)
  mul := (· * ·)
  one := 1
  left_distrib a b c := ext_STR02954 (by
    rw [val_mul_STR02954, PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_add,
      val_mul_STR02954, val_mul_STR02954]; exact mul_add _ _ _)
  right_distrib a b c := ext_STR02954 (by
    rw [val_mul_STR02954, PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_add,
      val_mul_STR02954, val_mul_STR02954]; exact add_mul _ _ _)
  zero_mul a := ext_STR02954 (by
    rw [val_mul_STR02954]; exact zero_mul _)
  mul_zero a := ext_STR02954 (by
    rw [val_mul_STR02954]; exact mul_zero _)
  mul_assoc a b c := ext_STR02954 (by
    rw [val_mul_STR02954, val_mul_STR02954, val_mul_STR02954, val_mul_STR02954]; exact mul_assoc _ _ _)
  one_mul a := ext_STR02954 (by
    rw [val_mul_STR02954, val_one_STR02954]; funext t; simp)
  mul_one a := ext_STR02954 (by
    rw [val_mul_STR02954, val_one_STR02954]; funext t; simp)
  mul_comm a b := ext_STR02954 (by
    rw [val_mul_STR02954, val_mul_STR02954]; exact mul_comm _ _)
  norm_mul_le := norm_mul_le_STR02954


noncomputable instance instNormedAlgebra_STR02954 : NormedAlgebra ℝ PeriodicHolder_STR02968 :=
  { Algebra.ofModule
      (fun r x y => ext_STR02954 (by
        rw [PeriodicHolder_STR02968.val_smul, val_mul_STR02954, val_mul_STR02954,
          PeriodicHolder_STR02968.val_smul]; exact smul_mul_assoc _ _ _))
      (fun r x y => ext_STR02954 (by
        rw [PeriodicHolder_STR02968.val_smul, val_mul_STR02954, val_mul_STR02954,
          PeriodicHolder_STR02968.val_smul]; exact mul_smul_comm _ _ _)) with
    norm_smul_le := fun r x => (norm_smul r x).le }

theorem norm_one_STR02954 : ‖(1 : PeriodicHolder_STR02968)‖ = 1 := by
  have h1 := (c0_const_STR02953 (α := 1 / 2) half_pos_STR02968).2
  have h2 : (1 : ℝ) ≤ ‖(1 : PeriodicHolder_STR02968)‖ := by
    have := (PeriodicHolder_STR02968.isPerHolder (1 : PeriodicHolder_STR02968)).abs_le_supNorm 0
    have h3 : (1 : PeriodicHolder_STR02968).val 0 = 1 := rfl
    rw [h3, abs_one] at this
    rw [PeriodicHolder_STR02968.norm_def]
    linarith [holderSemi_nonneg_STR02968 (1 / 2) (1 : PeriodicHolder_STR02968).val]
  exact le_antisymm h1 h2

instance instNormOneClass_STR02954 : NormOneClass PeriodicHolder_STR02968 := ⟨norm_one_STR02954⟩

/-- Evaluation at a point is a ring homomorphism. -/
def evalHom_STR02954 (t : ℝ) : PeriodicHolder_STR02968 →+* ℝ where
  toFun f := f.val t
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evalHom_continuous_STR02954 (t : ℝ) : Continuous (evalHom_STR02954 t) := by
  refine AddMonoidHomClass.continuous_of_bound (evalHom_STR02954 t) 1 fun f => ?_
  rw [one_mul, Real.norm_eq_abs, PeriodicHolder_STR02968.norm_def]
  have := f.isPerHolder.abs_le_supNorm t
  have h2 := holderSemi_nonneg_STR02968 (1 / 2) f.val
  change |f.val t| ≤ _
  linarith

theorem exp_val_STR02954 (w : PeriodicHolder_STR02968) (t : ℝ) :
    (exp w).val t = Real.exp (w.val t) := by
  have := map_exp_of_mem_ball (𝕂 := ℝ) (evalHom_STR02954 t) (evalHom_continuous_STR02954 t) w
    ((expSeries_radius_eq_top ℝ PeriodicHolder_STR02968).symm ▸ edist_lt_top _ _)
  rw [← Real.exp_eq_exp_ℝ] at this
  exact this

theorem exp_smooth_STR02954 : ContDiff ℝ ∞ (exp : PeriodicHolder_STR02968 → PeriodicHolder_STR02968) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (exp_analytic x).contDiffAt


theorem fderiv_exp_STR02954 (x : PeriodicHolder_STR02968) :
    fderiv ℝ (exp : PeriodicHolder_STR02968 → PeriodicHolder_STR02968) x
      = ContinuousLinearMap.mul ℝ PeriodicHolder_STR02968 (exp x) := by
  rw [hasFDerivAt_exp.fderiv]
  ext v
  simp

theorem iteratedFDeriv_exp_STR02954 (n : ℕ) (w : PeriodicHolder_STR02968)
    (v : Fin n → PeriodicHolder_STR02968) :
    iteratedFDeriv ℝ n (exp : PeriodicHolder_STR02968 → PeriodicHolder_STR02968) w v
      = exp w * ∏ i, v i := by
  induction n with
  | zero => simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [iteratedFDeriv_succ_apply_right]
    have h1 : (fun y => fderiv ℝ (exp : PeriodicHolder_STR02968 → PeriodicHolder_STR02968) y)
        = (ContinuousLinearMap.mul ℝ PeriodicHolder_STR02968) ∘ exp := by
      funext y; exact fderiv_exp_STR02954 y
    rw [h1, (ContinuousLinearMap.mul ℝ PeriodicHolder_STR02968).iteratedFDeriv_comp_left
      (exp_smooth_STR02954.contDiffAt) (by exact_mod_cast le_top)]
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousLinearMap.mul_apply']
    rw [ih, Fin.prod_univ_castSucc]
    rw [mul_assoc]; rfl


theorem norm_exp_le_STR02954 (w : PeriodicHolder_STR02968) : ‖exp w‖ ≤ Real.exp ‖w‖ := by
  have h1 := exp_series_hasSum_exp' (𝕂 := ℝ) w
  have h2 := exp_series_hasSum_exp' (𝕂 := ℝ) ‖w‖
  rw [← Real.exp_eq_exp_ℝ] at h2
  refine h1.norm_le_of_bounded h2 fun n => ?_
  rw [norm_smul, smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr
  exact norm_pow_le w n

theorem norm_iteratedFDeriv_exp_le_STR02954 (n : ℕ) (w : PeriodicHolder_STR02968) {R : ℝ}
    (hw : ‖w‖ ≤ R) (v : Fin n → PeriodicHolder_STR02968) :
    ‖iteratedFDeriv ℝ n (exp : PeriodicHolder_STR02968 → PeriodicHolder_STR02968) w v‖
      ≤ Real.exp R * ∏ i, ‖v i‖ := by
  rw [iteratedFDeriv_exp_STR02954]
  calc ‖exp w * ∏ i, v i‖ ≤ ‖exp w‖ * ‖∏ i, v i‖ := norm_mul_le _ _
    _ ≤ Real.exp R * ∏ i, ‖v i‖ := by
      gcongr
      · exact (norm_exp_le_STR02954 w).trans (Real.exp_le_exp.2 hw)
      · exact Finset.norm_prod_le Finset.univ v

theorem norm_iteratedFDeriv_exp_le'_STR02954 (n : ℕ) (w : PeriodicHolder_STR02968) {R : ℝ}
    (hw : ‖w‖ ≤ R) :
    ‖iteratedFDeriv ℝ n (exp : PeriodicHolder_STR02968 → PeriodicHolder_STR02968) w‖
      ≤ Real.exp R := by
  refine ContinuousMultilinearMap.opNorm_le_bound (Real.exp_pos R).le fun v => ?_
  exact norm_iteratedFDeriv_exp_le_STR02954 n w hw v

/-- The function `t ↦ cos (3 t)` as an element of the Hölder algebra. -/
theorem cos3_mem_STR02954 : IsPerHolder_STR02968 (1 / 2) (fun t : ℝ => Real.cos (3 * t)) := by
  have hper : Function.Periodic (fun t : ℝ => Real.cos (3 * t)) (2 * Real.pi) := fun t => by
    show Real.cos (3 * (t + 2 * Real.pi)) = Real.cos (3 * t)
    rw [mul_add, show 3 * (2 * Real.pi) = (3 : ℕ) * (2 * Real.pi) by push_cast; ring]
    exact Real.cos_add_nat_mul_two_pi _ 3
  have hd : Differentiable ℝ (fun t : ℝ => Real.cos (3 * t)) := by fun_prop
  have hb : DGPS.Analysis.PeriodicHolder.Bdd (deriv (fun t : ℝ => Real.cos (3 * t))) := ⟨3, fun x => by
    have : deriv (fun t : ℝ => Real.cos (3 * t)) x = -(Real.sin (3 * x) * 3) := by
      rw [deriv_cos (by fun_prop)]; simp
    rw [this, abs_neg, abs_mul]
    have := Real.abs_sin_le_one (3 * x)
    norm_num
    linarith⟩
  obtain ⟨h1, -⟩ := c0_of_deriv_STR02953 (α := 1 / 2) half_pos_STR02968 (by norm_num) hper hd hb
  exact ⟨h1.1, continuous_of_circHolderBdd_STR02953 half_pos_STR02968 h1.2, h1.2⟩


/-- The Hölder-algebra element `t ↦ cos (3 t)`. -/
noncomputable def c3_STR02954 : PeriodicHolder_STR02968 :=
  PeriodicHolder_STR02968.mk (fun t => Real.cos (3 * t)) cos3_mem_STR02954

/-- The normalised Haar mean as a bounded linear functional on the Hölder algebra. -/
noncomputable def meanCLM_STR02954 : PeriodicHolder_STR02968 →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => meanT_STR02901 f.val
      map_add' := fun f g => meanT_add_STR02953 f.isPerHolder.2.1 g.isPerHolder.2.1
      map_smul' := fun c f => meanT_smul_STR02953 c f.val } 1 (fun f => by
        show |meanT_STR02901 f.val| ≤ 1 * ‖f‖
        have h1 := abs_meanT_le_STR02953 (M := supNorm_STR02968 f.val)
          (fun t => f.isPerHolder.abs_le_supNorm t)
        rw [PeriodicHolder_STR02968.norm_def, one_mul]
        linarith [holderSemi_nonneg_STR02968 (1 / 2) f.val])

theorem meanCLM_apply_STR02954 (f : PeriodicHolder_STR02968) :
    meanCLM_STR02954 f = meanT_STR02901 f.val := rfl

/-- The linear parametrisation `(h, u) ↦ h cos 3t + u`. -/
noncomputable def lin_STR02954 : ℝ × PeriodicHolder_STR02968 →L[ℝ] PeriodicHolder_STR02968 :=
  (ContinuousLinearMap.fst ℝ ℝ PeriodicHolder_STR02968).smulRight c3_STR02954
    + ContinuousLinearMap.snd ℝ ℝ PeriodicHolder_STR02968

theorem lin_apply_STR02954 (x : ℝ × PeriodicHolder_STR02968) :
    lin_STR02954 x = x.1 • c3_STR02954 + x.2 := rfl

/-- The partition function `Z(h,u) = ∫ e^{h cos 3t + u} dm`. -/
noncomputable def Z_STR02954 (x : ℝ × PeriodicHolder_STR02968) : ℝ :=
  meanCLM_STR02954 (exp (x.1 • c3_STR02954 + x.2))

theorem Z_eq_meanT_STR02954 (x : ℝ × PeriodicHolder_STR02968) :
    Z_STR02954 x = meanT_STR02901 (fun s => Real.exp (x.1 * Real.cos (3 * s) + x.2.val s)) := by
  unfold Z_STR02954
  rw [meanCLM_apply_STR02954]
  congr 1
  funext s
  rw [exp_val_STR02954]
  rfl

theorem Z_pos_STR02954 (x : ℝ × PeriodicHolder_STR02968) : 0 < Z_STR02954 x := by
  rw [Z_eq_meanT_STR02954]
  refine meanT_pos_STR02901 ?_ fun s => Real.exp_pos _
  have h := (exp (x.1 • c3_STR02954 + x.2)).isPerHolder.2.1
  have : (fun s => Real.exp (x.1 * Real.cos (3 * s) + x.2.val s))
      = (exp (x.1 • c3_STR02954 + x.2)).val := by
    funext s; rw [exp_val_STR02954]; rfl
  rw [this]; exact h

/-- The normalised density `ρ(h,u) = e^{h cos 3t + u} / Z(h,u)` in the Hölder algebra. -/
noncomputable def rho_STR02954 (x : ℝ × PeriodicHolder_STR02968) : PeriodicHolder_STR02968 :=
  (Z_STR02954 x)⁻¹ • exp (x.1 • c3_STR02954 + x.2)

theorem rho_val_STR02954 (x : ℝ × PeriodicHolder_STR02968) (t : ℝ) :
    (rho_STR02954 x).val t = rhoT_STR02901 x.1 x.2.val t := by
  unfold rho_STR02954 rhoT_STR02901
  rw [PeriodicHolder_STR02968.val_smul, Pi.smul_apply, smul_eq_mul, exp_val_STR02954,
    Z_eq_meanT_STR02954, inv_mul_eq_div]
  rfl


theorem F_smooth_STR02954 :
    ContDiff ℝ ∞ (fun x : ℝ × PeriodicHolder_STR02968 => exp (x.1 • c3_STR02954 + x.2)) :=
  exp_smooth_STR02954.comp lin_STR02954.contDiff

theorem Z_smooth_STR02954 : ContDiff ℝ ∞ Z_STR02954 :=
  meanCLM_STR02954.contDiff.comp F_smooth_STR02954

theorem invZ_smooth_STR02954 : ContDiff ℝ ∞ (fun x => (Z_STR02954 x)⁻¹) :=
  Z_smooth_STR02954.inv fun x => (Z_pos_STR02954 x).ne'

theorem logZ_smooth_STR02954 : ContDiff ℝ ∞ (fun x => Real.log (Z_STR02954 x)) :=
  Z_smooth_STR02954.log fun x => (Z_pos_STR02954 x).ne'

theorem rho_smooth_STR02954 : ContDiff ℝ ∞ rho_STR02954 :=
  invZ_smooth_STR02954.smul F_smooth_STR02954

theorem exists_bound_upto_STR02954 {α : Type*} (S : Set α) (f : ℕ → α → ℝ)
    (h : ∀ i, ∃ C, ∀ x ∈ S, f i x ≤ C) (n : ℕ) : ∃ C, ∀ x ∈ S, ∀ i ≤ n, f i x ≤ C := by
  induction n with
  | zero =>
    obtain ⟨C, hC⟩ := h 0
    exact ⟨C, fun x hx i hi => by obtain rfl := Nat.le_zero.1 hi; exact hC x hx⟩
  | succ n ih =>
    obtain ⟨C1, h1⟩ := ih
    obtain ⟨C2, h2⟩ := h (n + 1)
    refine ⟨max C1 C2, fun x hx i hi => ?_⟩
    rcases Nat.lt_or_ge i (n + 1) with hlt | hge
    · exact (h1 x hx i (Nat.lt_succ_iff.1 hlt)).trans (le_max_left _ _)
    · obtain rfl : i = n + 1 := le_antisymm hi hge
      exact (h2 x hx).trans (le_max_right _ _)

theorem norm_iteratedFDeriv_F_le_STR02954 (n : ℕ) (x : ℝ × PeriodicHolder_STR02968) {R : ℝ}
    (hx : ‖x.1 • c3_STR02954 + x.2‖ ≤ R) :
    ‖iteratedFDeriv ℝ n (fun x : ℝ × PeriodicHolder_STR02968 => exp (x.1 • c3_STR02954 + x.2)) x‖
      ≤ Real.exp R * ‖lin_STR02954‖ ^ n := by
  have h1 : (fun x : ℝ × PeriodicHolder_STR02968 => exp (x.1 • c3_STR02954 + x.2))
      = exp ∘ lin_STR02954 := rfl
  rw [h1, lin_STR02954.iteratedFDeriv_comp_right exp_smooth_STR02954 x (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  gcongr
  exact norm_iteratedFDeriv_exp_le'_STR02954 n _ hx

theorem norm_iteratedFDeriv_Z_le_STR02954 (n : ℕ) (x : ℝ × PeriodicHolder_STR02968) {R : ℝ}
    (hx : ‖x.1 • c3_STR02954 + x.2‖ ≤ R) :
    ‖iteratedFDeriv ℝ n Z_STR02954 x‖
      ≤ ‖meanCLM_STR02954‖ * (Real.exp R * ‖lin_STR02954‖ ^ n) := by
  have h1 : Z_STR02954 = meanCLM_STR02954 ∘
      (fun x : ℝ × PeriodicHolder_STR02968 => exp (x.1 • c3_STR02954 + x.2)) := rfl
  rw [h1]
  refine (meanCLM_STR02954.norm_iteratedFDeriv_comp_left
    (F_smooth_STR02954.contDiffAt) (by exact_mod_cast le_top)).trans ?_
  gcongr
  exact norm_iteratedFDeriv_F_le_STR02954 n x hx


theorem norm_iteratedDeriv_inv_le_STR02954 (i : ℕ) {z : ℝ} (hz : 1 / 2 ≤ z) :
    ‖iteratedDeriv i (fun z : ℝ => z⁻¹) z‖ ≤ (i.factorial : ℝ) * 2 ^ (i + 1) := by
  rw [iteratedDeriv_eq_iterate]
  change ‖deriv^[i] Inv.inv z‖ ≤ _
  rw [iter_deriv_inv]
  have hz0 : 0 < z := lt_of_lt_of_le (by norm_num) hz
  have e : z ^ (-1 - (i : ℤ)) = (z ^ (i + 1))⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
  rw [e, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_natCast, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (pow_pos hz0 _))]
  gcongr
  have h2 : ((1 : ℝ) / 2) ^ (i + 1) ≤ z ^ (i + 1) := by gcongr
  calc (z ^ (i + 1))⁻¹ ≤ (((1 : ℝ) / 2) ^ (i + 1))⁻¹ := inv_anti₀ (by positivity) h2
    _ = 2 ^ (i + 1) := by rw [one_div, inv_pow, inv_inv]

theorem norm_iteratedFDerivWithin_inv_le_STR02954 (i : ℕ) {z : ℝ} (hz : 1 / 2 ≤ z) :
    ‖iteratedFDerivWithin ℝ i (fun z : ℝ => z⁻¹) (Set.Ioi 0) z‖
      ≤ (i.factorial : ℝ) * 2 ^ (i + 1) := by
  have hz0 : z ∈ Set.Ioi (0 : ℝ) := lt_of_lt_of_le (by norm_num) hz
  rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi hz0, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact norm_iteratedDeriv_inv_le_STR02954 i hz

theorem norm_iteratedFDerivWithin_log_le_STR02954 (i : ℕ) {z K : ℝ} (hz : 1 / 2 ≤ z) (hzK : z ≤ K)
    (hK : 1 ≤ K) :
    ‖iteratedFDerivWithin ℝ i Real.log (Set.Ioi 0) z‖
      ≤ Real.log 2 + Real.log K + (i.factorial : ℝ) * 2 ^ (i + 1) := by
  have hz0 : z ∈ Set.Ioi (0 : ℝ) := lt_of_lt_of_le (by norm_num) hz
  rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi hz0, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hf : 0 ≤ (i.factorial : ℝ) * 2 ^ (i + 1) := by positivity
  cases i with
  | zero =>
    rw [iteratedDeriv_zero, Real.norm_eq_abs]
    have h1 : Real.log z ≤ Real.log K := Real.log_le_log (by linarith) hzK
    have h2 : Real.log (1 / 2) ≤ Real.log z := Real.log_le_log (by norm_num) hz
    rw [one_div, Real.log_inv] at h2
    rw [abs_le]
    constructor <;> simp <;> linarith
  | succ k =>
    rw [iteratedDeriv_succ', Real.deriv_log']
    have := norm_iteratedDeriv_inv_le_STR02954 k hz
    have h3 : (k.factorial : ℝ) * 2 ^ (k + 1) ≤ ((k + 1).factorial : ℝ) * 2 ^ (k + 1 + 1) := by
      have e : (((k + 1).factorial : ℕ) : ℝ) * 2 ^ (k + 1 + 1)
          = 2 * ((k : ℝ) + 1) * ((k.factorial : ℝ) * 2 ^ (k + 1)) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have h0 : (0 : ℝ) ≤ k.factorial * 2 ^ (k + 1) := by positivity
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      rw [e]; nlinarith
    exact (this.trans h3).trans (by linarith)


/-- The constant bounding `Z` on the region `‖h cos 3t + u‖ ≤ R`. -/
noncomputable def K_STR02954 (R : ℝ) : ℝ := max 1 (‖meanCLM_STR02954‖ * Real.exp R)

theorem one_le_K_STR02954 (R : ℝ) : 1 ≤ K_STR02954 R := le_max_left _ _

theorem Z_le_K_STR02954 (x : ℝ × PeriodicHolder_STR02968) {R : ℝ}
    (hx : ‖x.1 • c3_STR02954 + x.2‖ ≤ R) : Z_STR02954 x ≤ K_STR02954 R := by
  refine le_trans ?_ (le_max_right _ _)
  calc Z_STR02954 x ≤ ‖Z_STR02954 x‖ := le_abs_self _
    _ ≤ ‖meanCLM_STR02954‖ * ‖exp (x.1 • c3_STR02954 + x.2)‖ := meanCLM_STR02954.le_opNorm _
    _ ≤ ‖meanCLM_STR02954‖ * Real.exp R := by
      gcongr
      exact (norm_exp_le_STR02954 _).trans (Real.exp_le_exp.2 hx)

theorem norm_iteratedFDeriv_Z_le_pow_STR02954 (i : ℕ) (hi : 1 ≤ i)
    (x : ℝ × PeriodicHolder_STR02968) {R : ℝ} (hx : ‖x.1 • c3_STR02954 + x.2‖ ≤ R) :
    ‖iteratedFDeriv ℝ i Z_STR02954 x‖ ≤ (K_STR02954 R * ‖lin_STR02954‖) ^ i := by
  refine (norm_iteratedFDeriv_Z_le_STR02954 i x hx).trans ?_
  rw [mul_pow]
  have hK := one_le_K_STR02954 R
  have h1 : ‖meanCLM_STR02954‖ * Real.exp R ≤ K_STR02954 R := le_max_right _ _
  have h2 : K_STR02954 R ≤ K_STR02954 R ^ i := le_self_pow₀ hK (by omega)
  have h3 : 0 ≤ ‖lin_STR02954‖ ^ i := by positivity
  calc ‖meanCLM_STR02954‖ * (Real.exp R * ‖lin_STR02954‖ ^ i)
      = (‖meanCLM_STR02954‖ * Real.exp R) * ‖lin_STR02954‖ ^ i := by ring
    _ ≤ K_STR02954 R ^ i * ‖lin_STR02954‖ ^ i := by gcongr; exact h1.trans h2

theorem norm_iteratedFDeriv_comp_Ioi_STR02954 {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Set.Ioi 0)) (n : ℕ) (x : ℝ × PeriodicHolder_STR02968) {C D : ℝ}
    (hC : ∀ i ≤ n, ‖iteratedFDerivWithin ℝ i g (Set.Ioi 0) (Z_STR02954 x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i Z_STR02954 x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ Z_STR02954) x‖ ≤ n.factorial * C * D ^ n :=
  norm_iteratedFDeriv_comp_le' (t := Set.Ioi 0)
    (by rintro _ ⟨y, rfl⟩; exact Z_pos_STR02954 y) isOpen_Ioi.uniqueDiffOn hg Z_smooth_STR02954
    (by exact_mod_cast le_top) x hC hD

theorem invZ_bound_each_STR02954 (n : ℕ) (R : ℝ) :
    ∃ C : ℝ, ∀ x : ℝ × PeriodicHolder_STR02968, ‖x.1 • c3_STR02954 + x.2‖ ≤ R →
      1 / 2 ≤ Z_STR02954 x → ‖iteratedFDeriv ℝ n (fun x => (Z_STR02954 x)⁻¹) x‖ ≤ C := by
  refine ⟨n.factorial * (n.factorial * 2 ^ (n + 1)) * (K_STR02954 R * ‖lin_STR02954‖) ^ n,
    fun x hx hz => ?_⟩
  have := norm_iteratedFDeriv_comp_Ioi_STR02954
    (g := fun z : ℝ => z⁻¹) (contDiffOn_id.inv fun z hz => ne_of_gt hz) n x
    (C := n.factorial * 2 ^ (n + 1)) (D := K_STR02954 R * ‖lin_STR02954‖)
    (fun i hi => (norm_iteratedFDerivWithin_inv_le_STR02954 i hz).trans (by
      gcongr
      · norm_num)) (fun i hi _ => norm_iteratedFDeriv_Z_le_pow_STR02954 i hi x hx)
  exact this

theorem logZ_bound_each_STR02954 (n : ℕ) (R : ℝ) :
    ∃ C : ℝ, ∀ x : ℝ × PeriodicHolder_STR02968, ‖x.1 • c3_STR02954 + x.2‖ ≤ R →
      1 / 2 ≤ Z_STR02954 x →
        ‖iteratedFDeriv ℝ n (fun x => Real.log (Z_STR02954 x)) x‖ ≤ C := by
  refine ⟨n.factorial * (Real.log 2 + Real.log (K_STR02954 R) + n.factorial * 2 ^ (n + 1))
    * (K_STR02954 R * ‖lin_STR02954‖) ^ n, fun x hx hz => ?_⟩
  have hlog : ContDiffOn ℝ ∞ Real.log (Set.Ioi 0) :=
    Real.contDiffOn_log.mono fun z hz => hz.ne'
  have := norm_iteratedFDeriv_comp_Ioi_STR02954 (g := Real.log) hlog n x
    (C := Real.log 2 + Real.log (K_STR02954 R) + n.factorial * 2 ^ (n + 1))
    (D := K_STR02954 R * ‖lin_STR02954‖)
    (fun i hi => (norm_iteratedFDerivWithin_log_le_STR02954 i hz (Z_le_K_STR02954 x hx)
      (one_le_K_STR02954 R)).trans (by
        gcongr
        · norm_num))
    (fun i hi _ => norm_iteratedFDeriv_Z_le_pow_STR02954 i hi x hx)
  exact this

theorem rho_bound_each_STR02954 (n : ℕ) (R : ℝ) :
    ∃ C : ℝ, ∀ x : ℝ × PeriodicHolder_STR02968, ‖x.1 • c3_STR02954 + x.2‖ ≤ R →
      1 / 2 ≤ Z_STR02954 x → ‖iteratedFDeriv ℝ n rho_STR02954 x‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_upto_STR02954
    {x : ℝ × PeriodicHolder_STR02968 | ‖x.1 • c3_STR02954 + x.2‖ ≤ R ∧ 1 / 2 ≤ Z_STR02954 x}
    (fun i x => ‖iteratedFDeriv ℝ i (fun x => (Z_STR02954 x)⁻¹) x‖)
    (fun i => by
      obtain ⟨C, hC⟩ := invZ_bound_each_STR02954 i R
      exact ⟨C, fun x hx => hC x hx.1 hx.2⟩) n
  refine ⟨∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * max C 0 * (Real.exp R * ‖lin_STR02954‖ ^ (n - i)), fun x hx hz => ?_⟩
  have h1 := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (f := fun x => (Z_STR02954 x)⁻¹)
    (g := fun x : ℝ × PeriodicHolder_STR02968 => exp (x.1 • c3_STR02954 + x.2))
    invZ_smooth_STR02954 F_smooth_STR02954 x (n := n) (by exact_mod_cast le_top)
  refine h1.trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have e1 : ‖iteratedFDeriv ℝ i (fun x => (Z_STR02954 x)⁻¹) x‖ ≤ max C 0 :=
    (hC x ⟨hx, hz⟩ i hi').trans (le_max_left _ _)
  have e2 := norm_iteratedFDeriv_F_le_STR02954 (n - i) x hx
  gcongr

theorem str029_54_smooth_exponential_normalization_holder_algebra :
    ContDiff ℝ ∞ (exp : PeriodicHolder_STR02968 → PeriodicHolder_STR02968) ∧
    (∀ (n : ℕ) (w : PeriodicHolder_STR02968) (v : Fin n → PeriodicHolder_STR02968),
      iteratedFDeriv ℝ n (exp : PeriodicHolder_STR02968 → PeriodicHolder_STR02968) w v
        = exp w * ∏ i, v i) ∧
    (∀ (n : ℕ) (w : PeriodicHolder_STR02968) (R : ℝ), ‖w‖ ≤ R →
      ∀ v : Fin n → PeriodicHolder_STR02968,
        ‖iteratedFDeriv ℝ n (exp : PeriodicHolder_STR02968 → PeriodicHolder_STR02968) w v‖
          ≤ Real.exp R * ∏ i, ‖v i‖) ∧
    (∀ x : ℝ × PeriodicHolder_STR02968, 0 < Z_STR02954 x ∧
      Z_STR02954 x
        = meanT_STR02901 (fun s => Real.exp (x.1 * Real.cos (3 * s) + x.2.val s))) ∧
    ContDiff ℝ ∞ (fun x : ℝ × PeriodicHolder_STR02968 => (Z_STR02954 x)⁻¹) ∧
    ContDiff ℝ ∞ (fun x : ℝ × PeriodicHolder_STR02968 => Real.log (Z_STR02954 x)) ∧
    ContDiff ℝ ∞ rho_STR02954 ∧
    (∀ (x : ℝ × PeriodicHolder_STR02968) (t : ℝ),
      (rho_STR02954 x).val t = rhoT_STR02901 x.1 x.2.val t) ∧
    (∀ (n : ℕ) (R : ℝ), ∃ C : ℝ, ∀ x : ℝ × PeriodicHolder_STR02968,
      ‖x.1 • c3_STR02954 + x.2‖ ≤ R → 1 / 2 ≤ Z_STR02954 x →
        ‖iteratedFDeriv ℝ n Z_STR02954 x‖ ≤ C ∧
        ‖iteratedFDeriv ℝ n (fun x => (Z_STR02954 x)⁻¹) x‖ ≤ C ∧
        ‖iteratedFDeriv ℝ n (fun x => Real.log (Z_STR02954 x)) x‖ ≤ C ∧
        ‖iteratedFDeriv ℝ n rho_STR02954 x‖ ≤ C) := by
  refine ⟨exp_smooth_STR02954, iteratedFDeriv_exp_STR02954, ?_, fun x => ⟨Z_pos_STR02954 x,
    Z_eq_meanT_STR02954 x⟩, invZ_smooth_STR02954, logZ_smooth_STR02954, rho_smooth_STR02954,
    rho_val_STR02954, fun n R => ?_⟩
  · intro n w R hw v
    exact norm_iteratedFDeriv_exp_le_STR02954 n w hw v
  · obtain ⟨C1, h1⟩ := invZ_bound_each_STR02954 n R
    obtain ⟨C2, h2⟩ := logZ_bound_each_STR02954 n R
    obtain ⟨C3, h3⟩ := rho_bound_each_STR02954 n R
    refine ⟨max (max C1 C2) (max C3 (‖meanCLM_STR02954‖ * (Real.exp R * ‖lin_STR02954‖ ^ n))),
      fun x hx hz => ⟨?_, ?_, ?_, ?_⟩⟩
    · exact (norm_iteratedFDeriv_Z_le_STR02954 n x hx).trans
        ((le_max_right _ _).trans (le_max_right _ _))
    · exact (h1 x hx hz).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (h2 x hx hz).trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact (h3 x hx hz).trans ((le_max_left _ _).trans (le_max_right _ _))

end DGPS.Frontier.STR029
