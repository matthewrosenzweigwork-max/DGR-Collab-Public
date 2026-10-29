import DGPS.Frontier.STR029.T12
import DGPS.Frontier.STR029.T69

/-!
# STR029.55: Assemble smooth range calculus and its derivative

Task id: STR029.55 (node STR029, frontier unit).
Title: Assemble smooth range calculus and its derivative.

On the concrete Banach carriers `PeriodicHolder_STR02968` (`C^{0,1/2}`), `PeriodicC2_STR02969`
(`C^{2,1/2}`) and the closed subspaces `E_STR02969 ⊂ C^{2,1/2}`, `Y_STR02969 ⊂ C^{0,1/2}` (mean
zero, orthogonal to `cos` and `sin`), the full gradient `(h, γ, u) ↦ G(h, γ, u)` with values in
`C^{0,1/2}` and the concrete range map `R = P G` are smooth, `R 0 = 0`, and
`D_w R(0) w = -2 (w'' + w)` for `w ∈ E`. All iterated derivatives of each finite order are bounded
on a small ball around zero.

## Provides

* `DGPS.Frontier.STR029.str029_55_assemble_smooth_range_calculus_derivative`: the conjunction of
  smoothness of `Gmap_STR02955`, `GmapE_STR02955`, `Rmap_STR02955`, the pointwise formulas, the
  value `R 0 = 0`, the derivative formula at zero, and the local bounds on `iteratedFDeriv` for
  every order.
* `DGPS.Frontier.STR029.Gmap_STR02955`: the gradient map `ℝ × ℝ × C^{2,1/2} → C^{0,1/2}`.
* `DGPS.Frontier.STR029.GmapE_STR02955`: the same map restricted to `ℝ × ℝ × E`.
* `DGPS.Frontier.STR029.Rmap_STR02955`: the range map `P G` on `ℝ × ℝ × E` with values in `Y`.
* `DGPS.Frontier.STR029.PCLM_STR02955` and `DGPS.Frontier.STR029.PY_STR02955`: the projection `P`
  as a bounded operator on `C^{0,1/2}`, and its corestriction to `Y`.
* `DGPS.Frontier.STR029.Gmap_smooth_STR02955`, `GmapE_smooth_STR02955`, `Rmap_smooth_STR02955`:
  smoothness of the three maps.
* `DGPS.Frontier.STR029.Rmap_zero_STR02955`: `R 0 = 0`.
* `DGPS.Frontier.STR029.fderivR_STR02955`: the pointwise form of `D_w R(0) w`.
* `DGPS.Frontier.STR029.bdd_iteratedFDeriv_STR02955`: local boundedness of `iteratedFDeriv` of a
  smooth map at zero.

The proof builds bounded linear maps from the predicate-form operators of STR029.53, uses the
smooth density map of STR029.54 and the explicit gradient of STR029.50, and computes the derivative
at zero along the line `s ↦ G(0, 0, s w)` by the product rule.

## R5 notes

* Smoothness is `ContDiff ℝ ∞` on the whole domain. This implies smoothness on every open
  neighbourhood of zero, so it is stronger than the literal wording.
* The derivative bounds are stated as: for every order `n` there are `r > 0` and `M` with
  `‖iteratedFDeriv ℝ n F x‖ ≤ M` whenever `‖x‖ < r`. The radius `r` is existentially quantified,
  and it is the "sufficiently small norm-bounded neighbourhood" of the statement. The bounds are
  stated for `G` on the full space, for `G` restricted to `E`, and for `R`.
* The three arguments of the product space are `(h, γ, u)` with norm the product (maximum) norm.
  `G` is defined for all `u` in `C^{2,1/2}`. The map `R` takes `u` in `E`, the closed subspace of
  mean zero functions, in agreement with the range projection `P` of STR029.53.
* `R` is valued in `Y`, obtained from `P G` by corestriction. The projection is
  `P f = f - mean f - 2 <f, cos> cos - 2 <f, sin> sin`, as in STR029.53.
* The derivative `D_w R(0) w` is the Fréchet derivative of `R` at zero applied to the vector
  `(0, 0, w)`, i.e. the partial derivative in the `u` direction, with `w ∈ E`. It is given
  pointwise as `-2 (w'' + w)`, where `w''` is `deriv (deriv w.val)`.
* The pointwise formulas relate `G` to `gradG_STR02950` and `R` to `projP_STR02953` applied to
  `gradG_STR02950`. The explicit gradient expression is the one of STR029.12 and STR029.50.
* The carriers are the concrete Banach spaces of STR029.68 and STR029.69, with `α = 1/2`.
* The common optimizer-chart predicate, the weighted carriers, the AbsoluteDensity domain and the
  angular-to-physical normalisation are not assumed anywhere in this unit.
* The Euler range map is not assumed equal to the variational range map. `R = P G` is the
  variational range map, defined here directly from the gradient, and no Euler equation is used.
* No hypothesis is added to the frozen statement.
-/

open Filter Topology Function NormedSpace DGPS.Analysis.PeriodicHolder
open scoped ContDiff

namespace DGPS.Frontier.STR029

theorem mkHolder_STR02955 {g : ℝ → ℝ} (hg : IsC0Alpha_STR02953 (1 / 2) g) :
    IsPerHolder_STR02968 (1 / 2) g :=
  ⟨hg.1, continuous_of_circHolderBdd_STR02953 half_pos_STR02968 hg.2, hg.2⟩

theorem embs_STR02955 :
    IsBoundedLinearOn_STR02953 (IsC2Alpha_STR02901 (1 / 2)) (IsC0Alpha_STR02953 (1 / 2))
      (c2Norm_STR02901 (1 / 2)) (c0Norm_STR02953 (1 / 2)) (fun u => u) ∧
    IsBoundedLinearOn_STR02953 (IsC2Alpha_STR02901 (1 / 2)) (IsC0Alpha_STR02953 (1 / 2))
      (c2Norm_STR02901 (1 / 2)) (c0Norm_STR02953 (1 / 2)) (fun u => deriv u) ∧
    IsBoundedLinearOn_STR02953 (IsC2Alpha_STR02901 (1 / 2)) (IsC0Alpha_STR02953 (1 / 2))
      (c2Norm_STR02901 (1 / 2)) (c0Norm_STR02953 (1 / 2)) (fun u => deriv (deriv u)) := by
  have : HolderExponent (1 / 2 : ℝ) := holderExponent_half_STR02901
  exact str029_53_holder_multiplication_bounded_linear_operations_embeddings

/-- The bounded linear map `C^{2,1/2} → C^{0,1/2}` built from bounded-linear data. -/
noncomputable def embCLM_STR02955 (L : (ℝ → ℝ) → (ℝ → ℝ))
    (hL : IsBoundedLinearOn_STR02953 (IsC2Alpha_STR02901 (1 / 2)) (IsC0Alpha_STR02953 (1 / 2))
      (c2Norm_STR02901 (1 / 2)) (c0Norm_STR02953 (1 / 2)) L) :
    PeriodicC2_STR02969 →L[ℝ] PeriodicHolder_STR02968 :=
  LinearMap.mkContinuous
    { toFun := fun u => PeriodicHolder_STR02968.mk (L u.val) (mkHolder_STR02955 (hL.1 u.val u.isC2))
      map_add' := fun u v => ext_STR02954 (hL.2.1.1 u.val v.val u.isC2 v.isC2)
      map_smul' := fun c u => ext_STR02954 (hL.2.1.2 c u.val u.isC2) }
    hL.2.2.choose (fun u => hL.2.2.choose_spec.2 u.val u.isC2)

theorem embCLM_val_STR02955 (L : (ℝ → ℝ) → (ℝ → ℝ))
    (hL : IsBoundedLinearOn_STR02953 (IsC2Alpha_STR02901 (1 / 2)) (IsC0Alpha_STR02953 (1 / 2))
      (c2Norm_STR02901 (1 / 2)) (c0Norm_STR02953 (1 / 2)) L) (u : PeriodicC2_STR02969) :
    (embCLM_STR02955 L hL u).val = L u.val := rfl

noncomputable def e0_STR02955 : PeriodicC2_STR02969 →L[ℝ] PeriodicHolder_STR02968 :=
  embCLM_STR02955 _ embs_STR02955.1
noncomputable def e1_STR02955 : PeriodicC2_STR02969 →L[ℝ] PeriodicHolder_STR02968 :=
  embCLM_STR02955 _ embs_STR02955.2.1
noncomputable def e2_STR02955 : PeriodicC2_STR02969 →L[ℝ] PeriodicHolder_STR02968 :=
  embCLM_STR02955 _ embs_STR02955.2.2

theorem e0_val_STR02955 (u : PeriodicC2_STR02969) : (e0_STR02955 u).val = u.val := rfl
theorem e1_val_STR02955 (u : PeriodicC2_STR02969) : (e1_STR02955 u).val = deriv u.val := rfl
theorem e2_val_STR02955 (u : PeriodicC2_STR02969) : (e2_STR02955 u).val = deriv (deriv u.val) := rfl


theorem sin3_mem_STR02955 : IsPerHolder_STR02968 (1 / 2) (fun t : ℝ => Real.sin (3 * t)) := by
  have hper : Function.Periodic (fun t : ℝ => Real.sin (3 * t)) (2 * Real.pi) := fun t => by
    show Real.sin (3 * (t + 2 * Real.pi)) = Real.sin (3 * t)
    rw [mul_add, show 3 * (2 * Real.pi) = (3 : ℕ) * (2 * Real.pi) by push_cast; ring]
    exact Real.sin_add_nat_mul_two_pi _ 3
  have hd : Differentiable ℝ (fun t : ℝ => Real.sin (3 * t)) := by fun_prop
  have hb : Bdd (deriv (fun t : ℝ => Real.sin (3 * t))) := ⟨3, fun x => by
    have : deriv (fun t : ℝ => Real.sin (3 * t)) x = Real.cos (3 * x) * 3 := by
      rw [deriv_sin (by fun_prop)]; simp
    rw [this, abs_mul]
    have := Real.abs_cos_le_one (3 * x)
    norm_num
    linarith⟩
  obtain ⟨h1, -⟩ := c0_of_deriv_STR02953 (α := 1 / 2) half_pos_STR02968 (by norm_num) hper hd hb
  exact mkHolder_STR02955 h1

/-- The Hölder-algebra element `t ↦ sin (3 t)`. -/
noncomputable def s3_STR02955 : PeriodicHolder_STR02968 :=
  PeriodicHolder_STR02968.mk (fun t => Real.sin (3 * t)) sin3_mem_STR02955

/-- The density-weighted bracket of the gradient, as a Hölder-algebra element. -/
noncomputable def Gfun_STR02955 (h γ : ℝ) (u : PeriodicC2_STR02969) : PeriodicHolder_STR02968 :=
  rho_STR02954 (h, e0_STR02955 u) *
    ((-2 : ℝ) • e2_STR02955 u + (6 * h) • (s3_STR02955 * e1_STR02955 u) -
      e1_STR02955 u * e1_STR02955 u - (2 * (1 + γ)) • e0_STR02955 u -
      meanCLM_STR02954 (e1_STR02955 u * e1_STR02955 u * rho_STR02954 (h, e0_STR02955 u)) • (1 : PeriodicHolder_STR02968) +
      (2 * (1 + γ) * meanCLM_STR02954 (e0_STR02955 u * rho_STR02954 (h, e0_STR02955 u))) •
        (1 : PeriodicHolder_STR02968))

theorem Gfun_val_STR02955 (h γ : ℝ) (u : PeriodicC2_STR02969) :
    (Gfun_STR02955 h γ u).val = gradG_STR02950 h γ u.val := by
  funext t
  unfold Gfun_STR02955 gradG_STR02950
  rw [val_mul_STR02954, Pi.mul_apply, rho_val_STR02954]
  congr 1
  have hI : meanCLM_STR02954 (e1_STR02955 u * e1_STR02955 u * rho_STR02954 (h, e0_STR02955 u)) =
      meanT_STR02901 (fun r => deriv u.val r ^ 2 * rhoT_STR02901 h u.val r) := by
    rw [meanCLM_apply_STR02954]
    congr 1
    funext r
    rw [val_mul_STR02954, val_mul_STR02954, Pi.mul_apply, Pi.mul_apply, rho_val_STR02954]
    simp only [e1_val_STR02955, e0_val_STR02955]
    ring
  have hE : meanCLM_STR02954 (e0_STR02955 u * rho_STR02954 (h, e0_STR02955 u)) =
      meanT_STR02901 (fun r => u.val r * rhoT_STR02901 h u.val r) := by
    rw [meanCLM_apply_STR02954]
    congr 1
    funext r
    rw [val_mul_STR02954, Pi.mul_apply, rho_val_STR02954]
    simp only [e0_val_STR02955]
  rw [hI, hE]
  simp only [PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_sub,
    PeriodicHolder_STR02968.val_smul, val_mul_STR02954, val_one_STR02954, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, e1_val_STR02955, e0_val_STR02955,
    e2_val_STR02955]
  show _ = _
  have : s3_STR02955.val t = Real.sin (3 * t) := rfl
  rw [this]
  ring

/-- The full gradient `(h, γ, u) ↦ G(h, γ, u)` with values in `C^{0,1/2}`. -/
noncomputable def Gmap_STR02955 (x : ℝ × ℝ × PeriodicC2_STR02969) : PeriodicHolder_STR02968 :=
  Gfun_STR02955 x.1 x.2.1 x.2.2

theorem Gmap_smooth_STR02955 : ContDiff ℝ ∞ Gmap_STR02955 := by
  have hρ : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => rho_STR02954 (x.1, e0_STR02955 x.2.2)) :=
    rho_smooth_STR02954.comp (contDiff_fst.prodMk (e0_STR02955.contDiff.comp (contDiff_snd.comp contDiff_snd)))
  have h0 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => e0_STR02955 x.2.2) :=
    e0_STR02955.contDiff.comp (contDiff_snd.comp contDiff_snd)
  have h1 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => e1_STR02955 x.2.2) :=
    e1_STR02955.contDiff.comp (contDiff_snd.comp contDiff_snd)
  have h2 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => e2_STR02955 x.2.2) :=
    e2_STR02955.contDiff.comp (contDiff_snd.comp contDiff_snd)
  have hh : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => x.1) := contDiff_fst
  have hg : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => x.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hI : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 =>
      meanCLM_STR02954 (e1_STR02955 x.2.2 * e1_STR02955 x.2.2 * rho_STR02954 (x.1, e0_STR02955 x.2.2))) :=
    meanCLM_STR02954.contDiff.comp ((h1.mul h1).mul hρ)
  have hE : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 =>
      meanCLM_STR02954 (e0_STR02955 x.2.2 * rho_STR02954 (x.1, e0_STR02955 x.2.2))) :=
    meanCLM_STR02954.contDiff.comp (h0.mul hρ)
  have hc1 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => (6 * x.1)) :=
    contDiff_const.mul hh
  have hc2 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => (2 * (1 + x.2.1))) :=
    contDiff_const.mul (contDiff_const.add hg)
  have hc3 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 =>
      (2 * (1 + x.2.1) * meanCLM_STR02954 (e0_STR02955 x.2.2 * rho_STR02954 (x.1, e0_STR02955 x.2.2)))) :=
    hc2.mul hE
  have t1 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => (-2 : ℝ) • e2_STR02955 x.2.2) :=
    (contDiff_const (c := (-2 : ℝ))).smul h2
  have t2 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 =>
      (6 * x.1) • (s3_STR02955 * e1_STR02955 x.2.2)) :=
    hc1.smul (contDiff_const.mul h1)
  have t3 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => e1_STR02955 x.2.2 * e1_STR02955 x.2.2) :=
    h1.mul h1
  have t4 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => (2 * (1 + x.2.1)) • e0_STR02955 x.2.2) :=
    hc2.smul h0
  have t5 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 =>
      meanCLM_STR02954 (e1_STR02955 x.2.2 * e1_STR02955 x.2.2 * rho_STR02954 (x.1, e0_STR02955 x.2.2)) •
        (1 : PeriodicHolder_STR02968)) :=
    hI.smul contDiff_const
  have t6 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 =>
      (2 * (1 + x.2.1) * meanCLM_STR02954 (e0_STR02955 x.2.2 * rho_STR02954 (x.1, e0_STR02955 x.2.2))) •
        (1 : PeriodicHolder_STR02968)) :=
    hc3.smul contDiff_const
  have hB := ((((t1.add t2).sub t3).sub t4).sub t5).add t6
  exact hρ.mul hB

/-! ### The complementary projection as a bounded operator into `Y` -/

theorem meanT_const_STR02955 (a : ℝ) : meanT_STR02901 (fun _ => a) = a := by
  unfold meanT_STR02901
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  field_simp

theorem meanT_lin3_STR02955 {g g1 g2 g3 : ℝ → ℝ} (hg : Continuous g) (h1 : Continuous g1)
    (h2 : Continuous g2) (h3 : Continuous g3) (a1 a2 a3 : ℝ) :
    meanT_STR02901 (fun t => g t - a1 * g1 t - a2 * g2 t - a3 * g3 t) =
      meanT_STR02901 g - a1 * meanT_STR02901 g1 - a2 * meanT_STR02901 g2 -
        a3 * meanT_STR02901 g3 := by
  unfold meanT_STR02901
  have i0 : IntervalIntegrable g MeasureTheory.volume 0 (2 * Real.pi) := hg.intervalIntegrable _ _
  have i1 : IntervalIntegrable (fun t => a1 * g1 t) MeasureTheory.volume 0 (2 * Real.pi) :=
    (continuous_const.mul h1).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => a2 * g2 t) MeasureTheory.volume 0 (2 * Real.pi) :=
    (continuous_const.mul h2).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun t => a3 * g3 t) MeasureTheory.volume 0 (2 * Real.pi) :=
    (continuous_const.mul h3).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (i0.sub i1 |>.sub i2) i3,
    intervalIntegral.integral_sub (i0.sub i1) i2, intervalIntegral.integral_sub i0 i1,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  ring

theorem meanT_cos_STR02955 : meanT_STR02901 Real.cos = 0 := by
  unfold meanT_STR02901
  rw [integral_cos]; simp

theorem meanT_sin_STR02955 : meanT_STR02901 Real.sin = 0 := by
  unfold meanT_STR02901
  rw [integral_sin]; simp

theorem meanT_cc_STR02955 : meanT_STR02901 (fun t => Real.cos t * Real.cos t) = 1 / 2 := by
  unfold meanT_STR02901
  simp only [← sq]
  rw [integral_cos_sq]
  have hpi : (Real.pi) ≠ 0 := Real.pi_ne_zero
  simp only [Real.sin_zero, Real.sin_two_pi]
  field_simp
  ring

theorem meanT_ss_STR02955 : meanT_STR02901 (fun t => Real.sin t * Real.sin t) = 1 / 2 := by
  unfold meanT_STR02901
  simp only [← sq]
  rw [integral_sin_sq]
  have hpi : (Real.pi) ≠ 0 := Real.pi_ne_zero
  simp only [Real.cos_zero, Real.cos_two_pi, Real.sin_zero, Real.sin_two_pi]
  field_simp
  ring

theorem meanT_sc_STR02955 : meanT_STR02901 (fun t => Real.sin t * Real.cos t) = 0 := by
  unfold meanT_STR02901
  rw [integral_sin_mul_cos₁]; simp

theorem projP_inE_STR02955 {f : ℝ → ℝ} (hf : Continuous f) : InE_STR02901 (projP_STR02953 f) := by
  have hc := Real.continuous_cos
  have hs := Real.continuous_sin
  have e0 : projP_STR02953 f = fun t => f t - meanT_STR02901 f * (fun _ => (1 : ℝ)) t -
      (2 * pair_STR02953 Real.cos f) * Real.cos t - (2 * pair_STR02953 Real.sin f) * Real.sin t := by
    funext t; simp only [projP_STR02953]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, meanT_lin3_STR02955 hf continuous_const hc hs, meanT_const_STR02955, meanT_cos_STR02955,
      meanT_sin_STR02955]
    ring
  · have e1 : (fun t => projP_STR02953 f t * Real.cos t) = fun t => f t * Real.cos t -
        meanT_STR02901 f * Real.cos t - (2 * pair_STR02953 Real.cos f) * (Real.cos t * Real.cos t) -
        (2 * pair_STR02953 Real.sin f) * (Real.sin t * Real.cos t) := by
      funext t; simp only [projP_STR02953]; ring
    rw [e1, meanT_lin3_STR02955 (g := fun t => f t * Real.cos t) (g1 := Real.cos)
      (g2 := fun t => Real.cos t * Real.cos t) (g3 := fun t => Real.sin t * Real.cos t)
      (hf.mul hc) hc (hc.mul hc) (hs.mul hc), meanT_cc_STR02955,
      meanT_cos_STR02955, meanT_sc_STR02955]
    simp only [pair_STR02953]
    ring
  · have e1 : (fun t => projP_STR02953 f t * Real.sin t) = fun t => f t * Real.sin t -
        meanT_STR02901 f * Real.sin t - (2 * pair_STR02953 Real.cos f) * (Real.cos t * Real.sin t) -
        (2 * pair_STR02953 Real.sin f) * (Real.sin t * Real.sin t) := by
      funext t; simp only [projP_STR02953]; ring
    have hcs : meanT_STR02901 (fun t => Real.cos t * Real.sin t) = 0 := by
      simpa only [mul_comm] using meanT_sc_STR02955
    rw [e1, meanT_lin3_STR02955 (g := fun t => f t * Real.sin t) (g1 := Real.sin)
      (g2 := fun t => Real.cos t * Real.sin t) (g3 := fun t => Real.sin t * Real.sin t)
      (hf.mul hs) hs (hc.mul hs) (hs.mul hs), meanT_ss_STR02955,
      meanT_sin_STR02955, hcs]
    simp only [pair_STR02953]
    ring

theorem projBdd_STR02955 :
    IsBoundedLinearOn_STR02953 (IsC0Alpha_STR02953 (1 / 2)) (IsC0Alpha_STR02953 (1 / 2))
      (c0Norm_STR02953 (1 / 2)) (c0Norm_STR02953 (1 / 2)) projP_STR02953 := by
  have : HolderExponent (1 / 2 : ℝ) := holderExponent_half_STR02901
  exact (str029_53_holder_multiplication_bounded_linear_operations_projection
    (α := (1 / 2 : ℝ))).1

/-- The complementary projection `P` as a bounded operator on `C^{0,1/2}`. -/
noncomputable def PCLM_STR02955 : PeriodicHolder_STR02968 →L[ℝ] PeriodicHolder_STR02968 :=
  LinearMap.mkContinuous
    { toFun := fun f => PeriodicHolder_STR02968.mk (projP_STR02953 f.val)
        (mkHolder_STR02955 (projBdd_STR02955.1 f.val (isC0_val_STR02954 f)))
      map_add' := fun f g => ext_STR02954
        (projBdd_STR02955.2.1.1 f.val g.val (isC0_val_STR02954 f) (isC0_val_STR02954 g))
      map_smul' := fun c f => ext_STR02954
        (projBdd_STR02955.2.1.2 c f.val (isC0_val_STR02954 f)) }
    projBdd_STR02955.2.2.choose
    (fun f => projBdd_STR02955.2.2.choose_spec.2 f.val (isC0_val_STR02954 f))

theorem PCLM_val_STR02955 (f : PeriodicHolder_STR02968) :
    (PCLM_STR02955 f).val = projP_STR02953 f.val := rfl

theorem PCLM_mem_STR02955 (f : PeriodicHolder_STR02968) : PCLM_STR02955 f ∈ Y_STR02969 :=
  (holderData_STR02969.mem_sub_iff _).2
    (by
      show InE_STR02901 (projP_STR02953 f.val)
      exact projP_inE_STR02955 f.isPerHolder.2.1)

/-- The complementary projection `P` as a bounded operator `C^{0,1/2} → Y`. -/
noncomputable def PY_STR02955 : PeriodicHolder_STR02968 →L[ℝ] Y_STR02969 :=
  PCLM_STR02955.codRestrict Y_STR02969 PCLM_mem_STR02955

theorem PY_val_STR02955 (f : PeriodicHolder_STR02968) :
    (PY_STR02955 f : PeriodicHolder_STR02968) = PCLM_STR02955 f := rfl

/-- The inclusion `ℝ × ℝ × E → ℝ × ℝ × C^{2,1/2}`. -/
noncomputable def incl_STR02955 : ℝ × ℝ × E_STR02969 →L[ℝ] ℝ × ℝ × PeriodicC2_STR02969 :=
  ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ ℝ)
    (ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ ℝ) E_STR02969.subtypeL)

/-- The full gradient restricted to `u ∈ E`. -/
noncomputable def GmapE_STR02955 (x : ℝ × ℝ × E_STR02969) : PeriodicHolder_STR02968 :=
  Gmap_STR02955 (incl_STR02955 x)

/-- The concrete range map `R = P G` on `ℝ × ℝ × E`, valued in `Y`. -/
noncomputable def Rmap_STR02955 (x : ℝ × ℝ × E_STR02969) : Y_STR02969 :=
  PY_STR02955 (Gmap_STR02955 (incl_STR02955 x))

theorem GmapE_smooth_STR02955 : ContDiff ℝ ∞ GmapE_STR02955 :=
  Gmap_smooth_STR02955.comp incl_STR02955.contDiff

theorem Rmap_smooth_STR02955 : ContDiff ℝ ∞ Rmap_STR02955 :=
  PY_STR02955.contDiff.comp GmapE_smooth_STR02955

/-! ### Values and derivative at zero -/

theorem rho_zero_STR02955 : rho_STR02954 ((0 : ℝ), (0 : PeriodicHolder_STR02968)) = 1 := by
  apply ext_STR02954
  funext t
  rw [rho_val_STR02954]
  have h0 : (0 : PeriodicHolder_STR02968).val = fun _ => 0 := rfl
  simp only [rhoT_STR02901, h0, zero_mul, add_zero, Real.exp_zero]
  rw [meanT_const_STR02955]
  simp [val_one_STR02954]

theorem Gmap_zero_STR02955 : Gmap_STR02955 0 = 0 := by
  simp [Gmap_STR02955, Gfun_STR02955]

theorem Rmap_zero_STR02955 : Rmap_STR02955 0 = 0 := by
  simp [Rmap_STR02955, Gmap_zero_STR02955]

theorem pathDeriv_STR02955 (w : PeriodicC2_STR02969) (hw : meanCLM_STR02954 (e0_STR02955 w) = 0) :
    HasDerivAt (fun s : ℝ => Gmap_STR02955 (0, 0, s • w))
      ((-2 : ℝ) • e2_STR02955 w - (2 : ℝ) • e0_STR02955 w) 0 := by
  have hρd : Differentiable ℝ (fun s : ℝ => rho_STR02954 ((0 : ℝ), s • e0_STR02955 w)) :=
    (rho_smooth_STR02954.differentiable (by simp)).comp
      (differentiable_const _ |>.prodMk (differentiable_id.smul_const _))
  have hρ := (hρd 0).hasDerivAt
  have hs : HasDerivAt (fun s : ℝ => s) 1 0 := hasDerivAt_id 0
  have hsb := hs.smul_const (e1_STR02955 w)
  have hsa := hs.smul_const (e0_STR02955 w)
  have hsc := hs.smul_const (e2_STR02955 w)
  have hin1 := (hsb.mul hsb).mul hρ
  have hin2 := hsa.mul hρ
  have hm1 := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hin1
  have hm2 := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hin2
  have hB := (((((hsc.const_smul (-2 : ℝ)).add ((hsb.const_mul s3_STR02955).const_smul (6 * (0 : ℝ)))).sub
    (hsb.mul hsb)).sub (hsa.const_smul (2 * (1 + (0 : ℝ))))).sub
    (hm1.smul_const (1 : PeriodicHolder_STR02968))).add
    ((hm2.const_mul (2 * (1 + (0 : ℝ)))).smul_const (1 : PeriodicHolder_STR02968))
  have hG := hρ.mul hB
  convert hG using 1
  · funext s
    simp only [Gmap_STR02955, Gfun_STR02955, map_smul]
    rfl
  · simp [rho_zero_STR02955, hw]

theorem fderivG_STR02955 (w : PeriodicC2_STR02969) (hw : meanCLM_STR02954 (e0_STR02955 w) = 0) :
    fderiv ℝ Gmap_STR02955 0 ((0 : ℝ), (0 : ℝ), w) =
      (-2 : ℝ) • e2_STR02955 w - (2 : ℝ) • e0_STR02955 w := by
  have hG : HasFDerivAt Gmap_STR02955 (fderiv ℝ Gmap_STR02955 0) 0 :=
    (Gmap_smooth_STR02955.differentiable (by simp) 0).hasFDerivAt
  have hsw : HasDerivAt (fun s : ℝ => s • w) w 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).smul_const w
  have hpath : HasDerivAt (fun s : ℝ => ((0 : ℝ), (0 : ℝ), s • w)) ((0 : ℝ), (0 : ℝ), w) 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk hsw)
  have hc := hG.comp_hasDerivAt_of_eq (0 : ℝ) hpath (by simp; rfl)
  exact hc.unique (pathDeriv_STR02955 w hw)

theorem projP_of_inE_STR02955 {g : ℝ → ℝ} (hg : InE_STR02901 g) : projP_STR02953 g = g := by
  funext t
  simp only [projP_STR02953, pair_STR02953]
  rw [hg.1, hg.2.1, hg.2.2]
  ring

theorem inE_smul_STR02955 (c : ℝ) {g : ℝ → ℝ} (hg : InE_STR02901 g) :
    InE_STR02901 (fun t => c * g t) := by
  have e : ∀ b : ℝ → ℝ, meanT_STR02901 (fun t => c * g t * b t) = c * meanT_STR02901 (fun t => g t * b t) := by
    intro b
    have e1 : (fun t => c * g t * b t) = c • fun t => g t * b t := by
      funext t; simp [mul_assoc]
    rw [e1, meanT_smul_STR02953]
  refine ⟨?_, ?_, ?_⟩
  · show meanT_STR02901 (c • g) = 0
    rw [meanT_smul_STR02953, hg.1, mul_zero]
  · rw [e, hg.2.1, mul_zero]
  · rw [e, hg.2.2, mul_zero]

theorem ftc_mean_STR02955 {F f : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (f x) x) (hf : Continuous f)
    (hper : F (2 * Real.pi) = F 0) : meanT_STR02901 f = 0 := by
  unfold meanT_STR02901
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x) (hf.intervalIntegrable _ _),
    hper, sub_self, mul_zero]

theorem c2_inE_STR02955 {w : ℝ → ℝ} (hw : IsC2Alpha_STR02901 (1 / 2) w) (hm : meanT_STR02901 w = 0) :
    InE_STR02901 (fun t => deriv (deriv w) t + w t) := by
  obtain ⟨hper, hd, hd1, hc2, -⟩ := hw
  have hper1 : Function.Periodic (deriv w) (2 * Real.pi) := periodic_deriv_STR02901 hper
  have p0 : w (2 * Real.pi) = w 0 := by simpa using hper 0
  have p1 : deriv w (2 * Real.pi) = deriv w 0 := by simpa using hper1 0
  have cw : Continuous w := hd.continuous
  have cw1 : Continuous (deriv w) := hd1.continuous
  refine ⟨?_, ?_, ?_⟩
  · have h1 : meanT_STR02901 (deriv (deriv w)) = 0 :=
      ftc_mean_STR02955 (fun x => (hd1 x).hasDerivAt) hc2 p1
    have e : (fun t => deriv (deriv w) t + w t) = deriv (deriv w) + w := rfl
    rw [e, meanT_add_STR02953 hc2 cw, h1, hm, add_zero]
  · refine ftc_mean_STR02955 (F := fun t => deriv w t * Real.cos t + w t * Real.sin t) (fun x => ?_)
      ((hc2.add cw).mul Real.continuous_cos) ?_
    · have := ((hd1 x).hasDerivAt.mul (Real.hasDerivAt_cos x)).add
        ((hd x).hasDerivAt.mul (Real.hasDerivAt_sin x))
      convert this using 1
      ring
    · simp [p0, p1]
  · refine ftc_mean_STR02955 (F := fun t => deriv w t * Real.sin t - w t * Real.cos t) (fun x => ?_)
      ((hc2.add cw).mul Real.continuous_sin) ?_
    · have := ((hd1 x).hasDerivAt.mul (Real.hasDerivAt_sin x)).sub
        ((hd x).hasDerivAt.mul (Real.hasDerivAt_cos x))
      convert this using 1
      ring
    · simp [p0, p1]

theorem fderiv_incl_STR02955 {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : ℝ × ℝ × PeriodicC2_STR02969 → Z} (hF : ContDiff ℝ ∞ F) (v : ℝ × ℝ × E_STR02969) :
    fderiv ℝ (fun x => F (incl_STR02955 x)) 0 v = fderiv ℝ F 0 (incl_STR02955 v) := by
  have h1 : HasFDerivAt F (fderiv ℝ F (incl_STR02955 0)) (incl_STR02955 0) :=
    (hF.differentiable (by simp) _).hasFDerivAt
  have h2 := h1.comp (0 : ℝ × ℝ × E_STR02969) incl_STR02955.hasFDerivAt
  show fderiv ℝ (F ∘ incl_STR02955) 0 v = _
  rw [h2.fderiv, map_zero]
  rfl

theorem fderivR_STR02955 (w : E_STR02969) (t : ℝ) :
    ((fderiv ℝ Rmap_STR02955 0 ((0 : ℝ), (0 : ℝ), w) : Y_STR02969) : PeriodicHolder_STR02968).val t =
      -2 * (deriv (deriv (w : PeriodicC2_STR02969).val) t + (w : PeriodicC2_STR02969).val t) := by
  have hGE : HasFDerivAt GmapE_STR02955 (fderiv ℝ GmapE_STR02955 0) 0 :=
    (GmapE_smooth_STR02955.differentiable (by simp) 0).hasFDerivAt
  have hR : HasFDerivAt Rmap_STR02955 (PY_STR02955.comp (fderiv ℝ GmapE_STR02955 0)) 0 :=
    PY_STR02955.hasFDerivAt.comp (0 : ℝ × ℝ × E_STR02969) hGE
  have hwE : InE_STR02901 (w : PeriodicC2_STR02969).val := (c2Data_STR02969.mem_sub_iff _).1 w.2
  have hmean : meanCLM_STR02954 (e0_STR02955 (w : PeriodicC2_STR02969)) = 0 := hwE.1
  have hd : fderiv ℝ GmapE_STR02955 0 ((0 : ℝ), (0 : ℝ), w) =
      (-2 : ℝ) • e2_STR02955 (w : PeriodicC2_STR02969) - (2 : ℝ) • e0_STR02955 (w : PeriodicC2_STR02969) :=
    (fderiv_incl_STR02955 Gmap_smooth_STR02955 ((0 : ℝ), (0 : ℝ), w)).trans
      (fderivG_STR02955 (w : PeriodicC2_STR02969) hmean)
  rw [hR.fderiv]
  show (PCLM_STR02955 (fderiv ℝ GmapE_STR02955 0 ((0 : ℝ), (0 : ℝ), w))).val t = _
  rw [hd, PCLM_val_STR02955]
  have hf : ((-2 : ℝ) • e2_STR02955 (w : PeriodicC2_STR02969) -
      (2 : ℝ) • e0_STR02955 (w : PeriodicC2_STR02969)).val = fun t =>
        -2 * (deriv (deriv (w : PeriodicC2_STR02969).val) t + (w : PeriodicC2_STR02969).val t) := by
    funext t
    simp only [PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_smul, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, e2_val_STR02955, e0_val_STR02955]
    ring
  rw [hf, projP_of_inE_STR02955 (inE_smul_STR02955 (-2) (c2_inE_STR02955 (w : PeriodicC2_STR02969).isC2 hwE.1))]

theorem bdd_iteratedFDeriv_STR02955 {X Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {F : X → Z} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ∃ r > 0, ∃ M : ℝ, ∀ x : X, ‖x‖ < r → ‖iteratedFDeriv ℝ n F x‖ ≤ M := by
  have hc : Continuous (fun x => iteratedFDeriv ℝ n F x) :=
    hF.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hev : ∀ᶠ x in 𝓝 (0 : X), ‖iteratedFDeriv ℝ n F x‖ < ‖iteratedFDeriv ℝ n F 0‖ + 1 :=
    (hc.norm.continuousAt (x := 0)).eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 hev
  exact ⟨ε, hε, ‖iteratedFDeriv ℝ n F 0‖ + 1, fun x hx =>
    (h (by simpa [dist_zero_right] using hx)).le⟩

/-- STR029.55, assembled smooth range calculus and its derivative. Writing `G` for the full
gradient on `ℝ × ℝ × C^{2,1/2}` (values in `C^{0,1/2}`), `Gₑ` for its restriction to
`ℝ × ℝ × E`, and `R = P G` for the concrete range map on `ℝ × ℝ × E` with values in `Y`:
(1) to (3) `G`, `Gₑ`, `R` are `C^∞` (smooth on the whole space, hence on every neighbourhood of
zero); (4) `G` has the pointwise formula `gradG_STR02950`; (5) `R` has the pointwise formula
`projP_STR02953 (gradG_STR02950 …)`; (6) `R 0 = 0`; (7) `D_w R(0) w = -2 (w'' + w)` for `w ∈ E`;
(8) to (10) for every order `n` there is a radius `r > 0` and a bound `M` for
`‖iteratedFDeriv ℝ n ·‖` on the ball of radius `r`, for each of `G`, `Gₑ`, `R`. -/
theorem str029_55_assemble_smooth_range_calculus_derivative :
    ContDiff ℝ ∞ Gmap_STR02955 ∧ ContDiff ℝ ∞ GmapE_STR02955 ∧ ContDiff ℝ ∞ Rmap_STR02955 ∧
      (∀ (h γ : ℝ) (u : PeriodicC2_STR02969) (t : ℝ),
        (Gmap_STR02955 (h, γ, u)).val t = gradG_STR02950 h γ u.val t) ∧
      (∀ (x : ℝ × ℝ × E_STR02969) (t : ℝ),
        ((Rmap_STR02955 x : Y_STR02969) : PeriodicHolder_STR02968).val t =
          projP_STR02953 (gradG_STR02950 x.1 x.2.1 (x.2.2 : PeriodicC2_STR02969).val) t) ∧
      Rmap_STR02955 0 = 0 ∧
      (∀ (w : E_STR02969) (t : ℝ),
        ((fderiv ℝ Rmap_STR02955 0 ((0 : ℝ), (0 : ℝ), w) : Y_STR02969) :
            PeriodicHolder_STR02968).val t =
          -2 * (deriv (deriv (w : PeriodicC2_STR02969).val) t + (w : PeriodicC2_STR02969).val t)) ∧
      (∀ n : ℕ, ∃ r > 0, ∃ M : ℝ, ∀ x : ℝ × ℝ × PeriodicC2_STR02969, ‖x‖ < r →
        ‖iteratedFDeriv ℝ n Gmap_STR02955 x‖ ≤ M) ∧
      (∀ n : ℕ, ∃ r > 0, ∃ M : ℝ, ∀ x : ℝ × ℝ × E_STR02969, ‖x‖ < r →
        ‖iteratedFDeriv ℝ n GmapE_STR02955 x‖ ≤ M) ∧
      (∀ n : ℕ, ∃ r > 0, ∃ M : ℝ, ∀ x : ℝ × ℝ × E_STR02969, ‖x‖ < r →
        ‖iteratedFDeriv ℝ n Rmap_STR02955 x‖ ≤ M) := by
  refine ⟨Gmap_smooth_STR02955, GmapE_smooth_STR02955, Rmap_smooth_STR02955, ?_, ?_,
    Rmap_zero_STR02955, fderivR_STR02955, ?_, ?_, ?_⟩
  · intro h γ u t
    exact congrFun (Gfun_val_STR02955 h γ u) t
  · intro x t
    show (PCLM_STR02955 (Gmap_STR02955 (incl_STR02955 x))).val t = _
    rw [PCLM_val_STR02955]
    exact congrArg (fun g => projP_STR02953 g t) (Gfun_val_STR02955 x.1 x.2.1 (x.2.2 : PeriodicC2_STR02969))
  · exact bdd_iteratedFDeriv_STR02955 Gmap_smooth_STR02955
  · exact bdd_iteratedFDeriv_STR02955 GmapE_smooth_STR02955
  · exact bdd_iteratedFDeriv_STR02955 Rmap_smooth_STR02955

end DGPS.Frontier.STR029
