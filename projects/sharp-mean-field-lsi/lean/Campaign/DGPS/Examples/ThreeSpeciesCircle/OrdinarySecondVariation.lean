import DGPS.Frontier.STR029.T56
import DGPS.Frontier.STR029.T62
import DGPS.Frontier.STR029.T24

/-!
The actual STR029 logarithmic chart has Hessian twice the weighted Dirichlet-minus-
covariance form at a critical density. All derivatives below are of the existing chart
and its existing Holder-valued gradient. The chart carrier is PeriodicC2_STR02969;
no Frechet differentiability on an unbundled H1 class is asserted.
-/

open Filter Topology Function NormedSpace
open MeasureTheory DGPS.Circle.AngularNormalization
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle.OrdinarySecondVariation

private theorem line_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : E) : HasDerivAt (fun s : ℝ => u + s • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u

/-- The first derivative of the actual bundled chart, paired with an arbitrary direction. -/
theorem fderiv_JC2_apply (h γ : ℝ) (u v : PeriodicC2_STR02969) :
    fderiv ℝ (JC2_STR02956 h γ) u v =
      meanCLM_STR02954 (Gfun_STR02955 h γ u * e0_STR02955 v) := by
  rw [fderiv_JC2_STR02924, meanCLM_apply_STR02954]
  congr 1
  funext t
  rw [val_mul_STR02954, Pi.mul_apply, Gfun_val_STR02955]
  rfl

/-- Differentiating the existing normalized gradient at an actual critical chart. -/
theorem gradient_line_deriv (h γ : ℝ) (u v : PeriodicC2_STR02969)
    (hcrit : ∀ t, gradG_STR02950 h γ u.val t = 0) :
    HasDerivAt (fun s : ℝ => Gfun_STR02955 h γ (u + s • v))
      (rho_STR02954 (h, e0_STR02955 u) *
        ((-2 : ℝ) • e2_STR02955 v +
          (6 * h) • (s3_STR02955 * e1_STR02955 v) -
          (2 : ℝ) • (e1_STR02955 u * e1_STR02955 v) -
          (2 * (1 + γ)) • e0_STR02955 v +
          (2 * (1 + γ) * meanCLM_STR02954
            (e0_STR02955 v * rho_STR02954 (h, e0_STR02955 u))) •
            (1 : PeriodicHolder_STR02968))) 0 := by
  let U := e0_STR02955 u
  let V := e0_STR02955 v
  let D := e1_STR02955 u
  let Dv := e1_STR02955 v
  let R := rho_STR02954 (h, U)
  let c := meanCLM_STR02954 (V * R)
  let I' := 2 * meanCLM_STR02954 (D * Dv * R) +
    meanCLM_STR02954 (R * (D * D - meanCLM_STR02954 (D * D * R) •
      (1 : PeriodicHolder_STR02968)) * V)
  let E' := meanCLM_STR02954 (V * R + U * (R * (V - c • (1 : PeriodicHolder_STR02968))))
  have hR := hasDerivAt_rho_path_STR02949 h U V
  have hI := hasDerivAt_fisher_path_STR02949 h U V D Dv
  have hE := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_path_STR02949 U V).mul hR)
  simp only [zero_smul, add_zero] at hE
  have hlog := hasDerivAt_logZ_path_STR02949 h U V
  have hJ := (hI.sub ((hE.sub hlog).const_mul (2 * (1 + γ)))).add_const
    (-(2 * (1 + γ)) * Real.log (meanT_STR02901 (fun t => Real.exp (h * Real.cos (3 * t)))))
  have hJ0 : HasDerivAt (fun s : ℝ => Jchart_STR02950 h γ
      (fun t => u.val t + s * v.val t)) 0 0 := by
    have hh := str029_50_integrate_variation_compute_mean_variation h γ u.isC2 v.isC2
    simpa only [hcrit, zero_mul, meanT_STR02901, intervalIntegral.integral_zero,
      mul_zero] using hh
  have hJfun : (fun s : ℝ =>
      meanCLM_STR02954 ((D + s • Dv) * (D + s • Dv) * rho_STR02954 (h, U + s • V)) -
        2 * (1 + γ) *
          (meanCLM_STR02954 ((U + s • V) * rho_STR02954 (h, U + s • V)) -
            Real.log (Z_STR02954 (h, U + s • V))) +
        (-(2 * (1 + γ)) * Real.log
          (meanT_STR02901 (fun t => Real.exp (h * Real.cos (3 * t)))))) =
      (fun s : ℝ => Jchart_STR02950 h γ (fun t => u.val t + s * v.val t)) := by
    funext s
    rw [Jchart_STR02950, fisherChart_path_STR02949 h u.isC2 v.isC2 s,
      entropyChart_path_STR02949 h u.isC2 v.isC2 s]
    change _ = meanCLM_STR02954 ((D + s • Dv) * (D + s • Dv) *
      rho_STR02954 (h, U + s • V)) - 2 * (1 + γ) *
      (meanCLM_STR02954 ((U + s • V) * rho_STR02954 (h, U + s • V)) -
        Real.log (Z_STR02954 (h, U + s • V)) + _)
    ring
  have hcancel : -I' + 2 * (1 + γ) * E' = 2 * (1 + γ) * c := by
    simp only [Function.comp_def, Pi.sub_apply, Pi.mul_apply] at hJ
    rw [hJfun] at hJ
    have hh := hJ.unique hJ0
    change I' - 2 * (1 + γ) * (E' - c) = 0 at hh
    linarith
  let B := fun s : ℝ =>
    (-2 : ℝ) • (e2_STR02955 u + s • e2_STR02955 v) +
      (6 * h) • (s3_STR02955 * (D + s • Dv)) -
      (D + s • Dv) * (D + s • Dv) - (2 * (1 + γ)) • (U + s • V) -
      meanCLM_STR02954 ((D + s • Dv) * (D + s • Dv) *
        rho_STR02954 (h, U + s • V)) • (1 : PeriodicHolder_STR02968) +
      (2 * (1 + γ) * meanCLM_STR02954 ((U + s • V) *
        rho_STR02954 (h, U + s • V))) • (1 : PeriodicHolder_STR02968)
  have hB0 : B 0 = 0 := by
    apply ext_STR02954
    funext t
    have hg := hcrit t
    have hRpos : 0 < R.val t := by
      rw [show R.val t = rhoT_STR02901 h u.val t from rho_val_STR02954 (h, U) t]
      exact rhoT_pos_STR02901 h u.isC2.2.1.continuous t
    have hp : R.val t * (B 0).val t = 0 := by
      have hG : R * B 0 = Gfun_STR02955 h γ u := by
        dsimp only [B, R, U, D]
        simp only [zero_smul, add_zero]
        rfl
      rw [← Pi.mul_apply, ← val_mul_STR02954, hG, Gfun_val_STR02955]
      exact hg
    exact (mul_eq_zero.mp hp).resolve_left hRpos.ne'
  have hB1 := (line_deriv (e2_STR02955 u) (e2_STR02955 v)).const_smul (-2 : ℝ)
  have hB2 := ((hasDerivAt_const (0 : ℝ) s3_STR02955).mul
    (line_deriv D Dv)).const_smul (6 * h)
  have hB3 := (line_deriv D Dv).mul (line_deriv D Dv)
  have hB4 := (line_deriv U V).const_smul (2 * (1 + γ))
  have hB5 := hI.smul_const (1 : PeriodicHolder_STR02968)
  have hB6 := (hE.const_mul (2 * (1 + γ))).smul_const (1 : PeriodicHolder_STR02968)
  have hB := ((((hB1.add hB2).sub hB3).sub hB4).sub hB5).add hB6
  have hB' : HasDerivAt B
      ((-2 : ℝ) • e2_STR02955 v + (6 * h) • (s3_STR02955 * Dv) -
        (Dv * D + D * Dv) - (2 * (1 + γ)) • V -
        I' • (1 : PeriodicHolder_STR02968) +
        (2 * (1 + γ) * E') • (1 : PeriodicHolder_STR02968)) 0 := by
    convert hB using 1
    · funext s
      apply ext_STR02954
      funext t
      simp only [B, Function.comp_def, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        Pi.mul_apply, PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_sub,
        PeriodicHolder_STR02968.val_smul, val_mul_STR02954, smul_eq_mul]
    · apply ext_STR02954
      funext t
      simp only [I', E', R, c, zero_smul, add_zero, zero_mul, zero_add,
        PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_sub,
        PeriodicHolder_STR02968.val_smul, val_mul_STR02954, val_one_STR02954,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  have hh := hR.mul hB'
  simp only [zero_smul, add_zero] at hh
  have hfun : (fun s : ℝ => rho_STR02954 (h, U + s • V) * B s) =
      (fun s : ℝ => Gfun_STR02955 h γ (u + s • v)) := by
    funext s
    simp only [Gfun_STR02955, map_add, map_smul]
    rfl
  change HasDerivAt (fun s : ℝ => rho_STR02954 (h, U + s • V) * B s) _ 0 at hh
  rw [hfun] at hh
  apply hh.congr_deriv
  change (R * (V - c • (1 : PeriodicHolder_STR02968))) * B 0 + R * _ = _
  rw [hB0, mul_zero, zero_add]
  congr 1
  apply ext_STR02954
  funext t
  simp only [PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_sub,
    PeriodicHolder_STR02968.val_smul, val_mul_STR02954, val_one_STR02954,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  change _ = -2 * (e2_STR02955 v).val t +
    6 * h * (s3_STR02955.val t * Dv.val t) - 2 * (D.val t * Dv.val t) -
    2 * (1 + γ) * V.val t + 2 * (1 + γ) * c * 1
  have hc := hcancel
  nlinarith

/-- Weighted periodic integration by parts in the actual chart density. -/
theorem weighted_ibp (h : ℝ) (u v w : PeriodicC2_STR02969) :
    meanT_STR02901 (fun t =>
      deriv (deriv v.val) t * w.val t * rhoT_STR02901 h u.val t +
      deriv v.val t * deriv w.val t * rhoT_STR02901 h u.val t +
      deriv v.val t * w.val t * (rhoT_STR02901 h u.val t *
        (-(3 * h * Real.sin (3 * t)) + deriv u.val t))) = 0 := by
  have hder : ∀ x, HasDerivAt
      (fun t => deriv v.val t * w.val t * rhoT_STR02901 h u.val t)
      (deriv (deriv v.val) x * w.val x * rhoT_STR02901 h u.val x +
        deriv v.val x * deriv w.val x * rhoT_STR02901 h u.val x +
        deriv v.val x * w.val x * (rhoT_STR02901 h u.val x *
          (-(3 * h * Real.sin (3 * x)) + deriv u.val x))) x := by
    intro x
    exact (((v.isC2.2.2.1 x).hasDerivAt.mul (w.isC2.2.1 x).hasDerivAt).mul
      (hasDerivAt_rho_STR02950 h u.isC2 x)).congr_deriv (by
        simp only [Pi.mul_apply]
        ring)
  have hcont : Continuous (fun t =>
      deriv (deriv v.val) t * w.val t * rhoT_STR02901 h u.val t +
      deriv v.val t * deriv w.val t * rhoT_STR02901 h u.val t +
      deriv v.val t * w.val t * (rhoT_STR02901 h u.val t *
        (-(3 * h * Real.sin (3 * t)) + deriv u.val t))) := by
    have := u.isC2.2.1.continuous
    have := u.isC2.2.2.1.continuous
    have := v.isC2.2.2.1.continuous
    have := v.isC2.2.2.2.1
    have := w.isC2.2.1.continuous
    have := w.isC2.2.2.1.continuous
    have := continuous_rho_STR02950 h u.isC2.2.1.continuous
    fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := 2 * Real.pi) (fun x _ => hder x) (hcont.intervalIntegrable _ _)
  have hpv : deriv v.val (2 * Real.pi) = deriv v.val 0 := by
    simpa using (periodic_deriv_STR02901 v.isC2.1) 0
  have hpw : w.val (2 * Real.pi) = w.val 0 := by simpa using w.isC2.1 0
  have hpr : rhoT_STR02901 h u.val (2 * Real.pi) = rhoT_STR02901 h u.val 0 := by
    simpa using periodic_rho_STR02950 h u.isC2.1 0
  unfold meanT_STR02901
  rw [hint, hpv, hpw, hpr]
  simp

/-- The exact actual-chart Hessian, with angular rate `1 + gamma`. -/
theorem hessian_JC2_eq_weighted_form (h γ : ℝ) (u v w : PeriodicC2_STR02969)
    (hcrit : ∀ t, gradG_STR02950 h γ u.val t = 0) :
    fderiv ℝ (fderiv ℝ (JC2_STR02956 h γ)) u v w =
      2 * (meanT_STR02901 (fun t =>
          deriv v.val t * deriv w.val t * rhoT_STR02901 h u.val t) -
        (1 + γ) * (meanT_STR02901 (fun t =>
          v.val t * w.val t * rhoT_STR02901 h u.val t) -
          meanT_STR02901 (fun t => v.val t * rhoT_STR02901 h u.val t) *
            meanT_STR02901 (fun t => w.val t * rhoT_STR02901 h u.val t))) := by
  let R := rho_STR02954 (h, e0_STR02955 u)
  let c := meanCLM_STR02954 (e0_STR02955 v * R)
  let Z := (-2 : ℝ) • e2_STR02955 v +
    (6 * h) • (s3_STR02955 * e1_STR02955 v) -
    (2 : ℝ) • (e1_STR02955 u * e1_STR02955 v) -
    (2 * (1 + γ)) • e0_STR02955 v +
    (2 * (1 + γ) * c) • (1 : PeriodicHolder_STR02968)
  have hd := meanCLM_STR02954.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((gradient_line_deriv h γ u v hcrit).mul
      (hasDerivAt_const (0 : ℝ) (e0_STR02955 w)))
  simp only [Function.comp_def, Pi.mul_apply, mul_zero, add_zero] at hd
  have hfun : (fun s : ℝ => meanCLM_STR02954
      (Gfun_STR02955 h γ (u + s • v) * e0_STR02955 w)) =
      (fun s : ℝ => fderiv ℝ (JC2_STR02956 h γ) (u + s • v) w) := by
    funext s
    exact (fderiv_JC2_apply h γ _ w).symm
  rw [hfun] at hd
  have hDF : Differentiable ℝ (fderiv ℝ (JC2_STR02956 h γ)) :=
    ((JC2_smooth_STR02956 h γ).fderiv_right (m := 1) (by simp)).differentiable (by simp)
  have hD : DifferentiableAt ℝ (fun z => fderiv ℝ (JC2_STR02956 h γ) z w) u :=
    (hDF u).clm_apply (differentiableAt_const w)
  have hl := hD.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (line_deriv u v) (by simp)
  have hH : fderiv ℝ (fderiv ℝ (JC2_STR02956 h γ)) u v w =
      meanCLM_STR02954 ((R * Z) * e0_STR02955 w) := by
    have he := hl.unique hd
    rw [fderiv_clm_apply (hDF u) (differentiableAt_const w)] at he
    rw [(hasFDerivAt_const w u).fderiv] at he
    simpa only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.smulRight_apply,
      zero_apply, map_zero, zero_add, add_zero, zero_mul, mul_zero] using he
  rw [hH, meanCLM_apply_STR02954]
  let r := rhoT_STR02901 h u.val
  let A := fun t => deriv (deriv v.val) t * w.val t * r t +
    deriv v.val t * deriv w.val t * r t +
    deriv v.val t * w.val t * (r t * (-(3 * h * Real.sin (3 * t)) + deriv u.val t))
  let B := fun t => deriv v.val t * deriv w.val t * r t
  let C := fun t => v.val t * w.val t * r t
  let D := fun t => w.val t * r t
  have hc : c = meanT_STR02901 (fun t => v.val t * r t) := by
    rw [show c = meanCLM_STR02954 (e0_STR02955 v * R) from rfl,
      meanCLM_apply_STR02954]
    congr 1
    funext t
    rw [val_mul_STR02954, Pi.mul_apply, rho_val_STR02954]
    rfl
  have hf : ((R * Z) * e0_STR02955 w).val = fun t =>
      (-2) * A t + 2 * B t + (-(2 * (1 + γ))) * C t +
        (2 * (1 + γ) * c) * D t := by
    funext t
    simp only [Z, R, PeriodicHolder_STR02968.val_add,
      PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_smul,
      val_mul_STR02954, val_one_STR02954, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, Pi.mul_apply, smul_eq_mul, rho_val_STR02954,
      e0_val_STR02955, e1_val_STR02955, e2_val_STR02955]
    rw [show s3_STR02955.val t = Real.sin (3 * t) from rfl]
    dsimp only [A, B, C, D, r]
    ring
  have hrc : Continuous r := continuous_rho_STR02950 h u.isC2.2.1.continuous
  have huv : Continuous (deriv u.val) := u.isC2.2.2.1.continuous
  have hvv : Continuous v.val := v.isC2.2.1.continuous
  have hvd : Continuous (deriv v.val) := v.isC2.2.2.1.continuous
  have hvdd : Continuous (deriv (deriv v.val)) := v.isC2.2.2.2.1
  have hwv : Continuous w.val := w.isC2.2.1.continuous
  have hwd : Continuous (deriv w.val) := w.isC2.2.2.1.continuous
  have hA : Continuous A := by dsimp only [A]; fun_prop
  have hB : Continuous B := by dsimp only [B]; fun_prop
  have hC : Continuous C := by dsimp only [C]; fun_prop
  have hD' : Continuous D := by dsimp only [D]; fun_prop
  rw [hf, meanT_comb4_STR02950 hA hB hC hD']
  have hA0 : meanT_STR02901 A = 0 := weighted_ibp h u v w
  rw [hA0, hc]
  dsimp only [B, C, D, r]
  ring

/-- Specialization to the SAME actual ordinary optimizer and its genuine chart. The rate
is the actual physical quotient divided by `4*pi^2`, and criticality is proved by T62. -/
theorem ordinaryOptimizer_hessian (h : ℝ) (ρ : AbsoluteDensity 1)
    (hpos : 0 < ordinaryEntropy h ρ)
    (hmin : ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
      ordinaryFisher h ρ / (2 * ordinaryEntropy h ρ) ≤
        ordinaryFisher h ρ' / (2 * ordinaryEntropy h ρ'))
    (a b : ℝ) (w : E_STR02969)
    (hrep : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) =
      rhoT_STR02901 h (uT_STR02901 a b (w : PeriodicC2_STR02969).val) (angSec θ))
    (v z : PeriodicC2_STR02969) :
    let r := (str025_quot h ρ).toReal / (4 * Real.pi ^ 2)
    let u := a • cosC2_STR02915 + b • sinC2_STR02915 + (w : PeriodicC2_STR02969)
    fderiv ℝ (fderiv ℝ (JC2_STR02956 h (r - 1))) u v z =
      2 * (meanT_STR02901 (fun t =>
          deriv v.val t * deriv z.val t * rhoT_STR02901 h u.val t) -
        r * (meanT_STR02901 (fun t => v.val t * z.val t * rhoT_STR02901 h u.val t) -
          meanT_STR02901 (fun t => v.val t * rhoT_STR02901 h u.val t) *
            meanT_STR02901 (fun t => z.val t * rhoT_STR02901 h u.val t))) := by
  let r := (str025_quot h ρ).toReal / (4 * Real.pi ^ 2)
  let u := a • cosC2_STR02915 + b • sinC2_STR02915 + (w : PeriodicC2_STR02969)
  have hcrit := (str029_62_global_optimizer_positive_chart_fully_critical h ρ hpos hmin
    a b (w : PeriodicC2_STR02969).val (w : PeriodicC2_STR02969).isC2
    (inE_of_mem_STR02924 w) hrep r (str025_quot_toReal_STR02901 h ρ)).2.1
  have hcritU : ∀ t, gradG_STR02950 h (r - 1) u.val t = 0 := by
    simpa only [u, paramMap_val_STR02915] using hcrit
  have hr : 1 + (r - 1) = r := by ring
  simpa only [hr] using hessian_JC2_eq_weighted_form h (r - 1) u v z hcritU

end DGPS.Examples.ThreeSpeciesCircle.OrdinarySecondVariation
