import DGPS.Frontier.STR029.T02
import DGPS.Frontier.STR029.T24
import DGPS.Frontier.STR029.T04

/-!
# The full weak-H1 positive complement for the ordinary-root Hessian

The angular normalized log-density second variation is twice the quadratic form below.
This file proves its quantitative complementary bound from the actual weak Fourier
inequality. No strict root Poincare inequality or full Hessian identification is assumed.
-/

noncomputable section
open MeasureTheory Set Real Filter
open DGPS.Frontier.STR029
open scoped ContDiff Topology

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The angular half-Hessian form at a probability density, evaluated on a weak H1 tangent. -/
noncomputable def ordinaryRootHessianQuadratic (σ : ℝ → ℝ) (a : ℝ)
    (w g : ℝ → ℝ) : ℝ :=
  normInt_STR02933 (fun t => σ t * g t ^ 2) -
    a * (normInt_STR02933 (fun t => σ t * w t ^ 2) -
      (normInt_STR02933 (fun t => σ t * w t)) ^ 2)

/-- Coarse actual-density bounds give a uniform positive form on the full Fourier
complement. The weak derivative is explicit and all three low Haar modes are removed. -/
theorem ordinaryRootHessian_complement_lower (σ : ℝ → ℝ) (hσ : Measurable σ)
    (hσlo : ∀ t, (3 / 4 : ℝ) ≤ σ t) (hσhi : ∀ t, σ t ≤ (5 / 4 : ℝ))
    (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ (3 / 2 : ℝ))
    (w g : ℝ → ℝ) (hw : IsPeriodicWeakDerivative_STR02933 w g)
    (h0 : normInt_STR02933 w = 0)
    (hc : normInt_STR02933 (fun t => w t * Real.cos t) = 0)
    (hs : normInt_STR02933 (fun t => w t * Real.sin t) = 0) :
    (9 / 40 : ℝ) * normInt_STR02933 (fun t => g t ^ 2 + w t ^ 2) ≤
      ordinaryRootHessianQuadratic σ a w g := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π))
  have hw2 : Integrable (fun t => w t ^ 2) μ := hw.1.2.integrable_sq
  have hg2 : Integrable (fun t => g t ^ 2) μ := hw.2.1.2.integrable_sq
  have hσabs : ∀ t, ‖σ t‖ ≤ (5 / 4 : ℝ) := by
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hσlo t])]
    exact hσhi t
  have hsg : Integrable (fun t => σ t * g t ^ 2) μ := by
    have h := hg2.mul_bdd (c := (5 / 4 : ℝ)) hσ.aestronglyMeasurable
      (Eventually.of_forall hσabs)
    simpa only [mul_comm] using h
  have hsw : Integrable (fun t => σ t * w t ^ 2) μ := by
    have h := hw2.mul_bdd (c := (5 / 4 : ℝ)) hσ.aestronglyMeasurable
      (Eventually.of_forall hσabs)
    simpa only [mul_comm] using h
  have hmono : ∀ {f k : ℝ → ℝ}, Integrable f μ → Integrable k μ →
      (∀ t, f t ≤ k t) → normInt_STR02933 f ≤ normInt_STR02933 k := by
    intro f k hf hk hfk
    exact mul_le_mul_of_nonneg_left (integral_mono hf hk hfk) (by positivity)
  have hD : (3 / 4 : ℝ) * normInt_STR02933 (fun t => g t ^ 2) ≤
      normInt_STR02933 (fun t => σ t * g t ^ 2) := by
    rw [← normInt_mul_const_STR02933]
    exact hmono (hg2.const_mul _) hsg fun t =>
      mul_le_mul_of_nonneg_right (hσlo t) (sq_nonneg _)
  have hL : normInt_STR02933 (fun t => σ t * w t ^ 2) ≤
      (5 / 4 : ℝ) * normInt_STR02933 (fun t => w t ^ 2) := by
    rw [← normInt_mul_const_STR02933]
    exact hmono hsw (hw2.const_mul _) fun t =>
      mul_le_mul_of_nonneg_right (hσhi t) (sq_nonneg _)
  have hL0 : 0 ≤ normInt_STR02933 (fun t => w t ^ 2) := by
    unfold normInt_STR02933
    exact mul_nonneg (by positivity) (integral_nonneg fun t => sq_nonneg _)
  have hsL0 : 0 ≤ normInt_STR02933 (fun t => σ t * w t ^ 2) := by
    unfold normInt_STR02933
    exact mul_nonneg (by positivity) (integral_nonneg fun t =>
      mul_nonneg (by linarith [hσlo t]) (sq_nonneg _))
  have haL : a * normInt_STR02933 (fun t => σ t * w t ^ 2) ≤
      (3 / 2 : ℝ) * ((5 / 4 : ℝ) * normInt_STR02933 (fun t => w t ^ 2)) :=
    mul_le_mul ha hL hsL0 (by norm_num)
  have hFourier := (str029_02_complementary_fourier_quadratic_inequalities w g hw h0 hc hs).1
  have hsub : normInt_STR02933 (fun t => g t ^ 2 - w t ^ 2) =
      normInt_STR02933 (fun t => g t ^ 2) - normInt_STR02933 (fun t => w t ^ 2) := by
    unfold normInt_STR02933
    rw [integral_sub hg2 hw2]
    ring
  rw [hsub] at hFourier
  have hadd : normInt_STR02933 (fun t => g t ^ 2 + w t ^ 2) =
      normInt_STR02933 (fun t => g t ^ 2) + normInt_STR02933 (fun t => w t ^ 2) := by
    unfold normInt_STR02933
    rw [integral_add hg2 hw2]
    ring
  rw [hadd]
  unfold ordinaryRootHessianQuadratic
  have hmean := mul_nonneg ha0 (sq_nonneg (normInt_STR02933 (fun t => σ t * w t)))
  nlinarith


/-- Differentiating the actual range equation makes the actual graph tangent Hessian-
orthogonal to every fixed C2 complement direction. The graph witness is preserved. -/
theorem ordinaryRangeGraph_hessian_complement_zero
    {U : Set Par_STR02916} {V : Set E_STR02969} {ψ : Par_STR02916 → E_STR02969}
    (hU : IsOpen U) (hψC : ContDiffOn ℝ ∞ ψ U)
    (hψV : ∀ p ∈ U, ψ p ∈ V)
    (hR : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p)
    (h γ : ℝ) (x v : ℝ × ℝ)
    (hx : iota_STR02956 (h, γ) x ∈ U) (w : E_STR02969) :
    fderiv ℝ (fderiv ℝ (JC2_STR02956 h γ)) (Lamp_STR02956 ψ (h, γ) x)
      (fderiv ℝ (Lamp_STR02956 ψ (h, γ)) x v) (w : PeriodicC2_STR02969) = 0 := by
  let L := Lamp_STR02956 ψ (h, γ)
  let F : (ℝ × ℝ) → ℝ := fun y =>
    fderiv ℝ (JC2_STR02956 h γ) (L y) (w : PeriodicC2_STR02969)
  have hopen := isOpen_iota_preimage_STR02956 hU (h, γ)
  have hzero : F =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    dsimp only [F, L]
    rw [fderiv_JC2_STR02924]
    have hLv : (Lamp_STR02956 ψ (h, γ) y).val =
        uT_STR02901 y.1 y.2
          ((ψ (y.1, y.2, h, γ) : E_STR02969) : PeriodicC2_STR02969).val := rfl
    rw [hLv]
    exact meanT_mul_inE_STR02924 (continuous_val_STR02924 w)
      (inE_of_mem_STR02924 w) (projP_gradG_zero_STR02924 hψV hR y.1 y.2 h γ hy)
  have hL : DifferentiableAt ℝ L x :=
    ((Lamp_contDiffOn_STR02956 hψC (h, γ)).contDiffAt
      (hopen.mem_nhds hx)).differentiableAt (by simp)
  have hDF : Differentiable ℝ (fderiv ℝ (JC2_STR02956 h γ)) :=
    ((JC2_smooth_STR02956 h γ).fderiv_right (m := 1) (by simp)).differentiable (by simp)
  have hd := (((hDF (L x)).hasFDerivAt.clm_apply
    (hasFDerivAt_const (w : PeriodicC2_STR02969) (L x))).comp x hL.hasFDerivAt)
  have he := congrArg (fun A => A v) hd.fderiv
  change fderiv ℝ F x v = _ at he
  rw [hzero.fderiv_eq, (hasFDerivAt_const (0 : ℝ) x).fderiv] at he
  have hz : (0 : ℝ) =
      fderiv ℝ (fderiv ℝ (JC2_STR02956 h γ)) (L x) (fderiv ℝ L x v)
        (w : PeriodicC2_STR02969) := by
    simpa only [zero_apply, ContinuousLinearMap.comp_apply, add_apply,
      ContinuousLinearMap.flip_apply, map_zero, zero_add, add_zero] using he
  exact hz.symm


/-- At an actual critical chart, the reduced Hessian is the full chart Hessian on the
actual graph tangents. The second derivative of the graph drops out by criticality. -/
theorem ordinaryRangeGraph_reduced_hessian_at_critical
    {U : Set Par_STR02916} {ψ : Par_STR02916 → E_STR02969}
    (hU : IsOpen U) (hψC : ContDiffOn ℝ ∞ ψ U)
    (h γ : ℝ) (x v z : ℝ × ℝ) (hx : iota_STR02956 (h, γ) x ∈ U)
    (hcrit : ∀ t, gradG_STR02950 h γ (Lamp_STR02956 ψ (h, γ) x).val t = 0) :
    fderiv ℝ (fderiv ℝ (fun y => Fred_STR02956 ψ y (h, γ))) x v z =
      fderiv ℝ (fderiv ℝ (JC2_STR02956 h γ)) (Lamp_STR02956 ψ (h, γ) x)
        (fderiv ℝ (Lamp_STR02956 ψ (h, γ)) x v)
        (fderiv ℝ (Lamp_STR02956 ψ (h, γ)) x z) := by
  let L := Lamp_STR02956 ψ (h, γ)
  let F := fun y => Fred_STR02956 ψ y (h, γ)
  let c := fun y => fderiv ℝ (JC2_STR02956 h γ) (L y)
  let d := fun y => fderiv ℝ L y z
  have hopen := isOpen_iota_preimage_STR02956 hU (h, γ)
  have hLc : ContDiffAt ℝ ∞ L x :=
    (Lamp_contDiffOn_STR02956 hψC (h, γ)).contDiffAt (hopen.mem_nhds hx)
  have hL : DifferentiableAt ℝ L x := hLc.differentiableAt (by simp)
  have hDL : DifferentiableAt ℝ (fderiv ℝ L) x :=
    (hLc.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hDF : Differentiable ℝ (fderiv ℝ (JC2_STR02956 h γ)) :=
    ((JC2_smooth_STR02956 h γ).fderiv_right (m := 1) (by simp)).differentiable (by simp)
  have hc := (hDF (L x)).hasFDerivAt.comp x hL.hasFDerivAt
  have hd := hDL.hasFDerivAt.clm_apply (hasFDerivAt_const z x)
  have hprod := hc.clm_apply hd
  have hfun : (fun y => fderiv ℝ F y z) =ᶠ[𝓝 x] fun y => c y (d y) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    have hLy : DifferentiableAt ℝ L y :=
      ((Lamp_contDiffOn_STR02956 hψC (h, γ)).contDiffAt
        (hopen.mem_nhds hy)).differentiableAt (by simp)
    have hJ : DifferentiableAt ℝ (JC2_STR02956 h γ) (L y) :=
      ((JC2_smooth_STR02956 h γ).differentiable (by simp)) _
    change fderiv ℝ (fun y => Fred_STR02956 ψ y (h, γ)) y z = _
    rw [Fred_fun_eq_STR02956, fderiv_comp y hJ hLy]
    rfl
  have hJzero : fderiv ℝ (JC2_STR02956 h γ) (L x) = 0 := by
    ext q
    rw [fderiv_JC2_STR02924]
    simp [L, hcrit, meanT_STR02901]
  have hFc : ContDiffAt ℝ ∞ F x :=
    (Fred_contDiffOn_STR02956 hψC (h, γ)).contDiffAt (hopen.mem_nhds hx)
  have hFDF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hFc.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have he := congrArg (fun A => A v) hprod.fderiv
  change fderiv ℝ (fun y => c y (d y)) x v = _ at he
  rw [← hfun.fderiv_eq, fderiv_clm_apply hFDF (differentiableAt_const z)] at he
  simp only [(hasFDerivAt_const z x).fderiv] at he
  simp only [Function.comp_apply] at he
  rw [hJzero] at he
  simpa only [zero_apply, ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.flip_apply, map_zero, zero_add, add_zero] using he


/-- Exact normalization bounds for the actual exponential chart. -/
theorem ordinaryChart_density_bounds_of_exponent_bound (h ε : ℝ) (u : ℝ → ℝ)
    (hu : Continuous u) (hb : ∀ t, |h * Real.cos (3 * t) + u t| ≤ ε) :
    ∀ t, Real.exp (-2 * ε) ≤ rhoT_STR02901 h u t ∧
      rhoT_STR02901 h u t ≤ Real.exp (2 * ε) := by
  let P : ℝ → ℝ := fun t => h * Real.cos (3 * t) + u t
  have hP : Continuous P := by dsimp [P]; fun_prop
  have hZ := normInt_bounds_STR02904 (Real.continuous_exp.comp hP)
    (fun t => Real.exp_le_exp.mpr (neg_le_of_abs_le (hb t)))
    (fun t => Real.exp_le_exp.mpr (le_of_abs_le (hb t)))
  change Real.exp (-ε) ≤ meanT_STR02901 (fun t => Real.exp (P t)) ∧
    meanT_STR02901 (fun t => Real.exp (P t)) ≤ Real.exp ε at hZ
  have hZpos : 0 < meanT_STR02901 (fun t => Real.exp (P t)) :=
    (Real.exp_pos _).trans_le hZ.1
  intro t
  change Real.exp (-2 * ε) ≤ Real.exp (P t) / meanT_STR02901 (fun t => Real.exp (P t)) ∧
    Real.exp (P t) / meanT_STR02901 (fun t => Real.exp (P t)) ≤ Real.exp (2 * ε)
  constructor
  · apply (le_div_iff₀ hZpos).mpr
    calc
      _ ≤ Real.exp (-2 * ε) * Real.exp ε :=
        mul_le_mul_of_nonneg_left hZ.2 (Real.exp_pos _).le
      _ = Real.exp (-ε) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (neg_le_of_abs_le (hb t))
  · apply (div_le_iff₀ hZpos).mpr
    calc
      _ ≤ Real.exp ε := Real.exp_le_exp.mpr (le_of_abs_le (hb t))
      _ = Real.exp (2 * ε) * Real.exp (-ε) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hZ.1 (Real.exp_pos _).le


/-- The weighted mean in the covariance form is a genuine finite integral on the full
weak H1 domain, including for representatives which are merely L2. -/
theorem ordinaryRoot_weightedMean_integrable (σ : ℝ → ℝ) (hσ : Measurable σ)
    (C : ℝ) (hσC : ∀ t, ‖σ t‖ ≤ C) (w g : ℝ → ℝ)
    (hw : IsPeriodicWeakDerivative_STR02933 w g) :
    Integrable (fun t => σ t * w t) (volume.restrict (Ioc 0 (2 * π))) := by
  have hi := integrable_of_memLp_STR02934 hw.1.2
  have h := hi.mul_bdd (c := C) hσ.aestronglyMeasurable (Eventually.of_forall hσC)
  simpa only [mul_comm] using h

end DGPS.Examples.ThreeSpeciesCircle
