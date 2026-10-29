import DGPS.Foundations.SobolevFourier
import DGPS.Foundations.Entropy
import DGPS.Analysis.CircleMoments
import DGPS.Analysis.PeriodicHeatKernel

open MeasureTheory Set Filter Topology
open scoped ContDiff Real

namespace DGPS.Circle.HeatInformation

/-- A function on `ℝ` viewed on the circle through the section `secT`. -/
noncomputable def toCircle (g : ℝ → ℝ) : Torus 1 → ℝ := fun z => g (SharpLSI.secT z 0)

theorem toCircle_lift {g : ℝ → ℝ} (hg : Function.Periodic g 1) (y : Fin 1 → ℝ) :
    toCircle g (torusLift y) = g (y 0) := by
  unfold toCircle
  have h := congrFun (SharpLSI.liftT_secT (torusLift y)) 0
  simp only [torusLift, SharpLSI.liftT] at h
  have h2 : (((SharpLSI.secT (SharpLSI.liftT y) 0 - y 0 : ℝ)) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub]
    rw [sub_eq_zero]
    exact h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1:ℝ))).mp h2
  have : SharpLSI.secT (SharpLSI.liftT y) 0 = y 0 + n * 1 := by
    simp at hn; linarith
  rw [this]
  exact (hg.int_mul n) (y 0)


theorem isSmoothPeriodic_toCircle {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hper : Function.Periodic g 1) :
    IsSmoothPeriodic (toCircle g) := by
  unfold IsSmoothPeriodic
  have : (toCircle g) ∘ torusLift = fun y : Fin 1 → ℝ => g (y 0) := by
    funext y; exact toCircle_lift hper y
  rw [this]
  exact hg.comp (contDiff_apply ℝ ℝ 0)

theorem fderiv_apply_single {g : ℝ → ℝ} (hg : Differentiable ℝ g) (y : Fin 1 → ℝ) :
    fderiv ℝ (fun y : Fin 1 → ℝ => g (y 0)) y (Pi.single 0 1) = deriv g (y 0) := by
  have h1 : HasFDerivAt (fun y : Fin 1 → ℝ => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) y :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
  have h2 := (hg (y 0)).hasDerivAt.comp_hasFDerivAt y h1
  have h3 : fderiv ℝ (fun y : Fin 1 → ℝ => g (y 0)) y = deriv g (y 0) • ContinuousLinearMap.proj 0 :=
    h2.fderiv
  rw [h3]
  simp

/-- Wirtinger's inequality on the circle via the Fourier identity of FOU004. -/
theorem wirtinger {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hper : Function.Periodic g 1)
    (hmean : ∫ x in (0:ℝ)..1, g x = 0) :
    4 * π ^ 2 * ∫ x in (0:ℝ)..1, g x ^ 2 ≤ ∫ x in (0:ℝ)..1, deriv g x ^ 2 := by
  set u := toCircle g with hu
  have hus : IsSmoothPeriodic u := isSmoothPeriodic_toCircle hg hper
  have hw := hus.isWeakGradient
  have h1 := hasSum_gradWeight_weakGradient hw
  have h2 := hasSum_sq_fourierCoeff hw.memLp
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hgc : Continuous g := hg.continuous
  have hdc : Continuous (deriv g) := (contDiff_infty_iff_deriv.mp hg).2.continuous
  have e1 : ∫ x, u x ^ 2 ∂haar 1 = ∫ x in (0:ℝ)..1, g x ^ 2 := by
    have := Analysis.CircleMoments.integral_haar_secT (G := fun y : Fin 1 → ℝ => g (y 0) ^ 2)
      ((hgc.comp (continuous_apply 0)).pow 2).measurable
    simpa [hu, toCircle] using this
  have e2 : ∫ x, ‖smoothGrad u x‖ ^ 2 ∂haar 1 = ∫ x in (0:ℝ)..1, deriv g x ^ 2 := by
    have := Analysis.CircleMoments.integral_haar_secT
      (G := fun y : Fin 1 → ℝ => deriv g (y 0) ^ 2)
      ((hdc.comp (continuous_apply 0)).pow 2).measurable
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show ‖smoothGrad u x‖ ^ 2 = deriv g (SharpLSI.secT x 0) ^ 2
    rw [tangent_norm_sq]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, smoothGrad_apply]
    unfold coordPartial
    have hc : (u ∘ torusLift) = fun y : Fin 1 → ℝ => g (y 0) := by
      funext y; exact toCircle_lift hper y
    rw [hc, fderiv_apply_single hgd]
  have e0 : fourierCoeff u 0 = 0 := by
    unfold fourierCoeff UnitAddTorus.mFourierCoeff
    simp only [neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_smul]
    rw [integral_complex_ofReal]
    have := Analysis.CircleMoments.integral_haar_secT (G := fun y : Fin 1 → ℝ => g (y 0))
      (hgc.comp (continuous_apply 0)).measurable
    have e3 : ∫ x, u x ∂haar 1 = 0 := by simpa [hu, toCircle, hmean] using this
    have e4 : ((∫ x, u x ∂haar 1 : ℝ) : ℂ) = 0 := by rw [e3]; simp
    change ((∫ x, u x ∂(Measure.pi fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle)) : ℝ) : ℂ) = 0
    rw [← haar_eq_pi_haarAddCircle]
    exact e4
  rw [e1] at h2
  rw [e2] at h1
  have hle : ∀ k : Fin 1 → ℤ, 4 * π ^ 2 * ‖fourierCoeff u k‖ ^ 2 ≤ gradWeight k * ‖fourierCoeff u k‖ ^ 2 := by
    intro k
    by_cases hk : k = 0
    · subst hk; rw [e0]; simp
    · have hk0 : k 0 ≠ 0 := fun h => hk (by funext i; simpa [Subsingleton.elim i 0] using h)
      have : (1:ℝ) ≤ ((k 0 : ℤ) : ℝ) ^ 2 := by
        have : (1:ℤ) ≤ (k 0) ^ 2 := by
          have := Int.one_le_abs hk0
          nlinarith [sq_abs (k 0)]
        exact_mod_cast this
      have hw : 4 * π ^ 2 ≤ gradWeight k := by
        unfold gradWeight
        simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
        nlinarith [sq_nonneg π]
      exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)
  have := hasSum_le hle (h2.mul_left (4 * π ^ 2)) h1
  exact this

section Core

lemma deriv_inf {g : ℝ → ℝ} (h : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (deriv g) :=
  (contDiff_infty_iff_deriv.mp h).2

lemma hasDerivAt_inf {g : ℝ → ℝ} (h : ContDiff ℝ ∞ g) (x : ℝ) : HasDerivAt g (deriv g x) x :=
  ((h.differentiable (by simp)) x).hasDerivAt

lemma periodic_deriv {g : ℝ → ℝ} (h : Function.Periodic g 1) : Function.Periodic (deriv g) 1 := by
  intro x
  have h1 := deriv_comp_add_const (f := g) (a := (1:ℝ)) (x := x)
  have e : (fun y => g (y + 1)) = g := funext h
  rw [e] at h1
  exact h1.symm

lemma integral_hasDerivAt_periodic {G G' : ℝ → ℝ} (hG : ∀ x, HasDerivAt G (G' x) x)
    (hc : Continuous G') (hper : Function.Periodic G 1) : ∫ x in (0:ℝ)..1, G' x = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hG x) (hc.intervalIntegrable _ _)]
  have := hper 0
  simp only [zero_add] at this
  rw [this]; simp

/-- A smooth, periodic, positive function on `ℝ`. -/
structure GoodFn (q : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ q
  periodic : Function.Periodic q 1
  pos : ∀ x, 0 < q x

lemma exists_sqrt {f : ℝ → ℝ} (h : GoodFn f) :
    ∃ q, GoodFn q ∧ f = fun x => q x ^ 2 := by
  refine ⟨fun x => Real.sqrt (f x), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact h.smooth.sqrt (fun x => (h.pos x).ne')
  · intro x; simp only [h.periodic x]
  · intro x; exact Real.sqrt_pos.mpr (h.pos x)
  · funext x; simp [Real.sq_sqrt (h.pos x).le]

lemma f_derivs {q : ℝ → ℝ} (h : GoodFn q) :
    deriv (fun x => q x ^ 2) = (fun x => 2 * q x * deriv q x) ∧
    deriv (deriv (fun x => q x ^ 2)) =
      fun x => 2 * deriv q x ^ 2 + 2 * q x * deriv (deriv q) x := by
  have h1 : deriv (fun x => q x ^ 2) = (fun x => 2 * q x * deriv q x) := by
    funext x
    have := (hasDerivAt_inf h.smooth x).fun_pow 2
    rw [this.deriv]
    norm_num
  refine ⟨h1, ?_⟩
  rw [h1]
  funext x
  have a := (HasDerivAt.const_mul (2:ℝ) (hasDerivAt_inf h.smooth x)).fun_mul
    (hasDerivAt_inf (deriv_inf h.smooth) x)
  exact a.deriv.trans (by ring)

lemma core_Y {q : ℝ → ℝ} (h : GoodFn q) :
    3 * ∫ x in (0:ℝ)..1, deriv q x ^ 2 * deriv (deriv q) x / q x
      = ∫ x in (0:ℝ)..1, deriv q x ^ 4 / q x ^ 2 := by
  have h1 := deriv_inf h.smooth
  have h2 := deriv_inf h1
  have hq := h.smooth.continuous
  have h1c := h1.continuous
  have h2c := h2.continuous
  have hq0 : ∀ x, q x ≠ 0 := fun x => (h.pos x).ne'
  have hca : Continuous fun x => deriv q x ^ 2 * deriv (deriv q) x / q x :=
    ((h1c.pow 2).mul h2c).div hq hq0
  have hcb : Continuous fun x => deriv q x ^ 4 / q x ^ 2 :=
    (h1c.pow 4).div (hq.pow 2) (fun x => pow_ne_zero 2 (hq0 x))
  have hd : ∀ x, HasDerivAt (fun x => deriv q x ^ 3 / q x)
      (3 * (deriv q x ^ 2 * deriv (deriv q) x / q x) - deriv q x ^ 4 / q x ^ 2) x := by
    intro x
    have a := ((hasDerivAt_inf h1 x).fun_pow 3).fun_div (hasDerivAt_inf h.smooth x) (hq0 x)
    convert a using 1
    have := hq0 x
    norm_num
    field_simp
  have hp : Function.Periodic (fun x => deriv q x ^ 3 / q x) 1 := by
    intro x
    show deriv q (x + 1) ^ 3 / q (x + 1) = deriv q x ^ 3 / q x
    rw [periodic_deriv h.periodic x, h.periodic x]
  have hcm : Continuous fun x => 3 * (deriv q x ^ 2 * deriv (deriv q) x / q x) :=
    continuous_const.mul hca
  have := integral_hasDerivAt_periodic hd (hcm.sub hcb) hp
  rw [intervalIntegral.integral_sub (hcm.intervalIntegrable _ _)
    (hcb.intervalIntegrable _ _), intervalIntegral.integral_const_mul] at this
  linarith

lemma core_W {q : ℝ → ℝ} (h : GoodFn q) :
    4 * π ^ 2 * ∫ x in (0:ℝ)..1, deriv q x ^ 2
      ≤ ∫ x in (0:ℝ)..1, deriv (deriv q) x ^ 2 := by
  have h1 := deriv_inf h.smooth
  refine wirtinger h1 (periodic_deriv h.periodic) ?_
  exact integral_hasDerivAt_periodic (hasDerivAt_inf h.smooth) h1.continuous h.periodic

lemma core_V {q : ℝ → ℝ} (h : GoodFn q) (hm : ∫ x in (0:ℝ)..1, q x ^ 2 = 1) :
    (∫ x in (0:ℝ)..1, deriv q x ^ 2) ^ 2 ≤ ∫ x in (0:ℝ)..1, deriv q x ^ 4 / q x ^ 2 := by
  have h1 := deriv_inf h.smooth
  have hq := h.smooth.continuous
  have h1c := h1.continuous
  have hq0 : ∀ x, q x ≠ 0 := fun x => (h.pos x).ne'
  set V := ∫ x in (0:ℝ)..1, deriv q x ^ 2 with hV
  have hcb : Continuous fun x => deriv q x ^ 4 / q x ^ 2 :=
    (h1c.pow 4).div (hq.pow 2) (fun x => pow_ne_zero 2 (hq0 x))
  have hcv : Continuous fun x => deriv q x ^ 2 := h1c.pow 2
  have hcq : Continuous fun x => q x ^ 2 := hq.pow 2
  have hc2 : Continuous fun x => 2 * V * deriv q x ^ 2 := continuous_const.mul hcv
  have hc3 : Continuous fun x => V ^ 2 * q x ^ 2 := continuous_const.mul hcq
  have h0 : 0 ≤ ∫ x in (0:ℝ)..1, (deriv q x ^ 2 / q x - V * q x) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun x _ => sq_nonneg _)
  have e : ∀ x, (deriv q x ^ 2 / q x - V * q x) ^ 2
      = deriv q x ^ 4 / q x ^ 2 - 2 * V * deriv q x ^ 2 + V ^ 2 * q x ^ 2 := by
    intro x
    have := hq0 x
    field_simp
    ring
  simp_rw [e] at h0
  rw [intervalIntegral.integral_add (f := fun x => deriv q x ^ 4 / q x ^ 2 - 2 * V * deriv q x ^ 2)
    (g := fun x => V ^ 2 * q x ^ 2) ((hcb.sub hc2).intervalIntegrable _ _)
    (hc3.intervalIntegrable _ _),
    intervalIntegral.integral_sub (hcb.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hm] at h0
  rw [← hV] at h0
  nlinarith

/-- `I = ∫ f'^2 / f`. -/
noncomputable def fisherI (f : ℝ → ℝ) : ℝ := ∫ x in (0:ℝ)..1, deriv f x ^ 2 / f x
/-- `A = ∫ f''^2 / f`. -/
noncomputable def fisherA (f : ℝ → ℝ) : ℝ := ∫ x in (0:ℝ)..1, deriv (deriv f) x ^ 2 / f x
/-- `B = ∫ f'' f'^2 / f^2`. -/
noncomputable def fisherB (f : ℝ → ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1, deriv (deriv f) x * deriv f x ^ 2 / f x ^ 2
/-- `C = ∫ f'^4 / f^3`. -/
noncomputable def fisherC (f : ℝ → ℝ) : ℝ := ∫ x in (0:ℝ)..1, deriv f x ^ 4 / f x ^ 3

lemma core_f {f : ℝ → ℝ} (h : GoodFn f) (hm : ∫ x in (0:ℝ)..1, f x = 1) :
    3 * fisherB f = 2 * fisherC f ∧
      4 * π ^ 2 * fisherI f + 5 / 12 * fisherC f ≤ fisherA f ∧ fisherI f ^ 2 ≤ fisherC f := by
  obtain ⟨q, hq, rfl⟩ := exists_sqrt h
  have hY := core_Y hq
  have hW := core_W hq
  have hV := core_V hq hm
  have h1 := deriv_inf hq.smooth
  have h2 := deriv_inf h1
  have hqc := hq.smooth.continuous
  have h1c := h1.continuous
  have h2c := h2.continuous
  have hq0 : ∀ x, q x ≠ 0 := fun x => (hq.pos x).ne'
  have cX : Continuous fun x => deriv q x ^ 4 / q x ^ 2 :=
    (h1c.pow 4).div (hqc.pow 2) (fun x => pow_ne_zero 2 (hq0 x))
  have cY : Continuous fun x => deriv q x ^ 2 * deriv (deriv q) x / q x :=
    ((h1c.pow 2).mul h2c).div hqc hq0
  have cW : Continuous fun x => deriv (deriv q) x ^ 2 := h2c.pow 2
  have cV : Continuous fun x => deriv q x ^ 2 := h1c.pow 2
  have cX' : Continuous fun x => 8 * (deriv q x ^ 4 / q x ^ 2) := continuous_const.mul cX
  have cY' : Continuous fun x => 8 * (deriv q x ^ 2 * deriv (deriv q) x / q x) :=
    continuous_const.mul cY
  have cX4 : Continuous fun x => 4 * (deriv q x ^ 4 / q x ^ 2) := continuous_const.mul cX
  have cW' : Continuous fun x => 4 * deriv (deriv q) x ^ 2 := continuous_const.mul cW
  have eC : fisherC (fun x => q x ^ 2) = 16 * ∫ x in (0:ℝ)..1, deriv q x ^ 4 / q x ^ 2 := by
    unfold fisherC
    rw [(f_derivs hq).1, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    have := hq0 x
    simp only
    field_simp
    ring
  have eI : fisherI (fun x => q x ^ 2) = 4 * ∫ x in (0:ℝ)..1, deriv q x ^ 2 := by
    unfold fisherI
    rw [(f_derivs hq).1, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    have := hq0 x
    simp only
    field_simp
    ring
  have eB : fisherB (fun x => q x ^ 2) = 8 * (∫ x in (0:ℝ)..1, deriv q x ^ 4 / q x ^ 2)
      + 8 * ∫ x in (0:ℝ)..1, deriv q x ^ 2 * deriv (deriv q) x / q x := by
    unfold fisherB
    rw [(f_derivs hq).2, (f_derivs hq).1, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (cX'.intervalIntegrable _ _) (cY'.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    have := hq0 x
    simp only
    field_simp
    ring
  have eA : fisherA (fun x => q x ^ 2) = 4 * (∫ x in (0:ℝ)..1, deriv q x ^ 4 / q x ^ 2)
      + 8 * (∫ x in (0:ℝ)..1, deriv q x ^ 2 * deriv (deriv q) x / q x)
      + 4 * ∫ x in (0:ℝ)..1, deriv (deriv q) x ^ 2 := by
    unfold fisherA
    rw [(f_derivs hq).2, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (f := fun x => 4 * (deriv q x ^ 4 / q x ^ 2))
        (g := fun x => 8 * (deriv q x ^ 2 * deriv (deriv q) x / q x))
        (cX4.intervalIntegrable _ _) (cY'.intervalIntegrable _ _),
      ← intervalIntegral.integral_add
        (f := fun x => 4 * (deriv q x ^ 4 / q x ^ 2) + 8 * (deriv q x ^ 2 * deriv (deriv q) x / q x))
        (g := fun x => 4 * deriv (deriv q) x ^ 2)
        ((cX4.add cY').intervalIntegrable _ _) (cW'.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    have := hq0 x
    simp only
    field_simp
    ring
  rw [eA, eB, eC, eI]
  refine ⟨by linarith, by nlinarith, by nlinarith⟩


lemma core_H' {f : ℝ → ℝ} (h : GoodFn f) :
    ∫ x in (0:ℝ)..1, deriv (deriv f) x * (Real.log (f x) + 1) = -fisherI f := by
  have h1 := deriv_inf h.smooth
  have h2 := deriv_inf h1
  have hf := h.smooth.continuous
  have h1c := h1.continuous
  have h2c := h2.continuous
  have hf0 : ∀ x, f x ≠ 0 := fun x => (h.pos x).ne'
  have hlog : Continuous fun x => Real.log (f x) := hf.log hf0
  have cA : Continuous fun x => deriv (deriv f) x * Real.log (f x) := h2c.mul hlog
  have cI : Continuous fun x => deriv f x ^ 2 / f x := (h1c.pow 2).div hf hf0
  have hd : ∀ x, HasDerivAt (fun x => deriv f x * Real.log (f x))
      (deriv (deriv f) x * Real.log (f x) + deriv f x ^ 2 / f x) x := by
    intro x
    have a := (hasDerivAt_inf h1 x).fun_mul ((hasDerivAt_inf h.smooth x).log (hf0 x))
    convert a using 1
    field_simp
  have hp : Function.Periodic (fun x => deriv f x * Real.log (f x)) 1 := by
    intro x
    show deriv f (x + 1) * Real.log (f (x + 1)) = deriv f x * Real.log (f x)
    rw [periodic_deriv h.periodic x, h.periodic x]
  have h0 := integral_hasDerivAt_periodic hd (cA.add cI) hp
  have h00 := integral_hasDerivAt_periodic (hasDerivAt_inf h1) h2c (periodic_deriv h.periodic)
  rw [intervalIntegral.integral_add (cA.intervalIntegrable _ _) (cI.intervalIntegrable _ _)] at h0
  have e : ∀ x, deriv (deriv f) x * (Real.log (f x) + 1)
      = deriv (deriv f) x * Real.log (f x) + deriv (deriv f) x := fun x => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_add (cA.intervalIntegrable _ _) (h2c.intervalIntegrable _ _), h00]
  unfold fisherI
  linarith

lemma core_I' {f : ℝ → ℝ} (h : GoodFn f) :
    ∫ x in (0:ℝ)..1, (2 * deriv f x * deriv (deriv (deriv f)) x / f x
      - deriv f x ^ 2 * deriv (deriv f) x / f x ^ 2) = -2 * fisherA f + fisherB f := by
  have h1 := deriv_inf h.smooth
  have h2 := deriv_inf h1
  have h3 := deriv_inf h2
  have hf := h.smooth.continuous
  have h1c := h1.continuous
  have h2c := h2.continuous
  have h3c := h3.continuous
  have hf0 : ∀ x, f x ≠ 0 := fun x => (h.pos x).ne'
  have cA : Continuous fun x => deriv (deriv f) x ^ 2 / f x := (h2c.pow 2).div hf hf0
  have cB : Continuous fun x => deriv (deriv f) x * deriv f x ^ 2 / f x ^ 2 :=
    (h2c.mul (h1c.pow 2)).div (hf.pow 2) (fun x => pow_ne_zero 2 (hf0 x))
  have cA' : Continuous fun x => 2 * (deriv (deriv f) x ^ 2 / f x) := continuous_const.mul cA
  have cG : Continuous fun x => 2 * deriv f x * deriv (deriv (deriv f)) x / f x
      - deriv f x ^ 2 * deriv (deriv f) x / f x ^ 2 :=
    ((continuous_const.mul h1c).mul h3c).div hf hf0 |>.sub
      ((h1c.pow 2).mul h2c |>.div (hf.pow 2) (fun x => pow_ne_zero 2 (hf0 x)))
  have hd : ∀ x, HasDerivAt (fun x => 2 * deriv f x * deriv (deriv f) x / f x)
      ((2 * deriv f x * deriv (deriv (deriv f)) x / f x
        - deriv f x ^ 2 * deriv (deriv f) x / f x ^ 2)
        - deriv (deriv f) x * deriv f x ^ 2 / f x ^ 2 + 2 * (deriv (deriv f) x ^ 2 / f x)) x := by
    intro x
    have a := (((hasDerivAt_inf h1 x).const_mul (2:ℝ)).fun_mul (hasDerivAt_inf h2 x)).fun_div
      (hasDerivAt_inf h.smooth x) (hf0 x)
    convert a using 1
    have := hf0 x
    field_simp
    ring
  have hp : Function.Periodic (fun x => 2 * deriv f x * deriv (deriv f) x / f x) 1 := by
    intro x
    show 2 * deriv f (x + 1) * deriv (deriv f) (x + 1) / f (x + 1)
      = 2 * deriv f x * deriv (deriv f) x / f x
    rw [periodic_deriv h.periodic x, periodic_deriv (periodic_deriv h.periodic) x, h.periodic x]
  have h0 := integral_hasDerivAt_periodic hd ((cG.sub cB).add cA') hp
  rw [intervalIntegral.integral_add
    (f := fun x => 2 * deriv f x * deriv (deriv (deriv f)) x / f x
        - deriv f x ^ 2 * deriv (deriv f) x / f x ^ 2 - deriv (deriv f) x * deriv f x ^ 2 / f x ^ 2)
    (g := fun x => 2 * (deriv (deriv f) x ^ 2 / f x))
    ((cG.sub cB).intervalIntegrable _ _) (cA'.intervalIntegrable _ _),
    intervalIntegral.integral_sub
    (f := fun x => 2 * deriv f x * deriv (deriv (deriv f)) x / f x
        - deriv f x ^ 2 * deriv (deriv f) x / f x ^ 2)
    (g := fun x => deriv (deriv f) x * deriv f x ^ 2 / f x ^ 2)
    (cG.intervalIntegrable _ _) (cB.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul] at h0
  unfold fisherA fisherB
  linarith


end Core

section Param

/-- The open half-plane domain `t > 0`. -/
def dom : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ

lemma isOpen_dom : IsOpen dom := isOpen_Ioi.prod isOpen_univ

lemma mem_dom {t x : ℝ} (ht : 0 < t) : (t, x) ∈ dom := ⟨ht, trivial⟩

lemma hasDerivAt_integral_param {F F' : ℝ → ℝ → ℝ} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hF : ∀ t, 0 < t → Continuous (F t))
    (hF' : ContinuousOn (fun z : ℝ × ℝ => F' z.1 z.2) dom)
    (hd : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F s x) (F' t x) t) :
    HasDerivAt (fun t => ∫ x in (0:ℝ)..1, F t x) (∫ x in (0:ℝ)..1, F' t₀ x) t₀ := by
  have hK : IsCompact (Icc (t₀ / 2) (2 * t₀) ×ˢ Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hsub : Icc (t₀ / 2) (2 * t₀) ×ˢ Icc (0:ℝ) 1 ⊆ dom := by
    intro z hz
    exact ⟨lt_of_lt_of_le (by linarith) hz.1.1, trivial⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hF'.mono hsub)
  have hs : Ioo (t₀ / 2) (2 * t₀) ∈ 𝓝 t₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hcont : Continuous (F' t₀) := by
    have h1 : ContinuousOn (fun x : ℝ => F' t₀ x) univ :=
      hF'.comp (Continuous.continuousOn (by fun_prop : Continuous fun x : ℝ => (t₀, x)))
        (fun x _ => mem_dom ht₀)
    exact continuousOn_univ.mp h1
  have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (a := 0) (b := 1)
    (μ := volume) (F := F) (F' := F') (x₀ := t₀) (s := Ioo (t₀ / 2) (2 * t₀))
    (bound := fun _ => M) hs
    ((eventually_gt_nhds ht₀).mono fun t ht => (hF t ht).aestronglyMeasurable)
    ((hF t₀ ht₀).intervalIntegrable _ _) hcont.aestronglyMeasurable
    (Eventually.of_forall fun t ht x hx => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact hM (x, t) ⟨⟨hx.1.le, hx.2.le⟩, ⟨ht.1.le, ht.2⟩⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ x hx => hd x (by linarith [hx.1]) t)
  exact this.2

end Param

section Jets


/-- Smoothness of a space-time function on the open half-plane `t > 0`. -/
def Sm (q : ℝ → ℝ → ℝ) : Prop := ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => q z.1 z.2) dom

/-- Space derivative. -/
noncomputable def dX (q : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := deriv (q t) x

/-- Time derivative. -/
noncomputable def dT (q : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ := deriv (fun s => q s x) t

lemma Sm.contDiffAt {q : ℝ → ℝ → ℝ} (h : Sm q) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => q z.1 z.2) (t, x) :=
  ContDiffOn.contDiffAt h (isOpen_dom.mem_nhds (mem_dom ht))

lemma Sm.hasFDerivAt {q : ℝ → ℝ → ℝ} (h : Sm q) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasFDerivAt (fun z : ℝ × ℝ => q z.1 z.2) (fderiv ℝ (fun z : ℝ × ℝ => q z.1 z.2) (t, x)) (t, x) :=
  ((h.contDiffAt ht x).differentiableAt (by simp)).hasFDerivAt

lemma Sm.hasDerivAt_x {q : ℝ → ℝ → ℝ} (h : Sm q) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (q t) (fderiv ℝ (fun z : ℝ × ℝ => q z.1 z.2) (t, x) (0, 1)) x :=
  (h.hasFDerivAt ht x).comp_hasDerivAt x ((hasDerivAt_const x t).prodMk (hasDerivAt_id' x))

lemma Sm.hasDerivAt_t {q : ℝ → ℝ → ℝ} (h : Sm q) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => q s x) (fderiv ℝ (fun z : ℝ × ℝ => q z.1 z.2) (t, x) (1, 0)) t :=
  HasFDerivAt.comp_hasDerivAt (l := fun z : ℝ × ℝ => q z.1 z.2) t (h.hasFDerivAt ht x)
    ((hasDerivAt_id' t).prodMk (hasDerivAt_const t x))

lemma Sm.dX_eq {q : ℝ → ℝ → ℝ} (h : Sm q) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    dX q t x = fderiv ℝ (fun z : ℝ × ℝ => q z.1 z.2) (t, x) (0, 1) :=
  (h.hasDerivAt_x ht x).deriv

lemma Sm.dT_eq {q : ℝ → ℝ → ℝ} (h : Sm q) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    dT q t x = fderiv ℝ (fun z : ℝ × ℝ => q z.1 z.2) (t, x) (1, 0) :=
  (h.hasDerivAt_t ht x).deriv

lemma Sm.continuousOn {q : ℝ → ℝ → ℝ} (h : Sm q) :
    ContinuousOn (fun z : ℝ × ℝ => q z.1 z.2) dom := ContDiffOn.continuousOn h

lemma Sm.fderiv_apply {q : ℝ → ℝ → ℝ} (h : Sm q) (w : ℝ × ℝ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => fderiv ℝ (fun z : ℝ × ℝ => q z.1 z.2) z w) dom :=
  (ContDiffOn.fderiv_of_isOpen h isOpen_dom (by simp)).clm_apply contDiffOn_const

lemma Sm.smX {q : ℝ → ℝ → ℝ} (h : Sm q) : Sm (dX q) :=
  (h.fderiv_apply (0, 1)).congr (fun z hz => by
    obtain ⟨t, x⟩ := z
    exact h.dX_eq hz.1 x)

lemma Sm.smT {q : ℝ → ℝ → ℝ} (h : Sm q) : Sm (dT q) :=
  (h.fderiv_apply (1, 0)).congr (fun z hz => by
    obtain ⟨t, x⟩ := z
    exact h.dT_eq hz.1 x)

lemma Sm.fderiv_fderiv_apply {q : ℝ → ℝ → ℝ} (h : Sm q) {t : ℝ} (ht : 0 < t) (x : ℝ)
    (v w : ℝ × ℝ) :
    fderiv ℝ (fun z : ℝ × ℝ => fderiv ℝ (fun z : ℝ × ℝ => q z.1 z.2) z w) (t, x) v
      = fderiv ℝ (fderiv ℝ (fun z : ℝ × ℝ => q z.1 z.2)) (t, x) v w := by
  have hc : ContDiffAt ℝ ∞ (fderiv ℝ (fun z : ℝ × ℝ => q z.1 z.2)) (t, x) :=
    (ContDiffOn.fderiv_of_isOpen h isOpen_dom (by simp)).contDiffAt
      (isOpen_dom.mem_nhds (mem_dom ht))
  have hd := hc.differentiableAt (by simp)
  have := fderiv_clm_apply hd (differentiableAt_const w)
  rw [show (fun z : ℝ × ℝ => fderiv ℝ (fun z : ℝ × ℝ => q z.1 z.2) z w)
    = fun z => (fderiv ℝ (fun z : ℝ × ℝ => q z.1 z.2) z) ((fun _ => w) z) from rfl, this]
  simp

lemma Sm.mixed {q : ℝ → ℝ → ℝ} (h : Sm q) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    dT (dX q) t x = dX (dT q) t x := by
  have hX := h.smX
  have hT := h.smT
  have e1 : (fun z : ℝ × ℝ => dX q z.1 z.2) =ᶠ[𝓝 (t, x)]
      fun z => fderiv ℝ (fun z : ℝ × ℝ => q z.1 z.2) z (0, 1) := by
    filter_upwards [isOpen_dom.mem_nhds (mem_dom ht)] with z hz
    exact h.dX_eq hz.1 z.2
  have e2 : (fun z : ℝ × ℝ => dT q z.1 z.2) =ᶠ[𝓝 (t, x)]
      fun z => fderiv ℝ (fun z : ℝ × ℝ => q z.1 z.2) z (1, 0) := by
    filter_upwards [isOpen_dom.mem_nhds (mem_dom ht)] with z hz
    exact h.dT_eq hz.1 z.2
  rw [hX.dT_eq ht x, hT.dX_eq ht x, e1.fderiv_eq, e2.fderiv_eq,
    h.fderiv_fderiv_apply ht x, h.fderiv_fderiv_apply ht x]
  have hs := (h.contDiffAt ht x).isSymmSndFDerivAt (by simp)
  exact hs (1, 0) (0, 1)

lemma Sm.contDiff_slice {q : ℝ → ℝ → ℝ} (h : Sm q) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (q t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (h.contDiffAt ht x).comp x
    ((contDiff_const.prodMk contDiff_id).contDiffAt (x := x) (f := fun y : ℝ => (t, y)))

end Jets
section Entropy

lemma integral_haar_circle {G : ℝ → ℝ} (hG : Continuous G) :
    ∫ z, G (SharpLSI.secT z 0) ∂haar 1 = ∫ s in (0:ℝ)..1, G s := by
  have := Analysis.CircleMoments.integral_haar_secT (G := fun y : Fin 1 → ℝ => G (y 0))
    (hG.measurable.comp (measurable_pi_apply 0))
  simpa using this

lemma entropy_toReal {g : ℝ → ℝ} (hc : Continuous g) (hpos : ∀ x, 0 < g x)
    (hm : ∫ x in (0:ℝ)..1, g x = 1) :
    (homogeneousEntropy (haar 1) (toCircle g)).toReal = ∫ x in (0:ℝ)..1, g x * Real.log (g x) := by
  have hv : ∫ x, toCircle g x ∂haar 1 = 1 := (integral_haar_circle hc).trans hm
  rw [entropy_mass_one hv]
  have hlog : Continuous fun x => g x * Real.log (g x) := hc.mul (hc.log fun x => (hpos x).ne')
  have hφ : Continuous fun s => g s * Real.log (g s) - g s + 1 := (hlog.sub hc).add continuous_const
  have hnn : ∀ s, 0 ≤ g s * Real.log (g s) - g s + 1 := fun s =>
    self_mul_log_sub_add_one_nonneg (hpos s).le
  have hint : Integrable (fun x => g (SharpLSI.secT x 0) * Real.log (g (SharpLSI.secT x 0))
      - g (SharpLSI.secT x 0) + 1) (haar 1) := by
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
      hφ.continuousOn
    refine Integrable.of_bound ?_ M (ae_of_all _ fun z => ?_)
    · exact (hφ.measurable.comp ((measurable_pi_apply 0).comp SharpLSI.measurable_secT)).aestronglyMeasurable
    · have := secT_mem_Icc z
      exact hM _ ⟨by simpa using this.1 0, by simpa using this.2 0⟩
  have h1 : ∫⁻ x, ENNReal.ofReal (toCircle g x * Real.log (toCircle g x) - toCircle g x + 1) ∂haar 1
      = ENNReal.ofReal (∫ x, (g (SharpLSI.secT x 0) * Real.log (g (SharpLSI.secT x 0))
      - g (SharpLSI.secT x 0) + 1) ∂haar 1) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun z => hnn _)]
    rfl
  rw [h1, ENNReal.toReal_ofReal (integral_nonneg fun z => hnn _)]
  rw [integral_haar_circle hφ]
  have hI1 : IntervalIntegrable (fun x => g x * Real.log (g x)) volume 0 1 :=
    hlog.intervalIntegrable _ _
  have hI2 : IntervalIntegrable g volume 0 1 := hc.intervalIntegrable _ _
  rw [intervalIntegral.integral_add (f := fun x => g x * Real.log (g x) - g x) (g := fun _ => (1:ℝ))
    (hI1.sub hI2) intervalIntegrable_const,
    intervalIntegral.integral_sub hI1 hI2, hm]
  simp

end Entropy

section Assembly

lemma goodFn_slice {p : ℝ → ℝ → ℝ} (hsm : Sm p) (hper : ∀ t, 0 < t → Function.Periodic (p t) 1)
    (hpos : ∀ t, 0 < t → ∀ x, 0 < p t x) {t : ℝ} (ht : 0 < t) : GoodFn (p t) :=
  ⟨hsm.contDiff_slice ht, hper t ht, hpos t ht⟩

lemma entropy_hasDerivAt {p : ℝ → ℝ → ℝ} (hsm : Sm p)
    (hper : ∀ t, 0 < t → Function.Periodic (p t) 1)
    (hpos : ∀ t, 0 < t → ∀ x, 0 < p t x) (hmass : ∀ t, 0 < t → ∫ x in (0:ℝ)..1, p t x = 1)
    (hheat : ∀ t, 0 < t → ∀ x, deriv (fun s => p s x) t = deriv (deriv (p t)) x)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => (homogeneousEntropy (haar 1) (toCircle (p s))).toReal)
      (-fisherI (p t)) t := by
  have hmain : HasDerivAt (fun s => ∫ x in (0:ℝ)..1, p s x * Real.log (p s x))
      (∫ x in (0:ℝ)..1, dT p t x * (Real.log (p t x) + 1)) t := by
    refine hasDerivAt_integral_param (F := fun s x => p s x * Real.log (p s x))
      (F' := fun s x => dT p s x * (Real.log (p s x) + 1)) ht ?_ ?_ ?_
    · intro s hs
      have hc := (hsm.contDiff_slice hs).continuous
      exact hc.mul (hc.log fun x => (hpos s hs x).ne')
    · exact hsm.smT.continuousOn.mul
        ((hsm.continuousOn.log fun z hz => (hpos z.1 hz.1 z.2).ne').add continuousOn_const)
    · intro s hs x
      have h := hsm.hasDerivAt_t hs x
      rw [← hsm.dT_eq hs x] at h
      have h2 := h.fun_mul (h.log (hpos s hs x).ne')
      convert h2 using 1
      field_simp [(hpos s hs x).ne']
  have hfun : (fun s => ∫ x in (0:ℝ)..1, p s x * Real.log (p s x)) =ᶠ[𝓝 t]
      fun s => (homogeneousEntropy (haar 1) (toCircle (p s))).toReal := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact (entropy_toReal (hsm.contDiff_slice hs).continuous (hpos s hs) (hmass s hs)).symm
  have hval : ∫ x in (0:ℝ)..1, dT p t x * (Real.log (p t x) + 1) = -fisherI (p t) := by
    rw [← core_H' (goodFn_slice hsm hper hpos ht)]
    refine intervalIntegral.integral_congr fun x _ => ?_
    exact congrArg (· * _) (hheat t ht x)
  rw [← hval]
  exact hmain.congr_of_eventuallyEq hfun.symm

lemma fisherI_hasDerivAt {p : ℝ → ℝ → ℝ} (hsm : Sm p)
    (hper : ∀ t, 0 < t → Function.Periodic (p t) 1)
    (hpos : ∀ t, 0 < t → ∀ x, 0 < p t x)
    (hheat : ∀ t, 0 < t → ∀ x, deriv (fun s => p s x) t = deriv (deriv (p t)) x)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => fisherI (p s)) (-2 * fisherA (p t) + fisherB (p t)) t := by
  have hmain : HasDerivAt (fun s => ∫ x in (0:ℝ)..1, dX p s x ^ 2 / p s x)
      (∫ x in (0:ℝ)..1, (2 * dX p t x * dT (dX p) t x / p t x
        - dX p t x ^ 2 * dT p t x / p t x ^ 2)) t := by
    refine hasDerivAt_integral_param (F := fun s x => dX p s x ^ 2 / p s x)
      (F' := fun s x => 2 * dX p s x * dT (dX p) s x / p s x
        - dX p s x ^ 2 * dT p s x / p s x ^ 2) ht ?_ ?_ ?_
    · intro s hs
      have hc := (hsm.contDiff_slice hs).continuous
      have hd := (deriv_inf (hsm.contDiff_slice hs)).continuous
      exact (hd.pow 2).div hc fun x => (hpos s hs x).ne'
    · have hp := hsm.continuousOn
      have hne : ∀ z ∈ dom, p z.1 z.2 ≠ 0 := fun z hz => (hpos z.1 hz.1 z.2).ne'
      have h1 := hsm.smX.continuousOn
      have h2 := hsm.smX.smT.continuousOn
      have h3 := hsm.smT.continuousOn
      exact (((continuousOn_const.mul h1).mul h2).div hp hne).sub
        (((h1.pow 2).mul h3).div (hp.pow 2) fun z hz => pow_ne_zero 2 (hne z hz))
    · intro s hs x
      have h := hsm.hasDerivAt_t hs x
      rw [← hsm.dT_eq hs x] at h
      have hX := hsm.smX.hasDerivAt_t hs x
      rw [← hsm.smX.dT_eq hs x] at hX
      have h2 := (hX.fun_pow 2).fun_div h (hpos s hs x).ne'
      convert h2 using 1
      field_simp [(hpos s hs x).ne']
      ring
  have hval : ∫ x in (0:ℝ)..1, (2 * dX p t x * dT (dX p) t x / p t x
        - dX p t x ^ 2 * dT p t x / p t x ^ 2) = -2 * fisherA (p t) + fisherB (p t) := by
    rw [← core_I' (goodFn_slice hsm hper hpos ht)]
    refine intervalIntegral.integral_congr fun x _ => ?_
    have hT : dT p t = deriv (deriv (p t)) := funext (hheat t ht)
    have h3 : dT (dX p) t x = deriv (deriv (deriv (p t))) x := by
      rw [hsm.mixed ht x]
      show deriv (dT p t) x = _
      rw [hT]
    simp only [h3, hT]
    rfl
  rw [← hval]
  exact hmain

end Assembly

end DGPS.Circle.HeatInformation

namespace DGPS.Analysis

open DGPS.Circle.HeatInformation

/-- FOU015. For a smooth positive mass-one circle heat solution `p` (`∂ₜ p = ∂ₓₓ p`, on `t > 0`),
with `I = ∫ p'^2/p`, `A = ∫ p''^2/p`, `B = ∫ p'' p'^2/p^2`, `C = ∫ p'^4/p^3`, one has
`H' = -I`, `I' = -2A + B`, `3B = 2C`, `A ≥ a₀ I + 5C/12`, `C ≥ I^2` and hence
`I' ≤ -2 a₀ I - I^2/6` with `a₀ = 4π²`. -/
theorem circle_heat_information_remainder_differential_inequality (p : ℝ → ℝ → ℝ)
    (hsm : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => p z.1 z.2) (Set.Ioi 0 ×ˢ Set.univ))
    (hper : ∀ t, 0 < t → Function.Periodic (p t) 1)
    (hpos : ∀ t, 0 < t → ∀ x, 0 < p t x)
    (hmass : ∀ t, 0 < t → ∫ x in (0:ℝ)..1, p t x = 1)
    (hheat : ∀ t, 0 < t → ∀ x, deriv (fun s => p s x) t = deriv (deriv (p t)) x)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => (homogeneousEntropy (haar 1) (toCircle (p s))).toReal)
        (-fisherI (p t)) t ∧
      HasDerivAt (fun s => fisherI (p s)) (-2 * fisherA (p t) + fisherB (p t)) t ∧
      3 * fisherB (p t) = 2 * fisherC (p t) ∧
      4 * Real.pi ^ 2 * fisherI (p t) + 5 / 12 * fisherC (p t) ≤ fisherA (p t) ∧
      fisherI (p t) ^ 2 ≤ fisherC (p t) ∧
      -2 * fisherA (p t) + fisherB (p t) ≤
        -2 * (4 * Real.pi ^ 2) * fisherI (p t) - fisherI (p t) ^ 2 / 6 := by
  have hs : Sm p := hsm
  obtain ⟨h3, hA, hC⟩ := core_f (goodFn_slice hs hper hpos ht) (hmass t ht)
  refine ⟨entropy_hasDerivAt hs hper hpos hmass hheat ht,
    fisherI_hasDerivAt hs hper hpos hheat ht, h3, hA, hC, ?_⟩
  nlinarith [h3, hA, hC]

end DGPS.Analysis
