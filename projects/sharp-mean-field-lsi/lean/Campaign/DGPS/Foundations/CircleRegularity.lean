import DGPS.Foundations.SobolevEmbedding

/-!
# One-dimensional regularity on the circle (STR025b-i)

On `Torus 1` with the campaign's weak gradient `IsWeakGradient`:

* `circle_duBoisReymond`: a continuous `u` whose weak gradient is a.e. a continuous `g` is `C¹`
  along the circle parametrization `s ↦ torusLift (fun _ => s)` with derivative `g`.
* `circle_H1_holder_half`: an `H¹` function has a continuous representative with
  `|w x - w y| ≤ ‖∇u‖₂ · torusDist x y ^ (1/2)` and `|w x - ∫ u| ≤ ‖∇u‖₂`. This wraps the existing
  `sobolev_embedding_dim_one` / `exists_continuous_rep_one` (Hölder part) and adds the
  mean-oscillation sup bound.
* `circle_H1_tendstoUniformly`: `H¹` convergence gives uniform convergence of continuous
  representatives.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace DGPS

theorem continuous_circleParam : Continuous (fun s : ℝ => (torusLift (fun _ : Fin 1 => s) : Torus 1)) :=
  SharpLSI.continuous_liftT.comp (continuous_pi fun _ => continuous_id)

/-- Fundamental theorem of calculus along the circle for a smooth periodic function. -/
theorem circle_smooth_ftc {φ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) (a b : ℝ) :
    ∫ s in a..b, coordPartial 0 φ (torusLift fun _ : Fin 1 => s) =
      φ (torusLift fun _ : Fin 1 => b) - φ (torusLift fun _ : Fin 1 => a) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_smooth_one hφ s) ?_
  exact ((hφ.continuous_coordPartial 0).comp continuous_circleParam).intervalIntegrable _ _

/-- A continuous square function integrated over a window of length at most one. -/
theorem circle_sq_integral_circle_le {F : Torus 1 → ℝ} (hF : Continuous F) {a b : ℝ} (hab : a ≤ b)
    (hb : b ≤ a + 1) :
    (∫ s in a..b, F (torusLift fun _ : Fin 1 => s)) ^ 2 ≤ ∫ x, F x ^ 2 ∂haar 1 := by
  have hc : Continuous fun s : ℝ => F (torusLift fun _ : Fin 1 => s) :=
    hF.comp continuous_circleParam
  have hc2 : Continuous fun s : ℝ => F (torusLift fun _ : Fin 1 => s) ^ 2 := hc.pow 2
  have h1 := sq_intervalIntegral_le hc hab
  have hper : Function.Periodic (fun s : ℝ => F (torusLift fun _ : Fin 1 => s) ^ 2) 1 := by
    intro s
    simp only [torusLift_one_add]
  have h2 : ∫ s in a..b, F (torusLift fun _ : Fin 1 => s) ^ 2 ≤
      ∫ s in a..(a + 1), F (torusLift fun _ : Fin 1 => s) ^ 2 :=
    intervalIntegral.integral_mono_interval le_rfl hab hb
      (Eventually.of_forall fun s => sq_nonneg _) (hc2.intervalIntegrable _ _)
  have h3 : ∫ s in a..(a + 1), F (torusLift fun _ : Fin 1 => s) ^ 2 =
      ∫ x, F x ^ 2 ∂haar 1 := by
    rw [hper.intervalIntegral_add_eq a 0, integral_haar_one (fun x => F x ^ 2) (hF.pow 2)]
    simp
  have h4 : 0 ≤ ∫ s in a..b, F (torusLift fun _ : Fin 1 => s) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun s _ => sq_nonneg _
  have h5 : (b - a) * ∫ s in a..b, F (torusLift fun _ : Fin 1 => s) ^ 2 ≤
      ∫ s in a..b, F (torusLift fun _ : Fin 1 => s) ^ 2 := by
    nlinarith
  linarith

/-- On `Torus 1` the norm of a tangent vector is the absolute value of its coordinate. -/
theorem circle_eLpNorm_tangent_one {k : Torus 1 → Tangent 1} (hk : MemLp k 2 (haar 1)) :
    eLpNorm k 2 (haar 1) = eLpNorm (fun x => k x 0) 2 (haar 1) := by
  refine eLpNorm_congr_norm_ae hk.aestronglyMeasurable (memLp_coord hk 0).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]

/-- Core uniform convergence statement, with the gradients compared in the coordinate `0`. -/
theorem circle_tendstoUniformly_of_coord {u : ℕ → Torus 1 → ℝ} {g : ℕ → Torus 1 → Tangent 1}
    {u0 : Torus 1 → ℝ} {g0 : Torus 1 → Tangent 1} {U : ℕ → Torus 1 → ℝ} {U0 : Torus 1 → ℝ}
    (hu : ∀ n, IsWeakGradient (u n) (g n)) (h0 : IsWeakGradient u0 g0)
    (hU : ∀ n, Continuous (U n)) (hUa : ∀ n, U n =ᵐ[haar 1] u n)
    (hU0 : Continuous U0) (hU0a : U0 =ᵐ[haar 1] u0)
    (h1 : Tendsto (fun n => eLpNorm (fun x => u n x - u0 x) 2 (haar 1)) atTop (𝓝 0))
    (h2 : Tendsto (fun n => eLpNorm (fun x => g n x 0 - g0 x 0) 2 (haar 1)) atTop (𝓝 0)) :
    TendstoUniformly U U0 atTop := by
  set b : ℕ → ℝ := fun n => (eLpNorm (fun x => u n x - u0 x) 2 (haar 1)).toReal +
    (eLpNorm (fun x => g n x 0 - g0 x 0) 2 (haar 1)).toReal with hb
  have hbt : Tendsto b atTop (𝓝 0) := by
    have e1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    have e2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h2
    rw [ENNReal.toReal_zero] at e1 e2
    simpa using e1.add e2
  have hbd : ∀ n x, |U n x - U0 x| ≤ b n := by
    intro n x
    have hd := (hu n).add (h0.smul (-1))
    obtain ⟨w, hwc, hwa, -, hws⟩ := exists_continuous_rep_one hd
    have hae : (fun y => U n y - U0 y) =ᵐ[haar 1] w := by
      filter_upwards [hUa n, hU0a, hwa] with y h1 h2 h3
      rw [h1, h2, h3]; ring
    have heq : (fun y => U n y - U0 y) = w :=
      ((hU n).sub hU0).ae_eq_iff_eq (haar 1) hwc |>.mp hae
    have e1 : (fun y => u n y + -1 * u0 y) = fun y => u n y - u0 y := by
      funext y; ring
    have e2 : eLpNorm (fun y => g n y + (-1 : ℝ) • g0 y) 2 (haar 1) =
        eLpNorm (fun y => g n y 0 - g0 y 0) 2 (haar 1) := by
      rw [circle_eLpNorm_tangent_one hd.memLp_grad]
      congr 1; funext y; simp [sub_eq_add_neg]
    have := hws x
    rw [e1, e2] at this
    have h3 := congrFun heq x
    rw [h3]
    exact this
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hbt.eventually (gt_mem_nhds hε)] with n hn x
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt (hbd n x) hn


/-- `H¹` convergence on the circle implies uniform convergence of continuous representatives. -/
theorem circle_H1_tendstoUniformly {u : ℕ → Torus 1 → ℝ} {g : ℕ → Torus 1 → Tangent 1}
    {u0 : Torus 1 → ℝ} {g0 : Torus 1 → Tangent 1} {U : ℕ → Torus 1 → ℝ} {U0 : Torus 1 → ℝ}
    (hu : ∀ n, IsWeakGradient (u n) (g n)) (h0 : IsWeakGradient u0 g0)
    (hU : ∀ n, Continuous (U n)) (hUa : ∀ n, U n =ᵐ[haar 1] u n)
    (hU0 : Continuous U0) (hU0a : U0 =ᵐ[haar 1] u0)
    (h1 : Tendsto (fun n => eLpNorm (fun x => u n x - u0 x) 2 (haar 1)) atTop (𝓝 0))
    (h2 : Tendsto (fun n => eLpNorm (fun x => g n x - g0 x) 2 (haar 1)) atTop (𝓝 0)) :
    TendstoUniformly U U0 atTop := by
  refine circle_tendstoUniformly_of_coord hu h0 hU hUa hU0 hU0a h1 ?_
  have hm : ∀ n, MemLp (fun x => g n x - g0 x) 2 (haar 1) := fun n =>
    (hu n).memLp_grad.sub h0.memLp_grad
  have : ∀ n, eLpNorm (fun x => g n x 0 - g0 x 0) 2 (haar 1) =
      eLpNorm (fun x => g n x - g0 x) 2 (haar 1) := fun n => by
    rw [circle_eLpNorm_tangent_one (hm n)]
    rfl
  simpa only [this] using h2

/-- `d = 1` (STR025b-i, part 2). An `H¹` function on the circle has a continuous representative
`w` with `|w x - w y| ≤ ‖∇u‖₂ · |x - y|^{1/2}` (distance on the circle, `torusDist`) and
`|w x - mean u| ≤ ‖∇u‖₂`. The Hölder part is the existing `exists_continuous_rep_one`
(`sobolev_embedding_dim_one`); the oscillation bound is new. -/
theorem circle_H1_holder_half {u : Torus 1 → ℝ} {g : Torus 1 → Tangent 1}
    (hg : IsWeakGradient u g) :
    ∃ w : Torus 1 → ℝ, Continuous w ∧ w =ᵐ[haar 1] u ∧
      (∀ x y, |w x - w y| ≤
        (eLpNorm g 2 (haar 1)).toReal * torusDist x y ^ (1 / 2 : ℝ)) ∧
      ∀ x, |w x - ∫ y, u y ∂haar 1| ≤ (eLpNorm g 2 (haar 1)).toReal := by
  obtain ⟨w, hc, hae, hh, -⟩ := sobolev_embedding_dim_one hg
  have hH : ∀ x y, |w x - w y| ≤ (eLpNorm g 2 (haar 1)).toReal * Real.sqrt (torusDist x y) := hh
  refine ⟨w, hc, hae, fun x y => by rw [← Real.sqrt_eq_rpow]; exact hH x y, fun x => ?_⟩
  have hmean : ∫ y, w y ∂haar 1 = ∫ y, u y ∂haar 1 := integral_congr_ae hae
  have hint : Integrable w (haar 1) := (memLp_two_of_continuous hc).integrable one_le_two
  obtain ⟨y1, hy1⟩ := exists_le_integral hint
  obtain ⟨y2, hy2⟩ := exists_integral_le hint
  rw [← hmean]
  have hs : ∀ a b : Torus 1, |w a - w b| ≤ (eLpNorm g 2 (haar 1)).toReal := fun a b => by
    refine (hH a b).trans ?_
    have h1 : Real.sqrt (torusDist a b) ≤ 1 :=
      Real.sqrt_le_one.mpr ((torusDist_one_le a b).trans (by norm_num))
    have h0 : 0 ≤ (eLpNorm g 2 (haar 1)).toReal := ENNReal.toReal_nonneg
    nlinarith
  rcases le_total (∫ y, w y ∂haar 1) (w x) with h | h
  · have := hs x y1
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have := le_abs_self (w x - w y1)
    linarith
  · have := hs y2 x
    rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have := le_abs_self (w y2 - w x)
    linarith

/-- Du Bois-Reymond on the circle (STR025b-i, part 1). A continuous `u` with weak gradient
a.e. equal to a continuous `g` is `C¹` along the parametrization `s ↦ torusLift (fun _ => s)`,
with derivative `g (torusLift (fun _ => s)) 0`. -/
theorem circle_duBoisReymond {u : Torus 1 → ℝ} {g g' : Torus 1 → Tangent 1}
    (hu : Continuous u) (hg : IsWeakGradient u g') (hgc : Continuous g)
    (hae : g' =ᵐ[haar 1] g) :
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => u (torusLift fun _ : Fin 1 => s))
      (g (torusLift fun _ : Fin 1 => t) 0) t) ∧
    ContDiff ℝ 1 (fun s : ℝ => u (torusLift fun _ : Fin 1 => s)) := by
  have hg2 : IsWeakGradient u g := hg.congr_ae (ae_eq_refl _) hae
  obtain ⟨v, hv, hvw, h1, h2⟩ := exists_smooth_tendsto_H1 hg2
  have hT : TendstoUniformly v u atTop :=
    circle_tendstoUniformly_of_coord hvw hg2 (fun n => (hv n).continuous_torus)
      (fun n => ae_eq_refl _) hu (ae_eq_refl _) h1 (by simpa using h2 0)
  have hGc : Continuous fun s : ℝ => g (torusLift fun _ : Fin 1 => s) 0 :=
    (continuous_apply (0 : Fin 1)).comp
      ((PiLp.continuous_ofLp 2 _).comp (hgc.comp continuous_circleParam))
  -- the integral identity on windows of length at most one
  have key : ∀ a b : ℝ, a ≤ b → b ≤ a + 1 →
      u (torusLift fun _ : Fin 1 => b) - u (torusLift fun _ : Fin 1 => a) =
        ∫ s in a..b, g (torusLift fun _ : Fin 1 => s) 0 := by
    intro a b hab hb
    set E := u (torusLift fun _ : Fin 1 => b) - u (torusLift fun _ : Fin 1 => a) -
      ∫ s in a..b, g (torusLift fun _ : Fin 1 => s) 0 with hE
    set t : ℕ → ℝ := fun n => (eLpNorm (fun x => smoothGrad (v n) x 0 - g x 0) 2
      (haar 1)).toReal with ht
    have htt : Tendsto t atTop (𝓝 0) := by
      have e := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (h2 0)
      rwa [ENNReal.toReal_zero] at e
    have hbound : ∀ n, |E| ≤ |u (torusLift fun _ : Fin 1 => b) - v n (torusLift fun _ : Fin 1 => b)|
        + |u (torusLift fun _ : Fin 1 => a) - v n (torusLift fun _ : Fin 1 => a)| + t n := by
      intro n
      have hFc : Continuous fun x => smoothGrad (v n) x 0 - g x 0 :=
        ((hv n).continuous_coordPartial 0).sub
          ((continuous_apply (0 : Fin 1)).comp (((PiLp.continuous_ofLp 2 _)).comp hgc))
      have hD : Continuous fun s : ℝ => coordPartial 0 (v n) (torusLift fun _ : Fin 1 => s) :=
        (hv n).continuous_coordPartial 0 |>.comp continuous_circleParam
      have hI : ∫ s in a..b, (smoothGrad (v n) (torusLift fun _ : Fin 1 => s) 0 -
          g (torusLift fun _ : Fin 1 => s) 0) =
          (v n (torusLift fun _ : Fin 1 => b) - v n (torusLift fun _ : Fin 1 => a)) -
            ∫ s in a..b, g (torusLift fun _ : Fin 1 => s) 0 := by
        simp only [smoothGrad_apply]
        rw [intervalIntegral.integral_sub (hD.intervalIntegrable _ _) (hGc.intervalIntegrable _ _),
          circle_smooth_ftc (hv n)]
      have hsq := circle_sq_integral_circle_le hFc hab hb
      have habs : |∫ s in a..b, (smoothGrad (v n) (torusLift fun _ : Fin 1 => s) 0 -
          g (torusLift fun _ : Fin 1 => s) 0)| ≤ t n := by
        have := Real.abs_le_sqrt hsq
        simp only [ht]
        rwa [toReal_eLpNorm_two (memLp_two_of_continuous hFc)]
      rw [hI] at habs
      have : E = (u (torusLift fun _ : Fin 1 => b) - v n (torusLift fun _ : Fin 1 => b)) -
          (u (torusLift fun _ : Fin 1 => a) - v n (torusLift fun _ : Fin 1 => a)) +
          ((v n (torusLift fun _ : Fin 1 => b) - v n (torusLift fun _ : Fin 1 => a)) -
            ∫ s in a..b, g (torusLift fun _ : Fin 1 => s) 0) := by rw [hE]; ring
      rw [this]
      calc _ ≤ |(u (torusLift fun _ : Fin 1 => b) - v n (torusLift fun _ : Fin 1 => b)) -
            (u (torusLift fun _ : Fin 1 => a) - v n (torusLift fun _ : Fin 1 => a))| +
            |(v n (torusLift fun _ : Fin 1 => b) - v n (torusLift fun _ : Fin 1 => a)) -
            ∫ s in a..b, g (torusLift fun _ : Fin 1 => s) 0| := abs_add_le _ _
        _ ≤ _ := by
          have := abs_sub (u (torusLift fun _ : Fin 1 => b) - v n (torusLift fun _ : Fin 1 => b))
            (u (torusLift fun _ : Fin 1 => a) - v n (torusLift fun _ : Fin 1 => a))
          linarith
    have hlim : Tendsto (fun n => |u (torusLift fun _ : Fin 1 => b) -
        v n (torusLift fun _ : Fin 1 => b)| + |u (torusLift fun _ : Fin 1 => a) -
        v n (torusLift fun _ : Fin 1 => a)| + t n) atTop (𝓝 (0 + 0 + 0)) := by
      have hp : ∀ x, Tendsto (fun n => |u x - v n x|) atTop (𝓝 0) := fun x => by
        have := (tendsto_const_nhds (x := u x)).sub (hT.tendsto_at x)
        simpa using this.abs
      exact ((hp _).add (hp _)).add htt
    have h0 : |E| ≤ 0 := by
      have := ge_of_tendsto' hlim hbound
      simpa using this
    have : E = 0 := abs_nonpos_iff.mp h0
    linarith
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => u (torusLift fun _ : Fin 1 => s))
      (g (torusLift fun _ : Fin 1 => t) 0) t := by
    intro t
    have hF : HasDerivAt (fun s : ℝ => u (torusLift fun _ : Fin 1 => t) +
        ∫ r in t..s, g (torusLift fun _ : Fin 1 => r) 0) (g (torusLift fun _ : Fin 1 => t) 0) t := by
      have := (hGc.integral_hasStrictDerivAt t t).hasDerivAt
      simpa using this.const_add (u (torusLift fun _ : Fin 1 => t))
    refine hF.congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds t one_pos] with s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    rcases le_total t s with h | h
    · have := key t s h (by linarith [le_abs_self (s - t), abs_sub_comm s t])
      linarith
    · have := key s t h (by linarith [neg_abs_le (s - t), abs_sub_comm s t])
      rw [intervalIntegral.integral_symm]
      linarith
  refine ⟨hderiv, ?_⟩
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hderiv t).differentiableAt, ?_⟩
  have : deriv (fun s : ℝ => u (torusLift fun _ : Fin 1 => s)) =
      fun s => g (torusLift fun _ : Fin 1 => s) 0 := funext fun t => (hderiv t).deriv
  rw [this]
  exact hGc

end DGPS
