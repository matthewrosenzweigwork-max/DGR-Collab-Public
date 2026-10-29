import DGPS.FiniteN.ScalarFoldFIN056
/-!
# Exact fold cubic coordinate (FIN057)

Near the stationary inflection point `t_* = -s_*` of the scalar auxiliary potential
`ψ = scalarPsi κ h_c` (`κ > 2`), the function `φ = ψ(t_*) - ψ` vanishes to third order and has
`φ'''(t_*) = -g''(s_*) > 0` (FIN056).  We prove the factorization `φ = (t - t_*)^3 a(t)` with `a`
smooth and `a(t_*) = φ'''(t_*)/6 > 0` using Taylor's formula with integral remainder, a
parametric-integral smoothness lemma and smoothness of `I₀`, then define the real cube root
coordinate `v(t) = (t - t_*) (3 a(t))^{1/3}`, so that `v^3 = 3 (ψ(t_*) - ψ)` exactly, and construct
its smooth inverse.

The main theorem is `DGPS.FiniteN.exact_fold_cubic_coordinate`.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace DGPS.FiniteN.ScalarFoldFIN057


/-- Hadamard-type parametric integral `t ↦ ∫₀¹ w(s) G(c + s (t - c)) ds`. -/
noncomputable def hadIFIN057 (c : ℝ) (w G : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, w s * G (c + s * (t - c))

section Had

variable {U : Set ℝ} {c : ℝ}

theorem mem_of_convex_FIN057 (hconv : Convex ℝ U) (hc : c ∈ U) {x s : ℝ} (hx : x ∈ U)
    (hs : s ∈ Icc (0 : ℝ) 1) : c + s * (x - c) ∈ U := by
  have := hconv hc hx (sub_nonneg.2 hs.2) hs.1 (by ring)
  convert this using 1
  simp only [smul_eq_mul]
  ring

theorem exists_bound_FIN057 (hU : IsOpen U) (hconv : Convex ℝ U) (hc : c ∈ U) {G : ℝ → ℝ}
    (hG : ContinuousOn G U) {t0 : ℝ} (ht0 : t0 ∈ U) :
    ∃ ε > 0, ∃ B : ℝ, Metric.ball t0 ε ⊆ U ∧
      ∀ x ∈ Metric.ball t0 ε, ∀ s ∈ Icc (0 : ℝ) 1, |G (c + s * (x - c))| ≤ B := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU t0 ht0
  have hsub : Metric.closedBall t0 (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  set K : Set ℝ := (fun p : ℝ × ℝ => c + p.1 * (p.2 - c)) ''
    (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall t0 (ε / 2)) with hK
  have hKc : IsCompact K :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).image (by fun_prop)
  have hKU : K ⊆ U := by
    rintro _ ⟨⟨s, x⟩, ⟨hs, hx⟩, rfl⟩
    exact mem_of_convex_FIN057 hconv hc (hsub hx) hs
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hG.mono hKU)
  refine ⟨ε / 2, by linarith, C, (Metric.ball_subset_closedBall).trans hsub, ?_⟩
  intro x hx s hs
  have : c + s * (x - c) ∈ K :=
    ⟨(s, x), ⟨hs, Metric.ball_subset_closedBall hx⟩, rfl⟩
  simpa using hC _ this

theorem path_continuousOn_FIN057 (hconv : Convex ℝ U) (hc : c ∈ U) {G : ℝ → ℝ}
    (hG : ContinuousOn G U) {x : ℝ} (hx : x ∈ U) :
    ContinuousOn (fun s : ℝ => G (c + s * (x - c))) (Icc (0 : ℝ) 1) :=
  hG.comp (by fun_prop : Continuous fun s : ℝ => c + s * (x - c)).continuousOn
    (fun s hs => mem_of_convex_FIN057 hconv hc hx hs)

theorem hadI_continuousOn_FIN057 (hU : IsOpen U) (hconv : Convex ℝ U) (hc : c ∈ U)
    {w G : ℝ → ℝ} (hw : Continuous w) (hG : ContinuousOn G U) :
    ContinuousOn (hadIFIN057 c w G) U := by
  intro t0 ht0
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨ε, hε, B, hball, hB⟩ := exists_bound_FIN057 hU hconv hc hG ht0
  obtain ⟨Cw, hCw⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hw.continuousOn : ContinuousOn w (Icc (0 : ℝ) 1))
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => Cw * B) ?_ ?_ ?_ ?_
  · refine Filter.eventually_of_mem (Metric.ball_mem_nhds t0 hε) fun x hx => ?_
    rw [Set.uIoc_of_le zero_le_one]
    have := (hw.continuousOn (s := Icc (0 : ℝ) 1)).mul
      (path_continuousOn_FIN057 hconv hc hG (hball hx))
    exact (this.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · refine Filter.eventually_of_mem (Metric.ball_mem_nhds t0 hε) fun x hx => ?_
    refine ae_of_all _ fun s hs => ?_
    rw [Set.uIoc_of_le zero_le_one] at hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
    rw [norm_mul]
    have h1 := hCw s hs'
    have h2 := hB x hx s hs'
    rw [Real.norm_eq_abs] at h1 ⊢
    exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun s hs => ?_
    have hpt : c + s * (t0 - c) ∈ U := by
      rw [Set.uIoc_of_le zero_le_one] at hs
      exact mem_of_convex_FIN057 hconv hc ht0 (Ioc_subset_Icc_self hs)
    have h1 : ContinuousAt G (c + s * (t0 - c)) := hG.continuousAt (hU.mem_nhds hpt)
    have h2 : ContinuousAt (fun x : ℝ => c + s * (x - c)) t0 := by fun_prop
    exact continuousAt_const.mul (h1.comp (f := fun x : ℝ => c + s * (x - c)) h2)

theorem hadI_hasDerivAt_FIN057 (hU : IsOpen U) (hconv : Convex ℝ U) (hc : c ∈ U)
    {w G : ℝ → ℝ} (hw : Continuous w) (hG : ContDiffOn ℝ 1 G U) {t0 : ℝ} (ht0 : t0 ∈ U) :
    HasDerivAt (hadIFIN057 c w G) (hadIFIN057 c (fun s => s * w s) (deriv G) t0) t0 := by
  have hG' : ContinuousOn (deriv G) U := hG.continuousOn_deriv_of_isOpen hU le_rfl
  have hGc : ContinuousOn G U := hG.continuousOn
  obtain ⟨ε, hε, B, hball, hB⟩ := exists_bound_FIN057 hU hconv hc hG' ht0
  obtain ⟨Cw, hCw⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hw.continuousOn : ContinuousOn w (Icc (0 : ℝ) 1))
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1) (𝕜 := ℝ)
    (F := fun (x s : ℝ) => w s * G (c + s * (x - c)))
    (F' := fun (x s : ℝ) => (s * w s) * deriv G (c + s * (x - c)))
    (bound := fun _ => Cw * B) (x₀ := t0) (s := Metric.ball t0 ε)
    (Metric.ball_mem_nhds t0 hε) ?_ ?_ ?_ ?_ ?_ ?_
  · exact key.2
  · refine Filter.eventually_of_mem (Metric.ball_mem_nhds t0 hε) fun x hx => ?_
    rw [Set.uIoc_of_le zero_le_one]
    have := (hw.continuousOn (s := Icc (0 : ℝ) 1)).mul
      (path_continuousOn_FIN057 hconv hc hGc (hball hx))
    exact (this.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · have := (hw.continuousOn (s := Icc (0 : ℝ) 1)).mul
      (path_continuousOn_FIN057 hconv hc hGc ht0)
    exact ContinuousOn.intervalIntegrable (by rw [Set.uIcc_of_le zero_le_one]; exact this)
  · rw [Set.uIoc_of_le zero_le_one]
    have := ((continuous_id.mul hw).continuousOn (s := Icc (0 : ℝ) 1)).mul
      (path_continuousOn_FIN057 hconv hc hG' ht0)
    exact (this.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · refine ae_of_all _ fun s hs x hx => ?_
    rw [Set.uIoc_of_le zero_le_one] at hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := hCw s hs'
    rw [Real.norm_eq_abs] at h1
    have h2 := hB x hx s hs'
    have h3 : |s| ≤ 1 := by rw [abs_of_nonneg hs'.1]; exact hs'.2
    have hCw0 : 0 ≤ Cw := (abs_nonneg _).trans h1
    have hB0 : 0 ≤ B := (abs_nonneg _).trans h2
    calc |s| * |w s| * |deriv G (c + s * (x - c))| ≤ 1 * Cw * B := by
          refine mul_le_mul (mul_le_mul h3 h1 (abs_nonneg _) zero_le_one) h2 (abs_nonneg _) ?_
          positivity
      _ = Cw * B := by ring
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun s hs x hx => ?_
    have hxU : x ∈ U := hball hx
    have hpt : c + s * (x - c) ∈ U := by
      rw [Set.uIoc_of_le zero_le_one] at hs
      exact mem_of_convex_FIN057 hconv hc hxU (Ioc_subset_Icc_self hs)
    have hd : DifferentiableAt ℝ G (c + s * (x - c)) :=
      (hG.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hpt)
    have h1 : HasDerivAt (fun y : ℝ => c + s * (y - c)) s x := by
      simpa using (((hasDerivAt_id x).sub_const c).const_mul s).const_add c
    have h2 := hd.hasDerivAt.comp x h1
    have h3 := h2.const_mul (w s)
    refine h3.congr_deriv ?_
    ring

theorem hadI_contDiffOn_FIN057 (hU : IsOpen U) (hconv : Convex ℝ U) (hc : c ∈ U) :
    ∀ n : ℕ, ∀ {w G : ℝ → ℝ}, Continuous w → ContDiffOn ℝ n G U →
      ContDiffOn ℝ n (hadIFIN057 c w G) U := by
  intro n
  induction n with
  | zero =>
    intro w G hw hG
    rw [Nat.cast_zero, contDiffOn_zero] at hG ⊢
    exact hadI_continuousOn_FIN057 hU hconv hc hw hG
  | succ n ih =>
    intro w G hw hG
    have hG1 : ContDiffOn ℝ 1 G U := hG.of_le (by exact_mod_cast Nat.succ_pos n)
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen hU] at hG ⊢
    obtain ⟨_, _, hd⟩ := hG
    refine ⟨?_, fun h => absurd h (by simp), ?_⟩
    · intro t ht
      exact (hadI_hasDerivAt_FIN057 hU hconv hc hw hG1 ht).differentiableAt.differentiableWithinAt
    · have := ih (w := fun s => s * w s) (G := deriv G) (continuous_id.mul hw) hd
      refine this.congr fun t ht => ?_
      exact (hadI_hasDerivAt_FIN057 hU hconv hc hw hG1 ht).deriv

theorem hadI_contDiffOn_top_FIN057 (hU : IsOpen U) (hconv : Convex ℝ U) (hc : c ∈ U)
    {w G : ℝ → ℝ} (hw : Continuous w) (hG : ContDiffOn ℝ ∞ G U) :
    ContDiffOn ℝ ∞ (hadIFIN057 c w G) U := by
  rw [contDiffOn_infty] at hG ⊢
  exact fun n => hadI_contDiffOn_FIN057 hU hconv hc n hw (hG n)

theorem deriv_contDiffOn_FIN057 (hU : IsOpen U) {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (deriv f) U :=
  ((contDiffOn_infty_iff_deriv_of_isOpen hU).1 hf).2

theorem differentiableAt_of_contDiffOn_FIN057 (hU : IsOpen U) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) {x : ℝ} (hx : x ∈ U) : DifferentiableAt ℝ f x :=
  ((contDiffOn_infty_iff_deriv_of_isOpen hU).1 hf).1.differentiableAt (hU.mem_nhds hx)

/-- Taylor's formula with integral remainder at order three, in the form needed for the
cubic factorization. -/
theorem taylor3_FIN057 (hU : IsOpen U) (hconv : Convex ℝ U) (hc : c ∈ U) {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ U) (h0 : φ c = 0) (h1 : deriv φ c = 0)
    (h2 : deriv (deriv φ) c = 0) {t : ℝ} (ht : t ∈ U) :
    φ t = (t - c) ^ 3 *
      hadIFIN057 c (fun s => (1 - s) ^ 2 / 2) (deriv (deriv (deriv φ))) t := by
  have hd1 := deriv_contDiffOn_FIN057 hU hφ
  have hd2 := deriv_contDiffOn_FIN057 hU hd1
  have hd3 := deriv_contDiffOn_FIN057 hU hd2
  set p : ℝ → ℝ := fun s => c + s * (t - c) with hp
  have hpU : ∀ s ∈ Icc (0 : ℝ) 1, p s ∈ U := fun s hs =>
    mem_of_convex_FIN057 hconv hc ht hs
  have hpd : ∀ s : ℝ, HasDerivAt p (t - c) s := by
    intro s
    have := (((hasDerivAt_id s).mul_const (t - c)).const_add c)
    simpa only [id, one_mul] using this
  have hkey : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => (1 - s) ^ 2 / 2 * deriv (deriv φ) (p s) * (t - c) ^ 2
          + (1 - s) * deriv φ (p s) * (t - c) + φ (p s))
        ((1 - s) ^ 2 / 2 * deriv (deriv (deriv φ)) (p s) * (t - c) ^ 3) s := by
    intro s hs
    have hps := hpU s hs
    have e1 : HasDerivAt (fun s : ℝ => (1 - s) ^ 2 / 2) (-(1 - s)) s := by
      have := ((((hasDerivAt_id s).const_sub 1)).pow 2).div_const 2
      refine this.congr_deriv ?_
      simp only [id]; ring
    have e2 : HasDerivAt (fun s : ℝ => deriv (deriv φ) (p s))
        (deriv (deriv (deriv φ)) (p s) * (t - c)) s :=
      (differentiableAt_of_contDiffOn_FIN057 hU hd2 hps).hasDerivAt.comp s (hpd s)
    have e3 : HasDerivAt (fun s : ℝ => deriv φ (p s))
        (deriv (deriv φ) (p s) * (t - c)) s :=
      (differentiableAt_of_contDiffOn_FIN057 hU hd1 hps).hasDerivAt.comp s (hpd s)
    have e4 : HasDerivAt (fun s : ℝ => φ (p s)) (deriv φ (p s) * (t - c)) s :=
      (differentiableAt_of_contDiffOn_FIN057 hU hφ hps).hasDerivAt.comp s (hpd s)
    have e5 : HasDerivAt (fun s : ℝ => 1 - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub 1
    have := (((e1.mul e2).mul_const ((t - c) ^ 2)).add ((e5.mul e3).mul_const (t - c))).add e4
    refine this.congr_deriv ?_
    ring
  have hcont : ContinuousOn (fun s : ℝ => (1 - s) ^ 2 / 2 *
      deriv (deriv (deriv φ)) (p s) * (t - c) ^ 3) (Icc (0 : ℝ) 1) := by
    have h3 : ContinuousOn (fun s : ℝ => deriv (deriv (deriv φ)) (p s)) (Icc (0 : ℝ) 1) :=
      path_continuousOn_FIN057 hconv hc hd3.continuousOn ht
    have h4 : Continuous fun s : ℝ => (1 - s) ^ 2 / 2 := by fun_prop
    exact ((h4.continuousOn.mul h3).mul continuousOn_const)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun s hs => hkey s (by rwa [Set.uIcc_of_le zero_le_one] at hs))
    (ContinuousOn.intervalIntegrable (by rw [Set.uIcc_of_le zero_le_one]; exact hcont))
  have hp0 : p 0 = c := by simp [hp]
  have hp1 : p 1 = t := by simp [hp]
  simp only [hp0, hp1, h0, h1, h2] at hftc
  have hI : hadIFIN057 c (fun s => (1 - s) ^ 2 / 2) (deriv (deriv (deriv φ))) t * (t - c) ^ 3
      = ∫ s in (0 : ℝ)..1, (1 - s) ^ 2 / 2 * deriv (deriv (deriv φ)) (p s) * (t - c) ^ 3 := by
    unfold hadIFIN057
    rw [← intervalIntegral.integral_mul_const]
  rw [mul_comm, hI, hftc]
  norm_num

theorem hadI_self_FIN057 (G : ℝ → ℝ) :
    hadIFIN057 c (fun s => (1 - s) ^ 2 / 2) G c = G c / 6 := by
  unfold hadIFIN057
  simp only [sub_self, mul_zero, add_zero]
  have h : ∫ s in (0 : ℝ)..1, (1 - s) ^ 2 / 2 * G c = (∫ s in (0 : ℝ)..1, (1 - s) ^ 2 / 2) * G c :=
    intervalIntegral.integral_mul_const _ _
  rw [h, intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ 2) 1]
  simp only [sub_self, sub_zero, integral_pow]
  norm_num
  ring

/-- Cubic factorization of a smooth function vanishing to second order at `c`. -/
theorem cubic_factor_FIN057 {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (h0 : φ c = 0)
    (h1 : deriv φ c = 0) (h2 : deriv (deriv φ) c = 0)
    (h3 : 0 < deriv (deriv (deriv φ)) c) :
    ∃ a : ℝ → ℝ, ContDiff ℝ ∞ a ∧ 0 < a c ∧ ∀ t, φ t = (t - c) ^ 3 * a t := by
  have hU : IsOpen (univ : Set ℝ) := isOpen_univ
  have hconv : Convex ℝ (univ : Set ℝ) := convex_univ
  have hφ' : ContDiffOn ℝ ∞ φ univ := hφ.contDiffOn
  have hd3 := deriv_contDiffOn_FIN057 hU (deriv_contDiffOn_FIN057 hU (deriv_contDiffOn_FIN057 hU hφ'))
  refine ⟨hadIFIN057 c (fun s => (1 - s) ^ 2 / 2) (deriv (deriv (deriv φ))), ?_, ?_, fun t => ?_⟩
  · rw [← contDiffOn_univ]
    exact hadI_contDiffOn_top_FIN057 hU hconv (mem_univ c) (by fun_prop) hd3
  · rw [hadI_self_FIN057]; positivity
  · exact taylor3_FIN057 hU hconv (mem_univ c) hφ' h0 h1 h2 (mem_univ t)

end Had


section Bessel

open DGPS.Models DGPS.Circle.BesselMoments DGPS.Circle.AngularNormalization


open DGPS.Models DGPS.Circle.BesselMoments DGPS.Circle.AngularNormalization

/-- the exponential moments `x ↦ ∫ exp(x cos θ) cos(θ)^k` -/
noncomputable def expMomFIN057 (k : ℕ) (x : ℝ) : ℝ :=
  ∫ θ, Real.exp (x * angCos θ) * angCos θ ^ k ∂angHaar

theorem hasDerivAt_expMom_FIN057 (k : ℕ) (x : ℝ) :
    HasDerivAt (expMomFIN057 k) (expMomFIN057 (k + 1) x) x := by
  have hc : Continuous angCos := continuous_angMode 1
  have h := hasDerivAt_exp_integral (fun θ => angCos θ ^ k) (hc.pow k)
    (fun θ => by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (abs_angMode_le 1 θ)) x
  have e : expMomFIN057 (k + 1) x =
      ∫ θ, angCos θ * Real.exp (x * angCos θ) * angCos θ ^ k ∂angHaar := by
    unfold expMomFIN057
    congr 1
    funext θ
    simp only [pow_succ]
    ring
  rw [e]
  exact h

theorem expMom_contDiff_FIN057 (n : ℕ) : ∀ k : ℕ, ContDiff ℝ n (expMomFIN057 k) := by
  induction n with
  | zero =>
    intro k
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.mpr fun x => (hasDerivAt_expMom_FIN057 k x).continuousAt
  | succ n ih =>
    intro k
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hasDerivAt_expMom_FIN057 k x).differentiableAt, fun h => absurd h (by simp), ?_⟩
    have : deriv (expMomFIN057 k) = expMomFIN057 (k + 1) :=
      funext fun x => (hasDerivAt_expMom_FIN057 k x).deriv
    rw [this]
    exact ih (k + 1)

theorem besselI_zero_eq_expMom_FIN057 : besselI 0 = expMomFIN057 0 := by
  funext t
  simp [besselI, expMomFIN057, angMode_zero]

theorem besselI_zero_contDiff_FIN057 : ContDiff ℝ ∞ (besselI 0) := by
  rw [besselI_zero_eq_expMom_FIN057, contDiff_infty]
  exact fun n => expMom_contDiff_FIN057 n 0

theorem scalarPsi_contDiff_FIN057 (κ h : ℝ) : ContDiff ℝ ∞ (scalarPsi κ h) := by
  unfold scalarPsi
  refine ContDiff.sub (by fun_prop) ?_
  exact ContDiff.log besselI_zero_contDiff_FIN057 fun t => (besselI_zero_pos t).ne'


end Bessel
/-- Smooth inverse of a strictly increasing smooth map with positive bounded derivative. -/
theorem inverse_FIN057 {v : ℝ → ℝ} {α β m M : ℝ} {W : Set ℝ} (hαβ : α < β) (hW : IsOpen W)
    (hIW : Icc α β ⊆ W) (hv : ContDiffOn ℝ ∞ v W) (hm : 0 < m)
    (hb : ∀ t ∈ Ioo α β, m ≤ deriv v t ∧ deriv v t ≤ M) :
    ∃ T : ℝ → ℝ, ContDiffOn ℝ ∞ T (Ioo (v α) (v β)) ∧
      (∀ w ∈ Ioo (v α) (v β), T w ∈ Ioo α β ∧ v (T w) = w ∧
        1 / M ≤ deriv T w ∧ deriv T w ≤ 1 / m) ∧
      (∀ t ∈ Ioo α β, v t ∈ Ioo (v α) (v β) ∧ T (v t) = t) := by
  have hvc : ContinuousOn v (Icc α β) := hv.continuousOn.mono hIW
  have hmono : StrictMonoOn v (Icc α β) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc α β) hvc fun x hx => ?_
    rw [interior_Icc] at hx
    exact lt_of_lt_of_le hm (hb x hx).1
  have hvI : ∀ t ∈ Ioo α β, v t ∈ Ioo (v α) (v β) := fun t ht =>
    ⟨hmono ⟨le_rfl, hαβ.le⟩ (Ioo_subset_Icc_self ht) ht.1,
     hmono (Ioo_subset_Icc_self ht) ⟨hαβ.le, le_rfl⟩ ht.2⟩
  have hsurj : ∀ w ∈ Ioo (v α) (v β), ∃ t ∈ Ioo α β, v t = w := fun w hw =>
    intermediate_value_Ioo hαβ.le hvc hw
  have hinj : InjOn v (Ioo α β) := hmono.injOn.mono Ioo_subset_Icc_self
  set T : ℝ → ℝ := Function.invFunOn v (Ioo α β) with hTdef
  have hT : ∀ w ∈ Ioo (v α) (v β), T w ∈ Ioo α β ∧ v (T w) = w := fun w hw =>
    Function.invFunOn_pos (hsurj w hw)
  have hleft : ∀ t ∈ Ioo α β, T (v t) = t := fun t ht => hinj.leftInvOn_invFunOn ht
  have hTmono : MonotoneOn T (Ioo (v α) (v β)) := by
    intro w1 hw1 w2 hw2 h12
    by_contra hlt
    replace hlt := not_le.1 hlt
    have := hmono (Ioo_subset_Icc_self (hT w2 hw2).1) (Ioo_subset_Icc_self (hT w1 hw1).1) hlt
    rw [(hT w2 hw2).2, (hT w1 hw1).2] at this
    exact absurd h12 (not_le.2 this)
  have himg : T '' Ioo (v α) (v β) = Ioo α β := by
    ext t
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hT w hw).1
    · intro ht
      exact ⟨v t, hvI t ht, hleft t ht⟩
  have hJopen : ∀ w ∈ Ioo (v α) (v β), Ioo (v α) (v β) ∈ 𝓝 w := fun w hw => Ioo_mem_nhds hw.1 hw.2
  have hcont : ∀ w ∈ Ioo (v α) (v β), ContinuousAt T w := by
    intro w hw
    refine continuousAt_of_monotoneOn_of_image_mem_nhds hTmono (hJopen w hw) ?_
    rw [himg]
    have hTw := (hT w hw).1
    exact Ioo_mem_nhds hTw.1 hTw.2
  have hmem : ∀ w ∈ Ioo (v α) (v β), T w ∈ W := fun w hw =>
    hIW (Ioo_subset_Icc_self (hT w hw).1)
  have hpos : ∀ w ∈ Ioo (v α) (v β), 0 < deriv v (T w) := fun w hw =>
    lt_of_lt_of_le hm (hb _ (hT w hw).1).1
  have hder : ∀ w ∈ Ioo (v α) (v β), HasDerivAt T (deriv v (T w))⁻¹ w := by
    intro w hw
    refine HasDerivAt.of_local_left_inverse (hcont w hw)
      (differentiableAt_of_contDiffOn_FIN057 hW hv (hmem w hw)).hasDerivAt (hpos w hw).ne' ?_
    filter_upwards [hJopen w hw] with y hy using (hT y hy).2
  have hderiv : ∀ w ∈ Ioo (v α) (v β), deriv T w = (deriv v (T w))⁻¹ := fun w hw =>
    (hder w hw).deriv
  have hdv := deriv_contDiffOn_FIN057 hW hv
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n T (Ioo (v α) (v β)) := by
    intro n
    induction n with
    | zero =>
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun w hw => (hcont w hw).continuousWithinAt
    | succ n ih =>
      rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
      refine ⟨fun w hw => (hder w hw).differentiableAt.differentiableWithinAt,
        fun h => absurd h (by simp), ?_⟩
      have h1 : ContDiffOn ℝ n (deriv v ∘ T) (Ioo (v α) (v β)) :=
        ((contDiffOn_infty.1 hdv) n).comp ih (fun w hw => hmem w hw)
      have h2 : ContDiffOn ℝ n (fun w => (deriv v (T w))⁻¹) (Ioo (v α) (v β)) :=
        h1.inv fun w hw => (hpos w hw).ne'
      exact h2.congr hderiv
  refine ⟨T, contDiffOn_infty.2 hsm, fun w hw => ⟨(hT w hw).1, (hT w hw).2, ?_, ?_⟩,
    fun t ht => ⟨hvI t ht, hleft t ht⟩⟩
  · rw [hderiv w hw, one_div]
    have hb' := hb _ (hT w hw).1
    exact inv_anti₀ (hpos w hw) hb'.2
  · rw [hderiv w hw, one_div]
    have hb' := hb _ (hT w hw).1
    exact inv_anti₀ hm hb'.1


/-- The smooth cube-root coordinate for a function with a cubic vanishing factor having a
positive smooth quotient. -/
theorem coordinate_FIN057 {a φ : ℝ → ℝ} {c : ℝ} (ha : ContDiff ℝ ∞ a) (hac : 0 < a c)
    (hφ : ∀ t, φ t = (t - c) ^ 3 * a t) :
    ∃ (α β : ℝ) (v T : ℝ → ℝ) (m M : ℝ), α < c ∧ c < β ∧ 0 < m ∧ m ≤ M ∧
      ContDiffOn ℝ ∞ v (Ioo α β) ∧ v c = 0 ∧
      (∀ t ∈ Ioo α β, v t ^ 3 = 3 * φ t) ∧
      (∀ t ∈ Ioo α β, m ≤ deriv v t ∧ deriv v t ≤ M) ∧
      StrictMonoOn v (Ioo α β) ∧
      ContDiffOn ℝ ∞ T (Ioo (v α) (v β)) ∧ T 0 = c ∧ 0 ∈ Ioo (v α) (v β) ∧
      (∀ w ∈ Ioo (v α) (v β), T w ∈ Ioo α β ∧ v (T w) = w ∧
        1 / M ≤ deriv T w ∧ deriv T w ≤ 1 / m) ∧
      (∀ t ∈ Ioo α β, v t ∈ Ioo (v α) (v β) ∧ T (v t) = t) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_lt continuous_const ha.continuous) c hac
  set b : ℝ → ℝ := fun t => Real.exp (Real.log (3 * a t) / 3) with hb
  set v : ℝ → ℝ := fun t => (t - c) * b t with hv
  have hapos : ∀ t ∈ Metric.ball c ε, 0 < a t := fun t ht => hball ht
  have hbsm : ContDiffOn ℝ ∞ b (Metric.ball c ε) := by
    refine ContDiffOn.exp (ContDiffOn.div_const (ContDiffOn.log ?_ ?_) 3)
    · exact (contDiff_const.mul ha).contDiffOn
    · intro t ht
      have := hapos t ht
      positivity
  have hvsm : ContDiffOn ℝ ∞ v (Metric.ball c ε) :=
    ((contDiff_id.sub contDiff_const).contDiffOn).mul hbsm
  have hcube : ∀ t ∈ Metric.ball c ε, v t ^ 3 = 3 * φ t := by
    intro t ht
    have h3 : b t ^ 3 = 3 * a t := by
      simp only [hb]
      rw [← Real.exp_nat_mul]
      have : ((3 : ℕ) : ℝ) * (Real.log (3 * a t) / 3) = Real.log (3 * a t) := by
        push_cast; ring
      rw [this, Real.exp_log (by have := hapos t ht; positivity)]
    simp only [hv]
    rw [mul_pow, h3, hφ t]
    ring
  have hbc : 0 < b c := Real.exp_pos _
  have hvc : v c = 0 := by simp [hv]
  have hbd : HasDerivAt b (deriv b c) c :=
    (differentiableAt_of_contDiffOn_FIN057 Metric.isOpen_ball hbsm
      (Metric.mem_ball_self hε)).hasDerivAt
  have hvd : HasDerivAt v (b c) c := by
    have := ((hasDerivAt_id c).sub_const c).mul hbd
    refine this.congr_deriv ?_
    simp
  have hdvc : deriv v c = b c := hvd.deriv
  have hdcont : ContinuousAt (deriv v) c :=
    ((deriv_contDiffOn_FIN057 Metric.isOpen_ball hvsm).continuousOn).continuousAt
      (Metric.ball_mem_nhds c hε)
  obtain ⟨δ1, hδ1, hδ1'⟩ := Metric.continuousAt_iff.1 hdcont (b c / 2) (by positivity)
  set δ : ℝ := min ε δ1 with hδ
  have hδpos : 0 < δ := lt_min hε hδ1
  have hδε : δ ≤ ε := min_le_left _ _
  have hδδ1 : δ ≤ δ1 := min_le_right _ _
  have hIW : ∀ t ∈ Icc (c - δ / 2) (c + δ / 2), t ∈ Metric.ball c δ := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hIoo : ∀ t ∈ Ioo (c - δ / 2) (c + δ / 2), t ∈ Metric.ball c δ := fun t ht =>
    hIW t (Ioo_subset_Icc_self ht)
  have hbound : ∀ t ∈ Ioo (c - δ / 2) (c + δ / 2),
      b c / 2 ≤ deriv v t ∧ deriv v t ≤ 3 * b c / 2 := by
    intro t ht
    have h1 := hδ1' (x := t) (by
      have := Metric.mem_ball.1 (hIoo t ht)
      exact lt_of_lt_of_le this hδδ1)
    rw [hdvc, Real.dist_eq, abs_lt] at h1
    constructor <;> linarith [h1.1, h1.2]
  have hvsmδ : ContDiffOn ℝ ∞ v (Metric.ball c δ) := hvsm.mono (Metric.ball_subset_ball hδε)
  obtain ⟨T, hTsm, hT1, hT2⟩ := inverse_FIN057 (v := v) (α := c - δ / 2) (β := c + δ / 2)
    (m := b c / 2) (M := 3 * b c / 2) (W := Metric.ball c δ) (by linarith) Metric.isOpen_ball
    hIW hvsmδ (by positivity) hbound
  have hmono : StrictMonoOn v (Ioo (c - δ / 2) (c + δ / 2)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) ?_ fun x hx => ?_
    · exact (hvsmδ.continuousOn).mono (fun t ht => hIoo t ht)
    · rw [interior_Ioo] at hx
      exact lt_of_lt_of_le (by positivity) (hbound x hx).1
  have hcI : c ∈ Ioo (c - δ / 2) (c + δ / 2) := ⟨by linarith, by linarith⟩
  have hvcJ := (hT2 c hcI).1
  have hT0 : T 0 = c := by
    have := (hT2 c hcI).2
    rwa [hvc] at this
  refine ⟨c - δ / 2, c + δ / 2, v, T, b c / 2, 3 * b c / 2, by linarith, by linarith,
    by positivity, by linarith, ?_, hvc, ?_, hbound, hmono, hTsm, hT0, ?_, hT1, hT2⟩
  · exact hvsm.mono (fun t ht => Metric.ball_subset_ball hδε (hIoo t ht))
  · intro t ht
    exact hcube t (Metric.ball_subset_ball hδε (hIoo t ht))
  · rw [← hvc]; exact hvcJ


end DGPS.FiniteN.ScalarFoldFIN057

namespace DGPS.FiniteN

open DGPS.Models DGPS.Circle.BesselMoments

/-- **Exact fold cubic coordinate.**  Let `ψ = ψ_{h_c}` be the scalar auxiliary potential at the
critical field `h_c` and `t_* = -s_*` the stationary inflection point of `ψ`.  On a fixed open
interval `I = (α, β)` around `t_*` there is a `C^∞` strictly increasing coordinate `v`, the real
cube root `v(t) = [3 (ψ(t_*) - ψ(t))]^{1/3}`, with `v(t_*) = 0` and `m ≤ v' ≤ M` for constants
`0 < m ≤ M`.  Its smooth inverse `T : (v α, v β) → I` satisfies `ψ(T(w)) = ψ(t_*) - w³/3`
exactly, `T(0) = t_*`, and `1/M ≤ T' ≤ 1/m`. -/
theorem exact_fold_cubic_coordinate (κ : ℝ) (hκ : 2 < κ) :
    let hc := scalarFoldField κ
    let ψ := scalarPsi κ hc
    let tStar := -scalarFoldPoint κ
    ∃ (α β : ℝ) (v T : ℝ → ℝ) (m M : ℝ), α < tStar ∧ tStar < β ∧ 0 < m ∧ m ≤ M ∧
      ContDiffOn ℝ ∞ v (Set.Ioo α β) ∧ v tStar = 0 ∧
      (∀ t ∈ Set.Ioo α β, v t ^ 3 = 3 * (ψ tStar - ψ t)) ∧
      (∀ t ∈ Set.Ioo α β, m ≤ deriv v t ∧ deriv v t ≤ M) ∧
      StrictMonoOn v (Set.Ioo α β) ∧
      ContDiffOn ℝ ∞ T (Set.Ioo (v α) (v β)) ∧ 0 ∈ Set.Ioo (v α) (v β) ∧ T 0 = tStar ∧
      (∀ w ∈ Set.Ioo (v α) (v β), T w ∈ Set.Ioo α β ∧ v (T w) = w ∧
        ψ (T w) = ψ tStar - w ^ 3 / 3 ∧ 1 / M ≤ deriv T w ∧ deriv T w ≤ 1 / m) ∧
      (∀ t ∈ Set.Ioo α β, v t ∈ Set.Ioo (v α) (v β) ∧ T (v t) = t) := by
  intro hc ψ tStar
  obtain ⟨-, -, tp, -, -, -, -, h1, h2, h3, h4, -⟩ := fold_auxiliary_cubic_geometry κ hκ
  have hψ : ContDiff ℝ ∞ ψ := ScalarFoldFIN057.scalarPsi_contDiff_FIN057 κ hc
  set φ : ℝ → ℝ := fun t => ψ tStar - ψ t with hφdef
  have e1 : deriv φ = fun t => -deriv ψ t := funext fun t => deriv_const_sub _
  have e2 : deriv (deriv φ) = fun t => -deriv (deriv ψ) t := by
    rw [e1]; funext t; exact deriv.neg
  have e3 : deriv (deriv (deriv φ)) = fun t => -deriv (deriv (deriv ψ)) t := by
    rw [e2]; funext t; exact deriv.neg
  have hφ : ContDiff ℝ ∞ φ := contDiff_const.sub hψ
  have hφ0 : φ tStar = 0 := by simp [hφdef]
  have hφ1 : deriv φ tStar = 0 := by rw [e1]; simp only [neg_eq_zero]; exact h1
  have hφ2 : deriv (deriv φ) tStar = 0 := by rw [e2]; simp only [neg_eq_zero]; exact h2
  have hφ3 : 0 < deriv (deriv (deriv φ)) tStar := by
    rw [e3]; show 0 < -deriv (deriv (deriv ψ)) tStar
    have : deriv (deriv (deriv ψ)) tStar = deriv (deriv besselRatio) (scalarFoldPoint κ) := h3
    rw [this]; linarith
  obtain ⟨a, ha, hapos, hfac⟩ := ScalarFoldFIN057.cubic_factor_FIN057 hφ hφ0 hφ1 hφ2 hφ3
  obtain ⟨α, β, v, T, m, M, hα, hβ, hm, hmM, hvsm, hv0, hcube, hbd, hmono, hTsm, hT0, hJ0,
    hT1, hT2⟩ := ScalarFoldFIN057.coordinate_FIN057 (φ := φ) ha hapos hfac
  refine ⟨α, β, v, T, m, M, hα, hβ, hm, hmM, hvsm, hv0, hcube, hbd, hmono, hTsm, hJ0, hT0,
    fun w hw => ?_, hT2⟩
  obtain ⟨hI, hv, hb1, hb2⟩ := hT1 w hw
  refine ⟨hI, hv, ?_, hb1, hb2⟩
  have := hcube (T w) hI
  rw [hv] at this
  show ψ (T w) = ψ tStar - w ^ 3 / 3
  linarith

end DGPS.FiniteN
