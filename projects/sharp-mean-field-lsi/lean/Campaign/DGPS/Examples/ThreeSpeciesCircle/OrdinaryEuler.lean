import DGPS.Examples.ThreeSpeciesCircle.OrdinaryOptimizers

/-!
# Weak Euler equation for ordinary-reference optimizers (STR025b-ii)

A minimizer of `Q = I/(2H)` over positive-entropy densities satisfies the weak Euler
equation, tested against every `H¹` function `φ` with weak gradient `G`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The entropy integrand `v ↦ v² log v²`. -/
noncomputable def eulF (v : ℝ) : ℝ := v ^ 2 * Real.log (v ^ 2)

/-- Its derivative `2 v log v² + 2 v`. -/
noncomputable def eulF' (v : ℝ) : ℝ := 2 * v * Real.log (v ^ 2) + 2 * v

theorem continuous_eulF : Continuous eulF := by
  have := Real.continuous_mul_log.comp (continuous_pow 2 : Continuous fun v : ℝ => v ^ 2)
  exact this

theorem hasDerivAt_eulF (v : ℝ) : HasDerivAt eulF (eulF' v) v := by
  by_cases hv : v = 0
  · subst hv
    have h0 : eulF' 0 = 0 := by simp [eulF']
    rw [h0, hasDerivAt_iff_tendsto_slope]
    have key : Tendsto (fun t : ℝ => t * Real.log (t ^ 2)) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun t : ℝ => |t| * Real.log |t| :=
        Real.continuous_mul_log.comp continuous_abs
      have h1 : Tendsto (fun t : ℝ => |t| * Real.log |t|) (𝓝 0) (𝓝 0) := by
        simpa using hc.tendsto 0
      have h2 : Tendsto (fun t : ℝ => 2 * (|t| * Real.log |t|)) (𝓝 0) (𝓝 0) := by
        simpa using h1.const_mul 2
      refine squeeze_zero_norm (fun t => ?_) (by simpa using h2.norm)
      rw [Real.norm_eq_abs, Real.log_pow]
      push_cast
      rw [abs_mul, abs_mul, abs_two]
      linarith
    refine (key.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    rw [slope_def_field]
    simp only [eulF]
    field_simp
    ring
  · have h1 : HasDerivAt (fun v : ℝ => v ^ 2) (2 * v) v := by simpa using hasDerivAt_pow 2 v
    have h2 := (h1.log (pow_ne_zero 2 hv))
    have h3 := (hasDerivAt_pow 2 v).mul h2
    convert h3 using 1
    · rfl
    · simp only [eulF']
      push_cast
      field_simp

theorem abs_mul_log_sq_le (v : ℝ) : |v * Real.log (v ^ 2)| ≤ 2 + 2 * v ^ 2 := by
  by_cases hv : v = 0
  · subst hv; simp
  have hlog : Real.log (v ^ 2) = 2 * Real.log |v| := by
    rw [Real.log_pow, Real.log_abs]; push_cast; ring
  have hpos : 0 < |v| := abs_pos.2 hv
  rw [hlog, abs_mul, abs_mul, abs_two]
  rcases le_or_gt 1 |v| with h1 | h1
  · have h2 : |Real.log (|v|)| ≤ |v| := by
      rw [abs_of_nonneg (Real.log_nonneg h1)]
      have := Real.log_le_sub_one_of_pos hpos
      linarith
    have : |v| * |Real.log (|v|)| ≤ v ^ 2 := by
      calc _ ≤ |v| * |v| := mul_le_mul_of_nonneg_left h2 hpos.le
        _ = v ^ 2 := by rw [← sq, sq_abs]
    linarith
  · have h2 : |Real.log (|v|)| ≤ |v|⁻¹ := by
      rw [abs_of_nonpos (Real.log_nonpos hpos.le h1.le)]
      have := Real.log_le_sub_one_of_pos (inv_pos.2 hpos)
      rw [Real.log_inv] at this
      have h3 : |v|⁻¹ - 1 ≤ |v|⁻¹ := by linarith
      linarith
    have : |v| * |Real.log (|v|)| ≤ 1 := by
      calc _ ≤ |v| * |v|⁻¹ := mul_le_mul_of_nonneg_left h2 hpos.le
        _ = 1 := mul_inv_cancel₀ hpos.ne'
    nlinarith [sq_nonneg v]

theorem abs_eulF'_le (v : ℝ) : |eulF' v| ≤ 5 + 5 * v ^ 2 := by
  have h1 := abs_mul_log_sq_le v
  have h2 : eulF' v = 2 * (v * Real.log (v ^ 2)) + 2 * v := by simp only [eulF']; ring
  rw [h2]
  calc _ ≤ |2 * (v * Real.log (v ^ 2))| + |2 * v| := abs_add_le _ _
    _ = 2 * |v * Real.log (v ^ 2)| + 2 * |v| := by simp only [abs_mul, abs_two]
    _ ≤ _ := by nlinarith [sq_abs v, sq_nonneg (|v| - 1)]

theorem measurable_eulF' : Measurable eulF' := by
  unfold eulF'; fun_prop

theorem hasDerivAt_integral_eulF {w φ : Torus 1 → ℝ} {Gw Gφ : Torus 1 → Tangent 1}
    (hw : IsWeakGradient w Gw) (hφ : IsWeakGradient φ Gφ) :
    HasDerivAt (fun t : ℝ => ∫ x, eulF (w x + t * φ x) ∂haar 1)
      (∫ x, eulF' (w x) * φ x ∂haar 1) 0 := by
  obtain ⟨B, hB0, hB⟩ := exists_ae_bound_one hφ
  have hwm := hw.memLp.aestronglyMeasurable
  have hφm := hφ.memLp.aestronglyMeasurable
  have hint_w : Integrable (fun x => w x ^ 2) (haar 1) := hw.memLp.integrable_sq
  have hint_φ : Integrable (fun x => φ x ^ 2) (haar 1) := hφ.memLp.integrable_sq
  have hint_φ1 : Integrable φ (haar 1) := hφ.memLp.integrable one_le_two
  have hbound_int : Integrable (fun x => 5 * |φ x| + 10 * B * w x ^ 2 + 10 * B * φ x ^ 2)
      (haar 1) :=
    ((hint_φ1.abs.const_mul 5).add (hint_w.const_mul _)).add (hint_φ.const_mul _)
  have hvm : ∀ t : ℝ, AEStronglyMeasurable (fun x => w x + t * φ x) (haar 1) :=
    fun t => hwm.add (hφm.const_mul t)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (t : ℝ) x => eulF (w x + t * φ x))
    (F' := fun (t : ℝ) x => eulF' (w x + t * φ x) * φ x)
    (x₀ := 0) (s := Metric.ball 0 1) (bound := fun x => 5 * |φ x| + 10 * B * w x ^ 2 + 10 * B * φ x ^ 2)
    (Metric.ball_mem_nhds _ one_pos)
    (Eventually.of_forall fun t => continuous_eulF.comp_aestronglyMeasurable (hvm t))
    (by
      have := integrable_sq_mul_log_sq_of_memH1 1 (⟨Gw, hw⟩ : MemH1 w)
      simpa [eulF] using this)
    (by
      have h1 : AEMeasurable (fun x => w x + (0:ℝ) * φ x) (haar 1) := (hvm 0).aemeasurable
      exact ((measurable_eulF'.comp_aemeasurable h1).mul hφm.aemeasurable).aestronglyMeasurable)
    (by
      filter_upwards [hB] with x hx t ht
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := abs_eulF'_le (w x + t * φ x)
      have h2 : (w x + t * φ x) ^ 2 ≤ 2 * w x ^ 2 + 2 * φ x ^ 2 := by
        have : (t * φ x) ^ 2 ≤ φ x ^ 2 := by
          rw [mul_pow]
          have : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
          nlinarith [sq_nonneg (φ x)]
        nlinarith [sq_nonneg (w x - t * φ x)]
      have h3 : |φ x| ≤ B := hx
      have h4 : 0 ≤ |φ x| := abs_nonneg _
      have h5 : |eulF' (w x + t * φ x)| ≤ 5 + 10 * w x ^ 2 + 10 * φ x ^ 2 := by linarith
      calc |eulF' (w x + t * φ x)| * |φ x| ≤ (5 + 10 * w x ^ 2 + 10 * φ x ^ 2) * |φ x| :=
            mul_le_mul_of_nonneg_right h5 h4
        _ = 5 * |φ x| + 10 * w x ^ 2 * |φ x| + 10 * φ x ^ 2 * |φ x| := by ring
        _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left h3 (sq_nonneg (w x))
          have := mul_le_mul_of_nonneg_left h3 (sq_nonneg (φ x))
          nlinarith)
    hbound_int
    (by
      refine Eventually.of_forall fun x t _ => ?_
      have hg : HasDerivAt (fun t : ℝ => w x + t * φ x) (φ x) t := by
        simpa using ((hasDerivAt_id t).mul_const (φ x)).const_add (w x)
      exact (hasDerivAt_eulF (w x + t * φ x)).comp t hg)
  simpa using hmain.2

theorem integrable_mul_bdd_two {c f1 f2 : Torus 1 → ℝ} {C : ℝ}
    (hc : AEStronglyMeasurable c (haar 1)) (hcb : ∀ x, |c x| ≤ C)
    (h1 : MemLp f1 2 (haar 1)) (h2 : MemLp f2 2 (haar 1)) :
    Integrable (fun x => f1 x * f2 x * c x) (haar 1) :=
  (h1.integrable_mul h2).mul_bdd (c := C) hc (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hcb x)

theorem integral_quad {c f1 f2 : Torus 1 → ℝ} {C : ℝ}
    (hc : AEStronglyMeasurable c (haar 1)) (hcb : ∀ x, |c x| ≤ C)
    (h1 : MemLp f1 2 (haar 1)) (h2 : MemLp f2 2 (haar 1)) (t : ℝ) :
    ∫ x, (f1 x + t * f2 x) ^ 2 * c x ∂haar 1 =
      ∫ x, f1 x * f1 x * c x ∂haar 1 + 2 * t * ∫ x, f1 x * f2 x * c x ∂haar 1 +
        t ^ 2 * ∫ x, f2 x * f2 x * c x ∂haar 1 := by
  have i11 := integrable_mul_bdd_two hc hcb h1 h1
  have i12 := integrable_mul_bdd_two hc hcb h1 h2
  have i22 := integrable_mul_bdd_two hc hcb h2 h2
  have : (fun x => (f1 x + t * f2 x) ^ 2 * c x) = fun x =>
      f1 x * f1 x * c x + (2 * t * (f1 x * f2 x * c x) + t ^ 2 * (f2 x * f2 x * c x)) := by
    funext x; ring
  have i3 : Integrable (fun x => 2 * t * (f1 x * f2 x * c x) + t ^ 2 * (f2 x * f2 x * c x))
      (haar 1) := (i12.const_mul _).add (i22.const_mul _)
  rw [this, integral_add i11 i3, integral_add (i12.const_mul _) (i22.const_mul _),
    integral_const_mul, integral_const_mul]
  ring

theorem hasDerivAt_integral_quad {c f1 f2 : Torus 1 → ℝ} {C : ℝ}
    (hc : AEStronglyMeasurable c (haar 1)) (hcb : ∀ x, |c x| ≤ C)
    (h1 : MemLp f1 2 (haar 1)) (h2 : MemLp f2 2 (haar 1)) :
    HasDerivAt (fun t : ℝ => ∫ x, (f1 x + t * f2 x) ^ 2 * c x ∂haar 1)
      (2 * ∫ x, f1 x * f2 x * c x ∂haar 1) 0 := by
  have : (fun t : ℝ => ∫ x, (f1 x + t * f2 x) ^ 2 * c x ∂haar 1) = fun t =>
      ∫ x, f1 x * f1 x * c x ∂haar 1 + 2 * t * ∫ x, f1 x * f2 x * c x ∂haar 1 +
        t ^ 2 * ∫ x, f2 x * f2 x * c x ∂haar 1 := funext (integral_quad hc hcb h1 h2)
  rw [this]
  have e : (fun t : ℝ => ∫ x, f1 x * f1 x * c x ∂haar 1 + 2 * t * ∫ x, f1 x * f2 x * c x ∂haar 1 +
        t ^ 2 * ∫ x, f2 x * f2 x * c x ∂haar 1) = (fun x => ∫ x, f1 x * f1 x * c x ∂haar 1 +
        2 * id x * ∫ x, f1 x * f2 x * c x ∂haar 1) +
        fun y => y ^ 2 * ∫ x, f2 x * f2 x * c x ∂haar 1 := by
    funext t; simp
  rw [e]
  have := (((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const (∫ x, f1 x * f2 x * c x ∂haar 1)).const_add
    (∫ x, f1 x * f1 x * c x ∂haar 1)
  have h3 := this.add (((hasDerivAt_pow 2 (0:ℝ))).mul_const (∫ x, f2 x * f2 x * c x ∂haar 1))
  convert h3 using 1
  simp

/-- The absolute density `|v|² / ∫ v²` obtained from an `H¹` function `v` with `∫ v² > 0`. -/
noncomputable def normAbs (v : Torus 1 → ℝ) (hv : MemH1 v) (hn : 0 < ∫ x, v x ^ 2 ∂haar 1) :
    AbsoluteDensity 1 where
  sqrt := fun x => |v x| / Real.sqrt (∫ x, v x ^ 2 ∂haar 1)
  sqrt_mem := by
    obtain ⟨G, hG⟩ := hv
    exact ⟨_, ((hG.abs).smul (Real.sqrt (∫ x, v x ^ 2 ∂haar 1))⁻¹).congr_ae
      (Eventually.of_forall fun x => by simp [div_eq_inv_mul]) (Eventually.of_forall fun x => rfl)⟩
  sqrt_nonneg := Eventually.of_forall fun x => by positivity
  mass_one := by
    simp only [div_pow, sq_abs, Real.sq_sqrt hn.le]
    rw [integral_div, div_self hn.ne']

theorem normAbs_density (v : Torus 1 → ℝ) (hv : MemH1 v) (hn : 0 < ∫ x, v x ^ 2 ∂haar 1)
    (x : Torus 1) : (normAbs v hv hn).density x = v x ^ 2 / ∫ x, v x ^ 2 ∂haar 1 := by
  simp only [AbsoluteDensity.density, normAbs, div_pow, sq_abs, Real.sq_sqrt hn.le]

theorem normAbs_fisher (h : ℝ) {v : Torus 1 → ℝ} {G : Torus 1 → Tangent 1}
    (hG : IsWeakGradient v G) (hn : 0 < ∫ x, v x ^ 2 ∂haar 1) :
    ordinaryFisher h (normAbs v ⟨G, hG⟩ hn) = ENNReal.ofReal
      ((∫ x, (2 * G x 0 - v x * logScore h x) ^ 2 ∂haar 1) / ∫ x, v x ^ 2 ∂haar 1) := by
  rw [ordinaryFisher_eq]
  congr 1
  set n := ∫ x, v x ^ 2 ∂haar 1 with hn_def
  have hGa := (hG.abs).smul (Real.sqrt n)⁻¹
  have hu : IsWeakGradient (normAbs v ⟨G, hG⟩ hn).sqrt
      (fun x => (Real.sqrt n)⁻¹ • (if 0 < v x then G x else if v x < 0 then -G x else 0)) :=
    hGa.congr_ae (Eventually.of_forall fun x => by simp [normAbs, div_eq_inv_mul, hn_def])
      (Eventually.of_forall fun x => rfl)
  have hae := weakGradient_ae_eq hu
  rw [← integral_div]
  have hsn : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn.le
  have hsp : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  refine integral_congr_ae ?_
  filter_upwards [hae, hG.ae_grad_eq_zero 0] with x hx hz
  have hx0 : weakGradient (normAbs v ⟨G, hG⟩ hn).sqrt (normAbs v ⟨G, hG⟩ hn).sqrt_mem x 0 =
      (Real.sqrt n)⁻¹ * (if 0 < v x then G x 0 else if v x < 0 then -G x 0 else 0) := by
    have := congrArg (fun y : Tangent 1 => y 0) hx
    simp only at this
    rw [this]
    split_ifs <;> simp
  rw [hx0]
  simp only [normAbs, hn_def.symm]
  rcases lt_trichotomy (v x) 0 with h1 | h1 | h1
  · have e : (if 0 < v x then G x 0 else if v x < 0 then -G x 0 else 0) = -G x 0 := by
      simp [not_lt.2 h1.le, h1]
    rw [e, abs_of_neg h1]
    field_simp
    rw [hsn]; ring
  · have := hz h1
    rw [h1]; simp [this]
  · have e : (if 0 < v x then G x 0 else if v x < 0 then -G x 0 else 0) = G x 0 := by
      simp [h1]
    rw [e, abs_of_pos h1]
    field_simp
    rw [hsn]; ring

theorem normAbs_entropy (h : ℝ) {v : Torus 1 → ℝ} (hv : MemH1 v)
    (hn : 0 < ∫ x, v x ^ 2 ∂haar 1) :
    ordinaryEntropy h (normAbs v hv hn) = ENNReal.ofReal
      ((∫ x, eulF (v x) ∂haar 1) / (∫ x, v x ^ 2 ∂haar 1) - Real.log (∫ x, v x ^ 2 ∂haar 1) -
        (∫ x, v x ^ 2 * Real.log (referenceDensity h x) ∂haar 1) / ∫ x, v x ^ 2 ∂haar 1) := by
  rw [ordinaryEntropy_eq, circleEntropy_eq]
  congr 1
  set n := ∫ x, v x ^ 2 ∂haar 1 with hn_def
  obtain ⟨G, hG⟩ := id hv
  have i1 : Integrable (fun x => eulF (v x)) (haar 1) :=
    integrable_sq_mul_log_sq_of_memH1 1 hv
  have i2 : Integrable (fun x => v x ^ 2) (haar 1) := hG.memLp.integrable_sq
  have i3 : Integrable (fun x => v x ^ 2 * Real.log (referenceDensity h x)) (haar 1) :=
    i2.mul_bdd (c := 2 * |h|) ((continuous_referenceDensity h).log
      (fun x => (referenceDensity_pos (h := h) x).ne')).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact abs_log_referenceDensity_le h x)
  have e1 : ∫ x, (normAbs v hv hn).density x * Real.log ((normAbs v hv hn).density x)
      ∂haar 1 = (∫ x, eulF (v x) ∂haar 1) / n - Real.log n := by
    have : (fun x => (normAbs v hv hn).density x *
        Real.log ((normAbs v hv hn).density x)) =
        fun x => eulF (v x) / n - Real.log n * (v x ^ 2 / n) := by
      funext x
      rw [normAbs_density]
      by_cases h0 : v x = 0
      · simp [h0, eulF]
      · have : v x ^ 2 ≠ 0 := pow_ne_zero 2 h0
        rw [Real.log_div this hn.ne']
        simp only [eulF]
        ring
    rw [this, integral_sub (i1.div_const _) ((i2.div_const _).const_mul _), integral_div,
      integral_const_mul, integral_div, ← hn_def]
    field_simp
  have e2 : ∫ x, (normAbs v hv hn).density x * Real.log (referenceDensity h x) ∂haar 1 =
      (∫ x, v x ^ 2 * Real.log (referenceDensity h x) ∂haar 1) / n := by
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [normAbs_density]
    ring
  rw [e1, e2]

theorem euler_scalar {A n Φ R : ℝ → ℝ} {A' n' Φ' R' : ℝ}
    (hA : HasDerivAt A A' 0) (hn : HasDerivAt n n' 0) (hΦ : HasDerivAt Φ Φ' 0)
    (hR : HasDerivAt R R' 0) (hn0 : n 0 = 1) (hE : 0 < Φ 0 - R 0)
    (hmin : ∀ᶠ t in 𝓝 (0:ℝ), 0 < Φ t / n t - Real.log (n t) - R t / n t →
      A 0 / (2 * (Φ 0 - R 0)) ≤
        A t / n t / (2 * (Φ t / n t - Real.log (n t) - R t / n t))) :
    (A' - A 0 * n') * (Φ 0 - R 0) = A 0 * (Φ' - R' - n' * ((Φ 0 - R 0) + 1)) := by
  have hn1 : n 0 ≠ 0 := by rw [hn0]; exact one_ne_zero
  set E : ℝ → ℝ := fun t => Φ t / n t - Real.log (n t) - R t / n t with hEdef
  have hE' : HasDerivAt E ((Φ' * n 0 - Φ 0 * n') / n 0 ^ 2 - n' / n 0 -
      (R' * n 0 - R 0 * n') / n 0 ^ 2) 0 := ((hΦ.div hn hn1).sub (hn.log hn1)).sub (hR.div hn hn1)
  have hE0 : E 0 = Φ 0 - R 0 := by simp [hEdef, hn0]
  have hEc : ContinuousAt E 0 := hE'.continuousAt
  have hpos : ∀ᶠ t in 𝓝 (0:ℝ), 0 < E t := hEc.eventually (lt_mem_nhds (by rw [hE0]; exact hE))
  have hAn : HasDerivAt (fun t => A t / n t) ((A' * n 0 - A 0 * n') / n 0 ^ 2) 0 := hA.div hn hn1
  have hQ : HasDerivAt (fun t => A t / n t / (2 * E t)) _ 0 :=
    hAn.div (hE'.const_mul 2) (by rw [hE0]; positivity)
  have hloc : IsLocalMin (fun t => A t / n t / (2 * E t)) 0 := by
    filter_upwards [hmin, hpos] with t h1 h2
    have := h1 h2
    have e0 : A 0 / n 0 / (2 * E 0) = A 0 / (2 * (Φ 0 - R 0)) := by rw [hn0, hE0, div_one]
    show A 0 / n 0 / (2 * E 0) ≤ A t / n t / (2 * E t)
    rw [e0]; exact this
  have h0 := hloc.hasDerivAt_eq_zero hQ
  rw [hE0, hn0] at h0
  have hx : 0 < 2 * (Φ 0 - R 0) := by positivity
  field_simp at h0
  nlinarith [h0]

theorem toReal_quot (a b : ℝ≥0∞) : (a / (2 * b)).toReal = a.toReal / (2 * b.toReal) := by
  rw [ENNReal.toReal_div, ENNReal.toReal_mul]; simp

theorem integrable_mul_mul_log {w φ : Torus 1 → ℝ} {Gw Gφ : Torus 1 → Tangent 1}
    (hw : IsWeakGradient w Gw) (hφ : IsWeakGradient φ Gφ) :
    Integrable (fun x => w x * φ x * Real.log (w x ^ 2)) (haar 1) := by
  obtain ⟨B, hB0, hB⟩ := exists_ae_bound_one hφ
  have hint : Integrable (fun x => B * (2 + 2 * w x ^ 2)) (haar 1) :=
    (integrable_const (2:ℝ) |>.add (hw.memLp.integrable_sq.const_mul 2)).const_mul B
  refine hint.mono' ?_ ?_
  · exact (hw.memLp.aestronglyMeasurable.mul hφ.memLp.aestronglyMeasurable).mul
      (Real.measurable_log.comp_aemeasurable
        (hw.memLp.aestronglyMeasurable.aemeasurable.pow_const 2)).aestronglyMeasurable
  · filter_upwards [hB] with x hx
    have := abs_mul_log_sq_le (w x)
    rw [Real.norm_eq_abs, show w x * φ x * Real.log (w x ^ 2) =
      (w x * Real.log (w x ^ 2)) * φ x by ring, abs_mul]
    calc _ ≤ (2 + 2 * w x ^ 2) * B :=
          mul_le_mul this hx (abs_nonneg _) (by positivity)
      _ = _ := by ring

theorem ordinaryOptimizer_weakEuler (h : ℝ) (ρ : AbsoluteDensity 1)
    (hpos : 0 < ordinaryEntropy h ρ)
    (hmin : ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
      str025_quot h ρ ≤ str025_quot h ρ')
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    ∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * logScore h x) *
        (2 * G x 0 - φ x * logScore h x) ∂haar 1 =
      2 * (str025_quot h ρ).toReal * ∫ x, ρ.sqrt x * φ x *
        (Real.log (ρ.sqrt x ^ 2) - Real.log (referenceDensity h x)) ∂haar 1 := by
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  obtain ⟨w, hwdef⟩ : ∃ w, w = ρ.sqrt := ⟨_, rfl⟩
  obtain ⟨Gw, hGwdef⟩ : ∃ Gw, Gw = weakGradient ρ.sqrt ρ.sqrt_mem := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s, s = logScore h := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : Torus 1 → ℝ, L = fun x => Real.log (referenceDensity h x) := ⟨_, rfl⟩
  rw [← hGwdef] at hw
  have hρw : ρ.sqrt = w := hwdef.symm
  rw [← hGwdef, ← hwdef, ← hsdef]
  rw [← hwdef] at hw
  have hLc : Continuous L := by
    rw [hLdef]
    exact (continuous_referenceDensity h).log (fun x => (referenceDensity_pos (h := h) x).ne')
  have hLb : ∀ x, |L x| ≤ 2 * |h| := fun x => by rw [hLdef]; exact abs_log_referenceDensity_le h x
  have hLm : AEStronglyMeasurable L (haar 1) := hLc.aestronglyMeasurable
  have hw1 : ∫ x, w x ^ 2 ∂haar 1 = 1 := by rw [hwdef]; exact ρ.mass_one
  have hsm : MemLp (fun x => w x * s x) 2 (haar 1) := by
    rw [hsdef]; exact memLp_mul_logScore h hw.memLp
  have hsm' : MemLp (fun x => φ x * s x) 2 (haar 1) := by
    rw [hsdef]; exact memLp_mul_logScore h hφ.memLp
  have hp : MemLp (fun x => 2 * Gw x 0 - w x * s x) 2 (haar 1) :=
    ((memLp_coord hw.memLp_grad 0).const_mul 2).sub hsm
  have hr : MemLp (fun x => 2 * G x 0 - φ x * s x) 2 (haar 1) :=
    ((memLp_coord hφ.memLp_grad 0).const_mul 2).sub hsm'
  have hone : AEStronglyMeasurable (fun _ : Torus 1 => (1:ℝ)) (haar 1) := aestronglyMeasurable_const
  -- the four scalar functions
  have hv : ∀ t : ℝ, IsWeakGradient (fun x => w x + t * φ x) (fun x => Gw x + t • G x) :=
    fun t => hw.add (hφ.smul t)
  have hnf : HasDerivAt (fun t : ℝ => ∫ x, (w x + t * φ x) ^ 2 ∂haar 1)
      (2 * ∫ x, w x * φ x ∂haar 1) 0 := by
    have := hasDerivAt_integral_quad (c := fun _ => (1:ℝ)) (C := 1) hone
      (fun x => by simp) hw.memLp hφ.memLp
    simpa using this
  have hAf : HasDerivAt (fun t : ℝ => ∫ x, ((2 * Gw x 0 - w x * s x) +
      t * (2 * G x 0 - φ x * s x)) ^ 2 ∂haar 1)
      (2 * ∫ x, (2 * Gw x 0 - w x * s x) * (2 * G x 0 - φ x * s x) ∂haar 1) 0 := by
    have := hasDerivAt_integral_quad (c := fun _ => (1:ℝ)) (C := 1) hone
      (fun x => by simp) hp hr
    simpa using this
  have hRf : HasDerivAt (fun t : ℝ => ∫ x, (w x + t * φ x) ^ 2 * L x ∂haar 1)
      (2 * ∫ x, w x * φ x * L x ∂haar 1) 0 :=
    hasDerivAt_integral_quad hLm hLb hw.memLp hφ.memLp
  have hΦf := hasDerivAt_integral_eulF hw hφ
  have hJ : ordinaryFisher h ρ = ENNReal.ofReal
      (∫ x, (2 * Gw x 0 - w x * s x) ^ 2 ∂haar 1) := by
    rw [ordinaryFisher_eq, ← hGwdef, ← hwdef, ← hsdef]
  have hE : ordinaryEntropy h ρ = ENNReal.ofReal
      ((∫ x, eulF (w x + (0:ℝ) * φ x) ∂haar 1) -
        ∫ x, (w x + (0:ℝ) * φ x) ^ 2 * L x ∂haar 1) := by
    rw [ordinaryEntropy_eq, circleEntropy_eq]
    simp only [AbsoluteDensity.density, zero_mul, add_zero, eulF, hLdef]
    rw [← hwdef]
  have hEpos : 0 < (∫ x, eulF (w x + (0:ℝ) * φ x) ∂haar 1) -
        ∫ x, (w x + (0:ℝ) * φ x) ^ 2 * L x ∂haar 1 := by
    rw [hE] at hpos; exact ENNReal.ofReal_pos.1 hpos
  have hJ0 : 0 ≤ ∫ x, (2 * Gw x 0 - w x * s x) ^ 2 ∂haar 1 :=
    integral_nonneg fun x => sq_nonneg _
  have hq0 : (str025_quot h ρ).toReal = (∫ x, (2 * Gw x 0 - w x * s x) ^ 2 ∂haar 1) /
      (2 * ((∫ x, eulF (w x + (0:ℝ) * φ x) ∂haar 1) -
        ∫ x, (w x + (0:ℝ) * φ x) ^ 2 * L x ∂haar 1)) := by
    unfold str025_quot
    rw [toReal_quot, hJ, hE, ENNReal.toReal_ofReal hJ0, ENNReal.toReal_ofReal hEpos.le]
  have hn0 : (∫ x, (w x + (0:ℝ) * φ x) ^ 2 ∂haar 1) = 1 := by simpa using hw1
  have hnpos : ∀ᶠ t in 𝓝 (0:ℝ), 0 < ∫ x, (w x + t * φ x) ^ 2 ∂haar 1 :=
    hnf.continuousAt.eventually (lt_mem_nhds (by show (0:ℝ) < ∫ x, (w x + (0:ℝ) * φ x) ^ 2 ∂haar 1; rw [hn0]; exact one_pos))
  have hmin' : ∀ᶠ t in 𝓝 (0:ℝ),
      0 < (∫ x, eulF (w x + t * φ x) ∂haar 1) / (∫ x, (w x + t * φ x) ^ 2 ∂haar 1) -
        Real.log (∫ x, (w x + t * φ x) ^ 2 ∂haar 1) -
        (∫ x, (w x + t * φ x) ^ 2 * L x ∂haar 1) / (∫ x, (w x + t * φ x) ^ 2 ∂haar 1) →
      (∫ x, ((2 * Gw x 0 - w x * s x) + (0:ℝ) * (2 * G x 0 - φ x * s x)) ^ 2 ∂haar 1) /
          (2 * ((∫ x, eulF (w x + (0:ℝ) * φ x) ∂haar 1) -
            ∫ x, (w x + (0:ℝ) * φ x) ^ 2 * L x ∂haar 1)) ≤
        (∫ x, ((2 * Gw x 0 - w x * s x) + t * (2 * G x 0 - φ x * s x)) ^ 2 ∂haar 1) /
          (∫ x, (w x + t * φ x) ^ 2 ∂haar 1) /
          (2 * ((∫ x, eulF (w x + t * φ x) ∂haar 1) / (∫ x, (w x + t * φ x) ^ 2 ∂haar 1) -
            Real.log (∫ x, (w x + t * φ x) ^ 2 ∂haar 1) -
            (∫ x, (w x + t * φ x) ^ 2 * L x ∂haar 1) / (∫ x, (w x + t * φ x) ^ 2 ∂haar 1))) := by
    filter_upwards [hnpos] with t hnt hEt
    have hvm : MemH1 (fun x => w x + t * φ x) := ⟨_, hv t⟩
    have hent : ordinaryEntropy h (normAbs _ hvm hnt) = ENNReal.ofReal
        ((∫ x, eulF (w x + t * φ x) ∂haar 1) / (∫ x, (w x + t * φ x) ^ 2 ∂haar 1) -
            Real.log (∫ x, (w x + t * φ x) ^ 2 ∂haar 1) -
            (∫ x, (w x + t * φ x) ^ 2 * L x ∂haar 1) / (∫ x, (w x + t * φ x) ^ 2 ∂haar 1)) := by
      rw [normAbs_entropy, hLdef]
    have hfish : ordinaryFisher h (normAbs _ hvm hnt) = ENNReal.ofReal
        ((∫ x, ((2 * Gw x 0 - w x * s x) + t * (2 * G x 0 - φ x * s x)) ^ 2 ∂haar 1) /
          (∫ x, (w x + t * φ x) ^ 2 ∂haar 1)) := by
      have := normAbs_fisher h (hv t) hnt
      rw [← hsdef] at this
      rw [this]
      have e : (fun x => (2 * (Gw x + t • G x) 0 - (w x + t * φ x) * s x) ^ 2) =
          fun x => ((2 * Gw x 0 - w x * s x) + t * (2 * G x 0 - φ x * s x)) ^ 2 := by
        funext x
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      simp only [e]
    have hA0 : 0 ≤ ∫ x, ((2 * Gw x 0 - w x * s x) + t * (2 * G x 0 - φ x * s x)) ^ 2 ∂haar 1 :=
      integral_nonneg fun x => sq_nonneg _
    have hpos' : 0 < ordinaryEntropy h (normAbs _ hvm hnt) := by
      rw [hent]; exact ENNReal.ofReal_pos.2 hEt
    have hle := hmin _ hpos'
    have hfin : str025_quot h (normAbs _ hvm hnt) ≠ ⊤ := by
      unfold str025_quot
      rw [hent, hfish]
      exact ENNReal.div_ne_top ENNReal.ofReal_ne_top
        (mul_ne_zero (by norm_num) (by rw [← hent]; exact hpos'.ne'))
    have := ENNReal.toReal_mono hfin hle
    rw [hq0] at this
    unfold str025_quot at this
    rw [toReal_quot, hent, hfish, ENNReal.toReal_ofReal hEt.le,
      ENNReal.toReal_ofReal (div_nonneg hA0 hnt.le)] at this
    simpa using this
  have key := euler_scalar hAf hnf hΦf hRf hn0 hEpos hmin'
  have i1 := integrable_mul_mul_log hw hφ
  have i2 : Integrable (fun x => w x * φ x * L x) (haar 1) :=
    integrable_mul_bdd_two hLm hLb hw.memLp hφ.memLp
  have i0 : Integrable (fun x => w x * φ x) (haar 1) := hw.memLp.integrable_mul hφ.memLp
  have hΦ' : ∫ x, eulF' (w x) * φ x ∂haar 1 =
      2 * ∫ x, w x * φ x * Real.log (w x ^ 2) ∂haar 1 + 2 * ∫ x, w x * φ x ∂haar 1 := by
    have e : (fun x => eulF' (w x) * φ x) =
        fun x => 2 * (w x * φ x * Real.log (w x ^ 2)) + 2 * (w x * φ x) := by
      funext x; simp only [eulF']; ring
    rw [e, integral_add (i1.const_mul 2) (i0.const_mul 2), integral_const_mul,
      integral_const_mul]
  have hK : ∫ x, w x * φ x * (Real.log (w x ^ 2) - Real.log (referenceDensity h x)) ∂haar 1 =
      ∫ x, w x * φ x * Real.log (w x ^ 2) ∂haar 1 - ∫ x, w x * φ x * L x ∂haar 1 := by
    rw [← integral_sub i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hLdef]; ring
  rw [hK, hq0]
  simp only [zero_mul, add_zero] at key hEpos ⊢
  rw [hΦ'] at key
  try simp only [hn0] at key
  set E0 := (∫ x, eulF (w x) ∂haar 1) - ∫ x, w x ^ 2 * L x ∂haar 1 with hE0
  have hE0p : 0 < E0 := hEpos
  generalize (∫ x, (2 * Gw x 0 - w x * s x) * (2 * G x 0 - φ x * s x) ∂haar 1) = B at key ⊢
  generalize (∫ x, (2 * Gw x 0 - w x * s x) ^ 2 ∂haar 1) = J at key ⊢
  generalize (∫ x, w x * φ x ∂haar 1) = a at key ⊢
  generalize (∫ x, w x * φ x * Real.log (w x ^ 2) ∂haar 1) = M1 at key ⊢
  generalize (∫ x, w x * φ x * L x ∂haar 1) = M2 at key ⊢
  have hB : B * E0 = J * (M1 - M2) := by linarith
  field_simp
  linarith

end DGPS.Examples.ThreeSpeciesCircle
