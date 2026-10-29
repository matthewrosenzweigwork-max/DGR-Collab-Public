import DGPS.Examples.RoughBoundary.LandscapeDerivatives

/-!
# SEM008: feature sup distance controls the `C²` parameter potential distance

For unit circle features `U, V` with `‖U - V‖∞ ≤ δ` and `‖t‖ ≤ R`: `|Λ_U - Λ_V| ≤ R δ`,
`‖∇Λ_U - ∇Λ_V‖ ≤ (1 + 2R) δ`, `‖D²Λ_U - D²Λ_V‖_op ≤ (4 + 6R) δ`.  The proof interpolates
`U_s = V + s (U - V)`, differentiates the tilted quantities in `s` under the integral (a generic
"polynomial tilt" calculus) and applies the mean value theorem on `[0, 1]`.
-/

open MeasureTheory Set Metric
open scoped Real ContDiff

namespace DGPS.Examples.RoughBoundary.Semicontinuity

section tilt

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- Essentially bounded real function. -/
def AEBdd (f : Ω → ℝ) : Prop := ∃ M : ℝ, ∀ᵐ w ∂μ, |f w| ≤ M

variable {μ}

lemma AEBdd.const (c : ℝ) : AEBdd μ (fun _ => c) := ⟨|c|, Filter.Eventually.of_forall fun _ => le_rfl⟩

lemma AEBdd.add {f g : Ω → ℝ} (hf : AEBdd μ f) (hg : AEBdd μ g) :
    AEBdd μ (fun w => f w + g w) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  exact ⟨M + N, (hM.and hN).mono fun w h => (abs_add_le _ _).trans (add_le_add h.1 h.2)⟩

lemma AEBdd.mul {f g : Ω → ℝ} (hf : AEBdd μ f) (hg : AEBdd μ g) :
    AEBdd μ (fun w => f w * g w) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨|M| * |N|, (hM.and hN).mono fun w h => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (h.1.trans (le_abs_self _)) (h.2.trans (le_abs_self _)) (abs_nonneg _)
    (abs_nonneg _)

lemma AEBdd.of_bound {f : Ω → ℝ} {M : ℝ} (h : ∀ᵐ w ∂μ, |f w| ≤ M) : AEBdd μ f := ⟨M, h⟩

/-- Data for a one-parameter tilted family: `a0 + τ a1` is the exponent and `g0 + τ g1 + τ² g2`
the observable. -/
structure TiltData (μ : Measure Ω) (a0 a1 g0 g1 g2 : Ω → ℝ) : Prop where
  m0 : Measurable a0
  m1 : Measurable a1
  n0 : Measurable g0
  n1 : Measurable g1
  n2 : Measurable g2
  b0 : AEBdd μ a0
  b1 : AEBdd μ a1
  c0 : AEBdd μ g0
  c1 : AEBdd μ g1
  c2 : AEBdd μ g2

lemma TiltData.bound {a0 a1 g0 g1 g2 : Ω → ℝ} (h : TiltData μ a0 a1 g0 g1 g2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ w ∂μ, |a0 w| ≤ M ∧ |a1 w| ≤ M ∧ |g0 w| ≤ M ∧ |g1 w| ≤ M ∧
      |g2 w| ≤ M := by
  obtain ⟨M0, h0⟩ := h.b0
  obtain ⟨M1, h1⟩ := h.b1
  obtain ⟨N0, k0⟩ := h.c0
  obtain ⟨N1, k1⟩ := h.c1
  obtain ⟨N2, k2⟩ := h.c2
  refine ⟨|M0| + |M1| + |N0| + |N1| + |N2|, by positivity, ?_⟩
  filter_upwards [h0, h1, k0, k1, k2] with w a b c d e
  have p0 := abs_nonneg M0
  have p1 := abs_nonneg M1
  have q0 := abs_nonneg N0
  have q1 := abs_nonneg N1
  have q2 := abs_nonneg N2
  have := le_abs_self M0
  have := le_abs_self M1
  have := le_abs_self N0
  have := le_abs_self N1
  have := le_abs_self N2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

lemma TiltData.one {a0 a1 g0 g1 g2 : Ω → ℝ} (h : TiltData μ a0 a1 g0 g1 g2) :
    TiltData μ a0 a1 (fun _ => 1) (fun _ => 0) (fun _ => 0) :=
  ⟨h.m0, h.m1, measurable_const, measurable_const, measurable_const, h.b0, h.b1,
    AEBdd.const _, AEBdd.const _, AEBdd.const _⟩

variable [IsProbabilityMeasure μ]

lemma poly_abs_le {x T M g0 g1 g2 : ℝ} (hx : |x| ≤ T) (h0 : |g0| ≤ M) (h1 : |g1| ≤ M)
    (h2 : |g2| ≤ M) : |g0 + x * g1 + x ^ 2 * g2| ≤ M * (1 + T + T ^ 2) := by
  have hT : 0 ≤ T := (abs_nonneg x).trans hx
  have e1 : |x * g1| ≤ T * M := by
    rw [abs_mul]; exact mul_le_mul hx h1 (abs_nonneg _) hT
  have e2 : |x ^ 2 * g2| ≤ T ^ 2 * M := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx 2) h2 (abs_nonneg _) (by positivity)
  calc |g0 + x * g1 + x ^ 2 * g2| ≤ |g0| + |x * g1| + |x ^ 2 * g2| := abs_add_three _ _ _
    _ ≤ M + T * M + T ^ 2 * M := by linarith
    _ = _ := by ring

lemma exp_lin_le {x T M a0 a1 : ℝ} (hx : |x| ≤ T) (h0 : |a0| ≤ M) (h1 : |a1| ≤ M) :
    Real.exp (a0 + x * a1) ≤ Real.exp (M * (1 + T)) := by
  have hT : 0 ≤ T := (abs_nonneg x).trans hx
  have e1 : |x * a1| ≤ T * M := by
    rw [abs_mul]; exact mul_le_mul hx h1 (abs_nonneg _) hT
  refine Real.exp_le_exp.mpr ?_
  have := le_abs_self (a0 + x * a1)
  have h3 := abs_add_le a0 (x * a1)
  nlinarith

/-- numerator -/
noncomputable def polyNum (μ : Measure Ω) (a0 a1 g0 g1 g2 : Ω → ℝ) (τ : ℝ) : ℝ :=
  ∫ w, (g0 w + τ * g1 w + τ ^ 2 * g2 w) * Real.exp (a0 w + τ * a1 w) ∂μ

/-- partition function -/
noncomputable def polyZ (μ : Measure Ω) (a0 a1 : Ω → ℝ) (τ : ℝ) : ℝ :=
  ∫ w, Real.exp (a0 w + τ * a1 w) ∂μ

/-- tilted expectation of the polynomial observable -/
noncomputable def polyTilt (μ : Measure Ω) (a0 a1 g0 g1 g2 : Ω → ℝ) (τ : ℝ) : ℝ :=
  polyNum μ a0 a1 g0 g1 g2 τ / polyZ μ a0 a1 τ

lemma hasDerivAt_polyNum {a0 a1 g0 g1 g2 : Ω → ℝ} (h : TiltData μ a0 a1 g0 g1 g2) (τ : ℝ) :
    HasDerivAt (polyNum μ a0 a1 g0 g1 g2)
      (∫ w, ((g1 w + 2 * τ * g2 w) + (g0 w + τ * g1 w + τ ^ 2 * g2 w) * a1 w) *
        Real.exp (a0 w + τ * a1 w) ∂μ) τ := by
  obtain ⟨M, hM0, hM⟩ := h.bound
  have m0 := h.m0
  have m1 := h.m1
  have n0 := h.n0
  have n1 := h.n1
  have n2 := h.n2
  set T : ℝ := |τ| + 1 with hT
  have hT0 : 0 ≤ T := by positivity
  have hTτ : |τ| ≤ T := by rw [hT]; linarith
  have hx : ∀ x ∈ ball τ 1, |x| ≤ T := by
    intro x hx
    have h1 := mem_ball.mp hx
    rw [Real.dist_eq] at h1
    have := abs_sub_abs_le_abs_sub x τ
    rw [hT]; linarith
  set Gb : ℝ := M * (1 + T + T ^ 2) with hGb
  set Eb : ℝ := Real.exp (M * (1 + T)) with hEb
  set B : ℝ := (M * (1 + 2 * T) + Gb * M) * Eb with hB
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ)
    (F := fun x w => (g0 w + x * g1 w + x ^ 2 * g2 w) * Real.exp (a0 w + x * a1 w))
    (F' := fun x w => ((g1 w + 2 * x * g2 w) + (g0 w + x * g1 w + x ^ 2 * g2 w) * a1 w) *
      Real.exp (a0 w + x * a1 w))
    (s := ball τ 1) (x₀ := τ) (bound := fun _ => B) (ball_mem_nhds τ one_pos) ?_ ?_ ?_ ?_
    (integrable_const B) ?_
  · exact key.2
  · refine Filter.Eventually.of_forall fun x => ?_
    exact (by fun_prop : Measurable fun w => (g0 w + x * g1 w + x ^ 2 * g2 w) *
      Real.exp (a0 w + x * a1 w)).aestronglyMeasurable
  · refine Integrable.of_bound (C := Gb * Eb) ?_ ?_
    · exact (by fun_prop : Measurable fun w => (g0 w + τ * g1 w + τ ^ 2 * g2 w) *
        Real.exp (a0 w + τ * a1 w)).aestronglyMeasurable
    · filter_upwards [hM] with w hw
      obtain ⟨b0, b1, c0, c1, c2⟩ := hw
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (poly_abs_le hTτ c0 c1 c2) (exp_lin_le hTτ b0 b1) (Real.exp_pos _).le
        (by positivity)
  · exact (by fun_prop : Measurable fun w => ((g1 w + 2 * τ * g2 w) +
      (g0 w + τ * g1 w + τ ^ 2 * g2 w) * a1 w) *
      Real.exp (a0 w + τ * a1 w)).aestronglyMeasurable
  · filter_upwards [hM] with w hw x hxm
    obtain ⟨b0, b1, c0, c1, c2⟩ := hw
    have hxT := hx x hxm
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have e1 : |g1 w + 2 * x * g2 w| ≤ M * (1 + 2 * T) := by
      have : |2 * x * g2 w| ≤ 2 * T * M := by
        rw [abs_mul, abs_mul]
        have : |(2 : ℝ)| = 2 := abs_of_pos two_pos
        rw [this]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hxT two_pos.le) c2 (abs_nonneg _)
          (by positivity)
      calc |g1 w + 2 * x * g2 w| ≤ |g1 w| + |2 * x * g2 w| := abs_add_le _ _
        _ ≤ M + 2 * T * M := by linarith
        _ = _ := by ring
    have e2 : |(g0 w + x * g1 w + x ^ 2 * g2 w) * a1 w| ≤ Gb * M := by
      rw [abs_mul]
      exact mul_le_mul (poly_abs_le hxT c0 c1 c2) b1 (abs_nonneg _) (by positivity)
    have e3 := (abs_add_le _ _).trans (add_le_add e1 e2)
    exact mul_le_mul e3 (exp_lin_le hxT b0 b1) (Real.exp_pos _).le (by positivity)
  · refine Filter.Eventually.of_forall fun w x _ => ?_
    have h1 : HasDerivAt (fun x : ℝ => g0 w + x * g1 w + x ^ 2 * g2 w)
        (g1 w + 2 * x * g2 w) x := by
      have := (((hasDerivAt_id x).mul_const (g1 w)).const_add (g0 w)).add
        ((hasDerivAt_pow 2 x).mul_const (g2 w))
      have e : (fun x : ℝ => g0 w + x * g1 w + x ^ 2 * g2 w) =
          ((fun x : ℝ => g0 w + id x * g1 w) + fun y : ℝ => y ^ 2 * g2 w) := by
        funext y; simp [id]
      rw [e]
      exact this.congr_deriv (by simp)
    have h2 : HasDerivAt (fun x : ℝ => a0 w + x * a1 w) (a1 w) x := by
      have := ((hasDerivAt_id x).mul_const (a1 w)).const_add (a0 w)
      simpa using this
    have h3 := (h2.exp)
    have := h1.mul h3
    convert this using 1
    ring

lemma hasDerivAt_polyZ {a0 a1 g0 g1 g2 : Ω → ℝ} (h : TiltData μ a0 a1 g0 g1 g2) (τ : ℝ) :
    HasDerivAt (polyZ μ a0 a1) (∫ w, a1 w * Real.exp (a0 w + τ * a1 w) ∂μ) τ := by
  have := hasDerivAt_polyNum h.one τ
  have e : polyZ μ a0 a1 = polyNum μ a0 a1 (fun _ => 1) (fun _ => 0) (fun _ => 0) := by
    funext x; simp [polyNum, polyZ]
  rw [e]
  simpa using this

lemma polyZ_pos (a0 a1 : Ω → ℝ) (hm0 : Measurable a0) (hm1 : Measurable a1)
    (h0 : AEBdd μ a0) (h1 : AEBdd μ a1) (τ : ℝ) : 0 < polyZ μ a0 a1 τ := by
  unfold polyZ
  refine integral_exp_pos ?_
  obtain ⟨M, hM⟩ := h0
  obtain ⟨N, hN⟩ := h1
  refine Integrable.of_bound (C := Real.exp (|M| + |τ| * |N|)) ?_ ?_
  · exact (by fun_prop : Measurable fun w => Real.exp (a0 w + τ * a1 w)).aestronglyMeasurable
  · filter_upwards [hM, hN] with w a b
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    have e1 : a0 w ≤ |M| := (le_abs_self _).trans (a.trans (le_abs_self _))
    have e2 : τ * a1 w ≤ |τ| * |N| := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (b.trans (le_abs_self _)) (abs_nonneg _)
    linarith

lemma hasDerivAt_polyTilt {a0 a1 g0 g1 g2 : Ω → ℝ} (h : TiltData μ a0 a1 g0 g1 g2) (τ : ℝ) :
    HasDerivAt (polyTilt μ a0 a1 g0 g1 g2)
      (((∫ w, ((g1 w + 2 * τ * g2 w) + (g0 w + τ * g1 w + τ ^ 2 * g2 w) * a1 w) *
          Real.exp (a0 w + τ * a1 w) ∂μ) * polyZ μ a0 a1 τ -
        polyNum μ a0 a1 g0 g1 g2 τ * (∫ w, a1 w * Real.exp (a0 w + τ * a1 w) ∂μ)) /
        polyZ μ a0 a1 τ ^ 2) τ :=
  (hasDerivAt_polyNum h τ).div (hasDerivAt_polyZ h τ)
    (polyZ_pos a0 a1 h.m0 h.m1 h.b0 h.b1 τ).ne'

lemma hasDerivAt_log_polyZ {a0 a1 g0 g1 g2 : Ω → ℝ} (h : TiltData μ a0 a1 g0 g1 g2) (τ : ℝ) :
    HasDerivAt (fun x => Real.log (polyZ μ a0 a1 x))
      ((∫ w, a1 w * Real.exp (a0 w + τ * a1 w) ∂μ) / polyZ μ a0 a1 τ) τ :=
  (hasDerivAt_polyZ h τ).log (polyZ_pos a0 a1 h.m0 h.m1 h.b0 h.b1 τ).ne'

lemma integrable_exp_tilt {a0 a1 : Ω → ℝ} (hm0 : Measurable a0) (hm1 : Measurable a1)
    (h0 : AEBdd μ a0) (h1 : AEBdd μ a1) (τ : ℝ) :
    Integrable (fun w => Real.exp (a0 w + τ * a1 w)) μ := by
  obtain ⟨M, hM⟩ := h0
  obtain ⟨N, hN⟩ := h1
  refine Integrable.of_bound (C := Real.exp (|M| + |τ| * |N|)) ?_ ?_
  · exact (by fun_prop : Measurable fun w => Real.exp (a0 w + τ * a1 w)).aestronglyMeasurable
  · filter_upwards [hM, hN] with w a b
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    have e1 : a0 w ≤ |M| := (le_abs_self _).trans (a.trans (le_abs_self _))
    have e2 : τ * a1 w ≤ |τ| * |N| := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (b.trans (le_abs_self _)) (abs_nonneg _)
    linarith

lemma abs_int_mul_exp_le {a0 a1 : Ω → ℝ} (hm0 : Measurable a0) (hm1 : Measurable a1)
    (h0 : AEBdd μ a0) (h1 : AEBdd μ a1) (τ : ℝ) {f : Ω → ℝ} {C : ℝ}
    (hC : ∀ᵐ w ∂μ, |f w| ≤ C) :
    |∫ w, f w * Real.exp (a0 w + τ * a1 w) ∂μ| ≤ C * polyZ μ a0 a1 τ := by
  have hint := (integrable_exp_tilt hm0 hm1 h0 h1 τ).const_mul C
  have := norm_integral_le_of_norm_le (f := fun w => f w * Real.exp (a0 w + τ * a1 w)) hint
    (hC.mono fun w hw => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le)
  rw [integral_const_mul] at this
  simpa [polyZ] using this

lemma abs_deriv_polyTilt_le {a0 a1 g0 g1 g2 : Ω → ℝ} (h : TiltData μ a0 a1 g0 g1 g2) (τ : ℝ)
    {c d B : ℝ}
    (hb : ∀ᵐ w ∂μ, |g0 w + τ * g1 w + τ ^ 2 * g2 w| ≤ c ∧ |g1 w + 2 * τ * g2 w| ≤ d ∧
      |a1 w| ≤ B) :
    |((∫ w, ((g1 w + 2 * τ * g2 w) + (g0 w + τ * g1 w + τ ^ 2 * g2 w) * a1 w) *
          Real.exp (a0 w + τ * a1 w) ∂μ) * polyZ μ a0 a1 τ -
        polyNum μ a0 a1 g0 g1 g2 τ * (∫ w, a1 w * Real.exp (a0 w + τ * a1 w) ∂μ)) /
        polyZ μ a0 a1 τ ^ 2| ≤ d + 2 * c * B := by
  have hZ := polyZ_pos a0 a1 h.m0 h.m1 h.b0 h.b1 τ
  obtain ⟨w0, hw0⟩ := hb.exists
  have hc : 0 ≤ c := (abs_nonneg _).trans hw0.1
  have hB : 0 ≤ B := (abs_nonneg _).trans hw0.2.2
  have hN : |polyNum μ a0 a1 g0 g1 g2 τ| ≤ c * polyZ μ a0 a1 τ :=
    abs_int_mul_exp_le h.m0 h.m1 h.b0 h.b1 τ (hb.mono fun w hw => hw.1)
  have hZ' : |∫ w, a1 w * Real.exp (a0 w + τ * a1 w) ∂μ| ≤ B * polyZ μ a0 a1 τ :=
    abs_int_mul_exp_le h.m0 h.m1 h.b0 h.b1 τ (hb.mono fun w hw => hw.2.2)
  have hN' : |∫ w, ((g1 w + 2 * τ * g2 w) + (g0 w + τ * g1 w + τ ^ 2 * g2 w) * a1 w) *
          Real.exp (a0 w + τ * a1 w) ∂μ| ≤ (d + c * B) * polyZ μ a0 a1 τ :=
    abs_int_mul_exp_le h.m0 h.m1 h.b0 h.b1 τ (hb.mono fun w hw => by
      refine (abs_add_le _ _).trans (add_le_add hw.2.1 ?_)
      rw [abs_mul]
      exact mul_le_mul hw.1 hw.2.2 (abs_nonneg _) hc)
  set Z := polyZ μ a0 a1 τ
  set N := polyNum μ a0 a1 g0 g1 g2 τ
  set N' := ∫ w, ((g1 w + 2 * τ * g2 w) + (g0 w + τ * g1 w + τ ^ 2 * g2 w) * a1 w) *
          Real.exp (a0 w + τ * a1 w) ∂μ
  set Z' := ∫ w, a1 w * Real.exp (a0 w + τ * a1 w) ∂μ
  have hd : 0 ≤ d := (abs_nonneg _).trans hw0.2.1
  rw [abs_div, abs_of_pos (pow_pos hZ 2), div_le_iff₀ (pow_pos hZ 2)]
  calc |N' * Z - N * Z'| ≤ |N' * Z| + |N * Z'| := abs_sub _ _
    _ = |N'| * Z + |N| * |Z'| := by rw [abs_mul, abs_mul, abs_of_pos hZ]
    _ ≤ (d + c * B) * Z * Z + c * Z * (B * Z) := by
      refine add_le_add (mul_le_mul_of_nonneg_right hN' hZ.le) ?_
      exact mul_le_mul hN hZ' (abs_nonneg _) (by positivity)
    _ = (d + 2 * c * B) * Z ^ 2 := by ring

lemma abs_deriv_log_polyZ_le {a0 a1 : Ω → ℝ} (hm0 : Measurable a0) (hm1 : Measurable a1)
    (h0 : AEBdd μ a0) (h1 : AEBdd μ a1) (τ : ℝ) {B : ℝ} (hb : ∀ᵐ w ∂μ, |a1 w| ≤ B) :
    |(∫ w, a1 w * Real.exp (a0 w + τ * a1 w) ∂μ) / polyZ μ a0 a1 τ| ≤ B := by
  have hZ := polyZ_pos a0 a1 hm0 hm1 h0 h1 τ
  rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  exact abs_int_mul_exp_le hm0 hm1 h0 h1 τ hb

omit [IsProbabilityMeasure μ] in
lemma mvt01 {f f' : ℝ → ℝ} {C : ℝ} (hf : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' s) s)
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, |f' s| ≤ C) : |f 1 - f 0| ≤ C := by
  have := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := 1)
    (fun x hx => (hf x hx).hasDerivWithinAt) (fun x hx => hb x (Ico_subset_Icc_self hx)) 1
    (right_mem_Icc.2 zero_le_one)
  simpa using this

end tilt

section feat

open DGPS.Examples.RoughBoundary.Landscape (E2 pint expPhi pint_exp_props)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Log partition `t ↦ log ∫ exp ⟪t, W⟫ dμ` of a feature `W`. -/
noncomputable def logPart (μ : Measure Ω) (W : Ω → E2) (t : E2) : ℝ :=
  Real.log (∫ w, Real.exp (inner ℝ t (W w)) ∂μ)

/-- Tilted mean of `⟪h, W⟫`. -/
noncomputable def meanW (μ : Measure Ω) (W : Ω → E2) (t h : E2) : ℝ :=
  (∫ w, inner ℝ h (W w) * Real.exp (inner ℝ t (W w)) ∂μ) / ∫ w, Real.exp (inner ℝ t (W w)) ∂μ

/-- Tilted second moment of `⟪h, W⟫ ⟪k, W⟫`. -/
noncomputable def secW (μ : Measure Ω) (W : Ω → E2) (t h k : E2) : ℝ :=
  (∫ w, inner ℝ h (W w) * inner ℝ k (W w) * Real.exp (inner ℝ t (W w)) ∂μ) /
    ∫ w, Real.exp (inner ℝ t (W w)) ∂μ

lemma abs_inner_le_of {x y : E2} {B : ℝ} (h : ‖y‖ ≤ B) : |inner ℝ x y| ≤ ‖x‖ * B :=
  (abs_real_inner_le_norm x y).trans (mul_le_mul_of_nonneg_left h (norm_nonneg x))

omit [IsProbabilityMeasure μ] in
lemma aebdd_inner {W : Ω → E2} {B : ℝ} (x : E2) (hW : ∀ᵐ w ∂μ, ‖W w‖ ≤ B) :
    AEBdd μ (fun w => inner ℝ x (W w)) :=
  ⟨‖x‖ * B, hW.mono fun _ hw => abs_inner_le_of hw⟩

lemma measurable_inner_feat {W : Ω → E2} (hW : Measurable W) (x : E2) :
    Measurable (fun w => inner ℝ x (W w)) :=
  measurable_const.inner hW

lemma contDiff_logPart {W : Ω → E2} (hW : Measurable W) (hb : ∀ᵐ w ∂μ, ‖W w‖ ≤ 1) :
    ContDiff ℝ ∞ (logPart μ W) := by
  have h := pint_exp_props (μ := μ) (V := W) hW hb 0
  exact h.1.log fun t => (h.2.1 t).ne'

lemma inner_line (t k x : E2) (τ : ℝ) :
    inner ℝ (t + τ • k) x = inner ℝ t x + τ * inner ℝ k x := by
  rw [inner_add_left, real_inner_smul_left]

omit [IsProbabilityMeasure μ] in
/-- Tilt data along the line `τ ↦ t + τ k`. -/
lemma tiltData_tline {W : Ω → E2} (hW : Measurable W) (hb : ∀ᵐ w ∂μ, ‖W w‖ ≤ 1) (t k h : E2) :
    TiltData μ (fun w => inner ℝ t (W w)) (fun w => inner ℝ k (W w))
      (fun w => inner ℝ h (W w)) (fun _ => 0) (fun _ => 0) :=
  ⟨measurable_inner_feat hW t, measurable_inner_feat hW k, measurable_inner_feat hW h,
    measurable_const, measurable_const, aebdd_inner t hb, aebdd_inner k hb, aebdd_inner h hb,
    AEBdd.const _, AEBdd.const _⟩

lemma hasDerivAt_logPart_line {W : Ω → E2} (hW : Measurable W) (hb : ∀ᵐ w ∂μ, ‖W w‖ ≤ 1)
    (t h : E2) : HasDerivAt (fun τ : ℝ => logPart μ W (t + τ • h)) (meanW μ W t h) 0 := by
  have := hasDerivAt_log_polyZ (tiltData_tline hW hb t h h) 0
  have e : (fun τ : ℝ => logPart μ W (t + τ • h)) = fun x => Real.log
      (polyZ μ (fun w => inner ℝ t (W w)) (fun w => inner ℝ h (W w)) x) := by
    funext τ; simp [logPart, polyZ, inner_line]
  rw [e]
  simpa [meanW, polyZ] using this

lemma fderiv_logPart {W : Ω → E2} (hW : Measurable W) (hb : ∀ᵐ w ∂μ, ‖W w‖ ≤ 1) (t h : E2) :
    fderiv ℝ (logPart μ W) t h = meanW μ W t h := by
  have hd : Differentiable ℝ (logPart μ W) := (contDiff_logPart hW hb).differentiable (by simp)
  have hline : HasDerivAt (fun τ : ℝ => t + τ • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add t
  have h1 := (hd t).hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hline (by simp)
  exact h1.unique (hasDerivAt_logPart_line hW hb t h)

lemma hasDerivAt_meanW_line {W : Ω → E2} (hW : Measurable W) (hb : ∀ᵐ w ∂μ, ‖W w‖ ≤ 1)
    (t k h : E2) :
    HasDerivAt (fun τ : ℝ => meanW μ W (t + τ • k) h)
      (secW μ W t h k - meanW μ W t h * meanW μ W t k) 0 := by
  have := hasDerivAt_polyTilt (tiltData_tline hW hb t k h) 0
  have e : (fun τ : ℝ => meanW μ W (t + τ • k) h) = polyTilt μ (fun w => inner ℝ t (W w))
      (fun w => inner ℝ k (W w)) (fun w => inner ℝ h (W w)) (fun _ => 0) (fun _ => 0) := by
    funext τ; simp [meanW, polyTilt, polyNum, polyZ, inner_line]
  rw [e]
  refine this.congr_deriv ?_
  have hZ := polyZ_pos (μ := μ) (fun w => inner ℝ t (W w)) (fun w => inner ℝ k (W w))
    (measurable_inner_feat hW t) (measurable_inner_feat hW k) (aebdd_inner t hb)
    (aebdd_inner k hb) 0
  simp only [polyZ, polyNum, zero_mul, add_zero, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at hZ ⊢
  simp only [secW, meanW]
  field_simp

lemma fderiv2_logPart {W : Ω → E2} (hW : Measurable W) (hb : ∀ᵐ w ∂μ, ‖W w‖ ≤ 1) (t k h : E2) :
    fderiv ℝ (fderiv ℝ (logPart μ W)) t k h = secW μ W t h k - meanW μ W t h * meanW μ W t k := by
  have hc := contDiff_logPart hW hb
  have hd2 : Differentiable ℝ (fderiv ℝ (logPart μ W)) :=
    (hc.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hline : HasDerivAt (fun τ : ℝ => t + τ • k) k 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const k).const_add t
  have h1 := (hd2 t).hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hline (by simp)
  have h2 := (ContinuousLinearMap.apply ℝ ℝ h).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have e : ((ContinuousLinearMap.apply ℝ ℝ h) ∘ (fderiv ℝ (logPart μ W) ∘ fun τ : ℝ => t + τ • k)) =
      fun τ : ℝ => meanW μ W (t + τ • k) h := by
    funext τ; simp [fderiv_logPart hW hb]
  rw [e] at h2
  have := h2.unique (hasDerivAt_meanW_line hW hb t k h)
  simpa using this

end feat

section sline

open DGPS.Examples.RoughBoundary.Landscape (E2)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma mvt01' {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ∃ d, HasDerivAt f d s ∧ |d| ≤ C) : |f 1 - f 0| ≤ C := by
  classical
  choose! f' hf' using hf
  exact mvt01 (f' := f') (fun s hs => (hf' s hs).1) (fun s hs => (hf' s hs).2)

lemma abs_polyTilt_le {a0 a1 g0 g1 g2 : Ω → ℝ} (h : TiltData μ a0 a1 g0 g1 g2) (τ : ℝ) {c : ℝ}
    (hb : ∀ᵐ w ∂μ, |g0 w + τ * g1 w + τ ^ 2 * g2 w| ≤ c) :
    |polyTilt μ a0 a1 g0 g1 g2 τ| ≤ c := by
  have hZ := polyZ_pos a0 a1 h.m0 h.m1 h.b0 h.b1 τ
  unfold polyTilt
  rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  exact abs_int_mul_exp_le h.m0 h.m1 h.b0 h.b1 τ hb

/-- the interpolated partition function / tilted mean / second moment, along `U_s = V + s (U-V)` -/
noncomputable def mline (μ : Measure Ω) (U V : Ω → E2) (t h : E2) (s : ℝ) : ℝ :=
  polyTilt μ (fun w => inner ℝ t (V w)) (fun w => inner ℝ t (U w - V w))
    (fun w => inner ℝ h (V w)) (fun w => inner ℝ h (U w - V w)) (fun _ => 0) s

noncomputable def qline (μ : Measure Ω) (U V : Ω → E2) (t h k : E2) (s : ℝ) : ℝ :=
  polyTilt μ (fun w => inner ℝ t (V w)) (fun w => inner ℝ t (U w - V w))
    (fun w => inner ℝ h (V w) * inner ℝ k (V w))
    (fun w => inner ℝ h (V w) * inner ℝ k (U w - V w) + inner ℝ h (U w - V w) * inner ℝ k (V w))
    (fun w => inner ℝ h (U w - V w) * inner ℝ k (U w - V w)) s

omit [IsProbabilityMeasure μ] in
lemma mline_zero (U V : Ω → E2) (t h : E2) : mline μ U V t h 0 = meanW μ V t h := by
  simp [mline, polyTilt, polyNum, polyZ, meanW]

omit [IsProbabilityMeasure μ] in
lemma mline_one (U V : Ω → E2) (t h : E2) : mline μ U V t h 1 = meanW μ U t h := by
  unfold mline polyTilt polyNum polyZ meanW
  congr 1
  · congr 1; funext w; simp [inner_sub_right]
  · congr 1; funext w; simp [inner_sub_right]

omit [IsProbabilityMeasure μ] in
lemma qline_zero (U V : Ω → E2) (t h k : E2) : qline μ U V t h k 0 = secW μ V t h k := by
  simp [qline, polyTilt, polyNum, polyZ, secW]

omit [IsProbabilityMeasure μ] in
lemma qline_one (U V : Ω → E2) (t h k : E2) : qline μ U V t h k 1 = secW μ U t h k := by
  unfold qline polyTilt polyNum polyZ secW
  congr 1
  · congr 1; funext w; simp only [inner_sub_right]; ring_nf
  · congr 1; funext w; simp [inner_sub_right]

omit [IsProbabilityMeasure μ] in
lemma logline_one (U V : Ω → E2) (t : E2) :
    polyZ μ (fun w => inner ℝ t (V w)) (fun w => inner ℝ t (U w - V w)) 1 =
      ∫ w, Real.exp (inner ℝ t (U w)) ∂μ := by
  unfold polyZ
  congr 1; funext w; simp [inner_sub_right]

omit [IsProbabilityMeasure μ] in
lemma logline_zero (U V : Ω → E2) (t : E2) :
    polyZ μ (fun w => inner ℝ t (V w)) (fun w => inner ℝ t (U w - V w)) 0 =
      ∫ w, Real.exp (inner ℝ t (V w)) ∂μ := by
  simp [polyZ]

omit [MeasurableSpace Ω] in
/-- the interpolation inner-product bound -/
lemma abs_sline_inner_le {U V : Ω → E2} {w : Ω} (h : E2) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hU : ‖U w‖ ≤ 1) (hV : ‖V w‖ ≤ 1) :
    |inner ℝ h (V w) + s * inner ℝ h (U w - V w)| ≤ ‖h‖ := by
  have e : inner ℝ h (V w) + s * inner ℝ h (U w - V w) =
      (1 - s) * inner ℝ h (V w) + s * inner ℝ h (U w) := by
    rw [inner_sub_right]; ring
  rw [e]
  have h1 : |inner ℝ h (V w)| ≤ ‖h‖ := by simpa using abs_inner_le_of (x := h) hV
  have h2 : |inner ℝ h (U w)| ≤ ‖h‖ := by simpa using abs_inner_le_of (x := h) hU
  have hs0 : 0 ≤ s := hs.1
  have hs1 : 0 ≤ 1 - s := by linarith [hs.2]
  calc |(1 - s) * inner ℝ h (V w) + s * inner ℝ h (U w)|
      ≤ |(1 - s) * inner ℝ h (V w)| + |s * inner ℝ h (U w)| := abs_add_le _ _
    _ = (1 - s) * |inner ℝ h (V w)| + s * |inner ℝ h (U w)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hs1, abs_of_nonneg hs0]
    _ ≤ (1 - s) * ‖h‖ + s * ‖h‖ := by gcongr
    _ = ‖h‖ := by ring

variable {U V : Ω → E2} (hUm : Measurable U) (hVm : Measurable V)
  (hU1 : ∀ᵐ w ∂μ, ‖U w‖ ≤ 1) (hV1 : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) {δ R : ℝ}
  (hδ : ∀ᵐ w ∂μ, ‖U w - V w‖ ≤ δ) {t : E2} (ht : ‖t‖ ≤ R)

include hUm hVm hU1 hV1 hδ

omit [IsProbabilityMeasure μ] hU1 in
lemma tiltData_mean (h : E2) :
    TiltData μ (fun w => inner ℝ t (V w)) (fun w => inner ℝ t (U w - V w))
      (fun w => inner ℝ h (V w)) (fun w => inner ℝ h (U w - V w)) (fun _ => 0) :=
  ⟨measurable_inner_feat hVm t, measurable_inner_feat (W := fun w => U w - V w) (hUm.sub hVm) t,
    measurable_inner_feat hVm h, measurable_inner_feat (W := fun w => U w - V w) (hUm.sub hVm) h,
    measurable_const, aebdd_inner t hV1, aebdd_inner (W := fun w => U w - V w) t hδ,
    aebdd_inner h hV1, aebdd_inner (W := fun w => U w - V w) h hδ, AEBdd.const _⟩

omit [IsProbabilityMeasure μ] hU1 in
lemma tiltData_sec (h k : E2) :
    TiltData μ (fun w => inner ℝ t (V w)) (fun w => inner ℝ t (U w - V w))
      (fun w => inner ℝ h (V w) * inner ℝ k (V w))
      (fun w => inner ℝ h (V w) * inner ℝ k (U w - V w) + inner ℝ h (U w - V w) * inner ℝ k (V w))
      (fun w => inner ℝ h (U w - V w) * inner ℝ k (U w - V w)) := by
  have mD : ∀ x : E2, Measurable fun w => inner ℝ x (U w - V w) :=
    fun x => measurable_inner_feat (W := fun w => U w - V w) (hUm.sub hVm) x
  have mV : ∀ x : E2, Measurable fun w => inner ℝ x (V w) := fun x => measurable_inner_feat hVm x
  have bD : ∀ x : E2, AEBdd μ fun w => inner ℝ x (U w - V w) :=
    fun x => aebdd_inner (W := fun w => U w - V w) x hδ
  have bV : ∀ x : E2, AEBdd μ fun w => inner ℝ x (V w) := fun x => aebdd_inner x hV1
  exact ⟨mV t, mD t, (mV h).mul (mV k), ((mV h).mul (mD k)).add ((mD h).mul (mV k)),
    (mD h).mul (mD k), bV t, bD t, (bV h).mul (bV k), ((bV h).mul (bD k)).add ((bD h).mul (bV k)),
    (bD h).mul (bD k)⟩

omit hUm hVm hU1 hV1 in
lemma abs_tD_le (x : E2) (hx : ‖x‖ ≤ R) :
    ∀ᵐ w ∂μ, |inner ℝ x (U w - V w)| ≤ R * δ := by
  have hδ0 : 0 ≤ δ := by
    obtain ⟨w, hw⟩ := hδ.exists
    exact (norm_nonneg _).trans hw
  filter_upwards [hδ] with w hw
  refine (abs_inner_le_of hw).trans ?_
  exact mul_le_mul_of_nonneg_right hx hδ0

include ht in
lemma mline_deriv (h : E2) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ d, HasDerivAt (mline μ U V t h) d s ∧ |d| ≤ ‖h‖ * δ + 2 * ‖h‖ * (R * δ) := by
  have TD := tiltData_mean hUm hVm hV1 hδ (t := t) h
  refine ⟨_, hasDerivAt_polyTilt TD s, ?_⟩
  have := abs_deriv_polyTilt_le TD s (c := ‖h‖) (d := ‖h‖ * δ) (B := R * δ) ?_
  · simpa [mul_assoc] using this
  · filter_upwards [hU1, hV1, hδ, abs_tD_le hδ t ht] with w a b c d
    refine ⟨?_, ?_, d⟩
    · simpa using abs_sline_inner_le h hs a b
    · simpa using abs_inner_le_of (x := h) c

lemma abs_mline_le (h : E2) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : |mline μ U V t h s| ≤ ‖h‖ := by
  have TD := tiltData_mean hUm hVm hV1 hδ (t := t) h
  refine abs_polyTilt_le TD s ?_
  filter_upwards [hU1, hV1] with w a b
  simpa using abs_sline_inner_le h hs a b

include ht in
lemma qline_deriv (h k : E2) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ d, HasDerivAt (qline μ U V t h k) d s ∧
      |d| ≤ 2 * (‖h‖ * ‖k‖ * δ) + 2 * (‖h‖ * ‖k‖) * (R * δ) := by
  have hδ0 : 0 ≤ δ := by
    obtain ⟨w, hw⟩ := hδ.exists
    exact (norm_nonneg _).trans hw
  have TD := tiltData_sec hUm hVm hV1 hδ (t := t) h k
  refine ⟨_, hasDerivAt_polyTilt TD s, ?_⟩
  have := abs_deriv_polyTilt_le TD s (c := ‖h‖ * ‖k‖) (d := 2 * (‖h‖ * ‖k‖ * δ)) (B := R * δ) ?_
  · simpa [mul_assoc] using this
  · filter_upwards [hU1, hV1, hδ, abs_tD_le hδ t ht] with w a b c d
    refine ⟨?_, ?_, d⟩
    · have e : inner ℝ h (V w) * inner ℝ k (V w) +
          s * (inner ℝ h (V w) * inner ℝ k (U w - V w) + inner ℝ h (U w - V w) * inner ℝ k (V w)) +
          s ^ 2 * (inner ℝ h (U w - V w) * inner ℝ k (U w - V w)) =
          (inner ℝ h (V w) + s * inner ℝ h (U w - V w)) *
            (inner ℝ k (V w) + s * inner ℝ k (U w - V w)) := by ring
      rw [e, abs_mul]
      exact mul_le_mul (abs_sline_inner_le h hs a b) (abs_sline_inner_le k hs a b)
        (abs_nonneg _) (norm_nonneg _)
    · have e : inner ℝ h (V w) * inner ℝ k (U w - V w) + inner ℝ h (U w - V w) * inner ℝ k (V w) +
          2 * s * (inner ℝ h (U w - V w) * inner ℝ k (U w - V w)) =
          inner ℝ h (U w - V w) * (inner ℝ k (V w) + s * inner ℝ k (U w - V w)) +
            (inner ℝ h (V w) + s * inner ℝ h (U w - V w)) * inner ℝ k (U w - V w) := by ring
      rw [e]
      have h1 : |inner ℝ h (U w - V w)| ≤ ‖h‖ * δ := abs_inner_le_of c
      have h2 : |inner ℝ k (U w - V w)| ≤ ‖k‖ * δ := abs_inner_le_of c
      have h3 := abs_sline_inner_le (U := U) (V := V) h hs a b
      have h4 := abs_sline_inner_le (U := U) (V := V) k hs a b
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have p1 := mul_le_mul h1 h4 (abs_nonneg _) (mul_nonneg (norm_nonneg h) hδ0)
      have p2 := mul_le_mul h3 h2 (abs_nonneg _) (norm_nonneg h)
      nlinarith

omit hU1 in
include ht in
lemma logPart_diff_le : |logPart μ U t - logPart μ V t| ≤ R * δ := by
  have TD := tiltData_mean hUm hVm hV1 hδ (t := t) t
  have := mvt01' (f := fun x => Real.log (polyZ μ (fun w => inner ℝ t (V w))
      (fun w => inner ℝ t (U w - V w)) x)) (C := R * δ)
    (fun s _ => ⟨_, hasDerivAt_log_polyZ TD s,
      abs_deriv_log_polyZ_le TD.m0 TD.m1 TD.b0 TD.b1 s (abs_tD_le hδ t ht)⟩)
  simp only [logline_one, logline_zero] at this
  exact this

include ht in
lemma meanW_diff_le (h : E2) :
    |meanW μ U t h - meanW μ V t h| ≤ (1 + 2 * R) * δ * ‖h‖ := by
  have := mvt01' (f := mline μ U V t h) (C := ‖h‖ * δ + 2 * ‖h‖ * (R * δ))
    (fun s hs => mline_deriv hUm hVm hU1 hV1 hδ ht h hs)
  rw [mline_one, mline_zero] at this
  calc _ ≤ _ := this
    _ = _ := by ring

include ht in
lemma meanW_prod_diff_le (h k : E2) :
    |meanW μ U t h * meanW μ U t k - meanW μ V t h * meanW μ V t k| ≤
      (‖h‖ * δ + 2 * ‖h‖ * (R * δ)) * ‖k‖ + ‖h‖ * (‖k‖ * δ + 2 * ‖k‖ * (R * δ)) := by
  have := mvt01' (f := fun s => mline μ U V t h s * mline μ U V t k s)
    (C := (‖h‖ * δ + 2 * ‖h‖ * (R * δ)) * ‖k‖ + ‖h‖ * (‖k‖ * δ + 2 * ‖k‖ * (R * δ)))
    (fun s hs => by
      obtain ⟨d1, hd1, b1⟩ := mline_deriv hUm hVm hU1 hV1 hδ ht h hs
      obtain ⟨d2, hd2, b2⟩ := mline_deriv hUm hVm hU1 hV1 hδ ht k hs
      refine ⟨d1 * mline μ U V t k s + mline μ U V t h s * d2, hd1.mul hd2, ?_⟩
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul b1 (abs_mline_le hUm hVm hU1 hV1 hδ k hs) (abs_nonneg _)
          (by linarith [abs_nonneg d1]))
        (mul_le_mul (abs_mline_le hUm hVm hU1 hV1 hδ h hs) b2 (abs_nonneg _) (norm_nonneg _)))
  simpa only [mline_one, mline_zero] using this

include ht in
lemma hess_entry_le (h k : E2) :
    |(secW μ U t h k - meanW μ U t h * meanW μ U t k) -
        (secW μ V t h k - meanW μ V t h * meanW μ V t k)| ≤ (4 + 6 * R) * δ * (‖h‖ * ‖k‖) := by
  have q := mvt01' (f := qline μ U V t h k) (C := 2 * (‖h‖ * ‖k‖ * δ) + 2 * (‖h‖ * ‖k‖) * (R * δ))
    (fun s hs => qline_deriv hUm hVm hU1 hV1 hδ ht h k hs)
  rw [qline_one, qline_zero] at q
  have p := meanW_prod_diff_le hUm hVm hU1 hV1 hδ ht h k
  have e : (secW μ U t h k - meanW μ U t h * meanW μ U t k) -
        (secW μ V t h k - meanW μ V t h * meanW μ V t k) =
      (secW μ U t h k - secW μ V t h k) -
        (meanW μ U t h * meanW μ U t k - meanW μ V t h * meanW μ V t k) := by ring
  rw [e]
  calc _ ≤ _ := abs_sub _ _
    _ ≤ _ := add_le_add q p
    _ = _ := by ring

include ht in
theorem logPart_c2_dist :
    |logPart μ U t - logPart μ V t| ≤ R * δ ∧
    ‖gradient (logPart μ U) t - gradient (logPart μ V) t‖ ≤ (1 + 2 * R) * δ ∧
    ‖fderiv ℝ (fderiv ℝ (logPart μ U)) t - fderiv ℝ (fderiv ℝ (logPart μ V)) t‖ ≤
      (4 + 6 * R) * δ := by
  have hδ0 : 0 ≤ δ := by
    obtain ⟨w, hw⟩ := hδ.exists
    exact (norm_nonneg _).trans hw
  have hR0 : 0 ≤ R := (norm_nonneg t).trans ht
  refine ⟨logPart_diff_le hUm hVm hV1 hδ ht, ?_, ?_⟩
  · unfold gradient
    rw [← map_sub, LinearIsometryEquiv.norm_map]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    rw [sub_apply, fderiv_logPart hUm
      (hU1.mono fun w hw => hw), fderiv_logPart hVm hV1, Real.norm_eq_abs]
    exact meanW_diff_le hUm hVm hU1 hV1 hδ ht h
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun k => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    rw [sub_apply, sub_apply,
      fderiv2_logPart hUm hU1, fderiv2_logPart hVm hV1, Real.norm_eq_abs]
    calc _ ≤ _ := hess_entry_le hUm hVm hU1 hV1 hδ ht h k
      _ = _ := by ring

end sline

section final

open DGPS.Examples.RoughBoundary.Landscape (E2)

/-- SEM008. If two unit circle features `U, V` satisfy `‖U - V‖∞ ≤ δ`, then on `‖t‖ ≤ R` the
log partitions `Λ_U, Λ_V` satisfy `|Λ_U - Λ_V| ≤ R δ`, `‖∇Λ_U - ∇Λ_V‖ ≤ (1 + 2R) δ` and
`‖D²Λ_U - D²Λ_V‖_op ≤ (4 + 6R) δ`. -/
theorem feature_sup_distance_controls_c2_parameter_potential_distance
    {U V : Torus 1 → E2} (hUm : Measurable U) (hVm : Measurable V)
    (hU1 : ∀ᵐ y ∂DGPS.haar 1, ‖U y‖ ≤ 1) (hV1 : ∀ᵐ y ∂DGPS.haar 1, ‖V y‖ ≤ 1)
    {δ R : ℝ} (hδ : ∀ᵐ y ∂DGPS.haar 1, ‖U y - V y‖ ≤ δ) {t : E2} (ht : ‖t‖ ≤ R) :
    |featureLogPartition U t - featureLogPartition V t| ≤ R * δ ∧
    ‖gradient (featureLogPartition U) t - gradient (featureLogPartition V) t‖ ≤
      (1 + 2 * R) * δ ∧
    ‖fderiv ℝ (fderiv ℝ (featureLogPartition U)) t -
        fderiv ℝ (fderiv ℝ (featureLogPartition V)) t‖ ≤ (4 + 6 * R) * δ :=
  logPart_c2_dist (μ := DGPS.haar 1) hUm hVm hU1 hV1 hδ ht

end final

end DGPS.Examples.RoughBoundary.Semicontinuity
