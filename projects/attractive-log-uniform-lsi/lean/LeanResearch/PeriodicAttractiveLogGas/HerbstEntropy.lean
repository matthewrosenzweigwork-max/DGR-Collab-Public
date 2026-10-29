import LeanResearch.PeriodicAttractiveLogGas.Rothaus
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The scalar calculation in manuscript lines 2889--2902, customarily
called Herbst's argument. Its entropy control is an explicit intermediate
interface; deriving that control from the actual source LSI and exponential
gradient chain is a separate task. Moment integrability, differentiation and
the zero-parameter limit are conclusions, not hypotheses of the final bound.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace PeriodicAttractiveLogGas.HerbstEntropy

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {F : Ω → ℝ} {M : ℝ}

/-- Compact domination also applies to an essentially bounded measurable
class, by transferring from its genuine bounded measurable representative. -/
theorem integrable_continuous_comp [IsFiniteMeasure μ]
    (hF : AEMeasurable F μ) (hb : ∀ᵐ x ∂μ, |F x| ≤ M)
    {k : ℝ → ℝ} (hk : Continuous k) : Integrable (fun x => k (F x)) μ := by
  obtain ⟨G, hG, hGb, hFG⟩ := exists_bounded_measurable_ae_eq hF hb
  exact (Rothaus.integrable_continuous_comp_bounded hG hGb hk).congr
    (hFG.mono fun x hx => congrArg k hx.symm)

/-- The actual derivative-integral interchange for an essentially bounded
observable follows from compact local domination in the frozen Rothaus API. -/
theorem hasDerivAt_integral_comp [IsFiniteMeasure μ]
    (hF : AEMeasurable F μ) (hb : ∀ᵐ x ∂μ, |F x| ≤ M)
    {P D : ℝ × ℝ → ℝ} (hP : Continuous P) (hD : Continuous D)
    (hd : ∀ r t, HasDerivAt (fun s => P (s,t)) (D (r,t)) r) (r : ℝ) :
    HasDerivAt (fun s => ∫ x, P (s,F x) ∂μ) (∫ x, D (r,F x) ∂μ) r := by
  obtain ⟨G, hG, hGb, hFG⟩ := exists_bounded_measurable_ae_eq hF hb
  have he : (fun s => ∫ x, P (s,F x) ∂μ) = fun s => ∫ x, P (s,G x) ∂μ := by
    funext s
    exact integral_congr_ae (hFG.mono fun x hx => congrArg (fun t => P (s,t)) hx)
  have heD : (∫ x, D (r,F x) ∂μ) = ∫ x, D (r,G x) ∂μ :=
    integral_congr_ae (hFG.mono fun x hx => congrArg (fun t => D (r,t)) hx)
  rw [he, heD]
  exact Rothaus.hasDerivAt_integral_comp_bounded hG hGb hP hD hd r

/-- The source moment-generating function, with its literal real integral. -/
def moment (μ : Measure Ω) (F : Ω → ℝ) (s : ℝ) : ℝ :=
  ∫ x, Real.exp (s * F x) ∂μ

theorem integrable_exp_mul [IsFiniteMeasure μ]
    (hF : AEMeasurable F μ) (hb : ∀ᵐ x ∂μ, |F x| ≤ M) (s : ℝ) :
    Integrable (fun x => Real.exp (s * F x)) μ :=
  integrable_continuous_comp hF hb
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))

theorem integrable_exp_slope [IsFiniteMeasure μ]
    (hF : AEMeasurable F μ) (hb : ∀ᵐ x ∂μ, |F x| ≤ M) (s : ℝ) :
    Integrable (fun x => F x * Real.exp (s * F x)) μ :=
  integrable_continuous_comp hF hb
    (continuous_id.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)))

/-- The full real derivative of the true exponential moment. -/
theorem hasDerivAt_moment [IsFiniteMeasure μ]
    (hF : AEMeasurable F μ) (hb : ∀ᵐ x ∂μ, |F x| ≤ M) (s : ℝ) :
    HasDerivAt (moment μ F) (∫ x, F x * Real.exp (s * F x) ∂μ) s := by
  apply hasDerivAt_integral_comp hF hb
    (P := fun p => Real.exp (p.1 * p.2)) (D := fun p => p.2 * Real.exp (p.1 * p.2))
  · fun_prop
  · fun_prop
  · intro r t
    simpa only [id_eq, mul_one, mul_comm] using (((hasDerivAt_id r).mul_const t).exp)

theorem moment_pos [IsProbabilityMeasure μ]
    (hF : AEMeasurable F μ) (hb : ∀ᵐ x ∂μ, |F x| ≤ M) (s : ℝ) :
    0 < moment μ F s := integral_exp_pos (integrable_exp_mul hF hb s)

@[simp] theorem moment_zero [IsProbabilityMeasure μ] : moment μ F 0 = 1 := by
  simp [moment]

theorem hasDerivAt_log_moment [IsProbabilityMeasure μ]
    (hF : AEMeasurable F μ) (hb : ∀ᵐ x ∂μ, |F x| ≤ M) (s : ℝ) :
    HasDerivAt (fun t => Real.log (moment μ F t))
      ((∫ x, F x * Real.exp (s * F x) ∂μ) / moment μ F s) s :=
  (hasDerivAt_moment hF hb s).log (moment_pos hF hb s).ne'

theorem hasDerivAt_log_moment_zero [IsProbabilityMeasure μ]
    (hF : AEMeasurable F μ) (hb : ∀ᵐ x ∂μ, |F x| ≤ M) :
    HasDerivAt (fun t => Real.log (moment μ F t)) (∫ x, F x ∂μ) 0 := by
  simpa only [zero_mul, Real.exp_zero, mul_one, moment_zero, div_one] using
    hasDerivAt_log_moment hF hb 0

/-- The entropy is genuinely finite before it is identified with the
source's real derivative expression. -/
theorem entropy_exp_eq [IsProbabilityMeasure μ]
    (hF : AEMeasurable F μ) (hb : ∀ᵐ x ∂μ, |F x| ≤ M) (s : ℝ) :
    entropy μ (fun x => Real.exp (s * F x)) =
      ((s * (∫ x, F x * Real.exp (s * F x) ∂μ) -
        moment μ F s * Real.log (moment μ F s) : ℝ) : EReal) := by
  have he : (fun x => Real.exp (s * F x) * Real.log (Real.exp (s * F x))) =
      fun x => s * (F x * Real.exp (s * F x)) := by
    funext x
    rw [Real.log_exp]
    ring
  have hi : Integrable (fun x => Real.exp (s * F x) * Real.log (Real.exp (s * F x))) μ := by
    rw [he]
    exact (integrable_exp_slope hF hb s).const_mul s
  rw [entropy_eq_integral (Eventually.of_forall fun x => (Real.exp_pos (s * F x)).le) hi,
    he, integral_const_mul]
  rfl

/-- The manuscript identity written with the actual derivative of H. -/
theorem entropy_exp_eq_deriv [IsProbabilityMeasure μ]
    (hF : AEMeasurable F μ) (hb : ∀ᵐ x ∂μ, |F x| ≤ M) (s : ℝ) :
    entropy μ (fun x => Real.exp (s * F x)) =
      ((s * deriv (moment μ F) s - moment μ F s * Real.log (moment μ F s) : ℝ) : EReal) := by
  rw [(hasDerivAt_moment hF hb s).deriv]
  exact entropy_exp_eq hF hb s

/-- The mean used below is an integral of a genuinely integrable observable. -/
theorem integrable_observable [IsFiniteMeasure μ]
    (hF : AEMeasurable F μ) (hb : ∀ᵐ x ∂μ, |F x| ≤ M) : Integrable F μ :=
  integrable_continuous_comp hF hb continuous_id

/-- The source logarithmic quotient has its true punctured limit at zero.
No assertion is made about its totalized value at zero. -/
theorem tendsto_log_moment_div [IsProbabilityMeasure μ]
    (hF : AEMeasurable F μ) (hb : ∀ᵐ x ∂μ, |F x| ≤ M) :
    Tendsto (fun s : ℝ => Real.log (moment μ F s) / s) (𝓝[≠] 0)
      (𝓝 (∫ x, F x ∂μ)) := by
  simpa only [zero_add, moment_zero, Real.log_one, sub_zero, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using (hasDerivAt_log_moment_zero hF hb).tendsto_slope_zero

theorem exp_centered (s : ℝ) (x : Ω) :
    Real.exp (s * (F x - ∫ x, F x ∂μ)) =
      Real.exp (-s * ∫ x, F x ∂μ) * Real.exp (s * F x) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem integrable_centered_exp [IsFiniteMeasure μ]
    (hF : AEMeasurable F μ) (hb : ∀ᵐ x ∂μ, |F x| ≤ M) (s : ℝ) :
    Integrable (fun x => Real.exp (s * (F x - ∫ x, F x ∂μ))) μ := by
  simp_rw [exp_centered]
  exact (integrable_exp_mul hF hb s).const_mul _

theorem centered_moment_eq (s : ℝ) :
    (∫ x, Real.exp (s * (F x - ∫ x, F x ∂μ)) ∂μ) =
      Real.exp (-s * ∫ x, F x ∂μ) * moment μ F s := by
  simp_rw [exp_centered]
  exact integral_const_mul _ _

/-- The positive-parameter scalar Herbst calculation. The entropy-control
hypothesis is the explicit intermediate input to the generic theorem, not a
claim that a source LSI or exponential-gradient rule is proved in this file. -/
theorem moment_le_of_entropy_control_pos [IsProbabilityMeasure μ]
    (hF : AEMeasurable F μ) (hb : ∀ᵐ x ∂μ, |F x| ≤ M) {A : ℝ}
    (hEnt : ∀ s : ℝ, entropy μ (fun x => Real.exp (s * F x)) ≤
      ((A * s ^ 2 * moment μ F s : ℝ) : EReal)) {s : ℝ} (hs : 0 < s) :
    moment μ F s ≤ Real.exp (s * (∫ x, F x ∂μ) + A * s ^ 2) := by
  let I : ℝ → ℝ := fun r => ∫ x, F x * Real.exp (r * F x) ∂μ
  let q : ℝ → ℝ := fun r => Real.log (moment μ F r) / r - A * r
  let d : ℝ → ℝ := fun r =>
    ((I r / moment μ F r) * r - Real.log (moment μ F r)) / r ^ 2 - A
  have hd (r : ℝ) (hr : 0 < r) : HasDerivAt q (d r) r := by
    simpa only [q, d, I, Pi.div_apply, Pi.sub_apply, id_eq, mul_one] using!
      ((hasDerivAt_log_moment hF hb r).div (hasDerivAt_id r) hr.ne').sub
        ((hasDerivAt_id r).const_mul A)
  have hdnonpos (r : ℝ) (hr : 0 < r) : d r ≤ 0 := by
    have hE : r * I r - moment μ F r * Real.log (moment μ F r) ≤
        A * r ^ 2 * moment μ F r := by
      have he := hEnt r
      rw [entropy_exp_eq hF hb r] at he
      exact_mod_cast he
    have hP := moment_pos hF hb r
    have hn : (I r / moment μ F r) * r - Real.log (moment μ F r) =
        (r * I r - moment μ F r * Real.log (moment μ F r)) / moment μ F r := by
      field_simp [hP.ne']
    change ((I r / moment μ F r) * r - Real.log (moment μ F r)) / r ^ 2 - A ≤ 0
    apply sub_nonpos.mpr
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    rw [hn]
    exact (div_le_iff₀ hP).mpr hE
  have hanti : AntitoneOn q (Ioi (0 : ℝ)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
      (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hd r (interior_subset hr)).hasDerivWithinAt)
      (fun r hr => hdnonpos r (interior_subset hr))
  have hA : Continuous (fun r : ℝ => A * r) := by fun_prop
  have ht : Tendsto (fun r : ℝ => A * r) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using (hA.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto q (𝓝[>] 0) (𝓝 (∫ x, F x ∂μ)) := by
    simpa only [sub_zero] using
      ((tendsto_log_moment_div hF hb).mono_left (nhdsGT_le_nhdsNE 0)).sub ht
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r ≤ s :=
    (eventually_le_nhds hs).filter_mono nhdsWithin_le_nhds
  have hq : q s ≤ ∫ x, F x ∂μ := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrs
    exact hanti hr hs hrs
  have hdiv : Real.log (moment μ F s) / s ≤ (∫ x, F x ∂μ) + A * s := by
    dsimp only [q] at hq
    linarith only [hq]
  have hlog : Real.log (moment μ F s) ≤ s * (∫ x, F x ∂μ) + A * s ^ 2 := by
    calc
      _ ≤ ((∫ x, F x ∂μ) + A * s) * s := (div_le_iff₀ hs).mp hdiv
      _ = _ := by ring
  calc
    moment μ F s = Real.exp (Real.log (moment μ F s)) := (Real.exp_log (moment_pos hF hb s)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog

theorem centered_exp_le_pos [IsProbabilityMeasure μ]
    (hF : AEMeasurable F μ) (hb : ∀ᵐ x ∂μ, |F x| ≤ M) {A : ℝ}
    (hEnt : ∀ s : ℝ, entropy μ (fun x => Real.exp (s * F x)) ≤
      ((A * s ^ 2 * moment μ F s : ℝ) : EReal)) {s : ℝ} (hs : 0 < s) :
    (∫ x, Real.exp (s * (F x - ∫ x, F x ∂μ)) ∂μ) ≤ Real.exp (A * s ^ 2) := by
  rw [centered_moment_eq]
  calc
    _ ≤ Real.exp (-s * ∫ x, F x ∂μ) *
        Real.exp (s * (∫ x, F x ∂μ) + A * s ^ 2) :=
      mul_le_mul_of_nonneg_left (moment_le_of_entropy_control_pos hF hb hEnt hs)
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Complete scalar Herbst bound for every real parameter, including zero
and negative parameters. Actual moment finiteness and differentiability were
derived above from essential boundedness. The sole remaining analytic input
is the displayed entropy control, to be supplied by an LSI application. -/
theorem centered_exp_le_of_entropy_control [IsProbabilityMeasure μ]
    (hF : AEMeasurable F μ) (hb : ∀ᵐ x ∂μ, |F x| ≤ M) {A : ℝ}
    (hEnt : ∀ s : ℝ, entropy μ (fun x => Real.exp (s * F x)) ≤
      ((A * s ^ 2 * moment μ F s : ℝ) : EReal)) (s : ℝ) :
    (∫ x, Real.exp (s * (F x - ∫ x, F x ∂μ)) ∂μ) ≤ Real.exp (A * s ^ 2) := by
  rcases lt_trichotomy s 0 with hs | hs | hs
  · have hbneg : ∀ᵐ x ∂μ, |(-F x)| ≤ M := by simpa only [abs_neg] using hb
    have hEneg : ∀ r : ℝ, entropy μ (fun x => Real.exp (r * (-F x))) ≤
        ((A * r ^ 2 * moment μ (fun x => -F x) r : ℝ) : EReal) := by
      intro r
      simpa only [moment, mul_neg, neg_mul, neg_sq] using hEnt (-r)
    have hh := centered_exp_le_pos hF.neg hbneg hEneg (neg_pos.mpr hs)
    change (∫ x, Real.exp ((-s) * (-F x - ∫ x, -F x ∂μ)) ∂μ) ≤
      Real.exp (A * (-s) ^ 2) at hh
    have he (x : Ω) : Real.exp ((-s) * (-F x - ∫ x, -F x ∂μ)) =
        Real.exp (s * (F x - ∫ x, F x ∂μ)) := by
      rw [integral_neg]
      congr 1
      ring
    simp_rw [he] at hh
    simpa only [neg_sq] using hh
  · subst s
    simp
  · exact centered_exp_le_pos hF hb hEnt hs

end PeriodicAttractiveLogGas.HerbstEntropy
