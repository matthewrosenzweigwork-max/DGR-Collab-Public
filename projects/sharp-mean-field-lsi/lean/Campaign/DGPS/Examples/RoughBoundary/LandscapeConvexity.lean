import DGPS.Examples.RoughBoundary.LandscapeDerivatives
import DGPS.Examples.RoughBoundary.FeatureMoments

/-!
# Uniform convex neighbourhood of zero (RUF022)

Source `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 3.2 (3.3).  For a feature `U` with
`‖U‖ ≤ 1`, mean `0` and covariance `I / 2` (the output of RUF006), the potential
`Ψ(t) = ‖t‖² / (2κ₀) - log ∫ exp ⟪t, U⟫` satisfies `Ψ(0) = 0`, `∇Ψ(0) = 0`, `D²Ψ(0) = h I` with
`h = 1/22`, `‖D³Ψ‖ ≤ 8` (third centred tilted moment), and on `‖t‖ ≤ h/16`
`D²Ψ(t) ≥ (h/2) I` and `Ψ(t) ≥ (h/4) ‖t‖²`.
-/

open MeasureTheory Set Metric
open scoped ContDiff Real

namespace DGPS.Examples.RoughBoundary.Landscape

section tilt
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {V : Ω → E2}

/-- Weighted exponential moment `t ↦ ∫ p(V) exp ⟪t, V⟫ dμ`. -/
noncomputable def mom (μ : Measure Ω) (V : Ω → E2) (p : E2 → ℝ) (t : E2) : ℝ :=
  pint μ V (fun q => p q.1 * expPhi q) t

/-- Linear functional `ℓ_w(u) = ⟪u, w⟫`. -/
noncomputable def ell (w u : E2) : ℝ := inner ℝ u w

lemma contDiff_weight {p : E2 → ℝ} (hp : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (fun q : E2 × E2 => p q.1 * expPhi q) :=
  (hp.comp contDiff_fst).mul contDiff_expPhi

lemma contDiff_ell (w : E2) : ContDiff ℝ ∞ (ell w) :=
  contDiff_id.inner ℝ contDiff_const

lemma contDiff_mom (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) {p : E2 → ℝ}
    (hp : ContDiff ℝ ∞ p) : ContDiff ℝ ∞ (mom μ V p) :=
  contDiff_pint (contDiff_weight hp) hV hb

lemma fderiv_mom_apply (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) {p : E2 → ℝ}
    (hp : ContDiff ℝ ∞ p) (t w : E2) :
    fderiv ℝ (mom μ V p) t w = mom μ V (fun u => p u * ell w u) t := by
  have hΦ := contDiff_weight hp
  have h := fderiv_pint hΦ hV hb
  unfold mom
  rw [h]
  unfold pint
  rw [ContinuousLinearMap.integral_apply
    (integrable_pint (contDiff_pd hΦ).continuous hV hb t)]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hd1 : HasFDerivAt (fun s => p (V y) * expPhi (V y, s)) (pd (fun q => p q.1 * expPhi q) (V y, t)) t :=
      hasFDerivAt_pd (hΦ.differentiable (by simp)) (V y) t
    have hd2 : HasDerivAt (fun s : ℝ => p (V y) * expPhi (V y, t + s • w))
        (p (V y) * expPhi (V y, t) * ell w (V y)) 0 := by
      have e : (fun s : ℝ => p (V y) * expPhi (V y, t + s • w)) =
          fun s : ℝ => p (V y) * Real.exp (inner ℝ t (V y) + s * ell w (V y)) := by
        funext s
        simp [expPhi, ell, inner_add_left, inner_smul_left, real_inner_comm]
      rw [e]
      have h1 : HasDerivAt (fun s : ℝ => inner ℝ t (V y) + s * ell w (V y)) (ell w (V y)) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).mul_const (ell w (V y))).const_add (inner ℝ t (V y))
      have h2 := (h1.exp).const_mul (p (V y))
      convert h2 using 1
      simp [expPhi]; ring
    have hl : HasDerivAt (fun s : ℝ => t + s • w) w 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const w).const_add t
    have hd3 := (hd1.comp_hasDerivAt_of_eq (0:ℝ) hl (by simp))
    have := hd3.unique hd2
    show (pd (fun q => p q.1 * expPhi q) (V y, t)) w = _
    rw [this]; ring

/-- Tilted expectation `E_t[p(V)] = ∫ p(V) e^{⟪t,V⟫} / ∫ e^{⟪t,V⟫}`. -/
noncomputable def nm (μ : Measure Ω) (V : Ω → E2) (p : E2 → ℝ) (t : E2) : ℝ :=
  mom μ V p t / mom μ V (fun _ => 1) t

omit [IsProbabilityMeasure μ] in
lemma mom_one : pint μ V expPhi = mom μ V (fun _ => 1) := by
  funext t; simp [mom, pint]

lemma mom_one_pos (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (t : E2) :
    0 < mom μ V (fun _ => 1) t := by
  rw [← mom_one]; exact (pint_exp_props hV hb 0).2.1 t

lemma contDiff_one_weight : ContDiff ℝ ∞ (fun _ : E2 => (1 : ℝ)) := contDiff_const

lemma fderiv_nm_apply (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) {p : E2 → ℝ}
    (hp : ContDiff ℝ ∞ p) (t w : E2) :
    fderiv ℝ (nm μ V p) t w = nm μ V (fun u => p u * ell w u) t - nm μ V p t * nm μ V (ell w) t := by
  have hZ := mom_one_pos hV hb t
  have hdp : DifferentiableAt ℝ (mom μ V p) t :=
    ((contDiff_mom hV hb hp).differentiable (by simp)) t
  have hdZ : DifferentiableAt ℝ (mom μ V (fun _ => 1)) t :=
    ((contDiff_mom hV hb contDiff_one_weight).differentiable (by simp)) t
  have hinv : HasFDerivAt (fun x => (mom μ V (fun _ => 1) x)⁻¹)
      ((-(mom μ V (fun _ => 1) t ^ 2)⁻¹) • fderiv ℝ (mom μ V (fun _ => 1)) t) t := by
    have := (hasDerivAt_inv hZ.ne').comp_hasFDerivAt t hdZ.hasFDerivAt
    exact this
  have hm := hdp.hasFDerivAt.mul hinv
  have e : nm μ V p = fun x => mom μ V p x * (mom μ V (fun _ => 1) x)⁻¹ := by
    funext x; simp [nm, div_eq_mul_inv]
  rw [e]
  have hf := HasFDerivAt.fderiv (show HasFDerivAt (fun x => mom μ V p x * (mom μ V (fun _ => 1) x)⁻¹) _ t from hm)
  rw [hf]
  have e1 : (fun u => (1 : ℝ) * ell w u) = ell w := by funext u; simp
  simp only [smul_apply, add_apply, smul_eq_mul,
    fderiv_mom_apply hV hb hp, fderiv_mom_apply hV hb contDiff_one_weight, e1]
  simp only [nm, div_eq_mul_inv]
  field_simp
  ring

lemma hasFDerivAt_log_mom (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (t : E2) :
    HasFDerivAt (fun x => Real.log (mom μ V (fun _ => 1) x))
      ((mom μ V (fun _ => 1) t)⁻¹ • fderiv ℝ (mom μ V (fun _ => 1)) t) t :=
  (((contDiff_mom hV hb contDiff_one_weight).differentiable (by simp)) t).hasFDerivAt.log
    (mom_one_pos hV hb t).ne'

/-- The potential `Ψ(t) = ‖t‖²/(2κ) − log ∫ e^{⟪t,V⟫}`. -/
noncomputable def pot (κ : ℝ) (μ : Measure Ω) (V : Ω → E2) (t : E2) : ℝ :=
  ‖t‖ ^ 2 / (2 * κ) - Real.log (mom μ V (fun _ => 1) t)

lemma contDiff_pot (κ : ℝ) (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) :
    ContDiff ℝ ∞ (pot κ μ V) := by
  refine (((contDiff_norm_sq ℝ).div_const _)).sub ?_
  exact (contDiff_mom hV hb contDiff_one_weight).log fun t => (mom_one_pos hV hb t).ne'

lemma fderiv_pot_apply (κ : ℝ) (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (x c : E2) :
    fderiv ℝ (pot κ μ V) x c = inner ℝ x c / κ - nm μ V (ell c) x := by
  have h1 : HasFDerivAt (fun t : E2 => ‖t‖ ^ 2 / (2 * κ)) ((2 * κ)⁻¹ • (2 • innerSL ℝ x)) x := by
    have := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_smul (2 * κ)⁻¹
    convert this using 1
    funext t; simp [div_eq_inv_mul]
  have h2 := (hasFDerivAt_log_mom hV hb x)
  have h3 := h1.sub h2
  have e : pot κ μ V = fun t => ‖t‖ ^ 2 / (2 * κ) - Real.log (mom μ V (fun _ => 1) t) := rfl
  have h3' : HasFDerivAt (fun t => ‖t‖ ^ 2 / (2 * κ) - Real.log (mom μ V (fun _ => 1) t))
    ((2 * κ)⁻¹ • (2 • innerSL ℝ x) - (mom μ V (fun _ => 1) x)⁻¹ • fderiv ℝ (mom μ V (fun _ => 1)) x) x := h3
  rw [e, h3'.fderiv]
  simp only [sub_apply, smul_apply, smul_eq_mul,
    fderiv_mom_apply hV hb contDiff_one_weight]
  have e1 : (fun u => (1 : ℝ) * ell c u) = ell c := by funext u; simp
  rw [e1]
  simp [nm, innerSL_apply_apply, div_eq_inv_mul]
  field_simp

omit [IsProbabilityMeasure μ] in
lemma nm_eq_integral (p : E2 → ℝ) (t : E2) :
    nm μ V p t = ∫ y, p (V y) * (Real.exp (inner ℝ t (V y)) / mom μ V (fun _ => 1) t) ∂μ := by
  unfold nm
  have : mom μ V p t = ∫ y, p (V y) * Real.exp (inner ℝ t (V y)) ∂μ := by
    simp [mom, pint, expPhi]
  rw [this, ← integral_div]
  congr 1
  funext y; ring

lemma integrable_tilt (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) {p : E2 → ℝ}
    (hp : Continuous p) (t : E2) :
    Integrable (fun y => p (V y) * (Real.exp (inner ℝ t (V y)) / mom μ V (fun _ => 1) t)) μ := by
  have hc : Continuous (fun q : E2 × E2 => p q.1 * expPhi q) :=
    (hp.comp continuous_fst).mul contDiff_expPhi.continuous
  have h := (integrable_pint hc hV hb t).div_const (mom μ V (fun _ => 1) t)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [expPhi]; ring

lemma nm_add (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) {p₁ p₂ : E2 → ℝ}
    (h₁ : Continuous p₁) (h₂ : Continuous p₂) (t : E2) :
    nm μ V (fun u => p₁ u + p₂ u) t = nm μ V p₁ t + nm μ V p₂ t := by
  simp only [nm_eq_integral]
  rw [← integral_add (integrable_tilt hV hb h₁ t) (integrable_tilt hV hb h₂ t)]
  congr 1; funext y; ring

lemma nm_sub (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) {p₁ p₂ : E2 → ℝ}
    (h₁ : Continuous p₁) (h₂ : Continuous p₂) (t : E2) :
    nm μ V (fun u => p₁ u - p₂ u) t = nm μ V p₁ t - nm μ V p₂ t := by
  simp only [nm_eq_integral]
  rw [← integral_sub (integrable_tilt hV hb h₁ t) (integrable_tilt hV hb h₂ t)]
  congr 1; funext y; ring

omit [IsProbabilityMeasure μ] in
lemma nm_const_mul {p : E2 → ℝ}
    (c : ℝ) (t : E2) :
    nm μ V (fun u => c * p u) t = c * nm μ V p t := by
  simp only [nm_eq_integral]
  rw [← integral_const_mul]
  congr 1; funext y; ring

lemma nm_one (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (t : E2) :
    nm μ V (fun _ => 1) t = 1 := by
  unfold nm
  exact div_self (mom_one_pos hV hb t).ne'

lemma nm_const (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (c : ℝ) (t : E2) :
    nm μ V (fun _ => c) t = c := by
  have := nm_const_mul (μ := μ) (V := V) (p := fun _ => (1 : ℝ)) c t
  simp only [mul_one] at this
  rw [this, nm_one hV hb]; ring

lemma tilt_nonneg (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (t : E2) (y : Ω) :
    0 ≤ Real.exp (inner ℝ t (V y)) / mom μ V (fun _ => 1) t :=
  div_nonneg (Real.exp_pos _).le (mom_one_pos hV hb t).le

lemma abs_nm_le (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) {p : E2 → ℝ}
    {M : ℝ} (hM : ∀ᵐ y ∂μ, |p (V y)| ≤ M) (t : E2) :
    |nm μ V p t| ≤ M := by
  rw [nm_eq_integral]
  have hq : Integrable (fun y => Real.exp (inner ℝ t (V y)) / mom μ V (fun _ => 1) t) μ := by
    simpa using integrable_tilt hV hb (p := fun _ => 1) continuous_const t
  have h1 := nm_one hV hb t
  rw [nm_eq_integral] at h1
  simp only [one_mul] at h1
  have := norm_integral_le_of_norm_le (hq.const_mul M)
    (f := fun y => p (V y) * (Real.exp (inner ℝ t (V y)) / mom μ V (fun _ => 1) t))
    (hM.mono fun y hy => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tilt_nonneg hV hb t y)]
      exact mul_le_mul_of_nonneg_right hy (tilt_nonneg hV hb t y))
  rw [Real.norm_eq_abs, integral_const_mul, h1, mul_one] at this
  exact this

lemma abs_ell_le (w : E2) {u : E2} (hu : ‖u‖ ≤ 1) : |ell w u| ≤ ‖w‖ := by
  have := abs_real_inner_le_norm u w
  have h2 : ‖u‖ * ‖w‖ ≤ ‖w‖ := mul_le_of_le_one_left (norm_nonneg _) hu
  exact this.trans h2

lemma continuous_ell (w : E2) : Continuous (ell w) := (contDiff_ell w).continuous

lemma contDiff_nm (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) {p : E2 → ℝ}
    (hp : ContDiff ℝ ∞ p) : ContDiff ℝ ∞ (nm μ V p) :=
  (contDiff_mom hV hb hp).div (contDiff_mom hV hb contDiff_one_weight)
    fun t => (mom_one_pos hV hb t).ne'

lemma fderiv_fderiv_apply' {f : E2 → ℝ} (hf : ContDiff ℝ ∞ f) (x a b : E2) :
    fderiv ℝ (fderiv ℝ f) x a b = fderiv ℝ (fun y => fderiv ℝ f y b) x a := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  have := fderiv_clm_apply hd (differentiableAt_const b) (x := x)
  have h2 : fderiv ℝ (fun y => (fderiv ℝ f y) b) x = (fderiv ℝ (fderiv ℝ f) x).flip b := by
    simpa using this
  rw [h2]; rfl

lemma hasFDerivAt_inner_div (κ : ℝ) (c x : E2) :
    HasFDerivAt (fun y : E2 => inner ℝ y c / κ) (κ⁻¹ • innerSL ℝ c) x := by
  have := ((innerSL ℝ c).hasFDerivAt (x := x)).const_smul κ⁻¹
  convert this using 1
  funext y; simp [div_eq_inv_mul, real_inner_comm]

lemma fderiv_fderiv_pot (κ : ℝ) (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (x b c : E2) :
    fderiv ℝ (fderiv ℝ (pot κ μ V)) x b c =
      inner ℝ b c / κ - (nm μ V (fun u => ell b u * ell c u) x - nm μ V (ell b) x * nm μ V (ell c) x) := by
  rw [fderiv_fderiv_apply' (contDiff_pot κ hV hb)]
  have e : (fun y => fderiv ℝ (pot κ μ V) y c) = fun y => inner ℝ y c / κ - nm μ V (ell c) y := by
    funext y; exact fderiv_pot_apply κ hV hb y c
  rw [e]
  have h2 : HasFDerivAt (nm μ V (ell c)) (fderiv ℝ (nm μ V (ell c)) x) x :=
    (((contDiff_nm hV hb (contDiff_ell c)).differentiable (by simp)) x).hasFDerivAt
  have h3 := (hasFDerivAt_inner_div κ c x).sub h2
  have h3' : HasFDerivAt (fun y => inner ℝ y c / κ - nm μ V (ell c) y)
    (κ⁻¹ • innerSL ℝ c - fderiv ℝ (nm μ V (ell c)) x) x := h3
  rw [h3'.fderiv]
  simp only [sub_apply, smul_apply, smul_eq_mul, innerSL_apply_apply,
    fderiv_nm_apply hV hb (contDiff_ell c)]
  have ec : (fun u => ell c u * ell b u) = fun u => ell b u * ell c u := by funext u; ring
  rw [ec, real_inner_comm]; ring


lemma nm_centered3 (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) {A B C : E2 → ℝ}
    (hA : Continuous A) (hB : Continuous B) (hC : Continuous C) (x : E2) :
    nm μ V (fun u => (A u - nm μ V A x) * (B u - nm μ V B x) * (C u - nm μ V C x)) x =
      nm μ V (fun u => A u * B u * C u) x - nm μ V A x * nm μ V (fun u => B u * C u) x
        - nm μ V B x * nm μ V (fun u => A u * C u) x - nm μ V C x * nm μ V (fun u => A u * B u) x
        + 2 * nm μ V A x * nm μ V B x * nm μ V C x := by
  generalize hα : nm μ V A x = α
  generalize hβ : nm μ V B x = β
  generalize hγ : nm μ V C x = γ
  have e : (fun u => (A u - α) * (B u - β) * (C u - γ)) =
      fun u => (((A u * B u * C u - α * (B u * C u)) - β * (A u * C u)) - γ * (A u * B u)) +
        (α * β) * C u + (α * γ) * B u + (β * γ) * A u - α * β * γ := by
    funext u; ring
  rw [e]
  simp (disch := fun_prop) only [nm_sub hV hb, nm_add hV hb, nm_const_mul, nm_const hV hb, hα, hβ, hγ]
  ring

lemma fderiv_hess_pot (κ : ℝ) (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (x a b c : E2) :
    fderiv ℝ (fun y => inner ℝ b c / κ - (nm μ V (fun u => ell b u * ell c u) y -
        nm μ V (ell b) y * nm μ V (ell c) y)) x a =
      -(nm μ V (fun u => (ell a u - nm μ V (ell a) x) * (ell b u - nm μ V (ell b) x) *
          (ell c u - nm μ V (ell c) x)) x) := by
  have hbc : ContDiff ℝ ∞ (fun u => ell b u * ell c u) := (contDiff_ell b).mul (contDiff_ell c)
  have d1 := (((contDiff_nm hV hb hbc).differentiable (by simp)) x).hasFDerivAt
  have d2 := (((contDiff_nm hV hb (contDiff_ell b)).differentiable (by simp)) x).hasFDerivAt
  have d3 := (((contDiff_nm hV hb (contDiff_ell c)).differentiable (by simp)) x).hasFDerivAt
  have h := (hasFDerivAt_const (inner ℝ b c / κ) x).sub (d1.sub (d2.mul d3))
  have h' : HasFDerivAt (fun y => inner ℝ b c / κ - (nm μ V (fun u => ell b u * ell c u) y -
        nm μ V (ell b) y * nm μ V (ell c) y)) _ x := h
  rw [h'.fderiv]
  simp only [sub_apply, smul_apply, add_apply, smul_eq_mul, zero_apply,
    fderiv_nm_apply hV hb hbc, fderiv_nm_apply hV hb (contDiff_ell b),
    fderiv_nm_apply hV hb (contDiff_ell c)]
  rw [nm_centered3 hV hb (continuous_ell a) (continuous_ell b) (continuous_ell c)]
  have e1 : (fun u => ell b u * ell c u * ell a u) = fun u => ell a u * ell b u * ell c u := by
    funext u; ring
  have e2 : (fun u => ell b u * ell a u) = fun u => ell a u * ell b u := by funext u; ring
  have e3 : (fun u => ell c u * ell a u) = fun u => ell a u * ell c u := by funext u; ring
  rw [e1, e2, e3]
  ring

lemma abs_centered_le (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (a x : E2) :
    ∀ᵐ y ∂μ, |ell a (V y) - nm μ V (ell a) x| ≤ 2 * ‖a‖ := by
  have h1 : |nm μ V (ell a) x| ≤ ‖a‖ :=
    abs_nm_le hV hb (hb.mono fun y hy => abs_ell_le a hy) x
  exact hb.mono fun y hy => by
    have := abs_ell_le a hy
    calc |ell a (V y) - nm μ V (ell a) x| ≤ |ell a (V y)| + |nm μ V (ell a) x| := abs_sub _ _
      _ ≤ 2 * ‖a‖ := by linarith

lemma abs_third_le (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (x a b c : E2) :
    |nm μ V (fun u => (ell a u - nm μ V (ell a) x) * (ell b u - nm μ V (ell b) x) *
          (ell c u - nm μ V (ell c) x)) x| ≤ 8 * (‖a‖ * ‖b‖ * ‖c‖) := by
  have hcont : Continuous (fun u => (ell a u - nm μ V (ell a) x) * (ell b u - nm μ V (ell b) x) *
          (ell c u - nm μ V (ell c) x)) := by
    have := continuous_ell a; have := continuous_ell b; have := continuous_ell c
    fun_prop
  refine (abs_nm_le hV hb (M := (2 * ‖a‖) * (2 * ‖b‖) * (2 * ‖c‖)) ?_ x).trans (le_of_eq (by ring))
  filter_upwards [abs_centered_le hV hb a x, abs_centered_le hV hb b x,
    abs_centered_le hV hb c x] with y ha hb' hc
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul ha hb' (abs_nonneg _) (by positivity)) hc (abs_nonneg _)
    (by positivity)

lemma norm_iteratedFDeriv_three_pot_le (κ : ℝ) (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (x : E2) :
    ‖iteratedFDeriv ℝ 3 (pot κ μ V) x‖ ≤ 8 := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by norm_num) fun m => ?_
  have hf := contDiff_pot κ hV hb
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 (pot κ μ V)) x :=
    (hf.differentiable_iteratedFDeriv (m := 2) (by norm_cast)) x
  have h1 : iteratedFDeriv ℝ 3 (pot κ μ V) x m =
      fderiv ℝ (fun y => iteratedFDeriv ℝ 2 (pot κ μ V) y (Fin.tail m)) x (m 0) := by
    rw [fderiv_continuousMultilinear_apply_const hd]
    exact iteratedFDeriv_succ_apply_left m
  have e : (fun y => iteratedFDeriv ℝ 2 (pot κ μ V) y (Fin.tail m)) = fun y =>
      inner ℝ (m 1) (m 2) / κ - (nm μ V (fun u => ell (m 1) u * ell (m 2) u) y -
        nm μ V (ell (m 1)) y * nm μ V (ell (m 2)) y) := by
    funext y
    rw [iteratedFDeriv_two_apply, fderiv_fderiv_pot κ hV hb]
    rfl
  rw [h1, e, fderiv_hess_pot κ hV hb, Real.norm_eq_abs, abs_neg]
  refine (abs_third_le hV hb x (m 0) (m 1) (m 2)).trans (le_of_eq ?_)
  simp [Fin.prod_univ_three]

lemma mom_one_zero : mom μ V (fun _ => 1) 0 = 1 := by
  simp [mom, pint, expPhi]

lemma nm_zero (p : E2 → ℝ) :
    nm μ V p 0 = ∫ y, p (V y) ∂μ := by
  rw [nm_eq_integral, mom_one_zero]
  simp

lemma integrable_coord (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (i j : Fin 2) :
    Integrable (fun y => V y i * V y j) μ := by
  refine Integrable.of_bound (C := 1) ?_ (hb.mono fun y hy => ?_)
  · have hi : Measurable fun y => V y i := (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp hV
    have hj : Measurable fun y => V y j := (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable.comp hV
    exact (hi.mul hj).aestronglyMeasurable
  · rw [norm_mul]
    have h1 : ‖V y i‖ ≤ 1 := (PiLp.norm_apply_le (V y) i).trans hy
    have h2 : ‖V y j‖ ≤ 1 := (PiLp.norm_apply_le (V y) j).trans hy
    calc ‖V y i‖ * ‖V y j‖ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := by norm_num

lemma hess_zero_aux (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1)
    (hmean : ∫ y, V y ∂μ = 0)
    (hcov : ∀ i j : Fin 2, ∫ y, V y i * V y j ∂μ = if i = j then 1 / 2 else 0) (b c : E2) :
    nm μ V (ell b) 0 = 0 ∧ nm μ V (fun u => ell b u * ell c u) 0 = inner ℝ b c / 2 := by
  have hint : Integrable V μ := Integrable.of_bound hV.aestronglyMeasurable 1 hb
  constructor
  · rw [nm_zero]
    have e : (fun y => ell b (V y)) = fun y => inner ℝ b (V y) := by
      funext y; exact real_inner_comm _ _
    rw [e, integral_inner hint, hmean, inner_zero_right]
  · rw [nm_zero]
    have e : ∀ y, ell b (V y) * ell c (V y) =
        b 0 * c 0 * (V y 0 * V y 0) + b 0 * c 1 * (V y 0 * V y 1) +
          b 1 * c 0 * (V y 1 * V y 0) + b 1 * c 1 * (V y 1 * V y 1) := by
      intro y
      simp [ell, PiLp.inner_apply, Fin.sum_univ_two]
      ring
    simp only [e]
    have i00 := integrable_coord hV hb 0 0
    have i01 := integrable_coord hV hb 0 1
    have i10 := integrable_coord hV hb 1 0
    have i11 := integrable_coord hV hb 1 1
    rw [integral_add, integral_add, integral_add, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul, hcov, hcov, hcov, hcov]
    · simp [PiLp.inner_apply, Fin.sum_univ_two]; ring
    all_goals first
      | exact i00.const_mul _ | exact i01.const_mul _ | exact i10.const_mul _
      | exact i11.const_mul _
      | exact ((i00.const_mul _).add (i01.const_mul _))
      | exact (((i00.const_mul _).add (i01.const_mul _)).add (i10.const_mul _))

lemma quad_lower_bound (f : E2 → ℝ) (hf : ContDiff ℝ ∞ f) (m : ℝ) (t : E2)
    (h0 : f 0 = 0) (h1 : fderiv ℝ f 0 = 0)
    (hH : ∀ s ∈ Icc (0:ℝ) 1, m * ‖t‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) (s • t) t t) :
    m / 2 * ‖t‖ ^ 2 ≤ f t := by
  set c : ℝ := m * ‖t‖ ^ 2 with hc
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s • t) t s := fun s => by
    simpa using (hasDerivAt_id s).smul_const t
  have hd1 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f (s • t)) (fderiv ℝ f (s • t) t) s := fun s =>
    ((hf.differentiable (by simp)) (s • t)).hasFDerivAt.comp_hasDerivAt s (hline s)
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hd2 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ f (s • t) t)
      (fderiv ℝ (fderiv ℝ f) (s • t) t t) s := fun s => by
    have h := (((hfd.differentiable (by simp)) (s • t)).hasFDerivAt.comp_hasDerivAt s (hline s))
    simpa using h.clm_apply (hasDerivAt_const s t)
  -- first integration
  have hd3 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ f (s • t) t - c * s)
      (fderiv ℝ (fderiv ℝ f) (s • t) t t - c * 1) s := fun s =>
    (hd2 s).sub ((hasDerivAt_id s).const_mul c)
  have hψ1 : MonotoneOn (fun s : ℝ => fderiv ℝ f (s • t) t - c * s) (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun s _ => (hd3 s).continuousAt.continuousWithinAt
    · exact fun s _ => (hd3 s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hd3 s).deriv]
      have := hH s (Ioo_subset_Icc_self hs)
      linarith
  have hpos : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ fderiv ℝ f (s • t) t - c * s := by
    intro s hs
    have := hψ1 (left_mem_Icc.2 zero_le_one) hs hs.1
    simpa [h1] using this
  have hψ2 : MonotoneOn (fun s : ℝ => f (s • t) - c / 2 * s ^ 2) (Icc 0 1) := by
    have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f (s • t) - c / 2 * s ^ 2)
        (fderiv ℝ f (s • t) t - c * s) s := fun s => by
      have := (hd1 s).sub (((hasDerivAt_pow 2 s).const_mul (c / 2)))
      convert this using 1
      simp; ring
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun s _ => (hd s).continuousAt.continuousWithinAt
    · exact fun s _ => (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hd s).deriv]
      exact hpos s (Ioo_subset_Icc_self hs)
  have := hψ2 (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_le_one
  simp [h0] at this
  rw [hc] at this
  linarith

lemma hess_variation (κ : ℝ) (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (v x : E2) :
    |fderiv ℝ (fderiv ℝ (pot κ μ V)) x v v - fderiv ℝ (fderiv ℝ (pot κ μ V)) 0 v v| ≤
      8 * ‖v‖ ^ 2 * ‖x‖ := by
  have hf := contDiff_pot κ hV hb
  have hfd : ContDiff ℝ ∞ (fderiv ℝ (pot κ μ V)) := hf.fderiv_right (by simp)
  have hfd2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (pot κ μ V))) := hfd.fderiv_right (by simp)
  have hGd : Differentiable ℝ (fun y => fderiv ℝ (fderiv ℝ (pot κ μ V)) y v v) :=
    ((hfd2.differentiable (by simp)).clm_apply (differentiable_const v)).clm_apply
      (differentiable_const v)
  have hGe : (fun y => fderiv ℝ (fderiv ℝ (pot κ μ V)) y v v) = fun y =>
      inner ℝ v v / κ - (nm μ V (fun u => ell v u * ell v u) y -
        nm μ V (ell v) y * nm μ V (ell v) y) :=
    funext fun y => fderiv_fderiv_pot κ hV hb y v v
  have hbound : ∀ y, ‖fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ (pot κ μ V)) y v v) y‖ ≤
      8 * ‖v‖ ^ 2 := by
    intro y
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a => ?_
    rw [hGe, fderiv_hess_pot κ hV hb, Real.norm_eq_abs, abs_neg]
    refine (abs_third_le hV hb y a v v).trans (le_of_eq ?_)
    ring
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (fun y _ => hGd y)
    (fun y _ => hbound y) convex_univ (mem_univ (0 : E2)) (mem_univ x)
  rw [Real.norm_eq_abs, sub_zero] at this
  exact this

lemma pot_zero (κ : ℝ) : pot κ μ V 0 = 0 := by
  simp [pot, mom_one_zero]

lemma fderiv_pot_zero (κ : ℝ) (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1)
    (hmean : ∫ y, V y ∂μ = 0)
    (hcov : ∀ i j : Fin 2, ∫ y, V y i * V y j ∂μ = if i = j then 1 / 2 else 0) :
    fderiv ℝ (pot κ μ V) 0 = 0 := by
  ext c
  rw [fderiv_pot_apply κ hV hb, (hess_zero_aux hV hb hmean hcov c c).1]
  simp

lemma hess_pot_zero (κ : ℝ) (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1)
    (hmean : ∫ y, V y ∂μ = 0)
    (hcov : ∀ i j : Fin 2, ∫ y, V y i * V y j ∂μ = if i = j then 1 / 2 else 0) (b c : E2) :
    fderiv ℝ (fderiv ℝ (pot κ μ V)) 0 b c = (1 / κ - 1 / 2) * inner ℝ b c := by
  have h := hess_zero_aux hV hb hmean hcov b c
  rw [fderiv_fderiv_pot κ hV hb, h.1, h.2]
  ring

lemma convex_neighborhood (κ : ℝ) (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1)
    (hmean : ∫ y, V y ∂μ = 0)
    (hcov : ∀ i j : Fin 2, ∫ y, V y i * V y j ∂μ = if i = j then 1 / 2 else 0)
    {h : ℝ} (hh : h = 1 / κ - 1 / 2) (t : E2) (ht : ‖t‖ ≤ h / 16) :
    (∀ v : E2, h / 2 * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (pot κ μ V)) t v v) ∧
      h / 4 * ‖t‖ ^ 2 ≤ pot κ μ V t := by
  have hpos : 0 ≤ h / 16 := (norm_nonneg t).trans ht
  have hlow : ∀ x : E2, ‖x‖ ≤ h / 16 → ∀ v : E2,
      h / 2 * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (pot κ μ V)) x v v := by
    intro x hx v
    have h1 := hess_variation κ hV hb v x
    have h0 := hess_pot_zero κ hV hb hmean hcov v v
    rw [← hh, real_inner_self_eq_norm_sq] at h0
    have h2 : 8 * ‖v‖ ^ 2 * ‖x‖ ≤ 8 * ‖v‖ ^ 2 * (h / 16) :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    have h3 := (abs_le.1 (h1.trans h2)).1
    nlinarith [h3, h0]
  refine ⟨hlow t ht, ?_⟩
  suffices hq : h / 2 / 2 * ‖t‖ ^ 2 ≤ pot κ μ V t by linarith
  refine quad_lower_bound (pot κ μ V) (contDiff_pot κ hV hb) (h / 2) t (pot_zero κ)
    (fderiv_pot_zero κ hV hb hmean hcov) ?_
  intro s hs
  have hn : ‖s • t‖ ≤ h / 16 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc s * ‖t‖ ≤ 1 * ‖t‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      _ ≤ h / 16 := by linarith
  have := hlow _ hn t
  linarith

end tilt

section final

lemma featurePotential_eq (κ : ℝ) (U : Torus 1 → E2) :
    Semicontinuity.featurePotential κ U = pot κ (DGPS.haar 1) U := by
  funext t
  simp [Semicontinuity.featurePotential, Semicontinuity.featureLogPartition, pot, mom, pint,
    expPhi]

/-- RUF022: uniform convex neighbourhood of zero for the feature potential
`Ψ(t) = ‖t‖² / (2κ₀) - log ∫ exp ⟪t, U⟫` of a unit feature `U` with mean `0` and covariance
`I / 2`: `Ψ(0) = 0`, `∇Ψ(0) = 0`, `D²Ψ(0) = h I` with `h = 1/22`, `‖D³Ψ‖ ≤ 8`, and for
`‖t‖ ≤ h/16`, `D²Ψ(t) ≥ (h/2) I` and `Ψ(t) ≥ (h/4) ‖t‖²`. -/
theorem uniform_convex_neighborhood_of_zero {U : Torus 1 → E2} (hU : Measurable U)
    (hb : ∀ y, ‖U y‖ ≤ 1) (hmean : ∫ y, U y ∂DGPS.haar 1 = 0)
    (hcov : ∀ i j : Fin 2, ∫ y, U y i * U y j ∂DGPS.haar 1 = if i = j then 1 / 2 else 0) :
    Semicontinuity.featurePotential kappa0 U 0 = 0 ∧
      fderiv ℝ (Semicontinuity.featurePotential kappa0 U) 0 = 0 ∧
      (∀ v w : E2, fderiv ℝ (fderiv ℝ (Semicontinuity.featurePotential kappa0 U)) 0 v w =
        (1 / 22) * inner ℝ v w) ∧
      ContDiff ℝ ∞ (Semicontinuity.featurePotential kappa0 U) ∧
      (∀ t : E2, ‖iteratedFDeriv ℝ 3 (Semicontinuity.featurePotential kappa0 U) t‖ ≤ 8) ∧
      (∀ t : E2, ‖t‖ ≤ (1 / 22) / 16 → ∀ v : E2, (1 / 22) / 2 * ‖v‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ (Semicontinuity.featurePotential kappa0 U)) t v v) ∧
      (∀ t : E2, ‖t‖ ≤ (1 / 22) / 16 →
        (1 / 22) / 4 * ‖t‖ ^ 2 ≤ Semicontinuity.featurePotential kappa0 U t) := by
  have hbb : ∀ᵐ w ∂DGPS.haar 1, ‖U w‖ ≤ 1 := Filter.Eventually.of_forall hb
  have hk : 1 / kappa0 - 1 / 2 = 1 / 22 := by unfold kappa0; norm_num
  rw [featurePotential_eq]
  refine ⟨pot_zero _, fderiv_pot_zero _ hU hbb hmean hcov, ?_, contDiff_pot _ hU hbb,
    norm_iteratedFDeriv_three_pot_le _ hU hbb, ?_, ?_⟩
  · intro v w
    rw [hess_pot_zero _ hU hbb hmean hcov, hk]
  · intro t ht v
    exact (convex_neighborhood kappa0 hU hbb hmean hcov hk.symm t ht).1 v
  · intro t ht
    exact (convex_neighborhood kappa0 hU hbb hmean hcov hk.symm t ht).2

end final

end DGPS.Examples.RoughBoundary.Landscape
