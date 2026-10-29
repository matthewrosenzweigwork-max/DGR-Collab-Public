import Mathlib
import DGPS.Foundations.Entropy
import DGPS.FiniteN.OrderedRadialAlternative
import DGPS.FiniteN.OrderedRadialUniformFIN039
import DGPS.FiniteN.Tools.PlanarPoincare
import DGPS.FiniteN.Tools.Rothaus

/-!
# FIN040: recorded radial to planar log-Sobolev theorem

Cattiaux-Guillin-Wu, arXiv:1912.10825, Theorem 4.5 / Proposition 5.1, specialised to the plane.
For a rotationally invariant probability measure `nu` on `R^2` with radial law `sigma` (and uniform
angle), a radial LSI constant `L` and a radial Poincare constant `P` for `sigma` give the planar
entropy bound
`Ent_nu(F^2) <= 40 (L + |int r dsigma| * sqrt (max P (int r^2 dsigma))) * int |grad F|^2 dnu`.
Conventions: `Ent <= C_LS * E` and `Var <= C_P * E`.  The proof is formalised in this file:
Herbst argument and Gaussian trick for the exponential radial moment, entropy decomposition in
polar coordinates, the angular L^1 entropy estimate (FIN041), the radius weighted term, and the
direct planar Poincare inequality (FIN042).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal Real ContDiff
open DGPS.FiniteN.Tools.PlanarPoincare

namespace DGPS.FiniteN

/-- Radial log-Sobolev inequality for the smooth test class (FIN044 form). -/
def RadialLSIFIN040 (σ : Measure ℝ) (L : ℝ) : Prop :=
  ∀ u : ℝ → ℝ, ContDiff ℝ ∞ u → Integrable (fun r => u r ^ 2) σ →
    Integrable (fun r => deriv u r ^ 2) σ →
    homogeneousEntropy σ (fun r => u r ^ 2) ≤ ENNReal.ofReal (L * ∫ r, deriv u r ^ 2 ∂σ)

theorem hasDerivAt_mgf_FIN040 {σ : Measure ℝ} [IsProbabilityMeasure σ] {φ : ℝ → ℝ}
    (hφ : Continuous φ) {B : ℝ} (hB : ∀ r, |φ r| ≤ B) (s : ℝ) :
    Integrable (fun r => φ r * Real.exp (s * φ r)) σ ∧
    HasDerivAt (fun s => ∫ r, Real.exp (s * φ r) ∂σ) (∫ r, φ r * Real.exp (s * φ r) ∂σ) s := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hexp : ∀ x r, Real.exp (x * φ r) ≤ Real.exp (|x| * B) := fun x r => by
    apply Real.exp_le_exp.mpr
    calc x * φ r ≤ |x * φ r| := le_abs_self _
      _ = |x| * |φ r| := abs_mul _ _
      _ ≤ |x| * B := mul_le_mul_of_nonneg_left (hB r) (abs_nonneg _)
  have hmeas : ∀ x, Continuous fun r => Real.exp (x * φ r) := fun x => by fun_prop
  have hint : ∀ x, Integrable (fun r => Real.exp (x * φ r)) σ := fun x =>
    Integrable.of_bound (hmeas x).aestronglyMeasurable (Real.exp (|x| * B))
      (Filter.Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hexp x r)
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun x r => Real.exp (x * φ r))
    (F' := fun x r => φ r * Real.exp (x * φ r)) (bound := fun _ => B * Real.exp ((|s| + 1) * B))
    (s := Metric.ball s 1) (Metric.ball_mem_nhds s one_pos) ?_ (hint s) ?_ ?_ (integrable_const _) ?_
  · exact Filter.Eventually.of_forall fun x => (hmeas x).aestronglyMeasurable
  · exact (by fun_prop : Continuous fun r => φ r * Real.exp (s * φ r)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun r x hx => ?_
    have hx' : |x| ≤ |s| + 1 := by
      have := Metric.mem_ball.mp hx
      rw [Real.dist_eq] at this
      calc |x| = |(x - s) + s| := by ring_nf
        _ ≤ |x - s| + |s| := abs_add_le _ _
        _ ≤ |s| + 1 := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hB r) ((hexp x r).trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hx' hB0))) (Real.exp_pos _).le hB0
  · refine Filter.Eventually.of_forall fun r x _ => ?_
    have := ((hasDerivAt_id x).mul_const (φ r)).exp
    simpa [mul_comm] using this

theorem mgf_pos_FIN040 {σ : Measure ℝ} [IsProbabilityMeasure σ] {φ : ℝ → ℝ}
    (hφ : Continuous φ) {B : ℝ} (hB : ∀ r, |φ r| ≤ B) (s : ℝ) :
    0 < ∫ r, Real.exp (s * φ r) ∂σ := by
  have h1 := (hasDerivAt_mgf_FIN040 (σ := σ) hφ hB s)
  have hint : Integrable (fun r => Real.exp (s * φ r)) σ := by
    refine Integrable.of_bound (by fun_prop : Continuous fun r => Real.exp (s * φ r)).aestronglyMeasurable
      (Real.exp (|s| * B)) (Filter.Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc s * φ r ≤ |s * φ r| := le_abs_self _
      _ = |s| * |φ r| := abs_mul _ _
      _ ≤ |s| * B := mul_le_mul_of_nonneg_left (hB r) (abs_nonneg _)
  exact integral_exp_pos hint

/-- One step of the Herbst argument: the entropy inequality for `e^{sφ}`. -/
theorem herbst_step_FIN040 {σ : Measure ℝ} [IsProbabilityMeasure σ] {L : ℝ} (hL : 0 < L)
    (hlsi : RadialLSIFIN040 σ L) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {B : ℝ}
    (hB : ∀ r, |φ r| ≤ B) (hd : ∀ r, |deriv φ r| ≤ 1) (s : ℝ) :
    s * (∫ r, φ r * Real.exp (s * φ r) ∂σ)
      - (∫ r, Real.exp (s * φ r) ∂σ) * Real.log (∫ r, Real.exp (s * φ r) ∂σ)
      ≤ L * s ^ 2 / 4 * ∫ r, Real.exp (s * φ r) ∂σ := by
  have hφc : Continuous φ := hφ.continuous
  obtain ⟨hI1, -⟩ := hasDerivAt_mgf_FIN040 (σ := σ) hφc hB s
  have hI0 : Integrable (fun r => Real.exp (s * φ r)) σ := by
    refine Integrable.of_bound (by fun_prop : Continuous fun r => Real.exp (s * φ r)).aestronglyMeasurable
      (Real.exp (|s| * B)) (Filter.Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc s * φ r ≤ |s * φ r| := le_abs_self _
      _ = |s| * |φ r| := abs_mul _ _
      _ ≤ |s| * B := mul_le_mul_of_nonneg_left (hB r) (abs_nonneg _)
  set u : ℝ → ℝ := fun r => Real.exp (s * φ r / 2) with hu
  have hucd : ContDiff ℝ ∞ u := by
    have : ContDiff ℝ ∞ fun r => s * φ r / 2 := (contDiff_const.mul hφ).div_const _
    exact Real.contDiff_exp.comp this
  have hu2 : ∀ r, u r ^ 2 = Real.exp (s * φ r) := fun r => by
    simp only [hu]; rw [sq, ← Real.exp_add]; ring_nf
  have hdu : ∀ r, deriv u r = Real.exp (s * φ r / 2) * (s * deriv φ r / 2) := fun r => by
    have h1 : HasDerivAt φ (deriv φ r) r := (hφ.differentiable (by simp) r).hasDerivAt
    have h2 := (((h1.const_mul s).div_const 2).exp)
    simpa [hu, mul_comm] using h2.deriv
  have hdu2 : ∀ r, deriv u r ^ 2 = s ^ 2 / 4 * deriv φ r ^ 2 * Real.exp (s * φ r) := fun r => by
    rw [hdu, mul_pow, ← hu2 r]; simp only [hu]; ring
  have hdu2_le : ∀ r, deriv u r ^ 2 ≤ s ^ 2 / 4 * Real.exp (s * φ r) := fun r => by
    rw [hdu2]
    have : deriv φ r ^ 2 ≤ 1 := by
      have := hd r
      calc deriv φ r ^ 2 = |deriv φ r| ^ 2 := (sq_abs _).symm
        _ ≤ 1 := by nlinarith [abs_nonneg (deriv φ r)]
    have h3 : 0 < Real.exp (s * φ r) := Real.exp_pos _
    have h4 : s ^ 2 / 4 * deriv φ r ^ 2 ≤ s ^ 2 / 4 := by
      nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.2 this)]
    exact mul_le_mul_of_nonneg_right h4 h3.le
  have hdu2_cont : Continuous fun r => deriv u r ^ 2 := by
    have : Continuous fun r => deriv u r := hucd.continuous_deriv (by simp)
    fun_prop
  have hdu_int : Integrable (fun r => deriv u r ^ 2) σ := by
    refine Integrable.mono' (hI0.const_mul (s ^ 2 / 4)) hdu2_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hdu2_le r
  have hu2_int : Integrable (fun r => u r ^ 2) σ := by simpa [hu2] using hI0
  have key := hlsi u hucd hu2_int hdu_int
  have hform : homogeneousEntropy σ (fun r => u r ^ 2) = ENNReal.ofReal
      (s * (∫ r, φ r * Real.exp (s * φ r) ∂σ)
        - (∫ r, Real.exp (s * φ r) ∂σ) * Real.log (∫ r, Real.exp (s * φ r) ∂σ)) := by
    have hfun : (fun r => u r ^ 2) = fun r => Real.exp (s * φ r) := funext hu2
    rw [hfun, homogeneousEntropy_eq_formula (Filter.Eventually.of_forall fun r => (Real.exp_pos _).le)
      hI0]
    · congr 1
      have : ∀ r, Real.exp (s * φ r) * Real.log (Real.exp (s * φ r))
          = s * (φ r * Real.exp (s * φ r)) := fun r => by rw [Real.log_exp]; ring
      simp_rw [this]
      rw [integral_const_mul]
    · have : ∀ r, Real.exp (s * φ r) * Real.log (Real.exp (s * φ r))
          = s * (φ r * Real.exp (s * φ r)) := fun r => by rw [Real.log_exp]; ring
      simp_rw [this]
      exact hI1.const_mul s
  rw [hform] at key
  have hint_le : ∫ r, deriv u r ^ 2 ∂σ ≤ s ^ 2 / 4 * ∫ r, Real.exp (s * φ r) ∂σ := by
    rw [← integral_const_mul]
    exact integral_mono hdu_int (hI0.const_mul _) hdu2_le
  have hnn : 0 ≤ L * ∫ r, deriv u r ^ 2 ∂σ := mul_nonneg hL.le (integral_nonneg fun r => sq_nonneg _)
  have := (ENNReal.ofReal_le_ofReal_iff hnn).mp key
  calc _ ≤ L * ∫ r, deriv u r ^ 2 ∂σ := this
    _ ≤ L * (s ^ 2 / 4 * ∫ r, Real.exp (s * φ r) ∂σ) := mul_le_mul_of_nonneg_left hint_le hL.le
    _ = _ := by ring

/-- Herbst's argument for bounded smooth `1`-Lipschitz `φ`. -/
theorem herbst_bounded_FIN040 {σ : Measure ℝ} [IsProbabilityMeasure σ] {L : ℝ} (hL : 0 < L)
    (hlsi : RadialLSIFIN040 σ L) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {B : ℝ}
    (hB : ∀ r, |φ r| ≤ B) (hd : ∀ r, |deriv φ r| ≤ 1) {l : ℝ} (hl : 0 < l) :
    ∫ r, Real.exp (l * φ r) ∂σ ≤ Real.exp (l * ∫ r, φ r ∂σ + L * l ^ 2 / 4) := by
  have hφc : Continuous φ := hφ.continuous
  set Z : ℝ → ℝ := fun s => ∫ r, Real.exp (s * φ r) ∂σ with hZ
  set Z' : ℝ → ℝ := fun s => ∫ r, φ r * Real.exp (s * φ r) ∂σ with hZ'
  have hZd : ∀ s, HasDerivAt Z (Z' s) s := fun s => (hasDerivAt_mgf_FIN040 (σ := σ) hφc hB s).2
  have hZp : ∀ s, 0 < Z s := fun s => mgf_pos_FIN040 (σ := σ) hφc hB s
  have hZ0 : Z 0 = 1 := by simp [hZ]
  have hZ'0 : Z' 0 = ∫ r, φ r ∂σ := by simp [hZ']
  set G : ℝ → ℝ := fun s => Real.log (Z s) / s - L * s / 4 with hG
  have hGd : ∀ s, 0 < s → HasDerivAt G
      ((Z' s / Z s * s - Real.log (Z s) * 1) / s ^ 2 - L / 4) s := by
    intro s hs
    have h1 := (hZd s).log (hZp s).ne'
    have h2 := h1.div (hasDerivAt_id s) hs.ne'
    have h3 := h2.sub ((hasDerivAt_id s).const_mul L |>.div_const 4)
    have e : G = (fun y => Real.log (Z y)) / id - fun x => L * id x / 4 := by
      funext x; simp [hG]
    rw [e]
    exact h3.congr_deriv (by simp)
  have hGnp : ∀ s ∈ interior (Ioi (0 : ℝ)), deriv G s ≤ 0 := by
    intro s hs
    rw [interior_Ioi] at hs
    have hs' : 0 < s := hs
    rw [(hGd s hs').deriv]
    have hstep := herbst_step_FIN040 (σ := σ) hL hlsi hφ hB hd s
    have hzp := hZp s
    have : (Z' s / Z s * s - Real.log (Z s) * 1) / s ^ 2 = (s * Z' s - Z s * Real.log (Z s)) / (s ^ 2 * Z s) := by
      field_simp
    rw [this]
    have : (s * Z' s - Z s * Real.log (Z s)) / (s ^ 2 * Z s) ≤ L / 4 := by
      rw [div_le_iff₀ (by positivity)]
      have : s * Z' s - Z s * Real.log (Z s) ≤ L * s ^ 2 / 4 * Z s := hstep
      nlinarith
    linarith
  have hGdiff : DifferentiableOn ℝ G (interior (Ioi (0 : ℝ))) := by
    rw [interior_Ioi]
    exact fun s hs => (hGd s hs).differentiableAt.differentiableWithinAt
  have hGcont : ContinuousOn G (Ioi (0 : ℝ)) :=
    fun s hs => (hGd s hs).continuousAt.continuousWithinAt
  have hanti : AntitoneOn G (Ioi (0 : ℝ)) :=
    antitoneOn_of_deriv_nonpos (convex_Ioi 0) hGcont hGdiff hGnp
  -- limit at 0+
  have hlogd : HasDerivAt (fun s => Real.log (Z s)) (Z' 0 / Z 0) 0 := (hZd 0).log (hZp 0).ne'
  have hslope := hlogd.tendsto_slope_zero_right
  have hlim : Tendsto G (𝓝[>] 0) (𝓝 (∫ r, φ r ∂σ)) := by
    have h1 : Tendsto (fun t : ℝ => t⁻¹ • (Real.log (Z (0 + t)) - Real.log (Z 0)))
        (𝓝[>] 0) (𝓝 (Z' 0 / Z 0)) := hslope
    rw [hZ0, hZ'0] at h1
    simp only [div_one, Real.log_one, zero_add, sub_zero, smul_eq_mul] at h1
    have h2 : Tendsto (fun t : ℝ => L * t / 4) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => L * t / 4) (𝓝 0) (𝓝 (L * 0 / 4)) :=
        ((continuous_const.mul continuous_id).div_const 4).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have := h1.sub h2
    simp only [sub_zero] at this
    refine this.congr (fun t => ?_)
    simp [hG, div_eq_inv_mul]
  have hle : G l ≤ ∫ r, φ r ∂σ := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hl] with s hs
    exact hanti hs.1 hl hs.2.le
  have hlog : Real.log (Z l) ≤ l * (∫ r, φ r ∂σ) + L * l ^ 2 / 4 := by
    have : Real.log (Z l) / l ≤ (∫ r, φ r ∂σ) + L * l / 4 := by
      have := hle; simp only [hG] at this; linarith
    rw [div_le_iff₀ hl] at this
    nlinarith
  exact (Real.log_le_iff_le_exp (hZp l)).mp hlog

/-- The signed Herbst bound for a bounded smooth `1`-Lipschitz `φ` and every real `t`. -/
theorem herbst_signed_FIN040 {σ : Measure ℝ} [IsProbabilityMeasure σ] {L : ℝ} (hL : 0 < L)
    (hlsi : RadialLSIFIN040 σ L) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {B : ℝ}
    (hB : ∀ r, |φ r| ≤ B) (hd : ∀ r, |deriv φ r| ≤ 1) (t : ℝ) :
    ∫ r, Real.exp (t * φ r) ∂σ ≤ Real.exp (t * ∫ r, φ r ∂σ + L * t ^ 2 / 4) := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have h := herbst_bounded_FIN040 (σ := σ) hL hlsi (φ := fun r => -φ r) hφ.neg (B := B)
      (fun r => by rw [abs_neg]; exact hB r)
      (fun r => by rw [deriv.fun_neg, abs_neg]; exact hd r) (l := -t) (by linarith)
    have e1 : ∀ r, -t * -φ r = t * φ r := fun r => by ring
    simp_rw [e1] at h
    rw [integral_neg] at h
    have e2 : -t * -∫ r, φ r ∂σ + L * (-t) ^ 2 / 4 = t * ∫ r, φ r ∂σ + L * t ^ 2 / 4 := by ring
    rw [e2] at h
    exact h
  · subst ht; simp
  · exact herbst_bounded_FIN040 (σ := σ) hL hlsi hφ hB hd ht

/-- The arctan truncation of `r - m`. -/
noncomputable def truncFIN040 (m : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  ((n : ℝ) + 1) * Real.arctan ((r - m) / ((n : ℝ) + 1))

theorem truncFIN040_contDiff (m : ℝ) (n : ℕ) : ContDiff ℝ ∞ (truncFIN040 m n) := by
  unfold truncFIN040
  exact contDiff_const.mul (Real.contDiff_arctan.comp (((contDiff_id.sub contDiff_const)).div_const _))

theorem truncFIN040_bound (m : ℝ) (n : ℕ) (r : ℝ) :
    |truncFIN040 m n r| ≤ ((n : ℝ) + 1) * (π / 2) := by
  unfold truncFIN040
  have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [abs_mul, abs_of_pos hc]
  refine mul_le_mul_of_nonneg_left ?_ hc.le
  rw [abs_le]
  exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩

theorem truncFIN040_abs_le (m : ℝ) (n : ℕ) (r : ℝ) : |truncFIN040 m n r| ≤ |r - m| := by
  unfold truncFIN040
  have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [abs_mul, abs_of_pos hc]
  have := Real.abs_arctan_le_abs (x := (r - m) / ((n : ℝ) + 1))
  calc ((n : ℝ) + 1) * |Real.arctan ((r - m) / ((n : ℝ) + 1))|
      ≤ ((n : ℝ) + 1) * |(r - m) / ((n : ℝ) + 1)| := mul_le_mul_of_nonneg_left this hc.le
    _ = |r - m| := by rw [abs_div, abs_of_pos hc]; field_simp

theorem truncFIN040_deriv (m : ℝ) (n : ℕ) (r : ℝ) : |deriv (truncFIN040 m n) r| ≤ 1 := by
  have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : HasDerivAt (fun r => (r - m) / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1)) r := by
    simpa using ((hasDerivAt_id r).sub_const m).div_const ((n : ℝ) + 1)
  have h2 := (Real.hasDerivAt_arctan ((r - m) / ((n : ℝ) + 1))).comp r h1
  have h3 := h2.const_mul ((n : ℝ) + 1)
  have : deriv (truncFIN040 m n) r = ((n : ℝ) + 1) *
      ((1 / (1 + ((r - m) / ((n : ℝ) + 1)) ^ 2)) * (1 / ((n : ℝ) + 1))) := h3.deriv
  rw [this]
  have hq : 0 < 1 + ((r - m) / ((n : ℝ) + 1)) ^ 2 := by positivity
  have : ((n : ℝ) + 1) * ((1 / (1 + ((r - m) / ((n : ℝ) + 1)) ^ 2)) * (1 / ((n : ℝ) + 1)))
      = 1 / (1 + ((r - m) / ((n : ℝ) + 1)) ^ 2) := by field_simp
  rw [this, abs_of_pos (by positivity), div_le_one hq]
  nlinarith [sq_nonneg ((r - m) / ((n : ℝ) + 1))]

theorem truncFIN040_tendsto (m r : ℝ) :
    Tendsto (fun n : ℕ => truncFIN040 m n r) atTop (𝓝 (r - m)) := by
  have hd : HasDerivAt (fun e : ℝ => Real.arctan (e * (r - m))) (r - m) 0 := by
    have h1 : HasDerivAt (fun e : ℝ => e * (r - m)) (r - m) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const (r - m)
    have := (Real.hasDerivAt_arctan (0 * (r - m))).comp 0 h1
    simpa [Function.comp_def] using this
  have hs := hasDerivAt_iff_tendsto_slope_zero.mp hd
  have hn : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall fun n => by simp only [mem_compl_iff, mem_singleton_iff]; positivity
  have := hs.comp hn
  refine this.congr (fun n => ?_)
  have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  simp only [Function.comp, zero_add, zero_mul, Real.arctan_zero, sub_zero, smul_eq_mul, truncFIN040]
  rw [one_div, inv_inv]
  congr 2
  field_simp

/-- Sub-Gaussian mgf bound for the centered radius (Herbst plus Fatou). -/
theorem subgaussian_centered_FIN040 {σ : Measure ℝ} [IsProbabilityMeasure σ] {L : ℝ} (hL : 0 < L)
    (hlsi : RadialLSIFIN040 σ L) {m : ℝ} (hm1 : Integrable (fun r : ℝ => r - m) σ)
    (hm0 : ∫ r, (r - m) ∂σ = 0) (t : ℝ) :
    ∫⁻ r, ENNReal.ofReal (Real.exp (t * (r - m))) ∂σ ≤ ENNReal.ofReal (Real.exp (L * t ^ 2 / 4)) := by
  have hcont : ∀ n, Continuous (truncFIN040 m n) := fun n => (truncFIN040_contDiff m n).continuous
  have hmeas : ∀ n, Measurable fun r => ENNReal.ofReal (Real.exp (t * truncFIN040 m n r)) :=
    fun n => Measurable.ennreal_ofReal
      (by have := hcont n; fun_prop : Continuous fun r => Real.exp (t * truncFIN040 m n r)).measurable
  have hptw : ∀ r, Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (t * truncFIN040 m n r))) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (t * (r - m))))) := fun r =>
    (ENNReal.tendsto_ofReal ((Real.continuous_exp.tendsto _).comp
      ((truncFIN040_tendsto m r).const_mul t)))
  have hfatou := lintegral_liminf_le (μ := σ) (u := (atTop : Filter ℕ)) hmeas
  have hlim : ∀ r, liminf (fun n : ℕ => ENNReal.ofReal (Real.exp (t * truncFIN040 m n r))) (atTop : Filter ℕ)
      = ENNReal.ofReal (Real.exp (t * (r - m))) := fun r => (hptw r).liminf_eq
  simp_rw [hlim] at hfatou
  refine hfatou.trans ?_
  -- bound each term
  have hint_t : Tendsto (fun n : ℕ => ∫ r, truncFIN040 m n r ∂σ) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := σ) (F := fun n r => truncFIN040 m n r)
      (f := fun r => r - m) (bound := fun r => |r - m|)
      (fun n => (hcont n).aestronglyMeasurable) hm1.abs
      (fun n => Filter.Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs]; exact truncFIN040_abs_le m n r)
      (Filter.Eventually.of_forall fun r => truncFIN040_tendsto m r)
    rwa [hm0] at this
  have hrhs : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (t * ∫ r, truncFIN040 m n r ∂σ + L * t ^ 2 / 4)))
      atTop (𝓝 (ENNReal.ofReal (Real.exp (L * t ^ 2 / 4)))) := by
    refine ENNReal.tendsto_ofReal ((Real.continuous_exp.tendsto _).comp ?_)
    have := (hint_t.const_mul t).add_const (L * t ^ 2 / 4)
    simpa using this
  rw [← hrhs.liminf_eq]
  refine liminf_le_liminf (Filter.Eventually.of_forall fun n => ?_)
  have hbd := truncFIN040_bound m n
  have hint : Integrable (fun r => Real.exp (t * truncFIN040 m n r)) σ := by
    refine Integrable.of_bound (by have := hcont n; fun_prop : Continuous fun r => Real.exp (t * truncFIN040 m n r)).aestronglyMeasurable
      (Real.exp (|t| * (((n : ℝ) + 1) * (π / 2)))) (Filter.Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc t * truncFIN040 m n r ≤ |t * truncFIN040 m n r| := le_abs_self _
      _ = |t| * |truncFIN040 m n r| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbd r) (abs_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun r => (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal (herbst_signed_FIN040 (σ := σ) hL hlsi (truncFIN040_contDiff m n) hbd
    (truncFIN040_deriv m n) t)

theorem integral_exp_mul_gaussian_FIN040 (u : ℝ) :
    ∫ g, Real.exp (u * g) ∂gaussianReal 0 1 = Real.exp (u ^ 2 / 2) := by
  have := mgf_gaussianReal (μ := 0) (v := 1) (X := id) (p := gaussianReal 0 1)
    ⟨aemeasurable_id, by simp⟩ u
  simpa [mgf] using this

theorem gaussian_exp_quarter_FIN040 :
    ∫⁻ g, ENNReal.ofReal (Real.exp (g ^ 2 / 4)) ∂gaussianReal 0 1 = ENNReal.ofReal (√2) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1)
      (by fun_prop : Measurable fun g : ℝ => ENNReal.ofReal (Real.exp (g ^ 2 / 4)))]
  have e : ∀ g : ℝ, (gaussianPDF 0 1 * fun g => ENNReal.ofReal (Real.exp (g ^ 2 / 4))) g =
      ENNReal.ofReal ((√(2 * π))⁻¹ * Real.exp (-(1 / 4) * g ^ 2)) := fun g => by
    simp only [Pi.mul_apply, gaussianPDF, gaussianPDFReal]
    rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add]
    congr 3
    show -(g - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ)) + g ^ 2 / 4 = -(1 / 4) * g ^ 2
    rw [NNReal.coe_one]; ring
    rw [NNReal.coe_one, mul_one]
  simp_rw [e]
  have hint : Integrable (fun g : ℝ => (√(2 * π))⁻¹ * Real.exp (-(1 / 4) * g ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun g => by positivity), integral_const_mul, integral_gaussian]
  congr 1
  have h2 : √(π / (1 / 4)) = 2 * √π := by
    rw [show π / (1 / 4) = 2 ^ 2 * π by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  rw [h2, Real.sqrt_mul (by norm_num)]
  have hpi : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have h22 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2p : 0 < √2 := by positivity
  field_simp
  nlinarith

/-- Square-exponential moment of the centered radius from the sub-Gaussian mgf bound. -/
theorem exp_sq_moment_FIN040 {σ : Measure ℝ} [IsProbabilityMeasure σ] {L : ℝ} (hL : 0 < L) {m : ℝ}
    (hsub : ∀ t : ℝ, ∫⁻ r, ENNReal.ofReal (Real.exp (t * (r - m))) ∂σ
      ≤ ENNReal.ofReal (Real.exp (L * t ^ 2 / 4))) :
    ∫⁻ r, ENNReal.ofReal (Real.exp ((r - m) ^ 2 / (2 * L))) ∂σ ≤ ENNReal.ofReal (√2) := by
  set γ := gaussianReal 0 1 with _hγ
  set u : ℝ := √(1 / L) with hu
  have hu2 : u ^ 2 = 1 / L := Real.sq_sqrt (by positivity)
  have h1 : ∀ r, ENNReal.ofReal (Real.exp ((r - m) ^ 2 / (2 * L))) =
      ∫⁻ g, ENNReal.ofReal (Real.exp (u * (r - m) * g)) ∂γ := fun r => by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal _)
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le), integral_exp_mul_gaussian_FIN040]
    congr 2
    rw [mul_pow, hu2]; field_simp
  simp_rw [h1]
  rw [lintegral_lintegral_swap (by
    exact (Measurable.ennreal_ofReal (Real.measurable_exp.comp
      (((measurable_const.mul (measurable_fst.sub_const m)).mul measurable_snd)))).aemeasurable)]
  calc ∫⁻ g, ∫⁻ r, ENNReal.ofReal (Real.exp (u * (r - m) * g)) ∂σ ∂γ
      ≤ ∫⁻ g, ENNReal.ofReal (Real.exp (g ^ 2 / 4)) ∂γ := by
        refine lintegral_mono fun g => ?_
        have := hsub (u * g)
        have e1 : ∀ r, u * (r - m) * g = u * g * (r - m) := fun r => by ring
        simp_rw [e1]
        refine this.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (le_of_eq ?_)))
        rw [mul_pow, hu2]; field_simp
    _ = ENNReal.ofReal (√2) := gaussian_exp_quarter_FIN040

/-- Entropy is transported by measurable maps. -/
theorem homogeneousEntropy_map_FIN040 {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {T : α → β} (hT : Measurable T) {g : β → ℝ} (hg : Measurable g) :
    homogeneousEntropy (μ.map T) g = homogeneousEntropy μ (fun x => g (T x)) := by
  have hi : ∫ y, g y ∂(μ.map T) = ∫ x, g (T x) ∂μ := integral_map hT.aemeasurable hg.aestronglyMeasurable
  unfold homogeneousEntropy
  rw [hi]
  split_ifs with h
  · rfl
  · have hm : Measurable fun y => ENNReal.ofReal (entropyIntegrand (∫ x, g (T x) ∂μ) (g y)) := by
      simp only [entropyIntegrand]; fun_prop
    exact lintegral_map hm hT

/-- A bound for `x log x` on `[0, C]`. -/
theorem mul_log_bound_FIN040 (C : ℝ) :
    ∃ K : ℝ, ∀ x : ℝ, 0 ≤ x → x ≤ C → |x * Real.log x| ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0:ℝ)) (b := C)).exists_bound_of_continuousOn
    (Real.continuous_mul_log.continuousOn (s := Icc 0 C))
  exact ⟨K, fun x h0 h1 => by simpa using hK x ⟨h0, h1⟩⟩


theorem entropy_fubini_FIN040 {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {σ : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure σ]
    {w : α × β → ℝ} (hw : Measurable w) (hw0 : ∀ p, 0 ≤ w p) {C : ℝ} (hwC : ∀ p, w p ≤ C) :
    ∫ p, w p * Real.log (w p) ∂(μ.prod σ)
        - (∫ p, w p ∂(μ.prod σ)) * Real.log (∫ p, w p ∂(μ.prod σ))
      = (∫ θ, (∫ r, w (θ, r) * Real.log (w (θ, r)) ∂σ
            - (∫ r, w (θ, r) ∂σ) * Real.log (∫ r, w (θ, r) ∂σ)) ∂μ)
        + (∫ θ, (∫ r, w (θ, r) ∂σ) * Real.log (∫ r, w (θ, r) ∂σ) ∂μ
          - (∫ θ, ∫ r, w (θ, r) ∂σ ∂μ) * Real.log (∫ θ, ∫ r, w (θ, r) ∂σ ∂μ)) := by
  obtain ⟨K, hK⟩ := mul_log_bound_FIN040 C
  have hΦ : Measurable fun x : ℝ => x * Real.log x := by fun_prop
  have hint1 : Integrable (fun p => w p * Real.log (w p)) (μ.prod σ) :=
    Integrable.of_bound (hΦ.comp hw).aestronglyMeasurable K
      (Eventually.of_forall fun p => by simpa using hK _ (hw0 p) (hwC p))
  have hint2 : Integrable w (μ.prod σ) :=
    Integrable.of_bound hw.aestronglyMeasurable |C|
      (Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hw0 p)]; exact (hwC p).trans (le_abs_self C))
  have hX := hint1.integral_prod_left
  have ha := hint2.integral_prod_left
  have haC : ∀ θ, ∫ r, w (θ, r) ∂σ ≤ C := fun θ => by
    have hwi : Integrable (fun r => w (θ, r)) σ :=
      Integrable.of_bound (hw.comp measurable_prodMk_left).aestronglyMeasurable |C|
        (Eventually.of_forall fun r => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hw0 _)]; exact (hwC _).trans (le_abs_self C))
    calc ∫ r, w (θ, r) ∂σ ≤ ∫ _r, C ∂σ := integral_mono hwi (integrable_const _) fun r => hwC _
      _ = C := by simp
  have hΦa : Integrable (fun θ => (∫ r, w (θ, r) ∂σ) * Real.log (∫ r, w (θ, r) ∂σ)) μ :=
    Integrable.of_bound (hΦ.comp_aemeasurable ha.1.aemeasurable).aestronglyMeasurable K
      (Eventually.of_forall fun θ => by
        simpa using hK _ (integral_nonneg fun r => hw0 _) (haC θ))
  rw [integral_prod _ hint1, integral_prod _ hint2, integral_sub hX hΦa]
  ring


theorem slice_entropy_le_FIN040 {σ : Measure ℝ} [IsProbabilityMeasure σ] {L : ℝ} (hL : 0 ≤ L)
    (hlsi : RadialLSIFIN040 σ L) {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) {B D : ℝ}
    (hB : ∀ r, |u r| ≤ B) (hD : ∀ r, |deriv u r| ≤ D) :
    ∫ r, u r ^ 2 * Real.log (u r ^ 2) ∂σ - (∫ r, u r ^ 2 ∂σ) * Real.log (∫ r, u r ^ 2 ∂σ)
      ≤ L * ∫ r, deriv u r ^ 2 ∂σ := by
  have hc : Continuous u := hu.continuous
  have hdc : Continuous (deriv u) := hu.continuous_deriv (by simp)
  have hi : Integrable (fun r => u r ^ 2) σ :=
    Integrable.of_bound (hc.pow 2).aestronglyMeasurable (B ^ 2)
      (Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB r) 2)
  have hdi : Integrable (fun r => deriv u r ^ 2) σ :=
    Integrable.of_bound (hdc.pow 2).aestronglyMeasurable (D ^ 2)
      (Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hD r) 2)
  obtain ⟨K, hK⟩ := mul_log_bound_FIN040 (B ^ 2)
  have hlog : Integrable (fun r => u r ^ 2 * Real.log (u r ^ 2)) σ :=
    Integrable.of_bound ((Real.continuous_mul_log.comp (hc.pow 2)).aestronglyMeasurable) K
      (Eventually.of_forall fun r => by
        simpa using hK _ (sq_nonneg _) (by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB r) 2))
  have hent := hlsi u hu hi hdi
  rw [homogeneousEntropy_eq_formula (Eventually.of_forall fun r => sq_nonneg _) hi hlog] at hent
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hL (integral_nonneg fun r => sq_nonneg _))).1 hent


theorem slice_weighted_FIN040 {σ : Measure ℝ} [IsProbabilityMeasure σ] {L t M : ℝ} (hL : 0 ≤ L)
    (ht : 0 < t) (hlsi : RadialLSIFIN040 σ L)
    (hMi : Integrable (fun r : ℝ => Real.exp (t * r ^ 2)) σ)
    (hM : ∫ r, Real.exp (t * r ^ 2) ∂σ = M) {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) {B D : ℝ}
    (hB : ∀ r, |u r| ≤ B) (hD : ∀ r, |deriv u r| ≤ D) :
    Integrable (fun r => r ^ 2 * u r ^ 2) σ ∧
      t * ∫ r, r ^ 2 * u r ^ 2 ∂σ
        ≤ L * ∫ r, deriv u r ^ 2 ∂σ + (∫ r, u r ^ 2 ∂σ) * Real.log M := by
  have hc : Continuous u := hu.continuous
  have hdc : Continuous (deriv u) := hu.continuous_deriv (by simp)
  have hi : Integrable (fun r => u r ^ 2) σ :=
    Integrable.of_bound (hc.pow 2).aestronglyMeasurable (B ^ 2)
      (Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB r) 2)
  have hdi : Integrable (fun r => deriv u r ^ 2) σ :=
    Integrable.of_bound (hdc.pow 2).aestronglyMeasurable (D ^ 2)
      (Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hD r) 2)
  have hent := hlsi u hu hi hdi
  have hne : homogeneousEntropy σ (fun r => u r ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hent
  obtain ⟨hI, hg⟩ := gibbs_weighted_moment (h := fun r => u r ^ 2) ht hMi hM (hc.pow 2).measurable
    (fun r => sq_nonneg _) hi hne
  have hent' : (homogeneousEntropy σ (fun r => u r ^ 2)).toReal ≤ L * ∫ r, deriv u r ^ 2 ∂σ :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hent).trans
      (ENNReal.toReal_ofReal (mul_nonneg hL (integral_nonneg fun r => sq_nonneg _))).le
  have e1 : ∫ r, t * r ^ 2 * u r ^ 2 ∂σ = t * ∫ r, r ^ 2 * u r ^ 2 ∂σ := by
    rw [← integral_const_mul]; congr 1; ext r; ring
  refine ⟨?_, by rw [e1] at hg; linarith⟩
  have := hI.const_mul t⁻¹
  refine this.congr (Eventually.of_forall fun r => ?_)
  simp only
  field_simp


theorem continuous_hpolar_FIN040 {H : ℝ × ℝ → ℝ} (hH : ContDiff ℝ ∞ H) :
    Continuous fun p : ℝ × ℝ => H (polar p) := hH.continuous.comp continuous_polar

theorem hasDerivAt_slice_integral_FIN040 {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hr : Integrable (fun r : ℝ => r) σ) {H : ℝ × ℝ → ℝ} (hH : ContDiff ℝ ∞ H) {B K : ℝ}
    (hB : ∀ x, |H x| ≤ B) (hK : ∀ p, |tanDer H p| ≤ K) (θ0 : ℝ) :
    HasDerivAt (fun θ => ∫ r, H (polar (θ, r)) ^ 2 ∂σ)
      (∫ r, 2 * H (polar (θ0, r)) * (r * tanDer H (θ0, r)) ∂σ) θ0 := by
  have hc := continuous_hpolar_FIN040 hH
  have hτ := continuous_tanDer hH
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hmeas : ∀ θ, AEStronglyMeasurable (fun r => H (polar (θ, r)) ^ 2) σ := fun θ =>
    ((hc.comp (Continuous.prodMk_right θ)).pow 2).aestronglyMeasurable
  have hderiv : ∀ θ r, HasDerivAt (fun t => H (polar (t, r)) ^ 2)
      (2 * H (polar (θ, r)) * (r * tanDer H (θ, r))) θ := fun θ r => by
    have := (hasDerivAt_tangential hH θ r).pow 2
    convert this using 1
    simp
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := σ)
    (F := fun θ r => H (polar (θ, r)) ^ 2)
    (F' := fun θ r => 2 * H (polar (θ, r)) * (r * tanDer H (θ, r))) (x₀ := θ0)
    (bound := fun r => 2 * B * K * |r|) (s := Metric.ball θ0 1) (Metric.ball_mem_nhds θ0 one_pos)
    (Eventually.of_forall hmeas)
    (Integrable.of_bound (hmeas θ0) (B ^ 2) (Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2))
    (by
      refine ((hc.comp (Continuous.prodMk_right θ0)).const_mul 2).mul ?_ |>.aestronglyMeasurable
      exact (continuous_id.mul (hτ.comp (Continuous.prodMk_right θ0))))
    (Eventually.of_forall fun r θ _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      have h1 := hB (polar (θ, r))
      have h2 := hK (θ, r)
      have h3 : |(2 : ℝ)| = 2 := abs_of_pos two_pos
      rw [h3]
      have : 2 * |H (polar (θ, r))| * (|r| * |tanDer H (θ, r)|) ≤ 2 * B * (|r| * K) := by
        gcongr
      calc _ ≤ 2 * B * (|r| * K) := this
        _ = _ := by ring)
    ((hr.abs.const_mul (2 * B * K)))
    (Eventually.of_forall fun r θ _ => hderiv θ r)
  exact this.2


theorem angleLaw_map_coe_FIN040 :
    angleLaw.map ((↑) : ℝ → AddCircle (2 * π)) = AddCircle.haarAddCircle (T := 2 * π) := by
  have h := AddCircle.measurePreserving_mk (2 * π) 0
  rw [zero_add] at h
  have h2 : (volume.restrict (Ioc 0 (2 * π))).map ((↑) : ℝ → AddCircle (2 * π)) = volume :=
    h.map_eq
  rw [angleLaw, Measure.map_smul, h2, AddCircle.volume_eq_smul_haarAddCircle,
    smul_smul, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ Real.two_pi_pos.ne',
    ENNReal.ofReal_one, one_smul]
  exact h.measurable.aemeasurable

theorem circle_entropy_FIN040 {A A' : ℝ → ℝ} (hA : ∀ θ, HasDerivAt A (A' θ) θ)
    (hA'c : Continuous A') (hper : Function.Periodic A (2 * π))
    (hper' : Function.Periodic A' (2 * π)) (hA0 : ∀ θ, 0 ≤ A θ) {D : ℝ}
    (hD : ∀ θ, |A' θ| ≤ D) :
    ∫ θ, A θ * Real.log (A θ) ∂angleLaw - (∫ θ, A θ ∂angleLaw) * Real.log (∫ θ, A θ ∂angleLaw)
      ≤ ∫ θ in (0:ℝ)..(2 * π), |A' θ| := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun x => (hA x).continuousAt
  set g : AddCircle (2 * π) → ℝ := hper.lift with hg
  set g' : AddCircle (2 * π) → ℝ := hper'.lift with hg'
  have hgc : ∀ t : ℝ, g (t : AddCircle (2 * π)) = A t := fun t => hper.lift_coe t
  have hgc' : ∀ t : ℝ, g' (t : AddCircle (2 * π)) = A' t := fun t => hper'.lift_coe t
  have hq : Topology.IsQuotientMap (QuotientAddGroup.mk' (AddSubgroup.zmultiples (2 * π))) :=
    QuotientAddGroup.isQuotientMap_mk _
  have hgcont : Continuous g := hq.continuous_iff.2 (by
    have : (g ∘ QuotientAddGroup.mk' (AddSubgroup.zmultiples (2 * π))) = A := funext hgc
    rw [this]; exact hAc)
  have hg'cont : Continuous g' := hq.continuous_iff.2 (by
    have : (g' ∘ QuotientAddGroup.mk' (AddSubgroup.zmultiples (2 * π))) = A' := funext hgc'
    rw [this]; exact hA'c)
  have hg0 : ∀ x, 0 ≤ g x := fun x => by
    induction x using QuotientAddGroup.induction_on with
    | H t => exact (hgc t).symm ▸ hA0 t
  have hfun : (fun t : ℝ => g (t : AddCircle (2 * π))) = A := funext hgc
  have hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun t : ℝ => g (t : AddCircle (2 * π))) a b := by
    intro a b
    rw [hfun]
    have hL : LipschitzWith (Real.toNNReal D) A := by
      refine lipschitzWith_of_nnnorm_deriv_le (fun x => (hA x).differentiableAt) fun x => ?_
      rw [(hA x).deriv]
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ hD0]
      exact hD x
    exact (hL.lipschitzOnWith).absolutelyContinuousOnInterval
  have hd : ∀ᵐ x : ℝ, deriv (fun t : ℝ => g (t : AddCircle (2 * π))) x = g' (x : AddCircle (2 * π)) :=
    Eventually.of_forall fun x => by rw [hfun, (hA x).deriv, hgc']
  have h41 := optional_circle_l1_entropy_bound hg0 hac hd
  have hm : Measurable ((↑) : ℝ → AddCircle (2 * π)) := (AddCircle.measurePreserving_mk (2 * π) 0).measurable
  have hbridge : homogeneousEntropy angleLaw A
      = homogeneousEntropy (AddCircle.haarAddCircle (T := 2 * π)) g := by
    rw [← angleLaw_map_coe_FIN040, homogeneousEntropy_map_FIN040 hm hgcont.measurable]
    congr 1
  have hint : ∫ x, |g' x| ∂(AddCircle.haarAddCircle (T := 2 * π)) = (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), |A' θ| := by
    rw [← angleLaw_map_coe_FIN040, integral_map hm.aemeasurable (hg'cont.abs.aestronglyMeasurable),
      ← integral_angleLaw]
    congr 1
  have hAi : Integrable A angleLaw := integrable_angleLaw_of_continuous hAc
  have hAli : Integrable (fun θ => A θ * Real.log (A θ)) angleLaw :=
    integrable_angleLaw_of_continuous (Real.continuous_mul_log.comp hAc)
  have hform := homogeneousEntropy_eq_formula (P := angleLaw) (Eventually.of_forall hA0) hAi hAli
  rw [← hbridge, hform, hint, ← mul_assoc, mul_inv_cancel₀ Real.two_pi_pos.ne', one_mul] at h41
  exact (ENNReal.ofReal_le_ofReal_iff (intervalIntegral.integral_nonneg Real.two_pi_pos.le
    fun _ _ => abs_nonneg _)).1 h41

theorem polar_add_two_pi_FIN040 (θ r : ℝ) : polar (θ + 2 * π, r) = polar (θ, r) := by
  simp [polar, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem tanDer_add_two_pi_FIN040 (H : ℝ × ℝ → ℝ) (θ r : ℝ) :
    tanDer H (θ + 2 * π, r) = tanDer H (θ, r) := by
  simp [tanDer, polar_add_two_pi_FIN040, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The angular entropy term is at most `4π J`, where `J` is the `ρ`-integral of `|H r ∂_θ H|`. -/
theorem circle_term_FIN040 {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hr : Integrable (fun r : ℝ => r) σ) {H : ℝ × ℝ → ℝ} (hH : ContDiff ℝ ∞ H) {B K : ℝ}
    (hB : ∀ x, |H x| ≤ B) (hK : ∀ p, |tanDer H p| ≤ K) :
    ∫ θ, (∫ r, H (polar (θ, r)) ^ 2 ∂σ) * Real.log (∫ r, H (polar (θ, r)) ^ 2 ∂σ) ∂angleLaw
      - (∫ θ, ∫ r, H (polar (θ, r)) ^ 2 ∂σ ∂angleLaw) *
        Real.log (∫ θ, ∫ r, H (polar (θ, r)) ^ 2 ∂σ ∂angleLaw)
      ≤ 4 * π * ∫ p, |H (polar p) * (p.2 * tanDer H p)| ∂(angleLaw.prod σ) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK (0, 0))
  have hc := continuous_hpolar_FIN040 hH
  have hτ := continuous_tanDer hH
  set A : ℝ → ℝ := fun θ => ∫ r, H (polar (θ, r)) ^ 2 ∂σ with hAdef
  set A' : ℝ → ℝ := fun θ => ∫ r, 2 * H (polar (θ, r)) * (r * tanDer H (θ, r)) ∂σ with hA'def
  have hbd : ∀ θ r, |2 * H (polar (θ, r)) * (r * tanDer H (θ, r))| ≤ 2 * B * K * |r| := fun θ r => by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (two_pos : (0:ℝ) < 2)]
    have h1 := hB (polar (θ, r))
    have h2 := hK (θ, r)
    calc 2 * |H (polar (θ, r))| * (|r| * |tanDer H (θ, r)|) ≤ 2 * B * (|r| * K) := by gcongr
      _ = _ := by ring
  have hmeasA' : ∀ θ, AEStronglyMeasurable (fun r => 2 * H (polar (θ, r)) * (r * tanDer H (θ, r))) σ :=
    fun θ => (((hc.comp (Continuous.prodMk_right θ)).const_mul 2).mul
      (continuous_id.mul (hτ.comp (Continuous.prodMk_right θ)))).aestronglyMeasurable
  have hA : ∀ θ, HasDerivAt A (A' θ) θ := fun θ => hasDerivAt_slice_integral_FIN040 hr hH hB hK θ
  have hA'c : Continuous A' := by
    refine continuous_of_dominated (bound := fun r => 2 * B * K * |r|) (fun θ => hmeasA' θ)
      (fun θ => Eventually.of_forall fun r => by rw [Real.norm_eq_abs]; exact hbd θ r)
      (hr.abs.const_mul _) (Eventually.of_forall fun r => ?_)
    exact ((hc.comp (Continuous.prodMk_left r)).const_mul 2).mul
      (continuous_const.mul (hτ.comp (Continuous.prodMk_left r)))
  have hper : Function.Periodic A (2 * π) := fun θ => by
    simp only [hAdef, polar_add_two_pi_FIN040]
  have hper' : Function.Periodic A' (2 * π) := fun θ => by
    simp only [hA'def, polar_add_two_pi_FIN040, tanDer_add_two_pi_FIN040]
  have hA0 : ∀ θ, 0 ≤ A θ := fun θ => integral_nonneg fun r => sq_nonneg _
  have hD : ∀ θ, |A' θ| ≤ 2 * B * K * ∫ r, |r| ∂σ := fun θ => by
    calc |A' θ| ≤ ∫ r, |2 * H (polar (θ, r)) * (r * tanDer H (θ, r))| ∂σ := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (fun r => 2 * H (polar (θ, r)) * (r * tanDer H (θ, r)))
      _ ≤ ∫ r, 2 * B * K * |r| ∂σ := integral_mono_of_nonneg
          (Eventually.of_forall fun r => abs_nonneg _) (hr.abs.const_mul _)
          (Eventually.of_forall fun r => hbd θ r)
      _ = _ := by rw [integral_const_mul]
  have key := circle_entropy_FIN040 hA hA'c hper hper' hA0 hD
  refine key.trans ?_
  have hJi : Integrable (fun p : ℝ × ℝ => |H (polar p) * (p.2 * tanDer H p)|) (angleLaw.prod σ) := by
    refine ((hr.abs.comp_snd angleLaw).const_mul (B * K)).mono'
      ((hc.mul (continuous_snd.mul hτ)).abs.aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_abs, abs_mul, abs_mul]
    have h1 := hB (polar p)
    have h2 := hK p
    calc |H (polar p)| * (|p.2| * |tanDer H p|) ≤ B * (|p.2| * K) := by gcongr
      _ = _ := by ring
  have hjint := hJi.integral_prod_left
  have hA'abs : Integrable (fun θ => |A' θ|) angleLaw :=
    (integrable_angleLaw_of_continuous hA'c.abs)
  have hle : ∀ θ, |A' θ| ≤ 2 * ∫ r, |H (polar (θ, r)) * (r * tanDer H (θ, r))| ∂σ := fun θ => by
    calc |A' θ| ≤ ∫ r, |2 * H (polar (θ, r)) * (r * tanDer H (θ, r))| ∂σ := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (fun r => 2 * H (polar (θ, r)) * (r * tanDer H (θ, r)))
      _ = 2 * ∫ r, |H (polar (θ, r)) * (r * tanDer H (θ, r))| ∂σ := by
          rw [← integral_const_mul]
          congr 1; ext r
          rw [mul_assoc, abs_mul, abs_of_pos (two_pos : (0:ℝ) < 2)]
  have h1 : ∫ θ, |A' θ| ∂angleLaw ≤ 2 * ∫ p, |H (polar p) * (p.2 * tanDer H p)| ∂(angleLaw.prod σ) := by
    rw [integral_prod _ hJi, ← integral_const_mul]
    exact integral_mono hA'abs (hjint.const_mul 2) hle
  have h2 := integral_angleLaw (fun θ => |A' θ|)
  have h3 : ∫ θ in (0:ℝ)..(2 * π), |A' θ| = 2 * π * ∫ θ, |A' θ| ∂angleLaw := by
    rw [h2, ← mul_assoc, mul_inv_cancel₀ Real.two_pi_pos.ne', one_mul]
  rw [h3]
  nlinarith [Real.pi_pos]

theorem core1_FIN040 {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hr : Integrable (fun r : ℝ => r) σ) {L : ℝ} (hL : 0 ≤ L) (hlsi : RadialLSIFIN040 σ L)
    {H : ℝ × ℝ → ℝ} (hH : ContDiff ℝ ∞ H) {B K1 K2 : ℝ} (hB : ∀ x, |H x| ≤ B)
    (hrad : ∀ p, |radDer H p| ≤ K1) (htan : ∀ p, |tanDer H p| ≤ K2) :
    ∫ p, H (polar p) ^ 2 * Real.log (H (polar p) ^ 2) ∂(angleLaw.prod σ)
        - (∫ p, H (polar p) ^ 2 ∂(angleLaw.prod σ)) *
          Real.log (∫ p, H (polar p) ^ 2 ∂(angleLaw.prod σ))
      ≤ L * ∫ p, radDer H p ^ 2 ∂(angleLaw.prod σ)
        + 4 * π * ∫ p, |H (polar p) * (p.2 * tanDer H p)| ∂(angleLaw.prod σ) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hK10 : 0 ≤ K1 := (abs_nonneg _).trans (hrad (0, 0))
  have hc := continuous_hpolar_FIN040 hH
  have hρc := continuous_radDer hH
  have hF := entropy_fubini_FIN040 (μ := angleLaw) (σ := σ) (w := fun p : ℝ × ℝ => H (polar p) ^ 2)
    (hc.pow 2).measurable (fun p => sq_nonneg _) (C := B ^ 2) (fun p => by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2)
  beta_reduce at hF
  rw [hF]
  have hslice : ∀ θ, ∫ r, H (polar (θ, r)) ^ 2 * Real.log (H (polar (θ, r)) ^ 2) ∂σ
        - (∫ r, H (polar (θ, r)) ^ 2 ∂σ) * Real.log (∫ r, H (polar (θ, r)) ^ 2 ∂σ)
      ≤ L * ∫ r, radDer H (θ, r) ^ 2 ∂σ := by
    intro θ
    have hu : ContDiff ℝ ∞ (fun r => H (polar (θ, r))) :=
      hH.comp (contDiff_polar.comp (contDiff_const.prodMk contDiff_id))
    have hder : ∀ r, deriv (fun r => H (polar (θ, r))) r = radDer H (θ, r) := fun r =>
      (hasDerivAt_radial hH θ r).deriv
    have := slice_entropy_le_FIN040 hL hlsi hu (B := B) (D := K1) (fun r => hB _)
      (fun r => by rw [hder]; exact hrad _)
    simpa only [hder] using this
  have hradi : Integrable (fun p : ℝ × ℝ => radDer H p ^ 2) (angleLaw.prod σ) :=
    Integrable.of_bound (hρc.pow 2).aestronglyMeasurable (K1 ^ 2) (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hrad p) 2)
  have hT1 : ∫ θ, (∫ r, H (polar (θ, r)) ^ 2 * Real.log (H (polar (θ, r)) ^ 2) ∂σ
        - (∫ r, H (polar (θ, r)) ^ 2 ∂σ) * Real.log (∫ r, H (polar (θ, r)) ^ 2 ∂σ)) ∂angleLaw
      ≤ L * ∫ p, radDer H p ^ 2 ∂(angleLaw.prod σ) := by
    rw [integral_prod _ hradi, ← integral_const_mul]
    by_cases hi : Integrable (fun θ => ∫ r, H (polar (θ, r)) ^ 2 * Real.log (H (polar (θ, r)) ^ 2) ∂σ
        - (∫ r, H (polar (θ, r)) ^ 2 ∂σ) * Real.log (∫ r, H (polar (θ, r)) ^ 2 ∂σ)) angleLaw
    · exact integral_mono hi (hradi.integral_prod_left.const_mul L) hslice
    · rw [integral_undef hi]
      exact integral_nonneg fun θ => mul_nonneg hL (integral_nonneg fun r => sq_nonneg _)
  have hT2 := circle_term_FIN040 hr hH hB htan
  linarith

theorem core2_FIN040 {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hr2 : Integrable (fun r : ℝ => r ^ 2) σ) {L t M : ℝ} (hL : 0 ≤ L) (ht : 0 < t)
    (hlsi : RadialLSIFIN040 σ L)
    (hMi : Integrable (fun r : ℝ => Real.exp (t * r ^ 2)) σ)
    (hM : ∫ r, Real.exp (t * r ^ 2) ∂σ = M)
    {H : ℝ × ℝ → ℝ} (hH : ContDiff ℝ ∞ H) {B K1 : ℝ} (hB : ∀ x, |H x| ≤ B)
    (hrad : ∀ p, |radDer H p| ≤ K1) :
    t * ∫ p, p.2 ^ 2 * H (polar p) ^ 2 ∂(angleLaw.prod σ)
      ≤ L * ∫ p, radDer H p ^ 2 ∂(angleLaw.prod σ)
        + (∫ p, H (polar p) ^ 2 ∂(angleLaw.prod σ)) * Real.log M := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hc := continuous_hpolar_FIN040 hH
  have hρc := continuous_radDer hH
  have hradi : Integrable (fun p : ℝ × ℝ => radDer H p ^ 2) (angleLaw.prod σ) :=
    Integrable.of_bound (hρc.pow 2).aestronglyMeasurable (K1 ^ 2) (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hrad p) 2)
  have hwi : Integrable (fun p : ℝ × ℝ => H (polar p) ^ 2) (angleLaw.prod σ) :=
    Integrable.of_bound (hc.pow 2).aestronglyMeasurable (B ^ 2) (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2)
  have hQi : Integrable (fun p : ℝ × ℝ => p.2 ^ 2 * H (polar p) ^ 2) (angleLaw.prod σ) := by
    refine ((hr2.comp_snd angleLaw).const_mul (B ^ 2)).mono'
      ((continuous_snd.pow 2).mul (hc.pow 2)).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    have : H (polar p) ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2
    calc p.2 ^ 2 * H (polar p) ^ 2 ≤ p.2 ^ 2 * B ^ 2 := by gcongr
      _ = _ := by ring
  have hslice : ∀ θ, t * ∫ r, r ^ 2 * H (polar (θ, r)) ^ 2 ∂σ
      ≤ L * ∫ r, radDer H (θ, r) ^ 2 ∂σ + (∫ r, H (polar (θ, r)) ^ 2 ∂σ) * Real.log M := by
    intro θ
    have hu : ContDiff ℝ ∞ (fun r => H (polar (θ, r))) :=
      hH.comp (contDiff_polar.comp (contDiff_const.prodMk contDiff_id))
    have hder : ∀ r, deriv (fun r => H (polar (θ, r))) r = radDer H (θ, r) := fun r =>
      (hasDerivAt_radial hH θ r).deriv
    have := (slice_weighted_FIN040 hL ht hlsi hMi hM hu (B := B) (D := K1) (fun r => hB _)
      (fun r => by rw [hder]; exact hrad _)).2
    simpa only [hder] using this
  rw [integral_prod _ hQi, integral_prod _ hradi, integral_prod _ hwi, ← integral_const_mul,
    ← integral_const_mul, ← integral_mul_const, ← integral_add]
  · exact integral_mono (hQi.integral_prod_left.const_mul t)
      ((hradi.integral_prod_left.const_mul L).add (hwi.integral_prod_left.mul_const _)) hslice
  · exact hradi.integral_prod_left.const_mul L
  · exact hwi.integral_prod_left.mul_const _

theorem integrable_id_of_sq_FIN040 {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hr2 : Integrable (fun r : ℝ => r ^ 2) σ) : Integrable (fun r : ℝ => r) σ := by
  refine ((integrable_const (1:ℝ)).add hr2).mono' measurable_id.aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [sq_nonneg (|r| - 1), sq_abs r, abs_nonneg r]

theorem exp_moment_FIN040 {σ : Measure ℝ} [IsProbabilityMeasure σ] {L : ℝ} (hL : 0 < L)
    (hlsi : RadialLSIFIN040 σ L) (hr2 : Integrable (fun r : ℝ => r ^ 2) σ) :
    Integrable (fun r : ℝ => Real.exp (1 / (4 * L) * r ^ 2)) σ ∧
    ∃ M : ℝ, ∫ r, Real.exp (1 / (4 * L) * r ^ 2) ∂σ = M ∧ 0 < M ∧
      Real.log M ≤ Real.log 2 / 2 + (∫ r, r ∂σ) ^ 2 / (2 * L) ∧
      ∫ r, r ^ 2 ∂σ ≤ L + (∫ r, r ∂σ) ^ 2 ∧ (∫ r, r ∂σ) ^ 2 ≤ ∫ r, r ^ 2 ∂σ := by
  have hr := integrable_id_of_sq_FIN040 hr2
  set m := ∫ r, r ∂σ with hm
  have hm1 : Integrable (fun r : ℝ => r - m) σ := hr.sub (integrable_const _)
  have hm0 : ∫ r, (r - m) ∂σ = 0 := by
    rw [integral_sub hr (integrable_const _)]; simp [hm]
  have hsub := subgaussian_centered_FIN040 hL hlsi hm1 hm0
  have hmom := exp_sq_moment_FIN040 hL hsub
  have hcont : Continuous fun r : ℝ => Real.exp ((r - m) ^ 2 / (2 * L)) := by fun_prop
  have hcont2 : Continuous fun r : ℝ => Real.exp (1 / (4 * L) * r ^ 2) := by fun_prop
  have hpt : ∀ r : ℝ, ENNReal.ofReal (Real.exp (1 / (4 * L) * r ^ 2))
      ≤ ENNReal.ofReal (Real.exp (m ^ 2 / (2 * L))) *
        ENNReal.ofReal (Real.exp ((r - m) ^ 2 / (2 * L))) := fun r => by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have : 1 / (4 * L) * r ^ 2 ≤ m ^ 2 / (2 * L) + (r - m) ^ 2 / (2 * L) := by
      have e : 1 / (4 * L) * r ^ 2 = r ^ 2 / (4 * L) := by ring
      rw [e, ← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hL.le (sq_nonneg (r - 2 * m))]
    exact this
  have hlint : ∫⁻ r, ENNReal.ofReal (Real.exp (1 / (4 * L) * r ^ 2)) ∂σ
      ≤ ENNReal.ofReal (Real.exp (m ^ 2 / (2 * L))) * ENNReal.ofReal (√2) := by
    calc _ ≤ ∫⁻ r, ENNReal.ofReal (Real.exp (m ^ 2 / (2 * L))) *
          ENNReal.ofReal (Real.exp ((r - m) ^ 2 / (2 * L))) ∂σ := lintegral_mono hpt
      _ = ENNReal.ofReal (Real.exp (m ^ 2 / (2 * L))) *
          ∫⁻ r, ENNReal.ofReal (Real.exp ((r - m) ^ 2 / (2 * L))) ∂σ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr
  have hI : Integrable (fun r : ℝ => Real.exp (1 / (4 * L) * r ^ 2)) σ := by
    rw [← lintegral_ofReal_ne_top_iff_integrable hcont2.aestronglyMeasurable
      (Eventually.of_forall fun r => (Real.exp_pos _).le)]
    exact ne_top_of_le_ne_top (by simp [ENNReal.mul_eq_top]) hlint
  have hv : Integrable (fun r : ℝ => (r - m) ^ 2) σ := by
    have := (hr2.sub (hr.const_mul (2 * m))).add (integrable_const (m ^ 2))
    exact this.congr (Eventually.of_forall fun r => by simp only [Pi.add_apply, Pi.sub_apply]; ring)
  have hV : ∫ r, (r - m) ^ 2 ∂σ = ∫ r, r ^ 2 ∂σ - m ^ 2 := by
    have e : (fun r : ℝ => (r - m) ^ 2) = fun r => (r ^ 2 - 2 * m * r) + m ^ 2 := by
      funext r; ring
    have i1 : Integrable (fun r : ℝ => r ^ 2 - 2 * m * r) σ := hr2.sub (hr.const_mul (2 * m))
    have i2 : Integrable (fun r : ℝ => 2 * m * r) σ := hr.const_mul (2 * m)
    rw [e, integral_add i1 (integrable_const _), integral_sub hr2 i2, integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [← hm]; ring
  refine ⟨hI, _, rfl, ?_, ?_, ?_, ?_⟩
  · calc (0:ℝ) < 1 := one_pos
      _ = ∫ r, (1:ℝ) ∂σ := by simp
      _ ≤ _ := integral_mono (integrable_const _) hI fun r => by
          simp only
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by positivity)
  · have h1 : ENNReal.ofReal (∫ r, Real.exp (1 / (4 * L) * r ^ 2) ∂σ)
        ≤ ENNReal.ofReal (Real.exp (m ^ 2 / (2 * L)) * √2) := by
      rw [ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun r => (Real.exp_pos _).le),
        ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact hlint
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
    have hMpos : 0 < ∫ r, Real.exp (1 / (4 * L) * r ^ 2) ∂σ := by
      calc (0:ℝ) < 1 := one_pos
        _ = ∫ r, (1:ℝ) ∂σ := by simp
        _ ≤ _ := integral_mono (integrable_const _) hI fun r => by
            simp only
            rw [← Real.exp_zero]
            exact Real.exp_le_exp.mpr (by positivity)
    calc Real.log (∫ r, Real.exp (1 / (4 * L) * r ^ 2) ∂σ)
        ≤ Real.log (Real.exp (m ^ 2 / (2 * L)) * √2) := Real.log_le_log hMpos h2
      _ = Real.log 2 / 2 + m ^ 2 / (2 * L) := by
          rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp,
            Real.log_sqrt (by norm_num)]
          ring
  · -- variance bound
    have hg : Integrable (fun r : ℝ => 1 + (r - m) ^ 2 / (2 * L)) σ :=
      (integrable_const _).add (hv.div_const _)
    have hle : ENNReal.ofReal (∫ r, (1 + (r - m) ^ 2 / (2 * L)) ∂σ) ≤ ENNReal.ofReal (√2) := by
      rw [ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall fun r => by positivity)]
      refine le_trans (lintegral_mono fun r => ENNReal.ofReal_le_ofReal ?_) hmom
      have := Real.add_one_le_exp ((r - m) ^ 2 / (2 * L))
      linarith
    have h2 := (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg 2)).1 hle
    rw [integral_add (integrable_const _) (hv.div_const _), integral_div, hV] at h2
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h2
    have hs : √2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have : ∫ r, r ^ 2 ∂σ - m ^ 2 ≤ L := by
      have h3 : (∫ r, r ^ 2 ∂σ - m ^ 2) / (2 * L) ≤ 1 / 2 := by linarith
      rw [div_le_iff₀ (by positivity)] at h3
      linarith
    linarith
  · have : 0 ≤ ∫ r, (r - m) ^ 2 ∂σ := integral_nonneg fun r => sq_nonneg (r - m)
    rw [hV] at this
    linarith

theorem final_algebra_FIN040 {L m K S Er Et E Q V J : ℝ} (hL : 0 < L) (hK1 : m ^ 2 ≤ K)
    (hKL : K ≤ L + m ^ 2) (hS : S = L + |m| * √K) (hEr : 0 ≤ Er) (hEt : 0 ≤ Et)
    (hE : Er + Et = E) (hVK : V ≤ K * E)
    (hQ : Q ≤ 4 * L ^ 2 * Er + (2 * L + 2 * m ^ 2) * V)
    (hJ : J ≤ (Q / (3 * S) + 3 * S * Et) / 2) :
    L * Er + 4 * π * J + 2 * V ≤ 40 * S * E := by
  have hK0 : 0 ≤ K := (sq_nonneg m).trans hK1
  have hsK : 0 ≤ √K := Real.sqrt_nonneg K
  have hm0 : 0 ≤ |m| * √K := mul_nonneg (abs_nonneg m) hsK
  have hS0 : 0 < S := by rw [hS]; linarith
  have hLS : L ≤ S := by rw [hS]; linarith
  have habs : |m| ≤ √K := Real.abs_le_sqrt hK1
  have hm2S : m ^ 2 ≤ S := by
    have : m ^ 2 = |m| * |m| := by rw [← sq_abs]; ring
    have h2 : |m| * |m| ≤ |m| * √K := mul_le_mul_of_nonneg_left habs (abs_nonneg m)
    rw [hS]; nlinarith
  have hm2' : m ^ 2 ≤ |m| * √K := by
    have : m ^ 2 = |m| * |m| := by rw [← sq_abs]; ring
    have h2 : |m| * |m| ≤ |m| * √K := mul_le_mul_of_nonneg_left habs (abs_nonneg m)
    linarith
  have hKS : K ≤ S := hKL.trans (by rw [hS]; linarith)
  have hmK : m ^ 2 * K ≤ S ^ 2 := by
    have e : (|m| * √K) ^ 2 = m ^ 2 * K := by
      rw [mul_pow, sq_abs, Real.sq_sqrt hK0]
    have : |m| * √K ≤ S := by rw [hS]; linarith
    nlinarith
  have hLK : L * K ≤ S ^ 2 := by nlinarith
  have hEr_le : Er ≤ E := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hq : Q ≤ 8 * S ^ 2 * E := by
    have h1 : (2 * L + 2 * m ^ 2) * V ≤ (2 * L + 2 * m ^ 2) * (K * E) :=
      mul_le_mul_of_nonneg_left hVK (by positivity)
    have h2 : 4 * L ^ 2 * Er ≤ 4 * L ^ 2 * E := mul_le_mul_of_nonneg_left hEr_le (by positivity)
    have h3 : 4 * L ^ 2 + (2 * L + 2 * m ^ 2) * K ≤ 8 * S ^ 2 := by nlinarith
    nlinarith
  have hJ' : J ≤ 17 / 6 * S * E := by
    have h1 : Q / (3 * S) ≤ 8 / 3 * S * E := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h2 : 3 * S * Et ≤ 3 * S * E := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hpi := Real.pi_lt_d2
  have h4 : 4 * π * J ≤ 4 * 3.15 * (17 / 6 * S * E) := by
    have h0 : 0 ≤ 17 / 6 * S * E := by positivity
    rcases le_or_gt J 0 with hJ0 | hJ0
    · have : π * J ≤ 0 := mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le hJ0
      nlinarith
    · have : π * J ≤ 3.15 * J := mul_le_mul_of_nonneg_right hpi.le hJ0.le
      nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hEr_le hL.le, mul_nonneg hS0.le hE0, mul_nonneg hL.le hEr]

theorem integrable_of_abs_le_FIN040 {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ] {g : ℝ × ℝ → ℝ}
    (hg : Continuous g) {C : ℝ} (h : ∀ p, |g p| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs]; exact h p)

theorem amgm_FIN040 {x y lam : ℝ} (hlam : 0 < lam) :
    |x * y| ≤ ((1 / lam) * x ^ 2 + lam * y ^ 2) / 2 := by
  rw [abs_mul]
  have hx : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hy : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  rw [hx, hy]
  have : (1 / lam) * |x| ^ 2 + lam * |y| ^ 2 - 2 * (|x| * |y|) = (|x| - lam * |y|) ^ 2 / lam := by
    field_simp
    ring
  have h2 : 0 ≤ (|x| - lam * |y|) ^ 2 / lam := by positivity
  linarith

/-- FIN040 (recorded radial to planar LSI).  Let `σ` be a probability measure on `ℝ` with
`∫ r² dσ < ∞`, radial LSI constant `L > 0` and radial Poincaré constant `P ≤ L` (both tested on
smooth functions).  Then for the rotational measure `ν` with radial law `σ` and uniform angle, every
smooth bounded planar `F` with bounded gradient satisfies
`Ent_ν(F²) ≤ 40 (L + |∫ r dσ| √(max P (∫ r² dσ))) ∫ |∇F|² dν`. -/
theorem recorded_radial_to_planar_lsi_theorem {σ : Measure ℝ} [IsProbabilityMeasure σ] {L P : ℝ}
    (hL : 0 < L) (hPL : P ≤ L) (hr2 : Integrable (fun r : ℝ => r ^ 2) σ)
    (hlsi : RadialLSIFIN040 σ L)
    (hP : ∀ u : ℝ → ℝ, ContDiff ℝ ∞ u → Integrable (fun r => u r ^ 2) σ →
      Integrable (fun r => deriv u r ^ 2) σ →
      ∫ r, (u r - ∫ s, u s ∂σ) ^ 2 ∂σ ≤ P * ∫ r, deriv u r ^ 2 ∂σ)
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {B D : ℝ} (hB : ∀ x, |F x| ≤ B)
    (hD : ∀ x, gradSq F x ≤ D) :
    homogeneousEntropy (rotationalMeasure σ) (fun x => F x ^ 2) ≤
      ENNReal.ofReal (40 * (L + |∫ r, r ∂σ| * √(max P (∫ r, r ^ 2 ∂σ))) *
        ∫ x, gradSq F x ∂(rotationalMeasure σ)) := by
  set ν := rotationalMeasure σ with hν
  set ρ := angleLaw.prod σ with hρ
  have : IsProbabilityMeasure ν :=
    inferInstanceAs (IsProbabilityMeasure ((angleLaw.prod σ).map polar))
  have hmap : ∀ G : ℝ × ℝ → ℝ, Continuous G → ∫ x, G x ∂ν = ∫ p, G (polar p) ∂ρ := fun G hG =>
    integral_map continuous_polar.aemeasurable hG.aestronglyMeasurable
  have hr := integrable_id_of_sq_FIN040 hr2
  obtain ⟨hI, M, hM, hMpos, hlogM, hR2up, hR2lo⟩ := exp_moment_FIN040 hL hlsi hr2
  set m := ∫ r, r ∂σ with hm
  set R2 := ∫ r, r ^ 2 ∂σ with hR2
  set K := max P R2 with hK
  have hK1 : m ^ 2 ≤ K := hR2lo.trans (le_max_right _ _)
  have hKL : K ≤ L + m ^ 2 := max_le (by nlinarith [sq_nonneg m]) hR2up
  set S := L + |m| * √K with hS
  have hK0 : 0 ≤ K := (sq_nonneg m).trans hK1
  have hS0 : 0 < S := by
    have : 0 ≤ |m| * √K := mul_nonneg (abs_nonneg m) (Real.sqrt_nonneg K)
    rw [hS]; linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hgs0 : ∀ x, 0 ≤ gradSq F x := fun x => by unfold gradSq; positivity
  have hD0 : 0 ≤ D := (hgs0 0).trans (hD 0)
  set c := ∫ x, F x ∂ν with hc
  have hc_abs : |c| ≤ B := by
    have h := norm_integral_le_of_norm_le_const (μ := ν) (f := F) (C := B)
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
    simpa [Real.norm_eq_abs] using h
  obtain ⟨H, hHx⟩ : ∃ H : ℝ × ℝ → ℝ, ∀ x, H x = F x - c := ⟨fun x => F x - c, fun x => rfl⟩
  have hHeq : H = fun x => F x - c := funext hHx
  have hH : ContDiff ℝ ∞ H := by rw [hHeq]; exact hF.sub contDiff_const
  have hHB : ∀ x, |H x| ≤ 2 * B := fun x => by
    rw [hHx]
    calc |F x - c| ≤ |F x| + |c| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hB x]
  have hgH : ∀ x, gradSq H x = gradSq F x := fun x => by
    simp only [gradSq, hHeq, fderiv_sub_const]
  have hgsum : ∀ p, radDer H p ^ 2 + tanDer H p ^ 2 = gradSq F (polar p) := fun p => by
    rw [radDer_sq_add_tanDer_sq, hgH]
  have hrad : ∀ p, |radDer H p| ≤ √D := fun p => Real.abs_le_sqrt (by
    have := hgsum p; have := hD (polar p); nlinarith [sq_nonneg (tanDer H p)])
  have htan : ∀ p, |tanDer H p| ≤ √D := fun p => Real.abs_le_sqrt (by
    have := hgsum p; have := hD (polar p); nlinarith [sq_nonneg (radDer H p)])
  have hc1 : Continuous fun p => H (polar p) := hH.continuous.comp continuous_polar
  have hρc := continuous_radDer hH
  have hTc := continuous_tanDer hH
  have hgsc := continuous_gradSq hF
  -- integrabilities
  have hHi : Integrable (fun p => H (polar p) ^ 2) ρ :=
    integrable_of_abs_le_FIN040 (hc1.pow 2) (C := (2 * B) ^ 2) fun p => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hHB _) 2
  have hradi : Integrable (fun p => radDer H p ^ 2) ρ :=
    integrable_of_abs_le_FIN040 (hρc.pow 2) (C := (√D) ^ 2) fun p => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hrad p) 2
  have htani : Integrable (fun p => tanDer H p ^ 2) ρ :=
    integrable_of_abs_le_FIN040 (hTc.pow 2) (C := (√D) ^ 2) fun p => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (htan p) 2
  have hQi : Integrable (fun p : ℝ × ℝ => p.2 ^ 2 * H (polar p) ^ 2) ρ := by
    refine ((hr2.comp_snd angleLaw).const_mul ((2 * B) ^ 2)).mono'
      ((continuous_snd.pow 2).mul (hc1.pow 2)).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    have : H (polar p) ^ 2 ≤ (2 * B) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hHB _) 2
    calc p.2 ^ 2 * H (polar p) ^ 2 ≤ p.2 ^ 2 * (2 * B) ^ 2 := by gcongr
      _ = _ := by ring
  -- quantities
  set Er := ∫ p, radDer H p ^ 2 ∂ρ with hEr
  set Et := ∫ p, tanDer H p ^ 2 ∂ρ with hEt
  set E := ∫ x, gradSq F x ∂ν with hE
  set V := ∫ p, H (polar p) ^ 2 ∂ρ with hV
  set Q := ∫ p, p.2 ^ 2 * H (polar p) ^ 2 ∂ρ with hQ
  set J := ∫ p, |H (polar p) * (p.2 * tanDer H p)| ∂ρ with hJ
  have hEr0 : 0 ≤ Er := integral_nonneg fun p => sq_nonneg _
  have hEt0 : 0 ≤ Et := integral_nonneg fun p => sq_nonneg _
  have hV0 : 0 ≤ V := integral_nonneg fun p => sq_nonneg _
  have hJ0 : 0 ≤ J := integral_nonneg fun p => abs_nonneg _
  have hEsum : Er + Et = E := by
    rw [hEr, hEt, ← integral_add hradi htani, hE, hmap _ hgsc]
    exact integral_congr_ae (Eventually.of_forall fun p => hgsum p)
  -- Poincare / variance
  have hFi : Integrable (fun x => F x ^ 2) ν :=
    Integrable.of_bound (hF.continuous.pow 2).aestronglyMeasurable (B ^ 2)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2)
  have hGi : Integrable (gradSq F) ν :=
    Integrable.of_bound hgsc.aestronglyMeasurable D (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hgs0 x)]; exact hD x)
  have hpoin := optional_direct_planar_poincare_main (σ := σ) (P := P) (R2 := R2) hr2 rfl hP hF hFi hGi
  have hVeq : ∫ x, (F x - c) ^ 2 ∂ν = V := by
    rw [hV, hmap (fun x => (F x - c) ^ 2) (by fun_prop)]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [hHx]
  have hVK : V ≤ K * E := by
    rw [← hVeq]; exact hpoin
  -- Core 2
  have hcore2 := core2_FIN040 hr2 hL.le (t := 1 / (4 * L)) (by positivity) hlsi hI hM hH hHB hrad
  have hQle : Q ≤ 4 * L ^ 2 * Er + (2 * L + 2 * m ^ 2) * V := by
    have hlog2 : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
    have h1 : V * Real.log M ≤ V * (Real.log 2 / 2 + m ^ 2 / (2 * L)) :=
      mul_le_mul_of_nonneg_left hlogM hV0
    have h2 : Q = 4 * L * (1 / (4 * L) * Q) := by field_simp
    have h3 : 4 * L * (1 / (4 * L) * Q) ≤ 4 * L * (L * Er + V * Real.log M) :=
      mul_le_mul_of_nonneg_left hcore2 (by positivity)
    have h4 : 4 * L * (L * Er + V * (Real.log 2 / 2 + m ^ 2 / (2 * L)))
        = 4 * L ^ 2 * Er + V * (2 * L * Real.log 2 + 2 * m ^ 2) := by
      field_simp
      ring
    have h5 : V * (2 * L * Real.log 2) ≤ V * (2 * L) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hV0
    have h6 : 4 * L * (L * Er + V * Real.log M)
        ≤ 4 * L * (L * Er + V * (Real.log 2 / 2 + m ^ 2 / (2 * L))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h7 : V * (2 * L * Real.log 2 + 2 * m ^ 2)
        = V * (2 * L * Real.log 2) + V * (2 * m ^ 2) := by ring
    have h8 : (2 * L + 2 * m ^ 2) * V = V * (2 * L) + V * (2 * m ^ 2) := by ring
    linarith
  -- AM-GM for the angular term
  have hJle : J ≤ (Q / (3 * S) + 3 * S * Et) / 2 := by
    have hpt : ∀ p : ℝ × ℝ, |H (polar p) * (p.2 * tanDer H p)|
        ≤ (1 / (3 * S) * (p.2 ^ 2 * H (polar p) ^ 2) + 3 * S * tanDer H p ^ 2) / 2 := fun p => by
      have := amgm_FIN040 (x := H (polar p) * p.2) (y := tanDer H p) (lam := 3 * S) (by positivity)
      calc |H (polar p) * (p.2 * tanDer H p)| = |H (polar p) * p.2 * tanDer H p| := by
            rw [mul_assoc]
        _ ≤ _ := this
        _ = _ := by ring
    have hg : Integrable (fun p : ℝ × ℝ =>
        (1 / (3 * S) * (p.2 ^ 2 * H (polar p) ^ 2) + 3 * S * tanDer H p ^ 2) / 2) ρ :=
      ((hQi.const_mul _).add (htani.const_mul _)).div_const 2
    calc J ≤ ∫ p, (1 / (3 * S) * (p.2 ^ 2 * H (polar p) ^ 2) + 3 * S * tanDer H p ^ 2) / 2 ∂ρ :=
          integral_mono_of_nonneg (Eventually.of_forall fun p => abs_nonneg _) hg
            (Eventually.of_forall hpt)
      _ = (Q / (3 * S) + 3 * S * Et) / 2 := by
          rw [integral_div, integral_add (hQi.const_mul _) (htani.const_mul _),
            integral_const_mul, integral_const_mul]
          have : 1 / (3 * S) * Q = Q / (3 * S) := by ring
          rw [this]
  -- Core 1
  have hcore1 := core1_FIN040 hr hL.le hlsi hH hHB hrad htan
  have halg := final_algebra_FIN040 hL hK1 hKL rfl hEr0 hEt0 hEsum hVK hQle hJle
  -- assemble
  have hmem : MemLp F 2 ν :=
    MemLp.of_bound hF.continuous.aestronglyMeasurable B (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hB x)
  have hrot := DGPS.FiniteN.Tools.Rothaus.rothaus_centering_variance hmem
  have e1 : (fun x => (F x - ∫ y, F y ∂ν) ^ 2) = fun x => H x ^ 2 := by
    funext x; rw [hHx]
  rw [e1] at hrot
  have hvar : variance F ν = V := by
    rw [variance_eq_integral hF.continuous.measurable.aemeasurable, ← hVeq]
  rw [hvar] at hrot
  have hent : homogeneousEntropy ν (fun x => H x ^ 2)
      = homogeneousEntropy ρ (fun p => H (polar p) ^ 2) :=
    homogeneousEntropy_map_FIN040 (μ := ρ) continuous_polar.measurable
      (hH.continuous.pow 2).measurable
  obtain ⟨Kl, hKl⟩ := mul_log_bound_FIN040 ((2 * B) ^ 2)
  have hlogi : Integrable (fun p => H (polar p) ^ 2 * Real.log (H (polar p) ^ 2)) ρ :=
    Integrable.of_bound ((Real.continuous_mul_log.comp (hc1.pow 2)).aestronglyMeasurable) Kl
      (Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]
        refine hKl _ (sq_nonneg _) ?_
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hHB _) 2)
  have hform := homogeneousEntropy_eq_formula (P := ρ) (v := fun p => H (polar p) ^ 2)
    (Eventually.of_forall fun p => sq_nonneg _) hHi hlogi
  have hnn : 0 ≤ L * Er + 4 * π * J := by positivity
  calc homogeneousEntropy ν (fun x => F x ^ 2)
      ≤ homogeneousEntropy ν (fun x => H x ^ 2) + ENNReal.ofReal (2 * V) := hrot
    _ ≤ ENNReal.ofReal (L * Er + 4 * π * J) + ENNReal.ofReal (2 * V) := by
        gcongr
        rw [hent, hform]
        exact ENNReal.ofReal_le_ofReal hcore1
    _ = ENNReal.ofReal (L * Er + 4 * π * J + 2 * V) :=
        (ENNReal.ofReal_add hnn (by positivity)).symm
    _ ≤ ENNReal.ofReal (40 * S * E) := ENNReal.ofReal_le_ofReal halg

theorem sq_integral_le_FIN040 {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hr2 : Integrable (fun r : ℝ => r ^ 2) σ) : (∫ r, r ∂σ) ^ 2 ≤ ∫ r, r ^ 2 ∂σ := by
  have hm : MemLp (fun r : ℝ => r) 2 σ :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hr2
  have h := variance_eq_sub hm
  have h0 := variance_nonneg (fun r : ℝ => r) σ
  simp only [Pi.pow_apply] at h
  linarith

/-- FIN040 applied to FIN039 (and FIN035): for the ordered radial laws the planar LSI constant is
bounded uniformly in `N`. -/
theorem ordered_planar_lsi_FIN040 {κ : ℝ} (hκ : 2 < κ) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 = κ * DGPS.Circle.BesselMoments.besselRatio r0 ∧ ∃ A : ℝ, 0 < A ∧
      ∀ N : ℕ+, ∀ F : ℝ × ℝ → ℝ, ContDiff ℝ ∞ F → ∀ B D : ℝ, (∀ x, |F x| ≤ B) →
        (∀ x, gradSq F x ≤ D) →
        homogeneousEntropy (rotationalMeasure (orderedRadialLaw_FIN035 κ r0 (N : ℝ)))
            (fun x => F x ^ 2) ≤
          ENNReal.ofReal (A * ∫ x, gradSq F x ∂(rotationalMeasure
            (orderedRadialLaw_FIN035 κ r0 (N : ℝ)))) := by
  obtain ⟨r0, hr0, hroot, L, M, hL, hM, h⟩ := ordered_radial_uniform_lsi hκ
  refine ⟨r0, hr0, hroot, 40 * (L + √M * √(max (L / 2) M)), ?_, ?_⟩
  · positivity
  intro N F hF B D hB hD
  obtain ⟨hprob, hlsi', hmom⟩ := h N
  have := hprob
  set σ := orderedRadialLaw_FIN035 κ r0 (N : ℝ) with hσ
  obtain ⟨hi2, hm2⟩ := hmom 2 (by norm_num)
  obtain ⟨hi1, hm1⟩ := hmom 1 (by norm_num)
  have hftc : ∀ u : ℝ → ℝ, ContDiff ℝ ∞ u →
      (∀ x ∈ Ioi (0 : ℝ), ∀ y ∈ Ioi (0 : ℝ), u y - u x = ∫ t in x..y, deriv u t) ∧
      LocallyIntegrableOn (deriv u) (Ioi 0) volume := fun u hu => by
    have hc : Continuous (deriv u) := hu.continuous_deriv (by simp)
    refine ⟨fun x _ y _ => ?_, hc.locallyIntegrable.locallyIntegrableOn _⟩
    rw [intervalIntegral.integral_deriv_eq_sub (fun t _ => (hu.differentiable (by simp)) t)
      (hc.intervalIntegrable x y)]
  have hlsi : RadialLSIFIN040 σ L := fun u hu hu2 hd2 => by
    have := (hlsi' u (deriv u) (hftc u hu).1 (hftc u hu).2 hd2).1
    exact this
  have hP : ∀ u : ℝ → ℝ, ContDiff ℝ ∞ u → Integrable (fun r => u r ^ 2) σ →
      Integrable (fun r => deriv u r ^ 2) σ →
      ∫ r, (u r - ∫ s, u s ∂σ) ^ 2 ∂σ ≤ (L / 2) * ∫ r, deriv u r ^ 2 ∂σ := fun u hu hu2 hd2 => by
    have := (hlsi' u (deriv u) (hftc u hu).1 (hftc u hu).2 hd2).2
    rwa [variance_eq_integral hu.continuous.measurable.aemeasurable] at this
  have hr2 : Integrable (fun r : ℝ => r ^ 2) σ := hi2
  have hmain := recorded_radial_to_planar_lsi_theorem hL (by linarith) hr2 hlsi hP hF hB hD
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hE0 : 0 ≤ ∫ x, gradSq F x ∂(rotationalMeasure σ) :=
    integral_nonneg fun x => by unfold gradSq; positivity
  refine mul_le_mul_of_nonneg_right ?_ hE0
  have hR2 : ∫ r, r ^ 2 ∂σ ≤ M := hm2
  have hsq := sq_integral_le_FIN040 hr2
  have hm_abs : |∫ r, r ∂σ| ≤ √M := Real.abs_le_sqrt (hsq.trans hR2)
  have hK : √(max (L / 2) (∫ r, r ^ 2 ∂σ)) ≤ √(max (L / 2) M) :=
    Real.sqrt_le_sqrt (max_le_max le_rfl hR2)
  have : |∫ r, r ∂σ| * √(max (L / 2) (∫ r, r ^ 2 ∂σ)) ≤ √M * √(max (L / 2) M) :=
    mul_le_mul hm_abs hK (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  linarith

end DGPS.FiniteN
