import FullLabeledLSI.Infra.SpectralCalc
import FullLabeledLSI.Infra.HypercontrConvex
import FullLabeledLSI.Infra.HypercontrTorus7

/-!
# The Markov property of the reference heat semigroup on `L²(μ^{⊗N})`

Manuscript Section 6.3.  Let `S_t = exp(-tΛ)` be the spectral multiplier of `SpectralCalc`
(`Sfun hb t Ψ` is a representative of `S_t Ψ`) and `Q = μ^{⊗N}`.

* (M0) conservation: `∫ S_t Ψ = ∫ Ψ` and `S_t 1 = 1` a.e.;
* (M1) positivity on finite spectral sums, `‖(S_t u)⁻‖₂ ≤ ‖u⁻‖₂` for `u = ∑_{j ∈ T} c_j E_j`,
  from `convex_dissipation` applied to the smooth convex functions
  `Γ_ε(s) = ((√(s²+ε²) - s)/2)²` and `ε → 0`;
* (M2) positivity: `Ψ ≥ 0` a.e. implies `S_t Ψ ≥ 0` a.e. (finite spectral sums are dense in `L²`);
* (M3) the `L^s` contraction (`2 ≤ s < ∞`): `‖S_t Ψ‖_s ≤ ‖Ψ‖_s` (tangent lines of `|x|^s`, a countable
  family of rational tangents, positivity, conservation; then truncation and Fatou).
-/

open MeasureTheory SharpLSI Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace SharpLSI.FL.Spectral

/-! ### Generic `L^p` facts -/

section Generic

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma continuous_negPt : Continuous (fun y : ℝ => max (-y) 0) :=
  continuous_neg.max continuous_const

lemma eLpNorm_two_eq_ofReal_sqrt {f : α → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, f x ^ 2 ∂μ)) := by
  rw [← eLpNorm_congr_ae hf.coeFn_toLp, eLpNorm_coe_eq_ofReal_norm]
  congr 1
  rw [← norm_toLp_sq hf, Real.sqrt_sq (norm_nonneg _)]

lemma eLpNorm_two_le_of_integral_sq_le {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (h : ∫ x, f x ^ 2 ∂μ ≤ ∫ x, g x ^ 2 ∂μ) : eLpNorm f 2 μ ≤ eLpNorm g 2 μ := by
  rw [eLpNorm_two_eq_ofReal_sqrt hf, eLpNorm_two_eq_ofReal_sqrt hg]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt h)

/-- If `|f - g| ≤ δ` pointwise (probability measure), then `‖f‖_p ≤ ‖g‖_p + δ`. -/
lemma eLpNorm_le_add_of_abs_sub_le [IsProbabilityMeasure μ] {f g : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) {δ : ℝ}
    (h : ∀ x, |f x - g x| ≤ δ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm f p μ ≤ eLpNorm g p μ + ENNReal.ofReal δ := by
  have h2 : eLpNorm (f - g) p μ ≤ ENNReal.ofReal δ := by
    have := eLpNorm_le_of_ae_bound (p := p) (μ := μ) (f := f - g) (hf.sub hg) (C := δ)
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using h x)
    simpa using this
  calc eLpNorm f p μ = eLpNorm (g + (f - g)) p μ := by
        congr 1; funext x; simp
    _ ≤ eLpNorm g p μ + eLpNorm (f - g) p μ := eLpNorm_add_le hp
    _ ≤ eLpNorm g p μ + ENNReal.ofReal δ := add_le_add le_rfl h2

/-- `x ↦ x⁻ = max (-x) 0` is `1`-Lipschitz, on the level of `L^p` norms. -/
lemma eLpNorm_negPart_le_add {f g : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun x => max (-(f x)) 0) p μ ≤
      eLpNorm (fun x => max (-(g x)) 0) p μ + eLpNorm (fun x => f x - g x) p μ := by
  have h1 : eLpNorm (fun x => max (-(f x)) 0) p μ ≤
      eLpNorm ((fun x => max (-(g x)) 0) + (fun x => ‖f x - g x‖)) p μ := by
    refine eLpNorm_mono_real (continuous_negPt.comp_aestronglyMeasurable hf) fun x => ?_
    simp only [Pi.add_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    have h2 := le_max_left (-(g x)) 0
    have h3 := le_abs_self (g x - f x)
    have h4 := abs_sub_comm (g x) (f x)
    refine max_le ?_ (add_nonneg (le_max_right _ _) (abs_nonneg _))
    linarith
  calc eLpNorm (fun x => max (-(f x)) 0) p μ
      ≤ eLpNorm ((fun x => max (-(g x)) 0) + (fun x => ‖f x - g x‖)) p μ := h1
    _ ≤ eLpNorm (fun x => max (-(g x)) 0) p μ + eLpNorm (fun x => ‖f x - g x‖) p μ :=
        eLpNorm_add_le hp
    _ = eLpNorm (fun x => max (-(g x)) 0) p μ + eLpNorm (fun x => f x - g x) p μ := by
        rw [eLpNorm_norm (fun x => f x - g x) (hf.sub hg)]

/-- If `Ψ ≥ 0` a.e., then `‖u⁻‖_p ≤ ‖Ψ - u‖_p`. -/
lemma eLpNorm_negPart_le_of_nonneg {Ψ u : α → ℝ} (hu : AEStronglyMeasurable u μ)
    (hnn : 0 ≤ᵐ[μ] Ψ) (p : ℝ≥0∞) :
    eLpNorm (fun x => max (-(u x)) 0) p μ ≤ eLpNorm (fun x => Ψ x - u x) p μ := by
  refine eLpNorm_mono_ae (continuous_negPt.comp_aestronglyMeasurable hu) ?_
  filter_upwards [hnn] with x hx
  have hx' : 0 ≤ Ψ x := hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  refine max_le ?_ (abs_nonneg _)
  have := le_abs_self (Ψ x - u x)
  linarith

end Generic

/-! ### The smooth convex approximations `Γ_ε(s) = ((√(s²+ε²) - s)/2)²` of `(s⁻)²` -/

section Gamma

/-- `r_ε(s) = √(s² + ε²)`. -/
def rrE (ε s : ℝ) : ℝ := Real.sqrt (s ^ 2 + ε ^ 2)

/-- `h_ε(s) = (r_ε(s) - s)/2`, within `ε/2` of `s⁻ = max (-s) 0`. -/
def hhE (ε s : ℝ) : ℝ := (rrE ε s - s) / 2

/-- `h_ε'`. -/
def hhE1 (ε s : ℝ) : ℝ := (s / rrE ε s - 1) / 2

/-- `h_ε''`. -/
def hhE2 (ε s : ℝ) : ℝ := ε ^ 2 / (2 * rrE ε s ^ 3)

/-- `Γ_ε = h_ε²`. -/
def GamE (ε s : ℝ) : ℝ := hhE ε s ^ 2

variable {ε : ℝ}

lemma rr_pos (hε : 0 < ε) (s : ℝ) : 0 < rrE ε s := Real.sqrt_pos.2 (by positivity)

lemma rr_sq (ε s : ℝ) : rrE ε s ^ 2 = s ^ 2 + ε ^ 2 := Real.sq_sqrt (by positivity)

lemma abs_le_rr (ε s : ℝ) : |s| ≤ rrE ε s := Real.abs_le_sqrt (by nlinarith [sq_nonneg ε])

lemma rr_le (hε : 0 ≤ ε) (s : ℝ) : rrE ε s ≤ |s| + ε := by
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h1 := sq_abs s
  have h2 := mul_nonneg (abs_nonneg s) hε
  nlinarith [h1, h2]

lemma eps_le_rr (hε : 0 < ε) (s : ℝ) : ε ≤ rrE ε s := by
  have h := Real.sqrt_le_sqrt (show ε ^ 2 ≤ s ^ 2 + ε ^ 2 by nlinarith [sq_nonneg s])
  rwa [Real.sqrt_sq hε.le] at h

lemma hhE_nonneg (ε s : ℝ) : 0 ≤ hhE ε s := by
  unfold hhE
  linarith [abs_le_rr ε s, le_abs_self s]

lemma hhE_le (hε : 0 ≤ ε) (s : ℝ) : hhE ε s ≤ |s| + ε := by
  unfold hhE
  linarith [rr_le hε s, neg_abs_le s, abs_nonneg s]

lemma hhE1_bounds (hε : 0 < ε) (s : ℝ) : -1 ≤ hhE1 ε s ∧ hhE1 ε s ≤ 0 := by
  have hr := rr_pos hε s
  have h1 : s / rrE ε s ≤ 1 := by
    rw [div_le_one hr]
    exact (le_abs_self s).trans (abs_le_rr ε s)
  have h2 : -1 ≤ s / rrE ε s := by
    rw [le_div_iff₀ hr]
    linarith [neg_abs_le s, abs_le_rr ε s]
  unfold hhE1
  constructor <;> linarith

lemma hhE2_bounds (hε : 0 < ε) (s : ℝ) : 0 ≤ hhE2 ε s ∧ hhE2 ε s ≤ 1 / (2 * ε) := by
  have hr := rr_pos hε s
  constructor
  · unfold hhE2; positivity
  · unfold hhE2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h := eps_le_rr hε s
    have h3 := pow_le_pow_left₀ hε.le h 3
    nlinarith [h3]

lemma hasDerivAt_rr (hε : 0 < ε) (s : ℝ) : HasDerivAt (rrE ε) (s / rrE ε s) s := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 + ε ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).add_const (ε ^ 2)
  have h2 : HasDerivAt (rrE ε) (2 * s / (2 * rrE ε s)) s := h1.sqrt (by positivity)
  have h3 : 2 * s / (2 * rrE ε s) = s / rrE ε s := by
    have := (rr_pos hε s).ne'
    field_simp
  rwa [h3] at h2

lemma hasDerivAt_hhE (hε : 0 < ε) (s : ℝ) : HasDerivAt (hhE ε) (hhE1 ε s) s :=
  ((hasDerivAt_rr hε s).sub (hasDerivAt_id' s)).div_const 2

lemma hasDerivAt_hhE1 (hε : 0 < ε) (s : ℝ) : HasDerivAt (hhE1 ε) (hhE2 ε s) s := by
  have h := (((hasDerivAt_id' s).div (hasDerivAt_rr hε s) (rr_pos hε s).ne').sub_const
    1).div_const 2
  have e : (1 * rrE ε s - s * (s / rrE ε s)) / rrE ε s ^ 2 / 2 = hhE2 ε s := by
    have hr : rrE ε s ≠ 0 := (rr_pos hε s).ne'
    have hsq := rr_sq ε s
    unfold hhE2
    have h1 : 1 * rrE ε s - s * (s / rrE ε s) = ε ^ 2 / rrE ε s := by
      field_simp
      nlinarith [hsq]
    rw [h1]
    field_simp
  exact h.congr_deriv e

lemma continuous_hhE (hε : 0 < ε) : Continuous (hhE ε) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_hhE hε s).continuousAt

lemma hasDerivAt_GamE (hε : 0 < ε) (s : ℝ) :
    HasDerivAt (GamE ε) (2 * hhE ε s * hhE1 ε s) s := by
  have h := (hasDerivAt_hhE hε s).pow 2
  have e : ((2 : ℕ) : ℝ) * hhE ε s ^ (2 - 1) * hhE1 ε s = 2 * hhE ε s * hhE1 ε s := by
    norm_num
  exact h.congr_deriv e

lemma deriv_GamE (hε : 0 < ε) : deriv (GamE ε) = fun s => 2 * hhE ε s * hhE1 ε s :=
  funext fun s => (hasDerivAt_GamE hε s).deriv

lemma hasDerivAt_dGamE (hε : 0 < ε) (s : ℝ) :
    HasDerivAt (fun s => 2 * hhE ε s * hhE1 ε s)
      (2 * hhE1 ε s * hhE1 ε s + 2 * hhE ε s * hhE2 ε s) s :=
  (((hasDerivAt_hhE hε s).const_mul 2).mul (hasDerivAt_hhE1 hε s))

lemma deriv_deriv_GamE (hε : 0 < ε) (s : ℝ) :
    deriv (deriv (GamE ε)) s = 2 * hhE1 ε s * hhE1 ε s + 2 * hhE ε s * hhE2 ε s := by
  rw [deriv_GamE hε]
  exact (hasDerivAt_dGamE hε s).deriv

lemma deriv_deriv_GamE_nonneg (hε : 0 < ε) (s : ℝ) : 0 ≤ deriv (deriv (GamE ε)) s := by
  rw [deriv_deriv_GamE hε]
  have h1 := mul_self_nonneg (hhE1 ε s)
  have h2 := mul_nonneg (hhE_nonneg ε s) (hhE2_bounds hε s).1
  linarith

lemma contDiff_GamE (hε : 0 < ε) {n : WithTop ℕ∞} : ContDiff ℝ n (GamE ε) := by
  have hr : ContDiff ℝ n (rrE ε) := by
    have : ContDiff ℝ n (fun s : ℝ => s ^ 2 + ε ^ 2) := (contDiff_id.pow 2).add contDiff_const
    exact this.sqrt (fun s => by positivity)
  have h : ContDiff ℝ n (hhE ε) := (hr.sub contDiff_id).div_const 2
  exact h.pow 2

lemma GamE_growth (hε : 0 < ε) :
    ∃ C : ℝ, ∃ m : ℕ, ∀ s : ℝ,
      |GamE ε s| + |deriv (GamE ε) s| + |deriv (deriv (GamE ε)) s| ≤ C * (1 + |s|) ^ m := by
  refine ⟨(1 + ε) ^ 2 + 2 * (1 + ε) + (2 + (1 + ε) / ε), 2, fun s => ?_⟩
  have hy : 1 ≤ 1 + |s| := by linarith [abs_nonneg s]
  have hD0 : 0 ≤ 1 + ε := by linarith
  have hD : |s| + ε ≤ (1 + ε) * (1 + |s|) := by
    nlinarith [abs_nonneg s, mul_nonneg hε.le (abs_nonneg s)]
  have h0 := hhE_nonneg ε s
  have hEy : hhE ε s ≤ (1 + ε) * (1 + |s|) := (hhE_le hε.le s).trans hD
  have hb1 := hhE1_bounds hε s
  have hb2 := hhE2_bounds hε s
  have hy2 : (1 + |s|) ≤ (1 + |s|) ^ 2 := by nlinarith
  have hy3 : 1 ≤ (1 + |s|) ^ 2 := by nlinarith
  -- `|Γ|`
  have e1 : |GamE ε s| ≤ ((1 + ε) * (1 + |s|)) ^ 2 := by
    rw [abs_of_nonneg (by unfold GamE; positivity)]
    unfold GamE
    exact pow_le_pow_left₀ h0 hEy 2
  -- `|Γ'|`
  have e2 : |deriv (GamE ε) s| ≤ 2 * ((1 + ε) * (1 + |s|)) := by
    rw [deriv_GamE hε]
    show |2 * hhE ε s * hhE1 ε s| ≤ _
    have h5 : 0 ≤ hhE ε s * (hhE1 ε s + 1) := mul_nonneg h0 (by linarith [hb1.1])
    have h6 : hhE ε s * hhE1 ε s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0 hb1.2
    rw [abs_le]
    constructor <;> nlinarith
  -- `|Γ''|`
  have e3 : |deriv (deriv (GamE ε)) s| ≤ 2 + (1 + ε) * (1 + |s|) / ε := by
    have hnn := deriv_deriv_GamE_nonneg hε s
    rw [abs_of_nonneg hnn, deriv_deriv_GamE hε]
    have h7 : hhE1 ε s * hhE1 ε s ≤ 1 := by nlinarith [hb1.1, hb1.2]
    have h8 : hhE ε s * hhE2 ε s ≤ ((1 + ε) * (1 + |s|)) * (1 / (2 * ε)) :=
      mul_le_mul hEy hb2.2 hb2.1 (by positivity)
    have h9 : ((1 + ε) * (1 + |s|)) * (1 / (2 * ε)) = (1 + ε) * (1 + |s|) / ε / 2 := by
      field_simp
    have h10 : (1 + ε) * (1 + |s|) / ε / 2 * 2 = (1 + ε) * (1 + |s|) / ε := by ring
    nlinarith [h7, h8, h9, h10]
  have hK : (1 + ε) * (1 + |s|) / ε = ((1 + ε) / ε) * (1 + |s|) := by ring
  have h11 : ((1 + ε) / ε) * (1 + |s|) ≤ ((1 + ε) / ε) * (1 + |s|) ^ 2 :=
    mul_le_mul_of_nonneg_left hy2 (by positivity)
  have h12 : 2 * ((1 + ε) * (1 + |s|)) ≤ 2 * (1 + ε) * (1 + |s|) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hy2 hD0]
  have h13 : ((1 + ε) * (1 + |s|)) ^ 2 = (1 + ε) ^ 2 * (1 + |s|) ^ 2 := by ring
  nlinarith [e1, e2, e3, hK, h11, h12, h13, hy3]

lemma abs_negPt_sub_hhE (hε : 0 < ε) (s : ℝ) : |max (-s) 0 - hhE ε s| ≤ ε / 2 := by
  have h1 := abs_le_rr ε s
  have h2 := rr_le hε.le s
  unfold hhE
  rcases le_total 0 s with hs | hs
  · have hs' := abs_of_nonneg hs
    rw [max_eq_right (by linarith : -s ≤ 0), abs_le]
    constructor <;> linarith
  · have hs' := abs_of_nonpos hs
    rw [max_eq_left (by linarith : (0:ℝ) ≤ -s), abs_le]
    constructor <;> linarith

section Memb

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma memLp_hhE [IsFiniteMeasure μ] (hε : 0 < ε) {w : α → ℝ} (hw : MemLp w 2 μ) :
    MemLp (fun x => hhE ε (w x)) 2 μ := by
  refine MemLp.mono' (g := fun x => ‖w x‖ + ε) (hw.norm.add (memLp_const ε))
    ((continuous_hhE hε).comp_aestronglyMeasurable hw.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (hhE_nonneg ε _)]
  have := hhE_le hε.le (w x)
  rw [Real.norm_eq_abs]
  exact this

lemma eLpNorm_negPt_le_hhE [IsProbabilityMeasure μ] (hε : 0 < ε) {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => max (-(f x)) 0) 2 μ ≤
      eLpNorm (fun x => hhE ε (f x)) 2 μ + ENNReal.ofReal (ε / 2) :=
  eLpNorm_le_add_of_abs_sub_le (continuous_negPt.comp_aestronglyMeasurable hf)
    ((continuous_hhE hε).comp_aestronglyMeasurable hf) (fun x => abs_negPt_sub_hhE hε (f x))
    one_le_two

lemma eLpNorm_hhE_le_negPt [IsProbabilityMeasure μ] (hε : 0 < ε) {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => hhE ε (f x)) 2 μ ≤
      eLpNorm (fun x => max (-(f x)) 0) 2 μ + ENNReal.ofReal (ε / 2) :=
  eLpNorm_le_add_of_abs_sub_le ((continuous_hhE hε).comp_aestronglyMeasurable hf)
    (continuous_negPt.comp_aestronglyMeasurable hf)
    (fun x => by rw [abs_sub_comm]; exact abs_negPt_sub_hhE hε (f x)) one_le_two

end Memb

end Gamma

/-! ### Dissipation of `‖h_ε(u)‖₂` along the abstract heat flow -/

section Dissipation

variable {Ω : Type*} [MeasurableSpace Ω] {K : Type*} [Fintype K]
  {P : Measure Ω} [IsProbabilityMeasure P] {M : K → Ω → ℝ} {ν : K → ℝ}
  {G : (K → ℝ) → Ω → ℝ} {a : ℝ}

lemma memLp_uFun (h : Gross.GrossHyp P M ν G a) (c : K → ℝ) :
    MemLp (fun ω => Gross.uFun M c ω) 2 P := by
  have hk : ∀ k, MemLp (M k) 2 P := fun k => by simpa using h.memLp k 2
  have : MemLp (fun ω => ∑ k, c k * M k ω) 2 P :=
    memLp_finsetSum Finset.univ fun k _ => (hk k).const_mul (c k)
  exact this

/-- **Dissipation of the smoothed negative part.** -/
lemma eLpNorm_hhE_flow_le (h : Gross.GrossHyp P M ν G a) (c : K → ℝ) {ε : ℝ} (hε : 0 < ε)
    {t : ℝ} (ht : 0 ≤ t) :
    eLpNorm (fun ω => hhE ε (Gross.uFun M (Gross.flow ν t c) ω)) 2 P ≤
      eLpNorm (fun ω => hhE ε (Gross.uFun M (Gross.flow ν 0 c) ω)) 2 P := by
  have hanti := Gross.convex_dissipation h c (Γ := GamE ε) (contDiff_GamE hε)
    (deriv_deriv_GamE_nonneg hε) (GamE_growth hε)
  have hle : ∫ ω, GamE ε (Gross.uFun M (Gross.flow ν t c) ω) ∂P ≤
      ∫ ω, GamE ε (Gross.uFun M (Gross.flow ν 0 c) ω) ∂P :=
    hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  exact eLpNorm_two_le_of_integral_sq_le (memLp_hhE hε (memLp_uFun h _))
    (memLp_hhE hε (memLp_uFun h _)) hle

end Dissipation

/-! ### Coefficients: uniqueness and linearity -/

section Coeff

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

/-- Two `L²` functions with the same coefficients agree a.e. -/
lemma ae_eq_of_coeff_eq (hb : IsRefEigenbasis mu e lam) {f g : Config N d → ℝ}
    (hf : MemLp f 2 (Q mu N)) (hg : MemLp g 2 (Q mu N))
    (h : ∀ j, coeff mu e j f = coeff mu e j g) : f =ᵐ[Q mu N] g := by
  have : hf.toLp f = hg.toLp g := by
    refine repr_ext (tHB hb N) fun j => ?_
    rw [← coeff_eq_repr hb hf, ← coeff_eq_repr hb hg]
    exact h j
  exact (MemLp.toLp_eq_toLp_iff hf hg).1 this

lemma E_zero_apply (hb : IsRefEigenbasis mu e lam) (ω : Config N d) :
    E e (0 : Fin N → ℕ) ω = 1 := by
  simp [E, hb.zero]

lemma Lam_zero (hlam0 : lam 0 = 0) : Lam lam (0 : Fin N → ℕ) = 0 := by
  simp [Lam, hlam0]

lemma coeff_zero_index (hb : IsRefEigenbasis mu e lam) (Ψ : Config N d → ℝ) :
    coeff mu e (0 : Fin N → ℕ) Ψ = ∫ ω, Ψ ω ∂(Q mu N) := by
  unfold coeff
  simp [E_zero_apply hb]

lemma coeff_one (hb : IsRefEigenbasis mu e lam) (j : Fin N → ℕ) :
    coeff mu e j (fun _ : Config N d => (1 : ℝ)) = if j = 0 then 1 else 0 := by
  have h := tensor_orthonormal mu e hb.orthonormal N 0 j
  have h2 : ∫ ω, (1 : ℝ) * E e j ω ∂(Q mu N) = ∫ ω, E e 0 ω * E e j ω ∂(Q mu N) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp [E_zero_apply hb])
  unfold coeff
  rw [h2, h]
  by_cases hj : j = 0
  · subst hj; simp
  · simp [hj, Ne.symm hj]

lemma key_coeff_one (hb : IsRefEigenbasis mu e lam) (hlam0 : lam 0 = 0) (t : ℝ)
    (j : Fin N → ℕ) :
    Real.exp (-(t * Lam lam j)) * coeff mu e j (fun _ : Config N d => (1 : ℝ)) =
      coeff mu e j (fun _ : Config N d => (1 : ℝ)) := by
  rw [coeff_one hb]
  by_cases hj : j = 0
  · subst hj; simp [Lam_zero hlam0]
  · simp [hj]

lemma coeff_affine (hb : IsRefEigenbasis mu e lam) {f g : Config N d → ℝ}
    (hf : MemLp f 2 (Q mu N)) (hg : MemLp g 2 (Q mu N)) (α β γ : ℝ) (j : Fin N → ℕ) :
    coeff mu e j (fun X => α * f X + β * g X + γ) =
      α * coeff mu e j f + β * coeff mu e j g + γ * coeff mu e j (fun _ : Config N d => (1 : ℝ)) := by
  have hEj := tensor_memLp mu e (ref_memLp hb) N j
  have i1 : Integrable (fun X => f X * E e j X) (Q mu N) := hf.integrable_mul hEj
  have i2 : Integrable (fun X => g X * E e j X) (Q mu N) := hg.integrable_mul hEj
  have i3 : Integrable (fun X => (1 : ℝ) * E e j X) (Q mu N) :=
    (memLp_const (1 : ℝ) : MemLp (fun _ : Config N d => (1 : ℝ)) 2 (Q mu N)).integrable_mul hEj
  have hrw : ∀ X, (α * f X + β * g X + γ) * E e j X =
      α * (f X * E e j X) + β * (g X * E e j X) + γ * (1 * E e j X) := fun X => by ring
  unfold coeff
  simp_rw [hrw]
  have s1 : Integrable (fun X => α * (f X * E e j X)) (Q mu N) := i1.const_mul α
  have s2 : Integrable (fun X => β * (g X * E e j X)) (Q mu N) := i2.const_mul β
  have s3 : Integrable (fun X => γ * (1 * E e j X)) (Q mu N) := i3.const_mul γ
  have s12 : Integrable (fun X => α * (f X * E e j X) + β * (g X * E e j X)) (Q mu N) :=
    s1.add s2
  rw [integral_add s12 s3, integral_add s1 s2, integral_const_mul, integral_const_mul,
    integral_const_mul]

/-- Finite spectral sums are in `L²`. -/
lemma memLp_finsum (hb : IsRefEigenbasis mu e lam) (T : Finset (Fin N → ℕ))
    (c : (Fin N → ℕ) → ℝ) :
    MemLp (fun X : Config N d => ∑ j ∈ T, c j * E e j X) 2 (Q mu N) :=
  memLp_finsetSum T fun j _ => (tensor_memLp mu e (ref_memLp hb) N j).const_mul _

/-- The coefficients of a finite spectral sum. -/
lemma coeff_finsum (hb : IsRefEigenbasis mu e lam) (T : Finset (Fin N → ℕ))
    (c : (Fin N → ℕ) → ℝ) (k : Fin N → ℕ) :
    coeff mu e k (fun X : Config N d => ∑ j ∈ T, c j * E e j X) = if k ∈ T then c k else 0 := by
  have hEj : ∀ j, MemLp (E e j) 2 (Q mu N) := fun j => tensor_memLp mu e (ref_memLp hb) N j
  have hint : ∀ j ∈ T, Integrable (fun X => c j * (E e j X * E e k X)) (Q mu N) :=
    fun j _ => ((hEj j).integrable_mul (hEj k)).const_mul _
  have hrw : ∀ X : Config N d, (∑ j ∈ T, c j * E e j X) * E e k X =
      ∑ j ∈ T, c j * (E e j X * E e k X) := fun X => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  unfold coeff
  simp_rw [hrw]
  rw [integral_finsetSum _ hint]
  simp_rw [integral_const_mul, tensor_orthonormal mu e hb.orthonormal N]
  simp

end Coeff

/-! ### (M0) Conservation -/

section M0

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

/-- **(M0)** `∫ S_t Ψ = ∫ Ψ`. -/
theorem integral_Sfun_eq (hb : IsRefEigenbasis mu e lam) (hlam0 : lam 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {Ψ : Config N d → ℝ} (hΨ : MemLp Ψ 2 (Q mu N)) :
    ∫ X, Sfun hb t Ψ X ∂(Q mu N) = ∫ X, Ψ X ∂(Q mu N) := by
  have hlam := lam_nonneg_of_ref hb hlam0
  have h := coeff_Sfun hb hlam ht hΨ (0 : Fin N → ℕ)
  rw [coeff_zero_index hb, coeff_zero_index hb, Lam_zero hlam0] at h
  simpa using h

/-- **(M0)** `S_t 1 = 1` a.e. -/
theorem Sfun_one_ae (hb : IsRefEigenbasis mu e lam) (hlam0 : lam 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    Sfun hb t (fun _ : Config N d => (1 : ℝ)) =ᵐ[Q mu N] fun _ => 1 := by
  have hlam := lam_nonneg_of_ref hb hlam0
  have h1 : MemLp (fun _ : Config N d => (1 : ℝ)) 2 (Q mu N) := memLp_const 1
  refine ae_eq_of_coeff_eq hb (Sfun_memLp hb t h1) h1 fun j => ?_
  rw [coeff_Sfun hb hlam ht h1 j]
  exact key_coeff_one hb hlam0 t j

/-- Linearity of `S_t` (together with `S_t 1 = 1`): `S_t (α f + β g + γ) = α S_t f + β S_t g + γ`
a.e. -/
theorem Sfun_affine (hb : IsRefEigenbasis mu e lam) (hlam0 : lam 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {f g : Config N d → ℝ} (hf : MemLp f 2 (Q mu N)) (hg : MemLp g 2 (Q mu N)) (α β γ : ℝ) :
    Sfun hb t (fun X => α * f X + β * g X + γ) =ᵐ[Q mu N]
      fun X => α * Sfun hb t f X + β * Sfun hb t g X + γ := by
  have hlam := lam_nonneg_of_ref hb hlam0
  have hF : MemLp (fun X => α * f X + β * g X + γ) 2 (Q mu N) :=
    ((hf.const_mul α).add (hg.const_mul β)).add (memLp_const γ)
  have hSf := Sfun_memLp hb t hf
  have hSg := Sfun_memLp hb t hg
  have hR : MemLp (fun X => α * Sfun hb t f X + β * Sfun hb t g X + γ) 2 (Q mu N) :=
    ((hSf.const_mul α).add (hSg.const_mul β)).add (memLp_const γ)
  refine ae_eq_of_coeff_eq hb (Sfun_memLp hb t hF) hR fun j => ?_
  rw [coeff_Sfun hb hlam ht hF j, coeff_affine hb hf hg α β γ j,
    coeff_affine hb hSf hSg α β γ j, coeff_Sfun hb hlam ht hf j, coeff_Sfun hb hlam ht hg j]
  have h1 := key_coeff_one hb hlam0 t j
  linear_combination γ * h1

/-- `S_t` is `L²`-nonexpansive on differences. -/
theorem eLpNorm_Sfun_sub_le (hb : IsRefEigenbasis mu e lam) (hlam0 : lam 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {f g : Config N d → ℝ} (hf : MemLp f 2 (Q mu N)) (hg : MemLp g 2 (Q mu N)) :
    eLpNorm (fun X => Sfun hb t f X - Sfun hb t g X) 2 (Q mu N) ≤
      eLpNorm (fun X => f X - g X) 2 (Q mu N) := by
  have hlam := lam_nonneg_of_ref hb hlam0
  have h := Sfun_affine hb hlam0 ht hf hg 1 (-1) 0
  have hF : MemLp (fun X => 1 * f X + (-1) * g X + 0) 2 (Q mu N) :=
    ((hf.const_mul 1).add (hg.const_mul (-1))).add (memLp_const 0)
  calc eLpNorm (fun X => Sfun hb t f X - Sfun hb t g X) 2 (Q mu N)
      = eLpNorm (Sfun hb t (fun X => 1 * f X + (-1) * g X + 0)) 2 (Q mu N) := by
        refine eLpNorm_congr_ae ?_
        filter_upwards [h] with X hX
        rw [hX]; ring
    _ ≤ eLpNorm (fun X => 1 * f X + (-1) * g X + 0) 2 (Q mu N) :=
        eLpNorm_Sfun_le hb hlam ht hF
    _ = eLpNorm (fun X => f X - g X) 2 (Q mu N) := by
        congr 1; funext X; ring

/-- `S_t` of a finite spectral sum is the finite spectral sum with damped coefficients. -/
theorem Sfun_finsum (hb : IsRefEigenbasis mu e lam) (hlam0 : lam 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (T : Finset (Fin N → ℕ)) (c : (Fin N → ℕ) → ℝ) :
    Sfun hb t (fun X : Config N d => ∑ j ∈ T, c j * E e j X) =ᵐ[Q mu N]
      fun X => ∑ j ∈ T, (Real.exp (-(t * Lam lam j)) * c j) * E e j X := by
  have hlam := lam_nonneg_of_ref hb hlam0
  have hu := memLp_finsum hb T c
  have hv := memLp_finsum hb T (fun j => Real.exp (-(t * Lam lam j)) * c j)
  refine ae_eq_of_coeff_eq hb (Sfun_memLp hb t hu) hv fun k => ?_
  rw [coeff_Sfun hb hlam ht hu k, coeff_finsum hb T c k,
    coeff_finsum hb T (fun j => Real.exp (-(t * Lam lam j)) * c j) k]
  split_ifs <;> simp

end M0

/-! ### (M1) Positivity on finite spectral sums -/

section M1

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

/-- **(M1)** `‖(S_t u)⁻‖₂ ≤ ‖u⁻‖₂` for a finite spectral sum `u = ∑_{j∈T} c_j E_j`. -/
theorem eLpNorm_negPart_Sfun_finsum_le {eC : ℕ → Torus d → ℝ} (hac : mu ≪ volume)
    (hca : volume ≪ mu) (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) {a : ℝ} (ha : 0 < a) (hrls : ENNReal.ofReal a ≤ rLS mu)
    (hlam0 : lam 0 = 0) {t : ℝ} (ht : 0 ≤ t) (T : Finset (Fin N → ℕ)) (c : (Fin N → ℕ) → ℝ) :
    eLpNorm (fun X => max (-(Sfun hb t (fun X : Config N d => ∑ j ∈ T, c j * E e j X) X)) 0) 2
        (Q mu N) ≤
      eLpNorm (fun X : Config N d => max (-(∑ j ∈ T, c j * E e j X)) 0) 2 (Q mu N) := by
  classical
  have hH := Gross.torus_grossHyp hac hca hb hC1 hae ha hrls T
  have hu_mem : MemLp (fun X : Config N d => ∑ j ∈ T, c j * E e j X) 2 (Q mu N) :=
    memLp_finsum hb T c
  set u : Config N d → ℝ := fun X => ∑ j ∈ T, c j * E e j X with hu_def
  set c' : T → ℝ := fun k => c k.1 with hc'
  set w0 : Config N d → ℝ :=
    fun X => Gross.uFun (Gross.MT eC T) (Gross.flow (Gross.nuT lam T) 0 c') X with hw0
  set wt : Config N d → ℝ :=
    fun X => Gross.uFun (Gross.MT eC T) (Gross.flow (Gross.nuT lam T) t c') X with hwt
  have hu_ae : u =ᵐ[Q mu N] w0 := by
    filter_upwards [Gross.ae_poly_eq hae T c] with X hX
    have hf0 : Gross.flow (Gross.nuT lam T) 0 c' = c' := by
      funext k; simp [Gross.flow]
    show u X = Gross.uFun (Gross.MT eC T) (Gross.flow (Gross.nuT lam T) 0 c') X
    rw [hf0]
    exact hX
  have hSu_ae : Sfun hb t u =ᵐ[Q mu N] wt := by
    filter_upwards [Sfun_finsum hb hlam0 ht T c,
      Gross.ae_poly_eq hae T (fun j => Real.exp (-(t * Lam lam j)) * c j)] with X h1 h2
    rw [h1]
    exact h2
  have hSu := Sfun_memLp hb t hu_mem
  have hkey : ∀ ε : ℝ, 0 < ε →
      eLpNorm (fun X => max (-(Sfun hb t u X)) 0) 2 (Q mu N) ≤
        eLpNorm (fun X => max (-(u X)) 0) 2 (Q mu N) + ENNReal.ofReal ε := by
    intro ε hε
    have e1 := eLpNorm_negPt_le_hhE hε hSu.aestronglyMeasurable
    have e2 : eLpNorm (fun X => hhE ε (Sfun hb t u X)) 2 (Q mu N) =
        eLpNorm (fun X => hhE ε (wt X)) 2 (Q mu N) :=
      eLpNorm_congr_ae (hSu_ae.mono fun X hX => by simp only [hX])
    have e3 := eLpNorm_hhE_flow_le hH c' hε ht
    have e4 : eLpNorm (fun X => hhE ε (w0 X)) 2 (Q mu N) =
        eLpNorm (fun X => hhE ε (u X)) 2 (Q mu N) :=
      (eLpNorm_congr_ae (hu_ae.mono fun X hX => by simp only [hX])).symm
    have e5 := eLpNorm_hhE_le_negPt hε hu_mem.aestronglyMeasurable
    calc eLpNorm (fun X => max (-(Sfun hb t u X)) 0) 2 (Q mu N)
        ≤ eLpNorm (fun X => hhE ε (Sfun hb t u X)) 2 (Q mu N) + ENNReal.ofReal (ε / 2) := e1
      _ = eLpNorm (fun X => hhE ε (wt X)) 2 (Q mu N) + ENNReal.ofReal (ε / 2) := by rw [e2]
      _ ≤ eLpNorm (fun X => hhE ε (w0 X)) 2 (Q mu N) + ENNReal.ofReal (ε / 2) :=
          add_le_add e3 le_rfl
      _ = eLpNorm (fun X => hhE ε (u X)) 2 (Q mu N) + ENNReal.ofReal (ε / 2) := by rw [e4]
      _ ≤ (eLpNorm (fun X => max (-(u X)) 0) 2 (Q mu N) + ENNReal.ofReal (ε / 2)) +
            ENNReal.ofReal (ε / 2) := add_le_add e5 le_rfl
      _ = eLpNorm (fun X => max (-(u X)) 0) 2 (Q mu N) + ENNReal.ofReal ε := by
          rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 2; ring
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hδ' : (0 : ℝ) < δ := NNReal.coe_pos.2 hδ
  have := hkey δ hδ'
  rwa [ENNReal.ofReal_coe_nnreal] at this

end M1

/-! ### (M2) Positivity -/

section M2

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

/-- Finite spectral sums approximate every `L²` function. -/
lemma exists_finsum_approx (hb : IsRefEigenbasis mu e lam) {Ψ : Config N d → ℝ}
    (hΨ : MemLp Ψ 2 (Q mu N)) {η : ℝ} (hη : 0 < η) :
    ∃ T : Finset (Fin N → ℕ),
      eLpNorm (fun X => Ψ X - ∑ j ∈ T, coeff mu e j Ψ * E e j X) 2 (Q mu N) <
        ENNReal.ofReal η := by
  obtain ⟨x, hxdef⟩ : ∃ x : Lp ℝ 2 (Q mu N), x = hΨ.toLp Ψ := ⟨_, rfl⟩
  have hx : ⇑x =ᵐ[Q mu N] Ψ := by rw [hxdef]; exact hΨ.coeFn_toLp
  have hs := (tHB hb N).hasSum_repr x
  have hev : ∀ᶠ T : Finset (Fin N → ℕ) in atTop,
      dist (∑ j ∈ T, (tHB hb N).repr x j • tHB hb N j) x < η :=
    hs (Metric.ball_mem_nhds x hη)
  obtain ⟨T, hT⟩ := hev.exists
  refine ⟨T, ?_⟩
  have hp : ⇑(∑ j ∈ T, (tHB hb N).repr x j • tHB hb N j) =ᵐ[Q mu N]
      fun X => ∑ j ∈ T, coeff mu e j Ψ * E e j X := by
    have h := partial_ae hb (fun _ => (1 : ℝ)) T x hx
    have hF : Fpart mu e (fun _ => (1 : ℝ)) T Ψ = fun X => ∑ j ∈ T, coeff mu e j Ψ * E e j X := by
      funext X; simp [Fpart]
    rw [hF] at h
    simpa only [one_mul] using h
  have hsub : (fun X => Ψ X - ∑ j ∈ T, coeff mu e j Ψ * E e j X) =ᵐ[Q mu N]
      ⇑(x - ∑ j ∈ T, (tHB hb N).repr x j • tHB hb N j) := by
    filter_upwards [Lp.coeFn_sub x (∑ j ∈ T, (tHB hb N).repr x j • tHB hb N j), hx, hp]
      with X h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  rw [eLpNorm_congr_ae hsub, eLpNorm_coe_eq_ofReal_norm]
  refine (ENNReal.ofReal_lt_ofReal_iff hη).2 ?_
  rw [← dist_eq_norm, dist_comm]
  exact hT

/-- **(M2) Positivity.** If `Ψ ≥ 0` a.e. and `Ψ ∈ L²`, then `S_t Ψ ≥ 0` a.e. -/
theorem Sfun_nonneg_ae {eC : ℕ → Torus d → ℝ} (hac : mu ≪ volume) (hca : volume ≪ mu)
    (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) {a : ℝ} (ha : 0 < a) (hrls : ENNReal.ofReal a ≤ rLS mu)
    (hlam0 : lam 0 = 0) {t : ℝ} (ht : 0 ≤ t) {Ψ : Config N d → ℝ} (hΨ : MemLp Ψ 2 (Q mu N))
    (hnn : 0 ≤ᵐ[Q mu N] Ψ) : 0 ≤ᵐ[Q mu N] Sfun hb t Ψ := by
  have hS := Sfun_memLp hb t hΨ
  have key : ∀ η : ℝ, 0 < η →
      eLpNorm (fun X => max (-(Sfun hb t Ψ X)) 0) 2 (Q mu N) ≤ ENNReal.ofReal (2 * η) := by
    intro η hη
    obtain ⟨T, hT⟩ := exists_finsum_approx hb hΨ hη
    have hu_mem : MemLp (fun X : Config N d => ∑ j ∈ T, coeff mu e j Ψ * E e j X) 2 (Q mu N) :=
      memLp_finsum hb T _
    have hSu := Sfun_memLp hb t hu_mem
    have h1 := eLpNorm_negPart_le_add hS.aestronglyMeasurable hSu.aestronglyMeasurable
      (p := 2) one_le_two
    have h2 := eLpNorm_negPart_Sfun_finsum_le hac hca hb hC1 hae ha hrls hlam0 ht T
      (fun j => coeff mu e j Ψ)
    have h3 := eLpNorm_Sfun_sub_le hb hlam0 ht hΨ hu_mem
    have h4 := eLpNorm_negPart_le_of_nonneg hu_mem.aestronglyMeasurable hnn 2
    calc eLpNorm (fun X => max (-(Sfun hb t Ψ X)) 0) 2 (Q mu N)
        ≤ eLpNorm (fun X => max (-(Sfun hb t (fun X : Config N d =>
            ∑ j ∈ T, coeff mu e j Ψ * E e j X) X)) 0) 2 (Q mu N) +
          eLpNorm (fun X => Sfun hb t Ψ X - Sfun hb t (fun X : Config N d =>
            ∑ j ∈ T, coeff mu e j Ψ * E e j X) X) 2 (Q mu N) := h1
      _ ≤ eLpNorm (fun X : Config N d => max (-(∑ j ∈ T, coeff mu e j Ψ * E e j X)) 0) 2
            (Q mu N) +
          eLpNorm (fun X => Ψ X - ∑ j ∈ T, coeff mu e j Ψ * E e j X) 2 (Q mu N) :=
          add_le_add h2 h3
      _ ≤ eLpNorm (fun X => Ψ X - ∑ j ∈ T, coeff mu e j Ψ * E e j X) 2 (Q mu N) +
          eLpNorm (fun X => Ψ X - ∑ j ∈ T, coeff mu e j Ψ * E e j X) 2 (Q mu N) :=
          add_le_add h4 le_rfl
      _ ≤ ENNReal.ofReal η + ENNReal.ofReal η := add_le_add hT.le hT.le
      _ = ENNReal.ofReal (2 * η) := by
          rw [← ENNReal.ofReal_add hη.le hη.le]; congr 1; ring
  have hA0 : eLpNorm (fun X => max (-(Sfun hb t Ψ X)) 0) 2 (Q mu N) = 0 := by
    refine le_antisymm ?_ zero_le
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    have hδ' : (0 : ℝ) < δ := NNReal.coe_pos.2 hδ
    calc eLpNorm (fun X => max (-(Sfun hb t Ψ X)) 0) 2 (Q mu N)
        ≤ ENNReal.ofReal (2 * ((δ : ℝ) / 2)) := key _ (by linarith)
      _ = (δ : ℝ≥0∞) := by
          rw [show 2 * ((δ : ℝ) / 2) = δ by ring, ENNReal.ofReal_coe_nnreal]
      _ = 0 + δ := (zero_add _).symm
  have hz := (eLpNorm_eq_zero_iff (by norm_num)).1 hA0
  filter_upwards [hz] with X hX
  have h1 := le_max_left (-(Sfun hb t Ψ X)) 0
  have h2 : max (-(Sfun hb t Ψ X)) 0 = 0 := hX
  show (0 : ℝ) ≤ Sfun hb t Ψ X
  linarith

end M2

/-! ### (M3) The `L^s` contraction -/

section M3

/-- The slope function `ρ_s(q) = |q|^(s-2) q` of the tangent line to `|x|^s` at `q`. -/
def rho (s q : ℝ) : ℝ := |q| ^ (s - 2) * q

lemma continuous_abs_rpow {s : ℝ} (hs : 0 ≤ s) : Continuous (fun q : ℝ => |q| ^ s) :=
  continuous_abs.rpow_const fun _ => Or.inr hs

lemma continuous_rho {s : ℝ} (hs : 2 ≤ s) : Continuous (rho s) :=
  (continuous_abs.rpow_const fun _ => Or.inr (by linarith)).mul continuous_id

lemma abs_rho {s : ℝ} (hs : 2 ≤ s) (q : ℝ) : |rho s q| = |q| ^ (s - 1) := by
  unfold rho
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg q) _),
    show s - 1 = (s - 2) + 1 by ring, Real.rpow_add_one' (abs_nonneg q) (by linarith)]

lemma rho_mul_self {s : ℝ} (hs : 2 ≤ s) (q : ℝ) : rho s q * q = |q| ^ s := by
  unfold rho
  have h1 : q * q = |q| ^ (2 : ℝ) := by rw [Real.rpow_two, sq_abs]; ring
  have hne : s - 2 + 2 ≠ 0 := by
    have : (0 : ℝ) < s - 2 + 2 := by linarith
    exact this.ne'
  calc |q| ^ (s - 2) * q * q = |q| ^ (s - 2) * (q * q) := by ring
    _ = |q| ^ (s - 2) * |q| ^ (2 : ℝ) := by rw [h1]
    _ = |q| ^ (s - 2 + 2) := (Real.rpow_add' (abs_nonneg q) hne).symm
    _ = |q| ^ s := by congr 1; ring

/-- **Tangent line** of the convex function `|x|^s` at `q`. -/
lemma tangent_ineq {s : ℝ} (hs : 2 ≤ s) (x q : ℝ) :
    s * rho s q * x - (s - 1) * |q| ^ s ≤ |x| ^ s := by
  have hs1 : 1 < s := by linarith
  have hs0 : (0 : ℝ) < s := by linarith
  have hs1' : (0 : ℝ) < s - 1 := by linarith
  have hconj : s.HolderConjugate (s / (s - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hs1).2 rfl
  have hy := Real.young_inequality_of_nonneg (abs_nonneg x)
    (Real.rpow_nonneg (abs_nonneg q) (s - 1)) hconj
  have e1 : (|q| ^ (s - 1)) ^ (s / (s - 1)) = |q| ^ s := by
    rw [← Real.rpow_mul (abs_nonneg q)]
    congr 1
    field_simp
  rw [e1] at hy
  have e3 : s * (|x| ^ s / s + |q| ^ s / (s / (s - 1))) = |x| ^ s + (s - 1) * |q| ^ s := by
    field_simp
  have hy' : s * (|x| * |q| ^ (s - 1)) ≤ |x| ^ s + (s - 1) * |q| ^ s := by
    rw [← e3]
    exact mul_le_mul_of_nonneg_left hy hs0.le
  have h3 : rho s q * x ≤ |q| ^ (s - 1) * |x| := by
    calc rho s q * x ≤ |rho s q * x| := le_abs_self _
      _ = |q| ^ (s - 1) * |x| := by rw [abs_mul, abs_rho hs]
  nlinarith [mul_le_mul_of_nonneg_left h3 hs0.le]

lemma tangent_eq {s : ℝ} (hs : 2 ≤ s) (x : ℝ) :
    s * rho s x * x - (s - 1) * |x| ^ s = |x| ^ s := by
  have := rho_mul_self hs x
  calc s * rho s x * x - (s - 1) * |x| ^ s = s * (rho s x * x) - (s - 1) * |x| ^ s := by ring
    _ = |x| ^ s := by rw [this]; ring

/-- clamp -/
lemma abs_clamp_le_abs {n : ℝ} (hn : 0 ≤ n) (x : ℝ) : |max (min x n) (-n)| ≤ |x| :=
  abs_le.2 ⟨le_max_of_le_left (le_min (neg_abs_le x) (by linarith [abs_nonneg x])),
    max_le ((min_le_left _ _).trans (le_abs_self x)) (by linarith [abs_nonneg x])⟩

lemma abs_clamp_le_bound {n : ℝ} (hn : 0 ≤ n) (x : ℝ) : |max (min x n) (-n)| ≤ n :=
  abs_le.2 ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith)⟩

lemma clamp_eq_self {n x : ℝ} (h : |x| ≤ n) : max (min x n) (-n) = x := by
  have h' := abs_le.1 h
  rw [min_eq_left h'.2, max_eq_left h'.1]

lemma clamp_sub_sq_le {n : ℝ} (hn : 0 ≤ n) (x : ℝ) : (max (min x n) (-n) - x) ^ 2 ≤ x ^ 2 := by
  rcases le_total x n with h1 | h1
  · rw [min_eq_left h1]
    rcases le_total (-n) x with h2 | h2
    · rw [max_eq_left h2, sub_self]
      nlinarith [sq_nonneg x]
    · rw [max_eq_right h2]
      nlinarith [mul_nonneg hn (by linarith : 0 ≤ -(n + 2 * x))]
  · rw [min_eq_right h1, max_eq_left (by linarith)]
    nlinarith [mul_nonneg hn (by linarith : 0 ≤ 2 * x - n)]

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

/-- For bounded `Ψ`: `|S_t Ψ|^s ≤ S_t (|Ψ|^s)` a.e. (Jensen for the positive unital map `S_t`). -/
theorem rpow_Sfun_le_Sfun_rpow_bdd {eC : ℕ → Torus d → ℝ} (hac : mu ≪ volume)
    (hca : volume ≪ mu) (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) {a : ℝ} (ha : 0 < a) (hrls : ENNReal.ofReal a ≤ rLS mu)
    (hlam0 : lam 0 = 0) {s : ℝ} (hs : 2 ≤ s) {t : ℝ} (ht : 0 ≤ t) {Ψ : Config N d → ℝ}
    (hΨ : MemLp Ψ 2 (Q mu N)) {K : ℝ} (hK : ∀ X, |Ψ X| ≤ K) :
    ∀ᵐ X ∂(Q mu N), |Sfun hb t Ψ X| ^ s ≤ Sfun hb t (fun X => |Ψ X| ^ s) X := by
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hφmem : MemLp (fun X => |Ψ X| ^ s) 2 (Q mu N) := by
    refine MemLp.of_bound ((continuous_abs_rpow hs0).comp_aestronglyMeasurable
      hΨ.aestronglyMeasurable) (K ^ s) (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hK X) hs0
  have hq : ∀ q : ℚ, ∀ᵐ X ∂(Q mu N),
      s * rho s (q : ℝ) * Sfun hb t Ψ X - (s - 1) * |(q : ℝ)| ^ s ≤
        Sfun hb t (fun X => |Ψ X| ^ s) X := by
    intro q
    have hg := Sfun_affine hb hlam0 ht hφmem hΨ 1 (-(s * rho s (q : ℝ)))
      ((s - 1) * |(q : ℝ)| ^ s)
    have hgmem : MemLp (fun X => 1 * |Ψ X| ^ s + (-(s * rho s (q : ℝ))) * Ψ X +
        (s - 1) * |(q : ℝ)| ^ s) 2 (Q mu N) :=
      ((hφmem.const_mul 1).add (hΨ.const_mul _)).add (memLp_const _)
    have hnn : 0 ≤ᵐ[Q mu N] (fun X => 1 * |Ψ X| ^ s + (-(s * rho s (q : ℝ))) * Ψ X +
        (s - 1) * |(q : ℝ)| ^ s) :=
      Filter.Eventually.of_forall fun X => by
        show (0 : ℝ) ≤ 1 * |Ψ X| ^ s + (-(s * rho s (q : ℝ))) * Ψ X + (s - 1) * |(q : ℝ)| ^ s
        have := tangent_ineq hs (Ψ X) (q : ℝ)
        linarith
    have hpos := Sfun_nonneg_ae hac hca hb hC1 hae ha hrls hlam0 ht hgmem hnn
    filter_upwards [hpos, hg] with X h1 h2
    have h1' : (0 : ℝ) ≤ Sfun hb t (fun X => 1 * |Ψ X| ^ s + (-(s * rho s (q : ℝ))) * Ψ X +
        (s - 1) * |(q : ℝ)| ^ s) X := h1
    rw [h2] at h1'
    linarith
  have hall := ae_all_iff.2 hq
  filter_upwards [hall] with X hX
  have hclosed : IsClosed {r : ℝ | s * rho s r * Sfun hb t Ψ X - (s - 1) * |r| ^ s ≤
      Sfun hb t (fun X => |Ψ X| ^ s) X} :=
    isClosed_le (((continuous_const.mul (continuous_rho hs)).mul continuous_const).sub
      (continuous_const.mul (continuous_abs_rpow hs0))) continuous_const
  have h' : s * rho s (Sfun hb t Ψ X) * Sfun hb t Ψ X - (s - 1) * |Sfun hb t Ψ X| ^ s ≤
      Sfun hb t (fun X => |Ψ X| ^ s) X :=
    isClosed_property (Rat.denseRange_cast (𝕜 := ℝ)) hclosed (fun q => hX q) (Sfun hb t Ψ X)
  rwa [tangent_eq hs] at h'

/-- **(M3) for bounded `Ψ`.** -/
theorem eLpNorm_Sfun_le_bdd {eC : ℕ → Torus d → ℝ} (hac : mu ≪ volume)
    (hca : volume ≪ mu) (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) {a : ℝ} (ha : 0 < a) (hrls : ENNReal.ofReal a ≤ rLS mu)
    (hlam0 : lam 0 = 0) {s : ℝ} (hs : 2 ≤ s) {t : ℝ} (ht : 0 ≤ t) {Ψ : Config N d → ℝ}
    (hΨ : MemLp Ψ 2 (Q mu N)) {K : ℝ} (hK : ∀ X, |Ψ X| ≤ K) :
    eLpNorm (Sfun hb t Ψ) (ENNReal.ofReal s) (Q mu N) ≤
      eLpNorm Ψ (ENNReal.ofReal s) (Q mu N) := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hp0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.2 hs0).ne'
  have hptop : ENNReal.ofReal s ≠ ∞ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal s).toReal = s := ENNReal.toReal_ofReal hs0.le
  have hS := Sfun_memLp hb t hΨ
  have hφmem : MemLp (fun X => |Ψ X| ^ s) 2 (Q mu N) := by
    refine MemLp.of_bound ((continuous_abs_rpow hs0.le).comp_aestronglyMeasurable
      hΨ.aestronglyMeasurable) (K ^ s) (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hK X) hs0.le
  have hSφ := Sfun_memLp hb t hφmem
  have hle := rpow_Sfun_le_Sfun_rpow_bdd hac hca hb hC1 hae ha hrls hlam0 hs ht hΨ hK
  have hnnφ : 0 ≤ᵐ[Q mu N] (fun X => |Ψ X| ^ s) :=
    Filter.Eventually.of_forall fun X => Real.rpow_nonneg (abs_nonneg _) _
  have hnnS : 0 ≤ᵐ[Q mu N] Sfun hb t (fun X => |Ψ X| ^ s) :=
    Sfun_nonneg_ae hac hca hb hC1 hae ha hrls hlam0 ht hφmem hnnφ
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hS.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hΨ.aestronglyMeasurable, hpr]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  have e1 : ∀ x : ℝ, ‖x‖ₑ ^ s = ENNReal.ofReal (|x| ^ s) := fun x => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg x) hs0.le]
  simp_rw [e1]
  calc ∫⁻ X, ENNReal.ofReal (|Sfun hb t Ψ X| ^ s) ∂(Q mu N)
      ≤ ∫⁻ X, ENNReal.ofReal (Sfun hb t (fun X => |Ψ X| ^ s) X) ∂(Q mu N) :=
        lintegral_mono_ae (hle.mono fun X hX => ENNReal.ofReal_le_ofReal hX)
    _ = ENNReal.ofReal (∫ X, Sfun hb t (fun X => |Ψ X| ^ s) X ∂(Q mu N)) :=
        (ofReal_integral_eq_lintegral_ofReal (hSφ.integrable one_le_two) hnnS).symm
    _ = ENNReal.ofReal (∫ X, |Ψ X| ^ s ∂(Q mu N)) := by
        rw [integral_Sfun_eq hb hlam0 ht hφmem]
    _ = ∫⁻ X, ENNReal.ofReal (|Ψ X| ^ s) ∂(Q mu N) :=
        ofReal_integral_eq_lintegral_ofReal (hφmem.integrable one_le_two) hnnφ

/-- **(M3) The `L^s` contraction (P5)**, `2 ≤ s < ∞`: for `Ψ ∈ L²` (no `L^s` hypothesis is needed:
if `Ψ ∉ L^s` the right-hand side is `∞`). -/
theorem eLpNorm_Sfun_le_rpow {eC : ℕ → Torus d → ℝ} (hac : mu ≪ volume)
    (hca : volume ≪ mu) (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) {a : ℝ} (ha : 0 < a) (hrls : ENNReal.ofReal a ≤ rLS mu)
    (hlam0 : lam 0 = 0) {s : ℝ} (hs : 2 ≤ s) {t : ℝ} (ht : 0 ≤ t) {Ψ : Config N d → ℝ}
    (hΨ : MemLp Ψ 2 (Q mu N)) :
    eLpNorm (Sfun hb t Ψ) (ENNReal.ofReal s) (Q mu N) ≤
      eLpNorm Ψ (ENNReal.ofReal s) (Q mu N) := by
  have hS := Sfun_memLp hb t hΨ
  -- truncations
  set Ψn : ℕ → Config N d → ℝ := fun n X => max (min (Ψ X) (n : ℝ)) (-(n : ℝ)) with hΨn
  have hcont : ∀ n : ℕ, Continuous (fun x : ℝ => max (min x (n : ℝ)) (-(n : ℝ))) := fun n =>
    (continuous_id.min continuous_const).max continuous_const
  have hΨn_meas : ∀ n, AEStronglyMeasurable (Ψn n) (Q mu N) := fun n =>
    (hcont n).comp_aestronglyMeasurable hΨ.aestronglyMeasurable
  have hΨn_bdd : ∀ n X, |Ψn n X| ≤ (n : ℝ) := fun n X =>
    abs_clamp_le_bound (Nat.cast_nonneg n) (Ψ X)
  have hΨn_mem : ∀ n, MemLp (Ψn n) 2 (Q mu N) := fun n =>
    MemLp.of_bound (hΨn_meas n) (n : ℝ)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact hΨn_bdd n X)
  have hA : ∀ n, eLpNorm (Sfun hb t (Ψn n)) (ENNReal.ofReal s) (Q mu N) ≤
      eLpNorm Ψ (ENNReal.ofReal s) (Q mu N) := fun n =>
    (eLpNorm_Sfun_le_bdd hac hca hb hC1 hae ha hrls hlam0 hs ht (hΨn_mem n) (hΨn_bdd n)).trans
      (eLpNorm_mono (hΨn_meas n) fun X => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        exact abs_clamp_le_abs (Nat.cast_nonneg n) (Ψ X))
  -- `L²` convergence of the truncations
  have hI : Tendsto (fun n : ℕ => ∫ X, (Ψn n X - Ψ X) ^ 2 ∂(Q mu N)) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := Q mu N)
      (F := fun (n : ℕ) (X : Config N d) => (Ψn n X - Ψ X) ^ 2) (f := fun _ => (0 : ℝ))
      (fun X => Ψ X ^ 2)
      (fun n => (((hΨn_mem n).sub hΨ).integrable_sq).aestronglyMeasurable)
      hΨ.integrable_sq
      (fun n => Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact clamp_sub_sq_le (Nat.cast_nonneg n) (Ψ X))
      (Filter.Eventually.of_forall fun X => ?_)
    · simpa using h
    · refine tendsto_const_nhds.congr' ?_
      refine Filter.eventually_atTop.2 ⟨⌈|Ψ X|⌉₊, fun n hn => ?_⟩
      have hle : |Ψ X| ≤ (n : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.2 hn)
      show (0 : ℝ) = (max (min (Ψ X) (n : ℝ)) (-(n : ℝ)) - Ψ X) ^ 2
      rw [clamp_eq_self hle]
      simp
  have hconv : Tendsto (fun n : ℕ => eLpNorm (fun X => Ψn n X - Ψ X) 2 (Q mu N)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal
        (Real.sqrt (∫ X, (Ψn n X - Ψ X) ^ 2 ∂(Q mu N)))) atTop
        (𝓝 (ENNReal.ofReal (Real.sqrt 0))) :=
      ENNReal.tendsto_ofReal ((Real.continuous_sqrt.tendsto 0).comp hI)
    simp only [Real.sqrt_zero, ENNReal.ofReal_zero] at h1
    refine Tendsto.congr (fun n => ?_) h1
    exact (eLpNorm_two_eq_ofReal_sqrt ((hΨn_mem n).sub hΨ)).symm
  have hconvS : Tendsto (fun n : ℕ => eLpNorm (Sfun hb t (Ψn n) - Sfun hb t Ψ) 2 (Q mu N))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
      (fun n => zero_le) (fun n => ?_)
    exact eLpNorm_Sfun_sub_le hb hlam0 ht (hΨn_mem n) hΨ
  have hmeas : TendstoInMeasure (Q mu N) (fun n => Sfun hb t (Ψn n)) atTop (Sfun hb t Ψ) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hconvS
  obtain ⟨ns, hns, hae'⟩ := hmeas.exists_seq_tendsto_ae
  exact MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := fun i => Sfun hb t (Ψn (ns i)))
    (Filter.Eventually.of_forall fun i => hA (ns i))
    (fun i => (Sfun_memLp hb t (hΨn_mem (ns i))).aestronglyMeasurable)
    hS.aestronglyMeasurable hae'

/-- **(M3)** with the `L^s` hypothesis: `S_t` maps `L² ∩ L^s` into `L^s`, contractively. -/
theorem eLpNorm_Sfun_le_rpow' {eC : ℕ → Torus d → ℝ} (hac : mu ≪ volume)
    (hca : volume ≪ mu) (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) {a : ℝ} (ha : 0 < a) (hrls : ENNReal.ofReal a ≤ rLS mu)
    (hlam0 : lam 0 = 0) {s : ℝ} (hs : 2 ≤ s) {t : ℝ} (ht : 0 ≤ t) {Ψ : Config N d → ℝ}
    (hΨ : MemLp Ψ 2 (Q mu N)) (hΨs : MemLp Ψ (ENNReal.ofReal s) (Q mu N)) :
    MemLp (Sfun hb t Ψ) (ENNReal.ofReal s) (Q mu N) ∧
      eLpNorm (Sfun hb t Ψ) (ENNReal.ofReal s) (Q mu N) ≤
        eLpNorm Ψ (ENNReal.ofReal s) (Q mu N) := by
  have h := eLpNorm_Sfun_le_rpow hac hca hb hC1 hae ha hrls hlam0 hs ht hΨ
  exact ⟨h.trans_lt hΨs, h⟩

end M3

end SharpLSI.FL.Spectral

end
