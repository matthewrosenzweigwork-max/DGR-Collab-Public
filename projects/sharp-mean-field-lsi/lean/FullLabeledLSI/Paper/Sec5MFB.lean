import FullLabeledLSI.Paper.Sec5MFA

/-!
# Mean-field step B: species dissipation and Euler-Lagrange rewriting (M3, M4)
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} {β : Type*}

/-! ### C. (M3) the species dissipation in drift form -/

/-- `∫ ρₐ |gₐ/ρₐ + ∇V + b_{ρb}|² dm` (the integral `∫ ρₐ |∇ log ρₐ + ∇V + ∇(W*ρb)|²`), `ℝ≥0∞`-valued. -/
noncomputable def tiltDiss (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ)
    (ρa : Torus d → ℝ) (ga : Torus d → Fin d → ℝ) (ρb : Torus d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (ρa x * ∑ k, (ga x k / ρa x + lipGrad V x k + bForceL W ρb x k) ^ 2)
    ∂haar d

/-- **(M3) Species dissipation formula** (analogue of `dissipation_eq_of_ge`, Defective8:96, with the
drift taken from a *different* density `ρb`): for `ρa` a bounded `H¹` density with weak gradient `ga`
and `ρb` measurable and integrable (a probability density suffices),
`speciesDiss V W ρa ρb = ∫ ρa |ga/ρa + ∇V + b_{ρb}|² dm`.  The hypotheses on `ρb` are exactly what
`isWeakGrad_convDens` (ProductDissipation:90) needs; `HasWeakGrad (V + W*ρb)` holds with gradient
`lipGrad V + bForceL W ρb`. -/
theorem speciesDiss_eq_tiltDiss (hyp : Hyp V W KV KW) {ρa : Torus d → ℝ}
    {ga : Torus d → Fin d → ℝ} {c C : ℝ} (ha : IsBddH1Dens ρa ga c C) {ρb : Torus d → ℝ}
    (hbm : Measurable ρb) (hbi : Integrable ρb (haar d)) :
    speciesDiss V W ρa ρb = tiltDiss V W ρa ga ρb := by
  have hρ0 : ∀ x, 0 < ρa x := fun x => ha.pos.trans_le (ha.ge x)
  have hρi : Integrable ρa (haar d) := Integrable.of_bound ha.meas.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_pos (hρ0 x)]; exact ha.le x)
  have hgi : ∀ k, Integrable (fun x => ga x k) (haar d) := fun k =>
    (ha.grad_L2 k).integrable one_le_two
  have hS := isWeakGrad_sqrt_of_ge ha.grad hρi hgi ha.pos ha.ge
  have hVw := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp (W := W))
  have hCw := isWeakGrad_convDens hyp hbm hbi (W := W)
  have hVCw := hVw.add hCw
  unfold speciesDiss tiltDiss
  rw [if_pos ⟨ha.memH1_sqrt, ⟨_, hVCw⟩⟩]
  refine lintegral_congr_ae ?_
  filter_upwards [weakGrad_ae_eq hS, weakGrad_ae_eq hVCw] with x h1 h2
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h1, h2]
  have hs0 : 0 < Real.sqrt (ρa x) := Real.sqrt_pos.mpr (hρ0 x)
  have hsq : Real.sqrt (ρa x) ^ 2 = ρa x := Real.sq_sqrt (hρ0 x).le
  have key : ∀ (a gg t : ℝ), 0 < t →
      (2 * (gg / (2 * t)) + t * a) ^ 2 = t ^ 2 * (gg / t ^ 2 + a) ^ 2 := by
    intro a gg t ht
    field_simp
  rw [key _ _ _ hs0, hsq]
  ring

/-- Reindexing of `msDiss` for the conditional family. -/
theorem msDiss_finFamily (R : Finset β) (ρ : β → Torus d → ℝ) :
    msDiss V W (finFamily R ρ) =
      ∑ i ∈ R, ENNReal.ofReal ((R.card : ℝ)⁻¹) * speciesDiss V W (ρ i) (avgDensR R ρ) := by
  unfold msDiss
  rw [finFamily_bar]
  exact finFamily_sum R ρ
    (fun r => ENNReal.ofReal ((R.card : ℝ)⁻¹) * speciesDiss V W r (avgDensR R ρ))

/-! ### D. (M4) Euler-Lagrange rewriting of the drift -/

/-- The mean force `B_{ρ̄}(x)_k = ∫ b̃(x,y)_k ρ̄(y) dy` (`b̃ = bfixF` is the centered force
`∇₁K`; cf. `condB`, Defective18:55, which is the case `ρ̄ = condDens`). -/
noncomputable def bMean (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (ρbar : Torus d → ℝ) (x : Torus d) (k : Fin d) : ℝ :=
  ∫ y, bfixF W μ x y k * ρbar y ∂haar d

/-- `∫ ρₐ |gₐ/ρₐ + ∇Φ_μ + B_{ρ̄}|² dm` with `Φ_μ = V + W*μ` (the integral of the squared EL score
`∇ log(ρₐ/μ) + B`). -/
noncomputable def elDiss (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (ρa : Torus d → ℝ) (ga : Torus d → Fin d → ℝ) (ρbar : Torus d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (ρa x * ∑ k, (ga x k / ρa x + lipGrad (PhiMF V W μ) x k +
    bMean W μ ρbar x k) ^ 2) ∂haar d

/-- **(M4, pointwise form)** `∇V + b_{ρ̄} = ∇Φ_μ + B_{ρ̄}` a.e., for every probability density `ρ̄`
(no regularity beyond measurability).  Proof: `lipGrad_PhiMF_ae` (`∇Φ_μ = ∇V + β`, `β = b_μ`) and
`bForceL_sub_eq` (`b_{ρ̄} - β = ∫ b̃(·,y) ρ̄(y) dy`). -/
theorem ae_force_eq_el (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {ρbar : Torus d → ℝ} (hm : Measurable ρbar) (h0 : ∀ x, 0 ≤ ρbar x)
    (h1 : ∫ x, ρbar x ∂haar d = 1) :
    ∀ᵐ x ∂haar d, ∀ k, lipGrad V x k + bForceL W ρbar x k =
      lipGrad (PhiMF V W (μ : Measure (Torus d))) x k +
        bMean W (μ : Measure (Torus d)) ρbar x k := by
  have hac := minimizer_ac hyp hμ
  filter_upwards [lipGrad_PhiMF_ae hyp hac (μ := (μ : Measure (Torus d)))] with x hΦ k
  have hB := bForceL_sub_eq hyp (μ := (μ : Measure (Torus d))) hm h0 h1 x k
  unfold bMean
  rw [hΦ k]
  linarith

/-- **(M4)** `∫ ρₐ |ga/ρₐ + ∇V + b_{ρ̄}|² = ∫ ρₐ |ga/ρₐ + ∇Φ_μ + B_{ρ̄}|²` for *arbitrary* `ρₐ, ga`
(an a.e. rewriting of the integrand; `lintegral_congr_ae`). -/
theorem tiltDiss_eq_elDiss (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) (ρa : Torus d → ℝ) (ga : Torus d → Fin d → ℝ)
    {ρbar : Torus d → ℝ} (hm : Measurable ρbar) (h0 : ∀ x, 0 ≤ ρbar x)
    (h1 : ∫ x, ρbar x ∂haar d = 1) :
    tiltDiss V W ρa ga ρbar = elDiss V W (μ : Measure (Torus d)) ρa ga ρbar := by
  unfold tiltDiss elDiss
  refine lintegral_congr_ae ?_
  filter_upwards [ae_force_eq_el hyp hμ hm h0 h1] with x hx
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  have := hx k
  rw [show ga x k / ρa x + lipGrad V x k + bForceL W ρbar x k =
    ga x k / ρa x + lipGrad (PhiMF V W (μ : Measure (Torus d))) x k +
      bMean W (μ : Measure (Torus d)) ρbar x k by linarith]

/-- Finiteness: for bounded `H¹` data and a bounded probability `ρ̄`, `elDiss < ⊤`
(from `speciesDiss_lt_top` of AdmissibleFinite, M3 and M4). -/
theorem elDiss_lt_top (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {ρa : Torus d → ℝ} {ga : Torus d → Fin d → ℝ} {c C : ℝ}
    (ha : IsBddH1Dens ρa ga c C) {ρbar : Torus d → ℝ} (hm : Measurable ρbar)
    (h0 : ∀ x, 0 ≤ ρbar x) (h1 : ∫ x, ρbar x ∂haar d = 1) :
    elDiss V W (μ : Measure (Torus d)) ρa ga ρbar < ⊤ := by
  have hbi : Integrable ρbar (haar d) := integrable_of_integral_eq_one' h1
  rw [← tiltDiss_eq_elDiss hyp hμ ρa ga hm h0 h1, ← speciesDiss_eq_tiltDiss hyp ha hm hbi]
  exact speciesDiss_lt_top hyp (fun x => (ha.pos.trans_le (ha.ge x)).le) ha.int_one
    ha.memH1_sqrt hbi


end SharpLSI.FL
