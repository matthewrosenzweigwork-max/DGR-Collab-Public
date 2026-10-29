import FullLabeledLSI.Paper.Sec5MFB
import FullLabeledLSI.Paper.Sec5MFC

/-!
# Mean-field step D: the per-level inequality (M6, M7)
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} {β : Type*}

/-! ### G. (M6) the per-level mean-field inequality -/

/-- A bounded `H¹` density is integrable (its integral is `1 ≠ 0`). -/
theorem avgDensR_integrable {ρ : Torus d → ℝ} {g : Torus d → Fin d → ℝ} {c C : ℝ}
    (h : IsBddH1Dens ρ g c C) : Integrable ρ (haar d) := by
  by_contra hni
  have := h.int_one
  rw [integral_undef hni] at this
  exact zero_ne_one this


/-- **(M6) The per-level mean-field inequality** (ENNReal form; handles negative left side via
`ofReal`).  For `r₀ ≤ r_ms`, a minimizer `μ`, and the conditional laws `ρᵢ` (`i ∈ R`) with
`ρ̄ = avgDensR R ρ`:

`2 r₀ ( (1/n) ∑ H(ρᵢ|μ) + J(ρ̄) ) ≤ (1/n) ∑ ∫ ρᵢ |gᵢ/ρᵢ + ∇Φ_μ + B_{ρ̄}|² dm`.

Proof: `F := finFamily R ρ` admissible (M2); (M1) gives `ofReal (2 r₀ G_θ.toReal) ≤ msDiss F`;
`G_θ.toReal` by (M5R); `msDiss F = (1/n)∑ speciesDiss (ρᵢ) ρ̄` by `msDiss_finFamily`; then (M3)
(`ρ̄` measurable/integrable by `IsBddH1Dens.avg`) and (M4). -/
theorem two_r_meanfield_le (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hrr : ENNReal.ofReal r₀ ≤ rMs V W)
    {R : Finset β} (hR : R.Nonempty)
    {ρ : β → Torus d → ℝ} {g : β → Torus d → Fin d → ℝ} {c C : ℝ}
    (h : ∀ i ∈ R, IsBddH1Dens (ρ i) (g i) c C) :
    ENNReal.ofReal (2 * r₀ *
        ((R.card : ℝ)⁻¹ * ∑ i ∈ R, (klDiv (densMeasure (ρ i)) (μ : Measure (Torus d))).toReal +
          Jfun W μ (densMeasure (avgDensR R ρ)))) ≤
      ENNReal.ofReal ((R.card : ℝ)⁻¹) *
        ∑ i ∈ R, elDiss V W (μ : Measure (Torus d)) (ρ i) (g i) (avgDensR R ρ) := by
  have hbar := IsBddH1Dens.avg hR h
  have hF := finFamily_admissible hR h
  have h1 := two_r_ms_gap_le (V := V) (W := W) hr₀ hrr hF
  rw [msGap_finFamily_eq hyp hμ hR h, EReal.toReal_coe, msDiss_finFamily] at h1
  refine h1.trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [speciesDiss_eq_tiltDiss hyp (h i hi) hbar.meas (avgDensR_integrable hbar),
    tiltDiss_eq_elDiss hyp hμ (ρ i) (g i) hbar.meas (fun x => hbar.pos.le.trans (hbar.ge x))
      hbar.int_one]

/-- **(M6R) Real form** of (M6) (all terms finite; the left side is `≥ 0` in fact, since
`G_θ ≥ 0`, but this is not needed):
`2 r₀ ((1/n)∑ H(ρᵢ|μ) + J(ρ̄)) ≤ (1/n) ∑ (∫ ρᵢ |gᵢ/ρᵢ + ∇Φ_μ + B_{ρ̄}|² dm).toReal`. -/
theorem two_r_meanfield_real_le (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hrr : ENNReal.ofReal r₀ ≤ rMs V W)
    {R : Finset β} (hR : R.Nonempty)
    {ρ : β → Torus d → ℝ} {g : β → Torus d → Fin d → ℝ} {c C : ℝ}
    (h : ∀ i ∈ R, IsBddH1Dens (ρ i) (g i) c C) :
    2 * r₀ *
        ((R.card : ℝ)⁻¹ * ∑ i ∈ R, (klDiv (densMeasure (ρ i)) (μ : Measure (Torus d))).toReal +
          Jfun W μ (densMeasure (avgDensR R ρ))) ≤
      (R.card : ℝ)⁻¹ *
        ∑ i ∈ R, (elDiss V W (μ : Measure (Torus d)) (ρ i) (g i) (avgDensR R ρ)).toReal := by
  have hbar := IsBddH1Dens.avg hR h
  have hmain := two_r_meanfield_le hyp hμ hr₀ hrr hR h
  have hfin : ∀ i ∈ R, elDiss V W (μ : Measure (Torus d)) (ρ i) (g i) (avgDensR R ρ) ≠ ⊤ :=
    fun i hi => (elDiss_lt_top hyp hμ (h i hi) hbar.meas
      (fun x => hbar.pos.le.trans (hbar.ge x)) hbar.int_one).ne
  have hne : ENNReal.ofReal ((R.card : ℝ)⁻¹) *
      ∑ i ∈ R, elDiss V W (μ : Measure (Torus d)) (ρ i) (g i) (avgDensR R ρ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.2 hfin)
  have h2 := (ENNReal.ofReal_le_iff_le_toReal hne).1 hmain
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 (Nat.cast_nonneg _)),
    ENNReal.toReal_sum hfin] at h2
  exact h2

/-! ### H. (M7) averaging over an abstract parameter space (monotonicity wrapper) -/

/-- **(M7, abstract wrapper)**  If the conditional data `R ω, ρ ω, g ω` (`ω = (S, a)` in Section 5)
satisfy the hypotheses of (M6) for every (or `P`-a.e.) `ω`, with uniform constants, then the mean-field
inequality integrates over `ω` against any measure `P`.  No measurability is needed
(`lintegral_mono`/`lintegral_mono_ae`).  The identification of the two sides with the Section 5
quantities is the T-interface described in the header. -/
theorem lintegral_two_r_meanfield_le (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hrr : ENNReal.ofReal r₀ ≤ rMs V W)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : Ω → Finset β) (hR : ∀ ω, (R ω).Nonempty)
    (ρ : Ω → β → Torus d → ℝ) (g : Ω → β → Torus d → Fin d → ℝ) {c C : ℝ}
    (h : ∀ᵐ ω ∂P, ∀ i ∈ R ω, IsBddH1Dens (ρ ω i) (g ω i) c C) :
    ∫⁻ ω, ENNReal.ofReal (2 * r₀ *
        (((R ω).card : ℝ)⁻¹ * ∑ i ∈ R ω,
            (klDiv (densMeasure (ρ ω i)) (μ : Measure (Torus d))).toReal +
          Jfun W μ (densMeasure (avgDensR (R ω) (ρ ω))))) ∂P ≤
      ∫⁻ ω, ENNReal.ofReal (((R ω).card : ℝ)⁻¹) *
        ∑ i ∈ R ω, elDiss V W (μ : Measure (Torus d)) (ρ ω i) (g ω i) (avgDensR (R ω) (ρ ω)) ∂P := by
  exact lintegral_mono_ae (h.mono fun ω hω =>
    two_r_meanfield_le hyp hμ hr₀ hrr (hR ω) hω)


end SharpLSI.FL
