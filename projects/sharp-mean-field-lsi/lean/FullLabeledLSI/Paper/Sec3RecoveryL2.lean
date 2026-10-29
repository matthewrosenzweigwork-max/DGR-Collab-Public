import SharpSymmetricLSI.Paper.UpperApprox3
import FullLabeledLSI.Defs.F01_Species

/-!
# Proposition 3.2 regularization: species dissipation formula and `L²`-norm convergence
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `D_a = ∑ₖ ∫ |2Gₖ + √ρₐ (∇ₖV + bₖ[ρ̄])|²` for any weak gradient `G` of `√ρₐ`. -/
theorem speciesDiss_eq_of (hyp : Hyp V W KV KW) {ρa ρb : Torus d → ℝ}
    (hρbi : Integrable ρb (haar d))
    (hH1 : MemH1 (haar d) (fun x => Real.sqrt (ρa x))) {G : Torus d → Fin d → ℝ}
    (hG : IsWeakGrad (fun x => Real.sqrt (ρa x)) G) :
    speciesDiss V W ρa ρb = ∑ k, ∫⁻ x, ‖2 * G x k + Real.sqrt (ρa x) *
      (lipGrad V x k + bForceL W ρb x k)‖ₑ ^ 2 ∂haar d := by
  have hVw := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp (W := W))
  have hVC := hVw.add (isWeakGrad_convDens' hyp hρbi (W := W))
  unfold speciesDiss
  rw [if_pos ⟨hH1, ⟨_, hVC⟩⟩]
  have hm : ∀ k, AEMeasurable (fun x => ‖2 * G x k + Real.sqrt (ρa x) *
      (lipGrad V x k + bForceL W ρb x k)‖ₑ ^ 2) (haar d) := fun k =>
    ((((hG.aestronglyMeasurable_grad k).const_mul 2).add
      (hG.aestronglyMeasurable_fun.mul ((measurable_lipGrad hyp.continuous_V k).add
        (measurable_bForceL' hyp hρbi k)).aestronglyMeasurable)).enorm).pow_const 2
  rw [← lintegral_finsetSum' _ fun k _ => hm k]
  refine lintegral_congr_ae ?_
  filter_upwards [weakGrad_ae_eq hG, weakGrad_ae_eq hVC] with x h1 h2
  rw [h1, h2, ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
  exact Finset.sum_congr rfl fun k _ => ofReal_sq_eq_enorm_sq _

/-- `L²` convergence gives convergence of the squared norms. -/
theorem tendsto_lintegral_enorm_sq_of_L2Tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ} (h : L2Tendsto μ f g) (hfm : ∀ j, AEMeasurable (f j) μ)
    (hgm : AEMeasurable g μ) (hg : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ ≠ ⊤) :
    Tendsto (fun j => ∫⁻ x, ‖f j x‖ₑ ^ 2 ∂μ) atTop (𝓝 (∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ)) := by
  have hn : ∀ {u : α → ℝ}, AEMeasurable u μ → eLpNorm u 2 μ ^ 2 = ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ := by
    intro u hu
    have := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := u) (p := (2 : NNReal)) (by norm_num)
    simpa using this hu.aestronglyMeasurable
  set e : ℕ → ℝ≥0∞ := fun j => eLpNorm (fun x => f j x - g x) 2 μ with he
  set a : ℕ → ℝ≥0∞ := fun j => eLpNorm (f j) 2 μ with ha
  set b : ℝ≥0∞ := eLpNorm g 2 μ with hb
  have hel : Tendsto e atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => (∫⁻ x, ‖f j x - g x‖ₑ ^ 2 ∂μ) ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp h
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
      exact this
    refine h1.congr fun j => ?_
    have := hn ((hfm j).sub hgm)
    simp only [Pi.sub_apply] at this
    rw [← this]
    have key : ∀ y : ℝ≥0∞, (y ^ 2) ^ (1 / (2 : ℝ)) = y := fun y => by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    exact key _
  have hbt : b ≠ ⊤ := by
    intro hbt
    apply hg
    rw [← hn hgm]
    have : eLpNorm g 2 μ = ⊤ := hbt
    rw [this]; simp
  have hup : ∀ j, a j ≤ b + e j := fun j => by
    have := eLpNorm_add_le (μ := μ) (p := 2) (f := g) (g := fun x => f j x - g x) (by norm_num)
    have e1 : (g + fun x => f j x - g x) = f j := by funext x; simp
    rw [e1] at this
    exact this
  have hlo : ∀ j, b ≤ a j + e j := fun j => by
    have := eLpNorm_add_le (μ := μ) (p := 2) (f := f j) (g := fun x => g x - f j x) (by norm_num)
    have e1 : (f j + fun x => g x - f j x) = g := by funext x; simp
    rw [e1] at this
    have e2 : eLpNorm (fun x => g x - f j x) 2 μ = e j := by
      rw [he]; simp only
      rw [← eLpNorm_neg]; congr 1; funext x; simp
    rw [e2] at this
    exact this
  have hlim : Tendsto a atTop (𝓝 b) := by
    have hu : Tendsto (fun j => b + e j) atTop (𝓝 b) := by simpa using hel.const_add b
    have hl : Tendsto (fun j => b - e j) atTop (𝓝 b) := by
      simpa using ENNReal.Tendsto.sub tendsto_const_nhds hel (Or.inl hbt)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu (fun j => ?_) (fun j => hup j)
    exact tsub_le_iff_right.2 (hlo j)
  have hc : Tendsto (fun j => a j ^ 2) atTop (𝓝 (b ^ 2)) :=
    ((ENNReal.continuous_pow 2).tendsto b).comp hlim
  have e1 : ∀ j, a j ^ 2 = ∫⁻ x, ‖f j x‖ₑ ^ 2 ∂μ := fun j => hn (hfm j)
  have e2 : b ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ := hn hgm
  simp only [e1, e2] at hc
  exact hc

end SharpLSI.FL
