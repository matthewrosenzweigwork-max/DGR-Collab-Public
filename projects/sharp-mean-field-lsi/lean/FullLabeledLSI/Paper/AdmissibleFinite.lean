import FullLabeledLSI.Defs.F01_Species
import SharpSymmetricLSI.Paper.PartitionLimit

/-!
# Finite gap and dissipation of admissible families

Adaptation of `SharpLSI.dissipation_lt_top_of_memH1` / `gap_lt_top_aux` (AdmFinite) to the
multi-species quantities of F1: the species term `speciesDiss V W ρₐ ρ̄` is finite for
`√ρₐ ∈ H¹(m)`, `ρₐ ≥ 0` integrable and `ρ̄` integrable, because the force `V + W*ρ̄` is Lipschitz.
-/

noncomputable section
open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-- `speciesDiss V W ρa ρbar < ⊤` for `√ρa ∈ H¹`, `ρa ≥ 0` a probability density and `ρbar`
integrable (the force `V + W*ρbar` is Lipschitz under (1.2)). -/
theorem speciesDiss_lt_top {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) {ρa ρbar : Torus d → ℝ} (h0 : ∀ x, 0 ≤ ρa x)
    (h1 : ∫ x, ρa x ∂haar d = 1) (hH : MemH1 (haar d) (fun x => Real.sqrt (ρa x)))
    (hρbar : Integrable ρbar (haar d)) : speciesDiss V W ρa ρbar < ⊤ := by
  have hρi := integrable_of_integral_eq_one' h1
  obtain ⟨LC, hLC⟩ := lipschitz_convDens hyp hρbar (W := W)
  have hLV := lipschitz_of_coordSemiconvex hyp.continuous_V hyp.KV_nonneg (coordSemiconvex_V hyp)
  set Φ : Torus d → ℝ := fun x => V x + convDens W ρbar x
  have hΦL : LipschitzWith (_ + LC) (Φ ∘ liftT) := hLV.add hLC
  have hΦc : Continuous Φ :=
    hyp.continuous_V.add (lipschitzWith_of_liftT hLC).continuous
  have hΦw := isWeakGrad_lipGrad hΦc hΦL
  set CΦ : ℝ := ((Real.toNNReal (KV * Fintype.card (Fin d) / 2) + LC : ℝ≥0) : ℝ)
  have hΦb : ∀ y k, |lipGrad Φ y k| ≤ CΦ := fun y k => abs_lipGrad_le hΦL y k
  unfold speciesDiss
  rw [if_pos ⟨hH, ⟨_, hΦw⟩⟩]
  obtain ⟨hw, -, hgL2⟩ := hH
  set g := weakGrad (fun y => Real.sqrt (ρa y))
  have hsq : Integrable (fun x => sqNorm (g x)) (haar d) := by
    refine hgL2.integrable_sq.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [Real.sq_sqrt (sqNorm_nonneg _)]
  set B : Torus d → ℝ := fun x => 8 * sqNorm (g x) + 2 * (Fintype.card (Fin d) * CΦ ^ 2) * ρa x
  have hBi : Integrable B (haar d) := (hsq.const_mul 8).add (hρi.const_mul _)
  have hle : ∀ᵐ x ∂haar d, ENNReal.ofReal (∑ k, (2 * g x k + Real.sqrt (ρa x) * weakGrad Φ x k) ^ 2)
      ≤ ENNReal.ofReal (B x) := by
    filter_upwards [weakGrad_ae_eq hΦw] with x hx
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hx]
    simp only [B, sqNorm]
    rw [Finset.mul_sum, mul_comm (2 * _ : ℝ) (ρa x)]
    have hcard : (Fintype.card (Fin d) : ℝ) * CΦ ^ 2 = ∑ _k : Fin d, CΦ ^ 2 := by simp
    rw [hcard, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have hG : lipGrad Φ x k ^ 2 ≤ CΦ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hΦb x k) 2
    have hs : Real.sqrt (ρa x) ^ 2 = ρa x := Real.sq_sqrt (h0 x)
    nlinarith [sq_nonneg (2 * g x k - Real.sqrt (ρa x) * lipGrad Φ x k), h0 x,
      mul_le_mul_of_nonneg_left hG (h0 x)]
  calc _ ≤ ∫⁻ x, ENNReal.ofReal (B x) ∂haar d := lintegral_mono_ae hle
    _ < ⊤ := hBi.lintegral_lt_top

/-- The average density of an admissible family is integrable. -/
theorem bar_integrable {F : Family d} (hF : F.Admissible) : Integrable F.bar (haar d) := by
  have : F.bar = fun x => ∑ a, F.θ a * F.ρ a x := rfl
  rw [this]
  exact integrable_finsetSum _ fun a _ =>
    (integrable_of_integral_eq_one' (hF.2.2 a).2.1).const_mul _

/-- Admissible families have finite dissipation. -/
theorem msDiss_lt_top_of_admissible {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) {F : Family d} (hF : F.Admissible) : msDiss V W F < ⊤ := by
  unfold msDiss
  refine ENNReal.sum_lt_top.2 fun a _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  obtain ⟨h0, h1, hH⟩ := hF.2.2 a
  exact speciesDiss_lt_top hyp h0 h1 hH (bar_integrable hF)

/-- Admissible families have finite gap, bounded below. -/
theorem msGap_bounds_of_admissible {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) {F : Family d} (hF : F.Admissible) :
    msGap V W F < ⊤ ∧ ⊥ < msGap V W F := by
  have hK : (∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (haar d) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun a _ => by
      obtain ⟨h0, h1, hH⟩ := hF.2.2 a
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (klDiv_densMeasure_ne_top_of_memH1 h0 h1 hH)
  set S : ℝ≥0∞ := ∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (haar d)
  have hS : ((S : ℝ≥0∞) : EReal) = ((S.toReal : ℝ) : EReal) := by
    rw [← EReal.coe_ennreal_toReal hK]
  have hmsGap : msGap V W F = ((S.toReal + (potE V (densMeasure F.bar) +
      interE W (densMeasure F.bar) (densMeasure F.bar) / 2) - (Fstar V W).toReal : ℝ) : EReal) := by
    unfold msGap
    rw [hS]
    nth_rewrite 1 [Fstar_eq_coe hyp]
    simp [EReal.coe_add, EReal.coe_sub]
  rw [hmsGap]
  exact ⟨EReal.coe_lt_top _, EReal.bot_lt_coe _⟩

end SharpLSI.FL
