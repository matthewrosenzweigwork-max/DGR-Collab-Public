import FullLabeledLSI.Paper.Sec8NoInt4

/-!
# Section 8.5: the closing remark (no interaction)

For `W = 0` and `N ≥ 1`: `r_N^all = r_LS(μ)`, `r_ms = r_LS(μ)` and `r_* = r_LS(μ)`.
-/

open MeasureTheory InformationTheory Filter Topology SharpLSI
open scoped ENNReal

namespace SharpLSI.FL
namespace Sec8

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- A constant `r` with `2 r G_θ ≤ D_θ` for all admissible families is below `r_ms`. -/
theorem le_rMs_of_crit (hd : 1 ≤ d) (hyp : Hyp V W KV KW) {r : ℝ≥0∞}
    (h : ∀ F : Family d, F.Admissible → 2 * r * (msGap V W F).toENNReal ≤ msDiss V W F) :
    r ≤ rMs V W := by
  unfold rMs
  refine le_iInf₂ fun F hF => ?_
  have hpos : 0 < (msGap V W F).toENNReal := EReal.toENNReal_pos_iff.2 hF.2
  have hfin : (msGap V W F).toENNReal ≠ ⊤ :=
    EReal.toENNReal_ne_top_iff.2 (msGap_msDiss_lt_top hd hyp hF.1).1.ne
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hpos.ne'))
    (Or.inl (ENNReal.mul_ne_top (by norm_num) hfin))]
  calc r * (2 * (msGap V W F).toENNReal) = 2 * r * (msGap V W F).toENNReal := by ring
    _ ≤ _ := h F hF.1

section W0

variable (hyp : Hyp V (fun _ _ => (0 : ℝ)) KV KW) {μ : ProbabilityMeasure (Torus d)}
  (hμ : IsMinimizer V (fun _ _ => (0 : ℝ)) μ)
include hyp hμ

theorem w0_crit {r : ℝ≥0∞}
    (hr : ∀ ρ : Torus d → ℝ, (∀ x, 0 ≤ ρ x) → ∫ x, ρ x ∂haar d = 1 →
      MemH1 (haar d) (fun x => Real.sqrt (ρ x)) →
      2 * (r * klDiv (densMeasure ρ) (μ : Measure (Torus d))) ≤
        dissipation V (fun _ _ => (0 : ℝ)) ρ)
    {F : Family d} (hF : F.Admissible) :
    2 * r * (msGap V (fun _ _ => (0 : ℝ)) F).toENNReal ≤ msDiss V (fun _ _ => (0 : ℝ)) F := by
  rw [w0_msGap hyp hμ hF, EReal.toENNReal_coe, msDiss_zero', Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  calc 2 * r * (ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (μ : Measure (Torus d)))
      = ENNReal.ofReal (F.θ a) * (2 * (r * klDiv (densMeasure (F.ρ a)) (μ : Measure (Torus d)))) := by
        ring
    _ ≤ _ := mul_le_mul' le_rfl (hr _ (hF.2.2 a).1 (hF.2.2 a).2.1 (hF.2.2 a).2.2)

theorem w0_rLS_le_rMs (hd : 1 ≤ d) : rLS (μ : Measure (Torus d)) ≤ rMs V (fun _ _ => (0 : ℝ)) :=
  le_rMs_of_crit hd hyp fun F hF => w0_crit hyp hμ
    (fun ρ h0 h1 hH => w0_species_bound hyp hμ h0 h1 hH) hF

theorem w0_rMs_le_rLS : rMs V (fun _ _ => (0 : ℝ)) ≤ rLS (μ : Measure (Torus d)) := by
  refine le_trans ?_ (equilibrium_inf_le_rLS hyp hμ)
  refine le_iInf₂ fun F hF => ?_
  exact iInf₂_le F hF.1

theorem w0_rStar_le_rMs (hd : 1 ≤ d) :
    rStar V (fun _ _ => (0 : ℝ)) ≤ rMs V (fun _ _ => (0 : ℝ)) := by
  refine le_rMs_of_crit hd hyp fun F hF => w0_crit hyp hμ (fun ρ h0 h1 hH => ?_) hF
  by_cases hK : klDiv (densMeasure ρ) (μ : Measure (Torus d)) = 0
  · rw [hK]; simp
  haveI : IsProbabilityMeasure (densMeasure ρ) := isProbabilityMeasure_densMeasure' h0 h1
  have hgap := w0_gap_eq hyp hμ ⟨densMeasure ρ, this⟩
  have hgap' : gap V (fun _ _ => (0 : ℝ)) (densMeasure ρ) =
      ((klDiv (densMeasure ρ) (μ : Measure (Torus d)) : ℝ≥0∞) : EReal) := hgap
  have hpos : 0 < gap V (fun _ _ => (0 : ℝ)) (densMeasure ρ) := by
    rw [hgap']
    exact EReal.coe_ennreal_pos.2 (pos_iff_ne_zero.2 hK)
  have hAd : SharpLSI.Admissible V (fun _ _ => (0 : ℝ)) ρ := ⟨h0, h1, hH, hpos⟩
  have hlt := (SharpLSI.gap_lt_top_of_admissible hyp hAd).1
  rw [hgap'] at hlt
  have hKt : klDiv (densMeasure ρ) (μ : Measure (Torus d)) ≠ ⊤ := fun ht => by
    rw [ht, EReal.coe_ennreal_top] at hlt; exact lt_irrefl _ hlt
  have h1 : rStar V (fun _ _ => (0 : ℝ)) ≤
      dissipation V (fun _ _ => (0 : ℝ)) ρ /
        (2 * (gap V (fun _ _ => (0 : ℝ)) (densMeasure ρ)).toENNReal) := iInf₂_le ρ hAd
  rw [hgap', EReal.toENNReal_coe,
    ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hK))
      (Or.inl (ENNReal.mul_ne_top (by norm_num) hKt))] at h1
  calc 2 * (rStar V (fun _ _ => (0 : ℝ)) * klDiv (densMeasure ρ) (μ : Measure (Torus d)))
      = rStar V (fun _ _ => (0 : ℝ)) * (2 * klDiv (densMeasure ρ) (μ : Measure (Torus d))) := by
        ring
    _ ≤ _ := h1

theorem w0_rMs_eq (hd : 1 ≤ d) : rMs V (fun _ _ => (0 : ℝ)) = rLS (μ : Measure (Torus d)) :=
  le_antisymm (w0_rMs_le_rLS hyp hμ) (w0_rLS_le_rMs hyp hμ hd)

theorem w0_rStar_eq (hd : 1 ≤ d) : rStar V (fun _ _ => (0 : ℝ)) = rLS (μ : Measure (Torus d)) := by
  have h1 := w0_rStar_le_rMs hyp hμ hd
  have h2 := rMs_le_rStar (V := V) (W := fun _ _ => (0 : ℝ))
  rw [← w0_rMs_eq hyp hμ hd]
  exact le_antisymm h1 h2

theorem w0_rAll_eq {N : ℕ} (hN : 1 ≤ N) :
    rAll V (fun _ _ => (0 : ℝ)) N = rLS (μ : Measure (Torus d)) := by
  obtain ⟨c, C, L, hc, hb, hL⟩ := elDens_data hyp hμ
  have hμq : (μ : Measure (Torus d)) = densMeasure (elDens V (fun _ _ => (0 : ℝ)) μ) :=
    minimizer_eq_elDensity hyp hμ
  have hgp := gibbs_zero_eq_pi hyp hμ N
  have hac : (μ : Measure (Torus d)) ≪ volume := by
    have := withDensity_absolutelyContinuous (volume : Measure (Torus d))
      (fun x => ENNReal.ofReal (elDens V (fun _ _ => (0 : ℝ)) (μ : Measure (Torus d)) x))
    rwa [← densMeasure, ← hμq] at this
  refine le_antisymm ?_ (rLS_le_rAll_of_pi hyp hgp hac)
  haveI : IsProbabilityMeasure (densMeasure (elDens V (fun _ _ => (0 : ℝ)) (μ : Measure (Torus d)))) := by
    rw [← hμq]; infer_instance
  have hgp' : gibbs V (fun _ _ => (0 : ℝ)) N = Measure.pi fun _ : Fin N =>
      densMeasure (elDens V (fun _ _ => (0 : ℝ)) (μ : Measure (Torus d))) := by
    rw [hgp]; congr 1; funext _; exact hμq
  have := rAll_le_rLS_of_pi hyp hN hc hb hgp'
  rwa [← hμq] at this

end W0

/-- The closing remark of Section 8. -/
theorem no_interaction_core (hd : 1 ≤ d) (hyp : Hyp V (fun _ _ => (0 : ℝ)) KV KW)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V (fun _ _ => (0 : ℝ)) μ) :
    (∀ N : ℕ, 1 ≤ N → rAll V (fun _ _ => (0 : ℝ)) N = rLS (μ : Measure (Torus d))) ∧
      rMs V (fun _ _ => (0 : ℝ)) = rLS (μ : Measure (Torus d)) ∧
      rStar V (fun _ _ => (0 : ℝ)) = rLS (μ : Measure (Torus d)) :=
  ⟨fun _ hN => w0_rAll_eq hyp hμ hN, w0_rMs_eq hyp hμ hd, w0_rStar_eq hyp hμ hd⟩

end Sec8
end SharpLSI.FL
