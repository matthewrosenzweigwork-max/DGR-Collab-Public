import SharpSymmetricLSI.Paper.AppARStar3

/-!
# Appendix A.1: restriction of (1.7) to smooth positive densities (assembly)
-/

open MeasureTheory Set Filter Topology InformationTheory
open scoped ENNReal ContDiff

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

namespace H1Dens

variable {ρ : Torus d → ℝ} (h : H1Dens ρ)
include h

/-- Along a subsequence of any positive `s_n → 0`, all the a.e. convergences hold. -/
theorem exists_subseq_good {s : ℕ → ℝ} (hs0 : ∀ n, 0 < s n) (hs : Tendsto s atTop (𝓝[>] 0)) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧
      (∀ᵐ x ∂haar d, Tendsto (fun n => heatT (s (ms n)) ρ x) atTop (𝓝 (ρ x))) ∧
      (∀ᵐ x ∂haar d, ∀ k, Tendsto (fun n => sqrtHeatGrad (s (ms n)) ρ x k) atTop
        (𝓝 (weakGrad (fun z => Real.sqrt (ρ z)) x k))) ∧
      Tendsto (fun n => ∫⁻ x, ‖heatT (s (ms n)) ρ x - ρ x‖ₑ ∂haar d) atTop (𝓝 0) := by
  set g := weakGrad fun z => Real.sqrt (ρ z)
  set f : Option (Option (Fin d)) → Torus d → ℝ := fun i => match i with
    | none => ρ
    | some none => fun y => sqNorm (g y)
    | some (some k) => fun y => 2 * Real.sqrt (ρ y) * g y k with hfdef
  have hf : ∀ i, Integrable (f i) := fun i => match i with
    | none => h.integrable
    | some none => h.integrable_sqNorm
    | some (some k) => h.integrable_flux k
  obtain ⟨ms, hms, hae⟩ := exists_subseq_heatT_ae hf hs0 hs
  have hρae : ∀ᵐ x ∂haar d, Tendsto (fun n => heatT (s (ms n)) ρ x) atTop (𝓝 (ρ x)) :=
    hae.mono fun x hx => hx none
  refine ⟨ms, hms, hρae, ?_, (tendsto_heatT_L1 h.integrable).comp (hs.comp hms.tendsto_atTop)⟩
  exact h.ae_tendsto_sqrtHeatGrad (fun n => hs0 _) hρae (hae.mono fun x hx k => hx (some (some k)))
    (hae.mono fun x hx => hx (some none))

theorem tendsto_dissipation_heatT (hyp : Hyp V W KV KW) :
    Tendsto (fun t => dissipation V W (heatT t ρ)) (𝓝[>] 0) (𝓝 (dissipation V W ρ)) := by
  refine tendsto_nhdsGT_of_subseq fun s hs0 hs => ?_
  obtain ⟨ms, hms, hρae, hgae, hL1⟩ := h.exists_subseq_good hs0 hs
  exact ⟨ms, hms, h.tendsto_dissipation_seq hyp (fun n => hs0 _) hρae hgae hL1⟩

theorem tendsto_gap_heatT (hyp : Hyp V W KV KW) :
    Tendsto (fun t => gap V W (densMeasure (heatT t ρ))) (𝓝[>] 0)
      (𝓝 (gap V W (densMeasure ρ))) := by
  refine tendsto_nhdsGT_of_subseq fun s hs0 hs => ?_
  obtain ⟨ms, hms, hρae, -, hL1⟩ := h.exists_subseq_good hs0 hs
  exact ⟨ms, hms, h.tendsto_gap_seq hyp (fun n => hs0 _) hρae hL1⟩

end H1Dens

theorem rStar_smooth_approx_aux (hyp : Hyp V W KV KW) :
    rStar V W = ⨅ ρ ∈ {ρ | Admissible V W ρ ∧ IsSmoothT ρ ∧ ∀ x, 0 < ρ x},
      dissipation V W ρ / (2 * (gap V W (densMeasure ρ)).toENNReal) ∧
    ∀ ρ, Admissible V W ρ →
      (∀ t : ℝ, 0 < t → IsSmoothT (heatT t ρ) ∧ ∀ x, 0 < heatT t ρ x) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), Admissible V W (heatT t ρ)) ∧
      Tendsto (fun t => dissipation V W (heatT t ρ)) (𝓝[>] 0) (𝓝 (dissipation V W ρ)) ∧
      Tendsto (fun t => gap V W (densMeasure (heatT t ρ))) (𝓝[>] 0)
        (𝓝 (gap V W (densMeasure ρ))) := by
  have key : ∀ ρ, Admissible V W ρ →
      (∀ t : ℝ, 0 < t → IsSmoothT (heatT t ρ) ∧ ∀ x, 0 < heatT t ρ x) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), Admissible V W (heatT t ρ)) ∧
      Tendsto (fun t => dissipation V W (heatT t ρ)) (𝓝[>] 0) (𝓝 (dissipation V W ρ)) ∧
      Tendsto (fun t => gap V W (densMeasure (heatT t ρ))) (𝓝[>] 0)
        (𝓝 (gap V W (densMeasure ρ))) := by
    intro ρ hρ
    have h : H1Dens ρ := ⟨hρ.1, hρ.2.1, hρ.2.2.1⟩
    have hG := h.tendsto_gap_heatT hyp
    refine ⟨fun t ht => ⟨isSmoothT_heatT ht h.integrable, h.heatT_pos ht⟩, ?_,
      h.tendsto_dissipation_heatT hyp, hG⟩
    filter_upwards [hG.eventually (lt_mem_nhds hρ.2.2.2), self_mem_nhdsWithin] with t h1 ht
    have hh := h.heatT_h1Dens (show 0 < t from ht)
    exact ⟨hh.nonneg, hh.one, hh.h1, h1⟩
  refine ⟨le_antisymm ?_ ?_, key⟩
  · exact biInf_mono fun ρ hρ => hρ.1
  · unfold rStar
    refine le_iInf₂ fun ρ hρ => ?_
    have h : H1Dens ρ := ⟨hρ.1, hρ.2.1, hρ.2.2.1⟩
    obtain ⟨hsm, hadm, hD, hG⟩ := key ρ hρ
    have hb0 : 2 * (gap V W (densMeasure ρ)).toENNReal ≠ 0 :=
      mul_ne_zero two_ne_zero (by
        rw [Ne, EReal.toENNReal_eq_zero_iff, not_le]; exact hρ.2.2.2)
    have hden : Tendsto (fun t => 2 * (gap V W (densMeasure (heatT t ρ))).toENNReal) (𝓝[>] 0)
        (𝓝 (2 * (gap V W (densMeasure ρ)).toENNReal)) :=
      ENNReal.Tendsto.const_mul ((EReal.continuous_toENNReal.tendsto _).comp hG)
        (Or.inr ENNReal.ofNat_ne_top)
    have hratio := ENNReal.Tendsto.div hD (Or.inr hb0) hden (Or.inr (h.dissipation_ne_top hyp))
    refine ge_of_tendsto hratio ?_
    filter_upwards [hadm, self_mem_nhdsWithin] with t ht1 ht2
    obtain ⟨hs, hp⟩ := hsm t ht2
    exact iInf₂_le (f := fun ρ (_ : ρ ∈ {ρ | Admissible V W ρ ∧ IsSmoothT ρ ∧ ∀ x, 0 < ρ x}) =>
      dissipation V W ρ / (2 * (gap V W (densMeasure ρ)).toENNReal)) (heatT t ρ) ⟨ht1, hs, hp⟩

end SharpLSI
