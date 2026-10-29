import SharpSymmetricLSI.Paper.AppAEDI4

/-!
# Lemma A.1: (4.8), (4.9), (4.10) for every mild probability solution

The constructed solution satisfies (4.8) (`LinMild.edi_ereal`) and (4.9) (`lip_bound_linMild`).
Every mild probability solution agrees with it a.e. at every time (`appAMild_unique`), and `F`, `D`
and `d_Lip` are a.e.-invariant, so (4.8)–(4.9) hold for it; (4.10) follows (`decay_tail_of_EDI`).
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

namespace LinMild

variable {ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ} {A : ℝ}

/-- **(4.8) for the constructed solution.** -/
theorem edi_ereal (hyp : Hyp V W KV KW)
    (h : LinMild ρ₀ ρ (fun u y k => modFlux V W (ρ u) y k) A)
    (hpos : ∀ t, 0 ≤ t → ∀ᵐ x ∂haar d, 0 ≤ ρ t x) (hmass : ∀ t, 0 ≤ t → ∫ x, ρ t x ∂haar d = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    freeEnergy V W (densMeasure (ρ t)) +
        ((∫⁻ u in Icc s t, dissipation V W (ρ u) : ℝ≥0∞) : EReal) ≤
      freeEnergy V W (densMeasure (ρ s)) := by
  obtain ⟨K, hK0, hK⟩ := h.bdd t
  have ht0 : 0 ≤ t := hs.trans hst
  obtain ⟨hX, hx⟩ := h.edi_real hyp hpos hmass hs hst
  have eI : ∫⁻ u in Icc s t, dissipation V W (ρ u) = ∫⁻ u in Ioc s t, dissipation V W (ρ u) :=
    (setLIntegral_congr Ioc_ae_eq_Icc).symm
  rw [eI, freeEnergy_eq_limEK0 hyp (h.measurable_section t) (hK t ⟨ht0, le_rfl⟩) (hpos t ht0)
      (hmass t ht0),
    freeEnergy_eq_limEK0 hyp (h.measurable_section s) (hK s ⟨hs, hst⟩) (hpos s hs) (hmass s hs),
    ← EReal.coe_ennreal_toReal hX, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

end LinMild

/-- **Lemma A.1, (4.8)–(4.10)** for every mild probability solution. -/
theorem appAMild_evolution (hyp : Hyp V W KV KW) {ρ₀ : Torus d → ℝ} (hm : Measurable ρ₀)
    (h0 : ∀ x, 0 ≤ ρ₀ x) (h1 : ∫ x, ρ₀ x ∂haar d = 1) (hb : ∃ B, ∀ x, ρ₀ x ≤ B)
    {η : ℝ → Torus d → ℝ} (hη : AppAMild V W ρ₀ η) :
    (∀ s t, 0 ≤ s → s ≤ t →
      freeEnergy V W (densMeasure (η t)) +
          ((∫⁻ u in Icc s t, dissipation V W (η u) : ℝ≥0∞) : EReal) ≤
        freeEnergy V W (densMeasure (η s))) ∧
    (∀ s t, 0 ≤ s → s ≤ t →
      ENNReal.ofReal (dLipM (densMeasure (η s)) (densMeasure (η t))) ≤
        ∫⁻ u in Icc s t, dissipation V W (η u) ^ (1 / 2 : ℝ)) ∧
    (0 < rStar V W → ∀ t, 0 ≤ t →
      gap V W (densMeasure (η t)) ≤
        gap V W (densMeasure (η 0)) * ((Real.exp (-2 * (rStar V W).toReal * t) : ℝ) : EReal) ∧
      ∫⁻ u in Ioi t, dissipation V W (η u) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (Real.sqrt (2 / (rStar V W).toReal)) *
          (gap V W (densMeasure (η t))).toENNReal ^ (1 / 2 : ℝ)) := by
  obtain ⟨ρ, A, hL, hρ⟩ := exists_appAMild_linMild hyp hm h0 h1 hb
  have hpos : ∀ t, 0 ≤ t → ∀ᵐ x ∂haar d, 0 ≤ ρ t x := fun t ht => (hρ.prob t ht).1
  have hmass : ∀ t, 0 ≤ t → ∫ x, ρ t x ∂haar d = 1 := fun t ht => (hρ.prob t ht).2
  have hae : ∀ u, 0 ≤ u → η u =ᵐ[haar d] ρ u := fun u hu => appAMild_unique hyp hη hρ hu
  have hD : ∀ u, 0 ≤ u → dissipation V W (η u) = dissipation V W (ρ u) := fun u hu =>
    dissipation_congr_ae (hae u hu)
  have hM : ∀ u, 0 ≤ u → densMeasure (η u) = densMeasure (ρ u) := fun u hu =>
    densMeasure_congr_ae (hae u hu)
  have hI : ∀ s t, 0 ≤ s → ∀ F : ℝ≥0∞ → ℝ≥0∞,
      ∫⁻ u in Icc s t, F (dissipation V W (η u)) = ∫⁻ u in Icc s t, F (dissipation V W (ρ u)) :=
    fun s t hs F => setLIntegral_congr_fun measurableSet_Icc fun u hu => by
      rw [hD u (hs.trans hu.1)]
  have h48 : ∀ s t, 0 ≤ s → s ≤ t →
      freeEnergy V W (densMeasure (η t)) +
          ((∫⁻ u in Icc s t, dissipation V W (η u) : ℝ≥0∞) : EReal) ≤
        freeEnergy V W (densMeasure (η s)) := fun s t hs hst => by
    rw [hM t (hs.trans hst), hM s hs, hI s t hs (fun x => x)]
    exact hL.edi_ereal hyp hpos hmass hs hst
  refine ⟨h48, fun s t hs hst => ?_, ?_⟩
  · rw [hM s hs, hM t (hs.trans hst), hI s t hs (fun x => x ^ (1 / 2 : ℝ))]
    exact lip_bound_linMild hyp hL hpos hmass hs hst
  · obtain ⟨B, hB⟩ := hb
    have hF0 : freeEnergy V W (densMeasure (η 0)) ≠ ⊤ := by
      rw [hη.init, freeEnergy_eq_limEK0 hyp hm (K := B) (fun x => by rw [abs_of_nonneg (h0 x)]; exact hB x)
        (Eventually.of_forall h0) h1]
      exact EReal.coe_ne_top _
    exact decay_tail_of_EDI hyp hη.prob hF0 h48

end SharpLSI
