import SharpSymmetricLSI.Paper.AppAEDI
import SharpSymmetricLSI.Paper.AppAEvol1
import SharpSymmetricLSI.Paper.ProductEntropy

/-!
# Lemma A.1, (4.8) ⇒ (4.10)

`D`, `G` and the free energy depend only on the a.e. class of a density; `D ≥ 2 r_* G` for every
probability density (definition (1.7)); hence the energy–dissipation inequality (4.8) along a
family of probability densities gives (4.10) (`AppAEDI`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section Congr

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hasWeakGrad_congr_ae {u v : UnitAddTorus ι → ℝ} (h : u =ᵐ[volume] v)
    (hu : HasWeakGrad u) : HasWeakGrad v :=
  ⟨_, appA_isWeakGrad_congr_ae hu.choose_spec h⟩

theorem appA_weakGrad_congr_ae {u v : UnitAddTorus ι → ℝ} (h : u =ᵐ[volume] v)
    (hu : HasWeakGrad u) : weakGrad u =ᵐ[volume] weakGrad v :=
  weakGrad_ae_unique (appA_isWeakGrad_congr_ae (appA_isWeakGrad_weakGrad hu) h)
    (appA_isWeakGrad_weakGrad (hasWeakGrad_congr_ae h hu))

theorem appA_memH1_congr_ae {u v : UnitAddTorus ι → ℝ} (h : u =ᵐ[volume] v) (hu : MemH1 volume u) :
    MemH1 volume v := by
  refine ⟨hasWeakGrad_congr_ae h hu.1, hu.2.1.ae_eq h, hu.2.2.ae_eq ?_⟩
  filter_upwards [appA_weakGrad_congr_ae h hu.1] with x hx
  rw [hx]

end Congr

theorem sqrt_congr_ae {ρ ρ' : Torus d → ℝ} (h : ρ =ᵐ[haar d] ρ') :
    (fun x => Real.sqrt (ρ x)) =ᵐ[haar d] fun x => Real.sqrt (ρ' x) :=
  h.mono fun x hx => by simp only [hx]

theorem dissipation_congr_ae {ρ ρ' : Torus d → ℝ} (h : ρ =ᵐ[haar d] ρ') :
    dissipation V W ρ = dissipation V W ρ' := by
  have hs := sqrt_congr_ae h
  have hc : convDens W ρ = convDens W ρ' := convDens_congr_ae h
  unfold dissipation
  rw [hc]
  by_cases hH : MemH1 (haar d) (fun x => Real.sqrt (ρ x))
  · have hH' := appA_memH1_congr_ae hs hH
    by_cases hV : HasWeakGrad (fun x => V x + convDens W ρ' x)
    · rw [if_pos ⟨hH, hV⟩, if_pos ⟨hH', hV⟩]
      refine lintegral_congr_ae ?_
      filter_upwards [appA_weakGrad_congr_ae hs hH.1, hs] with x h1 h2
      rw [h1, h2]
    · rw [if_neg fun h => hV h.2, if_neg fun h => hV h.2]
  · have hH' : ¬ MemH1 (haar d) (fun x => Real.sqrt (ρ' x)) := fun h' =>
      hH (appA_memH1_congr_ae (hs.symm) h')
    rw [if_neg fun h => hH h.1, if_neg fun h => hH' h.1]

theorem densMeasure_congr_ae {ρ ρ' : Torus d → ℝ} (h : ρ =ᵐ[haar d] ρ') :
    densMeasure ρ = densMeasure ρ' := by
  unfold densMeasure
  exact withDensity_congr_ae (h.mono fun x hx => by simp only [hx])

/-- The nonnegative representative. -/
theorem posPart_ae_eq {ρ : Torus d → ℝ} (h0 : ∀ᵐ x ∂haar d, 0 ≤ ρ x) :
    ρ =ᵐ[haar d] fun x => max (ρ x) 0 :=
  h0.mono fun x hx => (max_eq_left hx).symm

theorem isProbabilityMeasure_densMeasure_ae {ρ : Torus d → ℝ} (h0 : ∀ᵐ x ∂haar d, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar d = 1) : IsProbabilityMeasure (densMeasure ρ) := by
  rw [densMeasure_congr_ae (posPart_ae_eq h0)]
  refine isProbabilityMeasure_densMeasure' (fun x => le_max_right _ _) ?_
  rw [← integral_congr_ae (posPart_ae_eq h0)]; exact h1

theorem Fstar_le_freeEnergy {ρ : Torus d → ℝ} (h0 : ∀ᵐ x ∂haar d, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar d = 1) : Fstar V W ≤ freeEnergy V W (densMeasure ρ) := by
  have := isProbabilityMeasure_densMeasure_ae h0 h1
  exact iInf_le (fun μ : ProbabilityMeasure (Torus d) => freeEnergy V W μ) ⟨densMeasure ρ, this⟩

theorem ereal_sub_coe_ne_top {a : EReal} {c : ℝ} (h : a ≠ ⊤) : a - c ≠ ⊤ := by
  induction a using EReal.rec with
  | bot => simp
  | top => exact absurd rfl h
  | coe x => rw [← EReal.coe_sub]; exact EReal.coe_ne_top _

theorem ereal_sub_coe_add_le {a b I : EReal} {c : ℝ} (h : a + I ≤ b) : a - c + I ≤ b - c := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← EReal.coe_neg, add_right_comm]
  exact add_le_add h le_rfl

theorem ereal_sub_coe_nonneg {a : EReal} {c : ℝ} (h : (c : EReal) ≤ a) : 0 ≤ a - c := by
  induction a using EReal.rec with
  | bot => simp at h
  | top => simp
  | coe x =>
    rw [← EReal.coe_sub]
    exact_mod_cast sub_nonneg.2 (by exact_mod_cast h)

/-- **(PL)**: `2 r_* G(ρ) ≤ D(ρ)` for every probability density with finite gap. -/
theorem rStar_mul_gap_le {ρ : Torus d → ℝ} (h0 : ∀ᵐ x ∂haar d, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar d = 1) (hG : gap V W (densMeasure ρ) ≠ ⊤) :
    2 * rStar V W * (gap V W (densMeasure ρ)).toENNReal ≤ dissipation V W ρ := by
  set ρ' : Torus d → ℝ := fun x => max (ρ x) 0
  have he := posPart_ae_eq h0
  rw [densMeasure_congr_ae he, dissipation_congr_ae (V := V) he] at *
  by_cases hG0 : (gap V W (densMeasure ρ')).toENNReal = 0
  · rw [hG0, mul_zero]; exact zero_le
  by_cases hD : dissipation V W ρ' = ⊤
  · rw [hD]; exact le_top
  have hH1 : MemH1 (haar d) (fun x => Real.sqrt (ρ' x)) := by
    by_contra hn
    exact hD (by unfold dissipation; rw [if_neg fun h => hn h.1])
  have hpos : 0 < gap V W (densMeasure ρ') := by
    have h' := hG0
    rw [EReal.toENNReal_eq_zero_iff, not_le] at h'; exact h'
  have hadm : Admissible V W ρ' := ⟨fun x => le_max_right _ _,
    by rw [← integral_congr_ae he]; exact h1, hH1, hpos⟩
  have hR : rStar V W ≤ dissipation V W ρ' / (2 * (gap V W (densMeasure ρ')).toENNReal) :=
    iInf₂_le (f := fun ρ (_ : ρ ∈ {ρ | Admissible V W ρ}) =>
      dissipation V W ρ / (2 * (gap V W (densMeasure ρ)).toENNReal)) ρ' hadm
  have h2G0 : 2 * (gap V W (densMeasure ρ')).toENNReal ≠ 0 := mul_ne_zero two_ne_zero hG0
  have h2Gt : 2 * (gap V W (densMeasure ρ')).toENNReal ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (by simpa [EReal.toENNReal_eq_top_iff] using hG)
  calc 2 * rStar V W * (gap V W (densMeasure ρ')).toENNReal
      = rStar V W * (2 * (gap V W (densMeasure ρ')).toENNReal) := by ring
    _ ≤ dissipation V W ρ' / (2 * (gap V W (densMeasure ρ')).toENNReal) *
          (2 * (gap V W (densMeasure ρ')).toENNReal) := by gcongr
    _ = dissipation V W ρ' := ENNReal.div_mul_cancel h2G0 h2Gt

/-- **(4.8) ⇒ (4.10)** for a family of probability densities. -/
theorem decay_tail_of_EDI (hyp : Hyp V W KV KW) {ρ : ℝ → Torus d → ℝ}
    (hprob : ∀ t, 0 ≤ t → (∀ᵐ x ∂haar d, 0 ≤ ρ t x) ∧ ∫ x, ρ t x ∂haar d = 1)
    (hF0 : freeEnergy V W (densMeasure (ρ 0)) ≠ ⊤)
    (h48 : ∀ s t, 0 ≤ s → s ≤ t →
      freeEnergy V W (densMeasure (ρ t)) +
          ((∫⁻ u in Icc s t, dissipation V W (ρ u) : ℝ≥0∞) : EReal) ≤
        freeEnergy V W (densMeasure (ρ s))) :
    0 < rStar V W → ∀ t, 0 ≤ t →
      gap V W (densMeasure (ρ t)) ≤
          gap V W (densMeasure (ρ 0)) * ((Real.exp (-2 * (rStar V W).toReal * t) : ℝ) : EReal) ∧
        ∫⁻ u in Ioi t, dissipation V W (ρ u) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (Real.sqrt (2 / (rStar V W).toReal)) *
            (gap V W (densMeasure (ρ t))).toENNReal ^ (1 / 2 : ℝ) := by
  intro hR t ht
  set c := (Fstar V W).toReal
  have hFs : Fstar V W = (c : EReal) := Fstar_eq_coe hyp
  have hgap : ∀ u, gap V W (densMeasure (ρ u)) = freeEnergy V W (densMeasure (ρ u)) - c :=
    fun u => by unfold gap; rw [hFs]
  have hnn : ∀ u, 0 ≤ u → 0 ≤ gap V W (densMeasure (ρ u)) := fun u hu => by
    rw [hgap]; exact ereal_sub_coe_nonneg (hFs ▸ Fstar_le_freeEnergy (hprob u hu).1 (hprob u hu).2)
  have hFle : ∀ u, 0 ≤ u → freeEnergy V W (densMeasure (ρ u)) ≤ freeEnergy V W (densMeasure (ρ 0)) :=
    fun u hu => le_trans (le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _)) (h48 0 u le_rfl hu)
  have hfin : ∀ u, 0 ≤ u → gap V W (densMeasure (ρ u)) ≠ ⊤ := fun u hu => by
    rw [hgap]
    have : freeEnergy V W (densMeasure (ρ u)) ≠ ⊤ := ne_top_of_le_ne_top hF0 (hFle u hu)
    exact ereal_sub_coe_ne_top this
  set G : ℝ → ℝ≥0∞ := fun u => (gap V W (densMeasure (ρ u))).toENNReal with hGdef
  have hGc : ∀ u, 0 ≤ u → ((G u : ℝ≥0∞) : EReal) = gap V W (densMeasure (ρ u)) := fun u hu =>
    EReal.coe_toENNReal (hnn u hu)
  have hGfin : ∀ u, 0 ≤ u → G u ≠ ⊤ := fun u hu => by
    simpa [hGdef, EReal.toENNReal_eq_top_iff] using hfin u hu
  have h48G : ∀ s t, 0 ≤ s → s ≤ t →
      G t + ∫⁻ u in Icc s t, dissipation V W (ρ u) ≤ G s := by
    intro s t hs hst
    rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_ennreal_add, hGc t (hs.trans hst),
      hGc s hs, hgap, hgap]
    exact ereal_sub_coe_add_le (h48 s t hs hst)
  have hPL : ∀ u, 0 ≤ u → 2 * rStar V W * G u ≤ dissipation V W (ρ u) := fun u hu =>
    rStar_mul_gap_le (hprob u hu).1 (hprob u hu).2 (hfin u hu)
  obtain ⟨h1, h2⟩ := edi_decay_and_tail hR hGfin h48G hPL ht
  refine ⟨?_, h2⟩
  rw [← hGc t ht, ← hGc 0 le_rfl]
  calc ((G t : ℝ≥0∞) : EReal) ≤ ((G 0 * ENNReal.ofReal (Real.exp (-2 * (rStar V W).toReal * t))
        : ℝ≥0∞) : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.2 h1
    _ = _ := by
        rw [EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left (Real.exp_pos _).le]

end SharpLSI
