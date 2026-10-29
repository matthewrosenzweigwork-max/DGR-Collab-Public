import SharpSymmetricLSI.Paper.R36Meas1
import SharpSymmetricLSI.Paper.AppAEDI4
import SharpSymmetricLSI.Statements.R36_Lemma_A_1

/-!
# R36 measurability (2): `u ↦ D(ρ_u)` is a.e.-measurable for mild solutions

On `(0, T]` the Fisher rate `Q₀(u) = ∫ |J_u|²/ρ_u` is the a.e. limit of the integrable rates
`R_{δₙ}(ρ_u)` (shifted by the integrable `B`), and Fatou bounds `∫ Q₀ < ∞`, so `Q₀ < ∞` a.e.
By `dissipation_eq_fisher`, `D(ρ_u) = Q₀(u)` a.e. (`LinMild.aemeasurable_dissipation`).
Uniqueness transfers this to every mild solution on `(0, ∞)` (`aemeasurable_dissipation_mild`).
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

namespace LinMild

variable {ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ} {A : ℝ}

theorem aemeasurable_dissipation (hyp : Hyp V W KV KW)
    (h : LinMild ρ₀ ρ (fun u y k => modFlux V W (ρ u) y k) A)
    (hpos : ∀ t, 0 ≤ t → ∀ᵐ x ∂haar d, 0 ≤ ρ t x) (hmass : ∀ t, 0 ≤ t → ∫ x, ρ t x ∂haar d = 1)
    {T : ℝ} (hT : 0 ≤ T) :
    AEMeasurable (fun u => dissipation V W (ρ u)) (volume.restrict (Ioc 0 T)) := by
  obtain ⟨K, hK0, hK⟩ := h.bdd T
  set N : ℝ → Torus d → Fin d → ℝ := fun u y k => modFlux V W (ρ u) y k with hNdef
  obtain ⟨C₁, C₂, hC₁, hC₂, hTd⟩ := tendsto_limRate_delta hyp K (V := V) (W := W)
  set B : ℝ → ℝ := fun u => C₁ * (dirE ρ u).toReal + C₂ + 1 with hBdef
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) T)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hBi : IntegrableOn B (Ioc 0 T) :=
    (((integrable_toReal_of_lintegral_ne_top h.measurable_dirE.aemeasurable
      (h.lintegral_dirE_lt_top hK0 hK hT).ne).const_mul C₁).add (integrable_const C₂)).add
      (integrable_const 1)
  set δn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδn : ∀ n, 0 < δn n := fun n => by positivity
  set R : ℕ → ℝ → ℝ := fun n u => limRate V W (δn n) (ρ u) (N u)
  have hRi : ∀ n, IntegrableOn (R n) (Ioc 0 T) := fun n =>
    h.integrableOn_limRate hyp (hδn n) hK0 hK hT
  have hρm : ∀ u, Measurable (ρ u) := fun u => h.measurable_section u
  have hid : ∀ n, ∫ u in Ioc 0 T, R n u = limEK V W (δn n) (ρ 0) - limEK V W (δn n) (ρ T) :=
    fun n => by
      have h1 := h.delta_identity_st hyp (hδn n) hK0 hK le_rfl hT le_rfl
      rw [limE_eq hyp (hδn n) (hρm T) (hK T ⟨hT, le_rfl⟩) (hmass T hT),
        limE_eq hyp (hδn n) (hρm 0) (hK 0 ⟨le_rfl, hT⟩) (hmass 0 le_rfl)] at h1
      simp only [R]; linarith
  set L := limEK0 V W (ρ 0) - limEK0 V W (ρ T)
  have hL : Tendsto (fun n => ∫ u in Ioc 0 T, R n u) atTop (𝓝 L) := by
    simp_rw [hid]
    exact (tendsto_limEK hyp (hρm 0) (hK 0 ⟨le_rfl, hT⟩) (hpos 0 le_rfl)).sub
      (tendsto_limEK hyp (hρm T) (hK T ⟨hT, le_rfl⟩) (hpos T hT))
  have hgood := h.ae_isWeakGrad hK0 hK hT
  set Q0 : ℝ → ℝ≥0∞ := fun u => ∫⁻ x, ENNReal.ofReal (∑ j, (weakGrad (ρ u) x j +
    ρ u x * aD V W (ρ u) x j) ^ 2) / ENNReal.ofReal (ρ u x) ∂haar d
  have hpt : ∀ᵐ u ∂(volume.restrict (Ioc 0 T)), (∀ n, 0 ≤ R n u + B u) ∧
      Tendsto (fun n => ENNReal.ofReal (R n u + B u)) atTop (𝓝 (Q0 u + ENNReal.ofReal (B u))) ∧
      (Q0 u ≠ ⊤ → dissipation V W (ρ u) = Q0 u) := by
    filter_upwards [hgood, ae_restrict_mem measurableSet_Ioc] with u hgu hu
    obtain ⟨g, hg, hg2, -, hgE⟩ := hgu
    have hu0 : 0 ≤ u := hu.1.le
    have hu' : u ∈ Icc 0 T := ⟨hu0, hu.2⟩
    have hE : ∑ j, ∫ x, g x j ^ 2 = (dirE ρ u).toReal := by
      rw [← hgE, ENNReal.toReal_ofReal (Finset.sum_nonneg fun j _ => integral_nonneg fun x => sq_nonneg _)]
    have hBu : C₁ * (∑ j, ∫ x, g x j ^ 2) + C₂ ≤ B u := by rw [hE]; simp only [hBdef]; linarith
    obtain ⟨h1, h2⟩ := hTd (hρm u) (hK u hu') (hpos u hu0) (hmass u hu0) hg hg2 (B u) hBu
    refine ⟨h1, h2, fun hQ => ?_⟩
    have hw := appA_isWeakGrad_weakGrad ⟨g, hg⟩
    have hwg : weakGrad (ρ u) =ᵐ[volume] g := appA_weakGrad_ae_eq hg
    exact dissipation_eq_fisher hyp (hρm u) (hK u hu') (hpos u hu0) hw
      (fun j => (hg2 j).ae_eq (hwg.mono fun x hx => (congrFun hx j).symm)) hQ
  have hFm : ∀ n, AEMeasurable (fun u => ENNReal.ofReal (R n u + B u)) (volume.restrict (Ioc 0 T)) :=
    fun n => ((hRi n).aestronglyMeasurable.add hBi.aestronglyMeasurable).aemeasurable.ennreal_ofReal
  have hGm : AEMeasurable (fun u => Q0 u + ENNReal.ofReal (B u)) (volume.restrict (Ioc 0 T)) :=
    aemeasurable_of_tendsto_metrizable_ae' hFm (hpt.mono fun u hu => hu.2.1)
  have hBm : AEMeasurable (fun u => ENNReal.ofReal (B u)) (volume.restrict (Ioc 0 T)) :=
    hBi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hQm : AEMeasurable Q0 (volume.restrict (Ioc 0 T)) :=
    (hGm.sub hBm).congr (Eventually.of_forall fun u =>
      ENNReal.add_sub_cancel_right ENNReal.ofReal_ne_top)
  -- Fatou: `∫ (Q₀ + B) < ∞`
  have hfatou := lintegral_liminf_le' (u := atTop) hFm
  have hrhs : Tendsto (fun n => ∫⁻ u in Ioc 0 T, ENNReal.ofReal (R n u + B u)) atTop
      (𝓝 (ENNReal.ofReal (L + ∫ u in Ioc 0 T, B u))) := by
    have e : ∀ n, ∫⁻ u in Ioc 0 T, ENNReal.ofReal (R n u + B u) =
        ENNReal.ofReal ((∫ u in Ioc 0 T, R n u) + ∫ u in Ioc 0 T, B u) := fun n => by
      rw [← integral_add (hRi n) hBi, ofReal_integral_eq_lintegral_ofReal
        (f := fun u => R n u + B u) ((hRi n).add hBi)]
      filter_upwards [hpt] with u hu
      exact hu.1 n
    simp_rw [e]
    exact ENNReal.tendsto_ofReal (hL.add_const _)
  rw [hrhs.liminf_eq] at hfatou
  have hG : ∫⁻ u in Ioc 0 T, (Q0 u + ENNReal.ofReal (B u)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans (le_of_eq ?_) hfatou)
    refine lintegral_congr_ae ?_
    filter_upwards [hpt] with u hu
    exact hu.2.1.liminf_eq.symm
  have hfin := ae_lt_top' hGm hG
  refine hQm.congr ?_
  filter_upwards [hpt, hfin] with u hu hf
  exact (hu.2.2 (ne_top_of_le_ne_top hf.ne le_self_add)).symm

end LinMild

/-- **`u ↦ D(ρ_u)` is a.e.-measurable on `(0, ∞)`** for every mild solution (R36). -/
theorem aemeasurable_dissipation_mild (hyp : Hyp V W KV KW) {ρ₀ : Torus d → ℝ}
    (hm : Measurable ρ₀) (h0 : ∀ x, 0 ≤ ρ₀ x) (h1 : ∫ x, ρ₀ x ∂haar d = 1)
    (hb : ∃ B, ∀ x, ρ₀ x ≤ B) {ρ : ℝ → Torus d → ℝ} (hρ : IsMildSolution V W ρ₀ ρ) :
    AEMeasurable (fun u => dissipation V W (ρ u)) (volume.restrict (Ioi 0)) := by
  obtain ⟨η, A, hL, hη⟩ := exists_appAMild_linMild hyp hm h0 h1 hb
  have hρ' : AppAMild V W ρ₀ ρ := ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.1, hρ.2.2.2.2⟩
  have hD : ∀ u, 0 ≤ u → dissipation V W (η u) = dissipation V W (ρ u) := fun u hu =>
    dissipation_congr_ae (appAMild_unique hyp hη hρ' hu)
  have hU : Ioi (0 : ℝ) = ⋃ n : ℕ, Ioc 0 (n : ℝ) := by
    ext u
    simp only [mem_Ioi, mem_iUnion, mem_Ioc]
    exact ⟨fun hu => ⟨⌈u⌉₊, hu, Nat.le_ceil u⟩, fun ⟨_, hu, _⟩ => hu⟩
  rw [hU, aemeasurable_iUnion_iff]
  intro n
  refine (hL.aemeasurable_dissipation hyp (fun t ht => (hη.prob t ht).1)
    (fun t ht => (hη.prob t ht).2) (Nat.cast_nonneg n)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  exact hD u hu.1.le

end SharpLSI
