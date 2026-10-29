import SharpSymmetricLSI.Paper.AppAEDI3

/-!
# The energy–dissipation inequality (3): Fatou

For the constructed solution and `0 ≤ s ≤ t`:
`∫_{(s,t]} D(ρ_u) du ≤ E^K_0(ρ_s) - E^K_0(ρ_t)` (`LinMild.edi_real`), by Fatou in time applied to
`R_{δₙ}(ρ_u) + B(u) → ∫|J_u|²/ρ_u + B(u) ≥ D(ρ_u) + B(u)`.
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

namespace LinMild

variable {ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ} {A : ℝ}

theorem edi_real (hyp : Hyp V W KV KW)
    (h : LinMild ρ₀ ρ (fun u y k => modFlux V W (ρ u) y k) A)
    (hpos : ∀ t, 0 ≤ t → ∀ᵐ x ∂haar d, 0 ≤ ρ t x) (hmass : ∀ t, 0 ≤ t → ∫ x, ρ t x ∂haar d = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫⁻ u in Ioc s t, dissipation V W (ρ u)) ≠ ⊤ ∧
      (∫⁻ u in Ioc s t, dissipation V W (ρ u)).toReal ≤ limEK0 V W (ρ s) - limEK0 V W (ρ t) := by
  obtain ⟨K, hK0, hK⟩ := h.bdd t
  have ht0 : 0 ≤ t := hs.trans hst
  rcases hst.lt_or_eq with hlt | heq
  swap
  · subst heq; simp
  set N : ℝ → Torus d → Fin d → ℝ := fun u y k => modFlux V W (ρ u) y k with hNdef
  obtain ⟨C₁, C₂, hC₁, hC₂, hT⟩ := tendsto_limRate_delta hyp K (V := V) (W := W)
  set B : ℝ → ℝ := fun u => C₁ * (dirE ρ u).toReal + C₂ + 1 with hBdef
  have hB1 : ∀ u, 1 ≤ B u := fun u => by
    have : 0 ≤ C₁ * (dirE ρ u).toReal := mul_nonneg hC₁ ENNReal.toReal_nonneg
    simp only [hBdef]; linarith
  haveI : IsFiniteMeasure (volume.restrict (Ioc s t)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hBi : IntegrableOn B (Ioc s t) := by
    have hfin : ∫⁻ u in Ioc s t, dirE ρ u ≠ ⊤ :=
      (lt_of_le_of_lt (lintegral_mono_set (Ioc_subset_Ioc hs le_rfl))
        (h.lintegral_dirE_lt_top hK0 hK ht0)).ne
    exact (((integrable_toReal_of_lintegral_ne_top h.measurable_dirE.aemeasurable hfin).const_mul
      C₁).add (integrable_const C₂)).add (integrable_const 1)
  set δn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδn : ∀ n, 0 < δn n := fun n => by positivity
  set R : ℕ → ℝ → ℝ := fun n u => limRate V W (δn n) (ρ u) (N u)
  have hRi : ∀ n, IntegrableOn (R n) (Ioc s t) := fun n =>
    (h.integrableOn_limRate hyp (hδn n) hK0 hK ht0).mono_set (Ioc_subset_Ioc hs le_rfl)
  -- the identity at level `δₙ`
  have hρm : ∀ u, Measurable (ρ u) := fun u => h.measurable_section u
  have hid : ∀ n, ∫ u in Ioc s t, R n u = limEK V W (δn n) (ρ s) - limEK V W (δn n) (ρ t) := fun n => by
    have h1 := h.delta_identity_st hyp (hδn n) hK0 hK hs hst le_rfl
    rw [limE_eq hyp (hδn n) (hρm t) (hK t ⟨ht0, le_rfl⟩) (hmass t ht0),
      limE_eq hyp (hδn n) (hρm s) (hK s ⟨hs, hst⟩) (hmass s hs)] at h1
    simp only [R]; linarith
  set L := limEK0 V W (ρ s) - limEK0 V W (ρ t)
  have hL : Tendsto (fun n => ∫ u in Ioc s t, R n u) atTop (𝓝 L) := by
    simp_rw [hid]
    exact (tendsto_limEK hyp (hρm s) (hK s ⟨hs, hst⟩) (hpos s hs)).sub
      (tendsto_limEK hyp (hρm t) (hK t ⟨ht0, le_rfl⟩) (hpos t ht0))
  -- the good times
  have hgood := ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc hs le_rfl)
    (h.ae_isWeakGrad hK0 hK ht0)
  set Q0 : ℝ → ℝ≥0∞ := fun u => ∫⁻ x, ENNReal.ofReal (∑ j, (weakGrad (ρ u) x j +
    ρ u x * aD V W (ρ u) x j) ^ 2) / ENNReal.ofReal (ρ u x) ∂haar d
  have hpt : ∀ᵐ u ∂(volume.restrict (Ioc s t)), (∀ n, 0 ≤ R n u + B u) ∧
      Tendsto (fun n => ENNReal.ofReal (R n u + B u)) atTop (𝓝 (Q0 u + ENNReal.ofReal (B u))) ∧
      dissipation V W (ρ u) ≤ Q0 u := by
    filter_upwards [hgood, ae_restrict_mem measurableSet_Ioc] with u hgu hu
    obtain ⟨g, hg, hg2, -, hgE⟩ := hgu
    have hu0 : 0 ≤ u := hs.trans hu.1.le
    have hu' : u ∈ Icc 0 t := ⟨hu0, hu.2⟩
    have hE : ∑ j, ∫ x, g x j ^ 2 = (dirE ρ u).toReal := by
      rw [← hgE, ENNReal.toReal_ofReal (Finset.sum_nonneg fun j _ => integral_nonneg fun x => sq_nonneg _)]
    have hBu : C₁ * (∑ j, ∫ x, g x j ^ 2) + C₂ ≤ B u := by rw [hE]; simp only [hBdef]; linarith
    obtain ⟨h1, h2⟩ := hT (hρm u) (hK u hu') (hpos u hu0) (hmass u hu0) hg hg2 (B u) hBu
    refine ⟨h1, h2, ?_⟩
    by_cases hQ : Q0 u = ⊤
    · rw [hQ]; exact le_top
    · have hw := appA_isWeakGrad_weakGrad ⟨g, hg⟩
      have hwg : weakGrad (ρ u) =ᵐ[volume] g := appA_weakGrad_ae_eq hg
      exact dissipation_le_fisher hyp (hρm u) (hK u hu') (hpos u hu0) hw
        (fun j => (hg2 j).ae_eq (hwg.mono fun x hx => (congrFun hx j).symm)) hQ
  -- Fatou
  have hFm : ∀ n, AEMeasurable (fun u => ENNReal.ofReal (R n u + B u)) (volume.restrict (Ioc s t)) :=
    fun n => ((hRi n).aestronglyMeasurable.add hBi.aestronglyMeasurable).aemeasurable.ennreal_ofReal
  have hfatou := lintegral_liminf_le' (u := atTop) hFm
  have hlhs : ∫⁻ u in Ioc s t, (dissipation V W (ρ u) + ENNReal.ofReal (B u)) ≤
      ∫⁻ u in Ioc s t, liminf (fun n => ENNReal.ofReal (R n u + B u)) atTop := by
    refine lintegral_mono_ae ?_
    filter_upwards [hpt] with u hu
    rw [hu.2.1.liminf_eq]; exact add_le_add hu.2.2 le_rfl
  have hrhs : Tendsto (fun n => ∫⁻ u in Ioc s t, ENNReal.ofReal (R n u + B u)) atTop
      (𝓝 (ENNReal.ofReal (L + ∫ u in Ioc s t, B u))) := by
    have e : ∀ n, ∫⁻ u in Ioc s t, ENNReal.ofReal (R n u + B u) =
        ENNReal.ofReal ((∫ u in Ioc s t, R n u) + ∫ u in Ioc s t, B u) := fun n => by
      rw [← integral_add (hRi n) hBi, ofReal_integral_eq_lintegral_ofReal
        (f := fun u => R n u + B u) ((hRi n).add hBi)]
      filter_upwards [hpt] with u hu
      exact hu.1 n
    simp_rw [e]
    exact ENNReal.tendsto_ofReal (hL.add_const _)
  rw [hrhs.liminf_eq] at hfatou
  have hmain := hlhs.trans hfatou
  have hBm : AEMeasurable (fun u => ENNReal.ofReal (B u)) (volume.restrict (Ioc s t)) :=
    hBi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [lintegral_add_right' _ hBm, ← ofReal_integral_eq_lintegral_ofReal hBi
    (Eventually.of_forall fun u => (zero_le_one.trans (hB1 u)))] at hmain
  set b := ∫ u in Ioc s t, B u
  have hb : t - s ≤ b := by
    have h1 : ∫ u in Ioc s t, (1 : ℝ) ≤ b :=
      setIntegral_mono (integrableOn_const (measure_Ioc_lt_top.ne)) hBi hB1
    rwa [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioc,
      max_eq_left (by linarith)] at h1
  have hb0 : 0 < b := by linarith
  set X := ∫⁻ u in Ioc s t, dissipation V W (ρ u)
  have hX : X ≠ ⊤ := by
    intro hX
    rw [hX, top_add] at hmain
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hmain)
  refine ⟨hX, ?_⟩
  have hx0 : 0 ≤ X.toReal := ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_toReal hX, ← ENNReal.ofReal_add hx0 hb0.le] at hmain
  rcases (ENNReal.ofReal_le_ofReal_iff' (p := X.toReal + b) (q := L + b)).1 hmain with h' | h'
  · linarith
  · linarith

end LinMild

end SharpLSI
