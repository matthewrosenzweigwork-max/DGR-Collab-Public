import SharpSymmetricLSI.Paper.AppAEnt9

/-!
# The energy–dissipation inequality (1): the identity at level `δ` between two times

`t ↦ R_δ(ρ_t)` is integrable (it is the a.e. limit of `R_{ε,δ}`, dominated by
`C₁ ∫|∇ρ_u|² + C₂`), and `E_δ(ρ_t) = E_δ(ρ_s) - ∫_{(s,t]} R_δ(ρ_u)` (`LinMild.delta_identity_st`).
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

namespace LinMild

variable {ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ} {N : ℝ → Torus d → Fin d → ℝ} {A : ℝ}

theorem integrableOn_limRate (hyp : Hyp V W KV KW) (h : LinMild ρ₀ ρ N A) {δ : ℝ} (hδ : 0 < δ)
    {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K) (hT0 : 0 ≤ T) :
    IntegrableOn (fun u => limRate V W δ (ρ u) (N u)) (Ioc 0 T) := by
  obtain ⟨C₁, C₂, hC⟩ := exists_epsRate_bound hyp hδ (W := W) (V := V) K (A * K)
  have hgood := h.ae_isWeakGrad hK0 hK hT0
  set bnd : ℝ → ℝ := fun u => C₁ * (dirE ρ u).toReal + C₂
  have hbnd : IntegrableOn bnd (Ioc 0 T) := by
    haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) T)) :=
      isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    exact ((integrable_toReal_of_lintegral_ne_top h.measurable_dirE.aemeasurable
      (h.lintegral_dirE_lt_top hK0 hK hT0).ne).const_mul C₁).add (integrable_const C₂)
  set εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεn : ∀ n, 0 < εn n := fun n => by positivity
  have hlim : ∀ᵐ u ∂(volume.restrict (Ioc 0 T)),
      Tendsto (fun n => epsRate V W δ (εn n) (ρ u) (N u)) atTop (𝓝 (limRate V W δ (ρ u) (N u))) := by
    filter_upwards [hgood, ae_restrict_mem measurableSet_Ioc] with u hgu hu
    obtain ⟨g, hg, hg2, -, -⟩ := hgu
    have hu' : u ∈ Icc 0 T := ⟨hu.1.le, hu.2⟩
    exact (tendsto_epsRate hyp hδ (h.measurable_section u) (hK u hu')
      (fun k => h.measurable_sectionN u k) (fun z k => h.abs_N_le hK hu' z k) hg hg2).comp
      tendsto_delta_seq
  have hmeas : ∀ n, AEStronglyMeasurable (fun u => epsRate V W δ (εn n) (ρ u) (N u))
      (volume.restrict (Ioc 0 T)) := fun n => by
    obtain ⟨Φ, hΦm, hΦ⟩ := h.exists_measurable_epsRate hyp hδ (hεn n) hK
    refine hΦm.aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (hΦ u ⟨hu.1.le, hu.2⟩).symm
  refine hbnd.mono' (aestronglyMeasurable_of_tendsto_ae _ hmeas hlim) ?_
  filter_upwards [hlim, hgood, ae_restrict_mem measurableSet_Ioc] with u hl hgu hu
  obtain ⟨g, hg, hg2, -, hgE⟩ := hgu
  have hu' : u ∈ Icc 0 T := ⟨hu.1.le, hu.2⟩
  have hE : ∑ j, ∫ x, g x j ^ 2 = (dirE ρ u).toReal := by
    rw [← hgE, ENNReal.toReal_ofReal (Finset.sum_nonneg fun j _ => integral_nonneg fun x => sq_nonneg _)]
  rw [Real.norm_eq_abs]
  refine le_of_tendsto hl.abs (Eventually.of_forall fun n => ?_)
  have := hC (εn n) (hεn n) (ρ u) (h.measurable_section u) (hK u hu') (N u)
    (fun k => h.measurable_sectionN u k) (fun z k => h.abs_N_le hK hu' z k) g hg hg2
  rwa [hE] at this

/-- **The identity at level `δ` between two times.** -/
theorem delta_identity_st (hyp : Hyp V W KV KW) (h : LinMild ρ₀ ρ N A) {δ : ℝ} (hδ : 0 < δ)
    {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (htT : t ≤ T) :
    limE V W δ (ρ t) = limE V W δ (ρ s) - ∫ u in Ioc s t, limRate V W δ (ρ u) (N u) := by
  have hT0 : 0 ≤ T := hs.trans (hst.trans htT)
  have hi := h.integrableOn_limRate hyp hδ hK0 hK hT0
  have ht := h.delta_identity hyp hδ hK0 hK ⟨hs.trans hst, htT⟩
  have hs' := h.delta_identity hyp hδ hK0 hK ⟨hs, hst.trans htT⟩
  have hsplit : ∫ u in Ioc 0 t, limRate V W δ (ρ u) (N u) =
      (∫ u in Ioc 0 s, limRate V W δ (ρ u) (N u)) + ∫ u in Ioc s t, limRate V W δ (ρ u) (N u) := by
    rw [← Ioc_union_Ioc_eq_Ioc hs hst]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hi.mono_set (Ioc_subset_Ioc le_rfl (hst.trans htT)))
      (hi.mono_set (Ioc_subset_Ioc hs htT))
  rw [ht, hs', hsplit]; ring

end LinMild

end SharpLSI
