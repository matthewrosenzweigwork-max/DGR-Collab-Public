import SharpSymmetricLSI.Paper.UpperComparison
import SharpSymmetricLSI.Paper.L2Conv
import SharpSymmetricLSI.Infra.MollifyL2

/-!
# Smooth approximation of admissible densities (Phase 3, lane D; R6 `upper_bound`)

For admissible `ρ` (`u = √ρ ∈ H¹`), the densities `ρⱼ ∝ (u ⋆ φ_{nⱼ})² + tⱼ` are smooth and
positive, `ρⱼ → ρ` in `L¹` and a.e., and `limsup D(ρⱼ) ≤ D(ρ)`. (Route departure from the heat
flow of Appendix A.1, recorded in `Audit/statement_map.md`.)
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace SharpLSI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A common a.e.-convergent subsequence for the mollifications of `u` and of the components of
its weak gradient. -/
theorem exists_subseq_moll_ae {u : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (hu : Integrable u volume) (hg : ∀ k, Integrable (fun y => g y k) volume) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ y ∂(volume : Measure (UnitAddTorus ι)),
      Tendsto (fun j => moll (ns j) u y) atTop (𝓝 (u y)) ∧
      ∀ k, Tendsto (fun j => moll (ns j) (fun z => g z k) y) atTop (𝓝 (g y k)) := by
  set F : ℕ → UnitAddTorus ι → ℝ := fun n y => |moll n u y - u y| +
    ∑ k, |moll n (fun z => g z k) y - g y k| with hF
  have hFm : ∀ n, AEStronglyMeasurable (F n) volume := fun n =>
    (((measurable_moll n hu).aestronglyMeasurable.sub hu.aestronglyMeasurable).norm).add
      (Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
        ((measurable_moll n (hg k)).aestronglyMeasurable.sub (hg k).aestronglyMeasurable).norm)
  have hlim : Tendsto (fun n => ∫⁻ y, ‖F n y - 0‖ₑ) atTop (𝓝 0) := by
    have hb : ∀ n, ∫⁻ y, ‖F n y - 0‖ₑ ≤ (∫⁻ y, ‖moll n u y - u y‖ₑ) +
        ∑ k, ∫⁻ y, ‖moll n (fun z => g z k) y - g y k‖ₑ := fun n => by
      have hm1 : ∀ k, AEMeasurable (fun y => ‖moll n (fun z => g z k) y - g y k‖ₑ) volume :=
        fun k => ((measurable_moll n (hg k)).aestronglyMeasurable.sub
          (hg k).aestronglyMeasurable).enorm
      have hm0 : AEMeasurable (fun y => ‖moll n u y - u y‖ₑ) volume :=
        ((measurable_moll n hu).aestronglyMeasurable.sub hu.aestronglyMeasurable).enorm
      rw [← lintegral_finsetSum' (f := fun k y => ‖moll n (fun z => g z k) y - g y k‖ₑ) _
        fun k _ => hm1 k, ← lintegral_add_left' hm0]
      refine lintegral_mono fun y => ?_
      rw [sub_zero, hF]
      simp only
      refine (enorm_add_le _ _).trans (add_le_add (by rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_abs]) ?_)
      refine (enorm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun k _ => by rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_abs]
    have hz : Tendsto (fun n => (∫⁻ y, ‖moll n u y - u y‖ₑ) +
        ∑ k, ∫⁻ y, ‖moll n (fun z => g z k) y - g y k‖ₑ) atTop (𝓝 0) := by
      have := (tendsto_moll hu).add (tendsto_finsetSum (Finset.univ : Finset ι)
        fun k _ => tendsto_moll (hg k))
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz (fun _ => zero_le) hb
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_of_tendsto_lintegral hFm
    (aestronglyMeasurable_const) hlim
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae] with y hy
  have hle1 : ∀ j, |moll (ns j) u y - u y| ≤ F (ns j) y := fun j =>
    le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => abs_nonneg _)
  have hle2 : ∀ k j, |moll (ns j) (fun z => g z k) y - g y k| ≤ F (ns j) y := fun k j =>
    (Finset.single_le_sum (f := fun k => |moll (ns j) (fun z => g z k) y - g y k|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ k)).trans (le_add_of_nonneg_left (abs_nonneg _))
  refine ⟨?_, fun k => ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun j => by rw [Real.norm_eq_abs]; exact hle1 j) hy
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun j => by rw [Real.norm_eq_abs]; exact hle2 k j) hy

theorem L2Tendsto_moll {u : UnitAddTorus ι → ℝ} (hu : Integrable u volume)
    (hu2 : ∫⁻ y, ‖u y‖ₑ ^ 2 ≠ ⊤) {ns : ℕ → ℕ}
    (hae : ∀ᵐ y ∂(volume : Measure (UnitAddTorus ι)),
      Tendsto (fun j => moll (ns j) u y) atTop (𝓝 (u y))) :
    L2Tendsto volume (fun j => moll (ns j) u) u :=
  tendsto_L2_of_ae (fun j => (measurable_moll _ hu).aemeasurable) hu.aemeasurable hae
    (fun j => lintegral_moll_sq_le _ hu) hu2

section Diss

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem convDens_congr_ae {ρ ρ' : Torus d → ℝ} (h : ρ =ᵐ[haar d] ρ') :
    convDens W ρ = convDens W ρ' := by
  funext x; unfold convDens
  exact integral_congr_ae (h.mono fun y hy => by simp only [hy])

theorem bForceL_congr_ae {ρ ρ' : Torus d → ℝ} (h : ρ =ᵐ[haar d] ρ') :
    bForceL W ρ = bForceL W ρ' := by
  funext x k; unfold bForceL
  exact integral_congr_ae (h.mono fun y hy => by simp only [hy])

theorem isWeakGrad_convDens' (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hρi : Integrable ρ (haar d)) :
    IsWeakGrad (convDens W ρ) (bForceL W ρ) := by
  set ρ' := hρi.aestronglyMeasurable.mk ρ
  have h : ρ =ᵐ[haar d] ρ' := hρi.aestronglyMeasurable.ae_eq_mk
  rw [convDens_congr_ae h, bForceL_congr_ae h]
  exact isWeakGrad_convDens hyp hρi.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    (hρi.congr h)

theorem measurable_bForceL' (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hρi : Integrable ρ (haar d))
    (k : Fin d) : Measurable fun x => bForceL W ρ x k := by
  set ρ' := hρi.aestronglyMeasurable.mk ρ
  have h : ρ =ᵐ[haar d] ρ' := hρi.aestronglyMeasurable.ae_eq_mk
  rw [bForceL_congr_ae h]
  exact (((measurable_bGrad hyp (W := W) k).mul
    (hρi.aestronglyMeasurable.stronglyMeasurable_mk.measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right
      (ν := haar d) (f := fun x y => bGrad W x y k * ρ' y)).measurable

/-- `D(ρ) = ∑ₖ ∫ |2Gₖ + √ρ (∇ₖV + bₖ)|²` for any weak gradient `G` of `√ρ`. -/
theorem dissipation_eq_of (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hρi : Integrable ρ (haar d))
    (hH1 : MemH1 (haar d) (fun x => Real.sqrt (ρ x))) {G : Torus d → Fin d → ℝ}
    (hG : IsWeakGrad (fun x => Real.sqrt (ρ x)) G) :
    dissipation V W ρ = ∑ k, ∫⁻ x, ‖2 * G x k + Real.sqrt (ρ x) *
      (lipGrad V x k + bForceL W ρ x k)‖ₑ ^ 2 ∂haar d := by
  have hVw := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp (W := W))
  have hVC := hVw.add (isWeakGrad_convDens' hyp hρi (W := W))
  unfold dissipation
  rw [if_pos ⟨hH1, ⟨_, hVC⟩⟩]
  have hm : ∀ k, AEMeasurable (fun x => ‖2 * G x k + Real.sqrt (ρ x) *
      (lipGrad V x k + bForceL W ρ x k)‖ₑ ^ 2) (haar d) := fun k =>
    ((((hG.aestronglyMeasurable_grad k).const_mul 2).add
      (hG.aestronglyMeasurable_fun.mul ((measurable_lipGrad hyp.continuous_V k).add
        (measurable_bForceL' hyp hρi k)).aestronglyMeasurable)).enorm).pow_const 2
  rw [← lintegral_finsetSum' _ fun k _ => hm k]
  refine lintegral_congr_ae ?_
  filter_upwards [weakGrad_ae_eq hG, weakGrad_ae_eq hVC] with x h1 h2
  rw [h1, h2, ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
  exact Finset.sum_congr rfl fun k _ => ofReal_sq_eq_enorm_sq _

end Diss

end SharpLSI
