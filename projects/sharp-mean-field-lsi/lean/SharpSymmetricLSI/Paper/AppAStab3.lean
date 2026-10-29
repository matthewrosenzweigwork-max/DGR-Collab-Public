import SharpSymmetricLSI.Paper.AppAStab2
import SharpSymmetricLSI.Infra.HeatTorus7

/-!
# Lemma A.1: mild solutions, continuity of the Duhamel integrand

`AppAMild V W ρ₀ ρ` is the unfolded `IsMildSolution` of R36. For such `ρ`, `t > 0` and `x`, the
Duhamel integrand `u ↦ ∇·e^{(t-u)Δ}(ρ_u a_{ρ_u})(x)` is continuous on `(0, t)`
(`continuousOn_duhamel`): the fluxes move continuously in `L¹` (flux Lipschitz bound), a
subsequence converges a.e., and `tendsto_divHeatT` applies.
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The unfolded mild-solution property (`IsMildSolution` of R36). -/
structure AppAMild (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ₀ : Torus d → ℝ)
    (ρ : ℝ → Torus d → ℝ) : Prop where
  prob : ∀ t, 0 ≤ t → (∀ᵐ x ∂haar d, 0 ≤ ρ t x) ∧ ∫ x, ρ t x ∂haar d = 1
  cont : ∀ t, 0 ≤ t →
    Tendsto (fun s => eLpNorm (fun x => ρ s x - ρ t x) 1 (haar d)) (𝓝[Ici 0] t) (𝓝 0)
  init : ρ 0 = ρ₀
  bdd : ∀ T, ∃ B : ℝ, ∀ t ∈ Icc 0 T, ∀ᵐ x ∂haar d, |ρ t x| ≤ B
  mild : ∀ t, 0 < t → ρ t =ᵐ[haar d] fun x => heatT t ρ₀ x +
    ∫ u in Ioc 0 t, divHeatT (t - u) (fun y k => ρ u y * appADrift V W (ρ u) y k) x

theorem AppAMild.probDens {ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ} (h : AppAMild V W ρ₀ ρ)
    {t : ℝ} (ht : 0 ≤ t) : IsProbDens (ρ t) :=
  ⟨Integrable.of_integral_ne_zero (by rw [(h.prob t ht).2]; exact one_ne_zero),
    (h.prob t ht).1, (h.prob t ht).2⟩

theorem lintegral_sub_eq_eLpNorm {f g : Torus d → ℝ} (hf : Integrable f (haar d))
    (hg : Integrable g (haar d)) :
    ∫⁻ x, ‖f x - g x‖ₑ ∂haar d = eLpNorm (fun x => f x - g x) 1 (haar d) := by
  rw [eLpNorm_one_eq_lintegral_enorm (f := fun x => f x - g x) (hf.sub hg).aestronglyMeasurable]

theorem aestronglyMeasurable_appAFlux (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ}
    (hρ : Integrable ρ (haar d)) (k : Fin d) :
    AEStronglyMeasurable (fun x => appAFlux V W ρ x k) (haar d) :=
  hρ.aestronglyMeasurable.mul (aestronglyMeasurable_appADrift hyp hρ k)

theorem abs_appAFlux_le (hyp : Hyp V W KV KW) {BV BW : ℝ}
    (hBV : ∀ᵐ x ∂haar d, ∀ k, |weakGrad V x k| ≤ BV)
    (hBW : ∀ᵐ p ∂(haar d).prod (haar d), ∀ k, |bGrad W p.1 p.2 k| ≤ BW)
    {ρ : Torus d → ℝ} (hρ : IsProbDens ρ) {B : ℝ} (hB : ∀ᵐ x ∂haar d, |ρ x| ≤ B) :
    ∀ᵐ x ∂haar d, ∀ k, |appAFlux V W ρ x k| ≤ B * (BV + BW) := by
  filter_upwards [abs_appADrift_le hyp hBV hBW hρ, hB] with x h1 h2 k
  unfold appAFlux
  rw [abs_mul]
  exact mul_le_mul h2 (h1 k) (abs_nonneg _) ((abs_nonneg _).trans h2)

/-- **Continuity of the Duhamel integrand.** -/
theorem continuousOn_duhamel (hyp : Hyp V W KV KW) {BV BW : ℝ} (hBV0 : 0 ≤ BV) (hBW0 : 0 ≤ BW)
    (hBV : ∀ᵐ x ∂haar d, ∀ k, |weakGrad V x k| ≤ BV)
    (hBW : ∀ᵐ p ∂(haar d).prod (haar d), ∀ k, |bGrad W p.1 p.2 k| ≤ BW)
    {ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ} (h : AppAMild V W ρ₀ ρ) {t : ℝ} (ht : 0 < t)
    (x : Torus d) :
    ContinuousOn (fun u => divHeatT (t - u) (appAFlux V W (ρ u)) x) (Ioo 0 t) := by
  obtain ⟨B, hB⟩ := h.bdd t
  intro u₀ hu₀
  rw [ContinuousWithinAt, tendsto_iff_seq_tendsto]
  intro v hv
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hw0' : Tendsto (v ∘ ns) atTop (𝓝[Ioo 0 t] u₀) := hv.comp hns
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hw0'.eventually self_mem_nhdsWithin)
  set w : ℕ → ℝ := fun j => v (ns (j + N)) with hw
  have hwI : ∀ j, w j ∈ Ioo 0 t := fun j => hN (j + N) (by omega)
  have hw' : Tendsto w atTop (𝓝[Ioo 0 t] u₀) :=
    hw0'.comp (tendsto_add_atTop_nat N)
  have hwC : Tendsto w atTop (𝓝[Ici 0] u₀) :=
    tendsto_nhdsWithin_mono_right (fun s hs => le_of_lt hs.1) hw'
  have hw0 : Tendsto w atTop (𝓝 u₀) := (tendsto_nhdsWithin_iff.1 hw').1
  have hu0 : 0 ≤ u₀ := hu₀.1.le
  -- `L¹` convergence of the densities and of the fluxes
  have hρL : Tendsto (fun j => ∫⁻ z, ‖ρ (w j) z - ρ u₀ z‖ₑ ∂haar d) atTop (𝓝 0) := by
    have := (h.cont u₀ hu0).comp hwC
    refine this.congr fun j => ?_
    simp only [Function.comp_apply]
    exact (lintegral_sub_eq_eLpNorm (h.probDens (hwI j).1.le).int (h.probDens hu0).int).symm
  set G : ℕ → Torus d → ℝ := fun j z =>
    ∑ k, |appAFlux V W (ρ (w j)) z k - appAFlux V W (ρ u₀) z k| with hG
  have hGL : Tendsto (fun j => ∫⁻ z, ‖G j z - 0‖ₑ ∂haar d) atTop (𝓝 0) := by
    have hbd : ∀ j, ∫⁻ z, ‖G j z - 0‖ₑ ∂haar d ≤
        ∑ _k : Fin d, ENNReal.ofReal (BV + 2 * BW) * ∫⁻ z, ‖ρ (w j) z - ρ u₀ z‖ₑ ∂haar d := by
      intro j
      have hj := hwI j
      calc ∫⁻ z, ‖G j z - 0‖ₑ ∂haar d
          ≤ ∫⁻ z, ∑ k, ‖appAFlux V W (ρ (w j)) z k - appAFlux V W (ρ u₀) z k‖ₑ ∂haar d := by
            refine lintegral_mono fun z => ?_
            rw [sub_zero]
            refine (enorm_sum_le _ _).trans (le_of_eq ?_)
            simp_rw [Real.enorm_abs]
        _ = ∑ k, ∫⁻ z, ‖appAFlux V W (ρ (w j)) z k - appAFlux V W (ρ u₀) z k‖ₑ ∂haar d := by
            rw [lintegral_finsetSum' (f := fun k z =>
              ‖appAFlux V W (ρ (w j)) z k - appAFlux V W (ρ u₀) z k‖ₑ) _ fun k _ =>
              (((aestronglyMeasurable_appAFlux hyp (h.probDens hj.1.le).int k).sub
                (aestronglyMeasurable_appAFlux hyp (h.probDens hu0).int k)).enorm)]
        _ ≤ _ := Finset.sum_le_sum fun k _ =>
            lintegral_appAFlux_sub_le hyp hBV0 hBW0 hBV hBW (h.probDens hj.1.le) (h.probDens hu0) k
    have hlim : Tendsto (fun j => ∑ _k : Fin d,
        ENNReal.ofReal (BV + 2 * BW) * ∫⁻ z, ‖ρ (w j) z - ρ u₀ z‖ₑ ∂haar d) atTop (𝓝 0) := by
      have h1 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (BV + 2 * BW)) hρL
        (Or.inr ENNReal.ofReal_ne_top)
      rw [mul_zero] at h1
      have h2 := ENNReal.Tendsto.const_mul (a := (Fintype.card (Fin d) : ℝ≥0∞)) h1
        (Or.inr (ENNReal.natCast_ne_top _))
      rw [mul_zero] at h2
      refine h2.congr fun j => ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) hbd
  have hGm : ∀ j, AEStronglyMeasurable (G j) (haar d) := fun j =>
    Finset.aestronglyMeasurable_fun_sum _ fun k _ => continuous_abs.comp_aestronglyMeasurable
      ((aestronglyMeasurable_appAFlux hyp (h.probDens (hwI j).1.le).int k).sub
        (aestronglyMeasurable_appAFlux hyp (h.probDens hu0).int k))
  obtain ⟨ms, hms, hae⟩ := exists_subseq_ae_of_tendsto_lintegral hGm aestronglyMeasurable_const hGL
  refine ⟨fun n => ms n + N, ?_⟩
  have hs : Tendsto (fun n => t - w (ms n)) atTop (𝓝 (t - u₀)) :=
    tendsto_const_nhds.sub (hw0.comp hms.tendsto_atTop)
  have key := tendsto_divHeatT (sub_pos.2 hu₀.2) hs (F₀ := appAFlux V W (ρ u₀))
    (F := fun n => appAFlux V W (ρ (w (ms n)))) (M := B * (BV + BW))
    (Eventually.of_forall fun n k =>
      aestronglyMeasurable_appAFlux hyp (h.probDens (hwI _).1.le).int k)
    (Eventually.of_forall fun n k => by
      filter_upwards [abs_appAFlux_le hyp hBV hBW (h.probDens (hwI (ms n)).1.le)
        (hB _ ⟨(hwI (ms n)).1.le, (hwI (ms n)).2.le⟩)] with z hz
      exact hz k)
    (fun k => by
      filter_upwards [hae] with z hz
      have h0 : Tendsto (fun n => |appAFlux V W (ρ (w (ms n))) z k - appAFlux V W (ρ u₀) z k|)
          atTop (𝓝 0) := by
        refine squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) hz
        exact Finset.single_le_sum
          (f := fun j => |appAFlux V W (ρ (w (ms n))) z j - appAFlux V W (ρ u₀) z j|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ k)
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simpa only [Real.norm_eq_abs] using h0) x
  exact key

end SharpLSI
