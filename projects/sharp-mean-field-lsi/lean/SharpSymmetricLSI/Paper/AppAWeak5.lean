import SharpSymmetricLSI.Paper.AppAWeak4
import SharpSymmetricLSI.Defs.D19_Lip

/-!
# The weak formulation (5): the `d_Lip` bound (4.9) for the constructed solution

`d_Lip(ρ_s m, ρ_t m) ≤ ∫_s^t D(ρ_u)^{1/2} du` (`lip_bound_linMild`): test the weak formulation
with the heat-smoothed Lipschitz function `e^{εΔ}φ` and let `ε → 0`.
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

theorem FlatLipschitzWith.continuous {ι : Type} [Fintype ι] {φ : UnitAddTorus ι → ℝ}
    (h : FlatLipschitzWith 1 φ) : Continuous φ := by
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (Real.sqrt (Fintype.card ι)))
    fun x y => ?_).continuous
  rw [Real.dist_eq, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  exact (h x y).trans (by rw [one_mul]; exact (flatDist_comparison x y).2)

theorem tendsto_integral_heatT_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    {φ : UnitAddTorus ι → ℝ} (hφ : Continuous φ)
    {r : UnitAddTorus ι → ℝ} (hr : Integrable r) :
    Tendsto (fun ε => ∫ x, heatT ε φ x * r x) (𝓝[>] 0) (𝓝 (∫ x, φ x * r x)) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
  have hφi : Integrable φ := (memLp_of_continuous hφ 2).integrable one_le_two
  refine tendsto_integral_filter_of_dominated_convergence (bound := fun x => C * |r x|) ?_ ?_
    (hr.abs.const_mul C) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (continuous_heatT hε hφi).aestronglyMeasurable.mul hr.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_heatT_le hε hφ.aestronglyMeasurable
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y (mem_univ _)) x)
      (abs_nonneg _)
  · exact Eventually.of_forall fun x => (tendsto_heatT_of_continuous hφ x).mul_const _

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem integral_densMeasure_ae {ρ : Torus d → ℝ} (hm : Measurable ρ)
    (h0 : ∀ᵐ x ∂haar d, 0 ≤ ρ x) (φ : Torus d → ℝ) :
    ∫ x, φ x ∂densMeasure ρ = ∫ x, φ x * ρ x ∂haar d := by
  unfold densMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun x => ENNReal.ofReal (ρ x)) (ENNReal.measurable_ofReal.comp hm)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [h0] with x hx
  simp only [Function.comp, ENNReal.toReal_ofReal hx, smul_eq_mul, mul_comm]

/-- **(4.9) for the constructed solution.** -/
theorem lip_bound_linMild (hyp : Hyp V W KV KW) {ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ} {A : ℝ}
    (hL : LinMild ρ₀ ρ (fun u y k => modFlux V W (ρ u) y k) A)
    (hpos : ∀ t, 0 ≤ t → ∀ᵐ x ∂haar d, 0 ≤ ρ t x) (hmass : ∀ t, 0 ≤ t → ∫ x, ρ t x ∂haar d = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ENNReal.ofReal (dLipM (densMeasure (ρ s)) (densMeasure (ρ t))) ≤
      ∫⁻ u in Icc s t, dissipation V W (ρ u) ^ (1 / 2 : ℝ) := by
  set R := ∫⁻ u in Icc s t, dissipation V W (ρ u) ^ (1 / 2 : ℝ)
  by_cases hR : R = ⊤
  · rw [hR]; exact le_top
  obtain ⟨K, hK0, hK⟩ := hL.bdd t
  have hint : ∀ u ∈ Icc 0 t, Integrable (ρ u) (haar d) := fun u hu =>
    appA_integrable_of_abs_le' (hL.measurable_section u) (hK u hu)
  have key : ∀ φ : Torus d → ℝ, FlatLipschitzWith 1 φ →
      |∫ x, φ x ∂densMeasure (ρ s) - ∫ x, φ x ∂densMeasure (ρ t)| ≤ R.toReal := by
    intro φ hφ
    have hc := hφ.continuous
    have hφi : Integrable φ := (memLp_of_continuous hc 2).integrable one_le_two
    rw [integral_densMeasure_ae (hL.measurable_section s) (hpos s hs),
      integral_densMeasure_ae (hL.measurable_section t) (hpos t (hs.trans hst)), abs_sub_comm]
    have hlim := ((tendsto_integral_heatT_mul hc (hint t ⟨hs.trans hst, le_rfl⟩)).sub
      (tendsto_integral_heatT_mul hc (hint s ⟨hs, hst⟩))).abs
    refine le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
    have hsm := isSmoothT_heatT hε hφi
    have hgr := sum_dpart_sq_le_one hsm (flatLipschitz_heatT hε hc hφ)
    have hw := hL.abs_weak_le hK0 hK hsm hgr hs hst le_rfl
      (F := fun u => dissipation V W (ρ u) ^ (1 / 2 : ℝ)) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu g hg _
        have hu0 : 0 ≤ u := hs.trans hu.1.le
        exact lintegral_flux_le hyp (hint u ⟨hu0, hu.2⟩) (hpos u hu0) (hmass u hu0) hg)
    exact (ENNReal.ofReal_le_iff_le_toReal hR).1 (hw.trans (lintegral_mono_set Ioc_subset_Icc_self))
  have hle : dLipM (densMeasure (ρ s)) (densMeasure (ρ t)) ≤ R.toReal := by
    unfold dLipM
    exact Real.sSup_le (fun x ⟨φ, hφ, _, hx⟩ => hx ▸ key φ hφ) ENNReal.toReal_nonneg
  exact (ENNReal.ofReal_le_ofReal hle).trans_eq (ENNReal.ofReal_toReal hR)

end SharpLSI
