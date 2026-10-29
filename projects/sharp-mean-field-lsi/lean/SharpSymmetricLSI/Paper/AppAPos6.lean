import SharpSymmetricLSI.Paper.AppAPos5

/-!
# Positivity (6): the energy inequality for `ρ^ε`

For `G ∈ C²` with `G'' ≥ 0` and a linear mild solution, with `φ_u = e^{εΔ}ρ_u` and
`ψ_u = e^{εΔ}N_u`:
`∫ G(φ_t) ≤ ∫ G(e^{εΔ}ρ₀) + ¼ ∫_{(0,t]} ∫ G''(φ_u) |ψ_u|² du` (`energy_ineq`).
-/

open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped Real ENNReal ContDiff

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem measurable_heatT_family {t : ℝ} {ρ : ℝ → UnitAddTorus ι → ℝ}
    (hρ : Measurable (Function.uncurry ρ)) :
    Measurable fun p : ℝ × UnitAddTorus ι => heatT t (ρ p.1) p.2 := by
  unfold heatT
  have hm : StronglyMeasurable (fun q : (ℝ × UnitAddTorus ι) × (ι → ℝ) =>
      ρ q.1.1 (q.1.2 - liftT q.2) * heatKernel t q.2) :=
    ((hρ.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).sub (measurable_liftT.comp measurable_snd)))).mul
      ((measurable_heatKernel t).comp measurable_snd)).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

theorem exists_bound_on_Icc {g : ℝ → ℝ} (hg : Continuous g) (R : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ r, |r| ≤ R → |g r| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun r hr => ?_⟩
  have := hM r (abs_le.1 hr)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- Young's inequality used to absorb the flux: `-a(a + h) ≤ h²/4`. -/
theorem neg_mul_add_le (a h : ℝ) : -(a * (a + h)) ≤ h ^ 2 / 4 := by
  nlinarith [sq_nonneg (a + h / 2)]

/-- The flux absorbed in the energy at a fixed time. -/
theorem energy_rate_le {Gp Gpp : ℝ → ℝ} (hGp : ∀ r, HasDerivAt Gp (Gpp r) r)
    (hGpp : Continuous Gpp) (hGpp0 : ∀ r, 0 ≤ Gpp r) {ε : ℝ} (hε : 0 < ε)
    {f : UnitAddTorus ι → ℝ} (hf : Measurable f) {F : UnitAddTorus ι → ι → ℝ}
    (hF : ∀ k, Measurable fun z => F z k) {B : ℝ} (hfB : ∀ x, |f x| ≤ B) (hFB : ∀ z k, |F z k| ≤ B) :
    ∫ x, Gp (heatT ε f x) * (lapHeat ε f x + divHeatT ε F x) ≤
      ∫ x, Gpp (heatT ε f x) * (∑ j, (heatT ε (fun z => F z j) x) ^ 2) / 4 := by
  set φ := heatT ε f
  set ψ : ι → UnitAddTorus ι → ℝ := fun j => heatT ε (fun z => F z j)
  have hφ : IsSmoothT φ := isSmoothT_heatT hε (appA_integrable_of_abs_le' hf hfB)
  have hψ : ∀ j, IsSmoothT (ψ j) := fun j =>
    isSmoothT_heatT hε (appA_integrable_of_abs_le' (hF j) fun z => hFB z j)
  have hc : ∀ {v : UnitAddTorus ι → ℝ}, IsSmoothT v → Continuous v := fun hv => continuous_of_isSmoothT hv
  have hGpc : Continuous Gp := continuous_iff_continuousAt.2 fun r => (hGp r).continuousAt
  have hae : (fun x => Gp (φ x) * (lapHeat ε f x + divHeatT ε F x)) =ᵐ[volume]
      fun x => ∑ j, Gp (φ x) * (dpart_appA (dpart_appA φ j) j x + dpart_appA (ψ j) j x) := by
    filter_upwards [lapHeat_ae_eq hε hf hfB, divHeatT_ae_eq hε hF hFB] with x h1 h2
    rw [h1, h2, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [integral_congr_ae hae, integral_finsetSum (f := fun j a =>
      Gp (φ a) * (dpart_appA (dpart_appA φ j) j a + dpart_appA (ψ j) j a)) _ fun j _ =>
    (memLp_of_continuous ((hGpc.comp (hc hφ)).mul ((hc (isSmoothT_dpart (isSmoothT_dpart hφ j) j)).add
      (hc (isSmoothT_dpart (hψ j) j)))) 1).integrable le_rfl]
  simp_rw [ibp_energy hGp hGpp hφ (hψ _)]
  simp_rw [← integral_neg]
  rw [← integral_finsetSum (f := fun j y => -(Gpp (φ y) * (dpart_appA φ j y * (dpart_appA φ j y + ψ j y))))
    _ fun j _ => ((memLp_of_continuous ((hGpp.comp (hc hφ)).mul
    ((hc (isSmoothT_dpart hφ j)).mul ((hc (isSmoothT_dpart hφ j)).add (hc (hψ j))))) 1).integrable
      le_rfl).neg]
  · refine integral_mono ?_ ?_ fun x => ?_
    · exact integrable_finsetSum _ fun j _ => ((memLp_of_continuous ((hGpp.comp (hc hφ)).mul
        ((hc (isSmoothT_dpart hφ j)).mul ((hc (isSmoothT_dpart hφ j)).add (hc (hψ j))))) 1).integrable
          le_rfl).neg
    · exact (memLp_of_continuous (((hGpp.comp (hc hφ)).mul (continuous_finset_sum _ fun j _ =>
        (hc (hψ j)).pow 2)).div_const 4) 1).integrable le_rfl
    · simp only
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_le_sum fun j _ => ?_
      have := mul_le_mul_of_nonneg_left (neg_mul_add_le (dpart_appA φ j x) (ψ j x)) (hGpp0 (φ x))
      linarith

end SharpLSI
