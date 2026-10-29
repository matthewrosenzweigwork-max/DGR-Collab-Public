import SharpSymmetricLSI.Paper.AppARStar2

/-!
# Appendix A.1, heat approximation: `D(ρ_n) → D(ρ)` and `G(ρ_n) → G(ρ)` along a sequence
-/

open MeasureTheory Set Filter Topology InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

namespace H1Dens

variable {ρ : Torus d → ℝ} (h : H1Dens ρ)
include h

/-- The integrand of `D(ρ)` is square integrable. -/
theorem lintegral_psi_ne_top (hyp : Hyp V W KV KW) (k : Fin d) :
    ∫⁻ x, ‖2 * weakGrad (fun z => Real.sqrt (ρ z)) x k + Real.sqrt (ρ x) *
      (lipGrad V x k + bForceL W ρ x k)‖ₑ ^ 2 ∂haar d ≠ ⊤ := by
  set u : Torus d → ℝ := fun x => Real.sqrt (ρ x)
  set gu := weakGrad u
  obtain ⟨Cb₀, hCb₀⟩ := bGrad_bdd hyp (W := W)
  set Cb := max Cb₀ 0
  have hCb : ∀ x y k, |bGrad W x y k| ≤ Cb := fun x y k => (hCb₀ x y k).trans (le_max_left _ _)
  set LV : ℝ := ((Real.toNNReal (KV * Fintype.card (Fin d) / 2) : NNReal) : ℝ)
  have hLV : ∀ x k, |lipGrad V x k| ≤ LV := fun x k => abs_lipGrad_le (lipschitz_V hyp (W := W)) x k
  have hg2f := memLp_two_lintegral_ne_top (h.memLp_grad k)
  have hu2f := memLp_two_lintegral_ne_top h.h1.2.1
  have hb : ∀ x, ‖2 * gu x k + u x * (lipGrad V x k + bForceL W ρ x k)‖ₑ ^ 2 ≤
      2 * (‖(2 : ℝ)‖ₑ ^ 2 * ‖gu x k‖ₑ ^ 2) + 2 * (‖LV + Cb‖ₑ ^ 2 * ‖u x‖ₑ ^ 2) := fun x => by
    refine (enorm_add_sq_le _ _).trans ?_
    rw [enorm_mul, enorm_mul, mul_pow, mul_pow, mul_comm (‖u x‖ₑ ^ 2)]
    gcongr
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    exact ((abs_add_le _ _).trans (add_le_add (hLV x k)
      (abs_bForceL_le hyp h.nonneg h.one hCb x k))).trans (le_abs_self _)
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hb)
  rw [lintegral_add_left' (((((h.isWeakGrad.aestronglyMeasurable_grad k).enorm).pow_const
      2).const_mul _).const_mul 2),
    lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num),
    lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top (by simp)
    hg2f), ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top (by simp) hu2f)⟩

theorem dissipation_ne_top (hyp : Hyp V W KV KW) : dissipation V W ρ ≠ ⊤ := by
  rw [dissipation_eq_of hyp h.integrable h.h1 h.isWeakGrad]
  exact ENNReal.sum_ne_top.mpr fun k _ => h.lintegral_psi_ne_top hyp k

/-- `D(ρ_n) → D(ρ)` along the sequence. -/
theorem tendsto_dissipation_seq (hyp : Hyp V W KV KW) {s : ℕ → ℝ} (hs0 : ∀ n, 0 < s n)
    (hρae : ∀ᵐ x ∂haar d, Tendsto (fun n => heatT (s n) ρ x) atTop (𝓝 (ρ x)))
    (hgae : ∀ᵐ x ∂haar d, ∀ k, Tendsto (fun n => sqrtHeatGrad (s n) ρ x k) atTop
      (𝓝 (weakGrad (fun z => Real.sqrt (ρ z)) x k)))
    (hL1 : Tendsto (fun n => ∫⁻ x, ‖heatT (s n) ρ x - ρ x‖ₑ ∂haar d) atTop (𝓝 0)) :
    Tendsto (fun n => dissipation V W (heatT (s n) ρ)) atTop (𝓝 (dissipation V W ρ)) := by
  set u : Torus d → ℝ := fun x => Real.sqrt (ρ x) with hudef
  set gu := weakGrad u
  set ρs : ℕ → Torus d → ℝ := fun n => heatT (s n) ρ with hρsdef
  have hρi := h.integrable
  have hui : Integrable u (haar d) := h.h1.2.1.integrable one_le_two
  have hu2f := memLp_two_lintegral_ne_top h.h1.2.1
  have hρs := fun n => h.heatT_h1Dens (hs0 n)
  have hρsi : ∀ n, Integrable (ρs n) (haar d) := fun n => (hρs n).integrable
  have hρsc : ∀ n, Continuous (ρs n) := fun n => continuous_heatT (hs0 n) hρi
  rw [dissipation_eq_of hyp hρi h.h1 h.isWeakGrad]
  have e : ∀ n, dissipation V W (ρs n) = ∑ k, ∫⁻ x, ‖2 * sqrtHeatGrad (s n) ρ x k +
      Real.sqrt (ρs n x) * (lipGrad V x k + bForceL W (ρs n) x k)‖ₑ ^ 2 ∂haar d := fun n =>
    dissipation_eq_of hyp (hρsi n) (hρs n).h1 (h.isWeakGrad_sqrt_heatT (hs0 n))
  refine Tendsto.congr (fun n => (e n).symm) (tendsto_finsetSum _ fun k _ => ?_)
  -- constants
  obtain ⟨Cb₀, hCb₀⟩ := bGrad_bdd hyp (W := W)
  set Cb := max Cb₀ 0
  have hCb : ∀ x y k, |bGrad W x y k| ≤ Cb := fun x y k => (hCb₀ x y k).trans (le_max_left _ _)
  set LV : ℝ := ((Real.toNNReal (KV * Fintype.card (Fin d) / 2) : NNReal) : ℝ)
  have hLV : ∀ x k, |lipGrad V x k| ≤ LV := fun x k => abs_lipGrad_le (lipschitz_V hyp (W := W)) x k
  have hsqrtL2 := h.L2Tendsto_sqrt_heatT hs0 hL1
  have h1 := h.L2Tendsto_sqrtHeatGrad hs0 hgae k
  have hmb : ∀ j x, |lipGrad V x k + bForceL W (ρs j) x k| ≤ LV + Cb := fun j x =>
    (abs_add_le _ _).trans (add_le_add (hLV x k)
      (abs_bForceL_le hyp (hρs j).nonneg (hρs j).one hCb x k))
  have hmb0 : ∀ x, |lipGrad V x k + bForceL W ρ x k| ≤ LV + Cb := fun x =>
    (abs_add_le _ _).trans (add_le_add (hLV x k) (abs_bForceL_le hyp h.nonneg h.one hCb x k))
  have hmm : ∀ j, Measurable fun x => lipGrad V x k + bForceL W (ρs j) x k := fun j =>
    (measurable_lipGrad hyp.continuous_V k).add (measurable_bForceL' hyp (hρsi j) k)
  have hmm0 : Measurable fun x => lipGrad V x k + bForceL W ρ x k :=
    (measurable_lipGrad hyp.continuous_V k).add (measurable_bForceL' hyp hρi k)
  have hez : Tendsto (fun j => Cb * (∫⁻ y, ‖ρs j y - ρ y‖ₑ ∂haar d).toReal) atTop (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1).const_mul Cb
    simpa using this
  have hbF : ∀ x, Tendsto (fun j => bForceL W (ρs j) x k) atTop (𝓝 (bForceL W ρ x k)) :=
    fun x => tendsto_of_abs_le hL1 fun j => abs_bForceL_sub_le hyp (hρsi j) hρi hCb x k
  have h2 := L2Tendsto.mul_bdd (μ := haar d)
    (m := fun j x => lipGrad V x k + bForceL W (ρs j) x k)
    (m₀ := fun x => lipGrad V x k + bForceL W ρ x k) (M := LV + Cb) hsqrtL2 hmb hmb0
    (fun j => (hmm j).aemeasurable.mul
      ((Real.continuous_sqrt.comp (hρsc j)).measurable.aemeasurable.sub hui.aemeasurable))
    (fun j => ((hmm j).sub hmm0).aemeasurable.mul hui.aemeasurable)
    (Eventually.of_forall fun x => by
      have hb : ∀ j, |((lipGrad V x k + bForceL W (ρs j) x k) -
          (lipGrad V x k + bForceL W ρ x k)) * u x| ≤
          Cb * (∫⁻ y, ‖ρs j y - ρ y‖ₑ ∂haar d).toReal * |u x| := fun j => by
        rw [abs_mul, add_sub_add_left_eq_sub]
        exact mul_le_mul_of_nonneg_right
          (abs_bForceL_sub_le hyp (hρsi j) hρi hCb x k) (abs_nonneg _)
      have hz := hez.mul_const |u x|
      rw [zero_mul] at hz
      exact squeeze_zero_norm (fun j => by rw [Real.norm_eq_abs]; exact hb j) hz) hu2f
  have hGm : ∀ j, AEMeasurable (fun x => 2 * sqrtHeatGrad (s j) ρ x k - 2 * gu x k) (haar d) :=
    fun j => ((h.continuous_sqrtHeatGrad (hs0 j) k).measurable.aemeasurable.const_mul 2).sub
      ((h.isWeakGrad.aestronglyMeasurable_grad k).aemeasurable.const_mul 2)
  have h3 := (h1.const_mul 2).add h2 hGm
  have hΨ : L2Tendsto (haar d)
      (fun j x => 2 * sqrtHeatGrad (s j) ρ x k + Real.sqrt (ρs j x) *
        (lipGrad V x k + bForceL W (ρs j) x k))
      (fun x => 2 * gu x k + u x * (lipGrad V x k + bForceL W ρ x k)) :=
    h3.of_le fun j x => le_of_eq (by congr 2; ring)
  refine hΨ.tendsto_lintegral_sq (fun j => ?_) ?_ ?_ (h.lintegral_psi_ne_top hyp k)
  · exact (((h.continuous_sqrtHeatGrad (hs0 j) k).measurable.const_mul 2).add
      ((Real.continuous_sqrt.comp (hρsc j)).measurable.mul (hmm j))).aemeasurable
  · exact ((h.isWeakGrad.aestronglyMeasurable_grad k).aemeasurable.const_mul 2).add
      (hui.aemeasurable.mul hmm0.aemeasurable)
  · filter_upwards [hρae, hgae] with x hx hgx
    exact ((hgx k).const_mul 2).add (((Real.continuous_sqrt.tendsto _).comp hx).mul
      (tendsto_const_nhds.add (hbF x)))

/-- `G(ρ_n) → G(ρ)` along the sequence. -/
theorem tendsto_gap_seq (hyp : Hyp V W KV KW) {s : ℕ → ℝ} (hs0 : ∀ n, 0 < s n)
    (hρae : ∀ᵐ x ∂haar d, Tendsto (fun n => heatT (s n) ρ x) atTop (𝓝 (ρ x)))
    (hL1 : Tendsto (fun n => ∫⁻ x, ‖heatT (s n) ρ x - ρ x‖ₑ ∂haar d) atTop (𝓝 0)) :
    Tendsto (fun n => gap V W (densMeasure (heatT (s n) ρ))) atTop
      (𝓝 (gap V W (densMeasure ρ))) := by
  set ρs : ℕ → Torus d → ℝ := fun n => heatT (s n) ρ with hρsdef
  have hρs := fun n => h.heatT_h1Dens (hs0 n)
  have hK := klDiv_ne_top_of_H1 h.nonneg h.one h.h1
  have hKn : ∀ n, klDiv (densMeasure (ρs n)) (haar d) ≤ klDiv (densMeasure ρ) (haar d) :=
    fun n => by
    rw [klDiv_densMeasure' (hρs n).nonneg (hρs n).one, klDiv_densMeasure' h.nonneg h.one]
    exact lintegral_klFun_heatT_le (hs0 n) h.nonneg h.integrable
  have hKnt : ∀ n, klDiv (densMeasure (ρs n)) (haar d) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top hK (hKn n)
  have hKl := klDiv_le_liminf h.nonneg h.one (fun n => (hρs n).nonneg) (fun n => (hρs n).one)
    (fun n => (continuous_heatT (hs0 n) h.integrable).measurable) hρae
  have hKt : Tendsto (fun n => klDiv (densMeasure (ρs n)) (haar d)) atTop
      (𝓝 (klDiv (densMeasure ρ) (haar d))) :=
    tendsto_of_le_liminf_of_limsup_le hKl
      (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall hKn))
  have hEl : Tendsto (fun n => energyMF V W (densMeasure (ρs n))) atTop
      (𝓝 (energyMF V W (densMeasure ρ))) :=
    (potE_tendsto hyp h.nonneg h.one (fun n => (hρs n).nonneg) (fun n => (hρs n).one) hL1).add
      ((interE_tendsto hyp h.nonneg h.one (fun n => (hρs n).nonneg) (fun n => (hρs n).one)
        hL1).div_const 2)
  rw [gap_eq_coe hyp hK]
  refine Tendsto.congr (fun n => (gap_eq_coe hyp (hKnt n)).symm) ?_
  exact (continuous_coe_real_ereal.tendsto _).comp
    ((((ENNReal.tendsto_toReal hK).comp hKt).add hEl).sub_const _)

end H1Dens

end SharpLSI
