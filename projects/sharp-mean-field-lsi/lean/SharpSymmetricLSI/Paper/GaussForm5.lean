import SharpSymmetricLSI.Paper.GaussForm4
import SharpSymmetricLSI.Defs.D18_GaussianForm

/-!
# R32 (A5): the Gaussian integration by parts with the row variables

For `C = (I+T)⁻¹` (`IsInverseOfIPlus`), `Y` the `L²(γ)` row variable `(Tz)_i`
(`IsRowVariable`), and `g` a function of the first `J` coordinates (`i < J`):
`∫ (z_i + Y) g(z_{<J}) dγ = ∫ ∂_i g(z_{<J}) dγ` (`stein_row`).
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Matrix
open scoped NNReal MatrixOrder ENNReal

namespace SharpLSI

variable {γ : Measure (ℕ → ℝ)} {C : ℕ → ℕ → ℝ}

theorem integrable_coord_gamma (hγ : IsCenteredGaussianCov γ C) (q : ℕ) :
    Integrable (fun z : ℕ → ℝ => z q) γ := by
  haveI := hγ.1
  have h := hγ.2 {q} (fun _ => 1)
  simp only [Finset.sum_singleton, one_mul] at h
  have hm : Measurable fun z : ℕ → ℝ => z q := measurable_pi_apply q
  have hi : Integrable id (γ.map fun z : ℕ → ℝ => z q) := by
    rw [h]; exact (memLp_id_gaussianReal 1).integrable le_rfl
  exact (integrable_map_measure aestronglyMeasurable_id hm.aemeasurable).1 hi

/-- `∑' k, T_{ik} C_{kl} = δ_{il} - C_{il}`. -/
theorem tsum_T_mul_C {T : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus T C) (i l : ℕ) :
    Summable (fun k => T i k * C k l) ∧
      ∑' k, T i k * C k l = (if i = l then 1 else 0) - C i l := by
  obtain ⟨-, hrow⟩ := hC l
  obtain ⟨hs, heq⟩ := hrow i
  have hδ : Summable fun k => (if i = k then 1 else 0) * C k l :=
    summable_of_ne_finset_zero (s := {i}) fun k hk => by
      simp only [Finset.mem_singleton] at hk; simp [Ne.symm hk]
  have hsum : Summable fun k => ((if i = k then 1 else 0) + T i k) * C k l := hs.of_abs
  have hT : Summable fun k => T i k * C k l :=
    (hsum.sub hδ).congr fun k => by ring
  refine ⟨hT, ?_⟩
  have hδv : ∑' k, (if i = k then (1 : ℝ) else 0) * C k l = C i l := by
    have : (fun k => (if i = k then (1 : ℝ) else 0) * C k l) = fun k => if k = i then C i l else 0 := by
      funext k
      by_cases h : k = i
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [this, tsum_ite_eq]
  have e2 : ∑' k, ((if i = k then 1 else 0) + T i k) * C k l =
      ∑' k, (if i = k then (1 : ℝ) else 0) * C k l + ∑' k, T i k * C k l := by
    rw [← hδ.tsum_add hT]; congr 1; funext k; ring
  rw [heq, hδv] at e2
  linarith

/-- **Gaussian integration by parts with the row variable** `Y ≈ (Tz)_i`. -/
theorem stein_row {T : ℕ → ℕ → ℝ} (hγ : IsCenteredGaussianCov γ C)
    (hPSD : ∀ N, (blockMat C N).PosSemidef) (hC : IsInverseOfIPlus T C) {i : ℕ}
    {Y : (ℕ → ℝ) → ℝ} (hY : IsRowVariable T γ i Y) {J : ℕ} {g : (Fin J → ℝ) → ℝ}
    (hg : Differentiable ℝ g) (hgc : Continuous fun y => fderiv ℝ g y) {B : ℝ}
    (hgB : ∀ y, |g y| ≤ B) (hdB : ∀ y, ‖fderiv ℝ g y‖ ≤ B) (hiJ : i < J) :
    ∫ z, (z i + Y z) * g (zBlock J z) ∂γ =
      ∫ z, fderiv ℝ g (zBlock J z) (Pi.single ⟨i, hiJ⟩ 1) ∂γ := by
  haveI := hγ.1
  set D : Fin J → ℝ := fun l => ∫ z, fderiv ℝ g (zBlock J z) (Pi.single l 1) ∂γ with hD
  have hst := fun q => stein_gamma_nat hγ hPSD hg hgc hgB hdB q
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB 0)
  have hgm : Measurable fun z => g (zBlock J z) := hg.continuous.measurable.comp (measurable_zBlock J)
  have hgb : ∀ᵐ z ∂γ, ‖g (zBlock J z)‖ ≤ B := Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]; exact hgB _
  have hzi : ∀ q, Integrable (fun z : ℕ → ℝ => z q * g (zBlock J z)) γ := fun q =>
    ((integrable_coord_gamma hγ q).bdd_mul hgm.aestronglyMeasurable hgb).congr
      (Eventually.of_forall fun z => mul_comm _ _)
  set Sn : ℕ → (ℕ → ℝ) → ℝ := fun n z => ∑ q ∈ Finset.range n, T i q * z q
  have h1 : ∀ n, ∫ z, Sn n z * g (zBlock J z) ∂γ =
      ∑ l : Fin J, (∑ q ∈ Finset.range n, T i q * C q l) * D l := fun n => by
    simp only [Sn, Finset.sum_mul]
    rw [integral_finsetSum _ fun q _ => ((hzi q).const_mul (T i q)).congr
      (Eventually.of_forall fun z => by ring)]
    have : ∀ q, ∫ z, T i q * z q * g (zBlock J z) ∂γ = T i q * ∑ l : Fin J, C q l * D l := fun q => by
      rw [← hst q, ← integral_const_mul]; congr 1; funext z; ring
    simp_rw [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun q _ => by ring
  have hYi : Integrable (fun z => Y z * g (zBlock J z)) γ :=
    ((hY.1.integrable one_le_two).bdd_mul hgm.aestronglyMeasurable hgb).congr
      (Eventually.of_forall fun z => mul_comm _ _)
  have hSi : ∀ n, Integrable (fun z => Sn n z * g (zBlock J z)) γ := fun n => by
    have := integrable_finsetSum (Finset.range n) fun q _ => (hzi q).const_mul (T i q)
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [Sn, Finset.sum_mul]
    exact Finset.sum_congr rfl fun q _ => by ring
  have h2 : Tendsto (fun n => ∫ z, Sn n z * g (zBlock J z) ∂γ) atTop
      (𝓝 (∫ z, Y z * g (zBlock J z) ∂γ)) := by
    refine tendsto_integral_of_L1 _ hYi.aestronglyMeasurable (Eventually.of_forall hSi) ?_
    have hup := ENNReal.Tendsto.const_mul hY.2 (a := ENNReal.ofReal B) (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => bot_le)
      fun n => ?_
    have hSnm : Measurable (Sn n) :=
      Finset.measurable_sum _ fun q _ => measurable_const.mul (measurable_pi_apply q)
    have hSm : AEStronglyMeasurable (fun z => Sn n z - Y z) γ :=
      hSnm.aestronglyMeasurable.sub hY.1.aestronglyMeasurable
    calc ∫⁻ z, ‖Sn n z * g (zBlock J z) - Y z * g (zBlock J z)‖ₑ ∂γ
        ≤ ∫⁻ z, ENNReal.ofReal B * ‖Sn n z - Y z‖ₑ ∂γ := lintegral_mono fun z => by
          rw [← sub_mul, enorm_mul, mul_comm]
          refine mul_le_mul_left ?_ _
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact hgB _)
      _ = ENNReal.ofReal B * eLpNorm (fun z => Sn n z - Y z) 1 γ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, eLpNorm_one_eq_lintegral_enorm]
          exact hSm
      _ ≤ ENNReal.ofReal B * eLpNorm (fun z => Sn n z - Y z) 2 γ :=
          mul_le_mul_right (eLpNorm_le_eLpNorm_of_exponent_le (p := 1) (q := 2) (by norm_num)) _
  -- the limit of the coefficients
  have h3 : Tendsto (fun n => ∑ l : Fin J, (∑ q ∈ Finset.range n, T i q * C q l) * D l) atTop
      (𝓝 (∑ l : Fin J, (∑' q, T i q * C q l) * D l)) :=
    tendsto_finsetSum _ fun l _ =>
      ((tsum_T_mul_C hC i l).1.hasSum.tendsto_sum_nat).mul_const _
  have hYg : ∫ z, Y z * g (zBlock J z) ∂γ = ∑ l : Fin J, (∑' q, T i q * C q l) * D l := by
    refine tendsto_nhds_unique h2 ?_
    simp_rw [h1]; exact h3
  rw [show (fun z => (z i + Y z) * g (zBlock J z)) =
      fun z => z i * g (zBlock J z) + Y z * g (zBlock J z) from funext fun z => add_mul _ _ _,
    integral_add (hzi i) hYi, hst i, hYg, ← Finset.sum_add_distrib]
  simp_rw [(tsum_T_mul_C hC i _).2]
  rw [Finset.sum_eq_single ⟨i, hiJ⟩]
  · simp only [hD, ite_true]; ring
  · intro l _ hl
    have : i ≠ (l : ℕ) := fun h => hl (Fin.ext h.symm)
    simp only [this, ite_false]; ring
  · simp

end SharpLSI
