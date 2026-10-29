import SharpSymmetricLSI.Paper.GaussLaw10

/-!
# R27 assembly: (6.10), Lemma 6.1, (6.11), conditional on Proposition 2.1 and Lemma 5.2

`gaussian_limit_law_of` proves the conclusion of `gaussian_limit_law` from
* `Prop21Conclusion V W μ` (Proposition 2.1: `I + T ≥ σ`), and
* the partition estimates of Lemma 5.2 (R19 `reference_entropy`): `|log K_N| ≤ B` and
  `∫ (e^{-U_N}/K_N)^p dμ^{⊗N} ≤ B` for some `p > 1`.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped InnerProductSpace BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem integral_exp_pow_le (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {N : ℕ} {B p : ℝ} (hp : 1 < p) (hlog : |Real.log (centeredPartition W μ N)| ≤ B)
    (hint : ∫ X, (rexp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
      ∂Measure.pi (fun _ : Fin N => μ) ≤ B) :
    ∫ X, rexp (-Ucentered W μ N X) ^ p ∂Measure.pi (fun _ : Fin N => μ) ≤ rexp B ^ p * B := by
  obtain ⟨BU, hBU⟩ := Ucentered_bdd hyp μ N
  have hK : rexp (-BU) ≤ centeredPartition W μ N := by
    unfold centeredPartition
    have := integral_mono (μ := Measure.pi fun _ : Fin N => μ) (integrable_const (rexp (-BU)))
      (Integrable.of_bound ((measurable_Ucentered hyp μ N).neg.exp).aestronglyMeasurable (rexp BU)
        (Eventually.of_forall fun X => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_exp.2 (by
            have := hBU X; rw [abs_le] at this; simp only [Pi.neg_apply]; linarith)))
      (fun X => Real.exp_le_exp.2 (by
        have := hBU X; rw [abs_le] at this; simp only [Pi.neg_apply]; linarith))
    simpa using this
  have hKpos : 0 < centeredPartition W μ N := (Real.exp_pos _).trans_le hK
  set K := centeredPartition W μ N
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hlog
  have hKle : K ≤ rexp B := by
    rw [← Real.exp_log hKpos]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans hlog)
  have hpt : ∀ X, rexp (-Ucentered W μ N X) ^ p = K ^ p * (rexp (-Ucentered W μ N X) / K) ^ p :=
    fun X => by
      rw [Real.div_rpow (Real.exp_pos _).le hKpos.le]
      field_simp
  simp_rw [hpt]
  rw [integral_const_mul]
  have h0 : 0 ≤ ∫ X, (rexp (-Ucentered W μ N X) / K) ^ p ∂Measure.pi (fun _ : Fin N => μ) :=
    integral_nonneg fun X => Real.rpow_nonneg (div_nonneg (Real.exp_pos _).le hKpos.le) _
  exact mul_le_mul (Real.rpow_le_rpow hKpos.le hKle (by linarith)) hint h0
    (Real.rpow_nonneg (Real.exp_pos _).le _)

/-- **(6.10), Lemma 6.1, (6.11)**, conditional on Proposition 2.1 and the partition estimates. -/
theorem gaussian_limit_law_of (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (h21 : Prop21Conclusion V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {Q : (ℕ → ℝ) → ℝ} (hQ : IsSecondChaos (Tmat W μ e) Q)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    (hpart : ∃ B p : ℝ, 1 < p ∧ ∀ N : ℕ, 1 ≤ N →
      |Real.log (centeredPartition W μ N)| ≤ B ∧
      ∫ X, (Real.exp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ B) :
    Tendsto (fun N => centeredPartition W μ N) atTop (𝓝 (Kinf W μ Q)) ∧ 0 < Kinf W μ Q ∧
    IsCenteredGaussianCov (gammaInfOf W μ Q) C ∧
    ∀ (J : ℕ) (g : (Fin J → ℝ) →ᵇ ℝ),
      Tendsto (fun N : ℕ => ∫ X, g (fun n => fluct e N n X) ∂gibbs V W N) atTop
        (𝓝 (∫ z, g (fun n => z n) ∂gammaInfOf W μ Q)) := by
  set μm := (μ : Measure (Torus d))
  have hμ := h21.minimizer
  have hT := Tmat_symm hyp hμ he
  have hS := (hasSum_Tmat_sq hyp hμ he).summable
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  obtain ⟨B, p, hp, hB⟩ := hpart
  have hB' : ∀ N : ℕ, 1 ≤ N → ∫ X, rexp (-Ucentered W μ N X) ^ p
      ∂Measure.pi (fun _ : Fin N => μm) ≤ rexp B ^ p * B := fun N hN =>
    integral_exp_pow_le hyp hp (hB N hN).1 (hB N hN).2
  have hint := integrable_exp_neg_Uinf (W := W) (μ := μm) hT hS hσ0 hσ hQ
  have hKinf := Kinf_pos (W := W) (μ := μm) hT hS hσ0 hσ hQ
  have hw := fun {J : ℕ} (g : (Fin J → ℝ) →ᵇ ℝ) => tendsto_weighted hyp hμ he hQ hint hp hB' g
  have hKN : Tendsto (fun N => centeredPartition W μ N) atTop (𝓝 (Kinf W μ Q)) := by
    have := hw (BoundedContinuousFunction.const (Fin 0 → ℝ) (1 : ℝ))
    simpa only [BoundedContinuousFunction.const_apply, one_mul, centeredPartition, Kinf] using this
  refine ⟨hKN, hKinf, isCenteredGaussianCov_gammaInf hT hS hσ0 hσ hQ hC, fun J g => ?_⟩
  have hgibbs : ∀ N : ℕ, ∫ X, g (fun n => fluct e N n X) ∂gibbs V W N =
      (∫ X, g (fun n => fluct e N n X) * rexp (-Ucentered W μ N X)
        ∂Measure.pi (fun _ : Fin N => μm)) / centeredPartition W μ N := by
    intro N
    have hm := measurable_Ucentered hyp μm N
    rw [gibbs_eq_centered_aux hyp hμ N, integral_withDensity_eq_integral_toReal_smul
      (by fun_prop : Measurable fun X : Config N d =>
        ENNReal.ofReal (rexp (-Ucentered W μ N X) / centeredPartition W μ N))
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    have hK0 : 0 ≤ centeredPartition W μ N :=
      integral_nonneg fun X => (Real.exp_pos _).le
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hK0)]
    ring
  simp_rw [hgibbs]
  have hlim := (hw g).div hKN hKinf.ne'
  convert hlim using 2
  rw [integral_gammaInf hT hS hσ0 hσ hQ, ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  ring

end SharpLSI
