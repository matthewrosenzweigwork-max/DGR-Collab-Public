import SharpSymmetricLSI.Paper.GroundT10

/-!
# R30 groundwork: partition limits, second moments of `U_N`, rescaled ground states
-/

open MeasureTheory InformationTheory Set Filter Topology Real
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem memLp_of_memH1C_pi {μ : Measure (Torus d)} {N : ℕ} {u : Config N d → ℝ}
    (hu : MemH1C (Measure.pi fun _ : Fin N => μ) u) : MemLp u 2 (Measure.pi fun _ : Fin N => μ) := by
  have h := hu.2.1
  rw [memLp_map_measure_iff h.aestronglyMeasurable measurable_flat.aemeasurable] at h
  exact h

/-- `K_N → K_∞ > 0` and the exponential moments, from Prop. 2.1 and the partition estimates. -/
theorem partition_limit_of (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (h21 : Prop21Conclusion V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {Q : (ℕ → ℝ) → ℝ} (hQ : IsSecondChaos (Tmat W μ e) Q)
    (hpart : ∃ B p : ℝ, 1 < p ∧ ∀ N : ℕ, 1 ≤ N →
      |Real.log (centeredPartition W μ N)| ≤ B ∧
      ∫ X, (Real.exp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ B) :
    Tendsto (fun N => centeredPartition W μ N) atTop (𝓝 (Kinf W μ Q)) ∧ 0 < Kinf W μ Q ∧
      Integrable (fun z => rexp (-Uinf W μ Q z)) gammaRef ∧
      ∃ q Bq : ℝ, 1 < q ∧ ∀ N : ℕ, 1 ≤ N → ∫ X, rexp (-Ucentered W μ N X) ^ q
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ Bq := by
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
  have hKN : Tendsto (fun N => centeredPartition W μ N) atTop (𝓝 (Kinf W μ Q)) := by
    have := tendsto_weighted hyp hμ he hQ hint hp hB'
      (BoundedContinuousFunction.const (Fin 0 → ℝ) (1 : ℝ))
    simpa only [BoundedContinuousFunction.const_apply, one_mul, centeredPartition, Kinf] using this
  exact ⟨hKN, hKinf, hint, p, _, hp, hB'⟩

/-- `∫ U_N² dμ^{⊗N}` is bounded uniformly in `N`. -/
theorem integral_Ucentered_sq_le (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    ∃ CU : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∫ X, Ucentered W μ N X ^ 2 ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ CU := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨BK, hBK⟩ := centeredKernel_bdd hyp μm
  obtain ⟨hdec, hsq, -, -⟩ := U_limit_aux hyp hμ he
  refine ⟨BK ^ 2 + BK ^ 2 / 2, fun N hN => ?_⟩
  set Q := Measure.pi fun _ : Fin N => μm
  have hKm := measurable_centeredKernel hyp μm
  set O : Config N d → ℝ := fun X =>
    (N : ℝ)⁻¹ * ∑ i, ∑ j, if i < j then centeredKernel W μ (X i) (X j) else 0
  set D : Config N d → ℝ := fun X => (2 * (N : ℝ))⁻¹ * ∑ i, centeredKernel W μ (X i) (X i)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hD : ∀ X, |D X| ≤ BK / 2 := fun X => by
    simp only [D]
    rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 * N)]
    have : |∑ i, centeredKernel W μ (X i) (X i)| ≤ N * BK := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => hBK (X i) (X i)).trans ?_
      simp
    calc (2 * (N : ℝ))⁻¹ * |∑ i, centeredKernel W μ (X i) (X i)| ≤ (2 * (N : ℝ))⁻¹ * (N * BK) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = BK / 2 := by field_simp
  have hOm : Measurable O := by
    refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _
      fun j _ => ?_)
    refine Measurable.ite ?_ (by
      exact hKm.comp (by fun_prop : Measurable fun X : Config N d => (X i, X j)) :
        Measurable fun X : Config N d => centeredKernel W μm (X i) (X j)) measurable_const
    exact MeasurableSet.const _
  have hOb : ∃ C, ∀ X, |O X| ≤ C := by
    refine ⟨(N : ℝ)⁻¹ * (N * (N * |BK|)), fun X => ?_⟩
    simp only [O]
    rw [abs_mul, abs_inv, abs_of_pos hNr]
    have hrow : ∀ i : Fin N, |∑ j, (if i < j then centeredKernel W μ (X i) (X j) else 0)| ≤
        N * |BK| := fun i => by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (g := fun _ => |BK|)
        fun j _ => ?_).trans (by simp))
      split_ifs
      · exact (hBK _ _).trans (le_abs_self _)
      · simp
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun i _ => hrow i).trans (by simp))) (by positivity)
  obtain ⟨CO, hCO⟩ := hOb
  have hOi : Integrable (fun X => O X ^ 2) Q :=
    integrable_of_bdd (hOm.pow_const 2) (C := CO ^ 2) fun X => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCO X) 2
  obtain ⟨BU, hBU⟩ := Ucentered_bdd hyp μm N
  have hUi : Integrable (fun X => Ucentered W μ N X ^ 2) Q :=
    integrable_of_bdd ((measurable_Ucentered hyp μm N).pow_const 2) (C := BU ^ 2) fun X => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hBU X) 2
  have hpt : ∀ X, Ucentered W μ N X ^ 2 ≤ 2 * O X ^ 2 + BK ^ 2 / 2 := fun X => by
    rw [hdec N hN X]
    have := hD X
    have h2 : D X ^ 2 ≤ (BK / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    show (O X + D X) ^ 2 ≤ 2 * O X ^ 2 + BK ^ 2 / 2
    nlinarith [sq_nonneg (O X - D X)]
  have hKK : ∫ x, ∫ y, centeredKernel W μ x y ^ 2 ∂μm ∂μm ≤ BK ^ 2 := by
    refine (integral_mono_of_nonneg (Eventually.of_forall fun x => integral_nonneg fun _ =>
      sq_nonneg _) (integrable_const (BK ^ 2)) (Eventually.of_forall fun x => ?_)).trans ?_
    · refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
        (integrable_const (BK ^ 2)) (Eventually.of_forall fun y => ?_)).trans (by simp)
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hBK x y) 2
    · simp
  calc ∫ X, Ucentered W μ N X ^ 2 ∂Q ≤ ∫ X, (2 * O X ^ 2 + BK ^ 2 / 2) ∂Q :=
        integral_mono hUi ((hOi.const_mul 2).add (integrable_const _)) hpt
    _ = 2 * (((N : ℝ) - 1) / (2 * N) * ∫ x, ∫ y, centeredKernel W μ x y ^ 2 ∂μm ∂μm) +
          BK ^ 2 / 2 := by
        rw [integral_add (hOi.const_mul 2) (integrable_const _), integral_const_mul, hsq N hN,
          integral_const]
        simp only [probReal_univ, smul_eq_mul, one_mul]
        rfl
    _ ≤ 2 * (1 / 2 * BK ^ 2) + BK ^ 2 / 2 := by
        have h1 : ((N : ℝ) - 1) / (2 * N) ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]; linarith
        have h2 : 0 ≤ ((N : ℝ) - 1) / (2 * N) := by
          have : (1 : ℝ) ≤ N := by exact_mod_cast hN
          positivity
        have h3 : 0 ≤ ∫ x, ∫ y, centeredKernel W μ x y ^ 2 ∂μm ∂μm :=
          integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
        nlinarith [mul_le_mul h1 hKK h3 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ = BK ^ 2 + BK ^ 2 / 2 := by ring

end SharpLSI
