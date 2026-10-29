import SharpSymmetricLSI.Paper.GaussLaw7

/-!
# R27: Lemma 6.1, `γ_∞` is centered Gaussian with covariance `C = (I+T)⁻¹`

`γ_∞ = K_∞⁻¹ e^{-U_∞} γ`, `U_∞ = Q/2 + d_K/2`, so `K_∞ = e^{-d_K/2} ∫ e^{-Q/2} dγ ≥ e^{-d_K/2}`
and the moment generating function of `∑_{i∈s} vᵢ zᵢ` under `γ_∞` is `exp(t²⟨v,Cv⟩/2)`. Moment
generating functions finite on `ℝ` determine the law (complex MGF, Mathlib).
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped InnerProductSpace ENNReal

namespace SharpLSI

variable {d : ℕ} {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)}

theorem exp_neg_Uinf (Q : (ℕ → ℝ) → ℝ) (z : ℕ → ℝ) :
    rexp (-Uinf W μ Q z) = rexp (-(diagMean W μ / 2)) * rexp (-(Q z / 2)) := by
  rw [← Real.exp_add]; unfold Uinf; ring_nf

section gauss
variable {T : ℕ → ℕ → ℝ} (hT : ∀ i j, T i j = T j i)
  (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) {σ : ℝ} (hσ0 : 0 < σ)
  (hσ : ∀ n (y : EuclideanSpace ℝ (Fin n)), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ)
  {Q : (ℕ → ℝ) → ℝ} (hQ : IsSecondChaos T Q)
include hT hS hσ0 hσ hQ

theorem integrable_exp_neg_Q : Integrable (fun z => rexp (-(Q z / 2))) gammaRef := by
  have := (gauss_limit hT hS hσ0 hσ hQ ∅ (fun _ => 0) 0).1
  simpa only [Finset.sum_empty, mul_zero, zero_sub] using this

omit hT hS hσ0 hσ hQ in
theorem Kinf_eq : Kinf W μ Q = rexp (-(diagMean W μ / 2)) * ∫ z, rexp (-(Q z / 2)) ∂gammaRef := by
  unfold Kinf; simp_rw [exp_neg_Uinf]; rw [integral_const_mul]

theorem Kinf_pos : 0 < Kinf W μ Q := by
  rw [Kinf_eq]
  exact mul_pos (Real.exp_pos _) (zero_lt_one.trans_le (one_le_integral_exp_Q hT hS hσ0 hσ hQ))

theorem integrable_exp_neg_Uinf : Integrable (fun z => rexp (-Uinf W μ Q z)) gammaRef := by
  simp_rw [exp_neg_Uinf]; exact (integrable_exp_neg_Q hT hS hσ0 hσ hQ).const_mul _

theorem aemeasurable_dens : AEMeasurable
    (fun z => ENNReal.ofReal (rexp (-Uinf W μ Q z) / Kinf W μ Q)) gammaRef :=
  ENNReal.measurable_ofReal.comp_aemeasurable
    ((integrable_exp_neg_Uinf (W := W) (μ := μ) hT hS hσ0 hσ hQ).1.aemeasurable.div_const _)

theorem integral_gammaInf (g : (ℕ → ℝ) → ℝ) :
    ∫ z, g z ∂gammaInfOf W μ Q = ∫ z, rexp (-Uinf W μ Q z) / Kinf W μ Q * g z ∂gammaRef := by
  unfold gammaInfOf
  rw [integral_withDensity_eq_integral_toReal_smul₀ (aemeasurable_dens hT hS hσ0 hσ hQ)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le (Kinf_pos hT hS hσ0 hσ hQ).le)]

theorem isProbabilityMeasure_gammaInf : IsProbabilityMeasure (gammaInfOf W μ Q) := by
  constructor
  unfold gammaInfOf
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((integrable_exp_neg_Uinf hT hS hσ0 hσ hQ).div_const _)
      (Eventually.of_forall fun _ => div_nonneg (Real.exp_pos _).le
        (Kinf_pos hT hS hσ0 hσ hQ).le), integral_div]
  rw [show ∫ z, rexp (-Uinf W μ Q z) ∂gammaRef = Kinf W μ Q from rfl,
    div_self (Kinf_pos hT hS hσ0 hσ hQ).ne', ENNReal.ofReal_one]

variable {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus T C)
include hC

omit hQ in
theorem quadC_nonneg (s : Finset ℕ) (v : ℕ → ℝ) : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j := by
  refine ge_of_tendsto (tendsto_inner_secRes hT hS hσ0 hσ hC s v) (Eventually.of_forall fun n => ?_)
  rw [inner_secRes]
  exact Finset.sum_nonneg fun k _ => mul_nonneg
    (inv_nonneg.2 (secEig_pos hT hσ0 hσ n k).le) (sq_nonneg _)

theorem mgf_gammaInf (s : Finset ℕ) (v : ℕ → ℝ) (t : ℝ) :
    mgf (fun z => ∑ i ∈ s, v i * z i) (gammaInfOf W μ Q) t =
      rexp (t ^ 2 * (∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j) / 2) := by
  rw [mgf, integral_gammaInf hT hS hσ0 hσ hQ]
  have h : ∀ z, rexp (-Uinf W μ Q z) / Kinf W μ Q * rexp (t * ∑ i ∈ s, v i * z i) =
      rexp (-(diagMean W μ / 2)) / Kinf W μ Q * rexp (t * ∑ i ∈ s, v i * z i - Q z / 2) := by
    intro z
    rw [exp_neg_Uinf, sub_eq_add_neg, Real.exp_add]; ring
  simp_rw [h]
  rw [integral_const_mul, integral_exp_lin_sub_Q hT hS hσ0 hσ hQ hC, Kinf_eq]
  have h1 : 0 < ∫ z, rexp (-(Q z / 2)) ∂gammaRef :=
    zero_lt_one.trans_le (one_le_integral_exp_Q hT hS hσ0 hσ hQ)
  field_simp

/-- **Lemma 6.1.** -/
theorem isCenteredGaussianCov_gammaInf : IsCenteredGaussianCov (gammaInfOf W μ Q) C := by
  have := isProbabilityMeasure_gammaInf (W := W) (μ := μ) hT hS hσ0 hσ hQ
  refine ⟨this, fun s v => ?_⟩
  set w := ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j
  have hw : ((w.toNNReal : NNReal) : ℝ) = w := Real.coe_toNNReal _ (quadC_nonneg hT hS hσ0 hσ hC s v)
  have hL : AEMeasurable (fun z : ℕ → ℝ => ∑ i ∈ s, v i * z i) (gammaInfOf W μ Q) :=
    (by fun_prop : Measurable fun z : ℕ → ℝ => ∑ i ∈ s, v i * z i).aemeasurable
  have : IsProbabilityMeasure ((gammaInfOf W μ Q).map fun z => ∑ i ∈ s, v i * z i) :=
    (Measure.isProbabilityMeasure_map_iff hL).mpr inferInstance
  have hm : mgf id (gaussianReal 0 w.toNNReal) =
      mgf id ((gammaInfOf W μ Q).map fun z => ∑ i ∈ s, v i * z i) := by
    rw [mgf_id_map hL]
    funext t
    rw [mgf_gammaInf hT hS hσ0 hσ hQ hC, show (id : ℝ → ℝ) = fun x => x from rfl,
      mgf_fun_id_gaussianReal, hw]
    simp only [w]
    congr 1; ring
  have hset : interior (integrableExpSet id (gaussianReal 0 w.toNNReal)) = Set.univ := by
    rw [interior_eq_univ]
    ext t
    simp only [integrableExpSet, Set.mem_ofPred_eq, id, Set.mem_univ, iff_true]
    exact integrable_exp_mul_gaussianReal t
  refine (Measure.ext_of_complexMGF_id_eq ?_).symm
  funext z
  exact eqOn_complexMGF_of_mgf hm (by simp)

end gauss

end SharpLSI
