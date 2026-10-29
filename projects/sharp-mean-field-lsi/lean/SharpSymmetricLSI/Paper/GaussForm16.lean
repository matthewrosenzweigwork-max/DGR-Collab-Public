import SharpSymmetricLSI.Paper.GaussForm15
import SharpSymmetricLSI.Paper.GaussLaw9
import SharpSymmetricLSI.Paper.ULimit4

/-!
# R32 (C2): the row variables `(Tz)_i` and closability conditional on Proposition 2.1

* Under `γ` with covariance `C`, `∫ (∑_{i∈s} vᵢzᵢ)² dγ = ⟨v, Cv⟩` (`integral_linSum_sq_gamma`).
* If `⟨v, Cv⟩ ≤ |v|²/σ` and the row `(T_{iq})_q` is in `ℓ²`, the partial sums
  `∑_{q<n} T_{iq} z_q` are Cauchy in `L²(γ)`; their limit is the row variable
  (`exists_rowVariable`).
* Conditional on `Prop21Conclusion` (R02, still open), all hypotheses of
  `gaussForm_eval_eq_of_rowVariables` hold: `gaussForm_eq_on_cyl_of_prop21`.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped InnerProductSpace ENNReal

namespace SharpLSI

section gauss
variable {γ : Measure (ℕ → ℝ)} {C : ℕ → ℕ → ℝ}

theorem measurable_linSum (s : Finset ℕ) (v : ℕ → ℝ) :
    Measurable fun z : ℕ → ℝ => ∑ i ∈ s, v i * z i :=
  Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _

theorem memLp_linSum_gamma (hγ : IsCenteredGaussianCov γ C) (s : Finset ℕ) (v : ℕ → ℝ) :
    MemLp (fun z : ℕ → ℝ => ∑ i ∈ s, v i * z i) 2 γ :=
  memLp_finsetSum (ε' := ℝ) _ fun i _ => (memLp_coord_gamma hγ i).const_mul (v i)

/-- `∫ (∑ vᵢzᵢ)² dγ = ⟨v, Cv⟩`. -/
theorem integral_linSum_sq_gamma (hγ : IsCenteredGaussianCov γ C) (s : Finset ℕ) (v : ℕ → ℝ)
    (h0 : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j) :
    ∫ z, (∑ i ∈ s, v i * z i) ^ 2 ∂γ = ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j := by
  have := hγ.1
  rw [show (∫ z, (∑ i ∈ s, v i * z i) ^ 2 ∂γ) =
      ∫ z, (fun x : ℝ => x ^ 2) (∑ i ∈ s, v i * z i) ∂γ from rfl,
    ← integral_map (measurable_linSum s v).aemeasurable (continuous_pow 2).aestronglyMeasurable,
    hγ.2 s v]
  have h := variance_id_gaussianReal (μ := 0)
    (v := (∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j).toNNReal)
  rw [variance_of_integral_eq_zero measurable_id.aemeasurable (by simp [integral_id_gaussianReal]),
    Real.coe_toNNReal _ h0] at h
  simpa using h

theorem eLpNorm_two_eq_sqrt_gamma {f : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 γ) :
    eLpNorm f 2 γ = ENNReal.ofReal (√(∫ z, f z ^ 2 ∂γ)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, Real.sqrt_eq_rpow]
  congr 1
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, one_div]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [Real.rpow_two, sq_abs]

variable {T : ℕ → ℕ → ℝ} {σ : ℝ}

/-- **The row variables exist** when `0 ≤ ⟨v,Cv⟩ ≤ |v|²/σ` and the row of `T` is in `ℓ²`. -/
theorem exists_rowVariable (hγ : IsCenteredGaussianCov γ C) (hσ0 : 0 < σ)
    (hnn : ∀ (s : Finset ℕ) (v : ℕ → ℝ), 0 ≤ ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j)
    (hup : ∀ (s : Finset ℕ) (v : ℕ → ℝ),
      ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j ≤ (∑ i ∈ s, v i ^ 2) / σ)
    {i : ℕ} (hrow : Summable fun q => T i q ^ 2) :
    ∃ Y, IsRowVariable T γ i Y := by
  have := hγ.1
  set S : ℕ → (ℕ → ℝ) → ℝ := fun n z => ∑ q ∈ Finset.range n, T i q * z q with hSdef
  have hmem : ∀ n, MemLp (S n) 2 γ := fun n => memLp_linSum_gamma hγ _ _
  set t : ℕ → ℝ := fun N => √((∑' k, T i (k + N) ^ 2) / σ) with ht
  have hdiff : ∀ N n, N ≤ n → eLpNorm (S n - S N) 2 γ ≤ ENNReal.ofReal (t N) := by
    intro N n hNn
    have hfun : S n - S N = fun z => ∑ q ∈ Finset.Ico N n, T i q * z q := by
      funext z
      simp only [Pi.sub_apply, hSdef, Finset.sum_Ico_eq_sub _ hNn]
    rw [hfun, eLpNorm_two_eq_sqrt_gamma (memLp_linSum_gamma hγ _ _), integral_linSum_sq_gamma hγ _ _ (hnn _ _)]
    refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ((hup _ _).trans ?_))
    refine div_le_div_of_nonneg_right ?_ hσ0.le
    rw [Finset.sum_Ico_eq_sum_range]
    simp_rw [add_comm N]
    exact Summable.sum_le_tsum _ (fun _ _ => sq_nonneg _) ((summable_nat_add_iff N).2 hrow)
  have htt : Tendsto t atTop (𝓝 0) := by
    have := ((tendsto_sum_nat_add fun q => T i q ^ 2).div_const σ).sqrt
    simpa [ht] using this
  set F : ℕ → Lp ℝ 2 γ := fun n => (hmem n).toLp (S n) with hF
  have hcau : CauchySeq F := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (htt.eventually (gt_mem_nhds hε))
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm, hF, ← MemLp.toLp_sub, Lp.norm_toLp]
    calc (eLpNorm (S n - S N) 2 γ).toReal ≤ t N :=
          ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg _) (hdiff N n hn)
      _ < ε := hN N le_rfl
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨G, Lp.memLp G, ?_⟩
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hG
  refine hG.congr fun n => eLpNorm_congr_ae ?_
  filter_upwards [(hmem n).coeFn_toLp] with z hz
  exact congrArg (· - G z) hz

end gauss

/-! ### Conditional on Proposition 2.1 -/

section prop21
variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
  (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  (h21 : Prop21Conclusion V W μ)
  {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
include hyp hμ he h21 hC

/-- Positive semidefinite finite blocks of `C`, conditional on Prop. 2.1. -/
theorem blockMat_posSemidef_of_prop21 (N : ℕ) : (blockMat C N).PosSemidef := by
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  exact blockMat_posSemidef (Tmat_symm hyp hμ he) (hasSum_Tmat_sq hyp hμ he).summable hσ0 hσ hC N

/-- The row variables `(Tz)_i ∈ L²(γ)`, conditional on Prop. 2.1. -/
theorem exists_rowVariables_of_prop21 {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C) :
    ∃ Y : ℕ → (ℕ → ℝ) → ℝ, ∀ i, IsRowVariable (Tmat W μ e) γ i (Y i) := by
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  have hT := Tmat_symm hyp hμ he
  have hS := (hasSum_Tmat_sq hyp hμ he).summable
  have hY : ∀ i, ∃ Y, IsRowVariable (Tmat W μ e) γ i Y := fun i =>
    exists_rowVariable hγ hσ0 (quadC_nonneg hT hS hσ0 hσ hC) (quadC_le hT hS hσ0 hσ hC)
      (hS.prod_factor i)
  exact ⟨fun i => (hY i).choose, fun i => (hY i).choose_spec⟩

/-- **Closability of (8.1), conditional on Prop. 2.1**: `ℰ_∞` agrees with (8.1) on cylinders. -/
theorem gaussForm_eq_on_cyl_of_prop21 {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    (c : Cyl) : gaussForm (lamShift lam) γ c.eval = c.form (lamShift lam) γ := by
  obtain ⟨Y, hY⟩ := exists_rowVariables_of_prop21 hyp hμ he h21 hC hγ
  exact gaussForm_eval_eq_of_rowVariables hγ (blockMat_posSemidef_of_prop21 hyp hμ he h21 hC) hC
    hY (fun i => he.lam_nonneg' (i + 1)) c

end prop21

end SharpLSI
