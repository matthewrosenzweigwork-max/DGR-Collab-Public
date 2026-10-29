import DGRHS.Gaussian.SeparableFeatureEvaluation

/-!
The actual continuous linear feature readout for the given square-integrable
Hilbert-valued map. No bounded-feature premise, spectrum, covariance operator,
Gram integral operator, adjoint or determinant is postulated here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology InnerProductSpace

namespace DGRHS.Gaussian

noncomputable section

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

private theorem memLp_readout {k : X → H} (hk2 : MemLp k 2 μ) (v : H) :
    MemLp (fun x => inner ℝ (k x) v) 2 μ := by
  apply hk2.of_le_mul (hk2.aestronglyMeasurable.inner aestronglyMeasurable_const)
  filter_upwards [] with x
  exact (norm_inner_le_norm (𝕜 := ℝ) (k x) v).trans_eq (mul_comm _ _)

private def readoutVector (k : X → H) (hk2 : MemLp k 2 μ) (v : H) : Lp ℝ 2 μ :=
  (memLp_readout hk2 v).toLp (fun x => inner ℝ (k x) v)

private theorem coeFn_readoutVector (k : X → H) (hk2 : MemLp k 2 μ) (v : H) :
    (readoutVector k hk2 v : X → ℝ) =ᵐ[μ] (fun x => inner ℝ (k x) v) :=
  (memLp_readout hk2 v).coeFn_toLp

private def readoutLinear (k : X → H) (hk2 : MemLp k 2 μ) : H →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := readoutVector k hk2
  map_add' v w := by
    apply Lp.ext
    filter_upwards [coeFn_readoutVector k hk2 (v + w), coeFn_readoutVector k hk2 v,
      coeFn_readoutVector k hk2 w, Lp.coeFn_add (readoutVector k hk2 v) (readoutVector k hk2 w)]
      with x hvw hv hw ha
    rw [ha, Pi.add_apply, hvw, hv, hw, inner_add_right]
  map_smul' a v := by
    change readoutVector k hk2 (a • v) = a • readoutVector k hk2 v
    apply Lp.ext
    filter_upwards [coeFn_readoutVector k hk2 (a • v), coeFn_readoutVector k hk2 v,
      Lp.coeFn_smul a (readoutVector k hk2 v)] with x hav hv hs
    rw [hs, Pi.smul_apply, hav, hv, inner_smul_right]
    rfl

private theorem readoutVector_norm_le (k : X → H) (hk2 : MemLp k 2 μ) (v : H) :
    ‖readoutVector k hk2 v‖ ≤ ‖hk2.toLp k‖ * ‖v‖ := by
  rw [mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coeFn_readoutVector k hk2 v, hk2.coeFn_toLp] with x hv hk
  rw [hv, hk]
  exact (norm_inner_le_norm (𝕜 := ℝ) (k x) v).trans_eq (mul_comm _ _)

/-- The actual feature readout Bv(x)=inner(k(x),v), as a bounded linear map. -/
def featureReadout (k : X → H) (hk2 : MemLp k 2 μ) : H →L[ℝ] Lp ℝ 2 μ :=
  (readoutLinear k hk2).mkContinuous ‖hk2.toLp k‖ (fun v => readoutVector_norm_le k hk2 v)

theorem coeFn_featureReadout (k : X → H) (hk2 : MemLp k 2 μ) (v : H) :
    (featureReadout k hk2 v : X → ℝ) =ᵐ[μ] (fun x => inner ℝ (k x) v) := by
  change (readoutVector k hk2 v : X → ℝ) =ᵐ[μ] (fun x => inner ℝ (k x) v)
  exact coeFn_readoutVector k hk2 v

theorem norm_featureReadout_apply_le (k : X → H) (hk2 : MemLp k 2 μ) (v : H) :
    ‖featureReadout k hk2 v‖ ≤ ‖hk2.toLp k‖ * ‖v‖ := by
  change ‖readoutVector k hk2 v‖ ≤ ‖hk2.toLp k‖ * ‖v‖
  exact readoutVector_norm_le k hk2 v

theorem inner_featureReadout_apply_apply (k : X → H) (hk2 : MemLp k 2 μ) (v w : H) :
    inner ℝ (featureReadout k hk2 v) (featureReadout k hk2 w) =
      ∫ x, inner ℝ (k x) v * inner ℝ (k x) w ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_featureReadout k hk2 v, coeFn_featureReadout k hk2 w] with x hv hw
  rw [hv, hw]
  change inner ℝ (k x) w * inner ℝ (k x) v = inner ℝ (k x) v * inner ℝ (k x) w
  ring

/-- Covariance with the same constructed W/g identifies the actual readout.
No independently chosen Gaussian representative is used. -/
theorem featureReadout_cov_with_indexedGaussian {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (k : X → H) (hk2 : MemLp k 2 μ) (g : X × (ℕ → ℝ) → ℝ)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x, ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) (v : H) :
    ∀ᵐ x ∂μ, (∫ ω, g (x, ω) * indexedGaussianIsometry b f hf v ω
      ∂IsonormalProcess.iidStdGaussian) = featureReadout k hk2 v x := by
  filter_upwards [hW, coeFn_featureReadout k hk2 v] with x hx hv
  rw [hv]
  calc
    _ = ∫ ω, indexedGaussianIsometry b f hf (k x) ω * indexedGaussianIsometry b f hf v ω
        ∂IsonormalProcess.iidStdGaussian := by
      apply integral_congr_ae
      filter_upwards [hx] with ω hω
      rw [hω]
    _ = _ := indexedGaussianIsometry_cov b f hf (k x) v

end
end DGRHS.Gaussian

#print axioms DGRHS.Gaussian.featureReadout
#print axioms DGRHS.Gaussian.coeFn_featureReadout
#print axioms DGRHS.Gaussian.norm_featureReadout_apply_le
#print axioms DGRHS.Gaussian.inner_featureReadout_apply_apply
#print axioms DGRHS.Gaussian.featureReadout_cov_with_indexedGaussian
#check DGRHS.Gaussian.featureReadout
#check DGRHS.Gaussian.coeFn_featureReadout
#check DGRHS.Gaussian.norm_featureReadout_apply_le
#check DGRHS.Gaussian.inner_featureReadout_apply_apply
#check DGRHS.Gaussian.featureReadout_cov_with_indexedGaussian
