import SharpSymmetricLSI.Paper.LipChain2
import SharpSymmetricLSI.Paper.EntFinite
import SharpSymmetricLSI.Paper.H1Config

/-!
# Lipschitz chain rule, part 3: `H¹(P_N)` is stable under Lipschitz maps

`memH1C_comp_lipschitz`: `f ∈ H¹(P_N)` and `χ` `L`-Lipschitz give `χ ∘ f ∈ H¹(P_N)` and
`ℰ_N(χ ∘ f) ≤ L² ℰ_N(f)`.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `L²(P_N)` (flattened) controls `L²(Leb)`. -/
theorem memLp_two_volume_of_gibbs_flat (hyp : Hyp V W KV KW) {N : ℕ}
    {u : UnitAddTorus (Fin N × Fin d) → ℝ} (hu : MemLp u 2 ((gibbs V W N).map flat))
    (hum : AEStronglyMeasurable u volume) : MemLp u 2 volume := by
  obtain ⟨C, hC, hle⟩ := lintegral_haar_le_gibbs hyp N
  refine (memLp_two_iff_integrable_sq hum).mpr ⟨hum.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => sq_nonneg _)]
  refine (hle _ (hum.pow 2).aemeasurable.ennreal_ofReal).trans_lt (ENNReal.mul_lt_top hC.lt_top ?_)
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => sq_nonneg _)).mp
    hu.integrable_sq.2

/-- **`χ ∘ f ∈ H¹(P_N)` and `ℰ_N(χ ∘ f) ≤ L² ℰ_N(f)`** for `L`-Lipschitz `χ`. -/
theorem memH1C_comp_lipschitz (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) {χ : ℝ → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ) :
    MemH1C (gibbs V W N) (χ ∘ f) ∧ energy V W N (χ ∘ f) ≤ (L : ℝ≥0∞) ^ 2 * energy V W N f := by
  obtain ⟨hw, hi, -⟩ := memH1C_data hyp hf
  have hac := gibbs_map_flat_ac hyp N
  haveI := gibbs_isProbabilityMeasure hyp N
  haveI : IsProbabilityMeasure ((gibbs V W N).map flat) :=
    inferInstance
  have hg2 : ∀ k, MemLp (fun y => weakGrad (f ∘ unflat) y k) 2 volume := fun k =>
    memLp_two_volume_of_gibbs_flat hyp (hf.2.2.of_le ((hw.aestronglyMeasurable_grad k).mono_ac hac.1)
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact abs_le_sqrt_sqNorm _ k)) (hw.aestronglyMeasurable_grad k)
  obtain ⟨G, hG, hGb⟩ := exists_isWeakGrad_comp_lipschitz hw hi hg2 hχ
  have hG' : IsWeakGrad ((χ ∘ f) ∘ unflat) G := hG
  have hGw : HasWeakGrad ((χ ∘ f) ∘ unflat) := ⟨G, hG'⟩
  have hae : ∀ᵐ y ∂((gibbs V W N).map flat),
      sqNorm (weakGrad ((χ ∘ f) ∘ unflat) y) ≤ (L : ℝ) ^ 2 * sqNorm (weakGrad (f ∘ unflat) y) :=
    hac.1.ae_le (by
      filter_upwards [weakGrad_ae_eq hG', hGb] with y h1 h2
      rw [h1]; exact h2)
  have hL0 : (0 : ℝ) ≤ L := L.2
  refine ⟨⟨hGw, ?_, ?_⟩, ?_⟩
  · refine ((memLp_const |χ 0|).add (hf.2.1.norm.const_mul (L : ℝ))).of_le
      (hχ.continuous.comp_aestronglyMeasurable hf.2.1.aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    have h := hχ.dist_le_mul ((f ∘ unflat) y) 0
    rw [Real.dist_eq, Real.dist_eq, sub_zero] at h
    have h3 := abs_sub_abs_le_abs_sub (χ ((f ∘ unflat) y)) (χ 0)
    simp only [Function.comp_apply] at h h3
    refine le_trans ?_ (Real.le_norm_self _)
    simp only [Pi.add_apply, Real.norm_eq_abs, Function.comp_apply]
    linarith
  · refine (hf.2.2.const_mul (L : ℝ)).of_le
      ((Real.continuous_sqrt.comp_aestronglyMeasurable
        (isWeakGrad_weakGrad hGw).aestronglyMeasurable_sqNorm).mono_ac hac.1) ?_
    filter_upwards [hae] with y hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (mul_nonneg hL0 (Real.sqrt_nonneg _))]
    calc Real.sqrt (sqNorm (weakGrad ((χ ∘ f) ∘ unflat) y))
        ≤ Real.sqrt ((L : ℝ) ^ 2 * sqNorm (weakGrad (f ∘ unflat) y)) := Real.sqrt_le_sqrt hy
      _ = L * Real.sqrt (sqNorm (weakGrad (f ∘ unflat) y)) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hL0]
  · rw [energy_eq hyp hGw, energy_eq hyp hf.1, ← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with y hy
    rw [show ((L : ℝ≥0∞) ^ 2) = ENNReal.ofReal ((L : ℝ) ^ 2) by
      rw [ENNReal.ofReal_pow hL0, ENNReal.ofReal_coe_nnreal], ← ENNReal.ofReal_mul (sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hy

end SharpLSI
