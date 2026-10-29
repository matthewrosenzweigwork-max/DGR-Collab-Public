import FullLabeledLSI.Paper.Sec8Lin7
import SharpSymmetricLSI.Paper.GaussLSI6
import SharpSymmetricLSI.Paper.WeightedHS1

/-!
# Section 8.3 (linearization), part 8: spectral tools for (8.11)

* `c1_lip`: a `C¹` function on the torus is Lipschitz;
* `cs2`: Cauchy–Schwarz for `L²(μ)` functions;
* `memH1_of_wg`, `dirPair_eq`: `H¹(μ)` membership and the Dirichlet pairing of a function with a
  bounded measurable weak gradient;
* `poincare_spec`: `λ₁ ∫ f² ≤ ∫|∇f|² dμ` for mean-zero `f ∈ H¹(μ)` (Parseval in the reference basis).
-/

open MeasureTheory InformationTheory Set Filter Topology Finset
open scoped ENNReal NNReal

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem c1_lip {g : Torus d → ℝ} (hg : ContDiff ℝ 1 (g ∘ liftT)) :
    ∃ L : ℝ≥0, LipschitzWith L g := by
  obtain ⟨M, hM⟩ := exists_bound_cgrad hg
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  exact ⟨_, lipschitz_of_dpart_bound hg hM0 fun k x => (hM x k).trans (le_max_left _ _)⟩

theorem cs2 {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {a b : Torus d → ℝ}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    |∫ x, a x * b x ∂μ| ≤ Real.sqrt (∫ x, a x ^ 2 ∂μ) * Real.sqrt (∫ x, b x ^ 2 ∂μ) := by
  have h := abs_real_inner_le_norm ha.toLp hb.toLp
  rw [inner_toLp ha hb] at h
  have e1 : ‖ha.toLp‖ = Real.sqrt (∫ x, a x ^ 2 ∂μ) := by
    rw [norm_eq_sqrt_real_inner, inner_toLp ha ha]
    congr 2; funext x; ring
  have e2 : ‖hb.toLp‖ = Real.sqrt (∫ x, b x ^ 2 ∂μ) := by
    rw [norm_eq_sqrt_real_inner, inner_toLp hb hb]
    congr 2; funext x; ring
  rwa [e1, e2] at h

theorem memLp_of_bdd {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {f : Torus d → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable B
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)

theorem memH1_of_wg {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
    {f : Torus d → ℝ} {gg : Torus d → Fin d → ℝ} (hw : IsWeakGrad f gg) (hfm : Measurable f)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) {K : ℝ} (hK : ∀ x k, |gg x k| ≤ K) : MemH1 μ f := by
  have hae : weakGrad f =ᵐ[μ] gg := hac.ae_le (weakGrad_ae_eq hw)
  refine ⟨⟨_, hw⟩, memLp_of_bdd hfm hB, ?_⟩
  refine MemLp.of_bound (C := Real.sqrt (d * K ^ 2)) ?_ ?_
  · exact Real.continuous_sqrt.comp_aestronglyMeasurable
      ((isWeakGrad_weakGrad ⟨_, hw⟩).aestronglyMeasurable_sqNorm.mono_ac hac)
  · filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hx]
    refine Real.sqrt_le_sqrt ?_
    unfold sqNorm
    calc ∑ k, gg x k ^ 2 ≤ ∑ _k : Fin d, K ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hK x k) 2
      _ = d * K ^ 2 := by simp

theorem dirPair_eq {μ : Measure (Torus d)} (hac : μ ≪ haar d) {f : Torus d → ℝ}
    {gg : Torus d → Fin d → ℝ} (hw : IsWeakGrad f gg) :
    dirPair μ (weakGrad f) (weakGrad f) = ∫ x, ∑ k, gg x k ^ 2 ∂μ := by
  unfold dirPair
  refine integral_congr_ae ?_
  filter_upwards [hac.ae_le (weakGrad_ae_eq hw)] with x hx
  rw [hx]
  exact Finset.sum_congr rfl fun k _ => (sq _).symm

/-- **Poincaré inequality from the spectrum**: `λ₁ ∫ f² ≤ ∫|∇f|² dμ` for mean-zero `f ∈ H¹(μ)`. -/
theorem poincare_spec {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e : ℕ → Torus d → ℝ}
    {lam : ℕ → ℝ} (hac : μ ≪ haar d) {C : ℝ} (hlow : haar d ≤ ENNReal.ofReal C • μ)
    (he : IsRefEigenbasis μ e lam) {f : Torus d → ℝ} (hf : MemH1 μ f) (hf0 : ∫ x, f x ∂μ = 0) :
    lam 1 * ∫ x, f x ^ 2 ∂μ ≤ dirPair μ (weakGrad f) (weakGrad f) := by
  have h1 := hasSum_sq_coeff he hf.2.1
  have h2 := energy_parseval hac hlow he hf
  have h0 : ∫ x, f x * e 0 x ∂μ = 0 := by
    rw [he.zero]; simpa using hf0
  refine hasSum_le (fun i => ?_) (h1.mul_left (lam 1)) h2
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [h0]; simp
  · exact mul_le_mul_of_nonneg_right (he.mono (Nat.succ_le_of_lt hi)) (sq_nonneg _)

theorem top_lip_bdd (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {u : Torus d → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hu0 : ∫ x, u x ∂μ = 0) :
    (∃ L : ℝ≥0, LipschitzWith L (Top W μ u)) ∧ ∃ B' : ℝ, ∀ x, |Top W μ u x| ≤ B' := by
  obtain ⟨CT, hCT⟩ := Top_W1inf hyp μ
  obtain ⟨hTb, hTL⟩ := hCT u ⟨memLp_of_bdd hu hB, hu0⟩
  exact ⟨⟨_, hTL⟩, _, hTb⟩

end Sec8
end SharpLSI.FL
