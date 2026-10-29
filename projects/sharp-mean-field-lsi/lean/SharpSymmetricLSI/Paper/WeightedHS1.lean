import SharpSymmetricLSI.Paper.EnergyParseval3
import SharpSymmetricLSI.Paper.CondForce2
import SharpSymmetricLSI.Paper.CenteredEntropy

/-!
# (6.3): the slices of the centered kernel (Phase 3, lane D; R24)
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section slice
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
include hyp hμ

/-- `m ≤ c⁻¹ μ` for the minimizer. -/
theorem haar_le_smul_minimizer : ∃ C : ℝ, haar d ≤ ENNReal.ofReal C • (μ : Measure (Torus d)) := by
  obtain ⟨c, C, L, hc, hb⟩ := elDensity_bounds hyp
  have hμp := minimizer_eq_elDensity hyp hμ
  refine ⟨1 / c, Measure.le_iff.mpr fun s hs => ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, hμp, densMeasure, withDensity_apply _ hs]
  calc haar d s = ENNReal.ofReal (1 / c) * (ENNReal.ofReal c * haar d s) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hc.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (1 / c) * ∫⁻ x in s, ENNReal.ofReal (elDens V W μ x) ∂haar d := by
        gcongr
        rw [← setLIntegral_const]
        exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal
          ((hb (μ : Measure (Torus d)) inferInstance).1 x).1

/-- The slice `x ↦ K(x,y)` has weak gradient `∇₁W(·,y) - β`. -/
theorem isWeakGrad_K_slice (y : Torus d) :
    IsWeakGrad (fun x => centeredKernel W μ x y) (fun x k => bfixF W μ x y k) := by
  have hac := minimizer_ac hyp hμ
  have h1 := isWeakGrad_slice hyp y (W := W)
  have h2 := (forceMean_props hyp hac).1
  have h := (h1.add (h2.cmul (-1))).add (isWeakGrad_const (-convMeas W μ y + interE W μ μ))
  convert h using 1
  · funext x; unfold centeredKernel; ring
  · funext x k; unfold bfixF; simp; ring

theorem memH1_K_slice (y : Torus d) : MemH1 (μ : Measure (Torus d)) (fun x => centeredKernel W μ x y) := by
  have hac := minimizer_ac hyp hμ
  obtain ⟨-, M, hM0, hM, hMβ, -⟩ := bfixF_props hyp hac
  obtain ⟨B, hB⟩ := centeredKernel_bdd hyp (μ : Measure (Torus d))
  have hw := isWeakGrad_K_slice hyp hμ y
  have hae := hac.ae_le (weakGrad_ae_eq hw)
  have hKm : Measurable fun x => centeredKernel W μ x y :=
    (measurable_centeredKernel hyp (μ : Measure (Torus d))).comp
      (measurable_id.prodMk measurable_const)
  refine ⟨⟨_, hw⟩, MemLp.of_bound hKm.aestronglyMeasurable B
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x y), ?_⟩
  refine MemLp.of_bound (C := Real.sqrt (d * M ^ 2)) ?_ ?_
  · exact Real.continuous_sqrt.comp_aestronglyMeasurable
      ((isWeakGrad_weakGrad ⟨_, hw⟩).aestronglyMeasurable_sqNorm.mono_ac hac)
  · filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hx]
    refine Real.sqrt_le_sqrt ?_
    unfold sqNorm
    calc ∑ k, bfixF W μ x y k ^ 2 ≤ ∑ _k : Fin d, M ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hM x y k) 2
      _ = d * M ^ 2 := by simp

/-- **The slice identity**: `∫ |∇₁K(x,y)|² dμ(x) = ∑ λᵢ (∫ K(x,y)eᵢ(x) dμ)²`. -/
theorem slice_energy {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) (y : Torus d) :
    HasSum (fun i => lam i * (∫ x, centeredKernel W μ x y * e i x ∂(μ : Measure (Torus d))) ^ 2)
      (∫ x, ∑ k, bfixF W μ x y k * bfixF W μ x y k ∂(μ : Measure (Torus d))) := by
  have hac := minimizer_ac hyp hμ
  obtain ⟨C, hlow⟩ := haar_le_smul_minimizer hyp hμ
  have h := energy_parseval hac hlow he (memH1_K_slice hyp hμ y)
  have hae := hac.ae_le (weakGrad_ae_eq (isWeakGrad_K_slice hyp hμ y))
  have e1 : dirPair (μ : Measure (Torus d)) (weakGrad fun x => centeredKernel W μ x y)
      (weakGrad fun x => centeredKernel W μ x y) =
      ∫ x, ∑ k, bfixF W μ x y k * bfixF W μ x y k ∂(μ : Measure (Torus d)) := by
    unfold dirPair
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  rwa [e1] at h

end slice

end SharpLSI
