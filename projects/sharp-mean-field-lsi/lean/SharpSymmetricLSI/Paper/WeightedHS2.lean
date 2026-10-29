import SharpSymmetricLSI.Paper.WeightedHS1

/-!
# (6.3): the weighted Hilbert–Schmidt identity (Phase 3, lane D; R24)

`∑_{i,j ≥ 1} λᵢ T_{ij}² = ∬ |∇ₓK(x,y)|² dμ dμ`: Parseval for the Dirichlet form in `x` for each
slice `K(·,y)`, Parseval in `L²(μ)` in `y` for the coefficients, and centering for the `e₀` terms.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section whs
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
include hyp hμ he

theorem centeredKernel_symm (x y : Torus d) :
    centeredKernel W (μ : Measure (Torus d)) x y = centeredKernel W μ y x := by
  unfold centeredKernel; rw [hyp.symm]; ring

theorem integral_abs_e_le (i : ℕ) : ∫ x, |e i x| ∂(μ : Measure (Torus d)) ≤ 1 := by
  have h := integral_abs_le_sqrt' (he.memLp i)
  have h1 : ∫ x, e i x ^ 2 ∂(μ : Measure (Torus d)) = 1 := by
    have := he.orthonormal i i
    simp only [if_true] at this
    calc ∫ x, e i x ^ 2 ∂(μ : Measure (Torus d)) = ∫ x, e i x * e i x ∂(μ : Measure (Torus d)) := by
          congr 1; funext x; ring
      _ = 1 := this
  rwa [h1, Real.sqrt_one] at h

/-- The coefficient functions `kᵢ(y) = ∫ K(x,y) eᵢ(x) dμ(x)`. -/
theorem coeff_props (i : ℕ) :
    MemLp (fun y => ∫ x, centeredKernel W μ x y * e i x ∂(μ : Measure (Torus d))) 2
      (μ : Measure (Torus d)) := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨B, hB⟩ := centeredKernel_bdd hyp μm
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary _) (Classical.arbitrary _))
  have hKm := measurable_centeredKernel hyp μm
  have hm : AEStronglyMeasurable (fun y => ∫ x, centeredKernel W μ x y * e i x ∂μm) μm := by
    have hf : AEStronglyMeasurable (fun q : Torus d × Torus d => centeredKernel W μ q.2 q.1 * e i q.2)
        (μm.prod μm) :=
      (hKm.comp measurable_swap).aestronglyMeasurable.mul
        ((he.memLp i).aestronglyMeasurable.aemeasurable.comp_snd (μ := μm)).aestronglyMeasurable
    exact hf.integral_prod_right'
  refine MemLp.of_bound hm B (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_integral_le_integral_abs).trans ?_
  have hint : Integrable (fun x => B * |e i x|) μm :=
    ((he.memLp i).integrable one_le_two).abs.const_mul B
  calc ∫ x, |centeredKernel W μ x y * e i x| ∂μm ≤ ∫ x, B * |e i x| ∂μm := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) hint
          (Eventually.of_forall fun x => ?_)
        show |centeredKernel W μ x y * e i x| ≤ B * |e i x|
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hB x y) (abs_nonneg _)
    _ ≤ B * 1 := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (integral_abs_e_le hyp hμ he i) hB0
    _ = B := mul_one B

/-- `∫ kᵢ eⱼ dμ = ∬ K(x,y) eᵢ(x) eⱼ(y)` (Fubini). -/
theorem coeff_fubini (i j : ℕ) :
    ∫ y, (∫ x, centeredKernel W μ x y * e i x ∂(μ : Measure (Torus d))) * e j y ∂(μ : Measure (Torus d)) =
      ∫ x, ∫ y, centeredKernel W μ x y * e i x * e j y ∂(μ : Measure (Torus d)) ∂(μ : Measure (Torus d)) := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨B, hB⟩ := centeredKernel_bdd hyp μm
  have hKm := measurable_centeredKernel hyp μm
  have hi := (he.memLp i).integrable one_le_two
  have hj := (he.memLp j).integrable one_le_two
  have hint : Integrable (Function.uncurry fun x y => centeredKernel W μ x y * e i x * e j y)
      (μm.prod μm) := by
    refine Integrable.mono' ((hi.abs.mul_prod hj.abs).const_mul B) ?_
      (Eventually.of_forall fun q => ?_)
    · exact (hKm.aestronglyMeasurable.mul (hi.aestronglyMeasurable.aemeasurable.comp_fst
        (ν := μm)).aestronglyMeasurable).mul
        (hj.aestronglyMeasurable.aemeasurable.comp_snd (μ := μm)).aestronglyMeasurable
    · simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
      have := hB q.1 q.2
      calc |centeredKernel W μ q.1 q.2| * |e i q.1| * |e j q.2| ≤ B * |e i q.1| * |e j q.2| := by
            gcongr
        _ = B * (|e i q.1| * |e j q.2|) := by ring
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [← integral_mul_const]

/-- The `e₀` coefficients vanish (centering). -/
theorem coeff_zero_right (i : ℕ) :
    ∫ y, (∫ x, centeredKernel W μ x y * e i x ∂(μ : Measure (Torus d))) * e 0 y
      ∂(μ : Measure (Torus d)) = 0 := by
  rw [coeff_fubini hyp hμ he]
  have : ∀ x, ∫ y, centeredKernel W μ x y * e i x * e 0 y ∂(μ : Measure (Torus d)) = 0 := fun x => by
    simp only [he.zero, mul_one]
    rw [integral_mul_const, integral_centeredKernel hyp _ x, zero_mul]
  simp [this]

theorem coeff_zero_left (y : Torus d) :
    ∫ x, centeredKernel W μ x y * e 0 x ∂(μ : Measure (Torus d)) = 0 := by
  simp only [he.zero, mul_one]
  simp_rw [centeredKernel_symm hyp hμ he _ y]
  exact integral_centeredKernel hyp _ y

end whs

end SharpLSI
