import DGRHS.Concentration.RowTuple

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace Topology
namespace DGRHS.Concentration

/-- The actual trace of one finite L2 row, before any C-bound is imposed. -/
theorem rowTuple_trace_identity {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {q : ℕ} (μ : Measure Ω) (ν : Fin q → Measure Ψ)
    [IsProbabilityMeasure μ] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin q → Ω × Ψ → ℝ) (A : ℝ)
    (hAES : ∀ j, AEStronglyMeasurable (h j) (μ.prod (ν j)))
    (hBound : ∀ j, ∀ᵐ p ∂μ.prod (ν j), |h j p| ≤ A) :
    (∫ x, ‖rowTuple ν h x‖^2 ∂μ) = ∑ j, ∫ p, (h j p)^2 ∂μ.prod (ν j) := by
  have hSq : ∀ j, Integrable (fun p ↦ (h j p)^2) (μ.prod (ν j)) := fun j ↦ by
    simpa only [sq_abs] using bounded_kernel_abs_moment_integrable μ (ν j) (h j) A (hAES j) (hBound j) 2
  have hs : ∀ᵐ x ∂μ, ∀ j, MemLp (fun y ↦ h j (x,y)) 2 (ν j) :=
    ae_all_iff.mpr (fun j ↦ bounded_kernel_sections_memLp μ (ν j) (h j) A (hAES j) (hBound j))
  calc
    _ = ∫ x, ∑ j, ∫ y, (h j (x,y))^2 ∂ν j ∂μ :=
      integral_congr_ae (hs.mono fun x hx ↦ rowTuple_norm_square ν h x hx)
    _ = ∑ j, ∫ x, ∫ y, (h j (x,y))^2 ∂ν j ∂μ :=
      integral_finsetSum Finset.univ (fun j _ ↦ (hSq j).integral_prod_left)
    _ = _ := Finset.sum_congr rfl (fun j _ ↦ (integral_prod _ (hSq j)).symm)

lemma rowTuple_trace_bound {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ) (A C : ℝ)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A)
    (hTrace : (∑ i, ∑ j, ∫ p, (h i j p)^2 ∂(μ i).prod (ν j)) ≤ C^2) :
    (∑ i, ∫ x, ‖rowTuple ν (h i) x‖^2 ∂μ i) ≤ C^2 := by
  simpa only [rowTuple_trace_identity _ _ _ A (hAES _) (hBound _)] using hTrace

/-- The genuine representative of the finite L2 section sum. -/
lemma rowSection_sum_coe {Ω Ψ : Type*} [MeasurableSpace Ψ] {n : ℕ}
    (ν : Measure Ψ) (h : Fin n → Ω × Ψ → ℝ) (ω : Fin n → Ω)
    (hx : ∀ i, MemLp (fun y ↦ h i (ω i,y)) 2 ν) :
    (∑ i, rowSection ν (h i) (ω i) : Lp ℝ 2 ν) =ᵐ[ν]
      (fun y ↦ ∑ i, h i (ω i,y)) := by
  have hs : ∀ᵐ y ∂ν, ∀ i, rowSection ν (h i) (ω i) y = h i (ω i,y) :=
    ae_all_iff.mpr (fun i ↦ rowSection_coe ν (h i) (ω i) (hx i))
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ rowSection ν (h i) (ω i)),hs] with y hy hh
  rw [hy]
  exact Finset.sum_congr rfl (fun i _ ↦ hh i)

lemma rowSection_sum_norm_square {Ω Ψ : Type*} [MeasurableSpace Ψ] {n : ℕ}
    (ν : Measure Ψ) (h : Fin n → Ω × Ψ → ℝ) (ω : Fin n → Ω)
    (hx : ∀ i, MemLp (fun y ↦ h i (ω i,y)) 2 ν) :
    ‖∑ i, rowSection ν (h i) (ω i)‖^2 = ∫ y, (∑ i, h i (ω i,y))^2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [rowSection_sum_coe ν h ω hx] with y hy
  change (∑ i, rowSection ν (h i) (ω i) : Lp ℝ 2 ν) y *
    (∑ i, rowSection ν (h i) (ω i) : Lp ℝ 2 ν) y = _
  rw [hy,pow_two]

/-- The full actual row-Hilbert norm equals the conditional scalar variance.
The exceptional slice sets are transferred through the actual finite product law. -/
theorem rowTuple_sum_norm_square {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ) (A : ℝ)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A) :
    ∀ᵐ ω ∂Measure.pi μ, ‖∑ i, rowTuple ν (h i) (ω i)‖^2 = kernelColumnVariance ν h ω := by
  have hs : ∀ᵐ ω ∂Measure.pi μ, ∀ i j, MemLp (fun y ↦ h i j (ω i,y)) 2 (ν j) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    exact (measurePreserving_pi_coordinate μ i).quasiMeasurePreserving.ae
      (bounded_kernel_sections_memLp (μ i) (ν j) (h i j) A (hAES i j) (hBound i j))
  filter_upwards [hs] with ω hω
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ j, ‖(∑ i, rowTuple ν (h i) (ω i)) j‖^2) = _
  have he : ∀ j, (∑ i, rowTuple ν (h i) (ω i)) j = ∑ i, rowSection (ν j) (fun p ↦ h i j p) (ω i) := by
    intro j
    exact map_sum (PiLp.projₗ (𝕜 := ℝ) 2 (fun j ↦ Lp ℝ 2 (ν j)) j) _ _
  simp_rw [he,rowSection_sum_norm_square _ _ _ (fun i ↦ hω i _)]
  rfl

#print axioms DGRHS.Concentration.rowTuple_trace_identity
#print axioms DGRHS.Concentration.rowTuple_trace_bound
#print axioms DGRHS.Concentration.rowTuple_sum_norm_square
#check @DGRHS.Concentration.rowTuple_sum_norm_square
end DGRHS.Concentration
