import DGRHS.Concentration.RowGeometry

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace Topology
namespace DGRHS.Concentration

/-- Full source D bilinear test; the tuple norms square to sums of L2 norm squares. -/
def kernelL2Bilinear {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] {n q : ℕ}
    (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    (h : Fin n → Fin q → Ω × Ψ → ℝ)
    (f : PiLp 2 (fun i ↦ Lp ℝ 2 (μ i))) (g : PiLp 2 (fun j ↦ Lp ℝ 2 (ν j))) : ℝ :=
  ∑ i, ∑ j, ∫ p, h i j p * f i p.1 * g j p.2 ∂(μ i).prod (ν j)

lemma kernel_l2_test_integrable {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) (ν : Measure Ψ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : Ω × Ψ → ℝ) (A : ℝ) (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν)
    (hAES : AEStronglyMeasurable h (μ.prod ν))
    (hBound : ∀ᵐ p ∂μ.prod ν, |h p| ≤ A) :
    Integrable (fun p ↦ h p * f p.1 * g p.2) (μ.prod ν) := by
  have hf : MemLp (fun p : Ω × Ψ ↦ f p.1) 2 (μ.prod ν) :=
    (Lp.memLp f).comp_measurePreserving measurePreserving_fst
  have hg : MemLp (fun p : Ω × Ψ ↦ g p.2) 2 (μ.prod ν) :=
    (Lp.memLp g).comp_measurePreserving measurePreserving_snd
  have hi := (hf.integrable_mul hg).bdd_mul hAES
    (by simpa only [Real.norm_eq_abs] using hBound)
  simpa only [Pi.mul_apply,mul_assoc] using hi

lemma rowSection_weighted_inner_integrable {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) (ν : Measure Ψ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : Ω × Ψ → ℝ) (A : ℝ) (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν)
    (hAES : AEStronglyMeasurable h (μ.prod ν))
    (hBound : ∀ᵐ p ∂μ.prod ν, |h p| ≤ A) :
    Integrable (fun x ↦ f x * inner ℝ g (rowSection ν h x)) μ := by
  have hi := kernel_l2_test_integrable μ ν h A f g hAES hBound
  apply hi.integral_prod_left.congr
  filter_upwards [bounded_kernel_sections_memLp μ ν h A hAES hBound] with x hx
  rw [rowSection_inner ν h x g hx,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  ring

lemma rowSection_weighted_inner_identity {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) (ν : Measure Ψ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : Ω × Ψ → ℝ) (A : ℝ) (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν)
    (hAES : AEStronglyMeasurable h (μ.prod ν))
    (hBound : ∀ᵐ p ∂μ.prod ν, |h p| ≤ A) :
    (∫ x, f x * inner ℝ g (rowSection ν h x) ∂μ) =
      ∫ p, h p * f p.1 * g p.2 ∂μ.prod ν := by
  rw [integral_prod _ (kernel_l2_test_integrable μ ν h A f g hAES hBound)]
  apply integral_congr_ae
  filter_upwards [bounded_kernel_sections_memLp μ ν h A hAES hBound] with x hx
  rw [rowSection_inner ν h x g hx,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  ring

/-- Actual finite product/Fubini identification of the source test with the row action. -/
theorem rowTuple_bilinear_identity {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ) (A : ℝ)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A)
    (f : PiLp 2 (fun i ↦ Lp ℝ 2 (μ i))) (g : PiLp 2 (fun j ↦ Lp ℝ 2 (ν j))) :
    (∑ i, ∫ x, f i x * inner ℝ g (rowTuple ν (h i) x) ∂μ i) = kernelL2Bilinear μ ν h f g := by
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun x ↦ f i x * inner ℝ g (rowTuple ν (h i) x)) =
      (fun x ↦ ∑ j, f i x * inner ℝ (g j) (rowSection (ν j) (h i j) x)) := by
    funext x
    simp only [PiLp.inner_apply,rowTuple_apply,Finset.mul_sum]
  rw [he,integral_finsetSum Finset.univ (fun j _ ↦
    rowSection_weighted_inner_integrable (μ i) (ν j) (h i j) A (f i) (g j) (hAES i j) (hBound i j))]
  exact Finset.sum_congr rfl (fun j _ ↦
    rowSection_weighted_inner_identity (μ i) (ν j) (h i j) A (f i) (g j) (hAES i j) (hBound i j))

#print axioms DGRHS.Concentration.kernel_l2_test_integrable
#print axioms DGRHS.Concentration.rowTuple_bilinear_identity
#check @DGRHS.Concentration.rowTuple_bilinear_identity
end DGRHS.Concentration
