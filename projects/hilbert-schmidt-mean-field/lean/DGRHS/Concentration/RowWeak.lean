import DGRHS.Concentration.RowBilinear

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace Topology
namespace DGRHS.Concentration

/-- Duality in the actual finite tuple of scalar L2 spaces. -/
lemma finite_l2_dual_square_bound {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) (X : Fin n → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 (μ i)) (D : ℝ) (hD : 0 ≤ D)
    (hTest : ∀ f : PiLp 2 (fun i ↦ Lp ℝ 2 (μ i)), ‖f‖ ≤ 1 →
      (∑ i, ∫ x, f i x * X i x ∂μ i) ≤ D) :
    (∑ i, ∫ x, (X i x)^2 ∂μ i) ≤ D^2 := by
  let Q : PiLp 2 (fun i ↦ Lp ℝ 2 (μ i)) :=
    WithLp.toLp 2 (fun i ↦ (hX i).toLp (X i))
  have hQ : ∀ i, (Q i : Ω → ℝ) =ᵐ[μ i] X i := fun i ↦ (hX i).coeFn_toLp
  have hNorm : ‖Q‖^2 = ∑ i, ∫ x, (X i x)^2 ∂μ i := by
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i _
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hQ i] with x hx
    simp [hx,pow_two]
  have hAction : ∀ f : PiLp 2 (fun i ↦ Lp ℝ 2 (μ i)),
      (∑ i, ∫ x, f i x * X i x ∂μ i) = inner ℝ f Q := by
    intro f
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hQ i] with x hx
    simp [hx,mul_comm]
  have hn : ‖Q‖ ≤ D := by
    by_cases hz : ‖Q‖ = 0
    · simpa only [hz] using hD
    · have hp : 0 < ‖Q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      let f := (‖Q‖⁻¹ : ℝ) • Q
      have hf : ‖f‖ ≤ 1 := by
        dsimp [f]
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ hz]
      have ht := hTest f hf
      rw [hAction] at ht
      have he : inner ℝ f Q = ‖Q‖ := by
        dsimp [f]
        rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
        field_simp
      rwa [he] at ht
  rw [← hNorm]
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

/-- The source full bilinear D-test implies the actual row-vector weak variance.
All tests are genuine L2 classes; no boundedness of the test functions is assumed. -/
theorem rowTuple_weak_variance_bound {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace.CountablyGenerated Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ) (A B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A)
    (hEnergy : ∀ i, ∀ᵐ x ∂μ i, (∑ j, ∫ y, (h i j (x,y))^2 ∂ν j) ≤ B^2)
    (hTest : ∀ (f : PiLp 2 (fun i ↦ Lp ℝ 2 (μ i)))
      (g : PiLp 2 (fun j ↦ Lp ℝ 2 (ν j))), ‖f‖ ≤ 1 → ‖g‖ ≤ 1 → kernelL2Bilinear μ ν h f g ≤ D) :
    ∀ g : PiLp 2 (fun j ↦ Lp ℝ 2 (ν j)), ‖g‖ ≤ 1 →
      (∑ i, ∫ x, (inner ℝ g (rowTuple ν (h i) x))^2 ∂μ i) ≤ D^2 := by
  intro g hg
  have hX : ∀ i, MemLp (fun x ↦ inner ℝ g (rowTuple ν (h i) x)) 2 (μ i) := by
    intro i
    apply bounded_real_memLp
      ((rowTuple_aestronglyMeasurable (μ i) ν (h i) A (hAES i) (hBound i)).const_inner)
    filter_upwards [rowTuple_bounded (μ i) ν (h i) A B hB (hAES i) (hBound i) (hEnergy i)] with x hx
    exact (abs_real_inner_le_norm _ _).trans (by
      calc
        ‖g‖ * ‖rowTuple ν (h i) x‖ ≤ 1 * B := mul_le_mul hg hx (norm_nonneg _) (by norm_num)
        _ = B := one_mul _)
  apply finite_l2_dual_square_bound μ _ hX D hD
  intro f hf
  rw [rowTuple_bilinear_identity μ ν h A hAES hBound f g]
  exact hTest f g hf hg

#print axioms DGRHS.Concentration.finite_l2_dual_square_bound
#print axioms DGRHS.Concentration.rowTuple_weak_variance_bound
#check @DGRHS.Concentration.rowTuple_weak_variance_bound
end DGRHS.Concentration
