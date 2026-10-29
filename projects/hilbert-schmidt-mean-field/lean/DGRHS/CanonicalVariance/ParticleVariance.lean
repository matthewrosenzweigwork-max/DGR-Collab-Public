/- Unchecked preparation outside frozen root proof. Actual particle variance. -/
import DGRHS.CanonicalVariance.CanonicalCovariance
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace DGRHS.CanonicalVariance
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι]
variable (μ : Measure S) [IsProbabilityMeasure μ]

def offDiagonalSum (h : S × S → ℝ) (x : ι → S) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset ι).offDiag, h (x p.1,x p.2)

lemma integrable_offDiagonalSum (h : S × S → ℝ)
    (hh : MemLp h 2 (μ.prod μ)) :
    Integrable (offDiagonalSum (ι := ι) h) (Measure.pi (fun _ ↦ μ)) := by
  classical
  unfold offDiagonalSum
  apply integrable_finsetSum
  intro p hp
  exact (DGRHS.Decoupling.memLp_coupled_term μ h 2 hh p.1 p.2
    (Finset.mem_offDiag.mp hp).2.2).integrable (by norm_num)

lemma integral_offDiagonalSum_eq_zero (h : S × S → ℝ)
    (hh : MemLp h 2 (μ.prod μ))
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0) :
    (∫ x : ι → S, offDiagonalSum h x ∂Measure.pi (fun _ ↦ μ)) = 0 := by
  classical
  unfold offDiagonalSum
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro p hp
    exact integral_coupled_term_eq_zero μ h hh hc p.1 p.2
      (Finset.mem_offDiag.mp hp).2.2
  · intro p hp
    exact (DGRHS.Decoupling.memLp_coupled_term μ h 2 hh p.1 p.2
      (Finset.mem_offDiag.mp hp).2.2).integrable (by norm_num)

/-- The exact second moment, with the empty and singleton arrays included. -/
theorem integral_offDiagonalSum_sq (h : S × S → ℝ)
    (hm : Measurable h) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0) :
    (∫ x : ι → S, (offDiagonalSum h x)^2 ∂Measure.pi (fun _ ↦ μ)) =
      2 * ((Finset.univ : Finset ι).offDiag.card : ℝ) *
        (∫ z, h z^2 ∂μ.prod μ) := by
  classical
  let s := (Finset.univ : Finset ι).offDiag
  let c := ∫ z, h z^2 ∂μ.prod μ
  have hi : ∀ p ∈ s, ∀ q ∈ s,
      Integrable (fun x : ι → S ↦ h (x p.1,x p.2) * h (x q.1,x q.2))
        (Measure.pi (fun _ ↦ μ)) := by
    intro p hp q hq
    exact integrable_coupled_pair_product μ h hh p.1 p.2 q.1 q.2
      (Finset.mem_offDiag.mp hp).2.2 (Finset.mem_offDiag.mp hq).2.2
  have he : (fun x : ι → S ↦ (offDiagonalSum h x)^2) =
      fun x ↦ ∑ p ∈ s, ∑ q ∈ s, h (x p.1,x p.2) * h (x q.1,x q.2) := by
    funext x
    exact (sq _).trans (Finset.sum_mul_sum s s _ _)
  rw [he, integral_finsetSum s (fun p hp ↦ integrable_finsetSum s (hi p hp))]
  have hv : ∀ p ∈ s, (∫ x : ι → S, ∑ q ∈ s,
      h (x p.1,x p.2) * h (x q.1,x q.2) ∂Measure.pi (fun _ ↦ μ)) = 2*c := by
    intro p hp
    have hp' := (Finset.mem_offDiag.mp hp).2.2
    have hps : p.swap ∈ s := Finset.mem_offDiag.mpr
      ⟨Finset.mem_univ _,Finset.mem_univ _,hp'.symm⟩
    rw [integral_finsetSum s (hi p hp)]
    calc
      _ = ∑ q ∈ s, ((if q = p then c else 0) +
            (if q = p.swap then c else 0)) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact integral_coupled_pair_product μ h hm hh hs hc p q hp'
          (Finset.mem_offDiag.mp hq).2.2
      _ = 2*c := by rw [Finset.sum_add_distrib]; simp [hp,hps]; ring
  rw [Finset.sum_congr rfl hv]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

def normalizedOffDiagonalSum (h : S × S → ℝ) (x : ι → S) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * offDiagonalSum h x

/-- Uniform second-moment control follows from exact cancellation, without
boundedness or pointwise canonical representatives. -/
theorem integral_normalizedOffDiagonalSum_sq_le (h : S × S → ℝ)
    (hm : Measurable h) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0) :
    (∫ x : ι → S, (normalizedOffDiagonalSum h x)^2
      ∂Measure.pi (fun _ ↦ μ)) ≤ 2 * (∫ z, h z^2 ∂μ.prod μ) := by
  classical
  simp only [normalizedOffDiagonalSum, mul_pow]
  rw [integral_const_mul, integral_offDiagonalSum_sq μ h hm hh hs hc]
  have hc0 : 0 ≤ ∫ z, h z^2 ∂μ.prod μ := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hcard : ((Finset.univ : Finset ι).offDiag.card : ℝ) ≤ (Fintype.card ι : ℝ)^2 := by
    have hb := Finset.card_le_card (show (Finset.univ : Finset ι).offDiag ⊆
      Finset.univ ×ˢ Finset.univ from fun p hp ↦ Finset.mem_product.mpr
        ⟨Finset.mem_univ _,Finset.mem_univ _⟩)
    simp only [Finset.card_product, Finset.card_univ] at hb
    rw [pow_two]
    exact_mod_cast hb
  have hn : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  by_cases hz : Fintype.card ι = 0
  · simp [hz,hc0]
  have hn0 : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hz
  apply le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num)) hc0)
      (sq_nonneg ((Fintype.card ι : ℝ)⁻¹)))
  field_simp [hn0]
  <;> ring_nf
  <;> exact le_rfl

end DGRHS.CanonicalVariance
#print axioms DGRHS.CanonicalVariance.integral_offDiagonalSum_eq_zero
#print axioms DGRHS.CanonicalVariance.integral_offDiagonalSum_sq
#print axioms DGRHS.CanonicalVariance.integral_normalizedOffDiagonalSum_sq_le
