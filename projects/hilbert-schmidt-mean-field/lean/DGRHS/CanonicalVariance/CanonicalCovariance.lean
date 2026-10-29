/- Unchecked preparation outside frozen root proof. Exact four-index cancellation. -/
import DGRHS.CanonicalVariance.CanonicalProducts
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
namespace DGRHS.CanonicalVariance
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι]
variable (μ : Measure S) [IsProbabilityMeasure μ]

lemma integral_coupled_product_swap_left (h : S × S → ℝ)
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (i j k l : ι) (hij : i ≠ j) :
    (∫ x : ι → S, h (x i,x j) * h (x k,x l) ∂Measure.pi (fun _ ↦ μ)) =
      ∫ x : ι → S, h (x j,x i) * h (x k,x l) ∂Measure.pi (fun _ ↦ μ) := by
  apply integral_congr_ae
  filter_upwards [symmetric_coupled_term_ae μ h hs i j hij] with x hx
  rw [hx]

lemma integral_coupled_product_swap_right (h : S × S → ℝ)
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (i j k l : ι) (hkl : k ≠ l) :
    (∫ x : ι → S, h (x i,x j) * h (x k,x l) ∂Measure.pi (fun _ ↦ μ)) =
      ∫ x : ι → S, h (x i,x j) * h (x l,x k) ∂Measure.pi (fun _ ↦ μ) := by
  apply integral_congr_ae
  filter_upwards [symmetric_coupled_term_ae μ h hs k l hkl] with x hx
  rw [hx]

/-- Every distinct unordered pair has zero cross moment. AE symmetry is enough;
no pointwise modification of the preserved source kernel is required. -/
lemma integral_distinct_unordered_pairs_eq_zero (h : S × S → ℝ)
    (hm : Measurable h) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
    (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l)
    (hp : (i,j) ≠ (k,l)) (hq : (j,i) ≠ (k,l)) :
    (∫ x : ι → S, h (x i,x j) * h (x k,x l) ∂Measure.pi (fun _ ↦ μ)) = 0 := by
  classical
  by_cases hik : i = k
  · subst k
    have hjl : j ≠ l := by intro hjl; subst l; exact hp rfl
    exact integral_common_index_eq_zero μ h hh hc i j l hij hkl hjl
  by_cases hil : i = l
  · subst l
    have hjk : j ≠ k := by intro hjk; subst k; exact hq rfl
    rw [integral_coupled_product_swap_right μ h hs i j k i hkl]
    exact integral_common_index_eq_zero μ h hh hc i j k hij hkl.symm hjk
  by_cases hjk : j = k
  · subst k
    have hil : i ≠ l := by intro hil; subst l; exact hq rfl
    rw [integral_coupled_product_swap_left μ h hs i j j l hij]
    exact integral_common_index_eq_zero μ h hh hc j i l hij.symm hkl hil
  by_cases hjl : j = l
  · subst l
    have hik : i ≠ k := by intro hik; subst k; exact hp rfl
    rw [integral_coupled_product_swap_left μ h hs i j k j hij,
      integral_coupled_product_swap_right μ h hs j i k j hkl]
    exact integral_common_index_eq_zero μ h hh hc j i k hij.symm hkl.symm hik
  exact integral_disjoint_pairs_eq_zero μ h hm hh hc i j k l hij hkl hik hil hjk hjl

/-- Exact covariance support on the two orientations of a single pair. -/
theorem integral_coupled_pair_product (h : S × S → ℝ)
    (hm : Measurable h) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
    (p q : ι × ι) (hp : p.1 ≠ p.2) (hq : q.1 ≠ q.2) :
    (∫ x : ι → S, h (x p.1,x p.2) * h (x q.1,x q.2)
      ∂Measure.pi (fun _ ↦ μ)) =
      (if q = p then ∫ z, h z^2 ∂μ.prod μ else 0) +
      (if q = p.swap then ∫ z, h z^2 ∂μ.prod μ else 0) := by
  classical
  have hn : p ≠ p.swap := by
    intro he
    exact hp (congrArg Prod.fst he)
  by_cases hqp : q = p
  · subst q
    simp only [ite_true, hn, if_false, add_zero]
    simpa only [← sq] using integral_coupled_term_sq μ h hh p.1 p.2 hp
  by_cases hqs : q = p.swap
  · subst q
    rw [if_neg hn.symm, if_pos rfl, zero_add]
    change (∫ x : ι → S, h (x p.1,x p.2) * h (x p.2,x p.1)
      ∂Measure.pi (fun _ ↦ μ)) = _
    rw [integral_coupled_product_swap_right μ h hs p.1 p.2 p.2 p.1 hp.symm]
    simpa only [← sq] using integral_coupled_term_sq μ h hh p.1 p.2 hp
  simp only [hqp, hqs, if_false, zero_add]
  exact integral_distinct_unordered_pairs_eq_zero μ h hm hh hs hc
    p.1 p.2 q.1 q.2 hp hq (Ne.symm hqp) (Ne.symm hqs)

end DGRHS.CanonicalVariance
#print axioms DGRHS.CanonicalVariance.integral_distinct_unordered_pairs_eq_zero
#print axioms DGRHS.CanonicalVariance.integral_coupled_pair_product
