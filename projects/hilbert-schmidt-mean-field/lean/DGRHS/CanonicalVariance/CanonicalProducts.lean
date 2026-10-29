/- Prepared outside frozen root snapshot. Not Lean checked. Actual canonical
pair cancellation for the off-diagonal particle variance proof. -/
import DGRHS.Decoupling.Product
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.L2Space
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DGRHS.CanonicalVariance
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι]
variable (μ : Measure S) [IsProbabilityMeasure μ]

lemma triple_pair_first_preserving :
    MeasurePreserving (fun p : S × (S × S) ↦ (p.1,p.2.1))
      (μ.prod (μ.prod μ)) (μ.prod μ) := by
  exact (MeasurePreserving.id μ).prod measurePreserving_fst
lemma triple_pair_second_preserving :
    MeasurePreserving (fun p : S × (S × S) ↦ (p.1,p.2.2))
      (μ.prod (μ.prod μ)) (μ.prod μ) := by
  exact (MeasurePreserving.id μ).prod measurePreserving_snd

lemma integrable_common_row_product (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ)) :
    Integrable (fun p : S × (S × S) ↦ h (p.1,p.2.1) * h (p.1,p.2.2))
      (μ.prod (μ.prod μ)) :=
  (hh.comp_measurePreserving (triple_pair_first_preserving μ)).integrable_mul
    (hh.comp_measurePreserving (triple_pair_second_preserving μ))

lemma integral_common_row_product_eq_zero (h : S × S → ℝ)
    (hh : MemLp h 2 (μ.prod μ))
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0) :
    (∫ p : S × (S × S), h (p.1,p.2.1) * h (p.1,p.2.2)
      ∂μ.prod (μ.prod μ)) = 0 := by
  rw [integral_prod _ (integrable_common_row_product μ h hh)]
  have he : (∫ x, ∫ yz : S × S, h (x,yz.1) * h (x,yz.2) ∂μ.prod μ ∂μ) =
      ∫ x, (∫ y, h (x,y) ∂μ) * (∫ z, h (x,z) ∂μ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    exact integral_prod_mul (fun y ↦ h (x,y)) (fun z ↦ h (x,z))
  rw [he]
  have hz : (fun x ↦ (∫ y, h (x,y) ∂μ) * (∫ z, h (x,z) ∂μ)) =ᵐ[μ]
      (fun _ ↦ 0) := hc.mono (fun x hx ↦ by dsimp only; rw [hx, zero_mul])
  rw [integral_congr_ae hz, integral_zero]

lemma triple_eval_measurePreserving (i j k : ι) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) :
    MeasurePreserving (fun x : ι → S ↦ (x i,(x j,x k)))
      (Measure.pi (fun _ ↦ μ)) (μ.prod (μ.prod μ)) := by
  have hi : iIndepFun (fun i (x : ι → S) ↦ x i) (Measure.pi (fun _ ↦ μ)) :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have h := (hi.indepFun_prodMk (fun i ↦ measurable_pi_apply i) j k i hij.symm hik.symm).symm
  refine ⟨by fun_prop, ?_⟩
  rw [h.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    ((measurable_pi_apply j).prodMk (measurable_pi_apply k)).aemeasurable,
    (measurePreserving_eval (fun _ : ι ↦ μ) i).map_eq,
    (DGRHS.Decoupling.pair_eval_measurePreserving μ j k hjk).map_eq]

lemma integral_canonical_kernel_eq_zero (h : S × S → ℝ)
    (hh : MemLp h 2 (μ.prod μ))
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0) :
    (∫ p, h p ∂μ.prod μ) = 0 := by
  rw [integral_prod _ (hh.integrable (by norm_num)), integral_congr_ae hc]
  simp

lemma integral_coupled_term_eq_zero (h : S × S → ℝ)
    (hh : MemLp h 2 (μ.prod μ))
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0) (i j : ι) (hij : i ≠ j) :
    (∫ x : ι → S, h (x i,x j) ∂Measure.pi (fun _ ↦ μ)) = 0 := by
  have hp := DGRHS.Decoupling.pair_eval_measurePreserving μ i j hij
  calc
    _ = ∫ p, h p ∂(Measure.pi (fun _ : ι ↦ μ)).map (fun x ↦ (x i,x j)) :=
      (integral_map hp.measurable.aemeasurable
        (by rw [hp.map_eq]; exact hh.aestronglyMeasurable)).symm
    _ = ∫ p, h p ∂μ.prod μ := by rw [hp.map_eq]
    _ = 0 := integral_canonical_kernel_eq_zero μ h hh hc

lemma integral_common_index_eq_zero (h : S × S → ℝ)
    (hh : MemLp h 2 (μ.prod μ))
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∫ x : ι → S, h (x i,x j) * h (x i,x k) ∂Measure.pi (fun _ ↦ μ)) = 0 := by
  have hp := triple_eval_measurePreserving μ i j k hij hik hjk
  have hF := integrable_common_row_product μ h hh
  calc
    _ = ∫ p : S × (S × S), h (p.1,p.2.1) * h (p.1,p.2.2)
        ∂(Measure.pi (fun _ : ι ↦ μ)).map (fun x ↦ (x i,(x j,x k))) :=
      (integral_map hp.measurable.aemeasurable
        (by rw [hp.map_eq]; exact hF.aestronglyMeasurable)).symm
    _ = ∫ p : S × (S × S), h (p.1,p.2.1) * h (p.1,p.2.2)
        ∂μ.prod (μ.prod μ) := by rw [hp.map_eq]
    _ = 0 := integral_common_row_product_eq_zero μ h hh hc

lemma integrable_coupled_pair_product (h : S × S → ℝ)
    (hh : MemLp h 2 (μ.prod μ)) (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l) :
    Integrable (fun x : ι → S ↦ h (x i,x j) * h (x k,x l))
      (Measure.pi (fun _ ↦ μ)) :=
  (DGRHS.Decoupling.memLp_coupled_term μ h 2 hh i j hij).integrable_mul
    (DGRHS.Decoupling.memLp_coupled_term μ h 2 hh k l hkl)

lemma integral_disjoint_pairs_eq_zero (h : S × S → ℝ)
    (hm : Measurable h) (hh : MemLp h 2 (μ.prod μ))
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
    (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    (∫ x : ι → S, h (x i,x j) * h (x k,x l) ∂Measure.pi (fun _ ↦ μ)) = 0 := by
  have hi : iIndepFun (fun i (x : ι → S) ↦ x i) (Measure.pi (fun _ ↦ μ)) :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have hd := (hi.indepFun_prodMk_prodMk (fun i ↦ measurable_pi_apply i)
    i j k l hik hil hjk hjl).comp hm hm
  have h1 := DGRHS.Decoupling.memLp_coupled_term μ h 2 hh i j hij
  have h2 := DGRHS.Decoupling.memLp_coupled_term μ h 2 hh k l hkl
  have he := hd.integral_mul_eq_mul_integral h1.aestronglyMeasurable h2.aestronglyMeasurable
  simp only [Function.comp_def,Pi.mul_apply] at he
  rw [he, integral_coupled_term_eq_zero μ h hh hc i j hij, zero_mul]

lemma symmetric_coupled_term_ae (h : S × S → ℝ)
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p) (i j : ι) (hij : i ≠ j) :
    (fun x : ι → S ↦ h (x j,x i)) =ᵐ[Measure.pi (fun _ ↦ μ)]
      (fun x ↦ h (x i,x j)) :=
  (DGRHS.Decoupling.pair_eval_measurePreserving μ i j hij).quasiMeasurePreserving.ae hs

lemma integral_coupled_term_sq (h : S × S → ℝ)
    (hh : MemLp h 2 (μ.prod μ)) (i j : ι) (hij : i ≠ j) :
    (∫ x : ι → S, h (x i,x j)^2 ∂Measure.pi (fun _ ↦ μ)) =
      ∫ p, h p^2 ∂μ.prod μ := by
  have hp := DGRHS.Decoupling.pair_eval_measurePreserving μ i j hij
  calc
    _ = ∫ p, h p^2 ∂(Measure.pi (fun _ : ι ↦ μ)).map (fun x ↦ (x i,x j)) :=
      (integral_map hp.measurable.aemeasurable
        (by rw [hp.map_eq]; exact hh.integrable_sq.aestronglyMeasurable)).symm
    _ = ∫ p, h p^2 ∂μ.prod μ := by rw [hp.map_eq]

end DGRHS.CanonicalVariance
#print axioms DGRHS.CanonicalVariance.integral_common_row_product_eq_zero
#print axioms DGRHS.CanonicalVariance.triple_eval_measurePreserving
#print axioms DGRHS.CanonicalVariance.integral_coupled_term_eq_zero
#print axioms DGRHS.CanonicalVariance.integral_common_index_eq_zero
#print axioms DGRHS.CanonicalVariance.integral_disjoint_pairs_eq_zero
#print axioms DGRHS.CanonicalVariance.integrable_coupled_pair_product
#print axioms DGRHS.CanonicalVariance.symmetric_coupled_term_ae
#print axioms DGRHS.CanonicalVariance.integral_coupled_term_sq
