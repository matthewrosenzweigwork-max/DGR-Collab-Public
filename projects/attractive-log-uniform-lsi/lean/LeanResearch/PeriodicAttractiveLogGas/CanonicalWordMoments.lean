import LeanResearch.PeriodicAttractiveLogGas.CanonicalDecoupling
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Literal ordered-slot word products from the decoupled moment expansion in
`thm:canonical-pairs`. Finite Hölder supplies product integrability; singleton
rows/columns are removed using AE canonicality and independent-coordinate Fubini. -/

noncomputable section
open MeasureTheory Finset
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas.CanonicalWordMoments

open PeriodicAttractiveLogGas.CanonicalDecoupling

variable {m n : ℕ} {α : Fin m → Type*} [∀ i, MeasurableSpace (α i)]
  (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
  (f : ∀ i j, α i → α j → ℝ)

/-- A row word and a column word specify the actual ordered kernel factors. -/
def wordProduct (r c : Fin n → Fin m) (Z : (∀ i, α i) × (∀ i, α i)) : ℝ :=
  ∏ ℓ, f (r ℓ) (c ℓ) (Z.1 (r ℓ)) (Z.2 (c ℓ))

theorem measurable_wordProduct
    (hf : ∀ i j, Measurable (Function.uncurry (f i j))) (r c : Fin n → Fin m) :
    Measurable (wordProduct f r c) := by
  apply Finset.measurable_prod
  intro ℓ _
  exact (hf (r ℓ) (c ℓ)).comp
    (((measurable_pi_apply (r ℓ)).comp measurable_fst).prodMk
      ((measurable_pi_apply (c ℓ)).comp measurable_snd))

/-- Generalized Hölder at the slot count; independence between factors is not required. -/
theorem integrable_wordProduct (hn : 1 ≤ n)
    (hmem : ∀ i j, MemLp (Function.uncurry (f i j)) (n : ℝ≥0∞) ((ν i).prod (ν j)))
    (r c : Fin n → Fin m) :
    Integrable (wordProduct f r c) ((Measure.pi ν).prod (Measure.pi ν)) := by
  have hterms (ℓ : Fin n) : MemLp
      (fun Z : (∀ i, α i) × (∀ i, α i) => f (r ℓ) (c ℓ) (Z.1 (r ℓ)) (Z.2 (c ℓ)))
      (n : ℝ≥0∞) ((Measure.pi ν).prod (Measure.pi ν)) :=
    (hmem (r ℓ) (c ℓ)).comp_measurePreserving (measurePreserving_decoupled_eval ν (r ℓ) (c ℓ))
  have hp := MemLp.fun_prod (s := (Finset.univ : Finset (Fin n))) (fun ℓ _ => hterms ℓ)
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have he : (∑ _ℓ : Fin n, (n : ℝ≥0∞)⁻¹)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [ENNReal.mul_inv_cancel hn0 (ENNReal.natCast_ne_top n), inv_one]
  rw [he] at hp
  exact MemLp.integrable le_rfl hp

omit [∀ i, MeasurableSpace (α i)] in
/-- Literal finite expansion, with row and column words separately enumerated. -/
theorem decoupledSum_pow_eq_sum_wordProducts (rpow : ℕ) (Z : (∀ i, α i) × (∀ i, α i)) :
    decoupledSum f Z ^ rpow =
      ∑ r : Fin rpow → Fin m, ∑ c : Fin rpow → Fin m, wordProduct f r c Z := by
  unfold decoupledSum wordProduct
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro r _
  exact Fintype.prod_sum (fun ℓ j => f (r ℓ) j (Z.1 (r ℓ)) (Z.2 j))

theorem integral_decoupledSum_pow_eq_sum (hn : 1 ≤ n)
    (hmem : ∀ i j, MemLp (Function.uncurry (f i j)) (n : ℝ≥0∞) ((ν i).prod (ν j))) :
    (∫ Z, decoupledSum f Z ^ n ∂(Measure.pi ν).prod (Measure.pi ν)) =
      ∑ r : Fin n → Fin m, ∑ c : Fin n → Fin m,
        ∫ Z, wordProduct f r c Z ∂(Measure.pi ν).prod (Measure.pi ν) := by
  simp_rw [decoupledSum_pow_eq_sum_wordProducts f n]
  rw [integral_finsetSum _ (fun r _ =>
    integrable_finsetSum _ (fun c _ => integrable_wordProduct ν f hn hmem r c))]
  apply Finset.sum_congr rfl
  intro r _
  exact integral_finsetSum _ (fun c _ => integrable_wordProduct ν f hn hmem r c)

/-- Replace one row coordinate by its value in a fresh independent vector. -/
def rowResample (i : Fin m)
    (ZW : ((∀ i, α i) × (∀ i, α i)) × ((∀ i, α i) × (∀ i, α i))) :
    (∀ i, α i) × (∀ i, α i) :=
  (mix (fun j => decide (j ≠ i)) (ZW.1.1, ZW.2.1), ZW.1.2)

theorem measurePreserving_rowResample (i : Fin m) :
    MeasurePreserving (rowResample (α := α) i)
      (((Measure.pi ν).prod (Measure.pi ν)).prod ((Measure.pi ν).prod (Measure.pi ν)))
      ((Measure.pi ν).prod (Measure.pi ν)) := by
  exact ((measurePreserving_mix ν (fun j => decide (j ≠ i))).prod
    (measurePreserving_fst (μ := Measure.pi ν) (ν := Measure.pi ν))).comp
      (measurePreserving_middle_swap (Measure.pi ν) (Measure.pi ν) (Measure.pi ν) (Measure.pi ν))

omit [∀ i, MeasurableSpace (α i)] in
/-- Exactly one factor depends on the resampled row coordinate. Other row and
column indices may repeat, and the erased product is one when `n = 1`. -/
theorem wordProduct_rowResample (r c : Fin n → Fin m) (ℓ₀ : Fin n)
    (hunique : ∀ ℓ, r ℓ = r ℓ₀ → ℓ = ℓ₀)
    (Z W : (∀ i, α i) × (∀ i, α i)) :
    wordProduct f r c (rowResample (r ℓ₀) (Z, W)) =
      f (r ℓ₀) (c ℓ₀) (W.1 (r ℓ₀)) (Z.2 (c ℓ₀)) *
        ∏ ℓ ∈ Finset.univ.erase ℓ₀, f (r ℓ) (c ℓ) (Z.1 (r ℓ)) (Z.2 (c ℓ)) := by
  unfold wordProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ℓ₀)]
  apply congrArg₂ (· * ·)
  · simp [rowResample, mix]
  · apply Finset.prod_congr rfl
    intro ℓ hℓ
    have hne : ℓ ≠ ℓ₀ := (Finset.mem_erase.mp hℓ).1
    have hr : r ℓ ≠ r ℓ₀ := fun h => hne (hunique ℓ h)
    simp [rowResample, mix, hr]

/-- The inner coordinate integral vanishes AE in the retained variables.
The exceptional set is pulled back from the law of the selected column. -/
theorem integral_rowResampled_wordProduct_eq_zero_ae
    (hf : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hleft : ∀ i j, ∀ᵐ y ∂ν j, (∫ x, f i j x y ∂ν i) = 0)
    (r c : Fin n → Fin m) (ℓ₀ : Fin n)
    (hunique : ∀ ℓ, r ℓ = r ℓ₀ → ℓ = ℓ₀) :
    ∀ᵐ Z ∂(Measure.pi ν).prod (Measure.pi ν),
      (∫ W, wordProduct f r c (rowResample (r ℓ₀) (Z, W))
        ∂(Measure.pi ν).prod (Measure.pi ν)) = 0 := by
  have hpcol : MeasurePreserving
      (fun Z : (∀ i, α i) × (∀ i, α i) => Z.2 (c ℓ₀))
      ((Measure.pi ν).prod (Measure.pi ν)) (ν (c ℓ₀)) :=
    (measurePreserving_eval ν (c ℓ₀)).comp measurePreserving_snd
  have hprow : MeasurePreserving
      (fun W : (∀ i, α i) × (∀ i, α i) => W.1 (r ℓ₀))
      ((Measure.pi ν).prod (Measure.pi ν)) (ν (r ℓ₀)) :=
    (measurePreserving_eval ν (r ℓ₀)).comp measurePreserving_fst
  filter_upwards [hpcol.quasiMeasurePreserving.ae (hleft (r ℓ₀) (c ℓ₀))] with Z hZ
  simp_rw [wordProduct_rowResample f r c ℓ₀ hunique Z]
  rw [integral_mul_const]
  have hsec : Measurable (fun x => f (r ℓ₀) (c ℓ₀) x (Z.2 (c ℓ₀))) :=
    (hf (r ℓ₀) (c ℓ₀)).comp (measurable_id.prodMk measurable_const)
  have he := integral_comp_of_measurePreserving hprow hsec.aestronglyMeasurable
  have hz : (∫ W, f (r ℓ₀) (c ℓ₀) (W.1 (r ℓ₀)) (Z.2 (c ℓ₀))
      ∂(Measure.pi ν).prod (Measure.pi ν)) = 0 := he.trans hZ
  rw [hz, zero_mul]

/-- True product-law singleton cancellation. Product integrability is derived
from the pairwise slot-count MemLp hypothesis before invoking Fubini. -/
theorem integral_wordProduct_eq_zero_of_row_singleton (hn : 1 ≤ n)
    (hf : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hmem : ∀ i j, MemLp (Function.uncurry (f i j)) (n : ℝ≥0∞) ((ν i).prod (ν j)))
    (hleft : ∀ i j, ∀ᵐ y ∂ν j, (∫ x, f i j x y ∂ν i) = 0)
    (r c : Fin n → Fin m) (ℓ₀ : Fin n)
    (hunique : ∀ ℓ, r ℓ = r ℓ₀ → ℓ = ℓ₀) :
    (∫ Z, wordProduct f r c Z ∂(Measure.pi ν).prod (Measure.pi ν)) = 0 := by
  have hP := integrable_wordProduct ν f hn hmem r c
  have hmp := measurePreserving_rowResample ν (r ℓ₀)
  have hR := hmp.integrable_comp_of_integrable hP
  calc
    (∫ Z, wordProduct f r c Z ∂(Measure.pi ν).prod (Measure.pi ν)) =
        ∫ ZW, wordProduct f r c (rowResample (r ℓ₀) ZW)
          ∂((Measure.pi ν).prod (Measure.pi ν)).prod ((Measure.pi ν).prod (Measure.pi ν)) :=
      (integral_comp_of_measurePreserving hmp hP.aestronglyMeasurable).symm
    _ = ∫ Z, ∫ W, wordProduct f r c (rowResample (r ℓ₀) (Z, W))
        ∂(Measure.pi ν).prod (Measure.pi ν) ∂(Measure.pi ν).prod (Measure.pi ν) :=
      integral_prod _ hR
    _ = ∫ _Z : (∀ i, α i) × (∀ i, α i), (0 : ℝ) ∂(Measure.pi ν).prod (Measure.pi ν) :=
      integral_congr_ae (integral_rowResampled_wordProduct_eq_zero_ae ν f hf hleft r c ℓ₀ hunique)
    _ = 0 := integral_zero _ _

/-- Column cancellation is row cancellation after swapping the two independent
copies and transposing each kernel. Only AE right canonicality is used. -/
theorem integral_wordProduct_eq_zero_of_column_singleton (hn : 1 ≤ n)
    (hf : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hmem : ∀ i j, MemLp (Function.uncurry (f i j)) (n : ℝ≥0∞) ((ν i).prod (ν j)))
    (hright : ∀ i j, ∀ᵐ x ∂ν i, (∫ y, f i j x y ∂ν j) = 0)
    (r c : Fin n → Fin m) (ℓ₀ : Fin n)
    (hunique : ∀ ℓ, c ℓ = c ℓ₀ → ℓ = ℓ₀) :
    (∫ Z, wordProduct f r c Z ∂(Measure.pi ν).prod (Measure.pi ν)) = 0 := by
  let ft : ∀ i j, α i → α j → ℝ := fun i j x y => f j i y x
  have hft (i j : Fin m) : Measurable (Function.uncurry (ft i j)) :=
    (hf j i).comp measurable_swap
  have hmt (i j : Fin m) :
      MemLp (Function.uncurry (ft i j)) (n : ℝ≥0∞) ((ν i).prod (ν j)) :=
    (hmem j i).comp_measurePreserving (Measure.measurePreserving_swap (μ := ν i) (ν := ν j))
  have hct (i j : Fin m) : ∀ᵐ y ∂ν j, (∫ x, ft i j x y ∂ν i) = 0 := hright j i
  have hrow := integral_wordProduct_eq_zero_of_row_singleton ν ft hn hft hmt hct c r ℓ₀ hunique
  have hP := integrable_wordProduct ν f hn hmem r c
  have he := integral_comp_of_measurePreserving
    (Measure.measurePreserving_swap (μ := Measure.pi ν) (ν := Measure.pi ν))
    hP.aestronglyMeasurable
  exact he.symm.trans hrow

/-- The multiplicity-one formulation used by the row-word count. -/
theorem integral_wordProduct_eq_zero_of_row_count_one (hn : 1 ≤ n)
    (hf : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hmem : ∀ i j, MemLp (Function.uncurry (f i j)) (n : ℝ≥0∞) ((ν i).prod (ν j)))
    (hleft : ∀ i j, ∀ᵐ y ∂ν j, (∫ x, f i j x y ∂ν i) = 0)
    (r c : Fin n → Fin m) (i : Fin m)
    (hcount : (Finset.univ.filter (fun ℓ => r ℓ = i)).card = 1) :
    (∫ Z, wordProduct f r c Z ∂(Measure.pi ν).prod (Measure.pi ν)) = 0 := by
  classical
  obtain ⟨ℓ₀, hℓ₀, huniq⟩ := Finset.card_eq_one_iff_existsUnique.mp hcount
  have hi : r ℓ₀ = i := (Finset.mem_filter.mp hℓ₀).2
  apply integral_wordProduct_eq_zero_of_row_singleton ν f hn hf hmem hleft r c ℓ₀
  intro ℓ hℓ
  exact huniq ℓ (Finset.mem_filter.mpr ⟨Finset.mem_univ ℓ, hℓ.trans hi⟩)

/-- The multiplicity-one formulation used by the column-word count. -/
theorem integral_wordProduct_eq_zero_of_column_count_one (hn : 1 ≤ n)
    (hf : ∀ i j, Measurable (Function.uncurry (f i j)))
    (hmem : ∀ i j, MemLp (Function.uncurry (f i j)) (n : ℝ≥0∞) ((ν i).prod (ν j)))
    (hright : ∀ i j, ∀ᵐ x ∂ν i, (∫ y, f i j x y ∂ν j) = 0)
    (r c : Fin n → Fin m) (i : Fin m)
    (hcount : (Finset.univ.filter (fun ℓ => c ℓ = i)).card = 1) :
    (∫ Z, wordProduct f r c Z ∂(Measure.pi ν).prod (Measure.pi ν)) = 0 := by
  classical
  obtain ⟨ℓ₀, hℓ₀, huniq⟩ := Finset.card_eq_one_iff_existsUnique.mp hcount
  have hi : c ℓ₀ = i := (Finset.mem_filter.mp hℓ₀).2
  apply integral_wordProduct_eq_zero_of_column_singleton ν f hn hf hmem hright r c ℓ₀
  intro ℓ hℓ
  exact huniq ℓ (Finset.mem_filter.mpr ⟨Finset.mem_univ ℓ, hℓ.trans hi⟩)

end PeriodicAttractiveLogGas.CanonicalWordMoments
