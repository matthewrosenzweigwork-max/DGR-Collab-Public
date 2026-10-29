import DGRHS.Attractive.FiniteHolder
import DGRHS.Decoupling.Moment

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.Attractive
variable {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ}

def arrayProduct (h : Ω × Ω → ℝ) (i j : Fin m → Fin n)
    (z : (Fin n → Ω) × (Fin n → Ω)) : ℝ :=
  ∏ l : Fin m, h (z.1 (i l), z.2 (j l))

def rowProduct (h : Ω × Ω → ℝ) (i j : Fin m → Fin n)
    (y : Fin n → Ω) (a : Fin n) (x : Ω) : ℝ :=
  ∏ l ∈ Finset.univ.filter (fun l ↦ i l = a), h (x,y (j l))

def multiplicity (i : Fin m → Fin n) (a : Fin n) : ℕ :=
  (Finset.univ.filter (fun l ↦ i l = a)).card

lemma arrayProduct_grouped (h : Ω × Ω → ℝ) (i j : Fin m → Fin n)
    (x y : Fin n → Ω) :
    (∏ a : Fin n, rowProduct h i j y a (x a)) = arrayProduct h i j (x,y) := by
  classical
  unfold rowProduct arrayProduct
  calc
    _ = ∏ a : Fin n, ∏ l ∈ Finset.univ.filter (fun l ↦ i l = a),
        h (x (i l),y (j l)) := by
      apply Finset.prod_congr rfl
      intro a ha
      apply Finset.prod_congr rfl
      intro l hl
      rw [(Finset.mem_filter.mp hl).2]
    _ = _ := Finset.prod_fiberwise Finset.univ i (fun l ↦ h (x (i l),y (j l)))

lemma arrayProduct_measurable (h : Ω × Ω → ℝ) (hh : Measurable h)
    (i j : Fin m → Fin n) : Measurable (arrayProduct h i j) := by
  unfold arrayProduct
  apply Finset.measurable_prod
  intro l hl
  exact hh.comp (((measurable_pi_apply (i l)).comp measurable_fst).prodMk
    ((measurable_pi_apply (j l)).comp measurable_snd))

lemma arrayProduct_section_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (i j : Fin m → Fin n) (y : Fin n → Ω) :
    Integrable (fun x ↦ arrayProduct h i j (x,y)) (Measure.pi (fun _ : Fin n ↦ μ)) := by
  have hi : ∀ a : Fin n, Integrable (rowProduct h i j y a) μ := fun a ↦
    (row_product_integrable_bound μ h hh C hC
      (Finset.univ.filter (fun l ↦ i l = a)) (fun l ↦ y (j l))).1
  convert Integrable.fintype_prod hi using 1
  funext x
  exact (arrayProduct_grouped h i j x y).symm

lemma arrayProduct_section_factorization (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (i j : Fin m → Fin n) (y : Fin n → Ω) :
    (∫ x : Fin n → Ω, arrayProduct h i j (x,y) ∂Measure.pi (fun _ ↦ μ)) =
      ∏ a : Fin n, ∫ x, rowProduct h i j y a x ∂μ := by
  simp_rw [← arrayProduct_grouped]
  exact integral_fintype_prod_eq_prod _

lemma arrayProduct_section_abs_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (i j : Fin m → Fin n) (y : Fin n → Ω) :
    (∫ x : Fin n → Ω, |arrayProduct h i j (x,y)| ∂Measure.pi (fun _ ↦ μ)) ≤
      ∏ a : Fin n, C^(multiplicity i a) * ((multiplicity i a).factorial : ℝ) := by
  classical
  simp_rw [← arrayProduct_grouped,Finset.abs_prod]
  rw [integral_fintype_prod_eq_prod (fun a x ↦ |rowProduct h i j y a x|)]
  apply Finset.prod_le_prod₀
  · intro a ha
    exact integral_nonneg fun x ↦ abs_nonneg _
  · intro a ha
    exact (row_product_integrable_bound μ h hh C hC
      (Finset.univ.filter (fun l ↦ i l = a)) (fun l ↦ y (j l))).2

/-- All omitted joint properness is supplied by the proper uniformly bounded
absolute section integrals before the mixed-array Fubini step. -/
lemma arrayProduct_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (i j : Fin m → Fin n) :
    Integrable (arrayProduct h i j)
      ((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ))) := by
  have hm := (arrayProduct_measurable h hh i j).stronglyMeasurable
  apply (integrable_prod_iff' hm.aestronglyMeasurable).2
  refine ⟨Filter.Eventually.of_forall (arrayProduct_section_integrable μ h hh C hC i j), ?_⟩
  apply (integrable_const (∏ a : Fin n,
    C^(multiplicity i a) * ((multiplicity i a).factorial : ℝ))).mono'
    hm.norm.integral_prod_left'.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y ↦ by
    have hnn : 0 ≤ ∫ x : Fin n → Ω, ‖arrayProduct h i j (x,y)‖
        ∂Measure.pi (fun _ ↦ μ) := integral_nonneg fun x ↦ norm_nonneg _
    rw [Real.norm_eq_abs,abs_of_nonneg hnn]
    simpa only [Real.norm_eq_abs] using arrayProduct_section_abs_bound μ h hh C hC i j y

#check @DGRHS.Attractive.arrayProduct_integrable
#print axioms DGRHS.Attractive.arrayProduct_integrable
#print axioms DGRHS.Attractive.arrayProduct_section_abs_bound

lemma sum_multiplicity (i : Fin m → Fin n) : ∑ a : Fin n, multiplicity i a = m := by
  classical
  simpa [multiplicity] using
    Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin m))
      (Finset.univ : Finset (Fin n)) i

lemma prod_powers_eq {ι : Type*} (s : Finset ι) (C : ℝ) (a : ι → ℕ) :
    (∏ i ∈ s, C^(a i)) = C^(∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.prod_insert hi,Finset.sum_insert hi,pow_add,ih]

lemma factorial_product_scale (C : ℝ) (i : Fin m → Fin n) :
    (∏ a : Fin n, C^(multiplicity i a) * ((multiplicity i a).factorial : ℝ)) =
      C^m * ∏ a : Fin n, ((multiplicity i a).factorial : ℝ) := by
  rw [Finset.prod_mul_distrib,prod_powers_eq,sum_multiplicity]

/-- The exact analytic array estimate in source2533–2567, including all properness
obligations. The survival restriction is unnecessary for this inequality. -/
theorem canonical_array_integral_abs_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (i j : Fin m → Fin n) :
    |∫ z, arrayProduct h i j z
      ∂((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ)))| ≤
      C^m * ∏ a : Fin n, ((multiplicity i a).factorial : ℝ) := by
  let ν := Measure.pi (fun _ : Fin n ↦ μ)
  have hi := arrayProduct_integrable μ h hh C hC i j
  have ha : Integrable (fun z ↦ |arrayProduct h i j z|) (ν.prod ν) := by
    simpa only [Real.norm_eq_abs] using hi.norm
  rw [← factorial_product_scale]
  calc
    _ ≤ ∫ z, |arrayProduct h i j z| ∂ν.prod ν := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (arrayProduct h i j)
    _ = ∫ y, ∫ x, |arrayProduct h i j (x,y)| ∂ν ∂ν := integral_prod_symm _ ha
    _ ≤ _ := by
      simpa using
        integral_mono_ae ha.integral_prod_right (integrable_const _)
          (Filter.Eventually.of_forall (arrayProduct_section_abs_bound μ h hh C hC i j))

/-- An unprimed label occurring once kills the actual mixed expectation. -/
theorem canonical_array_singleton_left (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (hc : ∀ᵐ y ∂μ, ∫ x, h (x,y) ∂μ = 0)
    (i j : Fin m → Fin n) (a : Fin n) (ha : multiplicity i a = 1) :
    (∫ z, arrayProduct h i j z
      ∂((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ)))) = 0 := by
  classical
  let ν := Measure.pi (fun _ : Fin n ↦ μ)
  obtain ⟨l,hl⟩ := Finset.card_eq_one.mp ha
  have hz : ∀ᵐ y ∂ν, ∫ x, rowProduct h i j y a x ∂μ = 0 := by
    filter_upwards [(measurePreserving_eval (fun _ : Fin n ↦ μ) (j l)).quasiMeasurePreserving.ae hc] with y hy
    simpa only [rowProduct,hl,Finset.prod_singleton] using hy
  have he : ∀ᵐ y ∂ν, (∫ x, arrayProduct h i j (x,y) ∂ν) = 0 := by
    filter_upwards [hz] with y hy
    rw [arrayProduct_section_factorization]
    exact Finset.prod_eq_zero (Finset.mem_univ a) hy
  rw [integral_prod_symm _ (arrayProduct_integrable μ h hh C hC i j),integral_congr_ae he]
  simp

/-- A primed singleton is killed by the true swapped-array law and symmetry. -/
theorem canonical_array_singleton_right (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (hs : ∀ x y, h (x,y) = h (y,x))
    (hc : ∀ᵐ y ∂μ, ∫ x, h (x,y) ∂μ = 0)
    (i j : Fin m → Fin n) (a : Fin n) (ha : multiplicity j a = 1) :
    (∫ z, arrayProduct h i j z
      ∂((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ)))) = 0 := by
  let ν := Measure.pi (fun _ : Fin n ↦ μ)
  have hm := (arrayProduct_integrable μ h hh C hC i j).aestronglyMeasurable
  calc
    _ = ∫ z, arrayProduct h i j z.swap ∂ν.prod ν :=
      (DGRHS.Decoupling.integral_comp_preserving
        (Measure.measurePreserving_swap (μ := ν) (ν := ν)) (arrayProduct h i j) hm).symm
    _ = ∫ z, arrayProduct h j i z ∂ν.prod ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z ↦ by
        unfold arrayProduct
        apply Finset.prod_congr rfl
        intro l hl
        exact hs _ _
    _ = 0 := canonical_array_singleton_left μ h hh C hC hc j i a ha

#check @DGRHS.Attractive.canonical_array_integral_abs_le
#check @DGRHS.Attractive.canonical_array_singleton_left
#check @DGRHS.Attractive.canonical_array_singleton_right
#print axioms DGRHS.Attractive.canonical_array_integral_abs_le
#print axioms DGRHS.Attractive.canonical_array_singleton_left
#print axioms DGRHS.Attractive.canonical_array_singleton_right
end DGRHS.Attractive
