import Mathlib

/-!
# Tensor completeness for an orthonormal basis of `L²(μ)` (item S1)

Let `μ` be a probability measure on `α` and `e : ℕ → α → ℝ` an orthonormal family in `L²(μ)`
that is complete (the only `L²` function orthogonal to every `e j` is `0` a.e.).  On `Fin N → α`
with the product measure `Q μ N := Measure.pi (fun _ => μ)` the tensor products
`E e j ω = ∏ i, e (j i) (ω i)`, `j : Fin N → ℕ`, are again orthonormal and complete in
`L²(Q μ N)`.

* `tensor_memLp` : each `E e j` is in `L²`;
* `tensor_orthonormal` : orthonormality (Fubini for products);
* `tensor_complete` : completeness (induction on `N`, splitting off the first coordinate with
  `measurePreserving_piFinSuccAbove`);
* `tensorHB` : the resulting Hilbert basis of `Lp ℝ 2 (Q μ N)`.
-/

open MeasureTheory

namespace SharpLSI.FL.Spectral

section Defs

variable {α : Type}

/-- The tensor product `ω ↦ ∏ i, e (j i) (ω i)` of the basis functions indexed by
`j : Fin N → ℕ`. -/
def E (e : ℕ → α → ℝ) {N : ℕ} (j : Fin N → ℕ) (ω : Fin N → α) : ℝ :=
  ∏ i, e (j i) (ω i)

lemma E_apply (e : ℕ → α → ℝ) {N : ℕ} (j : Fin N → ℕ) (ω : Fin N → α) :
    E e j ω = ∏ i, e (j i) (ω i) := rfl

lemma E_cons (e : ℕ → α → ℝ) {n : ℕ} (a : ℕ) (j : Fin n → ℕ) (x : α) (y : Fin n → α) :
    E e (Fin.cons a j : Fin (n + 1) → ℕ) (Fin.cons x y : Fin (n + 1) → α) = e a x * E e j y := by
  simp [E, Fin.prod_univ_succ]

end Defs

section Tensor

variable {α : Type} [MeasurableSpace α]

/-- The `N`-fold product measure on `Fin N → α`. -/
noncomputable abbrev Q (μ : Measure α) (N : ℕ) : Measure (Fin N → α) :=
  Measure.pi (fun _ : Fin N => μ)

variable (μ : Measure α) [IsProbabilityMeasure μ] (e : ℕ → α → ℝ)

/-! ### Membership in `L²` -/

/-- Every tensor product of basis functions lies in `L²(Q μ N)`. -/
theorem tensor_memLp (he_mem : ∀ j, MemLp (e j) 2 μ) (N : ℕ) (j : Fin N → ℕ) :
    MemLp (E e j) 2 (Q μ N) := by
  have hmeas : AEStronglyMeasurable (E e j) (Q μ N) := by
    unfold E
    refine Finset.aestronglyMeasurable_fun_prod _ (fun i _ => ?_)
    exact (he_mem (j i)).aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving
  rw [memLp_two_iff_integrable_sq hmeas]
  have hsq : (fun ω : Fin N → α => E e j ω ^ 2) =
      fun ω : Fin N → α => ∏ i, (e (j i) (ω i)) ^ 2 := by
    funext ω
    simp [E, Finset.prod_pow]
  rw [hsq]
  exact Integrable.fintype_prod (f := fun i (x : α) => (e (j i) x) ^ 2)
    (fun i => (he_mem (j i)).integrable_sq)

/-! ### Orthonormality -/

/-- The tensor products are orthonormal in `L²(Q μ N)`. -/
theorem tensor_orthonormal
    (he_orth : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0)
    (N : ℕ) (j j' : Fin N → ℕ) :
    ∫ ω, E e j ω * E e j' ω ∂(Q μ N) = if j = j' then 1 else 0 := by
  have h1 : ∀ ω : Fin N → α, E e j ω * E e j' ω = ∏ i, (e (j i) (ω i) * e (j' i) (ω i)) := by
    intro ω
    simp only [E, Finset.prod_mul_distrib]
  simp_rw [h1]
  rw [integral_fintype_prod_eq_prod (fun i (x : α) => e (j i) x * e (j' i) x)]
  simp_rw [he_orth]
  by_cases h : j = j'
  · subst h
    simp
  · simp only [h, ↓reduceIte]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-! ### Completeness -/

section Step

variable {β : Type} [MeasurableSpace β]

omit [IsProbabilityMeasure μ] in
/-- A product `u(x) v(y)` of `L²` functions in separate variables is `L²` on the product. -/
lemma memLp_mul_prod {ρ : Measure β} [IsProbabilityMeasure ρ] {u : α → ℝ} {v : β → ℝ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 ρ) :
    MemLp (fun z : α × β => u z.1 * v z.2) 2 (μ.prod ρ) := by
  have hm : AEStronglyMeasurable (fun z : α × β => u z.1 * v z.2) (μ.prod ρ) :=
    hu.aestronglyMeasurable.comp_fst.mul hv.aestronglyMeasurable.comp_snd
  rw [memLp_two_iff_integrable_sq hm]
  have hsq : (fun z : α × β => (u z.1 * v z.2) ^ 2) = fun z => u z.1 ^ 2 * v z.2 ^ 2 := by
    funext z
    ring
  rw [hsq]
  exact hu.integrable_sq.mul_prod hv.integrable_sq

/-- Cauchy–Schwarz against a unit vector: `(∫ u v)² ≤ ∫ u²` when `∫ v² = 1`. -/
lemma sq_integral_mul_le {ρ : Measure β} {u v : β → ℝ} (hu : MemLp u 2 ρ) (hv : MemLp v 2 ρ)
    (hv1 : ∫ y, v y * v y ∂ρ = 1) :
    (∫ y, u y * v y ∂ρ) ^ 2 ≤ ∫ y, u y ^ 2 ∂ρ := by
  obtain ⟨C, hC⟩ : ∃ C, C = ∫ y, u y * v y ∂ρ := ⟨_, rfl⟩
  rw [← hC]
  have hint1 : Integrable (fun y => u y ^ 2) ρ := hu.integrable_sq
  have hint2 : Integrable (fun y => u y * v y) ρ := hu.integrable_mul hv
  have hint3 : Integrable (fun y => v y * v y) ρ := hv.integrable_mul hv
  have h0 : 0 ≤ ∫ y, (u y - C * v y) ^ 2 ∂ρ := integral_nonneg (fun y => sq_nonneg _)
  have e1 : ∀ y, (u y - C * v y) ^ 2 =
      u y ^ 2 - (2 * C) * (u y * v y) + (C * C) * (v y * v y) := by
    intro y
    ring
  have h2 : ∫ y, (u y - C * v y) ^ 2 ∂ρ = ∫ y, u y ^ 2 ∂ρ - 2 * C * C + C * C * 1 := by
    have i2 : Integrable (fun y => (2 * C) * (u y * v y)) ρ := hint2.const_mul _
    have i3 : Integrable (fun y => (C * C) * (v y * v y)) ρ := hint3.const_mul _
    have i1 : Integrable (fun y => u y ^ 2 - (2 * C) * (u y * v y)) ρ := hint1.sub i2
    simp_rw [e1]
    rw [integral_add i1 i3, integral_sub hint1 i2, integral_const_mul, integral_const_mul, hv1,
      ← hC]
  nlinarith

/-- **Inductive step.**  If `e` is complete on `(α, μ)`, a family `E'` is orthonormal and complete
on `(β, ρ)`, then an `L²(μ ⊗ ρ)` function orthogonal to all `e a ⊗ E' j` vanishes a.e. -/
theorem step_complete {ρ : Measure β} [IsProbabilityMeasure ρ] {J : Type} [Countable J]
    (E' : J → β → ℝ)
    (he_mem : ∀ a, MemLp (e a) 2 μ)
    (he_complete : ∀ f : α → ℝ, MemLp f 2 μ → (∀ j, ∫ x, f x * e j x ∂μ = 0) → f =ᵐ[μ] 0)
    (hE_mem : ∀ j, MemLp (E' j) 2 ρ)
    (hE_norm : ∀ j, ∫ y, E' j y * E' j y ∂ρ = 1)
    (hE_complete : ∀ g : β → ℝ, MemLp g 2 ρ → (∀ j, ∫ y, g y * E' j y ∂ρ = 0) → g =ᵐ[ρ] 0)
    (F : α × β → ℝ) (hF : MemLp F 2 (μ.prod ρ))
    (horth : ∀ a j, ∫ z, F z * (e a z.1 * E' j z.2) ∂(μ.prod ρ) = 0) :
    F =ᵐ[μ.prod ρ] 0 := by
  have hF2 : Integrable (fun z => F z ^ 2) (μ.prod ρ) := hF.integrable_sq
  have hslice_int : ∀ᵐ x ∂μ, Integrable (fun y => F (x, y) ^ 2) ρ := hF2.prod_right_ae
  have hslice_meas : ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => F (x, y)) ρ :=
    hF.aestronglyMeasurable.prodMk_left
  have hslice_mem : ∀ᵐ x ∂μ, MemLp (fun y => F (x, y)) 2 ρ := by
    filter_upwards [hslice_int, hslice_meas] with x h1 h2
    exact (memLp_two_iff_integrable_sq h2).2 h1
  have hh_int : Integrable (fun x => ∫ y, F (x, y) ^ 2 ∂ρ) μ := hF2.integral_prod_left
  have hE_snd : ∀ j, MemLp (fun z : α × β => E' j z.2) 2 (μ.prod ρ) := fun j =>
    (hE_mem j).comp_measurePreserving (measurePreserving_snd (μ := μ) (ν := ρ))
  have hprod_int : ∀ j, Integrable (fun z : α × β => F z * E' j z.2) (μ.prod ρ) :=
    fun j => hF.integrable_mul (hE_snd j)
  obtain ⟨g, hg⟩ : ∃ g : J → α → ℝ, ∀ j x, g j x = ∫ y, F (x, y) * E' j y ∂ρ :=
    ⟨fun j x => ∫ y, F (x, y) * E' j y ∂ρ, fun _ _ => rfl⟩
  have hg_meas : ∀ j, AEStronglyMeasurable (g j) μ := by
    intro j
    have := (hprod_int j).aestronglyMeasurable.integral_prod_right'
    exact this.congr (Filter.Eventually.of_forall (fun x => (hg j x).symm))
  have hg_mem : ∀ j, MemLp (g j) 2 μ := by
    intro j
    rw [memLp_two_iff_integrable_sq (hg_meas j)]
    refine Integrable.mono' hh_int ((hg_meas j).mul (hg_meas j) |>.congr
      (Filter.Eventually.of_forall (fun x => by simp [sq]))) ?_
    filter_upwards [hslice_mem] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hg]
    exact sq_integral_mul_le hx (hE_mem j) (hE_norm j)
  have hg_orth : ∀ j a, ∫ x, g j x * e a x ∂μ = 0 := by
    intro j a
    have hint : Integrable (fun z : α × β => F z * (e a z.1 * E' j z.2)) (μ.prod ρ) :=
      hF.integrable_mul (memLp_mul_prod μ (he_mem a) (hE_mem j))
    calc ∫ x, g j x * e a x ∂μ
        = ∫ x, ∫ y, F (x, y) * (e a x * E' j y) ∂ρ ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          show g j x * e a x = _
          rw [hg, ← integral_mul_const]
          refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
          show F (x, y) * E' j y * e a x = _
          ring
      _ = ∫ z, F z * (e a z.1 * E' j z.2) ∂(μ.prod ρ) := (integral_prod _ hint).symm
      _ = 0 := horth a j
  have hg_zero : ∀ j, g j =ᵐ[μ] 0 := fun j => he_complete (g j) (hg_mem j) (hg_orth j)
  have hall : ∀ᵐ x ∂μ, ∀ j, g j x = 0 := by
    rw [ae_all_iff]
    intro j
    filter_upwards [hg_zero j] with x hx
    simpa using hx
  have hslice_zero : ∀ᵐ x ∂μ, (fun y => F (x, y)) =ᵐ[ρ] 0 := by
    filter_upwards [hslice_mem, hall] with x hx hgx
    exact hE_complete _ hx (fun j => by rw [← hg]; exact hgx j)
  have hh0 : ∀ᵐ x ∂μ, ∫ y, F (x, y) ^ 2 ∂ρ = (0 : α → ℝ) x := by
    filter_upwards [hslice_zero] with x hx
    have hx2 : (fun y => F (x, y) ^ 2) =ᵐ[ρ] 0 := by
      filter_upwards [hx] with y hy
      simp [hy]
    simpa using integral_eq_zero_of_ae hx2
  have hint0 : ∫ z, F z ^ 2 ∂(μ.prod ρ) = 0 := by
    rw [integral_prod _ hF2]
    exact (integral_congr_ae hh0).trans (by simp)
  have hz : (fun z => F z ^ 2) =ᵐ[μ.prod ρ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg (F z)) hF2).1 hint0
  filter_upwards [hz] with z hz'
  simpa using hz'

end Step

lemma piFinSuccAbove_zero_symm {n : ℕ} (x : α) (y : Fin n → α) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm (x, y) =
      (Fin.cons x y : Fin (n + 1) → α) := by
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  exact Fin.insertNth_zero' x y

/-- Completeness of the tensor products, by induction on `N`. -/
theorem tensor_complete_aux (he_mem : ∀ j, MemLp (e j) 2 μ)
    (he_orth : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0)
    (he_complete : ∀ f : α → ℝ, MemLp f 2 μ → (∀ j, ∫ x, f x * e j x ∂μ = 0) → f =ᵐ[μ] 0)
    (N : ℕ) :
    ∀ f : (Fin N → α) → ℝ, MemLp f 2 (Q μ N) →
      (∀ j : Fin N → ℕ, ∫ ω, f ω * E e j ω ∂(Q μ N) = 0) → f =ᵐ[Q μ N] 0 := by
  induction N with
  | zero =>
    intro f _ h
    have hE1 : ∀ (j : Fin 0 → ℕ) (ω : Fin 0 → α), E e j ω = 1 := by
      intro j ω
      simp [E]
    have hc : ∀ ω : Fin 0 → α, ω = (fun i => i.elim0) := fun ω => funext fun i => i.elim0
    have h0 := h (fun i => i.elim0)
    have hfz : f (fun i => i.elim0) = 0 := by
      have hconst : ∀ ω : Fin 0 → α,
          f ω * E e (fun i => i.elim0) ω = f (fun i => i.elim0) := by
        intro ω
        rw [hE1, mul_one, ← hc ω]
      simp_rw [hconst] at h0
      simpa [integral_const] using h0
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [hc ω]
    simpa using hfz
  | succ n ih =>
    intro f hf horth
    have hmp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0)
        (Q μ (n + 1)) (μ.prod (Q μ n)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
    have hF : MemLp (f ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm) 2
        (μ.prod (Q μ n)) := hf.comp_measurePreserving hmp.symm
    have hE_norm : ∀ j : Fin n → ℕ, ∫ y, E e j y * E e j y ∂(Q μ n) = 1 := by
      intro j
      rw [tensor_orthonormal μ e he_orth n j j]
      simp
    have key := step_complete μ e (fun j : Fin n → ℕ => E e j) he_mem he_complete
      (tensor_memLp μ e he_mem n) hE_norm (ih)
      (f ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm) hF ?_
    · have hae := hmp.quasiMeasurePreserving.ae key
      filter_upwards [hae] with ω hω
      simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply, Pi.zero_apply] at hω
      exact hω
    · intro a j
      have h1 := horth (Fin.cons a j : Fin (n + 1) → ℕ)
      rw [← hmp.symm.integral_comp'
        (fun ω => f ω * E e (Fin.cons a j : Fin (n + 1) → ℕ) ω)] at h1
      rw [← h1]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      obtain ⟨x, y⟩ := z
      simp only [Function.comp_apply, piFinSuccAbove_zero_symm, E_cons]

/-- **Completeness.**  If `e` is an orthonormal, complete family in `L²(μ)`, then the only
`L²(Q μ N)` function orthogonal to every tensor `E e j` is `0` a.e. -/
theorem tensor_complete (he_mem : ∀ j, MemLp (e j) 2 μ)
    (he_orth : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0)
    (he_complete : ∀ f : α → ℝ, MemLp f 2 μ → (∀ j, ∫ x, f x * e j x ∂μ = 0) → f =ᵐ[μ] 0)
    (N : ℕ) (f : (Fin N → α) → ℝ) (hf : MemLp f 2 (Q μ N))
    (horth : ∀ j : Fin N → ℕ, ∫ ω, f ω * E e j ω ∂(Q μ N) = 0) :
    f =ᵐ[Q μ N] 0 :=
  tensor_complete_aux μ e he_mem he_orth he_complete N f hf horth

/-! ### The tensor Hilbert basis -/

section HilbertBasis

/-- The `L²(Q μ N)` class of the tensor `E e j`. -/
noncomputable def tensorLp (he_mem : ∀ j, MemLp (e j) 2 μ) (N : ℕ) (j : Fin N → ℕ) :
    Lp ℝ 2 (Q μ N) :=
  (tensor_memLp μ e he_mem N j).toLp (E e j)

lemma tensorLp_ae (he_mem : ∀ j, MemLp (e j) 2 μ) (N : ℕ) (j : Fin N → ℕ) :
    (tensorLp μ e he_mem N j : (Fin N → α) → ℝ) =ᵐ[Q μ N] E e j :=
  (tensor_memLp μ e he_mem N j).coeFn_toLp

/-- The classes `tensorLp` form an orthonormal family in `L²(Q μ N)`. -/
theorem tensorLp_orthonormal (he_mem : ∀ j, MemLp (e j) 2 μ)
    (he_orth : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0) (N : ℕ) :
    Orthonormal ℝ (tensorLp μ e he_mem N) := by
  rw [orthonormal_iff_ite]
  intro j j'
  rw [L2.inner_def]
  have hae : ∀ᵐ ω ∂(Q μ N), inner ℝ (tensorLp μ e he_mem N j ω) (tensorLp μ e he_mem N j' ω) =
      E e j ω * E e j' ω := by
    filter_upwards [tensorLp_ae μ e he_mem N j, tensorLp_ae μ e he_mem N j'] with ω a b
    rw [RCLike.inner_apply, a, b]
    simp [mul_comm]
  rw [integral_congr_ae hae, tensor_orthonormal μ e he_orth N j j']

/-- The orthogonal complement of the span of the tensors is trivial. -/
theorem tensorLp_orthogonal_eq_bot (he_mem : ∀ j, MemLp (e j) 2 μ)
    (he_orth : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0)
    (he_complete : ∀ f : α → ℝ, MemLp f 2 μ → (∀ j, ∫ x, f x * e j x ∂μ = 0) → f =ᵐ[μ] 0)
    (N : ℕ) :
    (Submodule.span ℝ (Set.range (tensorLp μ e he_mem N)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  rw [Submodule.mem_orthogonal] at hf
  have hf' : ∀ j : Fin N → ℕ, ∫ ω, f ω * E e j ω ∂(Q μ N) = 0 := by
    intro j
    have h0 := hf (tensorLp μ e he_mem N j) (Submodule.subset_span ⟨j, rfl⟩)
    rw [L2.inner_def] at h0
    rw [← h0]
    refine integral_congr_ae ?_
    filter_upwards [tensorLp_ae μ e he_mem N j] with ω a
    rw [RCLike.inner_apply, a]
    simp
  exact Lp.eq_zero_iff_ae_eq_zero.2
    (tensor_complete μ e he_mem he_orth he_complete N f (Lp.memLp f) hf')

/-- **The tensor Hilbert basis.**  The functions `E e j`, `j : Fin N → ℕ`, form a Hilbert basis of
`L²(Q μ N)`. -/
noncomputable def tensorHB (he_mem : ∀ j, MemLp (e j) 2 μ)
    (he_orth : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0)
    (he_complete : ∀ f : α → ℝ, MemLp f 2 μ → (∀ j, ∫ x, f x * e j x ∂μ = 0) → f =ᵐ[μ] 0)
    (N : ℕ) : HilbertBasis (Fin N → ℕ) ℝ (Lp ℝ 2 (Q μ N)) :=
  HilbertBasis.mkOfOrthogonalEqBot (tensorLp_orthonormal μ e he_mem he_orth N)
    (tensorLp_orthogonal_eq_bot μ e he_mem he_orth he_complete N)

theorem tensorHB_coe (he_mem : ∀ j, MemLp (e j) 2 μ)
    (he_orth : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0)
    (he_complete : ∀ f : α → ℝ, MemLp f 2 μ → (∀ j, ∫ x, f x * e j x ∂μ = 0) → f =ᵐ[μ] 0)
    (N : ℕ) : ⇑(tensorHB μ e he_mem he_orth he_complete N) = tensorLp μ e he_mem N :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- The `j`-th vector of `tensorHB` is (a.e.) the function `E e j`. -/
theorem tensorHB_apply (he_mem : ∀ j, MemLp (e j) 2 μ)
    (he_orth : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0)
    (he_complete : ∀ f : α → ℝ, MemLp f 2 μ → (∀ j, ∫ x, f x * e j x ∂μ = 0) → f =ᵐ[μ] 0)
    (N : ℕ) (j : Fin N → ℕ) :
    (tensorHB μ e he_mem he_orth he_complete N j : (Fin N → α) → ℝ) =ᵐ[Q μ N] E e j := by
  rw [tensorHB_coe]
  exact tensorLp_ae μ e he_mem N j

end HilbertBasis

end Tensor

end SharpLSI.FL.Spectral
