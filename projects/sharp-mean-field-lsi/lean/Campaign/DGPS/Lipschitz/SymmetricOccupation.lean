import DGPS.Lipschitz.WeightedSpectrum
import DGPS.Particle.Sobolev
import DGPS.Particle.Symmetry
import DGPS.Particle.Contractions
import DGPS.FiniteN.Tools.WeightedSobolev
import DGPS.Particle.DiagonalForce
import DGPS.FiniteN.Tools.EntropyDefects

/-!
# Occupation basis and spectral tail (LIP057)

Let `μ` be a probability measure on `α` and `e : ℕ → α → ℝ` an orthonormal family in `L²(μ)`
that is complete (the only `L²` function orthogonal to every `e j` is `0` a.e.).  On `Fin N → α`
with the product measure `Qm μ N := Measure.pi (fun _ => μ)` the tensor products
`Tn e j ω = ∏ i, e (j i) (ω i)`, `j : Fin N → ℕ`, are again orthonormal and complete in
`L²(Qm μ N)`.

* `tensor_memLp` : each `Tn e j` is in `L²`;
* `tensor_orthonormal` : orthonormality (Fubini for products);
* `tensor_complete` : completeness (induction on `N`, splitting off the first coordinate with
  `measurePreserving_piFinSuccAbove`);
* `tensorHB` : the resulting Hilbert basis of `Lp ℝ 2 (Qm μ N)`.

The remaining sections build the symmetrized occupation functions `Eocc`, prove that they form a
Hilbert basis `occHB` of the symmetric subspace, prove the energy identity
`∑_k (∑_i λ_{k i}) ⟨Ψ, T_k⟩² = ∫ ∑_i |∇_iΨ|² dμ^N` for `Ψ ∈ H¹` (smooth case by slicing, general
case by smooth approximation), regroup it over occupation fibres, and conclude with
`DGPS.Lipschitz.occupation_basis_and_spectral_tail` (Parseval, energy identity, tail bound).
-/

open MeasureTheory

namespace DGPS.Lipschitz.SymmetricOccupation

section Defs

variable {α : Type}

/-- The tensor product `ω ↦ ∏ i, e (j i) (ω i)` of the basis functions indexed by
`j : Fin N → ℕ`. -/
def Tn (e : ℕ → α → ℝ) {N : ℕ} (j : Fin N → ℕ) (ω : Fin N → α) : ℝ :=
  ∏ i, e (j i) (ω i)

lemma Tn_apply (e : ℕ → α → ℝ) {N : ℕ} (j : Fin N → ℕ) (ω : Fin N → α) :
    Tn e j ω = ∏ i, e (j i) (ω i) := rfl

lemma Tn_cons (e : ℕ → α → ℝ) {n : ℕ} (a : ℕ) (j : Fin n → ℕ) (x : α) (y : Fin n → α) :
    Tn e (Fin.cons a j : Fin (n + 1) → ℕ) (Fin.cons x y : Fin (n + 1) → α) = e a x * Tn e j y := by
  simp [Tn, Fin.prod_univ_succ]

end Defs

section Tensor

variable {α : Type} [MeasurableSpace α]

/-- The `N`-fold product measure on `Fin N → α`. -/
noncomputable abbrev Qm (μ : Measure α) (N : ℕ) : Measure (Fin N → α) :=
  Measure.pi (fun _ : Fin N => μ)

variable (μ : Measure α) [IsProbabilityMeasure μ] (e : ℕ → α → ℝ)

/-! ### Membership in `L²` -/

/-- Every tensor product of basis functions lies in `L²(Qm μ N)`. -/
theorem tensor_memLp (he_mem : ∀ j, MemLp (e j) 2 μ) (N : ℕ) (j : Fin N → ℕ) :
    MemLp (Tn e j) 2 (Qm μ N) := by
  have hmeas : AEStronglyMeasurable (Tn e j) (Qm μ N) := by
    unfold Tn
    refine Finset.aestronglyMeasurable_fun_prod _ (fun i _ => ?_)
    exact (he_mem (j i)).aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving
  rw [memLp_two_iff_integrable_sq hmeas]
  have hsq : (fun ω : Fin N → α => Tn e j ω ^ 2) =
      fun ω : Fin N → α => ∏ i, (e (j i) (ω i)) ^ 2 := by
    funext ω
    simp [Tn, Finset.prod_pow]
  rw [hsq]
  exact Integrable.fintype_prod (f := fun i (x : α) => (e (j i) x) ^ 2)
    (fun i => (he_mem (j i)).integrable_sq)

/-! ### Orthonormality -/

/-- The tensor products are orthonormal in `L²(Qm μ N)`. -/
theorem tensor_orthonormal
    (he_orth : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0)
    (N : ℕ) (j j' : Fin N → ℕ) :
    ∫ ω, Tn e j ω * Tn e j' ω ∂(Qm μ N) = if j = j' then 1 else 0 := by
  have h1 : ∀ ω : Fin N → α, Tn e j ω * Tn e j' ω = ∏ i, (e (j i) (ω i) * e (j' i) (ω i)) := by
    intro ω
    simp only [Tn, Finset.prod_mul_distrib]
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
    ∀ f : (Fin N → α) → ℝ, MemLp f 2 (Qm μ N) →
      (∀ j : Fin N → ℕ, ∫ ω, f ω * Tn e j ω ∂(Qm μ N) = 0) → f =ᵐ[Qm μ N] 0 := by
  induction N with
  | zero =>
    intro f _ h
    have hE1 : ∀ (j : Fin 0 → ℕ) (ω : Fin 0 → α), Tn e j ω = 1 := by
      intro j ω
      simp [Tn]
    have hc : ∀ ω : Fin 0 → α, ω = (fun i => i.elim0) := fun ω => funext fun i => i.elim0
    have h0 := h (fun i => i.elim0)
    have hfz : f (fun i => i.elim0) = 0 := by
      have hconst : ∀ ω : Fin 0 → α,
          f ω * Tn e (fun i => i.elim0) ω = f (fun i => i.elim0) := by
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
        (Qm μ (n + 1)) (μ.prod (Qm μ n)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
    have hF : MemLp (f ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm) 2
        (μ.prod (Qm μ n)) := hf.comp_measurePreserving hmp.symm
    have hE_norm : ∀ j : Fin n → ℕ, ∫ y, Tn e j y * Tn e j y ∂(Qm μ n) = 1 := by
      intro j
      rw [tensor_orthonormal μ e he_orth n j j]
      simp
    have key := step_complete μ e (fun j : Fin n → ℕ => Tn e j) he_mem he_complete
      (tensor_memLp μ e he_mem n) hE_norm (ih)
      (f ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm) hF ?_
    · have hae := hmp.quasiMeasurePreserving.ae key
      filter_upwards [hae] with ω hω
      simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply, Pi.zero_apply] at hω
      exact hω
    · intro a j
      have h1 := horth (Fin.cons a j : Fin (n + 1) → ℕ)
      rw [← hmp.symm.integral_comp'
        (fun ω => f ω * Tn e (Fin.cons a j : Fin (n + 1) → ℕ) ω)] at h1
      rw [← h1]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      obtain ⟨x, y⟩ := z
      simp only [Function.comp_apply, piFinSuccAbove_zero_symm, Tn_cons]

/-- **Completeness.**  If `e` is an orthonormal, complete family in `L²(μ)`, then the only
`L²(Qm μ N)` function orthogonal to every tensor `Tn e j` is `0` a.e. -/
theorem tensor_complete (he_mem : ∀ j, MemLp (e j) 2 μ)
    (he_orth : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0)
    (he_complete : ∀ f : α → ℝ, MemLp f 2 μ → (∀ j, ∫ x, f x * e j x ∂μ = 0) → f =ᵐ[μ] 0)
    (N : ℕ) (f : (Fin N → α) → ℝ) (hf : MemLp f 2 (Qm μ N))
    (horth : ∀ j : Fin N → ℕ, ∫ ω, f ω * Tn e j ω ∂(Qm μ N) = 0) :
    f =ᵐ[Qm μ N] 0 :=
  tensor_complete_aux μ e he_mem he_orth he_complete N f hf horth

/-! ### The tensor Hilbert basis -/

section HilbertBasis

/-- The `L²(Qm μ N)` class of the tensor `Tn e j`. -/
noncomputable def tensorLp (he_mem : ∀ j, MemLp (e j) 2 μ) (N : ℕ) (j : Fin N → ℕ) :
    Lp ℝ 2 (Qm μ N) :=
  (tensor_memLp μ e he_mem N j).toLp (Tn e j)

lemma tensorLp_ae (he_mem : ∀ j, MemLp (e j) 2 μ) (N : ℕ) (j : Fin N → ℕ) :
    (tensorLp μ e he_mem N j : (Fin N → α) → ℝ) =ᵐ[Qm μ N] Tn e j :=
  (tensor_memLp μ e he_mem N j).coeFn_toLp

/-- The classes `tensorLp` form an orthonormal family in `L²(Qm μ N)`. -/
theorem tensorLp_orthonormal (he_mem : ∀ j, MemLp (e j) 2 μ)
    (he_orth : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0) (N : ℕ) :
    Orthonormal ℝ (tensorLp μ e he_mem N) := by
  rw [orthonormal_iff_ite]
  intro j j'
  rw [L2.inner_def]
  have hae : ∀ᵐ ω ∂(Qm μ N), inner ℝ (tensorLp μ e he_mem N j ω) (tensorLp μ e he_mem N j' ω) =
      Tn e j ω * Tn e j' ω := by
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
  have hf' : ∀ j : Fin N → ℕ, ∫ ω, f ω * Tn e j ω ∂(Qm μ N) = 0 := by
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

/-- **The tensor Hilbert basis.**  The functions `Tn e j`, `j : Fin N → ℕ`, form a Hilbert basis of
`L²(Qm μ N)`. -/
noncomputable def tensorHB (he_mem : ∀ j, MemLp (e j) 2 μ)
    (he_orth : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0)
    (he_complete : ∀ f : α → ℝ, MemLp f 2 μ → (∀ j, ∫ x, f x * e j x ∂μ = 0) → f =ᵐ[μ] 0)
    (N : ℕ) : HilbertBasis (Fin N → ℕ) ℝ (Lp ℝ 2 (Qm μ N)) :=
  HilbertBasis.mkOfOrthogonalEqBot (tensorLp_orthonormal μ e he_mem he_orth N)
    (tensorLp_orthogonal_eq_bot μ e he_mem he_orth he_complete N)

theorem tensorHB_coe (he_mem : ∀ j, MemLp (e j) 2 μ)
    (he_orth : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0)
    (he_complete : ∀ f : α → ℝ, MemLp f 2 μ → (∀ j, ∫ x, f x * e j x ∂μ = 0) → f =ᵐ[μ] 0)
    (N : ℕ) : ⇑(tensorHB μ e he_mem he_orth he_complete N) = tensorLp μ e he_mem N :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- The `j`-th vector of `tensorHB` is (a.e.) the function `Tn e j`. -/
theorem tensorHB_apply (he_mem : ∀ j, MemLp (e j) 2 μ)
    (he_orth : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0)
    (he_complete : ∀ f : α → ℝ, MemLp f 2 μ → (∀ j, ∫ x, f x * e j x ∂μ = 0) → f =ᵐ[μ] 0)
    (N : ℕ) (j : Fin N → ℕ) :
    (tensorHB μ e he_mem he_orth he_complete N j : (Fin N → α) → ℝ) =ᵐ[Qm μ N] Tn e j := by
  rw [tensorHB_coe]
  exact tensorLp_ae μ e he_mem N j

end HilbertBasis

end Tensor

section Comb

open Finset

variable {n r : ℕ}

/-- The word `lab` placed along the embedding `ι`, and `0` elsewhere. -/
noncomputable def kOf (lab : Fin r → ℕ) (ι : Fin r ↪ Fin n) : Fin n → ℕ :=
  Function.extend ι lab 0

theorem kOf_apply (lab : Fin r → ℕ) (ι : Fin r ↪ Fin n) (l : Fin r) :
    kOf lab ι (ι l) = lab l :=
  ι.injective.extend_apply lab 0 l

theorem kOf_of_notMem (lab : Fin r → ℕ) (ι : Fin r ↪ Fin n) {i : Fin n}
    (h : ∀ l, ι l ≠ i) : kOf lab ι i = 0 := by
  unfold kOf
  rw [Function.extend_apply' _ _ _ (by rintro ⟨a, ha⟩; exact h a ha)]
  rfl

theorem kOf_ne_zero_iff (lab : Fin r → ℕ) (hlab : ∀ l, lab l ≠ 0) (ι : Fin r ↪ Fin n)
    (i : Fin n) : kOf lab ι i ≠ 0 ↔ ∃ l, ι l = i := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    exact h (kOf_of_notMem lab ι h')
  · rintro ⟨l, rfl⟩
    rw [kOf_apply]
    exact hlab l

theorem prod_kOf {β : Type*} (φ : ℕ → β → ℝ) (h0 : ∀ x, φ 0 x = 1) (lab : Fin r → ℕ)
    (ι : Fin r ↪ Fin n) (x : Fin n → β) :
    ∏ i, φ (kOf lab ι i) (x i) = ∏ l, φ (lab l) (x (ι l)) := by
  have h1 : ∏ i ∈ univ.image ι, φ (kOf lab ι i) (x i) = ∏ i, φ (kOf lab ι i) (x i) := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    rw [kOf_of_notMem lab ι (fun l hl => hi (Finset.mem_image.2 ⟨l, Finset.mem_univ _, hl⟩)), h0]
  rw [← h1, Finset.prod_image (fun a _ b _ h => ι.injective h)]
  refine Finset.prod_congr rfl (fun l _ => ?_)
  rw [kOf_apply]

theorem kOf_eq_iff (lab : Fin r → ℕ) (hlab : ∀ l, lab l ≠ 0) (ι : Fin r ↪ Fin n)
    (k : Fin n → ℕ) :
    kOf lab ι = k ↔ (∀ l, k (ι l) = lab l) ∧ ∀ i, k i ≠ 0 → ∃ l, ι l = i := by
  constructor
  · rintro rfl
    exact ⟨fun l => kOf_apply lab ι l, fun i hi => (kOf_ne_zero_iff lab hlab ι i).1 hi⟩
  · rintro ⟨h1, h2⟩
    funext i
    by_cases hi : ∃ l, ι l = i
    · obtain ⟨l, rfl⟩ := hi
      rw [kOf_apply, h1]
    · push Not at hi
      rw [kOf_of_notMem lab ι hi]
      by_contra hne
      obtain ⟨l, hl⟩ := h2 i (Ne.symm hne)
      exact hi l hl

/-- Fibre cardinality of `kOf` over a nonzero value. -/
theorem card_fiber_kOf (lab : Fin r → ℕ) (hlab : ∀ l, lab l ≠ 0) (ι : Fin r ↪ Fin n)
    {j : ℕ} (hj : j ≠ 0) :
    Fintype.card {i : Fin n // kOf lab ι i = j} = Fintype.card {l : Fin r // lab l = j} := by
  symm
  refine Fintype.card_of_bijective (f := fun l => ⟨ι l.1, by rw [kOf_apply]; exact l.2⟩) ⟨?_, ?_⟩
  · intro a b h
    apply Subtype.ext
    exact ι.injective (congrArg Subtype.val h)
  · rintro ⟨i, hi⟩
    have : kOf lab ι i ≠ 0 := by rw [hi]; exact hj
    obtain ⟨l, rfl⟩ := (kOf_ne_zero_iff lab hlab ι _).1 this
    exact ⟨⟨l, by rw [← hi, kOf_apply]⟩, rfl⟩

end Comb

section Comb2

open Finset

variable {n r : ℕ}

/-- `∏ α_j !` for the occupation vector of the word `lab`. -/
noncomputable def occFact (lab : Fin r → ℕ) : ℕ :=
  ∏ j ∈ Finset.univ.image lab, (Fintype.card {l : Fin r // lab l = j}).factorial

theorem occFact_pos (lab : Fin r → ℕ) : 0 < occFact lab :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem kOf_embed_perm (lab : Fin r → ℕ) (hlab : ∀ l, lab l ≠ 0) (ι : Fin r ↪ Fin n)
    (σ : Equiv.Perm (Fin n)) :
    kOf lab ι ∘ σ = kOf lab (ι.trans σ.symm.toEmbedding) := by
  symm
  rw [kOf_eq_iff lab hlab]
  refine ⟨fun l => ?_, fun i hi => ?_⟩
  · simp [kOf_apply]
  · obtain ⟨l, hl⟩ := (kOf_ne_zero_iff lab hlab ι _).1 hi
    refine ⟨l, ?_⟩
    simp [hl]

theorem kOf_embed_equiv (lab : Fin r → ℕ) (hlab : ∀ l, lab l ≠ 0) (ι : Fin r ↪ Fin n)
    (σ : Equiv.Perm (Fin r)) (hσ : lab ∘ σ = lab) :
    kOf lab (σ.toEmbedding.trans ι) = kOf lab ι := by
  rw [kOf_eq_iff lab hlab]
  refine ⟨fun l => ?_, fun i hi => ?_⟩
  · simp [kOf_apply, ← congrFun hσ l]
  · obtain ⟨l, hl⟩ := (kOf_ne_zero_iff lab hlab ι _).1 hi
    exact ⟨σ.symm l, by simp [hl]⟩

/-- The fibre of `kOf lab` through `kOf lab ι` has `∏ α_j!` elements. -/
theorem card_fiber_embed (lab : Fin r → ℕ) (hlab : ∀ l, lab l ≠ 0) (ι : Fin r ↪ Fin n) :
    Fintype.card {ι' : Fin r ↪ Fin n // kOf lab ι' = kOf lab ι} = occFact lab := by
  classical
  rw [occFact, ← DomMulAct.stabilizer_card' lab]
  symm
  refine Fintype.card_of_bijective
    (f := fun σ => (⟨σ.1.toEmbedding.trans ι, kOf_embed_equiv lab hlab ι σ.1 σ.2⟩ :
      {ι' : Fin r ↪ Fin n // kOf lab ι' = kOf lab ι})) ⟨?_, ?_⟩
  · intro a b h
    apply Subtype.ext
    apply Equiv.ext
    intro l
    have := congrArg (fun x : {ι' : Fin r ↪ Fin n // kOf lab ι' = kOf lab ι} => x.1 l) h
    exact ι.injective this
  · rintro ⟨ι', hι'⟩
    have hmem : ∀ l, ∃ l', ι l' = ι' l := by
      intro l
      refine (kOf_ne_zero_iff lab hlab ι _).1 ?_
      rw [← hι', kOf_apply]
      exact hlab l
    choose g hg using hmem
    have ginj : Function.Injective g := by
      intro a b h
      apply ι'.injective
      rw [← hg a, ← hg b, h]
    let σ : Equiv.Perm (Fin r) := Equiv.ofBijective g (Finite.injective_iff_bijective.1 ginj)
    have hσ : lab ∘ σ = lab := by
      funext l
      have h1 : kOf lab ι' (ι' l) = lab l := kOf_apply lab ι' l
      have h2 : kOf lab ι (ι (g l)) = lab (g l) := kOf_apply lab ι (g l)
      simp only [Function.comp_apply]
      show lab (g l) = lab l
      rw [← h2, hg, ← hι', h1]
    refine ⟨⟨σ, hσ⟩, ?_⟩
    apply Subtype.ext
    apply Function.Embedding.ext
    intro l
    exact hg l

noncomputable def Kset (n : ℕ) (lab : Fin r → ℕ) : Finset (Fin n → ℕ) :=
  open scoped Classical in Finset.univ.image (kOf lab : (Fin r ↪ Fin n) → Fin n → ℕ)

theorem mem_Kset_iff (lab : Fin r → ℕ) (k : Fin n → ℕ) :
    k ∈ Kset n lab ↔ ∃ ι : Fin r ↪ Fin n, kOf lab ι = k := by
  classical
  simp [Kset]

theorem card_Kset_mul (lab : Fin r → ℕ) (hlab : ∀ l, lab l ≠ 0) :
    (Kset n lab).card * occFact lab = n.descFactorial r := by
  classical
  have h1 : Fintype.card (Fin r ↪ Fin n) = n.descFactorial r := by
    rw [Fintype.card_embedding_eq]; simp
  rw [← h1, ← Finset.card_univ,
    Finset.card_eq_sum_card_image (kOf lab : (Fin r ↪ Fin n) → Fin n → ℕ) Finset.univ]
  have : Kset n lab = Finset.univ.image (kOf lab : (Fin r ↪ Fin n) → Fin n → ℕ) := by
    simp [Kset]
  rw [← this, Finset.card_eq_sum_ones, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨ι, hι⟩ := (mem_Kset_iff lab k).1 hk
  rw [one_mul, ← card_fiber_embed lab hlab ι, ← hι, Fintype.card_subtype]

/-- Membership in `Kset` is a statement about the occupation counts. -/
theorem mem_Kset_iff_counts (lab : Fin r → ℕ) (hlab : ∀ l, lab l ≠ 0) (k : Fin n → ℕ) :
    k ∈ Kset n lab ↔ ∀ j, j ≠ 0 →
      Fintype.card {i : Fin n // k i = j} = Fintype.card {l : Fin r // lab l = j} := by
  classical
  rw [mem_Kset_iff]
  constructor
  · rintro ⟨ι, rfl⟩ j hj
    exact card_fiber_kOf lab hlab ι hj
  · intro h
    let P := {i : Fin n // k i ≠ 0}
    have hfib : ∀ j, Nonempty ({l : Fin r // lab l = j} ≃ {p : P // k p.1 = j}) := by
      intro j
      by_cases hj : j = 0
      · subst hj
        have : IsEmpty {l : Fin r // lab l = 0} := ⟨fun l => hlab l.1 l.2⟩
        have : IsEmpty {p : P // k p.1 = 0} := ⟨fun p => p.1.2 p.2⟩
        exact ⟨Equiv.equivOfIsEmpty _ _⟩
      · refine ⟨Fintype.equivOfCardEq ?_⟩
        rw [← h j hj]
        refine (Fintype.card_congr ?_).symm
        exact
          { toFun := fun p => ⟨p.1.1, p.2⟩
            invFun := fun i => ⟨⟨i.1, by rw [i.2]; exact hj⟩, i.2⟩
            left_inv := fun p => rfl
            right_inv := fun i => rfl }
    let e := fun j => (hfib j).some
    let ψ : Fin r ≃ P := Equiv.ofFiberEquiv (f := lab) (g := fun p : P => k p.1) e
    have hψ : ∀ l, k (ψ l).1 = lab l := fun l => Equiv.ofFiberEquiv_map e l
    refine ⟨⟨fun l => (ψ l).1, fun a b hab => ψ.injective (Subtype.ext hab)⟩, ?_⟩
    rw [kOf_eq_iff lab hlab]
    refine ⟨fun l => hψ l, fun i hi => ⟨ψ.symm ⟨i, hi⟩, ?_⟩⟩
    show ((ψ (ψ.symm ⟨i, hi⟩)) : Fin n) = i
    rw [Equiv.apply_symm_apply]

theorem comp_perm_mem_Kset (lab : Fin r → ℕ) (hlab : ∀ l, lab l ≠ 0) {k : Fin n → ℕ}
    (hk : k ∈ Kset n lab) (σ : Equiv.Perm (Fin n)) : k ∘ σ ∈ Kset n lab := by
  obtain ⟨ι, rfl⟩ := (mem_Kset_iff lab k).1 hk
  rw [kOf_embed_perm lab hlab]
  exact (mem_Kset_iff lab _).2 ⟨_, rfl⟩

theorem exists_perm_of_mem_Kset (lab : Fin r → ℕ) (hlab : ∀ l, lab l ≠ 0) {k k' : Fin n → ℕ}
    (hk : k ∈ Kset n lab) (hk' : k' ∈ Kset n lab) : ∃ σ : Equiv.Perm (Fin n), k' = k ∘ σ := by
  obtain ⟨ι, rfl⟩ := (mem_Kset_iff lab k).1 hk
  obtain ⟨ι', rfl⟩ := (mem_Kset_iff lab k').1 hk'
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair (f := ι) (g := ι') ι.injective ι'.injective
  refine ⟨τ.symm, ?_⟩
  rw [kOf_embed_perm lab hlab]
  congr 1
  apply Function.Embedding.ext
  intro a
  simp [hτ]

/-- The occupation vector of `k : Fin n → ℕ`: how often each nonzero value occurs. -/
noncomputable def occK (k : Fin n → ℕ) : ℕ →₀ ℕ :=
  Multiset.toFinsupp ((Finset.univ.val.map k).filter (· ≠ 0))

theorem occK_apply (k : Fin n → ℕ) (j : ℕ) :
    occK k j = if j = 0 then 0 else Fintype.card {i : Fin n // k i = j} := by
  classical
  unfold occK
  rw [Multiset.toFinsupp_apply, Multiset.count_filter]
  by_cases hj : j = 0
  · simp [hj]
  · simp only [hj, ne_eq, not_false_eq_true, ite_true, ite_false]
    rw [Multiset.count_map, Fintype.card_subtype]
    simp only [Finset.card_def, Finset.filter_val]
    congr 2
    funext i
    exact propext eq_comm

theorem occK_zero (k : Fin n → ℕ) : occK k 0 = 0 := by simp [occK_apply]

theorem occK_sum_le (k : Fin n → ℕ) : (occK k).sum (fun _ m => m) ≤ n := by
  classical
  have h := Finsupp.card_toMultiset (occK k)
  have h' : Finsupp.toMultiset (occK k) = (Finset.univ.val.map k).filter (· ≠ 0) :=
    Multiset.toFinsupp_toMultiset _
  rw [h'] at h
  have h2 : (occK k).sum (fun _ m => m) = (occK k).sum (fun _ => id) := rfl
  rw [h2, ← h]
  calc _ ≤ Multiset.card (Finset.univ.val.map k) := Multiset.card_le_card (Multiset.filter_le _ _)
    _ = n := by simp

/-- Occupation vectors for `n` particles: finitely supported on the labels `j ≥ 1`
(`a 0 = 0`) with total mass `r = ∑ a j ≤ n`. -/
def Occ (n : ℕ) : Type := {a : ℕ →₀ ℕ // a 0 = 0 ∧ (a.sum fun _ m => m) ≤ n}

/-- The occupation vector of a configuration `k`. -/
noncomputable def occOfK (k : Fin n → ℕ) : Occ n := ⟨occK k, occK_zero k, occK_sum_le k⟩

theorem exists_lab (a : Occ n) :
    ∃ (r : ℕ) (lab : Fin r → ℕ), r ≤ n ∧ (∀ l, lab l ≠ 0) ∧
      ∀ j, j ≠ 0 → Fintype.card {l : Fin r // lab l = j} = a.1 j := by
  classical
  set L : List ℕ := (Finsupp.toMultiset a.1).toList with hL
  have hLm : (L : Multiset ℕ) = Finsupp.toMultiset a.1 := Multiset.coe_toList _
  refine ⟨L.length, L.get, ?_, ?_, ?_⟩
  · have := Finsupp.card_toMultiset a.1
    have h2 : (L.length : ℕ) = Multiset.card (Finsupp.toMultiset a.1) := by
      rw [← hLm]; simp
    rw [h2, this]
    exact a.2.2
  · intro l h0
    have hmem : L.get l ∈ L := List.get_mem _ _
    rw [h0, ← Multiset.mem_coe, hLm, Finsupp.mem_toMultiset] at hmem
    exact (Finsupp.mem_support_iff.1 hmem) a.2.1
  · intro j hj
    have hcount : L.count j = a.1 j := by
      rw [← Multiset.coe_count, hLm, Finsupp.count_toMultiset]
    rw [← hcount, Fintype.card_subtype]
    have hmap : (Finset.univ.val.map L.get : Multiset ℕ) = (L : Multiset ℕ) := by
      rw [Fin.univ_val_map, List.ofFn_get]
    have h3 : Multiset.count j (Finset.univ.val.map L.get) = L.count j := by
      rw [hmap, Multiset.coe_count]
    rw [← h3, Multiset.count_map, Finset.card_def, Finset.filter_val]
    congr 2
    funext l
    exact propext eq_comm

/-- The configurations `k : Fin n → ℕ` with occupation vector `a`. -/
noncomputable def Kocc (n : ℕ) (a : Occ n) : Finset (Fin n → ℕ) :=
  open scoped Classical in
  (Fintype.piFinset fun _ : Fin n => insert 0 a.1.support).filter (fun k => occK k = a.1)

theorem mem_Kocc (a : Occ n) (k : Fin n → ℕ) : k ∈ Kocc n a ↔ occK k = a.1 := by
  classical
  unfold Kocc
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  by_cases hi : k i = 0
  · simp [hi]
  · refine Finset.mem_insert_of_mem (Finsupp.mem_support_iff.2 ?_)
    rw [← h, occK_apply]
    simp only [hi, ↓reduceIte]
    have : Nonempty {i' : Fin n // k i' = k i} := ⟨⟨i, rfl⟩⟩
    exact Fintype.card_ne_zero

theorem Kset_eq_Kocc (a : Occ n) (lab : Fin r → ℕ) (hlab : ∀ l, lab l ≠ 0)
    (hcnt : ∀ j, j ≠ 0 → Fintype.card {l : Fin r // lab l = j} = a.1 j) :
    Kset n lab = Kocc n a := by
  ext k
  rw [mem_Kset_iff_counts lab hlab, mem_Kocc]
  constructor
  · intro h
    ext j
    by_cases hj : j = 0
    · rw [hj, occK_zero, a.2.1]
    · rw [occK_apply]; simp only [hj, ↓reduceIte]; rw [h j hj, hcnt j hj]
  · intro h j hj
    rw [hcnt j hj, ← h, occK_apply]; simp only [hj, ↓reduceIte]

theorem occOfK_mem_Kocc (k : Fin n → ℕ) : k ∈ Kocc n (occOfK k) :=
  (mem_Kocc _ _).2 rfl

theorem Kocc_eq_of_mem {a b : Occ n} {k : Fin n → ℕ} (ha : k ∈ Kocc n a) (hb : k ∈ Kocc n b) :
    a = b := by
  rw [mem_Kocc] at ha hb
  exact Subtype.ext (ha.symm.trans hb)

end Comb2

section Func

open Finset

variable {α : Type} {n r : ℕ}

/-- The occupation function of the word `lab` (ordered distinct labels), normalised by
`√(N^{\underline r} ∏ α_j!)`. -/
noncomputable def Eocc (e : ℕ → α → ℝ) (N : ℕ) (lab : Fin r → ℕ) (ω : Fin N → α) : ℝ :=
  (Real.sqrt ((N.descFactorial r * occFact lab : ℕ) : ℝ))⁻¹ *
    ∑ ι : Fin r ↪ Fin N, ∏ l, e (lab l) (ω (ι l))

theorem sum_embed_eq (e : ℕ → α → ℝ) (h0 : ∀ x, e 0 x = 1) (lab : Fin r → ℕ)
    (hlab : ∀ l, lab l ≠ 0) (ω : Fin n → α) :
    ∑ ι : Fin r ↪ Fin n, ∏ l, e (lab l) (ω (ι l)) =
      (occFact lab : ℝ) * ∑ k ∈ Kset n lab, Tn e k ω := by
  classical
  have h1 : ∀ ι : Fin r ↪ Fin n, ∏ l, e (lab l) (ω (ι l)) = Tn e (kOf lab ι) ω := by
    intro ι
    rw [Tn_apply, prod_kOf e (fun x => h0 x) lab ι]
  simp_rw [h1]
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin r ↪ Fin n)))
    (t := Kset n lab) (g := kOf lab) (fun ι _ => (mem_Kset_iff lab _).2 ⟨ι, rfl⟩), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨ι, hι⟩ := (mem_Kset_iff lab k).1 hk
  have : ∀ ι' ∈ (Finset.univ.filter fun ι' : Fin r ↪ Fin n => kOf lab ι' = k),
      Tn e (kOf lab ι') ω = Tn e k ω := by
    intro ι' hι'
    rw [(Finset.mem_filter.1 hι').2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [← card_fiber_embed lab hlab ι, ← hι, Fintype.card_subtype]

theorem Eocc_eq (e : ℕ → α → ℝ) (h0 : ∀ x, e 0 x = 1) (lab : Fin r → ℕ)
    (hlab : ∀ l, lab l ≠ 0) (ω : Fin n → α) :
    Eocc e n lab ω = (Real.sqrt (Kset n lab).card)⁻¹ * ∑ k ∈ Kset n lab, Tn e k ω := by
  unfold Eocc
  rw [sum_embed_eq e h0 lab hlab ω, ← card_Kset_mul lab hlab]
  have hp : (0 : ℝ) < occFact lab := by exact_mod_cast occFact_pos lab
  by_cases hK : (Kset n lab).card = 0
  · have : Kset n lab = ∅ := Finset.card_eq_zero.1 hK
    simp [this]
  · have hK' : (0 : ℝ) < (Kset n lab).card := by exact_mod_cast Nat.pos_of_ne_zero hK
    push_cast
    rw [show ((Kset n lab).card : ℝ) * occFact lab * occFact lab =
        (Real.sqrt (Kset n lab).card * occFact lab) ^ 2 by
      rw [mul_pow, Real.sq_sqrt hK'.le]; ring]
    rw [Real.sqrt_sq (by positivity)]
    field_simp

end Func

section Hilb

open Finset

variable {α : Type} [MeasurableSpace α]

/-- An orthonormal basis `ε` of `L²(μ)` with `ε 0 ≡ 1` pointwise. -/
structure CompleteONB (μ : Measure α) (ε : ℕ → α → ℝ) : Prop where
  mem : ∀ j, MemLp (ε j) 2 μ
  orth : ∀ i j, ∫ x, ε i x * ε j x ∂μ = if i = j then 1 else 0
  complete : ∀ f : α → ℝ, MemLp f 2 μ → (∀ j, ∫ x, f x * ε j x ∂μ = 0) → f =ᵐ[μ] 0
  zero : ∀ x, ε 0 x = 1

noncomputable instance (N : ℕ) : DecidableEq (Occ N) := Classical.decEq _

variable (μ : Measure α) [IsProbabilityMeasure μ] (ε : ℕ → α → ℝ)

/-- The tensor Hilbert basis attached to a `CompleteONB`. -/
noncomputable abbrev tB (h : CompleteONB μ ε) (N : ℕ) : HilbertBasis (Fin N → ℕ) ℝ (Lp ℝ 2 (Qm μ N)) :=
  tensorHB μ ε h.mem h.orth h.complete N

theorem Kocc_card_pos {N : ℕ} (a : Occ N) : 0 < (Kocc N a).card := by
  obtain ⟨r, lab, hr, hlab, hcnt⟩ := exists_lab a
  rw [← Kset_eq_Kocc a lab hlab hcnt]
  have h := card_Kset_mul (n := N) lab hlab
  have hpos : 0 < N.descFactorial r := Nat.descFactorial_pos.2 hr
  rw [← h] at hpos
  exact Nat.pos_of_mul_pos_right hpos

/-- The `L²` class of the occupation function `E_a`. -/
noncomputable def occLp (h : CompleteONB μ ε) (N : ℕ) (a : Occ N) : Lp ℝ 2 (Qm μ N) :=
  (Real.sqrt (Kocc N a).card)⁻¹ • ∑ k ∈ Kocc N a, tB μ ε h N k

theorem inner_occLp (h : CompleteONB μ ε) (N : ℕ) (a b : Occ N) :
    inner ℝ (occLp μ ε h N a) (occLp μ ε h N b) = if a = b then 1 else 0 := by
  classical
  have hon := (tB μ ε h N).orthonormal
  rw [orthonormal_iff_ite] at hon
  unfold occLp
  rw [inner_smul_left, inner_smul_right, sum_inner]
  simp_rw [inner_sum, hon]
  simp only [Finset.sum_ite_eq, conj_trivial]
  have hA := Kocc_card_pos (N := N) a
  have hB := Kocc_card_pos (N := N) b
  by_cases hab : a = b
  · subst hab
    simp only [↓reduceIte]
    have : ∑ k ∈ Kocc N a, (if k ∈ Kocc N a then (1 : ℝ) else 0) = (Kocc N a).card := by
      simp
    rw [this]
    have hs : (0 : ℝ) < Real.sqrt (Kocc N a).card := Real.sqrt_pos.2 (by exact_mod_cast hA)
    field_simp
    rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  · simp only [hab, ↓reduceIte]
    have : ∑ k ∈ Kocc N a, (if k ∈ Kocc N b then (1 : ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have : k ∉ Kocc N b := fun hkb => hab (Kocc_eq_of_mem hk hkb)
      simp [this]
    rw [this]
    simp

theorem occLp_orthonormal (h : CompleteONB μ ε) (N : ℕ) : Orthonormal ℝ (occLp μ ε h N) := by
  rw [orthonormal_iff_ite]
  exact inner_occLp μ ε h N

/-! ### Permutation action and the symmetric subspace -/

theorem comp_perm_mem_Kocc {N : ℕ} (a : Occ N) {k : Fin N → ℕ} (hk : k ∈ Kocc N a)
    (σ : Equiv.Perm (Fin N)) : k ∘ σ ∈ Kocc N a := by
  obtain ⟨r, lab, hr, hlab, hcnt⟩ := exists_lab a
  rw [← Kset_eq_Kocc a lab hlab hcnt] at hk ⊢
  exact comp_perm_mem_Kset lab hlab hk σ

theorem exists_perm_of_mem_Kocc {N : ℕ} (a : Occ N) {k k' : Fin N → ℕ} (hk : k ∈ Kocc N a)
    (hk' : k' ∈ Kocc N a) : ∃ σ : Equiv.Perm (Fin N), k' = k ∘ σ := by
  obtain ⟨r, lab, hr, hlab, hcnt⟩ := exists_lab a
  rw [← Kset_eq_Kocc a lab hlab hcnt] at hk hk'
  exact exists_perm_of_mem_Kset lab hlab hk hk'

theorem measurePreserving_permArg (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (fun ω : Fin N → α => ω ∘ σ) (Qm μ N) (Qm μ N) := by
  have hm : Measurable (fun ω : Fin N → α => ω ∘ σ) :=
    Measurable.of_eval fun i => measurable_pi_apply (σ i)
  refine ⟨hm, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : (fun ω : Fin N → α => ω ∘ σ) ⁻¹' (Set.univ.pi s) = Set.univ.pi fun k => s (σ.symm k) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Function.comp_apply]
    exact ⟨fun h k => by simpa using h (σ.symm k), fun h i => by simpa using h (σ i)⟩
  rw [this, Measure.pi_pi]
  exact σ.symm.prod_comp (fun i => μ (s i))

/-- The label-permutation `ω ↦ ω ∘ σ` acting on `L²(Qm μ N)`. -/
noncomputable def permLp (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    Lp ℝ 2 (Qm μ N) →ₗᵢ[ℝ] Lp ℝ 2 (Qm μ N) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun ω : Fin N → α => ω ∘ σ) (measurePreserving_permArg μ N σ)

theorem permLp_ae (N : ℕ) (σ : Equiv.Perm (Fin N)) (f : Lp ℝ 2 (Qm μ N)) :
    (permLp μ N σ f : (Fin N → α) → ℝ) =ᵐ[Qm μ N] fun ω => f (ω ∘ σ) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_permArg μ N σ)

theorem permLp_tB (h : CompleteONB μ ε) (N : ℕ) (σ : Equiv.Perm (Fin N)) (k : Fin N → ℕ) :
    permLp μ N σ (tB μ ε h N k) = tB μ ε h N (k ∘ σ.symm) := by
  refine Lp.ext ?_
  have h1 := permLp_ae μ N σ (tB μ ε h N k)
  have h2 := (measurePreserving_permArg μ N σ).quasiMeasurePreserving.ae_eq_comp
    (tensorHB_apply μ ε h.mem h.orth h.complete N k)
  have h3 := tensorHB_apply μ ε h.mem h.orth h.complete N (k ∘ σ.symm)
  filter_upwards [h1, h2, h3] with ω a b c
  rw [a, c]
  refine b.trans ?_
  show ∏ i, ε (k i) (ω (σ i)) = ∏ i, ε (k (σ.symm i)) (ω i)
  rw [← Equiv.prod_comp σ (fun i => ε (k (σ.symm i)) (ω i))]
  simp

/-- The closed subspace of permutation-symmetric elements of `L²(Qm μ N)`. -/
def symSub (N : ℕ) : Submodule ℝ (Lp ℝ 2 (Qm μ N)) where
  carrier := {f | ∀ σ : Equiv.Perm (Fin N), permLp μ N σ f = f}
  add_mem' := fun {f g} hf hg σ => by rw [map_add, hf σ, hg σ]
  zero_mem' := fun σ => map_zero _
  smul_mem' := fun c f hf σ => by rw [map_smul, hf σ]

theorem mem_symSub {N : ℕ} {f : Lp ℝ 2 (Qm μ N)} :
    f ∈ symSub μ N ↔ ∀ σ : Equiv.Perm (Fin N), permLp μ N σ f = f := Iff.rfl

theorem isClosed_symSub (N : ℕ) : IsClosed (symSub μ N : Set (Lp ℝ 2 (Qm μ N))) := by
  have : (symSub μ N : Set (Lp ℝ 2 (Qm μ N))) =
      ⋂ σ : Equiv.Perm (Fin N), {f | permLp μ N σ f = f} := by
    ext f
    simp [mem_symSub]
  rw [this]
  exact isClosed_iInter fun σ => isClosed_eq (permLp μ N σ).continuous continuous_id

theorem occLp_mem_symSub (h : CompleteONB μ ε) (N : ℕ) (a : Occ N) :
    occLp μ ε h N a ∈ symSub μ N := by
  classical
  intro σ
  unfold occLp
  rw [map_smul, map_sum]
  congr 1
  simp_rw [permLp_tB μ ε h N σ]
  refine Finset.sum_nbij' (fun k => k ∘ σ.symm) (fun k => k ∘ σ) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    exact comp_perm_mem_Kocc a hk σ.symm
  · intro k hk
    exact comp_perm_mem_Kocc a hk σ
  · intro k _
    funext i
    simp
  · intro k _
    funext i
    simp
  · intro k _
    rfl

theorem inner_symm_tB (h : CompleteONB μ ε) (N : ℕ) {f : Lp ℝ 2 (Qm μ N)} (hf : f ∈ symSub μ N)
    (k : Fin N → ℕ) (σ : Equiv.Perm (Fin N)) :
    inner ℝ f (tB μ ε h N (k ∘ σ)) = inner ℝ f (tB μ ε h N k) := by
  have h1 : tB μ ε h N (k ∘ σ) = permLp μ N σ.symm (tB μ ε h N k) := by
    rw [permLp_tB]
    simp
  rw [h1]
  conv_lhs => rw [← hf σ.symm]
  exact (permLp μ N σ.symm).inner_map_map _ _

theorem inner_symm_occLp (h : CompleteONB μ ε) (N : ℕ) {f : Lp ℝ 2 (Qm μ N)}
    (hf : f ∈ symSub μ N) (a : Occ N) {k : Fin N → ℕ} (hk : k ∈ Kocc N a) :
    inner ℝ f (occLp μ ε h N a) = Real.sqrt (Kocc N a).card * inner ℝ f (tB μ ε h N k) := by
  classical
  unfold occLp
  rw [inner_smul_right, inner_sum]
  have : ∀ k' ∈ Kocc N a, inner ℝ f (tB μ ε h N k') = inner ℝ f (tB μ ε h N k) := by
    intro k' hk'
    obtain ⟨σ, rfl⟩ := exists_perm_of_mem_Kocc a hk hk'
    exact inner_symm_tB μ ε h N hf k σ
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  have hA := Kocc_card_pos (N := N) a
  have hs : (0 : ℝ) < Real.sqrt (Kocc N a).card := Real.sqrt_pos.2 (by exact_mod_cast hA)
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg _)]

theorem occOfK_eq_iff {N : ℕ} (a : Occ N) (k : Fin N → ℕ) : occOfK k = a ↔ k ∈ Kocc N a := by
  rw [mem_Kocc]
  exact ⟨fun h' => by rw [← h']; rfl, fun h' => Subtype.ext h'⟩

/-- **Parseval for symmetric functions in the occupation basis.** -/
theorem hasSum_sq_occLp (h : CompleteONB μ ε) (N : ℕ) {f : Lp ℝ 2 (Qm μ N)}
    (hf : f ∈ symSub μ N) :
    HasSum (fun a : Occ N => (inner ℝ f (occLp μ ε h N a)) ^ 2) (‖f‖ ^ 2) := by
  classical
  have h1 := (tB μ ε h N).hasSum_inner_mul_inner f f
  have h1' : HasSum (fun k : Fin N → ℕ => (inner ℝ f (tB μ ε h N k)) ^ 2) (‖f‖ ^ 2) := by
    rw [← real_inner_self_eq_norm_sq]
    convert h1 using 2 with k
    rw [real_inner_comm (tB μ ε h N k) f, sq]
  have h2 := h1'.tsum_fiberwise (occOfK : (Fin N → ℕ) → Occ N)
  convert h2 using 1
  funext a
  have hset : (occOfK : (Fin N → ℕ) → Occ N) ⁻¹' {a} = (Kocc N a : Set (Fin N → ℕ)) := by
    ext k
    simp [occOfK_eq_iff]
  rw [hset]
  have hne : (Kocc N a).Nonempty := Finset.card_pos.1 (Kocc_card_pos a)
  obtain ⟨k0, hk0⟩ := hne
  rw [Finset.tsum_subtype' (Kocc N a) (fun k => (inner ℝ f (tB μ ε h N k)) ^ 2),
    inner_symm_occLp μ ε h N hf a hk0, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have : ∀ k ∈ Kocc N a, (inner ℝ f (tB μ ε h N k)) ^ 2 = (inner ℝ f (tB μ ε h N k0)) ^ 2 := by
    intro k hk
    obtain ⟨σ, rfl⟩ := exists_perm_of_mem_Kocc a hk0 hk
    rw [inner_symm_tB μ ε h N hf]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]

theorem occLp_orthonormal_symSub (h : CompleteONB μ ε) (N : ℕ) :
    Orthonormal ℝ (fun a : Occ N => (⟨occLp μ ε h N a, occLp_mem_symSub μ ε h N a⟩ : symSub μ N)) := by
  rw [orthonormal_iff_ite]
  intro a b
  rw [Submodule.coe_inner]
  exact inner_occLp μ ε h N a b

instance completeSpace_symSub (N : ℕ) : CompleteSpace (symSub μ N) :=
  (isClosed_symSub μ N).completeSpace_coe

/-- **The occupation basis of the symmetric subspace.** -/
noncomputable def occHB (h : CompleteONB μ ε) (N : ℕ) : HilbertBasis (Occ N) ℝ (symSub μ N) :=
  HilbertBasis.mkOfOrthogonalEqBot (occLp_orthonormal_symSub μ ε h N) (by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_orthogonal] at hx
    have h0 : ∀ a : Occ N, inner ℝ (x : Lp ℝ 2 (Qm μ N)) (occLp μ ε h N a) = 0 := by
      intro a
      have := hx ⟨occLp μ ε h N a, occLp_mem_symSub μ ε h N a⟩
        (Submodule.subset_span ⟨a, rfl⟩)
      rw [real_inner_comm, Submodule.coe_inner] at this
      exact this
    have h1 := hasSum_sq_occLp μ ε h N x.2
    simp_rw [h0] at h1
    have h2 : ‖(x : Lp ℝ 2 (Qm μ N))‖ ^ 2 = 0 := by
      have : HasSum (fun _ : Occ N => (0 : ℝ) ^ 2) 0 := by simp
      exact h1.unique this
    have h3 : ‖(x : Lp ℝ 2 (Qm μ N))‖ = 0 := by simpa using h2
    exact Subtype.ext (norm_eq_zero.1 h3))

theorem occHB_apply (h : CompleteONB μ ε) (N : ℕ) (a : Occ N) :
    ((occHB μ ε h N a : symSub μ N) : Lp ℝ 2 (Qm μ N)) = occLp μ ε h N a := by
  unfold occHB
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]

end Hilb

section LIP057B
open MeasureTheory
open scoped ENNReal

theorem pi_le_smul_pow_LIP057 {α : Type} [MeasurableSpace α] {ν₁ ν₂ : Measure α}
    [SigmaFinite ν₁] [SigmaFinite ν₂] {K : ℝ≥0∞} (h : ν₁ ≤ K • ν₂) :
    ∀ n : ℕ, Measure.pi (fun _ : Fin n => ν₁) ≤ K ^ n • Measure.pi (fun _ : Fin n => ν₂)
  | 0 => by
    rw [pow_zero, one_smul, Measure.pi_of_empty, Measure.pi_of_empty]
  | n + 1 => by
    have ih := pi_le_smul_pow_LIP057 h n
    have e₁ := ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν₁) 0).symm
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0)).map_eq
    have e₂ := ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν₂) 0).symm
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0)).map_eq
    rw [← e₁, ← e₂, pow_succ']
    have h2 : ν₁.prod (Measure.pi fun _ : Fin n => ν₁) ≤
        (K • ν₂).prod (K ^ n • Measure.pi fun _ : Fin n => ν₂) := Measure.prod_mono h ih
    rw [Measure.prod_smul_left, Measure.prod_smul_right] at h2
    calc _ ≤ Measure.map (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm
          ((K • K ^ n • ν₂.prod (Measure.pi fun _ : Fin n => ν₂))) :=
          Measure.map_mono h2 (MeasurableEquiv.measurable _)
      _ = _ := by
        rw [Measure.map_smul _ (MeasurableEquiv.measurable _).aemeasurable,
          Measure.map_smul _ (MeasurableEquiv.measurable _).aemeasurable, mul_smul]

section Slice

variable {α : Type} [MeasurableSpace α]

/-- The measurable equivalence `(p, x) ↦ insertNth i x p`. -/
def insEquiv (n : ℕ) (i : Fin (n + 1)) : ((Fin n → α) × α) ≃ᵐ (Fin (n + 1) → α) :=
  MeasurableEquiv.prodComm.trans (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) i).symm

theorem insEquiv_apply (n : ℕ) (i : Fin (n + 1)) (q : (Fin n → α) × α) :
    insEquiv n i q = Fin.insertNth i q.2 q.1 := rfl

theorem measurePreserving_insEquiv (ν : Measure α) [SigmaFinite ν] (n : ℕ) (i : Fin (n + 1)) :
    MeasurePreserving (insEquiv n i) ((Qm ν n).prod ν) (Qm ν (n + 1)) :=
  (Measure.measurePreserving_swap).trans
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) i).symm

theorem integrable_insertNth (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ) (i : Fin (n + 1))
    {F : (Fin (n + 1) → α) → ℝ} (hF : Integrable F (Qm ν (n + 1))) :
    Integrable (fun q : (Fin n → α) × α => F (Fin.insertNth i q.2 q.1)) ((Qm ν n).prod ν) :=
  ((measurePreserving_insEquiv ν n i).integrable_comp hF.aestronglyMeasurable).2 hF

theorem integral_insertNth (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ) (i : Fin (n + 1))
    (F : (Fin (n + 1) → α) → ℝ) :
    ∫ ω, F ω ∂Qm ν (n + 1) = ∫ q, F (Fin.insertNth i q.2 q.1) ∂((Qm ν n).prod ν) :=
  ((measurePreserving_insEquiv ν n i).integral_comp' (f := insEquiv n i) F).symm

theorem integral_insertNth_iter (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ) (i : Fin (n + 1))
    {F : (Fin (n + 1) → α) → ℝ} (hF : Integrable F (Qm ν (n + 1))) :
    ∫ ω, F ω ∂Qm ν (n + 1) = ∫ p, ∫ x, F (Fin.insertNth i x p) ∂ν ∂Qm ν n := by
  rw [integral_insertNth ν n i F]
  exact integral_prod (fun q : (Fin n → α) × α => F (Fin.insertNth i q.2 q.1))
    (integrable_insertNth ν n i hF)

omit [MeasurableSpace α] in
theorem Tn_insertNth (ε : ℕ → α → ℝ) {n : ℕ} (i : Fin (n + 1)) (j : ℕ) (k' : Fin n → ℕ) (x : α)
    (p : Fin n → α) :
    Tn ε (Fin.insertNth i j k' : Fin (n + 1) → ℕ) (Fin.insertNth i x p : Fin (n + 1) → α) =
      ε j x * Tn ε k' p := by
  simp [Tn, Fin.prod_univ_succAbove _ i]

end Slice


open DGPS

section SliceTorus

variable {d n : ℕ}

theorem slice_funext (φ : ParticleSpace d (Nat.succPNat n) → ℝ) (i : Fin (n + 1))
    (p : Fin n → Torus d) :
    (fun x : Torus d => φ (Fin.insertNth i x p)) =
      fun t : Torus d => φ (Function.update (Fin.insertNth i (0 : Torus d) p :
        ParticleSpace d (Nat.succPNat n)) i t) := by
  funext t
  congr 1
  exact (Fin.update_insertNth (α := fun _ => Torus d) i (0 : Torus d) t p).symm

theorem isSmoothPeriodic_slice {φ : ParticleSpace d (Nat.succPNat n) → ℝ}
    (hφ : IsSmoothPeriodicParticle φ) (i : Fin (n + 1)) (p : Fin n → Torus d) :
    IsSmoothPeriodic (fun x : Torus d => φ (Fin.insertNth i x p)) := by
  rw [slice_funext]
  exact DGPS.Lipschitz.df_isSmoothPeriodic_slice hφ _ i

theorem coordPartial_slice {φ : ParticleSpace d (Nat.succPNat n) → ℝ}
    (hφ : IsSmoothPeriodicParticle φ) (i : Fin (n + 1)) (p : Fin n → Torus d) (l : Fin d)
    (x : Torus d) :
    coordPartial l (fun x : Torus d => φ (Fin.insertNth i x p)) x =
      particlePartial (N := Nat.succPNat n) i l φ (Fin.insertNth i x p) := by
  rw [slice_funext]
  refine (DGPS.Lipschitz.df_coordPartial_slice hφ (Fin.insertNth i (0 : Torus d) p :
    ParticleSpace d (Nat.succPNat n)) i l x).trans ?_
  congr 1
  exact Fin.update_insertNth (α := fun _ => Torus d) i (0 : Torus d) x p

end SliceTorus


section Parseval

variable {α : Type} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (ε : ℕ → α → ℝ)

theorem inner_toLp_tB (h : CompleteONB μ ε) (N : ℕ) {f : (Fin N → α) → ℝ}
    (hf : MemLp f 2 (Qm μ N)) (k : Fin N → ℕ) :
    inner ℝ (hf.toLp f) (tB μ ε h N k) = ∫ ω, f ω * Tn ε k ω ∂Qm μ N := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, tensorHB_apply μ ε h.mem h.orth h.complete N k] with ω a b
  rw [RCLike.inner_apply]
  show (tB μ ε h N k) ω * (hf.toLp f) ω = _
  rw [a, b, mul_comm]

theorem hasSum_sq_integral_tB (h : CompleteONB μ ε) (N : ℕ) {f : (Fin N → α) → ℝ}
    (hf : MemLp f 2 (Qm μ N)) :
    HasSum (fun k : Fin N → ℕ => (∫ ω, f ω * Tn ε k ω ∂Qm μ N) ^ 2)
      (∫ ω, f ω ^ 2 ∂Qm μ N) := by
  have h1 := (tB μ ε h N).hasSum_inner_mul_inner (hf.toLp f) (hf.toLp f)
  have e2 : inner ℝ (hf.toLp f) (hf.toLp f) = ∫ ω, f ω ^ 2 ∂Qm μ N := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with ω a
    rw [RCLike.inner_apply, a]
    simp [sq]
  rw [e2] at h1
  convert h1 using 2 with k
  rw [real_inner_comm (hf.toLp f) (tB μ ε h N k), inner_toLp_tB μ ε h N hf k, sq]

end Parseval

end LIP057B

section LIP057E1
open MeasureTheory
open scoped ENNReal

section Assembly

variable {α : Type} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (ε : ℕ → α → ℝ)

/-- The `j`-th Fourier coefficient of the slice of `F` through `p` in the `i`-th slot. -/
noncomputable def sliceCoeff {n : ℕ} (i : Fin (n + 1)) (F : (Fin (n + 1) → α) → ℝ) (j : ℕ)
    (p : Fin n → α) : ℝ :=
  ∫ x, F (Fin.insertNth i x p) * ε j x ∂μ

variable {μ ε}

theorem integrable_mul_Tn_LIP057 (h : CompleteONB μ ε) (N : ℕ) {F : (Fin N → α) → ℝ}
    (hF : Measurable F) {M : ℝ} (hM : ∀ ω, |F ω| ≤ M) (k : Fin N → ℕ) :
    Integrable (fun ω => F ω * Tn ε k ω) (Qm μ N) :=
  ((tensor_memLp μ ε h.mem N k).integrable one_le_two).bdd_mul hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by simpa using hM ω)

theorem measurable_sliceCoeff (hε : ∀ j, Measurable (ε j)) {n : ℕ} (i : Fin (n + 1))
    {F : (Fin (n + 1) → α) → ℝ} (hF : Measurable F) (j : ℕ) :
    Measurable (sliceCoeff μ ε i F j) := by
  have h1 : Measurable (fun q : (Fin n → α) × α => F (Fin.insertNth i q.2 q.1) * ε j q.2) :=
    (hF.comp (insEquiv n i).measurable).mul ((hε j).comp measurable_snd)
  exact (h1.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

theorem abs_sliceCoeff_le (h : CompleteONB μ ε) {n : ℕ} (i : Fin (n + 1))
    {F : (Fin (n + 1) → α) → ℝ} {M : ℝ} (hM : ∀ ω, |F ω| ≤ M) (j : ℕ) (p : Fin n → α) :
    |sliceCoeff μ ε i F j p| ≤ ∫ x, M * ‖ε j x‖ ∂μ := by
  unfold sliceCoeff
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (((h.mem j).integrable one_le_two).norm.const_mul M) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (by simpa using hM _) (norm_nonneg _)

theorem memLp_sliceCoeff (h : CompleteONB μ ε) (hε : ∀ j, Measurable (ε j)) {n : ℕ}
    (i : Fin (n + 1)) {F : (Fin (n + 1) → α) → ℝ} (hF : Measurable F) {M : ℝ}
    (hM : ∀ ω, |F ω| ≤ M) (j : ℕ) : MemLp (sliceCoeff μ ε i F j) 2 (Qm μ n) :=
  MemLp.of_bound (measurable_sliceCoeff hε i hF j).aestronglyMeasurable (∫ x, M * ‖ε j x‖ ∂μ)
    (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact abs_sliceCoeff_le h i hM j p)

theorem integral_mul_Tn_insertNth (h : CompleteONB μ ε) {n : ℕ} (i : Fin (n + 1))
    {F : (Fin (n + 1) → α) → ℝ} (hF : Measurable F) {M : ℝ} (hM : ∀ ω, |F ω| ≤ M)
    (j : ℕ) (k' : Fin n → ℕ) :
    ∫ ω, F ω * Tn ε (Fin.insertNth i j k' : Fin (n + 1) → ℕ) ω ∂Qm μ (n + 1) =
      ∫ p, sliceCoeff μ ε i F j p * Tn ε k' p ∂Qm μ n := by
  rw [integral_insertNth_iter μ n i (integrable_mul_Tn_LIP057 h (n + 1) hF hM _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [Tn_insertNth, sliceCoeff]
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

end Assembly

end LIP057E1

section LIP057E2
open MeasureTheory
open scoped ENNReal

section Assembly2

variable {α : Type} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] {ε : ℕ → α → ℝ}

theorem hasSum_slice_LIP057 (h : CompleteONB μ ε) (hεm : ∀ j, Measurable (ε j))
    (lam : ℕ → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    {n : ℕ} (i : Fin (n + 1)) {F : (Fin (n + 1) → α) → ℝ} (hF : Measurable F) {M : ℝ}
    (hM : ∀ ω, |F ω| ≤ M) (e : (Fin n → α) → ℝ) (he : Integrable e (Qm μ n))
    (hE : ∀ p, HasSum (fun j => lam j * (sliceCoeff μ ε i F j p) ^ 2) (e p)) :
    HasSum (fun k : Fin (n + 1) → ℕ => lam (k i) * (∫ ω, F ω * Tn ε k ω ∂Qm μ (n + 1)) ^ 2)
      (∫ p, e p ∂Qm μ n) := by
  set s : ℕ → (Fin n → α) → ℝ := fun j => sliceCoeff μ ε i F j with hs
  have hsL : ∀ j, MemLp (s j) 2 (Qm μ n) := fun j => memLp_sliceCoeff h hεm i hF hM j
  have hfint : ∀ j, Integrable (fun p => lam j * (s j p) ^ 2) (Qm μ n) := fun j =>
    ((hsL j).integrable_sq).const_mul (lam j)
  -- step 2: sum over j of the integrals
  have hnn : ∀ j p, 0 ≤ lam j * (s j p) ^ 2 := fun j p => mul_nonneg (hlam j) (sq_nonneg _)
  have hnorm : ∀ j, ∫ p, ‖lam j * (s j p) ^ 2‖ ∂Qm μ n = ∫ p, lam j * (s j p) ^ 2 ∂Qm μ n := by
    intro j
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    exact Real.norm_of_nonneg (hnn j p)
  have hsum : Summable fun j => ∫ p, lam j * (s j p) ^ 2 ∂Qm μ n := by
    refine summable_of_sum_le (c := ∫ p, e p ∂Qm μ n)
      (fun j => integral_nonneg fun p => hnn j p) fun u => ?_
    rw [← integral_finsetSum _ (fun j _ => hfint j)]
    refine integral_mono (integrable_finsetSum _ fun j _ => hfint j) he fun p => ?_
    exact sum_le_hasSum u (fun j _ => hnn j p) (hE p)
  have h2 : HasSum (fun j => ∫ p, lam j * (s j p) ^ 2 ∂Qm μ n) (∫ p, e p ∂Qm μ n) := by
    have := hasSum_integral_of_summable_integral_norm hfint
      (by simpa only [hnorm] using hsum)
    convert this using 2
    funext p
    exact (hE p).tsum_eq.symm
  -- step 1: Parseval in each j
  have h1 : ∀ j, HasSum (fun k' : Fin n → ℕ =>
      lam j * (∫ p, s j p * Tn ε k' p ∂Qm μ n) ^ 2) (∫ p, lam j * (s j p) ^ 2 ∂Qm μ n) := by
    intro j
    have := (hasSum_sq_integral_tB μ ε h n (hsL j)).mul_left (lam j)
    rwa [← integral_const_mul] at this
  -- step 3: the product family
  set G : ℕ × (Fin n → ℕ) → ℝ := fun q =>
    lam q.1 * (∫ p, s q.1 p * Tn ε q.2 p ∂Qm μ n) ^ 2 with hG
  have hGnn : 0 ≤ G := fun q => mul_nonneg (hlam _) (sq_nonneg _)
  have hGs : Summable G := by
    rw [summable_prod_of_nonneg hGnn]
    refine ⟨fun j => (h1 j).summable, ?_⟩
    exact hsum.congr fun j => ((h1 j).tsum_eq).symm
  have hGsum : HasSum G (∫ p, e p ∂Qm μ n) := by
    have := hGs.hasSum
    rwa [hGs.tsum_prod' (fun j => (h1 j).summable), tsum_congr fun j => (h1 j).tsum_eq,
      h2.tsum_eq] at this
  -- step 4: reindex
  refine (Equiv.hasSum_iff (Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℕ) i)).1 ?_
  convert hGsum using 1
  funext q
  simp only [Function.comp_apply, Fin.insertNthEquiv_apply, hG, hs]
  have hq : (Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℕ) i) q = Fin.insertNth i q.1 q.2 := rfl
  rw [hq, Fin.insertNth_apply_same, integral_mul_Tn_insertNth h i hF hM q.1 q.2]

end Assembly2

end LIP057E2

section LIP057F1
open MeasureTheory Filter Topology

theorem hasSum_of_approx_LIP057 {ι : Type*} (Λ : ι → ℝ) (hΛ : ∀ i, 0 ≤ Λ i)
    (x : ℕ → ι → ℝ) (y : ι → ℝ) (E : ℕ → ℝ) (E' : ℝ) (D : ℕ → ℕ → ℝ) (δ : ℕ → ℝ)
    (hx : ∀ m, HasSum (fun i => Λ i * (x m i) ^ 2) (E m))
    (hxy : ∀ i, Tendsto (fun m => x m i) atTop (𝓝 (y i)))
    (hE : Tendsto E atTop (𝓝 E'))
    (hd : ∀ m m', HasSum (fun i => Λ i * (x m i - x m' i) ^ 2) (D m m'))
    (hD : ∀ m m', D m m' ≤ δ m + δ m') (hδ : Tendsto δ atTop (𝓝 0)) :
    HasSum (fun i => Λ i * (y i) ^ 2) E' := by
  have hnn : ∀ (z : ι → ℝ), ∀ i, 0 ≤ Λ i * (z i) ^ 2 := fun z i => mul_nonneg (hΛ i) (sq_nonneg _)
  -- finite sums of `Λ y²` converge from those of `Λ (x m)²`
  have hfin : ∀ s : Finset ι, Tendsto (fun m => ∑ i ∈ s, Λ i * (x m i) ^ 2) atTop
      (𝓝 (∑ i ∈ s, Λ i * (y i) ^ 2)) := by
    intro s
    refine tendsto_finsetSum _ fun i _ => ?_
    exact ((hxy i).pow 2).const_mul _
  have hup : ∀ s : Finset ι, ∑ i ∈ s, Λ i * (y i) ^ 2 ≤ E' := by
    intro s
    refine le_of_tendsto_of_tendsto (hfin s) hE (Eventually.of_forall fun m => ?_)
    exact sum_le_hasSum s (fun i _ => hnn (x m) i) (hx m)
  have hsum : Summable (fun i => Λ i * (y i) ^ 2) :=
    summable_of_sum_le (fun i => hnn y i) hup
  have hT : ∑' i, Λ i * (y i) ^ 2 ≤ E' := hsum.tsum_le_of_sum_le hup
  -- distance estimate
  have hdist : ∀ (m : ℕ) (s : Finset ι), ∑ i ∈ s, Λ i * (x m i - y i) ^ 2 ≤ δ m := by
    intro m s
    have h1 : Tendsto (fun m' => ∑ i ∈ s, Λ i * (x m i - x m' i) ^ 2) atTop
        (𝓝 (∑ i ∈ s, Λ i * (x m i - y i) ^ 2)) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      exact ((tendsto_const_nhds.sub (hxy i)).pow 2).const_mul _
    have h2 : Tendsto (fun m' => δ m + δ m') atTop (𝓝 (δ m + 0)) :=
      tendsto_const_nhds.add hδ
    rw [add_zero] at h2
    refine le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun m' => ?_)
    exact (sum_le_hasSum s (fun i _ => hnn (fun i => x m i - x m' i) i) (hd m m')).trans (hD m m')
  -- lower bound
  have hlow : ∀ t : ℝ, 0 < t → E' ≤ (1 + t) * ∑' i, Λ i * (y i) ^ 2 := by
    intro t ht
    have hm : ∀ m, E m ≤ (1 + 1 / t) * δ m + (1 + t) * ∑' i, Λ i * (y i) ^ 2 := by
      intro m
      rw [← (hx m).tsum_eq]
      refine (hx m).summable.tsum_le_of_sum_le fun s => ?_
      have hpt : ∀ i, Λ i * (x m i) ^ 2 ≤
          (1 + 1 / t) * (Λ i * (x m i - y i) ^ 2) + (1 + t) * (Λ i * (y i) ^ 2) := by
        intro i
        have key : (x m i) ^ 2 ≤ (1 + 1 / t) * (x m i - y i) ^ 2 + (1 + t) * (y i) ^ 2 := by
          have h3 : 2 * (x m i - y i) * y i ≤ (1 / t) * (x m i - y i) ^ 2 + t * (y i) ^ 2 := by
            have : 0 ≤ (1 / t) * (x m i - y i - t * y i) ^ 2 := by positivity
            have e : (1 / t) * (x m i - y i - t * y i) ^ 2 =
                (1 / t) * (x m i - y i) ^ 2 - 2 * (x m i - y i) * y i + t * (y i) ^ 2 := by
              field_simp
              ring
            linarith
          nlinarith [h3]
        calc Λ i * (x m i) ^ 2 ≤ Λ i * ((1 + 1 / t) * (x m i - y i) ^ 2 + (1 + t) * (y i) ^ 2) :=
              mul_le_mul_of_nonneg_left key (hΛ i)
          _ = _ := by ring
      calc ∑ i ∈ s, Λ i * (x m i) ^ 2
          ≤ ∑ i ∈ s, ((1 + 1 / t) * (Λ i * (x m i - y i) ^ 2) + (1 + t) * (Λ i * (y i) ^ 2)) :=
            Finset.sum_le_sum fun i _ => hpt i
        _ = (1 + 1 / t) * ∑ i ∈ s, Λ i * (x m i - y i) ^ 2 +
              (1 + t) * ∑ i ∈ s, Λ i * (y i) ^ 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ (1 + 1 / t) * δ m + (1 + t) * ∑' i, Λ i * (y i) ^ 2 := by
            refine add_le_add (mul_le_mul_of_nonneg_left (hdist m s) (by positivity))
              (mul_le_mul_of_nonneg_left ?_ (by positivity))
            exact sum_le_hasSum s (fun i _ => hnn y i) hsum.hasSum
    have h4 : Tendsto (fun m => (1 + 1 / t) * δ m + (1 + t) * ∑' i, Λ i * (y i) ^ 2) atTop
        (𝓝 ((1 + 1 / t) * 0 + (1 + t) * ∑' i, Λ i * (y i) ^ 2)) :=
      (hδ.const_mul _).add tendsto_const_nhds
    rw [mul_zero, zero_add] at h4
    exact le_of_tendsto_of_tendsto hE h4 (Eventually.of_forall hm)
  have hT0 : 0 ≤ ∑' i, Λ i * (y i) ^ 2 := tsum_nonneg (hnn y)
  have hge : E' ≤ ∑' i, Λ i * (y i) ^ 2 := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    have hpos : 0 < ∑' i, Λ i * (y i) ^ 2 + 1 := by linarith
    have h1 := hlow (η / (∑' i, Λ i * (y i) ^ 2 + 1)) (by positivity)
    refine h1.trans ?_
    have h6 : η / (∑' i, Λ i * (y i) ^ 2 + 1) * ∑' i, Λ i * (y i) ^ 2 ≤ η := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith [hη, hT0]
    nlinarith [h6]
  have : ∑' i, Λ i * (y i) ^ 2 = E' := le_antisymm hT hge
  rw [← this]
  exact hsum.hasSum

end LIP057F1

section LIP057G1
open MeasureTheory
open scoped ENNReal

section Spec

open DGPS

/-- Spectral data of the one-particle weighted problem, in the form used by the energy identity. -/
structure SpecData {d : ℕ} (μ : Measure (Torus d)) (ε : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) : Prop where
  onb : CompleteONB μ ε
  meas : ∀ j, Measurable (ε j)
  nonneg : ∀ j, 0 ≤ lam j
  energy : ∀ f : Torus d → ℝ, IsSmoothPeriodic f →
    HasSum (fun j => lam j * (∫ x, f x * ε j x ∂μ) ^ 2)
      (∫ x, ∑ l : Fin d, (coordPartial l f x) ^ 2 ∂μ)
  dom : ∃ K : NNReal, μ ≤ (K : ℝ≥0∞) • haar d

variable {d : ℕ}

theorem bound_of_continuous_LIP057 {X : Type*} [TopologicalSpace X] [CompactSpace X] {f : X → ℝ}
    (hf : Continuous f) : ∃ M : ℝ, ∀ x, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨M, fun x => by simpa using hM x (Set.mem_univ x)⟩

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {ε : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}

theorem smooth_energy_LIP057 (S : SpecData μ ε lam) {n : ℕ}
    {φ : ParticleSpace d (Nat.succPNat n) → ℝ} (hφ : IsSmoothPeriodicParticle φ) :
    HasSum (fun k : Fin (n + 1) → ℕ =>
        (∑ i, lam (k i)) * (∫ ω, φ ω * Tn ε k ω ∂Qm μ (n + 1)) ^ 2)
      (∫ ω, ∑ i : Fin (n + 1), ∑ l : Fin d,
        (particlePartial (N := Nat.succPNat n) i l φ ω) ^ 2 ∂Qm μ (n + 1)) := by
  have hφc : Continuous φ := DGPS.FiniteN.EntropyDefects.continuous_of_smooth hφ
  obtain ⟨M, hM⟩ := bound_of_continuous_LIP057 hφc
  have hG : ∀ i : Fin (n + 1), Continuous fun ω : Fin (n + 1) → Torus d =>
      ∑ l : Fin d, (particlePartial (N := Nat.succPNat n) i l φ ω) ^ 2 := fun i =>
    continuous_finsetSum _ fun l _ =>
      (DGPS.FiniteN.EntropyDefects.continuous_particlePartial hφ i l).pow 2
  have hGi : ∀ i : Fin (n + 1), Integrable (fun ω : Fin (n + 1) → Torus d =>
      ∑ l : Fin d, (particlePartial (N := Nat.succPNat n) i l φ ω) ^ 2) (Qm μ (n + 1)) :=
    fun i => DGPS.FiniteN.EntropyDefects.integrable_of_continuous (hG i)
  have hslot : ∀ i : Fin (n + 1), HasSum (fun k : Fin (n + 1) → ℕ =>
      lam (k i) * (∫ ω, φ ω * Tn ε k ω ∂Qm μ (n + 1)) ^ 2)
      (∫ ω, ∑ l : Fin d, (particlePartial (N := Nat.succPNat n) i l φ ω) ^ 2 ∂Qm μ (n + 1)) := by
    intro i
    have := hasSum_slice_LIP057 S.onb S.meas lam S.nonneg i hφc.measurable hM
      (fun p => ∫ x, ∑ l : Fin d,
        (particlePartial (N := Nat.succPNat n) i l φ (Fin.insertNth i x p)) ^ 2 ∂μ)
      ((integrable_insertNth μ n i (hGi i)).integral_prod_left) (fun p => by
        have h := S.energy _ (isSmoothPeriodic_slice hφ i p)
        simp only [coordPartial_slice hφ] at h
        exact h)
    rwa [integral_insertNth_iter μ n i (hGi i)]
  have hsum := hasSum_sum (s := Finset.univ) (fun i _ => hslot i)
  rw [← integral_finsetSum _ (fun i _ => hGi i)] at hsum
  convert hsum using 1
  funext k
  rw [Finset.sum_mul]

end Spec

end LIP057G1

section LIP057G2
open MeasureTheory Filter Topology
open scoped ENNReal

section Extend

variable {X : Type*} [MeasurableSpace X] {Q : Measure X} [IsProbabilityMeasure Q]
  {J : Type*} [Fintype J] {ι : Type*}

theorem hasSum_extend_LIP057 (Λ : ι → ℝ) (hΛ : ∀ i, 0 ≤ Λ i) (T : ι → X → ℝ)
    (hT : ∀ k, MemLp (T k) 2 Q)
    (hT1 : ∀ (k : ι) (u : X → ℝ), MemLp u 2 Q → |∫ x, u x * T k x ∂Q| ≤ (eLpNorm u 2 Q).toReal)
    (ψ : ℕ → X → ℝ) (Ψ : X → ℝ) (a : ℕ → J → X → ℝ) (b : J → X → ℝ)
    (hψ : ∀ m, MemLp (ψ m) 2 Q) (hΨ : MemLp Ψ 2 Q)
    (ha : ∀ m j, MemLp (a m j) 2 Q) (hb : ∀ j, MemLp (b j) 2 Q)
    (hψc : Tendsto (fun m => eLpNorm (ψ m - Ψ) 2 Q) atTop (𝓝 0))
    (hac : ∀ j, Tendsto (fun m => eLpNorm (a m j - b j) 2 Q) atTop (𝓝 0))
    (hx : ∀ m, HasSum (fun k => Λ k * (∫ x, ψ m x * T k x ∂Q) ^ 2) (∫ x, ∑ j, (a m j x) ^ 2 ∂Q))
    (hd : ∀ m m', HasSum (fun k => Λ k * (∫ x, ψ m x * T k x ∂Q - ∫ x, ψ m' x * T k x ∂Q) ^ 2)
      (∫ x, ∑ j, (a m j x - a m' j x) ^ 2 ∂Q)) :
    HasSum (fun k => Λ k * (∫ x, Ψ x * T k x ∂Q) ^ 2) (∫ x, ∑ j, (b j x) ^ 2 ∂Q) := by
  have hsumint : ∀ (c : J → X → ℝ), (∀ j, MemLp (c j) 2 Q) →
      ∫ x, ∑ j, (c j x) ^ 2 ∂Q = ∑ j, ∫ x, (c j x) ^ 2 ∂Q := fun c hc =>
    integral_finsetSum _ fun j _ => (hc j).integrable_sq
  refine hasSum_of_approx_LIP057 Λ hΛ (fun m k => ∫ x, ψ m x * T k x ∂Q)
    (fun k => ∫ x, Ψ x * T k x ∂Q) (fun m => ∫ x, ∑ j, (a m j x) ^ 2 ∂Q)
    (∫ x, ∑ j, (b j x) ^ 2 ∂Q) (fun m m' => ∫ x, ∑ j, (a m j x - a m' j x) ^ 2 ∂Q)
    (fun m => 2 * ∑ j, ∫ x, (a m j x - b j x) ^ 2 ∂Q) hx ?_ ?_ hd ?_ ?_
  · -- convergence of the coefficients
    intro k
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun m => dist_nonneg) (fun m => ?_)
      (((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hψc))
    have e : ∫ x, ψ m x * T k x ∂Q - ∫ x, Ψ x * T k x ∂Q = ∫ x, (ψ m - Ψ) x * T k x ∂Q := by
      have i1 : Integrable (fun x => ψ m x * T k x) Q := (hψ m).integrable_mul (hT k)
      have i2 : Integrable (fun x => Ψ x * T k x) Q := hΨ.integrable_mul (hT k)
      rw [← integral_sub i1 i2]
      congr 1
      funext x
      simp [sub_mul]
    rw [Real.dist_eq, e]
    exact hT1 k (ψ m - Ψ) ((hψ m).sub hΨ)
  · -- convergence of the energies
    rw [hsumint b hb]
    simp_rw [hsumint (a _) (ha _)]
    refine tendsto_finsetSum _ fun j _ => ?_
    exact DGPS.FiniteN.Tools.WeightedSobolev.tendsto_integral_sq_of_tendsto_eLpNorm
      (fun m => ha m j) (hb j) (hac j)
  · -- the distance estimate
    intro m m'
    rw [hsumint (fun j x => a m j x - a m' j x) (fun j => (ha m j).sub (ha m' j))]
    have hle : ∀ j, ∫ x, (a m j x - a m' j x) ^ 2 ∂Q ≤
        2 * ∫ x, (a m j x - b j x) ^ 2 ∂Q + 2 * ∫ x, (a m' j x - b j x) ^ 2 ∂Q := by
      intro j
      have i0 : Integrable (fun x => (a m j x - a m' j x) ^ 2) Q :=
        ((ha m j).sub (ha m' j)).integrable_sq
      have i1 : Integrable (fun x => 2 * (a m j x - b j x) ^ 2) Q :=
        ((ha m j).sub (hb j)).integrable_sq.const_mul 2
      have i2 : Integrable (fun x => 2 * (a m' j x - b j x) ^ 2) Q :=
        ((ha m' j).sub (hb j)).integrable_sq.const_mul 2
      calc ∫ x, (a m j x - a m' j x) ^ 2 ∂Q
          ≤ ∫ x, (2 * (a m j x - b j x) ^ 2 + 2 * (a m' j x - b j x) ^ 2) ∂Q :=
            integral_mono i0 (i1.add i2) fun x => by
              nlinarith [sq_nonneg (a m j x + a m' j x - 2 * b j x)]
        _ = _ := by rw [integral_add i1 i2, integral_const_mul, integral_const_mul]
    calc ∑ j, ∫ x, (a m j x - a m' j x) ^ 2 ∂Q
        ≤ ∑ j, (2 * ∫ x, (a m j x - b j x) ^ 2 ∂Q + 2 * ∫ x, (a m' j x - b j x) ^ 2 ∂Q) :=
          Finset.sum_le_sum fun j _ => hle j
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  · -- δ → 0
    have h0 : ∀ j, Tendsto (fun m => ∫ x, (a m j x - b j x) ^ 2 ∂Q) atTop (𝓝 0) := by
      intro j
      have := DGPS.FiniteN.Tools.WeightedSobolev.tendsto_integral_sq_of_tendsto_eLpNorm
        (P := Q) (u := fun m => a m j - b j) (w := 0) (fun m => (ha m j).sub (hb j))
        MemLp.zero (by simpa using hac j)
      simpa using this
    have := (tendsto_finsetSum Finset.univ fun j _ => h0 j).const_mul 2
    simpa using this

end Extend

end LIP057G2

section LIP057G3
open MeasureTheory Filter Topology
open scoped ENNReal

section Energy

open DGPS

variable {d : ℕ}

theorem isSmooth_sub_LIP057 {N : ℕ+} {φ ψ : ParticleSpace d N → ℝ}
    (hφ : IsSmoothPeriodicParticle φ) (hψ : IsSmoothPeriodicParticle ψ) :
    IsSmoothPeriodicParticle (fun x => φ x - ψ x) := by
  unfold IsSmoothPeriodicParticle at *
  exact hφ.sub hψ

theorem particlePartial_sub_LIP057 {N : ℕ+} {φ ψ : ParticleSpace d N → ℝ}
    (hφ : IsSmoothPeriodicParticle φ) (hψ : IsSmoothPeriodicParticle ψ) (i : Fin N) (j : Fin d)
    (x : ParticleSpace d N) :
    particlePartial i j (fun y => φ y - ψ y) x = particlePartial i j φ x - particlePartial i j ψ x := by
  unfold particlePartial
  have hdφ : DifferentiableAt ℝ (φ ∘ particleLift) (fun k => SharpLSI.secT (x k)) :=
    (hφ.differentiable (by simp)) _
  have hdψ : DifferentiableAt ℝ (ψ ∘ particleLift) (fun k => SharpLSI.secT (x k)) :=
    (hψ.differentiable (by simp)) _
  have h : ((fun y => φ y - ψ y) ∘ particleLift) =
      fun z => (φ ∘ particleLift) z - (ψ ∘ particleLift) z := rfl
  rw [h, fderiv_fun_sub hdφ hdψ]
  simp

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {ε : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}

theorem abs_integral_mul_Tn_le_LIP057 (h : CompleteONB μ ε) (N : ℕ) (k : Fin N → ℕ)
    {u : (Fin N → Torus d) → ℝ} (hu : MemLp u 2 (Qm μ N)) :
    |∫ ω, u ω * Tn ε k ω ∂Qm μ N| ≤ (eLpNorm u 2 (Qm μ N)).toReal := by
  rw [← inner_toLp_tB μ ε h N hu k]
  calc _ ≤ ‖hu.toLp u‖ * ‖tB μ ε h N k‖ := abs_real_inner_le_norm _ _
    _ = _ := by rw [(tB μ ε h N).orthonormal.norm_eq_one k, mul_one, Lp.norm_toLp]

theorem Qm_le_LIP057 {K : NNReal} (hK : μ ≤ (K : ℝ≥0∞) • haar d) (n : ℕ) :
    Qm μ (n + 1) ≤ (K : ℝ≥0∞) ^ (n + 1) • particleHaar d (Nat.succPNat n) :=
  pi_le_smul_pow_LIP057 hK (n + 1)

theorem memLp_Qm_LIP057 {K : NNReal} (hK : μ ≤ (K : ℝ≥0∞) • haar d) (n : ℕ)
    {f : ParticleSpace d (Nat.succPNat n) → ℝ} (hf : MemLp f 2 (particleHaar d (Nat.succPNat n))) :
    MemLp f 2 (Qm μ (n + 1)) :=
  (hf.smul_measure (ENNReal.pow_ne_top ENNReal.coe_ne_top)).mono_measure (Qm_le_LIP057 hK n)

theorem tendsto_Qm_LIP057 {K : NNReal} (hK : μ ≤ (K : ℝ≥0∞) • haar d) (n : ℕ)
    {u : ℕ → ParticleSpace d (Nat.succPNat n) → ℝ}
    (hm : ∀ m, AEStronglyMeasurable (u m) (particleHaar d (Nat.succPNat n)))
    (h : Tendsto (fun m => eLpNorm (u m) 2 (particleHaar d (Nat.succPNat n))) atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm (u m) 2 (Qm μ (n + 1))) atTop (𝓝 0) := by
  set C : ℝ≥0∞ := ((K : ℝ≥0∞) ^ (n + 1)) ^ ((1 / (2 : ℝ≥0∞)).toReal) with hC
  have hCt : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
    (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have h2 : Tendsto (fun m => C * eLpNorm (u m) 2 (particleHaar d (Nat.succPNat n))) atTop
      (𝓝 (C * 0)) := ENNReal.Tendsto.const_mul h (Or.inr hCt)
  rw [mul_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun m => zero_le)
    (fun m => ?_)
  refine ((eLpNorm_mono_measure (u m) (Qm_le_LIP057 hK n)).trans_eq
    (eLpNorm_smul_measure_of_ne_top (by norm_num) (u m) _ (hm m))).trans ?_
  exact (smul_eq_mul _ _).le

theorem energy_identity_LIP057 (S : SpecData μ ε lam) {n : ℕ}
    {Ψ : ParticleSpace d (Nat.succPNat n) → ℝ}
    {g : ParticleSpace d (Nat.succPNat n) → Fin (n + 1) → Tangent d}
    (hg : IsParticleHaarWeakGradient (Nat.succPNat n) Ψ g) :
    HasSum (fun k : Fin (n + 1) → ℕ =>
        (∑ i, lam (k i)) * (∫ ω, Ψ ω * Tn ε k ω ∂Qm μ (n + 1)) ^ 2)
      (∫ ω, ∑ i : Fin (n + 1), ∑ l : Fin d, (g ω i l) ^ 2 ∂Qm μ (n + 1)) := by
  obtain ⟨K, hK⟩ := S.dom
  obtain ⟨φ, hφ, h1, h2⟩ := DGPS.FiniteN.Tools.WeightedSobolev.exists_smooth_particle_tendsto hg
  have hQ := fun {f : ParticleSpace d (Nat.succPNat n) → ℝ} (hf : MemLp f 2 (particleHaar d (Nat.succPNat n))) =>
    memLp_Qm_LIP057 hK n hf
  have hφQ : ∀ m, MemLp (φ m) 2 (Qm μ (n + 1)) := fun m =>
    hQ ((hφ m).memLp_top.mono_exponent (p := 2) le_top)
  have haQ : ∀ m (j : Fin (n + 1) × Fin d), MemLp (particlePartial (N := Nat.succPNat n) j.1 j.2 (φ m)) 2 (Qm μ (n + 1)) :=
    fun m j => hQ (((hφ m).memLp_top_particlePartial j.1 j.2).mono_exponent (p := 2) le_top)
  have hbQ : ∀ j : Fin (n + 1) × Fin d, MemLp (fun x => g x j.1 j.2) 2 (Qm μ (n + 1)) :=
    fun j => hQ (memLp_particleCoord hg.memLp_grad j.1 j.2)
  have key := hasSum_extend_LIP057 (Q := Qm μ (n + 1)) (J := Fin (n + 1) × Fin d)
    (fun k : Fin (n + 1) → ℕ => ∑ i, lam (k i))
    (fun k => Finset.sum_nonneg fun i _ => S.nonneg _) (Tn ε)
    (fun k => tensor_memLp μ ε S.onb.mem (n + 1) k)
    (fun k u hu => abs_integral_mul_Tn_le_LIP057 S.onb (n + 1) k hu)
    φ Ψ (fun m j => particlePartial (N := Nat.succPNat n) j.1 j.2 (φ m)) (fun j x => g x j.1 j.2)
    hφQ (hQ hg.memLp) haQ hbQ
    (tendsto_Qm_LIP057 hK n (fun m => (DGPS.FiniteN.EntropyDefects.continuous_of_smooth (hφ m)).aestronglyMeasurable.sub
      hg.memLp.aestronglyMeasurable) h1)
    (fun j => tendsto_Qm_LIP057 hK n (fun m =>
      ((hφ m).memLp_top_particlePartial j.1 j.2).aestronglyMeasurable.sub
        (memLp_particleCoord hg.memLp_grad j.1 j.2).aestronglyMeasurable) (h2 j.1 j.2))
    ?_ ?_
  · simpa only [Fintype.sum_prod_type] using key
  · intro m
    have := smooth_energy_LIP057 S (hφ m)
    simpa only [Fintype.sum_prod_type] using this
  · intro m m'
    have hs := smooth_energy_LIP057 S (isSmooth_sub_LIP057 (hφ m) (hφ m'))
    have hint : ∀ m k, Integrable (fun ω => φ m ω * Tn ε k ω) (Qm μ (n + 1)) := fun m k => by
      have hc := DGPS.FiniteN.EntropyDefects.continuous_of_smooth (hφ m)
      obtain ⟨M, hM⟩ := bound_of_continuous_LIP057 hc
      exact integrable_mul_Tn_LIP057 S.onb (n + 1) hc.measurable hM k
    have e : ∀ k, ∫ ω, (φ m ω - φ m' ω) * Tn ε k ω ∂Qm μ (n + 1) =
        ∫ ω, φ m ω * Tn ε k ω ∂Qm μ (n + 1) - ∫ ω, φ m' ω * Tn ε k ω ∂Qm μ (n + 1) := fun k => by
      refine Eq.trans (integral_congr_ae (Eventually.of_forall fun ω => ?_))
        (integral_sub (hint m k) (hint m' k))
      show (φ m ω - φ m' ω) * Tn ε k ω = φ m ω * Tn ε k ω - φ m' ω * Tn ε k ω
      ring
    have hs' : HasSum (fun k : Fin (n + 1) → ℕ => (∑ i, lam (k i)) *
        (∫ ω, φ m ω * Tn ε k ω ∂Qm μ (n + 1) - ∫ ω, φ m' ω * Tn ε k ω ∂Qm μ (n + 1)) ^ 2)
        (∫ ω, ∑ i : Fin (n + 1), ∑ l : Fin d,
          (particlePartial (N := Nat.succPNat n) i l (φ m) ω -
            particlePartial (N := Nat.succPNat n) i l (φ m') ω) ^ 2 ∂Qm μ (n + 1)) := by
      convert hs using 1
      · funext k
        rw [e k]
      · refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
        exact (congrArg (· ^ 2) (particlePartial_sub_LIP057 (hφ m) (hφ m') i l ω)).symm
    simpa only [Fintype.sum_prod_type] using hs'

end Energy

end LIP057G3

section LIP057G4
open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace Real

section Weighted

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent

variable {d : ℕ} {w : Torus d → ℝ} {c C : ℝ}

theorem isProb_wMeasure_LIP057 (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) (hint : ∫ x, w x ∂haar d = 1) :
    IsProbabilityMeasure (wMeasure d w) := by
  refine ⟨?_⟩
  have h := integral_wMeasure hw hc hwb (fun _ => (1 : ℝ))
  have h1 : ∫ x, (1 : ℝ) ∂wMeasure d w = 1 := by
    rw [h]; simpa using hint
  have hfin : wMeasure d w Set.univ < ∞ := by
    have := wMeasure_le (d := d) (w := w) (c := c) (C := C) hwb Set.univ
    refine lt_of_le_of_lt this ?_
    simp [ENNReal.ofReal_lt_top]
  have : IsFiniteMeasure (wMeasure d w) := ⟨hfin⟩
  simp only [integral_const, smul_eq_mul, mul_one] at h1
  have h2 : (wMeasure d w).real Set.univ = 1 := h1
  rw [Measure.real, ENNReal.toReal_eq_one_iff] at h2
  exact h2

theorem specData_LIP057 (hd : 0 < d) (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) (hint : ∫ x, w x ∂haar d = 1) :
    ∃ (e : HilbertBasis ℕ ℝ (Hw d w)) (lam : ℕ → ℝ) (G : ℕ → Torus d → Tangent d)
      (ε : ℕ → Torus d → ℝ),
      (lam 0 = 0 ∧ lam 0 < lam 1 ∧ Monotone lam ∧ Tendsto lam atTop atTop) ∧
      (∀ j, IsWeakGradient ((e j : Hw d w) : Torus d → ℝ) (G j)) ∧
      (∀ j (f : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (f : Torus d → ℝ) Y →
        weightedForm w (G j) Y = lam j * ⟪e j, f⟫_ℝ) ∧
      (∀ (f : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (f : Torus d → ℝ) Y →
        HasSum (fun j => lam j * ⟪e j, f⟫_ℝ ^ 2) (weightedForm w Y Y)) ∧
      (∀ j : ℕ, 1 ≤ j → 4 * π ^ 2 * c / (25 * C) * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam j) ∧
      (∀ j, ε j =ᵐ[wMeasure d w] ((e j : Hw d w) : Torus d → ℝ)) ∧
      SpecData (wMeasure d w) ε lam := by
  classical
  obtain ⟨e, lam, G, h0, hl0, hl01, hmono, htend, hG, heig, hen, hgrow⟩ :=
    DGPS.Lipschitz.WeightedSpectrum.weighted_eigenbasis_and_growth hd hw hc hwb hint
  have := isProb_wMeasure_LIP057 hw hc hwb hint
  let ε : ℕ → Torus d → ℝ := fun j => if j = 0 then fun _ => 1 else ((e j : Hw d w) : Torus d → ℝ)
  have hεae : ∀ j, ε j =ᵐ[wMeasure d w] ((e j : Hw d w) : Torus d → ℝ) := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simpa [ε] using h0.symm
    · simp [ε, hj]
  have hmeas : ∀ j, Measurable (ε j) := by
    intro j
    by_cases hj : j = 0
    · simp [ε, hj]
    · simp only [ε, hj, ite_false]
      exact (Lp.stronglyMeasurable _).measurable
  have hmem : ∀ j, MemLp (ε j) 2 (wMeasure d w) := fun j =>
    (Lp.memLp (e j)).ae_eq (hεae j).symm
  have hinner : ∀ (j : ℕ) (f : Hw d w), ⟪e j, f⟫_ℝ = ∫ x, ε j x * (f : Torus d → ℝ) x ∂wMeasure d w := by
    intro j f
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hεae j] with x hx
    rw [hx]
    simp [mul_comm]
  have horth : ∀ i j, ∫ x, ε i x * ε j x ∂wMeasure d w = if i = j then 1 else 0 := by
    intro i j
    have h1 := orthonormal_iff_ite.mp e.orthonormal i j
    rw [hinner i (e j)] at h1
    rw [← h1]
    refine integral_congr_ae ?_
    filter_upwards [hεae j] with x hx
    rw [hx]
  have hlam : ∀ j, 0 ≤ lam j := fun j => hl0 ▸ hmono (Nat.zero_le j)
  have hcomp : ∀ f : Torus d → ℝ, MemLp f 2 (wMeasure d w) →
      (∀ j, ∫ x, f x * ε j x ∂wMeasure d w = 0) → f =ᵐ[wMeasure d w] 0 := by
    intro f hf hj
    set F : Hw d w := hf.toLp f with hF
    have hcoef : ∀ j, e.repr F j = 0 := by
      intro j
      rw [HilbertBasis.repr_apply_apply, hinner]
      rw [← hj j]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp hf] with x hx
      rw [hx, mul_comm]
    have hs := e.hasSum_repr F
    simp only [hcoef, zero_smul] at hs
    have hF0 : F = 0 := hs.unique hasSum_zero
    have := MemLp.coeFn_toLp hf
    rw [← hF, hF0] at this
    filter_upwards [this, Lp.coeFn_zero ℝ 2 (wMeasure d w)] with x h1 h2
    rw [← h1, h2]
  have hdom : ∃ K : NNReal, wMeasure d w ≤ (K : ℝ≥0∞) • haar d :=
    ⟨C.toNNReal, wMeasure_le hwb⟩
  have henergy : ∀ f : Torus d → ℝ, IsSmoothPeriodic f →
      HasSum (fun j => lam j * (∫ x, f x * ε j x ∂wMeasure d w) ^ 2)
        (∫ x, ∑ l : Fin d, (coordPartial l f x) ^ 2 ∂wMeasure d w) := by
    intro f hf
    have hwg := hf.isWeakGradient
    have hmem : MemLp f 2 (wMeasure d w) := (memLp_wMeasure_iff hc hwb).2 hwg.memLp
    set F : Hw d w := hmem.toLp f with hF
    have hFae : (F : Torus d → ℝ) =ᵐ[wMeasure d w] f := MemLp.coeFn_toLp hmem
    have hwgF : IsWeakGradient (F : Torus d → ℝ) (smoothGrad f) :=
      hwg.congr_ae (ae_eq_haar hc hwb hFae).symm (Filter.EventuallyEq.refl _ _)
    have h1 := hen F (smoothGrad f) hwgF
    rw [weightedForm_self] at h1
    have h2 : ∫ x, ‖smoothGrad f x‖ ^ 2 * w x ∂haar d =
        ∫ x, ∑ l : Fin d, (coordPartial l f x) ^ 2 ∂wMeasure d w := by
      rw [integral_wMeasure hw hc hwb]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul]
      rw [mul_comm, tangent_norm_sq]
      simp
    rw [h2] at h1
    convert h1 using 2 with j
    rw [hinner j F]
    congr 2
    refine integral_congr_ae ?_
    filter_upwards [hFae] with x hx
    rw [hx, mul_comm]
  exact ⟨e, lam, G, ε, ⟨hl0, hl01, hmono, htend⟩, hG, heig, hen, hgrow, hεae,
    ⟨⟨hmem, horth, hcomp, by simp [ε]⟩, hmeas, hlam, henergy, hdom⟩⟩

end Weighted

end LIP057G4

section LIP057G5
open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace Real

section Regroup

/-- The eigenvalue `Λ_a = ∑_j λ_j a_j` of an occupation vector. -/
noncomputable def occLam (lam : ℕ → ℝ) {N : ℕ} (a : Occ N) : ℝ := a.1.sum fun j m => lam j * m

theorem sum_lam_eq_occLam (lam : ℕ → ℝ) (h0 : lam 0 = 0) {N : ℕ} (k : Fin N → ℕ) :
    ∑ i, lam (k i) = occLam lam (occOfK k) := by
  classical
  show _ = (occK k).sum fun j m => lam j * m
  rw [Finsupp.sum_of_support_subset (occK k) (s := Finset.univ.image k) ?_ _ ?_]
  · rw [Finset.sum_comp (fun j => lam j) k]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [nsmul_eq_mul, occK_apply]
    by_cases hj : j = 0
    · simp [hj, h0]
    · simp only [hj, ite_false]
      rw [Fintype.card_subtype, mul_comm]
  · intro j hj
    rw [Finsupp.mem_support_iff, occK_apply] at hj
    by_cases h : j = 0
    · simp [h] at hj
    · simp only [h, ite_false] at hj
      have : 0 < Fintype.card {i : Fin N // k i = j} := Nat.pos_of_ne_zero hj
      obtain ⟨⟨i, hi⟩⟩ := Fintype.card_pos_iff.1 this
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  · intro j _
    simp

variable {α : Type} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (ε : ℕ → α → ℝ)

theorem tsum_fiber_sq (h : CompleteONB μ ε) (N : ℕ) {f : Lp ℝ 2 (Qm μ N)} (hf : f ∈ symSub μ N)
    (a : Occ N) :
    ∑' k : (occOfK ⁻¹' {a} : Set (Fin N → ℕ)), (inner ℝ f (tB μ ε h N k)) ^ 2 =
      (inner ℝ f (occLp μ ε h N a)) ^ 2 := by
  classical
  have hset : (occOfK : (Fin N → ℕ) → Occ N) ⁻¹' {a} = (Kocc N a : Set (Fin N → ℕ)) := by
    ext k
    simp [occOfK_eq_iff]
  rw [hset]
  have hne : (Kocc N a).Nonempty := Finset.card_pos.1 (Kocc_card_pos a)
  obtain ⟨k0, hk0⟩ := hne
  rw [Finset.tsum_subtype' (Kocc N a) (fun k => (inner ℝ f (tB μ ε h N k)) ^ 2),
    inner_symm_occLp μ ε h N hf a hk0, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have : ∀ k ∈ Kocc N a, (inner ℝ f (tB μ ε h N k)) ^ 2 = (inner ℝ f (tB μ ε h N k0)) ^ 2 := by
    intro k hk
    obtain ⟨σ, rfl⟩ := exists_perm_of_mem_Kocc a hk0 hk
    rw [inner_symm_tB μ ε h N hf]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]

/-- Regrouping the energy series along occupation fibres. -/
theorem hasSum_occ_of_hasSum_tB (h : CompleteONB μ ε) (N : ℕ) {f : Lp ℝ 2 (Qm μ N)}
    (hf : f ∈ symSub μ N) {lam : ℕ → ℝ} (h0 : lam 0 = 0) {E : ℝ}
    (hE : HasSum (fun k : Fin N → ℕ => (∑ i, lam (k i)) * (inner ℝ f (tB μ ε h N k)) ^ 2) E) :
    HasSum (fun a : Occ N => occLam lam a * (inner ℝ f (occLp μ ε h N a)) ^ 2) E := by
  classical
  have h2 := hE.tsum_fiberwise (occOfK : (Fin N → ℕ) → Occ N)
  convert h2 using 1
  funext a
  rw [← tsum_fiber_sq μ ε h N hf a, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hk : occOfK k.1 = a := k.2
  rw [sum_lam_eq_occLam lam h0 k.1, hk]

end Regroup

end LIP057G5

section LIP057G6
open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace Real

section Core

open DGPS

variable {α : Type} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (ε : ℕ → α → ℝ)

theorem occHB_ae_Eocc (h : CompleteONB μ ε) (N : ℕ) (a : Occ N) {r : ℕ} (lab : Fin r → ℕ)
    (hlab : ∀ l, lab l ≠ 0)
    (hcnt : ∀ j, j ≠ 0 → Fintype.card {l : Fin r // lab l = j} = a.1 j) :
    ((occHB μ ε h N a : symSub μ N) : Lp ℝ 2 (Qm μ N)) =ᵐ[Qm μ N] Eocc ε N lab := by
  classical
  rw [occHB_apply]
  unfold occLp
  have h1 := Lp.coeFn_smul ((Real.sqrt (Kocc N a).card)⁻¹) (∑ k ∈ Kocc N a, tB μ ε h N k)
  have h2 := Lp.coeFn_fun_finsetSum (Kocc N a) (fun k => tB μ ε h N k)
  have h3 : ∀ᵐ ω ∂(Qm μ N), ∀ k ∈ Kocc N a, (tB μ ε h N k : (Fin N → α) → ℝ) ω = Tn ε k ω :=
    (Filter.eventually_all_finset _).2 fun k _ =>
      tensorHB_apply μ ε h.mem h.orth h.complete N k
  filter_upwards [h1, h2, h3] with ω a1 a2 a3
  rw [a1, Eocc_eq ε h.zero lab hlab, Kset_eq_Kocc a lab hlab hcnt]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [a2]
  congr 1
  exact Finset.sum_congr rfl a3

end Core

section Tail

theorem tail_bound_LIP057 {ι : Type*} (q Λ : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hΛ : ∀ i, 0 ≤ Λ i)
    {E : ℝ} (hP : Summable q) (hO : HasSum (fun i => Λ i * q i) E) (L : ℝ) (hL : 0 < L) :
    Summable (fun a : {a : ι // L < Λ a} => q a) ∧
      ∑' a : {a : ι // L < Λ a}, q a ≤ E / L := by
  have hs1 : Summable (fun a : {a : ι // L < Λ a} => q a) :=
    hP.subtype {a : ι | L < Λ a}
  have hs2 : Summable (fun a : {a : ι // L < Λ a} => Λ a * q a) :=
    hO.summable.subtype {a : ι | L < Λ a}
  refine ⟨hs1, ?_⟩
  have h1 : L * ∑' a : {a : ι // L < Λ a}, q a ≤ ∑' a : {a : ι // L < Λ a}, Λ a * q a := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun a => mul_le_mul_of_nonneg_right (le_of_lt a.2) (hq a))
      (hs1.mul_left L) hs2
  have h2 : ∑' a : {a : ι // L < Λ a}, Λ a * q a ≤ E := by
    have := Summable.tsum_subtype_le (fun a => Λ a * q a) {a : ι | L < Λ a}
      (fun a => mul_nonneg (hΛ a) (hq a)) hO.summable
    rw [hO.tsum_eq] at this
    exact this
  rw [le_div_iff₀ hL, mul_comm]
  exact h1.trans h2

end Tail

section Energy

open DGPS

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {ε : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}

omit [IsProbabilityMeasure μ] in
theorem occLam_nonneg (S : SpecData μ ε lam) {N : ℕ} (a : Occ N) : 0 ≤ occLam lam a := by
  unfold occLam
  exact Finset.sum_nonneg fun j _ => mul_nonneg (S.nonneg j) (Nat.cast_nonneg _)

theorem occ_core_LIP057 (S : SpecData μ ε lam) (h0 : lam 0 = 0) {n : ℕ}
    {Ψ : ParticleSpace d (Nat.succPNat n) → ℝ}
    {g : ParticleSpace d (Nat.succPNat n) → Fin (n + 1) → Tangent d}
    (hg : IsParticleHaarWeakGradient (Nat.succPNat n) Ψ g)
    (hsym : ∀ σ : Equiv.Perm (Fin (n + 1)), (fun ω => Ψ (ω ∘ σ)) =ᵐ[Qm μ (n + 1)] Ψ) :
    ∃ c : Occ (n + 1) → ℝ,
      (∀ a, c a = ∫ ω, Ψ ω *
        ((occHB μ ε S.onb (n + 1) a : symSub μ (n + 1)) : Lp ℝ 2 (Qm μ (n + 1))) ω
          ∂Qm μ (n + 1)) ∧
      HasSum (fun a => c a ^ 2) (∫ ω, Ψ ω ^ 2 ∂Qm μ (n + 1)) ∧
      HasSum (fun a => occLam lam a * c a ^ 2)
        (∫ ω, particleTangentNormSq (g ω) ∂Qm μ (n + 1)) ∧
      ∀ L : ℝ, 0 < L → Summable (fun a : {a : Occ (n + 1) // L < occLam lam a} => c a ^ 2) ∧
        ∑' a : {a : Occ (n + 1) // L < occLam lam a}, c a ^ 2 ≤
          (∫ ω, particleTangentNormSq (g ω) ∂Qm μ (n + 1)) / L := by
  classical
  obtain ⟨K, hK⟩ := S.dom
  have hΨ : MemLp Ψ 2 (Qm μ (n + 1)) := memLp_Qm_LIP057 hK n hg.memLp
  set f : Lp ℝ 2 (Qm μ (n + 1)) := hΨ.toLp Ψ with hf
  have hfae : (f : (Fin (n + 1) → Torus d) → ℝ) =ᵐ[Qm μ (n + 1)] Ψ := hΨ.coeFn_toLp
  have hfs : f ∈ symSub μ (n + 1) := by
    intro σ
    refine Lp.ext ?_
    have e1 := permLp_ae μ (n + 1) σ f
    have e2 := (measurePreserving_permArg μ (n + 1) σ).quasiMeasurePreserving.ae_eq_comp hfae
    filter_upwards [e1, e2, hfae, hsym σ] with ω a b c d
    rw [a]
    exact b.trans (d.trans c.symm)
  have hinner : ∀ u : Lp ℝ 2 (Qm μ (n + 1)), inner ℝ f u = ∫ ω, Ψ ω * u ω ∂Qm μ (n + 1) := by
    intro u
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hfae] with ω hω
    rw [RCLike.inner_apply, hω]
    simp [mul_comm]
  have hcc : ∀ a : Occ (n + 1), ∫ ω, Ψ ω *
      ((occHB μ ε S.onb (n + 1) a : symSub μ (n + 1)) : Lp ℝ 2 (Qm μ (n + 1))) ω
        ∂Qm μ (n + 1) = inner ℝ f (occLp μ ε S.onb (n + 1) a) := by
    intro a
    rw [hinner, occHB_apply]
  refine ⟨fun a => inner ℝ f (occLp μ ε S.onb (n + 1) a), fun a => (hcc a).symm, ?_⟩
  have hnorm : ‖f‖ ^ 2 = ∫ ω, Ψ ω ^ 2 ∂Qm μ (n + 1) := by
    rw [← real_inner_self_eq_norm_sq, hinner]
    refine integral_congr_ae ?_
    filter_upwards [hfae] with ω hω
    rw [hω, sq]
  have hP := hasSum_sq_occLp μ ε S.onb (n + 1) hfs
  rw [hnorm] at hP
  have hE := energy_identity_LIP057 S hg
  have hE' : HasSum (fun k : Fin (n + 1) → ℕ =>
      (∑ i, lam (k i)) * (inner ℝ f (tB μ ε S.onb (n + 1) k)) ^ 2)
      (∫ ω, particleTangentNormSq (g ω) ∂Qm μ (n + 1)) := by
    have e : (∫ ω, particleTangentNormSq (g ω) ∂Qm μ (n + 1)) =
        ∫ ω, ∑ i : Fin (n + 1), ∑ l : Fin d, (g ω i l) ^ 2 ∂Qm μ (n + 1) := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      exact particleTangentNormSq_eq (g ω)
    rw [e]
    convert hE using 3 with k
    rw [hf, inner_toLp_tB μ ε S.onb (n + 1) hΨ k]
  have hO := hasSum_occ_of_hasSum_tB μ ε S.onb (n + 1) hfs h0 hE'
  refine ⟨hP, hO, fun L hL => ?_⟩
  have hsq : ∀ a : Occ (n + 1), 0 ≤ (inner ℝ f (occLp μ ε S.onb (n + 1) a)) ^ 2 :=
    fun a => sq_nonneg _
  exact tail_bound_LIP057 _ _ hsq (fun a => occLam_nonneg S a) hP.summable hO L hL

end Energy

end LIP057G6

end DGPS.Lipschitz.SymmetricOccupation

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace Real

namespace DGPS.Lipschitz

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent
open DGPS.Lipschitz.SymmetricOccupation

/-- LIP057.  **Occupation basis and spectral tail.**  Let `w` be a measurable weight with
`c ≤ w ≤ C` a.e. (`0 < c`) and `∫ w = 1` on `𝕋^d` (`0 < d`), and `μ = w m`.  There is a measurable
orthonormal basis `ε = (ε_j)` of `L²(μ)` (a representative of the eigenbasis of
`weighted_eigenbasis_and_growth`, with `ε_0 = 1`) with eigenvalues `lam` (`lam 0 = 0`,
monotone, tending to infinity, with the Weyl lower bound) such that for every `N ≥ 1`:

* the occupation functions `E_{α,N}` (`Eocc ε N lab`, the sum over ordered distinct labels with
  occupation `α`, divided by `√(N^{\underline r} ∏ α_j!)`; for `α = 0` this is the constant `1`) form,
  as classes in `L²(μ^N)`, a Hilbert basis `b` of the symmetric subspace `symSub μ N`;
* for every `Ψ ∈ H¹(𝕋^{dN})` (Haar weak gradient `g`) that is `μ^N`-a.e. symmetric, the coefficients
  `c_α = ∫ Ψ E_{α,N} dμ^N` satisfy `∑ c_α² = ‖Ψ‖²_{L²(μ^N)}`, `∑ Λ_α c_α² = ∫ ∑_i |∇_i Ψ|² dμ^N`
  with `Λ_α = ∑_j λ_j α_j` (`occLam`), and for every level `L > 0` the tail mass
  `∑_{Λ_α > L} c_α²` is at most `E_N^0(Ψ) / L`. -/
theorem occupation_basis_and_spectral_tail {d : ℕ} {w : Torus d → ℝ} {c C : ℝ}
    (hd : 0 < d) (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) (hint : ∫ x, w x ∂haar d = 1) :
    ∃ _ : IsProbabilityMeasure (wMeasure d w),
    ∃ (e : HilbertBasis ℕ ℝ (Hw d w)) (lam : ℕ → ℝ) (ε : ℕ → Torus d → ℝ),
      (lam 0 = 0 ∧ lam 0 < lam 1 ∧ Monotone lam ∧ Tendsto lam atTop atTop ∧
        ∀ j : ℕ, 1 ≤ j → 4 * π ^ 2 * c / (25 * C) * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam j) ∧
      (∀ j, ε j =ᵐ[wMeasure d w] ((e j : Hw d w) : Torus d → ℝ)) ∧
      CompleteONB (wMeasure d w) ε ∧
      ∀ N : ℕ+, ∃ b : HilbertBasis (Occ (N : ℕ)) ℝ (symSub (wMeasure d w) (N : ℕ)),
        (∀ (a : Occ (N : ℕ)) (r : ℕ) (lab : Fin r → ℕ), (∀ l, lab l ≠ 0) →
          (∀ j, j ≠ 0 → Fintype.card {l : Fin r // lab l = j} = a.1 j) →
          ((b a : symSub (wMeasure d w) (N : ℕ)) : Lp ℝ 2 (Qm (wMeasure d w) (N : ℕ))) =ᵐ[Qm (wMeasure d w) (N : ℕ)]
            Eocc ε (N : ℕ) lab) ∧
        ∀ (Ψ : ParticleSpace d N → ℝ) (g : ParticleSpace d N → Fin N → Tangent d),
          IsParticleHaarWeakGradient N Ψ g →
          (∀ σ : Equiv.Perm (Fin (N : ℕ)),
            (fun ω => Ψ (ω ∘ σ)) =ᵐ[Qm (wMeasure d w) (N : ℕ)] Ψ) →
          ∃ cf : Occ (N : ℕ) → ℝ,
            (∀ (a : Occ (N : ℕ)) (r : ℕ) (lab : Fin r → ℕ), (∀ l, lab l ≠ 0) →
              (∀ j, j ≠ 0 → Fintype.card {l : Fin r // lab l = j} = a.1 j) →
              cf a = ∫ ω, Ψ ω * Eocc ε (N : ℕ) lab ω ∂Qm (wMeasure d w) (N : ℕ)) ∧
            HasSum (fun a => cf a ^ 2) (∫ ω, Ψ ω ^ 2 ∂Qm (wMeasure d w) (N : ℕ)) ∧
            HasSum (fun a => occLam lam a * cf a ^ 2)
              (∫ ω, particleTangentNormSq (g ω) ∂Qm (wMeasure d w) (N : ℕ)) ∧
            ∀ L : ℝ, 0 < L →
              Summable (fun a : {a : Occ (N : ℕ) // L < occLam lam a} => cf a ^ 2) ∧
              ∑' a : {a : Occ (N : ℕ) // L < occLam lam a}, cf a ^ 2 ≤
                (∫ ω, particleTangentNormSq (g ω) ∂Qm (wMeasure d w) (N : ℕ)) / L := by
  classical
  obtain ⟨e, lam, G, ε, ⟨hl0, hl01, hmono, htend⟩, -, -, -, hgrow, hεae, S⟩ :=
    specData_LIP057 hd hw hc hwb hint
  have hP := isProb_wMeasure_LIP057 hw hc hwb hint
  refine ⟨hP, e, lam, ε, ⟨hl0, hl01, hmono, htend, hgrow⟩, hεae, S.onb, ?_⟩
  intro N
  obtain ⟨n, rfl⟩ : ∃ n, N = Nat.succPNat n := ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
  refine ⟨occHB (wMeasure d w) ε S.onb (n + 1), ?_, ?_⟩
  · intro a r lab hlab hcnt
    exact occHB_ae_Eocc (wMeasure d w) ε S.onb (n + 1) a lab hlab hcnt
  · intro Ψ g hg hsym
    obtain ⟨cf, hcf, h1, h2, h3⟩ := occ_core_LIP057 S hl0 hg hsym
    refine ⟨cf, ?_, h1, h2, h3⟩
    intro a r lab hlab hcnt
    refine (hcf a).trans (integral_congr_ae ?_)
    filter_upwards [occHB_ae_Eocc (wMeasure d w) ε S.onb (n + 1) a lab hlab hcnt] with ω hω
    exact congrArg (fun t => Ψ ω * t) hω

end DGPS.Lipschitz
