import Mathlib
import FullLabeledLSI.Paper.Sec6MomentsU
import FullLabeledLSI.Paper.Sec6MomentsZ

/-!
# Fluctuation moment bound over a subset of the coordinates (Section 6, item M1')

For i.i.d. `X₁, …, X_N ∼ μ`, a subset `Bc ⊆ {1, …, N}` of the coordinates and a bounded centered
observable `f`, we prove
`E[(∑_{i ∈ Bc} f(X_i))^{2k}] ≤ C_k |Bc|^k B^{2k}`
and the normalised version `E[(|Bc|^{-1/2} ∑_{i ∈ Bc} f(X_i))^{2k}] ≤ C_k B^{2k}` (for
`|Bc| ≥ 1`), with `C_k` the constant of `sum_moment_bound`.

Route: the restriction map `Fin N → α ⟶ Fin |Bc| → α`, `ω ↦ (j ↦ ω (e j))` for an equivalence
`e : Fin |Bc| ≃ Bc`, is measure preserving between the product measures; the sum over `Bc`
becomes a sum over `Fin |Bc|`, and we apply `sum_moment_bound`.
-/

open MeasureTheory

namespace SharpLSI.FL.Sec6

section RestrictZ2

variable {α : Type} [MeasurableSpace α]

/-- The restriction of a configuration `ω : Fin N → α` to the subset `Bc`, re-indexed by
`Fin |Bc|`. -/
noncomputable def restrictFin {N : ℕ} (Bc : Finset (Fin N)) (ω : Fin N → α) : Fin Bc.card → α :=
  fun j => ω ((Bc.equivFin.symm j : Bc) : Fin N)

/-- The restriction map preserves the product measures. -/
lemma measurePreserving_restrictFin (μ : Measure α) [IsProbabilityMeasure μ] (N : ℕ)
    (Bc : Finset (Fin N)) :
    MeasurePreserving (restrictFin (α := α) Bc) (Measure.pi fun _ : Fin N => μ)
      (Measure.pi fun _ : Fin Bc.card => μ) := by
  have h1 := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin N => μ) (fun i => i ∈ Bc)
  have h2 := measurePreserving_fst.comp h1
  have h3 : MeasurePreserving (MeasurableEquiv.arrowCongr' Bc.equivFin (MeasurableEquiv.refl α))
      (@Measure.pi {i // i ∈ Bc} (fun _ => α) (Subtype.fintype fun i => i ∈ Bc) _ fun _ => μ)
      (Measure.pi fun _ : Fin Bc.card => μ) := by
    convert measurePreserving_arrowCongr' (fun _ : {i // i ∈ Bc} => μ)
      (fun _ : Fin Bc.card => μ) Bc.equivFin (MeasurableEquiv.refl α)
      (fun _ => MeasurePreserving.id μ)
  have h4 := h3.comp h2
  convert h4 using 1
  funext ω j
  simp [restrictFin, MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr,
    MeasurableEquiv.piEquivPiSubtypeProd]

omit [MeasurableSpace α] in
lemma sum_restrictFin {N : ℕ} (Bc : Finset (Fin N)) (f : α → ℝ) (ω : Fin N → α) :
    ∑ i ∈ Bc, f (ω i) = ∑ j : Fin Bc.card, f (restrictFin Bc ω j) := by
  have h1 : ∑ i ∈ Bc, f (ω i) = ∑ i : Bc, f (ω i) := (Finset.sum_coe_sort Bc _).symm
  rw [h1]
  exact (Equiv.sum_comp Bc.equivFin.symm (fun i : Bc => f (ω i))).symm

end RestrictZ2

/-- **Fluctuation moment bound over a subset of the coordinates (unnormalised).** -/
theorem sum_moment_bound_finset (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
      (N : ℕ) (Bc : Finset (Fin N)) (f : α → ℝ) (B : ℝ), Measurable f → (∀ᵐ x ∂μ, |f x| ≤ B) →
      ∫ x, f x ∂μ = 0 →
      ∫ ω, (∑ i ∈ Bc, f (ω i)) ^ (2 * k) ∂(Measure.pi fun _ : Fin N => μ)
        ≤ C * (Bc.card : ℝ) ^ k * B ^ (2 * k) := by
  obtain ⟨C, hC0, hC⟩ := sum_moment_bound k
  refine ⟨C, hC0, ?_⟩
  intro α _ μ _ N Bc f B hf hB hf0
  have hmp := measurePreserving_restrictFin μ N Bc
  have hmeas : Measurable (fun x : Fin Bc.card → α => (∑ j : Fin Bc.card, f (x j)) ^ (2 * k)) :=
    (Finset.measurable_sum _ (fun j _ => hf.comp (measurable_pi_apply j))).pow_const _
  have hmap := integral_map (μ := Measure.pi fun _ : Fin N => μ) hmp.measurable.aemeasurable
    hmeas.aestronglyMeasurable
  rw [hmp.map_eq] at hmap
  have hcongr : ∫ ω, (∑ i ∈ Bc, f (ω i)) ^ (2 * k) ∂(Measure.pi fun _ : Fin N => μ) =
      ∫ ω, (∑ j : Fin Bc.card, f (restrictFin Bc ω j)) ^ (2 * k)
        ∂(Measure.pi fun _ : Fin N => μ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [sum_restrictFin Bc f ω]
  exact (hcongr.trans hmap.symm).trans_le (hC α μ Bc.card f B hf hB hf0)

/-- **Fluctuation moment bound over a subset of the coordinates (normalised).** For
`|Bc| ≥ 1`, `E[(|Bc|^{-1/2} ∑_{i ∈ Bc} f(X_i))^{2k}] ≤ C_k B^{2k}`. -/
theorem fluct_moment_bound_finset (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
      (N : ℕ) (Bc : Finset (Fin N)), 1 ≤ Bc.card → ∀ (f : α → ℝ) (B : ℝ), Measurable f →
      (∀ᵐ x ∂μ, |f x| ≤ B) → ∫ x, f x ∂μ = 0 →
      ∫ ω, ((Bc.card : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ i ∈ Bc, f (ω i)) ^ (2 * k)
          ∂(Measure.pi fun _ : Fin N => μ) ≤ C * B ^ (2 * k) := by
  obtain ⟨C, hC0, hC⟩ := sum_moment_bound_finset k
  refine ⟨C, hC0, ?_⟩
  intro α _ μ _ N Bc hBc f B hf hB hf0
  have hM : (1 : ℝ) ≤ Bc.card := by exact_mod_cast hBc
  have hMpos : (0 : ℝ) < Bc.card := by linarith
  have hc2 : ((Bc.card : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (Bc.card : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hMpos.le]
    norm_num [Real.rpow_neg_one]
  have hpt : ∀ ω : Fin N → α,
      ((Bc.card : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ i ∈ Bc, f (ω i)) ^ (2 * k) =
        ((Bc.card : ℝ)⁻¹) ^ k * (∑ i ∈ Bc, f (ω i)) ^ (2 * k) := by
    intro ω
    rw [mul_pow, pow_mul, hc2]
  have hmain := hC α μ N Bc f B hf hB hf0
  have hinv : ((Bc.card : ℝ)⁻¹) ^ k * (Bc.card : ℝ) ^ k = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hMpos.ne', one_pow]
  simp_rw [hpt]
  rw [integral_const_mul]
  calc ((Bc.card : ℝ)⁻¹) ^ k *
        ∫ ω, (∑ i ∈ Bc, f (ω i)) ^ (2 * k) ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ((Bc.card : ℝ)⁻¹) ^ k * (C * (Bc.card : ℝ) ^ k * B ^ (2 * k)) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = C * B ^ (2 * k) * (((Bc.card : ℝ)⁻¹) ^ k * (Bc.card : ℝ) ^ k) := by ring
    _ = C * B ^ (2 * k) := by rw [hinv, mul_one]

end SharpLSI.FL.Sec6
