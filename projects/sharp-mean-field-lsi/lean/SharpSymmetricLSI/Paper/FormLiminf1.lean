import SharpSymmetricLSI.Paper.NBody2

/-!
# R33 (8.20) groundwork: resampling one coordinate of a product measure

`(X, y) ↦ X[l ↦ y]` pushes `μ^{⊗N} ⊗ μ` to `μ^{⊗N}`; hence
`∫ G dμ^{⊗N} = ∫∫ G(X[l ↦ y]) dμ(y) dμ^{⊗N}(X)`.
-/

open MeasureTheory Filter Topology Set

namespace SharpLSI

section
variable {α : Type*} [MeasurableSpace α] {N : ℕ}

theorem measurable_update_pair (l : Fin N) :
    Measurable fun p : (Fin N → α) × α => Function.update p.1 l p.2 :=
  measurable_pi_iff.2 fun j => by
    by_cases h : j = l
    · subst h; simpa using measurable_snd
    · simp only [Function.update_of_ne h]
      exact (measurable_pi_apply j).comp measurable_fst

theorem measurePreserving_update (μ : Measure α) [IsProbabilityMeasure μ] (l : Fin N) :
    MeasurePreserving (fun p : (Fin N → α) × α => Function.update p.1 l p.2)
      ((Measure.pi fun _ : Fin N => μ).prod μ) (Measure.pi fun _ : Fin N => μ) := by
  refine ⟨measurable_update_pair l, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply (measurable_update_pair l) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (Fin N → α) × α => Function.update p.1 l p.2) ⁻¹' (univ.pi s) =
      (univ.pi fun j => if j = l then univ else s j) ×ˢ s l := by
    ext ⟨X, y⟩
    simp only [mem_preimage, mem_univ_pi, mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h l⟩
      split_ifs with hj
      · trivial
      · simpa [Function.update_of_ne hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = l
      · subst hj; simpa using h2
      · simpa [Function.update_of_ne hj, hj] using h1 j
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have h1 : ∏ j, μ (if j = l then univ else s j) = ∏ j ∈ Finset.univ.erase l, μ (s j) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l)]
    simp only [if_true, measure_univ, one_mul]
    exact Finset.prod_congr rfl fun j hj => by simp only [if_neg (Finset.ne_of_mem_erase hj)]
  rw [h1, mul_comm, Finset.mul_prod_erase _ (fun j => μ (s j)) (Finset.mem_univ l)]

theorem integral_update_resample (μ : Measure α) [IsProbabilityMeasure μ] (l : Fin N)
    {G : (Fin N → α) → ℝ} (hG : Integrable G (Measure.pi fun _ : Fin N => μ)) :
    ∫ X, G X ∂Measure.pi (fun _ : Fin N => μ) =
      ∫ X, ∫ y, G (Function.update X l y) ∂μ ∂Measure.pi (fun _ : Fin N => μ) := by
  have hmp := measurePreserving_update μ l
  have hGm : AEStronglyMeasurable G (((Measure.pi fun _ : Fin N => μ).prod μ).map
      (fun p : (Fin N → α) × α => Function.update p.1 l p.2)) := by
    rw [hmp.map_eq]; exact hG.aestronglyMeasurable
  conv_lhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable hGm]
  exact integral_prod _ ((hmp.integrable_comp hG.aestronglyMeasurable).2 hG)

end

end SharpLSI
