import SharpSymmetricLSI.Paper.Sec5_1
import SharpSymmetricLSI.Paper.CondEmpirical
import SharpSymmetricLSI.Paper.CondEntropy4
import SharpSymmetricLSI.Paper.R37Particle

/-!
# R19 (Lemma 5.2), part 2: elementary tools

* `mul_sum_range_le_of_mono`: for nondecreasing `r`, `N ∑_{j<ℓ} r_j ≤ ℓ ∑_{j<N} r_j`;
* `mul_empiricalTensor_two`: `N · B(L_N^{⊗2}) = (2N)⁻¹ ∑_{i,j} F(X_i, X_j)` for `B = F/2`;
* `integral_pi_two_S5`: `∫ F(z_0, z_1) dρ^{⊗2}(z) = ∫∫ F(x, y) dρ(x) dρ(y)`;
* `neg_le_integral_of_le`: a lower bound for a real integral from a pointwise `ℝ≥0∞` bound on the
  negative part (no measurability needed);
* `pi_map_perm`, `isSymmetricMeasure_tilted`: tilts of `μ^{⊗N}` by symmetric functions are
  symmetric.
-/

open MeasureTheory InformationTheory Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

theorem mul_sum_range_le_of_mono {r : ℕ → ℝ} {N ℓ : ℕ} (hℓ : ℓ ≤ N)
    (hmono : ∀ i i', i ≤ i' → i' < N → r i ≤ r i') :
    (N : ℝ) * ∑ j ∈ Finset.range ℓ, r j ≤ ℓ * ∑ j ∈ Finset.range N, r j := by
  rw [← Finset.sum_range_add_sum_Ico r hℓ]
  have key : ∑ _i ∈ Finset.Ico ℓ N, ∑ j ∈ Finset.range ℓ, r j ≤
      ∑ _j ∈ Finset.range ℓ, ∑ i ∈ Finset.Ico ℓ N, r i := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun i hi => ?_
    simp only [Finset.mem_range, Finset.mem_Ico] at hj hi
    exact hmono j i (by omega) hi.2
  simp only [Finset.sum_const, Nat.card_Ico, Finset.card_range, nsmul_eq_mul] at key
  rw [Nat.cast_sub hℓ] at key
  nlinarith [key]

theorem mul_empiricalTensor_two {N : ℕ} (F : Torus d → Torus d → ℝ) (X : Config N d) :
    (N : ℝ) * empiricalTensor 2 (fun z => F (z 0) (z 1) / 2) X =
      1 / (2 * (N : ℝ)) * ∑ i, ∑ j, F (X i) (X j) := by
  unfold empiricalTensor
  have e1 : ∑ i : Fin 2 → Fin N, (fun z : Fin 2 → Torus d => F (z 0) (z 1) / 2) (X ∘ i) =
      ∑ p : Fin N × Fin N, F (X p.1) (X p.2) / 2 :=
    Fintype.sum_equiv (finTwoArrowEquiv (Fin N)) _ _ (fun i => rfl)
  have e2 : ∑ p : Fin N × Fin N, F (X p.1) (X p.2) / 2 = (∑ i, ∑ j, F (X i) (X j)) / 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_div]
  rw [e1, e2]
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · have : (N : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    field_simp

theorem integral_pi_two_S5 {ρ : Measure (Torus d)} [IsProbabilityMeasure ρ] {F : Torus d → Torus d → ℝ}
    (hF : Measurable (Function.uncurry F)) {B : ℝ} (hB : ∀ x y, |F x y| ≤ B) :
    ∫ z, F (z 0) (z 1) ∂Measure.pi (fun _ : Fin 2 => ρ) = ∫ y, ∫ x, F x y ∂ρ ∂ρ := by
  have h := (measurePreserving_finTwoArrow ρ).integral_comp'
    (g := fun p : Torus d × Torus d => F p.1 p.2)
  have hint : Integrable (fun p : Torus d × Torus d => F p.1 p.2) (ρ.prod ρ) :=
    Integrable.of_bound hF.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hB _ _)
  rw [← integral_prod_symm _ hint, ← h]
  rfl

/-- A lower bound `∫ g ≥ -(∫⁻ (g⁻))`, with the negative part bounded pointwise in `ℝ≥0∞`. -/
theorem neg_le_integral_of_le {α : Type*} [MeasurableSpace α] {ν : Measure α} {g : α → ℝ}
    {H : α → ℝ≥0∞} {a : ℝ} (ha : 0 ≤ a) (h : ∀ x, ENNReal.ofReal (-g x) ≤ ENNReal.ofReal a * H x)
    (hH : ∫⁻ x, H x ∂ν ≠ ⊤) :
    -(a * (∫⁻ x, H x ∂ν).toReal) ≤ ∫ x, g x ∂ν := by
  have h3 : 0 ≤ a * (∫⁻ x, H x ∂ν).toReal := mul_nonneg ha ENNReal.toReal_nonneg
  by_cases hg : Integrable g ν
  · rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
    have h1 : ∫⁻ x, ENNReal.ofReal (-g x) ∂ν ≤ ENNReal.ofReal a * ∫⁻ x, H x ∂ν := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_mono h
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hH) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha] at h2
    have h5 : 0 ≤ (∫⁻ x, ENNReal.ofReal (g x) ∂ν).toReal := ENNReal.toReal_nonneg
    linarith
  · rw [integral_undef hg]
    linarith

theorem pi_map_perm (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {N : ℕ}
    (σ : Equiv.Perm (Fin N)) :
    (Measure.pi fun _ : Fin N => μ).map (permEquiv σ) = Measure.pi fun _ : Fin N => μ := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (permEquiv σ).measurable (MeasurableSet.univ_pi hs)]
  have : (permEquiv σ : Config N d → Config N d) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i => s (σ.symm i) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, permEquiv_apply,
      Function.comp_apply]
    exact ⟨fun h i => by simpa using h (σ.symm i), fun h i => by simpa using h (σ i)⟩
  rw [this, Measure.pi_pi]
  exact Equiv.prod_comp σ.symm (fun i => μ (s i))

theorem isSymmetricMeasure_tilted (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {N : ℕ}
    {f : Config N d → ℝ} (hfm : Measurable f) (hf : ∀ (σ : Equiv.Perm (Fin N)) X, f (X ∘ σ) = f X) :
    IsSymmetricMeasure ((Measure.pi fun _ : Fin N => μ).tilted f) := by
  intro σ
  change ((Measure.pi fun _ : Fin N => μ).tilted f).map (permEquiv σ) = _
  unfold Measure.tilted
  have hm : Measurable fun x => ENNReal.ofReal
      (rexp (f x) / ∫ x, rexp (f x) ∂(Measure.pi fun _ : Fin N => μ)) :=
    ENNReal.measurable_ofReal.comp ((measurable_exp.comp hfm).div_const _)
  rw [map_withDensity_equiv _ _ hm, pi_map_perm]
  congr 1
  funext X
  simp only [Function.comp_apply, permEquiv_symm_apply, hf]

end SharpLSI
