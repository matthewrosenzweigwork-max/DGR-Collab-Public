import SharpSymmetricLSI.Infra.Torus

/-!
# Lemma 4.2 (lane s42; R16): orthonormal features

Given finitely many `μ`-mean-zero bounded continuous functions `u₁, …, u_m` (the features of a
finite-rank kernel), there are bounded continuous, mean-zero, `L²(μ)`-orthonormal functions
`e₁, …, e_n` such that every `uᵢ` is (everywhere) a linear combination of the `e_j`. The measure
`μ` is assumed to charge every nonzero continuous function (true for a minimizer, whose density
is positive).
-/

noncomputable section
open MeasureTheory Module BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} (μ : Measure (Torus d)) [IsProbabilityMeasure μ]

theorem integrable_bcf_mul' (f g : Torus d →ᵇ ℝ) : Integrable (fun x => f x * g x) μ :=
  (f * g).integrable μ

/-- The `L²(μ)` pairing on a submodule of bounded continuous functions. -/
def l2Form (S : Submodule ℝ (Torus d →ᵇ ℝ)) : LinearMap.BilinForm ℝ S :=
  LinearMap.mk₂ ℝ (fun u v => ∫ x, (u : Torus d →ᵇ ℝ) x * (v : Torus d →ᵇ ℝ) x ∂μ)
    (fun u₁ u₂ v => by
      simp only [Submodule.coe_add, coe_add, Pi.add_apply, add_mul]
      exact integral_add (integrable_bcf_mul' μ _ _) (integrable_bcf_mul' μ _ _))
    (fun c u v => by
      simp only [Submodule.coe_smul, coe_smul, smul_eq_mul, mul_assoc]
      exact integral_const_mul _ _)
    (fun u v₁ v₂ => by
      simp only [Submodule.coe_add, coe_add, Pi.add_apply, mul_add]
      exact integral_add (integrable_bcf_mul' μ _ _) (integrable_bcf_mul' μ _ _))
    (fun c u v => by
      simp only [Submodule.coe_smul, coe_smul, smul_eq_mul, mul_left_comm _ c]
      exact integral_const_mul _ _)

theorem l2Form_apply (S : Submodule ℝ (Torus d →ᵇ ℝ)) (u v : S) :
    l2Form μ S u v = ∫ x, (u : Torus d →ᵇ ℝ) x * (v : Torus d →ᵇ ℝ) x ∂μ := rfl

/-- **Orthonormal features.** -/
theorem exists_orthonormal_features
    (hpos : ∀ u : Torus d →ᵇ ℝ, ∫ x, u x * u x ∂μ = 0 → u = 0)
    {m : ℕ} (u : Fin m → Torus d →ᵇ ℝ) (hu : ∀ i, ∫ x, u i x ∂μ = 0) :
    ∃ n : ℕ, ∃ e : Fin n → Torus d →ᵇ ℝ,
      (∀ j, ∫ x, e j x ∂μ = 0) ∧
      (∀ j k, ∫ x, e j x * e k x ∂μ = if j = k then 1 else 0) ∧
      ∀ i, ∃ α : Fin n → ℝ, ∀ x, u i x = ∑ j, α j * e j x := by
  set S : Submodule ℝ (Torus d →ᵇ ℝ) := Submodule.span ℝ (Set.range u) with hS
  have : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range u)
  set B := l2Form μ S with hB
  have hsymm : LinearMap.IsSymm B :=
    LinearMap.isSymm_def.mpr fun v w => by
      rw [RingHom.id_apply, hB, l2Form_apply, l2Form_apply]; congr 1; funext x; ring
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (K := ℝ) (V := S) (B := B) hsymm
  -- every element of `S` has mean zero
  have hmean : ∀ s ∈ S, ∫ x, s x ∂μ = 0 := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hu i
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [coe_add, Pi.add_apply]
      rw [integral_add (x.integrable μ) (y.integrable μ), hx, hy, add_zero]
    | smul a x _ hx =>
      simp only [coe_smul, smul_eq_mul]
      rw [integral_const_mul, hx, mul_zero]
  have hBpos : ∀ s : S, s ≠ 0 → 0 < B s s := by
    intro s hs
    rw [hB, l2Form_apply]
    refine lt_of_le_of_ne (integral_nonneg fun x => mul_self_nonneg _) fun h0 => hs ?_
    exact Subtype.ext (hpos _ h0.symm)
  have hBv : ∀ i, 0 < B (v i) (v i) := fun i => hBpos _ (v.ne_zero i)
  set c : Fin (finrank ℝ S) → ℝ := fun i => (Real.sqrt (B (v i) (v i)))⁻¹ with hc
  set e : Fin (finrank ℝ S) → Torus d →ᵇ ℝ := fun i => c i • ((v i : S) : Torus d →ᵇ ℝ) with he
  refine ⟨finrank ℝ S, e, fun j => ?_, fun j k => ?_, fun i => ?_⟩
  · show ∫ x, c j * ((v j : S) : Torus d →ᵇ ℝ) x ∂μ = 0
    rw [integral_const_mul, hmean _ (v j).2, mul_zero]
  · have h1 : ∫ x, e j x * e k x ∂μ = c j * c k * B (v j) (v k) := by
      rw [hB, l2Form_apply, ← integral_const_mul]
      congr 1; funext x; simp only [he, coe_smul, smul_eq_mul]; ring
    rw [h1]
    split_ifs with hjk
    · subst hjk
      have hs := Real.sq_sqrt (hBv j).le
      have hsp := (Real.sqrt_pos.mpr (hBv j)).ne'
      simp only [hc]
      field_simp
      rw [hs]
    · rw [show B (v j) (v k) = 0 from hv hjk, mul_zero]
  · set s : S := ⟨u i, Submodule.subset_span ⟨i, rfl⟩⟩
    refine ⟨fun j => v.repr s j * Real.sqrt (B (v j) (v j)), fun x => ?_⟩
    have hsum := v.sum_repr s
    have hx : u i x = ∑ j, v.repr s j * ((v j : S) : Torus d →ᵇ ℝ) x := by
      have : (s : Torus d →ᵇ ℝ) x = ∑ j, v.repr s j * ((v j : S) : Torus d →ᵇ ℝ) x := by
        conv_lhs => rw [← hsum]
        simp only [Submodule.coe_sum, Submodule.coe_smul, coe_sum, coe_smul, Finset.sum_apply,
          smul_eq_mul]
      exact this
    rw [hx]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsp := (Real.sqrt_pos.mpr (hBv j)).ne'
    simp only [he, hc, coe_smul, smul_eq_mul]
    field_simp

end SharpLSI
