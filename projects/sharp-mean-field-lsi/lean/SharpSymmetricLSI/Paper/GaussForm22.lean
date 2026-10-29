import SharpSymmetricLSI.Paper.GaussForm21
import SharpSymmetricLSI.Infra.GrossEnum

/-!
# R32 (F3): the generalized eigenbasis indexed increasingly by `ℕ`

From `exists_genEigen_set`: `σ‖u_x‖² ≤ B(u_x,u_x) = κ_x`, so by compactness of `J` the sublevel
sets `{κ ≤ L}` are finite (the `J u_x` are orthonormal, at mutual distance `√2`, inside a compact
set); `ℓ²` is infinite dimensional, so the index set is infinite; `exists_equiv_monotone` then
orders it (`exists_genEigen_nat`): `0 < ν_0 ≤ ν_1 ≤ … → ∞`.
-/

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace ENNReal

namespace SharpLSI

/-- The standard vectors `e_i` of `ℓ²` are orthonormal. -/
theorem orthonormal_single_L2N : Orthonormal ℝ fun i : ℕ => (lp.single 2 i 1 : L2N) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_single_L2N_left, one_mul, lp.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [Pi.single_apply, Ne.symm h, h]

theorem not_finiteDimensional_L2N : ¬ FiniteDimensional ℝ L2N := by
  intro h
  have := orthonormal_single_L2N.linearIndependent.finite
  exact not_finite ℕ

/-- Distinct members of an orthonormal family are at distance `√2 > 1`. -/
theorem one_lt_dist_of_orthonormal {ι : Type*} {v : ι → L2N} (hv : Orthonormal ℝ v) {i j : ι}
    (hij : i ≠ j) : 1 < dist (v i) (v j) := by
  have h2 : dist (v i) (v j) ^ 2 = 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, hv.1 i, hv.1 j, hv.2 hij]; norm_num
  nlinarith [dist_nonneg (x := v i) (y := v j)]

section gen
variable {T : ℕ → ℕ → ℝ} (hT : ∀ i j, T i j = T j i)
  (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) {σ : ℝ} (hσ0 : 0 < σ)
  (hσ : ∀ n (y : EuclideanSpace ℝ (Fin n)), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ)
  {lam' : ℕ → ℝ} (hpos : ∀ i, 0 < lam' i) {D : ℝ} (hD : ∀ i, |(√(lam' i))⁻¹| ≤ D)
include hT hS hσ0 hσ hpos

/-- **The generalized eigenbasis, increasingly indexed by `ℕ`.** With `J = diag(λ'^{-1/2})`:
`J u_j` is an orthonormal basis of `ℓ²`, `B(u_j, v) = ν_j ⟨J u_j, J v⟩`, i.e.
`u_j + T u_j = ν_j Λ⁻¹ u_j`, and `0 < ν_0 ≤ ν_1 ≤ … → ∞`. -/
theorem exists_genEigen_nat (htop : Tendsto lam' atTop atTop) :
    ∃ (u : ℕ → L2N) (ν : ℕ → ℝ), (∀ j, 0 < ν j) ∧ Monotone ν ∧ Tendsto ν atTop atTop ∧
      (∀ i j, ⟪diagOp hD (u i), diagOp hD (u j)⟫_ℝ = if i = j then 1 else 0) ∧
      (∀ y : L2N, (∀ j, ⟪diagOp hD (u j), y⟫_ℝ = 0) → y = 0) ∧
      (∀ j v, formB hS (u j) v = ν j * ⟪diagOp hD (u j), diagOp hD v⟫_ℝ) ∧
      (∀ j i, u j i + ∑' k, T i k * u j k = ν j * u j i / lam' i) ∧
      ∀ h : L2N, HasSum (fun j => (ν j)⁻¹ * ⟪diagOp hD (u j), h⟫_ℝ ^ 2)
        ⟪h, (isCoercive_formB hS hσ0 hσ).formSolutionOperator (diagOp hD) h⟫_ℝ := by
  obtain ⟨s, b, κ, u, hb, hκ, hJu, heq, hev, hexp⟩ :=
    exists_genEigen_set hT hS hσ0 hσ hpos hD htop
  have ho : Orthonormal ℝ ((↑) : s → L2N) := hb ▸ b.orthonormal
  -- `σ‖u_x‖² ≤ κ_x`
  have hnorm : ∀ x, σ * ‖u x‖ ^ 2 ≤ κ x := fun x => by
    have h1 := coercive_hsOp hS hσ (u x)
    have h2 := heq x (u x)
    rw [formB_apply, real_inner_self_eq_norm_sq, hJu x, real_inner_self_eq_norm_sq,
      ho.1 x] at h2
    linarith
  -- finite sublevel sets
  have hJ := isCompactOperator_diagOp hD (tendsto_inv_sqrt htop)
  have hfin : ∀ L, {x | κ x ≤ L}.Finite := by
    intro L
    set R := √(L / σ)
    have hK := hJ.isCompact_closure_image_closedBall R
    obtain ⟨t, htf, hcov⟩ := Metric.totallyBounded_iff.1 hK.totallyBounded (1 / 2) (by norm_num)
    have hmem : ∀ x : s, κ x ≤ L → (x : L2N) ∈ closure (diagOp hD '' Metric.closedBall 0 R) := by
      intro x hx
      refine subset_closure ⟨u x, ?_, hJu x⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      refine Real.le_sqrt_of_sq_le ?_
      rw [le_div_iff₀ hσ0]
      linarith [hnorm x]
    have hc : ∀ x : {x : s | κ x ≤ L}, ∃ y ∈ t, ((x : s) : L2N) ∈ Metric.ball y (1 / 2) := by
      intro x
      have := hcov (hmem x x.2)
      simpa only [mem_iUnion, exists_prop] using this
    choose c hct hcb using hc
    have hinj : Function.Injective c := by
      intro x x' h
      by_contra hne
      have hne' : (x : s) ≠ (x' : s) := fun h' => hne (Subtype.ext h')
      have h1 := one_lt_dist_of_orthonormal ho hne'
      have h2 := hcb x
      have h3 := hcb x'
      rw [h] at h2
      rw [Metric.mem_ball] at h2 h3
      linarith [dist_triangle_right ((x : s) : L2N) ((x' : s) : L2N) (c x')]
    have := htf.to_subtype
    have : Finite {x : s | κ x ≤ L} :=
      Finite.of_injective (fun x => (⟨c x, hct x⟩ : t)) fun x x' h => hinj (congrArg Subtype.val h)
    exact Set.toFinite _
  -- the index set is infinite
  have hinf : Infinite s := by
    by_contra hfs
    rw [not_infinite_iff_finite] at hfs
    have := Fintype.ofFinite s
    exact not_finiteDimensional_L2N (b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite)
  obtain ⟨e, he⟩ := exists_equiv_monotone κ hfin
  refine ⟨fun j => u (e j), fun j => κ (e j), fun j => hκ _, he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tendsto_atTop]
    intro L
    have hf : {j : ℕ | κ (e j) ≤ L}.Finite := (hfin L).preimage e.injective.injOn
    have := hf.eventually_cofinite_notMem
    rw [Nat.cofinite_eq_atTop] at this
    filter_upwards [this] with j hj
    simp only [not_le] at hj
    exact hj.le
  · intro i j
    rw [hJu, hJu]
    by_cases h : i = j
    · subst h; simp [ho.1]
    · rw [ite_eq_right_iff.2 (fun h' => absurd h' h), ho.2 (fun h' => h (e.injective h'))]
  · intro y hy
    have : b.repr y = 0 := by
      ext x
      rw [b.repr_apply_apply, hb]
      obtain ⟨j, rfl⟩ := e.surjective x
      have := hy j
      rw [hJu] at this
      simpa using this
    simpa using congrArg b.repr.symm this
  · exact fun j v => heq _ v
  · exact fun j i => hev _ i
  · intro h
    have := (e.hasSum_iff (f := fun x => (κ x)⁻¹ * ⟪(x : L2N), h⟫_ℝ ^ 2)).2 (hexp h)
    convert this using 1
    funext j
    simp only [Function.comp_apply, hJu]

end gen

end SharpLSI
