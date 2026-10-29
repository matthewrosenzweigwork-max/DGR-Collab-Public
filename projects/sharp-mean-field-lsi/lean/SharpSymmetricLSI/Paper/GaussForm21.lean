import SharpSymmetricLSI.Paper.GaussForm20
import SharpSymmetricLSI.Vendor.TauCeti.Analysis.InnerProductSpace.Variational.Rayleigh

/-!
# R32 (F2): the generalized eigenproblem `(I+T)u = κ Λ⁻¹ u` on `ℓ²`

* `diagOp`: the diagonal operator `x ↦ (d_i x_i)` for bounded `d`; compact when `d_i → 0`
  (`isCompactOperator_diagOp`), with dense range when all `d_i ≠ 0` (`denseRange_diagOp`).
* `formB`: the bounded bilinear form `B(u,v) = ⟨u, (I+T)v⟩`, coercive under `I + T_n ≥ σ`.
* `exists_genEigen_set`: TauCeti's variational spectral theorem with `J = diag(λ'^{-1/2})` gives a
  Hilbert basis `J u_x` of `ℓ²` with `u_x + T u_x = κ_x Λ⁻¹ u_x`, `κ_x > 0`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace SharpLSI

/-- `‖y‖ ≤ c‖x‖` from coordinatewise `y_i² ≤ c² x_i²`. -/
theorem norm_le_of_sq_le {x y : L2N} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, y i ^ 2 ≤ c ^ 2 * x i ^ 2) :
    ‖y‖ ≤ c * ‖x‖ := by
  have h1 : ‖y‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by
    rw [norm_sq_L2N, mul_pow, norm_sq_L2N, ← tsum_mul_left]
    exact (summable_sq_L2N y).tsum_le_tsum h ((summable_sq_L2N x).mul_left _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1

theorem inner_single_L2N_right (x : L2N) (i : ℕ) (a : ℝ) :
    ⟪x, lp.single 2 i a⟫_ℝ = x i * a := by
  rw [lp.inner_single_right (𝕜 := ℝ)]; simp [mul_comm]

theorem inner_single_L2N_left (x : L2N) (i : ℕ) (a : ℝ) :
    ⟪lp.single 2 i a, x⟫_ℝ = a * x i := by
  rw [lp.inner_single_left (𝕜 := ℝ)]; simp [mul_comm]

/-! ### Diagonal operators -/

section diag
variable {d : ℕ → ℝ} {D : ℝ} (hd : ∀ i, |d i| ≤ D)
include hd

theorem sq_le_of_abs_le (i : ℕ) : d i ^ 2 ≤ D ^ 2 := by
  have := pow_le_pow_left₀ (abs_nonneg _) (hd i) 2; rwa [sq_abs] at this

theorem summable_diag_sq (x : L2N) : Summable fun i => (d i * x i) ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun i => by rw [mul_pow]; exact mul_le_mul_of_nonneg_right (sq_le_of_abs_le hd i) (sq_nonneg _))
    ((summable_sq_L2N x).mul_left (D ^ 2))

/-- The diagonal linear map. -/
noncomputable def diagLin : L2N →ₗ[ℝ] L2N where
  toFun x := mkL2N (fun i => d i * x i) (summable_diag_sq hd x)
  map_add' x y := by ext i; simp [mul_add]
  map_smul' c x := by ext i; simp only [mkL2N_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    RingHom.id_apply]; ring

/-- **The diagonal operator** `x ↦ (d_i x_i)`. -/
noncomputable def diagOp : L2N →L[ℝ] L2N :=
  (diagLin hd).mkContinuous D fun x => norm_le_of_sq_le ((abs_nonneg _).trans (hd 0)) fun i => by
    show (d i * x i) ^ 2 ≤ D ^ 2 * x i ^ 2
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right (sq_le_of_abs_le hd i) (sq_nonneg _)

theorem diagOp_apply (x : L2N) (i : ℕ) : diagOp hd x i = d i * x i := rfl

theorem diagOp_single (i : ℕ) (a : ℝ) : diagOp hd (lp.single 2 i a) = lp.single 2 i (d i * a) := by
  ext j
  rw [diagOp_apply, lp.single_apply, lp.single_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem inner_diagOp_comm (x y : L2N) : ⟪x, diagOp hd y⟫_ℝ = ⟪diagOp hd x, y⟫_ℝ := by
  rw [inner_L2N, inner_L2N]
  exact tsum_congr fun i => by rw [diagOp_apply, diagOp_apply]; ring

/-- `J` has dense range when no `d_i` vanishes. -/
theorem denseRange_diagOp (hne : ∀ i, d i ≠ 0) : DenseRange (diagOp hd) := by
  rw [DenseRange, show Set.range (diagOp hd) = ((LinearMap.range (diagOp hd : L2N →ₗ[ℝ] L2N) :
      Submodule ℝ L2N) : Set L2N) from (LinearMap.coe_range _).symm,
    Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro y hy
  rw [Submodule.mem_orthogonal] at hy
  ext i
  have h := hy _ ⟨lp.single 2 i 1, rfl⟩
  simp only [ContinuousLinearMap.coe_coe, diagOp_single, mul_one, inner_single_L2N_left] at h
  simpa [hne i] using h

end diag

/-- A diagonal operator with `d_i → 0` is compact. -/
theorem isCompactOperator_diagOp {d : ℕ → ℝ} {D : ℝ} (hd : ∀ i, |d i| ≤ D)
    (hd0 : Tendsto d atTop (𝓝 0)) : IsCompactOperator (diagOp hd) := by
  set dn : ℕ → ℕ → ℝ := fun n i => if i < n then d i else 0 with hdn
  have hdnb : ∀ n i, |dn n i| ≤ D := fun n i => by
    simp only [hdn]; split_ifs
    · exact hd i
    · simpa using (abs_nonneg _).trans (hd 0)
  -- finite rank truncations
  have hcomp : ∀ n, IsCompactOperator (diagOp (hdnb n)) := by
    intro n
    let P : L2N →L[ℝ] (Fin n → ℝ) :=
      ContinuousLinearMap.pi fun i : Fin n => d i • lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 (i : ℕ)
    let E : (Fin n → ℝ) →L[ℝ] L2N := ∑ i : Fin n,
      (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 (i : ℕ)).comp
        (ContinuousLinearMap.proj i)
    have heq : diagOp (hdnb n) = E.comp P := by
      ext x j
      simp only [diagOp_apply, hdn, ContinuousLinearMap.comp_apply, E, P,
        FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply, ContinuousLinearMap.pi_apply,
        lp.singleContinuousLinearMap_apply]
      rw [lp.coeFn_sum, Finset.sum_apply]
      simp only [lp.single_apply]
      split_ifs with hj
      · rw [Finset.sum_eq_single ⟨j, hj⟩]
        · simp [lp.evalCLM]
        · intro b _ hb
          have : (b : ℕ) ≠ j := fun h => hb (Fin.ext h)
          simp [Ne.symm this]
        · simp
      · rw [zero_mul]
        refine (Finset.sum_eq_zero fun b _ => ?_).symm
        have : (b : ℕ) ≠ j := fun h => hj (h ▸ b.isLt)
        simp [Ne.symm this]
    rw [heq]
    exact (isCompactOperator_of_locallyCompactSpace_dom P).clm_comp E
  refine isCompactOperator_of_tendsto (l := atTop) (F := fun n => diagOp (hdnb n)) ?_
    (Eventually.of_forall hcomp)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hd0) (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_)
    (by linarith : ε / 2 < ε)
  refine norm_le_of_sq_le (by positivity) fun i => ?_
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, diagOp_apply, hdn]
  split_ifs with hi
  · simp; positivity
  · have h1 := hN i (by omega)
    rw [Real.dist_eq, sub_zero] at h1
    rw [zero_mul, zero_sub, neg_sq, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have := pow_le_pow_left₀ (abs_nonneg _) h1.le 2
    rwa [sq_abs] at this

/-! ### The form `B(u,v) = ⟨u,(I+T)v⟩` -/

section form
variable {T : ℕ → ℕ → ℝ} (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2)

/-- `B(u, v) = ⟨u, (I + T) v⟩`. -/
noncomputable def formB : L2N →L[ℝ] L2N →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ L2N L2N ℝ).flip (1 + hsOp hS)).comp (innerSL ℝ)

theorem formB_apply (u v : L2N) : formB hS u v = ⟪u, v⟫_ℝ + ⟪u, hsOp hS v⟫_ℝ := by
  simp [formB, inner_add_right]

theorem formB_symm (hT : ∀ i j, T i j = T j i) (u v : L2N) : formB hS u v = formB hS v u := by
  rw [formB_apply, formB_apply, real_inner_comm u v, inner_hsOp_comm hS hT u v,
    real_inner_comm (hsOp hS u) v]

theorem isCoercive_formB {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : ∀ n (y : EuclideanSpace ℝ (Fin n)), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ) :
    IsCoercive (formB hS) := by
  refine ⟨σ, hσ0, fun u => ?_⟩
  rw [formB_apply, real_inner_self_eq_norm_sq, mul_assoc, ← sq]
  exact coercive_hsOp hS hσ u

end form

/-! ### The generalized eigenbasis -/

theorem exists_bound_inv_sqrt {lam' : ℕ → ℝ} (hpos : ∀ i, 0 < lam' i)
    (htop : Tendsto lam' atTop atTop) :
    ∃ D, ∀ i, |(√(lam' i))⁻¹| ≤ D := by
  obtain ⟨N, hN⟩ := (tendsto_atTop.1 htop 1).exists_forall_of_atTop
  refine ⟨∑ i ∈ Finset.range N, (√(lam' i))⁻¹ + 1, fun i => ?_⟩
  have h0 : ∀ j, 0 ≤ (√(lam' j))⁻¹ := fun j => inv_nonneg.2 (Real.sqrt_nonneg _)
  rw [abs_of_nonneg (h0 i)]
  by_cases hi : i < N
  · have := Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_range.2 hi)
    linarith
  · have h1 : 1 ≤ lam' i := hN i (by omega)
    have h2 : (√(lam' i))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt h1)
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.range N) => h0 j
    linarith

theorem tendsto_inv_sqrt {lam' : ℕ → ℝ} (htop : Tendsto lam' atTop atTop) :
    Tendsto (fun i => (√(lam' i))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp htop)

section gen
variable {T : ℕ → ℕ → ℝ} (hT : ∀ i j, T i j = T j i)
  (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) {σ : ℝ} (hσ0 : 0 < σ)
  (hσ : ∀ n (y : EuclideanSpace ℝ (Fin n)), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ)
  {lam' : ℕ → ℝ} (hpos : ∀ i, 0 < lam' i) {D : ℝ} (hD : ∀ i, |(√(lam' i))⁻¹| ≤ D)
include hT hS hσ0 hσ hpos

omit hσ0 hσ hpos in
/-- `B(u, e_i) = u_i + (Tu)_i`. -/
theorem formB_single (u : L2N) (i : ℕ) :
    formB hS u (lp.single 2 i 1) = u i + ∑' k, T i k * u k := by
  rw [formB_apply, inner_single_L2N_right, inner_hsOp_comm hS hT, inner_single_L2N_right,
    hsOp_apply]
  ring

/-- **The generalized eigenbasis, indexed by a set.** -/
theorem exists_genEigen_set (htop : Tendsto lam' atTop atTop) :
    ∃ (s : Set L2N) (b : HilbertBasis s ℝ L2N) (κ : s → ℝ) (u : s → L2N),
      ⇑b = ((↑) : s → L2N) ∧ (∀ x, 0 < κ x) ∧ (∀ x, diagOp hD (u x) = x) ∧
      (∀ x v, formB hS (u x) v = κ x * ⟪diagOp hD (u x), diagOp hD v⟫_ℝ) ∧
      (∀ x i, u x i + ∑' k, T i k * u x k = κ x * u x i / lam' i) ∧
      ∀ h : L2N, HasSum (fun x => (κ x)⁻¹ * ⟪(x : L2N), h⟫_ℝ ^ 2)
        ⟪h, (isCoercive_formB hS hσ0 hσ).formSolutionOperator (diagOp hD) h⟫_ℝ := by
  have hB := isCoercive_formB hS hσ0 hσ
  have hJ := isCompactOperator_diagOp hD (tendsto_inv_sqrt htop)
  have hdense := denseRange_diagOp hD fun i => inv_ne_zero (Real.sqrt_pos.2 (hpos i)).ne'
  obtain ⟨s, b, κ, u, hb, hκ, -, hJu, heq, hexp⟩ :=
    hB.exists_hilbertBasis_forall_apply_eq_smul_inner hJ hdense (formB_symm hS hT)
  refine ⟨s, b, κ, u, hb, hκ, hJu, heq, fun x i => ?_, fun h => ?_⟩
  swap
  · have := (innerSL ℝ h).hasSum (hexp h)
    convert this using 1
    · funext x
      simp only [innerSL_apply_apply, real_inner_smul_right, b.repr_apply_apply, hb]
      rw [real_inner_comm h]; ring
    · exact (innerSL_apply_apply ℝ h _).symm
  have h := heq x (lp.single 2 i 1)
  rw [formB_single hT hS, diagOp_single, inner_single_L2N_right, diagOp_apply] at h
  rw [h]
  have hl : (√(lam' i))⁻¹ * (√(lam' i))⁻¹ = (lam' i)⁻¹ := by
    rw [← sq, inv_pow, Real.sq_sqrt (hpos i).le]
  rw [div_eq_mul_inv, ← hl]
  ring

end gen

end SharpLSI
