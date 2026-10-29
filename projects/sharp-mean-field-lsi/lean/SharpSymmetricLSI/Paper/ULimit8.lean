import SharpSymmetricLSI.Paper.ULimit7

/-!
# The decomposition `U_N = ½ ∑ T_{ab} Z_a Z_b + (diagonal) + (off-diagonal remainder)`
(Phase 3, lane D; R26)
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

section decomp
variable {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
  {κ : α → α → ℝ} {e : ℕ → α → ℝ} {T : ℕ → ℕ → ℝ}

/-- `U_N` for a general kernel. -/
def Ugen (κ : α → α → ℝ) (N : ℕ) (X : Fin N → α) : ℝ :=
  1 / (2 * (N : ℝ)) * ∑ i, ∑ j, κ (X i) (X j)

/-- The off-diagonal part `N^{-1} ∑_{i<j} κ(X_i, X_j)`. -/
def offDiag (κ : α → α → ℝ) (N : ℕ) (X : Fin N → α) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, ∑ j, if i < j then κ (X i) (X j) else 0

/-- The normalized sums `Z_a = N^{-1/2} ∑_l e_{a+1}(X_l)`. -/
def zSum (e : ℕ → α → ℝ) (N a : ℕ) (X : Fin N → α) : ℝ :=
  (√(N : ℝ))⁻¹ * ∑ l, e (a + 1) (X l)

theorem Ugen_eq_offDiag_add {κ : α → α → ℝ} (hs : ∀ x y, κ x y = κ y x) (N : ℕ) (X : Fin N → α) :
    Ugen κ N X = offDiag κ N X + (2 * (N : ℝ))⁻¹ * ∑ i, κ (X i) (X i) := by
  unfold Ugen offDiag
  rw [sum_sum_symm_eq (f := fun i j => κ (X i) (X j)) fun i j => hs _ _]
  rcases eq_or_ne (N : ℝ) 0 with h | h
  · simp [h]
  · field_simp

theorem Ugen_sub (κ₁ κ₂ : α → α → ℝ) (N : ℕ) (X : Fin N → α) :
    Ugen (fun x y => κ₁ x y - κ₂ x y) N X = Ugen κ₁ N X - Ugen κ₂ N X := by
  unfold Ugen
  simp only [Finset.sum_sub_distrib, mul_sub]

theorem sum_four_comm {ι κ' : Type*} (s : Finset ι) (t : Finset κ') (f : ι → ι → κ' → κ' → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, ∑ a ∈ t, ∑ b ∈ t, f i j a b = ∑ a ∈ t, ∑ b ∈ t, ∑ i ∈ s, ∑ j ∈ s, f i j a b := by
  calc ∑ i ∈ s, ∑ j ∈ s, ∑ a ∈ t, ∑ b ∈ t, f i j a b
      = ∑ i ∈ s, ∑ a ∈ t, ∑ j ∈ s, ∑ b ∈ t, f i j a b :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a ∈ t, ∑ i ∈ s, ∑ j ∈ s, ∑ b ∈ t, f i j a b := Finset.sum_comm
    _ = ∑ a ∈ t, ∑ i ∈ s, ∑ b ∈ t, ∑ j ∈ s, f i j a b :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a ∈ t, ∑ b ∈ t, ∑ i ∈ s, ∑ j ∈ s, f i j a b :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem Ugen_kTrunc {N : ℕ} (hN : 1 ≤ N) (R : ℕ) (X : Fin N → α) :
    Ugen (kTrunc T e R) N X = 1 / 2 * ∑ a ∈ Finset.range R, ∑ b ∈ Finset.range R,
      T a b * (zSum e N a X * zSum e N b X) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : (√(N : ℝ))⁻¹ * (√(N : ℝ))⁻¹ = (N : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hN'.le]
  have e1 : ∀ a b, zSum e N a X * zSum e N b X =
      (N : ℝ)⁻¹ * ∑ i, ∑ j, e (a + 1) (X i) * e (b + 1) (X j) := fun a b => by
    unfold zSum; rw [← hsq, ← Finset.sum_mul_sum]; ring
  unfold Ugen kTrunc
  rw [sum_four_comm (f := fun i j a b => T a b * (e (a + 1) (X i) * e (b + 1) (X j)))]
  simp_rw [e1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  field_simp

/-- **The decomposition.** -/
theorem Ugen_decomp (hD : KerData ν κ e T) {N : ℕ} (hN : 1 ≤ N) (R : ℕ) (X : Fin N → α) :
    Ugen κ N X = 1 / 2 * ∑ a ∈ Finset.range R, ∑ b ∈ Finset.range R,
        T a b * (zSum e N a X * zSum e N b X) +
      1 / 2 * ((∑ i, (κ (X i) (X i) - kTrunc T e R (X i) (X i))) / N) +
      offDiag (fun x y => κ x y - kTrunc T e R x y) N X := by
  have hs' : ∀ x y, κ x y - kTrunc T e R x y = κ y x - kTrunc T e R y x := fun x y => by
    rw [hD.symm, hD.kTrunc_symm]
  have h1 := Ugen_sub κ (kTrunc T e R) N X
  rw [Ugen_eq_offDiag_add hs', Ugen_kTrunc hN] at h1
  have hN' : (N : ℝ) ≠ 0 := by positivity
  rw [eq_sub_iff_add_eq] at h1
  rw [← h1]
  field_simp
  ring

/-- The pair laws of a product measure, for `MemLp`. -/
theorem memLp_pair_pi {N : ℕ} {κ' : α → α → ℝ}
    (hL : MemLp (fun p : α × α => κ' p.1 p.2) 2 (ν.prod ν)) {i j : Fin N} (hij : i ≠ j) :
    MemLp (fun X : Fin N → α => κ' (X i) (X j)) 2 (Measure.pi fun _ : Fin N => ν) := by
  have h0 : MemLp (fun q : α × α => κ' q.1 q.2) 2
      ((Measure.pi fun _ : Fin N => ν).map fun X => (X i, X j)) := by
    haveI := nonempty_of_isProbabilityMeasure ν
    rw [map_pair_pi_gen hij]; exact hL
  exact h0.comp_of_map (by fun_prop)

theorem memLp_offDiag {N : ℕ} {κ' : α → α → ℝ}
    (hL : MemLp (fun p : α × α => κ' p.1 p.2) 2 (ν.prod ν)) :
    MemLp (offDiag κ' N) 2 (Measure.pi fun _ : Fin N => ν) := by
  unfold offDiag
  refine (memLp_finsetSum _ fun i _ => memLp_finsetSum
    (f := fun j (X : Fin N → α) => if i < j then κ' (X i) (X j) else 0) _ fun j _ => ?_).const_mul _
  by_cases h : i < j
  · simp only [h, ite_true]; exact memLp_pair_pi hL h.ne
  · simp only [h, ite_false]; exact MemLp.zero

/-- `E|offDiag|² ≤ ½ ‖κ'‖²`. -/
theorem integral_offDiag_sq_le {N : ℕ} (hN : 1 ≤ N) {κ' : α → α → ℝ}
    (hm : AEStronglyMeasurable (Function.uncurry κ') (ν.prod ν)) (hs : ∀ x y, κ' x y = κ' y x)
    (hcent : ∀ w, ∫ y, κ' y w ∂ν = 0)
    (hL : MemLp (fun p : α × α => κ' p.1 p.2) 2 (ν.prod ν)) :
    ∫ X, offDiag κ' N X ^ 2 ∂(Measure.pi fun _ : Fin N => ν) ≤
      1 / 2 * ∫ p, κ' p.1 p.2 ^ 2 ∂(ν.prod ν) := by
  haveI := nonempty_of_isProbabilityMeasure ν
  unfold offDiag
  simp_rw [mul_pow]
  rw [integral_const_mul, integral_offdiag_sq hm hs (Eventually.of_forall hcent) hL.integrable_sq]
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : 0 ≤ ∫ p, κ' p.1 p.2 ^ 2 ∂(ν.prod ν) := integral_nonneg fun _ => sq_nonneg _
  have e : ((N : ℝ)⁻¹) ^ 2 * (N * (N - 1) / 2 * ∫ p, κ' p.1 p.2 ^ 2 ∂(ν.prod ν)) =
      (1 - (N : ℝ)⁻¹) * (1 / 2 * ∫ p, κ' p.1 p.2 ^ 2 ∂(ν.prod ν)) := by
    field_simp
  rw [e]
  have : 0 ≤ (N : ℝ)⁻¹ := by positivity
  nlinarith

end decomp

end SharpLSI
