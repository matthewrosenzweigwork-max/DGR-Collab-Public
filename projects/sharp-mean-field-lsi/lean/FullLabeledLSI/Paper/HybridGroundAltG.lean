import FullLabeledLSI.Paper.HybridGroundAltF

/-!
# Hybrid inequality (7.17), alternative route, part G: `v_R` in flat form

`vR A lam R (zext G) = ∑_{m<J} λ_{m+1}(¼ (T G)_m² - ½ T_mm + ½ G_m (T G)_m)` and, for the flat
quadratic form `S = Gcᵀ T Gc`, `vflat S λ' g = vR A lam R (zext (Gc g))`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal ContDiff

noncomputable section

namespace SharpLSI.FL.HLA

open SharpLSI SharpLSI.FL.Gross

section vR
variable {d : ℕ} {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}
  (A : FiniteRankApprox W μ e) {R J : ℕ} (hJ : ∀ i ∈ A.s R, i < J)

omit hJ in
theorem sum_sR_eq {f : ℕ → ℝ} (hf : ∀ m, m ∉ A.s R → f m = 0) (hJ : ∀ i ∈ A.s R, i < J) :
    ∑ m ∈ A.s R, f m = ∑ m : Fin J, f m := by
  rw [Finset.sum_range (fun m => f m) |>.symm]
  refine Finset.sum_subset (fun i hi => Finset.mem_range.2 (hJ i hi)) fun m _ hm => hf m hm

omit hJ in
theorem sum_inner_zext (hJ : ∀ i ∈ A.s R, i < J) (G : Fin J → ℝ) (m : ℕ) :
    ∑ j ∈ A.s R, A.a R m j * zext G j = if h : m < J then (Tm A R J *ᵥ G) ⟨m, h⟩ else 0 := by
  by_cases hm : m < J
  · rw [dif_pos hm]
    have : ∀ j : ℕ, j ∉ A.s R → A.a R m j * zext G j = 0 := fun j hj => by
      rw [A.supp R m j (Or.inr hj)]; ring
    rw [sum_sR_eq A (f := fun j => A.a R m j * zext G j) this hJ]
    simp only [mulVec, dotProduct, Tm_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simp [zext]
  · rw [dif_neg hm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : m ∉ A.s R := fun h => hm (hJ m h)
    rw [A.supp R m j (Or.inl this)]; ring

include hJ in
theorem vR_zext_eq (lam : ℕ → ℝ) (G : Fin J → ℝ) :
    vR A lam R (zext G) = ∑ m : Fin J, lam ((m : ℕ) + 1) *
      ((1 / 4) * (Tm A R J *ᵥ G) m ^ 2 - (1 / 2) * Tm A R J m m +
        (1 / 2) * (G m * (Tm A R J *ᵥ G) m)) := by
  have hz : ∀ m : Fin J, zext G m = G m := fun m => by simp [zext]
  have hinner : ∀ m : Fin J, ∑ j ∈ A.s R, A.a R m j * zext G j = (Tm A R J *ᵥ G) m := fun m => by
    rw [sum_inner_zext A hJ G m, dif_pos m.2]
  have hout : ∀ m : ℕ, m ∉ A.s R → ∑ j ∈ A.s R, A.a R m j * zext G j = 0 := fun m hm =>
    Finset.sum_eq_zero fun j _ => by rw [A.supp R m j (Or.inl hm)]; ring
  unfold vR
  have e1 : ∑ m ∈ A.s R, lam (m + 1) * (∑ j ∈ A.s R, A.a R m j * zext G j) ^ 2 =
      ∑ m : Fin J, lam ((m : ℕ) + 1) * (Tm A R J *ᵥ G) m ^ 2 := by
    rw [sum_sR_eq A (f := fun m => lam (m + 1) * (∑ j ∈ A.s R, A.a R m j * zext G j) ^ 2)
      (fun m hm => by simp [hout m hm]) hJ]
    exact Finset.sum_congr rfl fun m _ => by rw [hinner m]
  have e2 : ∑ m ∈ A.s R, A.a R m m * lam (m + 1) = ∑ m : Fin J, Tm A R J m m * lam ((m : ℕ) + 1) := by
    rw [sum_sR_eq A (f := fun m => A.a R m m * lam (m + 1))
      (fun m hm => by simp [A.supp R m m (Or.inl hm)]) hJ]
    rfl
  have e3 : ∑ i ∈ A.s R, ∑ j ∈ A.s R, zext G i * lam (i + 1) * A.a R i j * zext G j =
      ∑ i : Fin J, G i * lam ((i : ℕ) + 1) * (Tm A R J *ᵥ G) i := by
    have : ∀ i : ℕ, ∑ j ∈ A.s R, zext G i * lam (i + 1) * A.a R i j * zext G j =
        zext G i * lam (i + 1) * ∑ j ∈ A.s R, A.a R i j * zext G j := fun i => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [this]
    rw [sum_sR_eq A (f := fun i => zext G i * lam (i + 1) * ∑ j ∈ A.s R, A.a R i j * zext G j)
      (fun i hi => by simp [hout i hi]) hJ]
    exact Finset.sum_congr rfl fun i _ => by rw [hinner i, hz i]
  rw [e1, e2, e3, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

end vR

section flatS
variable {N J : ℕ} (B : Finset (Fin N)) (Tmat : Matrix (Fin J) (Fin J) ℝ)

theorem Gcm_apply' (m : Fin J) (k : Fin (N * J)) :
    Gcm J B m k = if flatMode k = m ∧ flatLab k ∉ B then (Real.sqrt (lowN N B))⁻¹ else 0 := rfl

theorem Gcm_T_mulVec (v : Fin J → ℝ) (k : Fin (N * J)) :
    ((Gcm J B)ᵀ *ᵥ v) k = if flatLab k ∉ B then (Real.sqrt (lowN N B))⁻¹ * v (flatMode k) else 0 := by
  simp only [mulVec, dotProduct, transpose_apply, Gcm_apply']
  by_cases h : flatLab k ∈ B
  · simp [h]
  · simp only [h, not_false_eq_true, and_true, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp [h]

theorem Sq_mulVec (g : Fin (N * J) → ℝ) (k : Fin (N * J)) :
    (((Gcm J B)ᵀ * Tmat * Gcm J B) *ᵥ g) k =
      if flatLab k ∉ B then (Real.sqrt (lowN N B))⁻¹ * (Tmat *ᵥ Gc J B g) (flatMode k) else 0 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact Gcm_T_mulVec B _ k

theorem Sq_diag (hB : B.card < N) (k : Fin (N * J)) :
    (((Gcm J B)ᵀ * Tmat * Gcm J B)) k k =
      if flatLab k ∉ B then (lowN N B)⁻¹ * Tmat (flatMode k) (flatMode k) else 0 := by
  have hn := lowN_pos hB
  simp only [Matrix.mul_apply, transpose_apply, Gcm_apply']
  by_cases h : flatLab k ∈ B
  · simp [h]
  · simp only [h, not_false_eq_true, and_true]
    simp only [ite_mul, zero_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    have hc : (Real.sqrt (lowN N B))⁻¹ * (Real.sqrt (lowN N B))⁻¹ = (lowN N B)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hn.le]
    rw [if_pos trivial, ← hc]
    ring

theorem vflat_eq_sum (hB : B.card < N) (lam : ℕ → ℝ) (g : Fin (N * J) → ℝ) :
    vflat ((Gcm J B)ᵀ * Tmat * Gcm J B) (fun k => lam ((flatMode k : ℕ) + 1)) g =
      ∑ m : Fin J, lam ((m : ℕ) + 1) *
        ((1 / 4) * (Tmat *ᵥ Gc J B g) m ^ 2 - (1 / 2) * Tmat m m +
          (1 / 2) * (Gc J B g m * (Tmat *ᵥ Gc J B g) m)) := by
  have hn := lowN_pos hB
  have hc : (Real.sqrt (lowN N B))⁻¹ * (Real.sqrt (lowN N B))⁻¹ = (lowN N B)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hn.le]
  unfold vflat
  simp only [Sq_mulVec, Sq_diag B Tmat hB]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [flatLab, flatMode, Equiv.symm_apply_apply]
  have hcard : ∑ i ∈ Bᶜ, (lowN N B)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, ← lowN_eq_card_compl]
    field_simp
  have hG : Gc J B g m = (Real.sqrt (lowN N B))⁻¹ * ∑ i ∈ Bᶜ, g (finProdFinEquiv (i, m)) :=
    Gc_apply B g m
  have e1 : ∀ i : Fin N, lam ((m : ℕ) + 1) *
      ((1 / 2 * (g (finProdFinEquiv (i, m)) *
          if i ∉ B then (Real.sqrt (lowN N B))⁻¹ * (Tmat *ᵥ Gc J B g) m else 0) -
        1 / 2 * (if i ∉ B then (lowN N B)⁻¹ * Tmat m m else 0)) +
        1 / 4 * ((if i ∉ B then (Real.sqrt (lowN N B))⁻¹ * (Tmat *ᵥ Gc J B g) m else 0) *
          if i ∉ B then (Real.sqrt (lowN N B))⁻¹ * (Tmat *ᵥ Gc J B g) m else 0)) =
      if i ∈ Bᶜ then lam ((m : ℕ) + 1) * ((1 / 2 * (Tmat *ᵥ Gc J B g) m) *
          ((Real.sqrt (lowN N B))⁻¹ * g (finProdFinEquiv (i, m))) -
        1 / 2 * Tmat m m * (lowN N B)⁻¹ + 1 / 4 * (Tmat *ᵥ Gc J B g) m ^ 2 * (lowN N B)⁻¹) else 0 := by
    intro i
    by_cases hi : i ∈ B
    · simp [hi]
    · have : i ∈ Bᶜ := by simpa using hi
      simp only [hi, this, not_false_eq_true, if_true]
      rw [← hc]; ring
  simp_rw [e1]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hcard]
  rw [hG]; ring


theorem vflat_eq_vR {d : ℕ} {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)}
    {e : ℕ → Torus d → ℝ} (A : FiniteRankApprox W μ e) {R : ℕ} (hJ : ∀ i ∈ A.s R, i < J)
    (hB : B.card < N) (lam : ℕ → ℝ) (g : Fin (N * J) → ℝ) :
    vflat ((Gcm J B)ᵀ * Tm A R J * Gcm J B) (fun k => lam ((flatMode k : ℕ) + 1)) g =
      vR A lam R (zext (Gc J B g)) := by
  rw [vflat_eq_sum B (Tm A R J) hB, vR_zext_eq A hJ]

end flatS

end SharpLSI.FL.HLA

end
