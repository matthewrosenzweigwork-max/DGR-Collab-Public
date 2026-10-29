import SharpSymmetricLSI.Paper.ULimit1
import SharpSymmetricLSI.Paper.CondForce1

/-!
# R31 groundwork: the variance of particle force sums ((7.11), conditional centering)

For bounded measurable `c(x,y) ∈ ℝ^d`, centered in `y` under `μ`, and bounded `c_Δ(x)`:
`∫ ∑ᵢ |N⁻¹(∑_{l≠i} c(Xᵢ,X_l) + c_Δ(Xᵢ))|² dμ^{⊗N} = ((N-1)/N)‖c‖² + N⁻¹‖c_Δ‖²`.
All cross terms vanish by centering in the other particle.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

section
variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {n : ℕ}
  {c : Torus d → Torus d → Fin d → ℝ} {cΔ : Torus d → Fin d → ℝ}
  (hcm : ∀ k, Measurable (Function.uncurry fun x y => c x y k))
  (hΔm : ∀ k, Measurable fun x => cΔ x k) {M : ℝ}
  (hcb : ∀ x y k, |c x y k| ≤ M) (hΔb : ∀ x k, |cΔ x k| ≤ M)
  (hcent : ∀ k, ∀ᵐ x ∂μ, ∫ y, c x y k ∂μ = 0)
include hcm hΔm hcb hΔb

omit hΔm hΔb in
theorem integrable_pair_c (k : Fin d) (i l : Fin (n + 1)) :
    Integrable (fun X : Fin (n + 1) → Torus d => c (X i) (X l) k)
      (Measure.pi fun _ : Fin (n + 1) => μ) :=
  integrable_of_bdd (by
    exact (hcm k).comp (by fun_prop : Measurable fun X : Fin (n + 1) → Torus d => (X i, X l)))
    fun X => hcb _ _ k

omit hcm hcb in
theorem integrable_diag_c (k : Fin d) (i : Fin (n + 1)) :
    Integrable (fun X : Fin (n + 1) → Torus d => cΔ (X i) k)
      (Measure.pi fun _ : Fin (n + 1) => μ) :=
  integrable_of_bdd ((hΔm k).comp (measurable_pi_apply i)) fun X => hΔb _ k

include hcent

theorem integral_forceSum_sq_i (i : Fin (n + 1)) (k : Fin d) :
    ∫ X, (∑ l ∈ Finset.univ.erase i, c (X i) (X l) k + cΔ (X i) k) ^ 2
        ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
      n * ∫ x, ∫ y, c x y k ^ 2 ∂μ ∂μ + ∫ x, cΔ x k ^ 2 ∂μ := by
  set P := Measure.pi fun _ : Fin (n + 1) => μ
  set E := Finset.univ.erase i
  have hA := fun l => integrable_pair_c (μ := μ) hcm hcb k i l
  have hD := integrable_diag_c (μ := μ) (n := n) hΔm hΔb k i
  have hAA : ∀ l m, Integrable (fun X : Fin (n + 1) → Torus d => c (X i) (X l) k * c (X i) (X m) k) P :=
    fun l m => (hA m).bdd_mul (hA l).1 (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs]; exact hcb _ _ k)
  have hAD : ∀ l, Integrable (fun X : Fin (n + 1) → Torus d => c (X i) (X l) k * cΔ (X i) k) P :=
    fun l => hD.bdd_mul (hA l).1 (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs]; exact hcb _ _ k)
  have hDD : Integrable (fun X : Fin (n + 1) → Torus d => cΔ (X i) k * cΔ (X i) k) P :=
    hD.bdd_mul hD.1 (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hΔb _ k)
  -- centering in the `l`-th particle
  have hcent' : ∀ᵐ w ∂μ, ∫ y, (fun y w => c w y k) y w ∂μ = 0 := hcent k
  have hzero : ∀ l ∈ E, ∀ (F : (Fin (n + 1) → Torus d) → ℝ),
      (∀ X y, F (Function.update X l y) = F X) →
      Integrable (fun X => c (X i) (X l) k * F X) P →
      ∫ X, c (X i) (X l) k * F X ∂P = 0 := by
    intro l hl F hF hint
    have hli : l ≠ i := Finset.ne_of_mem_erase hl
    exact integral_kernel_mul_eq_zero (κ := fun y w => c w y k) hcent' hli hF hint
  have hsq : ∀ X : Fin (n + 1) → Torus d,
      (∑ l ∈ E, c (X i) (X l) k + cΔ (X i) k) ^ 2 =
        ∑ l ∈ E, ∑ m ∈ E, c (X i) (X l) k * c (X i) (X m) k +
          2 * ∑ l ∈ E, c (X i) (X l) k * cΔ (X i) k + cΔ (X i) k * cΔ (X i) k := fun X => by
    have h : (∑ l ∈ E, c (X i) (X l) k + cΔ (X i) k) ^ 2 =
        (∑ l ∈ E, c (X i) (X l) k) * (∑ l ∈ E, c (X i) (X l) k) +
          2 * ((∑ l ∈ E, c (X i) (X l) k) * cΔ (X i) k) + cΔ (X i) k * cΔ (X i) k := by ring
    rw [h, Finset.sum_mul_sum, Finset.sum_mul]
  simp_rw [hsq]
  have i1 : Integrable (fun X : Fin (n + 1) → Torus d =>
      ∑ l ∈ E, ∑ m ∈ E, c (X i) (X l) k * c (X i) (X m) k) P :=
    integrable_finset_sum _ fun l _ => integrable_finset_sum _ fun m _ => hAA l m
  have i2 : Integrable (fun X : Fin (n + 1) → Torus d =>
      2 * ∑ l ∈ E, c (X i) (X l) k * cΔ (X i) k) P :=
    (integrable_finset_sum _ fun l _ => hAD l).const_mul 2
  rw [integral_add (f := fun X : Fin (n + 1) → Torus d =>
      ∑ l ∈ E, ∑ m ∈ E, c (X i) (X l) k * c (X i) (X m) k +
        2 * ∑ l ∈ E, c (X i) (X l) k * cΔ (X i) k) (i1.add i2) hDD,
    integral_add i1 i2, integral_finsetSum _ fun l _ =>
    integrable_finset_sum _ fun m _ => hAA l m, integral_const_mul,
    integral_finsetSum _ fun l _ => hAD l]
  have hAAv : ∀ l ∈ E, ∀ m ∈ E, ∫ X, c (X i) (X l) k * c (X i) (X m) k ∂P =
      if l = m then ∫ x, ∫ y, c x y k ^ 2 ∂μ ∂μ else 0 := by
    intro l hl m hm
    split_ifs with hlm
    · subst hlm
      have hli : l ≠ i := Finset.ne_of_mem_erase hl
      have hmap := map_pair_pi_gen (μ := μ) (N := n + 1) hli.symm
      have hfm : Measurable fun q : Torus d × Torus d => c q.1 q.2 k ^ 2 := (hcm k).pow_const 2
      calc ∫ X, c (X i) (X l) k * c (X i) (X l) k ∂P
          = ∫ X, (fun q : Torus d × Torus d => c q.1 q.2 k ^ 2) (X i, X l) ∂P := by
            simp only [sq]
        _ = ∫ q, c q.1 q.2 k ^ 2 ∂(μ.prod μ) := by
            rw [← hmap, integral_map (by fun_prop) hfm.aestronglyMeasurable]
        _ = _ := integral_prod _ (integrable_of_bdd hfm (C := M ^ 2) fun q => by
            rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hcb _ _ k) 2)
    · refine hzero l hl (fun X => c (X i) (X m) k) (fun X y => ?_) (hAA l m)
      have hml : m ≠ l := Ne.symm hlm
      have hil : i ≠ l := Ne.symm (Finset.ne_of_mem_erase hl)
      simp only [Function.update_of_ne hml, Function.update_of_ne hil]
  have hADv : ∀ l ∈ E, ∫ X, c (X i) (X l) k * cΔ (X i) k ∂P = 0 := by
    intro l hl
    refine hzero l hl (fun X => cΔ (X i) k) (fun X y => ?_) (hAD l)
    have hil : i ≠ l := Ne.symm (Finset.ne_of_mem_erase hl)
    simp only [Function.update_of_ne hil]
  have hDDv : ∫ X, cΔ (X i) k * cΔ (X i) k ∂P = ∫ x, cΔ x k ^ 2 ∂μ := by
    have hmp := measurePreserving_eval (fun _ : Fin (n + 1) => μ) i
    simp_rw [← sq]
    have hmap : P.map (fun X : Fin (n + 1) → Torus d => X i) = μ := hmp.map_eq
    have h := integral_map (μ := P) (φ := fun X : Fin (n + 1) → Torus d => X i)
      (measurable_pi_apply i).aemeasurable (f := fun x => cΔ x k ^ 2)
      (by rw [hmap]; exact ((hΔm k).pow_const 2).aestronglyMeasurable)
    rw [hmap] at h
    exact h.symm
  rw [Finset.sum_congr rfl fun l _ => integral_finsetSum _ fun m _ => hAA l m]
  rw [Finset.sum_congr rfl fun l hl => Finset.sum_congr rfl fun m hm => hAAv l hl m hm,
    Finset.sum_congr rfl hADv, hDDv]
  simp only [Finset.sum_ite_eq, Finset.sum_const_zero, mul_zero, add_zero]
  rw [Finset.sum_congr rfl fun l hl => ite_cond_eq_true _ _ (eq_true hl), Finset.sum_const, nsmul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  simp

/-- **The variance identity behind (7.11).** -/
theorem integral_forceSum_sq :
    ∫ X, ∑ i, ∑ k, ((((n + 1 : ℕ) : ℝ))⁻¹ *
        (∑ l ∈ Finset.univ.erase i, c (X i) (X l) k + cΔ (X i) k)) ^ 2
        ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
      (n : ℝ) / (n + 1) * ∫ x, ∫ y, ∑ k, c x y k ^ 2 ∂μ ∂μ +
        (((n + 1 : ℕ) : ℝ))⁻¹ * ∫ x, ∑ k, cΔ x k ^ 2 ∂μ := by
  have hS : ∀ i k, Integrable (fun X : Fin (n + 1) → Torus d =>
      (∑ l ∈ Finset.univ.erase i, c (X i) (X l) k + cΔ (X i) k) ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ) := fun i k => by
    refine integrable_of_bdd (C := ((n + 1) * M) ^ 2) ?_ fun X => ?_
    · refine ((Finset.measurable_sum _ fun l _ => ?_).add ((hΔm k).comp
        (measurable_pi_apply i))).pow_const 2
      exact (hcm k).comp (by fun_prop : Measurable fun X : Fin (n + 1) → Torus d => (X i, X l))
    · rw [abs_pow]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      refine (abs_add_le _ _).trans ?_
      refine (add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (g := fun _ => M) fun l _ => hcb _ _ k)) (hΔb _ k)).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
      have hM : 0 ≤ M := (abs_nonneg _).trans (hΔb (X i) k)
      push_cast; nlinarith
  have hpt : ∀ X : Fin (n + 1) → Torus d, ∑ i, ∑ k, ((((n + 1 : ℕ) : ℝ))⁻¹ *
      (∑ l ∈ Finset.univ.erase i, c (X i) (X l) k + cΔ (X i) k)) ^ 2 =
      ((((n + 1 : ℕ) : ℝ))⁻¹) ^ 2 * ∑ i, ∑ k,
        (∑ l ∈ Finset.univ.erase i, c (X i) (X l) k + cΔ (X i) k) ^ 2 := fun X => by
    simp_rw [mul_pow, Finset.mul_sum]
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum _ fun i _ => integrable_finset_sum _ fun k _ => hS i k]
  rw [Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun k _ => hS i k]
  simp_rw [integral_forceSum_sq_i hcm hΔm hcb hΔb hcent]
  have hc2 : ∀ k, Integrable (fun q : Torus d × Torus d => c q.1 q.2 k ^ 2) (μ.prod μ) := fun k =>
    integrable_of_bdd ((hcm k).pow_const 2) (C := M ^ 2) fun q => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hcb _ _ k) 2
  have hI : ∫ x, ∫ y, ∑ k, c x y k ^ 2 ∂μ ∂μ = ∑ k, ∫ x, ∫ y, c x y k ^ 2 ∂μ ∂μ := by
    rw [← integral_finsetSum _ fun k _ => (hc2 k).integral_prod_left]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    exact integral_finsetSum _ fun k _ => integrable_of_bdd
      (((hcm k).comp measurable_prodMk_left).pow_const 2) (C := M ^ 2) fun y => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hcb _ _ k) 2
  have hJ : ∫ x, ∑ k, cΔ x k ^ 2 ∂μ = ∑ k, ∫ x, cΔ x k ^ 2 ∂μ :=
    integral_finsetSum _ fun k _ => integrable_of_bdd ((hΔm k).pow_const 2) (C := M ^ 2)
      fun x => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hΔb _ k) 2
  rw [hI, hJ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  push_cast
  field_simp

end

end SharpLSI
