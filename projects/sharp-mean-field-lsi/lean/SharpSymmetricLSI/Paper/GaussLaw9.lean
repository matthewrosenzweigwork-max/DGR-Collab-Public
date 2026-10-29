import SharpSymmetricLSI.Paper.GaussLaw8
import SharpSymmetricLSI.Paper.Prop21Conclusion
import SharpSymmetricLSI.Paper.CenteredEntropy
import SharpSymmetricLSI.Paper.EnergyParseval1

/-!
# R27: `I + T ≥ σ` on the finite sections from Proposition 2.1

For `h = ∑_{i<n} y_i e_{i+1} ∈ L²_0(μ)`: `∫ h² = ‖y‖²` and `∫ h T h = ∑_{i,j<n} T_{ij} y_i y_j`,
so the bound `σ ∫ h² ≤ ⟨h,(I+T)h⟩` of `Prop21Conclusion` is `σ‖y‖² ≤ ‖y‖² + ⟨y, T_n y⟩`.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped InnerProductSpace

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
  (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)

/-- `h = ∑_{i<n} y_i e_{i+1}`. -/
def finComb (e : ℕ → Torus d → ℝ) {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) (x : Torus d) : ℝ :=
  ∑ i : Fin n, y i * e (i + 1) x

include he in
theorem memL20_finComb {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) :
    MemL20 (μ : Measure (Torus d)) (finComb e y) := by
  refine ⟨memLp_finsetSum (f := fun (i : Fin n) x => y i * e (i + 1) x) _
    fun i _ => (he.memLp _).const_mul _, ?_⟩
  unfold finComb
  rw [integral_finsetSum _ fun i _ => ((he.memLp _).integrable one_le_two).const_mul _]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_const_mul]
  have h := he.orthonormal (i + 1) 0
  simp only [he.zero, mul_one, Nat.add_one_ne_zero, ↓reduceIte] at h
  rw [h, mul_zero]

include he in
theorem integral_finComb_sq {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) :
    ∫ x, finComb e y x * finComb e y x ∂(μ : Measure (Torus d)) = ‖y‖ ^ 2 := by
  have hint : ∀ i j : Fin n, Integrable (fun x => y i * e (i + 1) x * (y j * e (j + 1) x))
      (μ : Measure (Torus d)) := fun i j => by
    have := ((he.memLp (i + 1)).integrable_mul (he.memLp (j + 1))).const_mul (y i * y j)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]; ring
  unfold finComb
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  rw [Finset.sum_eq_single i]
  · have : ∀ x, y i * e (i + 1) x * (y i * e (i + 1) x) = y i ^ 2 * (e (i + 1) x * e (i + 1) x) :=
      fun x => by ring
    simp_rw [this]
    rw [integral_const_mul, he.orthonormal]
    simp
  · intro j _ hji
    have : ∀ x, y i * e (i + 1) x * (y j * e (j + 1) x) = y i * y j * (e (i + 1) x * e (j + 1) x) :=
      fun x => by ring
    simp_rw [this]
    rw [integral_const_mul, he.orthonormal]
    have h1 : ¬((i : ℕ) + 1 = j + 1) := fun h => hji (Fin.ext (by omega))
    simp only [h1, ↓reduceIte, mul_zero]
  · simp

section top
variable (μ) in
/-- `k_j(x) = ∫ K(x,y) e_{j+1}(y) dμ(y)`. -/
noncomputable def kCoef (W : Torus d → Torus d → ℝ) (e : ℕ → Torus d → ℝ) (j : ℕ) (x : Torus d) : ℝ :=
  ∫ y, centeredKernel W μ x y * e (j + 1) y ∂(μ : Measure (Torus d))

include hyp he

theorem kCoef_props (j : ℕ) : AEStronglyMeasurable (kCoef μ W e j) (μ : Measure (Torus d)) ∧
    ∃ c, ∀ x, ‖kCoef μ W e j x‖ ≤ c := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨B, hB⟩ := centeredKernel_bdd hyp μm
  have hK := measurable_centeredKernel hyp μm
  have hei : Integrable (e (j + 1)) μm := (he.memLp _).integrable one_le_two
  refine ⟨?_, B * ∫ y, |e (j + 1) y| ∂μm, fun x => ?_⟩
  · have h : AEStronglyMeasurable (fun p : Torus d × Torus d =>
        centeredKernel W μ p.1 p.2 * e (j + 1) p.2) (μm.prod μm) :=
      hK.aestronglyMeasurable.mul (he.memLp (j + 1)).aestronglyMeasurable.comp_snd
    exact h.integral_prod_right'
  · rw [Real.norm_eq_abs, kCoef, ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun _ => abs_nonneg _) (hei.abs.const_mul _)
      (Eventually.of_forall fun y => ?_))
    dsimp only
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hB x y) (abs_nonneg _)

theorem integrable_kernel_mul (x : Torus d) (j : ℕ) :
    Integrable (fun y => centeredKernel W μ x y * e (j + 1) y) (μ : Measure (Torus d)) := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨B, hB⟩ := centeredKernel_bdd hyp μm
  have hK := measurable_centeredKernel hyp μm
  exact ((he.memLp _).integrable one_le_two).bdd_mul
    (hK.comp measurable_prodMk_left).aestronglyMeasurable
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB x y)

theorem integrable_e_mul_kCoef (i j : ℕ) :
    Integrable (fun x => e (i + 1) x * kCoef μ W e j x) (μ : Measure (Torus d)) := by
  obtain ⟨hm, c, hc⟩ := kCoef_props hyp he j
  have := ((he.memLp (i + 1)).integrable one_le_two).bdd_mul hm (Eventually.of_forall hc)
  exact this.congr (Eventually.of_forall fun x => by simp only; ring)

omit hyp he in
theorem integral_e_mul_kCoef (i j : ℕ) :
    ∫ x, e (i + 1) x * kCoef μ W e j x ∂(μ : Measure (Torus d)) = Tmat W μ e i j := by
  unfold Tmat kCoef
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only; ring

theorem Top_finComb {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) (x : Torus d) :
    Top W μ (finComb e y) x = ∑ j : Fin n, y j * kCoef μ W e j x := by
  rw [Top_eq_integral hyp (μ : Measure (Torus d)) (memL20_finComb he y) x]
  unfold finComb kCoef
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun (j : Fin n) _ =>
    ((integrable_kernel_mul hyp he x j).const_mul (y j)).congr
      (Eventually.of_forall fun z => by simp only; ring)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only; ring

theorem integral_finComb_Top {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => finComb e y x * Top W μ (finComb e y) x) (μ : Measure (Torus d)) ∧
    ∫ x, finComb e y x * Top W μ (finComb e y) x ∂(μ : Measure (Torus d)) =
      ⟪y, secOp (Tmat W μ e) n y⟫_ℝ := by
  have hpt : ∀ x, finComb e y x * Top W μ (finComb e y) x =
      ∑ i : Fin n, ∑ j : Fin n, y i * y j * (e (i + 1) x * kCoef μ W e j x) := fun x => by
    rw [Top_finComb hyp he, finComb, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint : ∀ i j : Fin n, Integrable (fun x => y i * y j * (e (i + 1) x * kCoef μ W e j x))
      (μ : Measure (Torus d)) := fun i j => (integrable_e_mul_kCoef hyp he i j).const_mul _
  simp_rw [hpt]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j,
    inner_secOp_self]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_e_mul_kCoef]
  ring

/-- **`I + T ≥ σ` on the finite sections.** -/
theorem secOp_ge_of_prop21 (h21 : Prop21Conclusion V W μ) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ n (y : EuclideanSpace ℝ (Fin n)),
      σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp (Tmat W μ e) n y⟫_ℝ := by
  obtain ⟨σ, hσ0, hσ⟩ := h21.sigma
  refine ⟨σ, hσ0, fun n y => ?_⟩
  have h := hσ _ (memL20_finComb he y)
  have hsq : ∀ x, finComb e y x ^ 2 = finComb e y x * finComb e y x := fun x => sq _
  simp_rw [hsq] at h
  rw [integral_finComb_sq he] at h
  obtain ⟨hi, heq⟩ := integral_finComb_Top hyp he y
  have hhh : Integrable (fun x => finComb e y x * finComb e y x) (μ : Measure (Torus d)) :=
    (memL20_finComb he y).1.integrable_mul (memL20_finComb he y).1
  unfold secondVar at h
  simp_rw [mul_add] at h
  rw [integral_add hhh hi, integral_finComb_sq he, heq] at h
  exact h

end top

end SharpLSI
