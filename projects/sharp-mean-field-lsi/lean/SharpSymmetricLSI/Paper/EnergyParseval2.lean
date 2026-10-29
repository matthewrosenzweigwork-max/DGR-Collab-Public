import SharpSymmetricLSI.Paper.EnergyParseval1
import SharpSymmetricLSI.Paper.LocalStructure1

/-!
# Parseval for the Dirichlet form of a reference eigenbasis (Phase 3, lane D; R24)

`∫|∇f|² dμ = ∑ λᵢ ⟨f, eᵢ⟩²` for `f ∈ H¹(μ)`, when `μ ≪ m` has density bounded below.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

section grad
variable (hac : μ ≪ haar d)
include hac

theorem memLp_grad_comp {f : Torus d → ℝ} (hf : MemH1 μ f) (k : Fin d) :
    MemLp (fun x => weakGrad f x k) 2 μ := by
  have hm : AEStronglyMeasurable (fun x => weakGrad f x k) μ :=
    ((isWeakGrad_weakGrad hf.1).aestronglyMeasurable_grad k).mono_ac hac
  refine hf.2.2.of_le hm (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact abs_le_sqrt_sqNorm _ k

end grad

/-- The Dirichlet pairing `∫ ∇u·∇v dμ` of two vector fields. -/
def dirPair (μ : Measure (Torus d)) (u v : Torus d → Fin d → ℝ) : ℝ := ∫ x, ∑ k, u x k * v x k ∂μ

theorem dirPair_integrable {u v : Torus d → Fin d → ℝ} (hu : ∀ k, MemLp (fun x => u x k) 2 μ)
    (hv : ∀ k, MemLp (fun x => v x k) 2 μ) : Integrable (fun x => ∑ k, u x k * v x k) μ :=
  integrable_finset_sum _ fun k _ => (hu k).integrable_mul (hv k)

theorem dirPair_sum_left {u : ℕ → Torus d → Fin d → ℝ} {v : Torus d → Fin d → ℝ}
    (hu : ∀ i k, MemLp (fun x => u i x k) 2 μ) (hv : ∀ k, MemLp (fun x => v x k) 2 μ)
    (a : ℕ → ℝ) (n : ℕ) :
    dirPair μ (fun x k => ∑ i ∈ Finset.range n, a i * u i x k) v =
      ∑ i ∈ Finset.range n, a i * dirPair μ (u i) v := by
  unfold dirPair
  have e : ∀ x, ∑ k, (∑ i ∈ Finset.range n, a i * u i x k) * v x k =
      ∑ i ∈ Finset.range n, a i * ∑ k, u i x k * v x k := fun x => by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e]
  rw [integral_finset_sum (f := fun i x => a i * ∑ k, u i x k * v x k) _ fun i _ =>
    (dirPair_integrable (hu i) hv).const_mul _]
  simp_rw [integral_const_mul]

section eig
variable (hac : μ ≪ haar d) (he : IsRefEigenbasis μ e lam)
include hac he

theorem eig_memLp (i : ℕ) (k : Fin d) : MemLp (fun x => weakGrad (e i) x k) 2 μ :=
  memLp_grad_comp hac (he.memH1 i) k

theorem dirPair_eig (i : ℕ) {φ : Torus d → ℝ} (hφ : MemH1 μ φ) :
    dirPair μ (weakGrad (e i)) (weakGrad φ) = lam i * ∫ x, e i x * φ x ∂μ :=
  he.eigen i φ hφ

theorem lam_nonneg (i : ℕ) : 0 ≤ lam i := by
  have h := dirPair_eig hac he i (he.memH1 i)
  rw [he.orthonormal, if_pos rfl, mul_one] at h
  rw [← h]
  exact integral_nonneg fun x => Finset.sum_nonneg fun k _ => mul_self_nonneg _

/-- The defect identity `∫|∇f - ∑_{i<n} cᵢ∇eᵢ|² = ∫|∇f|² - ∑_{i<n} λᵢcᵢ²`. -/
theorem defect_identity {f : Torus d → ℝ} (hf : MemH1 μ f) (n : ℕ) :
    dirPair μ (fun x k => weakGrad f x k - ∑ i ∈ Finset.range n,
        (∫ y, f y * e i y ∂μ) * weakGrad (e i) x k)
      (fun x k => weakGrad f x k - ∑ i ∈ Finset.range n,
        (∫ y, f y * e i y ∂μ) * weakGrad (e i) x k) =
      dirPair μ (weakGrad f) (weakGrad f) -
        ∑ i ∈ Finset.range n, lam i * (∫ y, f y * e i y ∂μ) ^ 2 := by
  set c : ℕ → ℝ := fun i => ∫ y, f y * e i y ∂μ with hc
  have hgf : ∀ k, MemLp (fun x => weakGrad f x k) 2 μ := memLp_grad_comp hac hf
  have hge := eig_memLp hac he
  set S : Torus d → Fin d → ℝ := fun x k => ∑ i ∈ Finset.range n, c i * weakGrad (e i) x k
  have hS : ∀ k, MemLp (fun x => S x k) 2 μ := fun k =>
    memLp_finset_sum _ fun i _ => (hge i k).const_mul (c i)
  have hfe : ∀ i, ∫ x, e i x * f x ∂μ = c i := fun i => by
    simp only [hc]; congr 1; funext x; ring
  -- `∫ ∇f·S = ∑ λᵢcᵢ²`, `∫ S·S = ∑ λᵢcᵢ²`
  have h1 : dirPair μ S (weakGrad f) = ∑ i ∈ Finset.range n, lam i * c i ^ 2 := by
    rw [dirPair_sum_left hge hgf]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dirPair_eig hac he i hf, hfe]; ring
  have h2 : dirPair μ S S = ∑ i ∈ Finset.range n, lam i * c i ^ 2 := by
    rw [dirPair_sum_left hge hS]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hsym : dirPair μ (weakGrad (e i)) S = dirPair μ S (weakGrad (e i)) := by
      unfold dirPair; congr 1; funext x; exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsym, dirPair_sum_left hge (hge i)]
    have : ∀ j, dirPair μ (weakGrad (e j)) (weakGrad (e i)) = lam j * if j = i then 1 else 0 :=
      fun j => by rw [dirPair_eig hac he j (he.memH1 i), he.orthonormal]
    simp_rw [this]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range.mp hi, if_true]
    have := Finset.mem_range.mp hi
    simp [Finset.mem_range.mpr this]; ring
  have expand : ∀ x, ∑ k, (weakGrad f x k - S x k) * (weakGrad f x k - S x k) =
      ∑ k, weakGrad f x k * weakGrad f x k - 2 * ∑ k, S x k * weakGrad f x k +
        ∑ k, S x k * S x k := fun x => by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  unfold dirPair at h1 h2 ⊢
  show ∫ x, ∑ k, (weakGrad f x k - S x k) * (weakGrad f x k - S x k) ∂μ = _
  simp_rw [expand]
  rw [integral_add (f := fun x => ∑ k, weakGrad f x k * weakGrad f x k -
      2 * ∑ k, S x k * weakGrad f x k) (g := fun x => ∑ k, S x k * S x k)
      ((dirPair_integrable hgf hgf).sub ((dirPair_integrable hS hgf).const_mul 2))
      (dirPair_integrable hS hS),
    integral_sub (f := fun x => ∑ k, weakGrad f x k * weakGrad f x k)
      (g := fun x => 2 * ∑ k, S x k * weakGrad f x k) (dirPair_integrable hgf hgf)
      ((dirPair_integrable hS hgf).const_mul 2), integral_const_mul, h1, h2]
  ring

/-- `∫|∑_{i∈s} aᵢ∇eᵢ|² = ∑_{i∈s} λᵢ aᵢ²`. -/
theorem dirPair_eigsum (a : ℕ → ℝ) (s : Finset ℕ) :
    dirPair μ (fun x k => ∑ i ∈ s, a i * weakGrad (e i) x k)
      (fun x k => ∑ i ∈ s, a i * weakGrad (e i) x k) = ∑ i ∈ s, lam i * a i ^ 2 := by
  have hge := eig_memLp hac he
  have hS : ∀ k, MemLp (fun x => ∑ i ∈ s, a i * weakGrad (e i) x k) 2 μ := fun k =>
    memLp_finset_sum _ fun i _ => (hge i k).const_mul (a i)
  have hl : ∀ (v : Torus d → Fin d → ℝ), (∀ k, MemLp (fun x => v x k) 2 μ) →
      dirPair μ (fun x k => ∑ i ∈ s, a i * weakGrad (e i) x k) v =
        ∑ i ∈ s, a i * dirPair μ (weakGrad (e i)) v := fun v hv => by
    unfold dirPair
    have e1 : ∀ x, ∑ k, (∑ i ∈ s, a i * weakGrad (e i) x k) * v x k =
        ∑ i ∈ s, a i * ∑ k, weakGrad (e i) x k * v x k := fun x => by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    simp_rw [e1]
    rw [integral_finset_sum (f := fun i x => a i * ∑ k, weakGrad (e i) x k * v x k) _ fun i _ =>
      (dirPair_integrable (hge i) hv).const_mul _]
    simp_rw [integral_const_mul]
  rw [hl _ hS]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hsym : dirPair μ (weakGrad (e i)) (fun x k => ∑ j ∈ s, a j * weakGrad (e j) x k) =
      dirPair μ (fun x k => ∑ j ∈ s, a j * weakGrad (e j) x k) (weakGrad (e i)) := by
    unfold dirPair; congr 1; funext x; exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsym, hl _ (hge i)]
  have : ∀ j, dirPair μ (weakGrad (e j)) (weakGrad (e i)) = lam j * if j = i then 1 else 0 :=
    fun j => by rw [dirPair_eig hac he j (he.memH1 i), he.orthonormal]
  simp_rw [this]
  simp [hi]; ring

end eig

end SharpLSI
