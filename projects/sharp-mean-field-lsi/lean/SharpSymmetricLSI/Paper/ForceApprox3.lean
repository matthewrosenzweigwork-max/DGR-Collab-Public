import SharpSymmetricLSI.Paper.ForceApprox2

/-!
# R31 groundwork: kernel-level weak gradients of a finite-rank `C¹` kernel

* On `𝕋^{2×d}`: `y ↦ K(y₀, y₁)` has the weak gradient `(∂₁K(y₀,y₁), ∂₁K(y₁,y₀))`.
* On `𝕋^d`: `z ↦ K(z,z)/2` has the weak gradient `∂₁K(z,z)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

section
variable {φ : ℕ → Torus d → ℝ} (hφ : ∀ i, ContDiff ℝ 1 (φ i ∘ liftT)) (s : Finset ℕ)
  {a : ℕ → ℕ → ℝ} (ha : ∀ i j, a i j = a j i)

include hφ ha in
theorem isWeakGrad_finKer_pair :
    IsWeakGrad (fun y : UnitAddTorus (Fin 2 × Fin d) => finKer φ s a (projBlock 0 y) (projBlock 1 y))
      (fun y p => if p.1 = 0 then finKerD φ s a (projBlock 0 y) (projBlock 1 y) p.2
        else finKerD φ s a (projBlock 1 y) (projBlock 0 y) p.2) := by
  have hT := fun (i j : ℕ) => (isWeakGrad_pair_term hφ i j (0 : Fin 2) 1).cmul (a i j)
  have h := isWeakGrad_finsetSum s fun i _ => isWeakGrad_finsetSum s fun j _ => hT i j
  convert h using 1
  · funext y
    simp only [finKer]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · funext y p
    obtain ⟨c, k⟩ := p
    fin_cases c
    · simp only [finKerD, Fin.zero_eta, Fin.isValue, ↓reduceIte, zero_ne_one]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    · simp only [finKerD, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [ha]; ring

include hφ ha in
theorem isWeakGrad_finKer_diag :
    IsWeakGrad (fun z : Torus d => finKer φ s a z z / 2) (fun z k => finKerD φ s a z z k) := by
  have hT : ∀ i j, IsWeakGrad (fun z : Torus d => φ i z * φ j z)
      (fun z k => cgrad (φ i) z k * φ j z + φ i z * cgrad (φ j) z k) := fun i j => by
    obtain ⟨C, hC⟩ := exists_bound_of_contDiff (hφ i)
    obtain ⟨C', hC'⟩ := exists_bound_cgrad (hφ i)
    obtain ⟨D, hD⟩ := exists_bound_of_contDiff (hφ j)
    obtain ⟨D', hD'⟩ := exists_bound_cgrad (hφ j)
    exact (isWeakGrad_of_contDiff (hφ i)).mul_lip
      (integrable_of_bdd (measurable_of_contDiff (hφ i)) hC)
      (fun k => integrable_of_bdd (measurable_cgrad (hφ i) k) fun y => hC' y k)
      (isWeakGrad_of_contDiff (hφ j)) (measurable_of_contDiff (hφ j)) hD
      (fun k => measurable_cgrad (hφ j) k) hD'
  have h := (isWeakGrad_finsetSum s fun i _ => isWeakGrad_finsetSum s fun j _ =>
    (hT i j).cmul (a i j)).cmul (1 / 2)
  convert h using 1
  · funext z
    simp only [finKer]
    rw [div_eq_inv_mul, one_div]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · funext z k
    simp only [finKerD, mul_add, Finset.sum_add_distrib]
    have : ∑ i ∈ s, ∑ j ∈ s, a i j * (φ i z * cgrad (φ j) z k) =
        ∑ i ∈ s, ∑ j ∈ s, a i j * cgrad (φ i) z k * φ j z := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [ha]; ring
    rw [this]
    have : ∑ i ∈ s, ∑ j ∈ s, a i j * (cgrad (φ i) z k * φ j z) =
        ∑ i ∈ s, ∑ j ∈ s, a i j * cgrad (φ i) z k * φ j z := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]; ring

end

end SharpLSI
