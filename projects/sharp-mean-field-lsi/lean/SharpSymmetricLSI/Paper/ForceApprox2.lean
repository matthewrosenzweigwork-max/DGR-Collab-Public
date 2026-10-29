import SharpSymmetricLSI.Paper.ForceApprox1
import SharpSymmetricLSI.Paper.NBody2
import SharpSymmetricLSI.Paper.GroundT1
import SharpSymmetricLSI.Paper.ProductFisherGrad
import SharpSymmetricLSI.Statements.R25_Lemma_A_2
import SharpSymmetricLSI.Defs.D08_Gibbs

/-!
# R31 groundwork: the weak gradient of `U_N^{(R)}` for a finite-rank `C¹` kernel

For `C¹` periodic `φ_i` and symmetric `a`, `K(x,y) = ∑_{i,j∈s} a_{ij} φ_i(x) φ_j(y)`. Then
`U^{(R)}_N = (2N)⁻¹ ∑_{a,b} K(X_a, X_b)` has the weak gradient
`∇_c U^{(R)}_N = N⁻¹ ∑_b ∂₁K(X_c, X_b)`, `∂₁K(x,y) = ∑ a_{ij} ∇φ_i(x) φ_j(y)`
(block projections and the product rule with Lipschitz factors; symmetry of `a`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- A copy of `Ukernel` (R31, `Statements/R31_Force_Approximation.lean`), definitionally equal to it,
so that the R31 proof files do not import the R31 statement file. -/
noncomputable def UkernelF (K : Torus d → Torus d → ℝ) (N : ℕ) (X : Config N d) : ℝ :=
  1 / (2 * (N : ℝ)) * ∑ i, ∑ j, K (X i) (X j)

/-- The finite-rank kernel. -/
noncomputable def finKer (φ : ℕ → Torus d → ℝ) (s : Finset ℕ) (a : ℕ → ℕ → ℝ) (x y : Torus d) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, a i j * φ i x * φ j y

/-- Its first-variable gradient `∂₁K(x,y)`. -/
noncomputable def finKerD (φ : ℕ → Torus d → ℝ) (s : Finset ℕ) (a : ℕ → ℕ → ℝ) (x y : Torus d)
    (k : Fin d) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, a i j * cgrad (φ i) x k * φ j y

section
variable {φ : ℕ → Torus d → ℝ} (hφ : ∀ i, ContDiff ℝ 1 (φ i ∘ liftT)) (s : Finset ℕ)
  {a : ℕ → ℕ → ℝ} (ha : ∀ i j, a i j = a j i)

include hφ in
theorem isWeakGrad_phi_block {N : ℕ} (i : ℕ) (b : Fin N) :
    IsWeakGrad (fun y : UnitAddTorus (Fin N × Fin d) => φ i (projBlock b y))
      (fun y p => if p.1 = b then cgrad (φ i) (projBlock b y) p.2 else 0) := by
  obtain ⟨C, hC⟩ := exists_bound_of_contDiff (hφ i)
  obtain ⟨C', hC'⟩ := exists_bound_cgrad (hφ i)
  exact isWeakGrad_comp_projBlock b (isWeakGrad_of_contDiff (hφ i))
    (integrable_of_bdd (measurable_of_contDiff (hφ i)) hC)
    fun k => integrable_of_bdd (measurable_cgrad (hφ i) k) fun y => hC' y k

include hφ in
/-- The pair term `φ_i(y_a) φ_j(y_b)`. -/
theorem isWeakGrad_pair_term {N : ℕ} (i j : ℕ) (b c : Fin N) :
    IsWeakGrad (fun y : UnitAddTorus (Fin N × Fin d) => φ i (projBlock b y) * φ j (projBlock c y))
      (fun y p => (if p.1 = b then cgrad (φ i) (projBlock b y) p.2 else 0) * φ j (projBlock c y) +
        φ i (projBlock b y) * (if p.1 = c then cgrad (φ j) (projBlock c y) p.2 else 0)) := by
  obtain ⟨C, hC⟩ := exists_bound_of_contDiff (hφ i)
  obtain ⟨C', hC'⟩ := exists_bound_cgrad (hφ i)
  obtain ⟨D, hD⟩ := exists_bound_of_contDiff (hφ j)
  obtain ⟨D', hD'⟩ := exists_bound_cgrad (hφ j)
  have hD'0 : 0 ≤ |D'| := abs_nonneg _
  refine (isWeakGrad_phi_block hφ i b).mul_lip
    (integrable_of_bdd ((measurable_of_contDiff (hφ i)).comp (measurable_projBlock b)) fun y => hC _)
    (fun p => integrable_of_bdd (C := |C'|) (by
      refine Measurable.ite (MeasurableSet.const _) ?_ measurable_const
      exact (measurable_cgrad (hφ i) p.2).comp (measurable_projBlock b)) fun y => by
        split_ifs
        · exact (hC' _ _).trans (le_abs_self _)
        · simp)
    (isWeakGrad_phi_block hφ j c)
    ((measurable_of_contDiff (hφ j)).comp (measurable_projBlock c)) (fun y => hD _)
    (fun p => by
      refine Measurable.ite (MeasurableSet.const _) ?_ measurable_const
      exact (measurable_cgrad (hφ j) p.2).comp (measurable_projBlock c))
    (L := |D'|) fun y p => by
      split_ifs
      · exact (hD' _ _).trans (le_abs_self _)
      · simpa using hD'0

omit hφ in
include ha in
theorem pair_sum_eq {N : ℕ} (u du : ℕ → Fin N → ℝ) (c : Fin N) :
    ∑ b : Fin N, ∑ c' : Fin N, ∑ i ∈ s, ∑ j ∈ s, a i j *
      ((if c = b then du i b else 0) * u j c' + u i b * (if c = c' then du j c' else 0)) =
    2 * ∑ b : Fin N, ∑ i ∈ s, ∑ j ∈ s, a i j * du i c * u j b := by
  simp only [mul_add, Finset.sum_add_distrib]
  have h1 : ∑ b : Fin N, ∑ c' : Fin N, ∑ i ∈ s, ∑ j ∈ s,
      a i j * ((if c = b then du i b else 0) * u j c') =
      ∑ c' : Fin N, ∑ i ∈ s, ∑ j ∈ s, a i j * du i c * u j c' := by
    rw [Finset.sum_eq_single c]
    · simp only [↓reduceIte]
      refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => ?_
      ring
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  have h2 : ∑ b : Fin N, ∑ c' : Fin N, ∑ i ∈ s, ∑ j ∈ s,
      a i j * (u i b * (if c = c' then du j c' else 0)) =
      ∑ b : Fin N, ∑ i ∈ s, ∑ j ∈ s, a i j * du i c * u j b := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_eq_single c]
    · simp only [↓reduceIte]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [ha]; ring
    · intro c' _ hc'
      simp [Ne.symm hc']
    · simp
  rw [h1, h2]; ring

include hφ ha in
/-- **The weak gradient of `U_N^{(R)}`.** -/
theorem isWeakGrad_Ukernel_finKer {N : ℕ} (hN : 1 ≤ N) :
    IsWeakGrad (fun y : UnitAddTorus (Fin N × Fin d) => UkernelF (finKer φ s a) N (unflat y))
      (fun y p => (N : ℝ)⁻¹ * ∑ b : Fin N, finKerD φ s a (projBlock p.1 y) (projBlock b y) p.2) := by
  have hT := fun (b c : Fin N) (i j : ℕ) => (isWeakGrad_pair_term hφ i j b c).cmul (a i j)
  have h := (isWeakGrad_finsetSum Finset.univ fun b _ => isWeakGrad_finsetSum Finset.univ
    fun c _ => isWeakGrad_finsetSum s fun i _ => isWeakGrad_finsetSum s fun j _ =>
      hT b c i j).cmul (1 / (2 * (N : ℝ)))
  convert h using 1
  · funext y
    simp only [UkernelF, finKer]
    congr 1
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc]; rfl
  · funext y p
    obtain ⟨c, k⟩ := p
    have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have := pair_sum_eq s ha (fun i b => φ i (projBlock b y))
      (fun i b => cgrad (φ i) (projBlock b y) k) c
    simp only at this ⊢
    rw [this]
    unfold finKerD
    field_simp

end

end SharpLSI
