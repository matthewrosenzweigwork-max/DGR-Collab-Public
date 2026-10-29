import SharpSymmetricLSI.Paper.LyapSchmidt3

/-!
# Section 4.2 (lane s42; R14): the complement `Y = E^⊥ ∩ {μ(u) = 0}` and `I + T` on it

* `meanC`, `pairC g` are the functionals `u ↦ μ(u)`, `u ↦ ⟨u, g⟩_μ` on `C(𝕋^d)`;
* `YC` is the closed subspace `{μ(u) = 0, ⟨u, φᵢ⟩ = 0}`; `QCraw` the projection onto it;
* `T` maps `YC` to itself (`TCY`), and `I + T` is invertible on `YC`: injective because
  `ker(I+T) = E`, surjective by the Fredholm alternative (`T = T_M + (T - T_M)` with `T_M` of
  finite rank from a uniform finite-rank approximation of the centered kernel).
-/

noncomputable section
open MeasureTheory Filter Real Topology

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section functionals
variable (μ : Measure (Torus d)) [IsProbabilityMeasure μ]

theorem abs_CT_le (u : CT d) (x : Torus d) : |u x| ≤ ‖u‖ := by
  rw [← Real.norm_eq_abs]; exact ContinuousMap.norm_coe_le_norm u x

/-- `u ↦ ⟨u, g⟩_μ`. -/
def pairC (g : CT d) : CT d →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun u => ∫ x, u x * g x ∂μ
      map_add' := fun u v => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (integrable_of_continuous (u.continuous.mul g.continuous))
          (integrable_of_continuous (v.continuous.mul g.continuous))
      map_smul' := fun c u => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ }
    ‖g‖ fun u => by
      rw [Real.norm_eq_abs]
      refine abs_integral_le_of_bdd fun x => ?_
      rw [abs_mul, mul_comm ‖g‖]
      exact mul_le_mul (abs_CT_le u x) (abs_CT_le g x) (abs_nonneg _) (norm_nonneg _)

theorem pairC_apply (g u : CT d) : pairC μ g u = ∫ x, u x * g x ∂μ := rfl

/-- `u ↦ μ(u)`. -/
def meanC : CT d →L[ℝ] ℝ := pairC μ 1

theorem meanC_apply (u : CT d) : meanC μ u = ∫ x, u x ∂μ := by
  simp [meanC, pairC_apply]

end functionals

section complement
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
  {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis' W μ φ)

/-- `u ↦ (μ(u), (⟨u, φᵢ⟩)ᵢ)`. -/
def lamC : CT d →L[ℝ] ℝ × (Fin n → ℝ) :=
  (meanC (μ : Measure (Torus d))).prod
    (ContinuousLinearMap.pi fun i => pairC (μ : Measure (Torus d)) (phiC hyp hφ i))

/-- `Y = E^⊥ ∩ {μ(u) = 0}` in `C(𝕋^d)`. -/
def YC : Submodule ℝ (CT d) := LinearMap.ker (lamC hyp hφ : CT d →ₗ[ℝ] ℝ × (Fin n → ℝ))

theorem mem_YC {u : CT d} : u ∈ YC hyp hφ ↔
    ∫ x, u x ∂(μ : Measure (Torus d)) = 0 ∧
      ∀ i, ∫ x, u x * phiC hyp hφ i x ∂(μ : Measure (Torus d)) = 0 := by
  simp only [YC, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, lamC,
    ContinuousLinearMap.prod_apply, Prod.mk_eq_zero, ContinuousLinearMap.pi_apply, meanC_apply,
    pairC_apply, funext_iff, Pi.zero_apply]

theorem isClosed_YC : IsClosed (YC hyp hφ : Set (CT d)) :=
  ContinuousLinearMap.isClosed_ker (lamC hyp hφ)

theorem completeSpace_YC : CompleteSpace (YC hyp hφ) :=
  (isClosed_YC hyp hφ).completeSpace_coe

/-- `u - μ(u) - ∑ ⟨u, φᵢ⟩ φᵢ`. -/
def QCraw : CT d →L[ℝ] CT d :=
  ContinuousLinearMap.id ℝ (CT d) - (meanC (μ : Measure (Torus d))).smulRight (1 : CT d) -
    ∑ i, (pairC (μ : Measure (Torus d)) (phiC hyp hφ i)).smulRight (phiC hyp hφ i)

theorem QCraw_apply (u : CT d) : QCraw hyp hφ u =
    u - (∫ x, u x ∂(μ : Measure (Torus d))) • (1 : CT d) -
      ∑ i, (∫ x, u x * phiC hyp hφ i x ∂(μ : Measure (Torus d))) • phiC hyp hφ i := by
  simp [QCraw, meanC_apply, pairC_apply, ContinuousLinearMap.sum_apply]

theorem QCraw_mem (u : CT d) : QCraw hyp hφ u ∈ YC hyp hφ := by
  have iu : Integrable (fun x => u x) (μ : Measure (Torus d)) :=
    integrable_of_continuous u.continuous
  set m := ∫ y, u y ∂(μ : Measure (Torus d)) with hm
  set c : Fin n → ℝ := fun i => ∫ y, u y * phiC hyp hφ i y ∂(μ : Measure (Torus d)) with hc
  have hv : ∀ x, QCraw hyp hφ u x = u x - m - ∑ i, c i * phiC hyp hφ i x := fun x => by
    rw [QCraw_apply]; simp [ContinuousMap.sum_apply, hm, hc]
  have i1 : Integrable (fun x => u x - m) (μ : Measure (Torus d)) := iu.sub (integrable_const m)
  have i2 : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun x => c i * phiC hyp hφ i x) (μ : Measure (Torus d)) := fun i _ =>
    integrable_of_continuous (continuous_const.mul (phiC hyp hφ i).continuous)
  have i3 : Integrable (fun x => ∑ i, c i * phiC hyp hφ i x) (μ : Measure (Torus d)) :=
    integrable_finsetSum _ i2
  rw [mem_YC]
  constructor
  · rw [integral_congr_ae (Eventually.of_forall hv), integral_sub i1 i3,
      integral_sub iu (integrable_const m), integral_finsetSum _ i2]
    simp [integral_const_mul, integral_phiC hyp hφ, hm]
  · intro j
    have hv' : ∀ x, QCraw hyp hφ u x * phiC hyp hφ j x = u x * phiC hyp hφ j x -
        m * phiC hyp hφ j x - ∑ i, c i * (phiC hyp hφ i x * phiC hyp hφ j x) := fun x => by
      rw [hv, sub_mul, sub_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    have j1 : Integrable (fun x => u x * phiC hyp hφ j x) (μ : Measure (Torus d)) :=
      integrable_of_continuous (u.continuous.mul (phiC hyp hφ j).continuous)
    have j2 : Integrable (fun x => m * phiC hyp hφ j x) (μ : Measure (Torus d)) :=
      integrable_of_continuous (continuous_const.mul (phiC hyp hφ j).continuous)
    have j3 : ∀ i ∈ (Finset.univ : Finset (Fin n)), Integrable
        (fun x => c i * (phiC hyp hφ i x * phiC hyp hφ j x)) (μ : Measure (Torus d)) := fun i _ =>
      integrable_of_continuous (continuous_const.mul
        ((phiC hyp hφ i).continuous.mul (phiC hyp hφ j).continuous))
    have j12 : Integrable (fun x => u x * phiC hyp hφ j x - m * phiC hyp hφ j x)
        (μ : Measure (Torus d)) := j1.sub j2
    rw [integral_congr_ae (Eventually.of_forall hv'), integral_sub j12 (integrable_finsetSum _ j3),
      integral_sub j1 j2, integral_finsetSum _ j3, integral_const_mul, integral_phiC hyp hφ,
      mul_zero, sub_zero]
    simp_rw [integral_const_mul, phiC_orthonormal hyp hφ]
    simp [hc]

theorem QCraw_of_mem {u : CT d} (hu : u ∈ YC hyp hφ) : QCraw hyp hφ u = u := by
  rw [QCraw_apply]
  obtain ⟨h1, h2⟩ := (mem_YC hyp hφ).mp hu
  simp [h1, h2]

theorem QCraw_idem (u : CT d) : QCraw hyp hφ (QCraw hyp hφ u) = QCraw hyp hφ u :=
  QCraw_of_mem hyp hφ (QCraw_mem hyp hφ u)

/-- If `u ∈ YC` and `QCraw v = 0` then `u + (v - QCraw v) = 0` forces `u = 0` and `v ∈ YC`
(the two summands lie in complementary subspaces). -/
theorem eq_zero_of_add_compl {u v : CT d} (hu : u ∈ YC hyp hφ)
    (h : u + (v - QCraw hyp hφ v) = 0) : u = 0 ∧ QCraw hyp hφ v = v := by
  have h1 := congrArg (QCraw hyp hφ) h
  rw [map_add, map_sub, QCraw_idem, sub_self, add_zero, QCraw_of_mem hyp hφ hu, map_zero] at h1
  refine ⟨h1, ?_⟩
  rw [h1, zero_add, sub_eq_zero] at h
  exact h.symm

/-- `kC a = ∑ aᵢ phiC i`. -/
def kC : EuclideanSpace ℝ (Fin n) →L[ℝ] CT d :=
  ∑ i, (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).smulRight (phiC hyp hφ i)

theorem kC_apply (a : EuclideanSpace ℝ (Fin n)) (x : Torus d) :
    kC hyp hφ a x = ∑ i, a i * phiC hyp hφ i x := by
  simp [kC, ContinuousLinearMap.sum_apply, ContinuousMap.sum_apply]

end complement

end SharpLSI
