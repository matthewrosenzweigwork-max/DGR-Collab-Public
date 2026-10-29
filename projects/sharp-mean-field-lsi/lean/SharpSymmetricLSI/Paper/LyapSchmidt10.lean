import SharpSymmetricLSI.Paper.LyapSchmidt8
import SharpSymmetricLSI.Paper.LyapSchmidt9

/-!
# Section 4.2 (lane s42; R14): the gradient of the reduced energy on the graph

On the zero set of `FC` (`y ∈ YC`, `P(log(1+h) + T h) = 0` with `h = kC a + y`):
* `log(1 + h) + T h = c + ∑ bᵢ φᵢ` with `c = μ(·)`, `bᵢ = ⟨·, φᵢ⟩` (`PhiC_eq_of_zero`);
* `μ(h) = 0`, `⟨h, φᵢ⟩ = aᵢ`;
* `DΨ(h) k = ∑ bᵢ ⟨k, φᵢ⟩` for mean-zero `k` (`DPsiC_eq`).
-/

noncomputable section
open MeasureTheory Filter Real Topology Metric
open scoped ContDiff

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section graph
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
  {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis' W μ φ)

/-- The coefficient vector `b(h) = (⟨log(1+h) + T h, φᵢ⟩)ᵢ`. -/
def bvec (h : CT d) : Fin n → ℝ :=
  fun i => pairC (μ : Measure (Torus d)) (phiC hyp hφ i) (PhiC hyp (μ : Measure (Torus d)) h)

theorem bvec_apply (h : CT d) (i : Fin n) :
    bvec hyp hφ h i = ∫ x, PhiC hyp (μ : Measure (Torus d)) h x * phiC hyp hφ i x
      ∂(μ : Measure (Torus d)) := rfl

/-- On the zero set: `log(1+h) + T h = c + ∑ bᵢ φᵢ`. -/
theorem PhiC_eq_of_zero {h : CT d} (hz : QCraw hyp hφ (PhiC hyp (μ : Measure (Torus d)) h) = 0)
    (x : Torus d) : PhiC hyp (μ : Measure (Torus d)) h x =
      (∫ y, PhiC hyp (μ : Measure (Torus d)) h y ∂(μ : Measure (Torus d))) +
        ∑ i, bvec hyp hφ h i * phiC hyp hφ i x := by
  have := congrArg (fun u : CT d => u x) hz
  simp only [QCraw_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul, mul_one, ContinuousMap.coe_sum, Finset.sum_apply,
    ContinuousMap.zero_apply] at this
  simp only [bvec_apply]
  linarith

/-- The gradient identity `DΨ(h) k = ∑ bᵢ ⟨k, φᵢ⟩`. -/
theorem DPsiC_eq {h k : CT d} (hz : QCraw hyp hφ (PhiC hyp (μ : Measure (Torus d)) h) = 0)
    (hh0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) (hk0 : ∫ x, k x ∂(μ : Measure (Torus d)) = 0) :
    DPsiC hyp (μ : Measure (Torus d)) h k =
      ∑ i, bvec hyp hφ h i * ∫ x, k x * phiC hyp hφ i x ∂(μ : Measure (Torus d)) := by
  set μm := (μ : Measure (Torus d))
  rw [DPsiC_apply]
  have hsa : ∫ x, TC hyp μm k x * h x ∂μm = ∫ x, k x * TC hyp μm h x ∂μm :=
    (Top_selfadjoint hyp μm (memL20_CT hyp μm hk0) (memL20_CT hyp μm hh0)).symm
  rw [hsa]
  set c := ∫ y, PhiC hyp μm h y ∂μm
  have hP := PhiC_eq_of_zero hyp hφ hz
  have e : ∫ x, k x * (logC h x + 1) ∂μm + (∫ x, k x * TC hyp μm h x ∂μm +
      ∫ x, k x * TC hyp μm h x ∂μm) / 2 = ∫ x, k x * PhiC hyp μm h x ∂μm := by
    have i1 : Integrable (fun x => k x * (logC h x + 1)) μm :=
      integrable_of_continuous (k.continuous.mul ((logC h).continuous.add continuous_const))
    have i2 : Integrable (fun x => k x * TC hyp μm h x) μm :=
      integrable_of_continuous (k.continuous.mul (TC hyp μm h).continuous)
    have i3 : Integrable (fun x => k x) μm := integrable_of_continuous k.continuous
    have e1 : ∫ x, k x * PhiC hyp μm h x ∂μm =
        ∫ x, (k x * (logC h x + 1) + k x * TC hyp μm h x - k x) ∂μm := by
      congr 1; funext x; simp only [PhiC, ContinuousMap.add_apply]; ring
    have i12 : Integrable (fun x => k x * (logC h x + 1) + k x * TC hyp μm h x) μm := i1.add i2
    rw [e1, integral_sub i12 i3, integral_add i1 i2, hk0]
    ring
  rw [e]
  have i4 : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun x => bvec hyp hφ h i * (k x * phiC hyp hφ i x)) μm := fun i _ =>
    integrable_of_continuous (continuous_const.mul (k.continuous.mul (phiC hyp hφ i).continuous))
  have e2 : (fun x => k x * PhiC hyp μm h x) =
      fun x => c * k x + ∑ i, bvec hyp hφ h i * (k x * phiC hyp hφ i x) := by
    funext x
    rw [hP x, mul_add, Finset.mul_sum, mul_comm (k x) c]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have i5 : Integrable (fun x => c * k x) μm :=
    integrable_of_continuous (continuous_const.mul k.continuous)
  have i6 : Integrable (fun x => ∑ i, bvec hyp hφ h i * (k x * phiC hyp hφ i x)) μm :=
    integrable_finsetSum _ i4
  rw [e2, integral_add i5 i6, integral_const_mul, hk0, mul_zero, zero_add,
    integral_finsetSum _ i4]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem integral_kC (a : EuclideanSpace ℝ (Fin n)) :
    ∫ x, kC hyp hφ a x ∂(μ : Measure (Torus d)) = 0 := by
  simp_rw [kC_apply]
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun x => a i * phiC hyp hφ i x) (μ : Measure (Torus d)) := fun i _ =>
    integrable_of_continuous (continuous_const.mul (phiC hyp hφ i).continuous)
  rw [integral_finsetSum _ hi]
  simp [integral_const_mul, integral_phiC hyp hφ]

theorem integral_kC_mul_phiC (a : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    ∫ x, kC hyp hφ a x * phiC hyp hφ j x ∂(μ : Measure (Torus d)) = a j := by
  simp_rw [kC_apply, Finset.sum_mul, mul_assoc]
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)), Integrable
      (fun x => a i * (phiC hyp hφ i x * phiC hyp hφ j x)) (μ : Measure (Torus d)) := fun i _ =>
    integrable_of_continuous (continuous_const.mul
      ((phiC hyp hφ i).continuous.mul (phiC hyp hφ j).continuous))
  rw [integral_finsetSum _ hi]
  simp [integral_const_mul, phiC_orthonormal hyp hφ]

end graph

end SharpLSI
