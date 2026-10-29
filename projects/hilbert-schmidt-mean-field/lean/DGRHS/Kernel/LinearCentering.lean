/- True continuous mean centering and finite linear combinations of actual
L2 observable classes. Representative statements are only almost everywhere. -/
import DGRHS.Kernel.L2Centering
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace DGRHS.Kernel
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

def centeringOperator : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ContinuousLinearMap.id ℝ (Lp ℝ 2 μ) - (innerSL ℝ (oneL2 (μ := μ))).smulRight oneL2

lemma centeringOperator_apply (v : Lp ℝ 2 μ) : centeringOperator v = centeredL2 v := by
  rw [centeredL2, ←inner_oneL2_eq_integral]
  rfl

def sourceCenteringOperator : Lp ℝ 2 μ →L[ℝ] meanZeroL2 μ :=
  centeringOperator.codRestrict (meanZeroL2 μ)
    (fun v => by rw [centeringOperator_apply]; exact centeredL2_mem_meanZero v)

lemma sourceCenteringOperator_apply (v : Lp ℝ 2 μ) :
    sourceCenteringOperator v = sourceCenteredL2 v := by
  apply Subtype.ext
  exact centeringOperator_apply v

lemma sourceCenteredL2_sum_smul {J : Type*} (s : Finset J) (θ : J → ℝ)
    (φ : J → Lp ℝ 2 μ) :
    sourceCenteredL2 (∑ k ∈ s, θ k • φ k) = ∑ k ∈ s, θ k • sourceCenteredL2 (φ k) := by
  simp_rw [←sourceCenteringOperator_apply]
  rw [map_sum]
  simp only [map_smul]

lemma lp_finite_sum_coeFn {J : Type*} (s : Finset J) (φ : J → Lp ℝ 2 μ) :
    (fun x => (∑ k ∈ s, φ k : Lp ℝ 2 μ) x) =ᵐ[μ] fun x => ∑ k ∈ s, φ k x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (Lp.coeFn_zero ℝ 2 μ).mono (fun x hx => by simpa only [Pi.zero_apply] using hx)
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    filter_upwards [Lp.coeFn_add (φ k) (∑ l ∈ s,φ l),ih] with x ha hs
    rw [ha,Pi.add_apply,hs]

lemma lp_finite_sum_smul_coeFn {J : Type*} [Countable J] (s : Finset J) (θ : J → ℝ)
    (φ : J → Lp ℝ 2 μ) :
    (fun x => (∑ k ∈ s, θ k • φ k : Lp ℝ 2 μ) x) =ᵐ[μ]
      fun x => ∑ k ∈ s, θ k * φ k x := by
  classical
  have hsm : ∀ k,∀ᵐ x ∂μ,(θ k • φ k : Lp ℝ 2 μ) x = θ k*φ k x :=
    fun k => Lp.coeFn_smul (θ k) (φ k)
  filter_upwards [lp_finite_sum_coeFn s (fun k => θ k • φ k),ae_all_iff.mpr hsm] with x hx hs
  rw [hx]
  exact Finset.sum_congr rfl (fun k _ => hs k)

lemma lp_finite_sum_smul_bounded {J : Type*} [Countable J] (s : Finset J) (θ K : J → ℝ)
    (φ : J → Lp ℝ 2 μ) (hK : ∀ k,∀ᵐ x ∂μ,|φ k x| ≤ K k) :
    ∀ᵐ x ∂μ,|(∑ k ∈ s,θ k • φ k : Lp ℝ 2 μ) x| ≤ ∑ k ∈ s,|θ k| * K k := by
  classical
  filter_upwards [lp_finite_sum_smul_coeFn s θ φ,ae_all_iff.mpr hK] with x hx hk
  rw [hx]
  calc
    _ ≤ ∑ k ∈ s,|θ k*φ k x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum (fun k _ => by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hk k) (abs_nonneg _))

lemma mean_finite_sum_smul {J : Type*} (s : Finset J) (θ : J → ℝ)
    (φ : J → Lp ℝ 2 μ) :
    (∫ x,(∑ k ∈ s,θ k • φ k : Lp ℝ 2 μ) x ∂μ) =
      ∑ k ∈ s,θ k*(∫ x,φ k x ∂μ) := by
  simp_rw [←inner_oneL2_eq_integral]
  rw [inner_sum]
  simp only [real_inner_smul_right]

lemma centered_covariance_finite_sum {J : Type*} (s : Finset J) (θ : J → ℝ)
    (φ : J → Lp ℝ 2 μ) (R : meanZeroL2 μ →L[ℝ] meanZeroL2 μ) :
    inner ℝ (sourceCenteredL2 (∑ k ∈ s,θ k • φ k) : Lp ℝ 2 μ)
      (R (sourceCenteredL2 (∑ k ∈ s,θ k • φ k)) : Lp ℝ 2 μ) =
      ∑ k ∈ s,∑ l ∈ s,θ k*θ l*inner ℝ (sourceCenteredL2 (φ k) : Lp ℝ 2 μ) (R (sourceCenteredL2 (φ l)) : Lp ℝ 2 μ) := by
  simp only [sourceCenteredL2_sum_smul,map_sum,map_smul,Submodule.coe_sum,Submodule.coe_smul]
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro k hk
  rw [real_inner_smul_left,inner_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [real_inner_smul_right]
  ring

lemma twoSidedInverse_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A R T : E →L[ℝ] E) (hR : ∀ v,A (R v)=v) (hT : ∀ v,T (A v)=v) : R=T := by
  ext v
  have hh := hT (R v)
  rw [hR] at hh
  exact hh.symm
end DGRHS.Kernel
#print axioms DGRHS.Kernel.sourceCenteredL2_sum_smul
#print axioms DGRHS.Kernel.lp_finite_sum_smul_coeFn
#print axioms DGRHS.Kernel.lp_finite_sum_smul_bounded
#print axioms DGRHS.Kernel.mean_finite_sum_smul
#print axioms DGRHS.Kernel.centered_covariance_finite_sum
#print axioms DGRHS.Kernel.twoSidedInverse_unique
#check @DGRHS.Kernel.centered_covariance_finite_sum
