/- Preparation: actual product-L2 diagonal spectral expansion. Not Lean checked.
The finite norm identity will connect the genuine kernel to its spectral sum. -/
import DGRHS.Kernel.SpectralHilbertSchmidt
open MeasureTheory
open Filter
open scoped InnerProductSpace BigOperators Topology
namespace DGRHS.Kernel
variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
noncomputable def separatedLp (f g : Lp ℝ 2 μ) : Lp ℝ 2 (μ.prod μ) :=
  (memLp_separated_mul μ (Lp.memLp f) (Lp.memLp g)).toLp (fun p ↦ f p.1 * g p.2)
lemma separatedLp_coeFn (f g : Lp ℝ 2 μ) :
    (separatedLp f g : α × α → ℝ) =ᵐ[μ.prod μ] fun p ↦ f p.1 * g p.2 :=
  (memLp_separated_mul μ (Lp.memLp f) (Lp.memLp g)).coeFn_toLp

lemma inner_separatedLp (f g f' g' : Lp ℝ 2 μ) :
    inner ℝ (separatedLp f g) (separatedLp f' g') = inner ℝ f f' * inner ℝ g g' := by
  rw [L2.inner_def]
  calc
    (∫ p, inner ℝ (separatedLp f g p) (separatedLp f' g' p) ∂(μ.prod μ))
        = ∫ p, (f p.1 * f' p.1) * (g p.2 * g' p.2) ∂(μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards [separatedLp_coeFn f g, separatedLp_coeFn f' g'] with p hp hp'
      simp only [hp, hp', RCLike.inner_apply', conj_trivial]
      ring
    _ = (∫ x, f x * f' x ∂μ) * (∫ y, g y * g' y ∂μ) := integral_prod_mul (μ := μ) (ν := μ) (fun x : α ↦ f x * f' x)
      (fun y : α ↦ g y * g' y)
    _ = inner ℝ f f' * inner ℝ g g' := by
      simp only [L2.inner_def, RCLike.inner_apply', conj_trivial]

lemma orthonormal_diagonal_separatedLp (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) :
    Orthonormal ℝ (fun i ↦ separatedLp (b i) (b i)) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  rw [inner_separatedLp, orthonormal_iff_ite.mp b.orthonormal i j]
  by_cases hij : i = j <;> simp [hij]

lemma inner_kernel_separatedLp (κ : Lp ℝ 2 (μ.prod μ)) (f g : Lp ℝ 2 μ) :
    inner ℝ κ (separatedLp f g) = inner ℝ (Operator.l2KernelOp κ g) f := by
  have h := inner_integralOperator (fun p ↦ κ p) (Lp.memLp κ) g f
  simp only [integralOperator, Lp.toLp_coeFn] at h
  rw [h, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [separatedLp_coeFn f g] with p hp
  simp only [hp, RCLike.inner_apply', conj_trivial]
  ring

lemma kernel_diagonal_coefficient (κ : Lp ℝ 2 (μ.prod μ))
    (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, Operator.l2KernelOp κ (b i) = eig i • b i) (i : ι) :
    inner ℝ κ (separatedLp (b i) (b i)) = eig i := by
  rw [inner_kernel_separatedLp, hb i]
  simp only [real_inner_smul_left, real_inner_self_eq_norm_sq,
    b.orthonormal.1 i, one_pow, mul_one]

lemma norm_kernel_spectral_remainder_sq (κ : Lp ℝ 2 (μ.prod μ))
    (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, Operator.l2KernelOp κ (b i) = eig i • b i) (s : Finset ι) :
    ‖κ - ∑ i ∈ s, eig i • separatedLp (b i) (b i)‖ ^ 2 =
      ‖κ‖ ^ 2 - ∑ i ∈ s, eig i ^ 2 := by
  rw [norm_sub_sq_real, inner_sum]
  simp_rw [inner_smul_right, kernel_diagonal_coefficient κ eig b hb]
  have hnorm : ‖∑ i ∈ s, eig i • separatedLp (b i) (b i)‖ ^ 2 = ∑ i ∈ s, eig i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simpa [pow_two] using (orthonormal_diagonal_separatedLp b).inner_sum eig eig s
  rw [hnorm]
  simp only [← pow_two]
  ring

lemma hasSum_kernel_diagonal_spectral [Countable ι] (κ : Lp ℝ 2 (μ.prod μ))
    (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, Operator.l2KernelOp κ (b i) = eig i • b i) :
    HasSum (fun i ↦ eig i • separatedLp (b i) (b i)) κ := by
  classical
  have hn (i : ι) : ‖Operator.l2KernelOp κ (b i)‖ ^ 2 = eig i ^ 2 := by
    rw [hb i, norm_smul, b.orthonormal.1 i, mul_one, Real.norm_eq_abs, sq_abs]
  have hs : Summable (fun i ↦ eig i ^ 2) :=
    (summable_norm_kernelOp_sq κ b b.orthonormal).congr hn
  have ht : (∑' i, eig i ^ 2) = ‖κ‖ ^ 2 := by
    calc
      (∑' i, eig i ^ 2) = ∑' i, ‖Operator.l2KernelOp κ (b i)‖ ^ 2 := tsum_congr (fun i ↦ (hn i).symm)
      _ = ‖κ‖ ^ 2 := tsum_norm_kernelOp_sq κ b
  have hc : Tendsto (fun _ : Finset ι ↦ ‖κ‖ ^ 2) atTop (𝓝 (‖κ‖ ^ 2)) := tendsto_const_nhds
  have hs' : Tendsto (fun s : Finset ι ↦ ∑ i ∈ s, eig i ^ 2) atTop
      (𝓝 (∑' i, eig i ^ 2)) := hs.hasSum
  have hsq : Tendsto (fun s : Finset ι ↦
      ‖κ - ∑ i ∈ s, eig i • separatedLp (b i) (b i)‖ ^ 2) atTop (𝓝 0) := by
    simpa only [norm_kernel_spectral_remainder_sq κ eig b hb, ht, sub_self]
      using hc.sub hs'
  have hnorm : Tendsto (fun s : Finset ι ↦
      ‖κ - ∑ i ∈ s, eig i • separatedLp (b i) (b i)‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt
  change Tendsto (fun s : Finset ι ↦ ∑ i ∈ s, eig i • separatedLp (b i) (b i)) atTop (𝓝 κ)
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa only [norm_sub_rev] using hnorm

end DGRHS.Kernel
#print axioms DGRHS.Kernel.norm_kernel_spectral_remainder_sq

#print axioms DGRHS.Kernel.hasSum_kernel_diagonal_spectral
