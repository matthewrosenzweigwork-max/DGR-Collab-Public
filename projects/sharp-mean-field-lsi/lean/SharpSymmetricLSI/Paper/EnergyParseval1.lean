import SharpSymmetricLSI.Defs.D16_GaussianLimit
import SharpSymmetricLSI.Paper.CondForce1

/-!
# Parseval in `L²(μ)` for a reference eigenbasis (Phase 3, lane D; R24)
-/

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

theorem IsRefEigenbasis.memLp (he : IsRefEigenbasis μ e lam) (i : ℕ) : MemLp (e i) 2 μ :=
  (he.memH1 i).2.1

/-- The eigenbasis as vectors of `L²(μ)`. -/
def refVec (he : IsRefEigenbasis μ e lam) (i : ℕ) : Lp ℝ 2 μ := (he.memLp i).toLp

theorem inner_toLp {f g : Torus d → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp, hg.toLp⟫_ℝ = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
  simp [mul_comm]

theorem orthonormal_refVec (he : IsRefEigenbasis μ e lam) : Orthonormal ℝ (refVec he) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [refVec, refVec, inner_toLp, he.orthonormal]

theorem refVec_span (he : IsRefEigenbasis μ e lam) :
    (Submodule.span ℝ (Set.range (refVec he)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  rw [Submodule.mem_orthogonal'] at hw
  have hz : ∀ j, ∫ x, w x * e j x ∂μ = 0 := fun j => by
    have := hw (refVec he j) (Submodule.subset_span ⟨j, rfl⟩)
    rw [L2.inner_def] at this
    rw [← this]
    refine integral_congr_ae ?_
    filter_upwards [(he.memLp j).coeFn_toLp] with x hx
    simp only [refVec]
    rw [hx, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
    simp [mul_comm]
  have h0 := he.complete w (Lp.memLp w) hz
  exact (Lp.eq_zero_iff_ae_eq_zero).mpr h0

/-- The reference basis as a Hilbert basis of `L²(μ)`. -/
def refHB (he : IsRefEigenbasis μ e lam) : HilbertBasis ℕ ℝ (Lp ℝ 2 μ) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_refVec he) (refVec_span he)

theorem refHB_apply (he : IsRefEigenbasis μ e lam) (i : ℕ) : refHB he i = refVec he i := by
  rw [refHB, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- **Parseval in `L²(μ)`.** -/
theorem hasSum_sq_coeff (he : IsRefEigenbasis μ e lam) {f : Torus d → ℝ} (hf : MemLp f 2 μ) :
    HasSum (fun i => (∫ x, f x * e i x ∂μ) ^ 2) (∫ x, f x ^ 2 ∂μ) := by
  have h := (refHB he).hasSum_inner_mul_inner hf.toLp hf.toLp
  have hc : ∀ i, ⟪hf.toLp, (refHB he) i⟫_ℝ * ⟪(refHB he) i, hf.toLp⟫_ℝ =
      (∫ x, f x * e i x ∂μ) ^ 2 := fun i => by
    have hb : (refHB he) i = refVec he i := by
      simp only [refHB, HilbertBasis.coe_mkOfOrthogonalEqBot]
    rw [hb, refVec, real_inner_comm (hf.toLp), inner_toLp hf (he.memLp i), sq]
  rw [show (fun i => ⟪hf.toLp, (refHB he) i⟫_ℝ * ⟪(refHB he) i, hf.toLp⟫_ℝ) =
    fun i => (∫ x, f x * e i x ∂μ) ^ 2 from funext hc, inner_toLp hf hf] at h
  simpa [sq] using h

/-- The partial sums converge in `L²(μ)`. -/
theorem tendsto_partial_sum (he : IsRefEigenbasis μ e lam) {f : Torus d → ℝ} (hf : MemLp f 2 μ) :
    Tendsto (fun n => ∫ x, (f x - ∑ i ∈ Finset.range n, (∫ y, f y * e i y ∂μ) * e i x) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  set c : ℕ → ℝ := fun i => ∫ y, f y * e i y ∂μ
  have hs := hasSum_sq_coeff he hf
  -- `∫ (f - S_n)² = ∫ f² - ∑_{i<n} c_i²`
  have hei : ∀ i, Integrable (fun x => f x * e i x) μ := fun i => hf.integrable_mul (he.memLp i)
  have hSL : ∀ n, MemLp (fun x => ∑ i ∈ Finset.range n, c i * e i x) 2 μ := fun n =>
    memLp_finset_sum _ fun i _ => (he.memLp i).const_mul (c i)
  have key : ∀ n, ∫ x, (f x - ∑ i ∈ Finset.range n, c i * e i x) ^ 2 ∂μ =
      ∫ x, f x ^ 2 ∂μ - ∑ i ∈ Finset.range n, c i ^ 2 := by
    intro n
    have hf2 := hf.integrable_sq
    have hcross : ∫ x, f x * ∑ i ∈ Finset.range n, c i * e i x ∂μ = ∑ i ∈ Finset.range n, c i ^ 2 := by
      simp_rw [Finset.mul_sum]
      rw [integral_finset_sum (f := fun i x => f x * (c i * e i x)) _ fun i _ =>
        ((hei i).const_mul (c i)).congr (Eventually.of_forall fun x => by ring)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (fun x => f x * (c i * e i x)) = fun x => c i * (f x * e i x) by funext x; ring,
        integral_const_mul, sq]
    have hsq : ∫ x, (∑ i ∈ Finset.range n, c i * e i x) ^ 2 ∂μ = ∑ i ∈ Finset.range n, c i ^ 2 := by
      have : ∀ x, (∑ i ∈ Finset.range n, c i * e i x) ^ 2 =
          ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, c i * c j * (e i x * e j x) := fun x => by
        rw [sq, Finset.sum_mul_sum]; refine Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => by ring
      simp_rw [this]
      rw [integral_finset_sum (f := fun i x => ∑ j ∈ Finset.range n, c i * c j * (e i x * e j x))
        _ fun i _ => integrable_finset_sum _ fun j _ =>
        ((he.memLp i).integrable_mul (he.memLp j)).const_mul _]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [integral_finset_sum (f := fun j x => c i * c j * (e i x * e j x)) _ fun j _ =>
        ((he.memLp i).integrable_mul (he.memLp j)).const_mul _]
      simp_rw [integral_const_mul, he.orthonormal]
      simp [Finset.sum_ite_eq, hi, sq]
    have e2 : ∀ x, (f x - ∑ i ∈ Finset.range n, c i * e i x) ^ 2 =
        f x ^ 2 - 2 * (f x * ∑ i ∈ Finset.range n, c i * e i x) +
          (∑ i ∈ Finset.range n, c i * e i x) ^ 2 := fun x => by ring
    simp_rw [e2]
    rw [integral_add (f := fun x => f x ^ 2 - 2 * (f x * ∑ i ∈ Finset.range n, c i * e i x))
        (g := fun x => (∑ i ∈ Finset.range n, c i * e i x) ^ 2)
        (hf2.sub ((hf.integrable_mul (hSL n)).const_mul 2)) (hSL n).integrable_sq,
      integral_sub (f := fun x => f x ^ 2) (g := fun x => 2 * (f x * ∑ i ∈ Finset.range n, c i * e i x))
        hf2 ((hf.integrable_mul (hSL n)).const_mul 2), integral_const_mul, hcross, hsq]
    ring
  refine (tendsto_congr key).mpr ?_
  have := hs.tendsto_sum_nat
  have h2 := (tendsto_const_nhds (x := ∫ x, f x ^ 2 ∂μ)).sub this
  rwa [sub_self] at h2

end SharpLSI
