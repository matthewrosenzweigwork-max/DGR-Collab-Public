import SharpSymmetricLSI.Paper.NBody5
import SharpSymmetricLSI.Paper.R29Compact

/-!
# The Hermite Hilbert basis of `L²(γ)` and synthesis from `ℓ²` coefficients (Phase 3, lane D; R29)
-/

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ENNReal

namespace SharpLSI

theorem memLp_hermiteBasis (α : ℕ →₀ ℕ) : MemLp (hermiteBasis α) 2 gammaRef := by
  have := memLp_hermiteBasis_mul_polyProd (β := α) (I := ∅) (Finset.disjoint_empty_right _)
    (fun _ => 1)
  simpa using this

/-- The Hermite basis as vectors of `L²(γ)`. -/
def hermVec (α : ℕ →₀ ℕ) : Lp ℝ 2 gammaRef := (memLp_hermiteBasis α).toLp

theorem orthonormal_hermVec : Orthonormal ℝ hermVec := by
  rw [orthonormal_iff_ite]
  intro α β
  rw [hermVec, hermVec, inner_toLp', integral_hermiteBasis_mul]

theorem hermVec_span : (Submodule.span ℝ (Set.range hermVec))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  rw [Submodule.mem_orthogonal'] at hw
  have hz : ∀ α, ∫ z, w z * hermiteBasis α z ∂gammaRef = 0 := fun α => by
    have := hw (hermVec α) (Submodule.subset_span ⟨α, rfl⟩)
    rw [L2.inner_def] at this
    rw [← this]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_hermiteBasis α).coeFn_toLp] with x hx
    simp only [hermVec]
    rw [hx, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
    simp [mul_comm]
  exact (Lp.eq_zero_iff_ae_eq_zero).mpr (hermiteBasis_complete (Lp.memLp w) hz)

/-- The Hermite Hilbert basis of `L²(γ)`. -/
def hermHB : HilbertBasis (ℕ →₀ ℕ) ℝ (Lp ℝ 2 gammaRef) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_hermVec hermVec_span

theorem hermHB_apply (α : ℕ →₀ ℕ) : hermHB α = hermVec α := by
  rw [hermHB, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- **Synthesis**: square-summable coefficients are the Hermite coefficients of an `L²(γ)`
function, with Parseval. -/
theorem exists_hermite_synthesis {x : (ℕ →₀ ℕ) → ℝ} {B : ℝ}
    (hx : ∀ S : Finset (ℕ →₀ ℕ), ∑ α ∈ S, x α ^ 2 ≤ B) :
    ∃ F : (ℕ → ℝ) → ℝ, MemLp F 2 gammaRef ∧
      (∀ α, ∫ z, F z * hermiteBasis α z ∂gammaRef = x α) ∧
      HasSum (fun α => x α ^ 2) (∫ z, F z ^ 2 ∂gammaRef) := by
  have hsum : Summable fun α => x α ^ 2 := summable_of_sum_le (fun α => sq_nonneg _) hx
  have hmem : Memℓp x 2 := by
    refine memℓp_gen ?_
    simpa [Real.norm_eq_abs, sq_abs] using hsum
  set v : lp (fun _ : ℕ →₀ ℕ => ℝ) 2 := ⟨x, hmem⟩
  set G := hermHB.repr.symm v
  have hcoef : ∀ α, ⟪G, hermHB α⟫_ℝ = x α := fun α => by
    have h1 : hermHB.repr G α = x α := by simp [G, v]
    rw [HilbertBasis.repr_apply_apply, real_inner_comm] at h1
    exact h1
  have hint : ∀ α, ⟪G, hermHB α⟫_ℝ = ∫ z, G z * hermiteBasis α z ∂gammaRef := fun α => by
    rw [hermHB_apply, hermVec, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_hermiteBasis α).coeFn_toLp] with z hz
    rw [hz, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
    simp [mul_comm]
  refine ⟨G, Lp.memLp G, fun α => (hint α).symm.trans (hcoef α), ?_⟩
  have h := hermHB.hasSum_inner_mul_inner G G
  have hself : ⟪G, G⟫_ℝ = ∫ z, G z ^ 2 ∂gammaRef := by
    rw [L2.inner_def]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp [real_inner_eq_re_inner, sq]
  rw [hself] at h
  convert h using 1
  funext α
  rw [hcoef, real_inner_comm, hcoef, sq]

end SharpLSI
