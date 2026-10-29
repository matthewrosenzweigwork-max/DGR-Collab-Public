import SharpSymmetricLSI.Paper.FormDuality1
import SharpSymmetricLSI.Paper.GaussForm29

/-!
# R32 (8.8), part 2: the Hermite basis in the diagonal variables

For `ξ : ℕ → (ℕ → ℝ) → ℝ` with `γ.map ξ = γ_ref = N(0,1)^{⊗ℕ}` and Hermite completeness (GaussForm29),
`H_α = h_α ∘ ξ` is a Hilbert basis of `L²(γ)` (`hxiBasis`). Consequences: the coefficient formula
`⟨H_α, f⟩ = ∫ H_α f dγ`, the expansion `∑ ⟨H_α, f⟩ H_α = f` and Parseval.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace SharpLSI

/-- `H_α(z) = h_α(ξ(z))`. -/
noncomputable def Hxi (ξ : ℕ → (ℕ → ℝ) → ℝ) (α : ℕ →₀ ℕ) (z : ℕ → ℝ) : ℝ :=
  hermiteBasis α (fun j => ξ j z)

theorem memLp_hermiteBasis_gammaRef (α : ℕ →₀ ℕ) : MemLp (hermiteBasis α) 2 gammaRef := by
  have e : hermiteBasis α = fun z => ∏ n ∈ α.support, (hermiteQ (α n)).eval (z n) := by
    funext z
    rw [hermiteBasis_eq_prod α subset_rfl z]
    exact Finset.prod_congr rfl fun n _ => hermiteN_eq_eval _ _
  rw [e]
  exact memLp_polyProd α.support fun n => hermiteQ (α n)

section basis
variable {γ : Measure (ℕ → ℝ)} [IsProbabilityMeasure γ] {ξ : ℕ → (ℕ → ℝ) → ℝ}
  (hΞ : AEMeasurable (fun z => fun j => ξ j z) γ)
  (hmap : γ.map (fun z => fun j => ξ j z) = gammaRef)

include hΞ hmap in
theorem memLp_Hxi (α : ℕ →₀ ℕ) : MemLp (Hxi ξ α) 2 γ := by
  have h := memLp_hermiteBasis_gammaRef α
  rw [← hmap] at h
  exact (memLp_map_measure_iff (measurable_hermiteBasis α).aestronglyMeasurable hΞ).mp h

include hΞ hmap in
theorem integral_Hxi_mul (α β : ℕ →₀ ℕ) :
    ∫ z, Hxi ξ α z * Hxi ξ β z ∂γ = if α = β then 1 else 0 := by
  have hm : AEStronglyMeasurable (fun y => hermiteBasis α y * hermiteBasis β y)
      (γ.map (fun z => fun j => ξ j z)) :=
    ((measurable_hermiteBasis α).mul (measurable_hermiteBasis β)).aestronglyMeasurable
  rw [← integral_hermiteBasis_mul α β, ← hmap, integral_map hΞ hm]
  rfl

include hΞ hmap in
theorem orthonormal_Hxi :
    Orthonormal ℝ (fun α : ℕ →₀ ℕ => (memLp_Hxi hΞ hmap α).toLp (Hxi ξ α)) := by
  rw [orthonormal_iff_ite]
  intro α β
  rw [L2.inner_def, ← integral_Hxi_mul hΞ hmap α β]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_Hxi hΞ hmap α).coeFn_toLp, (memLp_Hxi hΞ hmap β).coeFn_toLp] with z h1 h2
  rw [h1, h2, real_inner_eq_re_inner, RCLike.re_to_real, real_inner_comm]
  simp [mul_comm]

variable (hcomp : ∀ F : (ℕ → ℝ) → ℝ, MemLp F 2 γ →
    (∀ α : ℕ →₀ ℕ, ∫ z, F z * hermiteBasis α (fun j => ξ j z) ∂γ = 0) → F =ᵐ[γ] 0)

include hΞ hmap hcomp in
theorem span_Hxi_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range fun α : ℕ →₀ ℕ =>
      (memLp_Hxi hΞ hmap α).toLp (Hxi ξ α)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro g hg
  have horth : ∀ α, ∫ z, g z * hermiteBasis α (fun j => ξ j z) ∂γ = 0 := fun α => by
    have h := (Submodule.mem_orthogonal' _ g).mp hg _ (Submodule.subset_span ⟨α, rfl⟩)
    rw [L2.inner_def] at h
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_Hxi hΞ hmap α).coeFn_toLp] with z h1
    rw [real_inner_eq_re_inner, RCLike.re_to_real]
    simp [h1, Hxi, mul_comm]
  have h0 := hcomp g (Lp.memLp g) horth
  exact Lp.eq_zero_iff_ae_eq_zero.mpr h0

/-- **The Hermite basis `h_α(ξ)` of `L²(γ)`.** -/
noncomputable def hxiBasis : HilbertBasis (ℕ →₀ ℕ) ℝ (Lp ℝ 2 γ) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_Hxi hΞ hmap) (span_Hxi_orthogonal_eq_bot hΞ hmap hcomp)

theorem hxiBasis_apply (α : ℕ →₀ ℕ) :
    hxiBasis hΞ hmap hcomp α = (memLp_Hxi hΞ hmap α).toLp (Hxi ξ α) := by
  unfold hxiBasis; rw [HilbertBasis.coe_mkOfOrthogonalEqBot]

include hΞ hmap in
/-- The Hermite coefficients. -/
theorem inner_toLp_Hxi {f : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 γ) (α : ℕ →₀ ℕ) :
    ⟪(memLp_Hxi hΞ hmap α).toLp (Hxi ξ α), hf.toLp f⟫_ℝ = ∫ z, Hxi ξ α z * f z ∂γ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_Hxi hΞ hmap α).coeFn_toLp, hf.coeFn_toLp] with z h1 h2
  rw [h1, h2, real_inner_eq_re_inner, RCLike.re_to_real]
  simp [mul_comm]

end basis

end SharpLSI
