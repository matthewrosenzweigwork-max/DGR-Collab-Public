import DGPS.Examples.PolynomialSpeciesRangeCommon

/-! The full first derivative of the actual interacting graph vanishes at the
origin. Field, independent tilt and rate directions are controlled by the true
zero-amplitude equilibrium family, not by differentiating the selected root. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

/-- Common already produces all hypotheses for this full origin derivative.
This supplies the first-jet input for mixed field-amplitude second variations. -/
theorem polynomial_range_graph_full_derivative_zero
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters) ∈ U)
    (hψ : ContDiffOn ℝ ∞ ψ U)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0) :
    fderiv ℝ ψ (0 : PolynomialRangeParameters) = 0 := by
  have hd : DifferentiableAt ℝ ψ (0 : PolynomialRangeParameters) :=
    (hψ.contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)
  have hline (d : PolynomialRangeParameters) :
      HasDerivAt (fun z : ℝ => ψ (z • d)) (fderiv ℝ ψ 0 d) 0 := by
    have hs : HasDerivAt (fun z : ℝ => z • d) d 0 := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const d
    exact hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hs (by simp)
  apply ContinuousLinearMap.ext
  intro p
  rcases p with ⟨a, b, ⟨h, s⟩, γ⟩
  let α : PolynomialRangeParameters := (a, b, (0, 0), 0)
  let β : PolynomialRangeParameters := (0, 0, (h, s), γ)
  have hα : fderiv ℝ ψ 0 α = 0 := by
    let f := fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)
    let embed := fun x : ℝ × ℝ => ((x.1, x.2, (0, 0), 0) : PolynomialRangeParameters)
    have he : DifferentiableAt ℝ embed 0 := by dsimp only [embed]; fun_prop
    have he0 : embed 0 = 0 := by ext <;> rfl
    have hf : DifferentiableAt ℝ f 0 := by
      have hψd : DifferentiableAt ℝ ψ (embed 0) := by rw [he0]; exact hd
      exact hψd.comp 0 he
    have hs : HasDerivAt (fun z : ℝ => z • (a, b)) (a, b) 0 := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const (a, b)
    have hg := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hs (by simp)
    rw [hfirst, zero_apply] at hg
    have hg' : HasDerivAt (fun z : ℝ => ψ (z • α)) 0 0 := by
      convert hg using 1 <;> simp only [f, α, Function.comp_def, Prod.smul_mk, smul_zero, smul_eq_mul, mul_zero]
    exact (hline α).unique hg'
  have hβ : fderiv ℝ ψ 0 β = 0 := by
    have hp : Continuous (fun z : ℝ => z • β) := continuous_id.smul continuous_const
    have hpU : ∀ᶠ z : ℝ in 𝓝 0, z • β ∈ U :=
      (hp.tendsto 0).eventually (by change U ∈ 𝓝 ((0 : ℝ) • β); simpa only [zero_smul] using hU.mem_nhds h0U)
    have he : (fun z : ℝ => ψ (z • β)) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [hpU] with z hz
      have hβz : z • β = ((0, 0, (z * h, z * s), z * γ) : PolynomialRangeParameters) := by
        simp only [β, Prod.smul_mk, smul_zero, smul_eq_mul, mul_zero]
      rw [hβz] at hz ⊢
      exact hzero _ _ _ hz
    exact (hline β).unique ((hasDerivAt_const (0 : ℝ) (0 : E_STR02969)).congr_of_eventuallyEq he)
  change fderiv ℝ ψ 0 ((a, b, (h, s), γ) : PolynomialRangeParameters) = 0
  have he : ((a, b, (h, s), γ) : PolynomialRangeParameters) = α + β := by
    ext <;> simp [α, β]
  rw [he, map_add, hα, hβ, add_zero]

end DGPS.Examples.PolynomialSpecies
