import DGPS.Examples.PolynomialSpeciesRangeGraphFullDerivative
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! The actual mixed-parameter second equation of the same interacting graph.
Field, independent tilt and rate remain free. The full first derivative is
derived from Common before applying the second chain rule. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem pair_second (p : ℝ → PolynomialRangeParameters) (w : ℝ → E_STR02969)
    (hp : ContDiffAt ℝ 2 p 0) (hw : ContDiffAt ℝ 2 w 0) :
    iteratedDeriv 2 (fun z => (p z, w z)) 0 =
      (iteratedDeriv 2 p 0, iteratedDeriv 2 w 0) := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    iteratedDeriv_eq_iteratedFDeriv, iteratedFDeriv_prodMk hp hw (by simp)]
  rfl

/-- The true mixed-direction second graph equation. The graph inputs are
exactly Common-produced facts; its full first derivative is derived internally. -/
theorem polynomial_range_graph_mixed_second
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters) ∈ U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0)
    (hgraph : ∀ p ∈ U, polynomialRangeMap (p, ψ p) = 0)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (d : PolynomialRangeParameters) :
    polynomialOriginRangeEquiv (iteratedDeriv 2 (fun z : ℝ => ψ (z • d)) 0) =
      -iteratedDeriv 2 (fun z : ℝ => polynomialRangeMap (z • d, (0 : E_STR02969))) 0 := by
  let p := fun z : ℝ => z • d
  let w := fun z : ℝ => ψ (p z)
  let q := fun z : ℝ => (p z, w z)
  let q0 := fun z : ℝ => (p z, (0 : E_STR02969))
  have hp0 : p 0 = 0 := by simp [p]
  have hw0 : w 0 = 0 := by simp only [w, hp0, hψ0]
  have hp : ContDiff ℝ ∞ p := contDiff_id.smul contDiff_const
  have hw : ContDiffAt ℝ 2 w 0 := by
    have h : ContDiffAt ℝ 2 ψ (0 : PolynomialRangeParameters) :=
      (hψ.contDiffAt (hU.mem_nhds h0U)).of_le (by simp)
    rw [← hp0] at h
    exact h.comp 0 ((hp.of_le (by simp)).contDiffAt)
  have hp1 : HasDerivAt p d 0 := by simpa only [id_eq, one_smul] using
    (hasDerivAt_id (0 : ℝ)).smul_const d
  have hw1 : HasDerivAt w 0 0 := by
    have hψd : DifferentiableAt ℝ ψ (0 : PolynomialRangeParameters) :=
      (hψ.contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)
    have hd := hψd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hp1 hp0.symm
    rw [polynomial_range_graph_full_derivative_zero hU h0U hψ hzero hfirst, zero_apply] at hd
    exact hd
  have hq0 : q 0 = ((0 : PolynomialRangeParameters), (0 : E_STR02969)) := by simp only [q, hp0, hw0]
  have hq00 : q0 0 = ((0 : PolynomialRangeParameters), (0 : E_STR02969)) := by simp only [q0, hp0]
  have hq1 : deriv q 0 = (d, (0 : E_STR02969)) := (hp1.prodMk hw1).deriv
  have hq01 : deriv q0 0 = (d, (0 : E_STR02969)) :=
    (hp1.prodMk (hasDerivAt_const (0 : ℝ) (0 : E_STR02969))).deriv
  have hp2 : iteratedDeriv 2 p 0 = 0 := by
    rw [show p = fun z : ℝ => z • d from rfl,
      iteratedDeriv_smul_const (show ContDiffAt ℝ 2 (fun z : ℝ => z) 0 from contDiffAt_id)]
    simp [iteratedDeriv_fun_id]
  have hq : ContDiffAt ℝ 2 q 0 := ((hp.of_le (by simp)).contDiffAt).prodMk hw
  have hq0smooth : ContDiffAt ℝ 2 q0 0 :=
    ((hp.of_le (by simp)).contDiffAt).prodMk contDiffAt_const
  have hq2 : iteratedDeriv 2 q 0 = (0, iteratedDeriv 2 w 0) := by
    rw [show q = fun z => (p z, w z) from rfl,
      pair_second p w ((hp.of_le (by simp)).contDiffAt) hw, hp2]
  have hq02 : iteratedDeriv 2 q0 0 = 0 := by
    rw [show q0 = fun z => (p z, (0 : E_STR02969)) from rfl,
      pair_second p (fun _ => 0) ((hp.of_le (by simp)).contDiffAt) contDiffAt_const, hp2]
    simp
  have hMap : ContDiffAt ℝ 2 polynomialRangeMap
      ((0 : PolynomialRangeParameters), (0 : E_STR02969)) :=
    (polynomialRangeMap_smooth.of_le (by simp)).contDiffAt
  have hqMap : ContDiffAt ℝ 2 polynomialRangeMap (q 0) := by rw [hq0]; exact hMap
  have hq0Map : ContDiffAt ℝ 2 polynomialRangeMap (q0 0) := by rw [hq00]; exact hMap
  have hchain := iteratedDeriv_vcomp_two hqMap hq
  have hpure := iteratedDeriv_vcomp_two hq0Map hq0smooth
  rw [hq0, hq1, hq2] at hchain
  rw [hq00, hq01, hq02, map_zero, add_zero] at hpure
  have hpU : ∀ᶠ z : ℝ in 𝓝 0, p z ∈ U := by
    exact (hp.continuous.tendsto 0).eventually (by rw [hp0]; exact hU.mem_nhds h0U)
  have he : (polynomialRangeMap ∘ q) =ᶠ[𝓝 (0 : ℝ)] fun _ => 0 := by
    filter_upwards [hpU] with z hz
    exact hgraph _ hz
  have hz : iteratedDeriv 2 (polynomialRangeMap ∘ q) 0 = 0 := by
    rw [he.iteratedDeriv_eq 2]
    simp
  rw [hchain, ← hpure] at hz
  have hpartial : fderiv ℝ polynomialRangeMap ((0 : PolynomialRangeParameters), (0 : E_STR02969))
      (0, iteratedDeriv 2 w 0) = polynomialOriginRangeEquiv (iteratedDeriv 2 w 0) := by
    exact congrArg (fun L : E_STR02969 →L[ℝ] Y_STR02969 => L (iteratedDeriv 2 w 0))
      polynomialRangeMap_partial_origin
  rw [hpartial] at hz
  change polynomialOriginRangeEquiv (iteratedDeriv 2 w 0) =
    -iteratedDeriv 2 (polynomialRangeMap ∘ q0) 0
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hz)

end DGPS.Examples.PolynomialSpecies
