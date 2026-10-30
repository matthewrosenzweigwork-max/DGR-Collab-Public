import DGPS.Examples.PolynomialSpeciesScaledFactorIdentification
import DGPS.Examples.PolynomialSpeciesQuarticNondegeneracy
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! Stock IFT for the ACTUAL same-graph fourth factor. Its genuine zero slice
identifies the actual three-equation Jacobian with the explicitly proved
physical quartic Jacobian. No branch or nondegeneracy premise is supplied. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

/-- Independent parameter order: physical field and scaled reference tilt. -/
abbrev PolynomialFactorParameters := ℝ × ℝ

private def factorCoordinates (q : PolynomialFactorParameters × PolynomialFactorUnknowns) :
    ℝ × PolynomialScaledCoefficients := (q.1.1, (q.2.1.1, q.2.1.2, q.2.2, q.1.2))
private def factorValue (ψ : PolynomialRangeParameters → E_STR02969)
    (q : PolynomialFactorParameters × PolynomialFactorUnknowns) : ℝ :=
  polynomialScaledDeficitFactor ψ (factorCoordinates q)

/-- The ACTUAL factor equations, in endomorphism order (amplitude gradient,value).
The independent tilt remains a parameter; amplitude and rate are unknowns. -/
def polynomialFactorCriticalSystem (ψ : PolynomialRangeParameters → E_STR02969)
    (q : PolynomialFactorParameters × PolynomialFactorUnknowns) : PolynomialFactorUnknowns :=
  ((fderiv ℝ (fun x : ℝ × ℝ => factorValue ψ (q.1, (x, q.2.2))) q.2.1 (1, 0),
    fderiv ℝ (fun x : ℝ × ℝ => factorValue ψ (q.1, (x, q.2.2))) q.2.1 (0, 1)),
    factorValue ψ q)

private theorem system_contDiffAt (ψ : PolynomialRangeParameters → E_STR02969)
    (q : PolynomialFactorParameters × PolynomialFactorUnknowns)
    (hF : ContDiffAt ℝ ∞ (factorValue ψ) q) :
    ContDiffAt ℝ ∞ (polynomialFactorCriticalSystem ψ) q := by
  let lift := fun t : (PolynomialFactorParameters × PolynomialFactorUnknowns) × (ℝ × ℝ) =>
    (t.1.1, (t.2, t.1.2.2))
  have hlift : ContDiff ℝ ∞ lift := by dsimp only [lift]; fun_prop
  have huncurry : ContDiffAt ℝ ∞ (Function.uncurry
      (fun t : PolynomialFactorParameters × PolynomialFactorUnknowns =>
        fun x : ℝ × ℝ => factorValue ψ (t.1, (x, t.2.2)))) (q, q.2.1) :=
    hF.comp (q, q.2.1) hlift.contDiffAt
  have hD : ContDiffAt ℝ ∞ (fun t : PolynomialFactorParameters × PolynomialFactorUnknowns =>
      fderiv ℝ (fun x : ℝ × ℝ => factorValue ψ (t.1, (x, t.2.2))) t.2.1) q :=
    ContDiffAt.fderiv huncurry contDiffAt_snd.fst (by simp)
  exact ((hD.clm_apply contDiffAt_const).prodMk (hD.clm_apply contDiffAt_const)).prodMk hF

/-- Exact identity of the actual zero-field three-equation system with the
physical quartic system, for every independent tilt and every unknown. -/
theorem polynomialFactorCriticalSystem_origin
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (σ : ℝ) (z : PolynomialFactorUnknowns) :
    polynomialFactorCriticalSystem ψ ((0, σ), z) = polynomialQuarticCriticalSystem z := by
  have hz := polynomialScaledDeficitFactor_zero hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
  have hamp : (fun x : ℝ × ℝ => factorValue ψ ((0, σ), (x, z.2))) =
      fun x => polynomialScaledQuartic (x.1, x.2, z.2, 0) := by
    funext x
    change polynomialScaledDeficitFactor ψ (0, (x.1, x.2, z.2, σ)) = _
    rw [hz]
    rfl
  have hval : factorValue ψ ((0, σ), z) = polynomialScaledQuartic (z.1.1, z.1.2, z.2, 0) := by
    change polynomialScaledDeficitFactor ψ (0, (z.1.1, z.1.2, z.2, σ)) = _
    rw [hz]
    rfl
  simp only [polynomialFactorCriticalSystem, hamp, hval]
  exact (polynomialQuarticCriticalSystem_eq z).symm

/-- The stock smooth IFT gives a genuine locally unique actual-factor branch
at EACH of the two shared coefficient minima. All data refer to the supplied
SAME graph. Its actual zero slice proves nondegeneracy internally; no desired
Jacobian, branch, optimizer classification or rate conclusion is a premise. -/
theorem polynomial_actual_factor_implicit_branch
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (j : Fin 2) :
    ∃ β : PolynomialFactorParameters → PolynomialFactorUnknowns,
      β 0 = polynomialQuarticCriticalBase j ∧ ContDiffAt ℝ ∞ β 0 ∧
      (∀ᶠ p in 𝓝 (0 : PolynomialFactorParameters), polynomialFactorCriticalSystem ψ (p, β p) = 0) ∧
      ∀ᶠ q in 𝓝 ((0 : PolynomialFactorParameters), polynomialQuarticCriticalBase j),
        polynomialFactorCriticalSystem ψ q = 0 ↔ β q.1 = q.2 := by
  obtain ⟨O, hO, h0O, _hOU, hC, _hfactor, _hz, _hlimits⟩ :=
    polynomialScaledDeficitFactor_identified hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
  let z := polynomialQuarticCriticalBase j
  let q : PolynomialFactorParameters × PolynomialFactorUnknowns := (0, z)
  have hcoord : ContDiff ℝ ∞ factorCoordinates := by unfold factorCoordinates; fun_prop
  have hmem : factorCoordinates q ∈ O := h0O _
  have hF : ContDiffAt ℝ ∞ (factorValue ψ) q :=
    (hC.contDiffAt (hO.mem_nhds hmem)).comp q hcoord.contDiffAt
  have hS := system_contDiffAt ψ q hF
  have horigin : (fun w : PolynomialFactorUnknowns => polynomialFactorCriticalSystem ψ (0, w)) =
      polynomialQuarticCriticalSystem := by
    funext w
    exact polynomialFactorCriticalSystem_origin hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst 0 w
  have hbase : polynomialFactorCriticalSystem ψ q = 0 := by
    change polynomialFactorCriticalSystem ψ (0, z) = 0
    rw [congrFun horigin]
    exact (polynomialQuarticCriticalBase_nondegenerate j).1
  have hcomp := (hS.differentiableAt (by simp)).hasFDerivAt.comp z
    ((hasFDerivAt_const (0 : PolynomialFactorParameters) z).prodMk (hasFDerivAt_id z))
  have hpartial : fderiv ℝ (polynomialFactorCriticalSystem ψ) q ∘L
      ContinuousLinearMap.inr ℝ PolynomialFactorParameters PolynomialFactorUnknowns =
      fderiv ℝ polynomialQuarticCriticalSystem z := by
    calc
      _ = fderiv ℝ (fun w : PolynomialFactorUnknowns => polynomialFactorCriticalSystem ψ (0, w)) z := by
        exact hcomp.fderiv.symm
      _ = _ := by rw [horigin]
  have hunit := (polynomialQuarticCriticalBase_nondegenerate j).2
  have hinvertible : (fderiv ℝ (polynomialFactorCriticalSystem ψ) q ∘L
      ContinuousLinearMap.inr ℝ PolynomialFactorParameters PolynomialFactorUnknowns).IsInvertible := by
    rw [hpartial]
    have hb := ContinuousLinearMap.isUnit_iff_bijective.mp hunit
    exact ⟨ContinuousLinearEquiv.ofBijective _
      (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2), rfl⟩
  let β := hS.implicitFunction (by simp) hinvertible
  refine ⟨β, hS.implicitFunction_apply_self (by simp) hinvertible,
    hS.contDiffAt_implicitFunction (by simp) hinvertible, ?_, ?_⟩
  · simpa only [hbase] using hS.eventually_apply_implicitFunction (by simp) hinvertible
  · simpa only [hbase] using hS.eventually_apply_eq_iff_implicitFunction (by simp) hinvertible

/-- The stock smooth IFT gives a genuine locally unique actual-factor branch
at EACH of the two shared coefficient minima and EVERY bounded-tilt accumulation base. No convergence of the physical scaled tilt to zero is assumed. All data refer to the supplied
SAME graph. Its actual zero slice proves nondegeneracy internally; no desired
Jacobian, branch, optimizer classification or rate conclusion is a premise. -/
theorem polynomial_actual_factor_implicit_branch_at_tilt
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (σ₀ : ℝ) (j : Fin 2) :
    ∃ β : PolynomialFactorParameters → PolynomialFactorUnknowns,
      β (0, σ₀) = polynomialQuarticCriticalBase j ∧ ContDiffAt ℝ ∞ β (0, σ₀) ∧
      (∀ᶠ p in 𝓝 ((0, σ₀) : PolynomialFactorParameters), polynomialFactorCriticalSystem ψ (p, β p) = 0) ∧
      ∀ᶠ q in 𝓝 (((0, σ₀) : PolynomialFactorParameters), polynomialQuarticCriticalBase j),
        polynomialFactorCriticalSystem ψ q = 0 ↔ β q.1 = q.2 := by
  obtain ⟨O, hO, h0O, _hOU, hC, _hfactor, _hz, _hlimits⟩ :=
    polynomialScaledDeficitFactor_identified hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
  let z := polynomialQuarticCriticalBase j
  let q : PolynomialFactorParameters × PolynomialFactorUnknowns := ((0, σ₀), z)
  have hcoord : ContDiff ℝ ∞ factorCoordinates := by unfold factorCoordinates; fun_prop
  have hmem : factorCoordinates q ∈ O := h0O _
  have hF : ContDiffAt ℝ ∞ (factorValue ψ) q :=
    (hC.contDiffAt (hO.mem_nhds hmem)).comp q hcoord.contDiffAt
  have hS := system_contDiffAt ψ q hF
  have horigin : (fun w : PolynomialFactorUnknowns => polynomialFactorCriticalSystem ψ ((0, σ₀), w)) =
      polynomialQuarticCriticalSystem := by
    funext w
    exact polynomialFactorCriticalSystem_origin hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst σ₀ w
  have hbase : polynomialFactorCriticalSystem ψ q = 0 := by
    change polynomialFactorCriticalSystem ψ ((0, σ₀), z) = 0
    rw [congrFun horigin]
    exact (polynomialQuarticCriticalBase_nondegenerate j).1
  have hcomp := (hS.differentiableAt (by simp)).hasFDerivAt.comp z
    ((hasFDerivAt_const ((0, σ₀) : PolynomialFactorParameters) z).prodMk (hasFDerivAt_id z))
  have hpartial : fderiv ℝ (polynomialFactorCriticalSystem ψ) q ∘L
      ContinuousLinearMap.inr ℝ PolynomialFactorParameters PolynomialFactorUnknowns =
      fderiv ℝ polynomialQuarticCriticalSystem z := by
    calc
      _ = fderiv ℝ (fun w : PolynomialFactorUnknowns => polynomialFactorCriticalSystem ψ ((0, σ₀), w)) z := by
        exact hcomp.fderiv.symm
      _ = _ := by rw [horigin]
  have hunit := (polynomialQuarticCriticalBase_nondegenerate j).2
  have hinvertible : (fderiv ℝ (polynomialFactorCriticalSystem ψ) q ∘L
      ContinuousLinearMap.inr ℝ PolynomialFactorParameters PolynomialFactorUnknowns).IsInvertible := by
    rw [hpartial]
    have hb := ContinuousLinearMap.isUnit_iff_bijective.mp hunit
    exact ⟨ContinuousLinearEquiv.ofBijective _
      (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2), rfl⟩
  let β := hS.implicitFunction (by simp) hinvertible
  refine ⟨β, hS.implicitFunction_apply_self (by simp) hinvertible,
    hS.contDiffAt_implicitFunction (by simp) hinvertible, ?_, ?_⟩
  · simpa only [hbase] using hS.eventually_apply_implicitFunction (by simp) hinvertible
  · simpa only [hbase] using hS.eventually_apply_eq_iff_implicitFunction (by simp) hinvertible

end DGPS.Examples.PolynomialSpecies
