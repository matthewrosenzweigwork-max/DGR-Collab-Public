import DGPS.Lipschitz.T01UnrestrictedLower
import DGPS.Lipschitz.T01ReferenceEigenbasis
import DGPS.Lipschitz.T01SpectralBridge
import FullLabeledLSI.Paper.HybridGroundAltH

/-!
# Actual reference moments and the finite-rank hybrid comparison

The equilibrium witness below is shared by its reference measure, spectral basis, and centered
interaction kernel. The hybrid comparison uses the existing Gaussian ground-state calculation
at its structural hypotheses, without the legacy semiconvex equilibrium wrapper.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace DGPS.Lipschitz

open KernelApproximation SharpLSI.FL

/-- The actual direct-Lipschitz equilibrium supplies the reference eigenbasis and all hybrid
moments used in labeled replacement, with one common spectral witness. -/
theorem exists_equilibrium_hybrid_reference {d : ℕ}
    (A : InteractionData d) (hA : LipschitzData A) (hd : 0 < d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν) :
    ∃ (S : Spec d) (aux : Aux S) (D : KData d),
      S.mu = (μ : Measure (Torus d)) ∧ D.K = centeredKernel A S.mu ∧
      SharpLSI.IsRefEigenbasis S.mu S.v S.lam ∧
      (∀ j, Gross.C1T (S.v j)) ∧ S.lam 0 = 0 ∧ 0 < S.lam 1 ∧
      ∀ J : ℕ, HybridPolyMoment S.mu S.v S.lam J := by
  obtain ⟨S, aux, D, hS, hmono, hzero, hpos, hC1, heig, hD⟩ :=
    exists_equilibrium_spectral_data A hA hd μ hμ
  have he := legacy_reference_eigenbasis S aux hmono heig
  let P : BoundedPositiveReference d :=
    { density := S.w
      measurable_density := S.meas
      lower := S.c
      upper := S.C
      lower_pos := S.pos
      lower_le := S.bound.mono fun _ hx => hx.1
      le_upper := S.bound.mono fun _ hx => hx.2
      mass_one := S.prob }
  have hP : P.measure = S.mu := rfl
  have hC1' : ∀ j, Gross.C1T (S.v j) := hC1
  have hpos' : 0 < S.lam 1 := by simpa only [hzero] using hpos
  refine ⟨S, aux, D, hS, hD, he, hC1', hzero, hpos', fun J => ?_⟩
  have heP : SharpLSI.IsRefEigenbasis P.measure S.v S.lam := by rw [hP]; exact he
  simpa only [hP] using
    hybrid_moments_of_campaign_reference P heP hC1' hzero hpos' J

/-- Finite-rank hybrid ground-state nonnegativity for a campaign reference. The matrix
positivity and inverse are explicit finite-rank inputs; no particle compactness is assumed. -/
theorem hybrid_comparison_of_campaign_reference {d N J : ℕ}
    (P : BoundedPositiveReference d) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : SharpLSI.IsRefEigenbasis P.measure e lam)
    (hC1 : ∀ j, Gross.C1T (e j)) (hlam0 : lam 0 = 0)
    {W : Torus d → Torus d → ℝ} (A : FiniteRankApprox W P.measure e) {R : ℕ}
    (hJ : ∀ i ∈ A.s R, i < J) {σ : ℝ} (hσ : 0 < σ)
    (hpos : PosTm A R J σ) {C : ℕ → ℕ → ℝ}
    (hC : SharpLSI.IsInverseOfIPlus (A.a R) C)
    (Bs : Finset (Fin N)) (hB : Bs.card < N)
    (c : (Fin N → Fin (J + 1)) → ℝ) :
    0 ≤ (∑ j, (∑ i, lam (j i)) * c j ^ 2)
      + ∫ w, polyB e c Bs w ^ 2 * vR A lam R (zext (Gcoll Bs w.2))
          ∂hybMeasure P.measure N J
      - (bRate P.measure lam C).toReal / 2 *
          ((SharpLSI.ent (hybMeasure P.measure N J) (fun w => polyB e c Bs w ^ 2)).toReal
            + ∫ w, polyB e c Bs w ^ 2 * uR A R (zext (Gcoll Bs w.2))
                ∂hybMeasure P.measure N J
            + Real.log (kappaR A R) * ∫ w, polyB e c Bs w ^ 2
                ∂hybMeasure P.measure N J) := by
  obtain ⟨x, hx, hy⟩ := (P.lower_le.and P.le_upper).exists
  have hupper : 0 < P.upper := P.lower_pos.trans_le (hx.trans hy)
  obtain ⟨M, hM⟩ := (hC1 1).bounded
  have hrl : rLS P.measure ≤ ENNReal.ofReal (lam 1) :=
    rLS_le_lam_one_of_bdd P.measure_ac_haar he (Filter.Eventually.of_forall hM)
  exact HLA.hybrid_core A he P.measure_ac_haar P.haar_ac_measure hC1
    (fun _ => Filter.EventuallyEq.refl _ _) he.zero hlam0
    (div_pos P.lower_pos hupper) (legacy_reference_lsi_lower_bound P)
    hrl hJ hσ hpos hC Bs hB c

end DGPS.Lipschitz
