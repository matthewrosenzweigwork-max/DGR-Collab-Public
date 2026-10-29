import FullLabeledLSI.Nonvacuity.Prop82.Subthreshold
import SharpSymmetricLSI.Paper.FourierSynth

/-!
# Rellich extraction for the genuine minimizing sequence

This is the compactness portion only. Passing the nonlinear functionals to
the limit, excluding the zero-gap limit, and choosing a smooth strictly
positive representative are not consequences asserted by this file.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI.FL.Prop82

/-- Strong `L2` convergence of square roots and weak `L2` convergence of their
gradients, with the full-domain quotient still converging to `realRate`. -/
theorem exists_rellich_minimizing_sequence (hR : realRate < aCos * (3 / 2)) :
    ∃ rho : Nat → Torus 1 → Real,
      (∀ n, Admissible cosV (cosW 1) (rho n)) ∧
      (∀ n, entropy (rho n) < 6 ∧ fisher (rho n) < 18 * aCos) ∧
      Tendsto (fun n => realDiss (rho n) / (2 * realGap (rho n)))
        atTop (𝓝 realRate) ∧
      ∃ (u : Torus 1 → Real) (g : Torus 1 → Fin 1 → Real),
        MemLp u 2 (haar 1) ∧
        (∀ j, MemLp (fun x => g x j) 2 (haar 1)) ∧
        IsWeakGrad u g ∧
        Tendsto (fun n => ∫ x, (Real.sqrt (rho n x) - u x) ^ 2 ∂haar 1)
          atTop (𝓝 0) ∧
        ∀ j (h : Torus 1 → Real), MemLp h 2 (haar 1) →
          Tendsto (fun n => ∫ x, weakGrad (fun y => Real.sqrt (rho n y)) x j * h x ∂haar 1)
            atTop (𝓝 (∫ x, g x j * h x ∂haar 1)) := by
  obtain ⟨rho, ha, hq, hb, hlim⟩ := exists_subthreshold_minimizing_sequence hR
  let u : Nat → Torus 1 → Real := fun n x => Real.sqrt (rho n x)
  let g : Nat → Torus 1 → Fin 1 → Real := fun n => weakGrad (u n)
  have hH : ∀ n, MemH1 (haar 1) (u n) := fun n => (ha n).2.2.1
  have hw : ∀ n, IsWeakGrad (u n) (g n) := fun n => isWeakGrad_weakGrad (hH n).1
  have hg : ∀ n j, MemLp (fun x => g n x j) 2 (haar 1) := by
    intro n j
    refine (hH n).2.2.of_le ((hw n).aestronglyMeasurable_grad j) ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact abs_le_sqrt_sqNorm _ j
  have hbound : ∀ n, (∫ x, u n x ^ 2 ∂haar 1) +
      (∑ j : Fin 1, ∫ x, g n x j ^ 2 ∂haar 1) ≤ 1 + 9 * aCos / 2 :=
    fun n => (sqrt_H1_energy_bound (ha n) (hq n)).le
  obtain ⟨phi, hphi, f, G, hf, hG, hwf, hL2, hwlim⟩ :=
    rellich_torus hw (fun n => (hH n).2.1) hg hbound
  exact ⟨fun n => rho (phi n), fun n => ha (phi n), fun n => hb (phi n),
    hlim.comp hphi.tendsto_atTop, f, G, hf, hG, hwf, hL2, hwlim⟩

end SharpLSI.FL.Prop82
