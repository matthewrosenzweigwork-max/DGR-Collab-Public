import FullLabeledLSI.Paper.Sec8Fourier4
import FullLabeledLSI.Statements.S07_Prop_3_1
import SharpSymmetricLSI.Paper.DensMeasure

/-!
# Section 8.5 (Corollary 8.4), part 5: free energy, minimizer and gap for `W(x,y) = G(x-y) - G(0)`

For a probability measure `ν`: `W(ν,ν) = ∬ G(x-y) dν dν - G(0)`, which is `≥ ∫G - G(0)` by positive
type, with equality at `ν = m`.  Hence `F_* = (∫G - G(0))/2`, `m` is a minimizer and
`G_θ(ρ) = ∑ θ_a H(ρ_a|m) + ½ ∬ ρ̄ρ̄ K₁`.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {d : ℕ}

/-- `∬ G(x-y) dν(x) dν(y)` (with `x` the inner variable, as in `interE`). -/
noncomputable def Qint (ν : Measure (Torus d)) (G : Torus d → ℝ) : ℝ :=
  ∫ y, ∫ x, G (x - y) ∂ν ∂ν

theorem integrable_cont_meas {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_pair {G : Torus d → ℝ} (hG : Continuous G) (ν : Measure (Torus d))
    [IsFiniteMeasure ν] :
    Integrable (fun p : Torus d × Torus d => G (p.1 - p.2)) (ν.prod ν) :=
  integrable_cont_meas (ν.prod ν) (hG.comp (continuous_fst.sub continuous_snd))

theorem interE_WG {G : Torus d → ℝ} (hG : Continuous G) (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] : interE (WG G) ν ν = Qint ν G - G 0 := by
  unfold interE Qint WG
  have h1 : ∀ y, ∫ x, (G (x - y) - G 0) ∂ν = ∫ x, G (x - y) ∂ν - G 0 := fun y => by
    rw [integral_sub (f := fun x => G (x - y)) (g := fun _ => G 0)
      (integrable_cont_meas ν (hG.comp (continuous_id.sub continuous_const)))
      (integrable_const _)]
    simp
  simp_rw [h1]
  rw [integral_sub (Integrable.integral_prod_right (integrable_pair hG ν)) (integrable_const _)]
  simp

theorem Qint_swap {G : Torus d → ℝ} (hG : Continuous G) (ν : Measure (Torus d))
    [IsFiniteMeasure ν] : Qint ν G = ∫ x, ∫ y, G (x - y) ∂ν ∂ν := by
  unfold Qint
  exact (integral_integral_swap (f := fun x y => G (x - y)) (integrable_pair hG ν)).symm

theorem Qint_K1 {G : Torus d → ℝ} (hG : Continuous G) (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] : Qint ν (K1 G) = Qint ν G - meanT G := by
  unfold Qint K1
  have h1 : ∀ y, ∫ x, (G (x - y) - meanT G) ∂ν = ∫ x, G (x - y) ∂ν - meanT G := fun y => by
    rw [integral_sub (f := fun x => G (x - y)) (g := fun _ => meanT G)
      (integrable_cont_meas ν (hG.comp (continuous_id.sub continuous_const)))
      (integrable_const _)]
    simp
  simp_rw [h1]
  rw [integral_sub (Integrable.integral_prod_right (integrable_pair hG ν)) (integrable_const _)]
  simp

theorem Qint_nonneg_of_K {K : Torus d → ℝ} (hK : IsSmoothT K)
    (hpos : ∀ k, 0 ≤ (cf K k).re) (ν : Measure (Torus d)) [IsFiniteMeasure ν] :
    0 ≤ Qint ν K := by
  rw [Qint_swap (continuous_of_isSmoothT hK)]
  exact pos_type hK hpos ν

theorem meanT_le_Qint {G : Torus d → ℝ} (hG : IsSmoothT G)
    (hGk : ∀ k : Fin d → ℤ, k ≠ 0 → 0 ≤ (cf G k).re) (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] : meanT G ≤ Qint ν G := by
  have h := Qint_nonneg_of_K (isSmoothT_K1 hG) (re_cf_K1_nonneg hG hGk) ν
  rw [Qint_K1 (continuous_of_isSmoothT hG)] at h
  linarith

theorem Qint_haar {G : Torus d → ℝ} (hG : Continuous G) : Qint (haar d) G = meanT G := by
  unfold Qint
  have h : ∀ y : Torus d, ∫ x, G (x - y) ∂haar d = meanT G := fun y => by
    exact integral_sub_right_eq_self (μ := haar d) G y
  simp_rw [h]
  simp

/-- The free energy of a probability measure. -/
theorem freeEnergy_WG {G : Torus d → ℝ} (hG : Continuous G) (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] :
    freeEnergy (fun _ => (0 : ℝ)) (WG G) ν =
      ((klDiv ν (haar d) : ℝ≥0∞) : EReal) + (((Qint ν G - G 0) / 2 : ℝ) : EReal) := by
  unfold freeEnergy
  rw [interE_WG hG]
  simp [potE]

theorem freeEnergy_WG_haar {G : Torus d → ℝ} (hG : Continuous G) :
    freeEnergy (fun _ => (0 : ℝ)) (WG G) (haar d) = (((meanT G - G 0) / 2 : ℝ) : EReal) := by
  rw [freeEnergy_WG hG, klDiv_self, Qint_haar hG]
  simp

theorem Fstar_WG {G : Torus d → ℝ} (hG : IsSmoothT G)
    (hGk : ∀ k : Fin d → ℤ, k ≠ 0 → 0 ≤ (cf G k).re) :
    Fstar (fun _ => (0 : ℝ)) (WG G) = (((meanT G - G 0) / 2 : ℝ) : EReal) := by
  have hGc := continuous_of_isSmoothT hG
  apply le_antisymm
  · exact (iInf_le (fun ρ : ProbabilityMeasure (Torus d) => freeEnergy (fun _ => (0 : ℝ)) (WG G) ρ)
      ⟨haar d, inferInstance⟩).trans (freeEnergy_WG_haar hGc).le
  · refine le_iInf fun μ => ?_
    have : IsProbabilityMeasure (μ : Measure (Torus d)) := inferInstance
    rw [freeEnergy_WG hGc]
    have hQ := meanT_le_Qint hG hGk (μ : Measure (Torus d))
    calc (((meanT G - G 0) / 2 : ℝ) : EReal)
        ≤ (((Qint (μ : Measure (Torus d)) G - G 0) / 2 : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr (by linarith)
      _ = 0 + (((Qint (μ : Measure (Torus d)) G - G 0) / 2 : ℝ) : EReal) := (zero_add _).symm
      _ ≤ _ := add_le_add (EReal.coe_ennreal_nonneg _) le_rfl

theorem isMinimizer_haar_WG {G : Torus d → ℝ} (hG : IsSmoothT G)
    (hGk : ∀ k : Fin d → ℤ, k ≠ 0 → 0 ≤ (cf G k).re) :
    IsMinimizer (fun _ => (0 : ℝ)) (WG G) (⟨haar d, inferInstance⟩ : ProbabilityMeasure (Torus d)) := by
  unfold IsMinimizer
  rw [Fstar_WG hG hGk]
  exact freeEnergy_WG_haar (continuous_of_isSmoothT hG)

end Sec8
end SharpLSI.FL
