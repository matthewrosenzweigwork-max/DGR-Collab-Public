import LeanResearch.PeriodicAttractiveLogGas.RegularizationLemma
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Genuine L1 convergence of the prescribed Green kernels and gradients.
These are the limiting inputs for the integration by parts in source Lemma
3.1. The common gradient majorant is the already integrable inverse quotient
radius. Derivative convergence comes from the actual local harmonic identity,
and the single null pole is removed before dominated convergence.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PeriodicAttractiveLogGas

theorem eventually_regularizedGreenDifferential_eq
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hs : ∀ i, ε i ≤ (1 / 16 : ℝ))
    (ht : Tendsto ε l (𝓝 0)) {z : Torus} (hz : z ≠ 0) :
    ∀ᶠ i in l, regularizedGreenDifferential (ε i) (hε i) z = greenDifferential z := by
  have hx : centeredLift z ∈ offIntegerLattice := by
    change torusQuotient (centeredLift z) ≠ 0
    simpa only [torusQuotient_centeredLift] using hz
  obtain ⟨δ, hδ, hlocal⟩ := exists_regularizedGreen_lift_local_identity_on_compact
    (isCompact_singleton : IsCompact {centeredLift z}) (singleton_subset_iff.mpr hx)
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with i hi
  have hd := (hlocal (ε i) (hε i) (hs i) hi (centeredLift z) (mem_singleton _)).fderiv_eq (𝕜 := ℝ)
  simpa only [fderiv_add_const, regularizedGreenDifferential, greenDifferential] using hd

theorem eventually_regularizedGreenGradient_eq
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hs : ∀ i, ε i ≤ (1 / 16 : ℝ))
    (ht : Tendsto ε l (𝓝 0)) {z : Torus} (hz : z ≠ 0) :
    ∀ᶠ i in l, regularizedGreenGradient (ε i) (hε i) z = greenGradient z := by
  filter_upwards [eventually_regularizedGreenDifferential_eq hε hs ht hz] with i hi
  exact congrArg (fun L ↦ (InnerProductSpace.toDual ℝ PlanarSpace).symm L) hi

theorem exists_regularizedGreen_abs_majorant :
    ∃ M : Torus → ℝ, Integrable M torusMeasure ∧
      ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ (1 / 16 : ℝ) →
        ∀ᵐ z ∂torusMeasure, ‖regularizedGreen ε hε z‖ ≤ M z := by
  obtain ⟨Cg, hCg, hlower⟩ := exists_regularGreenRepresentative_lower_bound
  obtain ⟨C, hC, hupper⟩ := exists_regularizedGreen_upper_bound
  refine ⟨fun z ↦ ‖regularGreenRepresentative z‖ + Cg + C,
    (regularGreenRepresentative_integrable.norm.add (integrable_const Cg)).add
      (integrable_const C), ?_⟩
  intro ε hε hs
  filter_upwards [torusMeasure.ae_ne (0 : Torus)] with z hz
  have hlo := regularizedGreen_lower_bound hlower ε hε hs z
  have hup := hupper ε hε hs z hz
  have hscale : ε ^ 2 ≤ 1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hscale hC.le
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have hg := norm_nonneg (regularGreenRepresentative z)
    linarith
  · have hg := le_abs_self (regularGreenRepresentative z)
    rw [← Real.norm_eq_abs] at hg
    linarith

theorem tendsto_lintegral_regularizedGreen_sub
    (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (hs : ∀ i, ε i ≤ (1 / 16 : ℝ))
    (ht : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun i ↦ ∫⁻ z, ENNReal.ofReal
      ‖regularizedGreen (ε i) (hε i) z - regularGreenRepresentative z‖ ∂torusMeasure)
      atTop (𝓝 0) := by
  obtain ⟨M, hM, hb⟩ := exists_regularizedGreen_abs_majorant
  apply tendsto_lintegral_norm_of_dominated_convergence
    (fun i ↦ (continuous_regularizedGreen (ε i) (hε i)).aestronglyMeasurable)
    hM.hasFiniteIntegral (fun i ↦ hb (ε i) (hε i) (hs i))
  exact (torusMeasure.ae_ne (0 : Torus)).mono (fun z hz ↦
    tendsto_regularizedGreen hε hs ht hz)

theorem tendsto_lintegral_regularizedGreenGradient_sub
    (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (hs : ∀ i, ε i ≤ (1 / 16 : ℝ))
    (ht : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun i ↦ ∫⁻ z, ENNReal.ofReal
      ‖regularizedGreenGradient (ε i) (hε i) z - greenGradient z‖ ∂torusMeasure)
      atTop (𝓝 0) := by
  obtain ⟨C, _hC, hb⟩ := exists_regularizedGreenGradient_bound
  have hM : Integrable (fun z : Torus ↦ C / torusEuclideanNorm z) torusMeasure := by
    simpa only [div_eq_mul_inv] using integrable_torusEuclideanNorm_inv.const_mul C
  apply tendsto_lintegral_norm_of_dominated_convergence
    (fun i ↦ (continuous_regularizedGreenGradient (ε i) (hε i) (hs i)).aestronglyMeasurable)
    hM.hasFiniteIntegral
  · intro i
    exact (torusMeasure.ae_ne (0 : Torus)).mono (fun z hz ↦ hb (ε i) (hε i) (hs i) z hz)
  · exact (torusMeasure.ae_ne (0 : Torus)).mono (fun z hz ↦
      tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (eventually_regularizedGreenGradient_eq hε hs ht hz)))

theorem tendsto_integral_regularizedGreen_mul
    (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (hs : ∀ i, ε i ≤ (1 / 16 : ℝ))
    (ht : Tendsto ε atTop (𝓝 0)) (F : C(Torus, ℝ)) :
    Tendsto (fun i ↦ ∫ z, regularizedGreen (ε i) (hε i) z * F z ∂torusMeasure)
      atTop (𝓝 (∫ z, regularGreenRepresentative z * F z ∂torusMeasure)) := by
  obtain ⟨M, hM, hb⟩ := exists_regularizedGreen_abs_majorant
  apply tendsto_integral_of_dominated_convergence (fun z ↦ M z * ‖F‖)
    (fun i ↦ ((continuous_regularizedGreen (ε i) (hε i)).mul F.continuous).aestronglyMeasurable)
    (hM.mul_const ‖F‖)
  · intro i
    filter_upwards [hb (ε i) (hε i) (hs i)] with z hz
    change ‖regularizedGreen (ε i) (hε i) z * F z‖ ≤ M z * ‖F‖
    rw [norm_mul]
    exact mul_le_mul hz (F.norm_coe_le_norm z) (norm_nonneg _) ((norm_nonneg _).trans hz)
  · exact (torusMeasure.ae_ne (0 : Torus)).mono (fun z hz ↦
      (tendsto_regularizedGreen hε hs ht hz).mul tendsto_const_nhds)

theorem tendsto_integral_regularizedGreenGradient_inner
    (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (hs : ∀ i, ε i ≤ (1 / 16 : ℝ))
    (ht : Tendsto ε atTop (𝓝 0)) (F : C(Torus, PlanarSpace)) :
    Tendsto (fun i ↦ ∫ z, inner ℝ (regularizedGreenGradient (ε i) (hε i) z) (F z)
      ∂torusMeasure) atTop (𝓝 (∫ z, inner ℝ (greenGradient z) (F z) ∂torusMeasure)) := by
  obtain ⟨C, hC, hb⟩ := exists_regularizedGreenGradient_bound
  have hM : Integrable (fun z : Torus ↦ C / torusEuclideanNorm z * ‖F‖) torusMeasure := by
    simpa only [div_eq_mul_inv] using
      (integrable_torusEuclideanNorm_inv.const_mul C).mul_const ‖F‖
  apply tendsto_integral_of_dominated_convergence
    (fun z ↦ C / torusEuclideanNorm z * ‖F‖)
    (fun i ↦ ((continuous_regularizedGreenGradient (ε i) (hε i) (hs i)).inner
      F.continuous).aestronglyMeasurable) hM
  · intro i
    filter_upwards [torusMeasure.ae_ne (0 : Torus)] with z hz
    apply (norm_inner_le_norm _ _).trans
    exact mul_le_mul (hb (ε i) (hε i) (hs i) z hz) (F.norm_coe_le_norm z)
      (norm_nonneg _) (div_nonneg hC.le (torusEuclideanNorm_nonneg z))
  · filter_upwards [torusMeasure.ae_ne (0 : Torus)] with z hz
    have hpt : Tendsto (fun i ↦ regularizedGreenGradient (ε i) (hε i) z)
        atTop (𝓝 (greenGradient z)) :=
      tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (eventually_regularizedGreenGradient_eq hε hs ht hz))
    exact hpt.inner tendsto_const_nhds

end PeriodicAttractiveLogGas
